import GaussianFanMassInverse

/-! The actual optimized Gaussian dual value, including degenerate row systems.
Its infimum is over the literal centered offset space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingFanValue
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFacetDegree NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def optimizedValue (B : ι → FSC.Coord d) (p : ι → ℝ) : ℝ :=
  sInf (Set.range (fun h : centeredGauge ι => potential B p h))

theorem potential_nonneg (B : ι → FSC.Coord d) (p h : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : 0 ≤ potential B p h := by
  unfold potential
  apply sub_nonneg.mpr
  calc
    ∑ i, p i * h i ≤ ∑ i, p i * expectedMax B h :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (offset_le_expectedMax B h i) (hp i))
    _ = expectedMax B h := by rw [← Finset.sum_mul, hs, one_mul]

theorem potential_range_bddBelow (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    BddBelow (Set.range (fun h : centeredGauge ι => potential B p h)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨h,rfl⟩
  exact potential_nonneg B p h hp hs

theorem optimizedValue_nonneg (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : 0 ≤ optimizedValue B p := by
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨h,rfl⟩
  exact potential_nonneg B p h hp hs

theorem optimizedValue_le_potential (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (h : centeredGauge ι) :
    optimizedValue B p ≤ potential B p h :=
  csInf_le (potential_range_bddBelow B p hp hs) (Set.mem_range_self h)

theorem optimizedValue_eq_of_minimizer (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (h : centeredGauge ι)
    (hmin : ∀ k : centeredGauge ι, potential B p h ≤ potential B p k) :
    optimizedValue B p = potential B p h := by
  apply le_antisymm (optimizedValue_le_potential B p hp hs h)
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨k,rfl⟩
  exact hmin k

/-- Actual prescribed masses identify the attained infimum; no supplied
optimality or inverse hypothesis is needed. -/
theorem optimizedValue_eq_of_mass (B : ι → FSC.Coord d) (p : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) (h : centeredGauge ι)
    (hm : mass B h = p) : optimizedValue B p = potential B p h := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  obtain ⟨k,hk,hmin⟩ := exists_potential_minimizer B p hp hs
  have hkm : mass B k = p := funext (masses_eq_of_minimizer B hB p k hs hk hmin)
  have he := centered_offsets_unique B σ hσ hlower h k h.property hk (hm.trans hkm.symm)
  apply optimizedValue_eq_of_minimizer B p (fun i => (hp i).le) hs h
  intro l
  rw [he]
  exact hmin l l.property

/-- The row perturbation bound is uniform in every offset. -/
theorem max_score_rows_sub_bound (B C : ι → FSC.Coord d) (h : ι → ℝ) (x : FSC.Coord d) :
    |NegativeVoting.maxScore (scores B h x) - NegativeVoting.maxScore (scores C h x)| ≤
      ‖B-C‖ * ‖x‖ := by
  apply (maxScore_sub_bound _ _).trans
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro i
  have he : (scores B h x - scores C h x) i = inner ℝ ((B-C) i) x := by
    simp [scores, inner_sub_left]
  rw [he]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_le_pi_norm (B-C) i) (norm_nonneg x))

theorem expectedMax_rows_sub_bound (B C : ι → FSC.Coord d) (h : ι → ℝ) :
    |expectedMax B h - expectedMax C h| ≤
      ‖B-C‖ * ∫ x : FSC.Coord d, ‖x‖ ∂stdGaussian (FSC.Coord d) := by
  have hi := (max_integrable B h).sub (max_integrable C h)
  have hx : Integrable (fun x : FSC.Coord d => ‖x‖) (stdGaussian (FSC.Coord d)) :=
    IsGaussian.integrable_id.norm
  calc
    |expectedMax B h - expectedMax C h| =
        ‖∫ x, NegativeVoting.maxScore (scores B h x)-NegativeVoting.maxScore (scores C h x)
          ∂stdGaussian (FSC.Coord d)‖ := by
      rw [integral_sub (max_integrable B h) (max_integrable C h)]
      rfl
    _ ≤ ∫ x, ‖NegativeVoting.maxScore (scores B h x)-NegativeVoting.maxScore (scores C h x)‖
          ∂stdGaussian (FSC.Coord d) := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖B-C‖ * ‖x‖ ∂stdGaussian (FSC.Coord d) :=
      integral_mono hi.norm (hx.const_mul _) (fun x => max_score_rows_sub_bound B C h x)
    _ = _ := integral_const_mul _ _

theorem potential_rows_sub_bound (B C : ι → FSC.Coord d) (p h : ι → ℝ) :
    |potential B p h - potential C p h| ≤
      ‖B-C‖ * ∫ x : FSC.Coord d, ‖x‖ ∂stdGaussian (FSC.Coord d) := by
  have he : potential B p h - potential C p h = expectedMax B h - expectedMax C h := by
    unfold potential
    ring
  rw [he]
  exact expectedMax_rows_sub_bound B C h

/-- The actual infimum is Lipschitz in the rows even at singular row systems. -/
theorem optimizedValue_rows_sub_bound (B C : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    |optimizedValue B p - optimizedValue C p| ≤
      ‖B-C‖ * ∫ x : FSC.Coord d, ‖x‖ ∂stdGaussian (FSC.Coord d) := by
  have hupper (A D : ι → FSC.Coord d) : optimizedValue A p - optimizedValue D p ≤
      ‖A-D‖ * ∫ x : FSC.Coord d, ‖x‖ ∂stdGaussian (FSC.Coord d) := by
    have hc : optimizedValue A p -
        ‖A-D‖ * ∫ x : FSC.Coord d, ‖x‖ ∂stdGaussian (FSC.Coord d) ≤ optimizedValue D p := by
      apply le_csInf (Set.range_nonempty _)
      rintro z ⟨k,rfl⟩
      have h1 := optimizedValue_le_potential A p hp hs k
      have h2 := (abs_le.mp (potential_rows_sub_bound A D p k)).2
      linarith
    linarith
  exact abs_le.mpr ⟨by have ht := hupper C B; rw [norm_sub_rev C B] at ht; linarith, hupper B C⟩

theorem optimizedValue_continuous_rows (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Continuous (fun B : ι → FSC.Coord d => optimizedValue B p) := by
  let K : NNReal := ⟨∫ x : FSC.Coord d, ‖x‖ ∂stdGaussian (FSC.Coord d),
    integral_nonneg (fun x => norm_nonneg x)⟩
  have hL : LipschitzWith K (fun B : ι → FSC.Coord d => optimizedValue B p) := by
    apply LipschitzWith.of_dist_le_mul
    intro B C
    simp only [dist_eq_norm, Real.norm_eq_abs]
    change |optimizedValue B p - optimizedValue C p| ≤
      (∫ x : FSC.Coord d, ‖x‖ ∂stdGaussian (FSC.Coord d)) * ‖B-C‖
    simpa only [mul_comm] using optimizedValue_rows_sub_bound B C p hp hs
  exact hL.continuous

end NegativeVotingFanValue
