import GaussianFanQuadraticHessian
import GaussianFanMovingCells

/-! Actual second variations of the Gaussian expected maximum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators Topology

namespace NegativeVotingFanHessian
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanTestedCells
  NegativeVotingFanMovingCells NegativeVotingFacetDegree NegativeVotingCapTail

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The actual finite family of distinct rows stays distinct in a parameter
neighborhood. This is derived, rather than supplied as a path assumption. -/
theorem eventually_injective_rows (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) :
    ∀ᶠ p : Parameters d ι in 𝓝 (B,h), Function.Injective p.1 := by
  have he (i j : ι) : ∀ᶠ p : Parameters d ι in 𝓝 (B,h), p.1 i=p.1 j → i=j := by
    by_cases hij : i=j
    · exact Eventually.of_forall fun _ _ => hij
    have hc : ContinuousAt (fun p : Parameters d ι => p.1 i) (B,h) := by fun_prop
    have hd : ContinuousAt (fun p : Parameters d ι => p.1 j) (B,h) := by fun_prop
    have hn : B i ≠ B j := fun he => hij (hB he)
    have ht := (hc.ne_iff_eventually_ne hd).mp hn
    exact ht.mono fun _ hp he => (hp he).elim
  have hall : ∀ᶠ p : Parameters d ι in 𝓝 (B,h), ∀ i j, p.1 i=p.1 j → i=j :=
    eventually_all.mpr fun i => eventually_all.mpr (he i)
  exact hall

/-- A genuine derivative of the first derivative, evaluated on the fixed
second direction. Each term is the actual moving tested-cell derivative. -/
def secondDerivative (B : ι → FSC.Coord d) (h : ι → ℝ)
    (E : ι → FSC.Coord d) (e : ι → ℝ) : Parameters d ι →L[ℝ] ℝ :=
  ∑ i, testedCellDerivative B h i (fun x => inner ℝ (E i) x+e i)

theorem hasFDerivAt_jointDerivative_apply (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ)
    (E : ι → FSC.Coord d) (e : ι → ℝ) :
    HasFDerivAt (fun p : Parameters d ι => jointDerivative p.1 p.2 (E,e))
      (secondDerivative B h E e) (B,h) := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hs := HasFDerivAt.sum (u := Finset.univ) fun i _ =>
    hasFDerivAt_affine_testedCell B h σ hσ hlower i (E i) (e i)
  simp only [Finset.sum_apply] at hs
  apply hs.congr_of_eventuallyEq
  filter_upwards [eventually_injective_rows B hB h] with p hp
  simpa only [Finset.sum_apply] using jointDerivative_eq_cell_affine_tests p.1 hp p.2 E e

/-- Actual derivative along a jointly moving row/offset line. -/
theorem hasDerivAt_jointDerivative_line (B D E : ι → FSC.Coord d) (h v e : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    HasDerivAt (fun t : ℝ => jointDerivative (B+t•D) (h+t•v) (E,e))
      (secondDerivative B h E e (D,v)) 0 := by
  have hp : HasDerivAt (fun t : ℝ => (B,h)+t•(D,v)) (D,v) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (D,v)).const_add (B,h)
  have hg : HasFDerivAt (fun p : Parameters d ι => jointDerivative p.1 p.2 (E,e))
      (secondDerivative B h E e) ((B,h)+(0:ℝ)•(D,v)) := by
    simpa using hasFDerivAt_jointDerivative_apply B h σ hσ hlower E e
  exact hg.comp_hasDerivAt 0 hp

/-- The first derivative of the actual scalar expected maximum agrees locally
with its joint Frechet derivative evaluated on the line direction. -/
theorem deriv_expectedMax_line_eventually (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (hB : Function.Injective B) :
    (fun t : ℝ => deriv (fun s : ℝ => expectedMax (B+s•D) (h+s•v)) t) =ᶠ[𝓝 0]
      (fun t => jointDerivative (B+t•D) (h+t•v) (D,v)) := by
  have hp : ContinuousAt (fun t : ℝ => (B,h)+t•(D,v)) 0 := by fun_prop
  have hnear := hp.tendsto.eventually (by
    simpa using eventually_injective_rows B hB h)
  filter_upwards [hnear] with t ht
  have hline : HasDerivAt (fun s : ℝ => (B,h)+s•(D,v)) (D,v) t := by
    simpa using ((hasDerivAt_id t).smul_const (D,v)).const_add (B,h)
  have hh := (hasFDerivAt_expectedMax_joint (B+t•D) ht (h+t•v)).comp_hasDerivAt t hline
  exact hh.deriv

/-- The actual scalar second derivative exists, obtained by differentiating
the proved first derivative rather than postulating a Hessian identity. -/
theorem hasDerivAt_deriv_expectedMax_line (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    HasDerivAt (deriv (fun t : ℝ => expectedMax (B+t•D) (h+t•v)))
      (secondDerivative B h D v (D,v)) 0 := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  exact (hasDerivAt_jointDerivative_line B D D h v v σ hσ hlower).congr_of_eventuallyEq
    (deriv_expectedMax_line_eventually B D h v hB)



/-- The actual derivative of the first derivative equals the symmetric
Gaussian surface expression, after pairing both orientations. -/
theorem secondDerivative_apply_eq_mixedForm (B D E : ι → FSC.Coord d) (h v e : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    secondDerivative B h E e (D,v) = mixedForm B h D v E e := by
  rw [← orderedMixedResponse_eq_mixedForm]
  unfold secondDerivative orderedMixedResponse
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [testedCellDerivative_apply_ambient B h σ hσ hlower i
    (fun x => inner ℝ (E i) x+e i) (by fun_prop) (‖E i‖+|e i|)
    (by positivity) (affine_test_growth (E i) (e i)) (D,v)]
  have he (j : ι) : (fun x : FSC.Coord d => (inner ℝ (E i) x+e i) *
      (inner ℝ (D i-D j) x+v i-v j)) =
      fun x => affineScore E e i x*(affineScore D v i x-affineScore D v j x) := by
    funext x
    simp only [affineScore,inner_sub_left]
    ring
  simp_rw [he]
  change (∑ j : {j : ι // j ≠ i}, surfaceIntegral B h j.1 i
    (fun x => affineScore E e i x*(affineScore D v i x-affineScore D v j.1 x))) = _
  calc
    _ = ∑ j : {j : ι // j ≠ i}, surfaceIntegral B h i j.1
        (fun x => affineScore E e i x*(affineScore D v i x-affineScore D v j.1 x)) :=
      Finset.sum_congr rfl fun j _ => surfaceIntegral_reverse B h i j.1 _
    _ = ∑ j, surfaceIntegral B h i j
        (fun x => affineScore E e i x*(affineScore D v i x-affineScore D v j x)) := by
      rw [← Finset.sum_subtype (p := fun j : ι => j ≠ i) (Finset.univ.erase i)
        (fun j => by simp) (fun j => surfaceIntegral B h i j
          (fun x => affineScore E e i x*(affineScore D v i x-affineScore D v j x)))]
      apply Finset.sum_subset (Finset.erase_subset _ _)
      intro j _ hj
      have hji : j=i := by simpa using hj
      rw [hji,surfaceIntegral_diagonal]

/-- Mixed second variation of the actual Gaussian expected maximum. -/
theorem hasDerivAt_jointDerivative_line_mixedForm (B D E : ι → FSC.Coord d)
    (h v e : ι → ℝ) (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    HasDerivAt (fun t : ℝ => jointDerivative (B+t•D) (h+t•v) (E,e))
      (mixedForm B h D v E e) 0 := by
  rw [← secondDerivative_apply_eq_mixedForm B D E h v e σ hσ hlower]
  exact hasDerivAt_jointDerivative_line B D E h v e σ hσ hlower

/-- The actual second directional derivative is the paired square-facet
formula. All Gaussian differentiation and edge-nullness are derived. -/
theorem hasDerivAt_deriv_expectedMax_line_quadraticForm (B D : ι → FSC.Coord d)
    (h v : ι → ℝ) (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    HasDerivAt (deriv (fun t : ℝ => expectedMax (B+t•D) (h+t•v)))
      (quadraticForm B h D v) 0 := by
  rw [← mixedForm_self,← secondDerivative_apply_eq_mixedForm B D D h v v σ hσ hlower]
  exact hasDerivAt_deriv_expectedMax_line B D h v σ hσ hlower

/-- Numerical form of the genuine second derivative, useful for matrix and
Schur-complement calculations. -/
theorem deriv_deriv_expectedMax_line (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    deriv (deriv (fun t : ℝ => expectedMax (B+t•D) (h+t•v))) 0 =
      quadraticForm B h D v :=
  (hasDerivAt_deriv_expectedMax_line_quadraticForm B D h v σ hσ hlower).deriv

/-- Positivity is a consequence of the actual square-facet representation. -/
theorem deriv_deriv_expectedMax_line_nonneg (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) :
    0 ≤ deriv (deriv (fun t : ℝ => expectedMax (B+t•D) (h+t•v))) 0 := by
  rw [deriv_deriv_expectedMax_line B D h v σ hσ hlower]
  exact quadraticForm_nonneg B D h v

end NegativeVotingFanHessian
