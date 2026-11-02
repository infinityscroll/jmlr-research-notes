import GaussianSwitchingOrderedIntegral

/-! The actual pair bound at the prescribed cutoff θ^(-1/8).  All facet
integrals and error coefficients are retained.  The scalar absorption below
does not assume a positive lower bound on θ. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators Classical ENNReal Topology
namespace NegativeVotingSwitchingTiny
open NegativeVotingFan NegativeVotingSwitchingCell NegativeVotingSwitchingPair
  NegativeVotingWeightedFacet NegativeVotingSwitchingOrdered
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V]

def pairFacetCoefficient (B : V → E) (h : V → ℝ) (v : E → V → ℝ) (i j : V) : ℝ :=
  (gaussianPDFReal 0 1 (pairOffset B h i j) / (2 * ‖B i-B j‖)) *
    (∫ y in pairPlaneFacet B h i j, (max (pairPlaneForcing B h i j v y 0) 0)^2
      ∂stdGaussian _)

def pairCubicCoefficient (B : V → E) (h : V → ℝ) (σ D : ℝ) (i j : V) : ℝ :=
  gaussianPDFReal 0 1 (pairOffset B h i j) *
    (((Fintype.card V - 2 : ℕ) : ℝ) * D /
      (2 * ‖B i-B j‖^2 * (Real.sqrt (2*Real.pi) * σ * Real.sqrt (3/2))) +
      (2 + |pairOffset B h i j|) / ‖B i-B j‖^2)

def pairAmbientCoefficient (B : V → E) (v : E → V → ℝ) (i j : V) : ℝ :=
  (∫ x, |v x i + v x j|^32 ∂stdGaussian E) / ‖B i-B j‖^31

theorem pairCubicCoefficient_nonneg (B : V → E) (h : V → ℝ) (σ D : ℝ)
    (hσ : 0 ≤ σ) (hD : 0 ≤ D) (i j : V) : 0 ≤ pairCubicCoefficient B h σ D i j := by
  unfold pairCubicCoefficient
  apply mul_nonneg (gaussianPDFReal_nonneg _ _ _)
  positivity

theorem pairAmbientCoefficient_nonneg (B : V → E) (v : E → V → ℝ) (i j : V) :
    0 ≤ pairAmbientCoefficient B v i j := by
  unfold pairAmbientCoefficient
  exact div_nonneg (integral_nonneg fun x => pow_nonneg (abs_nonneg _) _) (by positivity)

/-- Exact scaling of the three non-facet error terms before choosing a cutoff. -/
theorem integral_cellReward_scaled
    (B : V → E) (h : V → ℝ) (i j : V) (hij : i ≠ j)
    (σ D : ℝ) (hσ : 0 < σ) (hlower : NegativeVotingCapTail.CenteredSingularLowerBound B σ)
    (hD : ∀ k ∈ thirdLabels i j, ‖B i-B k‖ ≤ D)
    (v : E → V → ℝ) (hvM : Measurable (fun x => v x i+v x j))
    (hv : MemLp (fun x => v x i+v x j) 32 (stdGaussian E))
    (θ M : ℝ) (hθ : 0 ≤ θ) (hM : 0 < M)
    (hη1 : θ*M/‖B i-B j‖ ≤ 1)
    (hsmall : (1+|pairOffset B h i j|)*(θ*M/‖B i-B j‖) ≤ 1/2)
    (W : ((ℝ ∙ (B i-B j))ᗮ) → ℝ) (hWM : Measurable W)
    (hW : MemLp W 32 (stdGaussian _)) (hW0 : ∀ y, 0 ≤ W y)
    (hcontrol : ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
      ContinuousOn (pairPlaneForcing B h i j v y) (Icc (0:ℝ) 1) ∧
      (∀ z ∈ Icc (0:ℝ) 1, pairPlaneForcing B h i j v y z ≤ W y) ∧
      (∀ z ∈ Icc (0:ℝ) 1, |pairPlaneForcing B h i j v y z-
        pairPlaneForcing B h i j v y 0| ≤ W y*z)) :
    (∫ x, cellReward B h i j v θ x ∂stdGaussian E) ≤
      θ^2 * pairFacetCoefficient B h v i j +
      (θ^3*M^3) * pairCubicCoefficient B h σ D i j +
      (θ*(M^31)⁻¹) * (∫ y, W y^32 ∂stdGaussian _) +
      θ^32 * pairAmbientCoefficient B v i j := by
  have hb := integral_cellReward_pair_bound B h i j hij σ D hσ hlower hD
    v hvM hv θ M hθ hM hη1 hsmall W hWM hW hW0 hcontrol
  convert hb using 1 <;>
    simp only [pairFacetCoefficient, pairCubicCoefficient, pairAmbientCoefficient] <;> ring

section Ordered
variable [Nonempty V]

/-- The leading coefficient is the actual ordered facet-square integral,
with no extra factor counting the labels. -/
def totalFacetCoefficient (B : V → E) (h : V → ℝ) (v : E → V → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, pairFacetCoefficient B h v i j

def totalCubicCoefficient (B : V → E) (h : V → ℝ) (σ D : ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, pairCubicCoefficient B h σ D i j

def totalNormalCoefficient (B : V → E)
    (W : ∀ i j : V, ((ℝ ∙ (B i-B j))ᗮ) → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ∫ y, (W i j y)^32 ∂stdGaussian _

def totalAmbientCoefficient (B : V → E) (v : E → V → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, pairAmbientCoefficient B v i j

theorem totalNormalCoefficient_nonneg (B : V → E)
    (W : ∀ i j : V, ((ℝ ∙ (B i-B j))ᗮ) → ℝ) : 0 ≤ totalNormalCoefficient B W := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact integral_nonneg (fun y => by positivity)

theorem totalAmbientCoefficient_nonneg (B : V → E) (v : E → V → ℝ) :
    0 ≤ totalAmbientCoefficient B v := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact pairAmbientCoefficient_nonneg B v i j

/-- The literal Gaussian cap is bounded by its leading facet integral and
three explicitly summed errors, under the genuine pair-normal hypotheses. -/
theorem integral_closedCellCap_scaled
    (B : V → E) (h : V → ℝ) (σ D : ℝ) (hσ : 0 < σ)
    (hlower : NegativeVotingCapTail.CenteredSingularLowerBound B σ)
    (hD : ∀ i j, ‖B i-B j‖ ≤ D)
    (v : E → V → ℝ) (hvM : ∀ i, Measurable (fun x => v x i))
    (hv : ∀ i j, i ≠ j → MemLp (fun x => v x i+v x j) 32 (stdGaussian E))
    (θ M : ℝ) (hθ : 0 ≤ θ) (hM : 0 < M)
    (hη1 : ∀ i j, i ≠ j → θ*M/‖B i-B j‖ ≤ 1)
    (hsmall : ∀ i j, i ≠ j →
      (1+|pairOffset B h i j|)*(θ*M/‖B i-B j‖) ≤ 1/2)
    (W : ∀ i j : V, ((ℝ ∙ (B i-B j))ᗮ) → ℝ)
    (hWM : ∀ i j, i ≠ j → Measurable (W i j))
    (hW : ∀ i j, i ≠ j → MemLp (W i j) 32 (stdGaussian _))
    (hW0 : ∀ i j, i ≠ j → ∀ y, 0 ≤ W i j y)
    (hcontrol : ∀ i j, i ≠ j → ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
      ContinuousOn (pairPlaneForcing B h i j v y) (Icc (0:ℝ) 1) ∧
      (∀ z ∈ Icc (0:ℝ) 1, pairPlaneForcing B h i j v y z ≤ W i j y) ∧
      (∀ z ∈ Icc (0:ℝ) 1, |pairPlaneForcing B h i j v y z-
        pairPlaneForcing B h i j v y 0| ≤ W i j y*z)) :
    (∫ x, closedCellCap B h v θ x ∂stdGaussian E) ≤
      θ^2 * totalFacetCoefficient B h v +
      (θ^3*M^3) * totalCubicCoefficient B h σ D +
      (θ*(M^31)⁻¹) * totalNormalCoefficient B W +
      θ^32 * totalAmbientCoefficient B v := by
  apply (integral_closedCellCap_le_ordered B h v θ hθ hvM hv).trans
  have hp : (∑ i, ∑ j ∈ Finset.univ.erase i,
      ∫ x, cellReward B h i j v θ x ∂stdGaussian E) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i,
      (θ^2 * pairFacetCoefficient B h v i j +
       (θ^3*M^3) * pairCubicCoefficient B h σ D i j +
       (θ*(M^31)⁻¹) * (∫ y, (W i j y)^32 ∂stdGaussian _) +
       θ^32 * pairAmbientCoefficient B v i j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    exact integral_cellReward_scaled B h i j hij σ D hσ hlower (fun k _ => hD i k)
      v ((hvM i).add (hvM j)) (hv i j hij) θ M hθ hM (hη1 i j hij) (hsmall i j hij)
      (W i j) (hWM i j hij) (hW i j hij) (hW0 i j hij) (hcontrol i j hij)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, totalFacetCoefficient,
    totalCubicCoefficient, totalNormalCoefficient, totalAmbientCoefficient] using hp

end Ordered

def tinyCutoff (θ : ℝ) : ℝ := θ ^ (-(1:ℝ)/8)

theorem tinyCutoff_pos (θ : ℝ) (hθ : 0 < θ) : 0 < tinyCutoff θ :=
  Real.rpow_pos_of_pos hθ _

theorem tinyCutoff_width (θ : ℝ) (hθ : 0 < θ) :
    θ * tinyCutoff θ = θ ^ ((7:ℝ)/8) := by
  unfold tinyCutoff
  have hh := Real.rpow_add hθ (1:ℝ) (-(1:ℝ)/8)
  norm_num at hh
  simpa only [neg_div] using hh.symm

theorem tinyCutoff_cubic (θ : ℝ) (hθ : 0 < θ) :
    θ^3 * (tinyCutoff θ)^3 = θ ^ ((21:ℝ)/8) := by
  unfold tinyCutoff
  rw [← Real.rpow_mul_natCast hθ.le, ← Real.rpow_natCast θ 3, ← Real.rpow_add hθ]
  norm_num

theorem tinyCutoff_tail (θ : ℝ) (hθ : 0 < θ) :
    θ * ((tinyCutoff θ)^31)⁻¹ = θ ^ ((39:ℝ)/8) := by
  unfold tinyCutoff
  rw [← Real.rpow_mul_natCast hθ.le, ← Real.rpow_neg hθ.le]
  have hh := Real.rpow_add hθ (1:ℝ) (-(-(1:ℝ)/8*(31:ℝ)))
  norm_num at hh ⊢
  simpa only [neg_div] using hh.symm

/-- The two smaller errors are dominated by the same θ^(21/8) scale. -/
theorem tinyCutoff_errors (θ C N A : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hN : 0 ≤ N) (hA : 0 ≤ A) :
    (θ^3*(tinyCutoff θ)^3)*C + (θ*((tinyCutoff θ)^31)⁻¹)*N + θ^32*A ≤
      (C+N+A) * θ ^ ((21:ℝ)/8) := by
  rw [tinyCutoff_cubic θ hθ, tinyCutoff_tail θ hθ]
  have htail := Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by norm_num : (21:ℝ)/8 ≤ 39/8)
  have hamb : θ^32 ≤ θ ^ ((21:ℝ)/8) := by
    rw [← Real.rpow_natCast θ 32]
    exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right htail hN, mul_le_mul_of_nonneg_right hamb hA]

/-- No amplitude floor occurs: a polynomial error coefficient can be absorbed
whenever C θ^(5/8)≤1, including arbitrarily small positive θ. -/
theorem tiny_error_absorbed (θ F C : ℝ) (hθ : 0 < θ)
    (hsmall : C * θ ^ ((5:ℝ)/8) ≤ 1) :
    F*θ^2 + C*θ^((21:ℝ)/8) ≤ (F+1)*θ^2 := by
  have he : θ^((21:ℝ)/8) = θ^2 * θ^((5:ℝ)/8) := by
    rw [← Real.rpow_natCast θ 2, ← Real.rpow_add hθ]
    norm_num
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hsmall (sq_nonneg θ)]

/-- A single alphabet threshold absorbs a fixed polynomial error at every
smaller amplitude.  The threshold precedes θ, so it cannot hide an amplitude
floor.  The strict exponent condition is precisely B > 8K/5. -/
theorem exists_uniform_tiny_threshold (C K B : ℝ) (hC : 0 ≤ C)
    (hgap : K < B * (5/8:ℝ)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 1 ≤ m ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ (m:ℝ)^(-B) →
        (C*(m:ℝ)^K)*θ^((5:ℝ)/8) ≤ 1 := by
  have hn : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hb := (tendsto_rpow_neg_atTop (sub_pos.mpr hgap)).comp hn
  have ht : Tendsto (fun m : ℕ => C*(m:ℝ)^(K-B*(5/8:ℝ))) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hb
    simpa only [neg_sub, Function.comp_apply, mul_zero] using hh
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (he.and (eventually_ge_atTop (1:ℕ)))
  refine ⟨N,?_⟩
  intro m hm
  obtain ⟨hsmall,hm1⟩ := hN m hm
  refine ⟨hm1,?_⟩
  intro θ hθ hθm
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<1) hm1)
  have hp := Real.rpow_le_rpow hθ.le hθm (by norm_num : (0:ℝ)≤5/8)
  have hmK : 0 ≤ C*(m:ℝ)^K := mul_nonneg hC (Real.rpow_nonneg hm0.le K)
  calc
    _ ≤ (C*(m:ℝ)^K)*((m:ℝ)^(-B))^((5:ℝ)/8) :=
      mul_le_mul_of_nonneg_left hp hmK
    _ = C*(m:ℝ)^(K-B*(5/8:ℝ)) := by
      rw [←Real.rpow_mul hm0.le, mul_assoc, ←Real.rpow_add hm0]
      congr 2
      ring
    _ ≤ 1 := hsmall.le

end NegativeVotingSwitchingTiny
