import GaussianRegularNoisePair
import GaussianFractionalMassEnergy

/-! Actual Gaussian integral of the projected regular routing estimate for
completed-measurable, almost-everywhere simplex-valued assignments. The pairing
is sum_i (f_i-g_i) T_{-r}g_i, without the first-variation factor two. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingRegularNoiseIntegral
open NegativeVoting NegativeVotingFan NegativeVotingRegularNoisePair
  NegativeVotingBalancedReference NegativeVotingFractionalMass
  NegativeVotingRegularFacetGaussianLower
variable {n d : ℕ}

def regularScoreLoss (B : Fin (n+2) → FSC.Coord d)
    (f : FSC.Coord d → Fin (n+2) → ℝ) (x : FSC.Coord d) : ℝ :=
  maxScore (fun i => inner ℝ (B i) x)-∑i,f x i*inner ℝ (B i) x

def regularPotentialPairing (B : Fin (n+2) → FSC.Coord d) (r : ℝ)
    (f : FSC.Coord d → Fin (n+2) → ℝ) (x : FSC.Coord d) : ℝ :=
  ∑i,(f x i-regularAssignment (fun k => (B k).ofLp) x.ofLp i)*
    gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x.ofLp i

def weightedRegularRoutingLoss (B : Fin (n+2) → FSC.Coord d) (r : ℝ)
    (f : FSC.Coord d → Fin (n+2) → ℝ) (x : FSC.Coord d) : ℝ :=
  projectedNoiseWeight B r x*regularScoreLoss B f x

theorem regularScoreLoss_nonneg (B : Fin (n+2) → FSC.Coord d)
    (f : FSC.Coord d → Fin (n+2) → ℝ) (x : FSC.Coord d)
    (hp : SimplexWeights (f x)) : 0 ≤ regularScoreLoss B f x := by
  let s : Fin (n+2) → ℝ := fun i => inner ℝ (B i) x
  change 0 ≤ maxScore s-∑i,f x i*s i
  rw [show maxScore s=s (chosenWinner s) from finite_max_eq_chosenWinner s]
  exact routingLoss_nonneg (f x) s (chosenWinner s) hp (chosenWinner_max s)

theorem regularScoreLoss_integrable (B : Fin (n+2) → FSC.Coord d)
    (f : FSC.Coord d → Fin (n+2) → ℝ)
    (hf : ∀i,AEMeasurable (fun x => f x i) (stdGaussian (FSC.Coord d)))
    (hp : ∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) :
    Integrable (regularScoreLoss B f) (stdGaussian (FSC.Coord d)) := by
  have hs (i : Fin (n+2)) : Integrable (fun x => inner ℝ (B i) x)
      (stdGaussian (FSC.Coord d)) := IsGaussian.integrable_dual _ (innerSL ℝ (B i))
  have hm := integrable_finite_max (stdGaussian (FSC.Coord d))
    (fun x i => inner ℝ (B i) x) Finset.univ Finset.univ_nonempty (fun i _ => hs i)
  exact hm.sub (integrable_score_mixture _ f _ hp hf hs)

theorem projectedNoiseWeight_continuous (B : Fin (n+2) → FSC.Coord d) (r : ℝ) :
    Continuous (projectedNoiseWeight B r) := by
  unfold projectedNoiseWeight
  fun_prop

theorem projectedNoiseWeight_le_scale (B : Fin (n+2) → FSC.Coord d)
    (r : ℝ) (hr : 0<r) (x : FSC.Coord d) :
    projectedNoiseWeight B r x ≤ referenceScale n*r := by
  have hL : 0 ≤ 1+Real.log ((n:ℝ)+2) := by
    have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hh := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith)
    linarith
  have hq : 0 ≤ 2*facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*r^2*
      ‖NegativeVotingCenteredParseval.frameOperator B x‖^2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) facetGaussianConstant_pos.le) hL) (sq_nonneg r))
      (sq_nonneg _)
  have he := Real.exp_le_one_iff.mpr (show
      -1-2*facetGaussianConstant*(1+Real.log ((n:ℝ)+2))*r^2*
        ‖NegativeVotingCenteredParseval.frameOperator B x‖^2 ≤ 0 by linarith)
  simpa only [projectedNoiseWeight,mul_one] using
    mul_le_mul_of_nonneg_left he (mul_nonneg (referenceScale_pos n).le hr.le)

theorem weightedRegularRoutingLoss_integrable (B : Fin (n+2) → FSC.Coord d)
    (r : ℝ) (hr : 0<r) (f : FSC.Coord d → Fin (n+2) → ℝ)
    (hf : ∀i,AEMeasurable (fun x => f x i) (stdGaussian (FSC.Coord d)))
    (hp : ∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) :
    Integrable (weightedRegularRoutingLoss B r f) (stdGaussian (FSC.Coord d)) := by
  apply (regularScoreLoss_integrable B f hf hp).bdd_mul (c := referenceScale n*r)
    (projectedNoiseWeight_continuous B r).measurable.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_pos (projectedNoiseWeight_pos B r hr x)]
  exact projectedNoiseWeight_le_scale B r hr x

theorem regularPotentialPairing_integrable (B : Fin (n+2) → FSC.Coord d) (r : ℝ)
    (f : FSC.Coord d → Fin (n+2) → ℝ)
    (hf : ∀i,AEMeasurable (fun x => f x i) (stdGaussian (FSC.Coord d)))
    (hp : ∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) :
    Integrable (regularPotentialPairing B r f) (stdGaussian (FSC.Coord d)) := by
  let g := regularAssignment (fun k => (B k).ofLp)
  let G : FSC.Coord d → Fin (n+2) → ℝ := fun x => g x.ofLp
  let P : FSC.Coord d → Fin (n+2) → ℝ := fun x => gaussianNoiseOperator (-r) g x.ofLp
  have hg (i : Fin (n+2)) : Measurable (fun x => g x i) := regularAssignment_measurable _ i
  have hgs (x : Fin d → ℝ) : SimplexWeights (g x) := regularAssignment_simplex _ x
  have hG (i : Fin (n+2)) : Measurable (fun x => G x i) := (hg i).comp (by fun_prop)
  have hGsimplex : ∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (G x) :=
    Eventually.of_forall (fun x => hgs x.ofLp)
  have hPmeas (i : Fin (n+2)) : Measurable (fun x => P x i) :=
    (measurable_gaussianNoiseOperator (-r) g hg i).comp (by fun_prop)
  have hPs (x : FSC.Coord d) : SimplexWeights (P x) :=
    gaussianNoiseOperator_simplex (-r) g hg hgs x.ofLp
  have hPi (i : Fin (n+2)) : Integrable (fun x => P x i)
      (stdGaussian (FSC.Coord d)) := by
    apply Integrable.of_mem_Icc (a := 0) (b := 1) (hPmeas i).aemeasurable
    filter_upwards with x
    exact ⟨(hPs x).1 i,simplex_weight_le_one (P x) (hPs x) i⟩
  apply integrable_finsetSum Finset.univ
  intro i _
  have hfi := integrable_weighted_score (stdGaussian (FSC.Coord d)) f P i hp (hf i) (hPi i)
  have hgi := integrable_weighted_score (stdGaussian (FSC.Coord d)) G P i
    hGsimplex (hG i).aemeasurable (hPi i)
  convert hfi.sub hgi using 1
  funext x
  change (f x i-G x i)*P x i=f x i*P x i-G x i*P x i
  ring

/-- Actual Gaussian integral comparison, with completed measurability and the
simplex constraints only almost everywhere. Both integrability inputs are
proved from these hypotheses. -/
theorem ae_simplex_integral_routing_lower (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hrhalf : r ≤ 1/2)
    (f : FSC.Coord d → Fin (n+2) → ℝ)
    (hf : ∀i,AEMeasurable (fun x => f x i) (stdGaussian (FSC.Coord d)))
    (hp : ∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (f x)) :
    (∫x,weightedRegularRoutingLoss B r f x ∂stdGaussian (FSC.Coord d)) ≤
      ∫x,regularPotentialPairing B r f x ∂stdGaussian (FSC.Coord d) := by
  apply integral_mono_ae (weightedRegularRoutingLoss_integrable B r hr f hf hp)
    (regularPotentialPairing_integrable B r f hf hp)
  filter_upwards [hp] with x hx
  exact regular_noise_fractional_loss_lower hn hmean B hG r hr hrhalf x (f x) hx

/-- The same inequality in the finite-product Gaussian coordinates of MainGoal.
Completed measurability and the simplex property remain only almost everywhere;
no choice of Borel representative or integrability premise is supplied. -/
theorem ae_simplex_product_integral_routing_lower (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hrhalf : r ≤ 1/2)
    (f : (Fin d → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀i,AEMeasurable (fun x => f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) :
    (∫x,projectedNoiseWeight B r (WithLp.toLp 2 x)*
      (maxScore (fun i => (∑j,(B i).ofLp j*x j))-
        ∑i,f x i*(∑j,(B i).ofLp j*x j)) ∂standardGaussian (Fin d)) ≤
    ∫x,(∑i,(f x i-regularAssignment (fun k => (B k).ofLp) x i)*
      gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x i)
        ∂standardGaussian (Fin d) := by
  let F : FSC.Coord d → Fin (n+2) → ℝ := fun x => f x.ofLp
  have hm := gaussian_ofLp_measurePreserving (κ := Fin d)
  have hF (i : Fin (n+2)) : AEMeasurable (fun x => F x i)
      (stdGaussian (FSC.Coord d)) :=
    ((hf i).aestronglyMeasurable.comp_measurePreserving hm).aemeasurable
  have hFp : ∀ᵐx ∂stdGaussian (FSC.Coord d),SimplexWeights (F x) :=
    hm.quasiMeasurePreserving.ae hp
  have hh := ae_simplex_integral_routing_lower hn hmean B hG r hr hrhalf F hF hFp
  have hleft :
      (∫x,projectedNoiseWeight B r (WithLp.toLp 2 x)*
        (maxScore (fun i => (∑j,(B i).ofLp j*x j))-
          ∑i,f x i*(∑j,(B i).ofLp j*x j)) ∂standardGaussian (Fin d))=
      ∫x,weightedRegularRoutingLoss B r F x ∂stdGaussian (FSC.Coord d) := by
    rw [integral_standardGaussian_eq_euclidean]
    apply integral_congr_ae
    filter_upwards with x
    simp only [weightedRegularRoutingLoss,regularScoreLoss,F,WithLp.toLp_ofLp,
      PiLp.inner_apply,Real.inner_apply]
  have hright :
      (∫x,(∑i,(f x i-regularAssignment (fun k => (B k).ofLp) x i)*
        gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x i)
          ∂standardGaussian (Fin d))=
      ∫x,regularPotentialPairing B r F x ∂stdGaussian (FSC.Coord d) :=
    integral_standardGaussian_eq_euclidean _
  rw [hleft,hright]
  exact hh

end NegativeVotingRegularNoiseIntegral
