import GaussianRegularCovarianceDeficit
import GaussianAssignmentCoordinateBridge

/-! Actual equality classification for completed-measurable fractional Gaussian
assignments.  Zero score loss forces the Gaussian winner rule; the exact regular
centroid Gram matrix supplies that zero loss. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical

namespace NegativeVotingAssignmentEquality
open NegativeVoting NegativeVotingFan NegativeVotingAssignmentDuality
  NegativeVotingCentroidOptimization NegativeVotingBalancedReference
  NegativeVotingBalancedMaximum NegativeVotingRegularCovarianceDeficit
  NegativeVotingFractionalMass NegativeVotingAssignmentCoordinateBridge
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean

section General
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem ae_eq_weights_of_zero_integral_gap
    (B : ι → FSC.Coord d) (hB : Function.Injective B) (h p : ι → ℝ)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f)
    (hzero : (∫ x, (maxScore (scores B h x)-∑ i,f x i*scores B h x i)
      ∂stdGaussian (FSC.Coord d))=0) :
    ∀ᵐ x ∂stdGaussian (FSC.Coord d), f x=weights B h x := by
  let winner : FSC.Coord d → ι := fun x => chosenWinner (scores B h x)
  have hstrict : ∀ᵐ x ∂stdGaussian (FSC.Coord d),
      ∀ i, i ≠ winner x → scores B h x i < scores B h x (winner x) := by
    filter_upwards [ae_scores_injective B hB h] with x hx
    intro i hi
    exact lt_of_le_of_ne (chosenWinner_max (scores B h x) i) (fun he => hi (hx he))
  have hzero' : (∫ x,routingLoss (f x) (scores B h x) (winner x)
      ∂stdGaussian (FSC.Coord d))=0 := by
    simpa only [routingLoss,maxScore,finite_max_eq_chosenWinner,winner] using hzero
  have hpure := ae_pure_of_integrable_scores (stdGaussian (FSC.Coord d)) f (scores B h)
    winner hf.2.1 hf.1 (score_integrable B h) hstrict hzero'
  filter_upwards [hpure,hstrict] with x hx hxs
  funext i
  exact (hx i).trans ((maxWeights_eq_indicator_of_strict_max (scores B h x) (winner x) hxs i).symm)

end General

variable {n d : ℕ}

theorem ae_regular_of_centroid_gram
    (p : Fin (n+2) → ℝ) (f : FSC.Coord d → Fin (n+2) → ℝ) (hf : Feasible p f)
    (hGram : ∀ i j,inner ℝ (centroidRows f i) (centroidRows f j)=
      (referenceScale n)^2*((if i=j then 1 else 0)-1/((n:ℝ)+2))) :
    ∃ R : Fin (n+2) → FSC.Coord d,
      (∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) ∧
      ∀ᵐ x ∂stdGaussian (FSC.Coord d),f x=weights R 0 x := by
  let B := centroidRows f
  let R : Fin (n+2) → FSC.Coord d := fun i => (referenceScale n)⁻¹ • B i
  have ha : 0 < referenceScale n := referenceScale_pos n
  have hm : (n:ℝ)+2 ≠ 0 := by positivity
  have hR : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2) := by
    intro i j
    dsimp [R,B]
    rw [real_inner_smul_left,real_inner_smul_right,hGram]
    field_simp [ne_of_gt ha,hm] <;> ring
  have hBR : (fun i => referenceScale n • R i)=B := by
    funext i
    simp only [R,smul_smul,mul_inv_cancel₀ (ne_of_gt ha),one_smul]
  have hBi : Function.Injective B := by
    intro i j hij
    by_contra hne
    have hh : inner ℝ (B i) (B i)=inner ℝ (B i) (B j) := congrArg (inner ℝ (B i)) hij
    change inner ℝ (centroidRows f i) (centroidRows f i)=
      inner ℝ (centroidRows f i) (centroidRows f j) at hh
    rw [hGram,hGram,if_pos rfl,if_neg hne] at hh
    nlinarith [sq_pos_of_pos ha]
  have hW : rowEnergy B=(referenceScale n)^2*((n:ℝ)+1) := by
    have hd (i : Fin (n+2)) : ‖B i‖^2=(referenceScale n)^2*(1-1/((n:ℝ)+2)) := by
      rw [←real_inner_self_eq_norm_sq]
      simpa [B] using hGram i i
    unfold rowEnergy
    simp_rw [hd]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_ofNat]
    field_simp [hm]
    ring
  have hmax := reference_expectedMax R hR
  rw [hBR] at hmax
  have hmaxE : expectedMax B 0=rowEnergy B := by
    rw [hmax,hW]
    unfold referenceScale
    field_simp [show (n:ℝ)+1 ≠ 0 by positivity] <;> ring
  have hmix : Integrable (fun x : FSC.Coord d => ∑ i,f x i*scores B 0 x i)
      (stdGaussian (FSC.Coord d)) :=
    integrable_score_mixture _ f (scores B 0) hf.2.1 hf.1 (score_integrable B 0)
  have hzero : (∫ x,(maxScore (scores B 0 x)-∑ i,f x i*scores B 0 x i)
      ∂stdGaussian (FSC.Coord d))=0 := by
    rw [integral_sub (max_integrable B 0) hmix]
    change expectedMax B 0-(∫ x,∑ i,f x i*(inner ℝ (B i) x+0)
      ∂stdGaussian (FSC.Coord d))=0
    simp only [add_zero]
    change expectedMax B 0-assignmentValue B f=0
    rw [hmaxE,show assignmentValue B f=centroidEnergy f from assignmentValue_centroid p f hf]
    simp only [centroidEnergy,B,sub_self]
  have hAE := ae_eq_weights_of_zero_integral_gap B hBi 0 p f hf hzero
  refine ⟨R,hR,?_⟩
  filter_upwards [hAE] with x hx
  rw [←hBR] at hx
  exact hx.trans (funext (scaled_weights_zero R (referenceScale n) ha x))

theorem ae_regular_of_zero_covariance_deficit (hn : 0 < n)
    (p : Fin (n+2) → ℝ) (f : FSC.Coord d → Fin (n+2) → ℝ) (hf : Feasible p f)
    (hz : regularCovarianceDeficit n (centroidRows f)=0) :
    ∃ rows : Fin (n+2) → Fin d → ℝ,RegularSimplexGram rows ∧
      ∀ᵐ x ∂stdGaussian (FSC.Coord d),f x=regularAssignment rows x.ofLp := by
  obtain ⟨R,hR,hAE⟩ := ae_regular_of_centroid_gram p f hf
    ((centroid_regular_deficit_zero_iff hn p f hf).mp hz)
  refine ⟨coordinateRows R,coordinateRows_gram R hR,?_⟩
  filter_upwards [hAE] with x hx
  exact hx.trans (funext (zero_weights_eq_regular R x))

/-- The exact equality class in the product coordinates of the full theorem.
No positive-mass or prescribed-uniform-mass premise is required. -/
theorem product_regular_of_zero_covariance_deficit (hn : 0 < n)
    (f : (Fin d → ℝ) → Fin (n+2) → ℝ)
    (hf : ∀ i,AEMeasurable (fun x => f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐ x ∂standardGaussian (Fin d),SimplexWeights (f x))
    (hz : regularCovarianceDeficit n
      (centroidRows (fun x : FSC.Coord d => f x.ofLp))=0) :
    ∃ rows : Fin (n+2) → Fin d → ℝ,RegularSimplexGram rows ∧
      ∀ᵐ x ∂standardGaussian (Fin d),f x=regularAssignment rows x := by
  have hF : Feasible (assignmentMass f) (fun x : FSC.Coord d => f x.ofLp) :=
    coordinateRule_feasible (LinearIsometryEquiv.refl ℝ (FSC.Coord d)) f hf hp
  obtain ⟨rows,hrows,hAE⟩ := ae_regular_of_zero_covariance_deficit hn
    (assignmentMass f) (fun x : FSC.Coord d => f x.ofLp) hF hz
  have hto : MeasurePreserving (WithLp.toLp 2)
      (standardGaussian (Fin d)) (stdGaussian (FSC.Coord d)) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  exact ⟨rows,hrows,hto.quasiMeasurePreserving.ae hAE⟩

end NegativeVotingAssignmentEquality
