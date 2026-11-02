import GaussianNearBalancedActualCap
import GaussianRegularCoefficientMajorant

/-! Actual regular-noise pair cancellation and its finite fractional cap.
This supplies the pointwise routing bridge, including all reference ties.
It does not assume or state the final noise comparison. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingOwnCentroidRoutingCap
open NegativeVoting NegativeVotingFan NegativeVotingRegularPairCoefficient
  NegativeVotingRegularFacetRange NegativeVotingReciprocalDampingTube
  NegativeVotingFacetConditionalPlane
  NegativeVotingSwitchingOrdered NegativeVotingSwitchingCell NegativeVotingBalancedReference

section Scalar
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem utilityRange_sq_le_scoreEnergy (u : ι → ℝ) :
    (utilityRange u)^2 ≤ 4*scoreEnergy u := by
  have hE:0 ≤ scoreEnergy u:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hi i:(u i)^2 ≤ scoreEnergy u:=Finset.single_le_sum
    (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  have hu i:u i ∈ Icc (-Real.sqrt (scoreEnergy u)) (Real.sqrt (scoreEnergy u)):=by
    apply abs_le.mp
    exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rw [sq_abs,Real.sq_sqrt hE];exact hi i)
  have hR:=utilityRange_le_of_between u _ _ hu
  have hR0:=utilityRange_nonneg u
  nlinarith [Real.sq_sqrt hE,Real.sqrt_nonneg (scoreEnergy u)]

def dampingEta (n : ℕ) (r : ℝ) : ℝ:=
  (rangeFacetConstant^2*(1+Real.log ((n:ℝ)+2))+4*rangeFacetConstant)*
    (r/Real.sqrt (1-r^2))^2

def dampingSizeConstant : ℝ:=2*(rangeFacetConstant^2+4*rangeFacetConstant)

theorem dampingSizeConstant_nonneg : 0 ≤ dampingSizeConstant := by
  unfold dampingSizeConstant
  positivity [rangeFacetConstant_pos]

theorem dampingEta_nonneg (n : ℕ) (r : ℝ) : 0 ≤ dampingEta n r := by
  unfold dampingEta
  positivity [rangeFacetConstant_pos,Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])]

theorem rangeExponent_le_damping (n : ℕ) (r : ℝ) (u : ι → ℝ) :
    rangeExponent n ((r/Real.sqrt (1-r^2))*utilityRange u) ≤
      1+dampingEta n r*scoreEnergy u := by
  let C:=rangeFacetConstant
  let L:=1+Real.log ((n:ℝ)+2)
  let t:=r/Real.sqrt (1-r^2)
  have hC:0 ≤ C:=rangeFacetConstant_pos.le
  have hL:0 ≤ L:=by
    dsimp [L]
    linarith [Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])]
  have hR:=utilityRange_sq_le_scoreEnergy u
  have h₁:(C*t*utilityRange u*Real.sqrt L)^2 ≤
      4*C^2*t^2*L*scoreEnergy u:=by
    calc
      _ = C^2*t^2*L*(utilityRange u)^2:=by rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hL];ring
      _ ≤ _:=by nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ C^2*t^2*L by positivity)]
  have hlin:C*t*utilityRange u*Real.sqrt L ≤ 1+C^2*t^2*L*scoreEnergy u:=by
    nlinarith [sq_nonneg (C*t*utilityRange u*Real.sqrt L-2)]
  have hquad:C*(t*utilityRange u)^2 ≤ 4*C*t^2*scoreEnergy u:=by
    nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ C*t^2 by positivity)]
  dsimp only [rangeExponent,dampingEta]
  change C*((t*utilityRange u)*Real.sqrt L+(t*utilityRange u)^2) ≤
    1+(C^2*L+4*C)*t^2*scoreEnergy u
  nlinarith only [hlin,hquad]

theorem dampingEta_le (n : ℕ) (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2) :
    dampingEta n r ≤ dampingSizeConstant*r^2*(1+Real.log ((n:ℝ)+2)) := by
  have hr1:r < 1:=by linarith
  have hs:=NegativeVotingRegularOU.negative_noise_scale_pos r hr hr1
  have hsq:=Real.sq_sqrt (show 0 ≤ 1-r^2 by nlinarith)
  have ht:(r/Real.sqrt (1-r^2))^2 ≤ 2*r^2:=by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
    rw [hsq]
    nlinarith [sq_nonneg r,mul_nonneg (sq_nonneg r) (show 0 ≤ 1-2*r^2 by nlinarith)]
  have hL:1 ≤ 1+Real.log ((n:ℝ)+2):=by
    linarith [Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])]
  have hC:=rangeFacetConstant_pos.le
  have hcoef:0 ≤ rangeFacetConstant^2*(1+Real.log ((n:ℝ)+2))+4*rangeFacetConstant:=by positivity
  have hh:=mul_le_mul_of_nonneg_left ht hcoef
  unfold dampingEta dampingSizeConstant
  nlinarith [mul_nonneg (show 0 ≤ 4*rangeFacetConstant*r^2 by positivity) (show 0 ≤ Real.log ((n:ℝ)+2) by linarith)]

end Scalar

/-- A common actual Gaussian damping lies below every divided pair coefficient.
The bound includes reference-score ties and uses no choice of winner. -/
theorem kappa_le_negativePairCoefficient {n d : ℕ} (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (R : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2) (x : FSC.Coord d)
    (i j : Fin (n+2)) (hij : i ≠ j) :
    kappa (dampingEta n r) (scoreOffsets R x) ≤ negativePairCoefficient R r x i j := by
  have hr1:r < 1:=by linarith
  have hQ:=rangeExponent_le_damping n r (scoreOffsets R x)
  have hb : -1-dampingEta n r*scoreEnergy (scoreOffsets R x) ≤
      -rangeExponent n ((r/Real.sqrt (1-r^2))*utilityRange (scoreOffsets R x)) := by linarith
  have hcoef:=negativePairCoefficient_range_bounds hn hmean R hG r hr hr1 x i j hij
  have hpre:=noise_prefactor_bounds r hr hrhalf
  apply (Real.exp_le_exp.mpr hb).trans
  exact (le_mul_of_one_le_left (Real.exp_nonneg _) hpre.1).trans hcoef.1

section PairAlgebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Pair-dependent divided coefficients are allowed. No fictitious common
additive perturbation or permanent/convexity surrogate is used. -/
theorem damped_pair_reward_lower (r κ k e c di dj ai aj : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hk : κ ≤ k)
    (he : 0 ≤ e) (hc : 0 ≤ c) (herr : |1-k| ≤ e) :
    -r*max ((κ⁻¹*(e*|di|+|ai|/r))+(κ⁻¹*(e*|dj|+|aj|/r))-c) 0 ≤
      r*k*c+r*(1-k)*(di-dj)+aj-ai := by
  let s:=κ⁻¹*(e*|di|+|ai|/r)+κ⁻¹*(e*|dj|+|aj|/r)
  have hs:0 ≤ s:=by dsimp [s];positivity
  have heq:r*κ*s=r*e*(|di|+|dj|)+|ai|+|aj|:=by
    dsimp [s]
    field_simp [hκ.ne',hr.ne']
    ring
  have he₁:|r*(1-k)*(di-dj)| ≤ r*e*(|di|+|dj|):=by
    rw [abs_mul,abs_mul,abs_of_pos hr]
    exact mul_le_mul (mul_le_mul_of_nonneg_left herr hr.le) (abs_sub di dj)
      (abs_nonneg _) (mul_nonneg hr.le he)
  have he₂:-(|aj|+|ai|) ≤ aj-ai:=by linarith [neg_le_abs aj,le_abs_self ai]
  have hbase:r*κ*(c-s) ≤ r*k*c+r*(1-k)*(di-dj)+aj-ai:=by
    have hk':r*κ*c ≤ r*k*c:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hr.le) hc
    nlinarith [neg_le_of_abs_le he₁]
  have hmax:κ*max (s-c) 0 ≤ max (s-c) 0:=mul_le_of_le_one_left (le_max_right _ _) hκ1
  have hlower:-r*max (s-c) 0 ≤ r*κ*(c-s):=by
    have hh:=mul_le_mul_of_nonneg_left (le_max_left (s-c) 0) (mul_nonneg hr.le hκ.le)
    nlinarith [mul_le_mul_of_nonneg_left hmax hr.le]
  exact hlower.trans hbase

end PairAlgebra


/-- The low-degree-corrected actual regular noise potential. Its omitted
constant is common to the labels and cancels in every routing difference. -/
def correctedRegularPotential {n d : ℕ}
    (R : Fin (n+2) → FSC.Coord d) (r : ℝ)
    (a : FSC.Coord d → Fin (n+2) → ℝ) (x : FSC.Coord d) (i : Fin (n+2)) : ℝ:=
  gaussianNoiseOperator (-r) (regularAssignment (fun k => (R k).ofLp)) x.ofLp i+
    r*referenceScale n*inner ℝ (R i) x+a x i

def pairForcing {n d : ℕ} (R D : Fin (n+2) → FSC.Coord d)
    (h : Fin (n+2) → ℝ) (r : ℝ) (a : FSC.Coord d → Fin (n+2) → ℝ)
    (x : FSC.Coord d) (i : Fin (n+2)) : ℝ:=
  inverseKappa (dampingEta n r) (scoreOffsets R x)*
    (smoothPairError n r (scoreOffsets R x)*|inner ℝ (D i) x+h i|+|a x i|/r)

/-- The actual fractional routing comparison is pointwise, so no winner
measurability premise and no tie deletion are used. The diagonal stays zero. -/
theorem fractional_routing_lower {n d : ℕ} (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (R D : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : Fin (n+2) → ℝ) (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2)
    (a : FSC.Coord d → Fin (n+2) → ℝ) (x : FSC.Coord d)
    (p : Fin (n+2) → ℝ) (hp : SimplexWeights p) :
    -r*closedCellCap (referenceScale n•R+D) h (pairForcing R D h r a) 1 x ≤
      ∑ j,p j*(r*(affineScore (referenceScale n•R+D) h
          (affineWinner (referenceScale n•R+D) h x) x-affineScore (referenceScale n•R+D) h j x)+
        correctedRegularPotential R r a x j-
        correctedRegularPotential R r a x (affineWinner (referenceScale n•R+D) h x)) := by
  let B:=referenceScale n•R+D
  let i:=affineWinner B h x
  let κ:=kappa (dampingEta n r) (scoreOffsets R x)
  let e:=smoothPairError n r (scoreOffsets R x)
  let cap:=closedCellCap B h (pairForcing R D h r a) 1 x
  have hr1:r < 1:=by linarith
  have hκ:0 < κ:=Real.exp_pos _
  have hη:=dampingEta_nonneg n r
  have hscore:0 ≤ scoreEnergy (scoreOffsets R x):=Finset.sum_nonneg fun j _ => sq_nonneg _
  have hκ1:κ ≤ 1:=by
    change Real.exp (-1-dampingEta n r*scoreEnergy (scoreOffsets R x)) ≤ 1
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hη hscore])
  have he:0 ≤ e:=smoothPairError_nonneg n r hr hr1 (scoreOffsets R x)
  have hcap:0 ≤ cap:=closedCellCap_nonneg B h _ 1 x
  have hpoint j:-r*cap ≤ r*(affineScore B h i x-affineScore B h j x)+
      correctedRegularPotential R r a x j-correctedRegularPotential R r a x i:=by
    by_cases hji:j=i
    · subst j
      simpa only [sub_self,mul_zero,zero_add,sub_self,neg_mul] using neg_nonpos.mpr (mul_nonneg hr.le hcap)
    have hij:i ≠ j:=Ne.symm hji
    let k:=negativePairCoefficient R r x i j
    have hk:κ ≤ k:=kappa_le_negativePairCoefficient hn hmean R hG r hr hrhalf x i j hij
    have herr:|1-k| ≤ e:=negativePairCoefficient_error_le hn hmean R hG r hr hrhalf x i j hij
    have hc:0 ≤ affineScore B h i x-affineScore B h j x:=sub_nonneg.mpr
      (affineWinner_mem_cell B h x j)
    have hlow:=damped_pair_reward_lower r κ k e
      (affineScore B h i x-affineScore B h j x)
      (inner ℝ (D i) x+h i) (inner ℝ (D j) x+h j) (a x i) (a x j)
      hr hκ hκ1 hk he hc herr
    have hreward:orderedReward (fun l => affineScore B h l x) (pairForcing R D h r a x) 1 i j ≤ cap:=by
      have hsup:=Finset.le_sup'
        (fun l => if l=i then 0 else orderedReward (fun k => affineScore B h k x)
          (pairForcing R D h r a x) 1 i l) (Finset.mem_univ j)
      have hs:orderedReward (fun l => affineScore B h l x) (pairForcing R D h r a x) 1 i j ≤
          switchingCap (fun l => affineScore B h l x) (pairForcing R D h r a x) 1 i:=by
        simpa only [hji,ite_false,switchingCap,maxScore] using hsup
      exact hs.trans (actualCap_le_closedCellCap B h _ 1 x)
    have hgap:=negativePairCoefficient_gap_identity R hG r hr hr1 x i j hij
    have hid:r*k*(affineScore B h i x-affineScore B h j x)+
        r*(1-k)*((inner ℝ (D i) x+h i)-(inner ℝ (D j) x+h j))+a x j-a x i=
        r*(affineScore B h i x-affineScore B h j x)+
          correctedRegularPotential R r a x j-correctedRegularPotential R r a x i:=by
      dsimp only [correctedRegularPotential,B,affineScore,Pi.add_apply,Pi.smul_apply]
      simp only [inner_add_left,real_inner_smul_left]
      simp only [inner_sub_left] at hgap
      dsimp only [k]
      nlinarith only [hgap]
    rw [hid] at hlow
    have hlow':-r*orderedReward (fun l => affineScore B h l x)
        (pairForcing R D h r a x) 1 i j ≤
        r*(affineScore B h i x-affineScore B h j x)+
          correctedRegularPotential R r a x j-correctedRegularPotential R r a x i:=by
      simpa only [orderedReward,one_mul,pairForcing,inverseKappa,κ,e] using hlow
    exact (mul_le_mul_of_nonpos_left hreward (neg_nonpos.mpr hr.le)).trans hlow'
  change -r*cap ≤ _
  calc
    _ = ∑ j,p j*(-r*cap):=by rw [←Finset.sum_mul,hp.2,one_mul]
    _ ≤ _:=Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpoint j) (hp.1 j)

/-- Exact identification with the forcing in the proved all-amplitude cap. -/
theorem pairForcing_eq_residualWeightedForcing {n d : ℕ}
    (R D : Fin (n+2) → FSC.Coord d) (h : Fin (n+2) → ℝ) (τ χ : ℝ)
    (p₀ p₁ : NegativeVotingFanScore.Parameters d (Fin (n+2)))
    (u : Fin (n+2) → FSC.Coord d → ℝ) :
    pairForcing R D h ((τ*χ)^2)
      (fun x i => NegativeVotingStructuredResidualInputs.actualResidual τ χ p₀ p₁ u i x)=
      NegativeVotingNearBalancedStructuredCap.residualWeightedForcing R D h
        (dampingEta n ((τ*χ)^2)) τ χ p₀ p₁ u := rfl

end NegativeVotingOwnCentroidRoutingCap
