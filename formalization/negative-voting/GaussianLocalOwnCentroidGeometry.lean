import GaussianOwnCentroidPrimalGap
import GaussianLocalOrbitDeficitPayment
import GaussianCompetitiveTightMassWindow

/-! Actual local own-centroid parameters with every geometric and mass
condition needed by the structured replacement derived from the local branch. -/
noncomputable section
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingLocalOwnCentroidGeometry
open NegativeVoting NegativeVotingAffine NegativeVotingModern
  NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanSelectedOffsets
  NegativeVotingAssignmentCoordinateBridge NegativeVotingAssignmentDuality
  NegativeVotingCentroidOptimization NegativeVotingFractionalMass
  NegativeVotingOwnCentroidPrimalGap NegativeVotingLocalOrbitDeficitPayment
  NegativeVotingBalancedReference NegativeVotingRegularCovarianceDeficit
  NegativeVotingProcrustes NegativeVotingGlobalCovarianceDeficit
  NegativeVotingExteriorRoutingGeometry NegativeVotingExteriorReference
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximum
  NegativeVotingGaussianMaximumSecondMoment NegativeVotingRegularSecondGap

structure LocalOwnCentroidData (n d : ℕ) (f : (Fin d→ℝ)→Fin (n+2)→ℝ) where
  R : Fin (n+2)→FSC.Coord d
  D : Fin (n+2)→FSC.Coord d
  v : centeredGauge (Fin (n+2))
  regular : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)
  rows : referenceScale n•R+D=centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)
  rowSmall : (∑i,‖D i‖^2) ≤ (referenceScale n)^2/256
  rowAbsolute : (∑i,‖D i‖^2) ≤ 4/((n:ℝ)+2)^2
  rowPaid : (∑i,‖D i‖^2) ≤ (96/globalRadius)*((n:ℝ)+2)*(1+Real.log ((n:ℝ)+2))*
    regularCovarianceDeficit n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f))
  massBound : ∀i,|(v:Fin (n+2)→ℝ) i| ≤ 1/(2*((n:ℝ)+2))
  masses : assignmentMass f=(fun _=>((n:ℝ)+2)⁻¹)+(v:Fin (n+2)→ℝ)
  massEnergy : (∑i,((v:Fin (n+2)→ℝ) i)^2)=massDeficit n f
  size : (∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)→ℝ) i)^2) ≤ 5/((n:ℝ)+2)
  scaleLower : (1/2:ℝ)*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) ≤ referenceScale n/2
  scaleUpper : referenceScale n ≤ 10*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)
  meanLower : 1 ≤ maximumMean n

theorem eventually_local_own_centroid_data :
    ∀ᶠ n:ℕ in atTop,∀d:ℕ,n+1 ≤ d →
      ∀f:(Fin d→ℝ)→Fin (n+2)→ℝ,
      (∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d))) →
      (∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) →
      0<regularCovarianceDeficit n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)) →
      regularOrbitDistance n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)) ≤ 1/((n:ℝ)+2) →
      (∀i,assignmentMass f i∈Icc (1/(2*((n:ℝ)+2))) (3/(2*((n:ℝ)+2)))) →
      Nonempty (LocalOwnCentroidData n d f) := by
  filter_upwards [eventually_exists_local_paid_reference,eventually_reference_scale_bounds,
    eventually_maximum_mean_sq_ge_one,
    (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 1024,
    eventually_ge_atTop (1:ℕ)] with n hpay hscale hmean hlog hn
  intro d hd f hf hp hpos hlocal hmass
  let B:=centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)
  have hfeas:=coordinateRule_feasible (LinearIsometryEquiv.refl ℝ _) f hf hp
  have hc:(∑i,B i)=0:=centroidRows_sum_zero _ _ hfeas
  obtain ⟨U,hU,habs,hpaid⟩:=hpay d hd B hc hpos hlocal
  let R:Fin (n+2)→FSC.Coord d:=(referenceScale n)⁻¹•U
  let D:Fin (n+2)→FSC.Coord d:=B-U
  let v:centeredGauge (Fin (n+2)):=⟨fun i=>assignmentMass f i-1/((n:ℝ)+2),mass_deviations_sum n f hf hp⟩
  let m:ℝ:=(n:ℝ)+2
  let L:ℝ:=1+Real.log m
  have hm:1 ≤ m:=by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hm0:0 < m:=by linarith
  have hL:1024 ≤ L:=by dsimp [Function.comp_def] at hlog;dsimp [L,m];linarith
  have hL0:0 ≤ L:=by linarith
  have hα:0<referenceScale n:=referenceScale_pos n
  have hR:∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2):=by
    simpa only [R,Nat.cast_add,Nat.cast_ofNat] using scaled_regular_normalized_gram U hU
  have heq:referenceScale n•R+D=B:=by
    dsimp [R,D]
    rw [smul_smul,mul_inv_cancel₀ hα.ne',one_smul]
    abel
  have hDabs:(∑i,‖D i‖^2) ≤ 4/m^2:=habs
  have hDsmall:(∑i,‖D i‖^2) ≤ (referenceScale n)^2/256:=by
    calc
      _ ≤ 4/m^2:=hDabs
      _ = (1024/m^2)/256:=by ring
      _ ≤ (L/m^2)/256:=by gcongr
      _ ≤ _:=div_le_div_of_nonneg_right hscale.1 (by norm_num)
  have hv:∀i,|(v:Fin (n+2)→ℝ) i| ≤ 1/(2*m):=by
    intro i
    have hi:=hmass i
    change |assignmentMass f i-1/m| ≤ 1/(2*m)
    rw [abs_le]
    have he:1/m=2*(1/(2*m)):=by field_simp
    have he3:3/(2*m)=3*(1/(2*m)):=by ring
    change 1/(2*m) ≤ assignmentMass f i ∧ assignmentMass f i ≤ 3/(2*m) at hi
    rw [he3] at hi
    rw [he]
    constructor <;>linarith
  have hv2:(∑i,((v:Fin (n+2)→ℝ) i)^2) ≤ 1/(4*m):=by
    have ht:(∑i,((v:Fin (n+2)→ℝ) i)^2) ≤ ∑i:Fin (n+2),(1/(2*m))^2:=by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
    apply ht.trans_eq
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
    change m*(1/(2*m))^2=1/(4*m)
    field_simp
    ring
  have hsize:(∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)→ℝ) i)^2) ≤ 5/m:=by
    have hh:4/m^2 ≤ 4/m:=by
      apply div_le_div_of_nonneg_left (by norm_num) hm0
      nlinarith
    have hz:1/(4*m) ≤ 1/m:=by
      apply div_le_div_of_nonneg_left (by norm_num) hm0
      nlinarith
    have he:4/m+1/m=5/m:=by ring
    linarith
  have hlo:Real.sqrt L/m ≤ referenceScale n:=by
    apply (sq_le_sq₀ (by positivity) hα.le).mp
    rw [div_pow,Real.sq_sqrt hL0]
    exact hscale.1
  have hup:referenceScale n ≤ 10*Real.sqrt L/m:=by
    apply (sq_le_sq₀ hα.le (by positivity)).mp
    rw [div_pow,mul_pow,Real.sq_sqrt hL0]
    have hh:20*L/m^2 ≤ 10^2*L/m^2:=by gcongr;norm_num
    exact hscale.2.trans hh
  refine ⟨⟨R,D,v,hR,heq,hDsmall,hDabs,hpaid,hv,?_,rfl,hsize,?_,hup,?_⟩⟩
  · funext i
    change assignmentMass f i=((n:ℝ)+2)⁻¹+(assignmentMass f i-1/((n:ℝ)+2))
    rw [one_div]
    ring
  · change (1/2:ℝ)*Real.sqrt L/m ≤ referenceScale n/2
    convert mul_le_mul_of_nonneg_left hlo (by norm_num : (0:ℝ)≤1/2) using 1 <;>ring
  · exact (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1) (maximumMean_pos n).le).mp (by simpa using hmean)

end NegativeVotingLocalOwnCentroidGeometry
