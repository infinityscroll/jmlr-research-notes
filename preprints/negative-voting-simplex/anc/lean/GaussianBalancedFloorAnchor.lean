import GaussianBalancedCovarianceMaximum
import GaussianCovarianceMassPath

/-! The balanced anchor for the actual positive-floor mass-value profile. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Asymptotics
open scoped Topology BigOperators RealInnerProductSpace

namespace NegativeVotingBalancedFloorAnchor
open NegativeVotingBalancedReference NegativeVotingBalancedMaximum
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceOptimizerContinuity
  NegativeVotingCovarianceOptimizerLipschitz NegativeVotingCovarianceMassPath
  NegativeVotingPositiveCovariance NegativeVotingCovarianceStrict
  NegativeVotingCovarianceBoundary NegativeVotingCovarianceRealization
  NegativeVotingLocalCovarianceFactor NegativeVotingFanInverse
  NegativeVotingCovarianceOffsets NegativeVotingFanSelectedOffsets

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zero_gradient_of_axis_derivatives (F : E×ℝ → ℝ) (x : E)
    (hF : DifferentiableAt ℝ F (x,0))
    (hstate : ∀ D : E, HasDerivAt (fun t : ℝ => F (x+t • D,0)) 0 0)
    (htime : HasDerivAt (fun t : ℝ => F (x,t)) 0 0) :
    HasFDerivAt F (0 : E×ℝ →L[ℝ] ℝ) (x,0) := by
  let L := fderiv ℝ F (x,0)
  have hd : HasFDerivAt F L (x,0) := hF.hasFDerivAt
  have hs (D : E) : L (D,0) = 0 := by
    have hl : HasDerivAt (fun t : ℝ => (x+t • D,(0:ℝ))) (D,0) 0 := by
      simpa only [one_smul,zero_add,Pi.add_apply,id_eq] using
        ((hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const D)).prodMk
          (hasDerivAt_const (0:ℝ) (0:ℝ))
    have hd' : HasFDerivAt F L (x+(0:ℝ) • D,0) := by
      simpa only [zero_smul,add_zero] using hd
    have hh : HasDerivAt (fun t : ℝ => F (x+t • D,0)) (L (D,0)) 0 :=
      hd'.comp_hasDerivAt (f:=fun t : ℝ => (x+t • D,(0:ℝ))) 0 hl
    exact hh.unique (hstate D)
  have ht : L (0,1) = 0 := by
    have hl : HasDerivAt (fun t : ℝ => (x,t)) (0,1) 0 :=
      (hasDerivAt_const (0:ℝ) x).prodMk (hasDerivAt_id (0:ℝ))
    exact (hd.comp_hasDerivAt 0 hl).unique htime
  have hL : L = 0 := by
    apply ContinuousLinearMap.ext
    intro z
    rcases z with ⟨D,a⟩
    have he : (D,a) = (D,(0:ℝ))+a • ((0:E),(1:ℝ)) := by ext <;> simp
    rw [he,map_add,map_smul,hs,ht]
    simp
  rw [hL] at hd
  exact hd

theorem zero_derivative_of_zero_gradient_comp (F : E → ℝ) (g : ℝ → E)
    (hF : HasFDerivAt F (0 : E →L[ℝ] ℝ) (g 0)) (hg : ContinuousAt g 0)
    (hO : (fun t : ℝ => g t-g 0) =O[𝓝 0] (fun t : ℝ => t)) :
    HasDerivAt (fun t : ℝ => F (g t)) 0 0 := by
  have hsmall : (fun x : E => F x-F (g 0)) =o[𝓝 (g 0)] (fun x : E => x-g 0) := by
    simpa only [ContinuousLinearMap.zero_apply,sub_zero] using hF.isLittleO
  have hh := (hsmall.comp_tendsto hg.tendsto).trans_isBigO hO
  apply HasDerivAt.of_isLittleO
  simpa only [Function.comp_def,smul_zero,sub_zero] using hh

end Calculus

section SelectedPath
variable {m d : ℕ} [NeZero m]

def selectedJointPath (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε : ℝ) (hε : 0 < ε) (p : PositiveProbability m)
    (v : centeredGauge (Fin m)) (t : ℝ) : SymmetricOperators (FSC.Coord d)×ℝ :=
  (selectedOperator b ε hε (probabilityChart p (t • v)),t)

theorem selectedJointPath_continuousAt (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε : ℝ) (hε : 0 < ε) (p : PositiveProbability m) (v : centeredGauge (Fin m)) :
    ContinuousAt (selectedJointPath b ε hε p v) 0 := by
  have hl : ContinuousAt (fun t : ℝ => t • v) 0 := by fun_prop
  have hb : ContinuousAt (probabilityChart p) ((0:ℝ) • v) := by
    simpa only [zero_smul] using probabilityChart_continuousAt p
  have hchart : ContinuousAt (fun t : ℝ => probabilityChart p (t • v)) 0 :=
    hb.comp (f:=fun t : ℝ => t • v) hl
  exact ((selectedOperator_continuous b ε hε).continuousAt.comp hchart).prodMk continuousAt_id

theorem selectedJointPath_isBigO (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (ε : ℝ) (hε : 0 < ε) (p : PositiveProbability m) (v : centeredGauge (Fin m)) :
    (fun t : ℝ => selectedJointPath b ε hε p v t-selectedJointPath b ε hε p v 0)
      =O[𝓝 0] (fun t : ℝ => t) := by
  obtain ⟨K,T,hT,hLip⟩ := selectedOperator_chart_lipschitz b ε hε p
  have h0T : (0 : centeredGauge (Fin m)) ∈ T := mem_of_mem_nhds hT
  have hl : ContinuousAt (fun t : ℝ => t • v) 0 := by fun_prop
  have hT' : T ∈ 𝓝 ((0:ℝ) • v) := by simpa only [zero_smul] using hT
  have ht : ∀ᶠ t : ℝ in 𝓝 0, t • v ∈ T := hl.eventually hT'
  apply IsBigO.of_bound ((K:ℝ)*‖v‖+1)
  filter_upwards [ht] with t ht
  have hc := hLip.dist_le_mul (t • v) ht 0 h0T
  simp only [dist_eq_norm,sub_zero,norm_smul,Real.norm_eq_abs] at hc
  change ‖(selectedOperator b ε hε (probabilityChart p (t • v)),t)-
    (selectedOperator b ε hε (probabilityChart p ((0:ℝ) • v)),0)‖ ≤ _
  simp only [zero_smul,Prod.mk_sub_mk,sub_zero,Prod.norm_mk,Real.norm_eq_abs]
  apply max_le
  · nlinarith [abs_nonneg t]
  · have hkv : 0 ≤ (K:ℝ)*‖v‖ := mul_nonneg K.property (norm_nonneg _)
    nlinarith [mul_nonneg hkv (abs_nonneg t)]

end SelectedPath

variable {n d : ℕ}

def balancedProbability (n : ℕ) : PositiveProbability (n+2) :=
  ⟨uniformMass n,uniformMass_pos n,uniformMass_sum n⟩

def referenceOperator (n d : ℕ) : SymmetricOperators (FSC.Coord d) :=
  ⟨referenceCovariance n d,ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (referenceCovariance_positive n d).1⟩

theorem probabilityChart_zero {m : ℕ} [NeZero m] (p : PositiveProbability m) :
    probabilityChart p 0 = p := by
  apply Subtype.ext
  rw [probabilityChart_coe p 0 (by simpa using p.property.1)]
  simp

theorem reference_mem_lowerCone (ε : ℝ) (hε : ε ≤ (referenceScale n)^2) :
    referenceCovariance n d ∈ lowerCovarianceCone ε := by
  change referenceCovariance n d-ε • ContinuousLinearMap.id ℝ (FSC.Coord d) ∈ psdCone
  have he : referenceCovariance n d-ε • ContinuousLinearMap.id ℝ (FSC.Coord d) =
      ((referenceScale n)^2-ε) • ContinuousLinearMap.id ℝ (FSC.Coord d) := by
    unfold referenceCovariance
    module
  rw [he]
  refine ⟨LinearMap.IsSymmetric.smul (by rfl) (fun x y => rfl),fun x => ?_⟩
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right]
  exact mul_nonneg (sub_nonneg.mpr hε) real_inner_self_nonneg

theorem selectedCovariance_balanced (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (ε : ℝ) (hε : 0 < ε) (hεa : ε < (referenceScale n)^2) :
    (selectedCovariance b ε hε (balancedProbability n) : FSC.Coord d →L[ℝ] FSC.Coord d) =
      referenceCovariance n d := by
  have hu := exists_unique_penalized_maximizer b (uniformMass n)
    (uniformMass_pos n) (uniformMass_sum n) hε
  apply hu.unique
  · exact ⟨(selectedCovariance b ε hε (balancedProbability n)).property.1,
      selectedCovariance_isMaxOn b ε hε (balancedProbability n)⟩
  · refine ⟨reference_mem_lowerCone ε hεa.le,?_⟩
    intro C hC
    exact balanced_reference_isMaxOn hn b hG hP
      (lowerCovarianceCone_subset_psd hε.le hC)

theorem selectedOperator_balanced (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (ε : ℝ) (hε : 0 < ε) (hεa : ε < (referenceScale n)^2) :
    selectedOperator b ε hε (balancedProbability n)=referenceOperator n d :=
  Subtype.ext (selectedCovariance_balanced hn b hG hP ε hε hεa)

theorem selected_balanced_value (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (ε : ℝ) (hε : 0 < ε) (hεa : ε < (referenceScale n)^2) :
    penalizedValue b (uniformMass n) (selectedCovariance b ε hε (balancedProbability n)) =
      NegativeVotingGaussianMaximumMean.referenceFirstWeight n := by
  rw [selectedCovariance_balanced hn b hG hP ε hε hεa]
  exact reference_penalized_value b hG hP

theorem reference_offsets_zero
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    operatorOffsets b (uniformMass n) (referenceCovariance n d)=0 := by
  let B : Fin (n+2) → FSC.Coord d := fun i => referenceScale n • b i
  have hl := scaled_centered_singular b hG (referenceScale n)
  have hg := adjoint_factor_gram (b : Fin (n+2) → FSC.Coord d)
    (referenceScale n • ContinuousLinearMap.id ℝ (FSC.Coord d))
  rw [scalar_factor_square] at hg
  change _ = Matrix.gram ℝ B at hg
  unfold operatorOffsets
  rw [hg,covarianceOffsets_gram B (referenceScale n) (referenceScale_pos n) hl
    (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)]
  exact selectedOffsets_eq B (uniformMass n) (referenceScale n) (referenceScale_pos n)
    hl 0 (reference_mass b hG)

theorem reference_path_gradient_zero (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (v : centeredGauge (Fin (n+2))) :
    HasFDerivAt (pathObjective b (uniformMass n) v)
      (0 : SymmetricOperators (FSC.Coord d)×ℝ →L[ℝ] ℝ) (referenceOperator n d,0) := by
  have hp : ∀ i,0<(uniformMass n+(0:ℝ) • (v:Fin (n+2)→ℝ)) i := by
    simpa only [zero_smul,add_zero] using uniformMass_pos n
  have hC : (referenceOperator n d : FSC.Coord d →L[ℝ] FSC.Coord d) ∈ pdCone :=
    referenceCovariance_positive n d
  apply zero_gradient_of_axis_derivatives
    (pathObjective b (uniformMass n) v) (referenceOperator n d)
    ((pathObjective_C2 b (uniformMass n) (uniformMass_sum n) v
      (referenceOperator n d) 0 hp hC).differentiableAt (by norm_num))
  · intro D
    have hh := reference_penalized_derivative hn b hG hP D
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp D.property)
    simpa only [pathObjective,pathValue,zero_smul,add_zero,Submodule.coe_add,
      Submodule.coe_smul,referenceOperator,penalizedValue,
      NegativeVotingCovarianceCoercivity.operatorTrace] using hh
  · have hh := path_time_derivative b (uniformMass n) (uniformMass_sum n) v
      (referenceOperator n d) 0 hp hC
    simpa only [zero_smul,add_zero,referenceOperator,reference_offsets_zero b hG,
      Submodule.coe_zero,Pi.zero_apply,zero_mul,Finset.sum_const_zero,mul_zero] using hh

theorem selected_balanced_path_derivative_zero (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (ε : ℝ) (hε : 0 < ε) (hεa : ε < (referenceScale n)^2)
    (v : centeredGauge (Fin (n+2))) :
    HasDerivAt (fun t : ℝ => penalizedValue b
      (probabilityChart (balancedProbability n) (t • v))
      (selectedCovariance b ε hε (probabilityChart (balancedProbability n) (t • v)))) 0 0 := by
  let p := balancedProbability n
  let g := selectedJointPath b ε hε p v
  have hg0 : g 0 = (referenceOperator n d,0) := by
    simp only [g,selectedJointPath,zero_smul,probabilityChart_zero,p,
      selectedOperator_balanced hn b hG hP ε hε hεa]
  have hF : HasFDerivAt (pathObjective b (uniformMass n) v)
      (0 : SymmetricOperators (FSC.Coord d)×ℝ →L[ℝ] ℝ) (g 0) := by
    rw [hg0]
    exact reference_path_gradient_zero hn b hG hP v
  have hh := zero_derivative_of_zero_gradient_comp (pathObjective b (uniformMass n) v) g hF
    (selectedJointPath_continuousAt b ε hε p v) (selectedJointPath_isBigO b ε hε p v)
  have hl : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t • v) 0 := by fun_prop
    simpa only [zero_smul] using hc.tendsto
  have he : (fun t : ℝ => penalizedValue b (probabilityChart p (t • v))
      (selectedCovariance b ε hε (probabilityChart p (t • v)))) =ᶠ[𝓝 0]
      (fun t : ℝ => pathObjective b (uniformMass n) v (g t)) := by
    filter_upwards [hl.eventually (eventually_positive_chart p)] with t ht
    have hc := probabilityChart_coe p (t • v) ht
    change penalizedValue b (probabilityChart p (t • v))
      (selectedCovariance b ε hε (probabilityChart p (t • v))) =
      penalizedValue b (uniformMass n+t • (v:Fin (n+2)→ℝ))
      (selectedCovariance b ε hε (probabilityChart p (t • v)))
    rw [hc]
    rfl
  exact hh.congr_of_eventuallyEq he

end NegativeVotingBalancedFloorAnchor
