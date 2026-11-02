import GaussianBalancedReference
import GaussianCovarianceRefinedCurvature

/-! The actual balanced covariance optimum, proved from the actual regular
centroid derivative and global covariance concavity. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingBalancedMaximum
open NegativeVoting NegativeVotingBalancedReference NegativeVotingCenteredParseval
  NegativeVotingCovarianceRealization NegativeVotingFan NegativeVotingFanScore
  NegativeVotingFanValue NegativeVotingFanInverse NegativeVotingFanValueDerivative
  NegativeVotingCapTail NegativeVotingFanCovarianceValue NegativeVotingCovarianceRefinement
  NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity NegativeVotingCovarianceStrict
  NegativeVotingFanCovarianceEnvelope NegativeVotingGaussianMaximum
  NegativeVotingGaussianMaximumMean NegativeVotingCentroidOptimization

variable {d n : ℕ}
def referenceCovariance (n d : ℕ) : FSC.Coord d →L[ℝ] FSC.Coord d :=
  (referenceScale n)^2 • ContinuousLinearMap.id ℝ (FSC.Coord d)

theorem referenceCovariance_positive (n d : ℕ) : referenceCovariance n d∈pdCone := by
  refine ⟨?_,?_⟩
  · intro x y
    change inner ℝ ((referenceScale n)^2 • x) y=inner ℝ x ((referenceScale n)^2 • y)
    simp only [real_inner_smul_left,real_inner_smul_right]
  · intro x hx
    change 0 < inner ℝ x ((referenceScale n)^2 • x)
    rw [real_inner_smul_right]
    exact mul_pos (sq_pos_of_pos (referenceScale_pos n)) (real_inner_self_pos.mpr hx)

theorem reference_mass (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    mass (fun i=>referenceScale n • B i) 0=uniformMass n := by
  funext i
  simp_rw [mass,scaled_weights_zero B (referenceScale n) (referenceScale_pos n)]
  exact congrFun (regular_fan_mass B hG) i

theorem reference_expectedMax (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    expectedMax (fun i=>referenceScale n • B i) 0=referenceScale n*maximumMean n := by
  unfold expectedMax
  have he (x : FSC.Coord d) :
      maxScore (scores (fun i=>referenceScale n • B i) 0 x)=
      referenceScale n*maxScore (scores B 0 x) := by
    change maxScore (fun i=>inner ℝ (referenceScale n • B i) x+0)=
      referenceScale n*maxScore (fun i=>inner ℝ (B i) x+0)
    simp only [add_zero,real_inner_smul_left]
    exact maxScore_mul_pos _ _ (referenceScale_pos n)
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  exact regular_fan_expectedMax B hG

theorem reference_optimizedValue (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    optimizedValue (fun i=>referenceScale n • B i) (uniformMass n)=
      referenceScale n*maximumMean n := by
  rw [optimizedValue_eq_of_mass _ _ (referenceScale n) (referenceScale_pos n)
    (scaled_centered_singular B hG _) (uniformMass_pos n) (uniformMass_sum n)
    (0 : centeredGauge (Fin (n+2))) (reference_mass B hG)]
  simp only [potential,Submodule.coe_zero,Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero]
  exact reference_expectedMax B hG

theorem scalar_factor_square (n d : ℕ) :
    (referenceScale n • ContinuousLinearMap.id ℝ (FSC.Coord d)).adjoint.comp
      (referenceScale n • ContinuousLinearMap.id ℝ (FSC.Coord d))=referenceCovariance n d := by
  have hs : (referenceScale n • ContinuousLinearMap.id ℝ (FSC.Coord d)).toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (referenceScale n • x) y=inner ℝ x (referenceScale n • y)
    simp only [real_inner_smul_left,real_inner_smul_right]
  rw [hs.clm_adjoint_eq]
  ext x
  simp [referenceCovariance,smul_smul,pow_two]

theorem reference_covariance_value
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    operatorValue b (uniformMass n) (referenceCovariance n d)=referenceFirstWeight n := by
  rw [←scalar_factor_square n d,operatorValue_factor]
  change optimizedValue (fun i=>referenceScale n • b i) (uniformMass n)=_
  rw [reference_optimizedValue b hG]
  unfold referenceScale referenceFirstWeight
  ring

theorem reference_covariance_trace
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x) :
    LinearMap.trace ℝ (FSC.Coord d) (referenceCovariance n d).toLinearMap=referenceFirstWeight n := by
  rw [←scalar_factor_square n d,parseval_square_trace b hP]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs,←Finset.mul_sum]
  have hG' : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  rw [regularGram_row_energy b hG']
  simp only [referenceScale,referenceFirstWeight,Nat.cast_add,Nat.cast_ofNat]
  have hn1 : (n:ℝ)+1≠0 := by positivity
  field_simp
  ring

theorem reference_penalized_value
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x) :
    penalizedValue b (uniformMass n) (referenceCovariance n d)=referenceFirstWeight n := by
  rw [penalizedValue,reference_covariance_value b hG,reference_covariance_trace b hG hP]
  ring

/-- Actual derivative at the regular scalar covariance in every symmetric
operator direction. The coefficient is the literal operator trace. -/
theorem reference_covariance_derivative (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (D : FSC.Coord d →L[ℝ] FSC.Coord d) (hD : D.toLinearMap.IsSymmetric) :
    HasDerivAt (fun t : ℝ=>operatorValue b (uniformMass n) (referenceCovariance n d+t • D))
      (LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap/2) 0 := by
  let a := referenceScale n
  let B : Fin (n+2) → FSC.Coord d := fun i=>a • b i
  let H : FSC.Coord d →L[ℝ] FSC.Coord d := (a^2)⁻¹ • D
  have ha : a≠0 := ne_of_gt (referenceScale_pos n)
  have hH : H.toLinearMap.IsSymmetric :=
    hD.smul (by rfl : starRingEnd ℝ ((a^2)⁻¹)=(a^2)⁻¹)
  have hlower : CenteredSingularLowerBound B a := scaled_centered_singular b hG a
  have hm : mass B (0 : centeredGauge (Fin (n+2)))=uniformMass n := reference_mass b hG
  have hd := hasDerivAt_intrinsic_covariance_value B (uniformMass n) a (referenceScale_pos n)
    hlower (uniformMass_pos n) (uniformMass_sum n) 0 hm H hH
  simp only [Submodule.coe_zero] at hd
  rw [←covariance_first_derivative_value B 0 a (referenceScale_pos n) hlower H] at hd
  have hv : rowDerivative B 0 (rowsOfOperator B ((1/2:ℝ) • H))=
      LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap/2 := by
    rw [rowDerivative_apply,parseval_trace b hP]
    simp only [rowsOfOperator_apply,B,H,a,ContinuousLinearMap.smul_apply,map_smul,Pi.smul_apply,
      scaled_regular_self_centroid hn b hG,real_inner_smul_left,real_inner_smul_right]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (b i) (D (b i))]
    field_simp [ne_of_gt (referenceScale_pos n)]
  have hg : Matrix.gram ℝ B=gramVelocity b (referenceCovariance n d) := by
    ext i j
    simp only [Matrix.gram_apply,B,gramVelocity,referenceCovariance,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,real_inner_smul_left,real_inner_smul_right,a]
    ring
  have hvel : gramVelocity B H=gramVelocity b D := by
    ext i j
    simp only [gramVelocity,B,H,ContinuousLinearMap.smul_apply,map_smul,
      real_inner_smul_left,real_inner_smul_right]
    field_simp [ha]
  have he : (fun t : ℝ=>operatorValue b (uniformMass n) (referenceCovariance n d+t • D))=
      (fun t : ℝ=>covarianceValue (Matrix.gram ℝ B+t • gramVelocity B H) (uniformMass n)) := by
    funext t
    unfold operatorValue
    rw [gramVelocity_add_smul,←hg,←hvel]
  rw [he]
  rwa [hv] at hd

/-- The actual balanced penalized objective has zero first derivative at the
reference scalar covariance, without any assumed optimality condition. -/
theorem reference_penalized_derivative (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (D : FSC.Coord d →L[ℝ] FSC.Coord d) (hD : D.toLinearMap.IsSymmetric) :
    HasDerivAt (fun t : ℝ=>penalizedValue b (uniformMass n) (referenceCovariance n d+t • D)) 0 0 := by
  have hd := reference_covariance_derivative hn b hG hP D hD
  have ht : HasDerivAt (fun t : ℝ=>LinearMap.trace ℝ (FSC.Coord d)
      (referenceCovariance n d+t • D).toLinearMap)
      (LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap) 0 := by
    have he (t : ℝ) : LinearMap.trace ℝ (FSC.Coord d) (referenceCovariance n d+t • D).toLinearMap=
        LinearMap.trace ℝ (FSC.Coord d) (referenceCovariance n d).toLinearMap+
          t*LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap := by
      change LinearMap.trace ℝ (FSC.Coord d)
        ((referenceCovariance n d).toLinearMap+t • D.toLinearMap)=_
      simp only [map_add,map_smul,smul_eq_mul]
    have heq := funext he
    rw [heq]
    simpa only [one_mul,id_eq] using ((hasDerivAt_id (0:ℝ)).mul_const
      (LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap)).const_add
      (LinearMap.trace ℝ (FSC.Coord d) (referenceCovariance n d).toLinearMap)
  have hh := (hd.const_mul 2).sub ht
  have he : 2*(LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap/2)-
      LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap=0 := by ring
  rw [he] at hh
  exact hh

theorem penalized_concaveOn_psd
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (p : Fin (n+2) → ℝ)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ConcaveOn ℝ psdCone (penalizedValue b p) := by
  refine ⟨psdCone_convex,?_⟩
  intro C hC D hD a c ha hc hac
  have hh := (operatorValue_concaveOn_psd b p hp hs).2 hC hD ha hc hac
  have htr : LinearMap.trace ℝ (FSC.Coord d) (a • C+c • D).toLinearMap=
      a*LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap+
      c*LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap := by
    change LinearMap.trace ℝ (FSC.Coord d) (a • C.toLinearMap+c • D.toLinearMap)=_
    simp only [map_add,map_smul,smul_eq_mul]
  simp only [penalizedValue,htr,smul_eq_mul] at hh ⊢
  nlinarith

/-- The proved zero derivative is a supporting tangent for the actual global
PSD covariance objective, including every singular competitor. -/
theorem balanced_reference_isMaxOn (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x) :
    IsMaxOn (penalizedValue b (uniformMass n)) psdCone (referenceCovariance n d) := by
  intro C hC
  have hC₀ := pdCone_subset_psdCone (referenceCovariance_positive n d)
  let L : ℝ →ᵃ[ℝ] (FSC.Coord d →L[ℝ] FSC.Coord d) := AffineMap.lineMap (referenceCovariance n d) C
  have hcon := (penalized_concaveOn_psd b (uniformMass n)
    (uniformMass_pos n) (uniformMass_sum n)).comp_affineMap L
  have hsub : Icc (0:ℝ) 1⊆L ⁻¹' psdCone := by
    intro t ht
    change AffineMap.lineMap (referenceCovariance n d) C t∈psdCone
    rw [AffineMap.lineMap_apply_module]
    exact psdCone_convex hC₀ hC (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hl := hcon.subset hsub (convex_Icc (0:ℝ) 1)
  have he : (penalizedValue b (uniformMass n) ∘ L)=
      (fun t : ℝ=>penalizedValue b (uniformMass n)
        (referenceCovariance n d+t • (C-referenceCovariance n d))) := by
    funext t
    simp only [Function.comp_apply,L,AffineMap.lineMap_apply_module',add_comm]
  rw [he] at hl
  have hd := reference_penalized_derivative hn b hG hP (C-referenceCovariance n d)
    (hC.1.sub hC₀.1)
  have hh := hl.slope_le_of_hasDerivAt (by norm_num) (by norm_num) (by norm_num : (0:ℝ)<1) hd
  simp only [slope_def_field,sub_zero,one_smul,zero_smul,add_zero,add_sub_cancel_left,div_one] at hh
  have hz : referenceCovariance n d+(0:ℝ) • (C-referenceCovariance n d)=referenceCovariance n d := by module
  have ho : referenceCovariance n d+(C-referenceCovariance n d)=C := by module
  rw [hz,ho] at hh
  change penalizedValue b (uniformMass n) C ≤ penalizedValue b (uniformMass n) (referenceCovariance n d)
  exact sub_nonpos.mp hh

/-- Exact balanced maximum: the actual iid Gaussian maximum mean fixes the
scalar covariance and the optimum mu^2/(m-1), with no balanced-max premise. -/
theorem balanced_covariance_value_le (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈psdCone) :
    penalizedValue b (uniformMass n) C ≤ referenceFirstWeight n := by
  have hh := balanced_reference_isMaxOn hn b hG hP hC
  simpa only [Set.mem_setOf_eq,reference_penalized_value b hG hP] using hh

theorem balanced_covariance_maximum (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x) :
    IsGreatest {v : ℝ | ∃ C : FSC.Coord d →L[ℝ] FSC.Coord d,
      C∈psdCone ∧ v=penalizedValue b (uniformMass n) C} (referenceFirstWeight n) := by
  refine ⟨⟨referenceCovariance n d,pdCone_subset_psdCone (referenceCovariance_positive n d),
    (reference_penalized_value b hG hP).symm⟩,?_⟩
  rintro v ⟨C,hC,rfl⟩
  exact balanced_covariance_value_le hn b hG hP C hC

/-- The same exact balanced bound holds for actual completed-measurable
fractional Gaussian assignments in every finite ambient dimension. -/
theorem balanced_centroidEnergy_le_reference (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (e : ℕ) (g : FSC.Coord e → Fin (n+2) → ℝ)
    (hg : NegativeVotingAssignmentDuality.Feasible (uniformMass n) g) :
    centroidEnergy g ≤ referenceFirstWeight n := by
  have hG' : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hbound := centroidEnergy_le_covariance_maximum b hG' hP (uniformMass n)
    (referenceCovariance n d) (fun C hC=>balanced_reference_isMaxOn hn b hG hP hC) g hg
  simpa only [reference_penalized_value b hG hP] using hbound

end NegativeVotingBalancedMaximum
