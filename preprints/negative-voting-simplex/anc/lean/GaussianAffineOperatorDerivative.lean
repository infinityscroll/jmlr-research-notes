import GaussianAffineCapDerivative
import GaussianCenteredParsevalBasis

/-! The actual Gaussian derivative under an arbitrary linear-plus-translation
motion, assembled from proved rank-one moving-cap derivatives. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory WeakSimplex Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingAffineOperatorDerivative
open NegativeVotingAffineCapDerivative NegativeVotingMovingCap NegativeVotingFanScore
  NegativeVotingCenteredParseval
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def affineVelocity (w : ι → FSC.Coord d) (A : FSC.Coord d →L[ℝ] FSC.Coord d)
    (z : FSC.Coord d) : Parameters d ι :=
  (fun j=>A.adjoint (w j),fun j=>-inner ℝ (w j) z)

theorem affineVelocity_decomposition (w : ι → FSC.Coord d)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    affineVelocity w A z=
      (∑ a : Fin d,affineRankOneVelocity w
        (A (EuclideanSpace.basisFun (Fin d) ℝ a)) (EuclideanSpace.basisFun (Fin d) ℝ a) 0)+
          affineRankOneVelocity w 0 0 z := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  apply Prod.ext
  · funext j
    simp only [affineVelocity,affineRankOneVelocity,Prod.fst_add,Prod.fst_sum,
      Finset.sum_apply,Pi.add_apply,inner_zero_left,inner_zero_right,zero_smul,add_zero]
    have hh := e.sum_repr' (A.adjoint (w j))
    simp_rw [ContinuousLinearMap.adjoint_inner_right] at hh
    simpa only [real_inner_comm] using hh.symm
  · funext j
    simp [affineVelocity,affineRankOneVelocity,Prod.snd_sum,Finset.sum_apply]

theorem basis_quadratic_sum (A : FSC.Coord d →L[ℝ] FSC.Coord d) (x : FSC.Coord d) :
    (∑ a : Fin d,inner ℝ (A (EuclideanSpace.basisFun (Fin d) ℝ a)) x*
      inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ a) x)=inner ℝ x (A x) := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hh := congrArg (fun y : FSC.Coord d=>inner ℝ y x) (congrArg A (e.sum_repr' x))
  simp only [map_sum,map_smul,sum_inner,real_inner_smul_left] at hh
  simpa only [mul_comm,real_inner_comm (A x) x] using hh

theorem basis_trace_sum (A : FSC.Coord d →L[ℝ] FSC.Coord d) :
    (∑ a : Fin d,inner ℝ (A (EuclideanSpace.basisFun (Fin d) ℝ a))
      (EuclideanSpace.basisFun (Fin d) ℝ a))=LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hA : A.toLinearMap=∑ a : Fin d,(innerSL ℝ (e a)).toLinearMap.smulRight (A (e a)) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.sum_apply,LinearMap.smulRight_apply,ContinuousLinearMap.coe_coe]
    change A x=∑ a : Fin d,inner ℝ (e a) x • A (e a)
    have hh := congrArg A (e.sum_repr' x)
    simpa only [map_sum,map_smul] using hh.symm
  symm
  rw [hA,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [LinearMap.trace_smulRight]
  exact real_inner_comm (A (e a)) (e a)

theorem bilinear_integrable (s : Set (FSC.Coord d)) (u v : FSC.Coord d) :
    Integrable (fun x : FSC.Coord d=>inner ℝ u x*inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict s) :=
  ((IsGaussian.memLp_two_id.const_inner (𝕜:=ℝ) u).integrable_mul
    (IsGaussian.memLp_two_id.const_inner (𝕜:=ℝ) v)).restrict

theorem capJointDerivative_affine (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    capJointDerivative w b (fun _=>1) (affineVelocity w A z)=
      (∫ x in FSC.cap w b,inner ℝ x (A x) ∂stdGaussian (FSC.Coord d))-
        FSC.capMass w b*LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap+
        (∫ x in FSC.cap w b,inner ℝ z x ∂stdGaussian (FSC.Coord d)) := by
  rw [affineVelocity_decomposition,map_add,map_sum]
  simp_rw [capJointDerivative_rankOne w hw b hb]
  simp only [inner_zero_left,integral_zero,mul_zero,sub_zero,zero_add,add_zero]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,basis_trace_sum]
  congr 1
  rw [←integral_finsetSum Finset.univ (fun a _=>bilinear_integrable _ _ _)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  exact basis_quadratic_sum A x

theorem affine_cap_eq_preimage (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) :
    FSC.cap (fun j=>w j+t • A.adjoint (w j)) (fun j=>b j-t*inner ℝ (w j) z)=
      (fun x=>x+t • A x+t • z) ⁻¹' FSC.cap w b := by
  ext x
  simp only [FSC.cap,Set.mem_setOf_eq,Set.mem_preimage,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,ContinuousLinearMap.adjoint_inner_left]
  apply forall_congr'
  intro j
  constructor <;> intro h <;> linarith

/-- Actual Gaussian affine-transport derivative. There is no assumed density
or score formula, invertibility hypothesis, or symmetry restriction on A. -/
theorem hasDerivAt_affine_gaussian_mass (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    HasDerivAt (fun t : ℝ=>(stdGaussian (FSC.Coord d)
      ((fun x=>x+t • A x+t • z) ⁻¹' FSC.cap w b)).toReal)
      ((∫ x in FSC.cap w b,inner ℝ x (A x) ∂stdGaussian (FSC.Coord d))-
        FSC.capMass w b*LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap+
        (∫ x in FSC.cap w b,inner ℝ z x ∂stdGaussian (FSC.Coord d))) 0 := by
  let δ := affineVelocity w A z
  have hF := hasFDerivAt_capTest w hw b hb (fun _=>1) continuous_const 1 (by norm_num)
    (fun x=>by simp)
  have hp : HasDerivAt (fun t : ℝ=>(w,b)+t • δ) δ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const δ).const_add (w,b)
  have hF' : HasFDerivAt (fun p : Parameters d ι=>capTest p (fun _=>1))
      (capJointDerivative w b (fun _=>1)) ((w,b)+(0:ℝ) • δ) := by simpa using hF
  have hh := hF'.comp_hasDerivAt (0:ℝ) hp
  have he (t : ℝ) : capTest ((w,b)+t • δ) (fun _=>1)=
      (stdGaussian (FSC.Coord d) ((fun x=>x+t • A x+t • z) ⁻¹' FSC.cap w b)).toReal := by
    rw [capTest_one]
    have hp' : ((w,b)+t • δ).2=fun j=>b j-t*inner ℝ (w j) z := by
      funext j
      simp [δ,affineVelocity,sub_eq_add_neg,mul_neg]
    rw [hp']
    change FSC.capMass (fun j=>w j+t • A.adjoint (w j)) _=_
    rw [FSC.capMass,affine_cap_eq_preimage]
  change HasDerivAt (fun t : ℝ=>capTest ((w,b)+t • δ) (fun _=>1))
    (capJointDerivative w b (fun _=>1) δ) 0 at hh
  simp_rw [he] at hh
  simpa only [δ,capJointDerivative_affine w hw b hb A z] using hh

/-- The actual logarithmic mass derivative at every positive-mass base cap. -/
theorem hasDerivAt_log_affine_gaussian_mass (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    HasDerivAt (fun t : ℝ=>Real.log ((stdGaussian (FSC.Coord d)
      ((fun x=>x+t • A x+t • z) ⁻¹' FSC.cap w b)).toReal))
      (((∫ x in FSC.cap w b,inner ℝ x (A x) ∂stdGaussian (FSC.Coord d))-
        FSC.capMass w b*LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap+
        (∫ x in FSC.cap w b,inner ℝ z x ∂stdGaussian (FSC.Coord d)))/FSC.capMass w b) 0 := by
  have hh := hasDerivAt_affine_gaussian_mass w hw b hb A z
  simpa [FSC.capMass] using hh.log (by simpa [FSC.capMass] using ne_of_gt hp)

end NegativeVotingAffineOperatorDerivative
