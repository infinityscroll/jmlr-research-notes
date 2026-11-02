import GaussianAffineCapNormalization

/-! Actual Gaussian logarithmic mass derivatives at arbitrary invertible
points of affine-transport paths. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingAffinePathDerivative
open NegativeVotingAffineCapNormalization NegativeVotingAffineOperatorDerivative
  NegativeVotingAffineLogMassBound
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def affineMass (w : ι → FSC.Coord d) (b : ι → ℝ)
    (M : FSC.Coord d →L[ℝ] FSC.Coord d) (v : FSC.Coord d) : ℝ :=
  (stdGaussian (FSC.Coord d) ((fun x=>M x+v) ⁻¹' FSC.cap w b)).toReal

theorem equiv_adjoint_injective (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) :
    Function.Injective M.toContinuousLinearMap.adjoint := by
  intro x y he
  have hd : M.toContinuousLinearMap.adjoint (x-y)=0 := by rw [map_sub,he,sub_self]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜:=ℝ)).mp
  have hh := ContinuousLinearMap.adjoint_inner_left M.toContinuousLinearMap
    (M.symm (x-y)) (x-y)
  simpa only [hd,inner_zero_left,ContinuousLinearEquiv.coe_coe,M.apply_symm_apply] using hh.symm

theorem affineMass_eq_normalized (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (v : FSC.Coord d) :
    affineMass w b M.toContinuousLinearMap v=
      FSC.capMass (transportedNormals w M.toContinuousLinearMap.adjoint)
        (transportedSupports w b M.toContinuousLinearMap.adjoint v) := by
  rw [FSC.capMass,transported_adjoint_cap_eq_preimage w hw b _ (equiv_adjoint_injective M) v]
  rfl

/-- The local transport is exactly the relative affine velocity M^-1 A,
M^-1 z on the current normalized cap. -/
theorem affine_path_cap_preimage (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (v : FSC.Coord d)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) :
    (fun x=>x+t • (M.symm (A x))+t • M.symm z) ⁻¹'
      FSC.cap (transportedNormals w M.toContinuousLinearMap.adjoint)
        (transportedSupports w b M.toContinuousLinearMap.adjoint v)=
      (fun x=>(M.toContinuousLinearMap+t • A) x+(v+t • z)) ⁻¹' FSC.cap w b := by
  rw [transported_adjoint_cap_eq_preimage w hw b _ (equiv_adjoint_injective M) v,
    ←Set.preimage_comp]
  congr 1
  funext x
  simp only [Function.comp_def,ContinuousLinearEquiv.coe_coe,map_add,map_smul,M.apply_symm_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]
  abel

/-- The literal derivative of log Gaussian mass along every affine parameter
line through any invertible base point. -/
theorem differentiableAt_log_affineMass (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (v : FSC.Coord d)
    (hp : 0 < affineMass w b M.toContinuousLinearMap v)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    DifferentiableAt ℝ (fun t : ℝ=>Real.log
      (affineMass w b (M.toContinuousLinearMap+t • A) (v+t • z))) 0 := by
  let W := transportedNormals w M.toContinuousLinearMap.adjoint
  let B := transportedSupports w b M.toContinuousLinearMap.adjoint v
  have hW := transportedNormals_unit w hw M.toContinuousLinearMap.adjoint (equiv_adjoint_injective M)
  have hB := transported_noCoincident w hw b hb _ (equiv_adjoint_injective M) v
  have hp' : 0 < FSC.capMass W B := by rwa [←affineMass_eq_normalized w hw b M v]
  have hh := hasDerivAt_log_affine_gaussian_mass W hW B hB hp'
    (M.symm.toContinuousLinearMap.comp A) (M.symm z)
  have hd := hh.differentiableAt
  change DifferentiableAt ℝ (fun t : ℝ=>Real.log ((stdGaussian (FSC.Coord d)
    ((fun x=>x+t • M.symm (A x)+t • M.symm z) ⁻¹' FSC.cap W B)).toReal)) 0 at hd
  dsimp only [W,B] at hd
  simp_rw [affine_path_cap_preimage w hw b M v A z] at hd
  exact hd

/-- Dimension-independent actual path rate, with the inverse base map
explicitly applied to both the linear and translation velocities. -/
theorem affineMass_log_derivative_bound (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (v : FSC.Coord d)
    (hp : 0 < affineMass w b M.toContinuousLinearMap v)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    |deriv (fun t : ℝ=>Real.log (affineMass w b (M.toContinuousLinearMap+t • A) (v+t • z))) 0| ≤
      4*Real.exp 1*(1+Real.log (1/affineMass w b M.toContinuousLinearMap v))*
        operatorHilbertSchmidt (M.symm.toContinuousLinearMap.comp A)+
      ‖M.symm z‖*(2*Real.sqrt (Real.log (1/affineMass w b M.toContinuousLinearMap v))+
        (Real.sqrt (2*Real.pi))⁻¹) := by
  have hW := transportedNormals_unit w hw M.toContinuousLinearMap.adjoint (equiv_adjoint_injective M)
  have hB := transported_noCoincident w hw b hb _ (equiv_adjoint_injective M) v
  have hp' : 0 < FSC.capMass (transportedNormals w M.toContinuousLinearMap.adjoint)
      (transportedSupports w b M.toContinuousLinearMap.adjoint v) := by
    rwa [←affineMass_eq_normalized w hw b M v]
  have hh := affine_log_mass_derivative_bound _ hW _ hB hp'
    (M.symm.toContinuousLinearMap.comp A) (M.symm z)
  change |deriv (fun t : ℝ=>Real.log ((stdGaussian (FSC.Coord d)
    ((fun x=>x+t • M.symm (A x)+t • M.symm z) ⁻¹' FSC.cap
      (transportedNormals w M.toContinuousLinearMap.adjoint)
      (transportedSupports w b M.toContinuousLinearMap.adjoint v))).toReal)) 0| ≤ _ at hh
  simp_rw [affine_path_cap_preimage w hw b M v A z] at hh
  rwa [←affineMass_eq_normalized w hw b M v] at hh

end NegativeVotingAffinePathDerivative
