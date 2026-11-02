import GaussianAffineNormControl

/-! Actual positivity of finite Gaussian caps under every invertible affine
transport, derived from Gaussian null boundaries and full support. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace Classical
namespace NegativeVotingAffinePositiveMass
open NegativeVotingAffinePathDerivative
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cap_strict_point_of_positive (w : ι → FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι → ℝ) (hp : 0 < FSC.capMass w b) :
    ∃ x : FSC.Coord d,∀ j,inner ℝ (w j) x < b j := by
  have hn (j : ι) : w j≠0 := by
    intro he
    have hh := hw j
    rw [he,norm_zero] at hh
    norm_num at hh
  have hae : ∀ᵐ x ∂stdGaussian (FSC.Coord d),∀ j,inner ℝ (w j) x≠b j :=
    ae_all_iff.mpr (fun j=>FSC.ae_inner_ne (w j) (hn j) (b j))
  by_contra he
  have hz : stdGaussian (FSC.Coord d) (FSC.cap w b)=0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with x hx
    intro hmem
    exact he ⟨x,fun j=>lt_of_le_of_ne (hmem j) (hx j)⟩
  simpa [FSC.capMass,hz] using hp

/-- No positive-mass assumption along the path is supplied: every invertible
affine image retains an actual strict feasible point and positive Gaussian mass. -/
theorem affineMass_pos (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hp : 0 < FSC.capMass w b)
    (M : FSC.Coord d ≃L[ℝ] FSC.Coord d) (v : FSC.Coord d) :
    0 < affineMass w b M.toContinuousLinearMap v := by
  obtain ⟨x,hx⟩ := cap_strict_point_of_positive w hw b hp
  let U : Set (FSC.Coord d) := {y | ∀ j,inner ℝ (w j) (M y+v)<b j}
  have hU : IsOpen U := by
    simp only [U,Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (continuous_const.inner (M.continuous.add continuous_const)) continuous_const
  have hmem : M.symm (x-v)∈U := by
    intro j
    simpa only [M.apply_symm_apply,sub_add_cancel] using hx j
  have hsub : U ⊆ (fun y=>M.toContinuousLinearMap y+v) ⁻¹' FSC.cap w b := by
    intro y hy j
    exact (hy j).le
  have hpos := (FSC.stdGaussian_pos_of_isOpen hU ⟨_,hmem⟩).trans_le (measure_mono hsub)
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

/-- Positivity for the complete actual near-identity line, including both ends. -/
theorem nearIdentity_affineMass_pos (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : ‖A‖ ≤ 1/2)
    (z : FSC.Coord d) (t : ℝ) (ht : |t| ≤ 1) :
    0 < affineMass w b (NegativeVotingAffineNormControl.nearIdentityMap A t) (t • z) :=
  affineMass_pos w hw b hp (NegativeVotingAffineNormControl.nearIdentityEquiv A hA t ht) (t • z)

end NegativeVotingAffinePositiveMass
