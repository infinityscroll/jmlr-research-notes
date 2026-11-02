import GaussianAffinePositiveMass

/-! Actual square-root logarithmic Gaussian mass along a complete invertible
near-identity affine line. All derivative and positivity inputs are derived. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingAffineLogScale
open NegativeVotingAffinePathDerivative NegativeVotingAffinePositiveMass
  NegativeVotingAffineNormControl NegativeVotingAffineLogMassBound
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def lineMass (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) : ℝ :=
  affineMass w b (nearIdentityMap A t) (t • z)

def lineLogMass (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) : ℝ :=
  Real.log (lineMass w b A z t)

def lineLogScale (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) : ℝ :=
  Real.sqrt (1-lineLogMass w b A z t)

theorem lineMass_le_one (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) :
    lineMass w b A z t ≤ 1 := by
  exact measureReal_le_one

theorem lineMass_nonneg (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) :
    0 ≤ lineMass w b A z t := ENNReal.toReal_nonneg

theorem lineLogMass_nonpos (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) :
    lineLogMass w b A z t ≤ 0 :=
  Real.log_nonpos (lineMass_nonneg w b A z t) (lineMass_le_one w b A z t)

theorem one_le_lineLogScale (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) :
    1 ≤ lineLogScale w b A z t := by
  have hn := lineLogMass_nonpos w b A z t
  have hs := Real.sq_sqrt (show 0 ≤ 1-lineLogMass w b A z t by linarith)
  have hp := Real.sqrt_nonneg (1-lineLogMass w b A z t)
  dsimp only [lineLogScale]
  nlinarith

theorem lineLogScale_sq (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) :
    (lineLogScale w b A z t)^2=1-lineLogMass w b A z t :=
  Real.sq_sqrt (by have := lineLogMass_nonpos w b A z t; linarith)

theorem line_shift_identity (w : ι → FSC.Coord d) (b : ι → ℝ)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (z : FSC.Coord d) (t : ℝ) :
    (fun s : ℝ=>Real.log (affineMass w b (nearIdentityMap A t+s • A) (t • z+s • z)))=
      fun s=>lineLogMass w b A z (t+s) := by
  funext s
  unfold lineLogMass lineMass nearIdentityMap
  congr 2 <;> module

theorem differentiableAt_lineLogMass (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : ‖A‖ ≤ 1/2)
    (z : FSC.Coord d) (t : ℝ) (ht : |t| ≤ 1) :
    DifferentiableAt ℝ (lineLogMass w b A z) t := by
  let M := nearIdentityEquiv A hA t ht
  have hp' := affineMass_pos w hw b hp M (t • z)
  have hh := differentiableAt_log_affineMass w hw b hb M (t • z) hp' A z
  change DifferentiableAt ℝ (fun s : ℝ=>Real.log
    (affineMass w b (nearIdentityMap A t+s • A) (t • z+s • z))) 0 at hh
  rw [line_shift_identity] at hh
  simpa only [add_zero] using (differentiableAt_comp_add_left t).mp hh

/-- Concrete logarithmic rate after discharging the inverse norm and relative
velocity estimates throughout the actual near-identity interval. -/
theorem lineLogMass_derivative_bound (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : ‖A‖ ≤ 1/2)
    (z : FSC.Coord d) (t : ℝ) (ht : |t| ≤ 1) :
    |deriv (lineLogMass w b A z) t| ≤
      8*Real.exp 1*(1-lineLogMass w b A z t)*operatorHilbertSchmidt A+
        2*‖z‖*(2*Real.sqrt (Real.log (1/lineMass w b A z t))+
          (Real.sqrt (2*Real.pi))⁻¹) := by
  let M := nearIdentityEquiv A hA t ht
  have hp' := affineMass_pos w hw b hp M (t • z)
  have hh := affineMass_log_derivative_bound w hw b hb M (t • z) hp' A z
  change |deriv (fun s : ℝ=>Real.log
    (affineMass w b (nearIdentityMap A t+s • A) (t • z+s • z))) 0| ≤ _ at hh
  rw [line_shift_identity,deriv_comp_const_add,add_zero] at hh
  have hi : ‖M.symm.toContinuousLinearMap‖ ≤ 2 := nearIdentity_inverse_norm_le A hA t ht
  have hS := (operatorHilbertSchmidt_comp_le M.symm.toContinuousLinearMap A).trans
    (mul_le_mul_of_nonneg_right hi (operatorHilbertSchmidt_nonneg A))
  have hz : ‖M.symm z‖ ≤ 2*‖z‖ := (M.symm.toContinuousLinearMap.le_opNorm z).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg z))
  have he : Real.log (1/lineMass w b A z t)= -lineLogMass w b A z t := by
    simp only [one_div,Real.log_inv,lineLogMass]
  have hq : 0 ≤ 4*Real.exp 1*(1+Real.log (1/lineMass w b A z t)) := by
    rw [he]
    have hn := lineLogMass_nonpos w b A z t
    exact mul_nonneg (by positivity) (by linarith)
  have hm : 0 ≤ 2*Real.sqrt (Real.log (1/lineMass w b A z t))+
      (Real.sqrt (2*Real.pi))⁻¹ := by positivity
  have hmul := add_le_add (mul_le_mul_of_nonneg_left hS hq)
    (mul_le_mul_of_nonneg_right hz hm)
  change |deriv (lineLogMass w b A z) t| ≤
    4*Real.exp 1*(1+Real.log (1/lineMass w b A z t))*
      operatorHilbertSchmidt (M.symm.toContinuousLinearMap.comp A)+
    ‖M.symm z‖*(2*Real.sqrt (Real.log (1/lineMass w b A z t))+
      (Real.sqrt (2*Real.pi))⁻¹) at hh
  have hs := hh.trans hmul
  rw [he] at hs
  rw [he]
  nlinarith

/-- The sharp entropy variable preserves a square-root logarithm on translation,
which is needed at the eventual c/log(m) neighborhood scale. -/
theorem hasDerivAt_lineLogScale (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : ‖A‖ ≤ 1/2)
    (z : FSC.Coord d) (t : ℝ) (ht : |t| ≤ 1) :
    HasDerivAt (lineLogScale w b A z)
      (-deriv (lineLogMass w b A z) t/(2*lineLogScale w b A z t)) t := by
  have hh := ((hasDerivAt_const t (1 : ℝ)).sub
    (differentiableAt_lineLogMass w hw b hb hp A hA z t ht).hasDerivAt).sqrt
    (show 1-lineLogMass w b A z t≠0 by
      have := lineLogMass_nonpos w b A z t; linarith)
  unfold lineLogScale
  simpa only [Pi.sub_def,zero_sub] using hh

theorem lineLogScale_derivative_bound (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b) (hp : 0 < FSC.capMass w b)
    (A : FSC.Coord d →L[ℝ] FSC.Coord d) (hA : ‖A‖ ≤ 1/2)
    (z : FSC.Coord d) (t : ℝ) (ht : |t| ≤ 1) :
    |deriv (lineLogScale w b A z) t| ≤
      4*Real.exp 1*operatorHilbertSchmidt A*lineLogScale w b A z t+3*‖z‖ := by
  have hd := (hasDerivAt_lineLogScale w hw b hb hp A hA z t ht).deriv
  have hF := one_le_lineLogScale w b A z t
  have hFs := lineLogScale_sq w b A z t
  have hFp : 0 < lineLogScale w b A z t := by linarith
  have hn := lineLogMass_nonpos w b A z t
  have he : Real.log (1/lineMass w b A z t)= -lineLogMass w b A z t := by
    simp only [one_div,Real.log_inv,lineLogMass]
  have hS : Real.sqrt (Real.log (1/lineMass w b A z t)) ≤ lineLogScale w b A z t := by
    rw [he]
    exact Real.sqrt_le_sqrt (by linarith)
  have hc : (Real.sqrt (2*Real.pi))⁻¹ ≤ 1 := by
    calc
      _ = gaussianPDFReal 0 1 0 := by simp [gaussianPDFReal]
      _ ≤ 1 := NegativeVotingRegularFacetMean.normalPDF_zero_le_one
  have hh := lineLogMass_derivative_bound w hw b hb hp A hA z t ht
  rw [←hFs] at hh
  have hz := norm_nonneg z
  have htail : 2*‖z‖*(2*Real.sqrt (Real.log (1/lineMass w b A z t))+
      (Real.sqrt (2*Real.pi))⁻¹) ≤ 6*‖z‖*lineLogScale w b A z t := by nlinarith
  rw [hd,abs_div,abs_neg,abs_of_pos (by positivity : 0 < 2*lineLogScale w b A z t)]
  apply (div_le_iff₀ (by positivity : 0 < 2*lineLogScale w b A z t)).mpr
  nlinarith

end NegativeVotingAffineLogScale
