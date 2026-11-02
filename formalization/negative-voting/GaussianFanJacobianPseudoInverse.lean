import GaussianFanMassInverse
import TauCeti.Analysis.Matrix.SchurComplement

/-! The canonical covariance pseudoinverse of the actual Gaussian fan mass
Jacobian. The matrix is the intrinsic-facet-weight Laplacian; range and kernel
compatibility are conclusions, not additional hypotheses. -/
noncomputable section
open Matrix
open scoped BigOperators

namespace NegativeVotingFanPseudoInverse
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFanInverse NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The literal matrix of subtraction of the arithmetic mean. -/
def centeringMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℝ :=
  1 - (Fintype.card ι : ℝ)⁻¹ • Matrix.of (fun _ _ => 1)

@[simp] theorem centeringMatrix_mulVec (v : ι → ℝ) :
    centeringMatrix ι *ᵥ v = (centering v : ι → ℝ) := by
  unfold centeringMatrix
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  ext i
  simp [Matrix.mulVec, dotProduct, div_eq_mul_inv, mul_comm]

/-- Every actual weighted fan Laplacian has zero-sum output. -/
theorem offsetJacobian_sum_mulVec (B : ι → FSC.Coord d) (h v : ι → ℝ) :
    ∑ i, (offsetJacobian B h *ᵥ v) i = 0 := by
  simp_rw [offsetJacobian_mulVec]
  have he : (∑ i, ∑ j, facetWeight B h i j * v i) =
      ∑ i, ∑ j, facetWeight B h i j * v j := by
    calc
      _ = ∑ j, ∑ i, facetWeight B h i j * v i := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [facetWeight_symm B h j i]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr he

/-- Tau Ceti's first Penrose equation and commutation, specialized to the
actual PSD Gaussian Jacobian. -/
theorem offsetJacobian_mul_mul_pseudoinverse (B : ι → FSC.Coord d) (h : ι → ℝ) :
    offsetJacobian B h * (offsetJacobian B h *
      (offsetJacobian B h).covariancePseudoInverse) = offsetJacobian B h := by
  rw [(offsetJacobian B h).commute_covariancePseudoInverse.eq, ← Matrix.mul_assoc]
  exact Matrix.mul_covariancePseudoInverse_mul (offsetJacobian_posSemidef B h)

/-- The canonical orthogonal range projection is exactly arithmetic centering.
The equality is proved for every vector, using the actual constant-kernel theorem. -/
theorem offsetJacobian_pseudoinverse_mulVec (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h v : ι → ℝ) :
    (offsetJacobian B h * (offsetJacobian B h).covariancePseudoInverse) *ᵥ v =
      (centering v : ι → ℝ) := by
  let J := offsetJacobian B h
  let P := J.covariancePseudoInverse
  let w := (J * P) *ᵥ v
  have hw : ∑ i, w i = 0 := by
    dsimp [w, P, J]
    rw [← Matrix.mulVec_mulVec]
    exact offsetJacobian_sum_mulVec B h _
  have hker : offsetJacobian B h *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub]
    change J *ᵥ v - J *ᵥ ((J * P) *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec]
    change J *ᵥ v - (offsetJacobian B h * (offsetJacobian B h *
      (offsetJacobian B h).covariancePseudoInverse)) *ᵥ v = 0
    rw [offsetJacobian_mul_mul_pseudoinverse, sub_self]
  obtain ⟨c, hc⟩ := (offsetJacobian_kernel_iff B hB h (v - w)).mp hker
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hc i)
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hw, sub_zero] at hs
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcmean : (∑ i, v i) / (Fintype.card ι : ℝ) = c := by
    apply (div_eq_iff hn).mpr
    simpa only [mul_comm] using hs
  ext i
  change w i = v i - (∑ j, v j) / (Fintype.card ι : ℝ)
  rw [hcmean]
  have hi : v i - w i = c := hc i
  linarith

/-- Literal matrix identity J J⁺ = I − 11ᵀ/m. -/
theorem offsetJacobian_mul_pseudoinverse (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι → ℝ) :
    offsetJacobian B h * (offsetJacobian B h).covariancePseudoInverse = centeringMatrix ι := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [offsetJacobian_pseudoinverse_mulVec B hB, centeringMatrix_mulVec]

/-- The same canonical centering matrix is J⁺ J. -/
theorem pseudoinverse_mul_offsetJacobian (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι → ℝ) :
    (offsetJacobian B h).covariancePseudoInverse * offsetJacobian B h = centeringMatrix ι := by
  rw [← (offsetJacobian B h).commute_covariancePseudoInverse.eq]
  exact offsetJacobian_mul_pseudoinverse B hB h

/-- The full range of the actual singular Jacobian is the centered subspace. -/
theorem offsetJacobian_range (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι → ℝ) :
    (Matrix.toLin' (offsetJacobian B h)).range = centeredGauge ι := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact offsetJacobian_sum_mulVec B h w
  · intro hv
    refine ⟨(offsetJacobian B h).covariancePseudoInverse *ᵥ v, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, offsetJacobian_mul_pseudoinverse B hB,
      centeringMatrix_mulVec]
    exact congrArg Subtype.val (centering_centered (⟨v, hv⟩ : centeredGauge ι))

/-- The kernel is precisely the one-dimensional space of constant offsets. -/
theorem offsetJacobian_kernel (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι → ℝ) :
    (Matrix.toLin' (offsetJacobian B h)).ker =
      Submodule.span ℝ {fun _ : ι => (1 : ℝ)} := by
  ext v
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, offsetJacobian_kernel_iff B hB]
  constructor
  · rintro ⟨c, hc⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    ext i
    simp [hc i]
  · intro hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨c, fun i => ?_⟩
    have hi := congrFun hc i
    simpa using hi.symm

/-- The canonical pseudoinverse also has zero-sum output. -/
theorem pseudoinverse_sum_mulVec (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h v : ι → ℝ) :
    ∑ i, ((offsetJacobian B h).covariancePseudoInverse *ᵥ v) i = 0 := by
  have hp : centeringMatrix ι * (offsetJacobian B h).covariancePseudoInverse =
      (offsetJacobian B h).covariancePseudoInverse := by
    rw [← pseudoinverse_mul_offsetJacobian B hB h]
    exact Matrix.covariancePseudoInverse_mul_self_mul _
  have he : (centering ((offsetJacobian B h).covariancePseudoInverse *ᵥ v) : ι → ℝ) =
      (offsetJacobian B h).covariancePseudoInverse *ᵥ v := by
    rw [← centeringMatrix_mulVec, Matrix.mulVec_mulVec, hp]
  have hs : ∑ i, (centering ((offsetJacobian B h).covariancePseudoInverse *ᵥ v) : ι → ℝ) i = 0 :=
    (centering ((offsetJacobian B h).covariancePseudoInverse *ᵥ v)).property
  rw [he] at hs
  exact hs

/-- Restriction of the canonical pseudoinverse to centered increments. Its
codomain proof is the derived range property, not a supplied compatibility. -/
def pseudoinverseOnGauge (B : ι → FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι → ℝ) : centeredGauge ι →L[ℝ] centeredGauge ι :=
  (LinearMap.codRestrict (centeredGauge ι)
    ((Matrix.toLin' (offsetJacobian B h).covariancePseudoInverse).comp
      (centeredGauge ι).subtype)
    (fun v => pseudoinverse_sum_mulVec B hB h (v : ι → ℝ))).toContinuousLinearMap

@[simp] theorem pseudoinverseOnGauge_apply (B : ι → FSC.Coord d)
    (hB : AffineIndependent ℝ B) (h : ι → ℝ) (v : centeredGauge ι) :
    (pseudoinverseOnGauge B hB h v : ι → ℝ) =
      (offsetJacobian B h).covariancePseudoInverse *ᵥ (v : ι → ℝ) := rfl

/-- The previously constructed actual derivative inverse acts by the
canonical matrix pseudoinverse on each centered mass increment. -/
theorem centeredMassDerivativeEquiv_symm_apply (B : ι → FSC.Coord d)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (h v : centeredGauge ι) :
    ((centeredMassDerivativeEquiv B σ hσ hlower h).symm v : ι → ℝ) =
      (offsetJacobian B (h : ι → ℝ)).covariancePseudoInverse *ᵥ (v : ι → ℝ) := by
  let hB := affineIndependent_of_centered_lower B σ hσ hlower
  let q := pseudoinverseOnGauge B hB (h : ι → ℝ) v
  have hsolve : centeredMassDerivativeEquiv B σ hσ hlower h q = v := by
    change centering (fun i => massDerivative B (h : ι → ℝ) i (q : ι → ℝ)) = v
    simp_rw [massDerivative_eq_offsetJacobian B σ hσ hlower]
    change centering (offsetJacobian B (h : ι → ℝ) *ᵥ
      ((offsetJacobian B (h : ι → ℝ)).covariancePseudoInverse *ᵥ (v : ι → ℝ))) = v
    rw [Matrix.mulVec_mulVec, offsetJacobian_pseudoinverse_mulVec B hB]
    simp only [centering_centered]
  have hback : (centeredMassDerivativeEquiv B σ hσ hlower h).symm v = q := by
    rw [← hsolve, ContinuousLinearEquiv.symm_apply_apply]
  exact congrArg Subtype.val hback

/-- Equality of continuous linear operators, with the actual Jacobian on the
left and Tau Ceti's canonical covariance pseudoinverse on the right. -/
theorem centeredMassDerivativeEquiv_symm_eq (B : ι → FSC.Coord d)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (h : centeredGauge ι) :
    ((centeredMassDerivativeEquiv B σ hσ hlower h).symm :
      centeredGauge ι →L[ℝ] centeredGauge ι) =
    pseudoinverseOnGauge B (affineIndependent_of_centered_lower B σ hσ hlower) (h : ι → ℝ) := by
  ext v i
  exact congrFun (centeredMassDerivativeEquiv_symm_apply B σ hσ hlower h v) i

/-- Every actual mass chart has this concrete pseudoinverse derivative at
every point of its open target. Chart existence was proved independently. -/
theorem mass_chart_inverse_hasFDerivAt_pseudoinverse (B : ι → FSC.Coord d)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (e : OpenPartialHomeomorph (centeredGauge ι) (centeredGauge ι))
    (he : ⇑e = centeredMass B) (q : centeredGauge ι) (hq : q ∈ e.target) :
    HasFDerivAt e.symm
      (pseudoinverseOnGauge B (affineIndependent_of_centered_lower B σ hσ hlower)
        (e.symm q : ι → ℝ)) q := by
  let L := centeredMassDerivativeEquiv B σ hσ hlower (e.symm q)
  have hd : HasFDerivAt e (L : centeredGauge ι →L[ℝ] centeredGauge ι) (e.symm q) := by
    rw [he]
    exact hasFDerivAt_centeredMass B σ hσ hlower (e.symm q)
  have hinv := e.hasFDerivAt_symm hq hd
  change HasFDerivAt e.symm
    ((centeredMassDerivativeEquiv B σ hσ hlower (e.symm q)).symm :
      centeredGauge ι →L[ℝ] centeredGauge ι) q at hinv
  rw [centeredMassDerivativeEquiv_symm_eq] at hinv
  exact hinv

/-- Concrete derivative equality for the actual inverse, expressed without
an abstract inverse linear equivalence. -/
theorem mass_chart_inverse_fderiv_apply (B : ι → FSC.Coord d)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (e : OpenPartialHomeomorph (centeredGauge ι) (centeredGauge ι))
    (he : ⇑e = centeredMass B) (q : centeredGauge ι) (hq : q ∈ e.target)
    (v : centeredGauge ι) :
    (fderiv ℝ e.symm q v : ι → ℝ) =
      (offsetJacobian B (e.symm q : ι → ℝ)).covariancePseudoInverse *ᵥ (v : ι → ℝ) := by
  rw [(mass_chart_inverse_hasFDerivAt_pseudoinverse B σ hσ hlower e he q hq).fderiv,
    pseudoinverseOnGauge_apply]

/-- Every positive probability vector is realized by an actual Gaussian fan
and an existing local C1 chart whose derivative is the canonical pseudoinverse.
There is no assumed inverse, prescribed-mass existence, or compatibility premise. -/
theorem exists_prescribed_mass_pseudoinverse_chart (B : ι → FSC.Coord d)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ h : centeredGauge ι, mass B (h : ι → ℝ) = p ∧
      ∃ e : OpenPartialHomeomorph (centeredGauge ι) (centeredGauge ι),
        (⇑e = centeredMass B) ∧ h ∈ e.source ∧ centering p ∈ e.target ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
        ∀ q ∈ e.target,
          mass B (e.symm q : ι → ℝ) =
            (fun i => (q : ι → ℝ) i + 1 / (Fintype.card ι : ℝ)) ∧
          HasFDerivAt e.symm
            (pseudoinverseOnGauge B (affineIndependent_of_centered_lower B σ hσ hlower)
              (e.symm q : ι → ℝ)) q := by
  obtain ⟨h, hm, e, he, hsource, htarget, hc, hreal⟩ :=
    exists_prescribed_mass_C1_chart B σ hσ hlower p hp hs
  exact ⟨h, hm, e, he, hsource, htarget, hc, fun q hq =>
    ⟨hreal q hq, mass_chart_inverse_hasFDerivAt_pseudoinverse B σ hσ hlower e he q hq⟩⟩

end NegativeVotingFanPseudoInverse
