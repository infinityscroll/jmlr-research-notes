import GaussianPositiveCovarianceFactor

/-! A genuine multivariable smooth row factor, obtained by the symmetric
squaring-map inverse function theorem at the identity. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology RealInnerProductSpace
namespace NegativeVotingLocalCovarianceFactor
open NegativeVotingPositiveCovariance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev SymmetricOperators (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] := ↥(selfAdjoint.submodule ℝ (E→L[ℝ]E))

def symmetricIdentity : SymmetricOperators E :=
  ⟨ContinuousLinearMap.id ℝ E,by exact IsSelfAdjoint.one (E→L[ℝ]E)⟩

def symmetricProjection : (E→L[ℝ]E)→L[ℝ]SymmetricOperators E :=
  (show (E→L[ℝ]E)→ₗ[ℝ]SymmetricOperators E from selfAdjointPart ℝ).toContinuousLinearMap

@[simp] theorem symmetricProjection_coe (S : SymmetricOperators E) :
    symmetricProjection (S : E→L[ℝ]E)=S := by
  exact S.property.selfAdjointPart_apply ℝ

theorem coe_symmetricProjection {T : E→L[ℝ]E} (hT : IsSelfAdjoint T) :
    (symmetricProjection T : E→L[ℝ]E)=T := hT.coe_selfAdjointPart_apply ℝ

def symmetricSquare (S : SymmetricOperators E) : SymmetricOperators E :=
  symmetricProjection ((S : E→L[ℝ]E)*(S : E→L[ℝ]E))

@[simp] theorem coe_symmetricSquare (S : SymmetricOperators E) :
    (symmetricSquare S : E→L[ℝ]E)=(S : E→L[ℝ]E)*(S : E→L[ℝ]E) := by
  exact coe_symmetricProjection (by simpa only [pow_two] using S.property.pow 2)

@[simp] theorem symmetricSquare_identity :
    symmetricSquare (symmetricIdentity (E:=E))=symmetricIdentity := by
  apply Subtype.ext
  rw [coe_symmetricSquare]
  change (1 : E→L[ℝ]E)*1=1
  simp

theorem contDiff_symmetricSquare : ContDiff ℝ ⊤ (symmetricSquare (E:=E)) := by
  exact symmetricProjection.contDiff.comp
    ((selfAdjoint.submodule ℝ (E→L[ℝ]E)).subtypeL.contDiff.mul
      (selfAdjoint.submodule ℝ (E→L[ℝ]E)).subtypeL.contDiff)

theorem hasFDerivAt_symmetricSquare_identity :
    HasFDerivAt (symmetricSquare (E:=E))
      ((2:ℝ)•ContinuousLinearMap.id ℝ (SymmetricOperators E)) symmetricIdentity := by
  let L:SymmetricOperators E→L[ℝ](E→L[ℝ]E):=
    (selfAdjoint.submodule ℝ (E→L[ℝ]E)).subtypeL
  have hh:=(symmetricProjection (E:=E)).hasFDerivAt.comp symmetricIdentity
    ((L.hasFDerivAt).mul' L.hasFDerivAt)
  convert hh using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro S
    change (2:ℝ)•S=symmetricProjection
      (((symmetricIdentity (E:=E)) : E→L[ℝ]E)*(S : E→L[ℝ]E)+
        (S : E→L[ℝ]E)*((symmetricIdentity (E:=E)) : E→L[ℝ]E))
    change (2:ℝ)•S=symmetricProjection (1*(S : E→L[ℝ]E)+(S : E→L[ℝ]E)*1)
    simp only [one_mul,mul_one,map_add,symmetricProjection_coe,two_smul]

theorem exists_local_symmetric_sqrt :
    ∃ s : SymmetricOperators E→SymmetricOperators E,
      ContDiffAt ℝ ⊤ s symmetricIdentity ∧ s symmetricIdentity=symmetricIdentity ∧
      ∀ᶠ Q in 𝓝 symmetricIdentity,symmetricSquare (s Q)=Q := by
  let L:SymmetricOperators E≃L[ℝ]SymmetricOperators E:=
    (LinearEquiv.smulOfNeZero ℝ (SymmetricOperators E) (2:ℝ) (by norm_num)).toContinuousLinearEquiv
  have hd : HasFDerivAt symmetricSquare (L : SymmetricOperators E→L[ℝ]SymmetricOperators E)
      symmetricIdentity := by
    convert hasFDerivAt_symmetricSquare_identity (E:=E) using 1
    apply ContinuousLinearMap.ext
    intro S
    rfl
  have hc:=contDiff_symmetricSquare (E:=E) |>.contDiffAt (x:=symmetricIdentity)
  let e:=hc.toOpenPartialHomeomorph symmetricSquare hd (by simp)
  have hsource : symmetricIdentity∈e.source:=hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have htarget : symmetricIdentity∈e.target := by
    have hh:=e.map_source hsource
    simpa only [e,ContDiffAt.toOpenPartialHomeomorph_coe,symmetricSquare_identity] using hh
  refine ⟨e.symm,?_,?_,?_⟩
  · have hh:=hc.to_localInverse hd (by simp)
    change ContDiffAt ℝ ⊤ e.symm (symmetricSquare symmetricIdentity) at hh
    simpa only [symmetricSquare_identity] using hh
  · have hh:=e.left_inv hsource
    simpa only [e,ContDiffAt.toOpenPartialHomeomorph_coe,symmetricSquare_identity] using hh
  · filter_upwards [e.open_target.mem_nhds htarget] with Q hQ
    exact e.right_inv hQ


def symmetricCongruence (R : E→L[ℝ]E) (C : SymmetricOperators E) : SymmetricOperators E :=
  symmetricProjection (R*(C : E→L[ℝ]E)*R)

theorem coe_symmetricCongruence (R : E→L[ℝ]E) (hR : R.toLinearMap.IsSymmetric)
    (C : SymmetricOperators E) :
    (symmetricCongruence R C : E→L[ℝ]E)=R*(C : E→L[ℝ]E)*R := by
  apply coe_symmetricProjection
  have hs:=ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hR
  change star (R*(C : E→L[ℝ]E)*R)=R*(C : E→L[ℝ]E)*R
  simp only [star_mul,hs.star_eq,C.property.star_eq,mul_assoc]

theorem contDiff_symmetricCongruence (R : E→L[ℝ]E) :
    ContDiff ℝ ⊤ (symmetricCongruence R) := by
  exact symmetricProjection.contDiff.comp
    ((contDiff_const.mul (selfAdjoint.submodule ℝ (E→L[ℝ]E)).subtypeL.contDiff).mul contDiff_const)

/-- The chart is smooth in all symmetric covariance entries simultaneously.
Its literal row Gram form equals the prescribed covariance near the base point. -/
theorem exists_local_smooth_covariance_factor
    (C₀ : SymmetricOperators E) (hC₀ : (C₀ : E→L[ℝ]E)∈pdCone) :
    ∃ (R : E≃L[ℝ]E) (A : SymmetricOperators E→(E→L[ℝ]E)),
      R.toLinearMap.IsSymmetric ∧ R.symm.toLinearMap.IsSymmetric ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=(C₀ : E→L[ℝ]E) ∧
      A C₀=R.toContinuousLinearMap ∧ ContDiffAt ℝ ⊤ A C₀ ∧
      ∀ᶠ C in 𝓝 C₀, ∀ x y:E, inner ℝ (A C x) (A C y)=inner ℝ x ((C : E→L[ℝ]E) y) := by
  obtain ⟨R,hR,hRi,hRR⟩:=exists_positive_factor (C₀ : E→L[ℝ]E) hC₀
  obtain ⟨s,hs,hsId,hsq⟩:=exists_local_symmetric_sqrt (E:=E)
  let Q:=symmetricCongruence R.symm.toContinuousLinearMap
  have hQ₀ : Q C₀=symmetricIdentity := by
    apply Subtype.ext
    rw [coe_symmetricCongruence _ hRi]
    ext x
    change R.symm ((C₀ : E→L[ℝ]E) (R.symm x))=x
    rw [←hRR]
    simp
  have hQ : ContDiff ℝ ⊤ Q:=contDiff_symmetricCongruence _
  let A : SymmetricOperators E→(E→L[ℝ]E):=
    fun C=>(s (Q C) : E→L[ℝ]E)*R.toContinuousLinearMap
  refine ⟨R,A,hR,hRi,hRR,?_,?_,?_⟩
  · dsimp [A]
    rw [hQ₀,hsId]
    change (1 : E→L[ℝ]E)*R.toContinuousLinearMap=R.toContinuousLinearMap
    exact one_mul _
  · have hsc : ContDiffAt ℝ ⊤ (fun C=>s (Q C)) C₀:=
      (show ContDiffAt ℝ ⊤ s (Q C₀) by rw [hQ₀]; exact hs).comp C₀ hQ.contDiffAt
    exact ((selfAdjoint.submodule ℝ (E→L[ℝ]E)).subtypeL.contDiff.contDiffAt.comp C₀ hsc).mul contDiffAt_const
  · have hev : ∀ᶠ C in 𝓝 C₀,symmetricSquare (s (Q C))=Q C :=
      (show Tendsto Q (𝓝 C₀) (𝓝 symmetricIdentity) by
        rw [←hQ₀]
        exact hQ.continuous.continuousAt).eventually hsq
    filter_upwards [hev] with C hC x y
    have hS := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (s (Q C)).property
    have hSsq : (s (Q C) : E→L[ℝ]E)*(s (Q C) : E→L[ℝ]E)=
        (Q C : E→L[ℝ]E) := by
      have hh:=congrArg (fun T:SymmetricOperators E=>(T : E→L[ℝ]E)) hC
      simpa only [coe_symmetricSquare] using hh
    calc
      inner ℝ (A C x) (A C y)=
          inner ℝ (R x) ((s (Q C) : E→L[ℝ]E) ((s (Q C) : E→L[ℝ]E) (R y))) := hS _ _
      _ = inner ℝ (R x) ((Q C : E→L[ℝ]E) (R y)) := by
        change inner ℝ (R x) (((s (Q C) : E→L[ℝ]E)*(s (Q C) : E→L[ℝ]E)) (R y))=_
        rw [hSsq]
      _ = inner ℝ (R x) (R.symm ((C : E→L[ℝ]E) y)) := by
        dsimp [Q]
        rw [coe_symmetricCongruence _ hRi]
        simp
      _ = inner ℝ x ((C : E→L[ℝ]E) y) := by
        have hh:=hR x (R.symm ((C : E→L[ℝ]E) y))
        change inner ℝ (R x) (R.symm ((C : E→L[ℝ]E) y))=
          inner ℝ x (R (R.symm ((C : E→L[ℝ]E) y))) at hh
        simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh


/-- Finite row systems inherit the actual multivariable smooth covariance chart. -/
theorem exists_local_smooth_rows {ι : Type*} [Fintype ι] (b : ι→E)
    (C₀ : SymmetricOperators E) (hC₀ : (C₀ : E→L[ℝ]E)∈pdCone) :
    ∃ (R : E≃L[ℝ]E) (B : SymmetricOperators E→ι→E),
      R.toLinearMap.IsSymmetric ∧ R.symm.toLinearMap.IsSymmetric ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=(C₀ : E→L[ℝ]E) ∧
      B C₀=(fun i=>R (b i)) ∧ ContDiffAt ℝ ⊤ B C₀ ∧
      ∀ᶠ C in 𝓝 C₀, ∀ i j,inner ℝ (B C i) (B C j)=inner ℝ (b i) ((C : E→L[ℝ]E) (b j)) := by
  obtain ⟨R,A,hR,hRi,hRR,hA₀,hA,hGram⟩:=exists_local_smooth_covariance_factor C₀ hC₀
  refine ⟨R,fun C i=>A C (b i),hR,hRi,hRR,?_,?_,?_⟩
  · simp only [hA₀,ContinuousLinearEquiv.coe_coe]
  · exact contDiffAt_pi.2 (fun i=>hA.clm_apply contDiffAt_const)
  · filter_upwards [hGram] with C hC i j
    exact hC (b i) (b j)

end NegativeVotingLocalCovarianceFactor
