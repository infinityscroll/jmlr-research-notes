import GaussianHessianReferenceRemainder
import GaussianRegularReferenceNormalization
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Differentiation at every point of the actual selected balanced segment,
and finite scalar comparison from an explicit bound on its derived Hessian.
The quantitative Hessian bound is not assumed solved by this integration lemma. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingBalancedEnergyComparison
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanQuadraticMoments
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingBalancedMomentComparison
  NegativeVotingFanCanonicalOffset NegativeVotingFanSelectedOffsets
  NegativeVotingCoherentLiftHessian NegativeVotingBalancedFacetHessian
  NegativeVotingSecondChaosMassAdjoint NegativeVotingCapTail
  NegativeVotingRegularReferenceNormalization NegativeVotingNearRegularBalancedGeometry
  NegativeVotingSecondChaosFacetGradient NegativeVotingGlobalTensorTransport
  NegativeVotingFanHessian NegativeVotingRegularOrbitRepresentation
  NegativeVotingRegularFacetCancellation NegativeVotingWeightedFacet
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def selectedEnergy (B D : ι→FSC.Coord d) (p : ι→ℝ) (t : ℝ) : ℝ :=
  secondEnergy (B+t•D) (selectedRowOffsets B D p t)

theorem selectedEnergy_translate (B D : ι→FSC.Coord d) (p : ι→ℝ) (t : ℝ) :
    (fun s:ℝ=>selectedEnergy (B+t•D) D p (s-t))=selectedEnergy B D p := by
  funext s
  unfold selectedEnergy selectedRowOffsets
  have he : (B+t•D)+(s-t)•D=B+s•D := by rw [sub_smul]; abel
  rw [he]

/-- Actual first derivative at every point, using only the C1 offset selector. -/
theorem selectedEnergy_hasDerivAt (B D : ι→FSC.Coord d) (p : ι→ℝ)
    (hp : ∀i,0<p i) (hs : ∑i,p i=1) (t σ : ℝ) (hσ : 0<σ)
    (hlower : CenteredSingularLowerBound (B+t•D) σ) :
    HasDerivAt (selectedEnergy B D p)
      (secondEnergyDerivative (B+t•D) (selectedRowOffsets B D p t)
        (D,canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)) t := by
  have hr : HasDerivAt (fun s:ℝ=>B+s•D) D t := by
    simpa using ((hasDerivAt_id t).smul_const D).const_add B
  exact (hasFDerivAt_secondEnergy (B+t•D) (selectedRowOffsets B D p t) σ hσ hlower).comp_hasDerivAt t
    (hr.prodMk (selectedRowOffsets_hasDerivAt B D t σ hσ hlower p hp hs))

/-- The actual second derivative at arbitrary t is the derived balanced facet
Hessian there. No smoothness of the selected coherent lift as t varies is used. -/
theorem selectedEnergy_deriv_hasDerivAt (B D : ι→FSC.Coord d) (p : ι→ℝ)
    (hp : ∀i,0<p i) (hs : ∑i,p i=1) (t σ : ℝ) (hσ : 0<σ)
    (hlower : CenteredSingularLowerBound (B+t•D) σ)
    (L : (ι→ℝ)→L[ℝ]FSC.Coord d) (hL : CoherentLift (B+t•D) L) :
    HasDerivAt (deriv (selectedEnergy B D p))
      (balancedFacetHessianValue (B+t•D) (selectedRowOffsets B D p t) L
        (massAdjoint (B+t•D) (selectedRowOffsets B D p t))
        (D,canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)) t := by
  have hd := hasDerivAt_selected_balanced_energy_deriv (B+t•D) D σ hσ hlower p hp hs L hL
  dsimp only at hd
  rw [frozenCorrectedHessian_eq_surface _ _ σ hσ hlower L hL] at hd
  change HasDerivAt (deriv (selectedEnergy (B+t•D) D p)) _ 0 at hd
  have hd0 : HasDerivAt (deriv (selectedEnergy (B+t•D) D p))
      (balancedFacetHessianValue (B+t•D) (selectedOffsets (B+t•D) p) L
        (massAdjoint (B+t•D) (selectedOffsets (B+t•D) p))
        (D,canonicalOffsetVariation (B+t•D) (selectedOffsets (B+t•D) p) D)) (t-t) := by
    simpa only [sub_self] using hd
  have hd' := hd0.scomp (h:=fun s:ℝ=>s-t) t ((hasDerivAt_id t).sub_const t)
  simp only [sub_self,one_smul] at hd'
  have he : (fun s:ℝ=>deriv (selectedEnergy (B+t•D) D p) (s-t))=
      deriv (selectedEnergy B D p) := by
    funext s
    rw [←deriv_comp_sub_const,selectedEnergy_translate]
  simpa only [Function.comp_def,he,selectedRowOffsets] using hd'

/-- Finite actual selected-energy comparison with its linear term removed.
The remaining premise is a bound on the concrete derived Hessian, not a
freestanding abstract scalar derivative. -/
theorem selectedEnergy_sub_linear_abs_le (B D : ι→FSC.Coord d) (p : ι→ℝ)
    (hp : ∀i,0<p i) (hs : ∑i,p i=1) (σ : ℝ) (hσ : 0<σ)
    (hlower : ∀t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (B+t•D) σ)
    (L : ℝ→(ι→ℝ)→L[ℝ]FSC.Coord d)
    (hL : ∀t∈Icc (0:ℝ) 1,CoherentLift (B+t•D) (L t))
    (C : ℝ) (hC : 0≤C)
    (hH : ∀t∈Ico (0:ℝ) 1,
      |balancedFacetHessianValue (B+t•D) (selectedRowOffsets B D p t) (L t)
        (massAdjoint (B+t•D) (selectedRowOffsets B D p t))
        (D,canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)|≤C) :
    |secondEnergy (B+D) (selectedOffsets (B+D) p)-secondEnergy B (selectedOffsets B p)-
      secondEnergyDerivative B (selectedOffsets B p)
        (D,canonicalOffsetVariation B (selectedOffsets B p) D)|≤C := by
  let f := selectedEnergy B D p
  let H := fun t:ℝ=>balancedFacetHessianValue (B+t•D) (selectedRowOffsets B D p t) (L t)
    (massAdjoint (B+t•D) (selectedRowOffsets B D p t))
    (D,canonicalOffsetVariation (B+t•D) (selectedRowOffsets B D p t) D)
  have hd (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivWithinAt (deriv f) (H t) (Icc (0:ℝ) 1) t :=
    (selectedEnergy_deriv_hasDerivAt B D p hp hs t σ hσ (hlower t ht) (L t) (hL t ht)).hasDerivWithinAt
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖H t‖≤C := by
    simpa only [Real.norm_eq_abs] using hH t ht
  have hdiff := norm_image_sub_le_of_norm_deriv_le_segment' hd hb
  let g := fun t:ℝ=>f t-t*deriv f 0
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      HasDerivWithinAt g (deriv f t-deriv f 0) (Icc (0:ℝ) 1) t := by
    have hh := (selectedEnergy_hasDerivAt B D p hp hs t σ hσ (hlower t ht)).differentiableAt.hasDerivAt
    convert (hh.sub ((hasDerivAt_id t).mul_const (deriv f 0))).hasDerivWithinAt using 1
    · rfl
    · simp only [one_mul,f]
  have hgb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖deriv f t-deriv f 0‖≤C := by
    have hh := hdiff t ⟨ht.1,ht.2.le⟩
    simp only [sub_zero] at hh
    exact hh.trans (mul_le_of_le_one_right hC ht.2.le)
  have hf := norm_image_sub_le_of_norm_deriv_le_segment_01' hg hgb
  have hzero := (selectedEnergy_hasDerivAt B D p hp hs 0 σ hσ (hlower 0 ⟨le_rfl,by norm_num⟩)).deriv
  dsimp only [g,f] at hf hzero
  rw [hzero] at hf
  simpa only [selectedEnergy,selectedRowOffsets,one_smul,zero_smul,add_zero,one_mul,zero_mul,sub_zero,
    Real.norm_eq_abs,sub_sub,add_comm] using hf

/-- Positive score scaling leaves the actual centered quadratic labels
unchanged, not merely their pairwise comparison sets. -/
theorem quadraticLabelTest_scaled_zero {n : ℕ} (R : Fin (n+2)→FSC.Coord d)
    (α : ℝ) (hα : 0<α) (i : Fin (n+2)) :
    quadraticLabelTest (α•R) 0 i=quadraticLabelTest R 0 i := by
  funext x
  unfold quadraticLabelTest
  simp only [secondMomentTensor_scaled_zero R α hα]

/-- Exact stationarity of the actual Gaussian second-chaos energy at every
positively scaled regular realization, including the minimal ambient dimension. -/
theorem secondEnergyDerivative_regular_scaled_zero {n : ℕ} (hn : 1 ≤ n)
    (R : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0<α) : secondEnergyDerivative (α•R) 0=0 := by
  apply ContinuousLinearMap.ext
  intro δ
  rcases δ with ⟨D,k⟩
  rw [secondEnergyDerivative_surface_formula (α•R) D 0 k α hα (regular_scaled_singular R hG α)]
  rw [surface_sum_label_gap (α•R) 0 (quadraticLabelTest (α•R) 0)
    (fun i j x=>affineScore D k i x-affineScore D k j x)
    (fun i j x=>by ring)
    (fun i j l=>by
      let μ := FSC.sliceLaw (pairNormal (α•R) i j) (pairOffset (α•R) 0 i j)
      letI : IsGaussian μ := NegativeVotingPolyhedral.sliceLaw_isGaussian _ _
      exact (quadraticLabelTest_memLp _ _ l μ).integrable_mul
        ((affine_score_slice_memLp (α•R) D 0 k i j i).sub
          (affine_score_slice_memLp (α•R) D 0 k i j j)))]
  have hz (i j : Fin (n+2)) : surfaceIntegral (α•R) 0 i j
      (fun x=>(quadraticLabelTest (α•R) 0 i x-quadraticLabelTest (α•R) 0 j x)*
        (affineScore D k i x-affineScore D k j x))=0 := by
    unfold surfaceIntegral
    have he : (∫x in affineFacet (α•R) 0 i j,
        (quadraticLabelTest (α•R) 0 i x-quadraticLabelTest (α•R) 0 j x)*
          (affineScore D k i x-affineScore D k j x)
          ∂FSC.sliceLaw (pairNormal (α•R) i j) (pairOffset (α•R) 0 i j))=
        ∫x in affineFacet (α•R) 0 i j,(0:ℝ)
          ∂FSC.sliceLaw (pairNormal (α•R) i j) (pairOffset (α•R) 0 i j) := by
      apply setIntegral_congr_fun (isClosed_affineFacet _ _ _ _).measurableSet
      intro x hx
      dsimp only
      rw [quadraticLabelTest_scaled_zero R α hα i,quadraticLabelTest_scaled_zero R α hα j]
      have hh := actual_regularJump_on_current_facet hn R (α•R) hG 0 α hα.ne' i j x hx
      simp only [errorGap,rowError,Pi.smul_apply,Pi.zero_apply,sub_self,inner_zero_left,
        zero_add,sub_zero,mul_zero,zero_mul] at hh
      change quadraticLabelTest R 0 i x-quadraticLabelTest R 0 j x=0 at hh
      rw [hh,zero_mul]
    rw [he,integral_zero,mul_zero]
  simp only [hz,Finset.sum_const_zero,mul_zero,ContinuousLinearMap.zero_apply]

/-- The actual mass-adjoint correction vanishes at the regular reference. -/
theorem massAdjoint_regular_scaled_zero {n : ℕ} (hn : 1 ≤ n)
    (R : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0<α) : massAdjoint (α•R) 0=0 := by
  have hg : massGradient (α•R) 0=0 := by
    funext i
    simp only [massGradient,offsetCoefficients,secondEnergyDerivative_regular_scaled_zero hn R hG α hα,
      ContinuousLinearMap.zero_apply,Pi.zero_apply]
  simp only [massAdjoint,hg,Matrix.mulVec_zero]

/-- Finite actual balanced energy comparison from the concrete Hessian bound,
with the reference linear term discharged by actual regular stationarity. -/
theorem selected_regular_energy_abs_le {n : ℕ} (hn : 1 ≤ n)
    (R D : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0<α) (σ : ℝ) (hσ : 0<σ)
    (hlower : ∀t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (α•R+t•D) σ)
    (L : ℝ→(Fin (n+2)→ℝ)→L[ℝ]FSC.Coord d)
    (hL : ∀t∈Icc (0:ℝ) 1,CoherentLift (α•R+t•D) (L t))
    (C : ℝ) (hC : 0≤C)
    (hH : ∀t∈Ico (0:ℝ) 1,
      |balancedFacetHessianValue (α•R+t•D)
        (selectedRowOffsets (α•R) D (fun _=>((n+2:ℕ):ℝ)⁻¹) t) (L t)
        (massAdjoint (α•R+t•D) (selectedRowOffsets (α•R) D (fun _=>((n+2:ℕ):ℝ)⁻¹) t))
        (D,canonicalOffsetVariation (α•R+t•D)
          (selectedRowOffsets (α•R) D (fun _=>((n+2:ℕ):ℝ)⁻¹) t) D)|≤C) :
    |secondEnergy (α•R+D) (selectedOffsets (α•R+D) (fun _=>((n+2:ℕ):ℝ)⁻¹))-
      secondEnergy R 0|≤C := by
  have hp : ∀i:Fin (n+2),0<((n+2:ℕ):ℝ)⁻¹ := fun _=>by positivity
  have hs : ∑i:Fin (n+2),((n+2:ℕ):ℝ)⁻¹=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by positivity)
  have hb := selectedEnergy_sub_linear_abs_le (α•R) D _ hp hs σ hσ hlower L hL C hC hH
  rw [selected_regular_scaled_zero R hG α hα,
    secondEnergyDerivative_regular_scaled_zero hn R hG α hα,ContinuousLinearMap.zero_apply,sub_zero] at hb
  have he : secondEnergy (α•R) 0=secondEnergy R 0 := by
    unfold secondEnergy
    simp only [secondMomentTensor_scaled_zero R α hα]
  rwa [he] at hb

end NegativeVotingBalancedEnergyComparison
