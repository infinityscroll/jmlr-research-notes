import GaussianBoundaryFunctionalRiesz
import GaussianBoundedOUCellTests
import GaussianFanQuadraticMoments
import GaussianFanQuadraticHessian
import GaussianFanOUTrace
import GaussianNearRegularBalancedGeometry
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Actual weak derivatives along Gaussian fan paths and their smoothed L²
comparison. Only statements explicitly proved below are asserted; the global
negative-voting theorem is not assumed. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

namespace NegativeVotingPathSmoothedComparison
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFacetDegree
  NegativeVotingWeightedFacet NegativeVotingCapTail NegativeVotingDisintegration
  NegativeVotingFanQuadraticMoments NegativeVotingFanTestedCells NegativeVotingFanHessian
  NegativeVotingFanMovingCells
  NegativeVotingBoundaryFunctionalRiesz NegativeVotingPolynomialFacetGeometricTrace
  NegativeVotingActualFacetOUTrace NegativeVotingBoundaryTraceAggregation
  NegativeVotingBoundaryHighChaosTrace NegativeVotingFanOUTrace
  NegativeVotingProjection NegativeVotingRareLabelHighChaos NegativeVotingHypercontractivity
  NegativeVotingModern OAI.MinUncut.GaussianHermite
  SlowEquilibration.GaussianMaximalCorrelation GaussianFin
  NegativeVotingNearRegularBalancedGeometry NegativeVotingBalancedMomentGeometry
  NegativeVotingBalancedMomentComparison NegativeVotingBalancedSecondChaosDerivative
  NegativeVotingFanSelectedOffsets NegativeVotingFanCanonicalOffset
  NegativeVotingPolynomialFacetLogBound
  NegativeVotingFanJacobian
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def testedFan (p : Parameters d ι) (F : ι → FSC.Coord d → ℝ) : ℝ :=
  ∑ i,∫ x in winningCell p.1 p.2 i,F i x ∂stdGaussian (FSC.Coord d)

def testedFanDerivative (B : ι → FSC.Coord d) (h : ι → ℝ)
    (F : ι → FSC.Coord d → ℝ) : Parameters d ι →L[ℝ] ℝ :=
  ∑ i,testedCellDerivative B h i (F i)

theorem hasFDerivAt_testedFan (B : ι → FSC.Coord d) (h : ι → ℝ)
    (ell0 : ℝ) (hell0 : 0<ell0) (hlower : CenteredSingularLowerBound B ell0)
    (F : ι → FSC.Coord d → ℝ) (hFc : ∀ i,Continuous (F i))
    (C : ι → ℝ) (hC : ∀ i,0≤C i) (hF : ∀ i x,|F i x|≤C i*(1+‖x‖^2)) :
    HasFDerivAt (fun p : Parameters d ι => testedFan p F)
      (testedFanDerivative B h F) (B,h) := by
  have hh := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hasFDerivAt_testedCell B h ell0 hell0 hlower i
      (F i) (hFc i) (C i) (hC i) (hF i))
  convert hh using 1
  · funext p
    simp only [testedFan,Finset.sum_apply]
  · rfl

/-- Actual scalar path derivative; no derivative of a chosen Riesz vector is
needed. -/
theorem hasDerivAt_testedFan_path (p : ℝ → Parameters d ι) (δ : Parameters d ι) (t : ℝ)
    (hp : HasDerivAt p δ t) (ell0 : ℝ) (hell0 : 0<ell0)
    (hlower : CenteredSingularLowerBound (p t).1 ell0)
    (F : ι → FSC.Coord d → ℝ) (hFc : ∀ i,Continuous (F i))
    (C : ι → ℝ) (hC : ∀ i,0≤C i) (hF : ∀ i x,|F i x|≤C i*(1+‖x‖^2)) :
    HasDerivAt (fun s => testedFan (p s) F)
      (testedFanDerivative (p t).1 (p t).2 F δ) t := by
  exact (hasFDerivAt_testedFan (p t).1 (p t).2 ell0 hell0 hlower F hFc C hC hF).comp_hasDerivAt t hp

omit [Nonempty ι] in
/-- The actual slice integral equals the intrinsic Gaussian chart integral. -/
theorem surfaceIntegral_eq_intrinsic (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i j : ι) (hij : B i≠B j) (F : FSC.Coord d → ℝ) (hF : Measurable F) :
    surfaceIntegral B h i j F = gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
      ∫ y in intrinsicFacet B h i j,F (facetChart B h i j y)
        ∂stdGaussian (tangentSpace (pairNormal B i j)) := by
  unfold surfaceIntegral
  rw [sliceLaw_eq_facetChart_map B h i j hij]
  rw [setIntegral_map (isClosed_affineFacet B h i j).measurableSet
    hF.aestronglyMeasurable (by unfold facetChart; fun_prop)]
  rfl

/-- The cell derivative is paired with the actual ordered boundary velocity.
The reversed slice in the primitive moving-cell formula is converted exactly. -/
theorem testedFanDerivative_apply (B : ι → FSC.Coord d) (h : ι → ℝ)
    (ell0 : ℝ) (hell0 : 0<ell0) (hlower : CenteredSingularLowerBound B ell0)
    (F : ι → FSC.Coord d → ℝ) (hFc : ∀ i,Continuous (F i))
    (C : ι → ℝ) (hC : ∀ i,0≤C i) (hF : ∀ i x,|F i x|≤C i*(1+‖x‖^2))
    (δ : Parameters d ι) :
    testedFanDerivative B h F δ = ∑ i,∑ j ∈ Finset.univ.erase i,
      surfaceIntegral B h i j (fun x => F i x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x)) := by
  simp only [testedFanDerivative,sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [NegativeVotingFanQuadraticMoments.testedCellDerivative_apply_ambient B h ell0 hell0 hlower
    i (F i) (hFc i) (C i) (hC i) (hF i) δ]
  change (∑ j : {j:ι // j≠i},surfaceIntegral B h j.1 i
    (fun x => F i x*(inner ℝ (δ.1 i-δ.1 j.1) x+δ.2 i-δ.2 j.1))) = _
  have he (j : ι) : surfaceIntegral B h j i
      (fun x => F i x*(inner ℝ (δ.1 i-δ.1 j) x+δ.2 i-δ.2 j)) =
      surfaceIntegral B h i j
        (fun x => F i x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x)) := by
    rw [surfaceIntegral_reverse]
    congr 1
    funext x
    unfold affineScore
    rw [inner_sub_left]
    ring
  simp_rw [he]
  rw [←Finset.sum_subtype (p := fun j : ι => j≠i) (Finset.univ.erase i)
    (fun j => by simp) (fun j => surfaceIntegral B h i j
      (fun x => F i x*(affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x)))]

omit [Nonempty ι] in
theorem ambientAverage_slice_memLp (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i j : ι) (hij : B i≠B j) {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1)
    (f : FSC.Coord d → ℝ) (hfM : Measurable f)
    (hf : MemLp f 2 (stdGaussian (FSC.Coord d))) :
    MemLp (ambientAverage ρ f) 2 (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := by
  rw [sliceLaw_eq_facetChart_map B h i j hij]
  apply (memLp_map_measure_iff ((ambientAverage_measurable ρ f hfM).aestronglyMeasurable)
    (show AEMeasurable (facetChart B h i j) _ from by unfold facetChart; fun_prop)).mpr
  exact ambientAverage_plane_memLp_two _ (pairNormal_norm B i j hij)
    (canonicalTangentCoordinates _) hρ hρ1 _ f hfM hf

def oneSidedTraceEnergy (B : ι → FSC.Coord d) (h : ι → ℝ) (ρ : ℝ)
    (f : ι → FSC.Coord d → ℝ) : ℝ :=
  ∑ i,∑ j∈Finset.univ.erase i,surfaceIntegral B h i j (fun x => (ambientAverage ρ (f i) x)^2)

theorem oneSidedTraceEnergy_highChaos_le (B : ι → FSC.Coord d) (h : ι → ℝ)
    (ell0 : ℝ) (hell0 : 0<ell0) (hlower : CenteredSingularLowerBound B ell0)
    (τ σ q G : ℝ) (hτ : 0<τ) (hσ : 0<σ) (hσ1 : σ<1)
    (hq : 2≤q) (ht : τ^2=1/(2*q-1)) (hG : 0≤G)
    (hdegree : ∀ i,intrinsicWeightedDegree B h i≤G)
    (f : ι → FSC.Coord d → ℝ) (hfM : ∀ i,Measurable (f i))
    (hf : ∀ i,MemLp (f i) 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ i b,OAI.MinUncut.GaussianHermite.degree b<k →
      OAI.MinUncut.GaussianHermite.coeff (fun x : Fin d→ℝ => f i (WithLp.toLp 2 x)) b=0) :
    oneSidedTraceEnergy B h (τ*σ) f ≤
      4*traceCoefficient (ι:=ι) ell0 G q*(σ^2)^k*
        ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hB : Function.Injective B := fun i j hh => by
    by_contra hij
    exact centered_singular_rows_ne B ell0 hell0 hlower i j hij hh
  let E := fun i => ∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d)
  let T := fun i j => gaussianPDFReal 0 1 (pairOffset B h i j)*
    ∫ y in intrinsicFacet B h i j,(ambientAverage (τ*σ) (f i) (facetChart B h i j y))^2
      ∂stdGaussian (tangentSpace (pairNormal B i j))
  have hmass i j : 0≤fanSurfaceMass B h i j := by
    unfold fanSurfaceMass planeSurfaceMass
    exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) ENNReal.toReal_nonneg
  have htrace i j (hij : i≠j) : T i j ≤
      (2*(σ^2)^k)*(fanSurfaceMass B h i j)^(1-1/q)*(E i+E j) := by
    have hh := plane_surface_highChaos_square_le (pairNormal B i j) (pairNormal_norm B i j (hB.ne hij))
      (canonicalTangentCoordinates _) τ σ q (pairOffset B h i j) hτ hσ hσ1 hq ht
      (intrinsicFacet B h i j) (isClosed_intrinsicFacet B h i j).measurableSet
      (f i) (hfM i) (hf i) k (hvanish i)
    change T i j ≤ 2*(fanSurfaceMass B h i j)^(1-1/q)*(σ^2)^k*E i at hh
    have he : 0≤E j := integral_nonneg (fun _ => sq_nonneg _)
    have hc : 0≤2*(fanSurfaceMass B h i j)^(1-1/q)*(σ^2)^k :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (hmass i j) _))
        (pow_nonneg (sq_nonneg σ) k)
    nlinarith [mul_nonneg hc he]
  have hh := ordered_trace_energy_le T (fanSurfaceMass B h) (fun i j => ‖B i-B j‖) E
    ell0 G q (2*(σ^2)^k) hell0 hG (by linarith) (by positivity)
    (fun i => integral_nonneg (fun _ => sq_nonneg _)) (fun i j _ => hmass i j)
    (fun i j hij => centered_singular_pair_norm_lower B ell0 hell0 hlower i j hij)
    (fanSurfaceMass_symm B h hB) (fun i j => norm_sub_rev _ _)
    (fun i => by simp_rw [fanSurfaceMass_div_edge]; exact hdegree i) htrace
  have hid : oneSidedTraceEnergy B h (τ*σ) f =
      ∑ i,∑ j∈Finset.univ.erase i,T i j/‖B i-B j‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [surfaceIntegral_eq_intrinsic B h i j (hB.ne (Finset.mem_erase.mp hj).1.symm)
      _ ((ambientAverage_measurable (τ*σ) (f i) (hfM i)).pow_const 2)]
    dsimp only [T]
    ring
  rw [hid]
  convert hh using 1
  ring

theorem testedFanDerivative_smoothed_sq_le (B : ι → FSC.Coord d) (h : ι → ℝ)
    (ell0 : ℝ) (hell0 : 0<ell0) (hlower : CenteredSingularLowerBound B ell0)
    (τ σ q G : ℝ) (hτ : 0<τ) (hσ : 0<σ) (hσ1 : σ<1)
    (hq : 2≤q) (ht : τ^2=1/(2*q-1)) (hG : 0≤G)
    (hdegree : ∀ i,intrinsicWeightedDegree B h i≤G)
    (f : ι → FSC.Coord d → ℝ) (hfM : ∀ i,Measurable (f i))
    (hf : ∀ i,MemLp (f i) 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ i b,OAI.MinUncut.GaussianHermite.degree b<k →
      OAI.MinUncut.GaussianHermite.coeff (fun x : Fin d→ℝ => f i (WithLp.toLp 2 x)) b=0)
    (hFc : ∀ i,Continuous (ambientAverage (τ*σ) (f i))) (C : ι → ℝ) (hC : ∀ i,0≤C i)
    (hgrowth : ∀ i x,|ambientAverage (τ*σ) (f i) x|≤C i*(1+‖x‖^2))
    (δ : Parameters d ι) :
    (testedFanDerivative B h (fun i => ambientAverage (τ*σ) (f i)) δ)^2 ≤
      8*traceCoefficient (ι:=ι) ell0 G q*(σ^2)^k*quadraticForm B h δ.1 δ.2*
        ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hB : Function.Injective B := fun i j hh => by
    by_contra hij
    exact centered_singular_rows_ne B ell0 hell0 hlower i j hij hh
  have hτsq : τ^2<1 := by
    rw [ht]
    apply (div_lt_one (by linarith : 0<2*q-1)).mpr
    linarith
  have hτ1 : τ<1 := by nlinarith
  have hp : 0<τ*σ := mul_pos hτ hσ
  have hp1 : τ*σ<1 := (mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)
  let μ := fun i j => (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)).restrict (affineFacet B h i j)
  let vel := fun i j x => affineScore δ.1 δ.2 i x-affineScore δ.1 δ.2 j x
  let z := fun i (_j:ι) => ambientAverage (τ*σ) (f i)
  let c := fun i j => gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖
  have hvel i j (_hij : i≠j) : MemLp (vel i j) 2 (μ i j) :=
    ((affine_score_slice_memLp B δ.1 h δ.2 i j i).sub
      (affine_score_slice_memLp B δ.1 h δ.2 i j j)).restrict (affineFacet B h i j)
  have hz i j (hij : i≠j) : MemLp (z i j) 2 (μ i j) :=
    (ambientAverage_slice_memLp B h i j (hB.ne hij) hp hp1 (f i) (hfM i) (hf i)).restrict _
  have hcs := ordered_weighted_pairing_sq_le (fun _ _ : ι => FSC.Coord d) μ vel z c
    (fun _ _ => 1) (fun i j => div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
    (fun _ _ _ => by norm_num) hvel hz
  have hid : testedFanDerivative B h (fun i => ambientAverage (τ*σ) (f i)) δ =
      ∑ i,∑ j∈Finset.univ.erase i,c i j*∫ x,vel i j x*z i j x ∂μ i j := by
    rw [testedFanDerivative_apply B h ell0 hell0 hlower _ hFc C hC hgrowth]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold surfaceIntegral
    apply congrArg (fun t : ℝ => c i j*t)
    apply integral_congr_ae
    filter_upwards with x
    exact mul_comm _ _
  let Q := ∑ i,∑ j∈Finset.univ.erase i,c i j*∫ x,(vel i j x)^2 ∂μ i j
  have hQ : 0≤Q := by
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg (fun j hj => mul_nonneg
      (div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _)))
  have hQeq : Q=2*quadraticForm B h δ.1 δ.2 := by
    have he i : (∑ j∈Finset.univ.erase i,c i j*∫ x,(vel i j x)^2 ∂μ i j) =
        ∑ j,surfaceIntegral B h i j (fun x => (vel i j x)^2) := by
      rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),surfaceIntegral_diagonal,add_zero]
      rfl
    dsimp only [Q]
    simp_rw [he]
    unfold quadraticForm
    dsimp only [vel]
    ring
  have hpair : (testedFanDerivative B h (fun i => ambientAverage (τ*σ) (f i)) δ)^2 ≤
      Q*oneSidedTraceEnergy B h (τ*σ) f := by
    rw [hid]
    simpa only [mul_one,div_one,Q,oneSidedTraceEnergy,surfaceIntegral,c,z,μ] using hcs
  have ht' := oneSidedTraceEnergy_highChaos_le B h ell0 hell0 hlower τ σ q G
    hτ hσ hσ1 hq ht hG hdegree f hfM hf k hvanish
  have hh := mul_le_mul_of_nonneg_left ht' hQ
  rw [hQeq] at hh
  rw [hQeq] at hpair
  exact hpair.trans (by nlinarith only [hh])

/-- Integrating the actual weak derivative uses a scalar mean-value theorem.
The hypothesis H bounds the literal path speed energy, not the desired output
norm. No measurable/differentiable selection of Riesz representatives is used. -/
theorem testedFan_path_smoothed_sq_le (p p' : ℝ → Parameters d ι)
    (hp : ∀ t∈Icc (0:ℝ) 1,HasDerivAt p (p' t) t)
    (ell0 : ℝ) (hell0 : 0<ell0)
    (hlower : ∀ t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (p t).1 ell0)
    (τ σ q G H : ℝ) (hτ : 0<τ) (hσ : 0<σ) (hσ1 : σ<1)
    (hq : 2≤q) (ht : τ^2=1/(2*q-1)) (hG : 0≤G) (hH : 0≤H)
    (hdegree : ∀ t∈Icc (0:ℝ) 1,∀ i,intrinsicWeightedDegree (p t).1 (p t).2 i≤G)
    (henergy : ∀ t∈Ico (0:ℝ) 1,quadraticForm (p t).1 (p t).2 (p' t).1 (p' t).2≤H)
    (f : ι → FSC.Coord d → ℝ) (hfM : ∀ i,Measurable (f i))
    (hf : ∀ i,MemLp (f i) 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ i b,OAI.MinUncut.GaussianHermite.degree b<k →
      OAI.MinUncut.GaussianHermite.coeff (fun x : Fin d→ℝ => f i (WithLp.toLp 2 x)) b=0)
    (hFc : ∀ i,Continuous (ambientAverage (τ*σ) (f i))) (C : ι → ℝ) (hC : ∀ i,0≤C i)
    (hgrowth : ∀ i x,|ambientAverage (τ*σ) (f i) x|≤C i*(1+‖x‖^2)) :
    (testedFan (p 1) (fun i => ambientAverage (τ*σ) (f i))-
      testedFan (p 0) (fun i => ambientAverage (τ*σ) (f i)))^2 ≤
      8*traceCoefficient (ι:=ι) ell0 G q*(σ^2)^k*H*
        ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  let A := 8*traceCoefficient (ι:=ι) ell0 G q*(σ^2)^k*
    ∑ i,∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d)
  have hA : 0≤A := by
    unfold A traceCoefficient
    positivity
  have hb : ∀ t∈Ico (0:ℝ) 1,
      ‖testedFanDerivative (p t).1 (p t).2 (fun i => ambientAverage (τ*σ) (f i)) (p' t)‖≤Real.sqrt (A*H) := by
    intro t ht'
    have htc : t∈Icc (0:ℝ) 1 := ⟨ht'.1,ht'.2.le⟩
    have hh := testedFanDerivative_smoothed_sq_le (p t).1 (p t).2 ell0 hell0 (hlower t htc)
      τ σ q G hτ hσ hσ1 hq ht hG (hdegree t htc) f hfM hf k hvanish hFc C hC hgrowth (p' t)
    have hh' : (testedFanDerivative (p t).1 (p t).2 (fun i => ambientAverage (τ*σ) (f i)) (p' t))^2≤A*H := by
      have he := mul_le_mul_of_nonneg_left (henergy t ht') hA
      dsimp only [A] at he
      nlinarith only [hh,he]
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt (mul_nonneg hA hH)]
    exact hh'
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht' => (hasDerivAt_testedFan_path p (p' t) t (hp t ht') ell0 hell0
      (hlower t ht') (fun i => ambientAverage (τ*σ) (f i)) hFc C hC hgrowth).hasDerivWithinAt) hb
  have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg (A*H))).mpr hm
  rw [Real.norm_eq_abs,sq_abs,Real.sq_sqrt (mul_nonneg hA hH)] at hs
  dsimp only [A] at hs
  nlinarith only [hs]

/-- Polarized Parseval for the actual real Gaussian L² representatives. -/
theorem coefficient_pairing_hasSum (f g : (Fin d→ℝ)→ℝ)
    (hf : MemLp f 2 (γFin d)) (hg : MemLp g 2 (γFin d)) :
    HasSum (fun b => coeff f b*coeff g b) (∫ x,f x*g x ∂γFin d) := by
  change MemLp f 2 (γpi (Fin d)) at hf
  change MemLp g 2 (γpi (Fin d)) at hg
  change HasSum _ (∫ x,f x*g x ∂γpi (Fin d))
  have hh := productHermiteBasis.hasSum_inner_mul_inner (hf.toLp f) (hg.toLp g)
  have he : (fun b => inner ℝ (hf.toLp f) (productHermiteBasis b)*
      inner ℝ (productHermiteBasis b) (hg.toLp g)) = fun b => coeff f b*coeff g b := by
    funext b
    rw [real_inner_comm (productHermiteBasis b) (hf.toLp f),hermite_basis_coefficient hf,hermite_basis_coefficient hg]
  rw [he,integral_inner_toLp] at hh
  exact hh

/-- Actual OU smoothing commuted across the L² pairing together with the
explicit high-mode projection. This holds for either correlation sign. -/
theorem gaussianAverage_highModes_pairing_symm (ρ : ℝ) (hρ : |ρ|≤1) (k : ℕ)
    (f g : (Fin d→ℝ)→ℝ) (hfM : Measurable f) (hgM : Measurable g)
    (hf : MemLp f 2 (γFin d)) (hg : MemLp g 2 (γFin d)) :
    (∫ x,gaussianAverage ρ (highModes k f) x*g x ∂γFin d) =
      ∫ x,f x*gaussianAverage ρ (highModes k g) x ∂γFin d := by
  have hf' := gaussianAverage_memLp_signed ρ hρ (highModes k f)
    (highModes_measurable k f hfM) (highModes_memLp k f hf)
  have hg' := gaussianAverage_memLp_signed ρ hρ (highModes k g)
    (highModes_measurable k g hgM) (highModes_memLp k g hg)
  have hleft := coefficient_pairing_hasSum (gaussianAverage ρ (highModes k f)) g hf' hg
  have hright := coefficient_pairing_hasSum f (gaussianAverage ρ (highModes k g)) hf hg'
  apply hleft.unique
  convert hright using 1
  funext b
  rw [gaussianAverage_coefficient ρ hρ (highModes k f) (highModes_measurable k f hfM)
    (highModes_memLp k f hf),gaussianAverage_coefficient ρ hρ (highModes k g)
    (highModes_measurable k g hgM) (highModes_memLp k g hg),coeff_highModes k f hf,coeff_highModes k g hg]
  split_ifs <;> ring

def ambientHighModes (k : ℕ) (f : FSC.Coord d → ℝ) (x : FSC.Coord d) : ℝ :=
  highModes k (fun y : Fin d→ℝ => f (WithLp.toLp 2 y)) x.ofLp

theorem ambientHighModes_measurable (k : ℕ) (f : FSC.Coord d → ℝ) (hfM : Measurable f) :
    Measurable (ambientHighModes k f) :=
  (highModes_measurable k (fun y : Fin d→ℝ => f (WithLp.toLp 2 y)) (hfM.comp (by fun_prop))).comp
    (by fun_prop)

theorem ambientHighModes_memLp_and_norm (k : ℕ) (f : FSC.Coord d → ℝ) (hfM : Measurable f)
    (hf : MemLp f 2 (stdGaussian (FSC.Coord d))) :
    MemLp (ambientHighModes k f) 2 (stdGaussian (FSC.Coord d)) ∧
      (∫ x,(ambientHighModes k f x)^2 ∂stdGaussian (FSC.Coord d))≤
        ∫ x,(f x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hT := NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d
  have hfin := hf.comp_measurePreserving hT
  have hm := highModes_memLp k _ hfin
  have hn := highModes_integral_sq_le k _ hfin
  constructor
  · rw [←hT.map_eq]
    apply (memLp_map_measure_iff ((ambientHighModes_measurable k f hfM).aestronglyMeasurable)
      hT.aemeasurable).mpr
    exact hm
  · have hi := hT.integral_comp' (fun x => (ambientHighModes k f x)^2)
    have hj := hT.integral_comp' (fun x => (f x)^2)
    rw [←hi,←hj]
    exact hn

theorem ambientHighModes_coeff_vanish (k : ℕ) (f : FSC.Coord d → ℝ)
    (hf : MemLp f 2 (stdGaussian (FSC.Coord d))) (b : Fin d→ℕ) (hb : degree b<k) :
    coeff (fun y : Fin d→ℝ => ambientHighModes k f (WithLp.toLp 2 y)) b=0 :=
  highModes_coeff_vanish k _
    (hf.comp_measurePreserving (NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d)) b hb

/-- Bounded continuous raw tests meet the actual moving-cell calculus after
smoothing and removing degrees below k≤3. -/
theorem bounded_test_smoothedHighModes_growth (ρ : ℝ) (hρ : |ρ|≤1) (k : ℕ) (hk : k≤3)
    (u : BoundedContinuousFunction (FSC.Coord d) ℝ) :
    Continuous (ambientAverage ρ (ambientHighModes k u)) ∧
      ∃ C:ℝ,0≤C ∧ ∀ x,|ambientAverage ρ (ambientHighModes k u) x|≤C*(1+‖x‖^2) := by
  have hh := NegativeVotingBoundedOUCellTests.gaussianAverage_highModes_continuous_quadratic
    ρ hρ k hk (fun y : Fin d→ℝ => u (WithLp.toLp 2 y)) (u.continuous.comp (by fun_prop))
    ‖u‖ (norm_nonneg _) (fun y => by simpa only [Real.norm_eq_abs] using u.norm_coe_le_norm (WithLp.toLp 2 y))
  have he : ambientAverage ρ (ambientHighModes k u) =
      fun x : FSC.Coord d => gaussianAverage ρ (highModes k (fun y : Fin d→ℝ => u (WithLp.toLp 2 y))) x.ofLp := by
    funext x
    exact ambientAverage_eq_gaussianAverage ρ (ambientHighModes k u) x
  rw [he]
  exact hh

def boundedFamilyToL2 (u : ι → BoundedContinuousFunction (FSC.Coord d) ℝ) : BoundaryL2 d ι :=
  WithLp.toLp 2 (fun i => BoundedContinuousFunction.toLp 2 (stdGaussian (FSC.Coord d)) ℝ (u i))

omit [DecidableEq ι] [Nonempty ι] in
theorem boundedFamilyToL2_denseRange : DenseRange (boundedFamilyToL2 (d:=d) (ι:=ι)) := by
  have hd := DenseRange.piMap (fun _ : ι =>
    BoundedContinuousFunction.toLp_denseRange (E:=ℝ) (p:=2) (stdGaussian (FSC.Coord d)) ℝ (by norm_num))
  exact (PiLp.homeomorph 2 (fun _ : ι => Lp ℝ 2 (stdGaussian (FSC.Coord d)))).symm.surjective.denseRange.comp
    hd (PiLp.continuous_toLp 2 _)

omit [DecidableEq ι] [Nonempty ι] in
/-- A weak bound proved on bounded continuous label tests extends to the full
Gaussian Hilbert norm by actual density. This is the final duality step, not an
assumption that bounded tests already exhaust L². -/
theorem norm_sq_le_of_boundedContinuous_tests (V : BoundaryL2 d ι) (B : ℝ) (hB : 0≤B)
    (hbound : ∀ u : ι → BoundedContinuousFunction (FSC.Coord d) ℝ,
      (inner ℝ V (boundedFamilyToL2 u))^2≤B*‖boundedFamilyToL2 u‖^2) : ‖V‖^2≤B := by
  have hh : (inner ℝ V V)^2≤B*‖V‖^2 :=
    boundedFamilyToL2_denseRange.induction_on (p := fun W : BoundaryL2 d ι =>
      (inner ℝ V W)^2≤B*‖W‖^2) V
      (isClosed_le (by fun_prop) (by fun_prop)) hbound
  rw [real_inner_self_eq_norm_sq] at hh
  by_cases hz : ‖V‖=0
  · simpa [hz] using hB
  · have hp : 0<‖V‖^2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg V) (Ne.symm hz))
    nlinarith only [hh,hp]

theorem boundedTest_memLp (u : BoundedContinuousFunction (FSC.Coord d) ℝ) :
    MemLp u 2 (stdGaussian (FSC.Coord d)) := u.memLp_top.mono_exponent le_top

def smoothedHighModes (ρ : ℝ) (k : ℕ) (f : FSC.Coord d → ℝ) : FSC.Coord d → ℝ :=
  ambientAverage ρ (ambientHighModes k f)

theorem smoothedHighModes_memLp (ρ : ℝ) (hρ : |ρ|≤1) (k : ℕ)
    (f : FSC.Coord d → ℝ) (hfM : Measurable f)
    (hf : MemLp f 2 (stdGaussian (FSC.Coord d))) :
    MemLp (smoothedHighModes ρ k f) 2 (stdGaussian (FSC.Coord d)) := by
  have hT := NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d
  have hm := gaussianAverage_memLp_signed ρ hρ _
    (highModes_measurable k _ (hfM.comp (by fun_prop)))
    (highModes_memLp k _ (hf.comp_measurePreserving hT))
  rw [←hT.map_eq]
  apply (memLp_map_measure_iff
    ((ambientAverage_measurable ρ _ (ambientHighModes_measurable k f hfM)).aestronglyMeasurable)
    hT.aemeasurable).mpr
  convert hm using 1
  funext x
  exact ambientAverage_eq_gaussianAverage ρ (ambientHighModes k f) (WithLp.toLp 2 x)

theorem smoothedHighModes_pairing_symm (ρ : ℝ) (hρ : |ρ|≤1) (k : ℕ)
    (f g : FSC.Coord d → ℝ) (hfM : Measurable f) (hgM : Measurable g)
    (hf : MemLp f 2 (stdGaussian (FSC.Coord d)))
    (hg : MemLp g 2 (stdGaussian (FSC.Coord d))) :
    (∫ x,smoothedHighModes ρ k f x*g x ∂stdGaussian (FSC.Coord d)) =
      ∫ x,f x*smoothedHighModes ρ k g x ∂stdGaussian (FSC.Coord d) := by
  have hT := NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d
  rw [←hT.integral_comp' (fun x => smoothedHighModes ρ k f x*g x),
    ←hT.integral_comp' (fun x => f x*smoothedHighModes ρ k g x)]
  have he (h : FSC.Coord d → ℝ) (x : Fin d→ℝ) :
      smoothedHighModes ρ k h (WithLp.toLp 2 x)=
        gaussianAverage ρ (highModes k (fun y : Fin d→ℝ => h (WithLp.toLp 2 y))) x :=
    ambientAverage_eq_gaussianAverage ρ (ambientHighModes k h) (WithLp.toLp 2 x)
  simp_rw [he]
  exact gaussianAverage_highModes_pairing_symm ρ hρ k _ _
    (hfM.comp (by fun_prop)) (hgM.comp (by fun_prop))
    (hf.comp_measurePreserving hT) (hg.comp_measurePreserving hT)

/-- Literal difference of the two winning-cell indicators. -/
def cellDifference (p₀ p₁ : Parameters d ι) (i : ι) (x : FSC.Coord d) : ℝ :=
  (winningCell p₁.1 p₁.2 i).indicator (fun _=>1) x-
    (winningCell p₀.1 p₀.2 i).indicator (fun _=>1) x

omit [DecidableEq ι] in
theorem cellDifference_measurable (p₀ p₁ : Parameters d ι) (i : ι) :
    Measurable (cellDifference p₀ p₁ i) :=
  (measurable_const.indicator (winningCell_measurable p₁.1 p₁.2 i)).sub
    (measurable_const.indicator (winningCell_measurable p₀.1 p₀.2 i))

omit [DecidableEq ι] in
theorem cellDifference_memLp (p₀ p₁ : Parameters d ι) (i : ι) :
    MemLp (cellDifference p₀ p₁ i) 2 (stdGaussian (FSC.Coord d)) :=
  ((memLp_const (1:ℝ)).indicator (winningCell_measurable p₁.1 p₁.2 i)).sub
    ((memLp_const (1:ℝ)).indicator (winningCell_measurable p₀.1 p₀.2 i))

def pathDifferenceToL2 (ρ : ℝ) (hρ : |ρ|≤1) (k : ℕ) (p₀ p₁ : Parameters d ι) :
    BoundaryL2 d ι :=
  WithLp.toLp 2 (fun i => (smoothedHighModes_memLp ρ hρ k _
    (cellDifference_measurable p₀ p₁ i) (cellDifference_memLp p₀ p₁ i)).toLp
      (smoothedHighModes ρ k (cellDifference p₀ p₁ i)))

omit [DecidableEq ι] in
theorem pathDifferenceToL2_ae (ρ : ℝ) (hρ : |ρ|≤1) (k : ℕ)
    (p₀ p₁ : Parameters d ι) (i : ι) :
    (fun x => pathDifferenceToL2 ρ hρ k p₀ p₁ i x) =ᵐ[stdGaussian (FSC.Coord d)]
      smoothedHighModes ρ k (cellDifference p₀ p₁ i) :=
  MemLp.coeFn_toLp (smoothedHighModes_memLp ρ hρ k _
    (cellDifference_measurable p₀ p₁ i) (cellDifference_memLp p₀ p₁ i))

omit [DecidableEq ι] in
theorem pathDifferenceToL2_pairing (ρ : ℝ) (hρ : |ρ|≤1) (k : ℕ)
    (p₀ p₁ : Parameters d ι) (u : ι → BoundedContinuousFunction (FSC.Coord d) ℝ) :
    inner ℝ (pathDifferenceToL2 ρ hρ k p₀ p₁) (boundedFamilyToL2 u) =
      testedFan p₁ (fun i => smoothedHighModes ρ k (u i))-
        testedFan p₀ (fun i => smoothedHighModes ρ k (u i)) := by
  rw [PiLp.inner_apply]
  simp only [testedFan,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MeasureTheory.L2.inner_def]
  have he : (∫ x,inner ℝ (pathDifferenceToL2 ρ hρ k p₀ p₁ i x)
      (boundedFamilyToL2 u i x) ∂stdGaussian (FSC.Coord d)) =
      ∫ x,smoothedHighModes ρ k (cellDifference p₀ p₁ i) x*u i x ∂stdGaussian (FSC.Coord d) := by
    apply integral_congr_ae
    filter_upwards [pathDifferenceToL2_ae ρ hρ k p₀ p₁ i,
      BoundedContinuousFunction.coeFn_toLp 2 (stdGaussian (FSC.Coord d)) ℝ (u i)] with x hx hu
    change inner ℝ _ ((BoundedContinuousFunction.toLp 2 (stdGaussian (FSC.Coord d)) ℝ (u i)) x) = _
    rw [hx,hu,Real.inner_apply]
  rw [he,smoothedHighModes_pairing_symm ρ hρ k _ _
    (cellDifference_measurable p₀ p₁ i) (u i).continuous.measurable
    (cellDifference_memLp p₀ p₁ i) (boundedTest_memLp (u i))]
  have hg := (smoothedHighModes_memLp ρ hρ k (u i) (u i).continuous.measurable (boundedTest_memLp (u i))).integrable (by norm_num)
  have hpoint : (fun x => cellDifference p₀ p₁ i x*smoothedHighModes ρ k (u i) x) =
      fun x => (winningCell p₁.1 p₁.2 i).indicator (smoothedHighModes ρ k (u i)) x-
        (winningCell p₀.1 p₀.2 i).indicator (smoothedHighModes ρ k (u i)) x := by
    funext x
    by_cases h₁ : x∈winningCell p₁.1 p₁.2 i <;>
      by_cases h₀ : x∈winningCell p₀.1 p₀.2 i <;> simp [cellDifference,h₁,h₀]
  rw [hpoint,integral_sub (hg.indicator (winningCell_measurable p₁.1 p₁.2 i))
    (hg.indicator (winningCell_measurable p₀.1 p₀.2 i)),
    integral_indicator (winningCell_measurable p₁.1 p₁.2 i),
    integral_indicator (winningCell_measurable p₀.1 p₀.2 i)]

omit [DecidableEq ι] [Nonempty ι] in
theorem boundedFamilyToL2_norm_sq (u : ι → BoundedContinuousFunction (FSC.Coord d) ℝ) :
    ‖boundedFamilyToL2 u‖^2=∑ i,∫ x,(u i x)^2 ∂stdGaussian (FSC.Coord d) := by
  rw [boundaryL2_norm_sq]
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (stdGaussian (FSC.Coord d)) ℝ (u i)] with x hx
  change ((BoundedContinuousFunction.toLp 2 (stdGaussian (FSC.Coord d)) ℝ (u i)) x)^2=_
  rw [hx]

omit [DecidableEq ι] in
theorem pathDifferenceToL2_norm_sq (ρ : ℝ) (hρ : |ρ|≤1) (k : ℕ)
    (p₀ p₁ : Parameters d ι) :
    ‖pathDifferenceToL2 ρ hρ k p₀ p₁‖^2=
      ∑ i,∫ x,(smoothedHighModes ρ k (cellDifference p₀ p₁ i) x)^2
        ∂stdGaussian (FSC.Coord d) := by
  rw [boundaryL2_norm_sq]
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [pathDifferenceToL2_ae ρ hρ k p₀ p₁ i] with x hx
  rw [hx]

/-- The actual high-mode smoothed difference of the endpoint winning-cell
indicators. Its squared L² norm is controlled by the literal quadratic energy
of the path. No path integral of selected Riesz representatives is used. The
restriction k≤3 comes solely from the available quadratic moving-cell calculus.
All geometric and path-energy premises remain explicit. -/
theorem path_smoothed_difference_l2_sq_le (p p' : ℝ → Parameters d ι)
    (hp : ∀ t∈Icc (0:ℝ) 1,HasDerivAt p (p' t) t)
    (ell0 : ℝ) (hell0 : 0<ell0)
    (hlower : ∀ t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (p t).1 ell0)
    (τ σ q G H : ℝ) (hτ : 0<τ) (hσ : 0<σ) (hσ1 : σ<1)
    (hq : 2≤q) (ht : τ^2=1/(2*q-1)) (hG : 0≤G) (hH : 0≤H)
    (hdegree : ∀ t∈Icc (0:ℝ) 1,∀ i,intrinsicWeightedDegree (p t).1 (p t).2 i≤G)
    (henergy : ∀ t∈Ico (0:ℝ) 1,quadraticForm (p t).1 (p t).2 (p' t).1 (p' t).2≤H)
    (k : ℕ) (hk : k≤3) :
    (∑ i,∫ x,(smoothedHighModes (τ*σ) k (cellDifference (p 0) (p 1) i) x)^2
      ∂stdGaussian (FSC.Coord d)) ≤
        8*traceCoefficient (ι:=ι) ell0 G q*(σ^2)^k*H := by
  have hτsq : τ^2<1 := by
    rw [ht]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hτ1 : τ<1 := by nlinarith
  have hprod : |τ*σ|≤1 := by
    rw [abs_of_pos (mul_pos hτ hσ)]
    exact ((mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)).le
  let B := 8*traceCoefficient (ι:=ι) ell0 G q*(σ^2)^k*H
  have hB : 0≤B := by
    dsimp [B,traceCoefficient]
    positivity
  have hb : ‖pathDifferenceToL2 (τ*σ) hprod k (p 0) (p 1)‖^2≤B := by
    apply norm_sq_le_of_boundedContinuous_tests _ B hB
    intro u
    rw [pathDifferenceToL2_pairing]
    have hfu i := ambientHighModes_memLp_and_norm k (u i) (u i).continuous.measurable (boundedTest_memLp (u i))
    have hgu i := bounded_test_smoothedHighModes_growth (τ*σ) hprod k hk (u i)
    choose C hC hgrowth using fun i => (hgu i).2
    have he := testedFan_path_smoothed_sq_le p p' hp ell0 hell0 hlower
      τ σ q G H hτ hσ hσ1 hq ht hG hH hdegree henergy
      (fun i => ambientHighModes k (u i))
      (fun i => ambientHighModes_measurable k (u i) (u i).continuous.measurable)
      (fun i => (hfu i).1) k
      (fun i b hb => ambientHighModes_coeff_vanish k (u i) (boundedTest_memLp (u i)) b hb)
      (fun i => (hgu i).1) C hC hgrowth
    apply he.trans
    change B*(∑ i,∫ x,(ambientHighModes k (u i) x)^2 ∂stdGaussian (FSC.Coord d))≤_
    rw [boundedFamilyToL2_norm_sq]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hfu i).2)) hB
  rw [pathDifferenceToL2_norm_sq] at hb
  exact hb

/-- Actual Gram geometry and actual cell masses discharge every facet-degree
premise in the path comparison. The remaining H is the genuine path velocity
quadratic form, not an assumed smoothed-output estimate. -/
theorem path_smoothed_difference_l2_sq_le_of_gram (p p' : ℝ → Parameters d ι)
    (hp : ∀ t∈Icc (0:ℝ) 1,HasDerivAt p (p' t) t)
    (ell0 α : ℝ) (hell0 : 0<ell0) (hα : 0<α)
    (hlower : ∀ t∈Icc (0:ℝ) 1,CenteredSingularLowerBound (p t).1 ell0)
    (e m L C : ℝ) (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L)
    (hC : 0 ≤ C) (hScale : e*Real.sqrt L/m ≤ ell0)
    (hDiagLower : ∀ t∈Icc (0:ℝ) 1,∀ i,α^2/2 ≤ inner ℝ ((p t).1 i) ((p t).1 i))
    (hDiagUpper : ∀ t∈Icc (0:ℝ) 1,∀ i,inner ℝ ((p t).1 i) ((p t).1 i)≤2*α^2)
    (hCross : ∀ t∈Icc (0:ℝ) 1,∀ i j,j≠i→inner ℝ ((p t).1 j) ((p t).1 i)≤α^2/4)
    (hmass : ∀ t∈Icc (0:ℝ) 1,∀ i,
      (stdGaussian (FSC.Coord d) (affineCell (p t).1 (p t).2 i)).toReal≤C/m)
    (τ σ q H : ℝ) (hτ : 0<τ) (hσ : 0<σ) (hσ1 : σ<1)
    (hq : 2≤q) (ht : τ^2=1/(2*q-1)) (hH : 0≤H)
    (hqlog : Real.log ((Fintype.card ι:ℝ)/ell0)≤q)
    (henergy : ∀ t∈Ico (0:ℝ) 1,quadraticForm (p t).1 (p t).2 (p' t).1 (p' t).2≤H)
    (k : ℕ) (hk : k≤3) :
    (∑ i,∫ x,(smoothedHighModes (τ*σ) k (cellDifference (p 0) (p 1) i) x)^2
      ∂stdGaussian (FSC.Coord d)) ≤
        8*Real.exp 1*max 1 (32*(C*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)*(σ^2)^k*H := by
  let G := 32*(C*Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e
  have hG : 0≤G := by dsimp [G]; positivity
  have hh := path_smoothed_difference_l2_sq_le p p' hp ell0 hell0 hlower
    τ σ q G H hτ hσ hσ1 hq ht hG hH
    (fun t ht' i => intrinsicWeightedDegree_uniform_of_gram
      (p t).1 (p t).2 ell0 α hell0 hα (hlower t ht') i e m L C
      he hm hL hlog hC hScale (hDiagLower t ht' i) (hDiagUpper t ht')
      (hCross t ht' i) (hmass t ht' i)) henergy k hk
  have hc := traceCoefficient_le_exp (ι:=ι) ell0 G q hell0 hG (by linarith)
    (by exact_mod_cast Fintype.card_pos) hqlog
  exact hh.trans (by
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤8 by norm_num))
        (pow_nonneg (sq_nonneg σ) k)) hH
    simpa only [G,mul_assoc] using hscale)

/-- The actual selected balanced tangent has logarithmic quadratic energy.
This uses variational minimization of the offset response, rather than any
assumed bound on the derivative of the selected offsets. -/
theorem selected_segment_quadraticForm_le {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hGram : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑ i,‖D i‖^2≤α^2/256)
    (e : ℝ) (he : 0<e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    quadraticForm (α•R+t•D) (selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t) D
      (canonicalOffsetVariation (α•R+t•D)
        (selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t) D) ≤
      4*(32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)*quarticLogConstant 2*
        (1+Real.log (m:ℝ))^4*∑ i,‖D i‖^2 := by
  let B := α•R+t•D
  let h := selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t
  have hlower := (segment_geometry hm R D hGram α hα hD t ht).1
  have hinj : Function.Injective B := fun i j hij => by
    by_contra hne
    exact centered_singular_rows_ne B (α/2) (by positivity) hlower i j hne hij
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have ha (i j : Fin m) (hij : i≠j) :
      |pairOffset B h i j|≤2*Real.sqrt (1+Real.log (m:ℝ)) := by
    have hh := pairOffset_le_of_uniform_mass B h hinj
      (fun i => by
        have hmass := congrFun (selected_uniform_mass B hinj) i
        simpa only [Fintype.card_fin,B,h,selectedRowOffsets] using hmass.ge) i j hij
    simpa only [Fintype.card_fin] using hh
  have hd (i : Fin m) : (∑ j,facetWeight B h i j)≤
      32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e := by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),facetWeight_self,add_zero]
    exact selected_segment_degree hm R D hGram α hα hD e he hscale t ht i
  have hh := canonical_edgeScoreEnergy_log_le B D h (α/2) (by positivity) hlower
    2 m (32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e) hm1
    (selected_segment_probability hm R D hGram α hα hD t ht) ha hd 0
  rw [edgeScoreEnergy_eq_twice_quadraticForm B D h _ hinj] at hh
  simp only [sub_zero] at hh
  change quadraticForm B h D (canonicalOffsetVariation B h D)≤_
  nlinarith only [hh]

/-- Actual uniformly balanced near-regular segment: selected offsets, all
facet geometry, and the path velocity energy are derived. The resulting bound
has no additional alphabet or ambient-dimension factor. -/
theorem near_regular_selected_smoothed_difference_l2_sq_le {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (R D : Fin m→FSC.Coord d)
    (hGram : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0<α) (hD : ∑ i,‖D i‖^2≤α^2/256)
    (e : ℝ) (he : 0<e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (τ σ q : ℝ) (hτ : 0<τ) (hσ : 0<σ) (hσ1 : σ<1)
    (hq : 2≤q) (ht : τ^2=1/(2*q-1)) (hqlog : Real.log ((m:ℝ)/(α/2))≤q)
    (k : ℕ) (hk : k≤3) :
    (∑ i,∫ x,(smoothedHighModes (τ*σ) k
      (cellDifference
        (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
        (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹)) i) x)^2
        ∂stdGaussian (FSC.Coord d)) ≤
      32*Real.exp 1*max 1 (32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)*
        (32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)*quarticLogConstant 2*
          (1+Real.log (m:ℝ))^4*(σ^2)^k*∑ i,‖D i‖^2 := by
  let p : ℝ→Parameters d (Fin m) := fun t =>
    (α•R+t•D,selectedRowOffsets (α•R) D (fun _=>(m:ℝ)⁻¹) t)
  let p' : ℝ→Parameters d (Fin m) := fun t =>
    (D,canonicalOffsetVariation (p t).1 (p t).2 D)
  let G := 32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e
  let H := 4*G*quarticLogConstant 2*(1+Real.log (m:ℝ))^4*∑ i,‖D i‖^2
  have hG : 0≤G := by dsimp [G]; positivity
  have hH : 0≤H := by dsimp [H,quarticLogConstant]; positivity
  have hpos : (0:ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hlower t (ht' : t∈Icc (0:ℝ) 1) := (segment_geometry hm R D hGram α hα hD t ht').1
  have hp t (ht' : t∈Icc (0:ℝ) 1) : HasDerivAt p (p' t) t := by
    have hoff := selectedRowOffsets_hasDerivAt (α•R) D t (α/2) (by positivity) (hlower t ht')
      (fun _=>(m:ℝ)⁻¹) (fun _=>inv_pos.mpr hpos) (by simp [ne_of_gt hpos])
    have hrow : HasDerivAt (fun s:ℝ=>α•R+s•D) D t := by
      simpa using ((hasDerivAt_id t).smul_const D).const_add (α•R)
    exact hrow.prodMk hoff
  have hh := path_smoothed_difference_l2_sq_le p p' hp (α/2) (by positivity)
    hlower τ σ q G H hτ hσ hσ1 hq ht hG hH
    (fun t ht' i => by
      exact selected_segment_degree hm R D hGram α hα hD e he hscale t ht' i)
    (fun t ht' => selected_segment_quadraticForm_le hm R D hGram α hα hD e he hscale
      t ⟨ht'.1,ht'.2.le⟩) k hk
  have hc := traceCoefficient_le_exp (ι:=Fin m) (α/2) G q (by positivity) hG (by linarith)
    (by simpa only [Fintype.card_fin] using hpos) (by simpa only [Fintype.card_fin] using hqlog)
  have hcoef := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤8 by norm_num))
      (pow_nonneg (sq_nonneg σ) k)) hH
  have hout := hh.trans hcoef
  simpa only [p,selectedRowOffsets,zero_smul,one_smul,add_zero,H,G,mul_assoc] using
    (show (∑ i,∫ x,(smoothedHighModes (τ*σ) k (cellDifference (p 0) (p 1) i) x)^2
      ∂stdGaussian (FSC.Coord d))≤
        32*Real.exp 1*max 1 G*G*quarticLogConstant 2*(1+Real.log (m:ℝ))^4*(σ^2)^k*
          ∑ i,‖D i‖^2 from by dsimp only [H] at hout; nlinarith only [hout])

end NegativeVotingPathSmoothedComparison
