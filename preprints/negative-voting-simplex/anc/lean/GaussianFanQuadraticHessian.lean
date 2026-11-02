import GaussianMovingCap
import GaussianFanTestedCells
import GaussianCapSecondMoment

/-! Pairing the actual opposite Gaussian faces in the expected-max Hessian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace BigOperators Topology Matrix

namespace NegativeVotingFanHessian
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanJacobian
  NegativeVotingWeightedFacet NegativeVotingCapTail NegativeVotingDisintegration NegativeVotingFacetDegree

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Density divided by edge length, times the actual affine-slice integral. -/
def surfaceIntegral (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι)
    (F : FSC.Coord d → ℝ) : ℝ :=
  gaussianPDFReal 0 1 (pairOffset B h i j) / ‖B i-B j‖ *
    ∫ x in affineFacet B h i j, F x
      ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)

theorem surfaceIntegral_diagonal (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i : ι) (F : FSC.Coord d → ℝ) : surfaceIntegral B h i i F = 0 := by
  simp [surfaceIntegral]

/-- Reversing an oriented face preserves its full Gaussian surface integral,
not merely its probability. -/
theorem surfaceIntegral_reverse (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i j : ι) (F : FSC.Coord d → ℝ) :
    surfaceIntegral B h j i F = surfaceIntegral B h i j F := by
  unfold surfaceIntegral
  rw [pairNormal_reverse B i j,pairOffset_reverse B h i j,norm_sub_rev (B j) (B i),
    affineFacet_reverse]
  have hp : gaussianPDFReal 0 1 (-pairOffset B h i j) = gaussianPDFReal 0 1 (pairOffset B h i j) :=
    NegativeVotingMassCentroid.normalPDF_even _
  rw [hp]
  simp only [FSC.sliceLaw,neg_smul,smul_neg,neg_neg,inner_neg_left]

theorem surfaceIntegral_nonneg (B : ι → FSC.Coord d) (h : ι → ℝ)
    (i j : ι) (F : FSC.Coord d → ℝ) (hF : ∀ x, 0 ≤ F x) :
    0 ≤ surfaceIntegral B h i j F := by
  exact mul_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) (norm_nonneg _))
    (integral_nonneg hF)

theorem surfaceIntegral_add (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι)
    (F G : FSC.Coord d → ℝ)
    (hF : Integrable F (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)))
    (hG : Integrable G (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j))) :
    surfaceIntegral B h i j (fun x => F x+G x) =
      surfaceIntegral B h i j F + surfaceIntegral B h i j G := by
  unfold surfaceIntegral
  rw [integral_add hF.restrict hG.restrict,mul_add]

/-- Every affine direction has a genuine second Gaussian moment under every
actual face law, including its possibly degenerate ambient realization. -/
theorem affine_score_slice_memLp (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (i j k : ι) : MemLp (affineScore D v k) 2
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := by
  letI := NegativeVotingPolyhedral.sliceLaw_isGaussian (pairNormal B i j) (pairOffset B h i j)
  exact (IsGaussian.memLp_two_id.const_inner (𝕜:=ℝ) (D k)).add (memLp_const (v k))

theorem response_integrable (B D : ι → FSC.Coord d) (h v : ι → ℝ) (i j k l : ι) :
    Integrable (fun x => affineScore D v k x * (affineScore D v k x-affineScore D v l x))
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := by
  exact (affine_score_slice_memLp B D h v i j k).integrable_mul
    ((affine_score_slice_memLp B D h v i j k).sub (affine_score_slice_memLp B D h v i j l))

def orderedResponse (B : ι → FSC.Coord d) (h : ι → ℝ)
    (D : ι → FSC.Coord d) (v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, surfaceIntegral B h i j
    (fun x => affineScore D v i x * (affineScore D v i x-affineScore D v j x))

/-- The explicit quadratic form whose identification with the actual second
derivative is established after the moving-cell derivative is composed. -/
def quadraticForm (B : ι → FSC.Coord d) (h : ι → ℝ)
    (D : ι → FSC.Coord d) (v : ι → ℝ) : ℝ :=
  (1/2:ℝ) * ∑ i, ∑ j, surfaceIntegral B h i j
    (fun x => (affineScore D v i x-affineScore D v j x)^2)

theorem surface_square_split (B D : ι → FSC.Coord d) (h v : ι → ℝ) (i j : ι) :
    surfaceIntegral B h i j (fun x => (affineScore D v i x-affineScore D v j x)^2) =
      surfaceIntegral B h i j
        (fun x => affineScore D v i x * (affineScore D v i x-affineScore D v j x)) +
      surfaceIntegral B h i j
        (fun x => affineScore D v j x * (affineScore D v j x-affineScore D v i x)) := by
  have he : (fun x => (affineScore D v i x-affineScore D v j x)^2) =
      fun x => affineScore D v i x * (affineScore D v i x-affineScore D v j x) +
        affineScore D v j x * (affineScore D v j x-affineScore D v i x) := by
    funext x
    ring
  rw [he]
  exact surfaceIntegral_add B h i j _ _ (response_integrable B D h v i j i j)
    (response_integrable B D h v i j j i)

/-- The two actual orientations combine into the square of the score gap. -/
theorem orderedResponse_eq_quadraticForm (B D : ι → FSC.Coord d) (h v : ι → ℝ) :
    orderedResponse B h D v = quadraticForm B h D v := by
  have hs : (∑ i, ∑ j, surfaceIntegral B h i j
      (fun x => affineScore D v j x * (affineScore D v j x-affineScore D v i x))) =
      orderedResponse B h D v := by
    rw [Finset.sum_comm]
    unfold orderedResponse
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact surfaceIntegral_reverse B h i j _
  unfold quadraticForm
  simp_rw [surface_square_split,Finset.sum_add_distrib]
  rw [hs]
  change orderedResponse B h D v = (1/2:ℝ)*(orderedResponse B h D v+orderedResponse B h D v)
  ring

theorem quadraticForm_nonneg (B D : ι → FSC.Coord d) (h v : ι → ℝ) :
    0 ≤ quadraticForm B h D v := by
  apply mul_nonneg (by norm_num : (0:ℝ)≤1/2)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    surfaceIntegral_nonneg B h i j _ (fun x => sq_nonneg _)

theorem surfaceIntegral_const (B : ι → FSC.Coord d) (h : ι → ℝ) (i j : ι) (c : ℝ) :
    surfaceIntegral B h i j (fun _ => c) = facetWeight B h i j*c := by
  by_cases hij : B i=B j
  · simp [surfaceIntegral,facetWeight,hij]
  rw [facetWeight_eq_ambient B h i j hij]
  unfold surfaceIntegral
  rw [setIntegral_const]
  simp only [smul_eq_mul,Measure.real]
  ring

/-- The offset block agrees with the previously checked actual mass Jacobian. -/
theorem quadraticForm_offsets (B : ι → FSC.Coord d) (h v : ι → ℝ) :
    quadraticForm B h (0 : ι → FSC.Coord d) v =
      ∑ i, v i * ((offsetJacobian B h) *ᵥ v) i := by
  rw [← orderedResponse_eq_quadraticForm]
  unfold orderedResponse
  simp only [affineScore,Pi.zero_apply,inner_zero_left,zero_add]
  simp_rw [surfaceIntegral_const,offsetJacobian_mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



/-- The symmetric mixed quadratic expression, in two arbitrary row/offset directions. -/
def mixedForm (B : ι → FSC.Coord d) (h : ι → ℝ)
    (D : ι → FSC.Coord d) (v : ι → ℝ) (E : ι → FSC.Coord d) (e : ι → ℝ) : ℝ :=
  (1/2:ℝ) * ∑ i, ∑ j, surfaceIntegral B h i j
    (fun x => (affineScore D v i x-affineScore D v j x) *
      (affineScore E e i x-affineScore E e j x))

def orderedMixedResponse (B : ι → FSC.Coord d) (h : ι → ℝ)
    (D : ι → FSC.Coord d) (v : ι → ℝ) (E : ι → FSC.Coord d) (e : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, surfaceIntegral B h i j
    (fun x => affineScore E e i x * (affineScore D v i x-affineScore D v j x))

theorem mixed_response_integrable (B D E : ι → FSC.Coord d) (h v e : ι → ℝ)
    (i j k l : ι) :
    Integrable (fun x => affineScore E e k x * (affineScore D v k x-affineScore D v l x))
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)) := by
  exact (affine_score_slice_memLp B E h e i j k).integrable_mul
    ((affine_score_slice_memLp B D h v i j k).sub (affine_score_slice_memLp B D h v i j l))

theorem surface_mixed_split (B D E : ι → FSC.Coord d) (h v e : ι → ℝ) (i j : ι) :
    surfaceIntegral B h i j (fun x =>
      (affineScore D v i x-affineScore D v j x)*(affineScore E e i x-affineScore E e j x)) =
      surfaceIntegral B h i j
        (fun x => affineScore E e i x * (affineScore D v i x-affineScore D v j x)) +
      surfaceIntegral B h i j
        (fun x => affineScore E e j x * (affineScore D v j x-affineScore D v i x)) := by
  have he : (fun x => (affineScore D v i x-affineScore D v j x)*
      (affineScore E e i x-affineScore E e j x)) =
      fun x => affineScore E e i x * (affineScore D v i x-affineScore D v j x) +
        affineScore E e j x * (affineScore D v j x-affineScore D v i x) := by
    funext x
    ring
  rw [he]
  exact surfaceIntegral_add B h i j _ _ (mixed_response_integrable B D E h v e i j i j)
    (mixed_response_integrable B D E h v e i j j i)

theorem orderedMixedResponse_eq_mixedForm (B D E : ι → FSC.Coord d) (h v e : ι → ℝ) :
    orderedMixedResponse B h D v E e = mixedForm B h D v E e := by
  have hs : (∑ i, ∑ j, surfaceIntegral B h i j
      (fun x => affineScore E e j x * (affineScore D v j x-affineScore D v i x))) =
      orderedMixedResponse B h D v E e := by
    rw [Finset.sum_comm]
    unfold orderedMixedResponse
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact surfaceIntegral_reverse B h i j _
  unfold mixedForm
  simp_rw [surface_mixed_split,Finset.sum_add_distrib]
  rw [hs]
  change orderedMixedResponse B h D v E e =
    (1/2:ℝ)*(orderedMixedResponse B h D v E e+orderedMixedResponse B h D v E e)
  ring

theorem mixedForm_symm (B D E : ι → FSC.Coord d) (h v e : ι → ℝ) :
    mixedForm B h D v E e = mixedForm B h E e D v := by
  unfold mixedForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext x
  exact mul_comm _ _

theorem mixedForm_self (B D : ι → FSC.Coord d) (h v : ι → ℝ) :
    mixedForm B h D v D v = quadraticForm B h D v := by
  simp only [mixedForm,quadraticForm,pow_two]

end NegativeVotingFanHessian
