import GaussianCovarianceSupportingPriceBound
import GaussianDiagonalIntegratedLaplacian

/-! The supporting covariance bound written in the actual one-dimensional
all-label Gaussian hazard coefficients. Every PSD competitor is included. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingDiagonalCovarianceSupport
open NegativeVotingCovarianceConcavity NegativeVotingCovarianceSupportingPriceBound
  NegativeVotingPositiveCovariance NegativeVotingCovarianceRealization
  NegativeVotingDiagonalIntegratedLaplacian NegativeVotingDiagonalScoreRealization
  NegativeVotingDiagonalWinnerIntegral NegativeVotingFanJacobian NegativeVotingFanSelectedOffsets
variable {n d : ℕ}

lemma symmetric_factor_inner (S C : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hS : S.toLinearMap.IsSymmetric) (hSC : S.comp S=C) (x y : FSC.Coord d) :
    inner ℝ (S x) (S y)=inner ℝ x (C y) := by
  have hh:=hS x (S y)
  change inner ℝ (S x) (S y)=inner ℝ x (S (S y)) at hh
  have he:S (S y)=C y:=congrArg (fun T:FSC.Coord d→L[ℝ]FSC.Coord d=>T y) hSC
  rwa [he] at hh

lemma symmetric_factor_norm_sq (S C : FSC.Coord d→L[ℝ]FSC.Coord d)
    (hS : S.toLinearMap.IsSymmetric) (hSC : S.comp S=C) (x : FSC.Coord d) :
    ‖S x‖^2=inner ℝ x (C x) := by
  simpa only [real_inner_self_eq_norm_sq] using symmetric_factor_inner S C hS hSC x x

/-- The positive diagonal support point is specified by its literal centered
score Gram matrix. The competitor covariance may be singular. -/
theorem operatorValue_le_diagonal_hazard_support
    (b : AffineBasis (Fin (n+1)) ℝ (FSC.Coord d))
    (p : Fin (n+1)→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1)
    (σ : Fin (n+1)→ℝ) (hσ : ∀i,0<σ i) (v : FSC.Coord (n+1))
    (C D : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C∈psdCone) (hD : D∈pdCone)
    (hGram : ∀i j,inner ℝ (b i) (D (b j))=
      inner ℝ (diagonalRows σ i-v) (diagonalRows σ j-v)) :
    operatorValue b p C ≤ (1/2:ℝ)*∑i,
      integratedRowSum σ (selectedOffsets (diagonalRows σ) p) i*
        (inner ℝ (b i) (C (b i))+inner ℝ (b i) (D (b i))) := by
  obtain ⟨R,hR,hRi,hRD⟩:=exists_positive_factor D hD
  obtain ⟨S,hS,hSC⟩:=exists_psd_factor C hC
  have hG:∀i j,inner ℝ (diagonalRows σ i-v) (diagonalRows σ j-v)=
      inner ℝ (mappedBasis b R i) (mappedBasis b R j):=by
    intro i j
    rw [←hGram i j]
    exact (symmetric_factor_inner R.toContinuousLinearMap D hR hRD (b i) (b j)).symm
  have ho:selectedOffsets (mappedBasis b R) p=selectedOffsets (diagonalRows σ) p:=
    selectedOffsets_diagonal_gram σ hσ v (mappedBasis b R) hG p hp hs
  have hbound:=operatorValue_le_price_support b p hp hs C D hC hD R hR hRi hRD
  have hL:=physical_laplacian_le_hazard_diagonal σ
    (selectedOffsets (diagonalRows σ) p) hσ v (mappedBasis b R) hG (fun i=>S (b i))
  have hRbound:=physical_laplacian_le_hazard_diagonal σ
    (selectedOffsets (diagonalRows σ) p) hσ v (mappedBasis b R) hG (fun i=>R (b i))
  have hSnorm:∀i j,‖S (b i)-S (b j)‖^2=inner ℝ (b i-b j) (C (b i-b j)):=by
    intro i j
    rw [←map_sub]
    exact symmetric_factor_norm_sq S C hS.1 hSC _
  have hRnorm:∀i j,‖R (b i)-R (b j)‖^2=inner ℝ (b i-b j) (D (b i-b j)):=by
    intro i j
    rw [←map_sub]
    exact symmetric_factor_norm_sq R.toContinuousLinearMap D hR hRD _
  simp_rw [hSnorm,symmetric_factor_norm_sq S C hS.1 hSC] at hL
  have hRnorm0 (i:Fin (n+1)):‖R (b i)‖^2=inner ℝ (b i) (D (b i)):=
    symmetric_factor_norm_sq R.toContinuousLinearMap D hR hRD _
  simp_rw [hRnorm,hRnorm0] at hRbound
  rw [ho] at hbound
  have hsum:(∑i,∑j,facetWeight (mappedBasis b R) (selectedOffsets (diagonalRows σ) p) i j*
      inner ℝ (b i-b j) ((C+D) (b i-b j)))=
      (∑i,∑j,facetWeight (mappedBasis b R) (selectedOffsets (diagonalRows σ) p) i j*
      inner ℝ (b i-b j) (C (b i-b j)))+
      (∑i,∑j,facetWeight (mappedBasis b R) (selectedOffsets (diagonalRows σ) p) i j*
      inner ℝ (b i-b j) (D (b i-b j))) := by
    simp only [ContinuousLinearMap.add_apply,inner_add_right,mul_add,Finset.sum_add_distrib]
  rw [hsum] at hbound
  simp only [mul_add,Finset.sum_add_distrib]
  linarith

end NegativeVotingDiagonalCovarianceSupport
