import GaussianCovariancePriceDerivative
import GaussianRayDeficit

/-! The actual supporting Price hyperplane for every PSD competitor.
The base covariance is positive, while the competitor may have any rank. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingCovarianceSupportingPriceBound
open NegativeVotingCovarianceConcavity NegativeVotingCovariancePrice
  NegativeVotingPositiveCovariance NegativeVotingRayDeficit NegativeVotingFanJacobian
  NegativeVotingFanSelectedOffsets NegativeVotingFanCovarianceEnvelope
variable {m d : ℕ} [NeZero m]

theorem operatorValue_radial_derivative (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1)
    (D : FSC.Coord d→L[ℝ]FSC.Coord d) (hD : D∈psdCone) :
    HasDerivAt (fun t:ℝ=>operatorValue b p (D+t • D)) (operatorValue b p D/2) 0 := by
  have ht:HasDerivAt (fun t:ℝ=>1+t) 1 0:=by
    convert (hasDerivAt_const (0:ℝ) 1).add (hasDerivAt_id (0:ℝ)) using 1 <;> simp [Pi.add_def]
  have hd:HasDerivAt (fun t:ℝ=>Real.sqrt (1+t)*operatorValue b p D)
      (operatorValue b p D/2) 0:=by
    convert (ht.sqrt (by norm_num)).mul_const (operatorValue b p D) using 1 <;> norm_num <;> ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [(show Continuous (fun t:ℝ=>1+t) by fun_prop).continuousAt.eventually
    (lt_mem_nhds (by norm_num : (0:ℝ)<1+(0:ℝ)))] with t ht
  have hh:=operatorValue_smul_square b p hp hs D hD (Real.sqrt (1+t)) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt ht.le] at hh
  have he:(1+t) • D=D+t • D:=by module
  rw [he] at hh
  exact hh

theorem price_euler_identity (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1)
    (D : FSC.Coord d→L[ℝ]FSC.Coord d) (hD : D∈pdCone)
    (R : FSC.Coord d≃L[ℝ]FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRD : R.toContinuousLinearMap.comp R.toContinuousLinearMap=D) :
    operatorValue b p D=(1/2:ℝ)*∑i,∑j,
      facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j*
        inner ℝ (b i-b j) (D (b i-b j)) := by
  have h1:=operatorValue_radial_derivative b p hp hs D (pdCone_subset_psdCone hD)
  have h2:=hasDerivAt_operatorValue_factor b p hp hs D D R hR hRi hRD hD.1
  have he:=h1.unique h2
  linarith

/-- A genuine Gaussian supporting hyperplane. Rank loss is allowed only
at the competitor, where no differentiability is assumed. -/
theorem operatorValue_le_price_support (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m→ℝ) (hp : ∀i,0<p i) (hs : ∑i,p i=1)
    (C D : FSC.Coord d→L[ℝ]FSC.Coord d) (hC : C∈psdCone) (hD : D∈pdCone)
    (R : FSC.Coord d≃L[ℝ]FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRD : R.toContinuousLinearMap.comp R.toContinuousLinearMap=D) :
    operatorValue b p C ≤ (1/4:ℝ)*∑i,∑j,
      facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j*
        inner ℝ (b i-b j) ((C+D) (b i-b j)) := by
  let L:ℝ→ᵃ[ℝ](FSC.Coord d→L[ℝ]FSC.Coord d):=AffineMap.lineMap D C
  have hcon:=(operatorValue_concaveOn_psd b p hp hs).comp_affineMap L
  have hsub:Icc (0:ℝ) 1⊆L⁻¹'psdCone:=by
    intro t ht
    change AffineMap.lineMap D C t∈psdCone
    rw [AffineMap.lineMap_apply_module]
    exact psdCone_convex (pdCone_subset_psdCone hD) hC (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hl:=hcon.subset hsub (convex_Icc (0:ℝ) 1)
  have he:(operatorValue b p ∘ L)=(fun t:ℝ=>operatorValue b p (D+t • (C-D))):=by
    funext t
    simp only [Function.comp_apply,L,AffineMap.lineMap_apply_module',add_comm]
  rw [he] at hl
  have hd:=hasDerivAt_operatorValue_factor b p hp hs D (C-D) R hR hRi hRD (hC.1.sub hD.1)
  have hh:=hl.slope_le_of_hasDerivAt (by norm_num) (by norm_num) (by norm_num : (0:ℝ)<1) hd
  simp only [slope_def_field,sub_zero,one_smul,zero_smul,add_zero,div_one] at hh
  have hc:D+(C-D)=C:=by module
  have hz:D+(0:ℝ) • (C-D)=D:=by module
  rw [hc,hz] at hh
  have heuler:=price_euler_identity b p hp hs D hD R hR hRi hRD
  have hadd:(∑i,∑j,facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j*
      inner ℝ (b i-b j) ((C+D) (b i-b j)))=
      (∑i,∑j,facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j*
      inner ℝ (b i-b j) ((C-D) (b i-b j)))+
      2*(∑i,∑j,facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j*
      inner ℝ (b i-b j) (D (b i-b j))) := by
    simp only [Finset.sum_add_distrib,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,inner_add_right,inner_sub_right]
    ring
  rw [hadd]
  linarith

end NegativeVotingCovarianceSupportingPriceBound
