import GaussianUniformLocalCurvature

/-! Retain the exact diagonal normal strain through the actual Gaussian
covariance curvature and ray deficit. The centered identity is imported from
NegativeVoting.EdgeEnergy; this module does not assume facet weights or a
local curvature conclusion at its final uniform endpoints. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingStrongDiagonalCurvature
open NegativeVoting NegativeVotingProcrustes NegativeVotingAffineNormControl
  NegativeVotingAffineLogMassBound NegativeVotingPositiveCovariance
  NegativeVotingCovarianceRefinement NegativeVotingCovarianceMixed
  NegativeVotingFanCycleHessian NegativeVotingFanCycleBridge NegativeVotingFan
  NegativeVotingFanCovarianceEnvelope NegativeVotingFanCovarianceValue
  NegativeVotingCovarianceConcavity NegativeVotingCovariancePath
  NegativeVotingFanInverse NegativeVotingAffineBasisLower NegativeVotingFanSelectedOffsets
  NegativeVotingFanJacobian NegativeVotingLocalCurvatureAlgebra
  NegativeVotingUniformLocalCurvature NegativeVotingRegularFacetNeighborhood
  NegativeVotingRegularFacetStability NegativeVotingBalancedReference
  NegativeVotingGaussianMaximum NegativeVotingRayDeficit NegativeVotingRegularCovarianceDeficit
variable {m d e : ℕ} [NeZero m]

/-- The full strain energy; the dimension factor on the diagonal is retained. -/
def refinedStrain (b : Fin m → FSC.Coord d)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) : ℝ :=
  (operatorHilbertSchmidt H)^2+
    (m:ℝ)/2*(∑i,(inner ℝ (b i) (H (b i)))^2)+
    (∑i,inner ℝ (b i) (H (b i)))^2/2

theorem refinedStrain_nonneg (b : Fin m → FSC.Coord d)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) : 0 ≤ refinedStrain b H := by
  unfold refinedStrain
  positivity

theorem frame_edge_energy_exact (b : Fin m → FSC.Coord d)
    (hb : ∑ i,b i=0) (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric) :
    (∑i,∑j,(inner ℝ (b i-b j) (H (b i-b j)))^2)=4*refinedStrain b H := by
  have hsym (i j) : inner ℝ (b i) (H (b j))=inner ℝ (b j) (H (b i)) :=
    (hH (b i) (b j)).symm.trans (real_inner_comm _ _)
  have hrow (i) : (∑j,inner ℝ (b i) (H (b j)))=0 := by
    rw [←inner_sum,←map_sum,hb,map_zero,inner_zero_right]
  have hh:=centered_symmetric_edge_energy (fun i j=>inner ℝ (b i) (H (b j))) hsym hrow
  rw [←scoreGram_HilbertSchmidt_sq b hP H] at hh
  have he (i j) : inner ℝ (b i-b j) (H (b i-b j))=
      inner ℝ (b i) (H (b i))+inner ℝ (b j) (H (b j))-2*inner ℝ (b i) (H (b j)) := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    rw [hsym j i]
    ring
  simp only [he]
  rw [hh]
  simp only [Fintype.card_fin,refinedStrain]
  ring

theorem normal_edge_energy_refined_lower (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hb : ∑ i, b i = 0) (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i)=x)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH : H.toLinearMap.IsSymmetric)
    (h : Fin m → ℝ) (w0 : ℝ) (hw0 : 0 ≤ w0)
    (hweights : ∀ i j, i ≠ j → w0 ≤ facetWeight (mappedBasis b R) h i j)
    (hedges : ∀ i j, i ≠ j → ‖R (b i-b j)‖^2 ≤ 3) :
    (2*w0/3)*refinedStrain b H ≤
      normalEdgeEnergy (mappedBasis b R) h (rowsOfOperator (mappedBasis b R) (conjugatedDirection R H)) := by
  have hp (i j : Fin m) : (w0/3)*(inner ℝ (b i-b j) (H (b i-b j)))^2 ≤
      NegativeVotingFanCycle.cycleEdgeWeight (mappedBasis b R) h i j *
      ‖(NegativeVotingFanCycle.faceDirection (mappedBasis b R) {i,j}).starProjection
        (rowsOfOperator (mappedBasis b R) (conjugatedDirection R H) i-
          rowsOfOperator (mappedBasis b R) (conjugatedDirection R H) j)‖^2 := by
    by_cases hij : i=j
    · subst j;simp
    have hvec : R (b i-b j) ≠ 0 := by
      intro hz
      have hh := congrArg R.symm hz
      have he : b i-b j=0 := by simpa using hh
      exact hij (b.ind.injective (sub_eq_zero.mp he))
    have hden : 0 < ‖R (b i-b j)‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hvec)
    have hw : w0 ≤ NegativeVotingFanCycle.cycleEdgeWeight (mappedBasis b R) h i j := by
      rw [cycleEdgeWeight_eq_facetWeight _ _ i j hij]
      exact hweights i j hij
    rw [mapped_normal_strain b R hR H i j hij]
    calc
      _ = w0*((inner ℝ (b i-b j) (H (b i-b j)))^2/3) := by ring
      _ ≤ w0*((inner ℝ (b i-b j) (H (b i-b j)))^2/‖R (b i-b j)‖^2) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (sq_nonneg _) hden (hedges i j hij)) hw0
      _ ≤ _ := mul_le_mul_of_nonneg_right hw (div_nonneg (sq_nonneg _) hden.le)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp i j))
  simp only [← Finset.mul_sum] at hs
  have he := mul_le_mul_of_nonneg_left (frame_edge_energy_exact b hb hP H hH).ge
    (div_nonneg hw0 (by norm_num : (0:ℝ) ≤ 3))
  unfold normalEdgeEnergy
  nlinarith

theorem actual_second_derivative_refined_of_weight_bound
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hb : ∑ i, b i = 0) (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i)=x)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (hRi : R.symm.toLinearMap.IsSymmetric)
    (C H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hH : H.toLinearMap.IsSymmetric) (h : centeredGauge (Fin m))
    (hm : mass (mappedBasis b R) h=p) (w0 : ℝ) (hw0 : 0 ≤ w0)
    (hweights : ∀ i j, i ≠ j → w0 ≤ facetWeight (mappedBasis b R) h i j)
    (hedges : ∀ i j, i ≠ j → ‖R (b i-b j)‖^2 ≤ 3) :
    deriv (deriv (fun t : ℝ => operatorValue b p (C+t • H))) 0 ≤
      -(w0/6)*refinedStrain b H := by
  have hsym : (conjugatedDirection R H).toLinearMap.IsSymmetric :=
    symmetric_conjugate _ _ hRi hH
  obtain ⟨h0,hm0,_,hd2,hq⟩ := exists_actual_covariance_derivatives (mappedBasis b R)
    p hp hs (conjugatedDirection R H) hsym
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound (mappedBasis b R)
  have heqoff : h0=h := Subtype.ext (NegativeVotingFanInverse.centered_offsets_unique
    (mappedBasis b R) σ hσ hlower _ _ h0.property h.property (hm0.trans hm.symm))
  subst h0
  have heq : (fun t : ℝ => operatorValue b p (C+t • H)) =
      (fun t : ℝ => covarianceValue (Matrix.gram ℝ (mappedBasis b R)+
        t • gramVelocity (mappedBasis b R) (conjugatedDirection R H)) p) := by
    funext t
    unfold operatorValue
    rw [gramVelocity_add_smul]
    congr 1
    have hG := factor_gram b C R hR hRR
    have hV := conjugate_gramVelocity b H R hR
    change Matrix.gram ℝ (mappedBasis b R)=gramVelocity b C at hG
    change gramVelocity (mappedBasis b R) (conjugatedDirection R H)=gramVelocity b H at hV
    rw [hG,hV]
  rw [heq,hd2.deriv]
  have hn := normal_edge_energy_refined_lower b hb hP R hR H hH h w0 hw0 hweights hedges
  nlinarith

theorem actual_second_derivative_refined_of_nearby_weights
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hb : ∑ i, b i = 0) (hP : ∀ x, (∑ i, inner ℝ (b i) x • b i)=x)
    (hG : ∀ i j, inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hR : R.toLinearMap.IsSymmetric)
    (hRi : R.symm.toLinearMap.IsSymmetric)
    (C H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hRR : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (hC : operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d)) ≤ 1/8)
    (hH : H.toLinearMap.IsSymmetric) (h : centeredGauge (Fin m))
    (hm : mass (mappedBasis b R) h=p) (a : ℝ) (ha : 0 ≤ a)
    (hweights : ∀ i j, i ≠ j → a/(2*m) ≤ facetWeight (mappedBasis b R) h i j) :
    deriv (deriv (fun t : ℝ => operatorValue b p (C+t • H))) 0 ≤
      -(a/(12*m))*refinedStrain b H := by
  have hh := actual_second_derivative_refined_of_weight_bound b hb hP p hp hs R hR hRi C H
    hRR hH h hm (a/(2*m)) (div_nonneg ha (by positivity)) hweights
    (near_identity_mapped_edge_norm_sq b hG R hR C hRR hC)
  convert hh using 1 <;> ring

/-- Actual uniform curvature, with the factor m on the diagonal strain.
The selected weights are supplied by the proved Gaussian bootstrap. -/
theorem uniform_refined_curvature {n : ℕ} (hn : 0<n) (hmean : 1 ≤ maximumMean n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (C H : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈pdCone)
    (hnear : operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d))≤
      facetRadius 64/(1+Real.log ((n:ℝ)+2))) (hH : H.toLinearMap.IsSymmetric) :
    deriv (deriv (fun t:ℝ=>operatorValue b (uniformMass n) (C+t • H))) 0 ≤
      -(referenceScale n/(12*((n:ℝ)+2)))*refinedStrain b H := by
  have hc:=facetRadius_bounds 64 (by norm_num)
  have hL : 1≤1+Real.log ((n:ℝ)+2):=by
    linarith [Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have he : 1≤Real.exp 1:=(Real.one_le_exp_iff).mpr (by norm_num)
  have hc8 : facetRadius 64≤(1:ℝ)/8:=by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) hc.1.le,hc.2.2.1]
  have hr : facetRadius 64/(1+Real.log ((n:ℝ)+2))≤(1:ℝ)/8:=
    (div_le_self hc.1.le hL).trans hc8
  have hG' : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(n+2:ℕ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  obtain ⟨R,hR,hRi,hRR⟩:=exists_positive_factor C hC
  have hw i j (hij:i≠j) :=
    (balanced_selected_weights_near_identity hn hmean b hG hP C hC hnear R hR hRR i j hij).1.le
  have hh:=actual_second_derivative_refined_of_nearby_weights b hb hP hG' (uniformMass n)
    (uniformMass_pos n) (uniformMass_sum n) R hR hRi C H hRR (hnear.trans hr) hH
    (selectedOffsets (mappedBasis b R) (uniformMass n))
    (selectedOffsets_mass _ (mappedBasis b R).ind.injective _ (uniformMass_pos n) (uniformMass_sum n))
    (referenceScale n) (referenceScale_pos n).le
    (by intro i j hij;simpa only [Nat.cast_add,Nat.cast_ofNat,div_div,mul_comm] using hw i j hij)
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

theorem refined_psd_ray_tangent_gap (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (radius coefficient:ℝ) (hradius:0<radius) (hcoef:0≤ coefficient)
    (hcurv:∀C H:FSC.Coord d→L[ℝ]FSC.Coord d,C∈pdCone →
      operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d))≤radius →
      H.toLinearMap.IsSymmetric →
      deriv (deriv (fun t:ℝ=>operatorValue b p (C+t • H))) 0≤-coefficient*refinedStrain b H)
    (K:FSC.Coord d→L[ℝ]FSC.Coord d) (hK:K∈psdCone)
    (he:0<operatorHilbertSchmidt (K-ContinuousLinearMap.id ℝ (FSC.Coord d))) :
    coefficient*refinedStrain b (K-ContinuousLinearMap.id ℝ (FSC.Coord d))/4*
      min 1 (radius/operatorHilbertSchmidt (K-ContinuousLinearMap.id ℝ (FSC.Coord d))) ≤
      operatorValue b p (ContinuousLinearMap.id ℝ (FSC.Coord d))+
        deriv (covarianceRayValue b p K) 0-operatorValue b p K := by
  let I:=ContinuousLinearMap.id ℝ (FSC.Coord d)
  let E:=K-I
  let e:=operatorHilbertSchmidt E
  let s:=min (1/2:ℝ) (radius/e)
  have hepos:0<e:=he
  have hratio:0<radius/e:=div_pos hradius hepos
  have hspos:0<s:=lt_min (by norm_num) hratio
  have hshalf:s≤1/2:=min_le_left _ _
  have hs1:s≤1:=by linarith
  have hE:E.toLinearMap.IsSymmetric:=hK.1.sub identity_positive.1
  have hcont:ContinuousOn (covarianceRayValue b p K) (Icc (0:ℝ) s):=
    (covarianceRayValue_continuousOn b p hp hs K hK).mono
      (fun t ht=>⟨ht.1,ht.2.trans hs1⟩)
  have hzero:covarianceRay K 0=I:=by
    apply ContinuousLinearMap.ext
    intro x
    simp [covarianceRay,I]
  have hone:covarianceRay K 1=K:=by unfold covarianceRay;module
  obtain ⟨a0,q0,hfirst0,_,_⟩:=exists_line_derivatives b p hp hs I E hE 0 (by
    change covarianceRay K 0∈pdCone
    rw [hzero]
    exact identity_positive)
  have hd0:HasDerivAt (covarianceRayValue b p K) (deriv (covarianceRayValue b p K) 0) 0:=
    hfirst0.differentiableAt.hasDerivAt
  have hj:∀t∈Ioo (0:ℝ) s,∃q:ℝ,DifferentiableAt ℝ (covarianceRayValue b p K) t ∧
      HasDerivAt (deriv (covarianceRayValue b p K)) q t ∧ q≤-(coefficient*refinedStrain b E):=by
    intro t ht
    have ht1:t<1:=lt_of_lt_of_le ht.2 hs1
    have hpd:covarianceRay K t∈pdCone:=covarianceRay_positive K hK t ht.1.le ht1
    obtain ⟨a,q,hfirst,hsecond,_⟩:=exists_line_derivatives b p hp hs I E hE t hpd
    have hnorm:operatorHilbertSchmidt (covarianceRay K t-I)≤ radius:=by
      have hh:covarianceRay K t-I=t • E:=by dsimp [covarianceRay,I,E];abel
      rw [hh,operatorHilbertSchmidt_smul,abs_of_nonneg ht.1.le]
      exact (le_div_iff₀ hepos).mp (ht.2.le.trans (min_le_right _ _))
    have hbound:=hcurv (covarianceRay K t) E hpd hnorm hE
    have hshift:(fun u:ℝ=>operatorValue b p (covarianceRay K t+u • E))=
        (fun u:ℝ=>covarianceRayValue b p K (t+u)):=by
      funext u
      unfold covarianceRayValue covarianceRay
      congr 1
      dsimp [E,I]
      module
    rw [hshift,second_deriv_const_add] at hbound
    have hqeq:deriv (deriv (covarianceRayValue b p K)) t=q:=hsecond.deriv
    rw [hqeq] at hbound
    exact ⟨q,hfirst.differentiableAt,hsecond,by dsimp only [E] at *;linarith⟩
  have hgap:=concave_ray_gap (covarianceRayValue b p K) _ (coefficient*refinedStrain b E) s hspos hs1
    (covarianceRayValue_concaveOn b p hp hs K hK) hd0 hcont hj
  have hmin:min (1:ℝ) (radius/e)≤2*s:=by
    by_cases hh:radius/e≤1/2
    · rw [show s=radius/e from min_eq_right hh]
      have hm:=min_le_right (1:ℝ) (radius/e)
      linarith
    · rw [show s=(1/2:ℝ) from min_eq_left (not_le.mp hh).le]
      have hm:=min_le_left (1:ℝ) (radius/e)
      linarith
  have hmul:=mul_le_mul_of_nonneg_left hmin (mul_nonneg hcoef (refinedStrain_nonneg b E))
  have hout:coefficient*refinedStrain b E/4*min 1 (radius/e)≤
      covarianceRayValue b p K 0+deriv (covarianceRayValue b p K) 0-covarianceRayValue b p K 1:=by
    nlinarith
  simpa only [covarianceRayValue,hzero,hone] using hout


/-- Actual regular covariance deficit with the diagonal strain retained.
This includes singular endpoints and zero covariance defect. It has no
assumed local curvature, facet weight, or second derivative estimate. -/
theorem regular_deficit_refined_ray_bound {n : ℕ} (hn : 0<n)
    (hmean : 1 ≤ maximumMean n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (hb : ∑i,b i=0)
    (hP : ∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hG : ∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (B : Fin (n+2)→FSC.Coord e) (hB : ∑i,B i=0) :
    let E:=normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d)
    (referenceScale n)^2*refinedStrain b E/(48*((n:ℝ)+2))*
      min 1 ((facetRadius 64/(1+Real.log ((n:ℝ)+2)))/operatorHilbertSchmidt E) ≤
      regularCovarianceDeficit n B := by
  intro E
  have hzero (h : operatorHilbertSchmidt E=0) : refinedStrain b E=0 := by
    have he : E=0:=(operatorHilbertSchmidt_eq_zero_iff E).mp h
    rw [he]
    simp only [refinedStrain,ContinuousLinearMap.zero_apply,inner_zero_right,zero_pow (by decide : 2≠0),
      Finset.sum_const_zero,mul_zero,zero_div,add_zero]
    exact sq_eq_zero_iff.mpr ((operatorHilbertSchmidt_eq_zero_iff _).mpr rfl)
  by_cases hz : operatorHilbertSchmidt E=0
  · rw [hzero hz]
    simpa using regularCovarianceDeficit_nonneg hn B hB
  have hpos : 0<operatorHilbertSchmidt E:=
    lt_of_le_of_ne (operatorHilbertSchmidt_nonneg E) (Ne.symm hz)
  have hL : 0<1+Real.log ((n:ℝ)+2):=by
    have hh:=Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    linarith
  have hh:=refined_psd_ray_tangent_gap b (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
    (facetRadius 64/(1+Real.log ((n:ℝ)+2))) (referenceScale n/(12*((n:ℝ)+2)))
    (div_pos (facetRadius_bounds 64 (by norm_num)).1 hL) (by positivity [referenceScale_pos n])
    (fun C H hC hnear hH=>uniform_refined_curvature hn hmean b hb hP hG C H hC hnear hH)
    (normalizedRowCovariance n b B) (normalizedRowCovariance_psd b B) hpos
  have hmul:=mul_le_mul_of_nonneg_left hh (referenceScale_pos n).le
  rw [regularCovarianceDeficit_eq_scaled_tangent hn b hG hP B hB]
  convert hmul using 1 <;> dsimp only [E] <;> field_simp <;> ring

end NegativeVotingStrongDiagonalCurvature
