import GaussianBoundedRowGap
import GaussianCovarianceMixedEstimate
import GaussianLocalCurvatureAlgebra

/-! A dimension-free one-row curvature estimate using the proved Gaussian
Cheeger bound. The coefficient is weaker than the sharp isoperimetric
profile. No covariance-ray symmetrization or final row-exclusion estimate is
assumed by these actual facet/Hessian inequalities. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical RealInnerProductSpace
namespace NegativeVotingOneRowCurvature
open NegativeVoting NegativeVotingFan NegativeVotingFanScore NegativeVotingFanJacobian
  NegativeVotingBoundedRowGap NegativeVotingFiniteGraph NegativeVotingFanCycle
  NegativeVotingFanCycleBridge NegativeVotingFanCycleHessian NegativeVotingCovarianceMixed
  NegativeVotingFanCovarianceEnvelope NegativeVotingCapTail NegativeVotingAffineBasisLower
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceRefinement NegativeVotingCovariancePath
  NegativeVotingPositiveCovariance NegativeVotingFanCovarianceValue NegativeVotingLocalCurvatureAlgebra
  NegativeVotingFanInverse
variable {m d:ℕ} [NeZero m]

theorem singleton_surface_lower (hm:2≤ m) (B:Fin m→FSC.Coord d) (h:Fin m→ℝ)
    (hinj:Function.Injective B) (p:ℝ) (hp:0≤p) (hmass:∀ j,p≤ mass B h j) (i:Fin m) :
    p≤2*Real.pi*(∑ j,‖B i-B j‖*facetWeight B h i j) := by
  have hh:=physical_cut_expansion B h hinj p hp hmass ({i}:Finset (Fin m))
  have hc : (({i}:Finset (Fin m))ᶜ.card:ℝ)=(m:ℝ)-1 := by
    simp only [Finset.card_compl,Finset.card_singleton,Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1≤ m)]
    simp
  simp only [Finset.card_singleton,Nat.cast_one,hc] at hh
  have hm1 : (1:ℝ)≤(m:ℝ)-1 := by
    have hh : (2:ℝ)≤ m := by exact_mod_cast hm
    linarith
  rw [min_eq_left hm1,mul_one,cutWeight,Finset.sum_singleton] at hh
  have hs : (∑ j∈({i}:Finset (Fin m))ᶜ,‖B i-B j‖*facetWeight B h i j)≤
      ∑ j,‖B i-B j‖*facetWeight B h i j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _=>mul_nonneg (norm_nonneg _) (facetWeight_nonneg B h i j))
  exact (div_le_iff₀ (show 0<2*Real.pi by positivity)).mp (hh.trans hs) |>.trans_eq (by ring)

theorem singleton_degree_lower (hm:2≤ m) (B:Fin m→FSC.Coord d) (h:Fin m→ℝ)
    (hinj:Function.Injective B) (p:ℝ) (hp:0≤p) (hmass:∀ j,p≤ mass B h j)
    (i:Fin m) (ell:ℝ) (hedge:∀ j,j≠i→‖B i-B j‖=ell) :
    p≤2*Real.pi*ell*(∑ j,facetWeight B h i j) := by
  have hh:=singleton_surface_lower hm B h hinj p hp hmass i
  have he : (∑ j,‖B i-B j‖*facetWeight B h i j)=ell*(∑ j,facetWeight B h i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj:j=i
    · subst j;simp
    · rw [hedge j hj]
  rw [he] at hh
  nlinarith only [hh]

theorem normal_energy_incident_lower (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (h:Fin m→ℝ)
    (H:FSC.Coord d→L[ℝ]FSC.Coord d) (i:Fin m) (ell:ℝ) (hell:0<ell)
    (hedge:∀ j,j≠i→‖b i-b j‖=ell)
    (hstrain:∀ j,j≠i→inner ℝ (b i-b j) (H (b i-b j))=1) :
    (∑ j,facetWeight b h i j)≤2*ell^2*normalEdgeEnergy b h (rowsOfOperator b H) := by
  let e:Fin m→Fin m→ℝ:=fun a j=>cycleEdgeWeight b h a j*
    ‖(faceDirection b {a,j}).starProjection (rowsOfOperator b H a-rowsOfOperator b H j)‖^2
  have he0 a j : 0≤e a j := mul_nonneg (cycleEdgeWeight_pos b h a j).le (sq_nonneg _)
  have hs : (∑ j,e i j)≤∑ a,∑ j,e a j :=
    Finset.single_le_sum (fun a _=>Finset.sum_nonneg (fun j _=>he0 a j)) (Finset.mem_univ i)
  have he j : e i j=facetWeight b h i j/ell^2 := by
    by_cases hj:j=i
    · subst j;simp [e]
    · dsimp [e]
      rw [cycleEdgeWeight_eq_facetWeight b h i j (Ne.symm hj),normal_projection_pair_sq b i j (Ne.symm hj)]
      simp only [rowsOfOperator_apply,←map_sub,pairNormal,real_inner_smul_left,hedge j hj,hstrain j hj,mul_one]
      ring
  simp_rw [he] at hs
  rw [←Finset.sum_div] at hs
  have hh: (∑ j,facetWeight b h i j)≤(∑ a,∑ j,e a j)*ell^2 :=
    (div_le_iff₀ (sq_pos_of_pos hell)).mp hs
  change _≤2*ell^2*((1/2:ℝ)*(∑ a,∑ j,e a j))
  nlinarith only [hh]

/-- Actual one-row curvature. A constant incident strain of one and incident
length ell give a coefficient p/(16*pi*ell^3), using only Gaussian Cheeger.
The unused opposite oriented edges make the numerical factor conservative. -/
theorem covarianceHessianValue_one_row_le (hm:2≤ m)
    (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (h:Fin m→ℝ)
    (H:FSC.Coord d→L[ℝ]FSC.Coord d) (i:Fin m) (ell:ℝ) (hell:0<ell)
    (hedge:∀ j,j≠i→‖b i-b j‖=ell)
    (hstrain:∀ j,j≠i→inner ℝ (b i-b j) (H (b i-b j))=1)
    (p:ℝ) (hp:0≤p) (hmass:∀ j,p≤ mass b h j) :
    covarianceHessianValue b h H≤-p/(16*Real.pi*ell^3) := by
  obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound b
  have hh:=covarianceHessianValue_le_normal_energy b h σ hσ hlower H
  have hn:=normal_energy_incident_lower b h H i ell hell hedge hstrain
  have hd:=singleton_degree_lower hm b h b.ind.injective p hp hmass i ell hedge
  have hh':=mul_le_mul_of_nonneg_left hh (show 0≤16*Real.pi*ell^3 by positivity)
  have hn':=mul_le_mul_of_nonneg_left hn (show 0≤2*Real.pi*ell by positivity)
  apply (le_div_iff₀ (show 0<16*Real.pi*ell^3 by positivity)).mpr
  nlinarith only [hh',hn',hd]

/-- The preceding geometric estimate applies to the actual optimized value
on a positive covariance line. Incident lengths and strains are tested in
the original reference coordinates; the positive factor and balanced fan
are both constructed by the existing covariance differential theorem. -/
theorem exists_one_row_covariance_derivatives (hm:2≤ m)
    (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (p:Fin m→ℝ)
    (hp:∀ j,0<p j) (hs:∑ j,p j=1) (pmin:ℝ) (hpmin:0≤pmin) (hmin:∀ j,pmin≤p j)
    (C D:FSC.Coord d→L[ℝ]FSC.Coord d) (hC:C∈pdCone) (hD:D.toLinearMap.IsSymmetric)
    (i:Fin m) (ell:ℝ) (hell:0<ell)
    (hedge:∀ j,j≠i→inner ℝ (b i-b j) (C (b i-b j))=ell^2)
    (hstrain:∀ j,j≠i→inner ℝ (b i-b j) (D (b i-b j))=1) :
    ∃ a q:ℝ,HasDerivAt (fun t:ℝ=>operatorValue b p (C+t•D)) a 0 ∧
      HasDerivAt (deriv (fun t:ℝ=>operatorValue b p (C+t•D))) q 0 ∧
      q≤-pmin/(16*Real.pi*ell^3) := by
  obtain ⟨R,hR,hRi,hRR⟩:=exists_positive_factor C hC
  let H:=R.symm.toContinuousLinearMap.comp (D.comp R.symm.toContinuousLinearMap)
  have hH:H.toLinearMap.IsSymmetric:=symmetric_conjugate _ _ hRi hD
  obtain ⟨h₀,hmass,hd,hd2,_⟩:=exists_actual_covariance_derivatives (mappedBasis b R) p hp hs H hH
  have hlen j (hj:j≠i) : ‖mappedBasis b R i-mappedBasis b R j‖=ell := by
    have he : ‖R (b i-b j)‖^2=inner ℝ (b i-b j) (C (b i-b j)) := by
      rw [←real_inner_self_eq_norm_sq]
      have hh:=hR (b i-b j) (R (b i-b j))
      change inner ℝ (R (b i-b j)) (R (b i-b j))=
        inner ℝ (b i-b j) (R (R (b i-b j))) at hh
      rw [←hRR]
      exact hh
    rw [hedge j hj] at he
    change ‖R (b i)-R (b j)‖=ell
    rw [←map_sub]
    nlinarith [norm_nonneg (R (b i-b j))]
  have hstrain' j (hj:j≠i) :
      inner ℝ (mappedBasis b R i-mappedBasis b R j)
        (H (mappedBasis b R i-mappedBasis b R j))=1 := by
    change inner ℝ (R (b i)-R (b j)) (H (R (b i)-R (b j)))=1
    rw [←map_sub]
    exact (factor_inner_conjugated R hR D (b i-b j)).trans (hstrain j hj)
  have heq : (fun t:ℝ=>operatorValue b p (C+t•D))=
      (fun t:ℝ=>covarianceValue
        (Matrix.gram ℝ (mappedBasis b R)+t•gramVelocity (mappedBasis b R) H) p) := by
    funext t
    unfold operatorValue
    rw [gramVelocity_add_smul]
    congr 1
    have hG:=factor_gram b C R hR hRR
    have hV:=conjugate_gramVelocity b D R hR
    change Matrix.gram ℝ (mappedBasis b R)=gramVelocity b C at hG
    change gramVelocity (mappedBasis b R) H=gramVelocity b D at hV
    rw [hG,hV]
  rw [heq]
  refine ⟨_,_,hd,hd2,?_⟩
  apply covarianceHessianValue_one_row_le hm (mappedBasis b R) h₀ H i ell hell hlen hstrain' pmin hpmin
  intro j
  simpa only [congrFun hmass j] using hmin j

end NegativeVotingOneRowCurvature
