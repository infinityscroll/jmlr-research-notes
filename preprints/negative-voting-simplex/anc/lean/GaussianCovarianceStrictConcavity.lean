import GaussianCovarianceConcavity

/-! Strict covariance curvature from the actual normal edge strain. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Matrix Matrix.Norms.L2Operator
namespace NegativeVotingCovarianceStrict
open NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity
  NegativeVotingFanCovarianceValue NegativeVotingCovarianceRefinement
  NegativeVotingFanCycleHessian NegativeVotingFanCovarianceEnvelope
  NegativeVotingFanEnvelope NegativeVotingCovariancePath NegativeVotingFanCycle

section Polarization
variable {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype V] [DecidableEq V] [Nonempty V]

/-- Quadratic values on every edge of an affine basis determine a symmetric operator. -/
theorem symmetric_eq_zero_of_edge_quadratics (b : AffineBasis V ℝ E)
    (H : E →L[ℝ] E) (hH:H.toLinearMap.IsSymmetric)
    (hz:∀ i j,inner ℝ (b i-b j) (H (b i-b j))=0) : H=0 := by
  classical
  let a : V := Classical.choice inferInstance
  let e := b.basisOf a
  have hcross (i j : {i:V // i≠a}) : inner ℝ (e i) (H (e j))=0 := by
    have hi := hz i.val a
    have hj := hz j.val a
    have hij := hz i.val j.val
    have hdiagI : inner ℝ (e i) (H (e i))=0 := by simpa [e] using hi
    have hdiagJ : inner ℝ (e j) (H (e j))=0 := by simpa [e] using hj
    have hsub : e i-e j=b i.val-b j.val := by simp [e]
    have hdiagSub : inner ℝ (e i-e j) (H (e i-e j))=0 := by rw [hsub];exact hij
    have hsym : inner ℝ (e j) (H (e i))=inner ℝ (e i) (H (e j)) :=
      (real_inner_comm _ _).trans (hH _ _)
    rw [map_sub,inner_sub_left,inner_sub_right,inner_sub_right,hdiagI,hdiagJ,hsym] at hdiagSub
    linarith
  have hlin : H.toLinearMap=0 := by
    apply e.ext
    intro j
    have hform : (innerSL ℝ (H (e j))).toLinearMap=0 := by
      apply e.ext
      intro i
      change inner ℝ (H (e j)) (e i)=0
      rw [real_inner_comm]
      exact hcross i j
    have hv : inner ℝ (H (e j)) (H (e j))=0 :=
      LinearMap.congr_fun hform (H (e j))
    exact inner_self_eq_zero.mp hv
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun hlin x
end Polarization

variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Actual positive Gaussian facet weights make zero normal strain rigid. -/
theorem normalEdgeEnergy_eq_zero_iff (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH:H.toLinearMap.IsSymmetric) :
    normalEdgeEnergy b h (rowsOfOperator b H)=0 ↔ H=0 := by
  constructor
  · intro he
    apply symmetric_eq_zero_of_edge_quadratics b H hH
    have hs : (∑ i,∑ j,cycleEdgeWeight b h i j*
        ‖(faceDirection b {i,j}).starProjection (H (b i)-H (b j))‖^2)=0 := by
      change (1/2:ℝ)*(∑ i,∑ j,cycleEdgeWeight b h i j*
        ‖(faceDirection b {i,j}).starProjection (H (b i)-H (b j))‖^2)=0 at he
      linarith
    have hnon (i j:V) : 0≤cycleEdgeWeight b h i j*
        ‖(faceDirection b {i,j}).starProjection (H (b i)-H (b j))‖^2 :=
      mul_nonneg (cycleEdgeWeight_pos b h i j).le (sq_nonneg _)
    intro i j
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_:i∈Finset.univ) => Finset.sum_nonneg (fun j _=>hnon i j))).mp hs i (Finset.mem_univ _)
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_:j∈Finset.univ) => hnon i j)).mp hrow j (Finset.mem_univ _)
    have hproj : (faceDirection b {i,j}).starProjection (H (b i)-H (b j))=0 := by
      apply norm_eq_zero.mp
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp ht).resolve_left (cycleEdgeWeight_pos b h i j).ne')
    have hmem : b i-b j∈faceDirection b {i,j} := by
      exact vsub_mem_vectorSpan ℝ (mem_image_of_mem b (by simp)) (mem_image_of_mem b (by simp))
    have hi := (faceDirection b {i,j}).starProjection_inner_eq_zero
      (H (b i)-H (b j)) (b i-b j) hmem
    rw [hproj,sub_zero] at hi
    rw [map_sub,real_inner_comm]
    exact hi
  · rintro rfl
    simp [normalEdgeEnergy,rowsOfOperator]

theorem normalEdgeEnergy_pos (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (hH:H.toLinearMap.IsSymmetric) (hH0:H≠0) :
    0<normalEdgeEnergy b h (rowsOfOperator b H) := by
  have hn := normalEdgeEnergy_nonneg b h (rowsOfOperator b H)
  have he : normalEdgeEnergy b h (rowsOfOperator b H)≠0 := by
    intro he
    exact hH0 ((normalEdgeEnergy_eq_zero_iff b h H hH).mp he)
  exact lt_of_le_of_ne hn (Ne.symm he)


variable {m : ℕ} [NeZero m]

/-- Every nonzero symmetric direction has a genuinely negative actual second derivative. -/
theorem exists_derivatives_positive_strict (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp:∀ i,0<p i) (hs:∑ i,p i=1)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d) (hC:C∈pdCone)
    (hD:D.toLinearMap.IsSymmetric) (hD0:D≠0) :
    ∃ a q:ℝ, HasDerivAt (fun t:ℝ=>operatorValue b p (C+t•D)) a 0 ∧
      HasDerivAt (deriv (fun t:ℝ=>operatorValue b p (C+t•D))) q 0 ∧ q<0 := by
  obtain ⟨R,hR,hRi,hRR⟩ := exists_positive_factor C hC
  let H := R.symm.toContinuousLinearMap.comp (D.comp R.symm.toContinuousLinearMap)
  have hH : H.toLinearMap.IsSymmetric := symmetric_conjugate _ _ hRi hD
  have hH0 : H≠0 := by
    intro he
    apply hD0
    apply ContinuousLinearMap.ext
    intro x
    have hh := congrArg (fun T:FSC.Coord d →L[ℝ] FSC.Coord d => R (T (R x))) he
    simpa [H,ContinuousLinearMap.comp_apply] using hh
  obtain ⟨h₀,hm,hd,hd2,hq⟩ := exists_actual_covariance_derivatives (mappedBasis b R) p hp hs H hH
  have heq : (fun t:ℝ=>operatorValue b p (C+t•D))=
      (fun t:ℝ=>covarianceValue
        (Matrix.gram ℝ (mappedBasis b R)+t•gramVelocity (mappedBasis b R) H) p) := by
    funext t
    unfold operatorValue
    rw [gramVelocity_add_smul]
    congr 1
    have hG := factor_gram b C R hR hRR
    have hV := conjugate_gramVelocity b D R hR
    change Matrix.gram ℝ (mappedBasis b R)=gramVelocity b C at hG
    change gramVelocity (mappedBasis b R) H=gramVelocity b D at hV
    rw [hG,hV]
  rw [heq]
  refine ⟨_,_,hd,hd2,?_⟩
  have hn := normalEdgeEnergy_pos (mappedBasis b R) h₀ H hH hH0
  linarith

theorem exists_line_derivatives_strict (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp:∀ i,0<p i) (hs:∑ i,p i=1)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d) (hD:D.toLinearMap.IsSymmetric) (hD0:D≠0)
    (t:ℝ) (ht:C+t•D∈pdCone) :
    ∃ a q:ℝ, HasDerivAt (fun u:ℝ=>operatorValue b p (C+u•D)) a t ∧
      HasDerivAt (deriv (fun u:ℝ=>operatorValue b p (C+u•D))) q t ∧ q<0 := by
  obtain ⟨a,q,ha,hq,hq0⟩ := exists_derivatives_positive_strict b p hp hs (C+t•D) D ht hD hD0
  have heq : (fun s:ℝ=>operatorValue b p (C+t•D+s•D))=
      (fun s:ℝ=>operatorValue b p (C+(t+s)•D)) := by
    funext s
    congr 1
    module
  rw [heq] at ha hq
  have hder : deriv (fun s:ℝ=>operatorValue b p (C+(t+s)•D))=
      (fun s:ℝ=>deriv (fun u:ℝ=>operatorValue b p (C+u•D)) (t+s)) := by
    funext s
    exact deriv_comp_const_add (fun u:ℝ=>operatorValue b p (C+u•D)) t s
  rw [hder] at hq
  exact ⟨a,q,hasDerivAt_of_const_add_zero t a ha,hasDerivAt_of_const_add_zero t q hq,hq0⟩

theorem operatorValue_segment_strictConcave (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp:∀ i,0<p i) (hs:∑ i,p i=1)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d) (hC:C∈pdCone) (hD:D∈pdCone) (hCD:C≠D) :
    StrictConcaveOn ℝ (Icc (0:ℝ) 1) (fun t:ℝ=>operatorValue b p (C+t•(D-C))) := by
  have hsegment (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : C+t•(D-C)∈pdCone := by
    have heq : C+t•(D-C)=(1-t)•C+t•D := by module
    rw [heq]
    exact pdCone_convex hC hD (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hcont : ContinuousOn (fun t:ℝ=>operatorValue b p (C+t•(D-C))) (Icc 0 1) :=
    (operatorValue_continuousOn b p (fun i=>(hp i).le) hs).comp
      (by fun_prop) (fun t ht=>pdCone_subset_psdCone (hsegment t ht))
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) hcont
  intro t ht
  obtain ⟨a,q,ha,hq,hq0⟩ := exists_line_derivatives_strict b p hp hs C (D-C)
    (hD.1.sub hC.1) (sub_ne_zero.mpr (Ne.symm hCD)) t (hsegment t (interior_subset ht))
  simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply,hq.deriv] using hq0

/-- Global strict concavity for the actual optimized covariance value on the positive cone. -/
theorem operatorValue_strictConcaveOn_positive (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp:∀ i,0<p i) (hs:∑ i,p i=1) :
    StrictConcaveOn ℝ pdCone (operatorValue b p) := by
  refine ⟨pdCone_convex,?_⟩
  intro C hC D hD hCD a c ha hc hac
  have hh := (operatorValue_segment_strictConcave b p hp hs C D hC hD hCD).2
    (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ)∈Icc 0 1 by constructor <;> norm_num) (by norm_num) ha hc hac
  have heq : C+c•(D-C)=a•C+c•D := by
    have ha' : a=1-c := by linarith
    rw [ha']
    module
  simp only [one_smul,zero_add,add_sub_cancel,smul_eq_mul,mul_zero,mul_one,heq] at hh
  have hz : (0:ℝ)•(D-C)=0 := by ext x; simp
  rw [hz,add_zero] at hh
  simpa only [smul_eq_mul] using hh

/-- The actual penalized objective. Its trace is operator trace; identifying
it with row-energy trace requires a Parseval simplex frame separately. -/
def penalizedValue (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p:Fin m→ℝ)
    (C:FSC.Coord d →L[ℝ] FSC.Coord d) : ℝ :=
  2*operatorValue b p C-LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap

theorem penalizedValue_strictConcaveOn_positive (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp:∀ i,0<p i) (hs:∑ i,p i=1) :
    StrictConcaveOn ℝ pdCone (penalizedValue b p) := by
  refine ⟨pdCone_convex,?_⟩
  intro C hC D hD hCD a c ha hc hac
  have hh := (operatorValue_strictConcaveOn_positive b p hp hs).2 hC hD hCD ha hc hac
  simp only [smul_eq_mul] at hh
  have htr : LinearMap.trace ℝ (FSC.Coord d) (a•C+c•D).toLinearMap=
      a*LinearMap.trace ℝ (FSC.Coord d) C.toLinearMap+
      c*LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap := by
    change LinearMap.trace ℝ (FSC.Coord d) (a•C.toLinearMap+c•D.toLinearMap)=_
    simp only [map_add,map_smul,smul_eq_mul]
  simp only [penalizedValue,smul_eq_mul,htr]
  nlinarith

end NegativeVotingCovarianceStrict
