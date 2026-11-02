import GaussianPositiveCovarianceFactor
import GaussianCovarianceRefinedCurvature

/-! Global covariance concavity from the actual Gaussian first and second derivatives. -/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace Matrix Matrix.Norms.L2Operator
namespace NegativeVotingCovarianceConcavity
open NegativeVotingPositiveCovariance NegativeVotingFanCovarianceValue
  NegativeVotingCovarianceRefinement NegativeVotingFanCycleHessian
  NegativeVotingFanCovarianceEnvelope NegativeVotingFanEnvelope
  NegativeVotingCovariancePath
variable {m d : ℕ} [NeZero m]

/-- The covariance functional is evaluated on its literal Gaussian Gram matrix. -/
def operatorValue (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m → ℝ)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) : ℝ := covarianceValue (gramVelocity b C) p

theorem continuous_gramVelocity (B : Fin m → FSC.Coord d) :
    Continuous (fun C : FSC.Coord d →L[ℝ] FSC.Coord d => gramVelocity B C) := by
  unfold gramVelocity
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fun_prop

theorem operatorValue_continuousOn (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1) :
    ContinuousOn (operatorValue b p) psdCone := by
  exact (covarianceValue_continuousOn p hp hs).comp
    (continuous_gramVelocity b).continuousOn (fun C hC => gramVelocity_posSemidef b C hC)

theorem gramVelocity_add_smul (B : Fin m → FSC.Coord d)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d) (t : ℝ) :
    gramVelocity B (C+t•D)=gramVelocity B C+t•gramVelocity B D := by
  ext i j
  simp [gramVelocity,inner_add_right,real_inner_smul_right]

/-- Both actual derivatives exist at every positive covariance, in every
symmetric direction; the second derivative is nonpositive. -/
theorem exists_derivatives_positive (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d) (hC:C∈pdCone)
    (hD:D.toLinearMap.IsSymmetric) :
    ∃ a q : ℝ, HasDerivAt (fun t : ℝ => operatorValue b p (C+t•D)) a 0 ∧
      HasDerivAt (deriv (fun t : ℝ => operatorValue b p (C+t•D))) q 0 ∧ q≤0 := by
  obtain ⟨R,hR,hRi,hRR⟩ := exists_positive_factor C hC
  let H := R.symm.toContinuousLinearMap.comp (D.comp R.symm.toContinuousLinearMap)
  have hH : H.toLinearMap.IsSymmetric := symmetric_conjugate _ _ hRi hD
  obtain ⟨h₀,hm,hd,hd2,hq⟩ := exists_actual_covariance_derivatives (mappedBasis b R) p hp hs H hH
  have heq : (fun t : ℝ => operatorValue b p (C+t•D)) =
      (fun t : ℝ => covarianceValue
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
  have hn := normalEdgeEnergy_nonneg (mappedBasis b R) h₀
    (rowsOfOperator (mappedBasis b R) H)
  linarith

theorem hasDerivAt_of_const_add_zero {f : ℝ → ℝ} (t a : ℝ)
    (h : HasDerivAt (fun s => f (t+s)) a 0) : HasDerivAt f a t := by
  have h' : HasDerivAt (fun s => f (t+s)) a (t-t) := by simpa using h
  have hh := h'.comp_sub_const t t
  have heq : (fun u : ℝ => f (t+(u-t)))=f := by
    funext u
    congr 1
    ring
  simpa only [heq] using hh

/-- The shifted line has genuine first and second derivatives at its base point. -/
theorem exists_line_derivatives (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d) (hD:D.toLinearMap.IsSymmetric)
    (t : ℝ) (ht:C+t•D∈pdCone) :
    ∃ a q : ℝ, HasDerivAt (fun u : ℝ => operatorValue b p (C+u•D)) a t ∧
      HasDerivAt (deriv (fun u : ℝ => operatorValue b p (C+u•D))) q t ∧ q≤0 := by
  obtain ⟨a,q,ha,hq,hq0⟩ := exists_derivatives_positive b p hp hs (C+t•D) D ht hD
  have heq : (fun s : ℝ => operatorValue b p (C+t•D+s•D))=
      (fun s : ℝ => operatorValue b p (C+(t+s)•D)) := by
    funext s
    congr 1
    module
  rw [heq] at ha hq
  have hder : deriv (fun s : ℝ => operatorValue b p (C+(t+s)•D))=
      (fun s : ℝ => deriv (fun u : ℝ => operatorValue b p (C+u•D)) (t+s)) := by
    funext s
    exact deriv_comp_const_add (fun u : ℝ => operatorValue b p (C+u•D)) t s
  rw [hder] at hq
  exact ⟨a,q,hasDerivAt_of_const_add_zero t a ha,
    hasDerivAt_of_const_add_zero t q hq,hq0⟩

theorem operatorValue_segment_concave (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d) (hC:C∈pdCone) (hD:D∈pdCone) :
    ConcaveOn ℝ (Icc (0:ℝ) 1) (fun t : ℝ => operatorValue b p (C+t•(D-C))) := by
  have hsegment (t : ℝ) (ht:t∈Icc (0:ℝ) 1) : C+t•(D-C)∈pdCone := by
    have heq : C+t•(D-C)=(1-t)•C+t•D := by module
    rw [heq]
    exact pdCone_convex hC hD (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hcont : ContinuousOn (fun t : ℝ => operatorValue b p (C+t•(D-C))) (Icc 0 1) :=
    (operatorValue_continuousOn b p (fun i => (hp i).le) hs).comp
      (by fun_prop) (fun t ht => pdCone_subset_psdCone (hsegment t ht))
  have hjet (t : ℝ) (ht:t∈interior (Icc (0:ℝ) 1)) :
      ∃ a q : ℝ, HasDerivAt (fun u : ℝ => operatorValue b p (C+u•(D-C))) a t ∧
        HasDerivAt (deriv (fun u : ℝ => operatorValue b p (C+u•(D-C)))) q t ∧ q≤0 :=
    exists_line_derivatives b p hp hs C (D-C) (hD.1.sub hC.1) t
      (hsegment t (interior_subset ht))
  apply concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hcont
  · intro t ht
    obtain ⟨a,q,ha,hq,hq0⟩ := hjet t ht
    exact ha.differentiableAt.differentiableWithinAt
  · intro t ht
    obtain ⟨a,q,ha,hq,hq0⟩ := hjet t ht
    exact hq.differentiableAt.differentiableWithinAt
  · intro t ht
    obtain ⟨a,q,ha,hq,hq0⟩ := hjet t ht
    simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply, hq.deriv] using hq0

theorem operatorValue_concaveOn_positive (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ConcaveOn ℝ pdCone (operatorValue b p) := by
  refine ⟨pdCone_convex,?_⟩
  intro C hC D hD a c ha hc hac
  have hh := (operatorValue_segment_concave b p hp hs C D hC hD).2
    (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ)∈Icc 0 1 by constructor <;> norm_num) ha hc hac
  have heq : C+c•(D-C)=a•C+c•D := by
    have ha' : a=1-c := by linarith
    rw [ha']
    module
  simp only [zero_smul,one_smul,add_zero,zero_add,add_sub_cancel,
    smul_eq_mul,mul_zero,mul_one,heq] at hh
  have hz : (0:ℝ)•(D-C)=0 := by ext x; simp
  rw [hz,add_zero] at hh
  simpa only [smul_eq_mul] using hh


/-- The literal covariance value converges under positive regularization,
including at singular and zero covariance operators. -/
theorem operatorValue_regularization_tendsto
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC:C∈psdCone) :
    Tendsto (fun ε : ℝ => operatorValue b p (C+ε•ContinuousLinearMap.id ℝ (FSC.Coord d)))
      (𝓝[>] 0) (𝓝 (operatorValue b p C)) := by
  have hlin : Tendsto (fun ε : ℝ => C+ε•ContinuousLinearMap.id ℝ (FSC.Coord d))
      (𝓝[>] 0) (𝓝 C) := by
    have hh : Continuous (fun ε : ℝ => C+ε•ContinuousLinearMap.id ℝ (FSC.Coord d)) := by
      fun_prop
    have hT := (hh.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds : (𝓝[>] (0:ℝ)) ≤ 𝓝 0)
    have hz : C+(0:ℝ)•ContinuousLinearMap.id ℝ (FSC.Coord d)=C := by ext x; simp
    rw [hz] at hT
    exact hT
  have hwithin : Tendsto (fun ε : ℝ => C+ε•ContinuousLinearMap.id ℝ (FSC.Coord d))
      (𝓝[>] 0) (𝓝[psdCone] C) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hlin,?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pdCone_subset_psdCone (regularize_positive hC hε)
  exact ((operatorValue_continuousOn b p hp hs) C hC).tendsto.comp hwithin

/-- Actual global covariance concavity on the entire positive-semidefinite cone.
The boundary case is obtained from the proved covariance-value continuity,
not from an assumed differentiability statement at rank loss. -/
theorem operatorValue_concaveOn_psd (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    ConcaveOn ℝ psdCone (operatorValue b p) := by
  refine ⟨psdCone_convex,?_⟩
  intro C hC D hD a c ha hc hac
  have hE : a•C+c•D∈psdCone := psdCone_convex hC hD ha hc hac
  have hlimC := operatorValue_regularization_tendsto b p (fun i => (hp i).le) hs C hC
  have hlimD := operatorValue_regularization_tendsto b p (fun i => (hp i).le) hs D hD
  have hlimE := operatorValue_regularization_tendsto b p (fun i => (hp i).le) hs (a•C+c•D) hE
  have hineq : (fun ε : ℝ => a*operatorValue b p (C+ε•ContinuousLinearMap.id ℝ (FSC.Coord d))+
      c*operatorValue b p (D+ε•ContinuousLinearMap.id ℝ (FSC.Coord d))) ≤ᶠ[𝓝[>] 0]
      (fun ε : ℝ => operatorValue b p (a•C+c•D+ε•ContinuousLinearMap.id ℝ (FSC.Coord d))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hh := (operatorValue_concaveOn_positive b p hp hs).2
      (regularize_positive hC hε) (regularize_positive hD hε) ha hc hac
    have heq : a•(C+ε•ContinuousLinearMap.id ℝ (FSC.Coord d))+
        c•(D+ε•ContinuousLinearMap.id ℝ (FSC.Coord d))=
        a•C+c•D+ε•ContinuousLinearMap.id ℝ (FSC.Coord d) := by
      have ha' : a=1-c := by linarith
      rw [ha']
      module
    simpa only [smul_eq_mul,heq] using hh
  exact le_of_tendsto_of_tendsto ((hlimC.const_mul a).add (hlimD.const_mul c)) hlimE hineq

end NegativeVotingCovarianceConcavity
