import GaussianRegularCovarianceDeficit
import GaussianAffineNormControl
import GaussianValueSemiconcavity
import GaussianCovarianceMixedNeighborhood

/-! Propagation of actual local Gaussian covariance curvature along arbitrary
PSD rays, retaining singular endpoints. The quantitative local curvature
hypothesis is explicit until the separate facet-bootstrap module discharges it. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingRayDeficit
open NegativeVoting NegativeVotingFan NegativeVotingFanValue NegativeVotingAssignmentDuality
  NegativeVotingCovarianceRealization NegativeVotingPositiveCovariance
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceStrict
  NegativeVotingBalancedReference NegativeVotingBalancedMaximum
  NegativeVotingRegularCovarianceDeficit NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl NegativeVotingValueSemiconcavity
  NegativeVotingCovarianceMixedNeighborhood NegativeVotingLocalCovarianceFactor
  NegativeVotingFanCovarianceEnvelope NegativeVotingCovarianceRefinement
  NegativeVotingFanScore NegativeVotingFanValueDerivative NegativeVotingCenteredParseval
  NegativeVotingGaussianMaximumMean NegativeVotingFanCovarianceValue
  NegativeVotingCovarianceCoercivity NegativeVotingCapTail
variable {m n d e:ℕ} [NeZero m]

omit [NeZero m] in
/-- A quadratic drop on an initial interval propagates to the entire concave
ray by the chord inequality. No derivative at the far endpoint is needed. -/
theorem concave_ray_gap (f:ℝ→ℝ) (a A s:ℝ) (hs:0<s) (hs1:s≤1)
    (hc:ConcaveOn ℝ (Icc (0:ℝ) 1) f) (h0:HasDerivAt f a 0)
    (hcont:ContinuousOn f (Icc 0 s))
    (hj:∀t∈Ioo (0:ℝ) s,∃q:ℝ,DifferentiableAt ℝ f t ∧
      HasDerivAt (deriv f) q t ∧ q≤-A) :
    A*s/2≤ f 0+a-f 1 := by
  let g:ℝ→ℝ:=fun t=>f t+A/2*t^2
  have hg0:HasDerivAt g a 0:=by
    convert h0.add (((hasDerivAt_id (0:ℝ)).pow 2).const_mul (A/2)) using 1 <;>simp [g,Pi.add_def]
  have hgc:ContinuousOn g (Icc 0 s):=hcont.add
    (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hgd (t:ℝ) (ht:t∈Ioo (0:ℝ) s):DifferentiableAt ℝ g t:=
    (hj t ht).choose_spec.1.add (by fun_prop)
  have hgj (t:ℝ) (ht:t∈Ioo (0:ℝ) s):∃q:ℝ,HasDerivAt (deriv g) q t ∧ q≤0:=by
    obtain ⟨q,hfd,hq,hq0⟩:=hj t ht
    have hnear:∀ᶠ u in 𝓝 t,DifferentiableAt ℝ f u:=by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact (hj u hu).choose_spec.1
    have hh:=line_second_quadratic_penalty (K:=-A) (a:=0) (c:=1) hnear hq
    have heq:(fun u:ℝ=>f u-(-A)/2*((0:ℝ)+u*1)^2)=g:=by funext u;dsimp [g];ring
    rw [heq] at hh
    refine ⟨q+A,?_,by linarith⟩
    convert hh using 1 <;>ring
  have hconc:ConcaveOn ℝ (Icc (0:ℝ) s) g:=by
    apply concaveOn_of_deriv2_nonpos (convex_Icc 0 s) hgc
    · intro t ht
      exact (hgd t (by simpa only [interior_Icc] using ht)).differentiableWithinAt
    · intro t ht
      exact (hgj t (by simpa only [interior_Icc] using ht)).choose_spec.1.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨q,hq,hq0⟩:=hgj t (by simpa only [interior_Icc] using ht)
      simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply,Function.comp_def,hq.deriv] using hq0
  have hsl:=hconc.slope_le_of_hasDerivAt (show (0:ℝ)∈Icc 0 s by exact ⟨le_rfl,hs.le⟩)
    (show s∈Icc 0 s from ⟨hs.le,le_rfl⟩) hs hg0
  simp only [slope_def_field,sub_zero,g,zero_pow (by decide : 2≠0),mul_zero,add_zero] at hsl
  have hlocal: f s+A/2*s^2-f 0≤ a*s:=(div_le_iff₀ hs).mp hsl
  have hchord:=hc.2 (show (0:ℝ)∈Icc 0 1 by constructor <;>norm_num)
    (show (1:ℝ)∈Icc 0 1 by constructor <;>norm_num) (sub_nonneg.mpr hs1) hs.le
    (show (1-s)+s=1 by ring)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add] at hchord
  apply (mul_le_mul_iff_right₀ hs).mp
  nlinarith

theorem assignmentValue_smul_rows (B:Fin m→FSC.Coord d)
    (f:FSC.Coord d→Fin m→ℝ) (a:ℝ) :
    assignmentValue (fun i=>a • B i) f=a*assignmentValue B f := by
  unfold assignmentValue
  simp only [real_inner_smul_right,real_inner_smul_left]
  have he:(fun x:FSC.Coord d=>∑i,f x i*(a*inner ℝ (B i) x))=
      (fun x=>a*∑i,f x i*inner ℝ (B i) x):=by
    funext x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,integral_const_mul]

/-- Positive homogeneity is derived from actual attained assignment duality,
so duplicate rows and rank loss are included. -/
theorem optimizedValue_smul_rows (B:Fin m→FSC.Coord d) (p:Fin m→ℝ)
    (hp:∀i,0<p i) (hs:∑i,p i=1) (a:ℝ) (ha:0≤ a) :
    optimizedValue (fun i=>a • B i) p=a*optimizedValue B p := by
  obtain ⟨f,hf,hfv⟩:=(optimizedValue_isGreatest B p hp hs).1
  obtain ⟨g,hg,hgv⟩:=(optimizedValue_isGreatest (fun i=>a • B i) p hp hs).1
  apply le_antisymm
  · rw [←hgv,assignmentValue_smul_rows]
    exact mul_le_mul_of_nonneg_left (assignmentValue_le_optimizedValue B p g hg) ha
  · rw [←hfv,←assignmentValue_smul_rows]
    exact assignmentValue_le_optimizedValue _ p f hf

theorem operatorValue_smul_square (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (C:FSC.Coord d→L[ℝ]FSC.Coord d) (hC:C∈psdCone) (a:ℝ) (ha:0≤ a) :
    operatorValue b p (a^2 • C)=a*operatorValue b p C := by
  obtain ⟨S,hS,hSC⟩:=exists_psd_factor C hC
  have hfac:S.adjoint.comp S=C:=by rw [hS.1.clm_adjoint_eq];exact hSC
  have haS:(a • S).toLinearMap.IsSymmetric:=hS.1.smul (by rfl)
  have hasq:(a • S).adjoint.comp (a • S)=a^2 • C:=by
    rw [haS.clm_adjoint_eq]
    apply ContinuousLinearMap.ext
    intro x
    change a • S (a • S x)=a^2 • C x
    have hh:S (S x)=C x:=congrArg (fun L:FSC.Coord d→L[ℝ]FSC.Coord d=>L x) hSC
    rw [map_smul,hh,smul_smul,pow_two]
  rw [←hasq,operatorValue_factor,←hfac,operatorValue_factor]
  exact optimizedValue_smul_rows (fun i=>S (b i)) p hp hs a ha

theorem operatorHilbertSchmidt_smul (A:FSC.Coord d→L[ℝ]FSC.Coord d) (t:ℝ) :
    operatorHilbertSchmidt (t • A)=|t| * operatorHilbertSchmidt A := by
  apply (sq_eq_sq₀ (operatorHilbertSchmidt_nonneg _) (mul_nonneg (abs_nonneg t) (operatorHilbertSchmidt_nonneg _))).mp
  rw [operatorHilbertSchmidt_sq,mul_pow,sq_abs,operatorHilbertSchmidt_sq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ContinuousLinearMap.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

theorem operatorHilbertSchmidt_eq_zero_iff (A:FSC.Coord d→L[ℝ]FSC.Coord d) :
    operatorHilbertSchmidt A=0 ↔ A=0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (le_antisymm (by simpa only [h] using operator_norm_le_HilbertSchmidt A) (norm_nonneg A))
  · intro h
    simp [h,operatorHilbertSchmidt,operatorEntries]

omit [NeZero m] in
theorem second_deriv_const_add (f:ℝ→ℝ) (t:ℝ) :
    deriv (deriv (fun u:ℝ=>f (t+u))) 0=deriv (deriv f) t := by
  have he:deriv (fun u:ℝ=>f (t+u))=(fun u:ℝ=>deriv f (t+u)):=by
    funext u
    exact deriv_comp_const_add f t u
  rw [he,deriv_comp_const_add]
  simp only [add_zero]

omit [NeZero m] in
theorem identity_positive :
    (ContinuousLinearMap.id ℝ (FSC.Coord d))∈pdCone := by
  refine ⟨fun x y=>rfl,?_⟩
  intro x hx
  exact real_inner_self_pos.mpr hx

def covarianceRay (K:FSC.Coord d→L[ℝ]FSC.Coord d) (t:ℝ) :
    FSC.Coord d→L[ℝ]FSC.Coord d:=
  ContinuousLinearMap.id ℝ (FSC.Coord d)+t • (K-ContinuousLinearMap.id ℝ (FSC.Coord d))

def covarianceRayValue (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (p:Fin m→ℝ)
    (K:FSC.Coord d→L[ℝ]FSC.Coord d) (t:ℝ):ℝ:=operatorValue b p (covarianceRay K t)

omit [NeZero m] in
theorem covarianceRay_psd (K:FSC.Coord d→L[ℝ]FSC.Coord d) (hK:K∈psdCone)
    (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : covarianceRay K t∈psdCone := by
  have he:covarianceRay K t=(1-t) • ContinuousLinearMap.id ℝ (FSC.Coord d)+t • K:=by
    unfold covarianceRay
    module
  rw [he]
  exact psdCone_convex (pdCone_subset_psdCone identity_positive) hK
    (sub_nonneg.mpr ht.2) ht.1 (by ring)

omit [NeZero m] in
theorem covarianceRay_positive (K:FSC.Coord d→L[ℝ]FSC.Coord d) (hK:K∈psdCone)
    (t:ℝ) (ht0:0≤ t) (ht1:t<1) : covarianceRay K t∈pdCone := by
  have he:covarianceRay K t=(1-t) • ContinuousLinearMap.id ℝ (FSC.Coord d)+t • K:=by
    unfold covarianceRay
    module
  rw [he]
  refine ⟨(identity_positive.1.smul (by rfl : starRingEnd ℝ (1-t)=1-t)).add
    (hK.1.smul (by rfl : starRingEnd ℝ t=t)),?_⟩
  intro x hx
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,inner_add_right,real_inner_smul_right]
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht1) (real_inner_self_pos.mpr hx))
    (mul_nonneg ht0 (hK.2 x))

theorem covarianceRayValue_continuousOn (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (K:FSC.Coord d→L[ℝ]FSC.Coord d) (hK:K∈psdCone) :
    ContinuousOn (covarianceRayValue b p K) (Icc (0:ℝ) 1) := by
  exact (operatorValue_continuousOn b p (fun i=>(hp i).le) hs).comp
    (by unfold covarianceRay;fun_prop) (fun t ht=>covarianceRay_psd K hK t ht)

theorem covarianceRayValue_concaveOn (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (K:FSC.Coord d→L[ℝ]FSC.Coord d) (hK:K∈psdCone) :
    ConcaveOn ℝ (Icc (0:ℝ) 1) (covarianceRayValue b p K) := by
  refine ⟨convex_Icc 0 1,?_⟩
  intro x hx y hy a c ha hc hac
  have he:covarianceRay K (a*x+c*y)=a • covarianceRay K x+c • covarianceRay K y:=by
    have he':a=1-c:=by linarith
    rw [he']
    unfold covarianceRay
    module
  have hh:=(operatorValue_concaveOn_psd b p hp hs).2
    (covarianceRay_psd K hK x hx) (covarianceRay_psd K hK y hy) ha hc hac
  change a*operatorValue b p (covarianceRay K x)+c*operatorValue b p (covarianceRay K y)≤
    operatorValue b p (covarianceRay K (a*x+c*y))
  rw [he]
  exact hh

/-- This is the literal local Gaussian second-derivative estimate required
from the facet bootstrap. It is a named hypothesis, not an asserted theorem. -/
def LocalGaussianCurvature (b:AffineBasis (Fin m) ℝ (FSC.Coord d)) (p:Fin m→ℝ)
    (radius coefficient:ℝ):Prop:=
  ∀C H:FSC.Coord d→L[ℝ]FSC.Coord d,C∈pdCone →
    operatorHilbertSchmidt (C-ContinuousLinearMap.id ℝ (FSC.Coord d))≤ radius →
    H.toLinearMap.IsSymmetric →
    deriv (deriv (fun t:ℝ=>operatorValue b p (C+t • H))) 0≤
      -coefficient*(operatorHilbertSchmidt H)^2

/-- Local quantitative curvature, actual global concavity, and actual boundary
continuity imply a quantitative deficit for every nontrivial PSD target. -/
theorem gaussian_psd_ray_tangent_gap (b:AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p:Fin m→ℝ) (hp:∀i,0<p i) (hs:∑i,p i=1)
    (radius coefficient:ℝ) (hradius:0<radius) (hcoef:0≤ coefficient)
    (hcurv:LocalGaussianCurvature b p radius coefficient)
    (K:FSC.Coord d→L[ℝ]FSC.Coord d) (hK:K∈psdCone)
    (he:0<operatorHilbertSchmidt (K-ContinuousLinearMap.id ℝ (FSC.Coord d))) :
    coefficient*(operatorHilbertSchmidt (K-ContinuousLinearMap.id ℝ (FSC.Coord d)))^2/4*
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
      HasDerivAt (deriv (covarianceRayValue b p K)) q t ∧ q≤-(coefficient*e^2):=by
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
    exact ⟨q,hfirst.differentiableAt,hsecond,by dsimp [e];linarith⟩
  have hgap:=concave_ray_gap (covarianceRayValue b p K) _ (coefficient*e^2) s hspos hs1
    (covarianceRayValue_concaveOn b p hp hs K hK) hd0 hcont hj
  have hmin:min (1:ℝ) (radius/e)≤2*s:=by
    by_cases hh:radius/e≤1/2
    · rw [show s=radius/e from min_eq_right hh]
      have hm:=min_le_right (1:ℝ) (radius/e)
      linarith
    · rw [show s=(1/2:ℝ) from min_eq_left (not_le.mp hh).le]
      have hm:=min_le_left (1:ℝ) (radius/e)
      linarith
  have hmul:=mul_le_mul_of_nonneg_left hmin (mul_nonneg hcoef (sq_nonneg e))
  have hout:coefficient*e^2/4*min 1 (radius/e)≤
      covarianceRayValue b p K 0+deriv (covarianceRayValue b p K) 0-covarianceRayValue b p K 1:=by
    nlinarith
  simpa only [covarianceRayValue,hzero,hone] using hout

omit [NeZero m] in
/-- The actual Price derivative at the unscaled Parseval simplex. -/
theorem normalized_reference_derivative (hn:0<n)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (H:FSC.Coord d→L[ℝ]FSC.Coord d) (hH:H.toLinearMap.IsSymmetric) :
    HasDerivAt (fun t:ℝ=>operatorValue b (uniformMass n)
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H))
      (referenceScale n*operatorTrace H/2) 0 := by
  have hlower:CenteredSingularLowerBound (fun i=>b i) 1:=by
    simpa only [one_smul] using scaled_centered_singular b hG 1
  have hd:=hasDerivAt_intrinsic_covariance_value b (uniformMass n) 1 (by norm_num)
    hlower (uniformMass_pos n) (uniformMass_sum n) 0 (regular_fan_mass b hG) H hH
  simp only [Submodule.coe_zero] at hd
  rw [←covariance_first_derivative_value b 0 1 (by norm_num) hlower H] at hd
  have hv:rowDerivative b 0 (rowsOfOperator b ((1/2:ℝ) • H))=
      referenceScale n*operatorTrace H/2:=by
    rw [rowDerivative_apply,operatorTrace,parseval_trace b hP,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [rowsOfOperator_apply,ContinuousLinearMap.smul_apply,
      regular_fan_centroid hn b hG,real_inner_smul_left,real_inner_smul_right]
    rw [real_inner_comm (H (b i)) (b i)]
    ring
  rw [hv] at hd
  have he:(fun t:ℝ=>operatorValue b (uniformMass n)
      (ContinuousLinearMap.id ℝ (FSC.Coord d)+t • H))=
      (fun t:ℝ=>covarianceValue (Matrix.gram ℝ b+t • gramVelocity b H) (uniformMass n)):=by
    funext t
    unfold operatorValue
    rw [gramVelocity_add_smul]
    congr 2
  rw [he]
  exact hd

omit [NeZero m] in
def normalizedRowCovariance (n:ℕ)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (B:Fin (n+2)→FSC.Coord e):
    FSC.Coord d→L[ℝ]FSC.Coord d:=((referenceScale n)^2)⁻¹ • rowCovariance b B

omit [NeZero m] in
theorem normalizedRowCovariance_psd (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (B:Fin (n+2)→FSC.Coord e):normalizedRowCovariance n b B∈psdCone:=by
  have hC:=rowCovariance_psd b B
  refine ⟨hC.1.smul (by rfl),?_⟩
  intro x
  change 0≤ inner ℝ x (((referenceScale n)^2)⁻¹ • rowCovariance b B x)
  rw [real_inner_smul_right]
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (hC.2 x)

omit [NeZero m] in
theorem rowCovariance_eq_scaled_normalized
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (B:Fin (n+2)→FSC.Coord e):
    rowCovariance b B=(referenceScale n)^2 • normalizedRowCovariance n b B:=by
  unfold normalizedRowCovariance
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos (referenceScale_pos n))),one_smul]

omit [NeZero m] in
/-- Exact conversion from the normalized Gaussian tangent gap to the actual
row-covariance deficit, including every rectangular singular row system. -/
theorem regularCovarianceDeficit_eq_scaled_tangent (hn:0<n)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0):
    regularCovarianceDeficit n B=referenceScale n*
      (operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d))+
        deriv (covarianceRayValue b (uniformMass n) (normalizedRowCovariance n b B)) 0-
        operatorValue b (uniformMass n) (normalizedRowCovariance n b B)):=by
  let I:=ContinuousLinearMap.id ℝ (FSC.Coord d)
  let K:=normalizedRowCovariance n b B
  let a:=referenceScale n
  have hK:K∈psdCone:=normalizedRowCovariance_psd b B
  have hCK:rowCovariance b B=a^2 • K:=rowCovariance_eq_scaled_normalized b B
  have hv:=operatorValue_smul_square b (uniformMass n) (uniformMass_pos n)
    (uniformMass_sum n) K hK a (referenceScale_pos n).le
  have hvI:=operatorValue_smul_square b (uniformMass n) (uniformMass_pos n)
    (uniformMass_sum n) I (pdCone_subset_psdCone identity_positive) a (referenceScale_pos n).le
  change operatorValue b (uniformMass n) (referenceCovariance n d)=
    a*operatorValue b (uniformMass n) I at hvI
  rw [reference_covariance_value b hG] at hvI
  have htI: a^2*operatorTrace I=referenceFirstWeight n:=by
    have hh:=reference_covariance_trace b hG hP
    simpa only [a,I,operatorTrace,referenceCovariance,ContinuousLinearMap.toLinearMap_smul,map_smul,smul_eq_mul]
      using hh
  have hE:(K-I).toLinearMap.IsSymmetric:=hK.1.sub identity_positive.1
  have hd:=normalized_reference_derivative hn b hG hP (K-I) hE
  have hd':deriv (covarianceRayValue b (uniformMass n) K) 0=a*operatorTrace (K-I)/2:=hd.deriv
  change regularCovarianceDeficit n B=a*(operatorValue b (uniformMass n) I+
    deriv (covarianceRayValue b (uniformMass n) K) 0-operatorValue b (uniformMass n) K)
  rw [regularCovarianceDeficit_eq_covariance_gap b hG hP B hB,penalizedValue,hCK,hv,hd']
  have htK:operatorTrace (a^2 • K)=a^2*operatorTrace K:=by simp [operatorTrace]
  have htE:operatorTrace (K-I)=operatorTrace K-operatorTrace I:=by simp [operatorTrace]
  simp only [operatorTrace] at htK htE htI ⊢
  rw [htK,htE]
  nlinarith

omit [NeZero m] in
/-- Global quantitative covariance rigidity from the explicit local Gaussian
curvature input. The conclusion includes zero defect and singular endpoints. -/
theorem regularCovarianceDeficit_ray_bound (hn:0<n)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (radius coefficient:ℝ) (hradius:0<radius) (hcoef:0≤ coefficient)
    (hcurv:LocalGaussianCurvature b (uniformMass n) radius coefficient)
    (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0):
    let defect:=operatorHilbertSchmidt
      (normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d))
    referenceScale n*coefficient*defect^2/4*min 1 (radius/defect)≤
      regularCovarianceDeficit n B:=by
  dsimp only
  let K:=normalizedRowCovariance n b B
  let defect:=operatorHilbertSchmidt (K-ContinuousLinearMap.id ℝ (FSC.Coord d))
  by_cases hz:defect=0
  · change referenceScale n*coefficient*defect^2/4*min 1 (radius/defect)≤_
    rw [hz]
    simpa using regularCovarianceDeficit_nonneg hn B hB
  have hpos:0<defect:=lt_of_le_of_ne (operatorHilbertSchmidt_nonneg _) (Ne.symm hz)
  have hh:=gaussian_psd_ray_tangent_gap b (uniformMass n) (uniformMass_pos n)
    (uniformMass_sum n) radius coefficient hradius hcoef hcurv K
    (normalizedRowCovariance_psd b B) hpos
  have hm:=mul_le_mul_of_nonneg_left hh (referenceScale_pos n).le
  rw [regularCovarianceDeficit_eq_scaled_tangent hn b hG hP B hB]
  convert hm using 1 <;>ring

omit [NeZero m] in
/-- The manuscript scaling: local coefficient α/(12m) yields the global
α²e²/(48m) ray bound, with the radius retained exactly. -/
theorem regularCovarianceDeficit_ray_bound_normalized (hn:0<n)
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (radius:ℝ) (hradius:0<radius)
    (hcurv:LocalGaussianCurvature b (uniformMass n) radius
      (referenceScale n/(12*((n:ℝ)+2))))
    (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0):
    let defect:=operatorHilbertSchmidt
      (normalizedRowCovariance n b B-ContinuousLinearMap.id ℝ (FSC.Coord d))
    (referenceScale n)^2*defect^2/(48*((n:ℝ)+2))*min 1 (radius/defect)≤
      regularCovarianceDeficit n B:=by
  have hh:=regularCovarianceDeficit_ray_bound hn b hG hP radius
    (referenceScale n/(12*((n:ℝ)+2))) hradius
    (by exact div_nonneg (referenceScale_pos n).le (by positivity)) hcurv B hB
  dsimp only at hh ⊢
  have hc (z:ℝ):(referenceScale n)^2*z^2/(48*((n:ℝ)+2))=
      referenceScale n*(referenceScale n/(12*((n:ℝ)+2)))*z^2/4:=by
    field_simp
    ring
  rw [hc]
  exact hh

end NegativeVotingRayDeficit
