import GaussianOneRowCovarianceRay
import GaussianRayDeficit

/-! Fixed one-row exclusion from actual local covariance curvature.  Global
concavity and continuity retain singular endpoints of the covariance ray. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Classical RealInnerProductSpace Topology
namespace NegativeVotingOneRowRayExclusion
open NegativeVoting NegativeVotingOneRowCovarianceRay NegativeVotingOneRowCurvature
  NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity
  NegativeVotingRayDeficit NegativeVotingValueSemiconcavity
  NegativeVotingCenteredParseval NegativeVotingCovarianceCoercivity
  NegativeVotingCovarianceOptimizerDegree NegativeVotingBalancedReference
variable {m n d : ℕ} [NeZero m]

omit [NeZero m] in
theorem concave_stationary_max {f : ℝ → ℝ} {S : Set ℝ} {x : ℝ}
    (hc : ConcaveOn ℝ S f) (hx : x ∈ S) (hd : HasDerivAt f 0 x)
    (y : ℝ) (hy : y ∈ S) : f y ≤ f x := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hc.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field] at hh
    have := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · exact le_rfl
  · have hh := hc.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field] at hh
    have := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    linarith

omit [NeZero m] in
/-- A local uniform second-derivative bound gives a quadratic drop on the
local interval. The differentiability hypotheses concern its interior only. -/
theorem local_quadratic_drop (f : ℝ → ℝ) (c : ℝ)
    (hcont : ContinuousOn f (Icc (1/2:ℝ) (3/2)))
    (hzero : HasDerivAt f 0 1)
    (hj : ∀ t ∈ Ioo (1/2:ℝ) (3/2), ∃ q : ℝ,
      DifferentiableAt ℝ f t ∧ HasDerivAt (deriv f) q t ∧ q ≤ -c)
    (z : ℝ) (hz : z ∈ Icc (1/2:ℝ) (3/2)) :
    c/2*(z-1)^2 ≤ f 1-f z := by
  let g : ℝ → ℝ := fun t => f t+c/2*(t-1)^2
  have hgc : ContinuousOn g (Icc (1/2:ℝ) (3/2)) :=
    hcont.add (by fun_prop)
  have hgd (t : ℝ) (ht : t ∈ Ioo (1/2:ℝ) (3/2)) : DifferentiableAt ℝ g t :=
    (hj t ht).choose_spec.1.add (by fun_prop)
  have hgj (t : ℝ) (ht : t ∈ Ioo (1/2:ℝ) (3/2)) :
      ∃ q : ℝ, HasDerivAt (deriv g) q t ∧ q ≤ 0 := by
    obtain ⟨q,hfd,hq,hbound⟩ := hj t ht
    have hnear : ∀ᶠ u in 𝓝 t, DifferentiableAt ℝ f u := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact (hj u hu).choose_spec.1
    have hh := line_second_quadratic_penalty (K := -c) (a := -1) (c := 1) hnear hq
    have he : (fun u : ℝ => f u-(-c)/2*(-1+u*1)^2)=g := by
      funext u; dsimp [g]; ring
    rw [he] at hh
    refine ⟨q+c,?_,by linarith⟩
    convert hh using 1 <;> ring
  have hconc : ConcaveOn ℝ (Icc (1/2:ℝ) (3/2)) g := by
    apply concaveOn_of_deriv2_nonpos (convex_Icc _ _) hgc
    · intro t ht
      exact (hgd t (by simpa only [interior_Icc] using ht)).differentiableWithinAt
    · intro t ht
      exact (hgj t (by simpa only [interior_Icc] using ht)).choose_spec.1.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨q,hq,hq0⟩ := hgj t (by simpa only [interior_Icc] using ht)
      simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply,
        Function.comp_def,hq.deriv] using hq0
  have hg0 : HasDerivAt g 0 1 := by
    convert hzero.add ((((hasDerivAt_id (1:ℝ)).sub_const 1).pow 2).const_mul (c/2)) using 1 <;>
      simp [g,Pi.add_def]
  have hh := concave_stationary_max hconc (by norm_num) hg0 z hz
  dsimp [g] at hh
  nlinarith

omit [NeZero m] in
/-- Fixed radial exclusion, with no derivative assumption at the possibly
singular far endpoint. -/
theorem concave_fixed_exclusion (f : ℝ → ℝ) (b c δ a : ℝ)
    (hb : (3/2:ℝ) ≤ b) (hc : 0 ≤ c) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hconc : ConcaveOn ℝ (Icc (0:ℝ) b) f)
    (hcont : ContinuousOn f (Icc (1/2:ℝ) (3/2)))
    (hzero : HasDerivAt f 0 1)
    (hj : ∀ t ∈ Ioo (1/2:ℝ) (3/2), ∃ q : ℝ,
      DifferentiableAt ℝ f t ∧ HasDerivAt (deriv f) q t ∧ q ≤ -c)
    (ha : a ∈ Icc (0:ℝ) b) (hfar : δ ≤ |a-1|) :
    c*δ^2/2 ≤ f 1-f a := by
  have hgap : 0 < |a-1| := lt_of_lt_of_le hδ hfar
  let t : ℝ := δ/|a-1|
  have ht : 0 < t := div_pos hδ hgap
  have ht1 : t ≤ 1 := (div_le_one hgap).mpr hfar
  let z : ℝ := (1-t)*1+t*a
  have hzabs : |z-1|=δ := by
    have he : z-1=t*(a-1) := by dsimp [z]; ring
    rw [he,abs_mul,abs_of_pos ht]
    exact div_mul_cancel₀ δ (ne_of_gt hgap)
  have hz : z ∈ Icc (1/2:ℝ) (3/2) := by
    have hh := abs_le.mp (show |z-1| ≤ 1/2 by rw [hzabs]; exact hδ1)
    constructor <;> linarith
  have hlocal := local_quadratic_drop f c hcont hzero hj z hz
  have hsq : (z-1)^2=δ^2 := by rw [← sq_abs,hzabs]
  rw [hsq] at hlocal
  have hmem : (1:ℝ) ∈ Icc (0:ℝ) b := by constructor <;> linarith
  have hmax := concave_stationary_max hconc hmem hzero a ha
  have hchord := hconc.2 hmem ha (sub_nonneg.mpr ht1) ht.le (show (1-t)+t=1 by ring)
  change (1-t)*f 1+t*f a ≤ f z at hchord
  have hh := mul_le_mul_of_nonneg_right ht1 (sub_nonneg.mpr hmax)
  nlinarith

theorem oneRowCovariance_one (hm : 3 ≤ m) (b : Fin m → FSC.Coord d) (i : Fin m) :
    oneRowCovariance b i 1=ContinuousLinearMap.id ℝ (FSC.Coord d) := by
  have hm2 : (m:ℝ)-2 ≠ 0 := by
    have hh : (3:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hcoef : transverseCoefficient m 1=1 := by
    unfold transverseCoefficient
    convert div_self hm2 using 1 <;> ring
  rw [oneRowCovariance,hcoef,one_smul,one_smul]
  abel

theorem oneRowDirection_trace (hm : 3 ≤ m) (b : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x) (i : Fin m) :
    operatorTrace (oneRowDirection b i)=0 := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by linarith
  have hm1 : (m:ℝ)-1 ≠ 0 := by linarith
  have hm2 : (m:ℝ)-2 ≠ 0 := by linarith
  have htP : operatorTrace (rowProjector b i)=1 := by
    simp only [operatorTrace,rowProjector,ContinuousLinearMap.toLinearMap_smul,
      map_smul,smul_eq_mul,rankOne_trace,hG,if_pos rfl]
    field_simp <;> simp
  have htI : operatorTrace (ContinuousLinearMap.id ℝ (FSC.Coord d))=(m:ℝ)-1 := by
    rw [operatorTrace,parseval_trace b hP]
    simp only [ContinuousLinearMap.id_apply,hG,if_pos rfl,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp <;> simp
  change operatorTrace (rowProjector b i-((m:ℝ)-2)⁻¹•
    (ContinuousLinearMap.id ℝ (FSC.Coord d)-rowProjector b i))=0
  simp only [operatorTrace,ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_smul,map_sub,map_smul,smul_eq_mul] at htP htI ⊢
  rw [htP,htI]
  field_simp
  <;> ring

theorem oneRowValue_continuousOn (hm : 3 ≤ m)
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p : Fin m → ℝ) (hp : ∀ j,0 < p j) (hs : ∑ j,p j=1) (i : Fin m) :
    ContinuousOn (fun a : ℝ => operatorValue b p (oneRowCovariance b i a))
      (Icc (0:ℝ) ((m:ℝ)-1)) := by
  apply (operatorValue_continuousOn b p (fun j => (hp j).le) hs).comp
  · unfold oneRowCovariance transverseCoefficient
    fun_prop
  · intro a ha
    exact oneRowCovariance_psd hm b hG i a ha.1 ha.2

theorem oneRowValue_concaveOn (hm : 3 ≤ m)
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p : Fin m → ℝ) (hp : ∀ j,0 < p j) (hs : ∑ j,p j=1) (i : Fin m) :
    ConcaveOn ℝ (Icc (0:ℝ) ((m:ℝ)-1))
      (fun a : ℝ => operatorValue b p (oneRowCovariance b i a)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a c ha hc hac
  have he : oneRowCovariance b i (a*x+c*y)=
      a • oneRowCovariance b i x+c • oneRowCovariance b i y := by
    have ha' : a=1-c := by linarith
    rw [ha']
    simp only [oneRowCovariance,transverseCoefficient,div_eq_mul_inv]
    module
  have hh := (operatorValue_concaveOn_psd b p hp hs).2
    (oneRowCovariance_psd hm b hG i x hx.1 hx.2)
    (oneRowCovariance_psd hm b hG i y hy.1 hy.2) ha hc hac
  change a*operatorValue b p (oneRowCovariance b i x)+c*operatorValue b p (oneRowCovariance b i y) ≤
    operatorValue b p (oneRowCovariance b i (a*x+c*y))
  rw [he]
  exact hh

omit [NeZero m] in
theorem oneRowValue_reference_derivative (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x) (i : Fin (n+2)) :
    HasDerivAt (fun a : ℝ => operatorValue b (uniformMass n) (oneRowCovariance b i a)) 0 1 := by
  have hm : 3 ≤ n+2 := by omega
  have hG' : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hd := normalized_reference_derivative hn b hG hP (oneRowDirection b i)
    (oneRowDirection_symmetric b i)
  rw [oneRowDirection_trace hm b hG' hP i,mul_zero,zero_div] at hd
  apply hasDerivAt_of_const_add_zero 1 0
  convert hd using 1
  funext t
  rw [oneRowCovariance_affine,oneRowCovariance_one hm]

theorem oneRowValue_local_curvature (hm : 3 ≤ m)
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p : Fin m → ℝ) (hp : ∀ j,0 < p j) (hs : ∑ j,p j=1)
    (pmin : ℝ) (hpmin : 0 ≤ pmin) (hmin : ∀ j,pmin ≤ p j)
    (i : Fin m) (a : ℝ) (ha : a ∈ Ioo (1/2:ℝ) (3/2)) :
    ∃ q : ℝ, DifferentiableAt ℝ (fun t : ℝ => operatorValue b p (oneRowCovariance b i t)) a ∧
      HasDerivAt (deriv (fun t : ℝ => operatorValue b p (oneRowCovariance b i t))) q a ∧
      q ≤ -(pmin/(128*Real.pi)) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have ha0 := ha.1
  have ha1 := ha.2
  obtain ⟨v,q,hv,hq,hbound⟩ := exists_oneRowValue_derivatives hm b hG p hp hs pmin hpmin hmin i a
    (by linarith) (by linarith)
  refine ⟨q,hv.differentiableAt,hq,hbound.trans ?_⟩
  have hsqrt0 : 0 < Real.sqrt (a+1) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt2 : Real.sqrt (a+1) ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by linarith⟩
  have hcube : (Real.sqrt (a+1))^3 ≤ 8 := by nlinarith [sq_nonneg (Real.sqrt (a+1)-2)]
  have hden : 16*Real.pi*(Real.sqrt (a+1))^3 ≤ 128*Real.pi := by nlinarith [Real.pi_pos]
  have hh := div_le_div_of_nonneg_left hpmin (by positivity : 0 < 16*Real.pi*(Real.sqrt (a+1))^3) hden
  simpa only [neg_div] using neg_le_neg hh

omit [NeZero m] in
/-- The actual balanced covariance value loses a fixed amount outside every
fixed neighborhood of the regular row length. The endpoints a=0 and a=m-1
are explicitly allowed. -/
theorem oneRowValue_fixed_exclusion (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (i : Fin (n+2)) (a δ : ℝ) (ha : a ∈ Icc (0:ℝ) ((n:ℝ)+1))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hfar : δ ≤ |a-1|) :
    δ^2/(256*Real.pi*((n:ℝ)+2)) ≤
      operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d))-
      operatorValue b (uniformMass n) (oneRowCovariance b i a) := by
  have hm : 3 ≤ n+2 := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hG' : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hlocal : Icc (1/2:ℝ) (3/2) ⊆ Icc (0:ℝ) (((n+2:ℕ):ℝ)-1) := by
    intro t ht
    simp only [Nat.cast_add,Nat.cast_ofNat]
    constructor <;> linarith [ht.1,ht.2]
  have hh := concave_fixed_exclusion
    (fun t : ℝ => operatorValue b (uniformMass n) (oneRowCovariance b i t))
    (((n+2:ℕ):ℝ)-1) ((1/((n:ℝ)+2))/(128*Real.pi)) δ a (by push_cast; linarith)
    (by positivity) hδ hδ1
    (oneRowValue_concaveOn hm b hG' _ (uniformMass_pos n) (uniformMass_sum n) i)
    ((oneRowValue_continuousOn hm b hG' _ (uniformMass_pos n) (uniformMass_sum n) i).mono hlocal)
    (oneRowValue_reference_derivative hn b hG hP i)
    (fun t ht => oneRowValue_local_curvature hm b hG' _ (uniformMass_pos n) (uniformMass_sum n)
      (1/((n:ℝ)+2)) (by positivity) (fun j => le_rfl) i t ht)
    (by constructor; exact ha.1; push_cast; linarith [ha.2]) hfar
  rw [oneRowCovariance_one hm] at hh
  convert hh using 1 <;> field_simp <;> ring

omit [NeZero m] in
/-- A strict deficit threshold yields the fixed 1/256 squared-length window. -/
theorem oneRowValue_small_deficit (hn : 0 < n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (i : Fin (n+2)) (a : ℝ) (ha : a ∈ Icc (0:ℝ) ((n:ℝ)+1))
    (hloss : operatorValue b (uniformMass n) (ContinuousLinearMap.id ℝ (FSC.Coord d))-
      operatorValue b (uniformMass n) (oneRowCovariance b i a) <
        1/(16777216*Real.pi*((n:ℝ)+2))) : |a-1| < 1/256 := by
  by_contra hh
  have hfar : (1/256:ℝ) ≤ |a-1| := le_of_not_gt hh
  have hb := oneRowValue_fixed_exclusion hn b hG hP i a (1/256) ha (by norm_num) (by norm_num) hfar
  have he : (1/256:ℝ)^2/(256*Real.pi*((n:ℝ)+2))=1/(16777216*Real.pi*((n:ℝ)+2)) := by
    field_simp <;> ring
  rw [he] at hb
  exact (not_lt_of_ge hb) hloss

omit [NeZero m] in
/-- Conversion to the literal radial distance; no positive lower bound on the
target row is assumed. -/
theorem radial_close_of_square_close (x β δ : ℝ) (hx : 0 ≤ x) (hβ : 0 < β)
    (hδ : 0 ≤ δ) (h : |x^2/β^2-1| < δ) : |x-β| < β*δ := by
  have hfac : |x^2/β^2-1|=|x-β| * (x+β)/β^2 := by
    have heq : x^2/β^2-1=(x^2-β^2)/β^2 := by
      rw [sub_div,div_self (ne_of_gt (sq_pos_of_pos hβ))]
    rw [heq]
    rw [abs_div,abs_of_pos (sq_pos_of_pos hβ)]
    have he : x^2-β^2=(x-β)*(x+β) := by ring
    rw [he,abs_mul,abs_of_nonneg (by linarith : 0 ≤ x+β)]
  rw [hfac] at h
  have hh := (div_lt_iff₀ (sq_pos_of_pos hβ)).mp h
  have hb := mul_le_mul_of_nonneg_left (show β ≤ x+β by linarith) (abs_nonneg (x-β))
  have he : δ*β^2=(β*δ)*β := by ring
  rw [he] at hh
  have hh' : |x-β| * β < (β*δ)*β := lt_of_le_of_lt hb hh
  nlinarith

end NegativeVotingOneRowRayExclusion
