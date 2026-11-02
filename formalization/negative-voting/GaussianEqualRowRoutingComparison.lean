import GaussianEqualRowQuadraticCertificate
import GaussianSecondChaosLower

/-! Actual fractional routing against an equal-row Gaussian proxy. The
absolute tail is explicit; no calibrated row-payment or proxy-construction
claim is imported. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical RealInnerProductSpace
namespace NegativeVotingEqualRowRoutingComparison
open NegativeVoting NegativeVotingModern NegativeVotingEqualRowMaximumLaw
  NegativeVotingEqualRowMaximumComparison NegativeVotingEqualRowQuadraticCertificate
  NegativeVotingSquareExponential NegativeVotingSecondChaosLower NegativeVotingRegularScoreLaw
  OAI.MinUncut.GaussianHermite
variable {m d : ℕ} [NeZero m]

def weightedScore (Z : Fin m→FSC.Coord d) (f : (Fin d→ℝ)→Fin m→ℝ) (x:Fin d→ℝ) : ℝ :=
  ∑ i,f x i*linearObservable (Z i) x

def routingLoss (Z : Fin m→FSC.Coord d) (f : (Fin d→ℝ)→Fin m→ℝ) (x:Fin d→ℝ) : ℝ :=
  rowMaximum Z x-weightedScore Z f x

def rawMaxAbs (Z : Fin m→FSC.Coord d) (x:Fin d→ℝ) : ℝ :=
  maxScore (fun i=>|linearObservable (Z i) x|)

theorem routing_nonneg_finite (z w : Fin m→ℝ) (hw : ∀ i,0≤w i) (hs:∑ i,w i=1) :
    0≤ maxScore z-∑ i,w i*z i := by
  have hh : (∑ i,w i*z i)≤∑ i,w i*maxScore z :=
    Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left
      (Finset.le_sup' z (Finset.mem_univ i)) (hw i))
  rw [←Finset.sum_mul,hs,one_mul] at hh
  linarith

theorem routing_square_finite (z w : Fin m→ℝ) (hw : ∀ i,0≤w i) (hs:∑ i,w i=1)
    (T:ℝ) (hT:0≤T) :
    (maxScore z)^2-∑ i,w i*(z i)^2≤
      2*T*(maxScore z-∑ i,w i*z i)+
        64*Real.exp ((maxScore (fun i=>|z i|))^2/8)*Real.exp (-T^2/16) := by
  let V:=maxScore z
  let A:=maxScore (fun i=>|z i|)
  let c:=V-∑ i,w i*z i
  have hc : 0≤c := routing_nonneg_finite z w hw hs
  have hz i : |z i|≤A := Finset.le_sup' (fun i=>|z i|) (Finset.mem_univ i)
  have hA : 0≤A := le_trans (abs_nonneg (z 0)) (hz 0)
  have hV : V≤A := Finset.sup'_le _ _ (fun i _=>le_trans (le_abs_self _) (hz i))
  have hlo : -A≤∑ i,w i*z i := by
    calc
      -A = ∑ i,w i*(-A) := by rw [←Finset.sum_mul,hs,one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left
        (by have := (abs_le.mp (hz i)).1;linarith) (hw i))
  have hcA : c≤2*A := by dsimp [c];linarith
  have hsq : V^2-∑ i,w i*(z i)^2≤2*V*c := by
    have hh : 0≤∑ i,w i*(V-z i)^2 := Finset.sum_nonneg
      (fun i _=>mul_nonneg (hw i) (sq_nonneg _))
    have he : (∑ i,w i*(V-z i)^2)=V^2-2*V*(∑ i,w i*z i)+∑ i,w i*(z i)^2 := by
      simp_rw [sub_sq,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      rw [←Finset.sum_mul,hs,one_mul]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hh
    dsimp [c]
    nlinarith
  by_cases hVT : V≤T
  · have hh := mul_le_mul_of_nonneg_right hVT hc
    have he : 0≤64*Real.exp (A^2/8)*Real.exp (-T^2/16) := by positivity
    change V^2-_≤2*T*c+_
    nlinarith only [hsq,hh,he]
  · have hV0 : 0≤V := by linarith
    have hsqA : T^2≤A^2 := pow_le_pow_left₀ hT (by linarith) 2
    have hvc : 2*V*c≤4*A^2 := by
      have hh := mul_le_mul hV hcA hc hA
      nlinarith only [hh]
    have hex : A^2≤16*Real.exp (A^2/16) := by have := Real.add_one_le_exp (A^2/16);linarith
    have heg : Real.exp (A^2/16)≤Real.exp (A^2/8-T^2/16) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hbound : 4*A^2≤64*Real.exp (A^2/8)*Real.exp (-T^2/16) := by
      have heq : Real.exp (A^2/8)*Real.exp (-T^2/16)=Real.exp (A^2/8-T^2/16) := by
        rw [←Real.exp_add]
        congr 1
        ring
      rw [mul_assoc,heq]
      nlinarith only [hex,heg]
    change V^2-_≤2*T*c+_
    have ht : 0≤2*T*c := by positivity
    nlinarith only [hsq,hvc,hbound,ht]

theorem rawMaxAbs_eq (Z : Fin m→FSC.Coord d) (x:Fin d→ℝ) :
    rawMaxAbs Z x=affineMaxAbs Z 0 (WithLp.toLp 2 x) := by
  simp only [rawMaxAbs,affineMaxAbs,Pi.zero_apply,zero_add,linearObservable,
    PiLp.inner_apply,Real.inner_apply,WithLp.ofLp_toLp,mul_comm]

theorem rawMaxAbs_exp_integrable (Z : Fin m→FSC.Coord d) (hZ:∀ i,‖Z i‖≤1) :
    Integrable (fun x=>Real.exp ((rawMaxAbs Z x)^2/8)) (standardGaussian (Fin d)) := by
  have hm : MeasurePreserving (WithLp.toLp 2) (standardGaussian (Fin d)) (stdGaussian (FSC.Coord d)) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have hh := hm.integrable_comp_of_integrable (max_square_exp_integrable Z hZ 0)
  simpa only [Function.comp_def,←rawMaxAbs_eq] using hh

theorem integral_rawMaxAbs_exp_le (Z : Fin m→FSC.Coord d) (hZ:∀ i,‖Z i‖≤1) :
    (∫ x,Real.exp ((rawMaxAbs Z x)^2/8) ∂standardGaussian (Fin d))≤2*(m:ℝ) := by
  have hh := integral_max_square_exp_le Z hZ 0
  rw [←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)] at hh
  simpa only [←rawMaxAbs_eq,Pi.zero_apply,zero_pow (by decide : 2≠0),zero_div,
    Real.exp_zero,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hh

theorem weightedScore_integrable (Z : Fin m→FSC.Coord d)
    (f:(Fin d→ℝ)→Fin m→ℝ) (hf:∀ i,MemLp (fun x=>f x i) 2 (standardGaussian (Fin d))) :
    Integrable (weightedScore Z f) (standardGaussian (Fin d)) := by
  apply integrable_finsetSum
  intro i _
  exact (hf i).integrable_mul (linearObservable_memLp (Z i))

theorem routingLoss_integrable (Z : Fin m→FSC.Coord d)
    (f:(Fin d→ℝ)→Fin m→ℝ) (hf:∀ i,MemLp (fun x=>f x i) 2 (standardGaussian (Fin d))) :
    Integrable (routingLoss Z f) (standardGaussian (Fin d)) :=
  (rowMaximum_memLp_two Z).integrable (by norm_num) |>.sub (weightedScore_integrable Z f hf)

theorem normalized_routing_square_comparison (Z : Fin m→FSC.Coord d) (hZ:∀ i,‖Z i‖≤1)
    (f:(Fin d→ℝ)→Fin m→ℝ) (hf:∀ i,MemLp (fun x=>f x i) 2 (standardGaussian (Fin d)))
    (h0:∀ᵐ x ∂standardGaussian (Fin d),∀ i,0≤f x i)
    (hs:∀ᵐ x ∂standardGaussian (Fin d),∑ i,f x i=1) (T:ℝ) (hT:0≤T) :
    (∫ x,(rowMaximum Z x)^2 ∂standardGaussian (Fin d))-
      (∫ x,weightedRowSquare (fun i j=>Z i j) f x ∂standardGaussian (Fin d))≤
      2*T*(∫ x,routingLoss Z f x ∂standardGaussian (Fin d))+
        128*(m:ℝ)*Real.exp (-T^2/16) := by
  have hw := weightedRowSquare_integrable (fun i j=>Z i j) f hf
  have hm := (rowMaximum_memLp_two Z).integrable_sq
  have he := rawMaxAbs_exp_integrable Z hZ
  have hc := routingLoss_integrable Z f hf
  have hi : Integrable (fun x=>2*T*routingLoss Z f x+
      (64*Real.exp (-T^2/16))*Real.exp ((rawMaxAbs Z x)^2/8)) (standardGaussian (Fin d)) :=
    (hc.const_mul _).add (he.const_mul _)
  have hp : ∀ᵐ x ∂standardGaussian (Fin d),
      (rowMaximum Z x)^2-weightedRowSquare (fun i j=>Z i j) f x≤
        2*T*routingLoss Z f x+(64*Real.exp (-T^2/16))*Real.exp ((rawMaxAbs Z x)^2/8) := by
    filter_upwards [h0,hs] with x hx0 hxs
    have hh := routing_square_finite (fun i=>linearObservable (Z i) x) (f x) hx0 hxs T hT
    change (maxScore (fun i=>linearObservable (Z i) x))^2-
      (∑ i,f x i*(linearObservable (Z i) x)^2)≤
      2*T*(maxScore (fun i=>linearObservable (Z i) x)-∑ i,f x i*linearObservable (Z i) x)+
      (64*Real.exp (-T^2/16))*Real.exp ((maxScore (fun i=>|linearObservable (Z i) x|))^2/8)
    convert hh using 1 <;> ring
  have hb : Integrable (fun x=>(rowMaximum Z x)^2-weightedRowSquare (fun i j=>Z i j) f x)
      (standardGaussian (Fin d)) := hm.sub hw
  have hh := integral_mono_ae hb hi hp
  rw [integral_sub hm hw,integral_add (hc.const_mul _) (he.const_mul _),
    integral_const_mul,integral_const_mul] at hh
  have hu := mul_le_mul_of_nonneg_left (integral_rawMaxAbs_exp_le Z hZ)
    (show 0≤64*Real.exp (-T^2/16) by positivity)
  nlinarith only [hh,hu]

theorem linearObservable_smul (z : FSC.Coord d) (a:ℝ) (x:Fin d→ℝ) :
    linearObservable (a•z) x=a*linearObservable z x := by
  change (∑ j,(a*z j)*x j)=a*(∑ j,z j*x j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weightedScore_smul (Z : Fin m→FSC.Coord d) (f:(Fin d→ℝ)→Fin m→ℝ)
    (a:ℝ) (x:Fin d→ℝ) : weightedScore (a•Z) f x=a*weightedScore Z f x := by
  unfold weightedScore
  simp_rw [Pi.smul_apply,linearObservable_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weightedRowSquare_smul (Z : Fin m→FSC.Coord d) (f:(Fin d→ℝ)→Fin m→ℝ)
    (a:ℝ) (x:Fin d→ℝ) :
    weightedRowSquare (fun i j=>(a•Z) i j) f x=a^2*weightedRowSquare (fun i j=>Z i j) f x := by
  change (∑ i,f x i*(linearObservable (a•Z i) x)^2)=a^2*(∑ i,f x i*(linearObservable (Z i) x)^2)
  simp_rw [linearObservable_smul,mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem routingLoss_smul (Z : Fin m→FSC.Coord d) (f:(Fin d→ℝ)→Fin m→ℝ)
    (a:ℝ) (ha:0<a) (x:Fin d→ℝ) : routingLoss (a•Z) f x=a*routingLoss Z f x := by
  simp only [routingLoss,rowMaximum_pos_smul Z a ha,weightedScore_smul]
  ring

theorem routing_square_comparison (Z : Fin m→FSC.Coord d) (α:ℝ) (hα:0<α)
    (hZ:∀ i,‖Z i‖≤α)
    (f:(Fin d→ℝ)→Fin m→ℝ) (hf:∀ i,MemLp (fun x=>f x i) 2 (standardGaussian (Fin d)))
    (h0:∀ᵐ x ∂standardGaussian (Fin d),∀ i,0≤f x i)
    (hs:∀ᵐ x ∂standardGaussian (Fin d),∑ i,f x i=1) (T:ℝ) (hT:0≤T) :
    (∫ x,(rowMaximum Z x)^2 ∂standardGaussian (Fin d))-
      (∫ x,weightedRowSquare (fun i j=>Z i j) f x ∂standardGaussian (Fin d))≤
      2*α*T*(∫ x,routingLoss Z f x ∂standardGaussian (Fin d))+
        128*α^2*(m:ℝ)*Real.exp (-T^2/16) := by
  let B : Fin m→FSC.Coord d:=α⁻¹•Z
  have hB i : ‖B i‖≤1 := by
    change ‖α⁻¹•Z i‖≤1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hα)]
    calc
      α⁻¹*‖Z i‖≤α⁻¹*α := mul_le_mul_of_nonneg_left (hZ i) (inv_nonneg.mpr hα.le)
      _ = 1 := inv_mul_cancel₀ hα.ne'
  have he : α•B=Z := by dsimp [B];rw [smul_smul,mul_inv_cancel₀ hα.ne',one_smul]
  have hh := mul_le_mul_of_nonneg_left (normalized_routing_square_comparison B hB f hf h0 hs T hT)
    (sq_nonneg α)
  rw [←he]
  simp_rw [rowMaximum_pos_smul B α hα,mul_pow,weightedRowSquare_smul,routingLoss_smul B f α hα]
  rw [integral_const_mul,integral_const_mul,integral_const_mul]
  nlinarith only [hh]

theorem integral_weightedScore (Z : Fin m→FSC.Coord d)
    (f:(Fin d→ℝ)→Fin m→ℝ)
    (hf:∀ i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (h01:∀ i,∀ᵐ x ∂standardGaussian (Fin d),0≤f x i ∧ f x i≤1) :
    (∫ x,weightedScore Z f x ∂standardGaussian (Fin d))=
      ∑ i,inner ℝ (Z i) (firstMomentVector (fun x=>f x i)) := by
  have hi i : Integrable (fun x=>f x i*linearObservable (Z i) x) (standardGaussian (Fin d)) :=
    NegativeVotingMassCentroid.fractional_mul_integrable _ _ _ (hf i) (h01 i)
      ((linearObservable_memLp (Z i)).integrable (by norm_num))
  unfold weightedScore
  rw [integral_finsetSum _ (fun i _=>hi i)]
  exact Finset.sum_congr rfl (fun i _=>weighted_linearObservable_integral _ (hf i) (h01 i) _)

/-- Maximum comparison and fractional routing combine with the same literal
first-moment deficit. Its geometric payment is deliberately a separate task. -/
theorem equal_row_test_deficit (Z : Fin m→FSC.Coord d) (α:ℝ) (hα:0<α)
    (hZ:∀ i,‖Z i‖^2=α^2*(1-1/(m:ℝ)))
    (f:(Fin d→ℝ)→Fin m→ℝ) (hf:∀ i,MemLp (fun x=>f x i) 2 (standardGaussian (Fin d)))
    (h0:∀ᵐ x ∂standardGaussian (Fin d),∀ i,0≤f x i)
    (hs:∀ᵐ x ∂standardGaussian (Fin d),∑ i,f x i=1) (T:ℝ) (hT:0≤T) :
    α^2*((∫ y : Fin m→ℝ,(NegativeVotingGaussianMaximum.maximum y)^2 ∂standardGaussian (Fin m))-1)-
      ((∫ x,weightedRowSquare (fun i j=>Z i j) f x ∂standardGaussian (Fin d))-α^2*(1-1/(m:ℝ)))≤
      2*α*T*(α*(∫ y : Fin m→ℝ,NegativeVotingGaussianMaximum.maximum y ∂standardGaussian (Fin m))-
        (∫ x,weightedScore Z f x ∂standardGaussian (Fin d)))+
      144*α^2*(m:ℝ)*Real.exp (-T^2/16) := by
  have hcap i : ‖Z i‖≤α := by
    have hq : α^2*(1-1/(m:ℝ))≤α^2 := by
      have : 0≤1/(m:ℝ) := by positivity
      nlinarith [sq_nonneg α]
    have hn:=norm_nonneg (Z i)
    have hz:=hZ i
    nlinarith
  have hr:=routing_square_comparison Z α hα hcap f hf h0 hs T hT
  have hmx:=(equal_row_maximum_comparison Z α hα
    (fun i=>by simpa only [real_inner_self_eq_norm_sq] using hZ i) T hT).2
  have hroute : (∫ x,routingLoss Z f x ∂standardGaussian (Fin d))=
      (∫ x,rowMaximum Z x ∂standardGaussian (Fin d))-
        (∫ x,weightedScore Z f x ∂standardGaussian (Fin d)) :=
    integral_sub ((rowMaximum_memLp_two Z).integrable (by norm_num)) (weightedScore_integrable Z f hf)
  rw [hroute] at hr
  have he : Real.exp (-T^2/8)≤Real.exp (-T^2/16) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg T])
  have he' := mul_le_mul_of_nonneg_left he (show 0≤16*α^2*(m:ℝ) by positivity)
  nlinarith only [hr,hmx,he']

def regularQuadraticTestValue (m:ℕ) [NeZero m] (α:ℝ) : ℝ :=
  α^2*((∫ y : Fin m→ℝ,(NegativeVotingGaussianMaximum.maximum y)^2 ∂standardGaussian (Fin m))-1)

def proxyLoss (Z : Fin m→FSC.Coord d) (f:(Fin d→ℝ)→Fin m→ℝ) (α:ℝ) : ℝ :=
  α*(∫ y : Fin m→ℝ,NegativeVotingGaussianMaximum.maximum y ∂standardGaussian (Fin m))-
    (∫ x,weightedScore Z f x ∂standardGaussian (Fin d))

theorem proxyLoss_eq_centroid (Z : Fin m→FSC.Coord d)
    (f:(Fin d→ℝ)→Fin m→ℝ) (α:ℝ)
    (hf:∀ i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (h0:∀ᵐ x ∂standardGaussian (Fin d),∀ i,0≤f x i)
    (hs:∀ᵐ x ∂standardGaussian (Fin d),∑ i,f x i=1) :
    proxyLoss Z f α=α*(∫ y : Fin m→ℝ,NegativeVotingGaussianMaximum.maximum y ∂standardGaussian (Fin m))-
      ∑ i,inner ℝ (Z i) (firstMomentVector (fun x=>f x i)) := by
  unfold proxyLoss
  rw [integral_weightedScore Z f hf]
  intro i
  filter_upwards [h0,hs] with x hx0 hxs
  exact ⟨hx0 i,(Finset.single_le_sum (fun j _=>hx0 j) (Finset.mem_univ i)).trans_eq hxs⟩

theorem proxyLoss_nonneg (Z : Fin m→FSC.Coord d) (α:ℝ) (hα:0<α)
    (hZ:∀ i,‖Z i‖^2=α^2*(1-1/(m:ℝ)))
    (f:(Fin d→ℝ)→Fin m→ℝ) (hf:∀ i,MemLp (fun x=>f x i) 2 (standardGaussian (Fin d)))
    (h0:∀ᵐ x ∂standardGaussian (Fin d),∀ i,0≤f x i)
    (hs:∀ᵐ x ∂standardGaussian (Fin d),∑ i,f x i=1) : 0≤proxyLoss Z f α := by
  have hm:=(equal_row_maximum_comparison Z α hα
    (fun i=>by simpa only [real_inner_self_eq_norm_sq] using hZ i) 0 (by norm_num)).1
  have hc : 0≤∫ x,routingLoss Z f x ∂standardGaussian (Fin d) := by
    apply integral_nonneg_of_ae
    filter_upwards [h0,hs] with x hx0 hxs
    exact routing_nonneg_finite (fun i=>linearObservable (Z i) x) (f x) hx0 hxs
  have he : (∫ x,routingLoss Z f x ∂standardGaussian (Fin d))=
      (∫ x,rowMaximum Z x ∂standardGaussian (Fin d))-
        (∫ x,weightedScore Z f x ∂standardGaussian (Fin d)) :=
    integral_sub ((rowMaximum_memLp_two Z).integrable (by norm_num)) (weightedScore_integrable Z f hf)
  rw [he] at hc
  dsimp [proxyLoss]
  linarith

theorem positive_square_tangent (s t e:ℝ) (he:s-t≤e) :
    (max s 0)^2-2*(max s 0)*e≤(max t 0)^2 := by
  by_cases hs : 0 ≤ s
  · rw [max_eq_left hs]
    by_cases ht : 0 ≤ t
    · rw [max_eq_left ht]
      have hh:=mul_le_mul_of_nonneg_left he hs
      nlinarith [sq_nonneg (s-t)]
    · rw [max_eq_right (le_of_not_ge ht)]
      have hh:=mul_le_mul_of_nonneg_left he hs
      have hst:=mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_ge ht)
      nlinarith
  · rw [max_eq_right (le_of_not_ge hs)]
    simpa using sq_nonneg (max t 0)

theorem quadratic_fraction_identity (s e D:ℝ) (hD:D≠0) :
    (s^2/(2*D)-s/D*e)*(2*D)=s^2-2*s*e := by
  field_simp
  <;> ring

/-- Actual second-chaos lower comparison for any supplied centered equal-row
proxy. The first-moment proxy loss remains literal, with an absolute Gaussian
tail: this theorem makes no unproved exterior row-payment assertion. -/
theorem equal_row_second_chaos_proxy_lower
    (hm:3≤ m) (Z : Fin m→FSC.Coord d) (α:ℝ) (hα:0<α)
    (hZ:∀ i,‖Z i‖^2=α^2*(1-1/(m:ℝ))) (hcenter:∑ i,Z i=0)
    (f:(Fin d→ℝ)→Fin m→ℝ)
    (hf:∀ i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (h0:∀ᵐ x ∂standardGaussian (Fin d),∀ i,0≤f x i)
    (hs:∀ᵐ x ∂standardGaussian (Fin d),∑ i,f x i=1) (T:ℝ) (hT:0≤T) :
    (max (regularQuadraticTestValue m α) 0)^2/(2*regularDenominator m α)-
      (max (regularQuadraticTestValue m α) 0)/(regularDenominator m α)*
        (2*α*T*proxyLoss Z f α+144*α^2*(m:ℝ)*Real.exp (-T^2/16))≤chaosEnergy f 2 := by
  have hf2 i : MemLp (fun x=>f x i) 2 (standardGaussian (Fin d)) := by
    refine MemLp.of_bound (hf i).aestronglyMeasurable 1 ?_
    filter_upwards [h0,hs] with x hx0 hxsum
    rw [Real.norm_eq_abs,abs_of_nonneg (hx0 i)]
    exact (Finset.single_le_sum (fun j _=>hx0 j) (Finset.mem_univ i)).trans_eq hxsum
  have hd:=equal_row_test_deficit Z α hα hZ f hf2 h0 hs T hT
  have hc:=ae_simplex_equal_row_certificate_euclidean hm Z α hα hZ hcenter f hf h0 hs
  have hp:=positive_square_tangent _ _ _ hd
  have hD:=regularDenominator_pos hm α hα
  apply (mul_le_mul_iff_right₀ (show 0<2*regularDenominator m α by positivity)).mp
  have hc':= (div_le_iff₀ (show 0<2*regularDenominator m α by positivity)).mp hc
  rw [mul_comm (2*regularDenominator m α) (_-_)]
  rw [quadratic_fraction_identity _ _ _ hD.ne']
  change (max ((∫ x,weightedRowSquare (fun i j=>Z i j) f x ∂standardGaussian (Fin d))-α^2*(1-1/(m:ℝ))) 0)^2≤
    chaosEnergy f 2*(2*regularDenominator m α) at hc'
  dsimp [regularQuadraticTestValue,proxyLoss]
  nlinarith only [hp,hc']

end NegativeVotingEqualRowRoutingComparison
