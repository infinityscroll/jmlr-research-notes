import GaussianStructuredSwitchingFacet

/-! Whole normal-interval control for the actual weighted switching forcing.
Absolute values are handled by their Lipschitz inequality, not by pretending
they are differentiable at zeros. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingStructuredSwitchingTube
open NegativeVotingStructuredSwitchingFacet NegativeVotingStructuredSwitchingMoments
  NegativeVotingStructuredSwitchingNormal NegativeVotingDisintegration
  NegativeVotingActualFacetOUTrace NegativeVotingNormalTrace NegativeVotingNormalDerivatives
  NegativeVotingSmoothErrorMoment NegativeVotingReciprocalDampingTube
  NegativeVotingRegularPairCoefficient

/-- One common control for values and increments from the actual facet. -/
structure IntervalControl (f : ℝ→ℝ) (C : ℝ) : Prop where
  continuous : ContinuousOn f (Icc 0 1)
  bound : ∀t∈Icc (0:ℝ) 1, |f t| ≤ C
  increment : ∀t∈Icc (0:ℝ) 1, |f t-f 0| ≤ C*t

theorem IntervalControl.nonneg {f : ℝ→ℝ} {C : ℝ} (hf : IntervalControl f C) : 0 ≤ C :=
  (abs_nonneg _).trans (hf.bound 0 (by constructor <;> norm_num))

theorem IntervalControl.mono {f : ℝ→ℝ} {C D : ℝ} (hf : IntervalControl f C) (hCD : C ≤ D) :
    IntervalControl f D := ⟨hf.continuous,fun t ht=>(hf.bound t ht).trans hCD,
      fun t ht=>(hf.increment t ht).trans (mul_le_mul_of_nonneg_right hCD ht.1)⟩

theorem IntervalControl.add {f g : ℝ→ℝ} {C D : ℝ}
    (hf : IntervalControl f C) (hg : IntervalControl g D) :
    IntervalControl (fun t=>f t+g t) (C+D) := by
  refine ⟨hf.continuous.add hg.continuous,?_,?_⟩
  · intro t ht
    exact (abs_add_le _ _).trans (add_le_add (hf.bound t ht) (hg.bound t ht))
  · intro t ht
    have h:=(abs_add_le (f t-f 0) (g t-g 0)).trans
      (add_le_add (hf.increment t ht) (hg.increment t ht))
    convert h using 1 <;> congr 1 <;> ring

theorem IntervalControl.const_mul {f : ℝ→ℝ} {C : ℝ} (hf : IntervalControl f C) (c : ℝ) :
    IntervalControl (fun t=>c*f t) (|c| * C) := by
  refine ⟨hf.continuous.const_mul c,?_,?_⟩
  · intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.bound t ht) (abs_nonneg _)
  · intro t ht
    rw [←mul_sub,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hf.increment t ht) (abs_nonneg _)).trans_eq (by ring)

theorem IntervalControl.abs {f : ℝ→ℝ} {C : ℝ} (hf : IntervalControl f C) :
    IntervalControl (fun t=>|f t|) C := by
  refine ⟨hf.continuous.abs,?_,?_⟩
  · intro t ht
    simpa only [abs_abs] using hf.bound t ht
  · intro t ht
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans (hf.increment t ht)

theorem IntervalControl.sub {f g : ℝ→ℝ} {C D : ℝ}
    (hf : IntervalControl f C) (hg : IntervalControl g D) :
    IntervalControl (fun t=>f t-g t) (C+D) := by
  simpa only [abs_neg,abs_one,one_mul,neg_mul,one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))

theorem IntervalControl.mul {f g : ℝ→ℝ} {C D : ℝ}
    (hf : IntervalControl f C) (hg : IntervalControl g D) :
    IntervalControl (fun t=>f t*g t) (2*C*D) := by
  have hC:=hf.nonneg
  have hD:=hg.nonneg
  refine ⟨hf.continuous.mul hg.continuous,?_,?_⟩
  · intro t ht
    rw [abs_mul]
    exact (mul_le_mul (hf.bound t ht) (hg.bound t ht) (abs_nonneg _) hC).trans (by nlinarith)
  · intro t ht
    have h0:=hg.bound 0 (by constructor <;> norm_num)
    have h1:=mul_le_mul (hf.bound t ht) (hg.increment t ht) (abs_nonneg _) hC
    have h2:=mul_le_mul (hf.increment t ht) h0 (abs_nonneg _) (mul_nonneg hC ht.1)
    have h3:=abs_add_le (f t*(g t-g 0)) ((f t-f 0)*g 0)
    rw [abs_mul,abs_mul] at h3
    have he : f t*(g t-g 0)+(f t-f 0)*g 0=f t*g t-f 0*g 0:=by ring
    rw [he] at h3
    nlinarith only [h1,h2,h3]

/-- A literal affine score on the entire unit normal interval. -/
theorem affine_interval_control (a b : ℝ) :
    IntervalControl (fun t=>a+t*b) (|a|+|b|) := by
  refine ⟨by fun_prop,?_,?_⟩
  · intro t ht
    have hh:=mul_le_mul_of_nonneg_right ht.2 (abs_nonneg b)
    have ha:=abs_add_le a (t*b)
    rw [abs_mul,abs_of_nonneg ht.1] at ha
    nlinarith
  · intro t ht
    simp only [zero_mul,add_zero,add_sub_cancel_left,abs_mul,abs_of_nonneg ht.1]
    nlinarith [mul_nonneg (abs_nonneg a) ht.1]

/-- Exact product control for the literal weighted forcing.  The inputs are
normal controls for its analytic factors; zeros inside absolute values cause
no exceptional-case assumption. -/
theorem weighted_forcing_interval_control (r : ℝ) (hr : 0<r)
    (κ ε l u v : ℝ→ℝ) (K E L U V : ℝ)
    (hκ : IntervalControl κ K) (hε : IntervalControl ε E)
    (hl : IntervalControl l L) (hu : IntervalControl u U) (hv : IntervalControl v V) :
    IntervalControl (fun t=>κ t*(r*ε t*|l t|+|u t-v t|/r))
      (4*K*(r*E*L+(U+V)/r)) := by
  have hp := hκ.mul (((hε.mul hl.abs).const_mul r).add ((hu.sub hv).abs.const_mul r⁻¹))
  have he : (fun t=>κ t*(r*(ε t*|l t|)+r⁻¹*|u t-v t|))=
      (fun t=>κ t*(r*ε t*|l t|+|u t-v t|/r)):=by funext t; ring
  rw [he,abs_of_pos hr,abs_of_pos (inv_pos.mpr hr)] at hp
  apply hp.mono
  have hK:=hκ.nonneg
  have hU:=hu.nonneg
  have hV:=hv.nonneg
  have hpos : 0 ≤ K*((U+V)/r):=mul_nonneg hK (div_nonneg (add_nonneg hU hV) hr.le)
  simp only [div_eq_mul_inv] at hpos ⊢
  nlinarith only [hpos]


/-- Actual damping and error controls on a whole comparison-plane normal
interval, including every point of the interval on one Gaussian sample. -/
theorem exists_dimension_uniform_common_tube_controls
    (A K : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d k : ℕ,
      ∀ (R : Fin (n+2)→FSC.Coord d), (∀i,‖R i‖ ≤ 1) →
      ∀ (w:FSC.Coord d) (e:tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k), ‖w‖=1 →
      ∀ a b : ℝ, 0 ≤ b → a^2 ≤ b*logScale n →
      ∃ Wκ Wε : tangentSpace w→ℝ,
      Measurable Wκ ∧ Measurable Wε ∧ (∀y,0 ≤ Wκ y) ∧ (∀y,0 ≤ Wε y) ∧
      MemLp Wκ (ENNReal.ofReal (2*(A*logScale n))) (stdGaussian (tangentSpace w)) ∧
      MemLp Wε (ENNReal.ofReal (4*(A*logScale n))) (stdGaussian (tangentSpace w)) ∧
      eLpNorm Wκ (ENNReal.ofReal (2*(A*logScale n))) (stdGaussian (tangentSpace w)) ≤
        ENNReal.ofReal (planeDampingCoefficient b) ∧
      eLpNorm Wε (ENNReal.ofReal (4*(A*logScale n))) (stdGaussian (tangentSpace w)) ≤
        ENNReal.ofReal (NegativeVotingSmoothErrorTube.tubeConstant (4*A)*logScale n*
          Real.sqrt (logScale n)*Real.exp (1+(2*b+2)/4)) ∧
      ∀ r η : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η → η ≤ K*r^2*logScale n →
      ∀ y : tangentSpace w,
        IntervalControl (fun t=>inverseKappa η (fun j=>inner ℝ (R j) ((y:FSC.Coord d)+(a+t) • w))) (Wκ y) ∧
        IntervalControl (fun t=>smoothPairError n r
          (fun j=>inner ℝ (R j) ((y:FSC.Coord d)+(a+t) • w))/r) (Wε y) := by
  obtain ⟨Nε,hNε⟩:=NegativeVotingDimensionUniformErrorBounds.exists_dimension_uniform_error_tube (4*A) (by linarith)
  obtain ⟨Nκ,hNκ⟩:=exists_dimension_uniform_damping_tube (2*A) K (by linarith) hK
  refine ⟨max Nε Nκ,?_⟩
  intro n hn d k R hR w e hw a b hb ha
  let P:=fun i=>projectedRow w e (R i)
  let c:=fun i=>a*inner ℝ (R i) w
  let v:=fun i=>inner ℝ (R i) w
  have hv i : |v i| ≤ 1:=(abs_real_inner_le_norm _ _).trans (by rw [hw,mul_one]; exact hR i)
  have hP i : ‖P i‖ ≤ 1:=(projectedRow_norm_le w e (R i)).trans (hR i)
  have hc i : (c i)^2 ≤ b*logScale n:=by
    have hs : (v i)^2 ≤ 1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hv i) 2
    calc
      _=a^2*(v i)^2:=by dsimp [c,v]; ring
      _≤a^2*1:=mul_le_mul_of_nonneg_left hs (sq_nonneg a)
      _≤b*logScale n:=by simpa using ha
  obtain ⟨Uκ,hUκM,hUκ0,hUκmem,hUκnorm,hUκcontrol⟩:=
    hNκ n ((le_max_right _ _).trans hn) k P hP c b hb hc
  obtain ⟨Uε,hUεM,hUε0,hUεmem,hUεnorm,hUεcontrol⟩:=
    hNε n ((le_max_left _ _).trans hn) k P hP c b hb hc
  have hmp : MeasurePreserving e (stdGaussian (tangentSpace w)) (stdGaussian (FSC.Coord k)):=
    ⟨e.continuous.measurable,stdGaussian_map e⟩
  let Wκ:=Uκ ∘ e
  let Wε:=Uε ∘ e
  refine ⟨Wκ,Wε,hUκM.comp e.continuous.measurable,hUεM.comp e.continuous.measurable,
    fun y=>hUκ0 _,fun y=>hUε0 _,?_,?_,?_,?_,?_⟩
  · convert hUκmem.comp_measurePreserving hmp using 1
    congr 1; ring
  · convert hUεmem.comp_measurePreserving hmp using 1
    congr 1; ring
  · have hh : eLpNorm Wκ (ENNReal.ofReal ((2*A)*logScale n)) (stdGaussian (tangentSpace w)) ≤
        ENNReal.ofReal (2*Real.exp 1)*ENNReal.ofReal (Real.exp (1+(2*b+2)/4)):=by
      rw [eLpNorm_comp_measurePreserving hUκM.aestronglyMeasurable hmp]
      exact hUκnorm
    convert hh using 1
    · congr 2; ring
    · unfold planeDampingCoefficient
      rw [ENNReal.ofReal_mul (by positivity)]
  · have hh : eLpNorm Wε (ENNReal.ofReal ((4*A)*logScale n)) (stdGaussian (tangentSpace w)) ≤
        ENNReal.ofReal (NegativeVotingSmoothErrorTube.tubeConstant (4*A)*logScale n*Real.sqrt (logScale n))*
          ENNReal.ofReal (Real.exp (1+(2*b+2)/4)):=by
      rw [eLpNorm_comp_measurePreserving hUεM.aestronglyMeasurable hmp]
      exact hUεnorm
    convert hh using 1
    · congr 2; ring
    · rw [ENNReal.ofReal_mul (by
        have hC:=NegativeVotingSmoothErrorTube.tubeConstant_nonneg (4*A) (by linarith)
        have hL:0 ≤ logScale n:=by linarith [logScale_one_le n]
        positivity)]
  · intro r η hr hrange hη hηupper y
    have he (t:ℝ) (j:Fin (n+2)) : inner ℝ (R j) ((y:FSC.Coord d)+(a+t) • w)=
        c j+inner ℝ (P j) (e y)+t*v j:=by
      dsimp [c,P,v]
      rw [inner_add_right,inner_smul_right,projectedRow_inner,e.symm_apply_apply]
      ring
    simp_rw [he]
    have hk:=hUκcontrol r η hr hrange hη hηupper v hv (e y)
    have heps:=hUεcontrol r hr hrange v hv (e y)
    constructor
    · refine ⟨hk.1,?_,?_⟩
      · intro t ht
        rw [abs_of_pos (inverseKappa_pos _ _)]
        exact (hk.2 t ht).1
      · intro t ht
        simpa only [Wκ,Function.comp_apply,zero_mul,add_zero] using (hk.2 t ht).2.2
    · refine ⟨heps.1,?_,?_⟩
      · intro t ht
        rw [abs_div,abs_of_pos hr]
        exact (heps.2 t ht).1
      · intro t ht
        rw [←sub_div,abs_div,abs_of_pos hr]
        simpa only [Wε,Function.comp_apply,zero_mul,add_zero] using (heps.2 t ht).2.2


def normalOUCoefficient (τ a : ℝ) : ℝ :=
  Real.sqrt (normalRowSquare τ (|a|+1))+Real.sqrt (normalDerivativeRowSquare τ (|a|+1))
def tubeErrorCoefficient (A b : ℝ) (n : ℕ) : ℝ :=
  NegativeVotingSmoothErrorTube.tubeConstant (4*A)*logScale n*Real.sqrt (logScale n)*Real.exp (1+(2*b+2)/4)

/-- The actual weighted forcing has a common measurable normal envelope.
Its Lq bound is quantitative and independent of ambient dimension and of any
positive lower bound on the eventual switching amplitude. -/
theorem exists_dimension_uniform_weightedForcing_tube_control
    (A K : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d k : ℕ,
      ∀ (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ), (∀i,‖R i‖ ≤ 1) →
      ∀ (w:FSC.Coord d) (e:tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k), ‖w‖=1 →
      ∀ r η τ a b : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n → 0 ≤ b → a^2 ≤ b*logScale n →
        0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      ∀ i : Fin (n+2), ∃ W : tangentSpace w→ℝ,
      Measurable W ∧ (∀y,0 ≤ W y) ∧
      MemLp W (ENNReal.ofReal (A*logScale n)) (stdGaussian (tangentSpace w)) ∧
      realLp (stdGaussian (tangentSpace w)) (ENNReal.ofReal (A*logScale n)) W ≤
        4*planeDampingCoefficient b*(r*tubeErrorCoefficient A b n*
          (τ⁻¹*(‖D i‖+|a*inner ℝ (D i) w+h i|)+|inner ℝ (D i) w|)+
          normalOUCoefficient τ a*(realLp (stdGaussian (FSC.Coord d)) 2 (fD i)+
            realLp (stdGaussian (FSC.Coord d)) 2 (fu i))/r) ∧
      ∀ᵐ y : tangentSpace w ∂stdGaussian (tangentSpace w),
        IntervalControl (fun t=>weightedForcing R D h η r τ fD fu ((y:FSC.Coord d)+(a+t) • w) i) (W y) := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_common_tube_controls A K hA hK
  refine ⟨N,?_⟩
  intro n hn d k R D h hR w e hw r η τ a b hr hrange hη hηupper hb ha hτ hτ1 hqτ
    fD fu hfDM hfuM hfD hfu i
  let μ:=stdGaussian (tangentSpace w)
  let μ0:=stdGaussian (FSC.Coord d)
  let q:=A*logScale n
  let p:=ENNReal.ofReal q
  let p2:=ENNReal.ofReal (2*q)
  let p4:=ENNReal.ofReal (4*q)
  let native:=ENNReal.ofReal (1+(τ^2)⁻¹)
  have hq : 1 ≤ q:=by dsimp [q]; nlinarith [logScale_one_le n]
  have hq0 : 0<q:=by linarith
  have hp4 : p4 ≤ native:=ENNReal.ofReal_le_ofReal hqτ
  have hp2 : p2 ≤ native:=ENNReal.ofReal_le_ofReal (by dsimp [q] at hq0; linarith)
  have hCp : 0 ≤ normalOUCoefficient τ a:=add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hKp : 0 ≤ planeDampingCoefficient b:=by unfold planeDampingCoefficient; positivity
  have hEp : 0 ≤ tubeErrorCoefficient A b n:=by
    have hc:=NegativeVotingSmoothErrorTube.tubeConstant_nonneg (4*A) (by linarith)
    have hl:0 ≤ logScale n:=by linarith [logScale_one_le n]
    unfold tubeErrorCoefficient
    positivity
  obtain ⟨Wκ,Wε,hκM,hεM,hκ0,hε0,hκmem,hεmem,hκnorm,hεnorm,hcontrol⟩:=hN n hn d k R hR w e hw a b hb ha
  obtain ⟨UD,hUDM,hUD0,hUDmem,hUDnorm,hUDcontrol⟩:=ambient_normal_tube_envelope w hw e hτ hτ1 a
    (fD i) (hfDM i) (hfD i)
  obtain ⟨UU,hUUM,hUU0,hUUmem,hUUnorm,hUUcontrol⟩:=ambient_normal_tube_envelope w hw e hτ hτ1 a
    (fu i) (hfuM i) (hfu i)
  let base:=fun y:tangentSpace w=>inner ℝ (D i) ((y:FSC.Coord d)+a • w)+h i
  let slope:=inner ℝ (D i) w
  let WL:=fun y:tangentSpace w=>|base y|+|slope|
  let Kl:=τ⁻¹*(‖D i‖+|a*inner ℝ (D i) w+h i|)+|slope|
  have hbase:= (eLpNorm_le_eLpNorm_of_exponent_le (μ:=μ) (f:=base) hp4).trans
    (affine_plane_lq_le w e τ hτ hτ1 a (h i) (D i))
  have hbasemem : MemLp base p4 μ:=hbase.trans_lt ENNReal.ofReal_lt_top
  have hbasememabs : MemLp (fun y=>|base y|) p4 μ:=by simpa only [Real.norm_eq_abs] using hbasemem.norm
  have hp4one : 1 ≤ p4:=by exact_mod_cast ENNReal.ofReal_le_ofReal (show (1:ℝ) ≤ 4*q by linarith)
  have hconst : eLpNorm (fun _:tangentSpace w=>|slope|) p4 μ=ENNReal.ofReal |slope|:=by
    rw [eLpNorm_const' _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hp4one)) ENNReal.ofReal_ne_top]
    simp only [μ,measure_univ,ENNReal.one_rpow,mul_one,Real.enorm_eq_ofReal_abs,abs_abs]
  have hWLnorm : eLpNorm WL p4 μ ≤ ENNReal.ofReal Kl:=by
    have hh:=eLpNorm_add_le (μ:=μ) (f:=fun y=>|base y|) (g:=fun _=>|slope|) hp4one
    change eLpNorm WL p4 μ ≤ _ at hh
    have heabs : eLpNorm (fun y=>|base y|) p4 μ=eLpNorm base p4 μ:=by
      simpa only [Real.norm_eq_abs] using eLpNorm_norm base hbasemem.aestronglyMeasurable
    rw [heabs,hconst] at hh
    refine hh.trans ((add_le_add hbase le_rfl).trans_eq ?_)
    exact (ENNReal.ofReal_add (by positivity) (abs_nonneg _)).symm
  have hUDnorm' : eLpNorm UD p2 μ ≤ ENNReal.ofReal (normalOUCoefficient τ a*realLp μ0 2 (fD i)):=by
    refine ((eLpNorm_le_eLpNorm_of_exponent_le hp2).trans hUDnorm).trans_eq ?_
    rw [ENNReal.ofReal_mul hCp,realLp,ENNReal.ofReal_toReal (hfD i).eLpNorm_ne_top]
    rfl
  have hUUnorm' : eLpNorm (fun y=>-UU y) p2 μ ≤ ENNReal.ofReal (normalOUCoefficient τ a*realLp μ0 2 (fu i)):=by
    have hh:= (eLpNorm_le_eLpNorm_of_exponent_le (μ:=μ) (f:=UU) hp2).trans hUUnorm
    rw [show (fun y=>-UU y)= -UU from rfl,eLpNorm_neg]
    refine hh.trans_eq ?_
    rw [ENNReal.ofReal_mul hCp,realLp,ENNReal.ofReal_toReal (hfu i).eLpNorm_ne_top]
    rfl
  have hWL0 y : 0 ≤ WL y:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hWLM : Measurable WL:=by dsimp [WL,base]; fun_prop
  have hprod := weighted_product_norm_le q r (planeDampingCoefficient b) (tubeErrorCoefficient A b n)
    Kl (normalOUCoefficient τ a*realLp μ0 2 (fD i))
    (normalOUCoefficient τ a*realLp μ0 2 (fu i)) hq hr hKp hEp
    (by dsimp [Kl]; positivity) (mul_nonneg hCp (realLp_nonneg _ _))
    (mul_nonneg hCp (realLp_nonneg _ _)) Wκ Wε WL UD (fun y=>-UU y)
    hκnorm hεnorm hWLnorm hUDnorm' hUUnorm'
  let W:=fun y:tangentSpace w=>4*Wκ y*(r*Wε y*WL y+(UD y+UU y)/r)
  have heprod : (fun y=>Wκ y*(r*Wε y*|WL y|+|UD y-(-UU y)|/r))=
      (fun y=>Wκ y*(r*Wε y*WL y+(UD y+UU y)/r)):=by
    funext y
    rw [abs_of_nonneg (hWL0 y),sub_neg_eq_add,abs_of_nonneg (add_nonneg (hUD0 y) (hUU0 y))]
  rw [heprod] at hprod
  have hWM : Measurable W:=by dsimp [W]; fun_prop
  have hW0 y : 0 ≤ W y:=by
    dsimp [W]
    exact mul_nonneg (mul_nonneg (by norm_num) (hκ0 y))
      (add_nonneg (mul_nonneg (mul_nonneg hr.le (hε0 y)) (hWL0 y))
        (div_nonneg (add_nonneg (hUD0 y) (hUU0 y)) hr.le))
  refine ⟨W,hWM,hW0,?_,?_,?_⟩
  · convert hprod.1.const_mul 4 using 1
    funext y
    dsimp [W]
    ring
  · have heW : W=(fun y=>4*(Wκ y*(r*Wε y*WL y+(UD y+UU y)/r))):=by funext y; dsimp [W]; ring
    rw [heW,realLp_const_mul]
    rw [abs_of_pos (by norm_num : (0:ℝ)<4)]
    refine (mul_le_mul_of_nonneg_left hprod.2 (by norm_num : (0:ℝ) ≤ 4)).trans_eq ?_
    dsimp [Kl,slope,μ0]
    ring
  · filter_upwards [hUDcontrol,hUUcontrol] with y hUd hUu
    have hUDc : IntervalControl (fun t=>ambientAverage τ (fD i) ((y:FSC.Coord d)+(a+t) • w)) (UD y):=
      ⟨hUd.1,fun t ht=>(hUd.2 t ht).1,fun t ht=>by simpa only [add_zero] using (hUd.2 t ht).2.2⟩
    have hUUc : IntervalControl (fun t=>ambientAverage τ (fu i) ((y:FSC.Coord d)+(a+t) • w)) (UU y):=
      ⟨hUu.1,fun t ht=>(hUu.2 t ht).1,fun t ht=>by simpa only [add_zero] using (hUu.2 t ht).2.2⟩
    have hlc : IntervalControl (fun t=>inner ℝ (D i) ((y:FSC.Coord d)+(a+t) • w)+h i) (WL y):=by
      have he (t:ℝ) : inner ℝ (D i) ((y:FSC.Coord d)+(a+t) • w)+h i=base y+t*slope:=by
        dsimp [base,slope]
        simp only [inner_add_right,inner_smul_right]
        ring
      simp_rw [he]
      exact affine_interval_control (base y) slope
    have hh:=weighted_forcing_interval_control r hr _ _ _ _ _ _ _ _ _ _
      (hcontrol r η hr hrange hη hηupper y).1 (hcontrol r η hr hrange hη hηupper y).2 hlc hUDc hUUc
    convert hh using 1
    · funext t
      dsimp [weightedForcing]
      field_simp

end NegativeVotingStructuredSwitchingTube
