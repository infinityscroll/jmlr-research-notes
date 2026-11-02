import GaussianRegularHighTailCrossKernel
import GaussianCellOUContinuity

/-! A common tangential envelope for the literal two-normal quotient kernel.
The full-measure set precedes both real normal parameters. Thus later
substitution of a current-plane chart does not use an ambient-AE identity
on a null hyperplane. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped ENNReal NNReal
namespace NegativeVotingRegularHighTailCross
open NegativeVotingNormalTrace NegativeVotingNormalDerivatives
  NegativeVotingRegularHighTailCrossKernel NegativeVotingHypercontractivity
  NegativeVotingSmoothingComposition NegativeVotingRareLabelHighChaos
variable {n : ℕ}

abbrev pairGaussian : Measure (ℝ×ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

def pairFiberNorm (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (x : Fin n→ℝ) : ℝ :=
  Real.sqrt (∫ y,f (x,y)^2 ∂pairGaussian)

theorem pairFiberNorm_memLp_norm (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ)
    (hf : MemLp f 2 ((γFin n).prod pairGaussian)) :
    MemLp (pairFiberNorm f) 2 (γFin n) ∧
      eLpNorm (pairFiberNorm f) 2 (γFin n)=eLpNorm f 2 ((γFin n).prod pairGaussian) := by
  have hm : AEStronglyMeasurable (pairFiberNorm f) (γFin n) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (hf.aestronglyMeasurable.pow 2).integral_prod_right'
  have hs : (fun x=>pairFiberNorm f x^2)=fun x=>∫ y,f (x,y)^2 ∂pairGaussian := by
    funext x
    exact Real.sq_sqrt (integral_nonneg fun _=>sq_nonneg _)
  have hi : Integrable (fun x=>pairFiberNorm f x^2) (γFin n) := by
    rw [hs]
    exact hf.integrable_sq.integral_prod_left
  have hH := (memLp_two_iff_integrable_sq hm).mpr hi
  refine ⟨hH,?_⟩
  rw [eLpNorm_two_eq_sqrt_integral_sq hH,eLpNorm_two_eq_sqrt_integral_sq hf,hs,
    ←integral_prod (fun z=>f z^2) hf.integrable_sq]

theorem pairFiberNorm_measurable (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hf : Measurable f) :
    Measurable (pairFiberNorm f) :=
  Real.continuous_sqrt.measurable.comp
    ((hf.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable)

def quotientSection (τ a b : ℝ) (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (x : Fin n→ℝ) : ℝ :=
  ∫ y,twoNormalQuotientKernel τ a b y*f (x,y) ∂pairGaussian

def quotientTrace (τ a b : ℝ) (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) : (Fin n→ℝ)→ℝ :=
  gaussianAverage τ (quotientSection τ a b f)

theorem quotientSection_measurable (τ a b : ℝ)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hf : Measurable f) :
    Measurable (quotientSection τ a b f) :=
  (((twoNormalQuotientKernel_measurable τ a b).comp measurable_snd).mul hf).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem quotientSection_norm_le_fiber (τ a b : ℝ) (hτ : τ^2 ≤ 1/4)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (x : Fin n→ℝ)
    (hx : MemLp (fun y=>f (x,y)) 2 pairGaussian) :
    ‖quotientSection τ a b f x‖ ≤
      Real.sqrt (8*τ^2*Real.exp (τ^2*(a^2+b^2)))*pairFiberNorm f x := by
  have hh := norm_integral_mul_le_l2 (twoNormalQuotientKernel_memLp (by linarith : τ^2 < 1) a b) hx
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt (twoNormalQuotient_row_le τ a b (a^2+b^2) hτ le_rfl))
    (Real.sqrt_nonneg _))

/-- One common Gaussian-full-measure set for every real pair of output
normal coordinates. Dependence of those coordinates on a later free Gaussian
coordinate is therefore legitimate. -/
theorem ae_quotientTrace_bound (τ : ℝ) (hτ : τ^2 ≤ 1/4)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod pairGaussian)) :
    ∀ᵐ x ∂γFin n,∀ a b : ℝ,‖quotientTrace τ a b f x‖ ≤
      Real.sqrt (8*τ^2*Real.exp (τ^2*(a^2+b^2)))*
        gaussianAverage τ (pairFiberNorm f) x := by
  have hv : 0 ≤ 1-τ^2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n:=n) τ (Real.sqrt (1-τ^2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n:=n) τ (Real.sqrt (1-τ^2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv];ring)⟩
  have hsec : ∀ᵐ p ∂γFin n,MemLp (fun y=>f (p,y)) 2 pairGaussian := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,hf.integrable_sq.prod_right_ae] with p hpm hpi
    exact (memLp_two_iff_integrable_sq hpm).mpr hpi
  have hpull := hmix.quasiMeasurePreserving.ae hsec
  have hi := hmix.integrable_comp_of_integrable
    ((pairFiberNorm_memLp_norm f hf).1.integrable (by norm_num))
  filter_upwards [Measure.ae_ae_of_ae_prod hpull,hi.prod_right_ae] with x hx hxi
  intro a b
  have hb : ∀ᵐ z ∂γFin n,
      ‖quotientSection τ a b f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j)‖ ≤
        Real.sqrt (8*τ^2*Real.exp (τ^2*(a^2+b^2)))*
          pairFiberNorm f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j) := by
    filter_upwards [hx] with z hz
    exact quotientSection_norm_le_fiber τ a b hτ f _ hz
  have hsm : AEStronglyMeasurable
      (fun z:Fin n→ℝ=>quotientSection τ a b f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j)) (γFin n) :=
    ((quotientSection_measurable τ a b f hfm).comp (by fun_prop)).aestronglyMeasurable
  have hright : Integrable (fun z:Fin n→ℝ=>Real.sqrt (8*τ^2*Real.exp (τ^2*(a^2+b^2)))*
      pairFiberNorm f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j)) (γFin n) := hxi.const_mul _
  have hleft := hright.mono' hsm hb
  change ‖∫ z,quotientSection τ a b f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j) ∂γFin n‖ ≤ _
  calc
    _ ≤ ∫ z,‖quotientSection τ a b f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j)‖ ∂γFin n :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z,Real.sqrt (8*τ^2*Real.exp (τ^2*(a^2+b^2)))*
        pairFiberNorm f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j) ∂γFin n :=
      integral_mono_ae hleft.norm hright hb
    _ = _ := integral_const_mul _ _

/-- Tangential smoothing produces one nonnegative Lq envelope, independent
of the output normal coordinates, without an ambient dimension constant. -/
theorem quotientTrace_common_envelope (τ q : ℝ) (hτ : 0 < τ) (hτsmall : τ^2 ≤ 1/4)
    (hq : 0 < q) (hqt : q ≤ 1+(τ^2)⁻¹)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod pairGaussian)) :
    ∃ H : (Fin n→ℝ)→ℝ,Measurable H ∧ MemLp H (ENNReal.ofReal q) (γFin n) ∧
      (∀ x,0 ≤ H x) ∧ eLpNorm H (ENNReal.ofReal q) (γFin n) ≤
        eLpNorm f 2 ((γFin n).prod pairGaussian) ∧
      ∀ᵐ x ∂γFin n,∀ a b : ℝ,‖quotientTrace τ a b f x‖ ≤
        Real.sqrt (8*τ^2*Real.exp (τ^2*(a^2+b^2)))*H x := by
  let H := gaussianAverage τ (pairFiberNorm f)
  have hτ1 : τ < 1 := by nlinarith
  have hF := pairFiberNorm_memLp_norm f hf
  have hnorm : eLpNorm H (ENNReal.ofReal q) (γFin n) ≤ eLpNorm (pairFiberNorm f) 2 (γFin n) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqt)).trans
      (memLp_gaussian_average_l2_to_lq τ hτ hτ1 _ hF.1)
  refine ⟨H,gaussianAverage_measurable τ _ (pairFiberNorm_measurable f hfm),
    hnorm.trans_lt hF.1,?_,?_,ae_quotientTrace_bound τ hτsmall f hfm hf⟩
  · intro x
    exact integral_nonneg fun _=>Real.sqrt_nonneg _
  · exact hnorm.trans_eq hF.2

section ProductNorm
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem eLpNorm_product_mul (q : ℝ) (hq : 0 < q)
    (f : X→ℝ) (g : Y→ℝ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g ν) :
    eLpNorm (fun p:X×Y=>f p.1*g p.2) (ENNReal.ofReal q) (μ.prod ν)=
      eLpNorm f (ENNReal.ofReal q) μ*eLpNorm g (ENNReal.ofReal q) ν := by
  have hp : ENNReal.ofReal q≠0 := by positivity
  have hfg : AEStronglyMeasurable (fun p:X×Y=>f p.1*g p.2) (μ.prod ν) := hf.comp_fst.mul hg.comp_snd
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp ENNReal.ofReal_ne_top hfg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp ENNReal.ofReal_ne_top hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp ENNReal.ofReal_ne_top hg]
  simp only [ENNReal.toReal_ofReal hq.le,enorm_mul,ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rw [lintegral_prod_mul (f:=fun x:X=>‖f x‖ₑ^q) (g:=fun y:Y=>‖g y‖ₑ^q) (by fun_prop) (by fun_prop),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1/q)]

end ProductNorm

def freeNormalEnvelope (q : ℝ) (z : ℝ) : ℝ := Real.exp (z^2/(4*q))

theorem freeNormalEnvelope_norm_le (q : ℝ) (hq : 0 < q) :
    eLpNorm (freeNormalEnvelope q) (ENNReal.ofReal q) (gaussianReal 0 1) ≤
      (ENNReal.ofReal 2)^(1/q) := by
  let G := fun z:ℝ=>Real.exp (z^2/4)
  have hi : Integrable G (gaussianReal 0 1) := NegativeVotingSquareExponential.gaussian_square_exp_integrable
  have he : freeNormalEnvelope q=fun z:ℝ=>‖G z‖^(1/q) := by
    funext z
    simp only [freeNormalEnvelope,G,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),←Real.exp_mul]
    congr 1
    field_simp
  have hp : ENNReal.ofReal q*ENNReal.ofReal (1/q)=1 := by
    rw [←ENNReal.ofReal_mul hq.le]
    simp [hq.ne']
  rw [he,eLpNorm_norm_rpow G hi.aestronglyMeasurable (by positivity),hp,
    eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ←ofReal_integral_norm_eq_lintegral_enorm hi]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply ENNReal.ofReal_le_ofReal
  simpa only [G,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
    NegativeVotingSquareExponential.integral_gaussian_square_exp_le_two

theorem freeNormalEnvelope_memLp (q : ℝ) (hq : 0 < q) :
    MemLp (freeNormalEnvelope q) (ENNReal.ofReal q) (gaussianReal 0 1) :=
  (freeNormalEnvelope_norm_le q hq).trans_lt (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)

theorem sqrt_exp_eq (x : ℝ) : Real.sqrt (Real.exp x)=Real.exp (x/2) := by
  have he : Real.exp (x/2)^2=Real.exp x := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  nlinarith [Real.sq_sqrt (Real.exp_pos x).le,Real.sqrt_nonneg (Real.exp x),Real.exp_pos (x/2)]

theorem quotient_row_factor_le (τ q A a b z : ℝ) (hq : 0 < q)
    (hqt : q*τ^2 ≤ 1/2) (hab : a^2+b^2 ≤ A^2+z^2) :
    Real.sqrt (8*τ^2*Real.exp (τ^2*(a^2+b^2))) ≤
      (Real.sqrt (8*τ^2)*Real.exp (τ^2*A^2/2))*freeNormalEnvelope q z := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 8*τ^2),sqrt_exp_eq]
  unfold freeNormalEnvelope
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  have ht : τ^2 ≤ 1/(2*q) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*q)).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hab (sq_nonneg τ)
  have hz := mul_le_mul_of_nonneg_right ht (sq_nonneg z)
  have he : (1/(2*q))*z^2/2=z^2/(4*q) := by ring
  nlinarith only [hh,hz,he]

/-- Full two-normal-plane envelope. The normal coordinates may be any
measurable or nonmeasurable functions obeying the orthogonal radius bound;
the dominating function is measurable and has the displayed actual Lq norm.
Applications to a continuous OU potential inherit its Lq estimate by domination. -/
theorem quotientTrace_plane_envelope (τ q A : ℝ) (hτ : 0 < τ) (hq : 2 ≤ q)
    (hqt : q*τ^2 ≤ 1/2) (a b : ℝ→ℝ)
    (hab : ∀ z,(a z)^2+(b z)^2 ≤ A^2+z^2)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod pairGaussian)) :
    ∃ G : (Fin n→ℝ)×ℝ→ℝ,Measurable G ∧ MemLp G (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)) ∧
      (∀ p,0 ≤ G p) ∧
      eLpNorm G (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)) ≤
        ENNReal.ofReal (Real.sqrt (8*τ^2)*Real.exp (τ^2*A^2/2))*(ENNReal.ofReal 2)^(1/q)*
          eLpNorm f 2 ((γFin n).prod pairGaussian) ∧
      ∀ᵐ p ∂(γFin n).prod (gaussianReal 0 1),‖quotientTrace τ (a p.2) (b p.2) f p.1‖ ≤ G p := by
  have hq0 : 0 < q := by linarith
  have hτsmall : τ^2 ≤ 1/4 := by nlinarith [sq_nonneg τ]
  have hqrt : q ≤ 1+(τ^2)⁻¹ := by
    have hs : 0 < τ^2 := sq_pos_of_pos hτ
    have hh : q ≤ 1/τ^2 := (le_div_iff₀ hs).mpr (by linarith)
    simpa only [one_div] using (show q ≤ 1+1/τ^2 by linarith)
  obtain ⟨H,hHm,hH,hH0,hHnorm,hbound⟩ := quotientTrace_common_envelope τ q hτ hτsmall hq0 hqrt f hfm hf
  let C := Real.sqrt (8*τ^2)*Real.exp (τ^2*A^2/2)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  let G := fun p:(Fin n→ℝ)×ℝ=>C*(H p.1*freeNormalEnvelope q p.2)
  have hGm : Measurable G := by unfold G freeNormalEnvelope;fun_prop
  have hGnorm : eLpNorm G (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)) ≤
      ENNReal.ofReal C*(ENNReal.ofReal 2)^(1/q)*eLpNorm f 2 ((γFin n).prod pairGaussian) := by
    change eLpNorm (C • fun p:(Fin n→ℝ)×ℝ=>H p.1*freeNormalEnvelope q p.2)
      (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)) ≤ _
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,abs_of_nonneg hC,
      eLpNorm_product_mul q hq0 H (freeNormalEnvelope q) hH.aestronglyMeasurable
        (by unfold freeNormalEnvelope;fun_prop)]
    calc
      _ ≤ ENNReal.ofReal C*(eLpNorm f 2 ((γFin n).prod pairGaussian)*(ENNReal.ofReal 2)^(1/q)) := by
        exact mul_le_mul_right (mul_le_mul hHnorm (freeNormalEnvelope_norm_le q hq0) bot_le bot_le) _
      _ = _ := by ac_rfl
  have hGfin : ENNReal.ofReal C*(ENNReal.ofReal 2)^(1/q)*eLpNorm f 2 ((γFin n).prod pairGaussian) < ∞ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)) hf
  refine ⟨G,hGm,hGnorm.trans_lt hGfin,?_,hGnorm,?_⟩
  · intro p
    exact mul_nonneg hC (mul_nonneg (hH0 _) (Real.exp_pos _).le)
  · have hpull : ∀ᵐ p ∂(γFin n).prod (gaussianReal 0 1),∀ u v : ℝ,
        ‖quotientTrace τ u v f p.1‖ ≤ Real.sqrt (8*τ^2*Real.exp (τ^2*(u^2+v^2)))*H p.1 :=
      MeasureTheory.Measure.QuasiMeasurePreserving.ae
        (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ:=γFin n) (ν:=gaussianReal 0 1)) hbound
    filter_upwards [hpull] with p hp
    exact (hp (a p.2) (b p.2)).trans (by
      have hh := mul_le_mul_of_nonneg_right (quotient_row_factor_le τ q A (a p.2) (b p.2) p.2 hq0 hqt (hab p.2)) (hH0 p.1)
      convert hh using 1 <;> dsimp only [G,C] <;> ring)

def pairKernel (τ a b : ℝ) (y : ℝ×ℝ) : ℝ := normalKernel τ a y.1*normalKernel τ b y.2

theorem pairKernel_measurable (τ a b : ℝ) : Measurable (pairKernel τ a b) :=
  ((normalKernel_measurable τ a).comp measurable_fst).mul
    ((normalKernel_measurable τ b).comp measurable_snd)

theorem pairKernel_memLp (τ a b : ℝ) (hτ : τ^2 < 1) :
    MemLp (pairKernel τ a b) 2 pairGaussian := by
  apply (memLp_two_iff_integrable_sq (pairKernel_measurable τ a b).aestronglyMeasurable).mpr
  simpa only [pairKernel,mul_pow] using
    (normalKernel_memLp hτ a).integrable_sq.mul_prod (normalKernel_memLp hτ b).integrable_sq

theorem pairKernel_integral_sq (τ a b : ℝ) (hτ : τ^2 < 1) :
    (∫ y,pairKernel τ a b y^2 ∂pairGaussian)=normalRowSquare τ a*normalRowSquare τ b := by
  simp only [pairKernel,mul_pow]
  rw [integral_prod_mul (fun y:ℝ=>normalKernel τ a y^2) (fun y:ℝ=>normalKernel τ b y^2),
    integral_normalKernel_sq_eq hτ a,integral_normalKernel_sq_eq hτ b]

def pairSection (τ a b : ℝ) (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (x : Fin n→ℝ) : ℝ :=
  ∫ y,pairKernel τ a b y*f (x,y) ∂pairGaussian

def pairTrace (τ a b : ℝ) (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) : (Fin n→ℝ)→ℝ :=
  gaussianAverage τ (pairSection τ a b f)

theorem pairSection_measurable (τ a b : ℝ) (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hf : Measurable f) :
    Measurable (pairSection τ a b f) :=
  (((pairKernel_measurable τ a b).comp measurable_snd).mul hf).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

theorem pairSection_norm_le (τ a b : ℝ) (hτ : τ^2 < 1)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (x : Fin n→ℝ)
    (hx : MemLp (fun y=>f (x,y)) 2 pairGaussian) :
    ‖pairSection τ a b f x‖ ≤ Real.sqrt (normalRowSquare τ a*normalRowSquare τ b)*pairFiberNorm f x := by
  have hh := norm_integral_mul_le_l2 (pairKernel_memLp τ a b hτ) hx
  rw [pairKernel_integral_sq τ a b hτ] at hh
  exact hh

/-- Exact odd-part extraction for every normal coordinate, including zero. -/
theorem quotientSection_mul (τ a b : ℝ) (hτ : τ^2 < 1)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (x : Fin n→ℝ)
    (hx : MemLp (fun y=>f (x,y)) 2 pairGaussian) :
    a*quotientSection τ a b f x=(pairSection τ a b f x-pairSection τ (-a) b f x)/2 := by
  have haI : Integrable (fun y=>pairKernel τ a b y*f (x,y)) pairGaussian :=
    (pairKernel_memLp τ a b hτ).integrable_mul hx
  have hnI : Integrable (fun y=>pairKernel τ (-a) b y*f (x,y)) pairGaussian :=
    (pairKernel_memLp τ (-a) b hτ).integrable_mul hx
  unfold quotientSection pairSection
  rw [←integral_const_mul,←integral_sub haI hnI,←integral_div]
  apply integral_congr_ae
  filter_upwards with y
  have hh := normalQuotientKernel_mul τ a y.1
  dsimp only [twoNormalQuotientKernel,pairKernel]
  nlinarith only [congrArg (fun t:ℝ=>t*normalKernel τ b y.2*f (x,y)) hh]

/-- The exact product-Gaussian quotient identity holds on one tangential
full-measure set before both real normal coordinates are chosen. -/
theorem ae_quotientTrace_mul (τ : ℝ) (hτ : τ^2 < 1)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod pairGaussian)) :
    ∀ᵐ x ∂γFin n,∀ a b : ℝ,
      a*quotientTrace τ a b f x=(pairTrace τ a b f x-pairTrace τ (-a) b f x)/2 := by
  have hv : 0 ≤ 1-τ^2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n:=n) τ (Real.sqrt (1-τ^2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n:=n) τ (Real.sqrt (1-τ^2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv];ring)⟩
  have hsec : ∀ᵐ p ∂γFin n,MemLp (fun y=>f (p,y)) 2 pairGaussian := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,hf.integrable_sq.prod_right_ae] with p hpm hpi
    exact (memLp_two_iff_integrable_sq hpm).mpr hpi
  have hpull := hmix.quasiMeasurePreserving.ae hsec
  have hi := hmix.integrable_comp_of_integrable
    ((pairFiberNorm_memLp_norm f hf).1.integrable (by norm_num))
  filter_upwards [Measure.ae_ae_of_ae_prod hpull,hi.prod_right_ae] with x hx hxi
  intro a b
  have hint (u v : ℝ) : Integrable
      (fun z:Fin n→ℝ=>pairSection τ u v f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j)) (γFin n) := by
    have hb : ∀ᵐ z ∂γFin n,
        ‖pairSection τ u v f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j)‖ ≤
          Real.sqrt (normalRowSquare τ u*normalRowSquare τ v)*
            pairFiberNorm f (fun j=>τ*x j+Real.sqrt (1-τ^2)*z j) := by
      filter_upwards [hx] with z hz
      exact pairSection_norm_le τ u v hτ f _ hz
    exact (hxi.const_mul _).mono'
      (((pairSection_measurable τ u v f hfm).comp (by fun_prop)).aestronglyMeasurable) hb
  unfold quotientTrace pairTrace gaussianAverage
  rw [←integral_const_mul,←integral_sub (hint a b) (hint (-a) b),←integral_div]
  apply integral_congr_ae
  filter_upwards [hx] with z hz
  exact quotientSection_mul τ a b hτ f _ hz

theorem normalKernel_joint_measurable (τ : ℝ) (hτ : τ^2 < 1) :
    Measurable (fun p:ℝ×ℝ=>normalKernel τ p.1 p.2) := by
  have he : (fun p:ℝ×ℝ=>normalKernel τ p.1 p.2)=fun p:ℝ×ℝ=>
      (Real.sqrt (1-τ^2))⁻¹*Real.exp (-(p.2-τ*p.1)^2/(2*(1-τ^2))+p.2^2/2) :=
    funext fun p=>normalKernel_exp hτ p.1 p.2
  rw [he]
  fun_prop

theorem normalQuotientKernel_joint_measurable (τ : ℝ) (hτ : τ^2 < 1) :
    Measurable (fun p:ℝ×ℝ=>normalQuotientKernel τ p.1 p.2) := by
  unfold normalQuotientKernel
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · exact (normalDerivativeKernel_measurable τ 0).comp measurable_snd
  · have hn : Measurable (fun p:ℝ×ℝ=>normalKernel τ (-p.1) p.2) :=
      (normalKernel_joint_measurable τ hτ).comp (show Measurable (fun p:ℝ×ℝ=>(-p.1,p.2)) by fun_prop)
    exact ((normalKernel_joint_measurable τ hτ).sub hn).div
      (show Measurable (fun p:ℝ×ℝ=>2*p.1) by fun_prop)

theorem quotientSection_joint_measurable (τ : ℝ) (hτ : τ^2 < 1)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hf : Measurable f) :
    Measurable (fun p:(Fin n→ℝ)×(ℝ×ℝ)=>quotientSection τ p.2.1 p.2.2 f p.1) := by
  have hk : Measurable (fun p:((Fin n→ℝ)×(ℝ×ℝ))×(ℝ×ℝ)=>
      twoNormalQuotientKernel τ p.1.2.1 p.1.2.2 p.2*f (p.1.1,p.2)) := by
    unfold twoNormalQuotientKernel
    have h1 := (normalQuotientKernel_joint_measurable τ hτ).comp
      (show Measurable (fun p:((Fin n→ℝ)×(ℝ×ℝ))×(ℝ×ℝ)=>(p.1.2.1,p.2.1)) by fun_prop)
    have h2 := (normalKernel_joint_measurable τ hτ).comp
      (show Measurable (fun p:((Fin n→ℝ)×(ℝ×ℝ))×(ℝ×ℝ)=>(p.1.2.2,p.2.2)) by fun_prop)
    have h3 := hf.comp
      (show Measurable (fun p:((Fin n→ℝ)×(ℝ×ℝ))×(ℝ×ℝ)=>(p.1.1,p.2)) by fun_prop)
    exact (h1.mul h2).mul h3
  exact hk.stronglyMeasurable.integral_prod_right'.measurable

theorem quotientTrace_joint_measurable (τ : ℝ) (hτ : τ^2 < 1)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hf : Measurable f) :
    Measurable (fun p:(Fin n→ℝ)×(ℝ×ℝ)=>quotientTrace τ p.2.1 p.2.2 f p.1) := by
  have hk : Measurable (fun p:((Fin n→ℝ)×(ℝ×ℝ))×(Fin n→ℝ)=>
      quotientSection τ p.1.2.1 p.1.2.2 f (fun j=>τ*p.1.1 j+Real.sqrt (1-τ^2)*p.2 j)) :=
    (quotientSection_joint_measurable τ hτ f hf).comp
      (show Measurable (fun p:((Fin n→ℝ)×(ℝ×ℝ))×(Fin n→ℝ)=>
        ((fun j=>τ*p.1.1 j+Real.sqrt (1-τ^2)*p.2 j),p.1.2)) by fun_prop)
  exact hk.stronglyMeasurable.integral_prod_right'.measurable

/-- Actual Lq restriction bound in arbitrary orthogonal two-normal plane
coordinates. Both normal coordinates may vary along the free Gaussian
coordinate. The input is an arbitrary measurable L2 function. -/
theorem quotientTrace_plane_norm_le (τ q A : ℝ) (hτ : 0 < τ) (hq : 2 ≤ q)
    (hqt : q*τ^2 ≤ 1/2) (a b : ℝ→ℝ) (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ z,(a z)^2+(b z)^2 ≤ A^2+z^2)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod pairGaussian)) :
    MemLp (fun p:(Fin n→ℝ)×ℝ=>quotientTrace τ (a p.2) (b p.2) f p.1)
      (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)) ∧
    eLpNorm (fun p:(Fin n→ℝ)×ℝ=>quotientTrace τ (a p.2) (b p.2) f p.1)
      (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)) ≤
        ENNReal.ofReal (Real.sqrt (8*τ^2)*Real.exp (τ^2*A^2/2))*(ENNReal.ofReal 2)^(1/q)*
          eLpNorm f 2 ((γFin n).prod pairGaussian) := by
  have hs : τ^2 < 1 := by nlinarith [sq_nonneg τ]
  have hmeas : Measurable (fun p:(Fin n→ℝ)×ℝ=>quotientTrace τ (a p.2) (b p.2) f p.1) :=
    (quotientTrace_joint_measurable τ hs f hfm).comp
      (show Measurable (fun p:(Fin n→ℝ)×ℝ=>(p.1,(a p.2,b p.2))) by fun_prop)
  obtain ⟨G,hGm,hG,hG0,hGn,hGb⟩ := quotientTrace_plane_envelope τ q A hτ hq hqt a b hab f hfm hf
  have hdom : ∀ᵐ p ∂(γFin n).prod (gaussianReal 0 1),
      ‖quotientTrace τ (a p.2) (b p.2) f p.1‖ ≤ ‖G p‖ := by
    filter_upwards [hGb] with p hp
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hG0 p)] using hp
  exact ⟨hG.mono hmeas.aestronglyMeasurable hdom,
    (eLpNorm_mono_ae hmeas.aestronglyMeasurable hdom).trans hGn⟩

end NegativeVotingRegularHighTailCross
