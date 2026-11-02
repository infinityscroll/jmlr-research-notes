import GaussianNormalDerivatives
import GaussianNormalTraceAllExponents
import GaussianRareLabelHighChaos
import GaussianSquareExponential

/-! Two-normal-coordinate Mehler kernels and the literal antisymmetric
quotient needed on a current facet with a different regular reflection
normal. The existing normal-derivative foundation is imported unchanged. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped ENNReal NNReal
namespace NegativeVotingRegularHighTailCrossKernel
open NegativeVotingNormalTrace NegativeVotingNormalTraceAllExponents
  NegativeVotingNormalDerivatives

abbrev normalDerivativeKernel := normalKernelDerivative

 theorem normalDerivativeKernel_measurable (τ a : ℝ) : Measurable (normalDerivativeKernel τ a) :=
  normalKernelDerivative_measurable τ a

 theorem normalDerivativeKernel_memLp {τ : ℝ} (hτ : τ^2 < 1) (a : ℝ) :
    MemLp (normalDerivativeKernel τ a) 2 (gaussianReal 0 1) :=
  normalKernelDerivative_memLp hτ a

 theorem integral_normalDerivativeKernel_sq {τ : ℝ} (hτ : τ^2 < 1) (a : ℝ) :
    (∫ y,(normalDerivativeKernel τ a y)^2 ∂gaussianReal 0 1)=
      normalRowSquare τ a*(τ^2/(1-τ^4)+τ^4*a^2/(1+τ^2)^2) :=
  integral_normalKernelDerivative_sq hτ a

def twoNormalDerivativeKernel (τ a b : ℝ) (y : ℝ×ℝ) : ℝ :=
  normalDerivativeKernel τ a y.1*normalKernel τ b y.2

theorem twoNormalDerivativeKernel_memLp {τ : ℝ} (hτ : τ^2 < 1) (a b : ℝ) :
    MemLp (twoNormalDerivativeKernel τ a b) 2 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hm : Measurable (twoNormalDerivativeKernel τ a b) :=
    ((normalDerivativeKernel_measurable τ a).comp measurable_fst).mul
      ((normalKernel_measurable τ b).comp measurable_snd)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  simpa only [twoNormalDerivativeKernel,mul_pow] using
    (normalDerivativeKernel_memLp hτ a).integrable_sq.mul_prod
      (normalKernel_memLp hτ b).integrable_sq

/-- The two-coordinate derivative row is the exact ingredient for a current
plane and a different regular reflection normal. -/
theorem integral_twoNormalDerivativeKernel_sq {τ : ℝ} (hτ : τ^2 < 1) (a b : ℝ) :
    (∫ y,(twoNormalDerivativeKernel τ a b y)^2 ∂(gaussianReal 0 1).prod (gaussianReal 0 1))=
      normalRowSquare τ a*normalRowSquare τ b*
        (τ^2/(1-τ^4)+τ^4*a^2/(1+τ^2)^2) := by
  simp only [twoNormalDerivativeKernel,mul_pow]
  rw [integral_prod_mul (fun y:ℝ=>(normalDerivativeKernel τ a y)^2)
    (fun y:ℝ=>(normalKernel τ b y)^2),
    integral_normalDerivativeKernel_sq hτ a,integral_normalKernel_sq_eq hτ b]
  ring

theorem normalRowSquare_small_le (τ a : ℝ) (hτ : τ^2 ≤ 1/4) :
    normalRowSquare τ a ≤ 2*Real.exp (τ^2*a^2) := by
  have hs : (1/2:ℝ) ≤ Real.sqrt (1-τ^2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have ht : (1:ℝ) ≤ Real.sqrt (1+τ^2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg τ]
  have hsi : (Real.sqrt (1-τ^2))⁻¹ ≤ 2 := by
    rw [←one_div]
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (1-τ^2))).mpr
    linarith
  have hti : (Real.sqrt (1+τ^2))⁻¹ ≤ 1 := by
    rw [←one_div]
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (1+τ^2))).mpr
    linarith
  have hexp : Real.exp (τ^2*a^2/(1+τ^2)) ≤ Real.exp (τ^2*a^2) := by
    apply Real.exp_le_exp.mpr
    apply div_le_self (by positivity) (by nlinarith [sq_nonneg τ])
  unfold normalRowSquare
  calc
    _ ≤ 2*1*Real.exp (τ^2*a^2) := by gcongr
    _ = _ := by ring

/-- Uniform under contraction of either of the two exceptional coordinates.
Only the squared output radius enters, and the bound retains tau squared. -/
theorem twoNormalDerivative_row_le (τ a b R : ℝ) (hτ : τ^2 ≤ 1/4)
    (hR : a^2+b^2 ≤ R) :
    (∫ y,(twoNormalDerivativeKernel τ a b y)^2 ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) ≤
      8*τ^2*Real.exp (2*τ^2*R) := by
  have hsq : τ^2 < 1 := by linarith
  have hR0 : 0 ≤ R := by nlinarith [sq_nonneg a,sq_nonneg b]
  have h4 : τ^4 ≤ 1/2 := by nlinarith [sq_nonneg τ,sq_nonneg (τ^2-1/4)]
  have hv : 0 < 1-τ^4 := by linarith
  have hfirst : τ^2/(1-τ^4) ≤ 2*τ^2 := by
    apply (div_le_iff₀ hv).mpr
    nlinarith [mul_nonneg (sq_nonneg τ) (show 0 ≤ 1-2*τ^4 by linarith)]
  have hsecond : τ^4*a^2/(1+τ^2)^2 ≤ τ^4*R := by
    calc
      _ ≤ τ^4*a^2 := div_le_self (by positivity) (by nlinarith [sq_nonneg τ])
      _ ≤ τ^4*R := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg b]) (by positivity)
  have hbracket : τ^2/(1-τ^4)+τ^4*a^2/(1+τ^2)^2 ≤ 2*τ^2*(1+τ^2*R) := by
    nlinarith only [hfirst,hsecond,mul_nonneg (show 0 ≤ τ^4 by positivity) hR0]
  have hproduct : normalRowSquare τ a*normalRowSquare τ b ≤ 4*Real.exp (τ^2*R) := by
    calc
      _ ≤ (2*Real.exp (τ^2*a^2))*(2*Real.exp (τ^2*b^2)) :=
        mul_le_mul (normalRowSquare_small_le τ a hτ) (normalRowSquare_small_le τ b hτ)
          (normalRowSquare_nonneg τ b) (by positivity)
      _ = 4*Real.exp (τ^2*(a^2+b^2)) := by rw [mul_add,Real.exp_add];ring
      _ ≤ _ := by gcongr
  rw [integral_twoNormalDerivativeKernel_sq hsq]
  calc
    _ ≤ (4*Real.exp (τ^2*R))*(2*τ^2*(1+τ^2*R)) :=
      mul_le_mul hproduct hbracket (by positivity) (by positivity)
    _ ≤ (4*Real.exp (τ^2*R))*(2*τ^2*Real.exp (τ^2*R)) := by
      gcongr
      simpa only [add_comm] using Real.add_one_le_exp (τ^2*R)
    _ = _ := by rw [show 2*τ^2*R=τ^2*R+τ^2*R by ring,Real.exp_add];ring

/-- Antisymmetric divided difference, with its genuine derivative value at
zero. This row represents the regular-reference normal quotient directly. -/
def normalQuotientKernel (τ a y : ℝ) : ℝ :=
  if a=0 then normalDerivativeKernel τ 0 y else
    (normalKernel τ a y-normalKernel τ (-a) y)/(2*a)

theorem normalKernel_cross (τ a y : ℝ) (hτ : τ^2 < 1) :
    normalKernel τ a y*normalKernel τ (-a) y=
      Real.exp (-(τ^2*a^2)/(1-τ^2))*normalKernel τ 0 y^2 := by
  have hv : 1-τ^2≠0 := by linarith
  rw [normalKernel_exp hτ,normalKernel_exp hτ,normalKernel_exp hτ]
  have he : (-(y-τ*a)^2/(2*(1-τ^2))+y^2/2)+
      (-(y-τ*(-a))^2/(2*(1-τ^2))+y^2/2)=
      -(τ^2*a^2)/(1-τ^2)+2*(-(y-τ*0)^2/(2*(1-τ^2))+y^2/2) := by
    field_simp
    ring
  calc
    _ = (Real.sqrt (1-τ^2))⁻¹^2 * Real.exp
        ((-(y-τ*a)^2/(2*(1-τ^2))+y^2/2)+(-(y-τ*(-a))^2/(2*(1-τ^2))+y^2/2)) := by
      conv_rhs => rw [Real.exp_add]
      ring
    _ = _ := by rw [he];simp only [two_mul,Real.exp_add];ring

theorem integral_normalKernel_cross (τ a : ℝ) (hτ : τ^2 < 1) :
    (∫ y,normalKernel τ a y*normalKernel τ (-a) y ∂gaussianReal 0 1)=
      normalRowSquare τ 0*Real.exp (-(τ^2*a^2)/(1-τ^2)) := by
  simp_rw [normalKernel_cross τ a _ hτ]
  rw [integral_const_mul,integral_normalKernel_sq_eq hτ]
  ring

theorem normalQuotientKernel_memLp {τ : ℝ} (hτ : τ^2 < 1) (a : ℝ) :
    MemLp (normalQuotientKernel τ a) 2 (gaussianReal 0 1) := by
  unfold normalQuotientKernel
  by_cases ha : a=0
  · simp only [ha,↓reduceIte]
    exact normalDerivativeKernel_memLp hτ 0
  · simp only [ha,↓reduceIte]
    simpa only [div_eq_mul_inv,mul_comm,Pi.sub_apply] using
      ((normalKernel_memLp hτ a).sub (normalKernel_memLp hτ (-a))).const_mul (2*a)⁻¹

theorem normalQuotientKernel_measurable (τ a : ℝ) : Measurable (normalQuotientKernel τ a) := by
  unfold normalQuotientKernel
  by_cases ha : a=0
  · simp only [ha,↓reduceIte]
    exact normalDerivativeKernel_measurable τ 0
  · simp only [ha,↓reduceIte]
    exact ((normalKernel_measurable τ a).sub (normalKernel_measurable τ (-a))).div_const (2*a)

theorem exp_sub_le_tangent (u v : ℝ) : Real.exp u-Real.exp v ≤ (u-v)*Real.exp u := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (v-u)) (Real.exp_pos u).le
  rw [←Real.exp_add,sub_add_cancel] at hh
  nlinarith only [hh]

/-- Exact quotient-row bound. Unlike a supremum in the normal coordinate,
this retains both the tau factor and the small-tau offset exponent. -/
theorem integral_normalQuotientKernel_sq_le (τ a : ℝ) (hτ : τ^2 < 1) :
    (∫ y,normalQuotientKernel τ a y^2 ∂gaussianReal 0 1) ≤
      normalRowSquare τ a*τ^2/(1-τ^4) := by
  have hv : 0 < 1-τ^2 := by linarith
  have hp : 0 < 1+τ^2 := by positivity
  have h4 : 0 < 1-τ^4 := by
    rw [show 1-τ^4=(1-τ^2)*(1+τ^2) by ring]
    exact mul_pos hv hp
  by_cases ha : a=0
  · subst a
    simp only [normalQuotientKernel,↓reduceIte]
    rw [integral_normalDerivativeKernel_sq hτ]
    simp only [zero_pow (by decide : 2≠0),mul_zero,zero_div,add_zero]
    exact le_of_eq (by ring)
  have hn : normalRowSquare τ (-a)=normalRowSquare τ a := by simp only [normalRowSquare,neg_sq]
  have hi : (∫ y,(normalKernel τ a y-normalKernel τ (-a) y)^2 ∂gaussianReal 0 1)=
      2*(normalRowSquare τ a-normalRowSquare τ 0*Real.exp (-(τ^2*a^2)/(1-τ^2))) := by
    have he : (fun y=>(normalKernel τ a y-normalKernel τ (-a) y)^2)=
        fun y=>normalKernel τ a y^2+normalKernel τ (-a) y^2-
          2*(normalKernel τ a y*normalKernel τ (-a) y) := by funext y;ring
    have hprod : Integrable (fun y=>normalKernel τ a y*normalKernel τ (-a) y) (gaussianReal 0 1) :=
      (normalKernel_memLp hτ a).integrable_mul (normalKernel_memLp hτ (-a))
    have hsum : Integrable (fun y=>normalKernel τ a y^2+normalKernel τ (-a) y^2) (gaussianReal 0 1) :=
      (normalKernel_memLp hτ a).integrable_sq.add (normalKernel_memLp hτ (-a)).integrable_sq
    rw [he,integral_sub hsum (hprod.const_mul 2),
      integral_add (normalKernel_memLp hτ a).integrable_sq (normalKernel_memLp hτ (-a)).integrable_sq,
      integral_const_mul,integral_normalKernel_sq_eq hτ a,integral_normalKernel_sq_eq hτ (-a),
      hn,integral_normalKernel_cross τ a hτ]
    ring
  have he : (fun y=>normalQuotientKernel τ a y^2)=
      fun y=>(2*a)⁻¹^2*(normalKernel τ a y-normalKernel τ (-a) y)^2 := by
    funext y
    simp only [normalQuotientKernel,ha,↓reduceIte]
    ring
  rw [he,integral_const_mul,hi]
  let C := (Real.sqrt (1-τ^2))⁻¹*(Real.sqrt (1+τ^2))⁻¹
  let u := τ^2*a^2/(1+τ^2)
  let v := -(τ^2*a^2)/(1-τ^2)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hN : normalRowSquare τ a=C*Real.exp u := rfl
  have hN0 : normalRowSquare τ 0=C := by simp [normalRowSquare,C]
  rw [hN,hN0]
  have hb := mul_le_mul_of_nonneg_left (exp_sub_le_tangent u v) hC
  have hid : u-v=2*τ^2*a^2/(1-τ^4) := by dsimp only [u,v];field_simp;ring
  rw [hid] at hb
  calc
    _ ≤ (2*a)⁻¹^2*(2*(C*((2*τ^2*a^2/(1-τ^4))*Real.exp u))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith only [hb]
    _ = _ := by field_simp

/-- The quotient kernel has the exact odd-part identity even on the
reflection plane. Thus division introduces no exceptional-point assertion. -/
theorem normalQuotientKernel_mul (τ a y : ℝ) :
    a*normalQuotientKernel τ a y=(normalKernel τ a y-normalKernel τ (-a) y)/2 := by
  by_cases ha : a=0
  · subst a
    simp [normalQuotientKernel]
  · simp only [normalQuotientKernel,ha,↓reduceIte]
    field_simp

def twoNormalQuotientKernel (τ a b : ℝ) (y : ℝ×ℝ) : ℝ :=
  normalQuotientKernel τ a y.1*normalKernel τ b y.2

theorem twoNormalQuotientKernel_measurable (τ a b : ℝ) :
    Measurable (twoNormalQuotientKernel τ a b) :=
  ((normalQuotientKernel_measurable τ a).comp measurable_fst).mul
    ((normalKernel_measurable τ b).comp measurable_snd)

theorem twoNormalQuotientKernel_memLp {τ : ℝ} (hτ : τ^2 < 1) (a b : ℝ) :
    MemLp (twoNormalQuotientKernel τ a b) 2 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  apply (memLp_two_iff_integrable_sq (twoNormalQuotientKernel_measurable τ a b).aestronglyMeasurable).mpr
  simpa only [twoNormalQuotientKernel,mul_pow] using
    (normalQuotientKernel_memLp hτ a).integrable_sq.mul_prod
      (normalKernel_memLp hτ b).integrable_sq

/-- The direct quotient row has a dimension-free small-time bound. The
radius condition is exactly what an orthogonal current-plane chart supplies. -/
theorem twoNormalQuotient_row_le (τ a b R : ℝ) (hτ : τ^2 ≤ 1/4)
    (hR : a^2+b^2 ≤ R) :
    (∫ y,(twoNormalQuotientKernel τ a b y)^2 ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) ≤
      8*τ^2*Real.exp (τ^2*R) := by
  have hsq : τ^2 < 1 := by linarith
  have h4 : τ^4 ≤ 1/2 := by nlinarith [sq_nonneg τ,sq_nonneg (τ^2-1/4)]
  have hv : 0 < 1-τ^4 := by linarith
  have hfrac : τ^2/(1-τ^4) ≤ 2*τ^2 := by
    apply (div_le_iff₀ hv).mpr
    nlinarith [mul_nonneg (sq_nonneg τ) (show 0 ≤ 1-2*τ^4 by linarith)]
  have hprod : normalRowSquare τ a*normalRowSquare τ b ≤ 4*Real.exp (τ^2*R) := by
    calc
      _ ≤ (2*Real.exp (τ^2*a^2))*(2*Real.exp (τ^2*b^2)) :=
        mul_le_mul (normalRowSquare_small_le τ a hτ) (normalRowSquare_small_le τ b hτ)
          (normalRowSquare_nonneg τ b) (by positivity)
      _ = 4*Real.exp (τ^2*(a^2+b^2)) := by rw [mul_add,Real.exp_add];ring
      _ ≤ _ := by gcongr
  simp only [twoNormalQuotientKernel,mul_pow]
  rw [integral_prod_mul (fun y:ℝ=>(normalQuotientKernel τ a y)^2)
    (fun y:ℝ=>(normalKernel τ b y)^2),integral_normalKernel_sq_eq hsq b]
  calc
    _ ≤ (normalRowSquare τ a*τ^2/(1-τ^4))*normalRowSquare τ b :=
      mul_le_mul_of_nonneg_right (integral_normalQuotientKernel_sq_le τ a hsq)
        (normalRowSquare_nonneg τ b)
    _ = (normalRowSquare τ a*normalRowSquare τ b)*(τ^2/(1-τ^4)) := by ring
    _ ≤ (4*Real.exp (τ^2*R))*(2*τ^2) :=
      mul_le_mul hprod hfrac (by positivity) (by positivity)
    _ = _ := by ring

end NegativeVotingRegularHighTailCrossKernel
