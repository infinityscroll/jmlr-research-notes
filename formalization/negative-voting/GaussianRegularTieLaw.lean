import GaussianDiagonalBalanceEquation
import Mathlib.Probability.Moments.Variance

/-! The actual regular Gaussian tie law has density proportional to
φ(x)^2 Φ(x)^n, with n=m−2. Its normalization, polynomial integrability,
and integration-by-parts identities are derived from that literal density. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter WeakSimplex
open scoped BigOperators RealInnerProductSpace ENNReal Classical Topology
namespace NegativeVotingRegularTieLaw
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalFacetIntegral NegativeVotingHazardIntegrability
  NegativeVotingHazardPolynomialBounds

def tieWeight (n : ℕ) (x : ℝ) : ℝ := normalPDF x^2*normalCDF x^n

theorem tieWeight_pos (n : ℕ) (x : ℝ) : 0<tieWeight n x:=
  mul_pos (sq_pos_of_pos (normalPDF_pos x)) (pow_pos (normalCDF_pos x) n)

@[fun_prop] theorem tieWeight_continuous (n : ℕ) : Continuous (tieWeight n) := by
  unfold tieWeight
  exact ((continuous_iff_continuousAt.mpr (fun x=>(hasDerivAt_normalPDF x).continuousAt)).pow 2).mul
    (NegativeVotingMassCentroid.continuous_normalCDF.pow n)

theorem regular_hazardPairDensity (n : ℕ) (i j : Fin (n+2)) (x : ℝ) :
    hazardPairDensity (fun _ : Fin (n+2)=>(1:ℝ)) (fun _=>0) x i j=tieWeight n x := by
  unfold hazardPairDensity productCDF gaussianHazard gaussianCDF gaussianDensity tieWeight
  simp only [sub_zero,div_one,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [pow_add]
  field_simp [(normalCDF_pos x).ne']

theorem tieWeight_polynomial_integrable (n k : ℕ) :
    Integrable (fun x=>tieWeight n x*(1+|x|)^k) volume := by
  have hh:=integrable_hazardPairDensity_polynomial (fun _ : Fin (n+2)=>(1:ℝ))
    (fun _=>0) (by intro i;norm_num) 0 0 k
  simpa only [regular_hazardPairDensity] using hh

theorem tieWeight_integrable (n : ℕ) : Integrable (tieWeight n) volume := by
  simpa using tieWeight_polynomial_integrable n 0

def tieMass (n : ℕ) : ℝ := ∫x,tieWeight n x

theorem tieMass_pos (n : ℕ) : 0<tieMass n := by
  apply integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun x=>(tieWeight_pos n x).le)) (tieWeight_integrable n) |>.mpr
  have he : Function.support (tieWeight n)=Set.univ:=by
    ext x
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact (tieWeight_pos n x).ne'
  rw [he]
  simp

def tieLaw (n : ℕ) : Measure ℝ :=
  volume.withDensity (fun x=>ENNReal.ofReal (tieWeight n x/tieMass n))

instance tieLaw_probability (n : ℕ) : IsProbabilityMeasure (tieLaw n) := by
  constructor
  rw [tieLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [←ofReal_integral_eq_lintegral_ofReal ((tieWeight_integrable n).div_const (tieMass n))
    (ae_of_all _ (fun x=>div_nonneg (tieWeight_pos n x).le (tieMass_pos n).le))]
  rw [integral_div]
  change ENNReal.ofReal (tieMass n/tieMass n)=1
  rw [div_self (tieMass_pos n).ne',ENNReal.ofReal_one]

theorem integral_tieLaw (n : ℕ) (f : ℝ→ℝ) :
    (∫x,f x ∂tieLaw n)=(∫x,tieWeight n x*f x)/tieMass n := by
  rw [tieLaw,integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ (fun x=>ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (tieWeight_pos n _).le (tieMass_pos n).le),smul_eq_mul]
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem integrable_tieLaw_of_weighted (n : ℕ) (f : ℝ→ℝ)
    (hf : Integrable (fun x=>tieWeight n x*f x) volume) : Integrable f (tieLaw n) := by
  rw [tieLaw,integrable_withDensity_iff (by fun_prop)
    (ae_of_all _ (fun x=>ENNReal.ofReal_lt_top))]
  have hh:=hf.div_const (tieMass n)
  convert hh using 1
  funext x
  rw [ENNReal.toReal_ofReal (div_nonneg (tieWeight_pos n x).le (tieMass_pos n).le)]
  ring

theorem tieLaw_polynomial_integrable (n k : ℕ) : Integrable (fun x:ℝ=>(1+|x|)^k) (tieLaw n) :=
  integrable_tieLaw_of_weighted n _ (tieWeight_polynomial_integrable n k)

/-- All continuous functions of fixed polynomial growth are integrable
against the actual unnormalized tie density. -/
theorem weighted_integrable_of_polynomial_bound (n k : ℕ) (f : ℝ→ℝ) (hf : Continuous f)
    (C : ℝ) (hC : 0≤C) (hbound : ∀x,|f x|≤C*(1+|x|)^k) :
    Integrable (fun x=>tieWeight n x*f x) volume := by
  apply ((tieWeight_polynomial_integrable n k).const_mul C).mono'
    ((tieWeight_continuous n).mul hf).aestronglyMeasurable
  filter_upwards with x
  simp only [Pi.mul_apply,Real.norm_eq_abs,abs_mul,abs_of_pos (tieWeight_pos n x)]
  calc
    _≤tieWeight n x*(C*(1+|x|)^k):=mul_le_mul_of_nonneg_left (hbound x) (tieWeight_pos n x).le
    _=_:=by ring

theorem weighted_x_integrable (n : ℕ) : Integrable (fun x=>tieWeight n x*x) volume :=
  weighted_integrable_of_polynomial_bound n 1 id continuous_id 1 (by norm_num) (by intro x;simp only [id_eq,pow_one,one_mul];linarith)

theorem weighted_x_sq_integrable (n : ℕ) : Integrable (fun x=>tieWeight n x*x^2) volume := by
  apply weighted_integrable_of_polynomial_bound n 2 (fun x=>x^2) (by fun_prop) 1 (by norm_num)
  intro x
  rw [abs_of_nonneg (sq_nonneg _),one_mul]
  nlinarith [abs_nonneg x,sq_abs x]

@[fun_prop] theorem r_continuous : Continuous r := continuous_iff_continuousAt.mpr (fun x=>(hasDerivAt_r x).continuousAt)

theorem weighted_r_integrable (n : ℕ) : Integrable (fun x=>tieWeight n x*r x) volume := by
  apply weighted_integrable_of_polynomial_bound n 1 r r_continuous (r 0+1) (by positivity [r_pos 0])
  intro x
  rw [abs_of_pos (r_pos x),pow_one]
  have hh:=normal_hazard_linear_growth x
  nlinarith [r_pos 0,abs_nonneg x,mul_nonneg (r_pos 0).le (abs_nonneg x)]

theorem weighted_x_r_integrable (n : ℕ) : Integrable (fun x=>tieWeight n x*(x*r x)) volume := by
  apply weighted_integrable_of_polynomial_bound n 2 (fun x=>x*r x) (continuous_id.mul r_continuous)
    (r 0+1) (by positivity [r_pos 0])
  intro x
  rw [abs_mul,abs_of_pos (r_pos x)]
  have hh:=mul_le_mul_of_nonneg_left (normal_hazard_linear_growth x) (abs_nonneg x)
  have ht:0≤r 0*|x|:=mul_nonneg (r_pos 0).le (abs_nonneg x)
  have hs:0≤r 0*|x|^2:=mul_nonneg (r_pos 0).le (sq_nonneg _)
  nlinarith [r_pos 0,abs_nonneg x]

theorem tieWeight_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (tieWeight n) (tieWeight n x*(-2*x+(n:ℝ)*r x)) x := by
  have hp : HasDerivAt (fun y=>normalPDF y^2) (-2*x*normalPDF x^2) x:=by
    convert (hasDerivAt_normalPDF x).pow 2 using 1 <;> ring
  have hc : HasDerivAt (fun y=>normalCDF y^n) (normalCDF x^n*((n:ℝ)*r x)) x:=by
    cases n with
    | zero => simpa using hasDerivAt_const x (1:ℝ)
    | succ k =>
      convert (hasDerivAt_normalCDF x).pow (k+1) using 1
      unfold r
      simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,pow_succ]
      field_simp [(normalCDF_pos x).ne']
  convert hp.mul hc using 1
  · rfl
  · unfold tieWeight
    ring

theorem tieWeight_derivative_integrable (n : ℕ) :
    Integrable (fun x=>tieWeight n x*(-2*x+(n:ℝ)*r x)) volume := by
  convert ((weighted_x_integrable n).const_mul (-2)).add ((weighted_r_integrable n).const_mul n) using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- Both infinite-endpoint terms vanish by actual integrability of the
function and derivative; no boundary-value hypothesis is supplied. -/
theorem tieWeight_ibp_zero (n : ℕ) :
    -2*(∫x,tieWeight n x*x)+(n:ℝ)*(∫x,tieWeight n x*r x)=0 := by
  have hz:=integral_eq_zero_of_hasDerivAt_of_integrable (tieWeight_hasDerivAt n)
    (tieWeight_derivative_integrable n) (tieWeight_integrable n)
  have he : (fun x=>tieWeight n x*(-2*x+(n:ℝ)*r x))=
      fun x=>(-2)*(tieWeight n x*x)+(n:ℝ)*(tieWeight n x*r x):=by funext x;ring
  rw [he,integral_add ((weighted_x_integrable n).const_mul (-2)) ((weighted_r_integrable n).const_mul n),
    integral_const_mul,integral_const_mul] at hz
  exact hz

theorem tieWeight_x_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y=>tieWeight n y*y)
      (tieWeight n x*(1-2*x^2+(n:ℝ)*(x*r x))) x := by
  convert (tieWeight_hasDerivAt n x).mul (hasDerivAt_id x) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem tieWeight_x_derivative_integrable (n : ℕ) :
    Integrable (fun x=>tieWeight n x*(1-2*x^2+(n:ℝ)*(x*r x))) volume := by
  convert ((tieWeight_integrable n).sub ((weighted_x_sq_integrable n).const_mul 2)).add
    ((weighted_x_r_integrable n).const_mul n) using 1
  funext x
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem tieWeight_ibp_one (n : ℕ) :
    tieMass n-2*(∫x,tieWeight n x*x^2)+(n:ℝ)*(∫x,tieWeight n x*(x*r x))=0 := by
  have hz:=integral_eq_zero_of_hasDerivAt_of_integrable (tieWeight_x_hasDerivAt n)
    (tieWeight_x_derivative_integrable n) (weighted_x_integrable n)
  have he : (fun x=>tieWeight n x*(1-2*x^2+(n:ℝ)*(x*r x)))=
      fun x=>tieWeight n x-2*(tieWeight n x*x^2)+(n:ℝ)*(tieWeight n x*(x*r x)):=by funext x;ring
  have his : Integrable (fun x=>tieWeight n x-2*(tieWeight n x*x^2)) volume:=
    (tieWeight_integrable n).sub ((weighted_x_sq_integrable n).const_mul 2)
  rw [he,integral_add his
    ((weighted_x_r_integrable n).const_mul n),
    integral_sub (tieWeight_integrable n) ((weighted_x_sq_integrable n).const_mul 2),
    integral_const_mul,integral_const_mul] at hz
  exact hz

theorem tieLaw_memLp_id (n : ℕ) : MemLp (fun x:ℝ=>x) 2 (tieLaw n) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (integrable_tieLaw_of_weighted n _ (weighted_x_sq_integrable n))

theorem r_growth_bound (x : ℝ) : |r x|≤(r 0+1)*(1+|x|) := by
  rw [abs_of_pos (r_pos x)]
  have hh:=normal_hazard_linear_growth x
  nlinarith [r_pos 0,abs_nonneg x,mul_nonneg (r_pos 0).le (abs_nonneg x)]

theorem tieLaw_memLp_r (n : ℕ) : MemLp r 2 (tieLaw n) := by
  apply (memLp_two_iff_integrable_sq r_continuous.aestronglyMeasurable).mpr
  apply integrable_tieLaw_of_weighted
  apply weighted_integrable_of_polynomial_bound n 2 (fun x=>r x^2) (r_continuous.pow 2)
    ((r 0+1)^2) (sq_nonneg _)
  intro x
  have hh:=pow_le_pow_left₀ (abs_nonneg (r x)) (r_growth_bound x) 2
  simpa only [sq_abs,mul_pow,abs_of_nonneg (sq_nonneg (r x))] using hh

def tieMean (n : ℕ) : ℝ := ∫x,x ∂tieLaw n
def tieVariance (n : ℕ) : ℝ := variance (fun x:ℝ=>x) (tieLaw n)
def tieHazardCovariance (n : ℕ) : ℝ := covariance (fun x:ℝ=>x) r (tieLaw n)

/-- Exact centered integration by parts for the actual normalized tie law. -/
theorem tieLaw_covariance_identity (n : ℕ) :
    -2*tieVariance n+(n:ℝ)*tieHazardCovariance n = -1 := by
  have h0:=tieWeight_ibp_zero n
  have h1:=tieWeight_ibp_one n
  have hp:=tieMass_pos n
  unfold tieVariance tieHazardCovariance
  rw [variance_eq_sub (tieLaw_memLp_id n),covariance_eq_sub (tieLaw_memLp_id n) (tieLaw_memLp_r n)]
  simp only [Pi.pow_apply,Pi.mul_apply]
  simp_rw [integral_tieLaw]
  field_simp [hp.ne']
  have hxri : (∫x,tieWeight n x*x*r x)=(∫x,tieWeight n x*(x*r x)):=by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hxri]
  have h0m:=congrArg (fun z=>z*(∫x,tieWeight n x*x)) h0
  have h1m:=congrArg (fun z=>z*tieMass n) h1
  nlinarith [h0m,h1m]

end NegativeVotingRegularTieLaw
