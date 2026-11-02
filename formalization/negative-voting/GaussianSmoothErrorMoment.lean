import GaussianRegularCoefficientMajorant
import GaussianSquareExponential
import NegativeVoting.Threshold

/-!
# Gaussian moments of the literal smooth pair-coefficient error

The scalar estimates below retain the actual `smoothPairError / r`.  They
are ambient Gaussian estimates, and do not assert any facet restriction or
normal-derivative estimate.  All small-noise conditions are explicit.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Topology Classical ENNReal

namespace NegativeVotingSmoothErrorMoment
open NegativeVoting NegativeVotingRegularPairCoefficient
  NegativeVotingRegularFacetRange NegativeVotingSquareExponential

/-- A deliberately conservative constant, independent of the number of
scores, the ambient dimension and the noise parameter. -/
def momentConstant (A : ℝ) : ℝ :=
  Real.exp 1 * (2 + 40 * rangeFacetConstant + 576 * rangeFacetConstant * A)

theorem momentConstant_nonneg (A : ℝ) (hA : 0 ≤ A) : 0 ≤ momentConstant A := by
  have hC := rangeFacetConstant_pos.le
  unfold momentConstant
  positivity

private theorem sqrt_facts (L : ℝ) (hL : 1 ≤ L) :
    1 ≤ Real.sqrt L ∧ Real.sqrt L ≤ L ∧ 1 ≤ L * Real.sqrt L := by
  have hL0 : 0 ≤ L := by linarith
  have hs0 := Real.sqrt_nonneg L
  have hs2 := Real.sq_sqrt hL0
  have hs1 : 1 ≤ Real.sqrt L := by nlinarith
  have hsL : Real.sqrt L ≤ L := by nlinarith [sq_nonneg (Real.sqrt L - 1)]
  exact ⟨hs1, hsL, by nlinarith⟩

/-- Algebraic estimate before exponential absorption. -/
theorem range_polynomial_bound (C L M r v : ℝ)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hM : 0 ≤ M) (hr : 0 < r)
    (hv : 0 ≤ v) (hvupper : v ≤ 4 * r * (L + M)) :
    C * (v * Real.sqrt L + v ^ 2) / r ≤
      C * (4 * L * Real.sqrt L + 4 * M * Real.sqrt L +
        32 * r * L ^ 2 + 32 * r * M ^ 2) := by
  have hL0 : 0 ≤ L := by linarith
  have hsum : (L + M) ^ 2 ≤ 2 * (L ^ 2 + M ^ 2) := by
    nlinarith [sq_nonneg (L - M)]
  have hv2 := (sq_le_sq₀ hv (by positivity : 0 ≤ 4 * r * (L + M))).mpr hvupper
  have hlin := mul_le_mul_of_nonneg_right hvupper (Real.sqrt_nonneg L)
  have hquad := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 16 * r ^ 2)
  apply (div_le_iff₀ hr).mpr
  have h := mul_le_mul_of_nonneg_left (show
      v * Real.sqrt L + v ^ 2 ≤
        r * (4 * L * Real.sqrt L + 4 * M * Real.sqrt L +
          32 * r * L ^ 2 + 32 * r * M ^ 2) by nlinarith) hC
  nlinarith [h]

/-- The small-noise condition makes the true range exponent absorbable by
one Gaussian square exponential. -/
theorem range_exponent_small (C L M r q v : ℝ)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hM : 0 ≤ M) (hr : 0 < r)
    (hrhalf : r ≤ 1 / 2) (hq : 0 < q)
    (hsmall : 2560 * C * r * q * L ^ 2 ≤ 1)
    (hv : 0 ≤ v) (hvupper : v ≤ 4 * r * (L + M)) :
    C * (v * Real.sqrt L + v ^ 2) ≤ (1 + M ^ 2) / (64 * q) := by
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hs1, hsL, hLs⟩ := sqrt_facts L hL
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hM1 : M ≤ 1 + M ^ 2 := by nlinarith [sq_nonneg (M - 1 / 2)]
  have hLS : L * Real.sqrt L ≤ L ^ 2 := by nlinarith
  have hsL2 : Real.sqrt L ≤ L ^ 2 := by nlinarith
  have hMS : M * Real.sqrt L ≤ L ^ 2 * (1 + M ^ 2) := by
    calc
      _ ≤ (1 + M ^ 2) * Real.sqrt L :=
        mul_le_mul_of_nonneg_right hM1 (Real.sqrt_nonneg L)
      _ ≤ (1 + M ^ 2) * L ^ 2 :=
        mul_le_mul_of_nonneg_left hsL2 (by positivity)
      _ = _ := by ring
  have hrL : 32 * r * L ^ 2 ≤ 16 * L ^ 2 := by nlinarith
  have hrM : 32 * r * M ^ 2 ≤ 16 * L ^ 2 * M ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hL2 (sq_nonneg M)
    nlinarith
  have hpoly : 4 * L * Real.sqrt L + 4 * M * Real.sqrt L +
      32 * r * L ^ 2 + 32 * r * M ^ 2 ≤ 40 * L ^ 2 * (1 + M ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg M)]
  have hb := range_polynomial_bound C L M r v hC hL hM hr hv hvupper
  have hc := mul_le_mul_of_nonneg_left hpoly hC
  have hqbound : C * (v * Real.sqrt L + v ^ 2) ≤
      40 * C * r * L ^ 2 * (1 + M ^ 2) := by
    have hh := (div_le_iff₀ hr).mp (hb.trans hc)
    nlinarith [hh]
  apply (le_div_iff₀ (by positivity : 0 < 64 * q)).mpr
  have hh := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 1 + M ^ 2)
  have hh' := mul_le_mul_of_nonneg_right hqbound (by positivity : 0 ≤ 64 * q)
  nlinarith [hh, hh']

/-- A scalar pointwise estimate with the exact logarithmic order needed by
the later Gaussian moment estimate. -/
theorem scalar_error_envelope (C A L M r q v : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hL : 1 ≤ L) (hM : 0 ≤ M)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hq : 1 ≤ q) (hqA : q ≤ A * L)
    (hrL : r * L ^ 2 ≤ 1)
    (hsmall : 2560 * C * r * q * L ^ 2 ≤ 1)
    (hv : 0 ≤ v) (hvupper : v ≤ 4 * r * (L + M)) :
    ((2 * r ^ 2 + C * (v * Real.sqrt L + v ^ 2)) *
      Real.exp (C * (v * Real.sqrt L + v ^ 2))) / r ≤
    (Real.exp 1 * (2 + 40 * C + 576 * C * A)) *
      L * Real.sqrt L * Real.exp (M ^ 2 / (8 * q)) := by
  have hq0 : 0 < q := by linarith
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hs1, hsL, hLs⟩ := sqrt_facts L hL
  let E := Real.exp (M ^ 2 / (16 * q))
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hE0 : 0 ≤ E := by positivity
  have hM1 : M ≤ 1 + M ^ 2 := by nlinarith [sq_nonneg (M - 1 / 2)]
  have hME : M ^ 2 ≤ 16 * q * E := by
    have he := Real.add_one_le_exp (M ^ 2 / (16 * q))
    have hh := (div_le_iff₀ (by positivity : 0 < 16 * q)).mp
      (show M ^ 2 / (16 * q) ≤ E by dsimp [E]; linarith)
    nlinarith [hh]
  have hbase : 2 * r + C * (4 * L * Real.sqrt L + 4 * Real.sqrt L + 32) ≤
      (2 + 40 * C) * L * Real.sqrt L := by
    have hsLs : Real.sqrt L ≤ L * Real.sqrt L := by
      nlinarith [Real.sqrt_nonneg L]
    have hh : 4 * L * Real.sqrt L + 4 * Real.sqrt L + 32 ≤
        40 * L * Real.sqrt L := by linarith
    have hc := mul_le_mul_of_nonneg_left hh hC
    nlinarith
  have hqLs : q * Real.sqrt L ≤ A * L * Real.sqrt L :=
    mul_le_mul_of_nonneg_right hqA (Real.sqrt_nonneg L)
  have hrq : r * q ≤ A * L * Real.sqrt L := by
    have h1 : r * q ≤ q := by nlinarith
    have h2 : A * L ≤ A * L * Real.sqrt L := by
      have hh := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ A * L)
      simpa using hh
    exact h1.trans (hqA.trans h2)
  have htail : (4 * C * Real.sqrt L + 32 * C * r) * M ^ 2 ≤
      576 * C * A * L * Real.sqrt L * E := by
    have hh := mul_le_mul_of_nonneg_left hME
      (by positivity : 0 ≤ 4 * C * Real.sqrt L + 32 * C * r)
    have hh1 := mul_le_mul_of_nonneg_left hqLs (by positivity : 0 ≤ 64 * C * E)
    have hh2 := mul_le_mul_of_nonneg_left hrq (by positivity : 0 ≤ 512 * C * E)
    nlinarith [hh, hh1, hh2]
  have hp := range_polynomial_bound C L M r v hC hL hM hr hv hvupper
  have hp' : 2 * r + C * (v * Real.sqrt L + v ^ 2) / r ≤
      (2 + 40 * C + 576 * C * A) * L * Real.sqrt L * E := by
    have hMS := mul_le_mul_of_nonneg_right hM1 (Real.sqrt_nonneg L)
    have hpoly : 4 * L * Real.sqrt L + 4 * M * Real.sqrt L +
        32 * r * L ^ 2 + 32 * r * M ^ 2 ≤
        (4 * L * Real.sqrt L + 4 * Real.sqrt L + 32) +
          (4 * Real.sqrt L + 32 * r) * M ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hpoly hC
    have hbE := mul_le_mul_of_nonneg_left hE
      (by positivity : 0 ≤ (2 + 40 * C) * L * Real.sqrt L)
    nlinarith [hh, hbE]
  have hQ := range_exponent_small C L M r q v hC hL hM hr hrhalf hq0
    hsmall hv hvupper
  have hQ' : C * (v * Real.sqrt L + v ^ 2) ≤ 1 + M ^ 2 / (16 * q) := by
    have hh : (1 + M ^ 2) / (64 * q) ≤ 1 + M ^ 2 / (16 * q) := by
      apply (div_le_iff₀ (by positivity : 0 < 64 * q)).mpr
      field_simp
      nlinarith [sq_nonneg M]
    exact hQ.trans hh
  have he : E * Real.exp (C * (v * Real.sqrt L + v ^ 2)) ≤
      Real.exp 1 * Real.exp (M ^ 2 / (8 * q)) := by
    dsimp [E]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have heq : M ^ 2 / (8 * q) = 2 * (M ^ 2 / (16 * q)) := by ring
    linarith
  calc
    _ = (2 * r + C * (v * Real.sqrt L + v ^ 2) / r) *
        Real.exp (C * (v * Real.sqrt L + v ^ 2)) := by field_simp
    _ ≤ ((2 + 40 * C + 576 * C * A) * L * Real.sqrt L * E) *
        Real.exp (C * (v * Real.sqrt L + v ^ 2)) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le
    _ = ((2 + 40 * C + 576 * C * A) * L * Real.sqrt L) *
        (E * Real.exp (C * (v * Real.sqrt L + v ^ 2))) := by ring
    _ ≤ ((2 + 40 * C + 576 * C * A) * L * Real.sqrt L) *
        (Real.exp 1 * Real.exp (M ^ 2 / (8 * q))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

def logScale (n : ℕ) : ℝ := 1 + Real.log ((n : ℝ) + 2)

theorem logScale_one_le (n : ℕ) : 1 ≤ logScale n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
  unfold logScale
  linarith

/-- The explicit scalar restrictions hold eventually throughout the full
negative-voting noise range `0 < r ≤ 1/(m-1)`, with `m = n+2`. -/
theorem exists_voting_noise_threshold (A : ℝ) (hA : 0 ≤ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r : ℝ,
      0 < r → r ≤ 1 / ((n : ℝ) + 1) →
      r ≤ 1 / 2 ∧ r * (logScale n) ^ 2 ≤ 1 ∧
        2560 * rangeFacetConstant * A * r * (logScale n) ^ 3 ≤ 1 := by
  let K := 2560 * rangeFacetConstant * A + 1
  have hC := rangeFacetConstant_pos.le
  have hK : 1 ≤ K := by
    dsimp [K]
    have hh : 0 ≤ 2560 * rangeFacetConstant * A := by positivity
    linarith
  obtain ⟨N, hN⟩ := exists_uniform_remainder_threshold K 0
  refine ⟨max N 1, ?_⟩
  intro n hn r hr hrange
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hmpos : 0 < (n : ℝ) + 2 := by positivity
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hrprod : r * ((n : ℝ) + 1) ≤ 1 := (le_div_iff₀ hden).mp hrange
  have hrhalf : r ≤ 1 / 2 := by nlinarith
  have hrm : r * ((n : ℝ) + 2) ≤ 2 := by nlinarith
  have hLn := logScale_one_le n
  have hL0 : 0 ≤ logScale n := by linarith
  have hL23 : (logScale n) ^ 2 ≤ (logScale n) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (logScale n)) (sub_nonneg.mpr hLn)]
  have hrate := hN (n + 2) (by omega)
  simp only [zero_mul, add_zero, Nat.cast_add, Nat.cast_ofNat] at hrate
  change K * ((logScale n) ^ 3 / ((n : ℝ) + 2)) ≤ 1 / 2 at hrate
  have hrate' : 2 * K * (logScale n) ^ 3 ≤ (n : ℝ) + 2 := by
    have hh : K * (logScale n) ^ 3 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      simpa only [mul_div_assoc] using hrate
    have hh' := (div_le_iff₀ hmpos).mp hh
    linarith
  have hKr : r * K * (logScale n) ^ 3 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hrate' hr.le
    nlinarith [hh]
  have hrl : r * (logScale n) ^ 2 ≤ r * K * (logScale n) ^ 3 := by
    have hh1 := mul_le_mul_of_nonneg_left hL23 hr.le
    have hh2 := mul_le_mul_of_nonneg_left hK
      (by positivity : 0 ≤ r * (logScale n) ^ 3)
    nlinarith [hh1, hh2]
  refine ⟨hrhalf, hrl.trans hKr, ?_⟩
  have hh : 2560 * rangeFacetConstant * A ≤ K := by dsimp [K]; linarith
  have hh' := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ r * (logScale n) ^ 3)
  nlinarith [hh']

/-- Pointwise estimate for the literal envelope, with no surrogate error
function substituted. -/
theorem smoothPairError_div_le (n : ℕ) (A r q : ℝ)
    (hA : 0 ≤ A) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hq : 1 ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1)
    (u : Fin (n + 2) → ℝ) :
    smoothPairError n r u / r ≤ momentConstant A * logScale n *
      Real.sqrt (logScale n) *
        Real.exp ((maxScore (fun i => |u i|)) ^ 2 / (8 * q)) := by
  let M := maxScore (fun i => |u i|)
  let W := smoothUtilityRange u
  let τ := r / Real.sqrt (1 - r ^ 2)
  have hM : 0 ≤ M := (abs_nonneg (u 0)).trans
    (Finset.le_sup' (fun i => |u i|) (Finset.mem_univ 0))
  have hW : 0 ≤ W := smoothUtilityRange_nonneg u
  have hWupper : W ≤ 2 * logScale n + 2 * M := by
    have hh := smoothUtilityRange_le_max_abs u
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at hh
    dsimp [W, M, logScale]
    linarith
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτupper : τ ≤ 2 * r := by
    have hh := (noise_prefactor_bounds r hr hrhalf).2
    have hh' : (Real.sqrt (1 - r ^ 2))⁻¹ ≤ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh' hr.le
    simpa only [τ, div_eq_mul_inv, mul_comm r 2] using hm
  have hv : 0 ≤ τ * W := mul_nonneg hτ hW
  have hvupper : τ * W ≤ 4 * r * (logScale n + M) := by
    calc
      _ ≤ (2 * r) * W := mul_le_mul_of_nonneg_right hτupper hW
      _ ≤ (2 * r) * (2 * logScale n + 2 * M) :=
        mul_le_mul_of_nonneg_left hWupper (by positivity)
      _ = _ := by ring
  have hh := scalar_error_envelope rangeFacetConstant A (logScale n) M r q (τ * W)
    rangeFacetConstant_pos.le hA (logScale_one_le n) hM hr hrhalf hq hqA
    hrL hsmall hv hvupper
  simpa only [smoothPairError, rangeExponent, momentConstant, logScale, τ, W, M] using hh

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem smoothPairError_affine_aestronglyMeasurable (n : ℕ)
    (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ) (r : ℝ) :
    AEStronglyMeasurable
      (fun x : E => smoothPairError n r (fun i => a i + inner ℝ (B i) x) / r)
      (stdGaussian E) := by
  have hu : Continuous (fun x : E => fun i => a i + inner ℝ (B i) x) := by fun_prop
  exact (((smoothPairError_contDiff n r).continuous.comp hu).div_const r).aestronglyMeasurable

/-- Actual ambient Gaussian `L^q` membership, for arbitrary shifts and any
finite Gaussian score family with row norms at most one. -/
theorem smoothPairError_div_memLp (n : ℕ) (B : Fin (n + 2) → E)
    (hv : ∀ i, ‖B i‖ ≤ 1) (a : Fin (n + 2) → ℝ) (A r q : ℝ)
    (hA : 0 ≤ A) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hq : 1 ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1) :
    MemLp (fun x : E => smoothPairError n r (fun i => a i + inner ℝ (B i) x) / r)
      (ENNReal.ofReal q) (stdGaussian E) := by
  have hq0 : 0 < q := by linarith
  have hmem := (max_square_exp_q_memLp B hv a q hq0).const_mul
    (momentConstant A * logScale n * Real.sqrt (logScale n))
  apply hmem.mono' (smoothPairError_affine_aestronglyMeasurable n B a r)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
    (smoothPairError_nonneg n r hr (by linarith) _) hr.le)]
  exact smoothPairError_div_le n A r q hA hr hrhalf hq hqA hrL hsmall _

/-- A uniform Gaussian moment bound. The shift allowance is explicit:
`a_i^2 ≤ D (1 + log(n+2))`.  In particular `D = 0` covers the centered
regular-simplex scores. -/
theorem smoothPairError_div_norm_le (n : ℕ) (B : Fin (n + 2) → E)
    (hv : ∀ i, ‖B i‖ ≤ 1) (a : Fin (n + 2) → ℝ) (A D r q : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (ha : ∀ i, (a i) ^ 2 ≤ D * logScale n)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hqL : logScale n ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1) :
    eLpNorm (fun x : E => smoothPairError n r (fun i => a i + inner ℝ (B i) x) / r)
      (ENNReal.ofReal q) (stdGaussian E) ≤
      ENNReal.ofReal (momentConstant A * logScale n * Real.sqrt (logScale n)) *
        ENNReal.ofReal (Real.exp (1 + D / 4)) := by
  have hq : 1 ≤ q := (logScale_one_le n).trans hqL
  let K := momentConstant A * logScale n * Real.sqrt (logScale n)
  let G := fun x : E => Real.exp ((affineMaxAbs B a x) ^ 2 / (8 * q))
  have hK : 0 ≤ K := by
    have hC := momentConstant_nonneg A hA
    have hL := (logScale_one_le n)
    dsimp [K]
    positivity
  have hb := eLpNorm_mono_real
    (smoothPairError_affine_aestronglyMeasurable n B a r)
    (g := fun x : E => K * G x) (p := ENNReal.ofReal q) (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (smoothPairError_nonneg n r hr (by linarith) _) hr.le)]
      exact smoothPairError_div_le n A r q hA hr hrhalf hq hqA hrL hsmall _)
  have hG : eLpNorm G (ENNReal.ofReal q) (stdGaussian E) ≤
      ENNReal.ofReal (Real.exp (1 + D / 4)) := by
    apply max_square_exp_q_norm_le_uniform B hv a D q hD
    · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, logScale] using ha
    · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, logScale] using hqL
  calc
    _ ≤ eLpNorm (K • G) (ENNReal.ofReal q) (stdGaussian E) := hb
    _ = ENNReal.ofReal K * eLpNorm G (ENNReal.ofReal q) (stdGaussian E) := by
      rw [eLpNorm_const_smul]
      simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hK]
    _ ≤ _ := by gcongr

/-- Fixed logarithmic moment order: a single explicit noise condition
suffices, uniformly in the number of scores and the ambient dimension. -/
theorem smoothPairError_log_order_norm_le (n : ℕ) (B : Fin (n + 2) → E)
    (hv : ∀ i, ‖B i‖ ≤ 1) (a : Fin (n + 2) → ℝ) (A D r : ℝ)
    (hA : 1 ≤ A) (hD : 0 ≤ D)
    (ha : ∀ i, (a i) ^ 2 ≤ D * logScale n)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * A * r * (logScale n) ^ 3 ≤ 1) :
    eLpNorm (fun x : E => smoothPairError n r (fun i => a i + inner ℝ (B i) x) / r)
      (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ≤
      ENNReal.ofReal (momentConstant A * logScale n * Real.sqrt (logScale n)) *
        ENNReal.ofReal (Real.exp (1 + D / 4)) := by
  apply smoothPairError_div_norm_le n B hv a A D r (A * logScale n)
    (by linarith) hD ha hr hrhalf
  · have hL : 0 ≤ logScale n := by linarith [logScale_one_le n]
    nlinarith
  · exact le_rfl
  · exact hrL
  · convert hsmall using 1
    ring

/-- Uniform eventual moment endpoint for the whole voting range. The
threshold depends on `A`, not on dimension, the Gaussian score family,
the allowed shift parameter `D`, or the chosen positive noise `r`. -/
theorem exists_uniform_smoothPairError_moment_threshold (A : ℝ) (hA : 1 ≤ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (B : Fin (n + 2) → E), (∀ i, ‖B i‖ ≤ 1) →
      ∀ (a : Fin (n + 2) → ℝ) (D r : ℝ), 0 ≤ D →
      (∀ i, (a i) ^ 2 ≤ D * logScale n) →
      0 < r → r ≤ 1 / ((n : ℝ) + 1) →
      MemLp (fun x : E => smoothPairError n r (fun i => a i + inner ℝ (B i) x) / r)
        (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ∧
      eLpNorm (fun x : E => smoothPairError n r (fun i => a i + inner ℝ (B i) x) / r)
        (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ≤
        ENNReal.ofReal (momentConstant A * logScale n * Real.sqrt (logScale n)) *
          ENNReal.ofReal (Real.exp (1 + D / 4)) := by
  obtain ⟨N, hN⟩ := exists_voting_noise_threshold A (by linarith)
  refine ⟨N, ?_⟩
  intro n hn B hv a D r hD ha hr hrange
  obtain ⟨hrhalf, hrL, hsmall⟩ := hN n hn r hr hrange
  have hq : 1 ≤ A * logScale n := by nlinarith [logScale_one_le n]
  have hsmall' : 2560 * rangeFacetConstant * r * (A * logScale n) *
      (logScale n) ^ 2 ≤ 1 := by
    convert hsmall using 1
    ring
  exact ⟨smoothPairError_div_memLp n B hv a A r (A * logScale n)
      (by linarith) hr hrhalf hq le_rfl hrL hsmall',
    smoothPairError_log_order_norm_le n B hv a A D r hA hD ha hr hrhalf hrL hsmall⟩

end Euclidean
end NegativeVotingSmoothErrorMoment
