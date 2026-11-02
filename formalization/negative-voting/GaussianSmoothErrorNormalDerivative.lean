import GaussianSmoothErrorMoment

/-!
# Actual normal derivatives of the smooth pair-error envelope

The score slopes are literal affine directional derivatives.  This module
does not assert a derivative bound for the separate structured forcing.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Topology Classical ENNReal

namespace NegativeVotingSmoothErrorNormalDerivative
open NegativeVoting NegativeVotingRegularPairCoefficient
  NegativeVotingRegularFacetRange NegativeVotingSquareExponential
  NegativeVotingSmoothErrorMoment

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The difference of the two softmax averages of the score slopes. -/
def smoothRangeDirectional (u b : ι → ℝ) : ℝ :=
  (∑ i, Real.exp (u i) * b i) / (∑ i, Real.exp (u i)) -
    (∑ i, Real.exp (-u i) * b i) / (∑ i, Real.exp (-u i))

theorem hasDerivAt_smoothUtilityRange (u b : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => smoothUtilityRange (fun i => u i + s * b i))
      (smoothRangeDirectional (fun i => u i + t * b i) b) t := by
  have hp (i : ι) : HasDerivAt (fun s : ℝ => Real.exp (u i + s * b i))
      (Real.exp (u i + t * b i) * b i) t := by
    simpa using (((hasDerivAt_id t).mul_const (b i)).const_add (u i)).exp
  have hn (i : ι) : HasDerivAt (fun s : ℝ => Real.exp (-(u i + s * b i)))
      (Real.exp (-(u i + t * b i)) * (-b i)) t := by
    simpa using (((hasDerivAt_id t).mul_const (b i)).const_add (u i)).neg.exp
  have hps := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hp i)).log
    (sum_exp_pos (fun i => u i + t * b i)).ne'
  have hns := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hn i)).log
    (sum_exp_pos (fun i => -(u i + t * b i))).ne'
  convert hps.add hns using 1
  · rfl
  · simp only [smoothRangeDirectional, mul_neg, Finset.sum_neg_distrib, neg_div]
    ring

theorem abs_softmax_average_le_one (u b : ι → ℝ) (hb : ∀ i, |b i| ≤ 1) :
    |(∑ i, Real.exp (u i) * b i) / (∑ i, Real.exp (u i))| ≤ 1 := by
  have hn : |∑ i, Real.exp (u i) * b i| ≤ ∑ i, Real.exp (u i) := by
    calc
      _ ≤ ∑ i, |Real.exp (u i) * b i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        simpa using mul_le_mul_of_nonneg_left (hb i) (Real.exp_pos (u i)).le)
  rw [abs_div, abs_of_pos (sum_exp_pos u)]
  exact (div_le_one (sum_exp_pos u)).mpr hn

theorem abs_smoothRangeDirectional_le (u b : ι → ℝ) (hb : ∀ i, |b i| ≤ 1) :
    |smoothRangeDirectional u b| ≤ 2 := by
  unfold smoothRangeDirectional
  have hp := abs_softmax_average_le_one u b hb
  have hn := abs_softmax_average_le_one (fun i => -u i) b hb
  exact abs_le.mpr ⟨by linarith [(abs_le.mp hp).1, (abs_le.mp hn).2],
    by linarith [(abs_le.mp hp).2, (abs_le.mp hn).1]⟩

/-- The exact derivative of the literal smooth error; the final factor is
the actual softmax directional derivative, not an assumed majorant. -/
def smoothPairDirectional (n : ℕ) (r : ℝ) (u b : ι → ℝ) : ℝ :=
  let τ := r / Real.sqrt (1 - r ^ 2)
  let W := smoothUtilityRange u
  let Q := rangeExponent n (τ * W)
  (1 + 2 * r ^ 2 + Q) * Real.exp Q * rangeFacetConstant * τ *
    (Real.sqrt (logScale n) + 2 * τ * W) * smoothRangeDirectional u b

theorem hasDerivAt_smoothPairError (n : ℕ) (r : ℝ) (u b : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => smoothPairError n r (fun i => u i + s * b i))
      (smoothPairDirectional n r (fun i => u i + t * b i) b) t := by
  let τ := r / Real.sqrt (1 - r ^ 2)
  let W := fun s : ℝ => smoothUtilityRange (fun i => u i + s * b i)
  let Q := fun s : ℝ => rangeExponent n (τ * W s)
  have hW := hasDerivAt_smoothUtilityRange u b t
  have hQ : HasDerivAt Q
      (rangeFacetConstant * τ * (Real.sqrt (logScale n) + 2 * τ * W t) *
        smoothRangeDirectional (fun i => u i + t * b i) b) t := by
    convert (((hW.const_mul τ).mul_const (Real.sqrt (logScale n))).add
      ((hW.const_mul τ).pow 2)).const_mul rangeFacetConstant using 1
    · funext s
      simp only [Q, W, rangeExponent, logScale, Pi.add_apply, Pi.pow_apply]
    · dsimp [W]
      ring
  convert (hQ.const_add (2 * r ^ 2)).mul hQ.exp using 1
  · rfl
  · simp only [smoothPairDirectional, Q, W, τ]
    ring

theorem deriv_smoothPairError (n : ℕ) (r : ℝ) (u b : ι → ℝ) (t : ℝ) :
    deriv (fun s : ℝ => smoothPairError n r (fun i => u i + s * b i)) t =
      smoothPairDirectional n r (fun i => u i + t * b i) b :=
  (hasDerivAt_smoothPairError n r u b t).deriv

theorem continuous_smoothRangeDirectional (b : ι → ℝ) :
    Continuous (fun u : ι → ℝ => smoothRangeDirectional u b) := by
  unfold smoothRangeDirectional
  apply Continuous.sub
  · exact (by fun_prop : Continuous (fun u : ι → ℝ => ∑ i, Real.exp (u i) * b i)).div
      (by fun_prop) (fun u => (sum_exp_pos u).ne')
  · exact (by fun_prop : Continuous (fun u : ι → ℝ => ∑ i, Real.exp (-u i) * b i)).div
      (by fun_prop) (fun u => (sum_exp_pos (fun i => -u i)).ne')

theorem continuous_smoothPairDirectional (n : ℕ) (r : ℝ) (b : ι → ℝ) :
    Continuous (fun u : ι → ℝ => smoothPairDirectional n r u b) := by
  have hW := (smoothUtilityRange_contDiff (ι := ι)).continuous
  have hD := continuous_smoothRangeDirectional b
  unfold smoothPairDirectional rangeExponent
  fun_prop

end Finite

def derivativeMomentConstant (A : ℝ) : ℝ :=
  8 * rangeFacetConstant * Real.exp 1 * (13 + 64 * A)

theorem derivativeMomentConstant_nonneg (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ derivativeMomentConstant A := by
  have hC := rangeFacetConstant_pos.le
  unfold derivativeMomentConstant
  positivity

/-- Scalar absorption for the derivative prefactor. -/
theorem scalar_derivative_envelope (C A L M r q v Q : ℝ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hL : 1 ≤ L) (hM : 0 ≤ M)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hrL : r * L ^ 2 ≤ 1)
    (hq : 1 ≤ q) (hqA : q ≤ A * L)
    (hv : 0 ≤ v) (hvupper : v ≤ 4 * r * (L + M))
    (hQ : 0 ≤ Q) (hQupper : Q ≤ (1 + M ^ 2) / (64 * q)) :
    4 * C * (Real.sqrt L + 2 * v) * (1 + 2 * r ^ 2 + Q) * Real.exp Q ≤
      (8 * C * Real.exp 1 * (13 + 64 * A)) * L * Real.sqrt L *
        Real.exp (M ^ 2 / (8 * q)) := by
  have hq0 : 0 < q := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hs0 := Real.sqrt_nonneg L
  have hs2 := Real.sq_sqrt hL0
  have hs1 : 1 ≤ Real.sqrt L := by nlinarith
  have hLs : 1 ≤ L * Real.sqrt L := by nlinarith
  have hsLs : Real.sqrt L ≤ L * Real.sqrt L := by nlinarith
  have hL23 : L ≤ L ^ 2 := by nlinarith
  have hrL1 : r * L ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hL23 hr.le
    linarith
  have hv' : v ≤ 4 + 2 * M := by
    have hh := mul_le_mul_of_nonneg_right hrhalf hM
    nlinarith
  let E := Real.exp (M ^ 2 / (16 * q))
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hE0 : 0 ≤ E := by positivity
  have hME : M ^ 2 ≤ 16 * q * E := by
    have he := Real.add_one_le_exp (M ^ 2 / (16 * q))
    have hh := (div_le_iff₀ (by positivity : 0 < 16 * q)).mp
      (show M ^ 2 / (16 * q) ≤ E by dsimp [E]; linarith)
    nlinarith
  have hM1 : M ≤ 1 + M ^ 2 := by nlinarith [sq_nonneg (M - 1 / 2)]
  have hlin : Real.sqrt L + 2 * v ≤ (13 + 64 * A) * L * Real.sqrt L * E := by
    have hqLs : q ≤ A * L * Real.sqrt L := by
      have hh := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ A * L)
      exact hqA.trans (by simpa using hh)
    have hh := mul_le_mul_of_nonneg_right hqLs hE0
    have hh' := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ L * Real.sqrt L)
    nlinarith
  have hfac : 1 + 2 * r ^ 2 + Q ≤ 2 * Real.exp Q := by
    have he := Real.add_one_le_exp Q
    nlinarith
  have hQ' : 2 * Q ≤ 1 + M ^ 2 / (16 * q) := by
    have hh : 2 * ((1 + M ^ 2) / (64 * q)) ≤ 1 + M ^ 2 / (16 * q) := by
      field_simp
      nlinarith [sq_nonneg M]
    linarith
  have he : E * Real.exp (2 * Q) ≤ Real.exp 1 * Real.exp (M ^ 2 / (8 * q)) := by
    dsimp [E]
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have heq : M ^ 2 / (8 * q) = 2 * (M ^ 2 / (16 * q)) := by ring
    linarith
  calc
    _ ≤ 4 * C * (Real.sqrt L + 2 * v) * (2 * Real.exp Q) * Real.exp Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by positivity))
        (Real.exp_pos _).le
    _ = 8 * C * (Real.sqrt L + 2 * v) * Real.exp (2 * Q) := by
      rw [show (2 : ℝ) * Q = Q + Q by ring, Real.exp_add]
      ring
    _ ≤ 8 * C * ((13 + 64 * A) * L * Real.sqrt L * E) * Real.exp (2 * Q) := by
      gcongr
    _ = (8 * C * (13 + 64 * A) * L * Real.sqrt L) * (E * Real.exp (2 * Q)) := by ring
    _ ≤ (8 * C * (13 + 64 * A) * L * Real.sqrt L) *
        (Real.exp 1 * Real.exp (M ^ 2 / (8 * q))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- Pointwise control of the actual derivative, normalized by the noise
parameter.  The bound loses no inverse power of `r`. -/
theorem smoothPairDirectional_div_le (n : ℕ) (A r q : ℝ)
    (hA : 0 ≤ A) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hq : 1 ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1)
    (u b : Fin (n + 2) → ℝ) (hb : ∀ i, |b i| ≤ 1) :
    |smoothPairDirectional n r u b| / r ≤ derivativeMomentConstant A *
      logScale n * Real.sqrt (logScale n) *
        Real.exp ((maxScore (fun i => |u i|)) ^ 2 / (8 * q)) := by
  let L := logScale n
  let M := maxScore (fun i => |u i|)
  let W := smoothUtilityRange u
  let τ := r / Real.sqrt (1 - r ^ 2)
  let v := τ * W
  let Q := rangeExponent n v
  have hL : 1 ≤ L := logScale_one_le n
  have hM : 0 ≤ M := (abs_nonneg (u 0)).trans
    (Finset.le_sup' (fun i => |u i|) (Finset.mem_univ 0))
  have hW : 0 ≤ W := smoothUtilityRange_nonneg u
  have hWupper : W ≤ 2 * L + 2 * M := by
    have hh := smoothUtilityRange_le_max_abs u
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at hh
    dsimp [W, M, L, logScale]
    linarith
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτupper : τ ≤ 2 * r := by
    have hh := (noise_prefactor_bounds r hr hrhalf).2
    have hh' : (Real.sqrt (1 - r ^ 2))⁻¹ ≤ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh' hr.le
    simpa only [τ, div_eq_mul_inv, mul_comm r 2] using hm
  have hv : 0 ≤ v := mul_nonneg hτ hW
  have hvupper : v ≤ 4 * r * (L + M) := by
    calc
      _ ≤ (2 * r) * W := mul_le_mul_of_nonneg_right hτupper hW
      _ ≤ (2 * r) * (2 * L + 2 * M) :=
        mul_le_mul_of_nonneg_left hWupper (by positivity)
      _ = _ := by ring
  have hQ : 0 ≤ Q := rangeExponent_nonneg n v hv
  have hQupper : Q ≤ (1 + M ^ 2) / (64 * q) :=
    range_exponent_small rangeFacetConstant L M r q v rangeFacetConstant_pos.le
      hL hM hr hrhalf (by linarith) hsmall hv hvupper
  let K := (1 + 2 * r ^ 2 + Q) * Real.exp Q * rangeFacetConstant *
    (Real.sqrt L + 2 * v)
  have hK : 0 ≤ K := by
    have hC := rangeFacetConstant_pos.le
    dsimp [K]
    positivity
  have hformula : smoothPairDirectional n r u b = K * τ * smoothRangeDirectional u b := by
    dsimp [smoothPairDirectional, K, Q, v, L, W, τ]
    ring
  have hτdiv : τ / r ≤ 2 := (div_le_iff₀ hr).mpr hτupper
  have hD := abs_smoothRangeDirectional_le u b hb
  have hrough : |smoothPairDirectional n r u b| / r ≤
      4 * rangeFacetConstant * (Real.sqrt L + 2 * v) *
        (1 + 2 * r ^ 2 + Q) * Real.exp Q := by
    calc
      _ = K * (τ / r) * |smoothRangeDirectional u b| := by
        rw [hformula, abs_mul, abs_mul, abs_of_nonneg hK, abs_of_nonneg hτ]
        ring
      _ ≤ K * 2 * 2 := by gcongr
      _ = _ := by dsimp [K]; ring
  exact hrough.trans (scalar_derivative_envelope rangeFacetConstant A L M r q v Q
    rangeFacetConstant_pos.le hA hL hM hr hrhalf hrL hq hqA hv hvupper hQ hQupper)

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasDerivAt_smoothPairError_affine (n : ℕ) (r : ℝ)
    (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ) (x v : E) :
    HasDerivAt (fun t : ℝ => smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v)))
      (smoothPairDirectional n r (fun i => a i + inner ℝ (B i) x)
        (fun i => inner ℝ (B i) v)) 0 := by
  have hh := hasDerivAt_smoothPairError n r
    (fun i => a i + inner ℝ (B i) x) (fun i => inner ℝ (B i) v) 0
  simpa only [inner_add_right, real_inner_smul_right, add_assoc, zero_mul, add_zero] using hh

private theorem directional_aestronglyMeasurable (n : ℕ) (r : ℝ)
    (B : Fin (n + 2) → E) (a b : Fin (n + 2) → ℝ) :
    AEStronglyMeasurable (fun x : E =>
      smoothPairDirectional n r (fun i => a i + inner ℝ (B i) x) b / r) (stdGaussian E) := by
  have hu : Continuous (fun x : E => fun i => a i + inner ℝ (B i) x) := by fun_prop
  exact (((continuous_smoothPairDirectional n r b).comp hu).div_const r).aestronglyMeasurable

theorem smoothPairDirectional_div_memLp (n : ℕ) (B : Fin (n + 2) → E)
    (hv : ∀ i, ‖B i‖ ≤ 1) (a b : Fin (n + 2) → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (A r q : ℝ) (hA : 0 ≤ A) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hq : 1 ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1) :
    MemLp (fun x : E => smoothPairDirectional n r (fun i => a i + inner ℝ (B i) x) b / r)
      (ENNReal.ofReal q) (stdGaussian E) := by
  have hq0 : 0 < q := by linarith
  have hmem := (max_square_exp_q_memLp B hv a q hq0).const_mul
    (derivativeMomentConstant A * logScale n * Real.sqrt (logScale n))
  apply hmem.mono' (directional_aestronglyMeasurable n r B a b)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hr]
  exact smoothPairDirectional_div_le n A r q hA hr hrhalf hq hqA hrL hsmall _ b hb

theorem smoothPairDirectional_div_norm_le (n : ℕ) (B : Fin (n + 2) → E)
    (hv : ∀ i, ‖B i‖ ≤ 1) (a b : Fin (n + 2) → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (A D r q : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (ha : ∀ i, (a i) ^ 2 ≤ D * logScale n)
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hqL : logScale n ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1) :
    eLpNorm (fun x : E => smoothPairDirectional n r (fun i => a i + inner ℝ (B i) x) b / r)
      (ENNReal.ofReal q) (stdGaussian E) ≤
      ENNReal.ofReal (derivativeMomentConstant A * logScale n * Real.sqrt (logScale n)) *
        ENNReal.ofReal (Real.exp (1 + D / 4)) := by
  have hq : 1 ≤ q := (logScale_one_le n).trans hqL
  let K := derivativeMomentConstant A * logScale n * Real.sqrt (logScale n)
  let G := fun x : E => Real.exp ((affineMaxAbs B a x) ^ 2 / (8 * q))
  have hK : 0 ≤ K := by
    have hC := derivativeMomentConstant_nonneg A hA
    have hL := logScale_one_le n
    dsimp [K]
    positivity
  have hbound := eLpNorm_mono_real (directional_aestronglyMeasurable n r B a b)
    (g := fun x : E => K * G x) (p := ENNReal.ofReal q) (fun x => by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hr]
      exact smoothPairDirectional_div_le n A r q hA hr hrhalf hq hqA hrL hsmall _ b hb)
  have hG : eLpNorm G (ENNReal.ofReal q) (stdGaussian E) ≤
      ENNReal.ofReal (Real.exp (1 + D / 4)) := by
    apply max_square_exp_q_norm_le_uniform B hv a D q hD
    · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, logScale] using ha
    · simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat, logScale] using hqL
  calc
    _ ≤ eLpNorm (K • G) (ENNReal.ofReal q) (stdGaussian E) := hbound
    _ = ENNReal.ofReal K * eLpNorm G (ENNReal.ofReal q) (stdGaussian E) := by
      rw [eLpNorm_const_smul]
      simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hK]
    _ ≤ _ := by gcongr

/-- Actual normal-direction derivative and its Gaussian moment, uniformly
over the voting range after one dimension-independent threshold. -/
theorem exists_uniform_normal_derivative_moment_threshold (A : ℝ) (hA : 1 ≤ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (B : Fin (n + 2) → E), (∀ i, ‖B i‖ ≤ 1) →
      ∀ (a : Fin (n + 2) → ℝ) (D r : ℝ) (v : E),
      0 ≤ D → (∀ i, (a i) ^ 2 ≤ D * logScale n) → ‖v‖ ≤ 1 →
      0 < r → r ≤ 1 / ((n : ℝ) + 1) →
      let F := fun x : E =>
        deriv (fun t : ℝ => smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v))) 0 / r
      MemLp F (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ∧
      eLpNorm F (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ≤
        ENNReal.ofReal (derivativeMomentConstant A * logScale n * Real.sqrt (logScale n)) *
          ENNReal.ofReal (Real.exp (1 + D / 4)) := by
  obtain ⟨N, hN⟩ := exists_voting_noise_threshold A (by linarith)
  refine ⟨N, ?_⟩
  intro n hn B hv a D r v hD ha hvnorm hr hrange
  obtain ⟨hrhalf, hrL, hsmall⟩ := hN n hn r hr hrange
  have hb : ∀ i, |inner ℝ (B i) v| ≤ 1 := by
    intro i
    exact (abs_real_inner_le_norm (B i) v).trans (by nlinarith [hv i, norm_nonneg (B i), norm_nonneg v])
  have hqL : logScale n ≤ A * logScale n := by
    have hL0 : 0 ≤ logScale n := by linarith [logScale_one_le n]
    nlinarith
  have hq : 1 ≤ A * logScale n := (logScale_one_le n).trans hqL
  have hsmall' : 2560 * rangeFacetConstant * r * (A * logScale n) *
      (logScale n) ^ 2 ≤ 1 := by convert hsmall using 1; ring
  have heq : (fun x : E =>
      deriv (fun t : ℝ => smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v))) 0 / r) =
      (fun x : E => smoothPairDirectional n r (fun i => a i + inner ℝ (B i) x)
        (fun i => inner ℝ (B i) v) / r) := by
    funext x
    rw [(hasDerivAt_smoothPairError_affine n r B a x v).deriv]
  dsimp only
  rw [heq]
  exact ⟨smoothPairDirectional_div_memLp n B hv a _ hb A r (A * logScale n)
      (by linarith) hr hrhalf hq le_rfl hrL hsmall',
    smoothPairDirectional_div_norm_le n B hv a _ hb A D r (A * logScale n)
      (by linarith) hD ha hr hrhalf hqL le_rfl hrL hsmall'⟩

end Euclidean
end NegativeVotingSmoothErrorNormalDerivative
