import GaussianSmoothErrorNormalDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-!
# One Gaussian envelope for a whole normal segment

The same measurable function controls the literal normalized smooth error,
its actual directional derivative and its increment throughout `[0,1]`.
This concerns the smooth error factor, not the complete structured forcing.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Topology Classical ENNReal

namespace NegativeVotingSmoothErrorTube
open NegativeVoting NegativeVotingRegularPairCoefficient NegativeVotingRegularFacetRange
  NegativeVotingSquareExponential NegativeVotingSmoothErrorMoment
  NegativeVotingSmoothErrorNormalDerivative

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def doubledScore (u : ι → ℝ) (p : ι × Bool) : ℝ :=
  u p.1 + if p.2 then 1 else -1

theorem abs_add_one_le_double_max (u : ι → ℝ) (i : ι) :
    |u i| + 1 ≤ maxScore (fun p : ι × Bool => |doubledScore u p|) := by
  by_cases hu : 0 ≤ u i
  · have hh : |doubledScore u (i, true)| ≤ maxScore (fun p : ι × Bool => |doubledScore u p|) :=
      Finset.le_sup' (fun p : ι × Bool => |doubledScore u p|)
      (Finset.mem_univ (i, true))
    have he : |doubledScore u (i, true)| = |u i| + 1 := by
      dsimp [doubledScore]
      rw [abs_of_nonneg hu, abs_of_nonneg (show 0 ≤ u i + 1 by linarith)]
    rw [he] at hh
    exact hh
  · have hu' : u i ≤ 0 := le_of_not_ge hu
    have hh : |doubledScore u (i, false)| ≤ maxScore (fun p : ι × Bool => |doubledScore u p|) :=
      Finset.le_sup' (fun p : ι × Bool => |doubledScore u p|)
      (Finset.mem_univ (i, false))
    have he : |doubledScore u (i, false)| = |u i| + 1 := by
      dsimp [doubledScore]
      rw [abs_of_nonpos hu', abs_of_nonpos (show u i + -1 ≤ 0 by linarith)]
      ring
    rw [he] at hh
    exact hh

/-- The duplicated family is an exact representation of `max |u_i| + 1`. -/
theorem double_max_eq (u : ι → ℝ) :
    maxScore (fun p : ι × Bool => |doubledScore u p|) = maxScore (fun i => |u i|) + 1 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro p hp
    have hh : |u p.1| ≤ maxScore (fun i => |u i|) :=
      Finset.le_sup' (fun i => |u i|) (Finset.mem_univ p.1)
    have ha := abs_add_le (u p.1) (if p.2 then (1 : ℝ) else -1)
    cases hb : p.2 <;> simp only [hb, Bool.false_eq_true, ite_false, ite_true, abs_neg, abs_one] at ha
      <;> dsimp [doubledScore] <;> rw [hb] <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      <;> linarith
  · let i := chosenWinner (fun i => |u i|)
    have he : maxScore (fun i => |u i|) = |u i| := finite_max_eq_chosenWinner _
    rw [he]
    exact abs_add_one_le_double_max u i

theorem shifted_max_le_double (u b : ι → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    maxScore (fun i => |u i + t * b i|) ≤
      maxScore (fun p : ι × Bool => |doubledScore u p|) := by
  apply Finset.sup'_le
  intro i hi
  have htb : |t * b i| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ht.1]
    have hh := mul_le_mul_of_nonneg_left (hb i) ht.1
    nlinarith [ht.2]
  exact (abs_add_le _ _).trans ((show |u i| + |t * b i| ≤ |u i| + 1 by linarith).trans
    (abs_add_one_le_double_max u i))

end Finite

def tubeConstant (A : ℝ) : ℝ := momentConstant A + derivativeMomentConstant A

theorem tubeConstant_nonneg (A : ℝ) (hA : 0 ≤ A) : 0 ≤ tubeConstant A :=
  add_nonneg (momentConstant_nonneg A hA) (derivativeMomentConstant_nonneg A hA)

def scalarTubeEnvelope (n : ℕ) (A q : ℝ) (u : Fin (n + 2) → ℝ) : ℝ :=
  tubeConstant A * logScale n * Real.sqrt (logScale n) *
    Real.exp ((maxScore (fun p : Fin (n + 2) × Bool => |doubledScore u p|)) ^ 2 / (8 * q))

theorem scalarTubeEnvelope_nonneg (n : ℕ) (A q : ℝ) (hA : 0 ≤ A)
    (u : Fin (n + 2) → ℝ) : 0 ≤ scalarTubeEnvelope n A q u := by
  have hC := tubeConstant_nonneg A hA
  have hL := logScale_one_le n
  unfold scalarTubeEnvelope
  positivity

/-- A single pointwise envelope controls both the value and derivative at
every point of the closed normal segment. -/
theorem scalar_tube_control (n : ℕ) (A r q : ℝ)
    (hA : 0 ≤ A) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hq : 1 ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1)
    (u b : Fin (n + 2) → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |smoothPairError n r (fun i => u i + t * b i)| / r ≤ scalarTubeEnvelope n A q u ∧
      |smoothPairDirectional n r (fun i => u i + t * b i) b| / r ≤
        scalarTubeEnvelope n A q u := by
  let M := maxScore (fun i => |u i + t * b i|)
  let M' := maxScore (fun p : Fin (n + 2) × Bool => |doubledScore u p|)
  have hM : 0 ≤ M := (abs_nonneg (u 0 + t * b 0)).trans
    (Finset.le_sup' (fun i => |u i + t * b i|) (Finset.mem_univ 0))
  have hMM' : M ≤ M' := shifted_max_le_double u b hb t ht
  have hsq := (sq_le_sq₀ hM (hM.trans hMM')).mpr hMM'
  have he : Real.exp (M ^ 2 / (8 * q)) ≤ Real.exp (M' ^ 2 / (8 * q)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hL : 0 ≤ logScale n := by linarith [logScale_one_le n]
  have hC0 := momentConstant_nonneg A hA
  have hC1 := derivativeMomentConstant_nonneg A hA
  have hCT := tubeConstant_nonneg A hA
  have hC0' : momentConstant A ≤ tubeConstant A := by unfold tubeConstant; linarith
  have hC1' : derivativeMomentConstant A ≤ tubeConstant A := by unfold tubeConstant; linarith
  constructor
  · rw [abs_of_nonneg (smoothPairError_nonneg n r hr (by linarith) _)]
    apply (smoothPairError_div_le n A r q hA hr hrhalf hq hqA hrL hsmall _).trans
    unfold scalarTubeEnvelope
    change momentConstant A * logScale n * Real.sqrt (logScale n) * Real.exp (M ^ 2 / (8 * q)) ≤ _
    gcongr
  · apply (smoothPairDirectional_div_le n A r q hA hr hrhalf hq hqA hrL hsmall _ b hb).trans
    unfold scalarTubeEnvelope
    change derivativeMomentConstant A * logScale n * Real.sqrt (logScale n) * Real.exp (M ^ 2 / (8 * q)) ≤ _
    gcongr

theorem scalar_tube_increment (n : ℕ) (A r q : ℝ)
    (hA : 0 ≤ A) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hq : 1 ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1)
    (u b : Fin (n + 2) → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |smoothPairError n r (fun i => u i + t * b i) - smoothPairError n r u| / r ≤
      scalarTubeEnvelope n A q u * t := by
  have hder (s : ℝ) : HasDerivAt
      (fun z : ℝ => smoothPairError n r (fun i => u i + z * b i) / r)
      (smoothPairDirectional n r (fun i => u i + s * b i) b / r) s :=
    (hasDerivAt_smoothPairError n r u b s).div_const r
  have hbound (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) :
      ‖smoothPairDirectional n r (fun i => u i + s * b i) b / r‖ ≤ scalarTubeEnvelope n A q u := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr]
    exact (scalar_tube_control n A r q hA hr hrhalf hq hqA hrL hsmall u b hb s
      ⟨hs.1, hs.2.le⟩).2
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := 1) (fun s _ => (hder s).hasDerivWithinAt) hbound t ht
  simpa only [zero_mul, add_zero, sub_zero, ← sub_div, Real.norm_eq_abs,
    abs_div, abs_of_pos hr] using hh

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def doubledRows {ι : Type*} (B : ι → E) (p : ι × Bool) : E := B p.1
def doubledMeans {ι : Type*} (a : ι → ℝ) (p : ι × Bool) : ℝ :=
  a p.1 + if p.2 then 1 else -1

def tubeEnvelope (n : ℕ) (A q : ℝ) (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ)
    (x : E) : ℝ :=
  tubeConstant A * logScale n * Real.sqrt (logScale n) *
    Real.exp ((affineMaxAbs (doubledRows B) (doubledMeans a) x) ^ 2 / (8 * q))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem tubeEnvelope_eq_scalar (n : ℕ) (A q : ℝ)
    (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ) (x : E) :
    tubeEnvelope n A q B a x = scalarTubeEnvelope n A q (fun i => a i + inner ℝ (B i) x) := by
  unfold tubeEnvelope scalarTubeEnvelope affineMaxAbs
  congr 4
  congr 1
  funext p
  congr 1
  dsimp [doubledRows, doubledMeans, doubledScore]
  ring

theorem measurable_tubeEnvelope (n : ℕ) (A q : ℝ)
    (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ) :
    Measurable (tubeEnvelope n A q B a) := by
  unfold tubeEnvelope
  fun_prop

theorem double_logScale_bounds (n : ℕ) :
    logScale n ≤ 1 + Real.log (Fintype.card (Fin (n + 2) × Bool) : ℝ) ∧
      1 + Real.log (Fintype.card (Fin (n + 2) × Bool) : ℝ) ≤ 2 * logScale n := by
  have hm : 0 < (n : ℝ) + 2 := by positivity
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have htwo := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  have htwo' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_add, Nat.cast_ofNat, Real.log_mul hm.ne' (by norm_num : (2 : ℝ) ≠ 0), logScale]
  constructor <;> linarith

theorem tubeEnvelope_memLp (n : ℕ) (A q : ℝ) (hq : 0 < q)
    (B : Fin (n + 2) → E) (hv : ∀ i, ‖B i‖ ≤ 1) (a : Fin (n + 2) → ℝ) :
    MemLp (tubeEnvelope n A q B a) (ENNReal.ofReal q) (stdGaussian E) :=
  (max_square_exp_q_memLp (doubledRows B) (fun p => hv p.1) (doubledMeans a) q hq).const_mul _

theorem tubeEnvelope_norm_le (n : ℕ) (A D q : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hq : 2 * logScale n ≤ q)
    (B : Fin (n + 2) → E) (hv : ∀ i, ‖B i‖ ≤ 1)
    (a : Fin (n + 2) → ℝ) (ha : ∀ i, (a i) ^ 2 ≤ D * logScale n) :
    eLpNorm (tubeEnvelope n A q B a) (ENNReal.ofReal q) (stdGaussian E) ≤
      ENNReal.ofReal (tubeConstant A * logScale n * Real.sqrt (logScale n)) *
        ENNReal.ofReal (Real.exp (1 + (2 * D + 2) / 4)) := by
  have hL := logScale_one_le n
  have hD' : 0 ≤ 2 * D + 2 := by positivity
  have hmeans (p : Fin (n + 2) × Bool) : (doubledMeans a p) ^ 2 ≤
      (2 * D + 2) * (1 + Real.log (Fintype.card (Fin (n + 2) × Bool) : ℝ)) := by
    have hbase : (doubledMeans a p) ^ 2 ≤ (2 * D + 2) * logScale n := by
      have hh := ha p.1
      cases hb : p.2 <;> simp only [doubledMeans, hb, Bool.false_eq_true, ite_false, ite_true]
        <;> nlinarith [sq_nonneg (a p.1 - 1), sq_nonneg (a p.1 + 1)]
    exact hbase.trans (mul_le_mul_of_nonneg_left (double_logScale_bounds n).1 hD')
  have he := max_square_exp_q_norm_le_uniform (doubledRows B) (fun p => hv p.1)
    (doubledMeans a) (2 * D + 2) q hD' hmeans ((double_logScale_bounds n).2.trans hq)
  have hK : 0 ≤ tubeConstant A * logScale n * Real.sqrt (logScale n) := by
    have hC := tubeConstant_nonneg A hA
    positivity
  unfold tubeEnvelope
  change eLpNorm ((_ : ℝ) • (fun x : E => Real.exp
    ((affineMaxAbs (doubledRows B) (doubledMeans a) x) ^ 2 / (8 * q)))) _ _ ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hK]
  gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem tube_control (n : ℕ) (A r q : ℝ)
    (hA : 0 ≤ A) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hq : 1 ≤ q) (hqA : q ≤ A * logScale n)
    (hrL : r * (logScale n) ^ 2 ≤ 1)
    (hsmall : 2560 * rangeFacetConstant * r * q * (logScale n) ^ 2 ≤ 1)
    (B : Fin (n + 2) → E) (hv : ∀ i, ‖B i‖ ≤ 1)
    (a : Fin (n + 2) → ℝ) (v x : E) (hvnorm : ‖v‖ ≤ 1) :
    ContinuousOn (fun t : ℝ =>
      smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v)) / r) (Icc 0 1) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      |smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v))| / r ≤
        tubeEnvelope n A q B a x ∧
      |deriv (fun s : ℝ => smoothPairError n r (fun i => a i + inner ℝ (B i) (x + s • v))) t| / r ≤
        tubeEnvelope n A q B a x ∧
      |smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v)) -
        smoothPairError n r (fun i => a i + inner ℝ (B i) x)| / r ≤
        tubeEnvelope n A q B a x * t := by
  let u := fun i => a i + inner ℝ (B i) x
  let b := fun i => inner ℝ (B i) v
  have hb : ∀ i, |b i| ≤ 1 := by
    intro i
    exact (abs_real_inner_le_norm (B i) v).trans
      (by nlinarith [hv i, norm_nonneg (B i), norm_nonneg v])
  have hpath (t : ℝ) : HasDerivAt
      (fun s : ℝ => smoothPairError n r (fun i => a i + inner ℝ (B i) (x + s • v)))
      (smoothPairDirectional n r (fun i => u i + t * b i) b) t := by
    simpa only [u, b, inner_add_right, real_inner_smul_right, add_assoc] using
      hasDerivAt_smoothPairError n r u b t
  constructor
  · intro t ht
    exact ((hpath t).div_const r).continuousAt.continuousWithinAt
  · intro t ht
    rw [(hpath t).deriv, tubeEnvelope_eq_scalar]
    have hc := scalar_tube_control n A r q hA hr hrhalf hq hqA hrL hsmall u b hb t ht
    have hi := scalar_tube_increment n A r q hA hr hrhalf hq hqA hrL hsmall u b hb t ht
    refine ⟨?_, hc.2, ?_⟩
    · simpa only [u, b, inner_add_right, real_inner_smul_right, add_assoc] using hc.1
    · simpa only [u, b, inner_add_right, real_inner_smul_right, add_assoc] using hi

/-- One nonnegative measurable `L^q` envelope works simultaneously for every
normal vector of norm at most one, every tube parameter in `[0,1]`, and
every noise in the voting range.  Its construction is independent of all
three of these parameters. -/
theorem exists_uniform_smooth_error_tube (A : ℝ) (hA : 2 ≤ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (B : Fin (n + 2) → E), (∀ i, ‖B i‖ ≤ 1) →
      ∀ (a : Fin (n + 2) → ℝ) (D : ℝ), 0 ≤ D →
      (∀ i, (a i) ^ 2 ≤ D * logScale n) →
      ∃ W : E → ℝ, Measurable W ∧ (∀ x, 0 ≤ W x) ∧
        MemLp W (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ∧
        eLpNorm W (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ≤
          ENNReal.ofReal (tubeConstant A * logScale n * Real.sqrt (logScale n)) *
            ENNReal.ofReal (Real.exp (1 + (2 * D + 2) / 4)) ∧
        ∀ r : ℝ, 0 < r → r ≤ 1 / ((n : ℝ) + 1) →
          ∀ v : E, ‖v‖ ≤ 1 → ∀ x : E,
          ContinuousOn (fun t : ℝ =>
            smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v)) / r) (Icc 0 1) ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            |smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v))| / r ≤ W x ∧
            |deriv (fun s : ℝ => smoothPairError n r
              (fun i => a i + inner ℝ (B i) (x + s • v))) t| / r ≤ W x ∧
            |smoothPairError n r (fun i => a i + inner ℝ (B i) (x + t • v)) -
              smoothPairError n r (fun i => a i + inner ℝ (B i) x)| / r ≤ W x * t := by
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨N, hN⟩ := exists_voting_noise_threshold A hA0
  refine ⟨N, ?_⟩
  intro n hn B hv a D hD ha
  have hL := logScale_one_le n
  have hq : 2 * logScale n ≤ A * logScale n := by nlinarith
  have hq0 : 0 < A * logScale n := by nlinarith
  refine ⟨tubeEnvelope n A (A * logScale n) B a, measurable_tubeEnvelope n A _ B a,
    ?_, tubeEnvelope_memLp n A _ hq0 B hv a, tubeEnvelope_norm_le n A D _ hA0 hD hq B hv a ha, ?_⟩
  · intro x
    rw [tubeEnvelope_eq_scalar]
    exact scalarTubeEnvelope_nonneg n A _ hA0 _
  · intro r hr hrange v hvnorm x
    obtain ⟨hrhalf, hrL, hsmall⟩ := hN n hn r hr hrange
    have hsmall' : 2560 * rangeFacetConstant * r * (A * logScale n) * (logScale n) ^ 2 ≤ 1 := by
      convert hsmall using 1
      ring
    exact tube_control n A r (A * logScale n) hA0 hr hrhalf (by nlinarith) le_rfl
      hrL hsmall' B hv a v x hvnorm

/-- Tangent-space form: the normal slopes need not be represented by a
vector in the Gaussian space.  Thus projected Gaussian rows and the
original normal slopes can be used together on a facet chart. -/
theorem exists_uniform_affine_score_tube (A : ℝ) (hA : 2 ≤ A) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (B : Fin (n + 2) → E), (∀ i, ‖B i‖ ≤ 1) →
      ∀ (a : Fin (n + 2) → ℝ) (D : ℝ), 0 ≤ D →
      (∀ i, (a i) ^ 2 ≤ D * logScale n) →
      ∃ W : E → ℝ, Measurable W ∧ (∀ x, 0 ≤ W x) ∧
        MemLp W (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ∧
        eLpNorm W (ENNReal.ofReal (A * logScale n)) (stdGaussian E) ≤
          ENNReal.ofReal (tubeConstant A * logScale n * Real.sqrt (logScale n)) *
            ENNReal.ofReal (Real.exp (1 + (2 * D + 2) / 4)) ∧
        ∀ r : ℝ, 0 < r → r ≤ 1 / ((n : ℝ) + 1) →
          ∀ b : Fin (n + 2) → ℝ, (∀ i, |b i| ≤ 1) → ∀ x : E,
          ContinuousOn (fun t : ℝ =>
            smoothPairError n r (fun i => a i + inner ℝ (B i) x + t * b i) / r) (Icc 0 1) ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            |smoothPairError n r (fun i => a i + inner ℝ (B i) x + t * b i)| / r ≤ W x ∧
            |deriv (fun s : ℝ => smoothPairError n r
              (fun i => a i + inner ℝ (B i) x + s * b i)) t| / r ≤ W x ∧
            |smoothPairError n r (fun i => a i + inner ℝ (B i) x + t * b i) -
              smoothPairError n r (fun i => a i + inner ℝ (B i) x)| / r ≤ W x * t := by
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨N, hN⟩ := exists_voting_noise_threshold A hA0
  refine ⟨N, ?_⟩
  intro n hn B hv a D hD ha
  have hL := logScale_one_le n
  have hq : 2 * logScale n ≤ A * logScale n := by nlinarith
  have hq0 : 0 < A * logScale n := by nlinarith
  refine ⟨tubeEnvelope n A (A * logScale n) B a, measurable_tubeEnvelope n A _ B a,
    ?_, tubeEnvelope_memLp n A _ hq0 B hv a, tubeEnvelope_norm_le n A D _ hA0 hD hq B hv a ha, ?_⟩
  · intro x
    rw [tubeEnvelope_eq_scalar]
    exact scalarTubeEnvelope_nonneg n A _ hA0 _
  · intro r hr hrange b hb x
    obtain ⟨hrhalf, hrL, hsmall⟩ := hN n hn r hr hrange
    have hsmall' : 2560 * rangeFacetConstant * r * (A * logScale n) * (logScale n) ^ 2 ≤ 1 := by
      convert hsmall using 1
      ring
    let u := fun i => a i + inner ℝ (B i) x
    have hpath (t : ℝ) := hasDerivAt_smoothPairError n r u b t
    constructor
    · intro t ht
      exact ((hpath t).div_const r).continuousAt.continuousWithinAt
    · intro t ht
      rw [(hpath t).deriv, tubeEnvelope_eq_scalar]
      have hc := scalar_tube_control n A r (A * logScale n) hA0 hr hrhalf
        (by nlinarith) le_rfl hrL hsmall' u b hb t ht
      exact ⟨hc.1, hc.2, scalar_tube_increment n A r (A * logScale n) hA0 hr hrhalf
        (by nlinarith) le_rfl hrL hsmall' u b hb t ht⟩

end Euclidean
end NegativeVotingSmoothErrorTube
