import GaussianSmoothErrorTube
import GaussianRegularScoreProjection

/-!
# The literal reciprocal Gaussian damping on a whole normal tube

The smallness condition uses the finite score count, not the ambient
dimension.  For a regular frame its score energy is exactly the squared
norm of the orthogonal frame projection.  Normal slopes are independent
of the tangent Gaussian rows.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Topology Classical ENNReal

namespace NegativeVotingReciprocalDampingTube
open NegativeVoting NegativeVotingRegularPairCoefficient NegativeVotingRegularFacetRange
  NegativeVotingSquareExponential NegativeVotingSmoothErrorMoment NegativeVotingSmoothErrorTube
  NegativeVotingRegularScoreProjection

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def scoreEnergy (u : ι → ℝ) : ℝ := ∑ i, (u i) ^ 2
def kappa (η : ℝ) (u : ι → ℝ) : ℝ := Real.exp (-1 - η * scoreEnergy u)
def inverseKappa (η : ℝ) (u : ι → ℝ) : ℝ := (kappa η u)⁻¹
def inverseKappaDirectional (η : ℝ) (u b : ι → ℝ) : ℝ :=
  2 * η * (∑ i, u i * b i) * inverseKappa η u

omit [Nonempty ι] in
theorem inverseKappa_eq_exp (η : ℝ) (u : ι → ℝ) :
    inverseKappa η u = Real.exp (1 + η * scoreEnergy u) := by
  unfold inverseKappa kappa
  rw [← Real.exp_neg]
  congr 1
  ring

omit [Nonempty ι] in
theorem inverseKappa_pos (η : ℝ) (u : ι → ℝ) : 0 < inverseKappa η u := by
  rw [inverseKappa_eq_exp]
  positivity

omit [Nonempty ι] in
theorem hasDerivAt_inverseKappa (η : ℝ) (u b : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inverseKappa η (fun i => u i + s * b i))
      (inverseKappaDirectional η (fun i => u i + t * b i) b) t := by
  have hi (i : ι) : HasDerivAt (fun s : ℝ => (u i + s * b i) ^ 2)
      (2 * (u i + t * b i) * b i) t := by
    convert (((hasDerivAt_id t).mul_const (b i)).const_add (u i)).pow 2 using 1
    · funext s
      rfl
    · simp
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  convert ((hsum.const_mul η).const_add 1).exp using 1
  · funext s
    rw [inverseKappa_eq_exp]
    rfl
  · rw [inverseKappaDirectional, inverseKappa_eq_exp]
    simp only [scoreEnergy]
    rw [show (∑ i, 2 * (u i + t * b i) * b i) =
      2 * (∑ i, (u i + t * b i) * b i) by rw [Finset.mul_sum]; congr 1; funext i; ring]
    ring

theorem shifted_energy_bounds (u b : ι → ℝ) (hb : ∀ i, |b i| ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let M := maxScore (fun p : ι × Bool => |doubledScore u p|)
    scoreEnergy (fun i => u i + t * b i) ≤ (Fintype.card ι : ℝ) * M ^ 2 ∧
      |∑ i, (u i + t * b i) * b i| ≤ (Fintype.card ι : ℝ) * M := by
  dsimp only
  let M := maxScore (fun p : ι × Bool => |doubledScore u p|)
  have hm : ∀ i, |u i + t * b i| ≤ M := by
    intro i
    exact (Finset.le_sup' (fun i => |u i + t * b i|) (Finset.mem_univ i)).trans
      (shifted_max_le_double u b hb t ht)
  have hM : 0 ≤ M := (abs_nonneg (u (Classical.arbitrary ι) + t * b (Classical.arbitrary ι))).trans
    (hm (Classical.arbitrary ι))
  constructor
  · calc
      _ ≤ ∑ _i : ι, M ^ 2 := Finset.sum_le_sum (fun i _ => by
        have hh := (sq_le_sq₀ (abs_nonneg _) hM).mpr (hm i)
        simpa only [sq_abs] using hh)
      _ = _ := by simp [M]
  · calc
      _ ≤ ∑ i, |(u i + t * b i) * b i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, M := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        have hh := mul_le_mul_of_nonneg_left (hb i) (abs_nonneg (u i + t * b i))
        nlinarith [hm i])
      _ = _ := by simp [M]

/-- One square-exponential controls both the reciprocal and its actual
normal derivative, under a score-count smallness condition. -/
theorem scalar_damping_control (η q : ℝ) (hη : 0 ≤ η) (hq : 1 ≤ q)
    (hsmall : 64 * η * q * (Fintype.card ι : ℝ) ≤ 1)
    (u b : ι → ℝ) (hb : ∀ i, |b i| ≤ 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let W := 2 * Real.exp 1 * Real.exp
      ((maxScore (fun p : ι × Bool => |doubledScore u p|)) ^ 2 / (8 * q))
    inverseKappa η (fun i => u i + t * b i) ≤ W ∧
      |inverseKappaDirectional η (fun i => u i + t * b i) b| ≤ W := by
  let M := maxScore (fun p : ι × Bool => |doubledScore u p|)
  let c := η * (Fintype.card ι : ℝ)
  let E := Real.exp (c * M ^ 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hq0 : 0 < q := by linarith
  have hsmall' : 64 * c * q ≤ 1 := by dsimp [c]; nlinarith [hsmall]
  have hc1 : c ≤ 1 := by nlinarith
  have hM : 0 ≤ M := by
    have hh := abs_add_one_le_double_max u (Classical.arbitrary ι)
    exact (by positivity : 0 ≤ |u (Classical.arbitrary ι)| + 1).trans hh
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hE0 : 0 ≤ E := by positivity
  obtain ⟨henergy, hlin⟩ := shifted_energy_bounds u b hb t ht
  have hval : inverseKappa η (fun i => u i + t * b i) ≤ Real.exp 1 * E := by
    rw [inverseKappa_eq_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left henergy hη
    dsimp [c]
    nlinarith
  have hfactor : 2 * c * M ≤ E := by
    have hs := mul_nonneg hc (sq_nonneg (M - 1))
    have he := Real.add_one_le_exp (c * M ^ 2)
    dsimp [E]
    nlinarith
  have he : Real.exp 1 * E * E ≤ 2 * Real.exp 1 * Real.exp (M ^ 2 / (8 * q)) := by
    have hcq : 2 * c ≤ 1 / (8 * q) := by
      apply (le_div_iff₀ (by positivity : 0 < 8 * q)).mpr
      nlinarith
    have hpow := mul_le_mul_of_nonneg_right hcq (sq_nonneg M)
    have hEE : E * E ≤ Real.exp (M ^ 2 / (8 * q)) := by
      dsimp [E]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      convert hpow using 1 <;> ring
    have hh := mul_le_mul_of_nonneg_left hEE (Real.exp_pos 1).le
    have hnonneg : 0 ≤ Real.exp 1 * Real.exp (M ^ 2 / (8 * q)) := by positivity
    nlinarith
  constructor
  · apply hval.trans
    apply le_trans _ he
    have hh := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ Real.exp 1 * E)
    nlinarith
  · have hd : |inverseKappaDirectional η (fun i => u i + t * b i) b| ≤
        2 * c * M * (Real.exp 1 * E) := by
      rw [inverseKappaDirectional, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * η),
        abs_of_pos (inverseKappa_pos _ _)]
      have hh := mul_le_mul_of_nonneg_left hlin (by positivity : 0 ≤ 2 * η)
      calc
        _ ≤ (2 * η * ((Fintype.card ι : ℝ) * M)) * (Real.exp 1 * E) :=
          mul_le_mul hh hval (inverseKappa_pos _ _).le (by positivity)
        _ = _ := by dsimp [c]; ring
    apply hd.trans
    apply le_trans _ he
    have hh := mul_le_mul_of_nonneg_right hfactor (by positivity : 0 ≤ Real.exp 1 * E)
    nlinarith

end Finite

theorem inverseKappa_regular_projection {m d : ℕ} [NeZero m]
    (B : Fin m → FSC.Coord d)
    (hG : ∀ i j, inner ℝ (B i) (B j) = (if i = j then 1 else 0) - 1 / (m : ℝ))
    (η : ℝ) (x : FSC.Coord d) :
    inverseKappa η (fun i => inner ℝ (B i) x) =
      Real.exp (1 + η * ‖NegativeVotingCenteredParseval.frameOperator B x‖ ^ 2) := by
  rw [inverseKappa_eq_exp, frame_norm_sq B hG]
  rfl

theorem exists_damping_noise_threshold (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ r η : ℝ,
      0 < r → r ≤ 1 / ((n : ℝ) + 1) → 0 ≤ η → η ≤ K * r ^ 2 * logScale n →
      64 * η * (A * logScale n) * ((n : ℝ) + 2) ≤ 1 := by
  obtain ⟨N, hN⟩ := exists_voting_noise_threshold (K * A) (mul_nonneg hK hA)
  refine ⟨N, ?_⟩
  intro n hn r η hr hrange hη hηupper
  obtain ⟨hrhalf, hrL, hsmall⟩ := hN n hn r hr hrange
  have hL := logScale_one_le n
  have hL0 : 0 ≤ logScale n := by linarith
  have hC : 1 ≤ rangeFacetConstant := by
    unfold rangeFacetConstant
    have hh : 0 ≤ 512 * (Real.exp 1) ^ 3 := by positivity
    linarith
  have hrprod : r * ((n : ℝ) + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp hrange
  have hrm : r * ((n : ℝ) + 2) ≤ 2 := by nlinarith
  have hrm2 : r ^ 2 * ((n : ℝ) + 2) ≤ 2 * r := by
    have hh := mul_le_mul_of_nonneg_left hrm hr.le
    nlinarith
  have hL23 : (logScale n) ^ 2 ≤ (logScale n) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (logScale n)) (sub_nonneg.mpr hL)]
  calc
    _ ≤ 64 * (K * r ^ 2 * logScale n) * (A * logScale n) * ((n : ℝ) + 2) := by gcongr
    _ = (64 * K * A * (logScale n) ^ 2) * (r ^ 2 * ((n : ℝ) + 2)) := by ring
    _ ≤ (64 * K * A * (logScale n) ^ 2) * (2 * r) :=
      mul_le_mul_of_nonneg_left hrm2 (by positivity)
    _ = (128 * K * A * r) * (logScale n) ^ 2 := by ring
    _ ≤ (128 * K * A * r) * (logScale n) ^ 3 :=
      mul_le_mul_of_nonneg_left hL23 (by positivity)
    _ ≤ 2560 * rangeFacetConstant * (K * A) * r * (logScale n) ^ 3 := by
      have hh := mul_le_mul_of_nonneg_right (show (128 : ℝ) ≤ 2560 * rangeFacetConstant by linarith)
        (by positivity : 0 ≤ K * A * r * (logScale n) ^ 3)
      nlinarith
    _ ≤ 1 := hsmall

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def dampingEnvelope (n : ℕ) (q : ℝ) (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ)
    (x : E) : ℝ :=
  2 * Real.exp 1 * Real.exp ((affineMaxAbs (doubledRows B) (doubledMeans a) x) ^ 2 / (8 * q))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem dampingEnvelope_eq_scalar (n : ℕ) (q : ℝ)
    (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ) (x : E) :
    dampingEnvelope n q B a x = 2 * Real.exp 1 * Real.exp
      ((maxScore (fun p : Fin (n + 2) × Bool =>
        |doubledScore (fun i => a i + inner ℝ (B i) x) p|)) ^ 2 / (8 * q)) := by
  unfold dampingEnvelope affineMaxAbs
  congr 4
  congr 1
  funext p
  congr 1
  dsimp [doubledRows, doubledMeans, doubledScore]
  ring

theorem measurable_dampingEnvelope (n : ℕ) (q : ℝ)
    (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ) : Measurable (dampingEnvelope n q B a) := by
  unfold dampingEnvelope
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem dampingEnvelope_nonneg (n : ℕ) (q : ℝ)
    (B : Fin (n + 2) → E) (a : Fin (n + 2) → ℝ) (x : E) : 0 ≤ dampingEnvelope n q B a x := by
  unfold dampingEnvelope
  positivity

theorem dampingEnvelope_memLp (n : ℕ) (q : ℝ) (hq : 0 < q)
    (B : Fin (n + 2) → E) (hv : ∀ i, ‖B i‖ ≤ 1) (a : Fin (n + 2) → ℝ) :
    MemLp (dampingEnvelope n q B a) (ENNReal.ofReal q) (stdGaussian E) :=
  (max_square_exp_q_memLp (doubledRows B) (fun p => hv p.1) (doubledMeans a) q hq).const_mul _

theorem dampingEnvelope_norm_le (n : ℕ) (D q : ℝ) (hD : 0 ≤ D) (hq : 2 * logScale n ≤ q)
    (B : Fin (n + 2) → E) (hv : ∀ i, ‖B i‖ ≤ 1)
    (a : Fin (n + 2) → ℝ) (ha : ∀ i, (a i) ^ 2 ≤ D * logScale n) :
    eLpNorm (dampingEnvelope n q B a) (ENNReal.ofReal q) (stdGaussian E) ≤
      ENNReal.ofReal (2 * Real.exp 1) * ENNReal.ofReal (Real.exp (1 + (2 * D + 2) / 4)) := by
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
  unfold dampingEnvelope
  change eLpNorm ((2 * Real.exp 1) • (fun x : E => Real.exp
    ((affineMaxAbs (doubledRows B) (doubledMeans a) x) ^ 2 / (8 * q)))) _ _ ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos (by positivity : 0 < 2 * Real.exp 1)]
  gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem damping_tube_control (n : ℕ) (η q : ℝ) (hη : 0 ≤ η) (hq : 1 ≤ q)
    (hsmall : 64 * η * q * ((n : ℝ) + 2) ≤ 1)
    (B : Fin (n + 2) → E) (a b : Fin (n + 2) → ℝ) (hb : ∀ i, |b i| ≤ 1) (x : E) :
    ContinuousOn (fun t : ℝ => inverseKappa η (fun i => a i + inner ℝ (B i) x + t * b i)) (Icc 0 1) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      inverseKappa η (fun i => a i + inner ℝ (B i) x + t * b i) ≤ dampingEnvelope n q B a x ∧
      |deriv (fun s : ℝ => inverseKappa η (fun i => a i + inner ℝ (B i) x + s * b i)) t| ≤
        dampingEnvelope n q B a x ∧
      |inverseKappa η (fun i => a i + inner ℝ (B i) x + t * b i) -
        inverseKappa η (fun i => a i + inner ℝ (B i) x)| ≤ dampingEnvelope n q B a x * t := by
  let u := fun i => a i + inner ℝ (B i) x
  have hs : 64 * η * q * (Fintype.card (Fin (n + 2)) : ℝ) ≤ 1 := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using hsmall
  have hpath (t : ℝ) := hasDerivAt_inverseKappa η u b t
  have hcontrol (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := scalar_damping_control η q hη hq hs u b hb t ht
  constructor
  · intro t ht
    exact (hpath t).continuousAt.continuousWithinAt
  · intro t ht
    rw [(hpath t).deriv, dampingEnvelope_eq_scalar]
    refine ⟨(hcontrol t ht).1, (hcontrol t ht).2, ?_⟩
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := 1) (fun s _ => (hpath s).hasDerivWithinAt)
      (fun s hs => by simpa only [Real.norm_eq_abs] using (hcontrol s ⟨hs.1, hs.2.le⟩).2) t ht
    simpa only [zero_mul, add_zero, sub_zero, Real.norm_eq_abs] using hh

end Euclidean

/-- The threshold is formally chosen before the ambient dimension.  One
envelope works for every admissible noise and damping coefficient. -/
theorem exists_dimension_uniform_damping_tube (A K : ℝ) (hA : 2 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B : Fin (n + 2) → FSC.Coord d), (∀ i, ‖B i‖ ≤ 1) →
      ∀ (a : Fin (n + 2) → ℝ) (D : ℝ), 0 ≤ D →
      (∀ i, (a i) ^ 2 ≤ D * logScale n) →
      ∃ W : FSC.Coord d → ℝ, Measurable W ∧ (∀ x, 0 ≤ W x) ∧
        MemLp W (ENNReal.ofReal (A * logScale n)) (stdGaussian (FSC.Coord d)) ∧
        eLpNorm W (ENNReal.ofReal (A * logScale n)) (stdGaussian (FSC.Coord d)) ≤
          ENNReal.ofReal (2 * Real.exp 1) * ENNReal.ofReal (Real.exp (1 + (2 * D + 2) / 4)) ∧
        ∀ r η : ℝ, 0 < r → r ≤ 1 / ((n : ℝ) + 1) → 0 ≤ η → η ≤ K * r ^ 2 * logScale n →
          ∀ b : Fin (n + 2) → ℝ, (∀ i, |b i| ≤ 1) → ∀ x : FSC.Coord d,
          ContinuousOn (fun t : ℝ => inverseKappa η
            (fun i => a i + inner ℝ (B i) x + t * b i)) (Icc 0 1) ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            inverseKappa η (fun i => a i + inner ℝ (B i) x + t * b i) ≤ W x ∧
            |deriv (fun s : ℝ => inverseKappa η (fun i => a i + inner ℝ (B i) x + s * b i)) t| ≤ W x ∧
            |inverseKappa η (fun i => a i + inner ℝ (B i) x + t * b i) -
              inverseKappa η (fun i => a i + inner ℝ (B i) x)| ≤ W x * t := by
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨N, hN⟩ := exists_damping_noise_threshold A K hA0 hK
  refine ⟨N, ?_⟩
  intro n hn d B hv a D hD ha
  have hL := logScale_one_le n
  have hq : 2 * logScale n ≤ A * logScale n := by nlinarith
  have hq0 : 0 < A * logScale n := by nlinarith
  refine ⟨dampingEnvelope n (A * logScale n) B a, measurable_dampingEnvelope n _ B a,
    dampingEnvelope_nonneg n _ B a, dampingEnvelope_memLp n _ hq0 B hv a,
    dampingEnvelope_norm_le n D _ hD hq B hv a ha, ?_⟩
  intro r η hr hrange hη hηupper b hb x
  exact damping_tube_control n η (A * logScale n) hη (by nlinarith)
    (hN n hn r η hr hrange hη hηupper) B a b hb x

end NegativeVotingReciprocalDampingTube
