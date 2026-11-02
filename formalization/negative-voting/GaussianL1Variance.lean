import Mathlib
import FSC.Gaussian.StandardDensity
import SlowEquilibration.Upstream.OAI.Computability.MinUncut.GaussianHermite

/-!
Actual dimension-free Gaussian L1 variance control for bounded Lipschitz tests.
The rotation path argument retains the literal total gradient and derives its
almost-everywhere derivative interpretation from Rademacher's theorem.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace NegativeVotingGaussianL1

section Variance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem variance_le_bounded_pair_difference (f : Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (_hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B) :
    variance f μ ≤ B * ∫ z : Ω × Ω, |f z.1 - f z.2| ∂μ.prod μ := by
  have hf2 : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hd2 : MemLp (fun z : Ω × Ω => f z.1 - f z.2) 2 (μ.prod μ) :=
    (hf2.comp_fst μ).sub (hf2.comp_snd μ)
  have hd1 := hd2.integrable (by norm_num)
  have hmean : ∫ z : Ω × Ω, (f z.1 - f z.2) ∂μ.prod μ = 0 := by
    rw [integral_sub ((hf2.comp_fst μ).integrable (by norm_num))
      ((hf2.comp_snd μ).integrable (by norm_num))]
    simp [integral_fun_fst, integral_fun_snd]
  have hv : variance (fun z : Ω × Ω => f z.1 - f z.2) (μ.prod μ) =
      variance f μ + variance f μ := by
    simpa only [sub_eq_add_neg, Pi.neg_apply, variance_neg] using
      (variance_add_prod hf2 hf2.neg)
  rw [variance_eq_sub hd2, hmean, zero_pow (by norm_num : (2:ℕ) ≠ 0), sub_zero] at hv
  have hle : (∫ z : Ω × Ω, (f z.1 - f z.2)^2 ∂μ.prod μ) ≤
      (2 * B) * ∫ z : Ω × Ω, |f z.1 - f z.2| ∂μ.prod μ := by
    rw [← integral_const_mul]
    apply integral_mono (hd2.integrable_sq) (hd1.norm.const_mul (2*B))
    intro z
    have hh : |f z.1 - f z.2| ≤ 2*B :=
      (abs_sub (f z.1) (f z.2)).trans (by linarith [hbound z.1, hbound z.2])
    change (f z.1 - f z.2)^2 ≤ (2*B)*|f z.1 - f z.2|
    nlinarith [sq_abs (f z.1 - f z.2), abs_nonneg (f z.1 - f z.2)]
  simp only [Pi.pow_apply] at hv
  linarith
end Variance

variable {n : ℕ}
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def rotation (t : ℝ) (z : Space n × Space n) : Space n × Space n :=
  (Real.cos t • z.1 + Real.sin t • z.2,
   Real.sin t • z.1 - Real.cos t • z.2)

theorem rotation_preserves (t : ℝ) : MeasurePreserving (rotation (n:=n) t)
    ((stdGaussian (Space n)).prod (stdGaussian (Space n)))
    ((stdGaussian (Space n)).prod (stdGaussian (Space n))) := by
  let T : ((Fin n → ℝ) × (Fin n → ℝ)) → Space n × Space n :=
    fun z => (WithLp.toLp 2 z.1, WithLp.toLp 2 z.2)
  have hT0 : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → Space n)
      (OAI.MinUncut.GaussianHermite.γpi (Fin n)) (stdGaussian (Space n)) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hT : MeasurePreserving T _ _ := hT0.prod hT0
  have hh := (hT.comp (OAI.MinUncut.GaussianHermite.rotation_preserves
    (ι:=Fin n) (Real.cos t) (Real.sin t) (Real.cos_sq_add_sin_sq t))).map_eq
  have heq : T ∘ OAI.MinUncut.GaussianHermite.rotation (Real.cos t) (Real.sin t) =
      rotation t ∘ T := by
    funext z
    apply Prod.ext <;> ext i <;> rfl
  rw [heq, ← Measure.map_map (show Measurable (rotation (n:=n) t) from
    (show Continuous (rotation (n:=n) t) by unfold rotation; fun_prop).measurable) hT.measurable, hT.map_eq] at hh
  exact ⟨(by unfold rotation; fun_prop : Continuous (rotation (n:=n) t)).measurable, hh⟩

theorem rotation_measurable : Measurable (fun q : ℝ × (Space n × Space n) =>
    rotation q.1 q.2) := by
  apply Continuous.measurable
  unfold rotation; fun_prop

theorem rotation_first_hasDerivAt (z : Space n × Space n) (t : ℝ) :
    HasDerivAt (fun s => (rotation s z).1) (-(rotation t z).2) t := by
  convert ((Real.hasDerivAt_cos t).smul_const z.1).add
    ((Real.hasDerivAt_sin t).smul_const z.2) using 1
  · rfl
  · simp [rotation, neg_smul, sub_eq_add_neg, add_comm]

theorem rotation_first_absolutelyContinuous (z : Space n × Space n) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => (rotation t z).1) a b := by
  apply ContDiffOn.absolutelyContinuousOnInterval (E:=Space n)
  unfold rotation
  fun_prop

theorem measurable_gradient (f : Space n → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

theorem gradient_norm_le {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : Space n) : ‖gradient f x‖ ≤ L := by
  rw [gradient, (InnerProductSpace.toDual ℝ (Space n)).symm.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hf

theorem gaussian_ae_differentiable {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    ∀ᵐ x ∂stdGaussian (Space n), DifferentiableAt ℝ f x := by
  have hac : stdGaussian (Space n) ≪ (volume : Measure (Space n)) := by
    rw [FSC.stdGaussian_eq_volume_withDensity]
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le (hf.ae_differentiableAt (μ:=volume))


theorem gaussian_inner_abs_integral_le (v : Space n) :
    (∫ y, |inner ℝ v y| ∂stdGaussian (Space n)) ≤ ‖v‖ := by
  have hm : MemLp (fun y : Space n => inner ℝ v y) 2 (stdGaussian (Space n)) :=
    (innerSL ℝ v).comp_memLp' IsGaussian.memLp_two_id
  have hv := variance_dual_stdGaussian (innerSL ℝ v)
  have hm' : MemLp (innerSL ℝ v : Space n → ℝ) 2 (stdGaussian (Space n)) := hm
  rw [variance_eq_sub hm', integral_strongDual_stdGaussian, zero_pow (by norm_num : (2:ℕ)≠0),
    sub_zero, innerSL_apply_norm] at hv
  have ha := variance_nonneg (X:=fun y : Space n => |inner ℝ v y|)
    (μ:=stdGaussian (Space n))
  have hma : MemLp (fun y : Space n => |inner ℝ v y|) 2 (stdGaussian (Space n)) := by
    simpa only [Real.norm_eq_abs] using hm.norm
  rw [variance_eq_sub hma] at ha
  simp only [Pi.pow_apply, sq_abs, innerSL_apply_apply] at ha hv
  have hn : 0 ≤ ∫ y, |inner ℝ v y| ∂stdGaussian (Space n) := integral_nonneg fun _ => abs_nonneg _
  nlinarith [norm_nonneg v]

def rotationIntegrand (f : Space n → ℝ) (t : ℝ) (z : Space n × Space n) : ℝ :=
  |inner ℝ (gradient f (rotation t z).1) (rotation t z).2|

theorem rotationIntegrand_measurable (f : Space n → ℝ) :
    Measurable (fun q : ℝ × (Space n × Space n) => rotationIntegrand f q.1 q.2) := by
  exact ((measurable_gradient f).comp rotation_measurable.fst |>.inner
    rotation_measurable.snd).abs

theorem rotation_path_deriv_ae {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    ∀ᵐ z ∂(stdGaussian (Space n)).prod (stdGaussian (Space n)),
      ∀ᵐ t ∂volume,
      deriv (fun s => f (rotation s z).1) t =
        -inner ℝ (gradient f (rotation t z).1) (rotation t z).2 := by
  have hD : ∀ t, ∀ᵐ z ∂(stdGaussian (Space n)).prod (stdGaussian (Space n)),
      DifferentiableAt ℝ f (rotation t z).1 := by
    intro t
    exact (rotation_preserves t).quasiMeasurePreserving.ae
      (measurePreserving_fst.quasiMeasurePreserving.ae (gaussian_ae_differentiable hf))
  have hM : MeasurableSet {q : ℝ × (Space n × Space n) |
      DifferentiableAt ℝ f (rotation q.1 q.2).1} :=
    (measurableSet_of_differentiableAt ℝ f).preimage rotation_measurable.fst
  have hA := (Measure.ae_ae_comm hM).mp (ae_of_all volume hD)
  filter_upwards [hA] with z hz
  filter_upwards [hz] with t ht
  have hh := (ht.hasGradientAt.hasFDerivAt.comp_hasDerivAt t
    (rotation_first_hasDerivAt z t)).deriv
  simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply, inner_neg_right] using hh

theorem pair_difference_le_rotation_integral {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    ∀ᵐ z ∂(stdGaussian (Space n)).prod (stdGaussian (Space n)),
      |f z.2 - f z.1| ≤ ∫ t in (0:ℝ)..Real.pi/2, rotationIntegrand f t z := by
  filter_upwards [rotation_path_deriv_ae hf] with z hz
  have hAC := hf.comp_absolutelyContinuousOnInterval
    (rotation_first_absolutelyContinuous z 0 (Real.pi/2))
  have hFTC := hAC.integral_deriv_eq_sub
  simp only [Function.comp_def] at hFTC
  have he : (fun t => |deriv (fun s => f (rotation s z).1) t|) =ᵐ[volume]
      (fun t => rotationIntegrand f t z) := by
    filter_upwards [hz] with t ht
    rw [ht, abs_neg]
    rfl
  calc
    |f z.2 - f z.1| = |∫ t in (0:ℝ)..Real.pi/2, deriv (fun s => f (rotation s z).1) t| := by
      rw [hFTC]
      simp [rotation]
    _ ≤ ∫ t in (0:ℝ)..Real.pi/2, |deriv (fun s => f (rotation s z).1) t| :=
      by simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (a:=0) (b:=Real.pi/2)
          (f:=fun t => deriv (fun s => f (rotation s z).1) t) (by positivity))
    _ = _ := intervalIntegral.integral_congr_ae (he.mono fun _ ht _ => ht)


theorem gradient_integrable {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : Integrable (gradient f) (stdGaussian (Space n)) := by
  exact (MemLp.of_bound (p:=1) (measurable_gradient f).aestronglyMeasurable L
    (ae_of_all _ (gradient_norm_le hf))).integrable le_rfl

theorem rotation_second_norm_le (t : ℝ) (z : Space n × Space n) :
    ‖(rotation t z).2‖ ≤ ‖z.1‖ + ‖z.2‖ := by
  change ‖Real.sin t • z.1 - Real.cos t • z.2‖ ≤ _
  calc
    _ ≤ ‖Real.sin t • z.1‖ + ‖Real.cos t • z.2‖ := norm_sub_le _ _
    _ = |Real.sin t| * ‖z.1‖ + |Real.cos t| * ‖z.2‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ 1*‖z.1‖+1*‖z.2‖ := add_le_add
      (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (norm_nonneg _))
    _ = _ := by ring

theorem rotationIntegrand_bound {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (t : ℝ) (z : Space n × Space n) :
    ‖rotationIntegrand f t z‖ ≤ L*(‖z.1‖+‖z.2‖) := by
  simp only [rotationIntegrand, Real.norm_eq_abs, abs_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (gradient_norm_le hf _)
    (rotation_second_norm_le t z) (norm_nonneg _) L.coe_nonneg)

theorem independent_gradient_pair_integrable {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    Integrable (fun z : Space n × Space n => |inner ℝ (gradient f z.1) z.2|)
      ((stdGaussian (Space n)).prod (stdGaussian (Space n))) := by
  have hi : Integrable (fun z : Space n × Space n => L*‖z.2‖)
      ((stdGaussian (Space n)).prod (stdGaussian (Space n))) :=
    (IsGaussian.integrable_id.norm.comp_snd (stdGaussian (Space n))).const_mul L
  apply hi.mono' (((measurable_gradient f).comp measurable_fst).inner measurable_snd).abs.aestronglyMeasurable
  filter_upwards [] with z
  simp only [Real.norm_eq_abs, abs_abs]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (gradient_norm_le hf _) (norm_nonneg _))

theorem independent_gradient_pair_integral_le {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    (∫ z : Space n × Space n, |inner ℝ (gradient f z.1) z.2|
      ∂(stdGaussian (Space n)).prod (stdGaussian (Space n))) ≤
    ∫ x, ‖gradient f x‖ ∂stdGaussian (Space n) := by
  have hi := independent_gradient_pair_integrable hf
  rw [integral_prod _ hi]
  exact integral_mono hi.integral_prod_left (gradient_integrable hf).norm
    (fun x => gaussian_inner_abs_integral_le (gradient f x))

theorem rotationIntegrand_integral_eq (f : Space n → ℝ) (t : ℝ) :
    (∫ z : Space n × Space n, rotationIntegrand f t z
      ∂(stdGaussian (Space n)).prod (stdGaussian (Space n))) =
    ∫ z : Space n × Space n, |inner ℝ (gradient f z.1) z.2|
      ∂(stdGaussian (Space n)).prod (stdGaussian (Space n)) := by
  have hm : Measurable (fun z : Space n × Space n => |inner ℝ (gradient f z.1) z.2|) :=
    (((measurable_gradient f).comp measurable_fst).inner measurable_snd).abs
  have hh := integral_map (μ:=(stdGaussian (Space n)).prod (stdGaussian (Space n)))
    (rotation_preserves (n:=n) t).measurable.aemeasurable hm.aestronglyMeasurable
  rw [(rotation_preserves t).map_eq] at hh
  exact hh.symm

theorem rotationIntegrand_integral_le {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (t : ℝ) :
    (∫ z : Space n × Space n, rotationIntegrand f t z
      ∂(stdGaussian (Space n)).prod (stdGaussian (Space n))) ≤
    ∫ x, ‖gradient f x‖ ∂stdGaussian (Space n) := by
  rw [rotationIntegrand_integral_eq]
  exact independent_gradient_pair_integral_le hf

theorem rotationIntegrand_joint_integrable {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (a b : ℝ) :
    Integrable (fun q : ℝ × (Space n × Space n) => rotationIntegrand f q.1 q.2)
      ((volume.restrict (Ioc a b)).prod
        ((stdGaussian (Space n)).prod (stdGaussian (Space n)))) := by
  have hi0 : Integrable (fun z : Space n × Space n => L*(‖z.1‖+‖z.2‖))
      ((stdGaussian (Space n)).prod (stdGaussian (Space n))) :=
    ((IsGaussian.integrable_id.norm.comp_fst (stdGaussian (Space n))).add
      (IsGaussian.integrable_id.norm.comp_snd (stdGaussian (Space n)))).const_mul L
  exact (hi0.comp_snd (volume.restrict (Ioc a b))).mono'
    (rotationIntegrand_measurable f).aestronglyMeasurable
    (ae_of_all _ fun q => rotationIntegrand_bound hf q.1 q.2)

theorem gaussian_pair_difference_le_gradient {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    (∫ z : Space n × Space n, |f z.1 - f z.2|
      ∂(stdGaussian (Space n)).prod (stdGaussian (Space n))) ≤
    (Real.pi/2) * ∫ x, ‖gradient f x‖ ∂stdGaussian (Space n) := by
  have hab : (0:ℝ) ≤ Real.pi/2 := by positivity
  have hi := rotationIntegrand_joint_integrable hf 0 (Real.pi/2)
  have hpath := pair_difference_le_rotation_integral hf
  simp_rw [intervalIntegral.integral_of_le hab] at hpath
  have hle := integral_mono_of_nonneg
    (ae_of_all ((stdGaussian (Space n)).prod (stdGaussian (Space n)))
      (fun z => abs_nonneg (f z.2-f z.1))) hi.integral_prod_right hpath
  have hswap := integral_integral_swap (f:=fun t z => rotationIntegrand f t z) hi
  have hinner := integral_mono hi.integral_prod_left
    (integrable_const (∫ x, ‖gradient f x‖ ∂stdGaussian (Space n)))
    (fun t => rotationIntegrand_integral_le hf t)
  rw [hswap] at hinner
  have hfinal := hle.trans hinner
  simpa only [abs_sub_comm, integral_const, Measure.restrict_apply_univ,
    measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hab,
    smul_eq_mul] using hfinal

theorem gaussian_bounded_lipschitz_variance {f : Space n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B) :
    variance f (stdGaussian (Space n)) ≤
      (Real.pi/2)*B*(∫ x, ‖gradient f x‖ ∂stdGaussian (Space n)) := by
  calc
    _ ≤ B*(∫ z : Space n × Space n, |f z.1 - f z.2|
        ∂(stdGaussian (Space n)).prod (stdGaussian (Space n))) :=
      variance_le_bounded_pair_difference f hf.continuous.measurable B hB hbound
    _ ≤ B*((Real.pi/2)*(∫ x, ‖gradient f x‖ ∂stdGaussian (Space n))) :=
      mul_le_mul_of_nonneg_left (gaussian_pair_difference_le_gradient hf) hB
    _ = _ := by ring

end NegativeVotingGaussianL1
