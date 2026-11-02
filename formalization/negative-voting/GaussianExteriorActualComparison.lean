import GaussianSignedHighTailComparison

/-!
Actual infinite signed high-tail comparison for rare fractional coordinates.
All smoothing bounds below are derived from literal Gaussian L1 masses and
pointwise bounds; no desired tail or smoothed-norm estimate is a premise.
The exterior second-energy certificate and the geometric conversion to J are
separate obligations.
-/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped BigOperators ENNReal Classical
namespace NegativeVotingExteriorActualComparison
open NegativeVotingHypercontractivity NegativeVotingRareLabelHighChaos
  NegativeVotingProjection NegativeVotingSmoothingComposition
  NegativeVotingPathSmoothedComparison NegativeVotingSignedHighTailComparison
  NegativeVotingNormalTrace NegativeVotingNormalDerivatives
  NegativeVotingOUResidualMoment
  OAI.MinUncut.GaussianHermite
variable {d : ℕ}

def absoluteMass (f : (Fin d → ℝ) → ℝ) : ℝ := ∫ x, |f x| ∂γFin d

theorem absoluteMass_nonneg (f : (Fin d → ℝ) → ℝ) : 0 ≤ absoluteMass f :=
  integral_nonneg fun _ => abs_nonneg _

/-- For a bounded fractional coordinate, its genuine Lp norm is controlled
by its genuine L1 mass. Signed fractional differences are covered as well. -/
theorem eLpNorm_le_absoluteMass_rpow (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (f : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 (γFin d))
    (hb : ∀ᵐ x ∂γFin d, |f x| ≤ 1) :
    eLpNorm f (ENNReal.ofReal p) (γFin d) ≤
      ENNReal.ofReal ((absoluteMass f)^(1/p : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hfp := hf.mono_exponent (show ENNReal.ofReal p ≤ 2 by
    simpa using ENNReal.ofReal_le_ofReal hp2)
  have hi : Integrable (fun x => |f x|^p) (γFin d) := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
      hfp.integrable_norm_rpow'
  have hia : Integrable (fun x => |f x|) (γFin d) := by
    simpa only [Real.norm_eq_abs] using (hf.integrable (by norm_num)).norm
  have hh : (∫ x, |f x|^p ∂γFin d) ≤ absoluteMass f := by
    apply integral_mono_ae hi hia
    filter_upwards [hb] with x hx
    exact Real.rpow_le_self_of_le_one (abs_nonneg _) hx hp
  rw [hfp.eLpNorm_eq_integral_rpow_norm (by positivity) ENNReal.ofReal_ne_top]
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le]
  apply ENNReal.ofReal_le_ofReal
  simpa only [one_div] using
    (Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) hh
      (by positivity : 0 ≤ 1/p))

theorem gaussianAverage_pairing_symm (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (f g : (Fin d → ℝ) → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 (γFin d)) (hg : MemLp g 2 (γFin d)) :
    (∫ x, f x * gaussianAverage ρ g x ∂γFin d) =
      ∫ x, gaussianAverage ρ f x * g x ∂γFin d := by
  have hF := gaussianAverage_memLp_signed ρ hρ f hfm hf
  have hG := gaussianAverage_memLp_signed ρ hρ g hgm hg
  have h1 := coefficient_pairing_hasSum f (gaussianAverage ρ g) hf hG
  have h2 := coefficient_pairing_hasSum (gaussianAverage ρ f) g hF hg
  apply h1.unique
  convert h2 using 1
  ext b
  rw [gaussianAverage_coefficient ρ hρ g hgm hg,
    gaussianAverage_coefficient ρ hρ f hfm hf]
  ring

/-- The actual signed pairing factors through rare smoothing on both sides.
This bound retains every Hermite degree at least k. -/
theorem signed_pairing_abs_le_mass (τ σ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (f g : (Fin d → ℝ) → ℝ)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 (γFin d)) (hg : MemLp g 2 (γFin d))
    (hfb : ∀ᵐ x ∂γFin d, |f x| ≤ 1)
    (hgb : ∀ᵐ x ∂γFin d, |g x| ≤ 1) :
    |∫ x, f x * gaussianAverage (-(τ^2*σ)) (highModes k g) x ∂γFin d| ≤
      σ^k * (absoluteMass f)^(1/(1+τ^2) : ℝ) *
        (absoluteMass g)^(1/(1+τ^2) : ℝ) := by
  have hτa : |τ| ≤ 1 := by rw [abs_of_pos hτ]; exact hτ1.le
  have hσa : |-σ| ≤ 1 := by rw [abs_neg,abs_of_pos hσ]; exact hσ1.le
  have hp1 : 1 ≤ 1+τ^2 := by nlinarith
  have hp2 : 1+τ^2 ≤ 2 := by nlinarith
  let v := rareRepresentative τ σ k g
  have hvm : Measurable v := gaussianAverage_measurable (-σ) _
    (highModes_measurable k _ (gaussianAverage_measurable τ g hgm))
  have hv : MemLp v 2 (γFin d) := gaussianAverage_memLp_signed (-σ) hσa _
    (highModes_measurable k _ (gaussianAverage_measurable τ g hgm))
    (highModes_memLp k _ (gaussianAverage_memLp_two hτ hτ1 g hg))
  have hF := gaussianAverage_memLp_two hτ hτ1 f hf
  have he : (∫ x, f x * gaussianAverage (-(τ^2*σ)) (highModes k g) x ∂γFin d) =
      ∫ x, gaussianAverage τ f x * v x ∂γFin d := by
    rw [← gaussianAverage_pairing_symm τ hτa f v hfm hvm hf hv]
    apply integral_congr_ae
    filter_upwards [rareRepresentative_factorization τ σ hτ hτ1 hσ hσ1 k g hgm hg]
      with x hx
    exact congrArg (fun z => f x*z) hx.symm
  have hnF := (memLp_gaussian_average_l2_hypercontractive τ hτ hτ1 f hf).trans
    (eLpNorm_le_absoluteMass_rpow _ hp1 hp2 f hf hfb)
  have hnv := (rareRepresentative_eLpNorm_le τ σ hτ hτ1 hσ hσ1 k g hg).trans
    (mul_le_mul' le_rfl (eLpNorm_le_absoluteMass_rpow _ hp1 hp2 g hg hgb))
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ σ^k)] at hnv
  have hrF := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnF
  have hrv := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnv
  rw [eLpNorm_two_eq_sqrt_integral_sq hF,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (absoluteMass_nonneg f) _)] at hrF
  rw [eLpNorm_two_eq_sqrt_integral_sq hv,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg (by positivity)
      (Real.rpow_nonneg (absoluteMass_nonneg g) _))] at hrv
  rw [he]
  have hc := norm_integral_mul_le_l2 hF hv
  rw [Real.norm_eq_abs] at hc
  calc
    _ ≤ Real.sqrt (∫ x, (gaussianAverage τ f x)^2 ∂γFin d) *
        Real.sqrt (∫ x, (v x)^2 ∂γFin d) := hc
    _ ≤ (absoluteMass f)^(1/(1+τ^2) : ℝ) *
        (σ^k * (absoluteMass g)^(1/(1+τ^2) : ℝ)) :=
      mul_le_mul hrF hrv (Real.sqrt_nonneg _)
        (Real.rpow_nonneg (absoluteMass_nonneg f) _)
    _ = _ := by ring

theorem mass_power_sq_le (x b τ : ℝ) (hx : 0 ≤ x) (hxb : x ≤ b)
    (_hb : 0 < b) (hτ : τ^2 ≤ 1) :
    (x^(1/(1+τ^2) : ℝ))^2 ≤ b^((1-τ^2)/(1+τ^2) : ℝ)*x := by
  have hp : 0 < 1+τ^2 := by positivity
  have he : (0:ℝ) ≤ (1-τ^2)/(1+τ^2) := div_nonneg (by linarith) hp.le
  by_cases hx0 : x=0
  · subst x
    simp only [Real.zero_rpow (by positivity : (1/(1+τ^2):ℝ)≠0),zero_pow
      (by decide : 2≠0),mul_zero,le_refl]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hid : (x^(1/(1+τ^2) : ℝ))^2 = x^((1-τ^2)/(1+τ^2) : ℝ)*x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    have heq : 1/(1+τ^2)*(2:ℝ)=(1-τ^2)/(1+τ^2)+1 := by
      field_simp
      ring
    rw [Nat.cast_ofNat,heq,Real.rpow_add hxpos,Real.rpow_one]
  rw [hid]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxb he) hx

/-- Finite-label comparison with literal mass and mismatch data. The
exponent loss is one common rare-mass factor, not a label-count factor. -/
theorem signed_tail_sum_abs_le (ι : Type*) [Fintype ι] (τ σ b : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1) (hb : 0 < b)
    (k : ℕ) (f g : ι → (Fin d → ℝ) → ℝ)
    (hfm : ∀ i, Measurable (f i)) (hgm : ∀ i, Measurable (g i))
    (hf : ∀ i, MemLp (f i) 2 (γFin d)) (hg : ∀ i, MemLp (g i) 2 (γFin d))
    (hdb : ∀ i, ∀ᵐ x ∂γFin d, |f i x-g i x| ≤ 1)
    (hgb : ∀ i, ∀ᵐ x ∂γFin d, |g i x| ≤ 1)
    (hdm : ∀ i, absoluteMass (f i-g i) ≤ b)
    (hgmass : ∀ i, absoluteMass (g i) ≤ b)
    (hgsum : ∑ i, absoluteMass (g i)=1) :
    |∑ i, (energyPairing (-(τ^2*σ)) k (f i)-energyPairing (-(τ^2*σ)) k (g i))| ≤
      σ^k*b^((1-τ^2)/(1+τ^2) : ℝ)*
        (2*Real.sqrt (∑ i, absoluteMass (f i-g i)) + ∑ i, absoluteMass (f i-g i)) := by
  let u := fun i => (absoluteMass (f i-g i))^(1/(1+τ^2) : ℝ)
  let v := fun i => (absoluteMass (g i))^(1/(1+τ^2) : ℝ)
  let B := b^((1-τ^2)/(1+τ^2) : ℝ)
  let E := ∑ i, absoluteMass (f i-g i)
  have hB : 0 ≤ B := Real.rpow_nonneg hb.le _
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ => absoluteMass_nonneg _
  have hτsq : τ^2 ≤ 1 := by nlinarith
  have hr : 0 < τ^2*σ := by positivity
  have hr1 : τ^2*σ < 1 := by nlinarith [mul_pos (sq_pos_of_pos hτ) hσ]
  have hpoint (i : ι) :
      |energyPairing (-(τ^2*σ)) k (f i)-energyPairing (-(τ^2*σ)) k (g i)| ≤
        σ^k*(2*u i*v i+(u i)^2) := by
    rw [energyPairing_difference (τ^2*σ) hr hr1 k (f i) (g i) (hfm i) (hgm i) (hf i) (hg i)]
    have hc := signed_pairing_abs_le_mass τ σ hτ hτ1 hσ hσ1 k (f i-g i) (g i)
      ((hfm i).sub (hgm i)) (hgm i) ((hf i).sub (hg i)) (hg i) (hdb i) (hgb i)
    have hs := signed_pairing_abs_le_mass τ σ hτ hτ1 hσ hσ1 k (f i-g i) (f i-g i)
      ((hfm i).sub (hgm i)) ((hfm i).sub (hgm i)) ((hf i).sub (hg i)) ((hf i).sub (hg i))
      (hdb i) (hdb i)
    change |energyPairing (-(τ^2*σ)) k (f i-g i)| ≤ σ^k*u i*u i at hs
    have ha := abs_add_le (2*(∫ x, (f i x-g i x)*
      gaussianAverage (-(τ^2*σ)) (highModes k (g i)) x ∂γFin d))
      (energyPairing (-(τ^2*σ)) k (f i-g i))
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
    simp only [Pi.sub_apply] at hc
    refine ha.trans ?_
    calc
      _ ≤ 2*(σ^k*u i*v i)+σ^k*u i*u i :=
        add_le_add (mul_le_mul_of_nonneg_left hc (by norm_num)) hs
      _ = _ := by ring
  have hu : (∑ i, (u i)^2) ≤ B*E := by
    calc
      _ ≤ ∑ i, B*absoluteMass (f i-g i) := Finset.sum_le_sum fun i _ =>
        mass_power_sq_le _ b τ (absoluteMass_nonneg _) (hdm i) hb hτsq
      _ = _ := by rw [Finset.mul_sum]
  have hv : (∑ i, (v i)^2) ≤ B := by
    calc
      _ ≤ ∑ i, B*absoluteMass (g i) := Finset.sum_le_sum fun i _ =>
        mass_power_sq_le _ b τ (absoluteMass_nonneg _) (hgmass i) hb hτsq
      _ = _ := by rw [← Finset.mul_sum,hgsum,mul_one]
  have huv : (∑ i, u i*v i) ≤ B*Real.sqrt E := by
    calc
      _ ≤ Real.sqrt (∑ i, (u i)^2)*Real.sqrt (∑ i, (v i)^2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u v
      _ ≤ Real.sqrt (B*E)*Real.sqrt B :=
        mul_le_mul (Real.sqrt_le_sqrt hu) (Real.sqrt_le_sqrt hv)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Real.sqrt_mul hB]
        calc
          _ = (Real.sqrt B)^2*Real.sqrt E := by ring
          _ = _ := by rw [Real.sq_sqrt hB]
  calc
    _ ≤ ∑ i, |energyPairing (-(τ^2*σ)) k (f i)-energyPairing (-(τ^2*σ)) k (g i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, σ^k*(2*u i*v i+(u i)^2) := Finset.sum_le_sum fun i _ => hpoint i
    _ = σ^k*(2*(∑ i, u i*v i)+∑ i,(u i)^2) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ σ^k*(2*(B*Real.sqrt E)+B*E) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

theorem rare_factor_le (m τ C : ℝ) (hm : 3 ≤ m)
    (hscale : τ^2*Real.log m ≤ C) :
    (3/m)^((1-τ^2)/(1+τ^2) : ℝ) ≤ 3*Real.exp (2*C)/m := by
  have hm0 : 0 < m := by linarith
  have hp : 0 < 1+τ^2 := by positivity
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hc : 0 ≤ C := (mul_nonneg (sq_nonneg τ) hlog).trans hscale
  have hlogb : -Real.log (3/m) ≤ Real.log m := by
    rw [Real.log_div (by norm_num) hm0.ne']
    linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)]
  have hle : (-Real.log (3/m))*(2*τ^2)/(1+τ^2) ≤ 2*C := by
    apply (div_le_iff₀ hp).mpr
    have h1 := mul_le_mul_of_nonneg_right hlogb (show 0 ≤ 2*τ^2 by positivity)
    nlinarith [mul_nonneg hc (sq_nonneg τ)]
  have he : Real.log (3/m)*((1-τ^2)/(1+τ^2)) ≤ Real.log (3/m)+2*C := by
    have hid : Real.log (3/m)*((1-τ^2)/(1+τ^2)) =
        Real.log (3/m)+(-Real.log (3/m))*(2*τ^2)/(1+τ^2) := by
      field_simp
      ring
    rw [hid]
    linarith
  rw [Real.rpow_def_of_pos (by positivity : 0 < 3/m)]
  calc
    _ ≤ Real.exp (Real.log (3/m)+2*C) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add,Real.exp_log (by positivity : 0 < 3/m)]; ring

/-- The L1 total of a measurable simplex-valued rule is exactly one. -/
theorem absoluteMass_sum_eq_one (ι : Type*) [Fintype ι]
    (f : ι → (Fin d → ℝ) → ℝ) (hfm : ∀ i, Measurable (f i))
    (hf : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ f i x ∧ f i x ≤ 1) ∧ ∑ i, f i x=1) :
    (∀ i, MemLp (f i) 2 (γFin d)) ∧ ∑ i, absoluteMass (f i)=1 := by
  have hmem (i : ι) : MemLp (f i) 2 (γFin d) := by
    apply MemLp.of_bound (hfm i).aestronglyMeasurable 1
    filter_upwards [hf] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hx.1 i).1] using (hx.1 i).2
  refine ⟨hmem,?_⟩
  have hi (i : ι) : Integrable (fun x => |f i x|) (γFin d) := by
    simpa only [Real.norm_eq_abs] using ((hmem i).integrable (by norm_num)).norm
  unfold absoluteMass
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  have he : (fun x => ∑ i, |f i x|)=ᵐ[γFin d] fun _ => (1:ℝ) := by
    filter_upwards [hf] with x hx
    simpa only [abs_of_nonneg (hx.1 _).1] using hx.2
  rw [integral_congr_ae he]
  simp

/-- Actual rare fractional rules: infinite signed tail difference, with the
inverse label-count scale and square-root L1 mismatch. The only probabilistic
premises are measurability, simplex bounds, and actual coordinate masses. -/
theorem fractional_signed_tail_abs_le (ι : Type*) [Fintype ι] (m τ σ C : ℝ)
    (hm : 3 ≤ m) (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hscale : τ^2*Real.log m ≤ C) (k : ℕ)
    (f g : ι → (Fin d → ℝ) → ℝ)
    (hfm : ∀ i, Measurable (f i)) (hgm : ∀ i, Measurable (g i))
    (hf : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ f i x ∧ f i x ≤ 1) ∧ ∑ i, f i x=1)
    (hg : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ g i x ∧ g i x ≤ 1) ∧ ∑ i, g i x=1)
    (hfp : ∀ i, absoluteMass (f i) ≤ 3/(2*m))
    (hgp : ∀ i, absoluteMass (g i) ≤ 3/(2*m)) :
    |∑ i, (energyPairing (-(τ^2*σ)) k (f i)-energyPairing (-(τ^2*σ)) k (g i))| ≤
      12*Real.exp (2*C)*σ^k*Real.sqrt (∑ i, absoluteMass (f i-g i))/m := by
  have hm0 : 0 < m := by linarith
  obtain ⟨hF,hFsum⟩ := absoluteMass_sum_eq_one ι f hfm hf
  obtain ⟨hG,hGsum⟩ := absoluteMass_sum_eq_one ι g hgm hg
  have hdb (i : ι) : ∀ᵐ x ∂γFin d, |f i x-g i x| ≤ 1 := by
    filter_upwards [hf,hg] with x hx hy
    exact abs_le.mpr ⟨by linarith [(hx.1 i).1,(hy.1 i).2],
      by linarith [(hx.1 i).2,(hy.1 i).1]⟩
  have hgb (i : ι) : ∀ᵐ x ∂γFin d, |g i x| ≤ 1 := by
    filter_upwards [hg] with x hx
    rw [abs_of_nonneg (hx.1 i).1]
    exact (hx.1 i).2
  have hmass (i : ι) : absoluteMass (f i-g i) ≤ absoluteMass (f i)+absoluteMass (g i) := by
    have hfi : Integrable (fun x => |f i x|) (γFin d) := by
      simpa only [Real.norm_eq_abs] using ((hF i).integrable (by norm_num)).norm
    have hgi : Integrable (fun x => |g i x|) (γFin d) := by
      simpa only [Real.norm_eq_abs] using ((hG i).integrable (by norm_num)).norm
    have hdi : Integrable (fun x => |(f i-g i) x|) (γFin d) := by
      simpa only [Real.norm_eq_abs] using (((hF i).sub (hG i)).integrable (by norm_num)).norm
    unfold absoluteMass
    rw [← integral_add hfi hgi]
    exact integral_mono_ae hdi (hfi.add hgi) (Filter.Eventually.of_forall
      (fun x => abs_sub (f i x) (g i x)))
  have hdm (i : ι) : absoluteMass (f i-g i) ≤ 3/m := by
    calc
      _ ≤ absoluteMass (f i)+absoluteMass (g i) := hmass i
      _ ≤ 3/(2*m)+3/(2*m) := add_le_add (hfp i) (hgp i)
      _ = _ := by ring
  have hgmass (i : ι) : absoluteMass (g i) ≤ 3/m := by
    apply (hgp i).trans
    have hn : 0 ≤ 3/(2*m) := by positivity
    have he : 3/(2*m)+3/(2*m)=3/m := by ring
    linarith
  let E := ∑ i, absoluteMass (f i-g i)
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => absoluteMass_nonneg _
  have hE2 : E ≤ 2 := by
    calc
      _ ≤ ∑ i, (absoluteMass (f i)+absoluteMass (g i)) := Finset.sum_le_sum fun i _ => hmass i
      _ = 2 := by rw [Finset.sum_add_distrib,hFsum,hGsum]; norm_num
  have hEsqrt : 2*Real.sqrt E+E ≤ 4*Real.sqrt E := by
    have hs := Real.sq_sqrt hE
    have hn := Real.sqrt_nonneg E
    have hh : Real.sqrt E ≤ 2 := by nlinarith
    nlinarith
  have hh := signed_tail_sum_abs_le ι τ σ (3/m) hτ hτ1 hσ hσ1 (by positivity)
    k f g hfm hgm hF hG hdb hgb hdm hgmass hGsum
  calc
    _ ≤ σ^k*(3/m)^((1-τ^2)/(1+τ^2) : ℝ)*(2*Real.sqrt E+E) := hh
    _ ≤ σ^k*(3*Real.exp (2*C)/m)*(4*Real.sqrt E) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (rare_factor_le m τ C hm hscale) (by positivity))
        hEsqrt (by positivity) (by positivity)
    _ = _ := by ring

theorem absoluteMass_congr_ae {f g : (Fin d → ℝ) → ℝ} (hfg : f=ᵐ[γFin d]g) :
    absoluteMass f=absoluteMass g :=
  integral_congr_ae (hfg.fun_comp abs)

theorem highModes_congr_ae (k : ℕ) {f g : (Fin d → ℝ) → ℝ}
    (hfg : f=ᵐ[γFin d]g) : highModes k f=ᵐ[γFin d]highModes k g := by
  have hc (a : Fin d → ℕ) : coeff f a=coeff g a := by
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    exact congrArg (fun z => psi a x*z) hx
  filter_upwards [hfg] with x hx
  simp only [highModes,removeModes,projectModes,hc,hx]

theorem energyPairing_congr_ae (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (k : ℕ) {f g : (Fin d → ℝ) → ℝ} (hfg : f=ᵐ[γFin d]g) :
    energyPairing (-r) k f=energyPairing (-r) k g := by
  have hn := (gaussian_neg_measurePreserving d).quasiMeasurePreserving.ae
    (gaussianAverage_congr_ae r hr hr1 (highModes_congr_ae k hfg))
  unfold energyPairing
  simp only [gaussianAverage_neg]
  apply integral_congr_ae
  filter_upwards [hfg,hn] with x hx hnx
  rw [hx,hnx]

/-- The same actual endpoint for completed-Gaussian-measurable fractional
rules. Passing to Borel versions does not alter any mass or noise integral. -/
theorem ae_fractional_signed_tail_abs_le (ι : Type*) [Fintype ι] (m τ σ C : ℝ)
    (hm : 3 ≤ m) (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hscale : τ^2*Real.log m ≤ C) (k : ℕ)
    (f g : ι → (Fin d → ℝ) → ℝ)
    (hfm : ∀ i, AEMeasurable (f i) (γFin d))
    (hgm : ∀ i, AEMeasurable (g i) (γFin d))
    (hf : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ f i x ∧ f i x ≤ 1) ∧ ∑ i, f i x=1)
    (hg : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ g i x ∧ g i x ≤ 1) ∧ ∑ i, g i x=1)
    (hfp : ∀ i, absoluteMass (f i) ≤ 3/(2*m))
    (hgp : ∀ i, absoluteMass (g i) ≤ 3/(2*m)) :
    |∑ i, (energyPairing (-(τ^2*σ)) k (f i)-energyPairing (-(τ^2*σ)) k (g i))| ≤
      12*Real.exp (2*C)*σ^k*Real.sqrt (∑ i, absoluteMass (f i-g i))/m := by
  let f0 := fun i => (hfm i).mk (f i)
  let g0 := fun i => (hgm i).mk (g i)
  have hef (i : ι) : f i=ᵐ[γFin d]f0 i := (hfm i).ae_eq_mk
  have heg (i : ι) : g i=ᵐ[γFin d]g0 i := (hgm i).ae_eq_mk
  have hefAll : ∀ᵐ x ∂γFin d, ∀ i, f i x=f0 i x := ae_all_iff.mpr hef
  have hegAll : ∀ᵐ x ∂γFin d, ∀ i, g i x=g0 i x := ae_all_iff.mpr heg
  have hf0 : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ f0 i x ∧ f0 i x ≤ 1) ∧ ∑ i, f0 i x=1 := by
    filter_upwards [hf,hefAll] with x hx he
    simpa only [← he] using hx
  have hg0 : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ g0 i x ∧ g0 i x ≤ 1) ∧ ∑ i, g0 i x=1 := by
    filter_upwards [hg,hegAll] with x hx he
    simpa only [← he] using hx
  have hfp0 (i : ι) : absoluteMass (f0 i) ≤ 3/(2*m) := by
    rw [← absoluteMass_congr_ae (hef i)]
    exact hfp i
  have hgp0 (i : ι) : absoluteMass (g0 i) ≤ 3/(2*m) := by
    rw [← absoluteMass_congr_ae (heg i)]
    exact hgp i
  have hh := fractional_signed_tail_abs_le ι m τ σ C hm hτ hτ1 hσ hσ1 hscale k f0 g0
    (fun i => (hfm i).measurable_mk) (fun i => (hgm i).measurable_mk) hf0 hg0 hfp0 hgp0
  have hr : 0 < τ^2*σ := by positivity
  have hr1 : τ^2*σ < 1 := by nlinarith [mul_pos (sq_pos_of_pos hτ) hσ]
  have he1 (i : ι) := energyPairing_congr_ae (τ^2*σ) hr hr1 k (hef i)
  have he2 (i : ι) := energyPairing_congr_ae (τ^2*σ) hr hr1 k (heg i)
  have hem (i : ι) := absoluteMass_congr_ae ((hef i).sub (heg i))
  simpa only [← he1,← he2,← hem] using hh

/-- At the actual logarithmic smoothing scale, the entire degree-at-least-3
signed tail has the cubic r gain and only a square-root L1 mismatch loss. -/
theorem ae_fractional_cubic_tail_abs_le (ι : Type*) [Fintype ι] (m r : ℝ)
    (hm : 3 ≤ m) (hr : 0 < r) (hrL : 4*r*(1+Real.log m) < 1)
    (f g : ι → (Fin d → ℝ) → ℝ)
    (hfm : ∀ i, AEMeasurable (f i) (γFin d))
    (hgm : ∀ i, AEMeasurable (g i) (γFin d))
    (hf : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ f i x ∧ f i x ≤ 1) ∧ ∑ i, f i x=1)
    (hg : ∀ᵐ x ∂γFin d, (∀ i, 0 ≤ g i x ∧ g i x ≤ 1) ∧ ∑ i, g i x=1)
    (hfp : ∀ i, absoluteMass (f i) ≤ 3/(2*m))
    (hgp : ∀ i, absoluteMass (g i) ≤ 3/(2*m)) :
    |∑ i, (energyPairing (-r) 3 (f i)-energyPairing (-r) 3 (g i))| ≤
      768*Real.exp (1/2)*r^3*(1+Real.log m)^3*
        Real.sqrt (∑ i, absoluteMass (f i-g i))/m := by
  let L := 1+Real.log m
  let τ := Real.sqrt (1/(4*L))
  let σ := 4*r*L
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by linarith : 1 ≤ m)]
  have hL0 : 0 < L := by linarith
  have ht : 0 < τ := Real.sqrt_pos.mpr (by positivity)
  have htsq : τ^2=1/(4*L) := Real.sq_sqrt (by positivity)
  have ht1 : τ < 1 := by
    have : 1/(4*L) < 1 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
    nlinarith
  have hs : 0 < σ := by dsimp [σ]; positivity
  have hs1 : σ < 1 := hrL
  have hscale : τ^2*Real.log m ≤ 1/4 := by
    rw [htsq]
    have he : (1/(4*L))*Real.log m=Real.log m/(4*L) := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 4*L)).mpr
    dsimp [L]
    linarith
  have he : τ^2*σ=r := by rw [htsq]; dsimp [σ]; field_simp
  have hh := ae_fractional_signed_tail_abs_le ι m τ σ (1/4) hm ht ht1 hs hs1 hscale
    3 f g hfm hgm hf hg hfp hgp
  rw [he,show (2:ℝ)*(1/4)=1/2 by ring] at hh
  dsimp only [σ,L] at hh
  convert hh using 1
  ring

end NegativeVotingExteriorActualComparison
