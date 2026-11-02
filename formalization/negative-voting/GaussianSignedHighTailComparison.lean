import GaussianPathSmoothedComparison

/-! Actual signed high-mode quadratic forms: polarization and a smoothed
self-error estimate. This is an infinite-mode identity; no truncation is used. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped BigOperators ENNReal RealInnerProductSpace Classical
namespace NegativeVotingSignedHighTailComparison
open NegativeVotingPathSmoothedComparison NegativeVotingProjection
  NegativeVotingRareLabelHighChaos NegativeVotingOUResidualMoment
  NegativeVotingHypercontractivity OAI.MinUncut.GaussianHermite
  NegativeVotingModern SlowEquilibration.GaussianMaximalCorrelation
variable {d : ℕ}

def energyPairing (ρ : ℝ) (k : ℕ) (f : (Fin d→ℝ)→ℝ) : ℝ :=
  ∫ x,f x*gaussianAverage ρ (highModes k f) x ∂γFin d

/-- The signed quadratic remainder is bounded by a genuinely smoothed
Gaussian square integral, with the entire high-mode projection retained. -/
theorem energyPairing_neg_sq_abs_le (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (k : ℕ) (f : (Fin d→ℝ)→ℝ) (hfM : Measurable f) (hf : MemLp f 2 (γFin d)) :
    |energyPairing (-(s^2)) k f| ≤
      ∫ x,(gaussianAverage s (highModes k f) x)^2 ∂γFin d := by
  have hsa : |s| ≤ 1 := by rw [abs_of_pos hs];exact hs1.le
  have hsqa : |-(s^2)| ≤ 1 := by rw [abs_neg,abs_of_nonneg (sq_nonneg _)];nlinarith
  have hp := highModes_memLp k f hf
  have hpm := highModes_measurable k f hfM
  have hn := gaussianAverage_memLp_signed (-(s^2)) hsqa _ hpm hp
  have hpos := gaussianAverage_memLp_signed s hsa _ hpm hp
  have hpair := coefficient_pairing_hasSum f (gaussianAverage (-(s^2)) (highModes k f)) hf hn
  have hsum := NegativeVotingChaosDecay.coefficient_energy_hasSum_of_memLp hpos
  have hb (a : Fin d→ℕ) :
      ‖coeff f a*coeff (gaussianAverage (-(s^2)) (highModes k f)) a‖ ≤
        (coeff (gaussianAverage s (highModes k f)) a)^2 := by
    rw [gaussianAverage_coefficient _ hsqa _ hpm hp,
      gaussianAverage_coefficient s hsa _ hpm hp,coeff_highModes k f hf]
    by_cases ha : degree a < k
    · simp only [if_pos ha,mul_zero,norm_zero,zero_pow (by decide : 2≠0),le_refl]
    · simp only [if_neg ha,Real.norm_eq_abs,abs_mul,abs_pow,abs_neg,abs_of_nonneg (sq_nonneg s)]
      rw [mul_pow,←pow_mul,←pow_mul]
      rw [Nat.mul_comm 2 (degree a)]
      have heq : |coeff f a| * (s^(degree a*2) * |coeff f a|) =
          s^(degree a*2) * (coeff f a)^2 := by
        calc
          _ = s^(degree a*2) * |coeff f a|^2 := by ring
          _ = _ := by rw [sq_abs]
      exact heq.le
  have hh := tsum_of_norm_bounded hsum hb
  rw [hpair.tsum_eq] at hh
  exact hh

/-- Exact actual signed high-mode polarization, with the first-order term
expressed as the pairing against the fixed reference potential. -/
theorem energyPairing_difference (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (k : ℕ) (f g : (Fin d→ℝ)→ℝ)
    (hfM : Measurable f) (hgM : Measurable g)
    (hf : MemLp f 2 (γFin d)) (hg : MemLp g 2 (γFin d)) :
    energyPairing (-r) k f-energyPairing (-r) k g=
      2*(∫ x,(f x-g x)*gaussianAverage (-r) (highModes k g) x ∂γFin d)+
        energyPairing (-r) k (f-g) := by
  have hra : |-r| ≤ 1 := by rw [abs_neg,abs_of_pos hr];exact hr1.le
  let Tf := gaussianAverage (-r) (highModes k f)
  let Tg := gaussianAverage (-r) (highModes k g)
  have hTf := gaussianAverage_memLp_signed (-r) hra _ (highModes_measurable k f hfM) (highModes_memLp k f hf)
  have hTg := gaussianAverage_memLp_signed (-r) hra _ (highModes_measurable k g hgM) (highModes_memLp k g hg)
  have hlin := negative_highModes_difference_ae hr hr1 k f g hf hg
  have hcross := gaussianAverage_highModes_pairing_symm (-r) hra k g f hgM hfM hg hf
  have hid : energyPairing (-r) k (f-g)=
      (∫ x,f x*Tf x ∂γFin d)-(∫ x,f x*Tg x ∂γFin d)-
      (∫ x,g x*Tf x ∂γFin d)+(∫ x,g x*Tg x ∂γFin d) := by
    unfold energyPairing
    have hlinMul : (fun x => (f-g) x * gaussianAverage (-r) (highModes k (f-g)) x) =ᵐ[γFin d]
        (fun x => (f-g) x * (Tf-Tg) x) := by
      filter_upwards [hlin] with x hx
      exact congrArg (fun z => (f-g) x * z) hx
    rw [integral_congr_ae hlinMul]
    have he : (fun x=>(f-g) x*(Tf-Tg) x)=fun x=>f x*Tf x-f x*Tg x-g x*Tf x+g x*Tg x := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [he]
    have hff : Integrable (fun x => f x * Tf x) (γFin d) := hf.integrable_mul hTf
    have hfg : Integrable (fun x => f x * Tg x) (γFin d) := hf.integrable_mul hTg
    have hgf : Integrable (fun x => g x * Tf x) (γFin d) := hg.integrable_mul hTf
    have hgg : Integrable (fun x => g x * Tg x) (γFin d) := hg.integrable_mul hTg
    have hiadd := integral_add ((hff.sub hfg).sub hgf) hgg
    have hisub := integral_sub (hff.sub hfg) hgf
    have hisub' := integral_sub hff hfg
    dsimp only [Pi.sub_apply] at hiadd hisub
    rw [hiadd,hisub,hisub']
  have hsym : (∫ x,g x*Tf x ∂γFin d)=∫ x,f x*Tg x ∂γFin d := by
    simpa only [mul_comm] using hcross.symm
  have hc : (∫ x,(f x-g x)*Tg x ∂γFin d)=
      (∫ x,f x*Tg x ∂γFin d)-(∫ x,g x*Tg x ∂γFin d) := by
    simp only [sub_mul]
    exact integral_sub (hf.integrable_mul hTg) (hg.integrable_mul hTg)
  change energyPairing (-r) k f-energyPairing (-r) k g=2*(∫ x,(f x-g x)*Tg x ∂γFin d)+_
  rw [hid,hsym,hc]
  unfold energyPairing
  dsimp only [Tf,Tg]
  ring

end NegativeVotingSignedHighTailComparison
