import GaussianOUResidualMoment

/-! Rare-cell smoothing before high-chaos projection preserves the inverse
label-count scale. The factorization uses the actual signed OU integral. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set
open scoped ENNReal BigOperators
namespace NegativeVotingRareLabelHighChaos
open NegativeVotingHypercontractivity NegativeVotingSmoothingComposition
  NegativeVotingProjection NegativeVotingChaosDecay NegativeVotingOUResidualMoment
  NegativeVotingAffine OAI.MinUncut.GaussianHermite
  SlowEquilibration.GaussianMaximalCorrelation
variable {n : ℕ}

theorem highModes_measurable (k : ℕ) (f : (Fin n→ℝ)→ℝ) (hf : Measurable f) :
    Measurable (highModes k f) := by
  unfold highModes removeModes projectModes
  exact hf.sub (Finset.measurable_sum _ (fun a _=>
    measurable_const.mul (continuous_psi a).measurable))

theorem gaussianAverage_measurable (ρ : ℝ) (f : (Fin n→ℝ)→ℝ)
    (hf : Measurable f) : Measurable (gaussianAverage ρ f) :=
  measurable_noise ρ (Real.sqrt (1-ρ^2)) hf

theorem gaussianAverage_coefficient (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (f : (Fin n→ℝ)→ℝ) (hfM : Measurable f) (hf : MemLp f 2 (γFin n)) (b : Fin n→ℕ) :
    coeff (gaussianAverage ρ f) b=ρ^(degree b)*coeff f b := by
  have hs : 0 ≤ 1-ρ^2 := by nlinarith [abs_le.mp hρ |>.1, abs_le.mp hρ |>.2]
  exact noise_coefficient_L2 ρ (Real.sqrt (1-ρ^2))
    (by rw [Real.sq_sqrt hs];ring) hfM hf b

theorem gaussianAverage_memLp_signed (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (f : (Fin n→ℝ)→ℝ) (hfM : Measurable f) (hf : MemLp f 2 (γFin n)) :
    MemLp (gaussianAverage ρ f) 2 (γFin n) := by
  have hs : 0 ≤ 1-ρ^2 := by nlinarith [abs_le.mp hρ |>.1, abs_le.mp hρ |>.2]
  exact memLp_noise_L2 ρ (Real.sqrt (1-ρ^2))
    (by rw [Real.sq_sqrt hs];ring) hfM hf

theorem ae_eq_of_coeff_eq (f g : (Fin n→ℝ)→ℝ)
    (hf : MemLp f 2 (γFin n)) (hg : MemLp g 2 (γFin n))
    (hc : ∀ b,coeff f b=coeff g b) : f=ᵐ[γFin n]g := by
  have hz (b : Fin n→ℕ) : coeff (fun x=>f x-g x) b=0 := by
    rw [coeff_sub hf hg,hc,sub_self]
  have hh := coefficient_energy_hasSum_of_memLp (hf.sub hg)
  change HasSum (fun b : Fin n→ℕ=>(coeff (fun x=>f x-g x) b)^2)
    (∫ x,(f x-g x)^2 ∂γFin n) at hh
  simp only [hz,zero_pow (by decide : 2≠0)] at hh
  have hi : (∫ x,(f x-g x)^2 ∂γFin n)=0 := hh.unique hasSum_zero
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x=>sq_nonneg (f x-g x))) (hf.sub hg).integrable_sq).mp hi
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

theorem coeff_highModes (k : ℕ) (f : (Fin n→ℝ)→ℝ)
    (hf : MemLp f 2 (γFin n)) (b : Fin n→ℕ) :
    coeff (highModes k f) b=if degree b<k then 0 else coeff f b := by
  simp only [highModes,coeff_removeModes _ _ hf,mem_lowerModes_iff]

/-- The inner smoothed high-chaos representative, at signed time. -/
def rareRepresentative (τ σ : ℝ) (k : ℕ) (f : (Fin n→ℝ)→ℝ) :=
  gaussianAverage (-σ) (highModes k (gaussianAverage τ f))

theorem rareRepresentative_factorization (τ σ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (f : (Fin n→ℝ)→ℝ) (hfM : Measurable f) (hf : MemLp f 2 (γFin n)) :
    gaussianAverage τ (rareRepresentative τ σ k f)=ᵐ[γFin n]
      gaussianAverage (-(τ^2*σ)) (highModes k f) := by
  have hτa : |τ| ≤ 1 := by rw [abs_of_pos hτ]; exact hτ1.le
  have hσa : |-σ| ≤ 1 := by rw [abs_neg,abs_of_pos hσ];exact hσ1.le
  have hpa : |-(τ^2*σ)| ≤ 1 := by
    rw [abs_neg,abs_of_nonneg (by positivity)]
    nlinarith [mul_pos (sq_pos_of_pos hτ) hσ]
  have hgm := gaussianAverage_measurable τ f hfM
  have hg := gaussianAverage_memLp_two hτ hτ1 f hf
  have hpm := highModes_measurable k _ hgm
  have hp := highModes_memLp k _ hg
  have hvm := gaussianAverage_measurable (-σ) _ hpm
  have hv := gaussianAverage_memLp_signed (-σ) hσa _ hpm hp
  apply ae_eq_of_coeff_eq _ _ (gaussianAverage_memLp_signed τ hτa _ hvm hv)
    (gaussianAverage_memLp_signed _ hpa _ (highModes_measurable k f hfM) (highModes_memLp k f hf))
  intro b
  rw [gaussianAverage_coefficient τ hτa _ hvm hv,
    gaussianAverage_coefficient (-σ) hσa _ hpm hp,
    gaussianAverage_coefficient _ hpa _ (highModes_measurable k f hfM) (highModes_memLp k f hf),
    coeff_highModes k _ hg,coeff_highModes k f hf,
    gaussianAverage_coefficient τ hτa f hfM hf]
  split_ifs
  · simp only [mul_zero]
  rw [←mul_assoc,←mul_assoc,←mul_pow,←mul_pow]
  congr 2
  ring

/-- The sharp rare-cell factor is retained after removal of all low degrees. -/
theorem rareRepresentative_eLpNorm_le (τ σ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (f : (Fin n→ℝ)→ℝ) (hf : MemLp f 2 (γFin n)) :
    eLpNorm (rareRepresentative τ σ k f) 2 (γFin n) ≤
      ENNReal.ofReal (σ^k)*eLpNorm f (ENNReal.ofReal (1+τ^2)) (γFin n) := by
  have hg := gaussianAverage_memLp_two hτ hτ1 f hf
  unfold rareRepresentative
  rw [gaussianAverage_neg_eLpNorm hσ hσ1 _ (highModes_memLp k _ hg)]
  exact (gaussianAverage_eLpNorm_decay σ hσ hσ1 _ (highModes_memLp k _ hg) k
    (highModes_coeff_vanish k _ hg)).trans
    (by
      gcongr
      exact (highModes_eLpNorm_le k _ hg).trans
        (memLp_gaussian_average_l2_hypercontractive τ hτ hτ1 f hf))

theorem rareRepresentative_indicator_eLpNorm_le (τ σ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (E : Set (Fin n→ℝ)) (hE : MeasurableSet E) :
    eLpNorm (rareRepresentative τ σ k (E.indicator (fun _=>1))) 2 (γFin n) ≤
      ENNReal.ofReal (σ^k)*(γFin n E)^(1/(1+τ^2)) := by
  have hf : MemLp (E.indicator (fun _ : Fin n→ℝ=>(1:ℝ))) 2 (γFin n) :=
    (memLp_const (1:ℝ)).indicator hE
  have hh := rareRepresentative_eLpNorm_le τ σ hτ hτ1 hσ hσ1 k _ hf
  rw [eLpNorm_indicator_const hE.nullMeasurableSet
    (show ENNReal.ofReal (1+τ^2)≠0 by positivity) ENNReal.ofReal_ne_top,
    enorm_one,one_mul,ENNReal.toReal_ofReal (by positivity)] at hh
  exact hh

/-- At smoothing scale τ² log m ≤ C, the rare-label norm remains O(1/m),
not O(1/sqrt m). This is a scalar consequence with the constant displayed. -/
theorem rare_mass_power_le (m τ C : ℝ) (hm : 1 ≤ m)
    (hscale : τ^2*Real.log m ≤ C) :
    (1/m)^(1/(1+τ^2):ℝ) ≤ Real.exp C/m := by
  have hm0 : 0 < m := by linarith
  have hp : 0 < 1+τ^2 := by positivity
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm
  have hc : 0 ≤ C := (mul_nonneg (sq_nonneg τ) hlog).trans hscale
  have he : (1/m)^(1/(1+τ^2):ℝ)=
      Real.exp (τ^2*Real.log m/(1+τ^2))/m := by
    rw [Real.rpow_def_of_pos (by positivity : 0 < 1/m)]
    rw [one_div,Real.log_inv]
    have hinv : m⁻¹=Real.exp (-Real.log m) := by
      rw [Real.exp_neg,Real.exp_log hm0]
    conv_rhs => rw [div_eq_mul_inv,hinv,←Real.exp_add]
    congr 1
    field_simp
    ring
  rw [he]
  apply div_le_div_of_nonneg_right _ hm0.le
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_nonneg hc (sq_nonneg τ)]

/-- The actual inner representative of a cell of mass 1/m has the full
σ^k/m gain, uniformly in the ambient dimension. -/
theorem rareRepresentative_uniform_cell_bound (τ σ m C : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hm : 1 ≤ m) (hscale : τ^2*Real.log m ≤ C)
    (k : ℕ) (E : Set (Fin n→ℝ)) (hE : MeasurableSet E)
    (hmass : γFin n E=ENNReal.ofReal (1/m)) :
    eLpNorm (rareRepresentative τ σ k (E.indicator (fun _=>1))) 2 (γFin n) ≤
      ENNReal.ofReal (σ^k*(Real.exp C/m)) := by
  have hh := rareRepresentative_indicator_eLpNorm_le τ σ hτ hτ1 hσ hσ1 k E hE
  rw [hmass,ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 1/m)
    (by positivity : 0 ≤ 1/(1+τ^2)),←ENNReal.ofReal_mul (by positivity)] at hh
  exact hh.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (rare_mass_power_le m τ C hm hscale) (by positivity)))

end NegativeVotingRareLabelHighChaos
