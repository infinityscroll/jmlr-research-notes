import GaussianRegularTieLaw

/-! Exact variance and curvature-coefficient bounds for the actual regular
Gaussian tie law. The two-point covariance comparison uses the monotonicity
of the Gaussian hazard and of x plus that hazard. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WeakSimplex
open scoped BigOperators ENNReal Classical Topology
namespace NegativeVotingRegularTieVariance
open NegativeVotingRegularTieLaw

/-- The iterated pair-difference formula, with integrability discharged from
actual L2 functions. No independent-copy law is postulated. -/
theorem integral_pair_difference {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X→ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫x,∫y,(f x-f y)*(g x-g y) ∂μ ∂μ)=2*covariance f g μ := by
  have hfI:=hf.integrable (by norm_num)
  have hgI:=hg.integrable (by norm_num)
  have hfg : Integrable (fun x=>f x*g x) μ:=hf.integrable_mul hg
  have hin (x:X) : (∫y,(f x-f y)*(g x-g y) ∂μ)=
      f x*g x+(∫y,f y*g y ∂μ)-f x*(∫y,g y ∂μ)-(∫y,f y ∂μ)*g x := by
    have he : (fun y=>(f x-f y)*(g x-g y))=
        fun y=>(f x*g x+f y*g y)-f x*g y-f y*g x:=by funext y;ring
    have h1 : Integrable (fun y=>f x*g x+f y*g y) μ:=(integrable_const _).add hfg
    have h2 : Integrable (fun y=>f x*g x+f y*g y-f x*g y) μ:=h1.sub (hgI.const_mul _)
    rw [he,integral_sub h2 (hfI.mul_const _),integral_sub h1 (hgI.const_mul _),
      integral_add (integrable_const _) hfg,integral_const_mul,integral_mul_const]
    simp [integral_const_mul,integral_mul_const]
  simp_rw [hin]
  have h1 : Integrable (fun x=>f x*g x+(∫y,f y*g y ∂μ)) μ:=hfg.add (integrable_const _)
  have h2 : Integrable (fun x=>f x*g x+(∫y,f y*g y ∂μ)-f x*(∫y,g y ∂μ)) μ:=
    h1.sub (hfI.mul_const _)
  rw [integral_sub h2 (hgI.const_mul _),integral_sub h1 (hfI.mul_const _),
    integral_add hfg (integrable_const _),integral_mul_const,integral_const_mul,covariance_eq_sub hf hg]
  simp only [integral_const,probReal_univ,one_smul,Pi.mul_apply]
  ring

theorem covariance_nonneg_of_pair_difference {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X→ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfg : ∀x y,0≤(f x-f y)*(g x-g y)) : 0≤covariance f g μ := by
  have hh : 0≤∫x,∫y,(f x-f y)*(g x-g y) ∂μ ∂μ:=
    integral_nonneg (fun x=>integral_nonneg (fun y=>hfg x y))
  rw [integral_pair_difference μ f g hf hg] at hh
  linarith

theorem covariance_nonpos_of_pair_difference {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X→ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfg : ∀x y,(f x-f y)*(g x-g y)≤0) : covariance f g μ≤0 := by
  have hh : (∫x,∫y,(f x-f y)*(g x-g y) ∂μ ∂μ)≤0:=
    integral_nonpos (fun x=>integral_nonpos (fun y=>hfg x y))
  rw [integral_pair_difference μ f g hf hg] at hh
  linarith

theorem normal_hazard_antitone : Antitone r := by
  apply StrictAnti.antitone
  apply strictAnti_of_deriv_neg
  intro x
  rw [(hasDerivAt_r x).deriv]
  nlinarith [mul_pos (r_pos x) (H_pos x)]

theorem H_monotone : Monotone H := by
  apply monotone_of_deriv_nonneg (fun x=>(hasDerivAt_H x).differentiableAt)
  intro x
  rw [(hasDerivAt_H x).deriv]
  exact (H_deriv_pos x).le

theorem tieHazardCovariance_nonpos (n : ℕ) : tieHazardCovariance n≤0 := by
  apply covariance_nonpos_of_pair_difference (tieLaw n) (fun x:ℝ=>x) r (tieLaw_memLp_id n) (tieLaw_memLp_r n)
  intro x y
  rcases le_total x y with hxy|hyx
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxy) (sub_nonneg.mpr (normal_hazard_antitone hxy))
  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hyx) (sub_nonpos.mpr (normal_hazard_antitone hyx))

theorem tieHazardCovariance_add_variance_nonneg (n : ℕ) :
    0≤tieVariance n+tieHazardCovariance n := by
  have hH : MemLp H 2 (tieLaw n):=by
    change MemLp ((fun x:ℝ=>x)+r) 2 (tieLaw n)
    exact (tieLaw_memLp_id n).add (tieLaw_memLp_r n)
  have hh:=covariance_nonneg_of_pair_difference (tieLaw n) (fun x:ℝ=>x) H (tieLaw_memLp_id n) hH (by
    intro x y
    rcases le_total x y with hxy|hyx
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxy) (sub_nonpos.mpr (H_monotone hxy))
    · exact mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr (H_monotone hyx)))
  have he : H=(fun x:ℝ=>x)+r:=rfl
  rw [he,covariance_add_right (tieLaw_memLp_id n) (tieLaw_memLp_id n) (tieLaw_memLp_r n),
    covariance_self (tieLaw_memLp_id n).aemeasurable] at hh
  exact hh

/-- The actual normalized tie variance lies between the common-mean scale
1/m and the two-Gaussian scale 1/2. Both bounds follow from actual IBP and
monotonicity, with no variance or convexity certificate assumed. -/
theorem tieVariance_bounds (n : ℕ) : 1/((n:ℝ)+2)≤tieVariance n ∧ tieVariance n≤1/2 := by
  have hi:=tieLaw_covariance_identity n
  have hu:=tieHazardCovariance_nonpos n
  have hl:=tieHazardCovariance_add_variance_nonneg n
  have hn:0≤(n:ℝ):=Nat.cast_nonneg _
  constructor
  · rw [div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)]
    nlinarith [mul_nonneg hn hl]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hn hu]

def eta (n : ℕ) : ℝ := ((n:ℝ)+1-((n:ℝ)+2)*tieVariance n)/(2*(n:ℝ))

/-- Exact regular coefficient range for m=n+2≥3. -/
theorem eta_bounds (n : ℕ) (hn : 0<n) : 1/4≤eta n ∧ eta n≤1/2 := by
  have hv:=tieVariance_bounds n
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  unfold eta
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have hh:=mul_le_mul_of_nonneg_left hv.2 (by positivity : (0:ℝ)≤(n:ℝ)+2)
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have hh:1≤((n:ℝ)+2)*tieVariance n:=by
      have hp:= (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)).mp hv.1
      nlinarith
    nlinarith

end NegativeVotingRegularTieVariance
