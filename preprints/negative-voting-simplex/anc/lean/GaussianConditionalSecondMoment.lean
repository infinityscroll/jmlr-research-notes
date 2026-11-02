import GaussianChaosDecay
import GaussianSecondChaos

/-! Dimension-free conditional quadratic Gaussian moments from actual
hypercontractivity and the exact degree-two Hermite tensor identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open SlowEquilibration.GaussianMaximalCorrelation NegativeVotingModern
open NegativeVotingHypercontractivity NegativeVotingChaosDecay NegativeVotingNormalTrace GaussianFin
open scoped BigOperators ENNReal NNReal
namespace NegativeVotingConditionalSecondMoment

/-- The actual second-chaos energy survives Gaussian smoothing with factor τ⁴.
The total smoothed energy is actual squared L2 norm, not a spectral premise. -/
theorem quadratic_energy_le_smoothed {n : ℕ} (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : (Fin n→ℝ)→ℝ) (hf : Measurable f) (hf2 : MemLp f 2 (γFin n)) :
    τ^4*((1/2:ℝ)*∑ j,∑ k,(quadraticMoment f j k)^2) ≤
      ∫ x,(gaussianAverage τ f x)^2 ∂γFin n := by
  have hnonneg : 0 ≤ 1-τ^2 := by nlinarith
  have hmix : τ^2+(Real.sqrt (1-τ^2))^2=1 := by rw [Real.sq_sqrt hnonneg]; ring
  have hn := memLp_noise_L2 τ (Real.sqrt (1-τ^2)) hmix hf hf2
  have hS := coefficient_energy_hasSum_of_memLp hn
  have hle := Summable.tsum_le_tsum_of_inj
    (fun a : {a : Fin n→ℕ // degree a=2} => a.1) Subtype.coe_injective
    (fun a _ => sq_nonneg (coeff (noise τ (Real.sqrt (1-τ^2)) f) a)) (fun a => le_rfl)
    (hS.summable.subtype (fun a => degree a=2)) hS.summable
  rw [hS.tsum_eq] at hle
  have heq : (∑' a : {a : Fin n→ℕ // degree a=2},
      (coeff (noise τ (Real.sqrt (1-τ^2)) f) a.1)^2)=
      τ^4*chaosEnergy (fun x (_ : Unit) => f x) 2 := by
    calc
      _=∑' a : {a : Fin n→ℕ // degree a=2},τ^4*(coeff f a.1)^2 := by
        apply tsum_congr
        intro a
        rw [noise_coefficient_L2 τ (Real.sqrt (1-τ^2)) hmix hf hf2,a.property]
        ring
      _=τ^4*chaosEnergy (fun x (_ : Unit) => f x) 2 := by
        rw [tsum_mul_left]
        simp only [chaosEnergy,labelCoefficientEnergy,Fintype.sum_unique]
  rw [heq,chaosEnergy_two] at hle
  have hnEq : noise τ (Real.sqrt (1-τ^2)) f=gaussianAverage τ f := by
    funext x
    unfold noise gaussianAverage
    apply integral_congr_ae
    filter_upwards with y
    congr 1
  have hμ : γpi (Fin n)=γFin n := rfl
  rw [hnEq,hμ] at hle
  simpa only [Fintype.sum_unique] using hle

/-- The indicator Lp norm and concrete hypercontractivity give an exact
real-valued estimate for the actual smoothed Gaussian event. -/
theorem smoothed_indicator_norm_le {n : ℕ} (E : Set (Fin n→ℝ)) (hE : MeasurableSet E)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) :
    Real.sqrt (∫ x,(gaussianAverage τ (E.indicator (fun _ => (1:ℝ))) x)^2 ∂γFin n) ≤
      ((γFin n E).toReal)^(1/(1+τ^2)) := by
  let f := E.indicator (fun _ => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator hE
  have hf2 : MemLp f 2 (γFin n) := (memLp_const (1:ℝ)).indicator hE
  have hfp : MemLp f (ENNReal.ofReal (1+τ^2)) (γFin n) := (memLp_const (1:ℝ)).indicator hE
  have hmix : τ^2+(Real.sqrt (1-τ^2))^2=1 := by
    rw [Real.sq_sqrt (show 0 ≤ 1-τ^2 by nlinarith)]
    ring
  have hn : MemLp (gaussianAverage τ f) 2 (γFin n) := memLp_noise_L2 τ _ hmix hf hf2
  have hh := ENNReal.toReal_mono hfp.eLpNorm_ne_top
    (memLp_gaussian_average_l2_hypercontractive τ hτ hτ1 f hf2)
  rw [eLpNorm_two_eq_sqrt_integral_sq hn,ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hh
  have hp : ENNReal.ofReal (1+τ^2)≠0 := by positivity
  rw [show eLpNorm f (ENNReal.ofReal (1+τ^2)) (γFin n)=
      (γFin n E)^(1/(1+τ^2)) by
        rw [eLpNorm_indicator_const hE.nullMeasurableSet hp ENNReal.ofReal_ne_top]
        simp only [enorm_one,one_mul,ENNReal.toReal_ofReal (show 0 ≤ 1+τ^2 by positivity)],
    ←ENNReal.toReal_rpow] at hh
  exact hh

/-- Choose smoothing strictly below one even at event probability one. -/
theorem smoothing_parameters (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    let L := 1+Real.log (1/p)
    let τ := 1/Real.sqrt (2*L)
    1 ≤ L ∧ 0 < τ ∧ τ < 1 ∧ τ^2*L=1/2 ∧
      p^(1/(1+τ^2)) ≤ Real.exp 1*p := by
  dsimp only
  let L := 1+Real.log (1/p)
  let τ := 1/Real.sqrt (2*L)
  have hl : 0 ≤ Real.log (1/p) := Real.log_nonneg ((one_le_div hp).2 hp1)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs : 0 < Real.sqrt (2*L) := Real.sqrt_pos.2 (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2*L by positivity)
  have hs1 : 1 < Real.sqrt (2*L) := by nlinarith
  have ht : 0 < τ := by dsimp [τ]; positivity
  have ht1 : τ < 1 := (div_lt_one hs).2 hs1
  have hrel : τ^2*L=1/2 := by
    dsimp [τ]
    rw [div_pow,one_pow,hs2]
    field_simp
  refine ⟨hL,ht,ht1,hrel,?_⟩
  have hlog : Real.log (1/p) = -Real.log p := by rw [one_div,Real.log_inv]
  have hpow : Real.log p/(1+τ^2) ≤ Real.log p+1 := by
    apply (div_le_iff₀ (show 0 < 1+τ^2 by positivity)).2
    dsimp [L] at hrel
    rw [hlog] at hrel
    nlinarith [sq_nonneg τ]
  calc
    p^(1/(1+τ^2))=Real.exp (Real.log p/(1+τ^2)) := by rw [Real.rpow_def_of_pos hp]; congr 1; ring
    _≤Real.exp (Real.log p+1) := Real.exp_le_exp.mpr hpow
    _=Real.exp 1*p := by rw [Real.exp_add,Real.exp_log hp]; ring

/-- Exact literal tensor bound for every measurable Gaussian event of positive
mass, in every finite dimension; no convexity or regularity of its boundary. -/
theorem indicator_quadratic_frobenius_bound {n : ℕ}
    (E : Set (Fin n→ℝ)) (hE : MeasurableSet E) (hp : 0 < (γFin n E).toReal) :
    Real.sqrt (∑ j,∑ k,(quadraticMoment (E.indicator (fun _ => (1:ℝ))) j k)^2) ≤
      4*Real.exp 1*(γFin n E).toReal*(1+Real.log (1/(γFin n E).toReal)) := by
  let p := (γFin n E).toReal
  let L := 1+Real.log (1/p)
  let τ := 1/Real.sqrt (2*L)
  let f := E.indicator (fun _ => (1:ℝ))
  let V := ∑ j,∑ k,(quadraticMoment f j k)^2
  let J := ∫ x,(gaussianAverage τ f x)^2 ∂γFin n
  have hp1 : p ≤ 1 := measureReal_le_one
  obtain ⟨hL,ht,ht1,hrel,hpow⟩ := smoothing_parameters p hp hp1
  have hf : Measurable f := measurable_const.indicator hE
  have hf2 : MemLp f 2 (γFin n) := (memLp_const (1:ℝ)).indicator hE
  have henergy : τ^4*((1/2:ℝ)*V) ≤ J := quadratic_energy_le_smoothed τ ht ht1 f hf hf2
  have hnorm : Real.sqrt J ≤ Real.exp 1*p := (smoothed_indicator_norm_le E hE τ ht ht1).trans hpow
  have hJ : 0 ≤ J := integral_nonneg (fun x => sq_nonneg _)
  have hJbd : J ≤ (Real.exp 1*p)^2 := by
    have hh := mul_self_le_mul_self (Real.sqrt_nonneg J) hnorm
    nlinarith [Real.sq_sqrt hJ]
  have hscaled := mul_le_mul_of_nonneg_right henergy (show 0 ≤ 8*L^2 by positivity)
  have heq : τ^4*((1/2:ℝ)*V)*(8*L^2)=V := by
    calc
      _=4*(τ^2*L)^2*V := by ring
      _=V := by rw [hrel]; ring
  rw [heq] at hscaled
  have hV : V ≤ (4*Real.exp 1*p*L)^2 := by
    calc
      V ≤ (8*L^2)*J := by nlinarith [hscaled]
      _≤(8*L^2)*(Real.exp 1*p)^2 := mul_le_mul_of_nonneg_left hJbd (by positivity)
      _≤(4*Real.exp 1*p*L)^2 := by nlinarith [sq_nonneg (Real.exp 1*p*L)]
  change Real.sqrt V ≤ 4*Real.exp 1*p*L
  exact Real.sqrt_le_iff.mpr ⟨by positivity,hV⟩

/-- The actual conditional centered second-moment tensor, in product coordinates. -/
def conditionalQuadraticTensor {n : ℕ} (E : Set (Fin n→ℝ)) (j k : Fin n) : ℝ :=
  (∫ x in E,x j*x k-(if j=k then 1 else 0) ∂γFin n)/(γFin n E).toReal

theorem indicator_quadraticMoment_eq {n : ℕ} (E : Set (Fin n→ℝ))
    (hE : MeasurableSet E) (j k : Fin n) :
    quadraticMoment (E.indicator (fun _ => (1:ℝ))) j k=
      ∫ x in E,x j*x k-(if j=k then 1 else 0) ∂γFin n := by
  change (∫ x,(E.indicator (fun _ => (1:ℝ))) x*(x j*x k-(if j=k then 1 else 0)) ∂γFin n)=_
  rw [←integral_indicator hE]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈E <;> simp [hx]

/-- Dimension-free Frobenius bound for the literal conditional tensor. -/
theorem conditional_quadratic_frobenius_bound {n : ℕ}
    (E : Set (Fin n→ℝ)) (hE : MeasurableSet E) (hp : 0 < (γFin n E).toReal) :
    Real.sqrt (∑ j,∑ k,(conditionalQuadraticTensor E j k)^2) ≤
      4*Real.exp 1*(1+Real.log (1/(γFin n E).toReal)) := by
  let p := (γFin n E).toReal
  let V := ∑ j,∑ k,(quadraticMoment (E.indicator (fun _ => (1:ℝ))) j k)^2
  have he (j k : Fin n) : conditionalQuadraticTensor E j k=
      quadraticMoment (E.indicator (fun _ => (1:ℝ))) j k/p := by
    rw [indicator_quadraticMoment_eq E hE]
    rfl
  have hsum : (∑ j,∑ k,(conditionalQuadraticTensor E j k)^2)=V/p^2 := by
    simp_rw [he,div_pow]
    simp only [←Finset.sum_div,V]
  rw [hsum,Real.sqrt_div (show 0 ≤ V from Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))),Real.sqrt_sq hp.le]
  apply (div_le_iff₀ hp).2
  convert indicator_quadratic_frobenius_bound E hE hp using 1 <;> ring

/-- The same literal tensor in standard Euclidean Gaussian coordinates. -/
def euclideanConditionalQuadraticTensor {n : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n))) (j k : Fin n) : ℝ :=
  (∫ x in E,x j*x k-(if j=k then 1 else 0) ∂stdGaussian (EuclideanSpace ℝ (Fin n)))/
    ((stdGaussian (EuclideanSpace ℝ (Fin n))) E).toReal

theorem gaussian_toLp_measurePreserving (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n→ℝ)) (γFin n)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  refine ⟨(MeasurableEquiv.toLp 2 (Fin n→ℝ)).measurable,?_⟩
  exact map_pi_eq_stdGaussian

/-- The actual product/Euclidean Gaussian change of coordinates transports the
literal conditional tensor, without a density or moment-transfer premise. -/
theorem euclidean_conditional_quadratic_frobenius_bound {n : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : MeasurableSet E)
    (hp : 0 < ((stdGaussian (EuclideanSpace ℝ (Fin n))) E).toReal) :
    Real.sqrt (∑ j,∑ k,(euclideanConditionalQuadraticTensor E j k)^2) ≤
      4*Real.exp 1*(1+Real.log (1/((stdGaussian (EuclideanSpace ℝ (Fin n))) E).toReal)) := by
  let T := MeasurableEquiv.toLp 2 (Fin n→ℝ)
  let F := T ⁻¹' E
  have hF : MeasurableSet F := hE.preimage T.measurable
  have hT := gaussian_toLp_measurePreserving n
  have hmass : γFin n F=(stdGaussian (EuclideanSpace ℝ (Fin n))) E := by
    have hh := Measure.map_apply (μ:=γFin n) hT.measurable hE
    rw [hT.map_eq] at hh
    exact hh.symm
  have hmom (j k : Fin n) : conditionalQuadraticTensor F j k=euclideanConditionalQuadraticTensor E j k := by
    have hh := hT.integral_comp' (E.indicator (fun x => x j*x k-(if j=k then (1:ℝ) else 0)))
    have heq : (fun x : Fin n→ℝ => (E.indicator (fun y => y j*y k-(if j=k then (1:ℝ) else 0))) (T x))=
        F.indicator (fun x => x j*x k-(if j=k then (1:ℝ) else 0)) := by
      funext x
      by_cases hx : T x∈E
      · have hfx : x∈F := hx
        simp only [Set.indicator_of_mem hx,Set.indicator_of_mem hfx]
        rfl
      · have hfx : x∉F := hx
        simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem hfx]
    change (∫ x,(E.indicator (fun y => y j*y k-(if j=k then (1:ℝ) else 0))) (T x) ∂γFin n)=_ at hh
    rw [heq,integral_indicator hF,integral_indicator hE] at hh
    unfold conditionalQuadraticTensor euclideanConditionalQuadraticTensor
    rw [hmass,hh]
  have hb := conditional_quadratic_frobenius_bound F hF (by rw [hmass]; exact hp)
  simpa only [hmom,hmass] using hb

end NegativeVotingConditionalSecondMoment
