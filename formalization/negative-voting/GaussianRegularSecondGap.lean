import GaussianSecondChaosLower

/-! The actual regular second-chaos gap above the global perspective tangent
is eventually bounded by an absolute constant divided by the alphabet size. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology Classical
namespace NegativeVotingRegularSecondGap
open NegativeVoting NegativeVotingModern NegativeVotingRegularMaximum
  NegativeVotingCompetitiveParity NegativeVotingFractionalMass NegativeVotingSecondChaosLower
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingGaussianMaximumSecondMoment NegativeVotingGaussianMaximumLocalization

def referenceEll (n : ℕ) : ℝ := ((n:ℝ)+2)*referenceFirstWeight n-1

def referenceJensenFloor (n : ℕ) : ℝ := (referenceEll n)^2/(2*((n:ℝ)+2))

theorem eventually_maximum_mean_sq_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ maximumMean n^2 := by
  filter_upwards [eventually_gt_atTop (0:ℕ),upperQuantile_tendsto.eventually_ge_atTop 1,
    eventually_scaledMaximum_mean_lower] with n hn hb hm
  have hpos := upperQuantile_pos hn
  have hdiff : 0 ≤ maximumMean n-upperQuantile n :=
    (mul_nonneg_iff_of_pos_left hpos).mp (le_trans (by norm_num : (0:ℝ) ≤ 103/200) hm)
  nlinarith

theorem referenceEll_nonneg_of_mean_sq (n : ℕ) (ha : 1 ≤ maximumMean n^2) :
    0 ≤ referenceEll n := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h : maximumMean n^2 ≤ ((n:ℝ)+2)*maximumMean n^2/((n:ℝ)+1) :=
    (le_div_iff₀ hn).2 (by nlinarith [sq_nonneg (maximumMean n)])
  unfold referenceEll referenceFirstWeight
  simp only [div_eq_mul_inv,mul_assoc] at h ⊢
  nlinarith

theorem reference_tangent_floor_lower (n : ℕ) (hn : 0 < n) (hell : 0 ≤ referenceEll n) :
    referenceJensenFloor n ≤ referenceSecondWeight n := by
  let f := (maxWeights : (Fin (n+2) → ℝ) → Fin (n+2) → ℝ)
  have hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian (Fin (n+2))) :=
    fun i => (measurable_maxWeights id (fun k => measurable_pi_apply k) i).aemeasurable
  have hp : ∀ᵐ x ∂standardGaussian (Fin (n+2)), SimplexWeights (f x) := ae_of_all _ maxWeights_simplex
  have hP : assignmentMassSquares f=1/((n:ℝ)+2) := by
    calc
      _ = chaosEnergy f 0 := by rw [chaosEnergy_zero]; rfl
      _ = _ := canonical_chaosEnergy_zero n
  have hW : assignmentFirstEnergy f=referenceFirstWeight n := by
    rw [←canonical_chaosEnergy_one n hn,chaosEnergy_one]
    rfl
  have h := secondChaos_affine_tangent f hf hp (referenceEll n) hell
  rw [hP,hW,canonical_chaosEnergy_two n hn] at h
  convert h using 1
  unfold referenceJensenFloor referenceEll
  field_simp <;> ring

/-- Explicit scalar comparison of the actual moment formulas. -/
theorem second_gap_algebra (n a v L : ℝ) (hn : 0 < n) (hL : 1 ≤ L)
    (ha : 1 ≤ a) (hv0 : 0 ≤ v) (hs : a+v ≤ 5*L) (hv : v ≤ 6/L) :
    (n+2)*((n+2)*(a+v-1)^2/(2*(n+1)*n)-
      ((n+2)*a/(n+1)-1)^2/(2*(n+2))) ≤ 48+126*L^2/n := by
  have hL0 : 0 < L := by linarith
  have hd : 0 < n+1 := by positivity
  have hm : 0 < n+2 := by positivity
  let z := a+v-1
  let b := (n+2)*a/(n+1)-1
  let q := (n+2)^2/((n+1)*n)-1
  have hqeq : q=(3*n+4)/((n+1)*n) := by dsimp [q]; field_simp; ring
  have hq : q ≤ 7/n := by
    rw [hqeq]
    apply (div_le_div_iff₀ (mul_pos hd hn) hn).2
    nlinarith
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hz : z ≤ 6*L := by dsimp [z]; linarith
  have hzsq : z^2 ≤ 36*L^2 := by nlinarith
  have hqz : q*z^2 ≤ (7/n)*(36*L^2) :=
    mul_le_mul hq hzsq (sq_nonneg z) (by positivity)
  have hb : a-1 ≤ b := by
    dsimp [b]
    have h : a ≤ (n+2)*a/(n+1) := (le_div_iff₀ hd).2 (by nlinarith)
    linarith
  have hbsq : (a-1)^2 ≤ b^2 := (sq_le_sq₀ (by linarith) (by linarith)).2 hb
  have hzb : z^2-b^2 ≤ 2*a*v+v^2 := by dsimp [z] at *; nlinarith
  have haL : a ≤ 5*L := by linarith
  have hav : a*v ≤ 30 := by
    have h := mul_le_mul haL hv hv0 (by positivity : 0 ≤ 5*L)
    have he : (5*L)*(6/L)=(30:ℝ) := by field_simp; ring
    rwa [he] at h
  have hv6 : v ≤ 6 := hv.trans ((div_le_iff₀ hL0).2 (by linarith))
  have hv2 : v^2 ≤ 36 := by nlinarith
  have hbase : z^2-b^2 ≤ 96 := by nlinarith
  have hexact : (n+2)*((n+2)*(a+v-1)^2/(2*(n+1)*n)-
      ((n+2)*a/(n+1)-1)^2/(2*(n+2)))=(q*z^2+(z^2-b^2))/2 := by
    dsimp [q,z,b]
    field_simp
    ring
  rw [hexact]
  calc
    _ ≤ ((7/n)*(36*L^2)+96)/2 := by linarith [add_le_add hqz hbase]
    _ = _ := by ring

theorem reference_second_gap_majorant_tendsto :
    Tendsto (fun n : ℕ => 126*Real.log ((n:ℝ)+2)^2/(n:ℝ)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 2 one_ne_zero
  convert (h.comp size_tendsto).const_mul (126:ℝ) using 1
  · funext n
    dsimp only [Function.comp_def]
    ring
  · norm_num

/-- The actual regular coefficient, not an abstract O(1/m) premise, has a
uniform explicit eventual gap constant. -/
theorem eventually_reference_second_gap :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ referenceSecondWeight n-referenceJensenFloor n ∧
      referenceSecondWeight n-referenceJensenFloor n ≤ 50/((n:ℝ)+2) := by
  have heps := reference_second_gap_majorant_tendsto.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_maximum_mean_sq_ge_one,
    eventually_maximum_variance_log_bound,eventually_maximum_second_moment_log_bound,
    (Real.tendsto_log_atTop.comp size_tendsto).eventually_ge_atTop 1,heps]
    with n hn ha hv hs hL he
  have hv0 : 0 ≤ maximumVariance n := variance_nonneg _ _
  have hM : maximumSecondMoment n=maximumMean n^2+maximumVariance n := by
    rw [maximumVariance_eq_second_sub_mean_sq]
    ring
  have hbase := second_gap_algebra (n:ℝ) (maximumMean n^2) (maximumVariance n)
    (Real.log ((n:ℝ)+2)) (by exact_mod_cast hn) hL ha hv0 (by rwa [←hM]) hv
  have hbound : ((n:ℝ)+2)*(referenceSecondWeight n-referenceJensenFloor n) ≤
      48+126*Real.log ((n:ℝ)+2)^2/(n:ℝ) := by
    convert hbase using 1
    unfold referenceSecondWeight referenceJensenFloor referenceEll referenceFirstWeight
    rw [hM]
    ring
  refine ⟨sub_nonneg.mpr (reference_tangent_floor_lower n hn (referenceEll_nonneg_of_mean_sq n ha)),?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (n:ℝ)+2)).2
  nlinarith

end NegativeVotingRegularSecondGap
