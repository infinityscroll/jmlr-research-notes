import GaussianFanOptimizedValue

/-! Positive-mass continuity of the actual optimized Gaussian value, including
coincident rows and singular covariance representations. The modulus follows
from the genuine coercive offset minimizer, not from a supplied regularity input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingFanMassContinuity
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanValue
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

abbrev PositiveMassVector (ι : Type*) [Fintype ι] :=
  {p : ι → ℝ // (∀ i,0 < p i) ∧ ∑ i,p i=1}

/-- A true offset minimizer has a uniform bound on every positive mass box.
Distinctness and full rank of the score rows are not needed. -/
theorem exists_bounded_offset_minimizer (B : ι → FSC.Coord d) (p : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hp : ∀ i,δ ≤ p i) (hs : ∑ i,p i=1) :
    ∃ h : centeredGauge ι, optimizedValue B p=potential B p h ∧
      ‖h‖ ≤ expectedMax B 0/δ := by
  obtain ⟨h,hh,hmin⟩ := exists_potential_minimizer B p (fun i => hδ.trans_le (hp i)) hs
  refine ⟨⟨h,hh⟩,optimizedValue_eq_of_minimizer B p (fun i => hδ.le.trans (hp i)) hs
    ⟨h,hh⟩ (fun k => hmin k k.property),?_⟩
  have hc := potential_ge_massLower_mul_norm B p h hδ.le hp hs hh
  have hz := hmin 0 (by simp)
  simp only [potential,Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero] at hz
  change ‖h‖ ≤ expectedMax B 0/δ
  apply (le_div_iff₀ hδ).mpr
  dsimp only [potential] at hc
  nlinarith

theorem potential_mass_sub_bound (B : ι → FSC.Coord d) (p q h : ι → ℝ) :
    |potential B p h-potential B q h| ≤ (Fintype.card ι : ℝ)*‖p-q‖*‖h‖ := by
  have he : potential B p h-potential B q h=∑ i,(q i-p i)*h i := by
    unfold potential
    simp only [sub_mul,Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ i, |(q i-p i)*h i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, ‖q-p‖*‖h‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hi : |q i-p i| ≤ ‖q-p‖ := by
        simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (q-p) i
      have hh : |h i| ≤ ‖h‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm h i
      exact mul_le_mul hi hh (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,norm_sub_rev q p]; ring

/-- Actual local mass Lipschitz estimate, valid even at rank loss. -/
theorem optimizedValue_mass_sub_bound (B : ι → FSC.Coord d) (p q : ι → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hp : ∀ i,δ ≤ p i) (hq : ∀ i,δ ≤ q i)
    (hps : ∑ i,p i=1) (hqs : ∑ i,q i=1) :
    |optimizedValue B p-optimizedValue B q| ≤
      ((Fintype.card ι : ℝ)*expectedMax B 0/δ)*‖p-q‖ := by
  have hupper (a b : ι → ℝ) (ha : ∀ i,δ ≤ a i) (hb : ∀ i,δ ≤ b i)
      (has : ∑ i,a i=1) (hbs : ∑ i,b i=1) :
      optimizedValue B a-optimizedValue B b ≤
        ((Fintype.card ι : ℝ)*expectedMax B 0/δ)*‖a-b‖ := by
    obtain ⟨k,hk,hknorm⟩ := exists_bounded_offset_minimizer B b δ hδ hb hbs
    have hv := optimizedValue_le_potential B a (fun i => hδ.le.trans (ha i)) has k
    have hm := (abs_le.mp (potential_mass_sub_bound B a b k)).2
    have hn := mul_le_mul_of_nonneg_left hknorm
      (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) (norm_nonneg (a-b)))
    have heq : ((Fintype.card ι : ℝ)*‖a-b‖)*(expectedMax B 0/δ)=
        ((Fintype.card ι : ℝ)*expectedMax B 0/δ)*‖a-b‖ := by ring
    rw [heq] at hn
    rw [hk]
    change _ ≤ _ at hm
    change (Fintype.card ι : ℝ)*‖a-b‖*‖(k : ι → ℝ)‖ ≤ _ at hn
    linarith
  refine abs_le.mpr ⟨?_,hupper p q hp hq hps hqs⟩
  have hh := hupper q p hq hp hqs hps
  rw [norm_sub_rev q p] at hh
  linarith

/-- Joint continuity in arbitrary rows and positive prescribed masses.
The row modulus is uniform in the masses, while the mass modulus is supplied
by the actual bounded offset minimizers. -/
theorem optimizedValue_continuous_joint :
    Continuous (fun q : (ι → FSC.Coord d)×PositiveMassVector ι => optimizedValue q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q₀
  let p₀ : ι → ℝ := q₀.2
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ p₀ Finset.univ_nonempty
  let δ := p₀ i/2
  have hi0 : 0 < p₀ i := q₀.2.property.1 i
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hmass (j : ι) : δ < p₀ j := by
    have hij := hi j (Finset.mem_univ j)
    dsimp [δ]
    linarith
  have hnear : ∀ᶠ q : (ι → FSC.Coord d)×PositiveMassVector ι in 𝓝 q₀,
      ∀ j,δ ≤ (q.2 : ι → ℝ) j := by
    apply Filter.eventually_all.mpr
    intro j
    have hc : Continuous (fun q : (ι → FSC.Coord d)×PositiveMassVector ι => (q.2 : ι → ℝ) j) := by
      exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
    exact hc.continuousAt.tendsto.eventually (Ici_mem_nhds (hmass j))
  let K := (Fintype.card ι : ℝ)*expectedMax q₀.1 0/δ
  let G := ∫ x : FSC.Coord d,‖x‖ ∂stdGaussian (FSC.Coord d)
  let bound (q : (ι → FSC.Coord d)×PositiveMassVector ι) :=
    ‖q.1-q₀.1‖*G+K*‖(q.2 : ι → ℝ)-p₀‖
  have hcont : Continuous bound := by fun_prop
  have hlim : Tendsto bound (𝓝 q₀) (𝓝 0) := by
    simpa [bound,p₀] using hcont.tendsto q₀
  have hle : ∀ᶠ q : (ι → FSC.Coord d)×PositiveMassVector ι in 𝓝 q₀,
      ‖optimizedValue q.1 q.2-optimizedValue q₀.1 q₀.2‖ ≤ bound q := by
    filter_upwards [hnear] with q hq
    have hr := optimizedValue_rows_sub_bound q.1 q₀.1 q.2
      (fun j => (q.2.property.1 j).le) q.2.property.2
    have hp := optimizedValue_mass_sub_bound q₀.1 q.2 p₀ δ hδ hq
      (fun j => (hmass j).le) q.2.property.2 q₀.2.property.2
    have ht := abs_sub_le (optimizedValue q.1 q.2) (optimizedValue q₀.1 q.2)
      (optimizedValue q₀.1 p₀)
    change |optimizedValue q.1 q.2-optimizedValue q₀.1 p₀| ≤ _
    exact ht.trans (add_le_add hr hp)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hle hlim

end NegativeVotingFanMassContinuity
