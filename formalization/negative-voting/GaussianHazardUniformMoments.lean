import GaussianHazardUniformUpperCoefficients
import GaussianHazardUniformCoefficientBounds

/-! Actual uniform all-threshold moments for Gaussian pair-hazard densities.
The box width and alphabet threshold depend only on the requested powers and
loss. Both off-diagonal and analytic diagonal pairs are covered. -/
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology
namespace NegativeVotingHazardUniformMoments
open WeakSimplex NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingGaussianTail NegativeVotingHazardMomentEnvelope
  NegativeVotingHazardUniformUpperCoefficients NegativeVotingHazardUniformCoefficientBounds
  NegativeVotingHazardQuantileAsymptotics NegativeVotingDiagonalHazardDifferentiation

/-- The auxiliary tail condition in the explicit lower normalization is
satisfied eventually for each fixed positive box width. -/
lemma eventually_quantile_tail_half (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-a*(upperQuantile n)^2) ≤ 1/2 := by
  filter_upwards [upperQuantile_sq_tendsto.eventually_ge_atTop (Real.log 2/a)] with n hn
  have hh : Real.log 2 ≤ a*(upperQuantile n)^2 := by
    have ht := (div_le_iff₀ ha).mp hn
    nlinarith
  calc
    _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num

/-- Fixed scalar margins suffice; this form permits one common box width
when several moment orders are subsequently combined. -/
theorem eventually_box_moments (η : ℝ) (hη : 0 < η) (p q : ℕ)
    (a lam : ℝ) (ha : 0 < a) (ha1 : a ≤ 1/16) (hlam0 : 0 < lam)
    (hlam : lam ≤ (p:ℝ)+2) (hupper : 12*a*((p:ℝ)+2)+lam < η)
    (hlower : 48*a < η) :
    ∀ᶠ n : ℕ in atTop, ∀ (σ h : Fin (n+2) → ℝ),
      (∀ k,1-a ≤ σ k) → (∀ k,σ k ≤ 1+a) →
      (∀ k,|h k| ≤ a*upperQuantile n) → ∀ i j : Fin (n+2),
      ((n:ℝ)+2)^(-2-η) ≤ (∫x,hazardPairDensity σ h x i j) ∧
      (∫x,momentDensity σ h p q i j x) ≤ ((n:ℝ)+2)^(-2+η) ∧
      (∫x,momentDensity σ h p q i j x)/(∫x,hazardPairDensity σ h x i j) ≤
        ((n:ℝ)+2)^(2*η) := by
  have hKL := lowMomentConstant_nonneg p q
  have hKH := highMomentConstant_nonneg lam hlam0 p q
  have hLo := eventually_quantile_double_exp_le (2*lowMomentConstant p q) (by positivity)
    p (2*p+q+2) 3 (a/2) (by positivity)
  have hHi := eventually_rpow_quantile_polynomial_le (2*highMomentConstant lam p q) (by positivity)
    (p+q+2) (-2+12*a*((p:ℝ)+2)+lam) (-2+η) (by linarith)
  have hLower := eventually_rpow_quantile_polynomial_le (8/a) (by positivity)
    0 (-2-η) (-2-48*a) (by linarith)
  filter_upwards [eventually_gt_atTop (0:ℕ),upperQuantile_tendsto.eventually_ge_atTop 1,
    eventually_quantile_tail_half a ha,hLo,hHi,hLower] with n hn hb htail hlo hhi hlowern
  intro σ h hs hS hh i j
  let m : ℝ := (n:ℝ)+2
  let b := upperQuantile n
  have hm : 0 < m := by dsimp [m];positivity
  have hm1 : 1 ≤ m := by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hb0 : 0 ≤ b := by dsimp [b];linarith
  have hs0 : 0 < 1-a := by linarith
  have hρlow := integral_pair_quantile_lower n hn hb a ha ha1 σ h hs hS hh htail i j
  have hexp : m^(-48*a) ≤ Real.exp (-24*a*b^2) := by
    have ht := rpow_neg_twice_le_quantile_exp_neg_sq n hn (24*a) (by positivity)
    convert ht using 1 <;> dsimp only [m,b] <;> congr 1 <;> ring
  have hfactor : (a/8)*m^(-2-48*a)=a/(8*m^2)*m^(-48*a) := by
    rw [show (-2-48*a)=(-2:ℝ)+(-48*a) by ring,Real.rpow_add hm,
      Real.rpow_neg hm.le,Real.rpow_two]
    ring
  have hlowern' : (8/a)*m^(-2-η) ≤ m^(-2-48*a) := by
    simpa only [pow_zero,mul_one,m] using hlowern
  have hscaled : m^(-2-η) ≤ (a/8)*m^(-2-48*a) := by
    have ht := mul_le_mul_of_nonneg_left hlowern' (show 0 ≤ a/8 by positivity)
    convert ht using 1 <;> field_simp <;> ring
  have hlower : m^(-2-η) ≤ ∫x,hazardPairDensity σ h x i j := by
    apply hscaled.trans
    rw [hfactor]
    exact (mul_le_mul_of_nonneg_left hexp (show 0 ≤ a/(8*m^2) by positivity)).trans hρlow
  have hlow : 2*lowMomentEnvelope n a p q ≤ m^(-2+η) := by
    have ht := mul_le_mul_of_nonneg_left (lowMomentEnvelope_le n hn hb a ha ha1 p q)
      (show (0:ℝ) ≤ 2 by norm_num)
    have ht' : 2*lowMomentEnvelope n a p q ≤ m^(-(3:ℝ)) := by
      apply ht.trans
      convert hlo using 1 <;> (try dsimp only [m,b]) <;> ring
    exact ht'.trans (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith))
  have hhigh : 2*highMomentEnvelope n a lam p q ≤ m^(-2+η) := by
    have ht := mul_le_mul_of_nonneg_left (highMomentEnvelope_le n hn hb a lam ha ha1 hlam0 p q hlam)
      (show (0:ℝ) ≤ 2 by norm_num)
    apply ht.trans
    convert hhi using 1 <;> (try dsimp only [m,b]) <;> ring
  have hT : a*b ≤ (1-4*a)*b := by nlinarith
  have hsplit := integral_momentDensity_split σ h (1-a) (1+a) (a*b) ((1-4*a)*b) lam
    hs0 hs hS (mul_nonneg ha.le hb0) hh hT hlam0 p q hlam i j
  have hsplit' : (∫x,momentDensity σ h p q i j x) ≤
      lowMomentEnvelope n a p q+highMomentEnvelope n a lam p q := by
    simpa only [Fintype.card_fin,lowMomentEnvelope,highMomentEnvelope,b] using hsplit
  have hmoment : (∫x,momentDensity σ h p q i j x) ≤ m^(-2+η) := by linarith
  refine ⟨hlower,hmoment,?_⟩
  have hρpos : 0 < ∫x,hazardPairDensity σ h x i j :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hm _) hlower
  apply (div_le_iff₀ hρpos).mpr
  calc
    _ ≤ m^(-2+η) := hmoment
    _ = m^(2*η)*m^(-2-η) := by rw [←Real.rpow_add hm];congr 1;ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (Real.rpow_nonneg hm.le _)

/-- Arbitrarily small power loss for actual pair densities and normalized
moments, uniformly over every threshold, model in the fixed box, and pair. -/
theorem exists_uniform_box_moments (η : ℝ) (hη : 0 < η) (p q : ℕ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, ∀ (σ h : Fin (n+2) → ℝ),
        (∀ k,1-a ≤ σ k) → (∀ k,σ k ≤ 1+a) →
        (∀ k,|h k| ≤ a*upperQuantile n) → ∀ i j : Fin (n+2),
        ((n:ℝ)+2)^(-2-η) ≤ (∫x,hazardPairDensity σ h x i j) ∧
        (∫x,momentDensity σ h p q i j x) ≤ ((n:ℝ)+2)^(-2+η) ∧
        (∫x,momentDensity σ h p q i j x)/(∫x,hazardPairDensity σ h x i j) ≤
          ((n:ℝ)+2)^(2*η) := by
  let a : ℝ := min (1/32) (η/(384*((p:ℝ)+3)))
  let lam : ℝ := min 1 (η/8)
  have hp : 0 ≤ (p:ℝ) := Nat.cast_nonneg p
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1/16 := (min_le_left _ _).trans (by norm_num)
  have hlam0 : 0 < lam := lt_min (by norm_num) (by positivity)
  have hlam : lam ≤ (p:ℝ)+2 := (min_le_left _ _).trans (by linarith)
  have haη : a*(384*((p:ℝ)+3)) ≤ η :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hlamη : lam ≤ η/8 := min_le_right _ _
  have hap : 0 ≤ a*(p:ℝ) := mul_nonneg ha.le hp
  have hupper : 12*a*((p:ℝ)+2)+lam < η := by nlinarith
  have hlower : 48*a < η := by nlinarith
  exact ⟨a,ha,ha1,eventually_box_moments η hη p q a lam ha ha1 hlam0 hlam hupper hlower⟩

/-- Rescaling the loss parameter gives the requested normalized moment
exponent itself, while also tightening both unnormalized bounds. -/
theorem exists_uniform_box_normalized_moments (η : ℝ) (hη : 0 < η) (p q : ℕ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, ∀ (σ h : Fin (n+2) → ℝ),
        (∀ k,1-a ≤ σ k) → (∀ k,σ k ≤ 1+a) →
        (∀ k,|h k| ≤ a*upperQuantile n) → ∀ i j : Fin (n+2),
        ((n:ℝ)+2)^(-2-η/2) ≤ (∫x,hazardPairDensity σ h x i j) ∧
        (∫x,momentDensity σ h p q i j x) ≤ ((n:ℝ)+2)^(-2+η/2) ∧
        (∫x,momentDensity σ h p q i j x)/(∫x,hazardPairDensity σ h x i j) ≤
          ((n:ℝ)+2)^η := by
  obtain ⟨a,ha,ha1,he⟩ := exists_uniform_box_moments (η/2) (by positivity) p q
  refine ⟨a,ha,ha1,?_⟩
  simpa only [show 2*(η/2)=η by ring] using he

/-- A single box and a single alphabet threshold work for every prescribed
finite rectangle of moment orders. The normalized loss is exactly eta. -/
theorem exists_uniform_box_moment_family (η : ℝ) (hη : 0 < η) (P Q : ℕ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, ∀ (p q : ℕ), p ≤ P → q ≤ Q →
        ∀ (σ h : Fin (n+2) → ℝ),
        (∀ k,1-a ≤ σ k) → (∀ k,σ k ≤ 1+a) →
        (∀ k,|h k| ≤ a*upperQuantile n) → ∀ i j : Fin (n+2),
        ((n:ℝ)+2)^(-2-η/2) ≤ (∫x,hazardPairDensity σ h x i j) ∧
        (∫x,momentDensity σ h p q i j x) ≤ ((n:ℝ)+2)^(-2+η/2) ∧
        (∫x,momentDensity σ h p q i j x)/(∫x,hazardPairDensity σ h x i j) ≤
          ((n:ℝ)+2)^η := by
  let a : ℝ := min (1/32) ((η/2)/(384*((P:ℝ)+3)))
  let lam : ℝ := min 1 ((η/2)/8)
  have hP : 0 ≤ (P:ℝ) := Nat.cast_nonneg P
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1/16 := (min_le_left _ _).trans (by norm_num)
  have hlam0 : 0 < lam := lt_min (by norm_num) (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have haη : a*(384*((P:ℝ)+3)) ≤ η/2 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hlamη : lam ≤ (η/2)/8 := min_le_right _ _
  have hap : 0 ≤ a*(P:ℝ) := mul_nonneg ha.le hP
  have hupperP : 12*a*((P:ℝ)+2)+lam < η/2 := by nlinarith
  have hlower : 48*a < η/2 := by nlinarith
  have he (p : Fin (P+1)) (q : Fin (Q+1)) :
      ∀ᶠ n : ℕ in atTop, ∀ (σ h : Fin (n+2) → ℝ),
        (∀ k,1-a ≤ σ k) → (∀ k,σ k ≤ 1+a) →
        (∀ k,|h k| ≤ a*upperQuantile n) → ∀ i j : Fin (n+2),
        ((n:ℝ)+2)^(-2-η/2) ≤ (∫x,hazardPairDensity σ h x i j) ∧
        (∫x,momentDensity σ h p.val q.val i j x) ≤ ((n:ℝ)+2)^(-2+η/2) ∧
        (∫x,momentDensity σ h p.val q.val i j x)/(∫x,hazardPairDensity σ h x i j) ≤
          ((n:ℝ)+2)^η := by
    have hp : (p.val:ℝ) ≤ (P:ℝ) := by exact_mod_cast Nat.le_of_lt_succ p.isLt
    have hp0 : 0 ≤ (p.val:ℝ) := Nat.cast_nonneg p.val
    have hlam : lam ≤ (p.val:ℝ)+2 := by linarith
    have hupper : 12*a*((p.val:ℝ)+2)+lam < η/2 := by
      have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 12*a by positivity)
      nlinarith
    have ht := eventually_box_moments (η/2) (by positivity) p.val q.val a lam
      ha ha1 hlam0 hlam hupper hlower
    simpa only [show 2*(η/2)=η by ring] using ht
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards [eventually_all.mpr (fun p => eventually_all.mpr (he p))] with n hn
  intro p q hp hq
  exact hn ⟨p,by omega⟩ ⟨q,by omega⟩

end NegativeVotingHazardUniformMoments
