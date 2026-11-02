import GaussianUniformMassBound

/-! Actual near-balanced mass box for every competitive fractional assignment.
The threshold precedes dimension, the reference and the whole noise range. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology Classical
universe u
namespace NegativeVotingCompetitiveTightMassWindow
open NegativeVoting NegativeVotingFractionalMass NegativeVotingCompetitiveDeficit
  NegativeVotingUniformMassBound NegativeVotingCompetitiveSharpMass

 theorem scalar_mass_half_window (m r δ p:ℝ) (hm:4096 ≤ m) (hr:0 ≤ r)
    (hrm:r ≤ 2/m) (hδ:δ ≤ 256*r^2/m) (hp:(p-1/m)^2 ≤ δ) :
    p∈Icc (1/(2*m)) (3/(2*m)) := by
  have hm0:0 < m := by linarith
  have hrsq := pow_le_pow_left₀ hr hrm 2
  have hδ2 : m^2*δ ≤ 1024/m := by
    have hs:=mul_le_mul_of_nonneg_left hδ (sq_nonneg m)
    have ht:=mul_le_mul_of_nonneg_left hrsq (show 0 ≤ m^2*256/m by positivity)
    have he : (m^2*256/m)*(2/m)^2=1024/m := by field_simp;ring
    rw [he] at ht
    exact hs.trans (by convert ht using 1 <;> ring)
  have hsize : 1024/m ≤ (1/4:ℝ) := (div_le_iff₀ hm0).mpr (by linarith)
  have hs:= (mul_le_mul_of_nonneg_left hp (sq_nonneg m)).trans (hδ2.trans hsize)
  have he : m^2*(p-1/m)^2=(m*p-1)^2 := by field_simp
  rw [he] at hs
  have hab : |m*p-1| ≤ (1/2:ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)).mp
    rw [sq_abs]
    nlinarith
  have hb:=abs_le.mp hab
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2*m)).mpr
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 2*m)).mpr
    nlinarith

 theorem eventually_uniform_competitive_half_mass_window :
    ∀ᶠ n:ℕ in atTop,∀(κ:Type u) [Fintype κ]
      (Ref:Fin (n+2)→κ→ℝ) (hRef:RegularSimplexGram Ref)
      (f:(κ→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian κ))
      (hp:∀ᵐx ∂standardGaussian κ,SimplexWeights (f x))
      (r:ℝ) (hr0:0 ≤ r) (hr:r ≤ 1/((n:ℝ)+1))
      (hcomp:gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment Ref)),
      ∀i,assignmentMass f i∈Icc (1/(2*((n:ℝ)+2))) (3/(2*((n:ℝ)+2))) := by
  filter_upwards [eventually_uniform_competitive_deficit_bounds,eventually_ge_atTop (4096:ℕ)] with n hdef hn
  intro κ _ Ref hRef f hf hp r hr0 hr hcomp i
  have hD:=hdef κ Ref hRef f hf hp r hr0 hr hcomp
  have hδ:massDeficit n f ≤ 256*r^2/((n:ℝ)+2) := by
    have hh := hD.2.1.trans (mul_le_mul_of_nonneg_left hD.2.2.2 (by norm_num : (0:ℝ) ≤ 2))
    convert hh using 1 <;> ring
  have hpi:(assignmentMass f i-1/((n:ℝ)+2))^2 ≤ massDeficit n f := by
    unfold massDeficit
    exact Finset.single_le_sum (f:=fun j:Fin (n+2)=>(assignmentMass f j-1/((n:ℝ)+2))^2)
      (fun j _=>sq_nonneg _) (Finset.mem_univ i)
  have hr2:r ≤ 2/((n:ℝ)+2) := hr.trans ((div_le_div_iff₀ (by positivity) (by positivity)).mpr
    (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have hnR : (4096:ℝ) ≤ n := by exact_mod_cast hn
  exact scalar_mass_half_window ((n:ℝ)+2) r (massDeficit n f) (assignmentMass f i)
    (by linarith) hr0 hr2 hδ hpi

 theorem eventually_uniform_cubic_tail_scale :
    ∀ᶠ n:ℕ in atTop,∀ r : ℝ, 0 ≤ r → r ≤ 1/((n:ℝ)+1) →
      4*r*(1+Real.log ((n:ℝ)+2)) < 1 := by
  have he := (sharpMassMajorant_tendsto_zero 16).eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [he] with n hn
  intro r hr0 hr
  let m:ℝ := (n:ℝ)+2
  let L:ℝ := 1+Real.log m
  have hm:1 ≤ m := by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hm0:0 < m := by linarith
  have hL:1 ≤ L := by dsimp [L];linarith [Real.log_nonneg hm]
  have hr2:r ≤ 2/m := hr.trans ((div_le_div_iff₀ (by positivity) hm0).mpr
    (by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have hmain : (2/m)*16*L^2 < 1 := by
    have hs := NegativeVotingGaussianMaximumLocalization.referenceSecondWeight_nonneg n
    change (2/m)*16*L^2+2*NegativeVotingGaussianMaximumLocalization.referenceSecondWeight n+2/m < 1 at hn
    linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) hm0.le]
  have hratio : 4*r*L ≤ (2/m)*16*L^2 := by
    have hh:=mul_le_mul_of_nonneg_right hr2 (show 0 ≤ 4*L by positivity)
    have haux:=mul_le_mul_of_nonneg_left (show 4*L ≤ 16*L^2 by nlinarith) (show 0 ≤ 2/m by positivity)
    nlinarith
  exact hratio.trans_lt hmain

end NegativeVotingCompetitiveTightMassWindow
