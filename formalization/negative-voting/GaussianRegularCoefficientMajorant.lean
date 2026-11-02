import GaussianRegularPairCoefficientBounds

/-! A literal smooth, common score-range majorant for all divided regular-noise
coefficients. Gaussian moment estimates are kept separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace Topology Classical ContDiff
namespace NegativeVotingRegularPairCoefficient
open NegativeVoting NegativeVotingFacetConditionalPlane NegativeVotingRegularFacetRange
  NegativeVotingBalancedReference

section Finite
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def smoothUtilityRange (u : ι → ℝ) : ℝ :=
  Real.log (∑i,Real.exp (u i))+Real.log (∑i,Real.exp (-u i))

theorem sum_exp_pos (u : ι → ℝ) : 0 < ∑i,Real.exp (u i) :=
  (Real.exp_pos (u (Classical.arbitrary ι))).trans_le
    (Finset.single_le_sum (fun i _ => (Real.exp_pos (u i)).le) (Finset.mem_univ _))

theorem maxScore_le_log_sum_exp (u : ι → ℝ) : maxScore u ≤ Real.log (∑i,Real.exp (u i)) := by
  apply Finset.sup'_le
  intro i hi
  have hh := Real.log_le_log (Real.exp_pos (u i))
    (Finset.single_le_sum (fun j _ => (Real.exp_pos (u j)).le) (Finset.mem_univ i))
  simpa only [Real.log_exp] using hh

theorem utilityRange_le_smooth (u : ι → ℝ) : utilityRange u ≤ smoothUtilityRange u :=
  add_le_add (maxScore_le_log_sum_exp u) (maxScore_le_log_sum_exp (fun i => -u i))

theorem smoothUtilityRange_nonneg (u : ι → ℝ) : 0 ≤ smoothUtilityRange u :=
  (utilityRange_nonneg u).trans (utilityRange_le_smooth u)

theorem log_sum_exp_le_card_max (u : ι → ℝ) (M : ℝ) (hu : ∀i,u i ≤ M) :
    Real.log (∑i,Real.exp (u i)) ≤ Real.log (Fintype.card ι:ℝ)+M := by
  have hc : 0<(Fintype.card ι:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hh : (∑i,Real.exp (u i)) ≤ (Fintype.card ι:ℝ)*Real.exp M := by
    calc (∑i,Real.exp (u i)) ≤ ∑_i:ι,Real.exp M :=
      Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (hu i))
    _ = _ := by simp
  have hh' := Real.log_le_log (sum_exp_pos u) hh
  simpa only [Real.log_mul hc.ne' (Real.exp_ne_zero M),Real.log_exp] using hh'

theorem smoothUtilityRange_le_max_abs (u : ι → ℝ) :
    smoothUtilityRange u ≤ 2*Real.log (Fintype.card ι:ℝ)+2*maxScore (fun i => |u i|) := by
  have hm (i : ι) : |u i| ≤ maxScore (fun i => |u i|) :=
    Finset.le_sup' (fun j => |u j|) (Finset.mem_univ i)
  have hp := log_sum_exp_le_card_max u _ (fun i => (le_abs_self (u i)).trans (hm i))
  have hn := log_sum_exp_le_card_max (fun i => -u i) _
    (fun i => (neg_le_abs (u i)).trans (hm i))
  unfold smoothUtilityRange
  linarith

@[fun_prop] theorem smoothUtilityRange_contDiff :
    ContDiff ℝ ∞ (smoothUtilityRange : (ι → ℝ) → ℝ) := by
  have hp : ContDiff ℝ ∞ (fun u : ι → ℝ => ∑i,Real.exp (u i)) :=
    ContDiff.sum (fun i _ => (contDiff_apply ℝ ℝ i).exp)
  have hn : ContDiff ℝ ∞ (fun u : ι → ℝ => ∑i,Real.exp (-u i)) :=
    ContDiff.sum (fun i _ => (contDiff_apply ℝ ℝ i).neg.exp)
  exact (hp.log (fun u => (sum_exp_pos u).ne')).add
    (hn.log (fun u => (sum_exp_pos (fun i => -u i)).ne'))
end Finite

theorem noise_prefactor_bounds (r : ℝ) (hr : 0<r) (hrhalf : r ≤ 1/2) :
    1 ≤ (Real.sqrt (1-r^2))⁻¹ ∧ (Real.sqrt (1-r^2))⁻¹ ≤ 1+2*r^2 := by
  let s := Real.sqrt (1-r^2)
  have hs : 0<s := NegativeVotingRegularOU.negative_noise_scale_pos r hr (by linarith)
  have hs2 : s^2=1-r^2 := Real.sq_sqrt (by nlinarith [sq_nonneg r])
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg r]
  have hsh : 1/2 ≤ s := by nlinarith
  have hu : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hsu : s*s⁻¹=1 := mul_inv_cancel₀ hs.ne'
  have hu2 : s⁻¹ ≤ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hsh) hu]
  constructor
  · change 1 ≤ s⁻¹
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hu]
  · change s⁻¹ ≤ 1+2*r^2
    have hd : 1-s ≤ r^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hs.le]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) hu,
      mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hu2)]

theorem scalar_pair_error (p k a Q : ℝ) (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (hp : 1 ≤ p) (hpa : p ≤ 1+a)
    (hk : p*Real.exp (-Q) ≤ k ∧ k ≤ p*Real.exp Q) :
    |1-k| ≤ (a+Q)*Real.exp Q := by
  have he : 1 ≤ Real.exp Q := Real.one_le_exp_iff.mpr hQ
  have he0 := (Real.exp_pos Q).le
  have hen := (Real.exp_pos (-Q)).le
  have hlow : 1-Q ≤ k := by
    have hx := Real.add_one_le_exp (-Q)
    have hp' := mul_le_mul_of_nonneg_right hp hen
    simp only [one_mul] at hp'
    linarith [hk.1]
  have hhigh := hk.2.trans (mul_le_mul_of_nonneg_right hpa he0)
  have heprod : Real.exp (-Q)*Real.exp Q=1 := by rw [← Real.exp_add];simp
  have hx := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-Q)) he0
  rw [heprod] at hx
  have hmajor : Q ≤ (a+Q)*Real.exp Q := by
    nlinarith [mul_nonneg hQ (sub_nonneg.mpr he),mul_nonneg ha he0]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Common smooth envelope; its score argument is unscaled. -/
def smoothPairError {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (r : ℝ) (u : ι → ℝ) : ℝ :=
  let Q := rangeExponent n ((r/Real.sqrt (1-r^2))*smoothUtilityRange u)
  (2*r^2+Q)*Real.exp Q

@[fun_prop] theorem smoothPairError_contDiff {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (r : ℝ) : ContDiff ℝ ∞ (smoothPairError n r : (ι → ℝ) → ℝ) := by
  have hW := smoothUtilityRange_contDiff (ι:=ι)
  have hQ : ContDiff ℝ ∞ (fun u : ι → ℝ =>
      rangeExponent n ((r/Real.sqrt (1-r^2))*smoothUtilityRange u)) := by
    unfold rangeExponent
    fun_prop
  exact (contDiff_const.add hQ).mul hQ.exp

theorem smoothPairError_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (r : ℝ) (hr : 0<r) (hr1 : r<1) (u : ι → ℝ) :
    0 ≤ smoothPairError n r u := by
  have hs := NegativeVotingRegularOU.negative_noise_scale_pos r hr hr1
  have hQ := rangeExponent_nonneg n _ (mul_nonneg (div_pos hr hs).le (smoothUtilityRange_nonneg u))
  unfold smoothPairError
  positivity

theorem negativePairCoefficient_error_le {n d : ℕ} (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hrhalf : r ≤ 1/2) (x : FSC.Coord d)
    (i j : Fin (n+2)) (hij : i≠j) :
    |1-negativePairCoefficient B r x i j| ≤ smoothPairError n r (scoreOffsets B x) := by
  have hr1 : r<1 := by linarith
  have hs := NegativeVotingRegularOU.negative_noise_scale_pos r hr hr1
  have hτ : 0 ≤ r/Real.sqrt (1-r^2) := (div_pos hr hs).le
  have hq := rangeExponent_mono n _ _
    (mul_nonneg hτ (utilityRange_nonneg (scoreOffsets B x)))
    (mul_le_mul_of_nonneg_left (utilityRange_le_smooth (scoreOffsets B x)) hτ)
  have hk := negativePairCoefficient_range_bounds hn hmean B hG r hr hr1 x i j hij
  have hp := noise_prefactor_bounds r hr hrhalf
  have hinv := (inv_pos.mpr hs).le
  have hQ := rangeExponent_nonneg n _ (mul_nonneg hτ (smoothUtilityRange_nonneg (scoreOffsets B x)))
  apply scalar_pair_error _ _ (2*r^2) _ (by positivity) hQ hp.1 hp.2
  constructor
  · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hq)) hinv).trans hk.1
  · exact hk.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hq) hinv)

theorem smoothPairError_scores_contDiff {n d : ℕ}
    (B : Fin (n+2) → FSC.Coord d) (r : ℝ) :
    ContDiff ℝ ∞ (fun x => smoothPairError n r (scoreOffsets B x)) := by
  apply (smoothPairError_contDiff n r).comp
  apply contDiff_pi.mpr
  intro i
  exact (innerSL ℝ (B i)).contDiff

end NegativeVotingRegularPairCoefficient
