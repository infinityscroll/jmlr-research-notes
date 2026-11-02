import GaussianCompleteGraphComponentInverse
import Mathlib.Analysis.Calculus.MeanValue

/-! A summed Taylor remainder from a summed acceleration bound. The signs
are frozen at the endpoint, avoiding a separate mean-value point per label. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped BigOperators Classical
namespace NegativeVotingSummedTaylorRemainder
open NegativeVotingCompleteGraphComponentInverse

lemma scalar_second_remainder_le (f f₁ f₂ : ℝ→ℝ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hfirst : ∀t∈Icc 0 T,HasDerivAt f (f₁ t) t)
    (hsecond : ∀t∈Icc 0 T,HasDerivAt f₁ (f₂ t) t)
    (hbound : ∀t∈Icc 0 T,|f₂ t| ≤ B) :
    |f T-f 0-T*f₁ 0| ≤ B*T^2 := by
  have hvel:=norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht=>(hsecond t ht).hasDerivWithinAt)
    (fun t ht=>by simpa only [Real.norm_eq_abs] using hbound t (Ico_subset_Icc_self ht))
  have hg (t:ℝ) (ht:t∈Icc 0 T) :
      HasDerivAt (fun s=>f s-f 0-s*f₁ 0) (f₁ t-f₁ 0) t := by
    convert ((hfirst t ht).sub_const (f 0)).sub ((hasDerivAt_id t).mul_const (f₁ 0)) using 1 <;> simp [Pi.sub_def]
  have hgb (t:ℝ) (ht:t∈Ico 0 T) : ‖f₁ t-f₁ 0‖ ≤ B*T := by
    have hh:=hvel t (Ico_subset_Icc_self ht)
    simp only [sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ht.2.le hB)
  have hh:=norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hgb T ⟨hT,le_rfl⟩
  simpa only [sub_self,zero_mul,sub_zero,Real.norm_eq_abs,pow_two,mul_assoc] using hh

variable {V : Type*} [Fintype V]

lemma signedUnit_abs (x : ℝ) : |signedUnit x|=1 := by
  unfold signedUnit
  split_ifs <;> norm_num

/-- No continuity of the second derivatives is required. Actual derivatives
exist at every point of the closed interval, and only their L1 sum is bounded. -/
theorem summed_second_remainder_le (f f₁ f₂ : V→ℝ→ℝ) (T B : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hfirst : ∀i t,t∈Icc 0 T → HasDerivAt (f i) (f₁ i t) t)
    (hsecond : ∀i t,t∈Icc 0 T → HasDerivAt (f₁ i) (f₂ i t) t)
    (hbound : ∀t∈Icc 0 T,(∑i,|f₂ i t|) ≤ B) :
    (∑i,|f i T-f i 0-T*f₁ i 0|) ≤ B*T^2 := by
  let s:V→ℝ:=fun i=>signedUnit (f i T-f i 0-T*f₁ i 0)
  let F:ℝ→ℝ:=fun t=>∑i,s i*f i t
  let F₁:ℝ→ℝ:=fun t=>∑i,s i*f₁ i t
  let F₂:ℝ→ℝ:=fun t=>∑i,s i*f₂ i t
  have hF (t:ℝ) (ht:t∈Icc 0 T):HasDerivAt F (F₁ t) t:=
    HasDerivAt.fun_sum (u:=Finset.univ) fun i _=>(hfirst i t ht).const_mul (s i)
  have hF₁ (t:ℝ) (ht:t∈Icc 0 T):HasDerivAt F₁ (F₂ t) t:=
    HasDerivAt.fun_sum (u:=Finset.univ) fun i _=>(hsecond i t ht).const_mul (s i)
  have hF₂ (t:ℝ) (ht:t∈Icc 0 T):|F₂ t| ≤ B:=by
    have hh:=Finset.abs_sum_le_sum_abs (fun i=>s i*f₂ i t) Finset.univ
    simp only [abs_mul,s,signedUnit_abs,one_mul] at hh
    exact hh.trans (hbound t ht)
  have hscalar:=scalar_second_remainder_le F F₁ F₂ T B hT hB hF hF₁ hF₂
  have he:F T-F 0-T*F₁ 0=∑i,|f i T-f i 0-T*f₁ i 0|:=by
    simp only [F,F₁,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = s i*(f i T-f i 0-T*f₁ i 0):=by ring
      _ = _:=signedUnit_mul_self _
  rw [he,abs_of_nonneg (Finset.sum_nonneg fun i _=>abs_nonneg _)] at hscalar
  exact hscalar

end NegativeVotingSummedTaylorRemainder
