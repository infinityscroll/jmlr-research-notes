import GaussianSwitchingLpCap

/-! Finite label aggregation for the actual Lq switching estimate.
The near term pays only m^(1/(q+1)); the far term pays no label factor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
namespace NegativeVotingSwitchingLabelSum
open NegativeVotingSwitchingLp
variable {V : Type*} [Fintype V]

theorem sum_fractional_power_le (W : V → ℝ) (hW : ∀ i, 0 ≤ W i)
    (q : ℝ) (hq : 0 < q) :
    (∑ i, (W i)^(2*q/(q+1))) ≤
      (Fintype.card V:ℝ)^(1/(q+1)) * (∑ i, (W i)^2)^(q/(q+1)) := by
  have hqp : 0 < q+1 := by linarith
  have hc : ((q+1)/q).HolderConjugate (q+1) := by
    rw [Real.holderConjugate_iff]
    constructor
    · apply (lt_div_iff₀ hq).mpr
      linarith
    · field_simp
  have hh := Real.inner_le_Lp_mul_Lq Finset.univ
    (fun i => (W i)^(2*q/(q+1))) (fun _ => 1) hc
  have he : (∑ i, |(W i)^(2*q/(q+1))|^((q+1)/q)) = ∑ i, (W i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonneg (Real.rpow_nonneg (hW i) _), ←Real.rpow_mul (hW i)]
    have hexp : 2*q/(q+1)*((q+1)/q)=(2:ℝ) := by field_simp
    rw [hexp,Real.rpow_two]
  rw [he] at hh
  have hinv : 1/((q+1)/q)=q/(q+1) := by field_simp
  simpa only [mul_one,abs_one,Real.one_rpow,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,hinv,mul_comm,one_mul] using hh

theorem sum_large_power_le (W : V → ℝ) (hW : ∀ i, 0 ≤ W i)
    (q : ℝ) (hq : 2 ≤ q) :
    (∑ i, (W i)^q) ≤ (∑ i, (W i)^2)^(q/2) := by
  let S := ∑ i, (W i)^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rcases hS.eq_or_lt with hS | hS
  · have hzero (i : V) : W i=0 := by
      have hi := Finset.single_le_sum (s:=Finset.univ) (f:=fun i => (W i)^2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      change (W i)^2 ≤ S at hi
      nlinarith
    simp only [hzero, Real.zero_rpow (by linarith : q≠0), Finset.sum_const_zero,
      zero_pow (by decide : (2:ℕ)≠0), Real.zero_rpow (by linarith : q/2≠0), le_refl]
  · have hp (i : V) : (W i)^q ≤ (W i)^2 * S^((q-2)/2) := by
      have hi : (W i)^2 ≤ S := Finset.single_le_sum
        (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      have hb := Real.rpow_le_rpow (sq_nonneg (W i)) hi (by linarith : 0≤(q-2)/2)
      have he : ((W i)^2)^((q-2)/2)=(W i)^(q-2) := by
        rw [←Real.rpow_two, ←Real.rpow_mul (hW i)]
        congr 1
        ring
      rw [he] at hb
      have hadd : (W i)^2*(W i)^(q-2)=(W i)^q := by
        by_cases hw0 : W i=0
        · simp [hw0,Real.zero_rpow (by linarith : q≠0)]
        · have hwpos : 0<W i := lt_of_le_of_ne (hW i) (Ne.symm hw0)
          rw [←Real.rpow_two, ←Real.rpow_add hwpos]
          congr 1
          ring
      simpa only [hadd] using mul_le_mul_of_nonneg_left hb (sq_nonneg (W i))
    calc
      _ ≤ ∑ i, (W i)^2 * S^((q-2)/2) := Finset.sum_le_sum (fun i _ => hp i)
      _ = S*S^((q-2)/2) := by rw [←Finset.sum_mul]
      _ = S^(q/2) := by
        have he : (1:ℝ)+(q-2)/2=q/2 := by ring
        simpa only [Real.rpow_one,he] using (Real.rpow_add hS 1 ((q-2)/2)).symm

/-- This is an estimate for actual integrals over separate finite measures,
as needed for the source cells and target complements. -/
theorem sum_integral_reward_lq {X : Type*} [MeasurableSpace X]
    (μ : V → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (v c : V → X → ℝ) (W : V → ℝ) (q aStar C R : ℝ)
    (hq : 2 ≤ q) (haStar : 0<aStar) (hC : 1≤C) (hW : ∀ i, 0≤W i)
    (hR : 0≤R) (henergy : (∑ i, (W i)^2) ≤ R^2)
    (hv : ∀ i, MemLp (v i) (ENNReal.ofReal q) (μ i))
    (hcM : ∀ i, Measurable (c i)) (hc : ∀ i x, 0≤c i x)
    (hsub : ∀ i a, 0<a → a≤aStar → ((μ i) {x | c i x≤a}).toReal≤C*a)
    (hnorm : ∀ i, eLpNorm (v i) (ENNReal.ofReal q) (μ i)≤ENNReal.ofReal (W i)) :
    (∑ i, ∫ x, max (v i x-c i x) 0 ∂μ i) ≤
      (C+1)*(Fintype.card V:ℝ)^(1/(q+1))*R^(2*q/(q+1)) + R^q/aStar^(q-1) := by
  have hq0 : 0<q := by linarith
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    integral_reward_lq (v i) (c i) q aStar C (W i) hq haStar hC (hW i)
      (hv i) (hcM i) (hc i) (hsub i) (hnorm i))
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_div] at hs
  have hnear := (sum_fractional_power_le W hW q hq0).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => sq_nonneg _) henergy (by positivity))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤Fintype.card V) _))
  have hfar := (sum_large_power_le W hW q hq).trans
    (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => sq_nonneg _) henergy (by positivity))
  have hn : (R^2)^(q/(q+1))=R^(2*q/(q+1)) := by
    rw [←Real.rpow_two, ←Real.rpow_mul hR]
    congr 1
    ring
  have hf : (R^2)^(q/2)=R^q := by
    rw [←Real.rpow_two, ←Real.rpow_mul hR]
    congr 1
    ring
  rw [hn] at hnear
  rw [hf] at hfar
  exact hs.trans (by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hnear (by linarith : 0≤C+1))
      (div_le_div_of_nonneg_right hfar (by positivity : 0≤aStar^(q-1)))
    simpa only [mul_assoc] using hh)

end NegativeVotingSwitchingLabelSum
