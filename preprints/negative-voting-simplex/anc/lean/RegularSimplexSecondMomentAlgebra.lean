import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-! Finite tensor algebra forced by the stabilizer of one simplex label. -/
noncomputable section
open scoped BigOperators
namespace NegativeVotingRegularSecondAlgebra

private theorem sum_one_special {m : ℕ} (i : Fin m) (f : Fin m → ℝ) (c : ℝ)
    (hc : ∀ j, j ≠ i → f j=c) :
    (∑ j, f j)=f i+((m:ℝ)-1)*c := by
  have hm : 1 ≤ m := by have hi := i.isLt; omega
  have hs : (∑ j ∈ Finset.univ.erase i, f j)=((m:ℝ)-1)*c := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, c :=
        Finset.sum_congr rfl (fun j hj => hc j (Finset.mem_erase.mp hj).1)
      _ = _ := by simp [Finset.card_erase_of_mem,Nat.cast_sub hm,nsmul_eq_mul]
  have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  rw [hs] at hsplit
  linarith

private theorem sum_two_special {m : ℕ} (hm : 2 ≤ m) (i a : Fin m) (hia : i ≠ a)
    (f : Fin m → ℝ) (c : ℝ) (hc : ∀ j, j ≠ i → j ≠ a → f j=c) :
    (∑ j, f j)=f i+f a+((m:ℝ)-2)*c := by
  let s := (Finset.univ.erase i).erase a
  have ha : a ∈ Finset.univ.erase i := by simp [hia.symm]
  have hcard : s.card=m-2 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem ha,Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp [Nat.sub_sub]
  have hsum : (∑ j ∈ s, f j)=((m:ℝ)-2)*c := by
    calc
      _ = ∑ j ∈ s, c := by
        apply Finset.sum_congr rfl
        intro j hj
        have ha' := (Finset.mem_erase.mp hj).1
        have hi' := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        exact hc j hi' ha'
      _ = _ := by simp [hcard,Nat.cast_sub hm,nsmul_eq_mul]
  have h1 := Finset.sum_erase_add (Finset.univ.erase i) f ha
  have h2 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  change (∑ j ∈ s, f j)+f a=∑ j ∈ Finset.univ.erase i, f j at h1
  rw [hsum] at h1
  linarith

/-- Symmetry, zero trace and row sums, and the actual label stabilizer determine
the entire quadratic tensor. No unproved orbit-classification input is used. -/
theorem frobenius_sq_of_stabilizer {m : ℕ} (hm : 3 ≤ m) (i : Fin m)
    (q : Fin m → Fin m → ℝ) (hsym : ∀ a b, q a b=q b a)
    (hrow : ∀ a, ∑ b, q a b=0) (htrace : ∑ a, q a a=0)
    (hinv : ∀ a b, a ≠ i → b ≠ i → ∀ j k,
      q (Equiv.swap a b j) (Equiv.swap a b k)=q j k) :
    (∑ a, ∑ b, (q a b)^2)=(m:ℝ)^2*(q i i)^2/(((m:ℝ)-1)*((m:ℝ)-2)) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (m:ℝ)-1 ≠ 0 := by linarith
  have h2 : (m:ℝ)-2 ≠ 0 := by linarith
  have hdiag_const (a b : Fin m) (ha : a ≠ i) (hb : b ≠ i) : q a a=q b b := by
    simpa only [Equiv.swap_apply_left] using (hinv a b ha hb a a).symm
  have hrow_const (a b : Fin m) (ha : a ≠ i) (hb : b ≠ i) : q i a=q i b := by
    simpa only [Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm,Equiv.swap_apply_left]
      using (hinv a b ha hb i a).symm
  have hdiag (a : Fin m) (ha : a ≠ i) : q a a= -q i i/((m:ℝ)-1) := by
    have he := sum_one_special i (fun k => q k k) (q a a)
      (fun k hk => hdiag_const k a hk ha)
    rw [htrace] at he
    apply (eq_div_iff h1).mpr
    nlinarith
  have hrowi (a : Fin m) (ha : a ≠ i) : q i a= -q i i/((m:ℝ)-1) := by
    have he := sum_one_special i (fun k => q i k) (q i a)
      (fun k hk => hrow_const k a hk ha)
    rw [hrow i] at he
    apply (eq_div_iff h1).mpr
    nlinarith
  have hoff (a b : Fin m) (ha : a ≠ i) (hb : b ≠ i) (hab : a ≠ b) :
      q a b=2*q i i/(((m:ℝ)-1)*((m:ℝ)-2)) := by
    have hc (k : Fin m) (hk : k ≠ i) (hka : k ≠ a) : q a k=q a b := by
      simpa only [Equiv.swap_apply_of_ne_of_ne hab hka.symm,Equiv.swap_apply_left]
        using hinv b k hb hk a b
    have he := sum_two_special (by omega : 2 ≤ m) i a ha.symm (fun k => q a k) (q a b) hc
    rw [hrow a,hdiag a ha,hsym a i,hrowi a ha] at he
    apply (eq_div_iff (mul_ne_zero h1 h2)).mpr
    field_simp [h1] at he
    nlinarith
  have hri : (∑ k, (q i k)^2)=(q i i)^2+((m:ℝ)-1)*(-q i i/((m:ℝ)-1))^2 := by
    apply sum_one_special
    intro k hk
    rw [hrowi k hk]
  have hra (a : Fin m) (ha : a ≠ i) : (∑ k, (q a k)^2)=
      2*(-q i i/((m:ℝ)-1))^2+((m:ℝ)-2)*(2*q i i/(((m:ℝ)-1)*((m:ℝ)-2)))^2 := by
    have he := sum_two_special (by omega : 2 ≤ m) i a ha.symm (fun k => (q a k)^2)
      ((2*q i i/(((m:ℝ)-1)*((m:ℝ)-2)))^2)
      (fun k hk hka => by rw [hoff a k ha hk hka.symm])
    rw [hdiag a ha,hsym a i,hrowi a ha] at he
    rw [he]
    ring
  rw [sum_one_special i (fun a => ∑ b, (q a b)^2) _ hra,hri]
  field_simp [h1,h2]
  <;> ring

end NegativeVotingRegularSecondAlgebra
