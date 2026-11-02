import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite signed-square and weighted Cauchy conversion from genuine L1
coarea comparison to a counting-measure spectral gap. -/
noncomputable section
open scoped BigOperators
namespace NegativeVotingFiniteGraphRayleigh

/-- The signed square separates two real numbers quadratically. -/
theorem signedSquare_difference_lower (a b : ℝ) :
    (a-b)^2 ≤ 2*abs (a * abs a - b * abs b) := by
  have ho (a b : ℝ) (hab : b ≤ a) : (a-b)^2 ≤ 2*(a*abs a-b*abs b) := by
    by_cases hb : 0 ≤ b
    · have ha : 0 ≤ a := hb.trans hab
      rw [abs_of_nonneg ha,abs_of_nonneg hb]
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ a+3*b by linarith)]
    · by_cases ha : 0 ≤ a
      · rw [abs_of_nonneg ha,abs_of_nonpos (le_of_not_ge hb)]
        nlinarith [sq_nonneg (a+b)]
      · rw [abs_of_nonpos (le_of_not_ge ha),abs_of_nonpos (le_of_not_ge hb)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ -(3*a+b) by linarith)]
  rcases le_total b a with h | h
  · exact (ho a b h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
  · have hh := ho b a h
    nlinarith [neg_le_abs (a*abs a-b*abs b)]

theorem signedSquare_difference_upper (a b : ℝ) :
    abs (a * abs a - b * abs b) ≤ abs (a-b)*(abs a+abs b) := by
  calc
    _ = |(a-b)*abs a+b*(abs a-abs b)| := by congr 1; ring
    _ ≤ abs (a-b)*abs a+abs b*abs (abs a - abs b) := by
      simpa only [abs_mul,abs_abs] using abs_add_le ((a-b)*abs a) (b*(abs a-abs b))
    _ ≤ abs (a-b)*abs a+abs b*abs (a-b) := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (abs_abs_sub_abs_le_abs_sub a b) (abs_nonneg b))
    _ = _ := by ring

variable {V : Type*} [Fintype V] [Nonempty V]

theorem centered_pair_energy (v : V → ℝ) (hv : ∑ i, v i=0) :
    (∑ i, ∑ j, (v i-v j)^2)=2*(Fintype.card V:ℝ)*(∑ i, (v i)^2) := by
  have hi (i : V) : (∑ j, (v i-v j)^2)=(Fintype.card V:ℝ)*(v i)^2+∑ j, (v j)^2 := by
    simp_rw [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hv]
    simp [nsmul_eq_mul]
  simp_rw [hi,Finset.sum_add_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

/-- Weighted Cauchy is applied to the genuine edge weights, including zeros. -/
theorem weighted_difference_cauchy (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j) (v : V → ℝ) :
    (∑ i, ∑ j, w i j*abs (v i-v j)*(abs (v i)+abs (v j)))^2 ≤
      (∑ i, ∑ j, w i j*(v i-v j)^2)*(∑ i, ∑ j, w i j*(abs (v i)+abs (v j))^2) := by
  let f : V×V → ℝ := fun p => Real.sqrt (w p.1 p.2)*abs (v p.1-v p.2)
  let g : V×V → ℝ := fun p => Real.sqrt (w p.1 p.2)*(abs (v p.1)+abs (v p.2))
  have hm (p : V×V) : f p*g p=w p.1 p.2*abs (v p.1-v p.2)*(abs (v p.1)+abs (v p.2)) := by
    dsimp [f,g]
    calc
      _ = (Real.sqrt (w p.1 p.2))^2*abs (v p.1-v p.2)*(abs (v p.1)+abs (v p.2)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw p.1 p.2)]
  have hf (p : V×V) : (f p)^2=w p.1 p.2*(v p.1-v p.2)^2 := by
    dsimp [f]
    rw [mul_pow,Real.sq_sqrt (hw p.1 p.2),sq_abs]
  have hg (p : V×V) : (g p)^2=w p.1 p.2*(abs (v p.1)+abs (v p.2))^2 := by
    dsimp [g]
    rw [mul_pow,Real.sq_sqrt (hw p.1 p.2)]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simp_rw [hm,hf,hg,Fintype.sum_prod_type] at hc
  exact hc

/-- The weighted degree controls the second Cauchy factor. -/
theorem absolute_pair_energy_le_degree (w : V → V → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hsym : ∀ i j, w i j=w j i)
    (D : ℝ) (hD : ∀ i, ∑ j, w i j ≤ D) (v : V → ℝ) :
    (∑ i, ∑ j, w i j*(abs (v i)+abs (v j))^2) ≤ 4*D*(∑ i, (v i)^2) := by
  have hp (i j : V) : (abs (v i)+abs (v j))^2 ≤ 2*(v i)^2+2*(v j)^2 := by
    nlinarith [sq_nonneg (abs (v i)-abs (v j)),sq_abs (v i),sq_abs (v j)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hp i j) (hw i j)))
  have hr : (∑ i, ∑ j, w i j*(v i)^2) ≤ D*(∑ i, (v i)^2) := by
    simp_rw [← Finset.sum_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hD i) (sq_nonneg _)
  have hc : (∑ i, ∑ j, w i j*(v j)^2)=(∑ i, ∑ j, w i j*(v i)^2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have he : (∑ i, ∑ j, w i j*(2*(v i)^2+2*(v j)^2))=
      2*(∑ i, ∑ j, w i j*(v i)^2)+2*(∑ i, ∑ j, w i j*(v j)^2) := by
    have hp' (i j : V) : w i j*(2*(v i)^2+2*(v j)^2)=
        2*(w i j*(v i)^2)+2*(w i j*(v j)^2) := by ring
    simp_rw [hp',Finset.sum_add_distrib,← Finset.mul_sum]
  rw [he,hc] at hs
  linarith

/-- The finite L1 comparison implies the stated quantitative centered spectral gap. -/
theorem rayleigh_of_ordered_l1 (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hsym : ∀ i j, w i j=w j i) (k D : ℝ) (hk : 0 ≤ k)
    (hD : ∀ i, ∑ j, w i j ≤ D)
    (hL1 : ∀ g : V → ℝ,
      (k/(Fintype.card V:ℝ))*(∑ i, ∑ j, |g i-g j|) ≤ ∑ i, ∑ j, w i j*|g i-g j|)
    (v : V → ℝ) (hv : ∑ i, v i=0) :
    k^2*(∑ i, (v i)^2) ≤ 8*D*((1/2:ℝ)*∑ i, ∑ j, w i j*(v i-v j)^2) := by
  let S : ℝ := ∑ i, (v i)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  let g : V → ℝ := fun i => v i*abs (v i)
  have hp := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => signedSquare_difference_lower (v i) (v j)))
  rw [centered_pair_energy v hv] at hp
  simp_rw [← Finset.mul_sum] at hp
  have hp' : (Fintype.card V:ℝ)*S ≤ ∑ i, ∑ j, |g i-g j| := by
    dsimp [g,S]
    linarith
  have hl : k*S ≤ ∑ i, ∑ j, w i j*|g i-g j| := by
    calc
      _ = (k/(Fintype.card V:ℝ))*((Fintype.card V:ℝ)*S) := by field_simp [ne_of_gt hm]
      _ ≤ (k/(Fintype.card V:ℝ))*(∑ i, ∑ j, |g i-g j|) :=
        mul_le_mul_of_nonneg_left hp' (div_nonneg hk hm.le)
      _ ≤ _ := hL1 g
  have hu : (∑ i, ∑ j, w i j*|g i-g j|) ≤
      ∑ i, ∑ j, w i j*abs (v i-v j)*(abs (v i)+abs (v j)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left
      (signedSquare_difference_upper (v i) (v j)) (hw i j)
  have hE : 0 ≤ ∑ i, ∑ j, w i j*(v i-v j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (sq_nonneg _)
  have hR := hl.trans hu
  have hsq := (sq_le_sq₀ (mul_nonneg hk hS) ((mul_nonneg hk hS).trans hR)).mpr hR
  have hc := weighted_difference_cauchy w hw v
  have hb := mul_le_mul_of_nonneg_left (absolute_pair_energy_le_degree w hw hsym D hD v) hE
  have hfinal := hsq.trans (hc.trans hb)
  by_cases hz : S=0
  · change k^2*S ≤ _
    rw [hz,mul_zero]
    have hD0 : 0 ≤ D := (Finset.sum_nonneg fun j _ => hw (Classical.choice inferInstance) j).trans
      (hD (Classical.choice inferInstance))
    positivity
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    have hmul : (k^2*S)*S ≤ (8*D*((1/2:ℝ)*∑ i, ∑ j, w i j*(v i-v j)^2))*S := by
      change (k*S)^2 ≤ (∑ i, ∑ j, w i j*(v i-v j)^2)*(4*D*S) at hfinal
      convert hfinal using 1 <;> ring
    apply (mul_le_mul_iff_right₀ hSpos).mp
    convert hmul using 1 <;> ring

/-- Spectral-gap normalization matching the ordered Gaussian edge form. -/
theorem rayleigh_coefficient_of_ordered_l1 (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hsym : ∀ i j, w i j=w j i) (k D : ℝ) (hk : 0 ≤ k) (hDpos : 0 < D)
    (hD : ∀ i, ∑ j, w i j ≤ D)
    (hL1 : ∀ g : V → ℝ,
      (k/(Fintype.card V:ℝ))*(∑ i, ∑ j, |g i-g j|) ≤ ∑ i, ∑ j, w i j*|g i-g j|)
    (v : V → ℝ) (hv : ∑ i, v i=0) :
    (k^2/(8*D))*(∑ i, (v i)^2) ≤ (1/2:ℝ)*∑ i, ∑ j, w i j*(v i-v j)^2 := by
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 8) hDpos)).mpr
  have he := rayleigh_of_ordered_l1 w hw hsym k D hk hD hL1 v hv
  convert he using 1 <;> ring

end NegativeVotingFiniteGraphRayleigh
