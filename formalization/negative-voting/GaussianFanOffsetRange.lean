import GaussianFanRetainedCoefficient

/-! Actual positive Gaussian winning-cell masses control all affine offsets
and, after centering, each individual offset. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace BigOperators
namespace NegativeVotingConditionedFacet
open NegativeVotingFan NegativeVotingFanRetained NegativeVotingWeightedFacet
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def offsetRadius (D : ℝ) : ℝ := D*Real.sqrt (2*Real.log (2*(Fintype.card V : ℝ)))

theorem offsetRadius_nonneg (D : ℝ) (hD : 0 ≤ D) :
    0 ≤ offsetRadius (V:=V) D := mul_nonneg hD (Real.sqrt_nonneg _)

theorem pair_offset_difference_le (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀i j,‖B i-B j‖ ≤ D)
    (hmass : ∀i,1/(2*(Fintype.card V : ℝ)) ≤ mass B h i) (i j : V) :
    |h i-h j| ≤ offsetRadius (V:=V) D := by
  by_cases hij : i=j
  · subst j
    simpa only [sub_self,abs_zero] using offsetRadius_nonneg (V:=V) D hD
  have hm : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hm1 : (1:ℝ) ≤ Fintype.card V := by exact_mod_cast (Nat.succ_le_of_lt Fintype.card_pos)
  have hp : 0 < 1/(2*(Fintype.card V : ℝ)) := by positivity
  have hq := pairOffset_sq_le_log_mass B h hinj _ hp hmass i j hij
  rw [one_div_one_div] at hq
  have hlog : 0 ≤ 2*Real.log (2*(Fintype.card V : ℝ)) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hqa : |pairOffset B h i j| ≤ Real.sqrt (2*Real.log (2*(Fintype.card V : ℝ))) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt hlog]
    exact hq
  have he : h j-h i=pairOffset B h i j*‖B i-B j‖ := by
    have hn : ‖B i-B j‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hinj.ne hij))
    unfold pairOffset
    field_simp
  rw [abs_sub_comm,he,abs_mul,abs_norm]
  calc
    |pairOffset B h i j| *‖B i-B j‖ ≤
        Real.sqrt (2*Real.log (2*(Fintype.card V : ℝ)))*D :=
      mul_le_mul hqa (hrow i j) (norm_nonneg _) (Real.sqrt_nonneg _)
    _=offsetRadius (V:=V) D := by unfold offsetRadius;ring

theorem centered_offset_abs_le_pair_range (h : V → ℝ) (hs : ∑i,h i=0)
    (H : ℝ) (hpair : ∀i j,|h i-h j| ≤ H) (i : V) : |h i| ≤ H := by
  have hm : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have he : ∑j : V,(h i-h j)=(Fintype.card V : ℝ)*h i := by
    rw [Finset.sum_sub_distrib,hs]
    simp
  have hh : (Fintype.card V : ℝ)*|h i| ≤ (Fintype.card V : ℝ)*H := by
    calc
      (Fintype.card V : ℝ)*|h i|=|∑j : V,(h i-h j)| := by
        rw [he,abs_mul,abs_of_pos hm]
      _ ≤ ∑j : V,|h i-h j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_j : V,H := Finset.sum_le_sum fun j _ => hpair i j
      _=(Fintype.card V : ℝ)*H := by simp
  exact (mul_le_mul_iff_right₀ hm).mp hh

theorem centered_offsets_le_of_cell_masses (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (D : ℝ) (hD : 0 ≤ D)
    (hrow : ∀i j,‖B i-B j‖ ≤ D) (hs : ∑i,h i=0)
    (hmass : ∀i,1/(2*(Fintype.card V : ℝ)) ≤ mass B h i) (i : V) :
    |h i| ≤ offsetRadius (V:=V) D :=
  centered_offset_abs_le_pair_range h hs _ (pair_offset_difference_le B h hinj D hD hrow hmass) i

end NegativeVotingConditionedFacet
