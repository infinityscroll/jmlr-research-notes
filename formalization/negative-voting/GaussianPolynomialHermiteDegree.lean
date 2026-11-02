import GaussianFiniteHermiteInverseOU

/-! Actual pointwise degree bounds for finite products of affine scores. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open NegativeVotingModern NegativeVotingProjection NegativeVotingFiniteHermite
open scoped BigOperators Classical

namespace NegativeVotingPolynomialDegree
variable {κ : Type*} [Fintype κ]

def rawPsi (a : κ → ℕ) (x : κ → ℝ) : ℝ := ∏ i, he (a i) (x i)

def polynomialSpace (k : ℕ) : Submodule ℝ ((κ → ℝ) → ℝ) :=
  Submodule.span ℝ ((rawPsi (κ := κ)) '' {a | degree a ≤ k})

theorem rawPsi_mem {a : κ → ℕ} {k : ℕ} (ha : degree a ≤ k) :
    rawPsi a ∈ polynomialSpace k := by
  change rawPsi a ∈ Submodule.span ℝ _
  exact Submodule.subset_span ⟨a, ha, rfl⟩

theorem polynomialSpace_mono {j k : ℕ} (h : j ≤ k) :
    polynomialSpace (κ := κ) j ≤ polynomialSpace k := by
  unfold polynomialSpace
  apply Submodule.span_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, ha.trans h, rfl⟩

theorem coordinate_he (n : ℕ) (x : ℝ) :
    x * he n x = he (n+1) x + (n:ℝ) * he (n-1) x := by
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add,
      Nat.cast_one] using (show x * he (n+1) x = he (n+2) x + (n+1:ℝ) * he n x by
        rw [he_recurrence]; ring)

theorem rawPsi_update (a : κ → ℕ) (i : κ) (n : ℕ) (x : κ → ℝ) :
    rawPsi (Function.update a i n) x = he n (x i) *
      ∏ j ∈ Finset.univ.erase i, he (a j) (x j) := by
  classical
  unfold rawPsi
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem coordinate_rawPsi (a : κ → ℕ) (i : κ) :
    (fun x => x i * rawPsi a x) = rawPsi (Function.update a i (a i+1)) +
      (a i : ℝ) • rawPsi (Function.update a i (a i-1)) := by
  classical
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rawPsi_update]
  rw [rawPsi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [← mul_assoc, coordinate_he]
  ring

theorem degree_update_succ (a : κ → ℕ) (i : κ) :
    degree (Function.update a i (a i+1)) = degree a+1 := by
  classical
  unfold degree
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
    Function.update_self]
  have he : (∑ j ∈ Finset.univ.erase i, Function.update a i (a i+1) j) =
      ∑ j ∈ Finset.univ.erase i, a j :=
    Finset.sum_congr rfl (fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)
  rw [he, ← Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)]
  omega

theorem degree_update_pred_le (a : κ → ℕ) (i : κ) :
    degree (Function.update a i (a i-1)) ≤ degree a := by
  classical
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : j=i
  · subst j; simp
  · simp [Function.update_of_ne h]

theorem coordinate_mul_mem {k : ℕ} {f : (κ → ℝ) → ℝ}
    (hf : f ∈ polynomialSpace k) (i : κ) :
    (fun x => x i * f x) ∈ polynomialSpace (k+1) := by
  classical
  change f ∈ Submodule.span ℝ _ at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, ha, rfl⟩
      have hd : degree a ≤ k := ha
      rw [coordinate_rawPsi]
      exact (polynomialSpace (k+1)).add_mem
        (rawPsi_mem (by rw [degree_update_succ]; omega))
        ((polynomialSpace (k+1)).smul_mem _
          (rawPsi_mem ((degree_update_pred_le a i).trans (by omega))))
  | zero =>
      convert (polynomialSpace (κ := κ) (k+1)).zero_mem using 1
      ext x; simp
  | add f g hf hg ihf ihg =>
      convert (polynomialSpace (k+1)).add_mem ihf ihg using 1
      ext x; simp only [Pi.add_apply, mul_add]
  | smul c f hf ih =>
      convert (polynomialSpace (k+1)).smul_mem c ih using 1
      ext x; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem one_mem (k : ℕ) : (fun _ : κ → ℝ => (1:ℝ)) ∈ polynomialSpace k := by
  have he : rawPsi (fun _ : κ => 0) = (fun _ => (1:ℝ)) := by
    ext x; simp [rawPsi]
  rw [← he]
  exact rawPsi_mem (by simp [degree])

def affineFunction (l : κ → ℝ) (c : ℝ) (x : κ → ℝ) : ℝ := c + ∑ i, l i * x i

theorem affine_mul_mem {k : ℕ} {f : (κ → ℝ) → ℝ}
    (hf : f ∈ polynomialSpace k) (l : κ → ℝ) (c : ℝ) :
    (fun x => affineFunction l c x * f x) ∈ polynomialSpace (k+1) := by
  have h1 := (polynomialSpace (k+1)).smul_mem c
    (polynomialSpace_mono (Nat.le_succ k) hf)
  have h2 := (polynomialSpace (k+1)).sum_mem (fun i (_ : i ∈ Finset.univ) =>
    (polynomialSpace (k+1)).smul_mem (l i) (coordinate_mul_mem hf i))
  convert (polynomialSpace (k+1)).add_mem h1 h2 using 1
  ext x
  simp only [affineFunction, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    add_mul, Finset.sum_mul, mul_assoc]

theorem affine_product_mem {ι : Type*} (S : Finset ι) (l : ι → κ → ℝ) (c : ι → ℝ) :
    (fun x => ∏ i ∈ S, affineFunction (l i) (c i) x) ∈ polynomialSpace S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using one_mem (κ := κ) 0
  | @insert i S hi ih =>
      simpa only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi] using
        affine_mul_mem ih (l i) (c i)

theorem rawPsi_eq_normalized (a : κ → ℕ) :
    rawPsi a = (∏ i, Real.sqrt ((a i).factorial : ℝ)) • psi a := by
  funext x
  simp only [rawPsi, Pi.smul_apply, smul_eq_mul, psi, ← Finset.prod_mul_distrib, H]
  apply Finset.prod_congr rfl
  intro i hi
  field_simp [ne_of_gt (sqrt_factorial_pos (a i))]

/-- Algebraic membership supplies an exact finite expansion at every point. -/
theorem exists_normalized_expansion {k : ℕ} {f : (κ → ℝ) → ℝ}
    (hf : f ∈ polynomialSpace k) :
    ∃ c : (κ → ℕ) → ℝ, f = hermiteSum (lowerModes (k+1)) c := by
  classical
  have hin : polynomialSpace (κ := κ) k ≤
      Submodule.span ℝ ((psi (ι := κ)) '' {a | degree a ≤ k}) := by
    unfold polynomialSpace
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    rw [rawPsi_eq_normalized]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a,ha,rfl⟩)
  have hset : {a : κ → ℕ | degree a ≤ k} =
      (lowerModes (κ := κ) (k+1) : Set (κ → ℕ)) := by
    ext a; simp [mem_lowerModes_iff, Nat.lt_succ_iff]
  have hh := hin hf
  rw [hset] at hh
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℝ).mp hh
  refine ⟨c, ?_⟩
  ext x
  simpa only [hermiteSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (congrFun hc x).symm

end NegativeVotingPolynomialDegree
