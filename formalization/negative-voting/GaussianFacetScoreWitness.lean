import GaussianScoreRealization

/-! An explicit two-high-score point on any actual affine facet hyperplane.
The construction uses the score coordinates themselves and keeps their sum zero. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFacetScoreWitness
open NegativeVotingScoreRealization NegativeVotingCapTail
variable {V E : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem sum_two_spikes (i j : V) (hij : i ≠ j) (a b c : ℝ) :
    (∑ k : V, if k=i then a else if k=j then b else c) =
      a+b+((Fintype.card V : ℝ)-2)*c := by
  have he (k : V) : (if k=i then a else if k=j then b else c) =
      c+(if k=i then a-c else 0)+(if k=j then b-c else 0) := by
    by_cases hki : k=i
    · subst k;simp [hij]
    · by_cases hkj : k=j <;> simp [hki,hkj,hij.symm]
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

def twoHighScores (i j : V) (a Δ : ℝ) (k : V) : ℝ :=
  if k=i then a+Δ/2 else if k=j then a-Δ/2 else -2*a/((Fintype.card V : ℝ)-2)

theorem twoHighScores_sum (hm : 3 ≤ Fintype.card V) (i j : V) (hij : i ≠ j)
    (a Δ : ℝ) : ∑ k, twoHighScores i j a Δ k = 0 := by
  have hm' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hm
  have hd : (Fintype.card V : ℝ)-2 ≠ 0 := by linarith
  unfold twoHighScores
  rw [sum_two_spikes i j hij]
  field_simp
  <;> ring

theorem twoHighScores_sq_sum (hm : 3 ≤ Fintype.card V) (i j : V) (hij : i ≠ j)
    (a Δ : ℝ) : ∑ k, (twoHighScores i j a Δ k)^2 ≤ 6*a^2+Δ^2/2 := by
  have hm' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hm
  have hd : 0 < (Fintype.card V : ℝ)-2 := by linarith
  have he : (∑ k, (twoHighScores i j a Δ k)^2) =
      (a+Δ/2)^2+(a-Δ/2)^2+((Fintype.card V : ℝ)-2)*
        (-2*a/((Fintype.card V : ℝ)-2))^2 := by
    rw [← sum_two_spikes i j hij]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k=i <;> by_cases hkj : k=j <;> simp [twoHighScores,hki,hkj]
  have he' : (a+Δ/2)^2+(a-Δ/2)^2+((Fintype.card V : ℝ)-2)*
      (-2*a/((Fintype.card V : ℝ)-2))^2 =
      2*a^2+Δ^2/2+4*a^2/((Fintype.card V : ℝ)-2) := by
    field_simp
    <;> ring
  have hb : 4*a^2/((Fintype.card V : ℝ)-2) ≤ 4*a^2 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ (Fintype.card V : ℝ)-3 by linarith)]
  rw [he,he']
  linarith

/-- The two selected scores differ by the exact affine offset difference;
their common high level and every remaining score are prescribed explicitly. -/
theorem exists_facet_score_witness (b : AffineBasis V ℝ E) (hb : ∑ i, b i = 0)
    (hm : 3 ≤ Fintype.card V) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound b σ) (i j : V) (hij : i ≠ j)
    (a Δ : ℝ) : ∃ x : E,
      inner ℝ (b i) x = a+Δ/2 ∧ inner ℝ (b j) x = a-Δ/2 ∧
      (∀ k, k ≠ i → k ≠ j →
        inner ℝ (b k) x = -2*a/((Fintype.card V : ℝ)-2)) ∧
      inner ℝ (b i-b j) x = Δ ∧ ‖x‖^2 ≤ (6*a^2+Δ^2/2)/σ^2 := by
  obtain ⟨x,hx,hn⟩ := exists_centered_score_vector b hb σ hσ hlower
    (twoHighScores i j a Δ) (twoHighScores_sum hm i j hij a Δ)
  have hi : inner ℝ (b i) x = a+Δ/2 := by simpa [twoHighScores] using hx i
  have hj : inner ℝ (b j) x = a-Δ/2 := by simpa [twoHighScores,hij.symm] using hx j
  refine ⟨x,hi,hj,?_,?_,?_⟩
  · intro k hki hkj
    simpa [twoHighScores,hki,hkj] using hx k
  · rw [inner_sub_left,hi,hj];ring
  · exact hn.trans (div_le_div_of_nonneg_right (twoHighScores_sq_sum hm i j hij a Δ)
      (sq_nonneg σ))

theorem exists_dominant_facet_point (b : AffineBasis V ℝ E) (hb : ∑ i, b i = 0)
    (hm : 3 ≤ Fintype.card V) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound b σ) (i j : V) (hij : i ≠ j)
    (h : V → ℝ) (H a : ℝ) (hH : ∀ k, |h k| ≤ H) (ha : 0 ≤ a) :
    ∃ x : E,
      inner ℝ (b i) x-h i = inner ℝ (b j) x-h j ∧
      (∀ k, k ≠ i → k ≠ j → a-2*H ≤
        (inner ℝ (b i) x-h i)-(inner ℝ (b k) x-h k)) ∧
      inner ℝ (b i-b j) x = h i-h j ∧
      ‖x‖^2 ≤ (6*a^2+(h i-h j)^2/2)/σ^2 := by
  obtain ⟨x,hi,hj,hk,he,hn⟩ := exists_facet_score_witness b hb hm σ hσ hlower
    i j hij a (h i-h j)
  refine ⟨x,?_,?_,he,hn⟩
  · rw [hi,hj];ring
  · intro k hki hkj
    rw [hi,hk k hki hkj]
    have hhi := (abs_le.mp (hH i)).2
    have hhj := (abs_le.mp (hH j)).2
    have hhk := (abs_le.mp (hH k)).1
    have hm' : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hm
    have ht : 0 ≤ 2*a/((Fintype.card V : ℝ)-2) :=
      div_nonneg (mul_nonneg (by norm_num) ha) (by linarith)
    rw [neg_mul,neg_div]
    linarith

end NegativeVotingFacetScoreWitness
