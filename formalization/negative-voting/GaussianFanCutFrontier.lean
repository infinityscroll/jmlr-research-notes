import GaussianPolyhedralTube

/-! Actual frontier and shell covers for cuts of a finite continuous-score fan. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace NegativeVotingFanBoundary
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V]
section Topological
variable [TopologicalSpace E]

def winnerCell (s : V → E → ℝ) (i : V) : Set E := {x | ∀ j, s j x ≤ s i x}
def cutRegion (s : V → E → ℝ) (I : Set V) : Set E := ⋃ i ∈ I, winnerCell s i

theorem mem_cutRegion (s : V → E → ℝ) (I : Set V) (x : E) :
    x ∈ cutRegion s I ↔ ∃ i ∈ I, x ∈ winnerCell s i := by simp [cutRegion]

theorem isClosed_winnerCell (s : V → E → ℝ) (hs : ∀ i, Continuous (s i)) (i : V) :
    IsClosed (winnerCell s i) := by
  unfold winnerCell
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun j => isClosed_le (hs j) (hs i))

theorem isClosed_cutRegion (s : V → E → ℝ) (hs : ∀ i, Continuous (s i)) (I : Set V) :
    IsClosed (cutRegion s I) :=
  isClosed_iUnion_of_finite (fun i => isClosed_iUnion_of_finite (fun _ => isClosed_winnerCell s hs i))

theorem exists_winner (s : V → E → ℝ) (r : V) (x : E) : ∃ i, x ∈ winnerCell s i := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun j => s j x)
    (⟨r,Finset.mem_univ r⟩)
  exact ⟨i,fun j => hi j (Finset.mem_univ j)⟩

/-- Every actual boundary point has a tied winner on each side of the label cut. -/
theorem frontier_cutRegion_winners (s : V → E → ℝ) (hs : ∀ i, Continuous (s i))
    (I : Set V) {x : E} (hx : x ∈ frontier (cutRegion s I)) :
    ∃ i ∈ I, ∃ j ∈ Iᶜ, x ∈ winnerCell s i ∩ winnerCell s j := by
  have hxI := (isClosed_cutRegion s hs I).frontier_subset hx
  obtain ⟨i,hi,hwi⟩ := (mem_cutRegion s I x).mp hxI
  have hxC : x ∈ cutRegion s Iᶜ := by
    by_contra hno
    have hopen : IsOpen (cutRegion s Iᶜ)ᶜ := (isClosed_cutRegion s hs Iᶜ).isOpen_compl
    have hsub : (cutRegion s Iᶜ)ᶜ ⊆ cutRegion s I := by
      intro y hy
      obtain ⟨j,hj⟩ := exists_winner s i y
      have hjI : j ∈ I := by
        by_contra hjout
        exact hy ((mem_cutRegion s Iᶜ y).mpr ⟨j,hjout,hj⟩)
      exact (mem_cutRegion s I y).mpr ⟨j,hjI,hj⟩
    have hint : x ∈ interior (cutRegion s I) := mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hopen.mem_nhds hno) hsub)
    exact hx.2 hint
  obtain ⟨j,hj,hwj⟩ := (mem_cutRegion s Iᶜ x).mp hxC
  exact ⟨i,hi,j,hj,hwi,hwj⟩

end Topological

section Metric
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A point in an outer shell is at least as close to the actual frontier.
The frontier point is supplied by finite-dimensional nearest-point geometry. -/
theorem shell_subset_frontier_tube (A : Set E) (ε : ℝ) :
    thickening ε A \ A ⊆ thickening ε (frontier A) := by
  intro x hx
  obtain ⟨y,hy,_⟩ := mem_thickening_iff.mp hx.1
  have hcompl : Aᶜ ≠ univ := by
    intro he
    have hyC : y ∈ Aᶜ := he.symm ▸ (mem_univ y)
    exact hyC hy
  obtain ⟨z,hz,hd⟩ := exists_mem_frontier_infDist_compl_eq_dist hx.2 hcompl
  simp only [frontier_compl,compl_compl] at hz hd
  apply mem_thickening_iff.mpr
  refine ⟨z,hz,?_⟩
  rw [← hd]
  exact (mem_thickening_iff_infDist_lt ⟨y,hy⟩).mp hx.1

/-- The literal outer shell of a label cut is covered only by crossing-face
neighborhoods, rather than by all cell facets. -/
theorem cut_shell_crossing_cover (s : V → E → ℝ) (hs : ∀ i, Continuous (s i))
    (I : Set V) (ε : ℝ) :
    thickening ε (cutRegion s I) \ cutRegion s I ⊆
      ⋃ i ∈ I, ⋃ j ∈ Iᶜ, thickening ε (winnerCell s i ∩ winnerCell s j) := by
  intro x hx
  obtain ⟨z,hz,hxz⟩ := mem_thickening_iff.mp (shell_subset_frontier_tube _ ε hx)
  obtain ⟨i,hi,j,hj,hzij⟩ := frontier_cutRegion_winners s hs I hz
  exact mem_iUnion.2 ⟨i,mem_iUnion.2 ⟨hi,mem_iUnion.2
    ⟨j,mem_iUnion.2 ⟨hj,mem_thickening_iff.mpr ⟨z,hzij,hxz⟩⟩⟩⟩⟩

theorem cut_shell_measure_le [MeasurableSpace E] (μ : Measure E)
    (s : V → E → ℝ) (hs : ∀ i, Continuous (s i)) (I : Set V) (ε : ℝ) :
    μ (thickening ε (cutRegion s I) \ cutRegion s I) ≤
      ∑ i : {i : V // i ∈ I}, ∑ j : {j : V // j ∈ Iᶜ},
        μ (thickening ε (winnerCell s i ∩ winnerCell s j)) := by
  have he : (⋃ i ∈ I, ⋃ j ∈ Iᶜ, thickening ε (winnerCell s i ∩ winnerCell s j)) =
      ⋃ i : {i : V // i ∈ I}, ⋃ j : {j : V // j ∈ Iᶜ},
        thickening ε (winnerCell s i ∩ winnerCell s j) := by
    ext x
    simp
  calc
    _ ≤ μ (⋃ i ∈ I, ⋃ j ∈ Iᶜ, thickening ε (winnerCell s i ∩ winnerCell s j)) :=
      measure_mono (cut_shell_crossing_cover s hs I ε)
    _ = _ := congrArg μ he
    _ ≤ ∑ i : {i : V // i ∈ I}, μ (⋃ j : {j : V // j ∈ Iᶜ},
        thickening ε (winnerCell s i ∩ winnerCell s j)) := measure_iUnion_fintype_le μ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => measure_iUnion_fintype_le μ _)

end Metric
end NegativeVotingFanBoundary
