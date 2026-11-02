import GaussianTwoCellMeasure
import GaussianCentroidEnergyAttainment

/-! The actual two-cell Gaussian reallocation, retaining all cell masses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace
namespace NegativeVotingTwoCell
open NegativeVoting NegativeVotingAssignmentDuality NegativeVotingCentroidOptimization
  NegativeVotingMassCentroid
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- In dimension at least two, a genuine unit direction is perpendicular to
any prescribed vector; no nonzero-vector hypothesis is necessary. -/
theorem exists_unit_perpendicular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 2 ≤ Module.finrank ℝ E) (w : E) :
    ∃ v : E, ‖v‖=1 ∧ inner ℝ v w=0 := by
  let K : Submodule ℝ E := (ℝ ∙ w)ᗮ
  have hr : Module.finrank ℝ (ℝ ∙ w) ≤ 1 := finrank_span_le_card ({w} : Set E)
  have hsum := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ w)
  have hK : 0 < Module.finrank ℝ K := by dsimp [K]; omega
  letI : Nontrivial K := Module.nontrivial_of_finrank_pos hK
  obtain ⟨v,hv⟩ := exists_norm_eq K (show (0:ℝ) ≤ 1 by norm_num)
  refine ⟨v,hv,?_⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property

def pairUnion (f : FSC.Coord d → ι → ℝ) (i j : ι) (x : FSC.Coord d) : ℝ := f x i+f x j

def upperPair (f : FSC.Coord d → ι → ℝ) (i j : ι) (v : FSC.Coord d) (t : ℝ) : FSC.Coord d → ℝ :=
  {x | t < inner ℝ v x}.indicator (pairUnion f i j)

def lowerPair (f : FSC.Coord d → ι → ℝ) (i j : ι) (v : FSC.Coord d) (t : ℝ) : FSC.Coord d → ℝ :=
  {x | inner ℝ v x ≤ t}.indicator (pairUnion f i j)

def resplitPair (f : FSC.Coord d → ι → ℝ) (i j : ι) (v : FSC.Coord d) (t : ℝ)
    (x : FSC.Coord d) (k : ι) : ℝ :=
  if k=i then upperPair f i j v t x else if k=j then lowerPair f i j v t x else f x k

theorem pairUnion_bounds (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) :
    ∀ᵐ x ∂stdGaussian (FSC.Coord d), 0 ≤ pairUnion f i j x ∧ pairUnion f i j x ≤ 1 := by
  filter_upwards [hf.2.1] with x hx
  refine ⟨add_nonneg (hx.1 i) (hx.1 j),?_⟩
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i,j} : Finset ι))
    (fun k _ _ => hx.1 k)
  simpa [pairUnion,Finset.sum_pair hij,hx.2] using hs

theorem pairUnion_measurable (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) : AEMeasurable (pairUnion f i j) (stdGaussian (FSC.Coord d)) :=
  (hf.1 i).add (hf.1 j)

theorem pairUnion_mass (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) : ∫ x,pairUnion f i j x ∂stdGaussian (FSC.Coord d)=p i+p j := by
  unfold pairUnion
  rw [integral_add (feasible_coordinate_integrable p f hf i) (feasible_coordinate_integrable p f hf j),
    hf.2.2 i,hf.2.2 j]

theorem pairUnion_centroid (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) :
    NegativeVotingMassCentroid.gaussianCentroid (pairUnion f i j)=centroidRows f i+centroidRows f j := by
  unfold NegativeVotingMassCentroid.gaussianCentroid pairUnion centroidRows
  simp only [add_smul]
  rw [integral_add (fractional_vector_integrable _ (hf.1 i) (feasible_coordinate_bounds p f hf i))
    (fractional_vector_integrable _ (hf.1 j) (feasible_coordinate_bounds p f hf j))]
  rfl

theorem upperPair_add_lowerPair (f : FSC.Coord d → ι → ℝ) (i j : ι)
    (v : FSC.Coord d) (t : ℝ) (x : FSC.Coord d) :
    upperPair f i j v t x+lowerPair f i j v t x=pairUnion f i j x := by
  by_cases hx : t < inner ℝ v x
  · simp [upperPair,lowerPair,hx,not_le.mpr hx]
  · simp [upperPair,lowerPair,hx,not_lt.mp hx]

theorem resplitPair_sum (f : FSC.Coord d → ι → ℝ) (i j : ι) (hij : i≠j)
    (v : FSC.Coord d) (t : ℝ) (x : FSC.Coord d) :
    (∑ k,resplitPair f i j v t x k)=∑ k,f x k := by
  have he (k : ι) : resplitPair f i j v t x k=f x k+
      (if k=i then upperPair f i j v t x-f x i else 0)+
      (if k=j then lowerPair f i j v t x-f x j else 0) := by
    by_cases hki : k=i
    · subst k; simp [resplitPair,hij]
    · by_cases hkj : k=j
      · subst k; simp [resplitPair,hij.symm]
      · simp [resplitPair,hki,hkj]
  simp_rw [he]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hh := upperPair_add_lowerPair f i j v t x
  dsimp only [pairUnion] at hh
  linarith

theorem resplitPair_simplex (f : FSC.Coord d → ι → ℝ) (i j : ι) (hij : i≠j)
    (v : FSC.Coord d) (t : ℝ) (x : FSC.Coord d) (hx : SimplexWeights (f x)) :
    SimplexWeights (resplitPair f i j v t x) := by
  refine ⟨?_,(resplitPair_sum f i j hij v t x).trans hx.2⟩
  intro k
  have hu : 0 ≤ pairUnion f i j x := add_nonneg (hx.1 i) (hx.1 j)
  have hU : 0 ≤ upperPair f i j v t x := by
    unfold upperPair
    by_cases h : x ∈ {x | t < inner ℝ v x} <;> simp [h,hu]
  have hL : 0 ≤ lowerPair f i j v t x := by
    unfold lowerPair
    by_cases h : x ∈ {x | inner ℝ v x ≤ t} <;> simp [h,hu]
  unfold resplitPair
  split_ifs <;> first | exact hU | exact hL | exact hx.1 k

theorem upperPair_measurable (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (v : FSC.Coord d) (t : ℝ) :
    AEMeasurable (upperPair f i j v t) (stdGaussian (FSC.Coord d)) :=
  (pairUnion_measurable p f hf i j).indicator (measurableSet_lt measurable_const (by fun_prop))

theorem lowerPair_measurable (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (v : FSC.Coord d) (t : ℝ) :
    AEMeasurable (lowerPair f i j v t) (stdGaussian (FSC.Coord d)) :=
  (pairUnion_measurable p f hf i j).indicator (measurableSet_le (by fun_prop) measurable_const)

theorem upperPair_bounds (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ) :
    ∀ᵐ x ∂stdGaussian (FSC.Coord d), 0 ≤ upperPair f i j v t x ∧ upperPair f i j v t x ≤ 1 := by
  filter_upwards [pairUnion_bounds p f hf i j hij] with x hx
  by_cases ht : t < inner ℝ v x <;> simp [upperPair,ht,hx]

theorem lowerPair_bounds (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ) :
    ∀ᵐ x ∂stdGaussian (FSC.Coord d), 0 ≤ lowerPair f i j v t x ∧ lowerPair f i j v t x ≤ 1 := by
  filter_upwards [pairUnion_bounds p f hf i j hij] with x hx
  by_cases ht : inner ℝ v x ≤ t <;> simp [lowerPair,ht,hx]

theorem upperPair_mass (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ) :
    (projectedFractionalGaussian (pairUnion f i j) v).real (Ioi t)=
      ∫ x,upperPair f i j v t x ∂stdGaussian (FSC.Coord d) := by
  rw [projectedFractionalGaussian_set _ (pairUnion_measurable p f hf i j)
    ((pairUnion_bounds p f hf i j hij).mono fun _ h => h.1) v (Ioi t) measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases ht : t < inner ℝ v x <;> simp [upperPair,ht]

theorem lowerPair_mass (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ) :
    (projectedFractionalGaussian (pairUnion f i j) v).real (Iic t)=
      ∫ x,lowerPair f i j v t x ∂stdGaussian (FSC.Coord d) := by
  rw [projectedFractionalGaussian_set _ (pairUnion_measurable p f hf i j)
    ((pairUnion_bounds p f hf i j hij).mono fun _ h => h.1) v (Iic t) measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with x
  by_cases ht : inner ℝ v x ≤ t <;> simp [lowerPair,ht]

theorem resplitPair_feasible (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ)
    (hU : (projectedFractionalGaussian (pairUnion f i j) v).real (Ioi t)=p i)
    (hL : (projectedFractionalGaussian (pairUnion f i j) v).real (Iic t)=p j) :
    Feasible p (resplitPair f i j v t) := by
  refine ⟨?_,hf.2.1.mono (fun x hx => resplitPair_simplex f i j hij v t x hx),?_⟩
  · intro k
    by_cases hki : k=i
    · subst k
      simpa [resplitPair] using upperPair_measurable p f hf i j v t
    · by_cases hkj : k=j
      · subst k
        simpa [resplitPair,hij.symm] using lowerPair_measurable p f hf i j v t
      · simpa [resplitPair,hki,hkj] using hf.1 k
  · intro k
    by_cases hki : k=i
    · subst k
      simpa [resplitPair] using (upperPair_mass p f hf i j hij v t).symm.trans hU
    · by_cases hkj : k=j
      · subst k
        simpa [resplitPair,hij.symm] using (lowerPair_mass p f hf i j hij v t).symm.trans hL
      · simpa [resplitPair,hki,hkj] using hf.2.2 k

theorem upperPair_projection (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ) :
    inner ℝ v (NegativeVotingMassCentroid.gaussianCentroid (upperPair f i j v t))=
      ∫ y in Ioi t,y ∂projectedFractionalGaussian (pairUnion f i j) v := by
  rw [inner_gaussianCentroid _ v (upperPair_measurable p f hf i j v t)
    (upperPair_bounds p f hf i j hij v t),←integral_indicator measurableSet_Ioi,
    projectedFractionalGaussian_integral _ (pairUnion_measurable p f hf i j)
      ((pairUnion_bounds p f hf i j hij).mono fun _ h => h.1) v
      ((Ioi t).indicator (fun y : ℝ => y)) (measurable_id.indicator measurableSet_Ioi)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases ht : t < inner ℝ v x <;> simp [upperPair,ht]

theorem lowerPair_projection (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ) :
    inner ℝ v (NegativeVotingMassCentroid.gaussianCentroid (lowerPair f i j v t))=
      ∫ y in Iic t,y ∂projectedFractionalGaussian (pairUnion f i j) v := by
  rw [inner_gaussianCentroid _ v (lowerPair_measurable p f hf i j v t)
    (lowerPair_bounds p f hf i j hij v t),←integral_indicator measurableSet_Iic,
    projectedFractionalGaussian_integral _ (pairUnion_measurable p f hf i j)
      ((pairUnion_bounds p f hf i j hij).mono fun _ h => h.1) v
      ((Iic t).indicator (fun y : ℝ => y)) (measurable_id.indicator measurableSet_Iic)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases ht : inner ℝ v x ≤ t <;> simp [lowerPair,ht]

theorem pairProjection_mean_zero (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d)
    (hv : inner ℝ v (centroidRows f i+centroidRows f j)=0) :
    ∫ y,y ∂projectedFractionalGaussian (pairUnion f i j) v=0 := by
  rw [projectedFractionalGaussian_integral _ (pairUnion_measurable p f hf i j)
    ((pairUnion_bounds p f hf i j hij).mono fun _ h => h.1) v (fun y => y) measurable_id]
  rw [← inner_gaussianCentroid _ v (pairUnion_measurable p f hf i j)
    (pairUnion_bounds p f hf i j hij),pairUnion_centroid p f hf i j]
  exact hv

theorem resplitPair_centroid_sum (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i j : ι) (hij : i≠j) (v : FSC.Coord d) (t : ℝ) :
    centroidRows (resplitPair f i j v t) i+centroidRows (resplitPair f i j v t) j=
      centroidRows f i+centroidRows f j := by
  have hU := fractional_vector_integrable (upperPair f i j v t)
    (upperPair_measurable p f hf i j v t) (upperPair_bounds p f hf i j hij v t)
  have hL := fractional_vector_integrable (lowerPair f i j v t)
    (lowerPair_measurable p f hf i j v t) (lowerPair_bounds p f hf i j hij v t)
  simp only [centroidRows,resplitPair,ite_true,if_neg hij.symm]
  change (∫ x,upperPair f i j v t x • x ∂stdGaussian (FSC.Coord d))+
    (∫ x,lowerPair f i j v t x • x ∂stdGaussian (FSC.Coord d))=_
  rw [← integral_add hU hL]
  calc
    _ = NegativeVotingMassCentroid.gaussianCentroid (pairUnion f i j) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [←add_smul,upperPair_add_lowerPair]
    _ = _ := pairUnion_centroid p f hf i j

end NegativeVotingTwoCell
