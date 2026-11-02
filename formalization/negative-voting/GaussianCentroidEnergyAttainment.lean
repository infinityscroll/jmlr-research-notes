import GaussianAssignmentDuality

/-! Actual global centroid-energy attainment and Gaussian square completion.
No full rank, distinctness, or purity of the maximizing assignment is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Classical RealInnerProductSpace
namespace NegativeVotingCentroidOptimization
open NegativeVoting NegativeVotingFan NegativeVotingFanValue NegativeVotingFanInverse
  NegativeVotingMassCentroid NegativeVotingAssignmentDuality

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

def rowEnergy (B : ι → FSC.Coord d) : ℝ := ∑ i, ‖B i‖^2

def centroidRows (f : FSC.Coord d → ι → ℝ) : ι → FSC.Coord d :=
  fun i => NegativeVotingMassCentroid.gaussianCentroid (fun x => f x i)

def centroidEnergy (f : FSC.Coord d → ι → ℝ) : ℝ := rowEnergy (centroidRows f)

def rowObjective (B : ι → FSC.Coord d) (p : ι → ℝ) : ℝ :=
  2*optimizedValue B p-rowEnergy B

def gaussianNormMean (d : ℕ) : ℝ :=
  ∫ x : FSC.Coord d, ‖x‖ ∂stdGaussian (FSC.Coord d)

theorem rowEnergy_nonneg (B : ι → FSC.Coord d) : 0 ≤ rowEnergy B :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem rowEnergy_sub_zero_iff (B C : ι → FSC.Coord d) : rowEnergy (B-C)=0 ↔ B=C := by
  constructor
  · intro h
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖(B-C) j‖)).mp h i (Finset.mem_univ i)
    have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    exact sub_eq_zero.mp hz
  · intro h
    subst C
    simp [rowEnergy]

theorem assignmentValue_eq_pairing (B : ι → FSC.Coord d) (p : ι → ℝ)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f) :
    assignmentValue B f=∑ i, inner ℝ (B i) (centroidRows f i) := by
  have hi (i : ι) : Integrable (fun x => f x i*inner ℝ (B i) x) (stdGaussian (FSC.Coord d)) :=
    fractional_mul_integrable _ _ _ (hf.1 i) (feasible_coordinate_bounds p f hf i)
      (IsGaussian.integrable_dual _ (innerSL ℝ (B i)))
  rw [assignmentValue,integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact (inner_gaussianCentroid (fun x => f x i) (B i) (hf.1 i)
    (feasible_coordinate_bounds p f hf i)).symm

theorem assignmentValue_centroid (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) : assignmentValue (centroidRows f) f=centroidEnergy f := by
  rw [assignmentValue_eq_pairing _ p f hf]
  simp only [real_inner_self_eq_norm_sq,centroidEnergy,rowEnergy]

theorem centroidRows_sum_zero (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) : (∑ i, centroidRows f i)=0 := by
  have hi (i : ι) : Integrable (fun x => f x i • x) (stdGaussian (FSC.Coord d)) :=
    fractional_vector_integrable (fun x => f x i) (hf.1 i) (feasible_coordinate_bounds p f hf i)
  unfold centroidRows NegativeVotingMassCentroid.gaussianCentroid
  rw [←integral_finsetSum Finset.univ (fun i _ => hi i)]
  calc
    _ = ∫ x : FSC.Coord d, x ∂stdGaussian (FSC.Coord d) := by
      apply integral_congr_ae
      filter_upwards [hf.2.1] with x hx
      rw [←Finset.sum_smul,hx.2,one_smul]
    _ = 0 := integral_id_stdGaussian

/-- Exact square completion for the actual Gaussian centroid integrals. -/
theorem assignment_square_completion (B : ι → FSC.Coord d) (p : ι → ℝ)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f) :
    2*assignmentValue B f-rowEnergy B=
      centroidEnergy f-rowEnergy (B-centroidRows f) := by
  rw [assignmentValue_eq_pairing B p f hf]
  simp only [centroidEnergy,rowEnergy,Pi.sub_apply,norm_sub_sq_real,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

theorem optimizedValue_zero (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    optimizedValue (0 : ι → FSC.Coord d) p=0 := by
  apply le_antisymm _ (optimizedValue_nonneg _ p hp hs)
  have h := optimizedValue_le_potential (0 : ι → FSC.Coord d) p hp hs (0 : centeredGauge ι)
  simpa [potential,expectedMax,scores,NegativeVoting.maxScore] using h

theorem rowObjective_zero (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    rowObjective (0 : ι → FSC.Coord d) p=0 := by
  simp [rowObjective,optimizedValue_zero p hp hs,rowEnergy]

theorem gaussianNormMean_nonneg (d : ℕ) : 0 ≤ gaussianNormMean d :=
  integral_nonneg (fun x => norm_nonneg x)

theorem optimizedValue_norm_bound (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    optimizedValue B p ≤ ‖B‖*gaussianNormMean d := by
  have h := (abs_le.mp (optimizedValue_rows_sub_bound B 0 p hp hs)).2
  simpa only [optimizedValue_zero p hp hs,sub_zero,gaussianNormMean] using h

theorem pi_norm_sq_le_rowEnergy (B : ι → FSC.Coord d) : ‖B‖^2 ≤ rowEnergy B := by
  have hS := rowEnergy_nonneg B
  have hs := Real.sq_sqrt hS
  have hnorm : ‖B‖ ≤ Real.sqrt (rowEnergy B) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    have hi : ‖B i‖^2 ≤ rowEnergy B :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖B j‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (B i),Real.sqrt_nonneg (rowEnergy B)]
  nlinarith [norm_nonneg B,Real.sqrt_nonneg (rowEnergy B)]

theorem rowObjective_coercive_bound (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    rowObjective B p ≤ 2*gaussianNormMean d*‖B‖-‖B‖^2 := by
  have hv := optimizedValue_norm_bound B p hp hs
  have hE := pi_norm_sq_le_rowEnergy B
  unfold rowObjective
  nlinarith

theorem rowObjective_continuous (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    Continuous (fun B : ι → FSC.Coord d => rowObjective B p) :=
  ((optimizedValue_continuous_rows p hp hs).const_mul 2).sub
    (continuous_finsetSum Finset.univ (fun i _ => (continuous_apply i).norm.pow 2))

/-- An actual global row-objective maximizer exists in finite dimension.
The compactness radius may depend on d; the endpoint asserts attainment,
not a dimension-independent radius. -/
theorem exists_global_row_maximizer (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i=1) :
    ∃ B : ι → FSC.Coord d, ∀ C : ι → FSC.Coord d, rowObjective C p ≤ rowObjective B p := by
  let R := 2*gaussianNormMean d+1
  have hM := gaussianNormMean_nonneg d
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : (0 : ι → FSC.Coord d) ∈ Metric.closedBall 0 R := by
    simpa using hR.le
  obtain ⟨B,hB,hmax⟩ := (isCompact_closedBall (0 : ι → FSC.Coord d) R).exists_isMaxOn
    ⟨0,hz⟩ (rowObjective_continuous p hp hs).continuousOn
  refine ⟨B,fun C => ?_⟩
  by_cases hc : C ∈ Metric.closedBall 0 R
  · exact hmax hc
  · have hc' : R < ‖C‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hc
    have hCB := rowObjective_coercive_bound C p hp hs
    have hC0 : rowObjective C p ≤ 0 := by
      have hp' := mul_nonneg (norm_nonneg C) (by dsimp [R] at hc'; linarith : 0 ≤ ‖C‖-2*gaussianNormMean d)
      nlinarith
    have hB0 : 0 ≤ rowObjective B p := by simpa only [Set.mem_setOf_eq,rowObjective_zero p hp hs] using hmax hz
    exact hC0.trans hB0

/-- Weak duality at the actual centroid rows supplies the companion square
completion inequality for every feasible fractional assignment. -/
theorem centroidEnergy_le_rowObjective (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) : centroidEnergy f ≤ rowObjective (centroidRows f) p := by
  have h := assignmentValue_le_optimizedValue (centroidRows f) p f hf
  rw [assignmentValue_centroid p f hf] at h
  unfold rowObjective
  change centroidEnergy f ≤ 2*optimizedValue (centroidRows f) p-centroidEnergy f
  linarith

/-- A Borel pointwise-simplex assignment attains the global Gaussian centroid
energy, and its actual centroids are the maximizing rows themselves. This
includes duplicate rows and zero-dimensional ambient Gaussian space. -/
theorem exists_centroid_optimal_assignment (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1) :
    ∃ (B : ι → FSC.Coord d) (f : FSC.Coord d → ι → ℝ),
      Feasible p f ∧ (∀ i, Measurable (fun x => f x i)) ∧
      (∀ x, SimplexWeights (f x)) ∧ B=centroidRows f ∧
      (∑ i, B i)=0 ∧ optimizedValue B p=rowEnergy B ∧
      rowObjective B p=centroidEnergy f ∧
      (∀ C : ι → FSC.Coord d, rowObjective C p ≤ rowObjective B p) ∧
      ∀ g : FSC.Coord d → ι → ℝ, Feasible p g → centroidEnergy g ≤ centroidEnergy f := by
  obtain ⟨B,hB⟩ := exists_global_row_maximizer (d:=d) p (fun i => (hp i).le) hs
  obtain ⟨h,f,hfm,hfs,hfp,hval,_⟩ := exists_assignment_and_offsets B p hp hs
  have hf : Feasible p f := ⟨fun i => (hfm i).aemeasurable,ae_of_all _ hfs,hfp⟩
  have hsc : rowObjective B p=centroidEnergy f-rowEnergy (B-centroidRows f) := by
    unfold rowObjective
    rw [←hval]
    exact assignment_square_completion B p f hf
  have hc := centroidEnergy_le_rowObjective p f hf
  have hmax := hB (centroidRows f)
  have hz : rowEnergy (B-centroidRows f)=0 := by
    have hn := rowEnergy_nonneg (B-centroidRows f)
    linarith
  have heq : B=centroidRows f := (rowEnergy_sub_zero_iff B (centroidRows f)).1 hz
  have hv : rowObjective B p=centroidEnergy f := by rw [hsc,hz,sub_zero]
  have hGamma : optimizedValue B p=rowEnergy B := by
    rw [←hval,heq,assignmentValue_centroid p f hf]
    rfl
  refine ⟨B,f,hf,hfm,hfs,heq,?_,hGamma,hv,hB,?_⟩
  · rw [heq]
    exact centroidRows_sum_zero p f hf
  · intro g hg
    exact (centroidEnergy_le_rowObjective p g hg).trans ((hB (centroidRows g)).trans_eq hv)

end NegativeVotingCentroidOptimization
