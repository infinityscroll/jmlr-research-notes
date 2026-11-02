import GaussianRegularMaximumMoments
import GaussianCapSecondMoment
import GaussianFanTestedCells

/-! Actual boundary-derived invariants of the regular-max quadratic moment tensor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace Classical
namespace NegativeVotingRegularQuadratic
open NegativeVotingRegularMaximum NegativeVoting NegativeVotingModern
  NegativeVotingFacetDegree NegativeVotingCapTail NegativeVotingFan
  NegativeVotingFanTestedCells NegativeVotingPolyhedral NegativeVotingWeightedFacet
  OAI.MinUncut.GaussianHermite

def unitRows (n : ℕ) (i : Fin (n+2)) : FSC.Coord (n+2) := EuclideanSpace.single i 1

def moment (n : ℕ) (i a c : Fin (n+2)) : ℝ := quadraticMoment (fun x => maxWeights x i) a c

theorem moment_symm (n : ℕ) (i a c : Fin (n+2)) : moment n i a c=moment n i c a :=
  quadraticMoment_symm _ _ _

theorem unitRows_singular (n : ℕ) : CenteredSingularLowerBound (unitRows n) 1 := by
  intro q _
  have he : (∑ i, q i • unitRows n i)=WithLp.toLp 2 q := by
    ext k
    simp [unitRows,Pi.single_apply,PiLp.smul_apply]
  rw [he,EuclideanSpace.real_norm_sq_eq]
  simp

theorem unitRows_injective (n : ℕ) : Function.Injective (unitRows n) := by
  intro i j he
  by_contra hij
  exact (centered_singular_rows_ne (unitRows n) 1 zero_lt_one (unitRows_singular n) i j hij) he

theorem unitRows_weights (n : ℕ) (x : FSC.Coord (n+2)) (i : Fin (n+2)) :
    weights (unitRows n) (fun _ => 0) x i=maxWeights x.ofLp i := by
  have hs : scores (unitRows n) (fun _ => 0) x=x.ofLp := by
    funext j
    simp [scores,unitRows,EuclideanSpace.inner_single_left]
  rw [weights,hs]

theorem unitSupports_zero (n : ℕ) (i : Fin (n+2)) :
    cellSupports (unitRows n) (fun _ => 0) i=(fun _ => 0) := by
  funext j
  simp [cellSupports,pairOffset]

theorem unitNormals_sum_zero (n : ℕ) (i : Fin (n+2)) (j : {j : Fin (n+2) // j ≠ i}) :
    (∑ k, cellNormals (unitRows n) i j k)=0 := by
  simp only [cellNormals,pairNormal,PiLp.smul_apply,smul_eq_mul,← Finset.mul_sum,
    PiLp.sub_apply,Finset.sum_sub_distrib]
  simp [unitRows,EuclideanSpace.single_apply]

theorem unitCap_eq_winningCell (n : ℕ) (i : Fin (n+2)) :
    FSC.cap (cellNormals (unitRows n) i) (fun _ => 0)=winningCell (unitRows n) (fun _ => 0) i := by
  have h := affine_cap_eq_cell (unitRows n) (fun _ => 0) 1 zero_lt_one (unitRows_singular n) i
  rw [unitSupports_zero] at h
  exact h

theorem unitNormals_unit (n : ℕ) (i : Fin (n+2)) (j : {j : Fin (n+2) // j ≠ i}) :
    ‖cellNormals (unitRows n) i j‖=1 :=
  cellNormals_unit (unitRows n) 1 zero_lt_one (unitRows_singular n) i j

theorem unitNormals_separated (n : ℕ) (i : Fin (n+2)) :
    FSC.NoCoincident (cellNormals (unitRows n) i) (fun _ => 0) := by
  have h := cellNormals_noCoincident (unitRows n) (fun _ => 0) 1 zero_lt_one (unitRows_singular n) i
  rwa [unitSupports_zero] at h

def faceMoment (n : ℕ) (i : Fin (n+2)) (j : {j : Fin (n+2) // j ≠ i}) (c : Fin (n+2)) : ℝ :=
  ∫ x in faceEvent (cellNormals (unitRows n) i) (fun _ => 0) j,
    x c ∂FSC.sliceLaw (cellNormals (unitRows n) i j) 0

theorem coordinate_memLp_two {d : ℕ} (a : Fin d) :
    MemLp (fun x : FSC.Coord d => x a) 2 (stdGaussian (FSC.Coord d)) := by
  convert IsGaussian.memLp_dual (stdGaussian (FSC.Coord d)) (innerSL ℝ (EuclideanSpace.single a 1)) 2 (by simp) using 1
  funext x
  simp [EuclideanSpace.inner_single_left]

/-- Literal centered second moments equal the actual Gaussian face tensor. -/
theorem moment_boundary (n : ℕ) (i a c : Fin (n+2)) :
    moment n i a c = -∑ j : {j : Fin (n+2) // j ≠ i},
      (WeakSimplex.normalPDF 0*cellNormals (unitRows n) i j a)*faceMoment n i j c := by
  have he : moment n i a c=
      ∫ x in FSC.cap (cellNormals (unitRows n) i) (fun _ => 0),
        x a*x c-(if a=c then 1 else 0) ∂stdGaussian (FSC.Coord (n+2)) := by
    unfold moment quadraticMoment
    change (∫ x, maxWeights x i*quadraticCoordinate a c x ∂standardGaussian (Fin (n+2)))=_
    rw [integral_standardGaussian_eq_euclidean]
    simp only [quadraticCoordinate]
    simp_rw [← unitRows_weights n]
    rw [integral_weights_mul_eq_cell _ (unitRows_injective n),← unitCap_eq_winningCell]
  rw [he]
  have hip : IntegrableOn (fun x : FSC.Coord (n+2) => x a*x c)
      (FSC.cap (cellNormals (unitRows n) i) (fun _ => 0)) (stdGaussian (FSC.Coord (n+2))) := by
    simpa only [Pi.mul_def] using ((coordinate_memLp_two a).integrable_mul (coordinate_memLp_two c)).integrableOn
      (s := FSC.cap (cellNormals (unitRows n) i) (fun _ => 0))
  rw [integral_sub hip (integrable_const _),gaussian_cap_coordinate_second_moment
    _ (unitNormals_unit n i) _ (unitNormals_separated n i),setIntegral_const]
  simp only [faceMoment,FSC.capMass,Measure.real,smul_eq_mul]
  ring

theorem face_coordinate_integrable (n : ℕ) (i : Fin (n+2))
    (j : {j : Fin (n+2) // j ≠ i}) (c : Fin (n+2)) :
    IntegrableOn (fun x : FSC.Coord (n+2) => x c)
      (faceEvent (cellNormals (unitRows n) i) (fun _ => 0) j)
      (FSC.sliceLaw (cellNormals (unitRows n) i j) 0) := by
  letI := sliceLaw_isGaussian (cellNormals (unitRows n) i j) 0
  convert (IsGaussian.integrable_dual (FSC.sliceLaw (cellNormals (unitRows n) i j) 0)
      (innerSL ℝ (EuclideanSpace.single c 1))).integrableOn
      (s := faceEvent (cellNormals (unitRows n) i) (fun _ => 0) j) using 1
  funext x
  simp [EuclideanSpace.inner_single_left]

theorem face_normal_integral_zero (n : ℕ) (i : Fin (n+2))
    (j : {j : Fin (n+2) // j ≠ i}) :
    (∫ x in faceEvent (cellNormals (unitRows n) i) (fun _ => 0) j,
      inner ℝ (cellNormals (unitRows n) i j) x ∂FSC.sliceLaw (cellNormals (unitRows n) i j) 0)=0 := by
  let w := cellNormals (unitRows n) i j
  have hw : inner ℝ w w=1 := by rw [real_inner_self_eq_norm_sq,unitNormals_unit n i j];norm_num
  rw [← integral_indicator (measurableSet_faceEvent _ _ _)]
  unfold FSC.sliceLaw
  have hF : Measurable ((faceEvent (cellNormals (unitRows n) i) (fun _ => 0) j).indicator
      (inner ℝ w)) := (by fun_prop : Measurable (inner ℝ w)).indicator (measurableSet_faceEvent _ _ _)
  have hφ : Measurable (fun y : FSC.Coord (n+2) => (0:ℝ) • w+(y-inner ℝ w y • w)) := by
    convert (FSC.normalResidual w).continuous.measurable using 1
    funext y
    simp [FSC.normalResidual_apply]
  rw [integral_map (μ := stdGaussian (FSC.Coord (n+2)))
    (φ := fun y => (0:ℝ) • w+(y-inner ℝ w y • w))
    (f := (faceEvent (cellNormals (unitRows n) i) (fun _ => 0) j).indicator (inner ℝ w))
    hφ.aemeasurable hF.aestronglyMeasurable]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  by_cases hy : (0:ℝ) • w+(y-inner ℝ w y • w) ∈ faceEvent (cellNormals (unitRows n) i) (fun _ => 0) j
  · rw [Set.indicator_of_mem hy]
    change inner ℝ w ((0:ℝ) • w+(y-inner ℝ w y • w))=0
    simp only [zero_smul,zero_add,inner_sub_right,real_inner_smul_right,hw,mul_one,sub_self]
  · exact Set.indicator_of_notMem hy _

theorem faceMoment_normal_sum (n : ℕ) (i : Fin (n+2))
    (j : {j : Fin (n+2) // j ≠ i}) :
    (∑ a, cellNormals (unitRows n) i j a*faceMoment n i j a)=0 := by
  unfold faceMoment
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun a _ =>
    (face_coordinate_integrable n i j a).const_mul (cellNormals (unitRows n) i j a))]
  have he (x : FSC.Coord (n+2)) : (∑ a, cellNormals (unitRows n) i j a*x a)=
      inner ℝ (cellNormals (unitRows n) i j) x := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply,mul_comm]
  simp_rw [he]
  exact face_normal_integral_zero n i j

/-- Zero row sums are derived from the actual normal vectors and face formula. -/
theorem moment_column_sum_zero (n : ℕ) (i c : Fin (n+2)) : (∑ a, moment n i a c)=0 := by
  simp_rw [moment_boundary,Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,← Finset.mul_sum,unitNormals_sum_zero,mul_zero,zero_mul]
  simp

theorem moment_row_sum_zero (n : ℕ) (i a : Fin (n+2)) : (∑ c, moment n i a c)=0 := by
  simp_rw [moment_symm n i a]
  exact moment_column_sum_zero n i a

/-- Homogeneous cone trace cancellation comes from the literal zero-offset
Gaussian slice; radial independence is not postulated. -/
theorem moment_trace_zero (n : ℕ) (i : Fin (n+2)) : (∑ a, moment n i a a)=0 := by
  simp_rw [moment_boundary,Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  have he (j : {j : Fin (n+2) // j ≠ i}) :
      (∑ a, (WeakSimplex.normalPDF 0*cellNormals (unitRows n) i j a)*faceMoment n i j a)=0 := by
    calc
      _ = WeakSimplex.normalPDF 0*(∑ a, cellNormals (unitRows n) i j a*faceMoment n i j a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = 0 := by rw [faceMoment_normal_sum,mul_zero]
  simp_rw [he]
  simp

end NegativeVotingRegularQuadratic
