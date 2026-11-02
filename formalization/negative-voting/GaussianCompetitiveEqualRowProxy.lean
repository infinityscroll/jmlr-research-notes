import GaussianCovarianceRadialNormalization
import GaussianCompetitiveCovarianceTransfer
import GaussianCentroidOperatorBound

/-! A literal geometric-median equal-row proxy for every competitive Gaussian
fractional assignment. Only the original radial error remains in the squared
distance estimate; no row-payment inequality is assumed. -/
noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical RealInnerProductSpace Topology
universe u
namespace NegativeVotingCompetitiveEqualRowProxy
open NegativeVoting NegativeVotingCentroidOptimization NegativeVotingBalancedReference
  NegativeVotingRegularCovarianceDeficit NegativeVotingFanValue NegativeVotingAssignmentDuality
  NegativeVotingOneRowRadialCloseness NegativeVotingGeometricMedianProxy
  NegativeVotingCovarianceRadialNormalization NegativeVotingGaussianMaximumMean
  NegativeVotingCentroidOperatorBound NegativeVotingCompetitiveCovarianceTransfer
  NegativeVotingAssignmentCoordinateBridge NegativeVotingFractionalMass
  NegativeVotingRegularScoreLaw NegativeVotingCompetitiveDeficit

/-- The actual reference row energy beats every fixed multiple of 1/m. -/
theorem eventually_referenceFirstWeight_size_large (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C < referenceFirstWeight n*((n:ℝ)+2) := by
  filter_upwards [eventually_referenceScale_size_large (2*(max C 1+1))] with n hn
  have hm : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have ha := referenceScale_pos n
  have hmax : 1 ≤ max C 1 := le_max_right _ _
  have hpos : 0 < 2*(max C 1+1) := by linarith
  have hsq := pow_le_pow_left₀ hpos.le hn.le 2
  have hw : (referenceScale n*((n:ℝ)+2))^2 ≤
      2*(referenceFirstWeight n*((n:ℝ)+2)) := by
    rw [referenceFirstWeight_scale]
    nlinarith [mul_nonneg (sq_nonneg (referenceScale n)) hm]
  nlinarith [le_max_left C 1,sq_nonneg (max C 1)]

/-- This intermediate statement has only concrete feasible-assignment and
numerical deficit hypotheses. All geometry is produced by the proof. -/
theorem eventually_feasible_equalRowProxy :
    ∀ᶠ n : ℕ in atTop, ∀ (e : ℕ) (p : Fin (n+2) → ℝ)
      (f : FSC.Coord e → Fin (n+2) → ℝ), Feasible p f →
      (∀ i,p i ≤ 2/((n:ℝ)+2)) →
      regularCovarianceDeficit n (centroidRows f) ≤ 256/((n:ℝ)+2)^2 →
      |rowEnergy (centroidRows f)-referenceFirstWeight n| ≤ 256/((n:ℝ)+2)^2 →
      ∃ Z : Fin (n+2) → FSC.Coord e,
        (∑ i,Z i)=0 ∧ (∀ i,‖Z i‖=referenceRowRadius n) ∧
        (∀ i,Z i∈Submodule.span ℝ (Set.range (centroidRows f))) ∧
        (∑ i,‖Z i-centroidRows f i‖^2) ≤
          16386*radialError (centroidRows f) (referenceRowRadius n) := by
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_referenceFirstWeight_size_large 4096,
    eventually_reference_rows_radially_close 512] with n hn hlarge hclose
  intro e p f hf hp hR hW
  let B := centroidRows f
  let w := referenceFirstWeight n
  let m : ℝ := (n:ℝ)+2
  have hm : 0 < m := by dsimp [m]; positivity
  have hm1 : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hw : 0 < w := referenceFirstWeight_pos n
  have hsmall : 256/m^2 < w/8 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hm)).mpr
    change 4096 < w*m at hlarge
    have hx := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ w*m by positivity)
    nlinarith
  have hWpos : 0 < rowEnergy B := by
    change |rowEnergy B-w| ≤ 256/m^2 at hW
    have hh := (abs_le.mp hW).1
    linarith
  have hcenter : ∑ i,B i=0 := centroidRows_sum_zero p f hf
  have hs : 1/2 ≤ radialScale n B := radialScale_half_le hn B hcenter hWpos (hR.trans hsmall.le)
  have hnormcenter := normalizedRows_centered B hcenter
  have hnormenergy := normalizedRows_energy B hWpos
  have hnormR : regularCovarianceDeficit n (normalizedRows n B) ≤ 512/((n:ℝ)+2)^2 := by
    have hh := normalizedRows_deficit_le hn B hcenter hWpos hs
    change regularCovarianceDeficit n B ≤ 256/((n:ℝ)+2)^2 at hR
    exact (hh.trans (mul_le_mul_of_nonneg_left hR (by norm_num))).trans_eq (by ring)
  have hnormclose : ∀ i,|‖normalizedRows n B i‖-referenceRowRadius n| ≤ referenceRowRadius n/256 :=
    fun i => (hclose e _ hnormcenter hnormenergy hnormR i).le
  have hinv : (radialScale n B)⁻¹ ≤ 2 := by
    rw [←one_div]
    exact (one_div_le (radialScale_pos B hWpos) (by norm_num)).mpr hs
  have hinv2 : ((radialScale n B)⁻¹)^2 ≤ 4 := by
    nlinarith [inv_nonneg.mpr (radialScale_pos B hWpos).le]
  have hcov : ∀ x : FSC.Coord e, ∑ i,(inner ℝ (normalizedRows n B i) x)^2 ≤
      (((Fintype.card (Fin (n+2)):ℕ):ℝ)*(referenceRowRadius n)^2/8)*‖x‖^2 := by
    intro x
    have hh := scaled_centroid_directional_operator_bound p f hf (2/m) (by positivity)
      hp ((radialScale n B)⁻¹) x
    have hh' : (∑ i,(inner ℝ (normalizedRows n B i) x)^2) ≤
        ((radialScale n B)⁻¹)^2*(2/m)*‖x‖^2 := by
      simpa only [normalizedRows,B,real_inner_comm] using hh
    have hcoef : ((radialScale n B)⁻¹)^2*(2/m) ≤ w/8 := by
      have hb : ((radialScale n B)⁻¹)^2*(2/m) ≤ 8/m := by
        have h := mul_le_mul_of_nonneg_right hinv2 (show 0 ≤ 2/m by positivity)
        exact h.trans_eq (by ring)
      apply hb.trans
      apply (div_le_iff₀ hm).mpr
      change 4096 < w*m at hlarge
      linarith
    have hc := hh'.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖x‖))
    simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,referenceRadius_energy] using hc
  obtain ⟨c,hcspan,hcsmall,hcne,hcmin,hZcenter,hZnorm,hZspan,hZerror⟩ :=
    exists_centered_equalRowProxy_of_row_covariance (normalizedRows n B)
      (referenceRowRadius n) (referenceRowRadius_pos n) hnormcenter hnormclose hcov
  let Z := equalRowProxy (normalizedRows n B) (referenceRowRadius n) c
  have hspan : Submodule.span ℝ (Set.range (normalizedRows n B)) ≤
      Submodule.span ℝ (Set.range B) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  refine ⟨Z,hZcenter,hZnorm,fun i => hspan (hZspan i),?_⟩
  exact proxy_error_transfer B Z hWpos hs hZerror

/-- Complete geometric specialization: one alphabet threshold precedes every
ambient coordinate system, regular orientation, feasible fractional competitor,
and strictly negative correlation in the voting range. -/
theorem eventually_competitive_equalRowProxy :
    ∀ᶠ n : ℕ in atTop, ∀ (κ : Type u) [Fintype κ]
      (Ref : Fin (n+2) → κ → ℝ) (hRef : RegularSimplexGram Ref)
      (f : (κ → ℝ) → Fin (n+2) → ℝ)
      (hf : ∀ i,AEMeasurable (fun x => f x i) (standardGaussian κ))
      (hp : ∀ᵐ x ∂standardGaussian κ,SimplexWeights (f x))
      (r : ℝ) (hr0 : 0 < r) (hr : r ≤ 1/((n:ℝ)+1))
      (hcomp : gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment Ref))
      (e : ℕ) (coord : FSC.Coord e ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ),
      ∃ Z : Fin (n+2) → FSC.Coord e,
        (∑ i,Z i)=0 ∧ (∀ i,‖Z i‖=referenceRowRadius n) ∧
        (∀ i,Z i∈Submodule.span ℝ (Set.range (centroidRows (coordinateRule coord f)))) ∧
        (∑ i,‖Z i-centroidRows (coordinateRule coord f) i‖^2) ≤
          16386*radialError (centroidRows (coordinateRule coord f)) (referenceRowRadius n) := by
  filter_upwards [eventually_feasible_equalRowProxy,
    eventually_uniform_actual_covariance_deficit_transfer,
    NegativeVotingUniformMassBound.eventually_uniform_competitive_deficit_bounds,
    eventually_uniform_regular_competitive_mass_window] with n hproxy hR hD hmass
  intro κ _ Ref hRef f hf hp r hr0 hr hcomp e coord
  apply hproxy e (assignmentMass f) (coordinateRule coord f)
    (coordinateRule_feasible coord f hf hp)
    (fun i => ((hmass κ Ref hRef f hf hp r hr0.le hr hcomp).2 i).2)
  · have hh := (hR κ Ref hRef f hf hp r hr0 hr hcomp e coord).2
    apply hh.trans
    have hm : 0 < (n:ℝ)+2 := by positivity
    have hr2 : r ≤ 2/((n:ℝ)+2) := hr.trans (by
      apply (div_le_div_iff₀ (by positivity) hm).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) n])
    apply (div_le_div_iff₀ hm (sq_pos_of_pos hm)).mpr
    have hx := (le_div_iff₀ hm).mp hr2
    nlinarith [mul_le_mul_of_nonneg_right hx hm.le]
  · change |centroidEnergy (coordinateRule coord f)-referenceFirstWeight n| ≤ _
    rw [coordinateRule_centroidEnergy coord f hf hp]
    have hh := hD κ Ref hRef f hf hp r hr0.le hr hcomp
    have hbound : |assignmentFirstEnergy f-referenceFirstWeight n| ≤ 128*r/((n:ℝ)+2) := by
      apply (mul_le_mul_iff_right₀ hr0).mp
      have hx := hh.2.2.1.trans hh.2.2.2
      simp only [div_eq_mul_inv] at hx ⊢
      nlinarith
    apply hbound.trans
    have hm : 0 < (n:ℝ)+2 := by positivity
    have hr2 : r ≤ 2/((n:ℝ)+2) := hr.trans (by
      apply (div_le_div_iff₀ (by positivity) hm).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) n])
    apply (div_le_div_iff₀ hm (sq_pos_of_pos hm)).mpr
    have hx := (le_div_iff₀ hm).mp hr2
    nlinarith [mul_le_mul_of_nonneg_right hx hm.le]

end NegativeVotingCompetitiveEqualRowProxy
