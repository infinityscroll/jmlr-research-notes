import GaussianFanCycleSlice

/-! Actual stratum means with the shared child Gaussian normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem coordinateCap_independent_anchor (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i j : V) (hi : i ∈ S) (hj : j ∈ S) :
    coordinateCap b h S i = coordinateCap b h S j := by
  ext x
  rw [← coordinateEmbed_mem_winnerStratum_iff b h S i hi,
    ← coordinateEmbed_mem_winnerStratum_iff b h S j hj]

theorem capMass_independent_anchor (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i j : V) (hi : i ∈ S) (hj : j ∈ S) :
    FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) =
      FSC.capMass (coordinateCapNormal b S j) (intrinsicCapOffset b h S j) :=
  congrArg (fun C : Set (FaceCoordinates b S) => (stdGaussian (FaceCoordinates b S) C).toReal)
    (coordinateCap_independent_anchor b h S i j hi hj)

theorem stratumMassAt_independent_anchor (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i j : V) (hi : i ∈ S) (hj : j ∈ S) :
    stratumMassAt b h S i = stratumMassAt b h S j := by
  rw [stratumMassAt,stratumMassAt,capMass_independent_anchor b h S i j hi hj]

theorem stratumMeanPairing_independent_anchor (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i j : V) (hi : i ∈ S) (hj : j ∈ S) (v : E) :
    stratumMeanPairing b h S i v = stratumMeanPairing b h S j v := by
  rw [stratumMeanPairing,stratumMeanPairing,coordinateCap_independent_anchor b h S i j hi hj,
    capMass_independent_anchor b h S i j hi hj]

theorem coordinateCapNormal_coordinateDual (b : AffineBasis V ℝ E) (S : Set V)
    (i : V) (k : {k : V // k ∉ S}) (v : E) :
    ⟪coordinateCapNormal b S i k,coordinateDual b S v⟫ =
      -⟪v,faceBoundaryNormal b S i k⟫ := by
  rw [real_inner_comm,coordinateDual_pairing]
  simp [coordinateCapNormal,intrinsicCapNormal]

/-- Intrinsic Gaussian first moment with the genuine mass of every child stratum. -/
theorem stratum_tangent_first_moment (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (v : E) :
    stratumDensityFactor b h S *
      (∫ x in coordinateCap b h S i, ⟪coordinateDual b S v,x⟫
        ∂stdGaussian (FaceCoordinates b S)) =
    ∑ k : {k : V // k ∉ S}, stratumMassAt b h (Set.insert k.1 S) i *
      ⟪v,faceBoundaryNormal b S i k⟫ := by
  rw [coordinateCap_first_moment b h S i hi]
  simp only [coordinateCapNormal_coordinateDual,mul_neg,Finset.sum_neg_distrib,neg_neg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← stratum_boundary_weight_eq_child b h S i hi k]
  ring

/-- Actual ambient first moment, including the perpendicular affine origin. -/
theorem stratum_mean_boundary (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (v : E) :
    stratumMassAt b h S i * stratumMeanPairing b h S i v =
    stratumMassAt b h S i * ⟪v,faceAnchor b h S⟫+
      ∑ k : {k : V // k ∉ S}, stratumMassAt b h (Set.insert k.1 S) i *
        ⟪v,faceBoundaryNormal b S i k⟫ := by
  have hp := ne_of_gt (coordinateCap_mass_pos b h S i hi)
  rw [stratumMeanPairing_eq b h S i hi]
  calc
    _ = stratumMassAt b h S i * ⟪v,faceAnchor b h S⟫+
      stratumDensityFactor b h S *
        (∫ x in coordinateCap b h S i, ⟪coordinateDual b S v,x⟫
          ∂stdGaussian (FaceCoordinates b S)) := by
      unfold stratumMassAt
      field_simp [hp]
    _ = _ := by rw [stratum_tangent_first_moment b h S i hi v]

/-- Every excluded barycentric vector sees exactly its own child face. -/
theorem stratum_mean_barycentric_mass (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i k : V) (hi : i ∈ S) (hk : k ∉ S) :
    stratumMassAt b h S i * stratumMeanPairing b h S i (barycentricOutwardVector b k) =
      stratumMassAt b h (Set.insert k S) i / faceGapHeight b S i k := by
  have hq : faceAnchor b h S ∈ faceDirection b S :=
    ((faceDirection b S).orthogonalProjectionOnto (affineFanApex b h)).property
  have hz : ⟪barycentricOutwardVector b k,faceAnchor b h S⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hq
      (barycentricOutwardVector_mem_face_orthogonal b S k hk)
  rw [stratum_mean_boundary b h S i hi, hz,mul_zero,zero_add]
  simp_rw [barycentricOutwardVector_faceBoundaryNormal b S i k _ hi hk]
  rw [Finset.sum_eq_single (⟨k,hk⟩ : {k : V // k ∉ S})]
  · simp [div_eq_mul_inv]
  · intro l _ hl
    have hkl : k ≠ l.1 := by
      intro he
      apply hl
      exact Subtype.ext he.symm
    simp [hkl]
  · simp

theorem stratum_mean_barycentric (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i k : V) (hi : i ∈ S) (hk : k ∉ S) :
    stratumMeanPairing b h S i (barycentricOutwardVector b k) =
      stratumMassAt b h (Set.insert k S) i / faceGapHeight b S i k /
        stratumMassAt b h S i := by
  apply (eq_div_iff (ne_of_gt (stratumMassAt_pos b h S i hi))).2
  rw [mul_comm]
  exact stratum_mean_barycentric_mass b h S i k hi hk

theorem stratumMeanPairing_zero (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) : stratumMeanPairing b h S i 0 = 0 := by
  simp [stratumMeanPairing]

theorem stratumMeanPairing_sum {I : Type*} [Fintype I]
    (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) (i : V) (v : I → E) :
    stratumMeanPairing b h S i (∑ k, v k) = ∑ k, stratumMeanPairing b h S i (v k) := by
  simp_rw [stratumMeanPairing,sum_inner]
  rw [integral_finset_sum Finset.univ (fun k _ => coordinateEmbed_pairing_integrable b h S i (v k)),
    Finset.sum_div]

theorem sum_stratumMeanPairing_barycentric (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) :
    (∑ k, stratumMeanPairing b h S i (barycentricOutwardVector b k)) = 0 := by
  rw [← stratumMeanPairing_sum,barycentricOutwardVector_sum,stratumMeanPairing_zero]

end NegativeVotingFanCycle
