import GaussianFanCycleMoments
import GaussianFanCycleCoefficients
import GaussianCapCovarianceGap

/-! Actual intrinsic Gaussian covariance deficits and their child-face moments.
The weighted cycle matrix is identified from genuine boundary integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
open NegativeVotingPolyhedral

/-- Centering the genuine cap second-moment formula centers its face tests by
the same conditional mean. No inverse covariance-deficit matrix is used. -/
theorem cap_covariance_gap_centered_boundary {d : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (w : I → FSC.Coord d) (hw : ∀ j, ‖w j‖ = 1)
    (b : I → ℝ) (hp : 0 < FSC.capMass w b) (hsep : FSC.NoCoincident w b)
    (u v : FSC.Coord d) :
    FSC.capMass w b * (⟪u,v⟫-capConditionalCovariance w b u v) =
      ∑ j, (WeakSimplex.normalPDF (b j) * ⟪w j,u⟫) *
        (∫ x in faceEvent w b j,
          (⟪v,x⟫-(∫ y in FSC.cap w b, ⟪v,y⟫ ∂stdGaussian (FSC.Coord d))/FSC.capMass w b)
          ∂FSC.sliceLaw (w j) (b j)) := by
  let M : ℝ := (∫ y in FSC.cap w b, ⟪v,y⟫ ∂stdGaussian (FSC.Coord d))/FSC.capMass w b
  have hi (j : I) :
      (∫ x in faceEvent w b j, (⟪v,x⟫-M) ∂FSC.sliceLaw (w j) (b j)) =
      (∫ x in faceEvent w b j, ⟪v,x⟫ ∂FSC.sliceLaw (w j) (b j))-
        FSC.sliceMass w b j * M := by
    letI := sliceLaw_isGaussian (w j) (b j)
    have hv : Integrable (fun x : FSC.Coord d => ⟪v,x⟫)
        ((FSC.sliceLaw (w j) (b j)).restrict (faceEvent w b j)) :=
      (IsGaussian.integrable_dual _ (innerSL ℝ v)).restrict
    rw [integral_sub hv (integrable_const _), integral_const]
    simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, FSC.sliceMass, faceEvent]
  have hs : (∑ j, (WeakSimplex.normalPDF (b j)*⟪w j,u⟫) * (FSC.sliceMass w b j*M)) =
      capBoundaryFirstFlux w b u * M := by
    rw [capBoundaryFirstFlux, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hm := gaussian_cap_first_moment w hw b hsep v
  change (∫ y in FSC.cap w b, ⟪v,y⟫ ∂stdGaussian (FSC.Coord d)) =
    -capBoundaryFirstFlux w b v at hm
  change FSC.capMass w b * (⟪u,v⟫-capConditionalCovariance w b u v) =
    ∑ j, (WeakSimplex.normalPDF (b j)*⟪w j,u⟫) *
      (∫ x in faceEvent w b j, (⟪v,x⟫-M) ∂FSC.sliceLaw (w j) (b j))
  rw [gaussian_cap_covariance_boundary_gap w hw b hp hsep u v]
  simp_rw [hi, mul_sub, Finset.sum_sub_distrib]
  rw [hs]
  change FSC.capMass w b *
      (capBoundarySecondFlux w b u v/FSC.capMass w b+
        capBoundaryFirstFlux w b u*capBoundaryFirstFlux w b v/(FSC.capMass w b)^2) =
    capBoundarySecondFlux w b u v-capBoundaryFirstFlux w b u*M
  dsimp [M]
  rw [hm]
  field_simp [hp.ne']
  ring

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual conditional covariance deficit on the intrinsic Gaussian cap
of a winner stratum, evaluated on ambient test vectors. -/
def stratumDeficit (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i : V) (u v : E) : ℝ :=
  ⟪coordinateDual b S u,coordinateDual b S v⟫-
    capConditionalCovariance (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)
      (coordinateDual b S u) (coordinateDual b S v)

/-- The diagonal is literally the tangent-projector norm minus the actual
conditioned ambient directional variance. -/
theorem stratumDeficit_self (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V)
    (i : V) (hi : i ∈ S) (v : E) :
    stratumDeficit b h S i v v =
      ‖(faceDirection b S)ᗮ.starProjection v‖^2-stratumDirectionalVariance b h S i v := by
  unfold stratumDeficit stratumDirectionalVariance capConditionalCovariance
  simp_rw [coordinateEmbed_pairing, stratumMeanPairing_eq b h S i hi,
    add_sub_add_left_eq_sub, real_inner_self_eq_norm_sq, coordinateDual_norm, pow_two]
  rfl

theorem stratumDeficit_symmetric (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (u v : E) :
    stratumDeficit b h S i u v = stratumDeficit b h S i v u := by
  unfold stratumDeficit capConditionalCovariance
  rw [real_inner_comm (coordinateDual b S u) (coordinateDual b S v)]
  congr 2
  apply integral_congr_ae
  filter_upwards with x
  ring


/-- A centered ambient test transfers with the same actual stratum mass. -/
theorem stratum_centered_integral (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (v : E) (c : ℝ) :
    stratumDensityFactor b h S *
      (∫ x in coordinateCap b h S i, (⟪v,coordinateEmbed b h S x⟫-c)
        ∂stdGaussian (FaceCoordinates b S)) =
    stratumMassAt b h S i * (stratumMeanPairing b h S i v-c) := by
  rw [integral_sub (coordinateEmbed_pairing_integrable b h S i v) (integrable_const _),
    integral_const]
  simp only [measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
  change stratumDensityFactor b h S *
      ((∫ x in coordinateCap b h S i, ⟪v,coordinateEmbed b h S x⟫
        ∂stdGaussian (FaceCoordinates b S))-
        FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)*c) = _
  unfold stratumMassAt stratumMeanPairing
  field_simp [(coordinateCap_mass_pos b h S i hi).ne']

/-- The literal covariance deficit is a sum of the actual child-face mean
differences. All normal orientations and Gaussian density factors are derived. -/
theorem stratumDeficit_boundary (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (u v : E) :
    stratumMassAt b h S i * stratumDeficit b h S i u v =
      ∑ k : {k : V // k ∉ S},
        stratumMassAt b h (Set.insert k.1 S) i * ⟪u,faceBoundaryNormal b S i k⟫ *
          (stratumMeanPairing b h S i v-stratumMeanPairing b h (Set.insert k.1 S) i v) := by
  have hc := cap_covariance_gap_centered_boundary (coordinateCapNormal b S i)
    (coordinateCapNormal_norm b S i hi) (intrinsicCapOffset b h S i)
    (coordinateCap_mass_pos b h S i hi) (coordinateCapNormal_NoCoincident b h S i hi)
    (coordinateDual b S u) (coordinateDual b S v)
  have hcenter (x : FaceCoordinates b S) :
      ⟪v,coordinateEmbed b h S x⟫-stratumMeanPairing b h S i v =
      ⟪coordinateDual b S v,x⟫-
        (∫ y in coordinateCap b h S i, ⟪coordinateDual b S v,y⟫
          ∂stdGaussian (FaceCoordinates b S)) /
        FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) := by
    rw [coordinateEmbed_pairing,stratumMeanPairing_eq b h S i hi]
    ring
  change FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)*
      stratumDeficit b h S i u v =
    ∑ k, (WeakSimplex.normalPDF (intrinsicCapOffset b h S i k)*
      ⟪coordinateCapNormal b S i k,coordinateDual b S u⟫)*
      (∫ x in coordinateFaceEvent b h S i k,
        (⟪coordinateDual b S v,x⟫-
          (∫ y in coordinateCap b h S i, ⟪coordinateDual b S v,y⟫
            ∂stdGaussian (FaceCoordinates b S)) /
          FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i))
        ∂FSC.sliceLaw (coordinateCapNormal b S i k) (intrinsicCapOffset b h S i k)) at hc
  simp_rw [← hcenter] at hc
  calc
    _ = stratumDensityFactor b h S *
        (FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)*
          stratumDeficit b h S i u v) := by rw [stratumMassAt]; ring
    _ = _ := by
      rw [hc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [coordinateCapNormal_coordinateDual]
      have ht := stratum_boundary_integral_eq_child b h S i hi k
        (fun x => ⟪v,x⟫-stratumMeanPairing b h S i v) (by fun_prop)
      rw [stratum_centered_integral b h (Set.insert k.1 S) i (Set.mem_insert_of_mem k.1 hi) v
        (stratumMeanPairing b h S i v)] at ht
      calc
        _ = -⟪u,faceBoundaryNormal b S i k⟫ *
            (stratumDensityFactor b h S * WeakSimplex.normalPDF (intrinsicCapOffset b h S i k) *
              (∫ x in coordinateFaceEvent b h S i k,
                (⟪v,coordinateEmbed b h S x⟫-stratumMeanPairing b h S i v)
                ∂FSC.sliceLaw (coordinateCapNormal b S i k) (intrinsicCapOffset b h S i k))) := by ring
        _ = _ := by rw [ht]; ring

/-- Barycentric duality singles out one actual child face in the covariance
deficit, with its exact reciprocal-height coefficient. -/
theorem stratumDeficit_barycentric (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i k : V) (hi : i ∈ S) (hk : k ∉ S) (v : E) :
    stratumMassAt b h S i * stratumDeficit b h S i (barycentricOutwardVector b k) v =
      (stratumMassAt b h (Set.insert k S) i/faceGapHeight b S i k) *
        (stratumMeanPairing b h S i v-stratumMeanPairing b h (Set.insert k S) i v) := by
  rw [stratumDeficit_boundary b h S i hi]
  simp_rw [barycentricOutwardVector_faceBoundaryNormal b S i k _ hi hk]
  rw [Finset.sum_eq_single (⟨k,hk⟩ : {k : V // k ∉ S})]
  · simp [div_eq_mul_inv]
  · intro l _ hl
    have hkl : k ≠ l.1 := fun he => hl (Subtype.ext he.symm)
    simp [hkl]
  · simp


/-- Bilinearity follows from the proved actual boundary identity. -/
theorem stratumDeficit_sum_left {I : Type*} [Fintype I]
    (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) (i : V) (hi : i ∈ S)
    (u : I → E) (v : E) :
    stratumDeficit b h S i (∑ k, u k) v = ∑ k, stratumDeficit b h S i (u k) v := by
  apply mul_left_cancel₀ (stratumMassAt_pos b h S i hi).ne'
  rw [Finset.mul_sum]
  simp_rw [stratumDeficit_boundary b h S i hi, sum_inner, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem stratumDeficit_smul_left (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (c : ℝ) (u v : E) :
    stratumDeficit b h S i (c • u) v = c * stratumDeficit b h S i u v := by
  apply mul_left_cancel₀ (stratumMassAt_pos b h S i hi).ne'
  calc
    _ = ∑ k : {k : V // k ∉ S},
        stratumMassAt b h (Set.insert k.1 S) i * ⟪c • u,faceBoundaryNormal b S i k⟫ *
          (stratumMeanPairing b h S i v-stratumMeanPairing b h (Set.insert k.1 S) i v) :=
      stratumDeficit_boundary b h S i hi (c • u) v
    _ = c * (stratumMassAt b h S i * stratumDeficit b h S i u v) := by
      rw [stratumDeficit_boundary b h S i hi, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_smul_left]
      ring
    _ = _ := by ring

theorem stratumDeficit_sum_right {I : Type*} [Fintype I]
    (b : AffineBasis V ℝ E) (h : V → ℝ) (S : Set V) (i : V) (hi : i ∈ S)
    (u : E) (v : I → E) :
    stratumDeficit b h S i u (∑ k, v k) = ∑ k, stratumDeficit b h S i u (v k) := by
  rw [stratumDeficit_symmetric, stratumDeficit_sum_left b h S i hi]
  apply Finset.sum_congr rfl
  intro k _
  exact stratumDeficit_symmetric b h S i (v k) u

theorem stratumDeficit_smul_right (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (c : ℝ) (u v : E) :
    stratumDeficit b h S i u (c • v) = c * stratumDeficit b h S i u v := by
  rw [stratumDeficit_symmetric, stratumDeficit_smul_left b h S i hi,
    stratumDeficit_symmetric b h S i v u]

/-- Actual facet covariance deficit with its genuine edge weight. -/
def cycleDeficit (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j : V) (u v : E) : ℝ :=
  cycleEdgeWeight b h a j * stratumDeficit b h {a,j} a u v

theorem cycleDeficit_symmetric (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j : V) (u v : E) : cycleDeficit b h a j u v = cycleDeficit b h a j v u := by
  rw [cycleDeficit, cycleDeficit, stratumDeficit_symmetric]

/-- The exact Gaussian column identity E N^{-T}, expressed without any
inverse: each barycentric correction sees the parent-child mean difference. -/
theorem cycleDeficit_barycentric_column (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k : V) (haj : a ≠ j) (hka : k ≠ a) (hkj : k ≠ j) (v : E) :
    cycleTriangleWeight b h k a j * cycleDeficit b h a j (barycentricOutwardVector b k) v =
      stratumMeanPairing b h {a,j} a v-cycleMean b h k a j v := by
  have hk : k ∉ ({a,j} : Set V) := by simp [hka,hkj]
  have hd := stratumDeficit_barycentric b h {a,j} a k (by simp) hk v
  have hm := stratum_mean_barycentric_mass b h {a,j} a k (by simp) hk
  rw [← hm] at hd
  have hset : Set.insert k ({a,j} : Set V) = {k,a,j} := by
    ext x
    change (x=k ∨ x=a ∨ x=j) ↔ (x=k ∨ x=a ∨ x=j)
    rfl
  rw [hset] at hd
  have hlocal : stratumDeficit b h {a,j} a (barycentricOutwardVector b k) v =
      stratumMeanPairing b h {a,j} a (barycentricOutwardVector b k) *
        (stratumMeanPairing b h {a,j} a v-stratumMeanPairing b h {k,a,j} a v) := by
    apply mul_left_cancel₀ (stratumMassAt_pos b h {a,j} a (by simp)).ne'
    simpa only [mul_assoc] using hd
  have hchild : stratumMeanPairing b h {k,a,j} a v = cycleMean b h k a j v := by
    exact stratumMeanPairing_independent_anchor b h {k,a,j} a k (by simp) (by simp) v
  have hf := cycleTriangleWeight_facet_mean b h a j k haj hka hkj
  have hw := (cycleEdgeWeight_pos b h a j).ne'
  rw [cycleDeficit,hlocal,hchild,cycleTriangleWeight_cyclic b h k a j]
  calc
    _ = cycleEdgeWeight b h a j *
        (cycleTriangleWeight b h a j k * stratumMeanPairing b h {a,j} a
          (barycentricOutwardVector b k)) *
        (stratumMeanPairing b h {a,j} a v-cycleMean b h k a j v) := by ring
    _ = _ := by rw [hf]; field_simp

/-- Every entry of the published B form is the actual covariance deficit
between the two corresponding barycentric correction columns. -/
theorem cycleDeficit_barycentric_pair (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k l : V) (haj : a ≠ j) (hka : k ≠ a) (hkj : k ≠ j)
    (hla : l ≠ a) (hlj : l ≠ j) :
    cycleTriangleWeight b h k a j * cycleTriangleWeight b h l a j *
      cycleDeficit b h a j (barycentricOutwardVector b k) (barycentricOutwardVector b l) =
    1/cycleEdgeWeight b h a j-
      cycleTriangleWeight b h k a j * cycleMean b h l a j (barycentricOutwardVector b k) := by
  rw [cycleDeficit_symmetric]
  calc
    _ = cycleTriangleWeight b h k a j *
        (cycleTriangleWeight b h l a j *
          cycleDeficit b h a j (barycentricOutwardVector b l) (barycentricOutwardVector b k)) := by ring
    _ = cycleTriangleWeight b h k a j *
        (stratumMeanPairing b h {a,j} a (barycentricOutwardVector b k)-
          cycleMean b h l a j (barycentricOutwardVector b k)) := by
      rw [cycleDeficit_barycentric_column b h a j l haj hla hlj]
    _ = _ := by
      rw [mul_sub, cycleTriangleWeight_cyclic b h k a j,
        cycleTriangleWeight_facet_mean b h a j k haj hka hkj]


/-- Nonzero alternating triangle coefficients are supported on genuine triples. -/
theorem alternatingTriangle_nonzero_distinct (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) (a j k : V) (hn : lam a j k ≠ 0) :
    a ≠ j ∧ a ≠ k ∧ j ≠ k := by
  have hfirst (x y : V) : lam x x y = 0 := by
    have hh := hlam.1 x x y
    linarith
  have hlast (x y : V) : lam x y y = 0 := by
    have hh := alternatingTriangle_swap_last lam hlam x y y
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro he
    subst j
    exact hn (hfirst a k)
  · intro he
    subst k
    exact hn ((hlam.2 a j a).trans (hlast j a))
  · intro he
    subst k
    exact hn (hlast a j)

/-- The actual tangential cycle correction is a sum of the global
barycentric vectors with the derived geometric/Gaussian triangle weights. -/
def cycleCorrection (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) (a j : V) : E :=
  ∑ k, (cycleTriangleWeight b h k a j * lam k a j) • barycentricOutwardVector b k

theorem cycleDeficit_correction_expand (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) (a j : V) :
    cycleDeficit b h a j (cycleCorrection b h lam a j) (cycleCorrection b h eta a j) =
      ∑ k, ∑ l, (cycleTriangleWeight b h k a j * lam k a j) *
        (cycleTriangleWeight b h l a j * eta l a j) *
        cycleDeficit b h a j (barycentricOutwardVector b k) (barycentricOutwardVector b l) := by
  unfold cycleCorrection cycleDeficit
  rw [stratumDeficit_sum_left b h {a,j} a (by simp)]
  simp_rw [stratumDeficit_sum_right b h {a,j} a (by simp),
    stratumDeficit_smul_left b h {a,j} a (by simp),
    stratumDeficit_smul_right b h {a,j} a (by simp), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The full B form is exactly the genuine Gaussian covariance-deficit energy
of the cycle correction vectors, with the ordered-edge factor one half. -/
theorem cycleB_eq_actual_deficit (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam eta : V → V → V → ℝ) (hlam : AlternatingTriangle lam)
    (heta : AlternatingTriangle eta) :
    cycleB b h lam eta = (1/2:ℝ) * ∑ a, ∑ j,
      cycleDeficit b h a j (cycleCorrection b h lam a j) (cycleCorrection b h eta a j) := by
  rw [cycleB]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  rw [cycleDeficit_correction_expand]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : lam k a j = 0
  · simp [hl]
  by_cases he : eta l a j = 0
  · simp [he]
  obtain ⟨hka,hkj,haj⟩ := alternatingTriangle_nonzero_distinct lam hlam k a j hl
  obtain ⟨hla,hlj,_⟩ := alternatingTriangle_nonzero_distinct eta heta l a j he
  rw [← cycleDeficit_barycentric_pair b h a j k l haj hka hkj hla hlj]
  ring

/-- The deficit energy is nonnegative by the actual conditioned Gaussian
variance bound, without a positive-definiteness or invertibility assumption. -/
theorem cycleDeficit_nonneg (b : AffineBasis V ℝ E) (h : V → ℝ) (a j : V) (v : E) :
    0 ≤ cycleDeficit b h a j v v := by
  rw [cycleDeficit, stratumDeficit_self b h {a,j} a (by simp)]
  exact mul_nonneg (cycleEdgeWeight_pos b h a j).le
    (sub_nonneg.mpr (stratumDirectionalVariance_le_projector b h {a,j} a (by simp) v))

end NegativeVotingFanCycle
