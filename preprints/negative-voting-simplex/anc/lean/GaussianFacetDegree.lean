import GaussianWeightedFacetEnergy
import GaussianCapFirstMoment
import GaussianMassCentroid

/-!
# Actual affine Gaussian facet degrees

Boundary area is controlled by the actual cell centroid using a common inward
angle. Gaussian mass bounds then control the degree at the score scale.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace BigOperators Classical

namespace NegativeVotingFacetDegree

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- A genuine common inward angle controls the sum of nonnegative surface
weights by the norm of their outward-normal vector sum. -/
theorem surface_sum_le_normal_sum_norm (w : ι → E) (a : ι → ℝ)
    (ha : ∀ j, 0 ≤ a j) (u : E) (hu : ‖u‖ = 1) (c : ℝ) (hc : 0 < c)
    (hAngle : ∀ j, c ≤ -inner ℝ (w j) u) :
    (∑ j, a j) ≤ ‖-(∑ j, a j • w j)‖ / c := by
  apply (le_div_iff₀ hc).mpr
  calc
    _ = ∑ j, a j * c := by rw [Finset.sum_mul]
    _ ≤ ∑ j, a j * (-inner ℝ (w j) u) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hAngle j) (ha j))
    _ = inner ℝ (-(∑ j, a j • w j)) u := by
      simp only [inner_neg_left, sum_inner, real_inner_smul_left, mul_neg, Finset.sum_neg_distrib]
    _ ≤ ‖-(∑ j, a j • w j)‖ * ‖u‖ := real_inner_le_norm _ _
    _ = _ := by rw [hu, mul_one]


variable [DecidableEq ι]
open NegativeVotingCapTail NegativeVotingFan

/-- Every pair separation is bounded below by the centered singular scale. -/
theorem centered_singular_pair_norm_lower (rows : ι → E) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ) (i j : ι) (hij : i ≠ j) :
    σ ≤ ‖rows i - rows j‖ := by
  let q : ι → ℝ := fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)
  have hq : ∑ k, q k = 0 := by simp [q, Finset.sum_sub_distrib]
  have hsum : ∑ k, q k • rows k = rows i - rows j := by
    simp [q, sub_smul, Finset.sum_sub_distrib, ite_smul]
  have hi : q i = 1 := by simp [q, hij]
  have hs : 1 ≤ ∑ k, q k ^ 2 := by
    have hh := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset ι)) => sq_nonneg (q k))
      (Finset.mem_univ i)
    simpa only [hi, one_pow] using hh
  have hh := hlower q hq
  rw [hsum] at hh
  have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg σ)
  nlinarith [norm_nonneg (rows i - rows j)]

/-- The centered singular bound really separates every pair of rows. -/
theorem centered_singular_rows_ne (rows : ι → E) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ) (i j : ι) (hij : i ≠ j) :
    rows i ≠ rows j := by
  have hh := centered_singular_pair_norm_lower rows σ hσ hlower i j hij
  intro heq
  rw [heq, sub_self, norm_zero] at hh
  linarith

/-- A third row cannot lie on the affine line through a different pair;
this is derived from the checked quantitative tangent-slope inequality. -/
theorem centered_singular_triple_not_parallel (rows : ι → E) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : ℝ) :
    rows k - rows i ≠ t • (rows j - rows i) := by
  intro hrel
  have hh := triple_difference_lower_bound rows σ hσ.le hlower i j k hij hik hjk (1 / 2 - t)
  have hk : rows k = rows i + t • (rows j - rows i) := by
    exact (sub_eq_iff_eq_add.mp hrel).trans (add_comm _ _)
  have hz : rows k - (1 / 2 : ℝ) • (rows i + rows j) -
      (1 / 2 - t) • (rows i - rows j) = 0 := by
    rw [hk]
    module
  rw [hz, norm_zero] at hh
  have hp : 0 < σ * Real.sqrt (3 / 2) := mul_pos hσ (by positivity)
  linarith

/-- Distinct comparison normals at a fixed cell cannot be equal or opposite. -/
theorem centered_singular_normal_not_parallel (rows : ι → E) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : ℝ) :
    pairNormal rows k i ≠ t • pairNormal rows j i := by
  intro hrel
  have hki : ‖rows k - rows i‖ ≠ 0 := norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr (centered_singular_rows_ne rows σ hσ hlower k i hik.symm))
  have hdk : rows k - rows i = ‖rows k - rows i‖ • pairNormal rows k i := by
    simp only [pairNormal, smul_smul, mul_inv_cancel₀ hki, one_smul]
  have heq : rows k - rows i =
      (‖rows k - rows i‖ * t * ‖rows j - rows i‖⁻¹) • (rows j - rows i) := by
    nth_rw 1 [hdk]
    rw [hrel]
    simp only [pairNormal, smul_smul]
    module
  exact centered_singular_triple_not_parallel rows σ hσ hlower i j k hij hik hjk _ heq

omit [Fintype ι] [DecidableEq ι] in
/-- Direct Gram criterion for a common inward angle. The denominator is the
product of the edge length and the chosen row norm. -/
theorem inward_angle_of_gram_bound (a b : E) (ha : a ≠ 0) (hab : b ≠ a) (c : ℝ)
    (hGram : c * ‖b - a‖ * ‖a‖ ≤ inner ℝ a a - inner ℝ b a) :
    c ≤ -inner ℝ (‖b - a‖⁻¹ • (b - a)) (‖a‖⁻¹ • a) := by
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have he : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hi : -inner ℝ (‖b - a‖⁻¹ • (b - a)) (‖a‖⁻¹ • a) =
      (inner ℝ a a - inner ℝ b a) / (‖b - a‖ * ‖a‖) := by
    simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left]
    field_simp
    ring
  rw [hi]
  exact (le_div_iff₀ (mul_pos he hn)).mpr (by simpa only [mul_assoc] using hGram)

omit [Fintype ι] [DecidableEq ι] in
/-- A conservative, dimension-free criterion directly checkable from the Gram
matrix near a regular simplex. The resulting fixed angle is 1/32. -/
theorem inward_angle_of_dominant_diagonal (a b : E) (α : ℝ) (hα : 0 < α)
    (haLower : α ^ 2 / 2 ≤ inner ℝ a a)
    (haUpper : inner ℝ a a ≤ 2 * α ^ 2)
    (hbUpper : inner ℝ b b ≤ 2 * α ^ 2)
    (hCross : inner ℝ b a ≤ α ^ 2 / 4) :
    (1 / 32 : ℝ) ≤ -inner ℝ (‖b - a‖⁻¹ • (b - a)) (‖a‖⁻¹ • a) := by
  have ha : a ≠ 0 := by intro hz; simp [hz] at haLower; nlinarith [sq_pos_of_pos hα]
  have hab : b ≠ a := by intro he; rw [he] at hCross; nlinarith [sq_pos_of_pos hα]
  have hna : ‖a‖ ≤ 2 * α := by
    rw [real_inner_self_eq_norm_sq] at haUpper
    nlinarith [norm_nonneg a]
  have hnb : ‖b‖ ≤ 2 * α := by
    rw [real_inner_self_eq_norm_sq] at hbUpper
    nlinarith [norm_nonneg b]
  have hed : ‖b - a‖ ≤ 4 * α := (norm_sub_le _ _).trans (by linarith)
  have hp : ‖b - a‖ * ‖a‖ ≤ 8 * α ^ 2 := by
    have hh := mul_le_mul hed hna (norm_nonneg a) (by positivity : 0 ≤ 4 * α)
    nlinarith
  apply inward_angle_of_gram_bound a b ha hab
  nlinarith

end Geometry

section SetCentroid
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual vector first moment of a measurable Gaussian set obeys the
explicit logarithmic mass bound, by the already proved fractional theorem. -/
theorem set_centroid_norm_le_logarithmic_mass_bound (s : Set E) (hs : MeasurableSet s)
    (m C : ℝ) (hm : 1 ≤ m) (hmass : (stdGaussian E s).toReal ≤ C / m) :
    ‖∫ x in s, x ∂stdGaussian E‖ ≤
      (C * Real.sqrt (2 * Real.log m) + (Real.sqrt (2 * Real.pi))⁻¹) / m := by
  let f : E → ℝ := s.indicator (fun _ => 1)
  have hf : AEMeasurable f (stdGaussian E) := (measurable_const.indicator hs).aemeasurable
  have h01 : ∀ᵐ x ∂stdGaussian E, 0 ≤ f x ∧ f x ≤ 1 := by
    filter_upwards with x
    by_cases hx : x ∈ s <;> simp [f, hx]
  have hmass' : (∫ x, f x ∂stdGaussian E) ≤ C / m := by
    change (∫ x, s.indicator (1 : E → ℝ) x ∂stdGaussian E) ≤ C / m
    rw [integral_indicator_one hs]
    exact hmass
  have heq : NegativeVotingMassCentroid.gaussianCentroid f =
      ∫ x in s, x ∂stdGaussian E := by
    unfold NegativeVotingMassCentroid.gaussianCentroid
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ s <;> simp [f, hx]
  rw [← heq]
  exact NegativeVotingMassCentroid.gaussianCentroid_norm_le_logarithmic_mass_bound f m C hm hf h01 hmass'

end SetCentroid

section Polyhedron
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def capSurfaceWeight (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) : ℝ :=
  WeakSimplex.normalPDF (b j) * FSC.sliceMass w b j

omit [Fintype ι] [DecidableEq ι] in
theorem capSurfaceWeight_nonneg (w : ι → FSC.Coord d) (b : ι → ℝ) (j : ι) :
    0 ≤ capSurfaceWeight w b j := by
  exact mul_nonneg (WeakSimplex.normalPDF_pos _).le ENNReal.toReal_nonneg

/-- Actual Gaussian integration by parts discharges the centroid identity;
only the explicit geometric angle is required for this area bound. -/
theorem cap_surface_sum_le_centroid (w : ι → FSC.Coord d) (b : ι → ℝ)
    (hw : ∀ j, ‖w j‖ = 1) (hsep : FSC.NoCoincident w b)
    (u : FSC.Coord d) (hu : ‖u‖ = 1) (c : ℝ) (hc : 0 < c)
    (hAngle : ∀ j, c ≤ -inner ℝ (w j) u) :
    (∑ j, capSurfaceWeight w b j) ≤
      ‖∫ x in FSC.cap w b, x ∂stdGaussian (FSC.Coord d)‖ / c := by
  rw [NegativeVotingPolyhedral.gaussian_cap_vector_first_moment w hw b hsep]
  exact surface_sum_le_normal_sum_norm w (capSurfaceWeight w b)
    (capSurfaceWeight_nonneg w b) u hu c hc hAngle

/-- Edge separation converts the actual Gaussian surface-area estimate to
the offset-Laplacian weighted degree. -/
theorem cap_degree_le_centroid (w : ι → FSC.Coord d) (b edge : ι → ℝ)
    (hw : ∀ j, ‖w j‖ = 1) (hsep : FSC.NoCoincident w b)
    (u : FSC.Coord d) (hu : ‖u‖ = 1) (c ell : ℝ) (hc : 0 < c) (hell : 0 < ell)
    (hAngle : ∀ j, c ≤ -inner ℝ (w j) u) (hEdge : ∀ j, ell ≤ edge j) :
    (∑ j, capSurfaceWeight w b j / edge j) ≤
      ‖∫ x in FSC.cap w b, x ∂stdGaussian (FSC.Coord d)‖ / (c * ell) := by
  calc
    _ ≤ ∑ j, capSurfaceWeight w b j / ell := Finset.sum_le_sum (fun j _ =>
      div_le_div_of_nonneg_left (capSurfaceWeight_nonneg w b j) hell (hEdge j))
    _ = (∑ j, capSurfaceWeight w b j) / ell := by rw [Finset.sum_div]
    _ ≤ (‖∫ x in FSC.cap w b, x ∂stdGaussian (FSC.Coord d)‖ / c) / ell :=
      div_le_div_of_nonneg_right (cap_surface_sum_le_centroid w b hw hsep u hu c hc hAngle) hell.le
    _ = _ := by rw [div_div]

/-- Fully explicit mass-to-degree estimate for an actual finite Gaussian cap. -/
theorem cap_degree_le_logarithmic_mass_bound (w : ι → FSC.Coord d) (b edge : ι → ℝ)
    (hw : ∀ j, ‖w j‖ = 1) (hsep : FSC.NoCoincident w b)
    (u : FSC.Coord d) (hu : ‖u‖ = 1) (c ell m C : ℝ)
    (hc : 0 < c) (hell : 0 < ell) (hm : 1 ≤ m)
    (hAngle : ∀ j, c ≤ -inner ℝ (w j) u) (hEdge : ∀ j, ell ≤ edge j)
    (hmass : FSC.capMass w b ≤ C / m) :
    (∑ j, capSurfaceWeight w b j / edge j) ≤
      (C * Real.sqrt (2 * Real.log m) + (Real.sqrt (2 * Real.pi))⁻¹) / (m * c * ell) := by
  have hh := set_centroid_norm_le_logarithmic_mass_bound (FSC.cap w b)
    (FSC.measurableSet_cap w b) m C hm hmass
  calc
    _ ≤ ‖∫ x in FSC.cap w b, x ∂stdGaussian (FSC.Coord d)‖ / (c * ell) :=
      cap_degree_le_centroid w b edge hw hsep u hu c ell hc hell hAngle hEdge
    _ ≤ ((C * Real.sqrt (2 * Real.log m) + (Real.sqrt (2 * Real.pi))⁻¹) / m) / (c * ell) :=
      div_le_div_of_nonneg_right hh (mul_nonneg hc.le hell.le)
    _ = _ := by rw [div_div]; ring

end Polyhedron



/-- At the score scale sqrt(L)/m, the logarithmic mass bound yields a
constant degree. The algebra does not hide an asymptotic constant. -/
theorem logarithmic_degree_scale_bound (m L C c e : ℝ)
    (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L)
    (hC : 0 ≤ C) (hc : 0 < c) (he : 0 < e) :
    (C * Real.sqrt (2 * Real.log m) + (Real.sqrt (2 * Real.pi))⁻¹) /
        (m * c * (e * Real.sqrt L / m)) ≤
      (C * Real.sqrt 2 + (Real.sqrt (2 * Real.pi))⁻¹) / (c * e) := by
  have hm0 : 0 < m := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hs1 : 1 ≤ Real.sqrt L := by
    nlinarith [Real.sq_sqrt hL0, Real.sqrt_nonneg L]
  have hs0 : 0 < Real.sqrt L := by linarith
  have ht : Real.sqrt (2 * Real.log m) ≤ Real.sqrt 2 * Real.sqrt L := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hn : C * Real.sqrt (2 * Real.log m) + (Real.sqrt (2 * Real.pi))⁻¹ ≤
      (C * Real.sqrt 2 + (Real.sqrt (2 * Real.pi))⁻¹) * Real.sqrt L := by
    have h1 := mul_le_mul_of_nonneg_left ht hC
    have h2 := mul_le_mul_of_nonneg_left hs1
      (by positivity : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹)
    nlinarith
  have hd : m * c * (e * Real.sqrt L / m) = c * e * Real.sqrt L := by field_simp
  rw [hd]
  calc
    _ ≤ ((C * Real.sqrt 2 + (Real.sqrt (2 * Real.pi))⁻¹) * Real.sqrt L) /
        (c * e * Real.sqrt L) := div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by field_simp

section AffineCells
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
open NegativeVotingFan NegativeVotingCapTail NegativeVotingWeightedFacet

def cellNormals (rows : ι → FSC.Coord d) (i : ι) (j : {j : ι // j ≠ i}) : FSC.Coord d :=
  pairNormal rows j.1 i

def cellSupports (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (i : ι)
    (j : {j : ι // j ≠ i}) : ℝ := pairOffset rows offsets j.1 i

def cellEdges (rows : ι → FSC.Coord d) (i : ι) (j : {j : ι // j ≠ i}) : ℝ :=
  ‖rows j.1 - rows i‖

def affineCapDegree (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (i : ι) : ℝ :=
  ∑ j : {j : ι // j ≠ i}, capSurfaceWeight (cellNormals rows i)
    (cellSupports rows offsets i) j / cellEdges rows i j

theorem cellNormals_unit (rows : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ) (i : ι) (j : {j : ι // j ≠ i}) :
    ‖cellNormals rows i j‖ = 1 :=
  pairNormal_norm rows j.1 i (centered_singular_rows_ne rows σ hσ hlower j.1 i j.property)

/-- The actual singular-value premise rules out coincident comparison planes;
no generic-position or boundary regularity premise is supplied. -/
theorem cellNormals_noCoincident (rows : ι → FSC.Coord d) (offsets : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound rows σ) (i : ι) :
    FSC.NoCoincident (cellNormals rows i) (cellSupports rows offsets i) := by
  intro j k hjk
  have hv : j.1 ≠ k.1 := fun he => hjk (Subtype.ext he)
  have hnot := centered_singular_normal_not_parallel rows σ hσ hlower i k.1 j.1
    k.property.symm j.property.symm hv.symm
  constructor
  · intro he
    exact ((hnot 1) (by simpa only [one_smul, cellNormals] using he)).elim
  · intro he
    exact ((hnot (-1)) (by simpa only [neg_one_smul, cellNormals] using he)).elim

omit [Fintype ι] [DecidableEq ι] in
theorem cell_halfspace_iff_score (rows : ι → FSC.Coord d) (offsets : ι → ℝ)
    (i : ι) (j : {j : ι // j ≠ i}) (hij : rows j.1 ≠ rows i) (x : FSC.Coord d) :
    inner ℝ (cellNormals rows i j) x ≤ cellSupports rows offsets i j ↔
      affineScore rows offsets j.1 x ≤ affineScore rows offsets i x := by
  have hn : 0 < ‖rows j.1 - rows i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hij)
  have heq : inner ℝ (cellNormals rows i j) x =
      inner ℝ (rows j.1 - rows i) x / ‖rows j.1 - rows i‖ := by
    simp only [cellNormals, pairNormal, real_inner_smul_left, div_eq_mul_inv, mul_comm]
  rw [heq]
  unfold cellSupports pairOffset
  rw [div_le_div_iff_of_pos_right hn]
  simp only [inner_sub_left, affineScore]
  constructor <;> intro h <;> linarith

theorem affine_cap_eq_cell (rows : ι → FSC.Coord d) (offsets : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound rows σ) (i : ι) :
    FSC.cap (cellNormals rows i) (cellSupports rows offsets i) = affineCell rows offsets i := by
  ext x
  constructor
  · intro hx k
    by_cases hki : k = i
    · subst k
      exact le_rfl
    · exact (cell_halfspace_iff_score rows offsets i ⟨k, hki⟩
        (centered_singular_rows_ne rows σ hσ hlower k i hki) x).mp (hx ⟨k, hki⟩)
  · intro hx j
    exact (cell_halfspace_iff_score rows offsets i j
      (centered_singular_rows_ne rows σ hσ hlower j.1 i j.property) x).mpr (hx j.1)

/-- Degree of the actual affine score cell, with unit normals and the complete
noncoincidence condition derived from the centered singular lower bound. -/
theorem affineCapDegree_le_logarithmic_mass_bound
    (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ) (i : ι)
    (u : FSC.Coord d) (hu : ‖u‖ = 1) (c ell m C : ℝ)
    (hc : 0 < c) (hell : 0 < ell) (hm : 1 ≤ m)
    (hAngle : ∀ j : {j : ι // j ≠ i}, c ≤ -inner ℝ (cellNormals rows i j) u)
    (hEdge : ∀ j : {j : ι // j ≠ i}, ell ≤ cellEdges rows i j)
    (hmass : (stdGaussian (FSC.Coord d) (affineCell rows offsets i)).toReal ≤ C / m) :
    affineCapDegree rows offsets i ≤
      (C * Real.sqrt (2 * Real.log m) + (Real.sqrt (2 * Real.pi))⁻¹) / (m * c * ell) := by
  apply cap_degree_le_logarithmic_mass_bound _ _ _
    (cellNormals_unit rows σ hσ hlower i) (cellNormals_noCoincident rows offsets σ hσ hlower i)
    u hu c ell m C hc hell hm hAngle hEdge
  change (stdGaussian (FSC.Coord d)
    (FSC.cap (cellNormals rows i) (cellSupports rows offsets i))).toReal ≤ C / m
  rw [affine_cap_eq_cell rows offsets σ hσ hlower i]
  exact hmass


/-- The singular lower bound supplies edge separation. At the stated score
scale, the resulting degree bound is uniform in alphabet and dimension. -/
theorem affineCapDegree_uniform_of_angle
    (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ) (i : ι)
    (u : FSC.Coord d) (hu : ‖u‖ = 1) (c e m L C : ℝ)
    (hc : 0 < c) (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L)
    (hlog : Real.log m ≤ L) (hC : 0 ≤ C)
    (hScale : e * Real.sqrt L / m ≤ σ)
    (hAngle : ∀ j : {j : ι // j ≠ i}, c ≤ -inner ℝ (cellNormals rows i j) u)
    (hmass : (stdGaussian (FSC.Coord d) (affineCell rows offsets i)).toReal ≤ C / m) :
    affineCapDegree rows offsets i ≤
      (C * Real.sqrt 2 + (Real.sqrt (2 * Real.pi))⁻¹) / (c * e) := by
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by linarith
  have hEdge (j : {j : ι // j ≠ i}) : e * Real.sqrt L / m ≤ cellEdges rows i j :=
    hScale.trans (centered_singular_pair_norm_lower rows σ hσ hlower j.1 i j.property)
  exact (affineCapDegree_le_logarithmic_mass_bound rows offsets σ hσ hlower i u hu
    c (e * Real.sqrt L / m) m C hc (by positivity) hm hAngle hEdge hmass).trans
      (logarithmic_degree_scale_bound m L C c e hm hL hlog hC hc he)

/-- The explicit dominant-diagonal Gram conditions discharge the inward-angle
premise, producing a uniform actual affine-cap degree with angle 1/32. -/
theorem affineCapDegree_uniform_of_gram
    (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (hlower : CenteredSingularLowerBound rows σ) (i : ι) (e m L C : ℝ)
    (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L) (hC : 0 ≤ C)
    (hScale : e * Real.sqrt L / m ≤ σ)
    (hDiagLower : α ^ 2 / 2 ≤ inner ℝ (rows i) (rows i))
    (hDiagUpper : ∀ j, inner ℝ (rows j) (rows j) ≤ 2 * α ^ 2)
    (hCross : ∀ j, j ≠ i → inner ℝ (rows j) (rows i) ≤ α ^ 2 / 4)
    (hmass : (stdGaussian (FSC.Coord d) (affineCell rows offsets i)).toReal ≤ C / m) :
    affineCapDegree rows offsets i ≤
      32 * (C * Real.sqrt 2 + (Real.sqrt (2 * Real.pi))⁻¹) / e := by
  have hi : rows i ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at hDiagLower
    nlinarith [sq_pos_of_pos hα]
  have hAngle (j : {j : ι // j ≠ i}) : (1 / 32 : ℝ) ≤
      -inner ℝ (cellNormals rows i j) (‖rows i‖⁻¹ • rows i) :=
    inward_angle_of_dominant_diagonal (rows i) (rows j.1) α hα
      hDiagLower (hDiagUpper i) (hDiagUpper j.1) (hCross j.1 j.property)
  have hh := affineCapDegree_uniform_of_angle rows offsets σ hσ hlower i
    (‖rows i‖⁻¹ • rows i) (norm_smul_inv_norm hi) (1 / 32) e m L C
    (by norm_num) he hm hL hlog hC hScale hAngle hmass
  convert hh using 1
  ring


omit [Fintype ι] [DecidableEq ι] in
theorem pairNormal_reverse (rows : ι → FSC.Coord d) (i j : ι) :
    pairNormal rows j i = -pairNormal rows i j := by
  unfold pairNormal
  rw [norm_sub_rev]
  rw [show rows j - rows i = -(rows i - rows j) by abel, smul_neg]

omit [Fintype ι] [DecidableEq ι] in
theorem pairOffset_reverse (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (i j : ι) :
    pairOffset rows offsets j i = -pairOffset rows offsets i j := by
  unfold pairOffset
  rw [norm_sub_rev]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The outward cap slice and the inward chart use opposite normals and
opposite offsets, hence exactly the same actual Gaussian slice measure. -/
theorem cell_sliceLaw_eq_intrinsic_chart (rows : ι → FSC.Coord d) (offsets : ι → ℝ)
    (i : ι) (j : {j : ι // j ≠ i}) (hij : rows i ≠ rows j.1) :
    FSC.sliceLaw (cellNormals rows i j) (cellSupports rows offsets i j) =
      (stdGaussian (NegativeVotingDisintegration.tangentSpace (pairNormal rows i j.1))).map
        (facetChart rows offsets i j.1) := by
  unfold cellNormals cellSupports
  rw [pairNormal_reverse rows i j.1, pairOffset_reverse rows offsets i j.1]
  have heq : FSC.sliceLaw (-(pairNormal rows i j.1)) (-(pairOffset rows offsets i j.1)) =
      FSC.sliceLaw (pairNormal rows i j.1) (pairOffset rows offsets i j.1) := by
    unfold FSC.sliceLaw
    congr 1
    funext x
    simp only [neg_smul, smul_neg, neg_neg, inner_neg_left]
  rw [heq]
  unfold FSC.sliceLaw
  rw [NegativeVotingDisintegration.gaussian_affine_slice_map _ (pairNormal_norm rows i j.1 hij)]
  congr 1
  funext y
  exact add_comm _ _

/-- Identification of the actual conditional face mass with the intrinsic
Gaussian probability used by the weighted-facet energy theorem. -/
theorem cell_sliceMass_eq_intrinsicFacet (rows : ι → FSC.Coord d) (offsets : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound rows σ)
    (i : ι) (j : {j : ι // j ≠ i}) :
    FSC.sliceMass (cellNormals rows i) (cellSupports rows offsets i) j =
      (stdGaussian (NegativeVotingDisintegration.tangentSpace (pairNormal rows i j.1))
        (intrinsicFacet rows offsets i j.1)).toReal := by
  let S : Set (FSC.Coord d) := {x | ∀ k : {k : ι // k ≠ i}, k ≠ j →
    inner ℝ (cellNormals rows i k) x ≤ cellSupports rows offsets i k}
  have hSm : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
      measurableSet_le (by fun_prop) measurable_const))
  have hpre : (facetChart rows offsets i j.1) ⁻¹' S = intrinsicFacet rows offsets i j.1 := by
    ext y
    have hp := facetChart_on_pair_plane rows offsets i j.1
      (centered_singular_rows_ne rows σ hσ hlower i j.1 j.property.symm) y
    change (∀ k : {k : ι // k ≠ i}, k ≠ j →
      inner ℝ (cellNormals rows i k) (facetChart rows offsets i j.1 y) ≤ cellSupports rows offsets i k) ↔
      facetChart rows offsets i j.1 y ∈ affineFacet rows offsets i j.1
    constructor
    · intro hx
      refine ⟨hp, ?_⟩
      intro k
      by_cases hki : k = i
      · subst k
        exact le_rfl
      · by_cases hkj : k = j.1
        · subst k
          exact hp.ge
        · have hne : (⟨k, hki⟩ : {k : ι // k ≠ i}) ≠ j := fun he => hkj (congrArg Subtype.val he)
          exact (cell_halfspace_iff_score rows offsets i ⟨k, hki⟩
            (centered_singular_rows_ne rows σ hσ hlower k i hki) _).mp (hx ⟨k, hki⟩ hne)
    · intro hx k _
      exact (cell_halfspace_iff_score rows offsets i k
        (centered_singular_rows_ne rows σ hσ hlower k.1 i k.property) _).mpr (hx.2 k.1)
  change (FSC.sliceLaw (cellNormals rows i j) (cellSupports rows offsets i j) S).toReal = _
  rw [cell_sliceLaw_eq_intrinsic_chart rows offsets i j
    (centered_singular_rows_ne rows σ hσ hlower i j.1 j.property.symm),
    Measure.map_apply (by unfold facetChart; fun_prop) hSm, hpre]

/-- Exact normalization of every degree summand: one Gaussian density, one
intrinsic facet probability, and one edge-length denominator. -/
theorem cell_degree_summand_eq_intrinsic (rows : ι → FSC.Coord d) (offsets : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound rows σ)
    (i : ι) (j : {j : ι // j ≠ i}) :
    capSurfaceWeight (cellNormals rows i) (cellSupports rows offsets i) j / cellEdges rows i j =
      gaussianPDFReal 0 1 (pairOffset rows offsets i j.1) / ‖rows i - rows j.1‖ *
        (stdGaussian (NegativeVotingDisintegration.tangentSpace (pairNormal rows i j.1))
          (intrinsicFacet rows offsets i j.1)).toReal := by
  have hpdf : WeakSimplex.normalPDF (cellSupports rows offsets i j) =
      gaussianPDFReal 0 1 (pairOffset rows offsets i j.1) := by
    unfold cellSupports
    rw [pairOffset_reverse rows offsets i j.1, NegativeVotingMassCentroid.normalPDF_even]
    rfl
  unfold capSurfaceWeight
  rw [hpdf, cell_sliceMass_eq_intrinsicFacet rows offsets σ hσ hlower i j]
  unfold cellEdges
  rw [norm_sub_rev]
  ring


def intrinsicWeightedDegree (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (i : ι) : ℝ :=
  ∑ j ∈ Finset.univ.erase i,
    gaussianPDFReal 0 1 (pairOffset rows offsets i j) / ‖rows i - rows j‖ *
      (stdGaussian (NegativeVotingDisintegration.tangentSpace (pairNormal rows i j))
        (intrinsicFacet rows offsets i j)).toReal

/-- The cap derivative degree is exactly the degree used by
GaussianWeightedFacetEnergy, including its orientation and normalization. -/
theorem affineCapDegree_eq_intrinsicWeightedDegree
    (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound rows σ) (i : ι) :
    affineCapDegree rows offsets i = intrinsicWeightedDegree rows offsets i := by
  unfold affineCapDegree intrinsicWeightedDegree
  calc
    _ = ∑ j : {j : ι // j ≠ i},
        gaussianPDFReal 0 1 (pairOffset rows offsets i j.1) / ‖rows i - rows j.1‖ *
          (stdGaussian (NegativeVotingDisintegration.tangentSpace (pairNormal rows i j.1))
            (intrinsicFacet rows offsets i j.1)).toReal := by
      apply Finset.sum_congr rfl
      intro j _
      exact cell_degree_summand_eq_intrinsic rows offsets σ hσ hlower i j
    _ = _ := (Finset.sum_subtype (p := fun j : ι => j ≠ i) (Finset.univ.erase i) (fun j => by simp)
      (fun j => gaussianPDFReal 0 1 (pairOffset rows offsets i j) / ‖rows i - rows j‖ *
        (stdGaussian (NegativeVotingDisintegration.tangentSpace (pairNormal rows i j))
          (intrinsicFacet rows offsets i j)).toReal)).symm

/-- Uniform bound on the literal intrinsic Gaussian facet degree. Its premises
are mass, centered singular scale, and explicit Gram data, with no assumed
degree, boundary identity, unit normals, or noncoincidence condition. -/
theorem intrinsicWeightedDegree_uniform_of_gram
    (rows : ι → FSC.Coord d) (offsets : ι → ℝ) (σ α : ℝ) (hσ : 0 < σ) (hα : 0 < α)
    (hlower : CenteredSingularLowerBound rows σ) (i : ι) (e m L C : ℝ)
    (he : 0 < e) (hm : 1 ≤ m) (hL : 1 ≤ L) (hlog : Real.log m ≤ L) (hC : 0 ≤ C)
    (hScale : e * Real.sqrt L / m ≤ σ)
    (hDiagLower : α ^ 2 / 2 ≤ inner ℝ (rows i) (rows i))
    (hDiagUpper : ∀ j, inner ℝ (rows j) (rows j) ≤ 2 * α ^ 2)
    (hCross : ∀ j, j ≠ i → inner ℝ (rows j) (rows i) ≤ α ^ 2 / 4)
    (hmass : (stdGaussian (FSC.Coord d) (affineCell rows offsets i)).toReal ≤ C / m) :
    intrinsicWeightedDegree rows offsets i ≤
      32 * (C * Real.sqrt 2 + (Real.sqrt (2 * Real.pi))⁻¹) / e := by
  rw [← affineCapDegree_eq_intrinsicWeightedDegree rows offsets σ hσ hlower i]
  exact affineCapDegree_uniform_of_gram rows offsets σ α hσ hα hlower i e m L C
    he hm hL hlog hC hScale hDiagLower hDiagUpper hCross hmass

end AffineCells

end NegativeVotingFacetDegree
