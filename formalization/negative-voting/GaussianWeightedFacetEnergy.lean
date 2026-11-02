import GaussianFacetDisintegration
import GaussianNormalTrace

/-!
# Weighted facet energy from actual L32 traces

The geometric facet probability and edge-length bounds remain explicit.
The integral estimate and finite label summation are derived, not assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace BigOperators Classical

namespace NegativeVotingWeightedFacet

/-- Actual set-integral Hölder with the exponent used by the small-cap proof. -/
theorem set_integral_sq_le_l32 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (F : Set X) {v : X → ℝ}
    (hv : MemLp v 32 μ) :
    (∫ x in F, (v x) ^ 2 ∂μ) ≤
      (μ F).toReal ^ (15 / 16 : ℝ) * (eLpNorm v 32 μ).toReal ^ 2 := by
  have hv2 : MemLp v 2 (μ.restrict F) :=
    (hv.restrict F).mono_exponent (by norm_num)
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (2 : ℝ≥0∞) ≤ 32 by norm_num) (hv.restrict F).aestronglyMeasurable
  have hb := hh.trans (mul_le_mul'
    (eLpNorm_mono_measure v (Measure.restrict_le_self (μ := μ) (s := F))) le_rfl)
  norm_num only [ENNReal.toReal_ofNat, Measure.restrict_apply_univ] at hb
  have hr := ENNReal.toReal_mono (by finiteness) hb
  rw [NegativeVotingNormalTrace.eLpNorm_two_eq_sqrt_integral_sq hv2,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow] at hr
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 2
  rw [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)), mul_pow] at hp
  have he : ((μ F).toReal ^ (15 / 32 : ℝ)) ^ 2 = (μ F).toReal ^ (15 / 16 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
  rw [he] at hp
  simpa only [mul_comm] using hp


/-- The set-integral estimate with explicit probability and norm bounds. -/
theorem set_integral_sq_le_l32_of_bounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (F : Set X) {v : X → ℝ}
    (hv : MemLp v 32 μ) {P K : ℝ} (hP : (μ F).toReal ≤ P) (hK : 0 ≤ K)
    (hNorm : eLpNorm v 32 μ ≤ ENNReal.ofReal K) :
    (∫ x in F, (v x) ^ 2 ∂μ) ≤ P ^ (15 / 16 : ℝ) * K ^ 2 := by
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top hNorm
  rw [ENNReal.toReal_ofReal hK] at hn
  exact (set_integral_sq_le_l32 F hv).trans (mul_le_mul
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hP (by norm_num))
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hn 2)
    (sq_nonneg _) (Real.rpow_nonneg (ENNReal.toReal_nonneg.trans hP) _))


/-- Finite Hölder for the exponent carried by the actual set-integral bound. -/
theorem sum_rpow_fifteen_sixteenths_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ j ∈ s, 0 ≤ w j) :
    (∑ j ∈ s, w j ^ (15 / 16 : ℝ)) ≤
      (s.card : ℝ) ^ (1 / 16 : ℝ) * (∑ j ∈ s, w j) ^ (15 / 16 : ℝ) := by
  have hc : (16 / 15 : ℝ).HolderConjugate 16 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := Real.inner_le_Lp_mul_Lq s (fun j => w j ^ (15 / 16 : ℝ)) (fun _ => 1) hc
  have he : (∑ j ∈ s, |w j ^ (15 / 16 : ℝ)| ^ (16 / 15 : ℝ)) = ∑ j ∈ s, w j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_of_nonneg (Real.rpow_nonneg (hw j hj) _), ← Real.rpow_mul (hw j hj)]
    norm_num
  rw [he] at hh
  norm_num only [mul_one, abs_one, Real.one_rpow, Finset.sum_const, nsmul_eq_mul,
    mul_one, one_div_div] at hh
  simpa only [mul_comm] using hh

/-- Split the surface coefficient before applying finite Hölder. -/
theorem fractional_surface_identity (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    a * p ^ (15 / 16 : ℝ) = a ^ (1 / 16 : ℝ) * (a * p) ^ (15 / 16 : ℝ) := by
  rcases ha.eq_or_lt with ha | ha
  · rw [← ha]
    norm_num
  rw [Real.mul_rpow ha.le hp, ← mul_assoc, ← Real.rpow_add ha]
  norm_num

/-- Only the weighted row degree is required; no individual facet probability
upper or lower bound enters this coefficient estimate. -/
theorem facet_coefficient_sum_le_of_degree {ι : Type*} (s : Finset ι)
    (a p : ι → ℝ) (D G : ℝ) (hD : 0 ≤ D) (_hG : 0 ≤ G)
    (ha : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ D) (hp : ∀ j ∈ s, 0 ≤ p j)
    (hDegree : (∑ j ∈ s, a j * p j) ≤ G) :
    (∑ j ∈ s, a j * p j ^ (15 / 16 : ℝ)) ≤
      D ^ (1 / 16 : ℝ) * (s.card : ℝ) ^ (1 / 16 : ℝ) * G ^ (15 / 16 : ℝ) := by
  have hw (j) (hj : j ∈ s) : 0 ≤ a j * p j := mul_nonneg (ha j hj).1 (hp j hj)
  calc
    _ ≤ ∑ j ∈ s, D ^ (1 / 16 : ℝ) * (a j * p j) ^ (15 / 16 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [fractional_surface_identity _ _ (ha j hj).1 (hp j hj)]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (ha j hj).1 (ha j hj).2 (by norm_num))
        (Real.rpow_nonneg (hw j hj) _)
    _ = D ^ (1 / 16 : ℝ) * ∑ j ∈ s, (a j * p j) ^ (15 / 16 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ D ^ (1 / 16 : ℝ) *
        ((s.card : ℝ) ^ (1 / 16 : ℝ) * (∑ j ∈ s, a j * p j) ^ (15 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_rpow_fifteen_sixteenths_le s _ hw) (Real.rpow_nonneg hD _)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Finset.sum_nonneg hw) hDegree (by norm_num)) (by positivity))
        (Real.rpow_nonneg hD _)

section FiniteFacets
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (X : ι → ι → Type*) [∀ i j, MeasurableSpace (X i j)]
  (μ : ∀ i j, Measure (X i j)) [∀ i j, IsFiniteMeasure (μ i j)]
  (F : ∀ i j, Set (X i j)) (v : ∀ i j, X i j → ℝ)

def orderedFacetEnergy (surface edge : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    surface i j / edge i j * ∫ x in F i j, (v i j x) ^ 2 ∂μ i j

/-- A finite sum over actual facet integrals. Each label has one whole-plane
trace bound, reused on its incident facets. No energy bound is assumed. -/
theorem orderedFacetEnergy_le
    (surface edge : ι → ι → ℝ) (P ell0 density : ℝ) (K : ι → ℝ)
    (hP : 0 ≤ P) (hell : 0 < ell0) (hDensity : 0 ≤ density)
    (hK : ∀ i, 0 ≤ K i)
    (hSurface : ∀ i j, i ≠ j → 0 ≤ surface i j ∧ surface i j ≤ density)
    (hEdge : ∀ i j, i ≠ j → ell0 ≤ edge i j)
    (hFacet : ∀ i j, i ≠ j → (μ i j (F i j)).toReal ≤ P)
    (hMem : ∀ i j, i ≠ j → MemLp (v i j) 32 (μ i j))
    (hNorm : ∀ i j, i ≠ j → eLpNorm (v i j) 32 (μ i j) ≤ ENNReal.ofReal (K i)) :
    orderedFacetEnergy X μ F v surface edge ≤
      (density / ell0 * (Fintype.card ι : ℝ) * P ^ (15 / 16 : ℝ)) * ∑ i, K i ^ 2 := by
  unfold orderedFacetEnergy
  calc
    _ ≤ ∑ i, (density / ell0 * (Fintype.card ι : ℝ) * P ^ (15 / 16 : ℝ)) * K i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j ∈ Finset.univ.erase i,
            density / ell0 * P ^ (15 / 16 : ℝ) * K i ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
          have hc : surface i j / edge i j ≤ density / ell0 := by
            apply (div_le_div_iff₀ (hell.trans_le (hEdge i j hij)) hell).mpr
            exact (mul_le_mul_of_nonneg_right (hSurface i j hij).2 hell.le).trans
              (mul_le_mul_of_nonneg_left (hEdge i j hij) hDensity)
          have hi := set_integral_sq_le_l32_of_bounds (F i j)
            (hMem i j hij) (hFacet i j hij) (hK i) (hNorm i j hij)
          simpa only [mul_assoc] using mul_le_mul hc hi
            (integral_nonneg (fun _ => sq_nonneg _)) (div_nonneg hDensity hell.le)
        _ ≤ ∑ j : ι, density / ell0 * P ^ (15 / 16 : ℝ) * K i ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          intro _ _ _
          positivity
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ = _ := by rw [Finset.mul_sum]


/-- Weighted-facet energy from the actual offset degree, avoiding all individual
facet-probability upper bounds. The only analytic input is the whole-plane
L32 norm of each source-label trace. -/
theorem orderedFacetEnergy_le_of_degree
    (surface edge : ι → ι → ℝ) (ell0 density degree : ℝ) (K : ι → ℝ)
    (hell : 0 < ell0) (hDensity : 0 ≤ density) (hDegree0 : 0 ≤ degree)
    (hK : ∀ i, 0 ≤ K i)
    (hSurface : ∀ i j, i ≠ j → 0 ≤ surface i j ∧ surface i j ≤ density)
    (hEdge : ∀ i j, i ≠ j → ell0 ≤ edge i j)
    (hDegree : ∀ i, (∑ j ∈ Finset.univ.erase i,
      surface i j / edge i j * (μ i j (F i j)).toReal) ≤ degree)
    (hMem : ∀ i j, i ≠ j → MemLp (v i j) 32 (μ i j))
    (hNorm : ∀ i j, i ≠ j → eLpNorm (v i j) 32 (μ i j) ≤ ENNReal.ofReal (K i)) :
    orderedFacetEnergy X μ F v surface edge ≤
      ((density / ell0) ^ (1 / 16 : ℝ) * (Fintype.card ι : ℝ) ^ (1 / 16 : ℝ) *
        degree ^ (15 / 16 : ℝ)) * ∑ i, K i ^ 2 := by
  have hcoeff (i j) (hij : i ≠ j) :
      0 ≤ surface i j / edge i j ∧ surface i j / edge i j ≤ density / ell0 := by
    refine ⟨div_nonneg (hSurface i j hij).1 (hell.trans_le (hEdge i j hij)).le, ?_⟩
    apply (div_le_div_iff₀ (hell.trans_le (hEdge i j hij)) hell).mpr
    exact (mul_le_mul_of_nonneg_right (hSurface i j hij).2 hell.le).trans
      (mul_le_mul_of_nonneg_left (hEdge i j hij) hDensity)
  unfold orderedFacetEnergy
  calc
    _ ≤ ∑ i, ((density / ell0) ^ (1 / 16 : ℝ) * (Fintype.card ι : ℝ) ^ (1 / 16 : ℝ) *
        degree ^ (15 / 16 : ℝ)) * K i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hrow := facet_coefficient_sum_le_of_degree (Finset.univ.erase i)
        (fun j => surface i j / edge i j) (fun j => (μ i j (F i j)).toReal)
        (density / ell0) degree (div_nonneg hDensity hell.le) hDegree0
        (fun j hj => hcoeff i j (Finset.mem_erase.mp hj).1.symm)
        (fun _ _ => ENNReal.toReal_nonneg) (hDegree i)
      have hc : ((Finset.univ.erase i).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset (s := Finset.univ) i)
      have hrow' : (∑ j ∈ Finset.univ.erase i,
          surface i j / edge i j * (μ i j (F i j)).toReal ^ (15 / 16 : ℝ)) ≤
          (density / ell0) ^ (1 / 16 : ℝ) * (Fintype.card ι : ℝ) ^ (1 / 16 : ℝ) *
            degree ^ (15 / 16 : ℝ) := by
        apply hrow.trans
        gcongr
      calc
        _ ≤ ∑ j ∈ Finset.univ.erase i,
            (surface i j / edge i j * (μ i j (F i j)).toReal ^ (15 / 16 : ℝ)) * K i ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hij := (Finset.mem_erase.mp hj).1.symm
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (set_integral_sq_le_l32_of_bounds (F i j) (hMem i j hij) le_rfl (hK i) (hNorm i j hij))
            (hcoeff i j hij).1
        _ = (∑ j ∈ Finset.univ.erase i,
            surface i j / edge i j * (μ i j (F i j)).toReal ^ (15 / 16 : ℝ)) * K i ^ 2 := by
          rw [Finset.sum_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hrow' (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

end FiniteFacets


/-- Exact dimensional and logarithmic loss after inserting the proposed
geometric edge and facet-probability bounds. -/
theorem facet_scale_identity (m L c C density : ℝ)
    (hm : 0 < m) (hL : 0 < L) (hc : 0 < c) (hC : 0 < C) :
    density / (c * Real.sqrt L / m) * m *
      (C * Real.sqrt L / m ^ 2) ^ (15 / 16 : ℝ) =
      density / c * C ^ (15 / 16 : ℝ) * m ^ (1 / 8 : ℝ) * L ^ (-1 / 32 : ℝ) := by
  have hP : (C * Real.sqrt L / m ^ 2) ^ (15 / 16 : ℝ) =
      C ^ (15 / 16 : ℝ) * L ^ (15 / 32 : ℝ) / m ^ (15 / 8 : ℝ) := by
    rw [Real.div_rpow (mul_nonneg hC.le (Real.sqrt_nonneg _)) (sq_nonneg _),
      Real.mul_rpow hC.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hL.le, ← Real.rpow_two m, ← Real.rpow_mul hm.le]
    norm_num
  have hmr : m ^ 2 / m ^ (15 / 8 : ℝ) = m ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_two m, ← Real.rpow_sub hm]
    norm_num
  have hLr : L ^ (15 / 32 : ℝ) / Real.sqrt L = L ^ (-1 / 32 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hL]
    norm_num
  rw [hP]
  calc
    _ = density / c * C ^ (15 / 16 : ℝ) *
        (m ^ 2 / m ^ (15 / 8 : ℝ)) * (L ^ (15 / 32 : ℝ) / Real.sqrt L) := by
      field_simp
    _ = _ := by rw [hmr, hLr]


/-- The degree route has the same m^(1/8) loss but needs no facet-probability
hypothesis at all. -/
theorem facet_degree_scale_identity (m L c density degree : ℝ)
    (hm : 0 < m) (hL : 0 < L) (hc : 0 < c) (hDensity : 0 ≤ density) :
    (density / (c * Real.sqrt L / m)) ^ (1 / 16 : ℝ) * m ^ (1 / 16 : ℝ) *
        degree ^ (15 / 16 : ℝ) =
      (density / c) ^ (1 / 16 : ℝ) * degree ^ (15 / 16 : ℝ) *
        m ^ (1 / 8 : ℝ) * L ^ (-1 / 32 : ℝ) := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hb : density / (c * Real.sqrt L / m) * m = (density / c) * (m ^ 2 / Real.sqrt L) := by
    field_simp
  rw [← Real.mul_rpow (by positivity) hm.le, hb,
    Real.mul_rpow (div_nonneg hDensity hc.le) (by positivity),
    Real.div_rpow (sq_nonneg _) hs.le, ← Real.rpow_two m, ← Real.rpow_mul hm.le,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
  norm_num
  rw [Real.rpow_neg hL.le]
  ring

section AffineFacets
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open NegativeVotingFan NegativeVotingDisintegration

def pairOffset (rows : ι → E) (offsets : ι → ℝ) (i j : ι) : ℝ :=
  (offsets j - offsets i) / ‖rows i - rows j‖

def facetChart (rows : ι → E) (offsets : ι → ℝ) (i j : ι)
    (y : tangentSpace (pairNormal rows i j)) : E :=
  (y : E) + pairOffset rows offsets i j • pairNormal rows i j

def intrinsicFacet (rows : ι → E) (offsets : ι → ℝ) (i j : ι) :
    Set (tangentSpace (pairNormal rows i j)) :=
  {y | facetChart rows offsets i j y ∈ affineFacet rows offsets i j}


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
/-- The chosen normal offset makes the chart lie on the actual comparison
plane; the affine offsets have the stated orientation. -/
theorem facetChart_on_pair_plane (rows : ι → E) (offsets : ι → ℝ) (i j : ι)
    (hij : rows i ≠ rows j) (y : tangentSpace (pairNormal rows i j)) :
    affineScore rows offsets i (facetChart rows offsets i j y) =
      affineScore rows offsets j (facetChart rows offsets i j y) := by
  have hn : ‖rows i - rows j‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  have hunit := pairNormal_norm rows i j hij
  have hd : rows i - rows j = ‖rows i - rows j‖ • pairNormal rows i j := by
    simp only [pairNormal, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hy : inner ℝ (pairNormal rows i j) (y : E) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
  have hi : inner ℝ (rows i - rows j) (facetChart rows offsets i j y) =
      pairOffset rows offsets i j * ‖rows i - rows j‖ := by
    unfold facetChart
    nth_rw 1 [hd]
    rw [real_inner_smul_left, inner_add_right, hy, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hunit]
    ring
  apply sub_eq_zero.mp
  calc
    _ = inner ℝ (rows i - rows j) (facetChart rows offsets i j y) + offsets i - offsets j := by
      simp only [affineScore, inner_sub_left]
      ring
    _ = 0 := by
      rw [hi]
      unfold pairOffset
      field_simp
      ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] in
theorem isClosed_intrinsicFacet (rows : ι → E) (offsets : ι → ℝ) (i j : ι) :
    IsClosed (intrinsicFacet rows offsets i j) :=
  (isClosed_affineFacet rows offsets i j).preimage (by unfold facetChart; fun_prop)

/-- The ordered convention counts only the source-label square. With symmetric
facets it equals the unordered sum of the two endpoint squares, without a 2. -/
def affineWeightedFacetEnergy (rows : ι → E) (offsets : ι → ℝ) (v : ι → E → ℝ) : ℝ :=
  orderedFacetEnergy (fun i j => tangentSpace (pairNormal rows i j))
    (fun i j => stdGaussian (tangentSpace (pairNormal rows i j)))
    (intrinsicFacet rows offsets) (fun i j y => v i (facetChart rows offsets i j y))
    (fun i j => gaussianPDFReal 0 1 (pairOffset rows offsets i j))
    (fun i j => ‖rows i - rows j‖)

omit [BorelSpace E] in
/-- Actual Gaussian facet integrals with explicit geometric hypotheses and
whole-plane trace bounds. No conditional-facet norm bound is assumed. -/
theorem affineWeightedFacetEnergy_le
    (rows : ι → E) (offsets : ι → ℝ) (v : ι → E → ℝ)
    (P ell0 density : ℝ) (K : ι → ℝ)
    (hP : 0 ≤ P) (hell : 0 < ell0) (hDensity : 0 ≤ density)
    (hK : ∀ i, 0 ≤ K i)
    (hSurface : ∀ i j, i ≠ j → gaussianPDFReal 0 1 (pairOffset rows offsets i j) ≤ density)
    (hEdge : ∀ i j, i ≠ j → ell0 ≤ ‖rows i - rows j‖)
    (hFacet : ∀ i j, i ≠ j →
      (stdGaussian (tangentSpace (pairNormal rows i j)) (intrinsicFacet rows offsets i j)).toReal ≤ P)
    (hMem : ∀ i j, i ≠ j → MemLp (fun y => v i (facetChart rows offsets i j y)) 32
      (stdGaussian (tangentSpace (pairNormal rows i j))))
    (hNorm : ∀ i j, i ≠ j → eLpNorm (fun y => v i (facetChart rows offsets i j y)) 32
      (stdGaussian (tangentSpace (pairNormal rows i j))) ≤ ENNReal.ofReal (K i)) :
    affineWeightedFacetEnergy rows offsets v ≤
      (density / ell0 * (Fintype.card ι : ℝ) * P ^ (15 / 16 : ℝ)) * ∑ i, K i ^ 2 := by
  exact orderedFacetEnergy_le _ _ _ _ _ _ P ell0 density K hP hell hDensity hK
    (fun i j hij => ⟨gaussianPDFReal_nonneg _ _ _, hSurface i j hij⟩)
    hEdge hFacet hMem hNorm


omit [BorelSpace E] in
/-- The actual Gaussian-density bound is discharged. Only edge geometry,
the actual offset degree, and whole-plane L32 trace bounds remain explicit. -/
theorem affineWeightedFacetEnergy_le_of_degree
    (rows : ι → E) (offsets : ι → ℝ) (v : ι → E → ℝ)
    (ell0 degree : ℝ) (K : ι → ℝ)
    (hell : 0 < ell0) (hDegree0 : 0 ≤ degree) (hK : ∀ i, 0 ≤ K i)
    (hEdge : ∀ i j, i ≠ j → ell0 ≤ ‖rows i - rows j‖)
    (hDegree : ∀ i, (∑ j ∈ Finset.univ.erase i,
      gaussianPDFReal 0 1 (pairOffset rows offsets i j) / ‖rows i - rows j‖ *
        (stdGaussian (tangentSpace (pairNormal rows i j)) (intrinsicFacet rows offsets i j)).toReal) ≤ degree)
    (hMem : ∀ i j, i ≠ j → MemLp (fun y => v i (facetChart rows offsets i j y)) 32
      (stdGaussian (tangentSpace (pairNormal rows i j))))
    (hNorm : ∀ i j, i ≠ j → eLpNorm (fun y => v i (facetChart rows offsets i j y)) 32
      (stdGaussian (tangentSpace (pairNormal rows i j))) ≤ ENNReal.ofReal (K i)) :
    affineWeightedFacetEnergy rows offsets v ≤
      (((Real.sqrt (2 * Real.pi))⁻¹ / ell0) ^ (1 / 16 : ℝ) *
        (Fintype.card ι : ℝ) ^ (1 / 16 : ℝ) * degree ^ (15 / 16 : ℝ)) * ∑ i, K i ^ 2 := by
  apply orderedFacetEnergy_le_of_degree _ _ _ _ _ _ ell0
    (Real.sqrt (2 * Real.pi))⁻¹ degree K hell (by positivity) hDegree0 hK
  · intro i j _
    refine ⟨gaussianPDFReal_nonneg _ _ _, ?_⟩
    simpa only [NNReal.coe_one, mul_one] using
      NegativeVotingCapTail.gaussian_density_le_normalizer 0 1 (pairOffset rows offsets i j)
  · exact hEdge
  · exact hDegree
  · exact hMem
  · exact hNorm

omit [BorelSpace E] in
/-- Sufficient weighted-facet estimate with explicit m^(1/8)L^(-1/32) loss.
The only geometric inputs are edge separation and the actual weighted degree.
This does not assert that those geometric inputs hold for an arbitrary fan. -/
theorem affineWeightedFacetEnergy_eighth_power_bound
    (rows : ι → E) (offsets : ι → ℝ) (v : ι → E → ℝ)
    (L c degree : ℝ) (K : ι → ℝ)
    (hm : 0 < (Fintype.card ι : ℝ)) (hL : 0 < L) (hc : 0 < c)
    (hDegree0 : 0 ≤ degree) (hK : ∀ i, 0 ≤ K i)
    (hEdge : ∀ i j, i ≠ j → c * Real.sqrt L / (Fintype.card ι : ℝ) ≤ ‖rows i - rows j‖)
    (hDegree : ∀ i, (∑ j ∈ Finset.univ.erase i,
      gaussianPDFReal 0 1 (pairOffset rows offsets i j) / ‖rows i - rows j‖ *
        (stdGaussian (tangentSpace (pairNormal rows i j)) (intrinsicFacet rows offsets i j)).toReal) ≤ degree)
    (hMem : ∀ i j, i ≠ j → MemLp (fun y => v i (facetChart rows offsets i j y)) 32
      (stdGaussian (tangentSpace (pairNormal rows i j))))
    (hNorm : ∀ i j, i ≠ j → eLpNorm (fun y => v i (facetChart rows offsets i j y)) 32
      (stdGaussian (tangentSpace (pairNormal rows i j))) ≤ ENNReal.ofReal (K i)) :
    affineWeightedFacetEnergy rows offsets v ≤
      (((Real.sqrt (2 * Real.pi))⁻¹ / c) ^ (1 / 16 : ℝ) * degree ^ (15 / 16 : ℝ) *
        (Fintype.card ι : ℝ) ^ (1 / 8 : ℝ) * L ^ (-1 / 32 : ℝ)) * ∑ i, K i ^ 2 := by
  have hh := affineWeightedFacetEnergy_le_of_degree rows offsets v
    (c * Real.sqrt L / (Fintype.card ι : ℝ)) degree K (by positivity) hDegree0 hK
    hEdge hDegree hMem hNorm
  rw [facet_degree_scale_identity _ _ _ _ _ hm hL hc (by positivity)] at hh
  exact hh

end AffineFacets

end NegativeVotingWeightedFacet
