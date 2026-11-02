import GaussianFanBoundaryTransfer
import GaussianCheeger
import GaussianFanMassJacobian

/-! Concrete Gaussian fan cut conductance from actual Minkowski boundary and
intrinsic Gaussian facet masses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped Topology RealInnerProductSpace BigOperators ENNReal
namespace NegativeVotingFanBoundary
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingGaussianCheeger
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
local instance : (p : Prop) → Decidable p := Classical.propDecidable

theorem gaussian_cut_boundary_upper (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (I : Set V) :
    KLS.openBoundaryMeasure (stdGaussian (FSC.Coord d)) (cutRegion (affineScore B h) I) ≤
      ENNReal.ofReal (2*crossingFacetMass B h I) := by
  let A := cutRegion (affineScore B h) I
  have hA : MeasurableSet A := (isClosed_cutRegion (affineScore B h)
    (fun i => by unfold affineScore; fun_prop) I).measurableSet
  have hb (δ : ℝ) (hδ : 0<δ) :
      KLS.openBoundaryMeasure (stdGaussian (FSC.Coord d)) A ≤
        ENNReal.ofReal (2*crossingFacetMass B h I+δ) := by
    apply Filter.liminf_le_of_frequently_le
      (hu_le := ⟨0,Filter.Eventually.of_forall (fun _ => by positivity)⟩)
    have hh := cut_shell_quotient_eventually_le B h hinj I δ hδ
    apply Filter.Eventually.frequently
    filter_upwards [hh,self_mem_nhdsWithin] with ε he hε
    change (stdGaussian (FSC.Coord d) (thickening ε A)-stdGaussian (FSC.Coord d) A)/
      ENNReal.ofReal ε ≤ _
    rw [← measure_diff (self_subset_thickening hε A) hA.nullMeasurableSet (measure_ne_top _ _)]
    rw [← ENNReal.ofReal_toReal (measure_ne_top (stdGaussian (FSC.Coord d))
      (thickening ε A \ A)), ← ENNReal.ofReal_div_of_pos hε]
    exact ENNReal.ofReal_le_ofReal he
  have ht : Tendsto (fun δ : ℝ => ENNReal.ofReal (2*crossingFacetMass B h I+δ))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (2*crossingFacetMass B h I))) := by
    apply ENNReal.continuous_ofReal.tendsto _ |>.comp
    simpa using tendsto_const_nhds.add
      (show Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) from
        tendsto_id.mono_left nhdsWithin_le_nhds)
  apply isClosed_Ici.mem_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hb δ hδ

/-- The cut mass is the literal sum of the actual winning-cell probabilities;
Gaussian tie-nullness is derived from distinct sites. -/
theorem gaussian_cut_mass (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (I : Set V) :
    (stdGaussian (FSC.Coord d) (cutRegion (affineScore B h) I)).toReal =
      ∑i : {i : V // i∈I}, mass B h i := by
  have hU : cutRegion (affineScore B h) I =
      ⋃i : {i : V // i∈I}, winnerCell (affineScore B h) i := by
    ext x
    simp [cutRegion]
  have hd : Pairwise (Function.onFun (AEDisjoint (stdGaussian (FSC.Coord d)))
      (fun i : {i : V // i∈I} => winnerCell (affineScore B h) i)) := by
    intro i j hij
    have hae : ∀ᵐ x ∂stdGaussian (FSC.Coord d),
        x ∉ winnerCell (affineScore B h) i ∩ winnerCell (affineScore B h) j := by
      filter_upwards [ae_scores_injective B hinj h] with x hx
      intro hmem
      apply hij
      apply Subtype.ext
      apply hx
      exact le_antisymm (hmem.2 i) (hmem.1 j)
    simpa only [AEDisjoint,not_not,Set.setOf_mem_eq] using ae_iff.mp hae
  rw [hU,measure_iUnion₀ hd (fun i => (isClosed_winnerCell (affineScore B h)
    (fun k => by unfold affineScore; fun_prop) i).measurableSet.nullMeasurableSet),tsum_fintype]
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (mass_eq_winningCell B hinj h i).symm

theorem facetSurfaceMass_eq_edge_weight (B : V → FSC.Coord d) (h : V → ℝ)
    (i j : V) (hij : B i ≠ B j) :
    facetSurfaceMass B h i j=‖B i-B j‖*facetWeight B h i j := by
  have hn : ‖B i-B j‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hij)
  unfold facetSurfaceMass facetWeight
  field_simp

/-- The geometric cut surface is exactly the edge-length weighted cut in the
actual Gaussian mass Jacobian. -/
theorem crossingFacetMass_eq_edge_cut (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (I : Set V) :
    crossingFacetMass B h I = ∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ},
      ‖B i-B j‖*facetWeight B h i j := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply facetSurfaceMass_eq_edge_weight
  apply hinj.ne
  intro hij
  exact j.property (hij ▸ i.property)


/-- Actual dimension-free crossing-facet conductance, with every normalization
constant retained: 1/π from Gaussian Cheeger and 2 from the two-sided tube. -/
theorem gaussian_cut_surface_conductance (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (I : Set V) :
    min (∑i : {i : V // i∈I}, mass B h i)
      (1-∑i : {i : V // i∈I}, mass B h i) ≤ 2*Real.pi*crossingFacetMass B h I := by
  let A := cutRegion (affineScore B h) I
  have hA : MeasurableSet A := (isClosed_cutRegion (affineScore B h)
    (fun i => by unfold affineScore; fun_prop) I).measurableSet
  have hh := (gaussian_open_boundary_lower A hA).trans (gaussian_cut_boundary_upper B h hinj I)
  have hp : stdGaussian (FSC.Coord d) A ≤ 1 := prob_le_one
  have hs : 0≤2*crossingFacetMass B h I := mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => facetSurfaceMass_nonneg B h i j)))
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_div,ENNReal.toReal_min (measure_ne_top _ _)
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self),
    ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top,ENNReal.toReal_one,
    ENNReal.toReal_ofReal Real.pi_pos.le,ENNReal.toReal_ofReal hs] at hr
  have hf := (div_le_iff₀ Real.pi_pos).mp hr
  rw [gaussian_cut_mass B h hinj I] at hf
  nlinarith

/-- The same conductance theorem uses exactly the weights of the proved
Gaussian offset Jacobian; no perimeter or cut-mass hypothesis remains. -/
theorem gaussian_cut_jacobian_conductance (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (I : Set V) :
    min (∑i : {i : V // i∈I}, mass B h i)
      (1-∑i : {i : V // i∈I}, mass B h i) ≤
        2*Real.pi*(∑i : {i : V // i∈I}, ∑j : {j : V // j∈Iᶜ},
          ‖B i-B j‖*facetWeight B h i j) := by
  rw [← crossingFacetMass_eq_edge_cut B h hinj I]
  exact gaussian_cut_surface_conductance B h hinj I

end NegativeVotingFanBoundary
