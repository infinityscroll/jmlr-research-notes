import GaussianLowModeIsometry
import GaussianCellOUContinuity
import GaussianRegularCrossPlaneOU
import GaussianRegularFacetCylinder

/-! The literal regular-cell high-mode OU potential is odd under its actual
label-swap reflection. All projection and Gaussian-law interfaces are proved. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set
open scoped BigOperators RealInnerProductSpace Classical ENNReal
namespace NegativeVotingRegularCellReflection
open NegativeVotingLowModeIsometry NegativeVotingProjection NegativeVotingHypercontractivity
  NegativeVotingCellOUContinuity NegativeVotingQuadraticMomentPadding NegativeVotingFan
  NegativeVotingDisintegration NegativeVotingFacetConditionalPlane NegativeVotingWeightedFacet
variable {d : ℕ}

def rawIsometry (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d) : (Fin d→ℝ)→ₗ[ℝ](Fin d→ℝ) where
  toFun x := (T (WithLp.toLp 2 x)).ofLp
  map_add' x y := by change (T (WithLp.toLp 2 x+WithLp.toLp 2 y)).ofLp=_;rw [map_add];rfl
  map_smul' c x := by change (T (c • WithLp.toLp 2 x)).ofLp=_;rw [map_smul];rfl

 theorem rawIsometry_measurePreserving (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d) :
    MeasurePreserving (rawIsometry T) (γFin d) (γFin d) := by
  refine ⟨(rawIsometry T).continuous_of_finiteDimensional.measurable,?_⟩
  have hh := gaussian_coordinate_isometry_map T
  rw [←map_pi_eq_stdGaussian,Measure.map_map (by fun_prop) (by fun_prop)] at hh
  exact hh

 theorem rawIsometry_involutive (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d)
    (hT : Function.Involutive T) : Function.Involutive (rawIsometry T) := by
  intro x
  change (T (WithLp.toLp 2 (T (WithLp.toLp 2 x)).ofLp)).ofLp=x
  rw [WithLp.toLp_ofLp,hT]

 theorem rawIsometry_injective (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d) :
    Function.Injective (rawIsometry T) := by
  intro x y h
  apply WithLp.toLp_injective 2
  apply T.injective
  exact WithLp.ofLp_injective 2 h

 theorem gaussianAverage_comp_rawIsometry (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d)
    (ρ : ℝ) (f : (Fin d→ℝ)→ℝ) (x : Fin d→ℝ) :
    gaussianAverage ρ (fun y=>f (rawIsometry T y)) x=
      gaussianAverage ρ f (rawIsometry T x) := by
  have hi := (rawIsometry_measurePreserving T).integral_comp
    ((rawIsometry T).continuous_of_finiteDimensional.measurableEmbedding (rawIsometry_injective T))
    (fun y=>f (fun j=>ρ*rawIsometry T x j+Real.sqrt (1-ρ^2)*y j))
  have hm (y : Fin d→ℝ) : rawIsometry T (fun j=>ρ*x j+Real.sqrt (1-ρ^2)*y j)=
      fun j=>ρ*rawIsometry T x j+Real.sqrt (1-ρ^2)*rawIsometry T y j := by
    change rawIsometry T (ρ • x+Real.sqrt (1-ρ^2) • y)=_
    rw [map_add,map_smul,map_smul]
    rfl
  unfold gaussianAverage
  simp_rw [hm]
  exact hi

 theorem gaussianAverage_highModes_comp_involution
    (T : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d) (hT : Function.Involutive T)
    (ρ : ℝ) (f : (Fin d→ℝ)→ℝ) (hf : MemLp f 2 (γFin d)) (x : Fin d→ℝ) :
    gaussianAverage ρ (highModes 3 (fun y=>f (rawIsometry T y))) x=
      gaussianAverage ρ (highModes 3 f) (rawIsometry T x) := by
  rw [highModes_comp_involution (rawIsometry T) (rawIsometry_measurePreserving T)
    (rawIsometry_involutive T hT) f hf]
  exact gaussianAverage_comp_rawIsometry T ρ _ x

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def labelReflection (R : ι→FSC.Coord d) (i j : ι) : FSC.Coord d≃ₗᵢ[ℝ]FSC.Coord d :=
  ((ℝ ∙ (R i-R j))ᗮ).reflection

 theorem labelReflection_involutive (R : ι→FSC.Coord d) (i j : ι) :
    Function.Involutive (labelReflection R i j) := Submodule.reflection_involutive _

 theorem labelReflection_apply (R : ι→FSC.Coord d) (a : ℝ)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (x : FSC.Coord d) :
    labelReflection R i j x=x-inner ℝ (R i-R j) x • (R i-R j) := by
  unfold labelReflection
  rw [Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply,
    regular_gram_edge_norm R a hG i j hij]
  change -(2 • (inner ℝ (R i-R j) x/(Real.sqrt 2)^2) • (R i-R j)-x)=_
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  module

 theorem labelReflection_normal_formula (R : ι→FSC.Coord d) (a : ℝ)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (x : FSC.Coord d) :
    labelReflection R i j x=x-(2*inner ℝ (pairNormal R i j) x) • pairNormal R i j := by
  have hrow := regular_gram_rows_ne R a hG i j hij
  have he := edge_eq_norm_smul_pairNormal R i j hrow
  rw [regular_gram_edge_norm R a hG i j hij] at he
  rw [labelReflection_apply R a hG i j hij x,he,real_inner_smul_left,smul_smul]
  have hs : Real.sqrt 2*(inner ℝ (pairNormal R i j) x)*Real.sqrt 2=
      2*inner ℝ (pairNormal R i j) x := by
    nlinarith only [congrArg (fun t:ℝ=>t*inner ℝ (pairNormal R i j) x)
      (Real.sq_sqrt (by norm_num : (0:ℝ)≤2))]
  rw [hs]

 theorem labelReflection_rows (R : ι→FSC.Coord d) (a : ℝ)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (k : ι) :
    labelReflection R i j (R k)=R (Equiv.swap i j k) := by
  rw [labelReflection_apply R a hG i j hij,inner_sub_left,hG,hG]
  by_cases hki : k=i
  · subst k
    simp [hij,hij.symm]
  by_cases hkj : k=j
  · subst k
    simp [hij,hij.symm]
    module
  · simp [hki,hkj,Ne.symm hki,Ne.symm hkj,Equiv.swap_apply_of_ne_of_ne hki hkj]

 theorem cellWeight_labelReflection (R : ι→FSC.Coord d) (a : ℝ)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (k : ι) (x : Fin d→ℝ) :
    cellWeight R 0 k (rawIsometry (labelReflection R i j) x)=
      cellWeight R 0 (Equiv.swap i j k) x := by
  have hs (l : ι) : inner ℝ (R l) (labelReflection R i j (WithLp.toLp 2 x))=
      inner ℝ (R (Equiv.swap i j l)) (WithLp.toLp 2 x) := by
    rw [←labelReflection_rows R a hG i j hij l]
    have hh := (labelReflection R i j).inner_map_map (R l)
      (labelReflection R i j (WithLp.toLp 2 x))
    rw [labelReflection_involutive R i j (WithLp.toLp 2 x)] at hh
    exact hh.symm
  have he : WithLp.toLp 2 (rawIsometry (labelReflection R i j) x)∈winningCell R 0 k ↔
      WithLp.toLp 2 x∈winningCell R 0 (Equiv.swap i j k) := by
    change labelReflection R i j (WithLp.toLp 2 x)∈winningCell R 0 k ↔ _
    simp only [winningCell,mem_setOf_eq,scores,Pi.zero_apply,add_zero,hs]
    constructor
    · intro h l
      simpa only [Equiv.swap_apply_self] using h (Equiv.swap i j l)
    · intro h l
      exact h (Equiv.swap i j l)
  unfold cellWeight
  by_cases hx : WithLp.toLp 2 x∈winningCell R 0 (Equiv.swap i j k)
  · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (he.mpr hx)]
  · simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem (mt he.mp hx)]

/-- The actual high-mode regular potential swaps labels at every point. -/
theorem highModes_average_cell_swap (R : ι→FSC.Coord d) (a : ℝ)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (k : ι) (ρ : ℝ) (x : Fin d→ℝ) :
    gaussianAverage ρ (highModes 3 (cellWeight R 0 k)) (rawIsometry (labelReflection R i j) x)=
      gaussianAverage ρ (highModes 3 (cellWeight R 0 (Equiv.swap i j k))) x := by
  rw [←gaussianAverage_highModes_comp_involution _ (labelReflection_involutive R i j)
    ρ _ (cellWeight_memLp R 0 k) x]
  congr 2
  funext y
  exact cellWeight_labelReflection R a hG i j hij k y

 theorem highModes_average_gap_odd (R : ι→FSC.Coord d) (a : ℝ)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-a)
    (i j : ι) (hij : i≠j) (ρ : ℝ) (x : Fin d→ℝ) :
    (gaussianAverage ρ (highModes 3 (cellWeight R 0 i)) (rawIsometry (labelReflection R i j) x)-
      gaussianAverage ρ (highModes 3 (cellWeight R 0 j)) (rawIsometry (labelReflection R i j) x))=
    -(gaussianAverage ρ (highModes 3 (cellWeight R 0 i)) x-
      gaussianAverage ρ (highModes 3 (cellWeight R 0 j)) x) := by
  rw [highModes_average_cell_swap R a hG i j hij i,
    highModes_average_cell_swap R a hG i j hij j,Equiv.swap_apply_left,Equiv.swap_apply_right]
  ring
end NegativeVotingRegularCellReflection
