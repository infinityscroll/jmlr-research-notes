import GaussianFanCycleResidual
import GaussianEhrhardCoefficient

/-! Ehrhard refinement on actual intrinsic Gaussian winner strata. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
open NegativeVotingEhrhard
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A proper score stratum has intrinsic cap probability strictly below one:
a derived unit normal provides a nonempty open Gaussian complement. -/
theorem coordinateCap_mass_lt_one (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : V) (hk : k ∉ S) :
    FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i) < 1 := by
  let k₀ : {k : V // k ∉ S} := ⟨k,hk⟩
  let n := coordinateCapNormal b S i k₀
  let c := intrinsicCapOffset b h S i k₀
  let U : Set (FaceCoordinates b S) := {x | c < ⟪n,x⟫}
  have hn : ‖n‖=1 := coordinateCapNormal_norm b S i hi k₀
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hpoint : (c+1) • n ∈ U := by
    change c < ⟪n,(c+1) • n⟫
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hn]
    linarith
  have hpos := FSC.stdGaussian_pos_of_isOpen hU ⟨(c+1) • n,hpoint⟩
  have hsub : U ⊆ (coordinateCap b h S i)ᶜ := by
    intro x hx hcap
    exact (not_lt_of_ge (hcap k₀)) hx
  have hcompl : 0 < stdGaussian (FaceCoordinates b S) (coordinateCap b h S i)ᶜ :=
    lt_of_lt_of_le hpos (measure_mono hsub)
  have hreal : 0 < (stdGaussian (FaceCoordinates b S)).real (coordinateCap b h S i)ᶜ :=
    ENNReal.toReal_pos hcompl.ne' (measure_ne_top _ _)
  have hsum := probReal_add_probReal_compl (μ := stdGaussian (FaceCoordinates b S))
    (FSC.measurableSet_cap (coordinateCapNormal b S i) (intrinsicCapOffset b h S i))
  change FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)+
    (stdGaussian (FaceCoordinates b S)).real (coordinateCap b h S i)ᶜ=1 at hsum
  linarith

/-- Ehrhard is applied to the literal intrinsic cap. Its mean correction is
the ambient conditioned mean minus the actual perpendicular affine anchor. -/
theorem stratumDeficit_ehrhard (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (k : V) (hk : k ∉ S) (v : E) :
    ehrhardCoefficient (FSC.capMass (coordinateCapNormal b S i) (intrinsicCapOffset b h S i)) *
      (stratumMeanPairing b h S i v-⟪v,faceAnchor b h S⟫)^2 ≤
        stratumDeficit b h S i v v := by
  let w := coordinateCapNormal b S i
  let c := intrinsicCapOffset b h S i
  let u := coordinateDual b S v
  have hp : polyhedronMass w c ∈ Ioo (0:ℝ) 1 :=
    ⟨coordinateCap_mass_pos b h S i hi,coordinateCap_mass_lt_one b h S i hi k hk⟩
  have he := gaussian_polyhedron_ehrhard_conditional_variance_le w c hp u
  have hv : polyhedronConditionalVariance w c u = stratumDirectionalVariance b h S i v := by
    unfold polyhedronConditionalVariance stratumDirectionalVariance polyhedronMoment
    simp_rw [coordinateEmbed_pairing,stratumMeanPairing_eq b h S i hi,
      add_sub_add_left_eq_sub,pow_one]
    rfl
  have hm : polyhedronMoment w c u 1/polyhedronMass w c =
      stratumMeanPairing b h S i v-⟪v,faceAnchor b h S⟫ := by
    rw [stratumMeanPairing_eq b h S i hi]
    simp only [polyhedronMoment,pow_one,polyhedronMass,closedPolyhedron,
      coordinateCap,FSC.capMass,FSC.cap,w,c,u]
    ring
  change polyhedronConditionalVariance w c u ≤ ‖u‖^2-
    ehrhardCoefficient (FSC.capMass w c)*(polyhedronMoment w c u 1/polyhedronMass w c)^2 at he
  rw [hv,hm] at he
  change stratumDirectionalVariance b h S i v ≤ ‖coordinateDual b S v‖^2-
    ehrhardCoefficient (FSC.capMass w c)*(stratumMeanPairing b h S i v-⟪v,faceAnchor b h S⟫)^2 at he
  rw [coordinateDual_norm] at he
  rw [stratumDeficit_self b h S i hi]
  linarith

theorem exists_vertex_outside_pair (hcard : 3 ≤ Fintype.card V) (a j : V) :
    ∃ k : V, k ∉ ({a,j}:Set V) := by
  by_contra hn
  push_neg at hn
  have hsub : (Finset.univ : Finset V) ⊆ {a,j} := by
    intro k _
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_insert,Finset.mem_singleton] using hn k
  have hc := Finset.card_le_card hsub
  have hp : ({a,j} : Finset V).card ≤ 2 := by
    simpa using Finset.card_insert_le a ({j} : Finset V)
  rw [Finset.card_univ] at hc
  omega

/-- The genuine intrinsic Gaussian probability on the edge's winner stratum. -/
def cycleIntrinsicProbability (b : AffineBasis V ℝ E) (h : V → ℝ) (a j : V) : ℝ :=
  FSC.capMass (coordinateCapNormal b {a,j} a) (intrinsicCapOffset b h {a,j} a)

theorem cycleIntrinsicProbability_mem_Ioo (b : AffineBasis V ℝ E) (h : V → ℝ)
    (hcard : 3 ≤ Fintype.card V) (a j : V) : cycleIntrinsicProbability b h a j ∈ Ioo (0:ℝ) 1 := by
  obtain ⟨k,hk⟩ := exists_vertex_outside_pair hcard a j
  exact ⟨coordinateCap_mass_pos b h {a,j} a (by simp),
    coordinateCap_mass_lt_one b h {a,j} a (by simp) k hk⟩

/-- The actual weighted facet deficit contains the exact Ehrhard rank-one
mean term; no intrinsic-facet probability estimate is assumed. -/
theorem cycleDeficit_ehrhard (b : AffineBasis V ℝ E) (h : V → ℝ)
    (hcard : 3 ≤ Fintype.card V) (a j : V) (v : E) :
    cycleEdgeWeight b h a j * ehrhardCoefficient (cycleIntrinsicProbability b h a j) *
      (stratumMeanPairing b h {a,j} a v-⟪v,faceAnchor b h {a,j}⟫)^2 ≤
        cycleDeficit b h a j v v := by
  obtain ⟨k,hk⟩ := exists_vertex_outside_pair hcard a j
  have he := stratumDeficit_ehrhard b h {a,j} a (by simp) k hk v
  have hw := mul_le_mul_of_nonneg_left he (cycleEdgeWeight_pos b h a j).le
  simpa only [cycleDeficit,cycleIntrinsicProbability,mul_assoc] using hw


/-- Ehrhard is applied after subtraction of the entire cycle energy, to the
actual residual vectors. The global-offset and normal-anchor terms are retained. -/
theorem actual_cycle_ehrhard_bound (b : AffineBasis V ℝ E) (h : V → ℝ)
    (hcard : 3 ≤ Fintype.card V) (z : V → E) (beta : V → ℝ) (r : V)
    (hc : ∀ a, edgeBoundary (cycleFlux b h z beta) a = 0) :
    (1/2:ℝ) * (∑ a, ∑ j, cycleEdgeWeight b h a j *
      ehrhardCoefficient (cycleIntrinsicProbability b h a j) *
      ((beta a-beta j)+⟪z a-z j,faceAnchor b h {a,j}⟫)^2) ≤
    ((1/2:ℝ) * ∑ a, ∑ j, cycleDeficit b h a j (z a-z j) (z a-z j))-
      cycleMeanEnergy b h (cycleFlux b h z beta) := by
  obtain ⟨lam,hlam,hfill,_,he⟩ := exists_actual_cycle_residual b h z beta r hc
  rw [he]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro j _
  have hb := cycleDeficit_ehrhard b h hcard a j (cycleResidual b h z lam a j)
  rw [cycleResidual_tangential_mean b h z beta lam hlam hfill] at hb
  convert hb using 1 <;> ring

/-- The explicit quantitative coefficient depends on the actual intrinsic
facet probability, with no substitution of a cell mass or an assumed log m bound. -/
theorem actual_cycle_log_ehrhard_bound (b : AffineBasis V ℝ E) (h : V → ℝ)
    (hcard : 3 ≤ Fintype.card V) (z : V → E) (beta : V → ℝ) (r : V)
    (hc : ∀ a, edgeBoundary (cycleFlux b h z beta) a = 0) :
    (1/2:ℝ) * (∑ a, ∑ j, cycleEdgeWeight b h a j *
      (Real.exp (-4)/(2*(1+2*Real.log (1/cycleIntrinsicProbability b h a j)))) *
      ((beta a-beta j)+⟪z a-z j,faceAnchor b h {a,j}⟫)^2) ≤
    ((1/2:ℝ) * ∑ a, ∑ j, cycleDeficit b h a j (z a-z j) (z a-z j))-
      cycleMeanEnergy b h (cycleFlux b h z beta) := by
  apply le_trans ?_ (actual_cycle_ehrhard_bound b h hcard z beta r hc)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (ehrhardCoefficient_log_mass_lower (cycleIntrinsicProbability_mem_Ioo b h hcard a j))
    (cycleEdgeWeight_pos b h a j).le

end NegativeVotingFanCycle
