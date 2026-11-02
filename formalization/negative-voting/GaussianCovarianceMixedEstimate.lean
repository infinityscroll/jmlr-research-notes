import GaussianCovarianceRefinedCurvature

/-! Extracting the mixed offset control from the actual cycle-refined Hessian. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingCovarianceMixed
open NegativeVotingFanCycle NegativeVotingFanCycleBridge NegativeVotingFanCycleHessian
  NegativeVotingFan NegativeVotingWeightedFacet NegativeVotingFanJacobian
  NegativeVotingFanCovarianceEnvelope NegativeVotingFanCanonicalOffset NegativeVotingCapTail
  NegativeVotingAffineBasisLower
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The normal projection in the Hessian is exactly the scalar normal strain. -/
theorem normal_projection_pair_sq (b : AffineBasis V ℝ (FSC.Coord d))
    (i j : V) (hij : i ≠ j) (v : FSC.Coord d) :
    ‖(faceDirection b {i,j}).starProjection v‖^2 = (inner ℝ (pairNormal b i j) v)^2 := by
  have hw := pairNormal_norm b i j (b.ind.injective.ne hij)
  rw [faceDirection_pair_normal b i j hij,Submodule.starProjection_unit_singleton ℝ hw,
    norm_smul,Real.norm_eq_abs,hw,mul_one,sq_abs]

/-- Completing one real square retains the normal-anchor correction. -/
theorem offset_sq_le_refined (a q x beta : ℝ) (ha : 0 < a) :
    beta^2 ≤ (1/a+q^2)*(x^2+a*(beta+q*x)^2) := by
  have he : a*((1/a+q^2)*(x^2+a*(beta+q*x)^2)-beta^2) =
      (x+a*q*(beta+q*x))^2 := by
    field_simp [ne_of_gt ha]
    <;> ring
  have hn : 0 ≤ a*((1/a+q^2)*(x^2+a*(beta+q*x)^2)-beta^2) := by
    rw [he]
    exact sq_nonneg _
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp hn)

/-- The scalar completion applies to the literal Gaussian affine face. -/
theorem offset_sq_le_geometric_energy (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (z : V → FSC.Coord d) (beta : V → ℝ) (i j : V) (a : ℝ) (ha : 0 < a) :
    (beta i-beta j)^2 ≤ (1/a+(pairOffset b h i j)^2)*
      (‖(faceDirection b {i,j}).starProjection (z i-z j)‖^2+
        a*((beta i-beta j)+inner ℝ (z i-z j) (faceAnchor b h {i,j}))^2) := by
  by_cases hij : i=j
  · subst j; simp
  · rw [normal_projection_pair_sq b i j hij,faceAnchor_pair b h i j hij,
      inner_smul_right,real_inner_comm (z i-z j) (pairNormal b i j)]
    exact offset_sq_le_refined a (pairOffset b h i j) (inner ℝ (z i-z j) (pairNormal b i j))
      (beta i-beta j) ha

/-- The explicit coefficient already proved for the actual intrinsic Gaussian probability. -/
def facetLogCoefficient (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ) (i j : V) : ℝ :=
  Real.exp (-4)/(2*(1+2*Real.log (1/cycleIntrinsicProbability b h i j)))

theorem facetLogCoefficient_pos (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (hcard : 3 ≤ Fintype.card V) (i j : V) : 0 < facetLogCoefficient b h i j := by
  have hp := cycleIntrinsicProbability_mem_Ioo b h hcard i j
  have hlog : 0 ≤ Real.log (1/cycleIntrinsicProbability b h i j) :=
    Real.log_nonneg ((one_le_div hp.1).mpr hp.2.le)
  unfold facetLogCoefficient
  exact div_pos (Real.exp_pos _) (by positivity)

/-- Retention is defined using the actual analytic Jacobian edge weight. -/
def retainedOffsetEnergy (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (tau : ℝ) (v : V → ℝ) : ℝ :=
  (1/2:ℝ)*∑ i, ∑ j, if tau ≤ facetWeight b h i j then
    facetWeight b h i j*(v i-v j)^2 else 0


/-- Retained offset energy is controlled by the actual full refined energy.
The finite coefficient ceiling is stated only on the retained, genuine facets. -/
theorem retainedOffsetEnergy_le_refined (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (hcard : 3 ≤ Fintype.card V) (z : V → FSC.Coord d) (beta : V → ℝ)
    (tau K : ℝ) (hK : 0 ≤ K)
    (hcoeff : ∀ i j, i ≠ j → tau ≤ facetWeight b h i j →
      1/facetLogCoefficient b h i j+(pairOffset b h i j)^2 ≤ K) :
    retainedOffsetEnergy b h tau beta ≤ K*(normalEdgeEnergy b h z+
      (1/2:ℝ)*∑ i, ∑ j, cycleEdgeWeight b h i j*facetLogCoefficient b h i j*
        ((beta i-beta j)+inner ℝ (z i-z j) (faceAnchor b h {i,j}))^2) := by
  let e : V → V → ℝ := fun i j =>
    ‖(faceDirection b {i,j}).starProjection (z i-z j)‖^2+
      facetLogCoefficient b h i j*((beta i-beta j)+inner ℝ (z i-z j) (faceAnchor b h {i,j}))^2
  have he (i j : V) : 0 ≤ e i j :=
    add_nonneg (sq_nonneg _) (mul_nonneg (facetLogCoefficient_pos b h hcard i j).le (sq_nonneg _))
  have hp (i j : V) :
      (if tau ≤ facetWeight b h i j then facetWeight b h i j*(beta i-beta j)^2 else 0) ≤
        K*(cycleEdgeWeight b h i j*e i j) := by
    by_cases hij : i=j
    · subst j
      simp only [sub_self,zero_pow (by norm_num : 2 ≠ 0),mul_zero,ite_self]
      exact mul_nonneg hK (mul_nonneg (cycleEdgeWeight_pos b h i i).le (he i i))
    · by_cases ht : tau ≤ facetWeight b h i j
      · rw [if_pos ht,← cycleEdgeWeight_eq_facetWeight b h i j hij]
        have ho := (offset_sq_le_geometric_energy b h z beta i j _
          (facetLogCoefficient_pos b h hcard i j)).trans
          (mul_le_mul_of_nonneg_right (hcoeff i j hij ht) (he i j))
        have hw := mul_le_mul_of_nonneg_left ho (cycleEdgeWeight_pos b h i j).le
        convert hw using 1 <;> ring
      · rw [if_neg ht]
        exact mul_nonneg hK (mul_nonneg (cycleEdgeWeight_pos b h i j).le (he i j))
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp i j))) (by norm_num : (0:ℝ) ≤ 1/2)
  change retainedOffsetEnergy b h tau beta ≤ (1/2:ℝ)*∑ i, ∑ j, K*(cycleEdgeWeight b h i j*e i j) at hs
  convert hs using 1
  unfold normalEdgeEnergy e
  simp_rw [mul_add,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

/-- The actual canonical offset derivative is controlled by covariance curvature
once the retained graph gap and facet coefficient ceiling have been established.
Both remaining inputs concern the explicit finite Gaussian graph. -/
theorem canonicalOffset_half_sq_le_curvature (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (hcard : 3 ≤ Fintype.card V) (H : FSC.Coord d →L[ℝ] FSC.Coord d)
    (tau K lambda : ℝ) (hK : 0 ≤ K)
    (hcoeff : ∀ i j, i ≠ j → tau ≤ facetWeight b h i j →
      1/facetLogCoefficient b h i j+(pairOffset b h i j)^2 ≤ K)
    (hgap : ∀ v : V → ℝ, (∑ i, v i)=0 →
      lambda*(∑ i, (v i)^2) ≤ retainedOffsetEnergy b h tau v) :
    lambda*(∑ i, (canonicalOffsetVariation b h (rowsOfOperator b H) i/2)^2) ≤
      K*(-covarianceHessianValue b h H) := by
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound b
  let beta := canonicalOffsetVariation b h (rowsOfOperator b H)
  have hr := hgap beta (canonicalOffsetVariation_centered b (rowsOfOperator b H) h σ hσ hlower)
  have hb := retainedOffsetEnergy_le_refined b h hcard (rowsOfOperator b H) beta tau K hK hcoeff
  have hc := covarianceHessianValue_log_ehrhard_bound b h σ hσ hlower hcard H
  have he (i j : V) : rowsOfOperator b H i-rowsOfOperator b H j=H (b i-b j) := by
    change H (b i)-H (b j)=H (b i-b j)
    rw [map_sub]
  simp_rw [he] at hb
  change retainedOffsetEnergy b h tau beta ≤ K*(normalEdgeEnergy b h (rowsOfOperator b H)+
    (1/2:ℝ)*∑ i, ∑ j, cycleEdgeWeight b h i j*facetLogCoefficient b h i j*
      ((beta i-beta j)+inner ℝ (H (b i-b j)) (faceAnchor b h {i,j}))^2) at hb
  change covarianceHessianValue b h H ≤ -(1/4:ℝ)*normalEdgeEnergy b h (rowsOfOperator b H)-
    (1/8:ℝ)*∑ i, ∑ j, cycleEdgeWeight b h i j*facetLogCoefficient b h i j*
      ((beta i-beta j)+inner ℝ (H (b i-b j)) (faceAnchor b h {i,j}))^2 at hc
  have hh := mul_le_mul_of_nonneg_left hc hK
  have hs : (∑ i, (beta i/2)^2) = (∑ i, (beta i)^2)/4 := by
    simp only [div_pow]
    rw [← Finset.sum_div]
    norm_num
  change lambda*(∑ i, (beta i/2)^2) ≤ K*(-covarianceHessianValue b h H)
  rw [hs]
  nlinarith

end NegativeVotingCovarianceMixed
