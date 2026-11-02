import GaussianRegularFacetStability

/-! An explicit dimension-independent covariance/offset neighborhood in which
all actual regular-fan facet weights are strictly comparable to their reference. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingRegularFacetNeighborhood
open NegativeVotingFacetConditionalPlane NegativeVotingRegularFacetStability
  NegativeVotingBalancedReference NegativeVotingFanJacobian NegativeVotingAffineLogMassBound
  NegativeVotingAffineNormControl
variable {n d : ℕ}

def facetRadius (q : ℝ) : ℝ :=
  min (1/(64*Real.exp 1))
    (min (1/2) (Real.log 2/(4*(4096*(Real.exp 1)^3)*(1+q+q^2))))

theorem facetRadius_bounds (q : ℝ) (hq : 0 ≤ q) :
    0 < facetRadius q ∧ facetRadius q ≤ 1 ∧
      32*Real.exp 1*facetRadius q ≤ 1 ∧
      (4096*(Real.exp 1)^3)*(1+q+q^2)*facetRadius q < Real.log 2 := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hQ : 0 < 1+q+q^2 := by nlinarith [sq_nonneg q]
  have hc : 0 < facetRadius q := by unfold facetRadius; positivity
  have h1 : facetRadius q ≤ 1/(64*Real.exp 1) := min_le_left _ _
  have h2 : facetRadius q ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : facetRadius q ≤ Real.log 2/(4*(4096*(Real.exp 1)^3)*(1+q+q^2)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hm1 := (le_div_iff₀ (show 0 < 64*Real.exp 1 by positivity)).mp h1
  have hm3 := (le_div_iff₀ (show 0 < 4*(4096*(Real.exp 1)^3)*(1+q+q^2) by positivity)).mp h3
  exact ⟨hc,by linarith,by nlinarith,by nlinarith⟩

private theorem neighborhood_size (q L ε z : ℝ) (hq : 0 ≤ q) (hL : 1 ≤ L)
    (hε : 0 ≤ ε) (hz : 0 ≤ z) (hεc : ε ≤ facetRadius q/L)
    (hzq : z ≤ q*Real.sqrt L*ε) :
    32*Real.exp 1*ε ≤ 1 ∧
      4096*(Real.exp 1)^3*(ε*L+z*Real.sqrt L+z^2) < Real.log 2 := by
  obtain ⟨hc,hc1,hcsmall,hclog⟩ := facetRadius_bounds q hq
  have hLp : 0 < L := by linarith
  have hεL : ε*L ≤ facetRadius q := (le_div_iff₀ hLp).mp hεc
  have hεone : ε ≤ facetRadius q := by
    have hh := mul_le_mul_of_nonneg_left hL hε
    nlinarith
  have hsmall := (mul_le_mul_of_nonneg_left hεone (show 0 ≤ 32*Real.exp 1 by positivity)).trans hcsmall
  have hs := Real.sq_sqrt hLp.le
  have hshift : z*Real.sqrt L ≤ q*facetRadius q := by
    have hh := mul_le_mul_of_nonneg_right hzq (Real.sqrt_nonneg L)
    have he : q*Real.sqrt L*ε*Real.sqrt L=q*(ε*L) := by nlinarith [congrArg (fun x : ℝ=>q*ε*x) hs]
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hεL hq)
  have hεsq : ε^2*L ≤ (facetRadius q)^2 := by
    have hh := mul_le_mul hεone hεL (mul_nonneg hε hLp.le) hc.le
    nlinarith
  have hzs : z^2 ≤ q^2*(facetRadius q)^2 := by
    have hh := pow_le_pow_left₀ hz hzq 2
    have he : (q*Real.sqrt L*ε)^2=q^2*(ε^2*L) := by
      nlinarith [congrArg (fun x : ℝ=>q^2*ε^2*x) hs]
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hεsq (sq_nonneg q))
  have hcsq : (facetRadius q)^2 ≤ facetRadius q := by nlinarith
  have hzsq := hzs.trans (mul_le_mul_of_nonneg_left hcsq (sq_nonneg q))
  have hsum : ε*L+z*Real.sqrt L+z^2 ≤ (1+q+q^2)*facetRadius q := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4096*(Real.exp 1)^3 by positivity)
  refine ⟨hsmall,hh.trans_lt ?_⟩
  nlinarith

/-- One explicit positive radius is chosen before the dimension, rows, facet,
and covariance. This is the strict improvement region for the balanced-offset
continuation; the actual offset bound is the sole remaining path input. -/
theorem regular_facetWeight_neighborhood (q : ℝ) (hq : 0 ≤ q)
    (hn : 0 < n) (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (S : FSC.Coord d ≃L[ℝ] FSC.Coord d) (hS : S.toLinearMap.IsSymmetric)
    (hsmall : operatorHilbertSchmidt (covarianceError S) ≤
      facetRadius q/(1+Real.log ((n:ℝ)+2))) (h : FSC.Coord d)
    (hshift : ‖h‖ ≤ q*Real.sqrt (1+Real.log ((n:ℝ)+2))*operatorHilbertSchmidt (covarianceError S))
    (i j : Fin (n+2)) (hij : i≠j) :
    (referenceScale n/((n:ℝ)+2))/2 < facetWeight (transportedRows S B) (scoreOffsets B h) i j ∧
      facetWeight (transportedRows S B) (scoreOffsets B h) i j < 2*(referenceScale n/((n:ℝ)+2)) := by
  have hL : 1 ≤ 1+Real.log ((n:ℝ)+2) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ (n:ℝ)+2 by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
    linarith
  obtain ⟨hsize,hlog⟩ := neighborhood_size q (1+Real.log ((n:ℝ)+2))
    (operatorHilbertSchmidt (covarianceError S)) ‖h‖ hq hL
    (operatorHilbertSchmidt_nonneg _) (norm_nonneg h) hsmall hshift
  exact regular_facetWeight_strict_comparable hn hmean B hG S hS hsize h hlog i j hij

end NegativeVotingRegularFacetNeighborhood
