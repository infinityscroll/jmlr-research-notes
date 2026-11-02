import GaussianDiagonalOffsetComponentBound
import GaussianHazardUniformMoments
import GaussianRegularDiagonalBalance

/-! Actual selected diagonal offsets: uniform componentwise derivative bounds
from the literal balancing equation and proved all-threshold pair moments. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology RealInnerProductSpace
namespace NegativeVotingDiagonalUniformOffsetBound
open NegativeVotingDiagonalOffsetComponentBound NegativeVotingDiagonalBalanceEquation
  NegativeVotingDiagonalHazardDifferentiation NegativeVotingDiagonalWinnerIntegral
  NegativeVotingDiagonalFacetIntegral NegativeVotingDiagonalBalancedDerivative
  NegativeVotingFanSelectedOffsets NegativeVotingFanInverse NegativeVotingFanJacobian
  NegativeVotingHazardUniformMoments NegativeVotingHazardMomentEnvelope
  NegativeVotingHazardQuantileAsymptotics NegativeVotingGaussianMaximum
  NegativeVotingRegularDiagonalBalance

/-- Transfer the actual affine-line balancing derivative to any differentiable
variance-coordinate path with the same tangent. -/
theorem selected_derivative_of_path {n : ℕ}
    (σp : ℝ → Fin (n+2) → ℝ) (ζ : Fin (n+2) → ℝ) (t : ℝ)
    (hσ : ∀ i,0 < σp t i) (hpath : HasDerivAt σp ζ t)
    (p : Fin (n+2) → ℝ) (hp : ∀ i,0 < p i) (hs : ∑ i,p i=1)
    (k : centeredGauge (Fin (n+2)))
    (hk : HasDerivAt (fun s => selectedOffsets (diagonalRows (parameterLine (σp t) ζ s)) p) k 0) :
    HasDerivAt (fun s => selectedOffsets (diagonalRows (σp s)) p) k t := by
  let f := fun σ : Fin (n+2) → ℝ => selectedOffsets (diagonalRows σ) p
  have hf : DifferentiableAt ℝ f (σp t) :=
    (selected_diagonal_parameters_contDiffAt (σp t) hσ p hp hs).differentiableAt (by norm_num)
  have hf0 : HasFDerivAt f (fderiv ℝ f (σp t)) (parameterLine (σp t) ζ 0) := by
    rw [parameterLine_zero]
    exact hf.hasFDerivAt
  have ha := hf0.comp_hasDerivAt 0 (parameterLine_hasDerivAt (σp t) ζ)
  have he := ha.unique hk
  have ht := hf.hasFDerivAt.comp_hasDerivAt t hpath
  rw [he] at ht
  exact ht

lemma rpow_div_size (m e : ℝ) (hm : 0 < m) : m^e/m=m^(e-1) := by
  rw [Real.rpow_sub hm,Real.rpow_one]

/-- Numerical component estimate before absorbing the remaining quantile
factor. The actual Laplacian diagonal is treated by cancellation. -/
theorem selected_component_bound_of_pair_bounds {n : ℕ}
    (m : ℝ) (hm : m=(n:ℝ)+2) (η a b : ℝ) (hη : 0 < η)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (σ ζ ξ : Fin (n+2) → ℝ) (hσ : ∀ i,0 < σ i)
    (p : Fin (n+2) → ℝ) (hp : ∀ i,0 < p i) (hs : ∑ i,p i=1)
    (hh : ∀ i,|(selectedOffsets (diagonalRows σ) p : Fin (n+2) → ℝ) i| ≤ a*b)
    (hz : ∀ i,|ζ i/σ i| ≤ 2*|ξ i|)
    (hlower : ∀ i j,i≠j → m^(-2-η/2) ≤ ∫x,hazardPairDensity σ (selectedOffsets (diagonalRows σ) p) x i j)
    (hupper : ∀ i j,i≠j → (∫x,hazardPairDensity σ (selectedOffsets (diagonalRows σ) p) x i j) ≤ m^(-2+η/2))
    (hmoment : ∀ i j,i≠j → (∫x,hazardPairDensity σ (selectedOffsets (diagonalRows σ) p) x i j*(1+|x|)) ≤ m^(-2+η/2)) :
    ∃ k : centeredGauge (Fin (n+2)),
      HasDerivAt (fun t => selectedOffsets (diagonalRows (parameterLine σ ζ t)) p) k 0 ∧
      ∀ i,|(k : Fin (n+2) → ℝ) i| ≤ 6*(1+b)*m^(2*η)*(|ξ i|+meanAbs ξ) := by
  have hm0 : 0 < m := by rw [hm];positivity
  have hm1 : 1 ≤ m := by rw [hm];linarith [Nat.cast_nonneg (α:=ℝ) n]
  let h : Fin (n+2) → ℝ := selectedOffsets (diagonalRows σ) p
  let lo := m^(-1-η/2)
  let up := m^(-1+η/2)
  let B := 2*(1+a*b)*up
  have hlo : 0 < lo := Real.rpow_pos_of_pos hm0 _
  have hlu : lo ≤ up := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hB : 0 ≤ B := by dsimp [B,up];positivity
  have hweightslo : ∀ i j,i≠j → lo/(Fintype.card (Fin (n+2)):ℝ) ≤ facetWeight (diagonalRows σ) h i j := by
    intro i j hij
    rw [facetWeight_diagonal_integral σ h hσ i j hij]
    have he : lo/(Fintype.card (Fin (n+2)):ℝ)=m^(-2-η/2) := by
      simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,←hm]
      rw [rpow_div_size _ _ hm0]
      congr 1
      ring
    rw [he]
    exact hlower i j hij
  have hweightsup : ∀ i j,i≠j → facetWeight (diagonalRows σ) h i j ≤ up/(Fintype.card (Fin (n+2)):ℝ) := by
    intro i j hij
    rw [facetWeight_diagonal_integral σ h hσ i j hij]
    have he : up/(Fintype.card (Fin (n+2)):ℝ)=m^(-2+η/2) := by
      simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,←hm]
      rw [rpow_div_size _ _ hm0]
      congr 1
      ring
    rw [he]
    exact hupper i j hij
  have hbsource (i : Fin (n+2)) : |-varianceForcing σ h ζ i| ≤ B*(|ξ i|+meanAbs ξ) := by
    rw [abs_neg]
    have hbase := varianceForcing_component_le σ h ζ ξ hσ 2 (a*b) (m^(-2+η/2))
      (by norm_num) (mul_nonneg ha hb) (Real.rpow_nonneg hm0.le _) hz hh hmoment i
    apply hbase.trans_eq
    have he : m*m^(-2+η/2)=up := by
      dsimp [up]
      calc
        _ = m^(1:ℝ)*m^(-2+η/2) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hm0];congr 1;ring
    dsimp [B,meanAbs]
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,←hm]
    rw [←he]
    field_simp <;> ring
  obtain ⟨k,hk,heq⟩ := exists_selected_diagonal_laplacian_equation σ ζ hσ p hp hs
  have hbnd := weighted_source_component_bound (facetWeight (diagonalRows σ) h)
    (facetWeight_symm _ _) lo up B hlo hlu hB hweightslo hweightsup
    k (fun i => -varianceForcing σ h ζ i) ξ k.property heq hbsource
  have hratio : up/lo=m^η := by
    dsimp [up,lo]
    rw [←Real.rpow_sub hm0]
    congr 1
    ring
  have hratioB : B/lo=2*(1+a*b)*m^η := by dsimp [B];rw [mul_div_assoc,hratio]
  have hr1 : 1 ≤ m^η := Real.one_le_rpow hm1 hη.le
  have hcoef : B/lo*(1+2*up/lo) ≤ 6*(1+b)*m^(2*η) := by
    rw [hratioB,show 2*up/lo=2*(up/lo) by ring,hratio,
      show 2*η=η+η by ring,Real.rpow_add hm0]
    have hab : a*b ≤ b := by nlinarith
    have hfirst : 2*(1+a*b)*m^η ≤ 2*(1+b)*m^η :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hm0.le _)
    have hsecond : 1+2*m^η ≤ 3*m^η := by linarith
    have ht := mul_le_mul hfirst hsecond (by positivity : (0:ℝ) ≤ 1+2*m^η)
      (by positivity : (0:ℝ) ≤ 2*(1+b)*m^η)
    nlinarith only [ht]
  exact ⟨k,hk,fun i => (hbnd i).trans (mul_le_mul_of_nonneg_right hcoef (by positivity [meanAbs_nonneg ξ]))⟩

/-- Genuine selected-offset derivative bound at every model in a uniform box.
Neither a derivative nor a normalized moment estimate is assumed. -/
theorem exists_uniform_selected_offset_bound (η : ℝ) (hη : 0 < η) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, ∀ (σ ζ ξ : Fin (n+2) → ℝ)
        (p : Fin (n+2) → ℝ), (∀ i,0 < p i) → (∑ i,p i)=1 →
        (∀ i,1-a ≤ σ i) → (∀ i,σ i ≤ 1+a) →
        (∀ i,|(selectedOffsets (diagonalRows σ) p : Fin (n+2) → ℝ) i| ≤ a*upperQuantile n) →
        (∀ i,|ζ i/σ i| ≤ 2*|ξ i|) →
        ∃ k : centeredGauge (Fin (n+2)),
          HasDerivAt (fun t => selectedOffsets (diagonalRows (parameterLine σ ζ t)) p) k 0 ∧
          ∀ i,|(k : Fin (n+2) → ℝ) i| ≤ ((n:ℝ)+2)^(3*η)*(|ξ i|+meanAbs ξ) := by
  obtain ⟨a,ha,ha1,hmom⟩ := exists_uniform_box_moment_family η hη 0 1
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards [hmom,eventually_quantile_polynomial_le_rpow 6 (by norm_num) 1 η hη,
    upperQuantile_tendsto.eventually_ge_atTop 1] with n hmoment hpoly hb
  intro σ ζ ξ p hp hs hσlo hσhi hh hz
  have hσ : ∀ i,0 < σ i := fun i => lt_of_lt_of_le (by linarith) (hσlo i)
  have h0 := hmoment 0 0 (by omega) (by omega) σ (selectedOffsets (diagonalRows σ) p) hσlo hσhi hh
  have h1 := hmoment 0 1 (by omega) (by omega) σ (selectedOffsets (diagonalRows σ) p) hσlo hσhi hh
  have hp0 (i j : Fin (n+2)) : (∫x,momentDensity σ (selectedOffsets (diagonalRows σ) p) 0 0 i j x)=
      ∫x,hazardPairDensity σ (selectedOffsets (diagonalRows σ) p) x i j := by simp [momentDensity]
  have hp1 (i j : Fin (n+2)) : (∫x,momentDensity σ (selectedOffsets (diagonalRows σ) p) 0 1 i j x)=
      ∫x,hazardPairDensity σ (selectedOffsets (diagonalRows σ) p) x i j*(1+|x|) := by simp [momentDensity]
  obtain ⟨k,hk,hbound⟩ := selected_component_bound_of_pair_bounds ((n:ℝ)+2) rfl η a (upperQuantile n)
    hη ha.le (by linarith) (by linarith) σ ζ ξ hσ p hp hs hh hz
    (fun i j _ => (h0 i j).1)
    (fun i j _ => by simpa only [hp0] using (h0 i j).2.1)
    (fun i j _ => by simpa only [hp1] using (h1 i j).2.1)
  refine ⟨k,hk,fun i => (hbound i).trans ?_⟩
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hc : 6*(1+upperQuantile n)*((n:ℝ)+2)^(2*η) ≤ ((n:ℝ)+2)^(3*η) := by
    have ht := mul_le_mul_of_nonneg_right (by simpa only [pow_one] using hpoly)
      (Real.rpow_nonneg hm.le (2*η))
    apply ht.trans_eq
    rw [←Real.rpow_add hm]
    congr 1
    ring
  exact mul_le_mul_of_nonneg_right hc (by positivity [meanAbs_nonneg ξ])

end NegativeVotingDiagonalUniformOffsetBound
