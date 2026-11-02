import GaussianFanCycleDeficit
import GaussianFanCycleBalance

/-! Actual Gaussian cycle corrections and the exact residual deficit energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycle
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem stratumMeanPairing_sub (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (u v : E) :
    stratumMeanPairing b h S i (u-v) =
      stratumMeanPairing b h S i u-stratumMeanPairing b h S i v := by
  simp only [stratumMeanPairing,inner_sub_left]
  rw [integral_sub (coordinateEmbed_pairing_integrable b h S i u)
    (coordinateEmbed_pairing_integrable b h S i v),sub_div]

theorem stratumMeanPairing_smul (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (c : ℝ) (v : E) :
    stratumMeanPairing b h S i (c • v) = c * stratumMeanPairing b h S i v := by
  simp only [stratumMeanPairing,real_inner_smul_left,integral_const_mul]
  ring

theorem cycleMean_sub (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j k : V) (u v : E) : cycleMean b h a j k (u-v) =
      cycleMean b h a j k u-cycleMean b h a j k v :=
  stratumMeanPairing_sub b h {a,j,k} a u v

/-- The actual triangle mean term cancels for global cell vectors. This uses
the same triangle mean on all three boundary edges. -/
theorem cycleMean_gradient_sum_zero (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) (hlam : AlternatingTriangle lam) (z : V → E) :
    (∑ a, ∑ j, ∑ k, lam k a j * cycleMean b h k a j (z a-z j)) = 0 := by
  let U := ∑ a, ∑ j, ∑ k, lam a j k * cycleMean b h a j k (z a-z j)
  let T := ∑ a, ∑ j, ∑ k, lam a j k * cycleMean b h a j k (z j-z k)
  let W := ∑ a, ∑ j, ∑ k, lam a j k * cycleMean b h a j k (z k-z a)
  have hU : (∑ a, ∑ j, ∑ k, lam k a j * cycleMean b h k a j (z a-z j)) = U := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hlam.2 k a j,cycleMean_cyclic b h k a j]
  have hUW : U = W := by
    unfold U W
    rw [sum_triple_rotate (fun a j k => lam a j k * cycleMean b h a j k (z a-z j))]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hlam.2 k a j,cycleMean_cyclic b h k a j]
  have hWT : W = T := by
    unfold W T
    rw [sum_triple_rotate (fun a j k => lam a j k * cycleMean b h a j k (z k-z a))]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hlam.2 k a j,cycleMean_cyclic b h k a j]
  have hsum : U+T+W = 0 := by
    unfold U T W
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    simp only [cycleMean_sub]
    ring
  rw [hU]
  linarith

/-- Actual covariance pairing with the correction, before summing over edges. -/
theorem cycleDeficit_correction_right (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) (hlam : AlternatingTriangle lam) (a j : V) (u : E) :
    cycleDeficit b h a j u (cycleCorrection b h lam a j) =
      ∑ k, lam k a j * (stratumMeanPairing b h {a,j} a u-cycleMean b h k a j u) := by
  unfold cycleCorrection cycleDeficit
  rw [stratumDeficit_sum_right b h {a,j} a (by simp),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [stratumDeficit_smul_right b h {a,j} a (by simp)]
  by_cases hz : lam k a j = 0
  · simp [hz]
  obtain ⟨hka,hkj,haj⟩ := alternatingTriangle_nonzero_distinct lam hlam k a j hz
  calc
    _ = lam k a j * (cycleTriangleWeight b h k a j *
        cycleDeficit b h a j (barycentricOutwardVector b k) u) := by
      rw [cycleDeficit,stratumDeficit_symmetric b h {a,j} a u (barycentricOutwardVector b k)]
      ring
    _ = _ := by rw [cycleDeficit_barycentric_column b h a j k haj hka hkj]

/-- The cross term uses the actual graph gradient z_a-z_j; triangle terms
cancel exactly, leaving the boundary cycle paired with the actual facet mean. -/
theorem cycleDeficit_gradient_correction_pairing (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) (hlam : AlternatingTriangle lam) (z : V → E) :
    (∑ a, ∑ j, cycleDeficit b h a j (z a-z j) (cycleCorrection b h lam a j)) =
      ∑ a, ∑ j, triangleBoundary lam a j * stratumMeanPairing b h {a,j} a (z a-z j) := by
  simp_rw [cycleDeficit_correction_right b h lam hlam,mul_sub,Finset.sum_sub_distrib]
  rw [cycleMean_gradient_sum_zero b h lam hlam z,sub_zero]
  simp only [triangleBoundary,Finset.sum_mul]

/-- Subtraction is derived from actual covariance bilinearity. -/
theorem stratumDeficit_sub_left (b : AffineBasis V ℝ E) (h : V → ℝ)
    (S : Set V) (i : V) (hi : i ∈ S) (u v w : E) :
    stratumDeficit b h S i (u-v) w =
      stratumDeficit b h S i u w-stratumDeficit b h S i v w := by
  have hn := stratumDeficit_smul_left b h S i hi (-1) v w
  simp only [neg_one_smul,neg_one_mul] at hn
  have hs := stratumDeficit_sum_left (I := Fin 2) b h S i hi ![u,-v] w
  simpa [Fin.sum_univ_two,sub_eq_add_neg,hn] using hs

theorem cycleDeficit_sub_left (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j : V) (u v w : E) : cycleDeficit b h a j (u-v) w =
      cycleDeficit b h a j u w-cycleDeficit b h a j v w := by
  simp only [cycleDeficit,stratumDeficit_sub_left b h {a,j} a (by simp),mul_sub]

theorem cycleDeficit_sub_right (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j : V) (u v w : E) : cycleDeficit b h a j u (v-w) =
      cycleDeficit b h a j u v-cycleDeficit b h a j u w := by
  rw [cycleDeficit_symmetric,cycleDeficit_sub_left,
    cycleDeficit_symmetric b h a j v u,cycleDeficit_symmetric b h a j w u]

theorem cycleDeficit_sub_self (b : AffineBasis V ℝ E) (h : V → ℝ)
    (a j : V) (u v : E) : cycleDeficit b h a j (u-v) (u-v) =
      cycleDeficit b h a j u u-2*cycleDeficit b h a j u v+cycleDeficit b h a j v v := by
  rw [cycleDeficit_sub_left,cycleDeficit_sub_right,cycleDeficit_sub_right,
    cycleDeficit_symmetric b h a j v u]
  ring

/-- The actual residual subtracts one shared global cycle correction from the
cell-vector graph gradient on each oriented edge. -/
def cycleResidual (b : AffineBasis V ℝ E) (h : V → ℝ)
    (z : V → E) (lam : V → V → V → ℝ) (a j : V) : E :=
  z a-z j-cycleCorrection b h lam a j

/-- Exact residual expansion before inserting the optimizing graph cycle. -/
theorem cycleResidual_energy_expansion (b : AffineBasis V ℝ E) (h : V → ℝ)
    (z : V → E) (lam : V → V → V → ℝ) (hlam : AlternatingTriangle lam) :
    (1/2:ℝ) * ∑ a, ∑ j,
      cycleDeficit b h a j (cycleResidual b h z lam a j) (cycleResidual b h z lam a j) =
    (1/2:ℝ) * (∑ a, ∑ j, cycleDeficit b h a j (z a-z j) (z a-z j))-
      (∑ a, ∑ j, triangleBoundary lam a j * stratumMeanPairing b h {a,j} a (z a-z j))+
      cycleB b h lam lam := by
  have hr (a j : V) :
      cycleDeficit b h a j (cycleResidual b h z lam a j) (cycleResidual b h z lam a j) =
      cycleDeficit b h a j (z a-z j) (z a-z j)-
        2*cycleDeficit b h a j (z a-z j) (cycleCorrection b h lam a j)+
        cycleDeficit b h a j (cycleCorrection b h lam a j) (cycleCorrection b h lam a j) :=
    cycleDeficit_sub_self b h a j (z a-z j) (cycleCorrection b h lam a j)
  simp_rw [hr,Finset.sum_add_distrib,Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [cycleDeficit_gradient_correction_pairing b h lam hlam z,
    cycleB_eq_actual_deficit b h lam lam hlam hlam]
  ring


theorem cycleEdgeWeight_reverse (b : AffineBasis V ℝ E) (h : V → ℝ) (a j : V) :
    cycleEdgeWeight b h a j = cycleEdgeWeight b h j a := by
  by_cases haj : a=j
  · subst j; rfl
  rw [cycleEdgeWeight,cycleEdgeWeight,if_neg haj,if_neg (Ne.symm haj),norm_sub_rev (b j) (b a)]
  have hs : ({a,j}:Set V) = {j,a} := by ext x; simp [or_comm]
  rw [hs,stratumMassAt_independent_anchor b h {j,a} a j (by simp) (by simp)]

def cycleMeanEdge (b : AffineBasis V ℝ E) (h : V → ℝ) (z : V → E) (a j : V) : ℝ :=
  stratumMeanPairing b h {a,j} a (z a-z j)

theorem cycleMeanEdge_skew (b : AffineBasis V ℝ E) (h : V → ℝ) (z : V → E) :
    AlternatingEdge (cycleMeanEdge b h z) := by
  intro a j
  have hs : ({a,j}:Set V) = {j,a} := by ext x; simp [or_comm]
  rw [cycleMeanEdge,cycleMeanEdge,hs,
    stratumMeanPairing_independent_anchor b h {j,a} a j (by simp) (by simp)]
  rw [stratumMeanPairing_sub,stratumMeanPairing_sub]
  ring

/-- The genuine cycle candidate produced by one global offset vector. -/
def cycleFlux (b : AffineBasis V ℝ E) (h : V → ℝ) (z : V → E)
    (beta : V → ℝ) (a j : V) : ℝ :=
  cycleEdgeWeight b h a j * (cycleMeanEdge b h z a j+beta a-beta j)

theorem cycleFlux_skew (b : AffineBasis V ℝ E) (h : V → ℝ) (z : V → E) (beta : V → ℝ) :
    AlternatingEdge (cycleFlux b h z beta) := by
  intro a j
  unfold cycleFlux
  rw [cycleEdgeWeight_reverse b h a j,cycleMeanEdge_skew b h z a j]
  ring

/-- A graph cycle is orthogonal to every global offset gradient. -/
theorem cycle_gradient_pairing_zero (j : V → V → ℝ) (hj : AlternatingEdge j)
    (hcycle : ∀ a, edgeBoundary j a = 0) (beta : V → ℝ) :
    (∑ a, ∑ k, j a k * (beta a-beta k)) = 0 := by
  have hrow (a : V) : (∑ k, j a k) = 0 := by
    calc
      _ = -(∑ k, j k a) := by simp_rw [hj a,Finset.sum_neg_distrib]
      _ = 0 := by change -edgeBoundary j a=0; rw [hcycle,neg_zero]
  have h1 : (∑ a, ∑ k, j a k * beta a) = 0 := by
    simp_rw [← Finset.sum_mul,hrow,zero_mul]
    simp
  have h2 : (∑ a, ∑ k, j a k * beta k) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ k, edgeBoundary j k * beta k) = 0
    simp [hcycle]
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [h1,h2,sub_self]

def cycleMeanEnergy (b : AffineBasis V ℝ E) (h : V → ℝ) (j : V → V → ℝ) : ℝ :=
  (1/2:ℝ) * ∑ a, ∑ k, (j a k)^2/cycleEdgeWeight b h a k

/-- The full inverse-weight cycle energy equals its actual facet-mean pairing. -/
theorem cycleFlux_energy_pairing (b : AffineBasis V ℝ E) (h : V → ℝ) (z : V → E)
    (beta : V → ℝ) (hc : ∀ a, edgeBoundary (cycleFlux b h z beta) a = 0) :
    cycleMeanEnergy b h (cycleFlux b h z beta) =
      (1/2:ℝ) * ∑ a, ∑ k, cycleFlux b h z beta a k * cycleMeanEdge b h z a k := by
  have hi (a k : V) : (cycleFlux b h z beta a k)^2/cycleEdgeWeight b h a k =
      cycleFlux b h z beta a k*cycleMeanEdge b h z a k+
        cycleFlux b h z beta a k*(beta a-beta k) := by
    unfold cycleFlux
    field_simp [(cycleEdgeWeight_pos b h a k).ne']
    ring
  simp_rw [cycleMeanEnergy,hi,Finset.sum_add_distrib]
  rw [cycle_gradient_pairing_zero _ (cycleFlux_skew b h z beta) hc beta,add_zero]

/-- Every correction vector is genuinely tangent to its original facet. -/
theorem cycleCorrection_mem_tangent (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) (hlam : AlternatingTriangle lam) (a j : V) :
    cycleCorrection b h lam a j ∈ (faceDirection b {a,j})ᗮ := by
  unfold cycleCorrection
  apply Submodule.sum_mem
  intro k _
  by_cases hz : lam k a j=0
  · simp [hz]
  obtain ⟨hka,hkj,_⟩ := alternatingTriangle_nonzero_distinct lam hlam k a j hz
  apply Submodule.smul_mem
  exact barycentricOutwardVector_mem_face_orthogonal b {a,j} k (by simp [hka,hkj])

theorem cycleCorrection_anchor_pairing_zero (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) (hlam : AlternatingTriangle lam) (a j : V) :
    ⟪cycleCorrection b h lam a j,faceAnchor b h {a,j}⟫ = 0 := by
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    ((faceDirection b {a,j}).orthogonalProjectionOnto (affineFanApex b h)).property
    (cycleCorrection_mem_tangent b h lam hlam a j)

/-- The correction removes precisely the boundary cycle divided by its actual
edge weight from the actual conditional mean. -/
theorem cycleCorrection_mean (b : AffineBasis V ℝ E) (h : V → ℝ)
    (lam : V → V → V → ℝ) (hlam : AlternatingTriangle lam) (a j : V) :
    stratumMeanPairing b h {a,j} a (cycleCorrection b h lam a j) =
      triangleBoundary lam a j/cycleEdgeWeight b h a j := by
  rw [cycleCorrection,stratumMeanPairing_sum,triangleBoundary,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [stratumMeanPairing_smul]
  by_cases hz : lam k a j=0
  · simp [hz]
  obtain ⟨hka,hkj,haj⟩ := alternatingTriangle_nonzero_distinct lam hlam k a j hz
  calc
    _ = lam k a j * (cycleTriangleWeight b h a j k *
        stratumMeanPairing b h {a,j} a (barycentricOutwardVector b k)) := by
      rw [cycleTriangleWeight_cyclic b h k a j]
      ring
    _ = _ := by rw [cycleTriangleWeight_facet_mean b h a j k haj hka hkj]; ring

/-- Exact tangential mean of the residual. This is the corrected mean that
enters Ehrhard; the normal affine anchor is retained. -/
theorem cycleResidual_tangential_mean (b : AffineBasis V ℝ E) (h : V → ℝ)
    (z : V → E) (beta : V → ℝ) (lam : V → V → V → ℝ)
    (hlam : AlternatingTriangle lam) (hfill : triangleBoundary lam=cycleFlux b h z beta)
    (a j : V) :
    stratumMeanPairing b h {a,j} a (cycleResidual b h z lam a j)-
      ⟪cycleResidual b h z lam a j,faceAnchor b h {a,j}⟫ =
    -(beta a-beta j)-⟪z a-z j,faceAnchor b h {a,j}⟫ := by
  rw [cycleResidual,stratumMeanPairing_sub,inner_sub_left,
    cycleCorrection_anchor_pairing_zero b h lam hlam,
    cycleCorrection_mean b h lam hlam,hfill,cycleFlux]
  unfold cycleMeanEdge
  field_simp [(cycleEdgeWeight_pos b h a j).ne']
  ring

/-- Actual residual-energy identity with a constructed Gaussian weighted gauge.
Only divergence of the literal global-offset flux remains as an input; this is
the first-order condition supplied by the actual offset minimizer. -/
theorem exists_actual_cycle_residual (b : AffineBasis V ℝ E) (h : V → ℝ)
    (z : V → E) (beta : V → ℝ) (r : V)
    (hc : ∀ a, edgeBoundary (cycleFlux b h z beta) a = 0) :
    ∃ lam : V → V → V → ℝ, AlternatingTriangle lam ∧
      triangleBoundary lam=cycleFlux b h z beta ∧
      (∀ a j k l, cycleWeightedCoboundary b h lam a j k l=0) ∧
      ((1/2:ℝ) * ∑ a, ∑ j, cycleDeficit b h a j (z a-z j) (z a-z j))-
        cycleMeanEnergy b h (cycleFlux b h z beta) =
        (1/2:ℝ) * ∑ a, ∑ j,
          cycleDeficit b h a j (cycleResidual b h z lam a j) (cycleResidual b h z lam a j) := by
  obtain ⟨lam,hlam,hfill,hg,hbal⟩ := exists_actual_gaussian_cycle_balance b h r
    (cycleFlux b h z beta) (cycleFlux_skew b h z beta) hc
  refine ⟨lam,hlam,hfill,hg,?_⟩
  have he := cycleResidual_energy_expansion b h z lam hlam
  rw [hfill] at he
  change (1/2:ℝ) * ∑ a, ∑ j,
      cycleDeficit b h a j (cycleResidual b h z lam a j) (cycleResidual b h z lam a j) =
    (1/2:ℝ) * (∑ a, ∑ j, cycleDeficit b h a j (z a-z j) (z a-z j))-
      (∑ a, ∑ j, cycleFlux b h z beta a j*cycleMeanEdge b h z a j)+cycleB b h lam lam at he
  change cycleB b h lam lam=cycleMeanEnergy b h (cycleFlux b h z beta) at hbal
  have hp := cycleFlux_energy_pairing b h z beta hc
  rw [hbal] at he
  linarith

end NegativeVotingFanCycle
