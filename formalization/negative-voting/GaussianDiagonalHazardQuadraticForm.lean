import GaussianDiagonalHazardDifferentiation
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Exact rank-one subtraction in the diagonal-Gaussian hazard Laplacian.
In particular the discarded term is nonnegative for every Euclidean row
system, including singular systems. No covariance spectral bound is needed. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingDiagonalHazardQuadraticForm
open NegativeVotingDiagonalHazardDifferentiation
variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma weighted_pair_distance_identity (a : V → ℝ) (B : V → E) :
    (1/2:ℝ)*(∑i,∑j,a i*a j*‖B i-B j‖^2)=
      (∑i,a i)*(∑i,a i*‖B i‖^2)-‖∑i,a i • B i‖^2 := by
  have hnorm : ‖∑i,a i • B i‖^2=∑i,∑j,a i*a j*inner ℝ (B i) (B j) := by
    rw [←real_inner_self_eq_norm_sq,sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [real_inner_smul_left,real_inner_smul_right]
    ring
  have hleft' : (∑i,∑j,a i*a j*‖B i‖^2)=(∑j,a j)*(∑i,a i*‖B i‖^2) := by
    rw [Finset.sum_comm,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑i,∑j,a i*a j*‖B j‖^2)=(∑i,a i)*(∑j,a j*‖B j‖^2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hterm (i j : V) : a i*a j*‖B i-B j‖^2=
      a i*a j*‖B i‖^2+a i*a j*‖B j‖^2-2*(a i*a j*inner ℝ (B i) (B j)) := by
    rw [norm_sub_sq_real]
    ring
  simp_rw [hterm,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [hleft',hright,hnorm]
  ring

def hazardRowSum (σ h : V → ℝ) (x : ℝ) (i : V) : ℝ :=
  ∑j,hazardPairDensity σ h x i j

/-- The analytic diagonal is included in `hazardRowSum`; its zero edge
 contribution is exactly cancelled by the rank-one term. -/
theorem hazard_laplacian_exact (σ h : V → ℝ) (x : ℝ) (B : V → E) :
    (1/2:ℝ)*(∑i,∑j,hazardPairDensity σ h x i j*‖B i-B j‖^2)=
      (∑i,hazardRowSum σ h x i*‖B i‖^2)-
        productCDF σ h x*‖∑i,gaussianHazard (σ i) (h i) x • B i‖^2 := by
  let a : V → ℝ := fun i=>gaussianHazard (σ i) (h i) x
  have he := congrArg (fun z:ℝ=>productCDF σ h x*z) (weighted_pair_distance_identity a B)
  have hr : (∑i,hazardRowSum σ h x i*‖B i‖^2)=
      productCDF σ h x*((∑i,a i)*(∑i,a i*‖B i‖^2)) := by
    simp only [hazardRowSum,hazardPairDensity,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a]
    ring
  rw [hr]
  convert he using 1
  · simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a,hazardPairDensity]
    ring
  · dsimp [a]
    ring

/-- Dropping the rank-one square is valid for every target Gram matrix,
 regardless of its rank or off-diagonal entries. -/
theorem hazard_laplacian_le_diagonal (σ h : V → ℝ) (x : ℝ) (B : V → E) :
    (1/2:ℝ)*(∑i,∑j,hazardPairDensity σ h x i j*‖B i-B j‖^2) ≤
      ∑i,hazardRowSum σ h x i*‖B i‖^2 := by
  rw [hazard_laplacian_exact]
  apply sub_le_self
  apply mul_nonneg _ (sq_nonneg _)
  exact Finset.prod_nonneg fun i _=>(gaussianCDF_pos _ _ _).le

end NegativeVotingDiagonalHazardQuadraticForm
