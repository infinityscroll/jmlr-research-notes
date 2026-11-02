import GaussianCentroidEnergyAttainment
import GaussianCovarianceCoercivity

/-! The operator norm of the actual centroid matrix is bounded by the largest
assignment mass. This is a direct weighted square-completion argument and
requires no rank or separation of the centroid rows. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingCentroidOperatorBound
open NegativeVotingAssignmentDuality NegativeVotingMassCentroid NegativeVotingCentroidOptimization
  NegativeVotingCovarianceCoercivity
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

theorem centroid_directional_operator_bound (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (P : ℝ) (hP : 0 < P) (hp : ∀ i,p i ≤ P) (v : FSC.Coord d) :
    (∑i,(inner ℝ v (centroidRows f i))^2) ≤ P*‖v‖^2 := by
  let b : ι → ℝ := fun i=>inner ℝ v (centroidRows f i)
  let S : ℝ := ∑i,(b i)^2
  let Q : ℝ := ∑i,p i*(b i)^2
  let g : FSC.Coord d → ℝ := fun x=>
    ∑i,((2*b i/P)*(f x i*inner ℝ v x)-((b i)^2/P^2)*f x i)
  have hfi (i : ι) := feasible_coordinate_integrable p f hf i
  have hAi (i : ι) : Integrable (fun x=>f x i*inner ℝ v x) (stdGaussian (FSC.Coord d)) :=
    fractional_mul_integrable _ _ _ (hf.1 i) (feasible_coordinate_bounds p f hf i)
      (IsGaussian.integrable_dual _ (innerSL ℝ v))
  have hgi : Integrable g (stdGaussian (FSC.Coord d)) := by
    dsimp [g]
    apply integrable_finsetSum
    intro i _
    exact ((hAi i).const_mul _).sub ((hfi i).const_mul _)
  have hb (i : ι) : (∫x,f x i*inner ℝ v x ∂stdGaussian (FSC.Coord d))=b i :=
    (inner_gaussianCentroid _ v (hf.1 i) (feasible_coordinate_bounds p f hf i)).symm
  have hlabel (i : ι) :
      (∫x,((2*b i/P)*(f x i*inner ℝ v x)-((b i)^2/P^2)*f x i)
        ∂stdGaussian (FSC.Coord d))=(2*b i/P)*b i-((b i)^2/P^2)*p i := by
    have hh := integral_sub ((hAi i).const_mul (2*b i/P)) ((hfi i).const_mul ((b i)^2/P^2))
    simp only [Pi.sub_apply] at hh
    rw [hh,integral_const_mul,integral_const_mul,hb,hf.2.2]
  have hint (i : ι) : Integrable (fun x=>((2*b i/P)*(f x i*inner ℝ v x)-((b i)^2/P^2)*f x i))
      (stdGaussian (FSC.Coord d)) := by
    convert ((hAi i).const_mul (2*b i/P)).sub ((hfi i).const_mul ((b i)^2/P^2)) using 1
  have hIg : (∫x,g x ∂stdGaussian (FSC.Coord d))=2/P*S-Q/P^2 := by
    dsimp [g]
    rw [integral_finsetSum Finset.univ (fun i _=>hint i)]
    simp_rw [hlabel]
    dsimp [S,Q]
    rw [Finset.mul_sum,Finset.sum_div,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpoint : ∀ᵐ x ∂stdGaussian (FSC.Coord d),g x ≤ (inner ℝ v x)^2 := by
    filter_upwards [hf.2.1] with x hx
    calc
      g x ≤ ∑i,f x i*(inner ℝ v x)^2 := by
        dsimp [g]
        apply Finset.sum_le_sum
        intro i _
        have hh := mul_nonneg (hx.1 i) (sq_nonneg (inner ℝ v x-b i/P))
        apply sub_nonneg.mp
        convert hh using 1 <;> ring
      _ = _ := by rw [←Finset.sum_mul,hx.2,one_mul]
  have hquad : Integrable (fun x:FSC.Coord d=>(inner ℝ v x)^2) (stdGaussian (FSC.Coord d)) :=
    (IsGaussian.memLp_dual (stdGaussian (FSC.Coord d)) (innerSL ℝ v) 2 (by norm_num)).integrable_sq
  have hbound := integral_mono_ae hgi hquad hpoint
  rw [hIg,integral_inner_sq] at hbound
  have hQ : Q ≤ P*S := by
    dsimp [Q,S]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (hp i) (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hbound (sq_nonneg P)
  have he : (2/P*S-Q/P^2)*P^2=2*P*S-Q := by field_simp
  rw [he] at hmul
  have hh : P*S ≤ P*(P*‖v‖^2) := by nlinarith
  exact (mul_le_mul_iff_right₀ hP).mp hh

/-- The same covariance bound after any deterministic scalar normalization. -/
theorem scaled_centroid_directional_operator_bound (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (P : ℝ) (hP : 0 < P) (hp : ∀ i,p i ≤ P)
    (s : ℝ) (v : FSC.Coord d) :
    (∑i,(inner ℝ v (s • centroidRows f i))^2) ≤ s^2*P*‖v‖^2 := by
  simp only [real_inner_smul_right,mul_pow,←Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (centroid_directional_operator_bound p f hf P hP hp v)
    (sq_nonneg s)).trans_eq (by ring)

end NegativeVotingCentroidOperatorBound
