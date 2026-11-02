import GaussianCovarianceRealization
import GaussianRegularScoreLaw

/-! Literal balanced regular fan masses, centroids, and scalar normalization. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Classical ENNReal NNReal Topology
namespace NegativeVotingBalancedReference
open NegativeVoting NegativeVotingGaussianMaximum NegativeVotingRegularMaximum
  NegativeVotingRegularScoreLaw NegativeVotingFan NegativeVotingFanScore NegativeVotingFanValue
  NegativeVotingCapTail NegativeVotingCenteredParseval NegativeVotingCentroidOptimization
  NegativeVotingGaussianMaximumMean

/-- The actual iid Gaussian maximum has strictly positive mean, already for two coordinates. -/
theorem maximumMean_pos (n : ℕ) : 0 < maximumMean n := by
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:ℝ≥0)≠0)).isOpenPosMeasure
  letI : Measure.IsOpenPosMeasure (standardGaussian (Fin (n+2))) :=
    Measure.pi.isOpenPosMeasure (fun _ : Fin (n+2)=>gaussianReal 0 1)
  let F : (Fin (n+2) → ℝ) → ℝ := fun x=>maximum x-x 0
  have hF : Integrable F (standardGaussian (Fin (n+2))) :=
    maximum_integrable.sub (gaussian_product_coordinate_integrable (κ:=Fin (n+2)) (fun _=>0) (fun _=>1) 0)
  have hn : 0 ≤ F := fun x=>sub_nonneg.mpr (Finset.le_sup' x (Finset.mem_univ 0))
  have ho : IsOpen {x : Fin (n+2) → ℝ | x 0<x 1} := isOpen_lt (by fun_prop) (by fun_prop)
  have he : ({x : Fin (n+2) → ℝ | x 0<x 1} : Set (Fin (n+2) → ℝ)).Nonempty := by
    refine ⟨fun i=>if i=1 then 1 else 0,?_⟩
    have hi : (0:Fin (n+2))≠1 := by simp [Fin.ext_iff]
    simp only [Set.mem_setOf_eq,hi,ite_false,ite_true]
    norm_num
  have hs : {x : Fin (n+2) → ℝ | x 0<x 1} ⊆ Function.support F := by
    intro x hx
    have hm : x 1 ≤ maximum x := Finset.le_sup' x (Finset.mem_univ 1)
    change x 0<x 1 at hx
    change maximum x-x 0≠0
    linarith
  have hp : 0 < ∫ x,F x ∂standardGaussian (Fin (n+2)) :=
    (integral_pos_iff_support_of_nonneg hn hF).mpr ((ho.measure_pos _ he).trans_le (measure_mono hs))
  simpa only [F,integral_sub maximum_integrable
    (gaussian_product_coordinate_integrable (κ:=Fin (n+2)) (fun _=>0) (fun _=>1) 0),
    standardGaussian_coordinate_integral,sub_zero,maximumMean] using hp

def uniformMass (n : ℕ) : Fin (n+2) → ℝ := fun _=>1/((n:ℝ)+2)
def referenceScale (n : ℕ) : ℝ := maximumMean n/((n:ℝ)+1)

theorem uniformMass_pos (n : ℕ) (i : Fin (n+2)) : 0 < uniformMass n i := by
  unfold uniformMass
  positivity

theorem uniformMass_sum (n : ℕ) : (∑ i,uniformMass n i)=1 := by
  simp only [uniformMass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_ofNat]
  field_simp

theorem referenceScale_pos (n : ℕ) : 0 < referenceScale n :=
  div_pos (maximumMean_pos n) (by positivity)

theorem maxScore_mul_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (a : ℝ) (ha : 0<a) : maxScore (fun i=>a*s i)=a*maxScore s := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i _=>
      mul_le_mul_of_nonneg_left (Finset.le_sup' s (Finset.mem_univ i)) ha.le)
  · rw [maxScore,finite_max_eq_chosenWinner]
    exact Finset.le_sup' (fun i=>a*s i) (Finset.mem_univ (chosenWinner s))

theorem maxWeights_mul_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ι → ℝ) (a : ℝ) (ha : 0<a) (i : ι) :
    maxWeights (fun j=>a*s j) i=maxWeights s i := by
  have hI (j : ι) : maxIndicator (fun k=>a*s k) j=maxIndicator s j := by
    simp only [maxIndicator,maxScore_mul_pos s a ha,mul_eq_mul_left_iff,ne_of_gt ha,
      or_false]
  simp only [maxWeights,maxMultiplicity,hI]

variable {d n : ℕ}

def coordinateRows (B : Fin (n+2) → FSC.Coord d) : Fin (n+2) → Fin d → ℝ :=
  fun i=>(B i).ofLp

theorem coordinateRows_gram (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    RegularSimplexGram (coordinateRows B) := by
  intro i j
  simpa only [coordinateRows,PiLp.inner_apply,Real.inner_apply,Nat.cast_add,Nat.cast_ofNat]
    using hG i j

theorem zero_weights_eq_regular (B : Fin (n+2) → FSC.Coord d)
    (x : FSC.Coord d) (i : Fin (n+2)) :
    weights B 0 x i=regularAssignment (coordinateRows B) x.ofLp i := by
  unfold weights scores regularAssignment
  congr 1
  funext j
  simp only [Pi.zero_apply,add_zero,coordinateRows,PiLp.inner_apply,Real.inner_apply]

theorem scaled_weights_zero (B : Fin (n+2) → FSC.Coord d) (a : ℝ) (ha : 0<a)
    (x : FSC.Coord d) (i : Fin (n+2)) :
    weights (fun j=>a • B j) 0 x i=weights B 0 x i := by
  change maxWeights (fun j=>inner ℝ (a • B j) x+0) i=
    maxWeights (fun j=>inner ℝ (B j) x+0) i
  simp only [add_zero,real_inner_smul_left]
  exact maxWeights_mul_pos _ a ha i

theorem regular_fan_mass (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    mass B 0=uniformMass n := by
  funext i
  simp_rw [mass,zero_weights_eq_regular]
  rw [←integral_standardGaussian_eq_euclidean (κ:=Fin d) (fun x=>regularAssignment (coordinateRows B) x i),
    regularAssignment_mass _ (coordinateRows_gram B hG)]
  simp only [uniformMass,Nat.cast_add,Nat.cast_ofNat]

theorem regular_fan_expectedMax (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) :
    expectedMax B 0=maximumMean n := by
  unfold expectedMax scores
  simp only [Pi.zero_apply,add_zero,PiLp.inner_apply,Real.inner_apply]
  change (∫ x : EuclideanSpace ℝ (Fin d),
    maxScore (fun i : Fin (n+2)=>∑ k,coordinateRows B i k*x.ofLp k)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d)))=maximumMean n
  rw [←integral_standardGaussian_eq_euclidean (κ:=Fin d)
    (fun x=>maxScore (fun i : Fin (n+2)=>∑ k,coordinateRows B i k*x k))]
  exact regular_maximum_mean_eq_canonical n (coordinateRows B) (coordinateRows_gram B hG)

theorem regular_fan_centroid (hn : 0<n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) (i : Fin (n+2)) :
    centroid B 0 i=referenceScale n • B i := by
  apply PiLp.ext
  intro k
  have hc : (centroid B 0 i) k=
      ∫ x,regularAssignment (coordinateRows B) x i*x k ∂standardGaussian (Fin d) := by
    change (EuclideanSpace.proj (𝕜:=ℝ) k)
      (∫ x,weights B 0 x i • x ∂stdGaussian (FSC.Coord d))=_
    rw [←(EuclideanSpace.proj (𝕜:=ℝ) k).integral_comp_comm (centroid_integrable B 0 i)]
    change (∫ x : FSC.Coord d,weights B 0 x i*x k ∂stdGaussian (FSC.Coord d))=_
    simp_rw [zero_weights_eq_regular]
    exact (integral_standardGaussian_eq_euclidean (κ:=Fin d)
      (fun x=>regularAssignment (coordinateRows B) x i*x k)).symm
  rw [hc]
  have hh := regularAssignment_first_moment (coordinateRows B) (coordinateRows_gram B hG)
    (by omega : 3≤n+2) i k
  rw [regular_maximum_mean_eq_canonical n _ (coordinateRows_gram B hG)] at hh
  simpa only [referenceScale,coordinateRows,PiLp.smul_apply,smul_eq_mul,mul_comm,
    Nat.cast_add,Nat.cast_ofNat,show (n:ℝ)+2-1=(n:ℝ)+1 by ring] using hh

theorem scaled_centered_singular (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) (a : ℝ) :
    CenteredSingularLowerBound (fun i=>a • B i) a := by
  intro c hc
  have hsum : (∑ i,c i • (a • B i))=a • ∑ i,c i • B i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul,smul_smul,mul_comm]
  have hG' : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  rw [hsum,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,weighted_norm_sq B hG' c,hc]
  simp

theorem scaled_regular_self_centroid (hn : 0<n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) (i : Fin (n+2)) :
    centroid (fun j=>referenceScale n • B j) 0 i=referenceScale n • B i := by
  unfold centroid
  simp_rw [scaled_weights_zero B (referenceScale n) (referenceScale_pos n)]
  exact regular_fan_centroid hn B hG i

end NegativeVotingBalancedReference
