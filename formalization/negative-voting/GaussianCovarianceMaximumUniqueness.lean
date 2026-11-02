import GaussianBalancedCovarianceMaximum

/-! Uniqueness on the full PSD cone of an actual positive covariance maximizer.
The boundary comparison follows from global concavity and interior strictness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingCovarianceMaximumUniqueness
open NegativeVotingPositiveCovariance NegativeVotingCovarianceStrict
  NegativeVotingBalancedReference NegativeVotingBalancedMaximum
variable {n d : ℕ}

theorem half_positive_half_psd
    (C D : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈pdCone) (hD : D∈psdCone) :
    (1/2:ℝ) • C+(1/2:ℝ) • D∈pdCone := by
  refine ⟨(hC.1.smul (by rfl : starRingEnd ℝ (1/2)=(1/2:ℝ))).add
    (hD.1.smul (by rfl : starRingEnd ℝ (1/2)=(1/2:ℝ))),?_⟩
  intro x hx
  change 0 < inner ℝ x ((1/2:ℝ) • C x+(1/2:ℝ) • D x)
  rw [inner_add_right,real_inner_smul_right,real_inner_smul_right]
  exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) (hC.2 x hx))
    (mul_nonneg (by norm_num) (hD.2 x))

/-- Any positive global maximizer is unique even among singular covariances. -/
theorem positive_maximizer_unique
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d)) (p : Fin (n+2) → ℝ)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈pdCone)
    (hmax : ∀ A,A∈psdCone → penalizedValue b p A ≤ penalizedValue b p C)
    (D : FSC.Coord d →L[ℝ] FSC.Coord d) (hD : D∈psdCone)
    (hval : penalizedValue b p C ≤ penalizedValue b p D) : D=C := by
  by_contra hne
  let E := (1/2:ℝ) • C+(1/2:ℝ) • D
  have hE : E∈pdCone := half_positive_half_psd C D hC hD
  have hEC : E≠C := by
    intro he
    have hv : E-C=(1/2:ℝ) • (D-C) := by dsimp [E]; module
    rw [he,sub_self] at hv
    have hz : D-C=0 := (smul_eq_zero.mp hv.symm).resolve_left (by norm_num)
    exact hne (sub_eq_zero.mp hz)
  have hc := (penalized_concaveOn_psd b p hp hs).2
    (pdCone_subset_psdCone hC) hD (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at hc
  have hCE : penalizedValue b p C ≤ penalizedValue b p E := by
    change (1/2:ℝ)*penalizedValue b p C+(1/2:ℝ)*penalizedValue b p D≤penalizedValue b p E at hc
    linarith
  have hsx := (penalizedValue_strictConcaveOn_positive b p hp hs).2 hC hE
    (Ne.symm hEC) (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at hsx
  have hF := pdCone_subset_psdCone (pdCone_convex hC hE (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1))
  have hupper := hmax _ hF
  linarith

/-- The balanced scalar covariance is the unique actual PSD maximizer. -/
theorem balanced_reference_unique (hn : 0<n)
    (b : AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈psdCone)
    (heq : penalizedValue b (uniformMass n) C=NegativeVotingGaussianMaximumMean.referenceFirstWeight n) :
    C=referenceCovariance n d := by
  apply positive_maximizer_unique b (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
    (referenceCovariance n d) (referenceCovariance_positive n d)
    (fun A hA=>balanced_reference_isMaxOn hn b hG hP hA) C hC
  rw [reference_penalized_value b hG hP,heq]

end NegativeVotingCovarianceMaximumUniqueness
