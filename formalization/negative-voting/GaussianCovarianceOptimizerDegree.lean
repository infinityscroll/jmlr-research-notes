import GaussianCovariancePriceDerivative
import GaussianCenteredParsevalBasis

/-! Actual one-sided optimizer stationarity yields the Gaussian facet degree
bound. The exact centered Parseval Gram normalization is explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingCovarianceOptimizerDegree
open NegativeVotingPositiveCovariance NegativeVotingCovarianceOptimizer
  NegativeVotingCovarianceStrict NegativeVotingCovariancePrice
  NegativeVotingFanSelectedOffsets NegativeVotingFanJacobian
variable {m d : ℕ} [NeZero m]

theorem right_max_derivative_nonpos (f : ℝ → ℝ) (a : ℝ)
    (hd : HasDerivAt f a 0) (hmax : ∀ t,0<t→f t≤f 0) : a≤0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa only [zero_add,smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (sub_nonpos.mpr (hmax t ht))

theorem lowerCone_add_psd {ε : ℝ} (C D : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hC : C∈lowerCovarianceCone ε) (hD : D∈psdCone) (t : ℝ) (ht : 0≤t) :
    C+t • D∈lowerCovarianceCone ε := by
  change C+t • D-ε • ContinuousLinearMap.id ℝ (FSC.Coord d)∈psdCone
  have he : C+t • D-ε • ContinuousLinearMap.id ℝ (FSC.Coord d)=
      (C-ε • ContinuousLinearMap.id ℝ (FSC.Coord d))+t • D := by module
  rw [he]
  refine ⟨hC.1.add (hD.1.smul (by simp)),?_⟩
  intro x
  change 0 ≤ inner ℝ x ((C-ε • ContinuousLinearMap.id ℝ (FSC.Coord d)) x+t • D x)
  rw [inner_add_right,real_inner_smul_right]
  exact add_nonneg (hC.2 x) (mul_nonneg ht (hD.2 x))

/-- A literal PSD-direction KKT inequality for the actual optimizer. -/
theorem optimizer_price_le_trace (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (ε : ℝ) (C : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hC : C∈lowerCovarianceCone ε) (hmax : IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) C)
    (R : FSC.Coord d ≃L[ℝ] FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRC : R.toContinuousLinearMap.comp R.toContinuousLinearMap=C)
    (D : FSC.Coord d →L[ℝ] FSC.Coord d) (hD : D∈psdCone) :
    (1/2:ℝ)*∑ i,∑ j,facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j *
      inner ℝ (b i-b j) (D (b i-b j)) ≤ LinearMap.trace ℝ (FSC.Coord d) D.toLinearMap := by
  have hd := hasDerivAt_penalizedValue_factor b p hp hs C D R hR hRi hRC hD.1
  have hn := right_max_derivative_nonpos _ _ hd (fun t ht => by
    change penalizedValue b p (C+t • D)≤penalizedValue b p (C+(0:ℝ) • D)
    have he0 : C+(0:ℝ) • D=C := by module
    rw [he0]
    exact hmax (lowerCone_add_psd C D hC hD t ht.le))
  linarith

def rankOne (v : FSC.Coord d) : FSC.Coord d →L[ℝ] FSC.Coord d :=
  (innerSL ℝ v).smulRight v

@[simp] theorem rankOne_apply (v x : FSC.Coord d) : rankOne v x=inner ℝ v x • v := rfl

theorem rankOne_pairing (v x : FSC.Coord d) : inner ℝ x (rankOne v x)=(inner ℝ v x)^2 := by
  simp only [rankOne_apply,real_inner_smul_right]
  rw [real_inner_comm x v]
  ring

theorem rankOne_psd (v : FSC.Coord d) : rankOne v∈psdCone := by
  refine ⟨?_,fun x => by rw [rankOne_pairing]; positivity⟩
  intro x y
  change inner ℝ (inner ℝ v x • v) y=inner ℝ x (inner ℝ v y • v)
  simp only [real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm x v]
  ring

theorem rankOne_trace (v : FSC.Coord d) : LinearMap.trace ℝ (FSC.Coord d) (rankOne v).toLinearMap=
    inner ℝ v v := by
  change LinearMap.trace ℝ (FSC.Coord d) ((innerSL ℝ v).toLinearMap.smulRight v)=_
  rw [LinearMap.trace_smulRight]
  rfl

/-- The ordered edge energy of a centered Parseval coordinate is its actual
Jacobian degree; the diagonal is zero and the edge weights are symmetric. -/
theorem parseval_rankOne_edge_degree (b : Fin m → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (B : Fin m → FSC.Coord d) (h : Fin m → ℝ) (i : Fin m) :
    (1/2:ℝ)*∑ j,∑ k,facetWeight B h j k * inner ℝ (b j-b k) (rankOne (b i) (b j-b k))=
      ∑ j,facetWeight B h i j := by
  let v : Fin m → ℝ := fun j => if j=i then 1 else 0
  have hv (j k : Fin m) : inner ℝ (b j-b k) (rankOne (b i) (b j-b k))=(v j-v k)^2 := by
    rw [rankOne_pairing,inner_sub_right,hG,hG]
    have hvj : (if i=j then (1:ℝ) else 0)=v j := by
      by_cases h : i=j
      · simp [v,h]
      · simp [v,h,Ne.symm h]
    have hvk : (if i=k then (1:ℝ) else 0)=v k := by
      by_cases h : i=k
      · simp [v,h]
      · simp [v,h,Ne.symm h]
    rw [hvj,hvk]
    ring
  simp_rw [hv]
  have he := symmetric_laplacian_energy (facetWeight B h) (facetWeight_symm B h) v
  have hl : (∑ j,v j*(∑ k,facetWeight B h j k*(v j-v k)))=∑ j,facetWeight B h i j := by
    simp [v,mul_sub,Finset.sum_sub_distrib,mul_ite,ite_mul]
  exact he.symm.trans hl

/-- Every positive regularized covariance maximizer has literal facet degrees
at most one. No stationarity, Hessian, or graph-degree premise is supplied. -/
theorem exists_optimizer_factor_degree_le_one (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (ε : ℝ) (hε : 0<ε) (C : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hC : C∈lowerCovarianceCone ε) (hmax : IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) C) :
    ∃ R : FSC.Coord d ≃L[ℝ] FSC.Coord d,
      R.toLinearMap.IsSymmetric ∧ R.symm.toLinearMap.IsSymmetric ∧
      R.toContinuousLinearMap.comp R.toContinuousLinearMap=C ∧
      ∀ i, (∑ j,facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j)≤1 := by
  obtain ⟨R,hR,hRi,hRC⟩ := exists_positive_factor C (lowerCovarianceCone_subset_pd hε hC)
  refine ⟨R,hR,hRi,hRC,?_⟩
  intro i
  have hb := optimizer_price_le_trace b p hp hs ε C hC hmax R hR hRi hRC (rankOne (b i)) (rankOne_psd _)
  rw [parseval_rankOne_edge_degree b hG,rankOne_trace,hG] at hb
  have hn : 0≤1/(m:ℝ) := by positivity
  have hb' : (∑ j,facetWeight (mappedBasis b R) (selectedOffsets (mappedBasis b R) p) i j)≤1-1/(m:ℝ) := by simpa using hb
  exact hb'.trans (sub_le_self _ hn)

end NegativeVotingCovarianceOptimizerDegree
