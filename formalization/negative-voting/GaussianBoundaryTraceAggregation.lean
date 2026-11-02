import GaussianNormalTraceAllExponents
import GaussianWeightedFacetEnergy
import GaussianActualFacetOUTrace

/-! Variable-exponent finite-edge aggregation for the actual Gaussian boundary
trace.  The weighted row degree and edge separation remain explicit geometric
inputs.  No infinite boundary-distribution/Riesz or path theorem is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin NegativeVotingNormalTrace
open NegativeVotingNormalTraceAllExponents
open scoped BigOperators ENNReal

namespace NegativeVotingBoundaryTraceAggregation

theorem sum_fractional_surface_le {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (q : ℝ) (hq : 1 < q) :
    (∑ j ∈ s, (w j) ^ (1-1/q)) ≤
      (s.card : ℝ) ^ (1/q) * (∑ j ∈ s, w j) ^ (1-1/q) := by
  have hq0 : 0 < q := by linarith
  have hd : 0 < q-1 := by linarith
  have hc : (q/(q-1)).HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    constructor
    · apply (lt_div_iff₀ hd).mpr
      linarith
    · field_simp
      ring
  have hh := Real.inner_le_Lp_mul_Lq s (fun j => (w j) ^ (1-1/q)) (fun _ => 1) hc
  have he : (∑ j ∈ s, |(w j) ^ (1-1/q)| ^ (q/(q-1))) = ∑ j ∈ s, w j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_of_nonneg (Real.rpow_nonneg (hw j hj) _), ← Real.rpow_mul (hw j hj)]
    have hexp : (1-1/q)*(q/(q-1))=1 := by field_simp
    rw [hexp, Real.rpow_one]
  rw [he] at hh
  have hinv : 1/(q/(q-1))=1-1/q := by field_simp
  simpa only [mul_one,abs_one,Real.one_rpow,Finset.sum_const,nsmul_eq_mul,
    mul_one,hinv,mul_comm,one_mul] using hh

/-- The edge-length exponent is only -1/q, rather than the fixed L32 loss. -/
theorem fractional_edge_identity (μ ell q : ℝ) (hμ : 0 ≤ μ) (hell : 0 < ell) :
    μ^(1-1/q)/ell = ell^(-(1/q))*(μ/ell)^(1-1/q) := by
  have he : ell^(1/q)*ell^(1-1/q)=ell := by
    rw [←Real.rpow_add hell]
    have ht : 1/q+(1-1/q)=(1:ℝ) := by ring
    rw [ht,Real.rpow_one]
  calc
    _ = μ^(1-1/q)/(ell^(1/q)*ell^(1-1/q)) := by rw [he]
    _ = _ := by
      rw [Real.div_rpow hμ hell.le,Real.rpow_neg hell.le]
      field_simp

theorem surface_row_coefficient_le {ι : Type*} (s : Finset ι)
    (μ ell : ι → ℝ) (ell0 G q : ℝ) (hell0 : 0 < ell0) (_hG : 0 ≤ G)
    (hq : 1 < q) (hμ : ∀ j ∈ s, 0 ≤ μ j)
    (hell : ∀ j ∈ s, ell0 ≤ ell j)
    (hdegree : (∑ j ∈ s, μ j / ell j) ≤ G) :
    (∑ j ∈ s, (μ j)^(1-1/q)/ell j) ≤
      ell0^(-(1/q))*(s.card : ℝ)^(1/q)*G^(1-1/q) := by
  have hq0 : 0 < q := by linarith
  have ha : 0 ≤ 1-1/q := by
    have : 1/q ≤ (1:ℝ) := (div_le_one hq0).mpr hq.le
    linarith
  have hw j (hj : j ∈ s) : 0 ≤ μ j / ell j :=
    div_nonneg (hμ j hj) (hell0.le.trans (hell j hj))
  calc
    _ ≤ ∑ j ∈ s, ell0^(-(1/q))*(μ j/ell j)^(1-1/q) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [fractional_edge_identity _ _ q (hμ j hj) (hell0.trans_le (hell j hj))]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hell0 (hell j hj)
          (neg_nonpos.mpr (div_nonneg (by norm_num) hq0.le)))
        (Real.rpow_nonneg (hw j hj) _)
    _ = ell0^(-(1/q)) * ∑ j ∈ s, (μ j/ell j)^(1-1/q) := by rw [Finset.mul_sum]
    _ ≤ ell0^(-(1/q))*((s.card : ℝ)^(1/q)*(∑ j ∈ s, μ j/ell j)^(1-1/q)) :=
      mul_le_mul_of_nonneg_left (sum_fractional_surface_le s _ hw q hq)
        (Real.rpow_nonneg hell0.le _)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Finset.sum_nonneg hw) hdegree ha) (by positivity))
        (Real.rpow_nonneg hell0.le _)

section Labels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def effectiveWeight (μ ell : ι → ι → ℝ) (q : ℝ) (i j : ι) : ℝ :=
  if i=j then 0 else (μ i j)^(1-1/q)/ell i j

def traceCoefficient (ell0 G q : ℝ) : ℝ :=
  ell0^(-(1/q))*(Fintype.card ι : ℝ)^(1/q)*G^(1-1/q)

omit [DecidableEq ι] in
/-- Choosing q logarithmically makes the whole finite-edge coefficient
uniform. No lower individual facet probability is used. -/
theorem traceCoefficient_le_exp (ell0 G q : ℝ) (hell0 : 0 < ell0)
    (hG : 0 ≤ G) (hq : 1 < q) (hcard : 0 < (Fintype.card ι : ℝ))
    (hlog : Real.log ((Fintype.card ι : ℝ)/ell0) ≤ q) :
    traceCoefficient (ι := ι) ell0 G q ≤ Real.exp 1 * max 1 G := by
  have hq0 : 0 < q := by linarith
  have ha : 0 ≤ 1-1/q := by
    have : 1/q ≤ (1:ℝ) := (div_le_one hq0).mpr hq.le
    linarith
  have ha1 : 1-1/q ≤ (1:ℝ) := by
    have : 0 ≤ 1/q := by positivity
    linarith
  have hGpow : G^(1-1/q) ≤ max 1 G := by
    rcases le_total G 1 with hG1 | hG1
    · exact (Real.rpow_le_one hG hG1 ha).trans (le_max_left _ _)
    · exact (Real.rpow_le_self_of_one_le hG1 ha1).trans (le_max_right _ _)
  have hscale : ell0^(-(1/q))*(Fintype.card ι : ℝ)^(1/q) ≤ Real.exp 1 := by
    rw [Real.rpow_neg hell0.le, mul_comm, ←div_eq_mul_inv,
      ←Real.div_rpow hcard.le hell0.le, Real.rpow_def_of_pos (div_pos hcard hell0)]
    apply Real.exp_le_exp.mpr
    have h := (div_le_one hq0).mpr hlog
    simpa only [div_eq_mul_inv,one_mul] using h
  exact mul_le_mul hscale hGpow (Real.rpow_nonneg hG _) (Real.exp_pos _).le

theorem effectiveWeight_row_le (μ ell : ι → ι → ℝ) (ell0 G q : ℝ)
    (hell0 : 0 < ell0) (hG : 0 ≤ G) (hq : 1 < q)
    (hμ : ∀ i j, i≠j → 0 ≤ μ i j)
    (hell : ∀ i j, i≠j → ell0 ≤ ell i j)
    (hdegree : ∀ i, (∑ j ∈ Finset.univ.erase i, μ i j/ell i j) ≤ G) (i : ι) :
    (∑ j, effectiveWeight μ ell q i j) ≤ traceCoefficient (ι := ι) ell0 G q := by
  rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [show effectiveWeight μ ell q i i=0 from by simp [effectiveWeight],add_zero]
  simp only [effectiveWeight]
  have he : (∑ j ∈ Finset.univ.erase i, if i=j then 0 else (μ i j)^(1-1/q)/ell i j) =
      ∑ j ∈ Finset.univ.erase i, (μ i j)^(1-1/q)/ell i j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.mem_erase.mp hj).1.symm]
  rw [he]
  have h := surface_row_coefficient_le (Finset.univ.erase i) (μ i) (ell i) ell0 G q
    hell0 hG hq (fun j hj => hμ i j (Finset.mem_erase.mp hj).1.symm)
    (fun j hj => hell i j (Finset.mem_erase.mp hj).1.symm) (hdegree i)
  refine h.trans ?_
  unfold traceCoefficient
  have hc : ((Finset.univ.erase i).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset (s := Finset.univ) i)
  gcongr

omit [DecidableEq ι] in
/-- Symmetric finite edge summation. Both endpoint label costs are paid by
the same row-degree bound, without another alphabet factor. -/
theorem symmetric_pair_energy_le (ω : ι → ι → ℝ) (E : ι → ℝ) (K : ℝ)
    (_hω : ∀ i j, 0 ≤ ω i j) (hsym : ∀ i j, ω i j=ω j i)
    (hE : ∀ i, 0 ≤ E i) (hrow : ∀ i, (∑ j, ω i j) ≤ K) :
    (∑ i, ∑ j, ω i j*(E i+E j)) ≤ 2*K*∑ i, E i := by
  have hx : (∑ i, ∑ j, ω i j*E j) = ∑ i, ∑ j, ω i j*E i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  have hr : (∑ i, ∑ j, ω i j*E i) ≤ K*∑ i, E i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (hE i)
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hx]
  linarith

/-- Aggregation of surface-weighted traces with an explicit per-edge L²
input bound. The analytic trace inequality is supplied separately and exactly. -/
theorem ordered_trace_energy_le (T μ ell : ι → ι → ℝ) (E : ι → ℝ)
    (ell0 G q C : ℝ) (hell0 : 0 < ell0) (hG : 0 ≤ G) (hq : 1 < q)
    (hC : 0 ≤ C) (hE : ∀ i, 0 ≤ E i)
    (hμ : ∀ i j, i≠j → 0 ≤ μ i j)
    (hell : ∀ i j, i≠j → ell0 ≤ ell i j)
    (hμsym : ∀ i j, μ i j=μ j i) (hellsym : ∀ i j, ell i j=ell j i)
    (hdegree : ∀ i, (∑ j ∈ Finset.univ.erase i, μ i j/ell i j) ≤ G)
    (htrace : ∀ i j, i≠j → T i j ≤ C*(μ i j)^(1-1/q)*(E i+E j)) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, T i j/ell i j) ≤
      2*C*traceCoefficient (ι := ι) ell0 G q * ∑ i, E i := by
  let ω := effectiveWeight μ ell q
  have hω i j : 0 ≤ ω i j := by
    unfold ω effectiveWeight
    split_ifs with hij
    · rfl
    · exact div_nonneg (Real.rpow_nonneg (hμ i j hij) _) (hell0.le.trans (hell i j hij))
  have hs i j : ω i j=ω j i := by
    unfold ω effectiveWeight
    by_cases hij : i=j
    · subst j; rfl
    · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), hμsym i j, hellsym i j]
  have hpair := symmetric_pair_energy_le ω E (traceCoefficient (ι := ι) ell0 G q)
    hω hs hE (effectiveWeight_row_le μ ell ell0 G q hell0 hG hq hμ hell hdegree)
  calc
    _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, C*ω i j*(E i+E j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hij := (Finset.mem_erase.mp hj).1.symm
      have hb := div_le_div_of_nonneg_right (htrace i j hij) (hell0.le.trans (hell i j hij))
      simp only [ω,effectiveWeight,ite_eq_right hij]
      convert hb using 1
      ring
    _ ≤ ∑ i, ∑ j, C*ω i j*(E i+E j) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun j hj hji => mul_nonneg (mul_nonneg hC (hω i j)) (add_nonneg (hE i) (hE j)))
    _ = C * ∑ i, ∑ j, ω i j*(E i+E j) := by simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hpair hC
      nlinarith only [h]

end Labels

section Ambient
open NegativeVotingDisintegration NegativeVotingActualFacetOUTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def planeSurfaceMass (w : ι → ι → E) (a : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j))) (i j : ι) : ℝ :=
  gaussianPDFReal 0 1 (a i j) * (stdGaussian (tangentSpace (w i j)) (F i j)).toReal

/-- Actual ambient OU boundary traces, summed over all ordered distinct
labels. The Gaussian trace inequality, pair difference bound, and graph
summation are all derived. Symmetry, edge separation, and weighted degree
are the remaining geometric hypotheses on the given planes/facets. -/
theorem ambient_ordered_trace_energy_le {n : ι → ι → ℕ}
    (w : ι → ι → E) (a ell : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (e : ∀ i j, i≠j → tangentSpace (w i j) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i j)))
    (τ q ell0 G : ℝ) (hτ : 0 < τ) (hq : 2 ≤ q)
    (ht : τ^2=1/(2*q-1)) (hell0 : 0 < ell0) (hG : 0 ≤ G)
    (hw : ∀ i j, i≠j → ‖w i j‖=1)
    (hF : ∀ i j, i≠j → MeasurableSet (F i j))
    (hell : ∀ i j, i≠j → ell0 ≤ ell i j)
    (hμsym : ∀ i j, planeSurfaceMass w a F i j=planeSurfaceMass w a F j i)
    (hellsym : ∀ i j, ell i j=ell j i)
    (hdegree : ∀ i, (∑ j ∈ Finset.univ.erase i, planeSurfaceMass w a F i j/ell i j) ≤ G)
    (f : ι → E → ℝ) (hfM : ∀ i, Measurable (f i))
    (hf : ∀ i, MemLp (f i) 2 (stdGaussian E)) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      gaussianPDFReal 0 1 (a i j)/ell i j *
        ∫ y in F i j, (ambientAverage τ (fun x => f i x-f j x)
          ((y:E)+(a i j) • w i j))^2 ∂stdGaussian (tangentSpace (w i j))) ≤
      8*traceCoefficient (ι := ι) ell0 G q * ∑ i, ∫ x,(f i x)^2 ∂stdGaussian E := by
  let energy := fun i => ∫ x,(f i x)^2 ∂stdGaussian E
  let T := fun i j => gaussianPDFReal 0 1 (a i j) *
    ∫ y in F i j, (ambientAverage τ (fun x => f i x-f j x)
      ((y:E)+(a i j) • w i j))^2 ∂stdGaussian (tangentSpace (w i j))
  have henergy i : 0 ≤ energy i := integral_nonneg (fun _ => sq_nonneg _)
  have hμ i j (_hij : i≠j) : 0 ≤ planeSurfaceMass w a F i j :=
    mul_nonneg (gaussianPDFReal_nonneg _ _ _) ENNReal.toReal_nonneg
  have hdiff i j : (∫ x,(f i x-f j x)^2 ∂stdGaussian E) ≤ 2*(energy i+energy j) := by
    have h := integral_mono ((hf i).sub (hf j)).integrable_sq
      (((hf i).integrable_sq.add (hf j).integrable_sq).const_mul 2)
      (fun x => by
        simp only [Pi.sub_apply,Pi.add_apply]
        nlinarith [sq_nonneg (f i x+f j x)])
    simp only [Pi.sub_apply,Pi.add_apply] at h
    rw [integral_const_mul,integral_add (hf i).integrable_sq (hf j).integrable_sq] at h
    exact h
  have htrace i j (hij : i≠j) : T i j ≤
      4*(planeSurfaceMass w a F i j)^(1-1/q)*(energy i+energy j) := by
    have h := plane_surface_square_le (w i j) (hw i j hij) (e i j hij) τ q (a i j)
      hτ hq ht (F i j) (hF i j hij) (fun x => f i x-f j x)
      ((hfM i).sub (hfM j)) ((hf i).sub (hf j))
    change T i j ≤ 2*(planeSurfaceMass w a F i j)^(1-1/q)*
      ∫ x,(f i x-f j x)^2 ∂stdGaussian E at h
    have hh := mul_le_mul_of_nonneg_left (hdiff i j)
      (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg (hμ i j hij) (1-1/q)))
    exact h.trans (by nlinarith only [hh])
  have h := ordered_trace_energy_le T (planeSurfaceMass w a F) ell energy ell0 G q 4
    hell0 hG (by linarith) (by norm_num) henergy hμ hell hμsym hellsym hdegree htrace
  convert h using 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold T
    ring
  · unfold energy
    ring

end Ambient
end NegativeVotingBoundaryTraceAggregation
