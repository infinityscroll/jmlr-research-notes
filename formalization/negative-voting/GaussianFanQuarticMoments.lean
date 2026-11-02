import GaussianQuarticMovingCap
import GaussianFanMovingCells
import GaussianQuadraticAffineTransport

/-! Actual quartic Gaussian fan tests and the differentiated quadratic
transport bulk. Polynomial growth is established by finite algebra. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators ENNReal Topology Classical
namespace NegativeVotingFanQuarticMoments
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingMovingCap NegativeVotingDisintegration
  NegativeVotingWeightedFacet NegativeVotingFanMovingCells NegativeVotingQuadraticAffineTransport
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem hasFDerivAt_testedCell (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖^4)) :
    HasFDerivAt (fun p : Parameters d ι =>
      ∫ x in winningCell p.1 p.2 i, F x ∂stdGaussian (FSC.Coord d))
      (testedCellDerivative B h i F) (B,h) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  have hd := NegativeVotingQuarticMovingCap.hasFDerivAt_capTest (cellNormals B i)
    (cellNormals_unit B σ hσ hlower i) (cellSupports B h i)
    (cellNormals_noCoincident B h σ hσ hlower i) F hFc C hC hF
  rw [← fanParameterMap_base B h i] at hd
  have hh := hd.comp (B,h) (fanParameterMap B i).hasFDerivAt
  have he : (fun p : Parameters d ι => capTest (fanParameterMap B i p) F) =
      (fun p : Parameters d ι =>
        ∫ x in winningCell p.1 p.2 i, F x ∂stdGaussian (FSC.Coord d)) := by
    funext p
    unfold capTest
    rw [normalized_cap_eq_winningCell B hB]
  change HasFDerivAt (fun p => capTest (fanParameterMap B i p) F)
    (testedCellDerivative B h i F) (B,h) at hh
  rw [he] at hh
  exact hh

theorem testedCellDerivative_apply (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖^4)) (δ : Parameters d ι) :
    testedCellDerivative B h i F δ =
      ∑ j : {j : ι // j ≠ i}, WeakSimplex.normalPDF (cellSupports B h i j) / ‖B j.1-B i‖ *
        ∫ y in tangentFace (cellNormals B i) (cellSupports B h i) j,
          F (outwardFacetPoint B h i j y) *
            (inner ℝ (δ.1 i-δ.1 j.1) (outwardFacetPoint B h i j y) + δ.2 i-δ.2 j.1)
          ∂stdGaussian (tangentSpace (cellNormals B i j)) := by
  change capJointDerivative (cellNormals B i) (cellSupports B h i) F (fanParameterMap B i δ) = _
  rw [NegativeVotingQuarticMovingCap.capJointDerivative_apply _ (cellNormals_unit B σ hσ hlower i) _ F hFc C hC hF]
  apply Finset.sum_congr rfl
  intro j hj
  have he (x : FSC.Coord d) :
      F x * ((fanParameterMap B i δ).2 j - inner ℝ ((fanParameterMap B i δ).1 j) x) =
        (F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1)) / ‖B j.1-B i‖ := by
    rw [fanParameterMap_support, fanParameterMap_normal, real_inner_smul_left]
    simp only [inner_sub_left, div_eq_mul_inv]
    ring
  simp_rw [he]
  rw [integral_div]
  unfold outwardFacetPoint
  ring

theorem testedCellDerivative_apply_ambient (B : ι → FSC.Coord d) (h : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (F : FSC.Coord d → ℝ) (hFc : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ x, |F x| ≤ C * (1+‖x‖^4)) (δ : Parameters d ι) :
    testedCellDerivative B h i F δ =
      ∑ j : {j : ι // j ≠ i}, gaussianPDFReal 0 1 (pairOffset B h j.1 i) / ‖B j.1-B i‖ *
        ∫ x in affineFacet B h j.1 i,
          F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1)
          ∂FSC.sliceLaw (pairNormal B j.1 i) (pairOffset B h j.1 i) := by
  have hB : Function.Injective B := fun j k he => by
    by_contra hjk
    exact centered_singular_rows_ne B σ hσ hlower j k hjk he
  rw [testedCellDerivative_apply B h σ hσ hlower i F hFc C hC hF]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tangentFace_integral_eq_surface B h hB i j
    (fun x => F x * (inner ℝ (δ.1 i-δ.1 j.1) x + δ.2 i-δ.2 j.1))
    (by fun_prop)]
  rfl

def PolynomialGrowth (F : FSC.Coord d→ℝ) (k : ℕ) : Prop :=
  Continuous F ∧ ∃ C : ℝ,0≤C ∧ ∀ x,|F x|≤C*(1+‖x‖)^k

namespace PolynomialGrowth
 theorem const (c : ℝ) (k : ℕ) : PolynomialGrowth (fun _:FSC.Coord d=>c) k := by
  refine ⟨continuous_const,|c|,abs_nonneg c,fun x=>?_⟩
  have hh : 1≤(1+‖x‖)^k := one_le_pow₀ (by linarith [norm_nonneg x])
  nlinarith [abs_nonneg c]

 theorem inner (u : FSC.Coord d) : PolynomialGrowth (fun x=>inner ℝ u x) 1 := by
  refine ⟨by fun_prop,‖u‖,norm_nonneg u,fun x=>?_⟩
  have hh := abs_real_inner_le_norm u x
  simp only [pow_one]
  nlinarith [norm_nonneg u]

 theorem mono_degree {F : FSC.Coord d→ℝ} {k l : ℕ} (hF : PolynomialGrowth F k)
    (hkl : k≤l) : PolynomialGrowth F l := by
  obtain ⟨hFc,C,hC,hF⟩ := hF
  refine ⟨hFc,C,hC,fun x=>(hF x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1≤1+‖x‖) hkl) hC

 theorem add {F G : FSC.Coord d→ℝ} {k : ℕ} (hF : PolynomialGrowth F k)
    (hG : PolynomialGrowth G k) : PolynomialGrowth (fun x=>F x+G x) k := by
  obtain ⟨hFc,C,hC,hF⟩ := hF
  obtain ⟨hGc,D,hD,hG⟩ := hG
  refine ⟨hFc.add hGc,C+D,add_nonneg hC hD,fun x=>?_⟩
  have hh := (abs_add_le (F x) (G x)).trans (add_le_add (hF x) (hG x))
  simpa only [add_mul] using hh

 theorem sub {F G : FSC.Coord d→ℝ} {k : ℕ} (hF : PolynomialGrowth F k)
    (hG : PolynomialGrowth G k) : PolynomialGrowth (fun x=>F x-G x) k := by
  obtain ⟨hFc,C,hC,hF⟩ := hF
  obtain ⟨hGc,D,hD,hG⟩ := hG
  refine ⟨hFc.sub hGc,C+D,add_nonneg hC hD,fun x=>?_⟩
  have hh := (abs_sub (F x) (G x)).trans (add_le_add (hF x) (hG x))
  simpa only [add_mul] using hh

 theorem mul {F G : FSC.Coord d→ℝ} {k l : ℕ} (hF : PolynomialGrowth F k)
    (hG : PolynomialGrowth G l) : PolynomialGrowth (fun x=>F x*G x) (k+l) := by
  obtain ⟨hFc,C,hC,hF⟩ := hF
  obtain ⟨hGc,D,hD,hG⟩ := hG
  refine ⟨hFc.mul hGc,C*D,mul_nonneg hC hD,fun x=>?_⟩
  rw [abs_mul]
  calc
    _ ≤ (C*(1+‖x‖)^k)*(D*(1+‖x‖)^l) := mul_le_mul (hF x) (hG x) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add];ring

 theorem const_mul {F : FSC.Coord d→ℝ} {k : ℕ} (hF : PolynomialGrowth F k)
    (c : ℝ) : PolynomialGrowth (fun x=>c*F x) k := by
  obtain ⟨hFc,C,hC,hF⟩ := hF
  refine ⟨continuous_const.mul hFc,|c| * C,mul_nonneg (abs_nonneg c) hC,fun x=>?_⟩
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (hF x) (abs_nonneg c)).trans_eq (by ring)

 theorem finsetSum {κ : Type*} (s : Finset κ) (F : κ→FSC.Coord d→ℝ) (k : ℕ)
    (hF : ∀ a∈s,PolynomialGrowth (F a) k) : PolynomialGrowth (fun x=>∑ a∈s,F a x) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (d:=d) 0 k)
  | @insert a s ha ih =>
    have hh := (hF a (Finset.mem_insert_self a s)).add
      (ih (fun b hb=>hF b (Finset.mem_insert_of_mem hb)))
    simpa only [Finset.sum_insert ha] using hh

 theorem quartic_bound {F : FSC.Coord d→ℝ} (hF : PolynomialGrowth F 4) :
    ∃ C : ℝ,0≤C ∧ ∀ x,|F x|≤C*(1+‖x‖^4) := by
  obtain ⟨_,C,hC,hF⟩ := hF
  refine ⟨8*C,by positivity,fun x=>?_⟩
  calc
    _ ≤ C*(1+‖x‖)^4 := hF x
    _ ≤ C*(8*(1:ℝ)^4+8*‖x‖^4) := mul_le_mul_of_nonneg_left
      (NegativeVotingQuarticMovingCap.fourth_add_le 1 ‖x‖ (by norm_num) (norm_nonneg x)) hC
    _ = _ := by ring
end PolynomialGrowth

 theorem rankOneBulk_growth (v y u a z : FSC.Coord d) :
    PolynomialGrowth (rankOneBulk v y u a z) 4 := by
  have h1 := PolynomialGrowth.inner (d:=d)
  have h2 (p q:FSC.Coord d) : PolynomialGrowth (fun x=>inner ℝ p x*inner ℝ q x) 2 :=
    (h1 p).mul (h1 q)
  have h3 (p q r:FSC.Coord d) : PolynomialGrowth (fun x=>inner ℝ p x*inner ℝ q x*inner ℝ r x) 3 :=
    (h2 p q).mul (h1 r)
  have h4 : PolynomialGrowth (fun x=>inner ℝ u x*(inner ℝ v x*inner ℝ y x*inner ℝ a x)) 4 :=
    (h1 u).mul (h3 v y a)
  have hG := ((((h2 y a).const_mul (inner ℝ u v)).add
    ((h2 v a).const_mul (inner ℝ u y))).add ((h2 v y).const_mul (inner ℝ u a))).mono_degree (by decide : 2≤4)
  have hZ := ((h1 z).mul (h2 v y)).mono_degree (by decide : 3≤4)
  have hL := (((h1 y).const_mul (inner ℝ z v)).add ((h1 v).const_mul (inner ℝ z y))).mono_degree
    (by decide : 1≤4)
  exact ((h4.sub hG).add hZ).sub hL

 theorem affineBulk_growth (v y : FSC.Coord d) (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z : FSC.Coord d) : PolynomialGrowth (affineBulk v y A z) 4 := by
  have hh := (PolynomialGrowth.finsetSum Finset.univ (fun a:Fin d=>rankOneBulk v y
    (A (EuclideanSpace.basisFun (Fin d) ℝ a)) (EuclideanSpace.basisFun (Fin d) ℝ a) 0) 4
      (fun a _=>rankOneBulk_growth _ _ _ _ _)).add (rankOneBulk_growth v y 0 0 z)
  have he : (affineBulk v y A z)=(fun x=>(∑ a:Fin d,rankOneBulk v y
    (A (EuclideanSpace.basisFun (Fin d) ℝ a)) (EuclideanSpace.basisFun (Fin d) ℝ a) 0 x)+
      rankOneBulk v y 0 0 z x) := funext (affineBulk_decomposition v y A z)
  rw [he]
  exact hh

/-- The actual quartic bulk from quadratic affine transport is itself
Frechet differentiable under arbitrary joint row/offset variation. -/
 theorem hasFDerivAt_affineBulk_testedCell (B : ι→FSC.Coord d) (h : ι→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (i : ι)
    (v y : FSC.Coord d) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    HasFDerivAt (fun p:Parameters d ι=>∫ x in winningCell p.1 p.2 i,
      affineBulk v y A z x ∂stdGaussian (FSC.Coord d))
      (testedCellDerivative B h i (affineBulk v y A z)) (B,h) := by
  obtain ⟨C,hC,hF⟩ := (affineBulk_growth v y A z).quartic_bound
  exact hasFDerivAt_testedCell B h σ hσ hlower i _ (affineBulk_growth v y A z).1 C hC hF

end NegativeVotingFanQuarticMoments
