import GaussianFanMassJacobian
import GaussianFanMovingCells
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! One actual affine coordinate chart for all cells of an affinely independent
Gaussian fan. A fixed continuous right inverse for score differences is constructed
from finite score interpolation. The coordinate map is identity at the base. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingFanCoherentChart
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanJacobian
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

 def edgeDual (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι)
    (j : {j:ι // j≠i₀}) : FSC.Coord d :=
   Classical.choose (exists_inner_values (fun k:{k:ι // k≠i₀}=>B k.1-B i₀)
     ((affineIndependent_iff_linearIndependent_vsub ℝ B i₀).mp hB)
     (fun k=>if k=j then (1:ℝ) else 0))

 theorem edgeDual_inner (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι)
    (j k : {j:ι // j≠i₀}) :
    inner ℝ (B k.1-B i₀) (edgeDual B hB i₀ j)=if k=j then (1:ℝ) else 0 :=
  Classical.choose_spec (exists_inner_values (fun k:{k:ι // k≠i₀}=>B k.1-B i₀)
    ((affineIndependent_iff_linearIndependent_vsub ℝ B i₀).mp hB)
    (fun k=>if k=j then (1:ℝ) else 0)) k

 def scoreLiftCLM (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι) :
    (ι→ℝ)→L[ℝ] FSC.Coord d :=
   ∑ j:{j:ι // j≠i₀},((ContinuousLinearMap.proj j.1 : (ι→ℝ)→L[ℝ] ℝ)-
     ContinuousLinearMap.proj i₀).smulRight (edgeDual B hB i₀ j)

 theorem scoreLiftCLM_edge (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι)
    (q : ι→ℝ) (k : {k:ι // k≠i₀}) :
    inner ℝ (B k.1-B i₀) (scoreLiftCLM B hB i₀ q)=q k.1-q i₀ := by
  simp only [scoreLiftCLM,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.proj_apply,inner_sum,real_inner_smul_right,
    edgeDual_inner,mul_ite,mul_one,mul_zero]
  simp

 theorem scoreLiftCLM_base (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι)
    (q : ι→ℝ) (i : ι) :
    inner ℝ (B i-B i₀) (scoreLiftCLM B hB i₀ q)=q i-q i₀ := by
  by_cases hi:i=i₀
  · subst i
    simp
  · exact scoreLiftCLM_edge B hB i₀ q ⟨i,hi⟩

 theorem scoreLiftCLM_pair (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι)
    (q : ι→ℝ) (i j : ι) :
    inner ℝ (B i-B j) (scoreLiftCLM B hB i₀ q)=q i-q j := by
  rw [show B i-B j=(B i-B i₀)-(B j-B i₀) by abel,inner_sub_left,
    scoreLiftCLM_base,scoreLiftCLM_base]
  ring

 def rowScoreMap (D : ι→FSC.Coord d) : FSC.Coord d→L[ℝ] (ι→ℝ) :=
   ContinuousLinearMap.pi (fun i=>innerSL ℝ (D i))

 @[simp] theorem rowScoreMap_apply (D : ι→FSC.Coord d) (x : FSC.Coord d) (i : ι) :
    rowScoreMap D x i=inner ℝ (D i) x := rfl

 def rowScoreOperator : (ι→FSC.Coord d)→ₗ[ℝ] (FSC.Coord d→L[ℝ] (ι→ℝ)) where
   toFun := rowScoreMap
   map_add' D E := by ext x i; simp [rowScoreMap,inner_add_left]
   map_smul' c D := by ext x i; simp [rowScoreMap,real_inner_smul_left]

 def linearVariation (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (i₀ : ι) :
    Parameters d ι→L[ℝ] (FSC.Coord d→L[ℝ] FSC.Coord d) :=
   (ContinuousLinearMap.compL ℝ (FSC.Coord d) (ι→ℝ) (FSC.Coord d)
     (scoreLiftCLM B hB i₀)).comp
       (rowScoreOperator.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _))

 @[simp] theorem linearVariation_apply (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (i₀ : ι) (p : Parameters d ι) (x : FSC.Coord d) :
    linearVariation B hB i₀ p x=scoreLiftCLM B hB i₀ (fun i=>inner ℝ (p.1 i) x) := rfl

 def chartLinear (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (h : ι→ℝ)
    (i₀ : ι) (p : Parameters d ι) : FSC.Coord d→L[ℝ] FSC.Coord d :=
   ContinuousLinearMap.id ℝ (FSC.Coord d)+linearVariation B hB i₀ (p-(B,h))

 def chartShift (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B) (h : ι→ℝ)
    (i₀ : ι) (p : Parameters d ι) : FSC.Coord d :=
   scoreLiftCLM B hB i₀ (p.2-h)

 @[simp] theorem chartLinear_base (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) : chartLinear B hB h i₀ (B,h)=ContinuousLinearMap.id ℝ (FSC.Coord d) := by
  simp [chartLinear]

 @[simp] theorem chartShift_base (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) : chartShift B hB h i₀ (B,h)=0 := by simp [chartShift]

 theorem chart_pair_scores (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) (p : Parameters d ι) (x : FSC.Coord d) (i j : ι) :
    scores B h (chartLinear B hB h i₀ p x+chartShift B hB h i₀ p) i-
      scores B h (chartLinear B hB h i₀ p x+chartShift B hB h i₀ p) j=
      scores p.1 p.2 x i-scores p.1 p.2 x j := by
  have he := scoreLiftCLM_pair B hB i₀ (fun k=>inner ℝ (p.1 k-B k) x) i j
  have hs := scoreLiftCLM_pair B hB i₀ (p.2-h) i j
  simp only [inner_sub_left,Pi.sub_apply] at he hs
  simp only [scores,chartLinear,chartShift,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply,linearVariation_apply,Prod.fst_sub,Pi.sub_apply,
    inner_add_right,inner_sub_left]
  linarith

/-- One and the same affine map transports every actual winning cell.
The identity holds for every parameter p; local invertibility is separate. -/
 theorem winningCell_eq_chart_preimage (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) (p : Parameters d ι) (i : ι) :
    winningCell p.1 p.2 i=(fun x=>chartLinear B hB h i₀ p x+chartShift B hB h i₀ p) ⁻¹'
      winningCell B h i := by
  ext x
  simp only [winningCell,Set.mem_setOf_eq,Set.mem_preimage]
  apply forall_congr'
  intro j
  have hh := chart_pair_scores B hB h i₀ p x i j
  constructor <;> intro hle <;> linarith

 theorem contDiff_chartLinear (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) : ContDiff ℝ ⊤ (chartLinear B hB h i₀) := by
  unfold chartLinear
  fun_prop

 theorem contDiff_chartShift (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) : ContDiff ℝ ⊤ (chartShift B hB h i₀) := by
  unfold chartShift
  fun_prop

 theorem chartLinear_isUnit_of_small (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) (p : Parameters d ι)
    (hp : ‖linearVariation B hB i₀ (p-(B,h))‖<1) : IsUnit (chartLinear B hB h i₀ p) := by
  have hh := isUnit_one_sub_of_norm_lt_one (x:= -linearVariation B hB i₀ (p-(B,h)))
    (by simpa only [norm_neg] using hp)
  convert! hh using 1 <;> simp only [sub_neg_eq_add,chartLinear,ContinuousLinearMap.one_def]

 theorem eventually_chartLinear_isUnit (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) : ∀ᶠ p : Parameters d ι in 𝓝 (B,h),IsUnit (chartLinear B hB h i₀ p) := by
  have hc : ContinuousAt (fun p:Parameters d ι=>‖linearVariation B hB i₀ (p-(B,h))‖) (B,h) := by
    fun_prop
  have hh := hc.eventually_lt continuousAt_const (by simp : ‖linearVariation B hB i₀ ((B,h)-(B,h))‖<(1:ℝ))
  exact hh.mono fun p hp=>chartLinear_isUnit_of_small B hB h i₀ p hp

 theorem contDiffAt_chartInverse (B : ι→FSC.Coord d) (hB : AffineIndependent ℝ B)
    (h : ι→ℝ) (i₀ : ι) :
    ContDiffAt ℝ ⊤ (fun p=>Ring.inverse (chartLinear B hB h i₀ p)) (B,h) := by
  have hh : ContDiffAt ℝ ⊤ Ring.inverse (chartLinear B hB h i₀ (B,h)) := by
    convert! (contDiffAt_ringInverse ℝ (1:(FSC.Coord d→L[ℝ] FSC.Coord d)ˣ) :
      ContDiffAt ℝ ⊤ Ring.inverse _) using 1 <;>
      simp only [chartLinear_base,Units.val_one,ContinuousLinearMap.one_def]
  exact hh.comp (B,h) (contDiff_chartLinear B hB h i₀).contDiffAt

end NegativeVotingFanCoherentChart
