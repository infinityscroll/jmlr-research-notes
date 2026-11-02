import GaussianDiagonalHazardDifferentiation
import GaussianCellOUContinuity
import GaussianGeometricMedianProxy
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact one-dimensional winner-mass formulas for independent diagonal
Gaussian scores, derived from the actual finite product measure. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter WeakSimplex
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingDiagonalWinnerIntegral
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingFan
  NegativeVotingConditionalSecondMoment NegativeVotingHypercontractivity NegativeVotingCellOUContinuity
  NegativeVotingCapTail NegativeVotingFacetDegree NegativeVotingFanJacobian
variable {n m : ℕ}

def diagonalRows (σ : Fin m→ℝ) (i : Fin m) : FSC.Coord m := EuclideanSpace.single i (σ i)

def winnerEvent (σ h : Fin m→ℝ) (i : Fin m) : Set (Fin m→ℝ) :=
  {x | ∀j,σ j*x j+h j ≤ σ i*x i+h i}

def winnerIndicator (σ h : Fin m→ℝ) (i : Fin m) : (Fin m→ℝ)→ℝ :=
  (winnerEvent σ h i).indicator (fun _=>1)

theorem winnerEvent_measurable (σ h : Fin m→ℝ) (i : Fin m) : MeasurableSet (winnerEvent σ h i) := by
  unfold winnerEvent
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (by fun_prop) (by fun_prop)

theorem winnerIndicator_measurable (σ h : Fin m→ℝ) (i : Fin m) : Measurable (winnerIndicator σ h i):=
  measurable_const.indicator (winnerEvent_measurable σ h i)

theorem winnerIndicator_integrable (σ h : Fin m→ℝ) (i : Fin m) :
    Integrable (winnerIndicator σ h i) (γFin m):=
  (integrable_const 1).indicator (winnerEvent_measurable σ h i)

theorem gaussian_threshold_integral (a : Fin n→ℝ) :
    (∫x,(Set.pi Set.univ (fun j=>Iic (a j))).indicator (fun _=>(1:ℝ)) x ∂γFin n)=
      ∏j,normalCDF (a j) := by
  rw [integral_indicator (MeasurableSet.univ_pi (fun j=>measurableSet_Iic)),integral_const]
  simp only [Measure.restrict_apply_univ,smul_eq_mul,mul_one,measureReal_def]
  change (Measure.pi (fun _ : Fin n=>gaussianReal 0 1) (Set.pi Set.univ (fun j=>Iic (a j)))).toReal=_
  rw [Measure.pi_pi]
  simp only [←normalCDF_eq_measure_Iic,ENNReal.toReal_prod,ENNReal.toReal_ofReal (normalCDF_pos _).le]

theorem winnerIndicator_insertNth (σ h : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j)
    (i : Fin (n+1)) (y : ℝ) (z : Fin n→ℝ) :
    winnerIndicator σ h i (i.insertNth y z)=
      (Set.pi Set.univ (fun j=>Iic ((σ i*y+h i-h (i.succAbove j))/σ (i.succAbove j)))).indicator (fun _=>(1:ℝ)) z := by
  have he : i.insertNth y z∈winnerEvent σ h i ↔
      z∈Set.pi Set.univ (fun j=>Iic ((σ i*y+h i-h (i.succAbove j))/σ (i.succAbove j))):=by
    simp only [winnerEvent,Set.mem_setOf_eq,i.forall_iff_succAbove,Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove,le_refl,true_and,Set.mem_pi,Set.mem_univ,Set.mem_Iic,forall_const]
    apply forall_congr'
    intro j
    rw [le_div_iff₀ (hσ _)]
    constructor <;> intro hh <;> nlinarith only [hh]
  unfold winnerIndicator
  by_cases hy : i.insertNth y z∈winnerEvent σ h i
  · simp only [Set.indicator_of_mem hy,Set.indicator_of_mem (he.mp hy)]
  · simp only [Set.indicator_of_notMem hy,Set.indicator_of_notMem (fun hz=>hy (he.mpr hz))]

/-- Conditioning on the winning coordinate is an exact product-Gaussian
calculation, valid for arbitrary positive diagonal standard deviations. -/
theorem winner_integral_conditioned (σ h : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j) (i : Fin (n+1)) :
    (∫x,winnerIndicator σ h i x ∂γFin (n+1))=
      ∫y,(∏j:Fin n,gaussianCDF (σ (i.succAbove j)) (h (i.succAbove j)) (σ i*y+h i)) ∂gaussianReal 0 1 := by
  let T:=MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1)=>ℝ) i
  have hT : MeasurePreserving T (γFin (n+1))
      ((gaussianReal 0 1).prod (γFin n)):=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n+1)=>gaussianReal 0 1) i
  have hint : Integrable (fun p:ℝ×(Fin n→ℝ)=>winnerIndicator σ h i (T.symm p))
      ((gaussianReal 0 1).prod (γFin n)):=
    hT.symm.integrable_comp_of_integrable (winnerIndicator_integrable σ h i)
  rw [←hT.symm.integral_comp' (winnerIndicator σ h i),integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards with y
  have he : (fun z:Fin n→ℝ=>winnerIndicator σ h i (T.symm (y,z)))=
      (Set.pi Set.univ (fun j=>Iic ((σ i*y+h i-h (i.succAbove j))/σ (i.succAbove j)))).indicator (fun _=>(1:ℝ)):=by
    funext z
    exact winnerIndicator_insertNth σ h hσ i y z
  rw [he,gaussian_threshold_integral]
  rfl

@[simp] theorem diagonalRows_inner (σ : Fin m→ℝ) (i : Fin m) (x : FSC.Coord m) :
    inner ℝ (diagonalRows σ i) x=σ i*x i := by
  simp [diagonalRows,EuclideanSpace.inner_single_left]

theorem diagonalRows_injective (σ : Fin m→ℝ) (hσ : ∀i,0<σ i) :
    Function.Injective (diagonalRows σ) := by
  intro i j he
  by_contra hij
  have hh:=congrArg (fun x:FSC.Coord m=>x i) he
  simp [diagonalRows,PiLp.single_apply,hij,Ne.symm hij] at hh
  exact (hσ i).ne' hh

theorem cellWeight_diagonal (σ h : Fin m→ℝ) (i : Fin m) :
    NegativeVotingQuadraticMomentPadding.cellWeight (diagonalRows σ) h i=winnerIndicator σ h i := by
  funext x
  have he : WithLp.toLp 2 x∈winningCell (diagonalRows σ) h i ↔ x∈winnerEvent σ h i := by
    simp [winningCell,winnerEvent,scores]
  unfold NegativeVotingQuadraticMomentPadding.cellWeight winnerIndicator
  by_cases hx:x∈winnerEvent σ h i
  · simp [hx,he.mpr hx]
  · have hn : WithLp.toLp 2 x∉winningCell (diagonalRows σ) h i:=fun hh=>hx (he.mp hh)
    simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem hn]

/-- This is the actual Gaussian fan mass, not a separately postulated winner law. -/
theorem mass_diagonal_eq_winner_integral [Nonempty (Fin m)] (σ h : Fin m→ℝ) (hσ : ∀i,0<σ i) (i : Fin m) :
    mass (diagonalRows σ) h i=∫x,winnerIndicator σ h i x ∂γFin m := by
  have hh:=gaussianAverage_cellWeight_eq_mass (diagonalRows σ) (diagonalRows_injective σ hσ)
    h i 0 (by norm_num) 0
  simpa [gaussianAverage,cellWeight_diagonal] using hh.symm

theorem remainingProduct_eq_erase (f : Fin (n+1)→ℝ) (hf : ∀j,f j≠0) (i : Fin (n+1)) :
    (∏j:Fin n,f (i.succAbove j))=∏j∈Finset.univ.erase i,f j := by
  apply mul_left_cancel₀ (hf i)
  rw [←Fin.prod_univ_succAbove f i,Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

/-- Exact scalar affine substitution under the standard Gaussian. -/
theorem gaussian_affine_integral (σ h : ℝ) (hσ : 0<σ) (F : ℝ→ℝ) :
    (∫y,F (σ*y+h) ∂gaussianReal 0 1)=∫x,gaussianDensity σ h x*F x := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal)≠0)]
  let g:ℝ→ℝ:=fun x=>gaussianDensity σ h x*F x
  have hg : (fun y=>gaussianPDFReal 0 1 y • F (σ*y+h))=fun y=>σ*g (σ*y+h):=by
    funext y
    dsimp [g,gaussianDensity]
    have he : (σ*y+h-h)/σ=y:=by field_simp [hσ.ne'];ring
    rw [he]
    simp only [smul_eq_mul,normalPDF]
    field_simp [hσ.ne']
  rw [hg,integral_const_mul]
  have hh : (∫y,g (σ*y+h))=σ⁻¹*∫x,g x:=by
    rw [Measure.integral_comp_mul_left (fun x=>g (x+h)) σ,
      abs_of_pos (inv_pos.mpr hσ),smul_eq_mul,integral_add_right_eq_self]
  rw [hh]
  field_simp [hσ.ne']
  rfl

/-- Exact one-dimensional mass formula for independent, positive-variance
Gaussian scores, including the literal Gaussian density and all competing CDFs. -/
theorem mass_diagonal_integral (σ h : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j) (i : Fin (n+1)) :
    mass (diagonalRows σ) h i=
      ∫x,gaussianDensity (σ i) (h i) x*(∏j∈Finset.univ.erase i,gaussianCDF (σ j) (h j) x) := by
  rw [mass_diagonal_eq_winner_integral σ h hσ i,winner_integral_conditioned σ h hσ i]
  have hh : (fun y=>∏j:Fin n,gaussianCDF (σ (i.succAbove j)) (h (i.succAbove j)) (σ i*y+h i))=
      fun y=>∏j∈Finset.univ.erase i,gaussianCDF (σ j) (h j) (σ i*y+h i):=by
    funext y
    exact remainingProduct_eq_erase _ (fun j=>(gaussianCDF_pos _ _ _).ne') i
  rw [hh]
  exact gaussian_affine_integral (σ i) (h i) (hσ i) (fun x=>∏j∈Finset.univ.erase i,gaussianCDF (σ j) (h j) x)

/-- A common translation of every row leaves each literal winning cell unchanged. -/
theorem winningCell_common_row_sub {d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (B : V→FSC.Coord d) (h : V→ℝ) (v : FSC.Coord d) (i : V) :
    winningCell (fun j=>B j-v) h i=winningCell B h i := by
  ext x
  simp only [winningCell,Set.mem_setOf_eq,scores,inner_sub_left]
  apply forall_congr'
  intro j
  constructor <;> intro hh <;> linarith

theorem mass_common_row_sub {d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (B : V→FSC.Coord d) (hB : Function.Injective B) (h : V→ℝ) (v : FSC.Coord d) (i : V) :
    mass (fun j=>B j-v) h i=mass B h i := by
  have hb : Function.Injective (fun j=>B j-v):=by
    intro i j he
    apply hB
    simpa only [sub_add_cancel] using congrArg (fun x=>x+v) he
  rw [mass_eq_winningCell _ hb,mass_eq_winningCell _ hB,winningCell_common_row_sub]

/-- Centering the independent diagonal rows does not alter the exact mass law. -/
theorem mass_centered_diagonal_integral (σ h : Fin (n+1)→ℝ) (hσ : ∀j,0<σ j)
    (v : FSC.Coord (n+1)) (i : Fin (n+1)) :
    mass (fun j=>diagonalRows σ j-v) h i=
      ∫x,gaussianDensity (σ i) (h i) x*(∏j∈Finset.univ.erase i,gaussianCDF (σ j) (h j) x) := by
  rw [mass_common_row_sub _ (diagonalRows_injective σ hσ),mass_diagonal_integral σ h hσ i]

end NegativeVotingDiagonalWinnerIntegral
