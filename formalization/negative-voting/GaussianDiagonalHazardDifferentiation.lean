import GaussianMaximum
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Exact derivatives of the actual diagonal Gaussian maximum density.
Every label remains in the product derivative. These pointwise identities do
not assert the uniform moment or balanced-offset estimates still needed for
the exterior row-payment argument. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped BigOperators Topology Classical
namespace NegativeVotingDiagonalHazardDifferentiation
open WeakSimplex

/-- Standard deviation parametrization; all applications have positive σ. -/
def gaussianCDF (σ h x : ℝ) : ℝ := normalCDF ((x-h)/σ)
def gaussianDensity (σ h x : ℝ) : ℝ := normalPDF ((x-h)/σ)/σ
def gaussianHazard (σ h x : ℝ) : ℝ := gaussianDensity σ h x/gaussianCDF σ h x

def transportSpeed (σ h σ' h' x : ℝ) : ℝ := h'+σ'/σ*(x-h)
def densityLogDerivative (σ h σ' h' x : ℝ) : ℝ :=
  -σ'/σ+(x-h)*h'/σ^2+(x-h)^2*σ'/σ^3

lemma gaussianCDF_pos (σ h x : ℝ) : 0 < gaussianCDF σ h x := normalCDF_pos _
lemma gaussianDensity_pos (σ h x : ℝ) (hσ : 0 < σ) :
    0 < gaussianDensity σ h x := div_pos (normalPDF_pos _) hσ
lemma gaussianHazard_pos (σ h x : ℝ) (hσ : 0 < σ) :
    0 < gaussianHazard σ h x := div_pos (gaussianDensity_pos _ _ _ hσ) (gaussianCDF_pos _ _ _)

lemma standardized_hasDerivAt (σ h : ℝ → ℝ) (t σ' h' x : ℝ)
    (hσ : HasDerivAt σ σ' t) (hh : HasDerivAt h h' t) (hpos : 0 < σ t) :
    HasDerivAt (fun z=>(x-h z)/σ z)
      (-transportSpeed (σ t) (h t) σ' h' x/σ t) t := by
  have hd := ((hasDerivAt_const t x).sub hh).div hσ hpos.ne'
  convert hd using 1 <;> dsimp [transportSpeed] <;> field_simp <;> ring

lemma gaussianCDF_hasDerivAt (σ h : ℝ → ℝ) (t σ' h' x : ℝ)
    (hσ : HasDerivAt σ σ' t) (hh : HasDerivAt h h' t) (hpos : 0 < σ t) :
    HasDerivAt (fun z=>gaussianCDF (σ z) (h z) x)
      (-gaussianDensity (σ t) (h t) x*transportSpeed (σ t) (h t) σ' h' x) t := by
  have hd := (hasDerivAt_normalCDF ((x-h t)/σ t)).comp t
    (standardized_hasDerivAt σ h t σ' h' x hσ hh hpos)
  convert hd using 1
  · funext z; rfl
  · dsimp [gaussianDensity]; ring

lemma gaussianDensity_hasDerivAt (σ h : ℝ → ℝ) (t σ' h' x : ℝ)
    (hσ : HasDerivAt σ σ' t) (hh : HasDerivAt h h' t) (hpos : 0 < σ t) :
    HasDerivAt (fun z=>gaussianDensity (σ z) (h z) x)
      (gaussianDensity (σ t) (h t) x*densityLogDerivative (σ t) (h t) σ' h' x) t := by
  have hd := ((hasDerivAt_normalPDF ((x-h t)/σ t)).comp t
    (standardized_hasDerivAt σ h t σ' h' x hσ hh hpos)).div hσ hpos.ne'
  convert hd using 1
  · funext z; rfl
  · dsimp [gaussianDensity,densityLogDerivative,transportSpeed]; field_simp; ring

lemma gaussianHazard_hasDerivAt (σ h : ℝ → ℝ) (t σ' h' x : ℝ)
    (hσ : HasDerivAt σ σ' t) (hh : HasDerivAt h h' t) (hpos : 0 < σ t) :
    HasDerivAt (fun z=>gaussianHazard (σ z) (h z) x)
      (gaussianHazard (σ t) (h t) x*(densityLogDerivative (σ t) (h t) σ' h' x+
        gaussianHazard (σ t) (h t) x*transportSpeed (σ t) (h t) σ' h' x)) t := by
  have hd := (gaussianDensity_hasDerivAt σ h t σ' h' x hσ hh hpos).div
    (gaussianCDF_hasDerivAt σ h t σ' h' x hσ hh hpos) (gaussianCDF_pos _ _ _).ne'
  convert hd using 1
  · funext z; rfl
  · dsimp [gaussianHazard]
    field_simp [(gaussianCDF_pos (σ t) (h t) x).ne']
    <;> ring

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma product_hasDerivAt_of_logDerivative (s : Finset V) (f : V → ℝ → ℝ)
    (c : V → ℝ) (t : ℝ) (hf : ∀ i∈s,HasDerivAt (f i) (f i t*c i) t) :
    HasDerivAt (fun z=>∏i∈s,f i z) ((∏i∈s,f i t)*(∑i∈s,c i)) t := by
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const t (1:ℝ)
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs := ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj))
    have hd := hfi.mul hfs
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    convert hd using 1 <;> ring

def productCDF (σ h : V → ℝ) (x : ℝ) : ℝ := ∏i,gaussianCDF (σ i) (h i) x

def hazardPairDensity (σ h : V → ℝ) (x : ℝ) (i j : V) : ℝ :=
  productCDF σ h x*gaussianHazard (σ i) (h i) x*gaussianHazard (σ j) (h j) x

def totalHazardFlux (σ h σ' h' : V → ℝ) (x : ℝ) : ℝ :=
  ∑k,gaussianHazard (σ k) (h k) x*transportSpeed (σ k) (h k) (σ' k) (h' k) x

def hazardPairLogDerivative (σ h σ' h' : V → ℝ) (x : ℝ) (i j : V) : ℝ :=
  densityLogDerivative (σ i) (h i) (σ' i) (h' i) x+
  densityLogDerivative (σ j) (h j) (σ' j) (h' j) x+
  gaussianHazard (σ i) (h i) x*transportSpeed (σ i) (h i) (σ' i) (h' i) x+
  gaussianHazard (σ j) (h j) x*transportSpeed (σ j) (h j) (σ' j) (h' j) x-
  totalHazardFlux σ h σ' h' x

lemma productCDF_hasDerivAt (σ h : V → ℝ → ℝ) (t x : ℝ) (σ' h' : V → ℝ)
    (hσ : ∀ i,HasDerivAt (σ i) (σ' i) t) (hh : ∀ i,HasDerivAt (h i) (h' i) t)
    (hpos : ∀ i,0 < σ i t) :
    HasDerivAt (fun z=>productCDF (fun i=>σ i z) (fun i=>h i z) x)
      (-productCDF (fun i=>σ i t) (fun i=>h i t) x*
        totalHazardFlux (fun i=>σ i t) (fun i=>h i t) σ' h' x) t := by
  have hd := product_hasDerivAt_of_logDerivative Finset.univ
    (fun i z=>gaussianCDF (σ i z) (h i z) x)
    (fun i=>-gaussianHazard (σ i t) (h i t) x*transportSpeed (σ i t) (h i t) (σ' i) (h' i) x) t
    (fun i _=>by
      convert gaussianCDF_hasDerivAt (σ i) (h i) t (σ' i) (h' i) x (hσ i) (hh i) (hpos i) using 1
      dsimp [gaussianHazard]
      field_simp [(gaussianCDF_pos (σ i t) (h i t) x).ne'])
  convert hd using 1
  all_goals simp only [productCDF,totalHazardFlux,neg_mul,Finset.sum_neg_distrib,mul_neg]

/-- The derivative includes the full all-label flux. This also applies to
 i=j, which is an analytic coefficient and is not a geometric facet. -/
lemma hazardPairDensity_hasDerivAt (σ h : V → ℝ → ℝ) (t x : ℝ) (σ' h' : V → ℝ)
    (hσ : ∀ i,HasDerivAt (σ i) (σ' i) t) (hh : ∀ i,HasDerivAt (h i) (h' i) t)
    (hpos : ∀ i,0 < σ i t) (i j : V) :
    HasDerivAt (fun z=>hazardPairDensity (fun k=>σ k z) (fun k=>h k z) x i j)
      (hazardPairDensity (fun k=>σ k t) (fun k=>h k t) x i j*
        hazardPairLogDerivative (fun k=>σ k t) (fun k=>h k t) σ' h' x i j) t := by
  have hd := ((productCDF_hasDerivAt σ h t x σ' h' hσ hh hpos).mul
    (gaussianHazard_hasDerivAt (σ i) (h i) t (σ' i) (h' i) x (hσ i) (hh i) (hpos i))).mul
    (gaussianHazard_hasDerivAt (σ j) (h j) t (σ' j) (h' j) x (hσ j) (hh j) (hpos j))
  simp only [Pi.mul_apply] at hd
  convert hd using 1
  · funext z; rfl
  · dsimp [hazardPairDensity,hazardPairLogDerivative]; ring

end NegativeVotingDiagonalHazardDifferentiation
