import GaussianHazardWeightedSecondBounds

/-! Actual integrated second-density estimates from the uniform raw moments.
No derivative/interchange assertion is made by these integral inequalities. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators Topology Classical
namespace NegativeVotingHazardSecondMomentIntegral
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingHazardSecondDifferentiation
  NegativeVotingHazardWeightedSecondBounds NegativeVotingHazardMomentEnvelope
  NegativeVotingHazardIntegrability NegativeVotingHazardPolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def pairSecondDensity (σ h σ₁ h₁ σ₂ h₂ : V→ℝ) (i j : V) (x : ℝ) : ℝ :=
  hazardPairDensity σ h x i j*((hazardPairLogDerivative σ h σ₁ h₁ x i j)^2+
    hazardPairLogAcceleration σ h σ₁ h₁ σ₂ h₂ x i j)

def pairWeight (q u : V→ℝ) (i j : V) : ℝ :=
  4*((q i)^2+(q j)^2+mean (fun k=>(q k)^2))+u i+u j+mean u

lemma pairWeight_nonneg (q u : V→ℝ) (hu : ∀i,0 ≤ u i) (i j : V) : 0 ≤ pairWeight q u i j := by
  unfold pairWeight
  positivity [mean_nonneg (fun k=>(q k)^2) (fun _=>sq_nonneg _),mean_nonneg u hu,hu i,hu j]

lemma continuous_pairSecondDensity (σ h σ₁ h₁ σ₂ h₂ : V→ℝ) (i j : V) :
    Continuous (pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j) := by
  have hr:=continuous_hazardPairDensity σ h i j
  have ha (k:V):=continuous_gaussianHazard (σ k) (h k)
  unfold pairSecondDensity hazardPairLogDerivative hazardPairLogAcceleration totalHazardFlux
    hazardFluxAcceleration transportAcceleration densityLogAcceleration densityLogDerivative transportSpeed
  fun_prop

theorem pairSecondDensity_envelope (σ h σ₁ h₁ σ₂ h₂ q u : V→ℝ)
    (hσ : ∀i,0<σ i) (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i) (x : ℝ)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hb' : ∀i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (hL' : ∀i,|densityLogAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (i j : V) :
    |pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j x| ≤
      2*pairWeight q u i j*(momentDensity σ h 0 4 i j x+momentDensity σ h 2 4 i j x) := by
  have hc:=pairSecondCoefficient_abs_le σ h σ₁ h₁ σ₂ h₂ q u hσ x (1+|x|) hq hu hb hL hb' hL' i j
  have hr:=hazardPairDensity_nonneg σ h hσ x i j
  have hW:=pairWeight_nonneg q u hu i j
  have hy:(1+(Fintype.card V:ℝ)*maxHazard σ h x)^2 ≤
      2*(1+((Fintype.card V:ℝ)*maxHazard σ h x)^2) := by
    nlinarith [sq_nonneg ((Fintype.card V:ℝ)*maxHazard σ h x-1)]
  have hpow:=mul_le_mul_of_nonneg_left hy
    (by positivity : (0:ℝ) ≤ hazardPairDensity σ h x i j*(1+|x|)^4*pairWeight q u i j)
  unfold pairSecondDensity
  rw [abs_mul,abs_of_nonneg hr]
  refine (mul_le_mul_of_nonneg_left hc hr).trans ?_
  convert hpow using 1 <;> simp only [pairWeight,momentDensity,pow_zero] <;> ring

theorem pairSecondDensity_integrable (σ h σ₁ h₁ σ₂ h₂ q u : V→ℝ)
    (s H : ℝ) (hs : 0<s) (hσ : ∀i,s ≤ σ i) (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H)
    (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i)
    (hb : ∀x i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hL : ∀x i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hb' : ∀x i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (hL' : ∀x i,|densityLogAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (i j : V) : Integrable (pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j) volume := by
  have hI:=((integrable_momentDensity σ h s H hs hσ hH hh 0 4 i j).add
    (integrable_momentDensity σ h s H hs hσ hH hh 2 4 i j)).const_mul (2*pairWeight q u i j)
  apply hI.mono' (continuous_pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact pairSecondDensity_envelope σ h σ₁ h₁ σ₂ h₂ q u (fun i=>hs.trans_le (hσ i))
    hq hu x (hb x) (hL x) (hb' x) (hL' x) i j

theorem pairSecondDensity_integral_abs_le (σ h σ₁ h₁ σ₂ h₂ q u : V→ℝ)
    (s H M₀ M₂ : ℝ) (hs : 0<s) (hσ : ∀i,s ≤ σ i) (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H)
    (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i)
    (hb : ∀x i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hL : ∀x i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hb' : ∀x i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (hL' : ∀x i,|densityLogAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (i j : V) (hm₀ : (∫x,momentDensity σ h 0 4 i j x) ≤ M₀)
    (hm₂ : (∫x,momentDensity σ h 2 4 i j x) ≤ M₂) :
    |∫x,pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j x| ≤ 2*pairWeight q u i j*(M₀+M₂) := by
  have hI₀:=integrable_momentDensity σ h s H hs hσ hH hh 0 4 i j
  have hI₂:=integrable_momentDensity σ h s H hs hσ hH hh 2 4 i j
  have hI:=pairSecondDensity_integrable σ h σ₁ h₁ σ₂ h₂ q u s H hs hσ hH hh hq hu hb hL hb' hL' i j
  have henv: (∫x,|pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j x|) ≤
      2*pairWeight q u i j*((∫x,momentDensity σ h 0 4 i j x)+(∫x,momentDensity σ h 2 4 i j x)) := by
    rw [←integral_add hI₀ hI₂,←integral_const_mul]
    exact integral_mono hI.abs ((hI₀.add hI₂).const_mul _) fun x=>
      pairSecondDensity_envelope σ h σ₁ h₁ σ₂ h₂ q u (fun i=>hs.trans_le (hσ i))
        hq hu x (hb x) (hL x) (hb' x) (hL' x) i j
  have hn:=norm_integral_le_integral_norm (μ:=volume) (f:=pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j)
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans (henv.trans (mul_le_mul_of_nonneg_left (add_le_add hm₀ hm₂)
    (mul_nonneg (by norm_num) (pairWeight_nonneg q u hu i j))))

lemma sum_pairWeight (q u : V→ℝ) :
    (∑i,∑j,pairWeight q u i j)=3*(Fintype.card V:ℝ)*(4*(∑i,(q i)^2)+∑i,u i) := by
  unfold pairWeight
  simp_rw [mul_add,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp only [←Finset.mul_sum,←Finset.sum_mul,card_mul_mean]
  unfold mean
  field_simp
  ring

/-- Summing the actual pair integrals costs one label count, rather than two.
Thus raw pair moments of size m^(-2+eta) give a total m^(-1+eta)
coefficient against the summed squared perturbation. -/
theorem sum_pairSecondDensity_integral_abs_le (σ h σ₁ h₁ σ₂ h₂ q u : V→ℝ)
    (s H M₀ M₂ : ℝ) (hs : 0<s) (hσ : ∀i,s ≤ σ i) (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H)
    (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i)
    (hb : ∀x i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hL : ∀x i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hb' : ∀x i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (hL' : ∀x i,|densityLogAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (hm₀ : ∀i j,(∫x,momentDensity σ h 0 4 i j x) ≤ M₀)
    (hm₂ : ∀i j,(∫x,momentDensity σ h 2 4 i j x) ≤ M₂) :
    (∑i,∑j,|∫x,pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j x|) ≤
      6*(Fintype.card V:ℝ)*(M₀+M₂)*(4*(∑i,(q i)^2)+∑i,u i) := by
  have hh:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>
    Finset.sum_le_sum (s:=Finset.univ) fun j _=>
      pairSecondDensity_integral_abs_le σ h σ₁ h₁ σ₂ h₂ q u s H M₀ M₂ hs hσ hH hh
        hq hu hb hL hb' hL' i j (hm₀ i j) (hm₂ i j)
  refine hh.trans_eq ?_
  simp only [←Finset.sum_mul,←Finset.mul_sum]
  rw [sum_pairWeight]
  ring

end NegativeVotingHazardSecondMomentIntegral
