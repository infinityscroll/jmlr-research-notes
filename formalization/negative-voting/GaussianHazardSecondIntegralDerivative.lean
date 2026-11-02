import GaussianHazardRawIntegralDerivative
import GaussianDiagonalDerivativeEnvelopes
import GaussianHazardSecondMomentIntegral

/-! Actual second differentiation of the raw pair integral on a neighborhood
with bounded first and second coefficients. No continuity of accelerations is
required: the common dominating function is Gaussian times a polynomial. -/
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set WeakSimplex
open scoped BigOperators Classical Topology
namespace NegativeVotingHazardSecondIntegralDerivative
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingHazardSecondDifferentiation
  NegativeVotingHazardWeightedSecondBounds NegativeVotingHazardSecondMomentIntegral
  NegativeVotingHazardMomentEnvelope NegativeVotingHazardIntegrability
  NegativeVotingHazardPolynomialBounds NegativeVotingHazardRawIntegralDerivative
  NegativeVotingDiagonalDerivativeEnvelopes NegativeVotingDensityMomentBounds
variable {m : ℕ}

lemma rawFirst_integrable (σ h σ₁ h₁ q : Fin m→ℝ) (H : ℝ)
    (hσ : ∀i,1/2 ≤ σ i) (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H)
    (hq : ∀i,0 ≤ q i)
    (hb : ∀x i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hL : ∀x i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (i j : Fin m) :
    Integrable (fun x=>hazardPairDensity σ h x i j*hazardPairLogDerivative σ h σ₁ h₁ x i j) volume := by
  letI : Nonempty (Fin m) := ⟨i⟩
  let W := q i+q j+mean q
  have hI := ((integrable_momentDensity σ h (1/2) H (by norm_num) hσ hH hh 0 2 i j).add
    (integrable_momentDensity σ h (1/2) H (by norm_num) hσ hH hh 1 2 i j)).const_mul W
  apply hI.mono' ((continuous_hazardPairDensity σ h i j).mul
    (hazardPairLogDerivative_continuous σ h σ₁ h₁ i j)).aestronglyMeasurable
  filter_upwards with x
  have hr := hazardPairDensity_nonneg σ h (fun i=>by linarith [hσ i]) x i j
  have hp := pairLogDerivative_abs_le σ h σ₁ h₁ q (fun i=>by linarith [hσ i])
    x (1+|x|) hq (hb x) (hL x) i j
  simp only [Pi.mul_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hr]
  convert mul_le_mul_of_nonneg_left hp hr using 1 <;>
    try simp only [momentDensity,pow_zero,pow_one]
  all_goals dsimp [W];ring

lemma pairSecondDensity_box_bound (σ h σ₁ h₁ σ₂ h₂ q u : Fin m→ℝ)
    (S H x : ℝ) (hσ : ∀i,1/2 ≤ σ i) (hS : ∀i,σ i ≤ S)
    (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H) (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hb' : ∀i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (hL' : ∀i,|densityLogAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*(1+|x|)^4)
    (i j : Fin m) :
    |pairSecondDensity σ h σ₁ h₁ σ₂ h₂ i j x| ≤
      ((normalPDF 0/(1/2)*Real.exp (H^2/(2*S^2)))*linearHazardConstant (1/2) H*
        (1+(m:ℝ)*linearHazardConstant (1/2) H)^2*pairWeight q u i j)*
        (Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^7) := by
  letI : Nonempty (Fin m) := ⟨i⟩
  let C := linearHazardConstant (1/2) H
  let D := normalPDF 0/(1/2)*Real.exp (H^2/(2*S^2))
  let X := 1+|x|
  have hC : 0 ≤ C := linearHazardConstant_nonneg _ _ (by norm_num) hH
  have hD : 0 ≤ D := by dsimp [D];positivity [normalPDF_pos 0]
  have hX : 1 ≤ X := by dsimp [X];linarith [abs_nonneg x]
  have hpos (k:Fin m) : 0 < σ k := by linarith [hσ k]
  have hr : hazardPairDensity σ h x i j ≤ D*Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(C*X) := by
    exact (hazardPairDensity_le_density_hazard σ h hpos x i j).trans
      (mul_le_mul (gaussianDensity_box_envelope _ _ _ (1/2) S H (by norm_num) (hσ i) (hS i) (hh i))
        (uniform_hazard_polynomial _ _ _ (1/2) H (by norm_num) (hσ j) hH (hh j))
        (gaussianHazard_pos _ _ _ (hpos j)).le (by positivity))
  have hmax : maxHazard σ h x ≤ C*X := maxHazard_polynomial σ h (1/2) H x (by norm_num) hσ hH hh
  have hY : 1+(m:ℝ)*maxHazard σ h x ≤ (1+(m:ℝ)*C)*X := by
    have hm := mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg m)
    nlinarith
  have hY0 : 0 ≤ 1+(m:ℝ)*maxHazard σ h x := by positivity [maxHazard_nonneg σ h hpos x]
  have hY2 := pow_le_pow_left₀ hY0 hY 2
  have hc := pairSecondCoefficient_abs_le σ h σ₁ h₁ σ₂ h₂ q u hpos x X hq hu hb hL hb' hL' i j
  have hW := pairWeight_nonneg q u hu i j
  have hmul := mul_le_mul_of_nonneg_left hY2 (by positivity : 0 ≤ X^4*pairWeight q u i j)
  have hc' : |(hazardPairLogDerivative σ h σ₁ h₁ x i j)^2+
      hazardPairLogAcceleration σ h σ₁ h₁ σ₂ h₂ x i j| ≤
      (1+(m:ℝ)*C)^2*X^6*pairWeight q u i j := by
    have hc0 : |(hazardPairLogDerivative σ h σ₁ h₁ x i j)^2+
        hazardPairLogAcceleration σ h σ₁ h₁ σ₂ h₂ x i j| ≤
        X^4*(1+(m:ℝ)*maxHazard σ h x)^2*pairWeight q u i j := by
      simpa only [Fintype.card_fin,pairWeight] using hc
    refine hc0.trans ?_
    convert hmul using 1 <;> ring
  unfold pairSecondDensity
  rw [abs_mul,abs_of_nonneg (hazardPairDensity_nonneg σ h hpos x i j)]
  have hprod := mul_le_mul hr hc' (abs_nonneg _) (by positivity : 0 ≤ D*Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(C*X))
  convert hprod using 1 <;> dsimp [C,D,X] <;> ring

/-- Actual derivative of the first raw derivative integral. Local boundedness
of the second coefficients is sufficient; their continuity is not required. -/
theorem rawFirstIntegral_hasDerivAt (σ h σ₁ h₁ σ₂ h₂ : ℝ→Fin m→ℝ)
    (t S H : ℝ) (G : Set ℝ) (hG : G∈𝓝 t) (hH : 0 ≤ H)
    (q u : Fin m→ℝ) (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i)
    (hbox : ∀z∈G,∀i,1/2 ≤ σ z i ∧ σ z i ≤ S ∧ |h z i| ≤ H)
    (hσ : ∀z∈G,∀i,HasDerivAt (fun y=>σ y i) (σ₁ z i) z)
    (hh : ∀z∈G,∀i,HasDerivAt (fun y=>h y i) (h₁ z i) z)
    (hσ₁ : ∀z∈G,∀i,HasDerivAt (fun y=>σ₁ y i) (σ₂ z i) z)
    (hh₁ : ∀z∈G,∀i,HasDerivAt (fun y=>h₁ y i) (h₂ z i) z)
    (hqbound : ∀z∈G,∀i,firstEnvelope H (σ₁ z i) (h₁ z i) ≤ q i)
    (hubound : ∀z∈G,∀i,secondEnvelope H (σ₁ z i) (h₁ z i) (σ₂ z i) (h₂ z i) ≤ u i)
    (i j : Fin m) :
    HasDerivAt (fun z=>∫x,hazardPairDensity (σ z) (h z) x i j*
      hazardPairLogDerivative (σ z) (h z) (σ₁ z) (h₁ z) x i j)
      (∫x,pairSecondDensity (σ t) (h t) (σ₁ t) (h₁ t) (σ₂ t) (h₂ t) i j x) t := by
  letI : Nonempty (Fin m) := ⟨i⟩
  have ht : t∈G := mem_of_mem_nhds hG
  have hS : 0 < S := by linarith [(hbox t ht i).1,(hbox t ht i).2.1]
  have hb (z:ℝ) (hz:z∈G) (x:ℝ) (i:Fin m) :
      |transportSpeed (σ z i) (h z i) (σ₁ z i) (h₁ z i) x| ≤ q i*(1+|x|)^2 :=
    (transportSpeed_abs_le _ _ _ _ _ _ (hbox z hz i).1 hH (hbox z hz i).2.2).trans
      (mul_le_mul_of_nonneg_right (hqbound z hz i) (sq_nonneg _))
  have hL (z:ℝ) (hz:z∈G) (x:ℝ) (i:Fin m) :
      |densityLogDerivative (σ z i) (h z i) (σ₁ z i) (h₁ z i) x| ≤ q i*(1+|x|)^2 :=
    (densityLogDerivative_abs_le _ _ _ _ _ _ (hbox z hz i).1 hH (hbox z hz i).2.2).trans
      (mul_le_mul_of_nonneg_right (hqbound z hz i) (sq_nonneg _))
  have hb' (z:ℝ) (hz:z∈G) (x:ℝ) (i:Fin m) :
      |transportAcceleration (σ z i) (h z i) (σ₁ z i) (h₁ z i) (σ₂ z i) (h₂ z i) x| ≤ u i*(1+|x|)^4 :=
    (transportAcceleration_abs_le _ _ _ _ _ _ _ _ (hbox z hz i).1 hH (hbox z hz i).2.2).trans
      (mul_le_mul_of_nonneg_right (hubound z hz i) (by positivity))
  have hL' (z:ℝ) (hz:z∈G) (x:ℝ) (i:Fin m) :
      |densityLogAcceleration (σ z i) (h z i) (σ₁ z i) (h₁ z i) (σ₂ z i) (h₂ z i) x| ≤ u i*(1+|x|)^4 :=
    (densityLogAcceleration_abs_le _ _ _ _ _ _ _ _ (hbox z hz i).1 hH (hbox z hz i).2.2).trans
      (mul_le_mul_of_nonneg_right (hubound z hz i) (by positivity))
  let C := (normalPDF 0/(1/2)*Real.exp (H^2/(2*S^2)))*linearHazardConstant (1/2) H*
    (1+(m:ℝ)*linearHazardConstant (1/2) H)^2*pairWeight q u i j
  have hbase := rawFirst_integrable (σ t) (h t) (σ₁ t) (h₁ t) q H
    (fun i=>(hbox t ht i).1) hH (fun i=>(hbox t ht i).2.2) hq (hb t ht) (hL t ht) i j
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=G) (bound:=fun x:ℝ=>C*(Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^7))
    (F:=fun z x=>hazardPairDensity (σ z) (h z) x i j*hazardPairLogDerivative (σ z) (h z) (σ₁ z) (h₁ z) x i j)
    (F':=fun z x=>pairSecondDensity (σ z) (h z) (σ₁ z) (h₁ z) (σ₂ z) (h₂ z) i j x)
    hG (by filter_upwards with z;exact ((continuous_hazardPairDensity _ _ i j).mul
      (hazardPairLogDerivative_continuous _ _ _ _ i j)).aestronglyMeasurable)
    hbase (continuous_pairSecondDensity _ _ _ _ _ _ i j).aestronglyMeasurable ?_ ?_ ?_).2
  · filter_upwards with x
    intro z hz
    simpa only [Real.norm_eq_abs,C] using pairSecondDensity_box_bound (σ z) (h z) (σ₁ z) (h₁ z)
      (σ₂ z) (h₂ z) q u S H x (fun i=>(hbox z hz i).1) (fun i=>(hbox z hz i).2.1)
      hH (fun i=>(hbox z hz i).2.2) hq hu (hb z hz x) (hL z hz x) (hb' z hz x) (hL' z hz x) i j
  · have hi : Integrable (fun x:ℝ=>Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^7) volume := by
      simpa only [sub_zero] using integrable_gaussian_exp_kernel_polynomial S 0 (1/2) hS (by norm_num) 7
    exact hi.const_mul C
  · filter_upwards with x
    intro z hz
    exact hazardPairDensity_second_hasDerivAt (fun i z=>σ z i) (fun i z=>h z i)
      (fun i z=>σ₁ z i) (fun i z=>h₁ z i) z x (σ₂ z) (h₂ z)
      (hσ z hz) (hh z hz) (hσ₁ z hz) (hh₁ z hz) (fun i=>by linarith [(hbox z hz i).1]) i j

end NegativeVotingHazardSecondIntegralDerivative
