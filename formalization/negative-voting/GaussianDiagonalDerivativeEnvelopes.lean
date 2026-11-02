import GaussianHazardWeightedSecondBounds

/-! Scalar, literal derivative envelopes for diagonal Gaussian paths.
No selected-offset regularity or bound on its second derivative is assumed. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Classical
namespace NegativeVotingDiagonalDerivativeEnvelopes
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingHazardSecondDifferentiation
  NegativeVotingHazardWeightedSecondBounds

def firstEnvelope (H σ₁ h₁ : ℝ) : ℝ := 16*(1+H)^2*(|σ₁|+|h₁|)
def secondEnvelope (H σ₁ h₁ σ₂ h₂ : ℝ) : ℝ :=
  128*(1+H)^2*(|σ₂|+|h₂|+σ₁^2+h₁^2)

lemma firstEnvelope_nonneg (H σ₁ h₁ : ℝ) : 0 ≤ firstEnvelope H σ₁ h₁ := by
  unfold firstEnvelope; positivity
lemma secondEnvelope_nonneg (H σ₁ h₁ σ₂ h₂ : ℝ) :
    0 ≤ secondEnvelope H σ₁ h₁ σ₂ h₂ := by
  unfold secondEnvelope; positivity

lemma abs_div_pow_le (σ y : ℝ) (k : ℕ) (hσ : 1/2 ≤ σ) :
    |y/σ^k| ≤ (2:ℝ)^k*|y| := by
  have hp : 0 < σ := by linarith
  have hi : σ⁻¹ ≤ 2 := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2) hσ
    norm_num [one_div] at hi ⊢
    exact hi
  have hk := pow_le_pow_left₀ (inv_nonneg.mpr hp.le) hi k
  calc
    |y/σ^k| = |y| *(σ⁻¹)^k := by
      rw [abs_div,abs_pow,abs_of_pos hp,div_eq_mul_inv,inv_pow]
    _ ≤ |y| *(2:ℝ)^k := mul_le_mul_of_nonneg_left hk (abs_nonneg _)
    _ = _ := mul_comm _ _

private lemma abs_div_le (σ y : ℝ) (hσ : 1/2 ≤ σ) : |y/σ| ≤ 2*|y| := by
  simpa using abs_div_pow_le σ y 1 hσ

private lemma radius_bounds (H h x : ℝ) (hH : 0 ≤ H) (hh : |h| ≤ H) :
    1 ≤ (1+H)*(1+|x|) ∧ |x-h| ≤ (1+H)*(1+|x|) := by
  have hx := abs_nonneg x
  have ha : |x-h| ≤ |x|+|h| := abs_sub _ _
  constructor <;> nlinarith

private lemma transport_raw (σ h σ₁ h₁ x R : ℝ) (hσ : 1/2 ≤ σ)
    (hR : 1 ≤ R) (hb : |x-h| ≤ R) :
    |transportSpeed σ h σ₁ h₁ x| ≤ 16*R^2*(|σ₁|+|h₁|) := by
  have hmul := mul_le_mul (abs_div_le σ σ₁ hσ) hb (abs_nonneg _) (by positivity : 0 ≤ 2*|σ₁|)
  rw [←abs_mul] at hmul
  have ha := (abs_add_le h₁ (σ₁/σ*(x-h))).trans (add_le_add (le_refl |h₁|) hmul)
  have hRR : R ≤ R^2 := by nlinarith
  have h1 : 1 ≤ R^2 := by nlinarith
  have hA := mul_le_mul_of_nonneg_right hRR (abs_nonneg σ₁)
  have hB := mul_le_mul_of_nonneg_right h1 (abs_nonneg h₁)
  dsimp [transportSpeed]
  nlinarith [mul_nonneg (sq_nonneg R) (abs_nonneg σ₁),mul_nonneg (sq_nonneg R) (abs_nonneg h₁)]

private lemma density_raw (σ h σ₁ h₁ x R : ℝ) (hσ : 1/2 ≤ σ)
    (hR : 1 ≤ R) (hb : |x-h| ≤ R) :
    |densityLogDerivative σ h σ₁ h₁ x| ≤ 16*R^2*(|σ₁|+|h₁|) := by
  have ha : |-σ₁/σ| ≤ 2*|σ₁| := by simpa using abs_div_le σ (-σ₁) hσ
  have hb1 : |(x-h)*h₁/σ^2| ≤ 4*R*|h₁| := by
    have hd := abs_div_pow_le σ ((x-h)*h₁) 2 hσ
    rw [abs_mul] at hd
    norm_num at hd
    nlinarith [mul_le_mul_of_nonneg_right hb (abs_nonneg h₁)]
  have hb2 : |(x-h)^2*σ₁/σ^3| ≤ 8*R^2*|σ₁| := by
    have hd := abs_div_pow_le σ ((x-h)^2*σ₁) 3 hσ
    rw [abs_mul,abs_pow] at hd
    norm_num at hd
    have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hs
    nlinarith [mul_le_mul_of_nonneg_right hs (abs_nonneg σ₁)]
  have hc := (abs_add_le (-σ₁/σ+(x-h)*h₁/σ^2) ((x-h)^2*σ₁/σ^3)).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add ha hb1)) hb2)
  have hRR : R ≤ R^2 := by nlinarith
  have h1 : 1 ≤ R^2 := by nlinarith
  have hA := mul_le_mul_of_nonneg_right h1 (abs_nonneg σ₁)
  have hB := mul_le_mul_of_nonneg_right hRR (abs_nonneg h₁)
  dsimp [densityLogDerivative]
  nlinarith [mul_nonneg (sq_nonneg R) (abs_nonneg σ₁),mul_nonneg (sq_nonneg R) (abs_nonneg h₁)]

theorem transportSpeed_abs_le (σ h σ₁ h₁ H x : ℝ)
    (hσ : 1/2 ≤ σ) (hH : 0 ≤ H) (hh : |h| ≤ H) :
    |transportSpeed σ h σ₁ h₁ x| ≤ firstEnvelope H σ₁ h₁*(1+|x|)^2 := by
  rcases radius_bounds H h x hH hh with ⟨hR,hb⟩
  convert transport_raw σ h σ₁ h₁ x ((1+H)*(1+|x|)) hσ hR hb using 1 <;>
    dsimp [firstEnvelope] <;> ring

theorem densityLogDerivative_abs_le (σ h σ₁ h₁ H x : ℝ)
    (hσ : 1/2 ≤ σ) (hH : 0 ≤ H) (hh : |h| ≤ H) :
    |densityLogDerivative σ h σ₁ h₁ x| ≤ firstEnvelope H σ₁ h₁*(1+|x|)^2 := by
  rcases radius_bounds H h x hH hh with ⟨hR,hb⟩
  convert density_raw σ h σ₁ h₁ x ((1+H)*(1+|x|)) hσ hR hb using 1 <;>
    dsimp [firstEnvelope] <;> ring

private lemma transport_second_raw (σ h σ₁ h₁ σ₂ h₂ x R : ℝ) (hσ : 1/2 ≤ σ)
    (hR : 1 ≤ R) (hb : |x-h| ≤ R) :
    |transportAcceleration σ h σ₁ h₁ σ₂ h₂ x| ≤
      128*R^2*(|σ₂|+|h₂|+σ₁^2+h₁^2) := by
  have hfirst := abs_div_le σ σ₂ hσ
  have hsquare := abs_div_pow_le σ (σ₁^2) 2 hσ
  simp only [abs_sq] at hsquare
  norm_num at hsquare
  have hdiff : |σ₂/σ-σ₁^2/σ^2| ≤ 2*|σ₂|+4*σ₁^2 :=
    (abs_sub _ _).trans (add_le_add hfirst hsquare)
  have hprod := mul_le_mul hdiff hb (abs_nonneg _) (by positivity : 0 ≤ 2*|σ₂|+4*σ₁^2)
  rw [←abs_mul] at hprod
  have hcross : |σ₁*h₁/σ| ≤ σ₁^2+h₁^2 := by
    have hd := abs_div_le σ (σ₁*h₁) hσ
    rw [abs_mul] at hd
    nlinarith [sq_nonneg (|σ₁|-|h₁|),sq_abs σ₁,sq_abs h₁]
  have ha := (abs_sub (h₂+(σ₂/σ-σ₁^2/σ^2)*(x-h)) (σ₁*h₁/σ)).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (le_refl |h₂|) hprod)) hcross)
  have hRR : R ≤ R^2 := by nlinarith
  have h1 : 1 ≤ R^2 := by nlinarith
  have hA := mul_le_mul_of_nonneg_right hRR (abs_nonneg σ₂)
  have hB := mul_le_mul_of_nonneg_right h1 (abs_nonneg h₂)
  have hC := mul_le_mul_of_nonneg_right hRR (sq_nonneg σ₁)
  have hD := mul_le_mul_of_nonneg_right h1 (sq_nonneg h₁)
  dsimp [transportAcceleration]
  nlinarith [mul_nonneg (sq_nonneg R) (abs_nonneg σ₂),
    mul_nonneg (sq_nonneg R) (abs_nonneg h₂),mul_nonneg (sq_nonneg R) (sq_nonneg σ₁),
    mul_nonneg (sq_nonneg R) (sq_nonneg h₁)]

private lemma density_second_raw (σ h σ₁ h₁ σ₂ h₂ x R : ℝ) (hσ : 1/2 ≤ σ)
    (hR : 1 ≤ R) (hb : |x-h| ≤ R) :
    |densityLogAcceleration σ h σ₁ h₁ σ₂ h₂ x| ≤
      128*R^2*(|σ₂|+|h₂|+σ₁^2+h₁^2) := by
  have h1 : |-σ₂/σ| ≤ 2*|σ₂| := by simpa using abs_div_le σ (-σ₂) hσ
  have h2 : |σ₁^2/σ^2| ≤ 4*σ₁^2 := by
    have hd := abs_div_pow_le σ (σ₁^2) 2 hσ
    simp only [abs_sq] at hd
    norm_num at hd
    exact hd
  have h3 : |(x-h)*h₂/σ^2| ≤ 4*R*|h₂| := by
    have hd := abs_div_pow_le σ ((x-h)*h₂) 2 hσ
    simp only [abs_mul] at hd
    norm_num at hd
    nlinarith [mul_le_mul_of_nonneg_right hb (abs_nonneg h₂)]
  have h4 : |h₁^2/σ^2| ≤ 4*h₁^2 := by
    have hd := abs_div_pow_le σ (h₁^2) 2 hσ
    simp only [abs_sq] at hd
    norm_num at hd
    exact hd
  have h5 : |4*(x-h)*h₁*σ₁/σ^3| ≤ 16*R*(h₁^2+σ₁^2) := by
    have hd := abs_div_pow_le σ (4*(x-h)*h₁*σ₁) 3 hσ
    simp only [abs_mul] at hd
    norm_num at hd
    have hcross : 2*(|h₁| *|σ₁|) ≤ h₁^2+σ₁^2 := by
      nlinarith [sq_nonneg (|h₁|-|σ₁|),sq_abs σ₁,sq_abs h₁]
    have hm := mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg h₁) (abs_nonneg σ₁))
    have hc := mul_le_mul_of_nonneg_left hcross (by linarith : 0 ≤ R)
    nlinarith
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [sq_abs] at hs
  have h6 : |(x-h)^2*σ₂/σ^3| ≤ 8*R^2*|σ₂| := by
    have hd := abs_div_pow_le σ ((x-h)^2*σ₂) 3 hσ
    simp only [abs_mul,abs_pow] at hd
    norm_num at hd
    nlinarith [mul_le_mul_of_nonneg_right hs (abs_nonneg σ₂)]
  have h7 : |3*(x-h)^2*σ₁^2/σ^4| ≤ 48*R^2*σ₁^2 := by
    have hd := abs_div_pow_le σ (3*(x-h)^2*σ₁^2) 4 hσ
    simp only [abs_mul,abs_pow,abs_sq] at hd
    norm_num at hd
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg σ₁)]
  have ha : |densityLogAcceleration σ h σ₁ h₁ σ₂ h₂ x| ≤
      2*|σ₂|+4*σ₁^2+4*R*|h₂|+4*h₁^2+16*R*(h₁^2+σ₁^2)+8*R^2*|σ₂|+48*R^2*σ₁^2 := by
    unfold densityLogAcceleration
    exact (abs_sub _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add
          ((abs_sub _ _).trans (add_le_add
            ((abs_add_le _ _).trans (add_le_add
              ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)) h5)) h6)) h7)
  have hRR : R ≤ R^2 := by nlinarith
  have hOne : 1 ≤ R^2 := by nlinarith
  have hA := mul_le_mul_of_nonneg_right hOne (abs_nonneg σ₂)
  have hB := mul_le_mul_of_nonneg_right hRR (abs_nonneg h₂)
  have hC := mul_le_mul_of_nonneg_right hOne (sq_nonneg σ₁)
  have hD := mul_le_mul_of_nonneg_right hOne (sq_nonneg h₁)
  have hE := mul_le_mul_of_nonneg_right hRR (sq_nonneg σ₁)
  have hF := mul_le_mul_of_nonneg_right hRR (sq_nonneg h₁)
  nlinarith [mul_nonneg (sq_nonneg R) (abs_nonneg σ₂),
    mul_nonneg (sq_nonneg R) (abs_nonneg h₂),mul_nonneg (sq_nonneg R) (sq_nonneg σ₁),
    mul_nonneg (sq_nonneg R) (sq_nonneg h₁)]

theorem transportAcceleration_abs_le (σ h σ₁ h₁ σ₂ h₂ H x : ℝ)
    (hσ : 1/2 ≤ σ) (hH : 0 ≤ H) (hh : |h| ≤ H) :
    |transportAcceleration σ h σ₁ h₁ σ₂ h₂ x| ≤
      secondEnvelope H σ₁ h₁ σ₂ h₂*(1+|x|)^4 := by
  rcases radius_bounds H h x hH hh with ⟨hR,hb⟩
  have hr := transport_second_raw σ h σ₁ h₁ σ₂ h₂ x ((1+H)*(1+|x|)) hσ hR hb
  have hx : (1+|x|)^2 ≤ (1+|x|)^4 := by nlinarith [abs_nonneg x,sq_nonneg |x|]
  have hp := mul_le_mul_of_nonneg_left hx (secondEnvelope_nonneg H σ₁ h₁ σ₂ h₂)
  refine hr.trans ?_
  convert hp using 1 <;> dsimp [secondEnvelope] <;> ring

theorem densityLogAcceleration_abs_le (σ h σ₁ h₁ σ₂ h₂ H x : ℝ)
    (hσ : 1/2 ≤ σ) (hH : 0 ≤ H) (hh : |h| ≤ H) :
    |densityLogAcceleration σ h σ₁ h₁ σ₂ h₂ x| ≤
      secondEnvelope H σ₁ h₁ σ₂ h₂*(1+|x|)^4 := by
  rcases radius_bounds H h x hH hh with ⟨hR,hb⟩
  have hr := density_second_raw σ h σ₁ h₁ σ₂ h₂ x ((1+H)*(1+|x|)) hσ hR hb
  have hx : (1+|x|)^2 ≤ (1+|x|)^4 := by nlinarith [abs_nonneg x,sq_nonneg |x|]
  have hp := mul_le_mul_of_nonneg_left hx (secondEnvelope_nonneg H σ₁ h₁ σ₂ h₂)
  refine hr.trans ?_
  convert hp using 1 <;> dsimp [secondEnvelope] <;> ring

end NegativeVotingDiagonalDerivativeEnvelopes
