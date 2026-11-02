import GaussianHazardSecondDifferentiation
import GaussianHazardMomentEnvelope

/-! Weighted algebra for the complete all-label second derivative.
The mean-square structure avoids a label-count loss before integration. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped BigOperators Classical
namespace NegativeVotingHazardWeightedSecondBounds
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingHazardSecondDifferentiation
  NegativeVotingHazardMomentEnvelope NegativeVotingHazardPolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def mean (q : V→ℝ) : ℝ := (∑i,q i)/(Fintype.card V:ℝ)

lemma mean_nonneg (q : V→ℝ) (hq : ∀i,0 ≤ q i) : 0 ≤ mean q := by
  exact div_nonneg (Finset.sum_nonneg fun i _=>hq i) (Nat.cast_nonneg _)

lemma card_mul_mean (q : V→ℝ) : (Fintype.card V:ℝ)*mean q=∑i,q i := by
  unfold mean
  exact mul_div_cancel₀ _ (by exact_mod_cast Fintype.card_ne_zero)

lemma mean_square_le (q : V→ℝ) : (mean q)^2 ≤ mean (fun i=>(q i)^2) := by
  have hh:=Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ) (f:=q) (g:=fun _=>(1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  have hm:(0:ℝ)<Fintype.card V:=by exact_mod_cast Fintype.card_pos
  unfold mean
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hm)).2
  convert hh using 1 <;> field_simp <;> ring

lemma triple_square_le (a b c : ℝ) : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
  nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]

lemma maxHazard_le_card_mul (σ h : V→ℝ) (hσ : ∀i,0<σ i) (x : ℝ) :
    maxHazard σ h x ≤ (Fintype.card V:ℝ)*maxHazard σ h x := by
  have hm:(1:ℝ) ≤ Fintype.card V:=by exact_mod_cast Fintype.card_pos
  nlinarith [maxHazard_nonneg σ h hσ x]

lemma hazard_le_max (σ h : V→ℝ) (x : ℝ) (i : V) :
    gaussianHazard (σ i) (h i) x ≤ maxHazard σ h x :=
  Finset.le_sup' (fun k=>gaussianHazard (σ k) (h k) x) (Finset.mem_univ i)

lemma totalHazardFlux_abs_le (σ h σ₁ h₁ q : V→ℝ) (hσ : ∀i,0<σ i)
    (x X : ℝ) (hq : ∀i,0 ≤ q i)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2) :
    |totalHazardFlux σ h σ₁ h₁ x| ≤ maxHazard σ h x*X^2*(∑i,q i) := by
  unfold totalHazardFlux
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm (i:V):|gaussianHazard (σ i) (h i) x*transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤
      maxHazard σ h x*X^2*q i := by
    rw [abs_mul,abs_of_nonneg (gaussianHazard_pos _ _ _ (hσ i)).le]
    convert mul_le_mul (hazard_le_max σ h x i) (hb i) (abs_nonneg _)
      (maxHazard_nonneg σ h hσ x) using 1 <;> ring
  have hh:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>hterm i
  exact hh.trans_eq (by rw [Finset.mul_sum])

lemma abs_five (A B C D E : ℝ) : |A+B+C+D-E| ≤ |A|+|B|+|C|+|D|+|E| := by
  have h1:=abs_add_le A B
  have h2:=abs_add_le (A+B) C
  have h3:=abs_add_le (A+B+C) D
  have h4:|A+B+C+D-E| ≤ |A+B+C+D|+|E|:=by simpa using abs_sub_le (A+B+C+D) 0 E
  linarith


theorem pairLogDerivative_abs_le (σ h σ₁ h₁ q : V→ℝ) (hσ : ∀i,0<σ i)
    (x X : ℝ) (hq : ∀i,0 ≤ q i)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (i j : V) :
    |hazardPairLogDerivative σ h σ₁ h₁ x i j| ≤ 
      X^2*(1+(Fintype.card V:ℝ)*maxHazard σ h x)*(q i+q j+mean q) := by
  let H:=maxHazard σ h x
  have hH:0 ≤ H:=maxHazard_nonneg σ h hσ x
  have hM:0 ≤ mean q:=mean_nonneg q hq
  have hlocal (k:V) : |gaussianHazard (σ k) (h k) x*
      transportSpeed (σ k) (h k) (σ₁ k) (h₁ k) x| ≤ H*q k*X^2 := by
    rw [abs_mul,abs_of_nonneg (gaussianHazard_pos _ _ _ (hσ k)).le]
    convert mul_le_mul (hazard_le_max σ h x k) (hb k) (abs_nonneg _) hH using 1 <;> ring
  have ht:=totalHazardFlux_abs_le σ h σ₁ h₁ q hσ x X hq hb
  have hab : |hazardPairLogDerivative σ h σ₁ h₁ x i j| ≤ 
      |densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x|+
      |densityLogDerivative (σ j) (h j) (σ₁ j) (h₁ j) x|+
      |gaussianHazard (σ i) (h i) x*transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x|+
      |gaussianHazard (σ j) (h j) x*transportSpeed (σ j) (h j) (σ₁ j) (h₁ j) x|+
      |totalHazardFlux σ h σ₁ h₁ x| := by
    exact abs_five _ _ _ _ _
  have hbase:=hab.trans (add_le_add (add_le_add (add_le_add (add_le_add (hL i) (hL j))
    (hlocal i)) (hlocal j)) ht)
  have hmH:H ≤ (Fintype.card V:ℝ)*H:=maxHazard_le_card_mul σ h hσ x
  have hinc: H*(q i+q j) ≤ (Fintype.card V:ℝ)*H*(q i+q j):=
    mul_le_mul_of_nonneg_right hmH (add_nonneg (hq i) (hq j))
  have hcard:=card_mul_mean q
  have hs: q i*X^2+q j*X^2+H*q i*X^2+H*q j*X^2+H*X^2*(∑k,q k) ≤ 
      X^2*(1+(Fintype.card V:ℝ)*H)*(q i+q j+mean q) := by
    rw [←hcard]
    nlinarith [mul_nonneg (sq_nonneg X) hM,
      mul_le_mul_of_nonneg_left hinc (sq_nonneg X)]
  exact hbase.trans hs

theorem pairLogDerivative_sq_le (σ h σ₁ h₁ q : V→ℝ) (hσ : ∀i,0<σ i)
    (x X : ℝ) (hq : ∀i,0 ≤ q i)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (i j : V) :
    (hazardPairLogDerivative σ h σ₁ h₁ x i j)^2 ≤ 
      3*X^4*(1+(Fintype.card V:ℝ)*maxHazard σ h x)^2*
        ((q i)^2+(q j)^2+mean (fun k=>(q k)^2)) := by
  have hab:=pairLogDerivative_abs_le σ h σ₁ h₁ q hσ x X hq hb hL i j
  have hs:=pow_le_pow_left₀ (abs_nonneg _) hab 2
  rw [sq_abs] at hs
  have ht: (q i+q j+mean q)^2 ≤ 3*((q i)^2+(q j)^2+mean (fun k=>(q k)^2)) := by
    have hh:=triple_square_le (q i) (q j) (mean q)
    linarith [mean_square_le q]
  have hp:=mul_le_mul_of_nonneg_left ht
    (by positivity : (0:ℝ) ≤ X^4*(1+(Fintype.card V:ℝ)*maxHazard σ h x)^2)
  refine hs.trans ?_
  convert hp using 1 <;> ring


lemma hazardFluxAcceleration_abs_le (σ h σ₁ h₁ σ₂ h₂ q u : V→ℝ)
    (hσ : ∀i,0<σ i) (x X : ℝ) (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hb' : ∀i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*X^4)
    (i : V) :
    |hazardFluxAcceleration σ h σ₁ h₁ σ₂ h₂ x i| ≤
      maxHazard σ h x*X^4*((1+maxHazard σ h x)*(q i)^2+u i) := by
  let H:=maxHazard σ h x
  have hH:0 ≤ H:=maxHazard_nonneg σ h hσ x
  have ha:0 ≤ gaussianHazard (σ i) (h i) x:=(gaussianHazard_pos _ _ _ (hσ i)).le
  have hmul:|gaussianHazard (σ i) (h i) x*transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ H*(q i*X^2):=by
    rw [abs_mul,abs_of_nonneg ha]
    exact mul_le_mul (hazard_le_max σ h x i) (hb i) (abs_nonneg _) hH
  have hsum:|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x+
      gaussianHazard (σ i) (h i) x*transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤
      q i*X^2+H*(q i*X^2):=(abs_add_le _ _).trans (add_le_add (hL i) hmul)
  have hprod:=mul_le_mul hsum (hb i) (abs_nonneg _) (by positivity [hq i] : 0 ≤ q i*X^2+H*(q i*X^2))
  have hint:=add_le_add hprod (hb' i)
  rw [←abs_mul] at hint
  have hout:=mul_le_mul (hazard_le_max σ h x i) ((abs_add_le _ _).trans hint)
    (abs_nonneg _) hH
  unfold hazardFluxAcceleration
  rw [abs_mul,abs_of_nonneg ha]
  convert hout using 1 <;> ring

lemma weighted_accumulations (H m A B : ℝ) (hH : 0 ≤ H) (hm : 1 ≤ m)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (1+H)*A+H*m*B ≤ (1+m*H)^2*(A+B) ∧
    H*(1+H)*(A+m*B) ≤ (1+m*H)^2*(A+B) := by
  have hMH:H ≤ m*H:=by nlinarith
  have hw:0 ≤ m*H:=le_trans hH hMH
  have ha:1+H ≤ (1+m*H)^2:=by nlinarith [sq_nonneg (m*H)]
  have hb:m*H ≤ (1+m*H)^2:=by nlinarith [sq_nonneg (m*H)]
  have hc:H*(1+H) ≤ (1+m*H)^2:=by
    have hh:=mul_le_mul hMH (add_le_add_left hMH 1) (by linarith) hw
    nlinarith [sq_nonneg (m*H)]
  have hd:m*H*(1+H) ≤ (1+m*H)^2:=by
    have hh:=mul_le_mul_of_nonneg_left (add_le_add_left hMH 1) hw
    nlinarith [sq_nonneg (m*H)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right ha hA,mul_le_mul_of_nonneg_right hb hB]
  · nlinarith [mul_le_mul_of_nonneg_right hc hA,mul_le_mul_of_nonneg_right hd hB]

theorem pairLogAcceleration_abs_le (σ h σ₁ h₁ σ₂ h₂ q u : V→ℝ)
    (hσ : ∀i,0<σ i) (x X : ℝ) (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hb' : ∀i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*X^4)
    (hL' : ∀i,|densityLogAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*X^4)
    (i j : V) :
    |hazardPairLogAcceleration σ h σ₁ h₁ σ₂ h₂ x i j| ≤
      X^4*(1+(Fintype.card V:ℝ)*maxHazard σ h x)^2*
        ((q i)^2+(q j)^2+mean (fun k=>(q k)^2)+u i+u j+mean u) := by
  let H:=maxHazard σ h x
  have hH:0 ≤ H:=maxHazard_nonneg σ h hσ x
  have hm:(1:ℝ) ≤ Fintype.card V:=by exact_mod_cast Fintype.card_pos
  have hF (k:V):=hazardFluxAcceleration_abs_le σ h σ₁ h₁ σ₂ h₂ q u hσ x X hq hu hb hL hb' k
  have hS:|∑k,hazardFluxAcceleration σ h σ₁ h₁ σ₂ h₂ x k| ≤
      H*X^4*((1+H)*(∑k,(q k)^2)+∑k,u k) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hh:=Finset.sum_le_sum (s:=Finset.univ) fun k _=>hF k
    refine hh.trans_eq ?_
    rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum]
  have hbound:|hazardPairLogAcceleration σ h σ₁ h₁ σ₂ h₂ x i j| ≤
      u i*X^4+u j*X^4+H*X^4*((1+H)*(q i)^2+u i)+
      H*X^4*((1+H)*(q j)^2+u j)+H*X^4*((1+H)*(∑k,(q k)^2)+∑k,u k) := by
    exact (abs_five _ _ _ _ _).trans
      (add_le_add (add_le_add (add_le_add (add_le_add (hL' i) (hL' j)) (hF i)) (hF j)) hS)
  have hQ:0 ≤ mean (fun k=>(q k)^2):=mean_nonneg _ fun _=>sq_nonneg _
  have hU:0 ≤ mean u:=mean_nonneg u hu
  have hqbound:=(weighted_accumulations H (Fintype.card V) ((q i)^2+(q j)^2)
    (mean (fun k=>(q k)^2)) hH hm (add_nonneg (sq_nonneg _) (sq_nonneg _)) hQ).2
  have hubound:=(weighted_accumulations H (Fintype.card V) (u i+u j) (mean u)
    hH hm (add_nonneg (hu i) (hu j)) hU).1
  have hout:=mul_le_mul_of_nonneg_left (add_le_add hqbound hubound) (by positivity : (0:ℝ) ≤ X^4)
  refine hbound.trans ?_
  rw [←card_mul_mean (fun k=>(q k)^2),←card_mul_mean u]
  convert hout using 1 <;> ring

/-- The pointwise second density coefficient keeps coordinate squares plus
their average, with the same all-label hazard moment used by the actual
uniform integral theorem. -/
theorem pairSecondCoefficient_abs_le (σ h σ₁ h₁ σ₂ h₂ q u : V→ℝ)
    (hσ : ∀i,0<σ i) (x X : ℝ) (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hb' : ∀i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*X^4)
    (hL' : ∀i,|densityLogAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x| ≤ u i*X^4)
    (i j : V) :
    |(hazardPairLogDerivative σ h σ₁ h₁ x i j)^2+
      hazardPairLogAcceleration σ h σ₁ h₁ σ₂ h₂ x i j| ≤
      X^4*(1+(Fintype.card V:ℝ)*maxHazard σ h x)^2*
        (4*((q i)^2+(q j)^2+mean (fun k=>(q k)^2))+u i+u j+mean u) := by
  have h1:=pairLogDerivative_sq_le σ h σ₁ h₁ q hσ x X hq hb hL i j
  have h2:=pairLogAcceleration_abs_le σ h σ₁ h₁ σ₂ h₂ q u hσ x X hq hu hb hL hb' hL' i j
  have hh:=(abs_add_le ((hazardPairLogDerivative σ h σ₁ h₁ x i j)^2)
    (hazardPairLogAcceleration σ h σ₁ h₁ σ₂ h₂ x i j))
  rw [abs_of_nonneg (sq_nonneg (hazardPairLogDerivative σ h σ₁ h₁ x i j))] at hh
  exact hh.trans (by convert add_le_add h1 h2 using 1 <;> ring)

end NegativeVotingHazardWeightedSecondBounds
