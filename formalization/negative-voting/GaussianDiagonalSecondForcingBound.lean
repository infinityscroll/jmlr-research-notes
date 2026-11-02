import GaussianDiagonalDerivativeEnvelopes
import GaussianDiagonalOffsetContinuation
import GaussianHazardSecondMomentIntegral

/-! The second balancing source excludes the unknown offset acceleration.
The estimates concern literal integrals; differentiating the balancing identity
is a separate theorem. -/
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped BigOperators Classical Topology
namespace NegativeVotingDiagonalSecondForcingBound
open NegativeVotingDiagonalDerivativeEnvelopes NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingHazardSecondDifferentiation NegativeVotingHazardWeightedSecondBounds
  NegativeVotingHazardSecondMomentIntegral NegativeVotingHazardMomentEnvelope
  NegativeVotingHazardIntegrability NegativeVotingHazardPolynomialBounds
  NegativeVotingDiagonalOffsetComponentBound NegativeVotingDiagonalOffsetContinuation
  NegativeVotingHazardQuantileAsymptotics NegativeVotingGaussianMaximum
  NegativeVotingFanInverse NegativeVotingRegularDiagonalBalance

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The part of the differentiated mass flux which does not contain h''. -/
def secondForcingDensity (σ h σ₁ h₁ σ₂ : V→ℝ) (i j : V) (x : ℝ) : ℝ :=
  hazardPairDensity σ h x i j *
    (hazardPairLogDerivative σ h σ₁ h₁ x i j *
      (transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x-
        transportSpeed (σ j) (h j) (σ₁ j) (h₁ j) x)+
      (transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) 0 x-
        transportAcceleration (σ j) (h j) (σ₁ j) (h₁ j) (σ₂ j) 0 x))

def secondForcing (σ h σ₁ h₁ σ₂ : V→ℝ) (i : V) : ℝ :=
  ∑j,∫x,secondForcingDensity σ h σ₁ h₁ σ₂ i j x

lemma transportAcceleration_split (σ h σ₁ h₁ σ₂ h₂ x : ℝ) :
    transportAcceleration σ h σ₁ h₁ σ₂ h₂ x =
      h₂+transportAcceleration σ h σ₁ h₁ σ₂ 0 x := by
  unfold transportAcceleration;ring

lemma secondForcingDensity_diag (σ h σ₁ h₁ σ₂ : V→ℝ) (i : V) :
    secondForcingDensity σ h σ₁ h₁ σ₂ i i=0 := by
  funext x;simp [secondForcingDensity]

lemma continuous_secondForcingDensity (σ h σ₁ h₁ σ₂ : V→ℝ) (i j : V) :
    Continuous (secondForcingDensity σ h σ₁ h₁ σ₂ i j) := by
  have hr := continuous_hazardPairDensity σ h i j
  have ha (k:V) := continuous_gaussianHazard (σ k) (h k)
  unfold secondForcingDensity hazardPairLogDerivative totalHazardFlux
    transportSpeed transportAcceleration densityLogDerivative
  fun_prop

lemma secondForcing_coefficient_bound (σ h σ₁ h₁ σ₂ q u : V→ℝ)
    (hσ : ∀i,0<σ i) (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i) (x X : ℝ)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*X^2)
    (hb' : ∀i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) 0 x| ≤ u i*X^4)
    (i j : V) :
    |hazardPairLogDerivative σ h σ₁ h₁ x i j *
      (transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x-
        transportSpeed (σ j) (h j) (σ₁ j) (h₁ j) x)+
      (transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) 0 x-
        transportAcceleration (σ j) (h j) (σ₁ j) (h₁ j) (σ₂ j) 0 x)| ≤
      X^4*(1+(Fintype.card V:ℝ)*maxHazard σ h x)^2*pairWeight q u i j := by
  let P := hazardPairLogDerivative σ h σ₁ h₁ x i j
  let d := transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x-
    transportSpeed (σ j) (h j) (σ₁ j) (h₁ j) x
  let Z := 1+(Fintype.card V:ℝ)*maxHazard σ h x
  let Q := (q i)^2+(q j)^2+mean (fun k=>(q k)^2)
  have hZ : 1 ≤ Z := by
    have hnon : 0 ≤ (Fintype.card V:ℝ)*maxHazard σ h x := by positivity [maxHazard_nonneg σ h hσ x]
    dsimp [Z];linarith
  have hZ2 : 1 ≤ Z^2 := by nlinarith
  have hQ : 0 ≤ Q := by dsimp [Q];positivity [mean_nonneg (fun k=>(q k)^2) (fun _=>sq_nonneg _)]
  have hP : P^2 ≤ 3*X^4*Z^2*Q := pairLogDerivative_sq_le σ h σ₁ h₁ q hσ x X hq hb hL i j
  have hdabs : |d| ≤ (q i+q j)*X^2 := by
    have hh := (abs_sub _ _).trans (add_le_add (hb i) (hb j))
    convert hh using 1 <;> ring
  have hd : d^2 ≤ 2*X^4*Q := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) hdabs 2
    rw [sq_abs] at hs
    have ht : (q i+q j)^2 ≤ 2*Q := by
      dsimp [Q]
      nlinarith [sq_nonneg (q i-q j),mean_nonneg (fun k=>(q k)^2) (fun _=>sq_nonneg _)]
    have hm := mul_le_mul_of_nonneg_right ht (sq_nonneg (X^2))
    nlinarith
  have hdZ : d^2 ≤ 2*X^4*Z^2*Q := by
    have hm := mul_le_mul_of_nonneg_left hZ2 (by positivity : 0 ≤ 2*X^4*Q)
    exact hd.trans (by nlinarith)
  have hpabs : |P*d| ≤ (P^2+d^2)/2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|P|-|d|),sq_abs P,sq_abs d]
  have hpbound : |P*d| ≤ 4*X^4*Z^2*Q := by
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ X^4) (mul_nonneg (sq_nonneg Z) hQ)]
  have hab : |transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) 0 x-
        transportAcceleration (σ j) (h j) (σ₁ j) (h₁ j) (σ₂ j) 0 x| ≤
      (u i+u j)*X^4 := by
    convert (abs_sub _ _).trans (add_le_add (hb' i) (hb' j)) using 1 <;> ring
  have huZ : (u i+u j)*X^4 ≤ X^4*Z^2*(u i+u j+mean u) := by
    have hm := mul_le_mul_of_nonneg_left hZ2 (by positivity [hu i,hu j] : 0 ≤ X^4*(u i+u j))
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ X^4) (sq_nonneg Z)) (mean_nonneg u hu)]
  have hfinal := (abs_add_le _ _).trans (add_le_add hpbound (hab.trans huZ))
  convert hfinal using 1 <;> try dsimp [P,d,Z,Q,pairWeight]
  all_goals ring

theorem secondForcingDensity_envelope (σ h σ₁ h₁ σ₂ q u : V→ℝ)
    (hσ : ∀i,0<σ i) (hq : ∀i,0 ≤ q i) (hu : ∀i,0 ≤ u i) (x : ℝ)
    (hb : ∀i,|transportSpeed (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hL : ∀i,|densityLogDerivative (σ i) (h i) (σ₁ i) (h₁ i) x| ≤ q i*(1+|x|)^2)
    (hb' : ∀i,|transportAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) 0 x| ≤ u i*(1+|x|)^4)
    (i j : V) :
    |secondForcingDensity σ h σ₁ h₁ σ₂ i j x| ≤
      2*pairWeight q u i j*(momentDensity σ h 0 4 i j x+momentDensity σ h 2 4 i j x) := by
  have hc := secondForcing_coefficient_bound σ h σ₁ h₁ σ₂ q u hσ hq hu x (1+|x|) hb hL hb' i j
  have hr := hazardPairDensity_nonneg σ h hσ x i j
  have hy : (1+(Fintype.card V:ℝ)*maxHazard σ h x)^2 ≤
      2*(1+((Fintype.card V:ℝ)*maxHazard σ h x)^2) := by
    nlinarith [sq_nonneg ((Fintype.card V:ℝ)*maxHazard σ h x-1)]
  have hp := mul_le_mul_of_nonneg_left hy
    (by positivity [pairWeight_nonneg q u hu i j] :
      0 ≤ hazardPairDensity σ h x i j*(1+|x|)^4*pairWeight q u i j)
  unfold secondForcingDensity
  rw [abs_mul,abs_of_nonneg hr]
  refine (mul_le_mul_of_nonneg_left hc hr).trans ?_
  convert hp using 1 <;> try simp only [momentDensity,pow_zero]
  all_goals ring

theorem secondForcingDensity_integrable (σ h σ₁ h₁ σ₂ : V→ℝ)
    (H : ℝ) (hσ : ∀i,1/2 ≤ σ i) (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H)
    (i j : V) : Integrable (secondForcingDensity σ h σ₁ h₁ σ₂ i j) volume := by
  let q := fun i=>firstEnvelope H (σ₁ i) (h₁ i)
  let u := fun i=>secondEnvelope H (σ₁ i) (h₁ i) (σ₂ i) 0
  have hI := ((integrable_momentDensity σ h (1/2) H (by norm_num) hσ hH hh 0 4 i j).add
    (integrable_momentDensity σ h (1/2) H (by norm_num) hσ hH hh 2 4 i j)).const_mul (2*pairWeight q u i j)
  apply hI.mono' (continuous_secondForcingDensity σ h σ₁ h₁ σ₂ i j).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact secondForcingDensity_envelope σ h σ₁ h₁ σ₂ q u (fun i=>by linarith [hσ i])
    (fun i=>firstEnvelope_nonneg ..) (fun i=>secondEnvelope_nonneg ..) x
    (fun i=>transportSpeed_abs_le _ _ _ _ _ _ (hσ i) hH (hh i))
    (fun i=>densityLogDerivative_abs_le _ _ _ _ _ _ (hσ i) hH (hh i))
    (fun i=>transportAcceleration_abs_le _ _ _ _ _ _ _ _ (hσ i) hH (hh i)) i j

theorem secondForcingDensity_integral_abs_le (σ h σ₁ h₁ σ₂ : V→ℝ)
    (H M₀ M₂ : ℝ) (hσ : ∀i,1/2 ≤ σ i) (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H)
    (i j : V) (hm₀ : (∫x,momentDensity σ h 0 4 i j x) ≤ M₀)
    (hm₂ : (∫x,momentDensity σ h 2 4 i j x) ≤ M₂) :
    |∫x,secondForcingDensity σ h σ₁ h₁ σ₂ i j x| ≤
      2*pairWeight (fun i=>firstEnvelope H (σ₁ i) (h₁ i))
        (fun i=>secondEnvelope H (σ₁ i) (h₁ i) (σ₂ i) 0) i j*(M₀+M₂) := by
  let q := fun i=>firstEnvelope H (σ₁ i) (h₁ i)
  let u := fun i=>secondEnvelope H (σ₁ i) (h₁ i) (σ₂ i) 0
  have hI₀ := integrable_momentDensity σ h (1/2) H (by norm_num) hσ hH hh 0 4 i j
  have hI₂ := integrable_momentDensity σ h (1/2) H (by norm_num) hσ hH hh 2 4 i j
  have hI := secondForcingDensity_integrable σ h σ₁ h₁ σ₂ H hσ hH hh i j
  have henv : (∫x,|secondForcingDensity σ h σ₁ h₁ σ₂ i j x|) ≤
      2*pairWeight q u i j*((∫x,momentDensity σ h 0 4 i j x)+(∫x,momentDensity σ h 2 4 i j x)) := by
    rw [←integral_add hI₀ hI₂,←integral_const_mul]
    exact integral_mono hI.abs ((hI₀.add hI₂).const_mul _) fun x=>
      secondForcingDensity_envelope σ h σ₁ h₁ σ₂ q u (fun i=>by linarith [hσ i])
        (fun i=>firstEnvelope_nonneg ..) (fun i=>secondEnvelope_nonneg ..) x
        (fun i=>transportSpeed_abs_le _ _ _ _ _ _ (hσ i) hH (hh i))
        (fun i=>densityLogDerivative_abs_le _ _ _ _ _ _ (hσ i) hH (hh i))
        (fun i=>transportAcceleration_abs_le _ _ _ _ _ _ _ _ (hσ i) hH (hh i)) i j
  refine abs_integral_le_integral_abs.trans (henv.trans ?_)
  exact mul_le_mul_of_nonneg_left (add_le_add hm₀ hm₂)
    (by positivity [pairWeight_nonneg q u (fun i=>secondEnvelope_nonneg ..) i j])

theorem sum_secondForcing_abs_le (σ h σ₁ h₁ σ₂ : V→ℝ)
    (H M₀ M₂ : ℝ) (hσ : ∀i,1/2 ≤ σ i) (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H)
    (hm₀ : ∀i j,(∫x,momentDensity σ h 0 4 i j x) ≤ M₀)
    (hm₂ : ∀i j,(∫x,momentDensity σ h 2 4 i j x) ≤ M₂) :
    (∑i,|secondForcing σ h σ₁ h₁ σ₂ i|) ≤
      6*(Fintype.card V:ℝ)*(M₀+M₂)*
        (4*(∑i,(firstEnvelope H (σ₁ i) (h₁ i))^2)+
          ∑i,secondEnvelope H (σ₁ i) (h₁ i) (σ₂ i) 0) := by
  have hh₁ := Finset.sum_le_sum (s:=Finset.univ) fun i _=>
    Finset.abs_sum_le_sum_abs (fun j=>∫x,secondForcingDensity σ h σ₁ h₁ σ₂ i j x) Finset.univ
  have hh₂ := Finset.sum_le_sum (s:=Finset.univ) fun i _=>
    Finset.sum_le_sum (s:=Finset.univ) fun j _=>
      secondForcingDensity_integral_abs_le σ h σ₁ h₁ σ₂ H M₀ M₂ hσ hH hh i j (hm₀ i j) (hm₂ i j)
  refine hh₁.trans (hh₂.trans_eq ?_)
  simp only [←Finset.sum_mul,←Finset.mul_sum]
  rw [sum_pairWeight]
  ring

/-- Componentwise first-derivative control retains squared-direction energy
when summed; the mean term costs a constant, not a label count. -/
lemma sum_centered_magnitudes_sq (ξ : V→ℝ) :
    (∑i,(|ξ i|+meanAbs ξ)^2) ≤ 4*(∑i,(ξ i)^2) := by
  have hm : (0:ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hav := mean_square_le (fun i=>|ξ i|)
  have he : mean (fun i=>|ξ i|)=meanAbs ξ := rfl
  rw [he] at hav
  have hma : (Fintype.card V:ℝ)*(meanAbs ξ)^2 ≤ ∑i,(ξ i)^2 := by
    have hh := mul_le_mul_of_nonneg_left hav hm.le
    rw [card_mul_mean] at hh
    simpa only [sq_abs] using hh
  have hterm (i:V) : (|ξ i|+meanAbs ξ)^2 ≤ 2*(ξ i)^2+2*(meanAbs ξ)^2 := by
    nlinarith [sq_nonneg (|ξ i|-meanAbs ξ),sq_abs (ξ i)]
  have hs := Finset.sum_le_sum (s:=Finset.univ) fun i _=>hterm i
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  nlinarith

lemma sum_offset_speed_sq_le (ξ k : V→ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hk : ∀i,|k i| ≤ T*(|ξ i|+meanAbs ξ)) :
    (∑i,(k i)^2) ≤ 4*T^2*(∑i,(ξ i)^2) := by
  have hp (i:V) : (k i)^2 ≤ T^2*(|ξ i|+meanAbs ξ)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hk i) 2
    simpa only [sq_abs,mul_pow] using hh
  have hs := Finset.sum_le_sum (s:=Finset.univ) fun i _=>hp i
  rw [←Finset.mul_sum] at hs
  refine hs.trans ?_
  convert mul_le_mul_of_nonneg_left (sum_centered_magnitudes_sq ξ) (sq_nonneg T) using 1 <;> ring

lemma firstEnvelope_sq_le (H σ₁ h₁ : ℝ) :
    (firstEnvelope H σ₁ h₁)^2 ≤ 512*(1+H)^4*(σ₁^2+h₁^2) := by
  have hs : (|σ₁|+|h₁|)^2 ≤ 2*(σ₁^2+h₁^2) := by
    nlinarith [sq_nonneg (|σ₁|-|h₁|),sq_abs σ₁,sq_abs h₁]
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 256*(1+H)^4)
  convert hh using 1 <;> try dsimp [firstEnvelope]
  all_goals ring

lemma secondEnvelope_noaccel_le (H σ₁ h₁ σ₂ : ℝ) (hH : 0 ≤ H) :
    secondEnvelope H σ₁ h₁ σ₂ 0 ≤ 128*(1+H)^4*(|σ₂|+σ₁^2+h₁^2) := by
  have hp : (1+H)^2 ≤ (1+H)^4 := by
    exact pow_le_pow_right₀ (by linarith : 1 ≤ 1+H) (by norm_num : (2:ℕ) ≤ 4)
  have hh := mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 128*(|σ₂|+σ₁^2+h₁^2))
  convert hh using 1 <;> try simp only [secondEnvelope,abs_zero]
  all_goals ring

lemma variance_coefficient_component (H σ₁ h₁ σ₂ ξ : ℝ) (hH : 0 ≤ H)
    (hσ₁ : |σ₁| ≤ |ξ|) (hσ₂ : |σ₂| ≤ 2*ξ^2) :
    4*(firstEnvelope H σ₁ h₁)^2+secondEnvelope H σ₁ h₁ σ₂ 0 ≤
      4096*(1+H)^4*(ξ^2+h₁^2) := by
  have hs := pow_le_pow_left₀ (abs_nonneg _) hσ₁ 2
  simp only [sq_abs] at hs
  have hq := firstEnvelope_sq_le H σ₁ h₁
  have hu := secondEnvelope_noaccel_le H σ₁ h₁ σ₂ hH
  have hm₁ := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ (1+H)^4)
  have hm₂ := mul_le_mul_of_nonneg_left hσ₂ (by positivity : (0:ℝ) ≤ (1+H)^4)
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (1+H)^4) (sq_nonneg ξ),
    mul_nonneg (by positivity : (0:ℝ) ≤ (1+H)^4) (sq_nonneg h₁)]

lemma sum_variance_coefficients (H T : ℝ) (hH : 0 ≤ H) (hT : 1 ≤ T)
    (σ₁ h₁ σ₂ ξ : V→ℝ) (hσ₁ : ∀i,|σ₁ i| ≤ |ξ i|)
    (hσ₂ : ∀i,|σ₂ i| ≤ 2*(ξ i)^2)
    (hk : ∀i,|h₁ i| ≤ T*(|ξ i|+meanAbs ξ)) :
    4*(∑i,(firstEnvelope H (σ₁ i) (h₁ i))^2)+
      (∑i,secondEnvelope H (σ₁ i) (h₁ i) (σ₂ i) 0) ≤
      32768*(1+H)^4*T^2*(∑i,(ξ i)^2) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) fun i _=>
    variance_coefficient_component H (σ₁ i) (h₁ i) (σ₂ i) (ξ i) hH (hσ₁ i) (hσ₂ i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have hk₂ := sum_offset_speed_sq_le ξ h₁ T (by linarith) hk
  have hTm : 1 ≤ T^2 := by nlinarith
  have hE : 0 ≤ ∑i,(ξ i)^2 := Finset.sum_nonneg fun _ _=>sq_nonneg _
  have hK : 0 ≤ (1+H)^4 := by positivity
  have hsum := mul_le_mul_of_nonneg_left hk₂ (by positivity : (0:ℝ) ≤ 4096*(1+H)^4)
  have hbase := mul_le_mul_of_nonneg_right hTm (mul_nonneg hK hE)
  nlinarith [mul_nonneg (mul_nonneg hK (sq_nonneg T)) hE]

lemma variance_speed_abs_le (σ ξ : ℝ) (hσ : 1/2 ≤ σ) : |ξ/(2*σ)| ≤ |ξ| := by
  have hd := abs_div_pow_le σ ξ 1 hσ
  norm_num at hd
  calc
    |ξ/(2*σ)| = |ξ/σ|/2 := by rw [←abs_of_pos (by norm_num : (0:ℝ)<2),←abs_div];congr 1;ring
    _ ≤ |ξ| := by linarith

lemma variance_acceleration_abs_le (σ ξ : ℝ) (hσ : 1/2 ≤ σ) :
    |-(ξ^2)/(4*σ^3)| ≤ 2*ξ^2 := by
  have hd := abs_div_pow_le σ (ξ^2) 3 hσ
  simp only [abs_sq] at hd
  norm_num at hd
  calc
    |-(ξ^2)/(4*σ^3)| = |ξ^2/σ^3|/4 := by
      rw [←abs_of_pos (by norm_num : (0:ℝ)<4),←abs_div,←abs_neg];congr 1;ring
    _ ≤ 2*ξ^2 := by linarith

/-- A genuine summed source estimate with no offset acceleration in its
hypotheses or integrand. Raw pair moments and first speed control are explicit. -/
theorem variance_secondForcing_bound (σ h k ξ : V→ℝ) (H T M : ℝ)
    (hσ : ∀i,1/2 ≤ σ i) (hH : 0 ≤ H) (hh : ∀i,|h i| ≤ H)
    (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hk : ∀i,|k i| ≤ T*(|ξ i|+meanAbs ξ))
    (hm₀ : ∀i j,(∫x,momentDensity σ h 0 4 i j x) ≤ M)
    (hm₂ : ∀i j,(∫x,momentDensity σ h 2 4 i j x) ≤ M) :
    (∑i,|secondForcing σ h (fun i=>ξ i/(2*σ i)) k
      (fun i=>-(ξ i)^2/(4*(σ i)^3)) i|) ≤
      393216*(Fintype.card V:ℝ)*M*(1+H)^4*T^2*(∑i,(ξ i)^2) := by
  have hs := sum_secondForcing_abs_le σ h (fun i=>ξ i/(2*σ i)) k
    (fun i=>-(ξ i)^2/(4*(σ i)^3)) H M M hσ hH hh hm₀ hm₂
  have hc := sum_variance_coefficients H T hH hT (fun i=>ξ i/(2*σ i)) k
    (fun i=>-(ξ i)^2/(4*(σ i)^3)) ξ
    (fun i=>variance_speed_abs_le _ _ (hσ i))
    (fun i=>variance_acceleration_abs_le _ _ (hσ i)) hk
  refine hs.trans ?_
  convert mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 6*(Fintype.card V:ℝ)*(M+M)) using 1 <;> ring

/-- Uniform actual selected-path forcing. The common threshold precedes the
variance direction and time. In particular no offset box, moment estimate,
first-derivative bound or second derivative is assumed in this endpoint. -/
theorem exists_uniform_variance_secondForcing_bound (η A : ℝ)
    (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, MomentBoxControl n a η 2 8 ∧
        ∀ (ξ : Fin (n+2) → ℝ), (∀ i,|ξ i| ≤ A) →
        ∀ t∈Icc 0 (((n:ℝ)+2)^(-30*η)),
          ∃ k : centeredGauge (Fin (n+2)),
            HasDerivAt (varianceOffsets n ξ) k t ∧
            (∑i,|secondForcing (varianceSigma ξ t) (varianceOffsetVector n ξ t)
              (fun i=>ξ i/(2*varianceSigma ξ t i)) (k : Fin (n+2) → ℝ)
              (fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)) i|) ≤
              ((n:ℝ)+2)^(-1+8*η)*(∑i,(ξ i)^2) := by
  obtain ⟨a,ha,ha1,hcont⟩ := exists_uniform_variance_offset_continuation η A hη hA
  have habs := eventually_rpow_quantile_polynomial_le 393216 (by norm_num) 4
    (-1+13*η/2) (-1+8*η) (by linarith)
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards [hcont,habs,upperQuantile_tendsto.eventually_ge_atTop 1]
    with n hn habs_n hb
  refine ⟨hn.1,?_⟩
  intro ξ hξ t ht
  obtain ⟨hσ,hh,hsmall,k,hk,hkbound⟩ := hn.2 ξ hξ t ht
  refine ⟨k,hk,?_⟩
  let m : ℝ := (n:ℝ)+2
  let b : ℝ := upperQuantile n
  have hm : 0 < m := by dsimp [m];positivity
  have hm1 : 1 ≤ m := by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hb0 : 0 ≤ b := by dsimp [b];linarith
  have hhalf (i:Fin (n+2)) : 1/2 ≤ varianceSigma ξ t i := by
    linarith [(hσ i).1]
  have hoff (i:Fin (n+2)) : |varianceOffsetVector n ξ t i| ≤ a*b := (hh i).le
  have hM₀ (i j:Fin (n+2)) := (hn.1 0 4 (by norm_num) (by norm_num)
    (varianceSigma ξ t) (varianceOffsetVector n ξ t)
    (fun i=>(hσ i).1) (fun i=>(hσ i).2) hoff i j).2.1
  have hM₂ (i j:Fin (n+2)) := (hn.1 2 4 (by norm_num) (by norm_num)
    (varianceSigma ξ t) (varianceOffsetVector n ξ t)
    (fun i=>(hσ i).1) (fun i=>(hσ i).2) hoff i j).2.1
  have hbound := variance_secondForcing_bound (varianceSigma ξ t) (varianceOffsetVector n ξ t)
    (k : Fin (n+2) → ℝ) ξ (a*b) (m^(3*η)) (m^(-2+η/2)) hhalf
    (mul_nonneg ha.le hb0) hoff (Real.one_le_rpow hm1 (by positivity))
    (Real.rpow_nonneg hm.le _) hkbound hM₀ hM₂
  have hpoly : (1+a*b)^4 ≤ (1+b)^4 := by
    apply pow_le_pow_left₀ (by positivity)
    have haone : a ≤ 1 := by linarith
    nlinarith
  have hscale : 393216*(Fintype.card (Fin (n+2)):ℝ)*m^(-2+η/2)*(1+a*b)^4*(m^(3*η))^2 =
      393216*m^(-1+13*η/2)*(1+a*b)^4 := by
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
    change 393216*m*m^(-2+η/2)*(1+a*b)^4*(m^(3*η))^2 = _
    rw [←Real.rpow_mul_natCast hm.le]
    calc
      _ = 393216*(m^(1:ℝ)*m^(-2+η/2)*m^(3*η*2))*(1+a*b)^4 := by rw [Real.rpow_one];ring
      _ = _ := by rw [←Real.rpow_add hm,←Real.rpow_add hm];congr 2 <;> ring
  rw [hscale] at hbound
  have hcoef : 393216*m^(-1+13*η/2)*(1+a*b)^4 ≤ m^(-1+8*η) := by
    exact (mul_le_mul_of_nonneg_left hpoly (by positivity)).trans habs_n
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg fun _ _=>sq_nonneg _))

end NegativeVotingDiagonalSecondForcingBound
