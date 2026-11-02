import GaussianStructuredSwitchingAmplitude
import GaussianNearBalancedSourceInputs
import GaussianNearRegularEnergyLogBound

/-! Bounds for the literal switching amplitude, composed with actual selected
near-balanced cells and the actual high-mode residual inputs. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingStructuredAmplitudeBound
open NegativeVotingStructuredSwitchingAmplitude NegativeVotingStructuredSwitchingMoments
  NegativeVotingStructuredSwitchingFacet NegativeVotingStructuredSwitchingFacetEnergy
  NegativeVotingStructuredSwitchingTube NegativeVotingSmoothErrorMoment
  NegativeVotingNearBalancedSourceInputs NegativeVotingStructuredResidualInputs
  NegativeVotingNearRegularNormalizedBounds NegativeVotingNearRegularGraphGap
  NegativeVotingNearRegularEnergyLogBound NegativeVotingNormalTrace NegativeVotingNormalDerivatives
  NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanInverse
  NegativeVotingActualFacetOUTrace NegativeVotingDisintegration
  NegativeVotingPolynomialFacetLogBound NegativeVotingProjection
  OAI.MinUncut.GaussianHermite
variable {d n:ℕ}

theorem four_squares (a b c d:ℝ) :
    (a+b+c+d)^2  ≤  4*(a^2+b^2+c^2+d^2) := by
  nlinarith [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),
    sq_nonneg (b-c),sq_nonneg (b-d),sq_nonneg (c-d)]

theorem linear_four_square (a b c x y z w:ℝ) :
    (a*x+b*y+c*(z+w))^2   ≤  
      4*((a^2+b^2)*(x^2+y^2)+c^2*(z^2+w^2)) := by
  have hh:=four_squares (a*x) (b*y) (c*z) (c*w)
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg y),
    mul_nonneg (sq_nonneg b) (sq_nonneg x)]

def rowAmplitudeCoefficient (A b τ:ℝ) (n:ℕ):ℝ :=
  48*((dampingMomentConstant*errorMomentCoefficient A n*τ⁻¹)^2*2+
    (planeDampingCoefficient b*planeErrorCoefficient A b n*τ⁻¹)^2*
      ((1+Real.sqrt (b*logScale n))^2+1)+
    (4*planeDampingCoefficient b*tubeErrorCoefficient A b n)^2*
      ((τ⁻¹*(1+Real.sqrt (b*logScale n))+1)^2+(τ⁻¹)^2))

def residualAmplitudeCoefficient (b τ:ℝ) (n:ℕ):ℝ :=
  48*((dampingMomentConstant)^2+
    (planeDampingCoefficient b*Real.sqrt (2*Real.exp b))^2+
    (4*planeDampingCoefficient b*normalOUCoefficient τ (Real.sqrt (b*logScale n)))^2)

theorem amplitude_coefficients_nonneg (A b τ:ℝ) (n:ℕ) :
    0  ≤  rowAmplitudeCoefficient A b τ n ∧ 0  ≤  residualAmplitudeCoefficient b τ n := by
  dsimp [rowAmplitudeCoefficient,residualAmplitudeCoefficient]
  constructor   <;> positivity

/-- Square aggregation precedes any comparison over labels; there is no
cardinality factor in this bound for the literal defined amplitude. -/
theorem structuredAmplitude_sq_le (A b r τ:ℝ)
    (D:Fin (n+2)  →  FSC.Coord d) (h:Fin (n+2)  →  ℝ)
    (fD fu:Fin (n+2)  →  FSC.Coord d  →  ℝ) :
    (structuredAmplitude A b r τ D h fD fu)^2   ≤  
      rowAmplitudeCoefficient A b τ n*r^2*((∑i,‖D i‖^2)+(∑i,(h i)^2))+
      residualAmplitudeCoefficient b τ n/r^2*
        ((∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (fD i))^2)+
          (∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (fu i))^2)) := by
  let L:=logScale n
  let a:=dampingMomentConstant*errorMomentCoefficient A n*τ⁻¹
  let b₁:=planeDampingCoefficient b*planeErrorCoefficient A b n*τ⁻¹
  let c:=4*planeDampingCoefficient b*tubeErrorCoefficient A b n
  let s:=1+Real.sqrt (b*L)
  let C:=a^2*2+b₁^2*(s^2+1)+c^2*((τ⁻¹*s+1)^2+(τ⁻¹)^2)
  let Q:=(dampingMomentConstant)^2+(planeDampingCoefficient b*Real.sqrt (2*Real.exp b))^2+
    (4*planeDampingCoefficient b*normalOUCoefficient τ (Real.sqrt (b*L)))^2
  have hp i : (fullLabelMajorant A r τ D h fD fu i)^2+
      (forcingLabelMajorant A b r τ D h fD fu i)^2+
      (uniformTubeMajorant A b r τ D h fD fu i)^2   ≤  
      4*C*r^2*(‖D i‖^2+(h i)^2)+4*Q/r^2*
        ((realLp (stdGaussian (FSC.Coord d)) 2 (fD i))^2+
          (realLp (stdGaussian (FSC.Coord d)) 2 (fu i))^2) := by
    have h₁:=linear_four_square (a*r) (a*r) (dampingMomentConstant/r)
      ‖D i‖ |h i| (realLp (stdGaussian (FSC.Coord d)) 2 (fD i))
      (realLp (stdGaussian (FSC.Coord d)) 2 (fu i))
    have h₂:=linear_four_square (b₁*r*s) (b₁*r) (planeDampingCoefficient b*Real.sqrt (2*Real.exp b)/r)
      ‖D i‖ |h i| (realLp (stdGaussian (FSC.Coord d)) 2 (fD i))
      (realLp (stdGaussian (FSC.Coord d)) 2 (fu i))
    have h₃:=linear_four_square (c*r*(τ⁻¹*s+1)) (c*r*τ⁻¹)
      (4*planeDampingCoefficient b*normalOUCoefficient τ (Real.sqrt (b*L))/r)
      ‖D i‖ |h i| (realLp (stdGaussian (FSC.Coord d)) 2 (fD i))
      (realLp (stdGaussian (FSC.Coord d)) 2 (fu i))
    convert add_le_add (add_le_add h₁ h₂) h₃ using 1   <;>
      dsimp [fullLabelMajorant,forcingLabelMajorant,uniformTubeMajorant,a,b₁,c,s,C,Q,L]   <;>
      simp only [sq_abs]   <;> ring
  have hs:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hp i)
  have hx:0  ≤  ∑i,(fullLabelMajorant A r τ D h fD fu i)^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
  have hy:0  ≤  ∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
  have hz:0  ≤  ∑i,(uniformTubeMajorant A b r τ D h fD fu i)^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
  have htri (x y z:ℝ):(2*(x+y+z))^2  ≤  12*(x^2+y^2+z^2):=by
    nlinarith [sq_nonneg (x-y),sq_nonneg (x-z),sq_nonneg (y-z)]
  have ht:=htri (Real.sqrt (∑i,(fullLabelMajorant A r τ D h fD fu i)^2))
    (Real.sqrt (∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2))
    (Real.sqrt (∑i,(uniformTubeMajorant A b r τ D h fD fu i)^2))
  rw [Real.sq_sqrt hx,Real.sq_sqrt hy,Real.sq_sqrt hz] at ht
  change (structuredAmplitude A b r τ D h fD fu)^2  ≤  _ at ht
  apply ht.trans
  convert mul_le_mul_of_nonneg_left hs (show (0:ℝ)  ≤  12 by norm_num) using 1   <;>
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  dsimp [rowAmplitudeCoefficient,residualAmplitudeCoefficient,C,Q,a,b₁,c,s,L]
  ring

def errorBase (A:ℝ):ℝ := momentConstant (4*A)*Real.exp 1
def planeErrorBase (A b:ℝ):ℝ := momentConstant (4*A)*Real.exp (1+b/4)
def tubeErrorBase (A b:ℝ):ℝ :=
  NegativeVotingSmoothErrorTube.tubeConstant (4*A)*Real.exp (1+(2*b+2)/4)
def rowAmplitudeBase (A b T:ℝ):ℝ :=
  48*(2*(dampingMomentConstant*errorBase A)^2*T+
    (planeDampingCoefficient b*planeErrorBase A b)^2*T*(3+2*b)+
    (4*planeDampingCoefficient b*tubeErrorBase A b)^2*(T*(5+4*b)+2))
def residualAmplitudeBase (b:ℝ):ℝ :=
  48*((dampingMomentConstant)^2+(planeDampingCoefficient b)^2*(2*Real.exp b)+
    (4*planeDampingCoefficient b)^2*(8*Real.exp (2*b+2)*(b+2)))

theorem normalOUCoefficient_sq_le (τ b:ℝ) (hb:0  ≤  b)
    (hτ2:τ^2  ≤  1/2) (hrel:τ^2*logScale n  ≤  1/8192) :
    (normalOUCoefficient τ (Real.sqrt (b*logScale n)))^2  ≤  8*Real.exp (2*b+2)*(b+2) := by
  let L:=logScale n
  let a:=Real.sqrt (b*L)+1
  let B:=2*b+2
  have hL:1  ≤  L:=logScale_one_le n
  have hB:0  ≤  B:=by dsimp [B];positivity
  have ha:a^2  ≤  B*L:=by
    have hs:=Real.sq_sqrt (show 0  ≤  b*L by positivity)
    have hh:=add_sq_le (a:=Real.sqrt (b*L)) (b:=1)
    dsimp [a,B]
    nlinarith
  have hrow:=normalRowSquare_le_scaled τ a B L hB hτ2 hrel ha
  have h4:τ^4  ≤  1/4:=by nlinarith [sq_nonneg (τ^2-1/2)]
  have hfirst:τ^2/(1-τ^4)  ≤  1:=by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hA:τ^2*a^2  ≤  B/8192:=by
    have h₁:=mul_le_mul_of_nonneg_left ha (sq_nonneg τ)
    have h₂:=mul_le_mul_of_nonneg_left hrel hB
    nlinarith only [h₁,h₂]
  have hA':τ^4*a^2  ≤  B:=by
    have hh:=mul_le_mul_of_nonneg_left hA (sq_nonneg τ)
    have hsmall:τ^2*(B/8192)  ≤  B:=by nlinarith [mul_nonneg hB (sq_nonneg τ)]
    nlinarith only [hh,hsmall]
  have hsecond:τ^4*a^2/(1+τ^2)^2  ≤  B:=by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh:1  ≤  (1+τ^2)^2:=by nlinarith [sq_nonneg τ]
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hh)]
  have hrow0:0  ≤  normalRowSquare τ a:=by unfold normalRowSquare;positivity
  have hden:0  <  1-τ^4:=by linarith
  have hfactor0:0  ≤  τ^2/(1-τ^4)+τ^4*a^2/(1+τ^2)^2:=by positivity
  have hderiv:normalDerivativeRowSquare τ a  ≤  2*Real.exp B*(1+B):=by
    exact mul_le_mul hrow (add_le_add hfirst hsecond) hfactor0 (by positivity)
  have hd0:0  ≤  normalDerivativeRowSquare τ a:=mul_nonneg hrow0 hfactor0
  have hh:=add_sq_le (a:=Real.sqrt (normalRowSquare τ a))
    (b:=Real.sqrt (normalDerivativeRowSquare τ a))
  rw [Real.sq_sqrt hrow0,Real.sq_sqrt hd0] at hh
  have heq:normalOUCoefficient τ (Real.sqrt (b*logScale n))=
      Real.sqrt (normalRowSquare τ a)+Real.sqrt (normalDerivativeRowSquare τ a):=by
    simp only [normalOUCoefficient,abs_of_nonneg (Real.sqrt_nonneg _)];rfl
  rw [heq]
  dsimp only [B] at hrow hderiv
  nlinarith only [hh,hrow,hderiv]

theorem amplitude_coefficients_log_le (A b T τ:ℝ) (hb:0  ≤  b) (hT:0  ≤  T)
    (hinv:(τ⁻¹)^2  ≤  T*logScale n) (hτ2:τ^2  ≤  1/2) (hrel:τ^2*logScale n  ≤  1/8192) :
    rowAmplitudeCoefficient A b τ n  ≤  rowAmplitudeBase A b T*(logScale n)^5 ∧
      residualAmplitudeCoefficient b τ n  ≤  residualAmplitudeBase b := by
  let L:=logScale n
  have hL:1  ≤  L:=logScale_one_le n
  have hL0:0  ≤  L:=by linarith
  have hLpow:L^4  ≤  L^5:=pow_le_pow_right₀ hL (by omega)
  have he:(errorMomentCoefficient A n)^2=(errorBase A)^2*L^3:=by
    dsimp [errorMomentCoefficient,errorBase,L]
    simp only [mul_pow,Real.sq_sqrt (show 0  ≤  logScale n by linarith [logScale_one_le n])]
    ring
  have hp:(planeErrorCoefficient A b n)^2=(planeErrorBase A b)^2*L^3:=by
    dsimp [planeErrorCoefficient,planeErrorBase,L]
    simp only [mul_pow,Real.sq_sqrt (show 0  ≤  logScale n by linarith [logScale_one_le n])]
    ring
  have ht:(tubeErrorCoefficient A b n)^2=(tubeErrorBase A b)^2*L^3:=by
    dsimp [tubeErrorCoefficient,tubeErrorBase,L]
    simp only [mul_pow,Real.sq_sqrt (show 0  ≤  logScale n by linarith [logScale_one_le n])]
    ring
  have hs:(1+Real.sqrt (b*L))^2  ≤  (2+2*b)*L:=by
    have hh:=add_sq_le (a:=1) (b:=Real.sqrt (b*L))
    rw [Real.sq_sqrt (show 0  ≤  b*L by positivity)] at hh
    nlinarith
  have hs':(1+Real.sqrt (b*L))^2+1  ≤  (3+2*b)*L:=by linarith
  have hu:(τ⁻¹*(1+Real.sqrt (b*L))+1)^2+(τ⁻¹)^2  ≤  (T*(5+4*b)+2)*L^2:=by
    have hh:=add_sq_le (a:=τ⁻¹*(1+Real.sqrt (b*L))) (b:=1)
    have hm:=mul_le_mul hinv hs (sq_nonneg _) (by positivity : 0  ≤  T*L)
    have hl2:L  ≤  L^2:=by nlinarith
    have hi: (τ⁻¹)^2  ≤  T*L^2:=hinv.trans (mul_le_mul_of_nonneg_left hl2 hT)
    have h12:1  ≤  L^2:=one_le_pow₀ hL
    nlinarith only [hh,hm,hi,h12]
  constructor
  · unfold rowAmplitudeCoefficient rowAmplitudeBase
    simp only [mul_pow,he,hp,ht]
    have h₁:(dampingMomentConstant)^2*((errorBase A)^2*L^3)*(τ⁻¹)^2*2  ≤  
        2*(dampingMomentConstant*errorBase A)^2*T*L^5:=by
      calc
        _  ≤  (dampingMomentConstant)^2*((errorBase A)^2*L^3)*(T*L)*2:=by gcongr
        _=2*(dampingMomentConstant*errorBase A)^2*T*L^4:=by ring
        _  ≤  _:=mul_le_mul_of_nonneg_left hLpow (by positivity)
    have h₂:(planeDampingCoefficient b)^2*((planeErrorBase A b)^2*L^3)*(τ⁻¹)^2*
          ((1+Real.sqrt (b*L))^2+1)  ≤  (planeDampingCoefficient b*planeErrorBase A b)^2*T*(3+2*b)*L^5:=by
      calc
        _  ≤  (planeDampingCoefficient b)^2*((planeErrorBase A b)^2*L^3)*(T*L)*((3+2*b)*L):=by gcongr
        _=_:=by ring
    have h₃:4^2*(planeDampingCoefficient b)^2*((tubeErrorBase A b)^2*L^3)*
          ((τ⁻¹*(1+Real.sqrt (b*L))+1)^2+(τ⁻¹)^2)  ≤  
          (4*planeDampingCoefficient b*tubeErrorBase A b)^2*(T*(5+4*b)+2)*L^5:=by
      calc
        _  ≤  4^2*(planeDampingCoefficient b)^2*((tubeErrorBase A b)^2*L^3)*((T*(5+4*b)+2)*L^2):=by gcongr
        _=_:=by ring
    nlinarith only [h₁,h₂,h₃]
  · have hnormal:=normalOUCoefficient_sq_le (n:=n) τ b hb hτ2 hrel
    unfold residualAmplitudeCoefficient residualAmplitudeBase
    simp only [mul_pow,Real.sq_sqrt (show 0  ≤  2*Real.exp b by positivity)]
    gcongr

def massGapBase (e U:ℝ):ℝ := 2048*Real.pi^2*massDegree e*U^2
def offsetAmplitudeBase (e U:ℝ):ℝ := 1+2*offsetBase e U+2*(massGapBase e U)^2
def amplitudeLogConstant (A b T e U:ℝ):ℝ :=
  rowAmplitudeBase A b T*offsetAmplitudeBase e U+
  residualAmplitudeBase b*sourceCoefficient e U*T^4+residualAmplitudeBase b*T^3

theorem amplitude_bases_nonneg (A b T e U:ℝ) (hb:0  ≤  b) (hT:0  ≤  T) (he:0  <  e) :
    0  ≤  rowAmplitudeBase A b T ∧ 0  ≤  residualAmplitudeBase b ∧
      0  ≤  offsetAmplitudeBase e U ∧ 0  ≤  amplitudeLogConstant A b T e U := by
  have ho:= (base_nonneg e U 0 he le_rfl).2.2.1
  have hs:=sourceCoefficient_nonneg e U he
  have hrow:0  ≤  rowAmplitudeBase A b T:=by unfold rowAmplitudeBase;positivity
  have hres:0  ≤  residualAmplitudeBase b:=by unfold residualAmplitudeBase;positivity
  have hoff:0  ≤  offsetAmplitudeBase e U:=by unfold offsetAmplitudeBase;positivity
  exact ⟨hrow,hres,hoff,by unfold amplitudeLogConstant;positivity⟩

theorem selected_offset_polylog (hn:1  ≤  n) (R D:Fin (n+2)  →  FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α e U:ℝ) (hα:0  <  α) (he:0  <  e) (hU:0  ≤  U)
    (hD:∑i,‖D i‖^2  ≤  α^2/256)
    (hlower:e*Real.sqrt (logScale n)/((n+2:ℕ):ℝ)  ≤  α/2)
    (hupper:α  ≤  U*Real.sqrt (logScale n)/((n+2:ℕ):ℝ))
    (v:centeredGauge (Fin (n+2))) (hv:∀ i,|(v:Fin (n+2)  →  ℝ) i|  ≤  1/(2*((n+2:ℕ):ℝ))) :
    (∑i,‖D i‖^2)+(∑i,((selectedOffsets (α•R+D)
      ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)  →  ℝ)):Fin (n+2)  →  ℝ) i)^2)   ≤  
      offsetAmplitudeBase e U*(logScale n)^5*
        ((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)  →  ℝ) i)^2)) := by
  let L:=logScale n
  have hL:1  ≤  L:=logScale_one_le n
  have hlow:e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)  ≤  α/2:=by
    simpa only [logScale,Nat.cast_add,Nat.cast_ofNat] using hlower
  have hu:α  ≤  U*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ):=by
    simpa only [logScale,Nat.cast_add,Nat.cast_ofNat] using hupper
  have hh:=near_balanced_selected_offset_sq_le (by omega) R D hG α hα hD e he hlow v hv
  have hgap: (nearGap (n+2) α e)⁻¹  ≤  gapBase e U*L:=by
    simpa only [gapBase,L,logScale,Nat.cast_add,Nat.cast_ofNat] using
      nearGap_inv_le α e U hα he hU (by omega) hu
  have hmass:(massGap (n+2) α e)⁻¹  ≤   massGapBase e U*L:=by
    simpa only [massGapBase,L,logScale,Nat.cast_add,Nat.cast_ofNat] using
      massGap_inv_le α e U hα he hU (by omega) hu
  have hm0:0  ≤  (massGap (n+2) α e)⁻¹:=by
    rw [massGap_inv α e hα he]
    positivity [massDegree_pos e he]
  have ho:offsetCoefficient (n+2) α e  ≤  offsetBase e U*L^5:=by
    calc
      _=(4*traceBase e*L^4)*(nearGap (n+2) α e)⁻¹:=by
        dsimp [offsetCoefficient,traceBase,L,logScale]
        simp only [Nat.cast_add,Nat.cast_ofNat]
        ring
      _  ≤  (4*traceBase e*L^4)*(gapBase e U*L):=mul_le_mul_of_nonneg_left hgap
        (by unfold traceBase quarticLogConstant;positivity [degreeBound_pos e he])
      _=offsetBase e U*L^5:=by unfold offsetBase;ring
  have hm2:=pow_le_pow_left₀ hm0 hmass 2
  have h25:L^2  ≤  L^5:=pow_le_pow_right₀ hL (by omega)
  have hm5:(massGap (n+2) α e)⁻¹^2  ≤  (massGapBase e U)^2*L^5:=by
    rw [mul_pow] at hm2
    exact hm2.trans (mul_le_mul_of_nonneg_left h25 (sq_nonneg _))
  have hF:0  ≤  ∑i,‖D i‖^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
  have hZ:0  ≤  ∑i,((v:Fin (n+2)  →  ℝ) i)^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
  have hO0:0  ≤  offsetBase e U:=(base_nonneg e U 0 he le_rfl).2.2.1
  have h15:1  ≤  L^5:=one_le_pow₀ hL
  have hF':(∑i,‖D i‖^2)  ≤  L^5*(∑i,‖D i‖^2):=by nlinarith only [mul_nonneg hF (sub_nonneg.mpr h15)]
  have h₁:=mul_le_mul_of_nonneg_right ho (mul_nonneg (show (0:ℝ)  ≤  2 by norm_num) hF)
  have h₂:=mul_le_mul_of_nonneg_right hm5 (mul_nonneg (show (0:ℝ)  ≤  2 by norm_num) hZ)
  dsimp only [offsetAmplitudeBase]
  nlinarith [mul_nonneg hZ (show 0  ≤  L^5 by positivity),
    mul_nonneg (mul_nonneg hO0 (show 0  ≤  L^5 by positivity)) hZ,
    mul_nonneg (mul_nonneg (sq_nonneg (massGapBase e U)) (show 0  ≤  L^5 by positivity)) hF]

/-- The actual source inputs and selected offsets give a fixed polylogarithmic
bound for the literal amplitude. No desired forcing norm is a premise. -/
theorem near_balanced_amplitude_sq_le (hn:1  ≤  n) (R D:Fin (n+2)  →  FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α e U:ℝ) (hα:0  <  α) (he:0  <  e) (hU:0  ≤  U)
    (hD:∑i,‖D i‖^2  ≤  α^2/256)
    (hlower:e*Real.sqrt (logScale n)/((n+2:ℕ):ℝ)  ≤  α/2)
    (hupper:α  ≤  U*Real.sqrt (logScale n)/((n+2:ℕ):ℝ))
    (v:centeredGauge (Fin (n+2))) (hv:∀ i,|(v:Fin (n+2)  →  ℝ) i|  ≤  1/(2*((n+2:ℕ):ℝ)))
    (A b T r τ χ q:ℝ) (hb:0  ≤  b) (hT:0  ≤  T) (hτ:0  <  τ) (hχ:0  <  χ) (hχ1:χ  <  1)
    (hr:r=(τ*χ)^2) (hq:2  ≤  q) (ht:τ^2=1/(2*q-1))
    (hqlog:Real.log (((n+2:ℕ):ℝ)/(α/2))  ≤  q)
    (hinv:(τ⁻¹)^2  ≤  T*logScale n) (hτ2:τ^2  ≤  1/2) (hrel:τ^2*logScale n  ≤  1/8192)
    (u:Fin (n+2)  →  FSC.Coord d  →  ℝ) (huM:∀ i,Measurable (u i))
    (hu:∀ i,MemLp (u i) 2 (stdGaussian (FSC.Coord d)))
    (hu3:∀ i a,degree a  <  3  →  coeff (fun x:Fin d  →  ℝ=>u i (WithLp.toLp 2 x)) a=0) :
    (structuredAmplitude A b r τ D
      (selectedOffsets (α•R+D) ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)  →  ℝ)))
      (cellSource τ χ (α•R,selectedOffsets (α•R) (fun _=>((n+2:ℕ):ℝ)⁻¹))
        (α•R+D,selectedOffsets (α•R+D) ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)  →  ℝ))))
      (fun i=>highSource χ (u i)))^2   ≤  
      amplitudeLogConstant A b T e U*(logScale n)^10*
        (r^2*((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)  →  ℝ) i)^2))+
          r*(∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (u i))^2)) := by
  let L:=logScale n
  let F:ℝ:=(∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)  →  ℝ) i)^2)
  let W:ℝ:=∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (u i))^2
  have hL:1  ≤  L:=logScale_one_le n
  have hF:0  ≤  F:=by dsimp [F];positivity
  have hW:0  ≤  W:=by dsimp [W];positivity
  have hr0:0  <  r:=by rw [hr];positivity
  have hlow:e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)  ≤  α/2:=by
    simpa only [logScale,Nat.cast_add,Nat.cast_ofNat] using hlower
  have hupp:α  ≤  U*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ):=by
    simpa only [logScale,Nat.cast_add,Nat.cast_ofNat] using hupper
  have hsrc:=near_balanced_cellSource_polylog (by omega) R D hG α hα hD e U he hU
    hlow hupp v hv τ χ q hτ hχ hχ1 hq ht hqlog
  have hoff:=selected_offset_polylog hn R D hG α e U hα he hU hD hlower hupper v hv
  have hhi:=(highSource_sum_norm_sq_le χ hχ hχ1 u huM hu hu3).2
  have hcoeff:=amplitude_coefficients_log_le A b T τ hb hT hinv hτ2 hrel
  rcases amplitude_bases_nonneg A b T e U hb hT he with ⟨hrow0,hres0,hoff0,hlog0⟩
  have hs0:=sourceCoefficient_nonneg e U he
  have hchi8:χ^8/r^2=r^2*(τ⁻¹)^8:=by rw [hr];field_simp
  have hchi6:χ^6/r^2=r*(τ⁻¹)^6:=by rw [hr];field_simp
  have hinv8:(τ⁻¹)^8  ≤  T^4*L^4:=by
    have hh:=pow_le_pow_left₀ (sq_nonneg τ⁻¹) hinv 4
    simpa only [←pow_mul,mul_pow] using hh
  have hinv6:(τ⁻¹)^6  ≤  T^3*L^3:=by
    have hh:=pow_le_pow_left₀ (sq_nonneg τ⁻¹) hinv 3
    simpa only [←pow_mul,mul_pow] using hh
  have hh:=structuredAmplitude_sq_le A b r τ D
    (selectedOffsets (α•R+D) ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)  →  ℝ)))
    (cellSource τ χ (α•R,selectedOffsets (α•R) (fun _=>((n+2:ℕ):ℝ)⁻¹))
      (α•R+D,selectedOffsets (α•R+D) ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)  →  ℝ))))
    (fun i=>highSource χ (u i))
  simp only [Nat.cast_add,Nat.cast_ofNat] at hsrc
  change _  ≤   sourceCoefficient e U*L^4*χ^8*F at hsrc
  apply hh.trans
  calc
    _  ≤  (rowAmplitudeBase A b T*L^5)*r^2*(offsetAmplitudeBase e U*L^5*F)+
        residualAmplitudeBase b/r^2*(sourceCoefficient e U*L^4*χ^8*F+χ^6*W):=by
      gcongr   <;> first | positivity | exact hcoeff.1 | exact hoff | exact hcoeff.2 | simpa only [Nat.cast_add,Nat.cast_ofNat] using hsrc
    _=rowAmplitudeBase A b T*offsetAmplitudeBase e U*L^10*r^2*F+
        residualAmplitudeBase b*sourceCoefficient e U*L^4*(χ^8/r^2)*F+
        residualAmplitudeBase b*(χ^6/r^2)*W:=by ring
    _  ≤  rowAmplitudeBase A b T*offsetAmplitudeBase e U*L^10*r^2*F+
        residualAmplitudeBase b*sourceCoefficient e U*T^4*L^8*r^2*F+
        residualAmplitudeBase b*T^3*L^3*r*W:=by
      rw [hchi8,hchi6]
      have h₁:=mul_le_mul_of_nonneg_left hinv8
        (show 0  ≤  residualAmplitudeBase b*sourceCoefficient e U*L^4*r^2*F by positivity)
      have h₂:=mul_le_mul_of_nonneg_left hinv6
        (show 0  ≤  residualAmplitudeBase b*r*W by positivity)
      nlinarith only [h₁,h₂]
    _  ≤  amplitudeLogConstant A b T e U*L^10*(r^2*F+r*W):=by
      have h8:L^8  ≤  L^10:=pow_le_pow_right₀ hL (by omega)
      have h3:L^3  ≤  L^10:=pow_le_pow_right₀ hL (by omega)
      have h₁:=mul_le_mul_of_nonneg_left h8
        (show 0  ≤  residualAmplitudeBase b*sourceCoefficient e U*T^4*r^2*F by positivity)
      have h₂:=mul_le_mul_of_nonneg_left h3
        (show 0  ≤  residualAmplitudeBase b*T^3*r*W by positivity)
      unfold amplitudeLogConstant
      nlinarith [mul_nonneg (show 0  ≤  rowAmplitudeBase A b T*offsetAmplitudeBase e U*L^10 by positivity)
          (mul_nonneg hr0.le hW),
        mul_nonneg (show 0  ≤  residualAmplitudeBase b*sourceCoefficient e U*T^4*L^10 by positivity)
          (mul_nonneg hr0.le hW),
        mul_nonneg (show 0  ≤  residualAmplitudeBase b*T^3*L^10 by positivity)
          (mul_nonneg (sq_nonneg r) hF)]

/-- A scalar ceiling threshold, before any ambient dimension. The source
energy assumption here is discharged for the literal fractional residual in
the endpoint below. -/
theorem exists_amplitude_ceiling_threshold (K B:ℝ) (hK:0  ≤  K) (_hB:0  ≤  B) :
    ∃ N:ℕ, ∀ n :ℕ,N  ≤  n  →  ∀ θ r F W:ℝ,
      0  ≤  r  →  r  ≤  2/((n+2:ℕ):ℝ)  →  0  ≤  F  →  F  ≤  B/((n+2:ℕ):ℝ)  →  0  ≤  W  →  W  ≤  2*r^3  →  
      θ^2  ≤  K*(logScale n)^10*(r^2*F+r*W)  →  θ  ≤  ((n+2:ℕ):ℝ)^(-(5/4):ℝ) := by
  have hlim:=((tendsto_const_nhds: Tendsto (fun _:ℕ=>K*(4*B+32)) atTop (𝓝 (K*(4*B+32)))).mul
    ((NegativeVoting.logarithmic_remainder_tendsto_zero (10:ℕ) (1/2) (by norm_num) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun m:ℕ=>(m:ℝ)) atTop atTop)))
  simp only [mul_zero] at hlim
  have hl:=hlim.eventually (gt_mem_nhds (show (0:ℝ)  <  1 by norm_num))
  obtain ⟨N,hN⟩:=Filter.eventually_atTop.mp hl
  refine ⟨N,?_⟩
  intro n hn θ r F W hr hrange hF hFbound hW hWbound hθ
  let m:ℝ:=(n+2:ℕ)
  have hm:1  ≤  m:=by dsimp [m];exact_mod_cast (show 1  ≤  n+2 by omega)
  have hm0:0  <  m:=by linarith
  have hrate:=hN (n+2) (by omega)
  simp only [Function.comp_def,Real.rpow_natCast] at hrate
  have hrate':K*(4*B+32)*(logScale n)^10  ≤  m^(1/2:ℝ):=by
    have hh:(K*(4*B+32)*(logScale n)^10)/(m^(1/2:ℝ))  ≤  1:=by
      convert hrate.le using 1; simp only [logScale,m,Nat.cast_add,Nat.cast_ofNat]; ring
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hm0 _)).mp hh |>.trans_eq (one_mul _)
  have hbudget:r^2*F+r*W  ≤  (4*B+32)/m^3:=by
    have hw':W  ≤  2*(2/m)^3:=hWbound.trans (by gcongr)
    calc
      _  ≤  (2/m)^2*(B/m)+(2/m)*(2*(2/m)^3):=by gcongr
      _=4*B/m^3+32/m^4:=by ring
      _  ≤  4*B/m^3+32/m^3:=by
        gcongr
        norm_num
      _=(4*B+32)/m^3:=by ring
  have htheta:θ^2  ≤  (m^(-(5/4):ℝ))^2:=by
    calc
      _  ≤  K*(logScale n)^10*((4*B+32)/m^3):=hθ.trans
        (mul_le_mul_of_nonneg_left hbudget (by positivity))
      _=(K*(4*B+32)*(logScale n)^10)/m^3:=by ring
      _  ≤  m^(1/2:ℝ)/m^3:=div_le_div_of_nonneg_right hrate' (by positivity)
      _=(m^(-(5/4):ℝ))^2:=by
        rw [←Real.rpow_natCast m 3,←Real.rpow_sub hm0,←Real.rpow_natCast (m^(-(5/4):ℝ)) 2,
          ←Real.rpow_mul hm0.le]
        norm_num
  exact le_of_sq_le_sq htheta (Real.rpow_nonneg hm0.le _)

def actualAmplitude (A b r τ χ α:ℝ) (R D:Fin (n+2)  →  FSC.Coord d)
    (v:centeredGauge (Fin (n+2))) (u:Fin (n+2)  →  FSC.Coord d  →  ℝ):ℝ :=
  structuredAmplitude A b r τ D
    (selectedOffsets (α•R+D) ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)  →  ℝ)))
    (cellSource τ χ (α•R,selectedOffsets (α•R) (fun _=>((n+2:ℕ):ℝ)⁻¹))
      (α•R+D,selectedOffsets (α•R+D) ((fun _=>((n+2:ℕ):ℝ)⁻¹)+(v:Fin (n+2)  →  ℝ))))
    (fun i=>highSource χ (u i))

/-- The threshold is chosen before ambient dimension, all selected rows,
and fractional assignments. The residual is the literal smoothed odd
high-mode projection; its cubic energy decay is proved, not assumed. -/
theorem exists_dimension_uniform_actual_amplitude_ceiling
    (A b T e U B:ℝ) (hb:0  ≤  b) (hT:0  ≤  T) (he:0  <  e) (hU:0  ≤  U) (hB:0  ≤  B) :
    ∃N:ℕ,∀ n :ℕ,N  ≤  n  →  ∀ d :ℕ,∀R D:Fin (n+2)  →  FSC.Coord d,
      (∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))  →  
      ∀ α :ℝ,0  <  α  →  (∑i,‖D i‖^2)  ≤  α^2/256  →  
      e*Real.sqrt (logScale n)/((n+2:ℕ):ℝ)  ≤  α/2  →  
      α  ≤  U*Real.sqrt (logScale n)/((n+2:ℕ):ℝ)  →  
      ∀ v :centeredGauge (Fin (n+2)),(∀ i,|(v:Fin (n+2)  →  ℝ) i|  ≤  1/(2*((n+2:ℕ):ℝ)))  →  
      (∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)  →  ℝ) i)^2)  ≤  B/((n+2:ℕ):ℝ)  →  
      ∀ r τ χ q:ℝ,0  <  r  →  r  <  1  →  r  ≤  2/((n+2:ℕ):ℝ)  →  0  <  τ  →  0  <  χ  →  χ  <  1  →  r=(τ*χ)^2  →  
      2  ≤  q  →  τ^2=1/(2*q-1)  →  Real.log (((n+2:ℕ):ℝ)/(α/2))  ≤  q  →  
      (τ⁻¹)^2  ≤  T*logScale n  →  τ^2  ≤  1/2  →  τ^2*logScale n  ≤  1/8192  →  
      ∀ f g:Fin (n+2)  →  FSC.Coord d  →  ℝ,
      (∀ i,Measurable (f i))  →  (∀ i,Measurable (g i))  →  
      (∀ᵐ x ∂stdGaussian (FSC.Coord d),(∀ i,0  ≤  f i x ∧ f i x  ≤  1) ∧ ∑i,f i x=1)  →  
      (∀ᵐ x ∂stdGaussian (FSC.Coord d),(∀ i,0  ≤  g i x ∧ g i x  ≤  1) ∧ ∑i,g i x=1)  →  
      actualAmplitude A b r τ χ α R D v
        (fun i=>projectedOddResidual (Real.sqrt r) (f i-g i))  ≤  ((n+2:ℕ):ℝ)^(-(5/4):ℝ) := by
  have hK:0  ≤  amplitudeLogConstant A b T e U:=(amplitude_bases_nonneg A b T e U hb hT he).2.2.2
  obtain ⟨N,hN⟩:=exists_amplitude_ceiling_threshold (amplitudeLogConstant A b T e U) B hK hB
  refine ⟨max N 1,?_⟩
  intro n hn d R D hG α hα hD hlower hupper v hv hsize r τ χ q hr hr1 hrange
    hτ hχ hχ1 hrEq hq ht hqlog hinv hτ2 hrel f g hfm hgm hf hg
  have hn1:1  ≤  n:=(le_max_right N 1).trans hn
  have hs:0  <  Real.sqrt r:=Real.sqrt_pos.mpr hr
  have hs1:Real.sqrt r  <  1:=by nlinarith [Real.sq_sqrt hr.le]
  have hu:=fractional_projectedOddResidual_sum_norm_sq_le (Real.sqrt r) hs hs1 f g hfm hgm hf hg
  have huM i:=projectedOddResidual_measurable (Real.sqrt r) (f i-g i) ((hfm i).sub (hgm i))
  have hh:=near_balanced_amplitude_sq_le hn1 R D hG α e U hα he hU hD hlower hupper v hv
    A b T r τ χ q hb hT hτ hχ hχ1 hrEq hq ht hqlog hinv hτ2 hrel
    (fun i=>projectedOddResidual (Real.sqrt r) (f i-g i)) huM hu.1 hu.2.1
  have hUbound:(∑i,(realLp (stdGaussian (FSC.Coord d)) 2
      (projectedOddResidual (Real.sqrt r) (f i-g i)))^2)  ≤  2*r^3:=by
    convert hu.2.2 using 1
    rw [show (Real.sqrt r)^6=((Real.sqrt r)^2)^3 by ring,Real.sq_sqrt hr.le]
  exact hN n ((le_max_left N 1).trans hn) _ r _ _ hr.le hrange
    (by positivity) hsize (by positivity) hUbound hh

/-- The standard common smoothing scale supplies all scalar prerequisites of
the amplitude bound. Only the scale lower bound for the actual regular rows
enters the eventual logarithmic condition. -/
theorem exists_common_smoothing_threshold (A e:ℝ) (hA:8192  ≤  A) (he:0 < e) :
    ∃ N:ℕ,∀ n:ℕ,N  ≤  n  →  ∀ α τ:ℝ,0 < α  → 
      e*Real.sqrt (logScale n)/((n+2:ℕ):ℝ)  ≤  α/2  → 
      τ^2=1/(4*A*logScale n-1)  → 
      Real.log (((n+2:ℕ):ℝ)/(α/2))  ≤  2*A*logScale n ∧
      (τ⁻¹)^2  ≤  (4*A)*logScale n ∧ τ^2  ≤  1/2 ∧
      τ^2*logScale n  ≤  1/8192 ∧ 4*(A*logScale n)  ≤  1+(τ^2)⁻¹ ∧
      2  ≤  2*A*logScale n := by
  have hloglim:=Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m:ℕ=>(m:ℝ)) atTop atTop)
  obtain ⟨N,hN⟩:=Filter.eventually_atTop.mp (hloglim.eventually_ge_atTop |Real.log e|)
  refine ⟨N,?_⟩
  intro n hn α τ hα hlower ht
  let m:ℝ:=(n+2:ℕ)
  let L:=logScale n
  have hm:1  ≤  m:=by dsimp [m];exact_mod_cast (show 1 ≤ n+2 by omega)
  have hm0:0 < m:=by linarith
  have hL:1 ≤ L:=logScale_one_le n
  have hL0:0 ≤ L:=by linarith
  have hAm:8192*L ≤ A*L:=mul_le_mul_of_nonneg_right hA hL0
  have hden:0 < 4*A*L-1:=by nlinarith
  have hi:(τ⁻¹)^2=4*A*L-1:=by rw [inv_pow,ht];simp [L]
  have hl:|Real.log e| ≤ Real.log m:=by
    simpa only [Function.comp_def,m] using hN (n+2) (by omega)
  have hsmall:e/m ≤ α/2:=by
    have hs:1 ≤ Real.sqrt L:=Real.le_sqrt_of_sq_le (by simpa using hL)
    have hh:e/m ≤ e*Real.sqrt L/m:=div_le_div_of_nonneg_right (by nlinarith) hm0.le
    exact hh.trans hlower
  have hratio:m/(α/2) ≤ m^2/e:=by
    calc
      _ ≤ m/(e/m):=div_le_div_of_nonneg_left hm0.le (div_pos he hm0) hsmall
      _=_:=by field_simp
  have hlog:Real.log (m/(α/2)) ≤ 2*Real.log m-Real.log e:=by
    have hh:=Real.log_le_log (div_pos hm0 (by linarith)) hratio
    rw [Real.log_div (pow_ne_zero _ hm0.ne') he.ne',Real.log_pow] at hh
    simpa using hh
  have hLid:L=1+Real.log m:=by simp only [L,m,logScale,Nat.cast_add,Nat.cast_ofNat]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · change Real.log (m/(α/2)) ≤ 2*A*L
    nlinarith [neg_le_abs (Real.log e)]
  · rw [hi]
    change 4*A*L-1 ≤ 4*A*L
    linarith
  · rw [ht]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  · rw [ht,one_div]
    change (4*A*L-1)⁻¹*L ≤ 1/8192
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  · rw [ht]
    simp only [one_div,inv_inv]
    ring_nf
    rfl
  · change 2 ≤ 2*A*L
    nlinarith

end NegativeVotingStructuredAmplitudeBound
