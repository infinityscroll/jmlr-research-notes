import GaussianNearBalancedHighTailComparison
import GaussianNearRegularEnergyLogBound

/-! Uniform logarithmic bookkeeping for the actual near-balanced full tail.
The inverse graph gaps and the rare-label factor are retained explicitly. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology
namespace NegativeVotingNearBalancedTailLogBound
open NegativeVotingNearBalancedHighTailComparison NegativeVotingNearBalancedSourceInputs
  NegativeVotingNearRegularNormalizedBounds NegativeVotingNearRegularGraphGap
  NegativeVotingNearRegularEnergyLogBound NegativeVotingNearRegularEnergyComparison
  NegativeVotingPolynomialFacetLogBound NegativeVotingFanRetained

def tailDegree : ℝ := degreeBound (1/4)
def tailMassDegree : ℝ := massDegree (1/4)
def tailGapBase : ℝ := 2048*Real.pi^2*tailMassDegree*100
def tailOffsetBase : ℝ := offsetBase (1/4) 10
def crossBase (b:ℝ) : ℝ := 1024*Real.exp 1*b*(1+quarticLogConstant 2)*Real.exp 2*Real.exp 1
def selfBase : ℝ :=
  64*Real.exp 1*max 1 tailDegree*tailDegree*quarticLogConstant 2+
  16*Real.exp 1*max 1 tailMassDegree*tailGapBase
def tailBase : ℝ :=
  2*(crossBase tailDegree*(1+tailOffsetBase)+
    crossBase tailMassDegree*(1+2*tailOffsetBase+2*tailGapBase^2))+selfBase
def tailLogConstant : ℝ := tailBase*8193^3

lemma base_pos : 0<tailDegree ∧ 0<tailMassDegree ∧ 0<tailGapBase ∧
    0<tailOffsetBase ∧ 0<selfBase ∧ 0<tailBase ∧ 0<tailLogConstant := by
  dsimp [tailDegree,tailMassDegree,tailGapBase,tailOffsetBase,selfBase,tailBase,
    tailLogConstant,crossBase,offsetBase,traceBase,gapBase,degreeBound,massDegree,
    quarticLogConstant]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> positivity

lemma massGap_inv (m:ℕ) (α:ℝ) :
    (massGap m α (1/4))⁻¹=2048*Real.pi^2*tailMassDegree*((m:ℝ)*α)^2 := by
  simp only [massGap,retainedGapCoefficient,tailMassDegree,div_eq_mul_inv,
    mul_inv_rev,inv_pow,inv_inv]
  ring_nf
  simp only [inv_inv]

lemma coefficient_log_bound (m:ℕ) [NeZero m] (α τ σ F Z:ℝ)
    (hm:1≤(m:ℝ)) (hα:0<α) (hτ:0≤τ) (hτ1:τ≤1) (hσ:0≤σ)
    (hF:0≤F) (hZ:0≤Z)
    (hlo:Real.sqrt (1+Real.log (m:ℝ))/(2*(m:ℝ))≤α)
    (hhi:α≤10*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)) :
    2*fullCrossBound m α τ σ (1/4) F Z+σ^3*selfCoefficient m α (1/4) F Z ≤
      tailBase*σ^3*(1+Real.log (m:ℝ))^7*(F+Z) := by
  let L:=1+Real.log (m:ℝ)
  have hm0:0<(m:ℝ):=by linarith
  have hL:1≤L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hL0:0≤L:=by linarith
  have hs:1≤Real.sqrt L:=(Real.le_sqrt (by norm_num) hL0).mpr (by simpa using hL)
  have hma:1/((m:ℝ)*α)≤2:=by
    have hb:1/(2*(m:ℝ))≤α:=(div_le_div_of_nonneg_right hs (by positivity)).trans hlo
    apply (div_le_iff₀ (by positivity)).mpr
    have hh:1≤α*(2*(m:ℝ)):=(div_le_iff₀ (by positivity)).mp hb
    nlinarith
  have hK:0≤quarticLogConstant 2:=by unfold quarticLogConstant;positivity
  have hroot:Real.sqrt (quarticLogConstant 2*L^4)≤(1+quarticLogConstant 2)*L^2:=by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hk:quarticLogConstant 2≤(1+quarticLogConstant 2)^2:=by nlinarith
    have hh:=mul_le_mul_of_nonneg_right hk (show 0≤L^4 by positivity)
    nlinarith only [hh]
  have hb:=base_pos
  have hD:0≤tailDegree:=hb.1.le
  have hB:0≤tailMassDegree:=hb.2.1.le
  have hG:0≤tailGapBase:=hb.2.2.1.le
  have hO:0≤tailOffsetBase:=hb.2.2.2.1.le
  have hgap:(massGap m α (1/4))⁻¹≤tailGapBase*L:=by
    rw [massGap_inv]
    have hx:(m:ℝ)*α≤10*Real.sqrt L:=by
      have hh:α*(m:ℝ)≤10*Real.sqrt L:=(le_div_iff₀ hm0).mp hhi
      nlinarith only [hh]
    have hx2:=pow_le_pow_left₀ (show 0≤(m:ℝ)*α by positivity) hx 2
    have hs2:=Real.sq_sqrt hL0
    have hh:=mul_le_mul_of_nonneg_left hx2 (show 0≤2048*Real.pi^2*tailMassDegree by positivity)
    dsimp only [tailGapBase]
    convert hh using 1 <;> ring_nf <;> rw [hs2]
  have hngap:0≤(massGap m α (1/4))⁻¹:=(inv_pos.mpr (massGap_pos α (1/4) hα (by norm_num))).le
  have hnear: (nearGap m α (1/4))⁻¹≤gapBase (1/4) 10*L :=
    nearGap_inv_le α (1/4) 10 hα (by norm_num) (by norm_num) (by exact_mod_cast hm) hhi
  have hoff:offsetCoefficient m α (1/4)≤tailOffsetBase*L^5:=by
    calc
      _=(4*traceBase (1/4)*L^4)*(nearGap m α (1/4))⁻¹:=by
        dsimp [offsetCoefficient,traceBase,L];ring
      _≤(4*traceBase (1/4)*L^4)*(gapBase (1/4) 10*L):=by
        apply mul_le_mul_of_nonneg_left hnear
        dsimp [traceBase];positivity [degreeBound_pos (1/4) (by norm_num)]
      _=tailOffsetBase*L^5:=by dsimp [tailOffsetBase,offsetBase];ring
  have hoff0:=offsetCoefficient_nonneg m α (1/4) hα (by norm_num)
  have hone:1+offsetCoefficient m α (1/4)≤(1+tailOffsetBase)*L^5:=one_add_bound hL hO hoff
  have henergy:massPathEnergy m α (1/4) F Z≤
      (1+2*tailOffsetBase+2*tailGapBase^2)*L^5*(F+Z):=by
    have hpow1:(1:ℝ)≤L^5:=one_le_pow₀ hL
    have hpow2:L^2≤L^5:=pow_le_pow_right₀ hL (by omega)
    have hg2:=pow_le_pow_left₀ hngap hgap 2
    have hgs:(massGap m α (1/4))⁻¹^2≤tailGapBase^2*L^5:=by
      calc
        _≤(tailGapBase*L)^2:=hg2
        _=tailGapBase^2*L^2:=by ring
        _≤tailGapBase^2*L^5:=mul_le_mul_of_nonneg_left hpow2 (sq_nonneg _)
    dsimp only [massPathEnergy]
    calc
      _≤(1+2*(tailOffsetBase*L^5))*F+2*(tailGapBase^2*L^5)*Z:=by gcongr
      _≤(1+2*tailOffsetBase+2*tailGapBase^2)*L^5*(F+Z):=by
        nlinarith [mul_nonneg (show 0≤(1+2*tailOffsetBase)*L^5 by positivity) hZ,
          mul_nonneg (show 0≤2*tailGapBase^2*L^5 by positivity) hF,
          mul_le_mul_of_nonneg_right hpow1 hF]
  have cross (b:ℝ) (hb:0≤b) :
      32*Real.exp 1*b*Real.sqrt (quarticLogConstant 2*L^4)*
        ((8*τ*Real.exp 2)*(2*σ^3*(Real.exp 1/(m:ℝ)))/α)≤crossBase b*σ^3*L^2:=by
    calc
      _=(512*Real.exp 1*b*Real.sqrt (quarticLogConstant 2*L^4)*
        τ*Real.exp 2*σ^3*Real.exp 1)*(1/((m:ℝ)*α)):=by ring
      _≤(512*Real.exp 1*b*((1+quarticLogConstant 2)*L^2)*
        1*Real.exp 2*σ^3*Real.exp 1)*2:=by gcongr
      _=crossBase b*σ^3*L^2:=by dsimp [crossBase];ring
  have hr:rowCrossCoefficient m α τ σ (1/4)≤crossBase tailDegree*σ^3*L^2:=cross _ hD
  have hc:crossCoefficient m α τ σ (1/4)≤crossBase tailMassDegree*σ^3*L^2:=cross _ hB
  have hself:selfCoefficient m α (1/4) F Z≤ selfBase*L^4*(F+Z):=by
    have hl:L≤L^4:=by simpa using pow_le_pow_right₀ hL (show 1≤4 by omega)
    have hgl:(massGap m α (1/4))⁻¹≤tailGapBase*L^4:=hgap.trans (mul_le_mul_of_nonneg_left hl hG)
    dsimp only [selfCoefficient]
    change 64*Real.exp 1*max 1 tailDegree*tailDegree*quarticLogConstant 2*L^4*F+
      16*Real.exp 1*max 1 tailMassDegree*(massGap m α (1/4))⁻¹*Z≤_
    calc
      _≤64*Real.exp 1*max 1 tailDegree*tailDegree*quarticLogConstant 2*L^4*F+
        16*Real.exp 1*max 1 tailMassDegree*(tailGapBase*L^4)*Z:=by gcongr
      _≤ selfBase*L^4*(F+Z):=by
        dsimp only [selfBase]
        nlinarith [mul_nonneg (show 0≤64*Real.exp 1*max 1 tailDegree*tailDegree*quarticLogConstant 2*L^4 by positivity) hZ,
          mul_nonneg (show 0≤16*Real.exp 1*max 1 tailMassDegree*tailGapBase*L^4 by positivity) hF]
  have hcross:fullCrossBound m α τ σ (1/4) F Z≤
      (crossBase tailDegree*(1+tailOffsetBase)+crossBase tailMassDegree*
        (1+2*tailOffsetBase+2*tailGapBase^2))*σ^3*L^7*(F+Z):=by
    dsimp only [fullCrossBound]
    calc
      _≤(crossBase tailDegree*σ^3*L^2)*((1+tailOffsetBase)*L^5)*F+
        (crossBase tailMassDegree*σ^3*L^2)*((1+2*tailOffsetBase+2*tailGapBase^2)*L^5*(F+Z)):=by
          gcongr
          · dsimp [crossBase];positivity
          · dsimp [massPathEnergy];positivity
          · dsimp [crossBase];positivity
      _≤_:=by
        have hz:=mul_nonneg (show 0≤crossBase tailDegree*(1+tailOffsetBase)*σ^3*L^7 by dsimp [crossBase];positivity) hZ
        nlinarith only [hz]
  have h47:L^4≤L^7:=pow_le_pow_right₀ hL (by omega)
  have hsfinal:=mul_le_mul_of_nonneg_left
    (hself.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h47 hb.2.2.2.2.1.le) (by positivity)))
    (show 0≤σ^3 by positivity)
  dsimp only [tailBase]
  change _≤_*σ^3*L^7*(F+Z)
  nlinarith only [hcross,hsfinal]

end NegativeVotingNearBalancedTailLogBound
