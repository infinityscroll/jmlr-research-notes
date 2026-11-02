import GaussianDiagonalHazardSecondControl
import GaussianHazardSecondIntegralDerivative
import GaussianDiagonalSecondBalanceEquation
import GaussianRegularHazardDerivative
import GaussianSummedTaylorRemainder
import GaussianVarianceLocalBounds

/-! Literal selected-path hazard coefficients and their Taylor control.
All coefficient derivatives refer to the raw all-label integrals. -/
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped BigOperators Classical Topology
namespace NegativeVotingDiagonalHazardTaylor
open NegativeVotingDiagonalHazardSecondControl NegativeVotingHazardSecondIntegralDerivative
  NegativeVotingDiagonalSecondBalanceEquation NegativeVotingDiagonalOffsetContinuation
  NegativeVotingRegularHazardDerivative NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingHazardRawIntegralDerivative NegativeVotingHazardKernelPathDerivative
  NegativeVotingHazardSecondMomentIntegral NegativeVotingHazardSecondDifferentiation
  NegativeVotingDiagonalDerivativeEnvelopes NegativeVotingDiagonalSecondForcingBound
  NegativeVotingDiagonalBalanceEquation NegativeVotingFanInverse NegativeVotingBalancedReference
  NegativeVotingRegularTieVariance NegativeVotingSummedTaylorRemainder
variable {n : ℕ}

def sigmaVelocity (ξ : Fin (n+2)→ℝ) (t : ℝ) (i : Fin (n+2)) : ℝ :=
  ξ i/(2*varianceSigma ξ t i)
def sigmaAcceleration (ξ : Fin (n+2)→ℝ) (t : ℝ) (i : Fin (n+2)) : ℝ :=
  -(ξ i)^2/(4*(varianceSigma ξ t i)^3)
def offsetVelocity (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) : Fin (n+2)→ℝ :=
  ((deriv (varianceOffsets n ξ) t : centeredGauge (Fin (n+2))) : Fin (n+2)→ℝ)
def offsetAcceleration (n : ℕ) (ξ : Fin (n+2)→ℝ) (t : ℝ) : Fin (n+2)→ℝ :=
  ((deriv (deriv (varianceOffsets n ξ)) t : centeredGauge (Fin (n+2))) : Fin (n+2)→ℝ)

def coefficientPath (n : ℕ) (ξ : Fin (n+2)→ℝ) (i : Fin (n+2)) (t : ℝ) : ℝ :=
  hazardCoefficient (varianceSigma ξ t) (varianceOffsetVector n ξ t) i

def coefficientFirst (n : ℕ) (ξ : Fin (n+2)→ℝ) (i : Fin (n+2)) (t : ℝ) : ℝ :=
  ∑j,∫x,hazardPairDensity (varianceSigma ξ t) (varianceOffsetVector n ξ t) x i j*
    hazardPairLogDerivative (varianceSigma ξ t) (varianceOffsetVector n ξ t)
      (sigmaVelocity ξ t) (offsetVelocity n ξ t) x i j

def coefficientSecond (n : ℕ) (ξ : Fin (n+2)→ℝ) (i : Fin (n+2)) (t : ℝ) : ℝ :=
  ∑j,∫x,pairSecondDensity (varianceSigma ξ t) (varianceOffsetVector n ξ t)
    (sigmaVelocity ξ t) (offsetVelocity n ξ t) (sigmaAcceleration ξ t) (offsetAcceleration n ξ t) i j x

lemma varianceOffsetVector_eq_balanced (ξ : Fin (n+2)→ℝ) (t : ℝ) :
    varianceOffsetVector n ξ t=balancedVariancePath ξ t := by
  have hm : uniformMass n=(fun _ : Fin (n+2)=>((n:ℝ)+2)⁻¹) := by
    funext i;simp [uniformMass,one_div]
  have hs : varianceSigma ξ t=varianceStdPath ξ t := rfl
  unfold varianceOffsetVector varianceOffsets balancedVariancePath
  rw [hm,hs]

lemma coefficientPath_initial (hn : 0 < n) (ξ : Fin (n+2)→ℝ) (i : Fin (n+2)) :
    coefficientPath n ξ i 0=referenceScale n := by
  change hazardCoefficient (varianceStdPath ξ 0) (varianceOffsetVector n ξ 0) i=_
  rw [varianceOffsetVector_eq_balanced,varianceStdPath_zero,balancedVariancePath_zero]
  exact hazardCoefficient_regular n hn i

lemma offsetVector_hasDerivAt (ξ : Fin (n+2)→ℝ) (t : ℝ) (hpos : ∀i,0<1+t*ξ i) :
    HasDerivAt (varianceOffsetVector n ξ) (offsetVelocity n ξ t) t := by
  exact ((centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt).comp_hasDerivAt t
    ((varianceOffsets_contDiffAt ξ t hpos).differentiableAt (by norm_num)).hasDerivAt

lemma offsetVelocity_hasDerivAt (ξ : Fin (n+2)→ℝ) (t : ℝ) (hpos : ∀i,0<1+t*ξ i) :
    HasDerivAt (offsetVelocity n ξ) (offsetAcceleration n ξ t) t := by
  exact ((centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt).comp_hasDerivAt t
    (varianceOffsets_deriv_differentiableAt ξ t hpos).hasDerivAt

lemma coefficientPath_hasDerivAt (ξ : Fin (n+2)→ℝ) (t : ℝ) (hpos : ∀i,0<1+t*ξ i)
    (i : Fin (n+2)) : HasDerivAt (coefficientPath n ξ i) (coefficientFirst n ξ i t) t := by
  have hcσ := contDiffAt_pi.mp (varianceSigma_contDiffAt ξ t hpos 1)
  have hch : ∀i,ContDiffAt ℝ 1 (fun z=>varianceOffsetVector n ξ z i) t := by
    have hh := ((centeredGauge (Fin (n+2))).subtypeL.contDiff.contDiffAt).comp t
      (varianceOffsets_contDiffAt ξ t hpos)
    exact contDiffAt_pi.mp hh
  have hd := HasDerivAt.fun_sum (u:=Finset.univ) fun j _=>
    hazardPairIntegral_raw_hasDerivAt (varianceSigma ξ) (varianceOffsetVector n ξ) t
      hcσ hch (fun i=>Real.sqrt_pos.mpr (hpos i)) i j
  have hsigma : pathDerivative (varianceSigma ξ) t=sigmaVelocity ξ t := by
    funext i
    exact (hasDerivAt_pi.mp (varianceSigma_hasDerivAt ξ t hpos) i).deriv
  have hoff : pathDerivative (varianceOffsetVector n ξ) t=offsetVelocity n ξ t := by
    funext i
    exact (hasDerivAt_pi.mp (offsetVector_hasDerivAt ξ t hpos) i).deriv
  rw [hsigma,hoff] at hd
  exact hd

lemma coefficientFirst_initial (hn : 0 < n) (ξ : Fin (n+2)→ℝ) (hξ : ∑i,ξ i=0)
    (i : Fin (n+2)) : coefficientFirst n ξ i 0= -referenceScale n*eta n*ξ i := by
  have hactual := coefficientPath_hasDerivAt ξ 0 (by intro i;norm_num) i
  have hregular := hazardCoefficient_balancedVariance_hasDerivAt n hn ξ hξ i
  have he : coefficientPath n ξ i=(fun t=>hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i) := by
    funext t
    unfold coefficientPath
    rw [varianceOffsetVector_eq_balanced]
    rfl
  rw [he] at hactual
  exact hactual.unique hregular

lemma coefficientFirst_hasDerivAt_of_bounds (ξ : Fin (n+2)→ℝ) (i : Fin (n+2)) (t S H K₁ K₂ : ℝ)
    (G : Set ℝ) (hG : G∈𝓝 t) (hH : 0 ≤ H) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hbox : ∀z∈G,∀i,1/2 ≤ varianceSigma ξ z i ∧ varianceSigma ξ z i ≤ S ∧
      |varianceOffsetVector n ξ z i| ≤ H)
    (hfirst : ∀z∈G,∀i,|sigmaVelocity ξ z i| ≤ K₁ ∧ |offsetVelocity n ξ z i| ≤ K₁)
    (hsecond : ∀z∈G,∀i,|sigmaAcceleration ξ z i| ≤ K₂ ∧ |offsetAcceleration n ξ z i| ≤ K₂) :
    HasDerivAt (coefficientFirst n ξ i) (coefficientSecond n ξ i t) t := by
  let q : Fin (n+2)→ℝ := fun _=>32*(1+H)^2*K₁
  let u : Fin (n+2)→ℝ := fun _=>256*(1+H)^2*(K₂+K₁^2)
  have hpos (z:ℝ) (hz:z∈G) (i:Fin (n+2)) : 0<1+z*ξ i :=
    Real.sqrt_pos.mp (show 0<varianceSigma ξ z i from by linarith [(hbox z hz i).1])
  have hq (z:ℝ) (hz:z∈G) (i:Fin (n+2)) :
      firstEnvelope H (sigmaVelocity ξ z i) (offsetVelocity n ξ z i) ≤ q i := by
    have hh := add_le_add (hfirst z hz i).1 (hfirst z hz i).2
    have hp := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ)≤16*(1+H)^2)
    convert hp using 1 <;> dsimp [firstEnvelope,q] <;> ring
  have hu (z:ℝ) (hz:z∈G) (i:Fin (n+2)) :
      secondEnvelope H (sigmaVelocity ξ z i) (offsetVelocity n ξ z i)
        (sigmaAcceleration ξ z i) (offsetAcceleration n ξ z i) ≤ u i := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) (hfirst z hz i).1 2
    have ht := pow_le_pow_left₀ (abs_nonneg _) (hfirst z hz i).2 2
    simp only [sq_abs] at hs ht
    have hh := add_le_add (add_le_add (add_le_add (hsecond z hz i).1 (hsecond z hz i).2) hs) ht
    have hp := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ)≤128*(1+H)^2)
    convert hp using 1 <;> dsimp [secondEnvelope,u] <;> ring
  apply HasDerivAt.fun_sum (u:=Finset.univ)
  intro j _
  apply rawFirstIntegral_hasDerivAt (varianceSigma ξ) (varianceOffsetVector n ξ)
    (sigmaVelocity ξ) (offsetVelocity n ξ) (sigmaAcceleration ξ) (offsetAcceleration n ξ)
    t S H G hG hH q u (fun _=>by dsimp [q];positivity) (fun _=>by dsimp [u];positivity) hbox
  · intro z hz i;exact hasDerivAt_pi.mp (varianceSigma_hasDerivAt ξ z (hpos z hz)) i
  · intro z hz i;exact hasDerivAt_pi.mp (offsetVector_hasDerivAt ξ z (hpos z hz)) i
  · intro z hz i;exact hasDerivAt_pi.mp (varianceSigma_first_hasDerivAt ξ z (hpos z hz)) i
  · intro z hz i;exact hasDerivAt_pi.mp (offsetVelocity_hasDerivAt ξ z (hpos z hz)) i
  · exact hq
  · exact hu

/-- All derivatives and the summed acceleration estimate are actual. The
threshold precedes the variance direction and time, including t=0. -/
theorem exists_uniform_actual_hazard_derivatives (η A : ℝ) (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, MomentBoxControl n a η 2 8 ∧
        ∀ (ξ : Fin (n+2)→ℝ), (∀i,|ξ i| ≤ A) →
        ∀ t∈Icc 0 (((n:ℝ)+2)^(-30*η)),
          (∀i,HasDerivAt (coefficientPath n ξ i) (coefficientFirst n ξ i t) t) ∧
          (∀i,HasDerivAt (coefficientFirst n ξ i) (coefficientSecond n ξ i t) t) ∧
          (∑i,|coefficientSecond n ξ i t|) ≤
            referenceScale n*((n:ℝ)+2)^(20*η)*(∑i,(ξ i)^2) := by
  obtain ⟨a,ha,ha1,hcontrol⟩ := exists_uniform_hazard_second_control η A hη hA
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards [hcontrol,NegativeVotingVarianceLocalBounds.exists_variance_local_bounds η A hη hA]
    with n hn hlocal
  refine ⟨hn.1,?_⟩
  intro ξ hξ t ht
  obtain ⟨G,H,K₁,K₂,hG,hH,hK₁,hK₂,hbox⟩ := hlocal ξ hξ t ht
  have htG : t∈G := mem_of_mem_nhds hG
  have hhalf (i:Fin (n+2)) : 1/2 ≤ varianceSigma ξ t i := (hbox t htG i).1
  have hpos (i:Fin (n+2)) : 0<1+t*ξ i :=
    Real.sqrt_pos.mp (show 0<varianceSigma ξ t i from by linarith [hhalf i])
  refine ⟨fun i=>coefficientPath_hasDerivAt ξ t hpos i,?_,?_⟩
  · intro i
    apply coefficientFirst_hasDerivAt_of_bounds ξ i t 2 H K₁ K₂ G hG hH hK₁ hK₂
    · intro z hz i
      exact ⟨(hbox z hz i).1,(hbox z hz i).2.1,(hbox z hz i).2.2.1⟩
    · intro z hz i
      exact ⟨(hbox z hz i).2.2.2.1,(hbox z hz i).2.2.2.2.1⟩
    · intro z hz i
      exact ⟨(hbox z hz i).2.2.2.2.2.1,(hbox z hz i).2.2.2.2.2.2⟩
  · obtain ⟨k,hk,hkernel⟩ := hn.2 ξ hξ t ht
    obtain ⟨v,hv,heq⟩ := exists_variance_second_balance ξ t hhalf
    have hkd : deriv (varianceOffsets n ξ) t=k := hk.deriv
    have hvd : deriv (deriv (varianceOffsets n ξ)) t=v := hv.deriv
    rw [hkd] at heq
    have hb := hkernel v heq
    rw [←hkd,←hvd] at hb
    have htri := Finset.sum_le_sum (s:=Finset.univ) fun i _=>
      Finset.abs_sum_le_sum_abs
        (fun j=>∫x,pairSecondDensity (varianceSigma ξ t) (varianceOffsetVector n ξ t)
          (sigmaVelocity ξ t) (offsetVelocity n ξ t) (sigmaAcceleration ξ t)
          (offsetAcceleration n ξ t) i j x) Finset.univ
    exact htri.trans hb

/-- Summed Taylor remainder for the literal all-label hazard coefficient.
No offset box, moment bound, acceleration equation or differentiability
assumption occurs in this final endpoint. -/
theorem exists_uniform_hazard_taylor (η A : ℝ) (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, MomentBoxControl n a η 2 8 ∧
        ∀ (ξ : Fin (n+2)→ℝ), (∀i,|ξ i| ≤ A) → (∑i,ξ i=0) →
        ∀ t∈Icc 0 (((n:ℝ)+2)^(-30*η)),
          (∑i,|hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i-
            (referenceScale n-referenceScale n*eta n*t*ξ i)|) ≤
            ((n:ℝ)+2)^(20*η)*referenceScale n*t^2*(∑i,(ξ i)^2) := by
  obtain ⟨a,ha,ha1,hcontrol⟩ := exists_uniform_actual_hazard_derivatives η A hη hA
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards [hcontrol,eventually_gt_atTop 0] with n hn hn0
  refine ⟨hn.1,?_⟩
  intro ξ hξ hsum t ht
  let B := referenceScale n*((n:ℝ)+2)^(20*η)*(∑i,(ξ i)^2)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity [referenceScale_pos n,Finset.sum_nonneg (s:=Finset.univ) (fun i _=>sq_nonneg (ξ i))]
  have hfirst (i:Fin (n+2)) (s:ℝ) (hs:s∈Icc 0 t) :
      HasDerivAt (coefficientPath n ξ i) (coefficientFirst n ξ i s) s :=
    (hn.2 ξ hξ s ⟨hs.1,hs.2.trans ht.2⟩).1 i
  have hsecond (i:Fin (n+2)) (s:ℝ) (hs:s∈Icc 0 t) :
      HasDerivAt (coefficientFirst n ξ i) (coefficientSecond n ξ i s) s :=
    (hn.2 ξ hξ s ⟨hs.1,hs.2.trans ht.2⟩).2.1 i
  have hbound (s:ℝ) (hs:s∈Icc 0 t) : (∑i,|coefficientSecond n ξ i s|) ≤ B :=
    (hn.2 ξ hξ s ⟨hs.1,hs.2.trans ht.2⟩).2.2
  have hTaylor := summed_second_remainder_le (coefficientPath n ξ) (coefficientFirst n ξ)
    (coefficientSecond n ξ) t B ht.1 hB hfirst hsecond hbound
  have he (i:Fin (n+2)) : coefficientPath n ξ i t-coefficientPath n ξ i 0-t*coefficientFirst n ξ i 0=
      hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i-
        (referenceScale n-referenceScale n*eta n*t*ξ i) := by
    rw [coefficientPath_initial hn0 ξ i,coefficientFirst_initial hn0 ξ hsum i]
    unfold coefficientPath
    rw [varianceOffsetVector_eq_balanced]
    change hazardCoefficient (varianceStdPath ξ t) (balancedVariancePath ξ t) i-referenceScale n-
      t*(-referenceScale n*eta n*ξ i)=_
    ring
  simp_rw [he] at hTaylor
  convert hTaylor using 1 <;> dsimp [B] <;> ring

end NegativeVotingDiagonalHazardTaylor
