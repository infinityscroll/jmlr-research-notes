import GaussianDiagonalSecondOffsetBound

/-! Actual all-label integrated second-density control on the selected
variance path. The only remaining conditional input is the literal centered
acceleration balance equation; no acceleration estimate is assumed. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped BigOperators Classical Topology
namespace NegativeVotingDiagonalHazardSecondControl
open NegativeVotingDiagonalSecondOffsetBound NegativeVotingDiagonalSecondForcingBound
  NegativeVotingDiagonalDerivativeEnvelopes NegativeVotingDiagonalOffsetContinuation
  NegativeVotingDiagonalBalanceEquation NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingHazardSecondDifferentiation NegativeVotingHazardSecondMomentIntegral
  NegativeVotingHazardMomentEnvelope NegativeVotingHazardQuantileAsymptotics
  NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingBalancedReference NegativeVotingFanInverse

lemma eventually_referenceScale_ge_inverse_size :
    ∀ᶠ n : ℕ in atTop, 1/((n:ℝ)+2) ≤ referenceScale n := by
  filter_upwards [upperQuantile_tendsto.eventually_ge_atTop 1,
    eventually_scaledMaximum_mean_lower] with n hb hmean
  have hμ : 1 ≤ maximumMean n := by nlinarith
  unfold referenceScale
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)
    (by positivity : (0:ℝ)<(n:ℝ)+1)).2
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]

/-- This is the literal double sum, including the analytic diagonal terms.
A later differentiation theorem identifies it with the hazard acceleration. -/
theorem exists_uniform_hazard_second_control (η A : ℝ) (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, MomentBoxControl n a η 2 8 ∧
        ∀ (ξ : Fin (n+2)→ℝ), (∀i,|ξ i| ≤ A) →
        ∀ t∈Icc 0 (((n:ℝ)+2)^(-30*η)),
          ∃ k : centeredGauge (Fin (n+2)),
            HasDerivAt (varianceOffsets n ξ) k t ∧
            ∀ v : centeredGauge (Fin (n+2)),
              (∀i,offsetLaplacian (varianceSigma ξ t) (varianceOffsetVector n ξ t) v i=
                -secondForcing (varianceSigma ξ t) (varianceOffsetVector n ξ t)
                  (fun i=>ξ i/(2*varianceSigma ξ t i)) k
                  (fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)) i) →
              (∑i,∑j,|∫x,pairSecondDensity (varianceSigma ξ t) (varianceOffsetVector n ξ t)
                (fun i=>ξ i/(2*varianceSigma ξ t i)) k
                (fun i=>-(ξ i)^2/(4*(varianceSigma ξ t i)^3)) v i j x|) ≤
                referenceScale n*((n:ℝ)+2)^(20*η)*(∑i,(ξ i)^2) := by
  obtain ⟨a,ha,ha1,hcontrol⟩ := exists_uniform_variance_second_control η A hη hA
  have hconst := eventually_rpow_quantile_polynomial_le 12 (by norm_num) 0
    (-1+21*η/2) (-1+20*η) (by linarith)
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards [hcontrol,hconst,eventually_referenceScale_ge_inverse_size,
    upperQuantile_tendsto.eventually_ge_atTop 1] with n hn hconst_n hscale hb
  refine ⟨hn.1,?_⟩
  intro ξ hξ t ht
  obtain ⟨k,hk,hkbound,hσ,hh,hsource,hacc⟩ := hn.2 ξ hξ t ht
  refine ⟨k,hk,?_⟩
  intro v heq
  obtain ⟨hv,hcoeff⟩ := hacc v heq
  let m : ℝ := (n:ℝ)+2
  let H : ℝ := a*upperQuantile n
  let σ := varianceSigma ξ t
  let h := varianceOffsetVector n ξ t
  let σ₁ := fun i=>ξ i/(2*σ i)
  let σ₂ := fun i=>-(ξ i)^2/(4*(σ i)^3)
  let q := fun i=>firstEnvelope H (σ₁ i) ((k : Fin (n+2)→ℝ) i)
  let u := fun i=>secondEnvelope H (σ₁ i) ((k : Fin (n+2)→ℝ) i)
    (σ₂ i) ((v : Fin (n+2)→ℝ) i)
  let M := m^(-2+η/2)
  have hm : 0 < m := by dsimp [m];positivity
  have hM : 0 ≤ M := Real.rpow_nonneg hm.le _
  have hH : 0 ≤ H := mul_nonneg ha.le (by linarith)
  have hhalf (i:Fin (n+2)) : 1/2 ≤ σ i := by dsimp [σ];linarith [(hσ i).1]
  have hm₀ (i j:Fin (n+2)) := (hn.1 0 4 (by norm_num) (by norm_num) σ h
    (fun i=>(hσ i).1) (fun i=>(hσ i).2) hh i j).2.1
  have hm₂ (i j:Fin (n+2)) := (hn.1 2 4 (by norm_num) (by norm_num) σ h
    (fun i=>(hσ i).1) (fun i=>(hσ i).2) hh i j).2.1
  have hagg := sum_pairSecondDensity_integral_abs_le σ h σ₁ k σ₂ v q u (1/2) H M M
    (by norm_num) hhalf hH hh
    (fun i=>firstEnvelope_nonneg ..) (fun i=>secondEnvelope_nonneg ..)
    (fun x i=>transportSpeed_abs_le _ _ _ _ _ _ (hhalf i) hH (hh i))
    (fun x i=>densityLogDerivative_abs_le _ _ _ _ _ _ (hhalf i) hH (hh i))
    (fun x i=>transportAcceleration_abs_le _ _ _ _ _ _ _ _ (hhalf i) hH (hh i))
    (fun x i=>densityLogAcceleration_abs_le _ _ _ _ _ _ _ _ (hhalf i) hH (hh i)) hm₀ hm₂
  have hcoeff' : 4*(∑i,(q i)^2)+(∑i,u i) ≤ m^(10*η)*(∑i,(ξ i)^2) := hcoeff
  have hstep := mul_le_mul_of_nonneg_left hcoeff'
    (by positivity : 0 ≤ 6*(Fintype.card (Fin (n+2)):ℝ)*(M+M))
  have hraw := hagg.trans hstep
  have he : 6*(Fintype.card (Fin (n+2)):ℝ)*(M+M)*(m^(10*η)*(∑i,(ξ i)^2)) =
      (12*m^(-1+21*η/2))*(∑i,(ξ i)^2) := by
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat]
    change 6*m*(M+M)*(m^(10*η)*(∑i,(ξ i)^2))=_
    dsimp [M]
    calc
      _ = 12*(m^(1:ℝ)*m^(-2+η/2)*m^(10*η))*(∑i,(ξ i)^2) := by rw [Real.rpow_one];ring
      _ = _ := by rw [←Real.rpow_add hm,←Real.rpow_add hm];congr 2 <;> ring
  rw [he] at hraw
  have hc : 12*m^(-1+21*η/2) ≤ m^(-1+20*η) := by
    simpa only [pow_zero,mul_one,m] using hconst_n
  have href : m^(-1+20*η) ≤ referenceScale n*m^(20*η) := by
    rw [Real.rpow_add hm,Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_right (by simpa only [one_div,m] using hscale)
      (Real.rpow_nonneg hm.le _)
  exact hraw.trans (mul_le_mul_of_nonneg_right (hc.trans href)
    (Finset.sum_nonneg fun _ _=>sq_nonneg _))

end NegativeVotingDiagonalHazardSecondControl
