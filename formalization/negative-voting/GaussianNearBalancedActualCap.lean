import GaussianNearBalancedStructuredCap
import GaussianStructuredAmplitudeBound

/-! The actual near-balanced residual cap with its literal amplitude bound
and ceiling discharged. The threshold precedes the ambient dimension and
all fractional assignments. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingNearBalancedActualCap
open NegativeVotingNearBalancedStructuredCap NegativeVotingStructuredAmplitudeBound
  NegativeVotingStructuredSwitchingAllAmplitudes NegativeVotingStructuredSwitchingAmplitude
  NegativeVotingStructuredResidualInputs NegativeVotingNearBalancedSourceInputs
  NegativeVotingStructuredSwitchingMoments NegativeVotingSmoothErrorMoment
  NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanInverse
  NegativeVotingSwitchingOrdered NegativeVotingDisintegration
  NegativeVotingSwitchingModerateIntegral

def actualCapConstant (A e H:ℝ):ℝ :=
  capConstant A e 2 (massDegree e)*amplitudeLogConstant A 4 (4*A) e H

theorem capConstant_nonneg (A e:ℝ) (he:0 < e) : 0 ≤ capConstant A e 2 (massDegree e) := by
  have hm:0 ≤ moderateMarginConstant e 2:=le_trans zero_le_one (le_max_right _ _)
  unfold capConstant
  positivity [massDegree_pos e he]

/-- The completed analytic cap for the literal residual. In particular no
amplitude, moment, facet-envelope, margin, or normal-regularity conclusion is
assumed. The residual comes from genuine fractional assignments. -/
theorem exists_dimension_uniform_actual_cap
    (A K e H B:ℝ) (hA:8192 ≤ A) (hK:0 ≤ K) (he:0 < e) (hH:0 ≤ H) (hB:0 ≤ B) :
    ∃N:ℕ,∀ n :ℕ,N ≤ n → ∀ d :ℕ,∀ R D:Fin (n+2) → FSC.Coord d,
      (∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) → 
      ∀ α :ℝ,0 < α → (∑i,‖D i‖^2) ≤ α^2/256 → 
      e*Real.sqrt (logScale n)/((n:ℝ)+2) ≤ α/2 → 
      α ≤ H*Real.sqrt (logScale n)/((n:ℝ)+2) → 
      ∀ v :centeredGauge (Fin (n+2)),(∀ i,|(v:Fin (n+2) → ℝ) i| ≤ 1/(2*((n:ℝ)+2))) → 
      (∑i,‖D i‖^2)+(∑i,((v:Fin (n+2) → ℝ) i)^2) ≤ B/((n:ℝ)+2) → 
      ∀ η τ χ:ℝ,0 < τ → 0 < χ → χ < 1 → τ^2=1/(4*A*logScale n-1) → 
      (τ*χ)^2 ≤ 1/((n:ℝ)+1) → 0 ≤ η → η ≤ K*((τ*χ)^2)^2*logScale n → 
      ∀ f g:Fin (n+2) → FSC.Coord d → ℝ,
      (∀ i,Measurable (f i)) → (∀ i,Measurable (g i)) → 
      (∀ᵐ x ∂stdGaussian (FSC.Coord d),(∀ i,0 ≤ f i x ∧ f i x ≤ 1) ∧ ∑i,f i x=1) → 
      (∀ᵐ x ∂stdGaussian (FSC.Coord d),(∀ i,0 ≤ g i x ∧ g i x ≤ 1) ∧ ∑i,g i x=1) → 
      let r:ℝ:=(τ*χ)^2
      let u:=fun i=>projectedOddResidual (Real.sqrt r) (f i-g i)
      let p:Fin (n+2) → ℝ:=(fun _=>((n:ℝ)+2)⁻¹)+(v:Fin (n+2) → ℝ)
      let h:Fin (n+2) → ℝ:=selectedOffsets (α•R+D) p
      let p₀:NegativeVotingFanScore.Parameters d (Fin (n+2)):=
        (α•R,selectedOffsets (α•R) (fun _=>((n:ℝ)+2)⁻¹))
      let p₁:NegativeVotingFanScore.Parameters d (Fin (n+2)):=(α•R+D,h)
      (∫x,closedCellCap (α•R+D) h (residualWeightedForcing R D h η τ χ p₀ p₁ u) 1 x
        ∂stdGaussian (FSC.Coord d)) ≤ 
        actualCapConstant A e H*(logScale n)^10*
          (r^2*((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2) → ℝ) i)^2))+
            r*(∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (u i))^2)) := by
  obtain ⟨N₁,hN₁⟩:=exists_near_balanced_actualResidual_cap A K e H hA hK he hH
  obtain ⟨N₂,hN₂⟩:=exists_dimension_uniform_actual_amplitude_ceiling
    A 4 (4*A) e H B (by norm_num) (by linarith) he hH hB
  obtain ⟨N₃,hN₃⟩:=exists_common_smoothing_threshold A e hA he
  refine ⟨N₁+N₂+N₃+2,?_⟩
  intro n hn d R D hGram α hα hD hscale hupper v hv hsize η τ χ hτ hχ hχ1
    ht hrange hη hηupper f g hfm hgm hf hg r u p h p₀ p₁
  have hn1:1 ≤ n:=by omega
  have hm0:0 < (n:ℝ)+2:=by positivity
  have hGram':∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hGram
  have hscale':e*Real.sqrt (logScale n)/((n+2:ℕ):ℝ) ≤ α/2:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hscale
  have hupper':α ≤ H*Real.sqrt (logScale n)/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hupper
  have hv':∀ i,|(v:Fin (n+2) → ℝ) i| ≤ 1/(2*((n+2:ℕ):ℝ)):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hv
  have hsize':(∑i,‖D i‖^2)+(∑i,((v:Fin (n+2) → ℝ) i)^2) ≤ B/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hsize
  obtain ⟨hqlog,hinv,hτ2,hrel,hnative,hq⟩:=hN₃ n (by omega) α τ hα hscale' ht
  have hτ1:τ < 1:=by nlinarith
  have hr:0 < r:=sq_pos_of_pos (mul_pos hτ hχ)
  have hprod:τ*χ < 1:=(mul_lt_mul_of_pos_left hχ1 hτ).trans (by simpa using hτ1)
  have hr1:r < 1:=by dsimp only [r];nlinarith [mul_pos hτ hχ]
  have hr2:r ≤ 2/((n+2:ℕ):ℝ):=by
    have hden:0 < (n:ℝ)+1:=by positivity
    have hrat:1/((n:ℝ)+1) ≤ 2/((n:ℝ)+2):=by
      apply (div_le_div_iff₀ hden hm0).mpr
      nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hrange.trans hrat
  have ht':τ^2=1/(2*(2*A*logScale n)-1):=by convert ht using 1;ring
  have hceil:=hN₂ n (by omega) d R D hGram' α hα hD hscale' hupper' v hv' hsize'
    r τ χ (2*A*logScale n) hr hr1 hr2 hτ hχ hχ1 rfl hq ht' hqlog hinv hτ2 hrel f g hfm hgm hf hg
  have hs:0 < Real.sqrt r:=Real.sqrt_pos.mpr hr
  have hs1:Real.sqrt r < 1:=by nlinarith [Real.sq_sqrt hr.le]
  have hu:=fractional_projectedOddResidual_sum_norm_sq_le (Real.sqrt r) hs hs1 f g hfm hgm hf hg
  have huM i:Measurable (u i):=projectedOddResidual_measurable _ _ ((hfm i).sub (hgm i))
  have hbox:=uniform_massLine_box v hv' 1 ⟨by norm_num,le_rfl⟩
  have hlo:∀ i,1/(2*((n:ℝ)+2)) ≤ p i:=by
    intro i
    simpa only [massLine,one_smul,p,Nat.cast_add,Nat.cast_ofNat] using (hbox i).1
  have hup:∀ i,p i ≤ 2/((n:ℝ)+2):=by
    intro i
    simpa only [massLine,one_smul,p,Nat.cast_add,Nat.cast_ofNat] using (hbox i).2
  have hp:∑i,p i=1:=by
    have hv0:∑i,(v:Fin (n+2)→ℝ) i=0:=v.property
    simp only [p,Pi.add_apply,Finset.sum_add_distrib,hv0,add_zero,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
    exact mul_inv_cancel₀ hm0.ne'
  have hcap:=hN₁ n (by omega) d R D hGram α hα hD hscale hupper p hp hlo hup
    η τ χ hτ hτ1 hχ hχ1 hrange hη hηupper hnative u huM hu.1
  have hceil':structuredAmplitude A 4 r τ D h (cellSource τ χ p₀ p₁)
      (fun i=>highSource χ (u i)) ≤ ((n:ℝ)+2)^(-(5:ℝ)/4):=by
    simpa only [actualAmplitude,r,u,h,p,p₀,p₁,Nat.cast_add,Nat.cast_ofNat,neg_div] using hceil
  have hbound:=near_balanced_amplitude_sq_le hn1 R D hGram' α e H hα he hH hD hscale' hupper' v hv'
    A 4 (4*A) r τ χ (2*A*logScale n) (by norm_num) (by linarith) hτ hχ hχ1 rfl hq ht'
    hqlog hinv hτ2 hrel u huM hu.1 hu.2.1
  have hbound':(structuredAmplitude A 4 r τ D h (cellSource τ χ p₀ p₁)
      (fun i=>highSource χ (u i)))^2 ≤ 
      amplitudeLogConstant A 4 (4*A) e H*(logScale n)^10*
        (r^2*((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2) → ℝ) i)^2))+
          r*(∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (u i))^2)):=by
    simpa only [r,h,p,p₀,p₁,Nat.cast_add,Nat.cast_ofNat] using hbound
  apply (hcap hceil').trans
  convert mul_le_mul_of_nonneg_left hbound' (capConstant_nonneg A e he) using 1
  unfold actualCapConstant
  ring

end NegativeVotingNearBalancedActualCap
