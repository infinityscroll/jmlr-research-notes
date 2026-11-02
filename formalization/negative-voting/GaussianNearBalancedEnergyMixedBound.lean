import GaussianNearBalancedEnergyComparison

/-! A mixed row/mass estimate retaining the square-root cancellation needed
in local signed-noise absorption. Every selected-path derivative is actual. -/
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingNearBalancedEnergyMixedBound
open NegativeVotingNearBalancedEnergyComparison NegativeVotingNearBalancedSourceInputs
  NegativeVotingNearBalancedHighTailComparison NegativeVotingNearRegularBalancedGeometry
  NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanSelectedOffsets
  NegativeVotingFanQuadraticMoments NegativeVotingSecondChaosMassAdjoint
  NegativeVotingRegularCoefficientBound
variable {d : ℕ}

theorem near_mass_energy_abs_le_mixed {n : ℕ} (hn : 1 ≤ n)
    (R D : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e)
    (hscale : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2)
    (v : centeredGauge (Fin (n+2)))
    (hv : ∀ i,|(v : Fin (n+2) → ℝ) i| ≤ 1/(2*((n+2:ℕ):ℝ))) :
    |secondEnergy (α•R+D)
      (selectedOffsets (α•R+D) ((fun _ => ((n+2:ℕ):ℝ)⁻¹)+(v : Fin (n+2) → ℝ)))-
      secondEnergy (α•R+D) (selectedOffsets (α•R+D) (fun _ => ((n+2:ℕ):ℝ)⁻¹))| ≤
      Real.sqrt (massAdjointCoefficient n α e*((∑ i,‖D i‖^2)+(∑ i,((v : Fin (n+2) → ℝ) i)^2))*(∑ i,((v : Fin (n+2) → ℝ) i)^2)) := by
  let B:=α•R+D
  let p:Fin (n+2) → ℝ:=fun _ => ((n+2:ℕ):ℝ)⁻¹
  let f:=fun t : ℝ => secondEnergy B (offsetLine B p v t)
  let f':=fun t : ℝ => ∑ i,massAdjoint B (offsetLine B p v t) i*(v : Fin (n+2) → ℝ) i
  let F:=∑ i,‖D i‖^2
  let Z:=∑ i,((v : Fin (n+2) → ℝ) i)^2
  let C:=massAdjointCoefficient n α e
  have hF:0 ≤ F:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hZ:0 ≤ Z:=Finset.sum_nonneg fun i _ => sq_nonneg _
  have hC:0 ≤ C:=massAdjointCoefficient_nonneg n α e hα he
  have hm:3 ≤ n+2:=by omega
  have hm0:(0:ℝ) < (n+2:ℕ):=by positivity
  have hp:∑ i,p i=1:=by
    simp only [p,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ hm0.ne'
  have hg:=segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hd t (ht : t ∈ Icc (0:ℝ) 1) : HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t:=by
    have hpos:∀ i,0 < massLine p v t i:=fun i =>
      lt_of_lt_of_le (by positivity) (uniform_massLine_box v hv t ht i).1
    exact (mass_secondEnergy_hasDerivAt B (α/2) (by positivity) hg.1 p v hp t hpos).hasDerivWithinAt
  have hb t (ht : t ∈ Ico (0:ℝ) 1) : ‖f' t‖ ≤ Real.sqrt (C*(F+Z)*Z):=by
    have htc:t ∈ Icc (0:ℝ) 1:=⟨ht.1,ht.2.le⟩
    have hbnd:=scaled_mass_error_bounds v hv t htc
    have ha:=near_balanced_massAdjoint_sq_le hn R D hG α hα hD e he hscale (t•v) hbnd.1
    have ha':(∑ i,(massAdjoint B (offsetLine B p v t) i)^2) ≤ C*(F+Z):=by
      have ha'':(∑ i,(massAdjoint B (offsetLine B p v t) i)^2) ≤
          C*(F+(∑ i,(((t•v : centeredGauge (Fin (n+2))) : Fin (n+2) → ℝ) i)^2)):=by
        simpa only [C,F,B,offsetLine,massLine,p,Submodule.coe_smul] using ha
      exact ha''.trans (mul_le_mul_of_nonneg_left (by dsimp only [Z];linarith [hbnd.2]) hC)
    have hcs:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => massAdjoint B (offsetLine B p v t) i) (v : Fin (n+2) → ℝ)
    have hs:(f' t)^2 ≤ C*(F+Z)*Z:=hcs.trans (mul_le_mul_of_nonneg_right ha' hZ)
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt (by positivity)]
    exact hs
  have hh:=norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa only [f,offsetLine,massLine,one_smul,zero_smul,add_zero,B,p,F,Z,C,Real.norm_eq_abs] using hh

/-- The squared mixed estimate has no pure row-error term, even after all
coefficients have been bounded by a fixed logarithmic power. -/
theorem exists_dimension_uniform_mass_energy_mixed_log :
    ∃ N : ℕ,∀ n : ℕ,N ≤ n → ∀ d : ℕ,∀ R D : Fin (n+2) → FSC.Coord d,
      (∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ)) →
      ∀ α e H : ℝ,0 < α → 0 < e → 0 ≤ H →
      (∑ i,‖D i‖^2) ≤ α^2/256 →
      e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) ≤ α/2 →
      α ≤ H*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) →
      ∀ v : centeredGauge (Fin (n+2)),
      (∀ i,|(v : Fin (n+2) → ℝ) i| ≤ 1/(2*((n+2:ℕ):ℝ))) →
      (secondEnergy (α•R+D)
        (selectedOffsets (α•R+D) ((fun _ => ((n+2:ℕ):ℝ)⁻¹)+(v : Fin (n+2) → ℝ)))-
        secondEnergy (α•R+D) (selectedOffsets (α•R+D) (fun _ => ((n+2:ℕ):ℝ)⁻¹)))^2 ≤
        massAdjointBase e H*(1+Real.log ((n+2:ℕ):ℝ))^13*
          ((∑ i,‖D i‖^2)+(∑ i,((v : Fin (n+2) → ℝ) i)^2))*
            (∑ i,((v : Fin (n+2) → ℝ) i)^2) := by
  obtain ⟨N,hN⟩:=eventually_atTop.mp eventually_momentCoefficient_log_bound
  refine ⟨N+1,?_⟩
  intro n hn d R D hG α e H hα he hH hD hlower hupper v hv
  have hn1:1 ≤ n:=by omega
  have hγ:|NegativeVotingRegularQuadraticRepresentation.momentCoefficient n| ≤
      30*(1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hN n (by omega)
  have hc:=massAdjointCoefficient_log_le n hn1 α e H hα he hH hlower hupper hγ
  have hh:=near_mass_energy_abs_le_mixed hn1 R D hG α hα hD e he hlower v hv
  have hs:=pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hF:0 ≤ ∑i,‖D i‖^2:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hZ:0 ≤ ∑i,((v:Fin (n+2)→ℝ) i)^2:=Finset.sum_nonneg fun i _=>sq_nonneg _
  rw [sq_abs,Real.sq_sqrt (by positivity [massAdjointCoefficient_nonneg n α e hα he])] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (add_nonneg hF hZ)) hZ)

end NegativeVotingNearBalancedEnergyMixedBound
