import GaussianNearRegularEnergyLogBound

/-! Actual two-point second-energy comparison in a regular score ball.
The gradient bound is derived from the actual shifted Taylor estimate and
regular stationarity, without requiring twice differentiable offset choices. -/
noncomputable section
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingNearRegularEnergyRectangle
open NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanQuadraticMoments
  NegativeVotingNearRegularBalancedGeometry NegativeVotingNearRegularEnergyComparison
  NegativeVotingBalancedEnergyComparison NegativeVotingRegularReferenceNormalization
  NegativeVotingBalancedSecondChaosDerivative NegativeVotingFanCanonicalOffset
  NegativeVotingCoherentLiftHessian NegativeVotingCapTail NegativeVotingBalancedFacetHessian
  NegativeVotingSecondChaosMassAdjoint NegativeVotingFacetDegree NegativeVotingFanOffsetMinimization
variable {d n : ℕ}

def rowSq (X : Fin (n+2)→FSC.Coord d) : ℝ:=∑i,‖X i‖^2

def energy (R : Fin (n+2)→FSC.Coord d) (α : ℝ) (X : Fin (n+2)→FSC.Coord d) : ℝ:=
  secondEnergy (α•R+X) (selectedOffsets (α•R+X) (fun _=>(n+2:ℕ)⁻¹))

def energyGradient (R : Fin (n+2)→FSC.Coord d) (α : ℝ)
    (X V : Fin (n+2)→FSC.Coord d) : ℝ:=
  let B:=α•R+X
  let h:Fin (n+2)→ℝ:=selectedOffsets B (fun _=>(n+2:ℕ)⁻¹)
  secondEnergyDerivative B h (V,canonicalOffsetVariation B h V)

theorem rowSq_nonneg (X : Fin (n+2)→FSC.Coord d) : 0 ≤ rowSq X:=
  Finset.sum_nonneg fun i _=>sq_nonneg _

theorem rowSq_smul (t : ℝ) (X : Fin (n+2)→FSC.Coord d) : rowSq (t•X)=t^2*rowSq X := by
  simp only [rowSq,Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Finset.mul_sum]

theorem rowSq_add_le (X Y : Fin (n+2)→FSC.Coord d) : rowSq (X+Y) ≤ 2*rowSq X+2*rowSq Y := by
  simp only [rowSq,Pi.add_apply,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hh:=pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (X i) (Y i)) 2
  nlinarith [sq_nonneg (‖X i‖-‖Y i‖)]

theorem rowSq_eq_zero (X : Fin (n+2)→FSC.Coord d) (h : rowSq X=0) : X=0 := by
  funext i
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _=>sq_nonneg ‖X j‖)).mp h i (Finset.mem_univ i)))

theorem canonicalOffsetVariation_smul (B D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (σ : ℝ) (hσ : 0<σ) (hlower : CenteredSingularLowerBound B σ) (t : ℝ) :
    canonicalOffsetVariation B h (t•D)=t•canonicalOffsetVariation B h D := by
  have hr : rowMassVariation B h (t•D)=t•rowMassVariation B h D := by
    funext i
    simpa only [rowMassVariation,smul_zero,Pi.smul_apply,smul_eq_mul] using
      mixedForm_smul_left B D 0 h 0 (Pi.single i 1) σ hσ hlower t
  simp only [canonicalOffsetVariation,hr,Matrix.mulVec_smul,smul_neg]

theorem energyGradient_smul (R X V : Fin (n+2)→FSC.Coord d) (α σ : ℝ)
    (hσ : 0<σ) (hlower : CenteredSingularLowerBound (α•R+X) σ) (t : ℝ) :
    energyGradient R α X (t•V)=t*energyGradient R α X V := by
  dsimp only [energyGradient]
  rw [canonicalOffsetVariation_smul _ _ _ σ hσ hlower]
  exact map_smul _ t (V,canonicalOffsetVariation _ _ V)

/-- Actual Taylor remainder about an arbitrary base point in the regular ball. -/
theorem actual_taylor_abs_le (hn : 1 ≤ n) (R X Z : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ))
    (α e F : ℝ) (hα : 0<α) (he : 0<e) (hF : F ≤ α^2/256)
    (hscale : e*Real.sqrt (1+Real.log (n+2:ℕ))/(n+2:ℕ) ≤ α/2)
    (hpath : ∀t∈Icc (0:ℝ) 1,rowSq (X+t•Z) ≤ F) :
    |energy R α (X+Z)-energy R α X-energyGradient R α X Z| ≤
      energyComparisonCoefficient n α e F*rowSq Z := by
  let p : Fin (n+2)→ℝ:=fun _=>(n+2:ℕ)⁻¹
  have hp i : 0<p i:=by dsimp [p];positivity
  have hs : ∑i,p i=1:=by simp [p,show (n:ℝ)+2≠0 by positivity]
  let L : ℝ→(Fin (n+2)→ℝ)→L[ℝ]FSC.Coord d := fun t=>
    if ht:t∈Icc (0:ℝ) 1 then
      nearRegularLift hn R (X+t•Z) hG α hα ((hpath t ht).trans hF) else 0
  have hlower : ∀t∈Icc (0:ℝ) 1,CenteredSingularLowerBound ((α•R+X)+t•Z) (α/2) := by
    intro t ht
    have hh:=(segment_geometry (show 3 ≤ n+2 by omega) R (X+t•Z) hG α hα
      ((hpath t ht).trans hF) 1 ⟨by norm_num,le_rfl⟩).1
    simpa only [one_smul,add_assoc] using hh
  have hL : ∀t∈Icc (0:ℝ) 1,CoherentLift ((α•R+X)+t•Z) (L t) := by
    intro t ht
    dsimp only [L]
    rw [dif_pos ht]
    simpa only [add_assoc] using nearRegularLift_coherent hn R (X+t•Z) hG α hα _
  have hh:=selectedEnergy_sub_linear_abs_le (α•R+X) Z p hp hs (α/2) (by positivity) hlower L hL
    (energyComparisonCoefficient n α e F*rowSq Z)
    (mul_nonneg (energyComparisonCoefficient_nonneg n α e F hα he) (rowSq_nonneg Z))
    (by
      intro t ht
      have ht':t∈Icc (0:ℝ) 1:=⟨ht.1,ht.2.le⟩
      have hb:=selected_endpoint_hessian_abs_le hn R (X+t•Z) Z hG α hα
        ((hpath t ht').trans hF) e he hscale F (hpath t ht')
      simpa only [p,selectedRowOffsets,L,dif_pos ht',add_assoc,rowSq] using hb)
  simpa only [energy,energyGradient,p,add_assoc,rowSq] using hh

theorem energyGradient_at_regular (hn : 1 ≤ n) (R V : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ))
    (α : ℝ) (hα : 0<α) : energyGradient R α 0 V=0 := by
  simp only [energyGradient,add_zero,selected_regular_scaled_zero R hG α hα,
    secondEnergyDerivative_regular_scaled_zero hn R hG α hα,ContinuousLinearMap.zero_apply]

theorem reference_quadratic_abs_le (hn : 1 ≤ n) (R X : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ))
    (α e F : ℝ) (hα : 0<α) (he : 0<e) (hF : F ≤ α^2/256)
    (hscale : e*Real.sqrt (1+Real.log (n+2:ℕ))/(n+2:ℕ) ≤ α/2)
    (hX : rowSq X ≤ F) :
    |energy R α X-energy R α 0| ≤ energyComparisonCoefficient n α e F*rowSq X := by
  have hh:=actual_taylor_abs_le hn R 0 X hG α e F hα he hF hscale
    (fun t ht=>by simpa only [zero_add,rowSq] using (segment_rowEnergy_le X t ht).trans hX)
  simpa only [zero_add,energyGradient_at_regular hn R X hG α hα,sub_zero] using hh

/-- A genuine first-derivative bound with the product of the base displacement
and tangent sizes. This is stronger than separately bounding two energy errors. -/
theorem actual_gradient_abs_le (hn : 1 ≤ n) (R X V : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ))
    (α e F : ℝ) (hα : 0<α) (he : 0<e) (hF : F ≤ α^2/256)
    (hscale : e*Real.sqrt (1+Real.log (n+2:ℕ))/(n+2:ℕ) ≤ α/2)
    (hX : 4*rowSq X ≤ F) :
    |energyGradient R α X V| ≤
      6*energyComparisonCoefficient n α e F*Real.sqrt (rowSq X)*Real.sqrt (rowSq V) := by
  let K:=energyComparisonCoefficient n α e F
  have hK : 0 ≤ K:=energyComparisonCoefficient_nonneg n α e F hα he
  have hX0:=rowSq_nonneg X
  have hV0:=rowSq_nonneg V
  have hbase : CenteredSingularLowerBound (α•R+X) (α/2):=by
    have hh:=(segment_geometry (show 3 ≤ n+2 by omega) R X hG α hα (by change rowSq X ≤ α^2/256; linarith) 1 ⟨by norm_num,le_rfl⟩).1
    simpa only [one_smul] using hh
  by_cases hzX : rowSq X=0
  · rw [rowSq_eq_zero X hzX,energyGradient_at_regular hn R V hG α hα,abs_zero]
    positivity
  by_cases hzV : rowSq V=0
  · have hz : V=0:=rowSq_eq_zero V hzV
    have hg:=energyGradient_smul R X V α (α/2) (by positivity) hbase 0
    simp only [zero_smul,zero_mul] at hg
    rw [hz,hg,abs_zero]
    positivity
  have hXp : 0<rowSq X:=lt_of_le_of_ne hX0 (Ne.symm hzX)
  have hVp : 0<rowSq V:=lt_of_le_of_ne hV0 (Ne.symm hzV)
  let t:=Real.sqrt (rowSq X)/Real.sqrt (rowSq V)
  have ht : 0<t:=div_pos (Real.sqrt_pos.mpr hXp) (Real.sqrt_pos.mpr hVp)
  have ht2 : t^2*rowSq V=rowSq X:=by
    dsimp only [t]
    rw [div_pow,Real.sq_sqrt hX0,Real.sq_sqrt hV0]
    field_simp
  have hZ : rowSq (t•V)=rowSq X:=by rw [rowSq_smul,ht2]
  have hpath (s : ℝ) (hs:s∈Icc (0:ℝ) 1) : rowSq (X+s•(t•V)) ≤ F := by
    have hh:=rowSq_add_le X (s•(t•V))
    have hss:=segment_rowEnergy_le (t•V) s hs
    change rowSq (s•(t•V)) ≤ rowSq (t•V) at hss
    rw [hZ] at hss
    linarith
  have hTaylor:=actual_taylor_abs_le hn R X (t•V) hG α e F hα he hF hscale hpath
  rw [hZ,energyGradient_smul R X V α (α/2) (by positivity) hbase t] at hTaylor
  have hQX:=reference_quadratic_abs_le hn R X hG α e F hα he hF hscale (by linarith)
  have hXZ : rowSq (X+t•V) ≤ 4*rowSq X:=by
    have hh:=rowSq_add_le X (t•V)
    rw [hZ] at hh
    linarith
  have hQZ: |energy R α (X+t•V)-energy R α 0| ≤ 4*K*rowSq X:=by
    have hh:=reference_quadratic_abs_le hn R (X+t•V) hG α e F hα he hF hscale (hXZ.trans hX)
    exact hh.trans (by dsimp only [K];nlinarith [mul_le_mul_of_nonneg_left hXZ hK])
  have hg : |t*energyGradient R α X V| ≤ 6*K*rowSq X:=by
    have hT:=abs_le.mp hTaylor
    have hQ:=abs_le.mp hQX
    have hZ':=abs_le.mp hQZ
    apply abs_le.mpr
    constructor <;> dsimp only [K] at * <;> linarith
  rw [abs_mul,abs_of_pos ht] at hg
  apply (mul_le_mul_iff_right₀ ht).mp
  have heq : t*(6*K*Real.sqrt (rowSq X)*Real.sqrt (rowSq V))=6*K*rowSq X:=by
    dsimp only [t]
    rw [div_mul_eq_mul_div]
    field_simp
    rw [Real.sq_sqrt hX0]
    ring
  rw [heq]
  exact hg

/-- The actual rectangle estimate: the change from `X` to `X+V` is
quadratic in `V` and bilinear in the sizes of `X` and `V`. The Taylor
remainder and the gradient have both been derived for the selected fan. -/
theorem actual_rectangle_abs_le (hn : 1 ≤ n) (R X V : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ))
    (α e F : ℝ) (hα : 0<α) (he : 0<e) (hF : F ≤ α^2/256)
    (hscale : e*Real.sqrt (1+Real.log (n+2:ℕ))/(n+2:ℕ) ≤ α/2)
    (hX : 4*rowSq X ≤ F)
    (hpath : ∀t∈Icc (0:ℝ) 1,rowSq (X+t•V) ≤ F) :
    |energy R α (X+V)-energy R α X| ≤
      energyComparisonCoefficient n α e F *
        (rowSq V+6*Real.sqrt (rowSq X)*Real.sqrt (rowSq V)) := by
  have ht:=actual_taylor_abs_le hn R X V hG α e F hα he hF hscale hpath
  have hg:=actual_gradient_abs_le hn R X V hG α e F hα he hF hscale hX
  have htt:=abs_le.mp ht
  have hgg:=abs_le.mp hg
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A scalar ball condition supplies every point on the rectangle segment. -/
theorem actual_rectangle_abs_le_of_rowSq (hn : 1 ≤ n)
    (R X V : Fin (n+2)→FSC.Coord d)
    (hG : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ))
    (α e F : ℝ) (hα : 0<α) (he : 0<e) (hF : F ≤ α^2/256)
    (hscale : e*Real.sqrt (1+Real.log (n+2:ℕ))/(n+2:ℕ) ≤ α/2)
    (hsize : 4*(rowSq X+rowSq V) ≤ F) :
    |energy R α (X+V)-energy R α X| ≤
      energyComparisonCoefficient n α e F *
        (rowSq V+6*Real.sqrt (rowSq X)*Real.sqrt (rowSq V)) := by
  have hx:=rowSq_nonneg X
  have hv:=rowSq_nonneg V
  apply actual_rectangle_abs_le hn R X V hG α e F hα he hF hscale (by linarith)
  intro t ht
  have hs:=segment_rowEnergy_le V t ht
  change rowSq (t•V) ≤ rowSq V at hs
  have ha:=rowSq_add_le X (t•V)
  linarith

end NegativeVotingNearRegularEnergyRectangle
