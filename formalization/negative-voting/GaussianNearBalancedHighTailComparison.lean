import GaussianNearBalancedSourceInputs
import GaussianRegularHighTailCrossSelected
import GaussianSignedHighTailComparison

/-! Actual near-balanced regular high-tail comparison. The mass path uses
literal selected offsets and the proved Gaussian Jacobian response. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter Matrix
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingNearBalancedHighTailComparison
open NegativeVotingNearBalancedSourceInputs NegativeVotingRegularHighTailCrossSelected
  NegativeVotingRegularHighTailCrossPath NegativeVotingRegularHighTailCrossAggregation
  NegativeVotingRegularTransportBound NegativeVotingFan NegativeVotingFanScore
  NegativeVotingFanSelectedOffsets NegativeVotingFanInverse NegativeVotingFanJacobian
  NegativeVotingNearRegularBalancedGeometry NegativeVotingNearRegularGraphGap
  NegativeVotingNearRegularNormalizedBounds NegativeVotingPathSmoothedComparison
  NegativeVotingStructuredResidualInputs NegativeVotingDisintegration NegativeVotingFacetDegree
  NegativeVotingWeightedFacet NegativeVotingCapTail NegativeVotingPolynomialFacetLogBound
  NegativeVotingFanRetained NegativeVotingBalancedMomentGeometry
  NegativeVotingStructuredSwitchingMoments NegativeVotingActualFacetOUTrace
  NegativeVotingRegularReferenceNormalization NegativeVotingCellOUContinuity
  NegativeVotingQuadraticMomentPadding NegativeVotingBoundedOUCellTests
  NegativeVotingOUResidualMoment NegativeVotingProjection NegativeVotingRareLabelHighChaos
  NegativeVotingNormalTrace NegativeVotingConditionalSecondMoment NegativeVotingHypercontractivity
  NegativeVotingSignedHighTailComparison OAI.MinUncut.GaussianHermite
variable {d m:ℕ} [NeZero m]

theorem near_mass_probability (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (p:Fin m→ℝ) (hp:∀ i,0< p i) (hs:∑ i,p i=1)
    (hlo:∀ i,1/(2*(m:ℝ))≤ p i) (i j:Fin m) (hij:i≠j) :
    (m:ℝ)^(-4096:ℝ)≤(stdGaussian (tangentSpace (pairNormal (α•R+D) i j))
      (intrinsicFacet (α•R+D) (selectedOffsets (α•R+D) p) i j)).toReal := by
  have hg:=segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hinj:Function.Injective (α•R+D):=fun a b heq=> by
    by_contra hab
    exact centered_singular_rows_ne _ (α/2) (by positivity) hg.1 a b hab heq
  have hmasses l:1/(2*(Fintype.card (Fin m):ℝ))≤ mass (α•R+D) (selectedOffsets (α•R+D) p) l := by
    rw [selectedOffsets_mass _ hinj p hp hs,Fintype.card_fin]
    exact hlo l
  have hh:=NegativeVotingConditionedFacetGeneral.intrinsicProbability_polynomial_lower
    (α•R+D) (by simpa only [Fintype.card_fin] using hm) (α/2) (2*α) (by positivity)
    (by positivity) hg.1 hg.2.2.2.2 (by field_simp; linarith)
    (selectedOffsets (α•R+D) p) (selectedOffsets (α•R+D) p).property hmasses i j hij
  simpa only [Fintype.card_fin,NegativeVotingConditionedFacet.intrinsicProbability] using hh

theorem near_mass_pairOffset (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (p:Fin m→ℝ) (hp:∀ i,0< p i) (hs:∑ i,p i=1)
    (hlo:∀ i,1/(2*(m:ℝ))≤ p i) (i j:Fin m) (hij:i≠j) :
    |pairOffset (α•R+D) (selectedOffsets (α•R+D) p) i j|≤2*Real.sqrt (1+Real.log (m:ℝ)) := by
  have hg:=segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hinj:Function.Injective (α•R+D):=fun a b heq=> by
    by_contra hab
    exact centered_singular_rows_ne _ (α/2) (by positivity) hg.1 a b hab heq
  have hmR:(1:ℝ)≤ m:=by exact_mod_cast (show 1≤ m by omega)
  have hm0:(0:ℝ)< m:=by linarith
  have hmasses l:1/(2*(m:ℝ))≤ mass (α•R+D) (selectedOffsets (α•R+D) p) l := by
    rw [selectedOffsets_mass _ hinj p hp hs];exact hlo l
  have hh:=pairOffset_sq_le_log_mass (α•R+D) (selectedOffsets (α•R+D) p) hinj
    (1/(2*(m:ℝ))) (by positivity) hmasses i j hij
  have heq:1/(1/(2*(m:ℝ)))=2*(m:ℝ):=by field_simp
  rw [heq,Real.log_mul (by norm_num) hm0.ne'] at hh
  have hl2:Real.log 2≤1:=by
    have hh:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
    linarith
  have hL:0≤1+Real.log (m:ℝ):=by positivity [Real.log_nonneg hmR]
  have hsqrt:=Real.sq_sqrt hL
  nlinarith [Real.sqrt_nonneg (1+Real.log (m:ℝ)),sq_abs (pairOffset (α•R+D) (selectedOffsets (α•R+D) p) i j),
    abs_nonneg (pairOffset (α•R+D) (selectedOffsets (α•R+D) p) i j)]

omit [NeZero m] in
theorem scaled_mass_error_bounds (v:centeredGauge (Fin m))
    (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ))) (t:ℝ) (ht:t∈Icc (0:ℝ) 1) :
    (∀ i,|((t•v:centeredGauge (Fin m)):Fin m→ℝ) i|≤1/(2*(m:ℝ))) ∧
    (∑ i,(((t•v:centeredGauge (Fin m)):Fin m→ℝ) i)^2)≤∑ i,((v:Fin m→ℝ) i)^2 := by
  have hpoint i:|t*(v:Fin m→ℝ) i|≤|(v:Fin m→ℝ) i| := by
    rw [abs_mul,abs_of_nonneg ht.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (abs_nonneg ((v:Fin m→ℝ) i))
  constructor
  · intro i;exact (hpoint i).trans (hv i)
  · apply Finset.sum_le_sum
    intro i _
    simpa only [sq_abs,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul] using pow_le_pow_left₀ (abs_nonneg _) (hpoint i) 2

def massPathEnergy (m:ℕ) (α e F Z:ℝ):ℝ :=
  (1+2*offsetCoefficient m α e)*F+2*((massGap m α e)⁻¹)^2*Z

def crossCoefficient (m:ℕ) (α τ σ e:ℝ):ℝ :=
  32*Real.exp 1*massDegree e*Real.sqrt (quarticLogConstant 2*(1+Real.log (m:ℝ))^4)*
    ((8*τ*Real.exp 2)*(2*σ^3*(Real.exp 1/(m:ℝ)))/α)

/-- Actual selected mass-path cross term, retaining the rare-label factor and
cubic high-mode gain. Both coefficient energies are derived, not assumed. -/
theorem near_mass_cross_abs_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hdim:2≤ Module.finrank ℝ (FSC.Coord d))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (τ σ q:ℝ) (hτ:0<τ) (hτ1:τ<1) (hσ:0<σ) (hσ1:σ<1)
    (hq:2≤ q) (hqt:q*τ^2≤1/2) (hqlog:4096*Real.log (m:ℝ)≤ q)
    (hτlog:τ^2*(1+Real.log (m:ℝ))≤1) :
    |testedFan (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)))
        (regularTailPotential R τ σ)-
      testedFan (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹))
        (regularTailPotential R τ σ)| ≤
      crossCoefficient m α τ σ e*
        massPathEnergy m α e (∑ i,‖D i‖^2) (∑ i,((v:Fin m→ℝ) i)^2) := by
  let B:=α•R+D
  let p₀:Fin m→ℝ:=fun _=>(m:ℝ)⁻¹
  let p:ℝ→Parameters d (Fin m):=fun t=>(B,(offsetLine B p₀ v t:Fin m→ℝ))
  let p':ℝ→Parameters d (Fin m):=fun t=>(0,((deriv (offsetLine B p₀ v) t:centeredGauge (Fin m)):Fin m→ℝ))
  let F:=∑ i,‖D i‖^2
  let Z:=∑ i,((v:Fin m→ℝ) i)^2
  let E:=massPathEnergy m α e F Z
  have hO:0≤ offsetCoefficient m α e:=by
    unfold offsetCoefficient quarticLogConstant
    positivity [degreeBound_pos e he,nearGap_pos (m:=m) α e hα he]
  have hF:0≤ F:=Finset.sum_nonneg fun i _=> sq_nonneg _
  have hZ:0≤ Z:=Finset.sum_nonneg fun i _=> sq_nonneg _
  have hE:0≤ E:=by dsimp [E,massPathEnergy];positivity
  have hmR:(1:ℝ)≤ m:=by exact_mod_cast (show 1≤ m by omega)
  have hm0:(0:ℝ)< m:=by linarith
  have hL:0≤1+Real.log (m:ℝ):=by positivity [Real.log_nonneg hmR]
  have hg:=segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have hp₀:∑ i,p₀ i=1:=by simp [p₀,NeZero.ne m]
  have hbox t (ht:t∈Icc (0:ℝ) 1):∀ i,1/(2*(m:ℝ))≤ massLine p₀ v t i ∧
      massLine p₀ v t i≤2/(m:ℝ):=uniform_massLine_box v hv t ht
  have hpos t (ht:t∈Icc (0:ℝ) 1):∀ i,0< massLine p₀ v t i:=fun i=>
    lt_of_lt_of_le (by positivity) (hbox t ht i).1
  have hp t (ht:t∈Icc (0:ℝ) 1):HasDerivAt p (p' t) t:=by
    have hc:=offsetLine_C1 B (α/2) (by positivity) hg.1 p₀ v hp₀ t (hpos t ht)
    have hd:HasDerivAt (offsetLine B p₀ v) (deriv (offsetLine B p₀ v) t) t:=
      (hc.differentiableAt (by norm_num)).hasDerivAt
    have hs:HasDerivAt (fun s:ℝ=>(offsetLine B p₀ v s:Fin m→ℝ))
        ((deriv (offsetLine B p₀ v) t:centeredGauge (Fin m)):Fin m→ℝ) t:=
      (centeredGauge (Fin m)).subtypeL.hasFDerivAt.comp_hasDerivAt t hd
    exact (hasDerivAt_const t B).prodMk hs
  have ha t (ht:t∈Icc (0:ℝ) 1) i j (hij:i≠j):
      |pairOffset (p t).1 (p t).2 i j|≤2*Real.sqrt (1+Real.log (m:ℝ)):=
    near_mass_pairOffset hm R D hG α hα hD (massLine p₀ v t) (hpos t ht)
      (massLine_sum p₀ v hp₀ t) (fun i=>(hbox t ht i).1) i j hij
  have hprob t (ht:t∈Icc (0:ℝ) 1) i j (hij:i≠j):
      (m:ℝ)^(-4096:ℝ)≤(stdGaussian (tangentSpace (pairNormal (p t).1 i j))
        (intrinsicFacet (p t).1 (p t).2 i j)).toReal:=
    near_mass_probability hm R D hG α hα hD (massLine p₀ v t) (hpos t ht)
      (massLine_sum p₀ v hp₀ t) (fun i=>(hbox t ht i).1) i j hij
  have hdeg t (ht:t∈Icc (0:ℝ) 1) i:(∑ j,facetWeight (p t).1 (p t).2 i j)≤ massDegree e:=by
    rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),facetWeight_self,add_zero]
    exact near_mass_degree hm R D hG α hα hD e he hscale (massLine p₀ v t)
      (hpos t ht) (massLine_sum p₀ v hp₀ t) (fun i=>(hbox t ht i).2) i
  have hnorm t (ht:t∈Icc (0:ℝ) 1) i j (hij:i≠j):
      quotientNormFactor τ q (pairOffset (p t).1 (p t).2 i j)≤8*τ*Real.exp 2:=by
    have hs:=pow_le_pow_left₀ (abs_nonneg _) (ha t ht i j hij) 2
    simp only [sq_abs,mul_pow,Real.sq_sqrt hL] at hs
    convert quotientNormFactor_log_le τ q (pairOffset (p t).1 (p t).2 i j)
      2 (1+Real.log (m:ℝ)) hτ hq hL hτlog hs using 1
    norm_num
  have herr t (ht:t∈Ico (0:ℝ) 1):rowScoreEnergy (fun i=>(p t).1 i-α•R i) (p t).2 0 0≤ E:=by
    have htc:t∈Icc (0:ℝ) 1:=⟨ht.1,ht.2.le⟩
    have hsc:=scaled_mass_error_bounds v hv t htc
    have ho:=near_balanced_selected_offset_sq_le hm R D hG α hα hD e he hscale (t•v) hsc.1
    have hc:=mul_le_mul_of_nonneg_left hsc.2 (show 0≤2*((massGap m α e)⁻¹)^2 by positivity)
    have heq:(fun i=>(p t).1 i-α•R i)=D:=by funext i;dsimp [p,B];abel
    rw [heq]
    dsimp only [rowScoreEnergy]
    simp only [sub_zero]
    change F+(∑ i,(offsetLine B p₀ v t:Fin m→ℝ) i^2)≤ E
    have hoff:(offsetLine B p₀ v t:Fin m→ℝ)=
      selectedOffsets B (p₀+((t•v:centeredGauge (Fin m)):Fin m→ℝ)):=rfl
    rw [hoff]
    dsimp only [E,massPathEnergy]
    nlinarith only [ho,hc]
  have hvel t (ht:t∈Ico (0:ℝ) 1):rowScoreEnergy (p' t).1 (p' t).2 0 0≤ E:=by
    have hh:=near_mass_response_sq_le hm R D hG α hα hD e he hscale v hv t ⟨ht.1,ht.2.le⟩
    dsimp only [rowScoreEnergy,p']
    simp only [Pi.zero_apply,sub_zero,norm_zero,zero_pow (by decide:2≠0),Finset.sum_const_zero,zero_add]
    apply hh.trans
    change ((massGap m α e)⁻¹)^2*Z≤ E
    have hz:0≤((massGap m α e)⁻¹)^2*Z:=by positivity
    have hf:0≤(1+2*offsetCoefficient m α e)*F:=by positivity
    dsimp only [E,massPathEnergy]
    linarith
  have hh:=regular_path_cross_abs_le p p' hp (α/2) (by positivity) (fun _ _=> hg.1) R hG hdim
    α τ σ q 2 1 (8*τ*Real.exp 2) (massDegree e) E E hα hτ hτ1 hσ hσ1 hq hqt
    (by nlinarith only [hτlog,sq_nonneg τ]) (by positivity) (massDegree_pos e he).le hE hE
    hdeg hprob (fun t ht i j hij=> probability_log_le_of_power _ (m:ℝ) q hmR (hprob t ht i j hij) hqlog)
    ha hnorm (fun _=>0) (fun _=>0) (fun _=>0) (fun _=>0) herr hvel
  simp only [mul_assoc] at hh
  rw [Real.mul_self_sqrt hE] at hh
  simpa only [p,offsetLine,massLine,zero_smul,one_smul,add_zero,p₀,E,F,Z,crossCoefficient,mul_assoc] using hh


theorem smoothed_cellDifference_eq_potential_difference_three
    (p₀ p₁ : Parameters d (Fin m)) (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (h₀ : CenteredSingularLowerBound p₀.1 s₀) (h₁ : CenteredSingularLowerBound p₁.1 s₁)
    (k:ℕ) (hk:k≤3) (i : Fin m) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    smoothedHighModes (-r) k (cellDifference p₀ p₁ i)=
      smoothedHighModes (-r) k ((winningCell p₁.1 p₁.2 i).indicator (fun _ => 1))-
        smoothedHighModes (-r) k ((winningCell p₀.1 p₀.2 i).indicator (fun _ => 1)) := by
  have hra : |-r| < 1 := by rwa [abs_neg,abs_of_pos hr]
  let f := cellWeight p₁.1 p₁.2 i
  let g := cellWeight p₀.1 p₀.2 i
  have hfM := cellWeight_measurable p₁.1 p₁.2 i
  have hgM := cellWeight_measurable p₀.1 p₀.2 i
  have hf := cellWeight_memLp p₁.1 p₁.2 i
  have hg := cellWeight_memLp p₀.1 p₀.2 i
  have hcD := highModes_continuous_quadratic_of_average (-r) hra.le k hk
    (coordinateCellDifference p₀ p₁ i) (coordinateCellDifference_measurable p₀ p₁ i)
    (gaussianAverage_cellDifference_continuous p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i (-r) hra)
    2 (by norm_num) (coordinateCellDifference_abs_le p₀ p₁ i)
  have hcf := highModes_continuous_quadratic_of_average (-r) hra.le k hk f hfM
    (gaussianAverage_cellWeight_continuous p₁.1 s₁ hs₁ h₁ p₁.2 i (-r) hra)
    1 (by norm_num) (cellWeight_abs_le p₁.1 p₁.2 i)
  have hcg := highModes_continuous_quadratic_of_average (-r) hra.le k hk g hgM
    (gaussianAverage_cellWeight_continuous p₀.1 s₀ hs₀ h₀ p₀.2 i (-r) hra)
    1 (by norm_num) (cellWeight_abs_le p₀.1 p₀.2 i)
  have hleft : Continuous (gaussianAverage (-r) (highModes k (f-g))) :=
    hcD.1.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have hright : Continuous (gaussianAverage (-r) (highModes k f)-gaussianAverage (-r) (highModes k g)) :=
    (hcf.1.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))).sub
      (hcg.1.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)))
  let : (gaussianReal 0 1).IsOpenPosMeasure := GaussianFin.instIsOpenPosMeasureγ
  let : (γFin d).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure (fun _ : Fin d => gaussianReal 0 1)
  have he := (Continuous.ae_eq_iff_eq (γFin d) hleft hright).mp
    (negative_highModes_difference_ae hr hr1 k f g hf hg)
  funext x
  have hx := congrFun he x.ofLp
  change gaussianAverage (-r) (highModes k (coordinateCellDifference p₀ p₁ i)) x.ofLp=
    gaussianAverage (-r) (highModes k (cellWeight p₁.1 p₁.2 i)) x.ofLp-
      gaussianAverage (-r) (highModes k (cellWeight p₀.1 p₀.2 i)) x.ofLp at hx
  change ambientAverage (-r) (ambientHighModes k (cellDifference p₀ p₁ i)) x=
    ambientAverage (-r) (ambientHighModes k ((winningCell p₁.1 p₁.2 i).indicator (fun _ => 1))) x-
      ambientAverage (-r) (ambientHighModes k ((winningCell p₀.1 p₀.2 i).indicator (fun _ => 1))) x
  simp only [ambientAverage_eq_gaussianAverage]
  exact hx


/-- Exact cell-source additivity through an intermediate cell system. -/
theorem smoothed_cells_add (p₀ p₁ p₂:Parameters d (Fin m))
    (s₀ s₁ s₂:ℝ) (hs₀:0< s₀) (hs₁:0< s₁) (hs₂:0< s₂)
    (h₀:CenteredSingularLowerBound p₀.1 s₀) (h₁:CenteredSingularLowerBound p₁.1 s₁)
    (h₂:CenteredSingularLowerBound p₂.1 s₂)
    (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ<1) (k:ℕ) (hk:k≤3) (i:Fin m) :
    smoothedHighModes (-ρ) k (cellDifference p₀ p₂ i)=
      smoothedHighModes (-ρ) k (cellDifference p₀ p₁ i)+
        smoothedHighModes (-ρ) k (cellDifference p₁ p₂ i) := by
  rw [smoothed_cellDifference_eq_potential_difference_three p₀ p₂ s₀ s₂ hs₀ hs₂ h₀ h₂ k hk i ρ hρ hρ1,
    smoothed_cellDifference_eq_potential_difference_three p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ k hk i ρ hρ hρ1,
    smoothed_cellDifference_eq_potential_difference_three p₁ p₂ s₁ s₂ hs₁ hs₂ h₁ h₂ k hk i ρ hρ hρ1]
  abel

theorem smoothed_cells_sq_triangle (p₀ p₁ p₂:Parameters d (Fin m))
    (s₀ s₁ s₂:ℝ) (hs₀:0< s₀) (hs₁:0< s₁) (hs₂:0< s₂)
    (h₀:CenteredSingularLowerBound p₀.1 s₀) (h₁:CenteredSingularLowerBound p₁.1 s₁)
    (h₂:CenteredSingularLowerBound p₂.1 s₂)
    (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ<1) (k:ℕ) (hk:k≤3) :
    (∑ i,∫ x,(smoothedHighModes ρ k (cellDifference p₀ p₂ i) x)^2 ∂stdGaussian (FSC.Coord d)) ≤
      2*(∑ i,∫ x,(smoothedHighModes ρ k (cellDifference p₀ p₁ i) x)^2 ∂stdGaussian (FSC.Coord d))+
      2*(∑ i,∫ x,(smoothedHighModes ρ k (cellDifference p₁ p₂ i) x)^2 ∂stdGaussian (FSC.Coord d)) := by
  simp_rw [←smoothedHighModes_neg_integral_sq ρ]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  have hra:|-ρ|≤1:=by rw [abs_neg,abs_of_pos hρ];exact hρ1.le
  apply Finset.sum_le_sum
  intro i _
  have hf:=smoothedHighModes_memLp (-ρ) hra k _ (cellDifference_measurable p₀ p₁ i) (cellDifference_memLp p₀ p₁ i)
  have hg:=smoothedHighModes_memLp (-ρ) hra k _ (cellDifference_measurable p₁ p₂ i) (cellDifference_memLp p₁ p₂ i)
  have hh:=smoothedHighModes_memLp (-ρ) hra k _ (cellDifference_measurable p₀ p₂ i) (cellDifference_memLp p₀ p₂ i)
  calc
    _ ≤ ∫ x,2*(smoothedHighModes (-ρ) k (cellDifference p₀ p₁ i) x)^2+
        2*(smoothedHighModes (-ρ) k (cellDifference p₁ p₂ i) x)^2 ∂stdGaussian (FSC.Coord d) := by
      apply integral_mono hh.integrable_sq ((hf.integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2))
      intro x
      rw [smoothed_cells_add p₀ p₁ p₂ s₀ s₁ s₂ hs₀ hs₁ hs₂ h₀ h₁ h₂ ρ hρ hρ1 k hk i]
      change (smoothedHighModes (-ρ) k (cellDifference p₀ p₁ i) x+
        smoothedHighModes (-ρ) k (cellDifference p₁ p₂ i) x)^2≤
          2*(smoothedHighModes (-ρ) k (cellDifference p₀ p₁ i) x)^2+
          2*(smoothedHighModes (-ρ) k (cellDifference p₁ p₂ i) x)^2
      nlinarith [sq_nonneg (smoothedHighModes (-ρ) k (cellDifference p₀ p₁ i) x-
        smoothedHighModes (-ρ) k (cellDifference p₁ p₂ i) x)]
    _ = _ := by
      rw [integral_add (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2),integral_const_mul,integral_const_mul]

def selfCoefficient (m:ℕ) (α e F Z:ℝ):ℝ :=
  64*Real.exp 1*max 1 (degreeBound e)*degreeBound e*quarticLogConstant 2*(1+Real.log (m:ℝ))^4*F+
  16*Real.exp 1*max 1 (massDegree e)*(massGap m α e)⁻¹*Z

/-- Full near-balanced actual smoothed high-mode comparison for every k≤3. -/
theorem near_balanced_smoothed_sq_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (τ σ q:ℝ) (hτ:0<τ) (hσ:0<σ) (hσ1:σ<1)
    (hq:2≤ q) (ht:τ^2=1/(2*q-1)) (hqlog:Real.log ((m:ℝ)/(α/2))≤ q)
    (k:ℕ) (hk:k≤3) :
    (∑ i,∫ x,(smoothedHighModes (τ*σ) k (cellDifference
      (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
      (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ))) i) x)^2
        ∂stdGaussian (FSC.Coord d)) ≤
      (σ^2)^k*selfCoefficient m α e (∑ i,‖D i‖^2) (∑ i,((v:Fin m→ℝ) i)^2) := by
  have hτ1:τ<1:=by
    have :1/(2*q-1)<1:=(div_lt_iff₀ (by linarith)).mpr (by linarith)
    nlinarith
  have hprod:τ*σ<1:=(mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)
  have hg:=segment_geometry hm R D hG α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  have htri:=smoothed_cells_sq_triangle
    (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
    (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹))
    (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)))
    α (α/2) (α/2) hα (by positivity) (by positivity)
    (regular_scaled_singular R hG α) hg.1 hg.1 (τ*σ) (mul_pos hτ hσ) hprod k hk
  have hrow:=near_regular_selected_smoothed_difference_l2_sq_le hm R D hG α hα hD e he hscale
    τ σ q hτ hσ hσ1 hq ht hqlog k hk
  have hmass:=near_mass_smoothed_difference_l2_sq_le hm R D hG α hα hD e he hscale v hv
    τ σ q hτ hσ hσ1 hq ht hqlog k hk
  apply htri.trans
  convert add_le_add (mul_le_mul_of_nonneg_left hrow (show (0:ℝ)≤2 by norm_num))
    (mul_le_mul_of_nonneg_left hmass (show (0:ℝ)≤2 by norm_num)) using 1
  dsimp only [selfCoefficient,degreeBound]
  ring


def rowCrossCoefficient (m:ℕ) (α τ σ e:ℝ):ℝ :=
  32*Real.exp 1*degreeBound e*Real.sqrt (quarticLogConstant 2*(1+Real.log (m:ℝ))^4)*
    ((8*τ*Real.exp 2)*(2*σ^3*(Real.exp 1/(m:ℝ)))/α)

def fullCrossBound (m:ℕ) (α τ σ e F Z:ℝ):ℝ :=
  rowCrossCoefficient m α τ σ e*(1+offsetCoefficient m α e)*F+
    crossCoefficient m α τ σ e*massPathEnergy m α e F Z

/-- The row and mass paths together give the actual near-balanced cross term. -/
theorem near_balanced_cross_abs_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hdim:2≤ Module.finrank ℝ (FSC.Coord d))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0< e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (τ σ q:ℝ) (hτ:0<τ) (hτ1:τ<1) (hσ:0<σ) (hσ1:σ<1)
    (hq:2≤ q) (hqt:q*τ^2≤1/2) (hqlog:4096*Real.log (m:ℝ)≤ q)
    (hτlog:τ^2*(1+Real.log (m:ℝ))≤1) :
    |testedFan (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)))
        (regularTailPotential R τ σ)-
      testedFan (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
        (regularTailPotential R τ σ)| ≤
      fullCrossBound m α τ σ e (∑ i,‖D i‖^2) (∑ i,((v:Fin m→ℝ) i)^2) := by
  have hr:=near_regular_selected_cross_abs_le hm R D hG hdim α hα hD e he hscale
    τ σ q hτ hτ1 hσ hσ1 hq hqt hqlog hτlog
  have hvary:=near_mass_cross_abs_le hm R D hG hdim α hα hD e he hscale v hv
    τ σ q hτ hτ1 hσ hσ1 hq hqt hqlog hτlog
  have hh:=abs_sub_le
    (testedFan (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ))) (regularTailPotential R τ σ))
    (testedFan (α•R+D,selectedOffsets (α•R+D) (fun _=>(m:ℝ)⁻¹)) (regularTailPotential R τ σ))
    (testedFan (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹)) (regularTailPotential R τ σ))
  apply hh.trans
  convert add_le_add hvary hr using 1
  dsimp only [fullCrossBound,rowCrossCoefficient]
  ring

/-- Coordinate and ambient tested-cell pairings agree exactly. -/
theorem testedFan_eq_coordinate_pairing (p:Parameters d (Fin m)) (F:Fin m→FSC.Coord d→ℝ) :
    testedFan p F=∑ i,∫ x,cellWeight p.1 p.2 i x*F i (WithLp.toLp 2 x) ∂γFin d := by
  unfold testedFan
  apply Finset.sum_congr rfl
  intro i _
  rw [←integral_indicator (winningCell_measurable p.1 p.2 i),
    ←(gaussian_toLp_measurePreserving d).integral_comp'
      ((winningCell p.1 p.2 i).indicator (F i))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx:WithLp.toLp 2 x∈winningCell p.1 p.2 i <;> simp [cellWeight,hx]

def cellTailEnergy (ρ:ℝ) (k:ℕ) (p:Parameters d (Fin m)):ℝ :=
  ∑ i,energyPairing ρ k (cellWeight p.1 p.2 i)

/-- Exact infinite-mode polarization, with the actual regular fixed potential
and the actual difference of the two cell indicator families. -/
theorem cellTailEnergy_difference (R:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α:ℝ) (hα:0<α) (p:Parameters d (Fin m))
    (τ σ:ℝ) (hτ:0<τ) (hτ1:τ<1) (hσ:0<σ) (hσ1:σ<1) :
    cellTailEnergy (-(τ^2*σ)) 3 p-
      cellTailEnergy (-(τ^2*σ)) 3 (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹)) =
      2*(testedFan p (regularTailPotential R τ σ)-
        testedFan (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹)) (regularTailPotential R τ σ))+
      ∑ i,energyPairing (-(τ^2*σ)) 3
        (coordinateCellDifference (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹)) p i) := by
  let p₀:Parameters d (Fin m):=(α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
  have hr:0<τ^2*σ:=by positivity
  have hr1:τ^2*σ<1:=by nlinarith
  have hbase i:cellWeight p₀.1 p₀.2 i=cellWeight R 0 i:=by
    change cellWeight (α•R) (selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹)) i=_
    rw [selected_regular_scaled_zero R hG α hα]
    unfold cellWeight
    rw [winningCell_scaled_zero R α hα]
  have hraw i:(fun x:Fin d→ℝ=> regularTailPotential R τ σ i (WithLp.toLp 2 x))=
      gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight p₀.1 p₀.2 i)):=by
    rw [hbase]
    rfl
  have hav i:=gaussianAverage_memLp_signed (-(τ^2*σ))
    (show |-(τ^2*σ)|≤1 by rw [abs_neg,abs_of_pos hr];exact hr1.le)
    (highModes 3 (cellWeight p₀.1 p₀.2 i))
    (highModes_measurable _ _ (cellWeight_measurable _ _ i))
    (highModes_memLp _ _ (cellWeight_memLp _ _ i))
  have hcross i:(∫ x,(cellWeight p.1 p.2 i x-cellWeight p₀.1 p₀.2 i x)*
      gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight p₀.1 p₀.2 i)) x ∂γFin d)=
      (∫ x,cellWeight p.1 p.2 i x*regularTailPotential R τ σ i (WithLp.toLp 2 x) ∂γFin d)-
      ∫ x,cellWeight p₀.1 p₀.2 i x*regularTailPotential R τ σ i (WithLp.toLp 2 x) ∂γFin d := by
    simp_rw [sub_mul]
    have hIp : Integrable (fun x => cellWeight p.1 p.2 i x *
        gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight p₀.1 p₀.2 i)) x) (γFin d) :=
      (cellWeight_memLp p.1 p.2 i).integrable_mul (hav i)
    have hI₀ : Integrable (fun x => cellWeight p₀.1 p₀.2 i x *
        gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight p₀.1 p₀.2 i)) x) (γFin d) :=
      (cellWeight_memLp p₀.1 p₀.2 i).integrable_mul (hav i)
    rw [integral_sub hIp hI₀]
    simp_rw [←hraw]
  have hpol i:=energyPairing_difference (τ^2*σ) hr hr1 3
    (cellWeight p.1 p.2 i) (cellWeight p₀.1 p₀.2 i)
    (cellWeight_measurable _ _ i) (cellWeight_measurable _ _ i)
    (cellWeight_memLp _ _ i) (cellWeight_memLp _ _ i)
  change (∑ i,energyPairing (-(τ^2*σ)) 3 (cellWeight p.1 p.2 i))-
    (∑ i,energyPairing (-(τ^2*σ)) 3 (cellWeight p₀.1 p₀.2 i)) = _
  rw [←Finset.sum_sub_distrib]
  simp_rw [hpol]
  simp_rw [hcross]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_sub_distrib,
    ←testedFan_eq_coordinate_pairing,←testedFan_eq_coordinate_pairing]
  rfl

/-- The actual coordinate signed remainder is controlled by its ambient
smoothed square. No finite chaos truncation or facet restriction occurs. -/
theorem cellDifference_energy_abs_le (p₀ p₁:Parameters d (Fin m))
    (s:ℝ) (hs:0<s) (hs1:s<1) (k:ℕ) :
    |∑ i,energyPairing (-(s^2)) k (coordinateCellDifference p₀ p₁ i)| ≤
      ∑ i,∫ x,(smoothedHighModes s k (cellDifference p₀ p₁ i) x)^2
        ∂stdGaussian (FSC.Coord d) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hh:=energyPairing_neg_sq_abs_le s hs hs1 k (coordinateCellDifference p₀ p₁ i)
    (coordinateCellDifference_measurable p₀ p₁ i) (coordinateCellDifference_memLp p₀ p₁ i)
  apply hh.trans_eq
  rw [←(gaussian_toLp_measurePreserving d).integral_comp'
    (fun x=>(smoothedHighModes s k (cellDifference p₀ p₁ i) x)^2)]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  exact (ambientAverage_eq_gaussianAverage s (ambientHighModes k (cellDifference p₀ p₁ i))
    (WithLp.toLp 2 x)).symm

/-- Full near-balanced signed high-tail comparison, including the actual
mass displacement. Both the cross term and quadratic remainder are derived
from the selected cells. -/
theorem near_balanced_signed_tail_abs_le (hm:3 ≤ m) (R D:Fin m→FSC.Coord d)
    (hG:∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hdim:2≤ Module.finrank ℝ (FSC.Coord d))
    (α:ℝ) (hα:0<α) (hD:∑ i,‖D i‖^2≤α^2/256)
    (e:ℝ) (he:0<e) (hscale:e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ)≤α/2)
    (v:centeredGauge (Fin m)) (hv:∀ i,|(v:Fin m→ℝ) i|≤1/(2*(m:ℝ)))
    (τ σ q:ℝ) (hτ:0<τ) (hσ:0<σ) (hσ1:σ<1)
    (hq:2≤q) (ht:τ^2=1/(2*q+1))
    (hqlog:4096*Real.log (m:ℝ)≤q)
    (hτlog:τ^2*(1+Real.log (m:ℝ))≤1)
    (htraceLog:Real.log ((m:ℝ)/(α/2))≤q+1) :
    |cellTailEnergy (-(τ^2*σ)) 3
        (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)))-
      cellTailEnergy (-(τ^2*σ)) 3
        (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))| ≤
      2*fullCrossBound m α τ σ e (∑ i,‖D i‖^2) (∑ i,((v:Fin m→ℝ) i)^2)+
        σ^3*selfCoefficient m α e (∑ i,‖D i‖^2) (∑ i,((v:Fin m→ℝ) i)^2) := by
  have hτ1:τ<1:=by
    have :1/(2*q+1)<1:=(div_lt_iff₀ (by linarith)).mpr (by linarith)
    nlinarith
  have hqt:q*τ^2≤1/2:=by
    rw [ht,mul_one_div]
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hroot:0<Real.sqrt σ:=Real.sqrt_pos.mpr hσ
  have hroot1:Real.sqrt σ<1:=by nlinarith [Real.sq_sqrt hσ.le]
  have hs:τ*Real.sqrt σ<1:=
    (mul_lt_mul_of_pos_left hroot1 hτ).trans (by simpa using hτ1)
  have heq:(τ*Real.sqrt σ)^2=τ^2*σ:=by rw [mul_pow,Real.sq_sqrt hσ.le]
  have hcross:=near_balanced_cross_abs_le hm R D hG hdim α hα hD e he hscale v hv
    τ σ q hτ hτ1 hσ hσ1 hq hqt hqlog hτlog
  have hself:=cellDifference_energy_abs_le
    (α•R,selectedOffsets (α•R) (fun _=>(m:ℝ)⁻¹))
    (α•R+D,selectedOffsets (α•R+D) ((fun _=>(m:ℝ)⁻¹)+(v:Fin m→ℝ)))
    (τ*Real.sqrt σ) (mul_pos hτ hroot) hs 3
  rw [heq] at hself
  have hsmooth:=near_balanced_smoothed_sq_le hm R D hG α hα hD e he hscale v hv
    τ (Real.sqrt σ) (q+1) hτ hroot hroot1 (by linarith)
    (by convert ht using 1; ring) htraceLog 3 le_rfl
  rw [Real.sq_sqrt hσ.le] at hsmooth
  rw [cellTailEnergy_difference R hG α hα _ τ σ hτ hτ1 hσ hσ1]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_pos (show (0:ℝ)<2 by norm_num)]
  exact add_le_add (mul_le_mul_of_nonneg_left hcross (by norm_num)) (hself.trans hsmooth)

end NegativeVotingNearBalancedHighTailComparison
