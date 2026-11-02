import GaussianOwnCentroidSpectralReplacement

/-! Integration of the actual own-centroid routing bound.  The selected fan
is the literal Gaussian winning fan, and all ties are removed by the actual
Gaussian injectivity theorem. No final noise inequality is a premise. -/
noncomputable section
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace Classical
namespace NegativeVotingOwnCentroidLocalReplacement
open NegativeVoting NegativeVotingAffine NegativeVotingModern NegativeVotingFan
  NegativeVotingFanScore NegativeVotingFanTestedCells NegativeVotingCapTail
  NegativeVotingOwnCentroidRoutingCap NegativeVotingOwnCentroidSpectralReplacement
  NegativeVotingQuadraticMomentPadding NegativeVotingBalancedReference
  NegativeVotingStructuredResidualInputs NegativeVotingActualFacetOUTrace
  NegativeVotingProjection NegativeVotingRareLabelHighChaos NegativeVotingHypercontractivity
  NegativeVotingSwitchingOrdered NegativeVotingPathSmoothedComparison
  NegativeVotingDisintegration NegativeVotingCenteredParseval NegativeVotingCellOUContinuity
  NegativeVotingFacetDegree
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

theorem cellWeight_eq_winner_ae (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) :
    ∀ᵐ y ∂γFin d, ∀ i, cellWeight B h i y=
      if i=affineWinner B h (WithLp.toLp 2 y) then 1 else 0 := by
  have hmap : MeasurePreserving (WithLp.toLp 2) (γFin d) (stdGaussian (FSC.Coord d)) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have hi := hmap.quasiMeasurePreserving.ae (ae_scores_injective B hB h)
  filter_upwards [hi] with y hy i
  let x : FSC.Coord d:=WithLp.toLp 2 y
  let t := affineWinner B h x
  have ht j : affineScore B h j x ≤ affineScore B h t x := affineWinner_mem_cell B h x j
  by_cases hit : i=t
  · subst i
    change (winningCell B h t).indicator (fun _ => (1:ℝ)) x=if t=t then 1 else 0
    rw [Set.indicator_of_mem (show x∈winningCell B h t from ht),ite_eq_left rfl]
  · have hn : x∉winningCell B h i := by
      intro hi
      have he : scores B h x i=scores B h x t := le_antisymm (ht i) (hi t)
      exact hit (hy he)
    change (winningCell B h i).indicator (fun _ => (1:ℝ)) x=_
    rw [Set.indicator_of_notMem hn,ite_eq_right hit]

theorem cellWeight_simplex_ae (B : ι → FSC.Coord d) (hB : Function.Injective B)
    (h : ι → ℝ) :
    ∀ᵐ y ∂γFin d, SimplexWeights (fun i => cellWeight B h i y) := by
  filter_upwards [cellWeight_eq_winner_ae B hB h] with y hy
  constructor
  · intro i;change 0 ≤ cellWeight B h i y
    rw [hy i];split_ifs <;> norm_num
  · simp only [hy,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The finite routing integrand has no winner-measurability premise: its
almost-everywhere equality to two ordinary score mixtures proves integrability. -/
theorem integral_routing_potential_lower {n : ℕ} (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (R D : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : Fin (n+2) → ℝ) (hB : Function.Injective (referenceScale n•R+D))
    (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2)
    (a : FSC.Coord d → Fin (n+2) → ℝ)
    (Q : (Fin d → ℝ) → Fin (n+2) → ℝ) (c : ℝ)
    (hQ : ∀ x i,correctedRegularPotential R r a x i=c+Q x.ofLp i)
    (hQL2 : ∀ i,MemLp (fun y => Q y i) 2 (γFin d))
    (f : (Fin d → ℝ) → Fin (n+2) → ℝ)
    (hfM : ∀ i,Measurable (fun y => f y i))
    (hfs : ∀ᵐ y ∂γFin d,SimplexWeights (f y))
    (hmoment : ∀ i j,momentMatrix f i j=((referenceScale n•R+D) i).ofLp j)
    (hmass : ∀ i,(∫ y,f y i ∂γFin d)=∫ y,cellWeight (referenceScale n•R+D) h i y ∂γFin d)
    (hcap : Integrable (closedCellCap (referenceScale n•R+D) h (pairForcing R D h r a) 1)
      (stdGaussian (FSC.Coord d))) :
    -r*(∫ x,closedCellCap (referenceScale n•R+D) h (pairForcing R D h r a) 1 x
      ∂stdGaussian (FSC.Coord d)) ≤
      r*centroidRouting f (fun y i => cellWeight (referenceScale n•R+D) h i y)+
        ∑ i,∫ y,(f y i-cellWeight (referenceScale n•R+D) h i y)*Q y i ∂γFin d := by
  let B:=referenceScale n•R+D
  let g : (Fin d → ℝ) → Fin (n+2) → ℝ:=fun y i => cellWeight B h i y
  let S : (Fin d → ℝ) → Fin (n+2) → ℝ:=affineScores (momentMatrix f) h
  let J : (Fin d → ℝ) → ℝ:=fun y =>
    r*((∑ i,g y i*S y i)-(∑ i,f y i*S y i))+∑ i,(f y i-g y i)*Q y i
  have hf i : MemLp (fun y => f y i) 2 (γFin d) := by
    apply MemLp.of_bound (hfM i).aestronglyMeasurable 1
    filter_upwards [hfs] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (hy.1 i)]
    exact simplex_weight_le_one _ hy i
  have hg i : MemLp (fun y => g y i) 2 (γFin d):=cellWeight_memLp B h i
  have hgM i : Measurable (fun y => g y i):=cellWeight_measurable B h i
  have hgs : ∀ᵐ y ∂γFin d,SimplexWeights (g y):=cellWeight_simplex_ae B hB h
  have hroute := cellWeight_eq_winner_ae B hB h
  have hSi (y : Fin d → ℝ) (i : Fin (n+2)) : S y i=affineScore B h i (WithLp.toLp 2 y) := by
    simp only [S,affineScores,hmoment,affineScore,PiLp.inner_apply,Real.inner_apply,B]
  have hJI : Integrable J (γFin d) :=
    ((integrable_affine_mixture _ h g (fun i => (hgM i).aemeasurable) hgs).sub
      (integrable_affine_mixture _ h f (fun i => (hfM i).aemeasurable) hfs)).const_mul r |>.add
      (integrable_finsetSum Finset.univ (fun i _ => ((hf i).sub (hg i)).integrable_mul (hQL2 i)))
  have hmap : MeasurePreserving (WithLp.toLp 2) (γFin d) (stdGaussian (FSC.Coord d)) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have hcapC := hmap.integrable_comp_of_integrable hcap
  have hp : ∀ᵐ y ∂γFin d,
      -r*closedCellCap B h (pairForcing R D h r a) 1 (WithLp.toLp 2 y) ≤ J y := by
    filter_upwards [hfs,hroute] with y hy hgy
    have hh := fractional_routing_lower hn hmean R D hG h r hr hrhalf a
      (WithLp.toLp 2 y) (f y) hy
    change -r*closedCellCap B h (pairForcing R D h r a) 1 (WithLp.toLp 2 y) ≤
      ∑ j,f y j*(r*(affineScore B h (affineWinner B h (WithLp.toLp 2 y)) (WithLp.toLp 2 y)-
        affineScore B h j (WithLp.toLp 2 y))+correctedRegularPotential R r a (WithLp.toLp 2 y) j-
        correctedRegularPotential R r a (WithLp.toLp 2 y) (affineWinner B h (WithLp.toLp 2 y))) at hh
    simp_rw [hQ,← hSi] at hh
    have he : (∑ j,f y j*(r*(S y (affineWinner B h (WithLp.toLp 2 y))-S y j)+
        (c+Q y j)-(c+Q y (affineWinner B h (WithLp.toLp 2 y)))))=J y := by
      calc
        _=(∑ j, f y j*(r*S y (affineWinner B h (WithLp.toLp 2 y)))-
          r*(∑ j,f y j*S y j))+(∑ j,f y j*Q y j)-
            ∑ j,f y j*Q y (affineWinner B h (WithLp.toLp 2 y)) := by
          simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _=J y := by
          rw [← Finset.sum_mul,← Finset.sum_mul,hy.2,one_mul,one_mul]
          dsimp only [J]
          simp only [g,hgy,sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul,
            Finset.sum_ite_eq',Finset.mem_univ,ite_true]
          ring
    rw [he] at hh
    exact hh
  have hi := integral_mono_ae (hcapC.const_mul (-r)) hJI hp
  have hrouteEq := centroidRouting_eq_affine_integral f g h
    (fun i => (hfM i).aemeasurable) (fun i => (hgM i).aemeasurable) hfs hgs hmass
  have hJIeq : (∫ y,J y ∂γFin d)=r*centroidRouting f g+
      ∑ i,∫ y,(f y i-g y i)*Q y i ∂γFin d := by
    rw [hrouteEq]
    unfold J
    rw [integral_add,integral_const_mul,integral_finsetSum]
    · rfl
    · intro i _;exact ((hf i).sub (hg i)).integrable_mul (hQL2 i)
    · exact ((integrable_affine_mixture _ h g (fun i => (hgM i).aemeasurable) hgs).sub
        (integrable_affine_mixture _ h f (fun i => (hfM i).aemeasurable) hfs)).const_mul r
    · exact integrable_finsetSum Finset.univ (fun i _ => ((hf i).sub (hg i)).integrable_mul (hQL2 i))
  rw [hJIeq,integral_const_mul] at hi
  have hcapEq : (∫ y,closedCellCap B h (pairForcing R D h r a) 1 (WithLp.toLp 2 y) ∂γFin d)=
      ∫ x,closedCellCap B h (pairForcing R D h r a) 1 x ∂stdGaussian (FSC.Coord d) := by
    exact integral_standardGaussian_eq_euclidean (κ:=Fin d)
      (fun y => closedCellCap B h (pairForcing R D h r a) 1 (WithLp.toLp 2 y))
  change -r*(∫ y,closedCellCap B h (pairForcing R D h r a) 1 (WithLp.toLp 2 y) ∂γFin d) ≤ _ at hi
  rw [hcapEq] at hi
  exact hi

def actualOddSource (s : ℝ) (f : (Fin d → ℝ) → ι → ℝ)
    (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) : FSC.Coord d → ℝ :=
  projectedOddResidual s (fun x => f x.ofLp i-cellWeight B h i x.ofLp)

omit [Fintype ι] [Nonempty ι] in
theorem actualOddSource_coordinate (s : ℝ) (f : (Fin d → ℝ) → ι → ℝ)
    (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) (x : FSC.Coord d) :
    actualOddSource s f B h i x=
      gaussianAverage s (oddHighModes (fun y => f y i-cellWeight B h i y)) x.ofLp := by
  unfold actualOddSource projectedOddResidual
  rw [ambientAverage_eq_gaussianAverage]
  rfl

omit [Fintype ι] [Nonempty ι] in
theorem actualOddSource_second_average (s : ℝ) (f : (Fin d → ℝ) → ι → ℝ)
    (B : ι → FSC.Coord d) (h : ι → ℝ) (i : ι) (x : FSC.Coord d) :
    ambientAverage s (actualOddSource s f B h i) x=
      gaussianAverage s (gaussianAverage s (oddHighModes (fun y => f y i-cellWeight B h i y))) x.ofLp := by
  rw [ambientAverage_eq_gaussianAverage]
  simp only [actualOddSource_coordinate]

theorem actualOddSource_memLp_and_square (s : ℝ) (hs : |s| ≤ 1)
    (f : (Fin d → ℝ) → ι → ℝ) (B : ι → FSC.Coord d) (h : ι → ℝ)
    (hfM : ∀ i,Measurable (fun y=>f y i))
    (hf : ∀ i,MemLp (fun y=>f y i) 2 (γFin d)) (i : ι) :
    Measurable (actualOddSource s f B h i) ∧
    MemLp (actualOddSource s f B h i) 2 (stdGaussian (FSC.Coord d)) ∧
    (NegativeVotingStructuredSwitchingMoments.realLp (stdGaussian (FSC.Coord d)) 2 (actualOddSource s f B h i))^2=
      ∫ y,(gaussianAverage s (oddHighModes (fun z=>f z i-cellWeight B h i z)) y)^2 ∂γFin d := by
  have huM : Measurable (actualOddSource s f B h i) :=
    projectedOddResidual_measurable s _
      (((hfM i).comp (by fun_prop)).sub ((cellWeight_measurable B h i).comp (by fun_prop)))
  have hv := (hf i).sub (cellWeight_memLp B h i)
  have hvM := (hfM i).sub (cellWeight_measurable B h i)
  have huC := gaussianAverage_memLp_signed s hs _ (oddHighModes_measurable _ hvM)
    (oddHighModes_memLp _ hv)
  change MemLp (gaussianAverage s (oddHighModes (fun y=>f y i-cellWeight B h i y))) 2 (γFin d) at huC
  have hmap : MeasurePreserving (WithLp.toLp 2) (γFin d) (stdGaussian (FSC.Coord d)) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have hu : MemLp (actualOddSource s f B h i) 2 (stdGaussian (FSC.Coord d)) := by
    rw [← hmap.map_eq]
    apply (memLp_map_measure_iff huM.aestronglyMeasurable hmap.aemeasurable).mpr
    simpa only [Function.comp_def,actualOddSource_coordinate] using huC
  refine ⟨huM,hu,?_⟩
  rw [realLp_two_sq_eq_integral hu,
    ← (NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d).integral_comp'
      (fun x=>(actualOddSource s f B h i x)^2)]
  simp only [actualOddSource_coordinate]
  rfl

/-- Actual fractional-to-own-centroid-fan replacement, retaining both the
centroid square and the entire odd residual. The cap here is the literal
weighted actualResidual cap, not a prescribed error bound. -/
theorem own_centroid_replacement_cap_lower {n : ℕ} (hn : 0 < n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (R D : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (h : Fin (n+2) → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hB : CenteredSingularLowerBound (referenceScale n•R+D) σ)
    (τ χ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hχ : 0 < χ) (hχ1 : χ < 1)
    (hrhalf : (τ*χ)^2 ≤ 1/2)
    (f : (Fin d → ℝ) → Fin (n+2) → ℝ)
    (hfM : ∀ i,Measurable (fun y => f y i))
    (hfs : ∀ᵐ y ∂γFin d,SimplexWeights (f y))
    (hmoment : ∀ i j,momentMatrix f i j=((referenceScale n•R+D) i).ofLp j)
    (hmass : ∀ i,(∫ y,f y i ∂γFin d)=∫ y,cellWeight (referenceScale n•R+D) h i y ∂γFin d) :
    let r:ℝ:=(τ*χ)^2
    let B:=referenceScale n•R+D
    let g: (Fin d → ℝ) → Fin (n+2) → ℝ:=fun y i=>cellWeight B h i y
    let u:=actualOddSource (τ*χ) f B h
    let v:=NegativeVotingNearBalancedStructuredCap.residualWeightedForcing R D h (dampingEta n r)
      τ χ (referenceScale n•R,0) (B,h) u
    Integrable (closedCellCap B h v 1) (stdGaussian (FSC.Coord d)) →
    r*centroidResidual f g+
      (∑ i,∫ y,(gaussianAverage (τ*χ) (oddHighModes (fun z=>f z i-g z i)) y)^2 ∂γFin d)-
      2*r*(∫ x,closedCellCap B h v 1 x ∂stdGaussian (FSC.Coord d)) ≤
        gaussianNoiseStability (-r) f-gaussianNoiseStability (-r) g := by
  intro r B g u v hcap
  have hs : 0 < τ*χ:=mul_pos hτ hχ
  have hs1 : τ*χ < 1:=(mul_lt_mul_of_pos_left hχ1 hτ).trans (by simpa using hτ1)
  have hsa : |τ*χ| ≤ 1:=by rw [abs_of_pos hs];exact hs1.le
  have hr : 0 < r:=sq_pos_of_pos hs
  have hra : |-r| ≤ 1:=by rw [abs_neg,abs_of_pos hr];linarith
  have hf i : MemLp (fun y=>f y i) 2 (γFin d) := by
    apply MemLp.of_bound (hfM i).aestronglyMeasurable 1
    filter_upwards [hfs] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (hy.1 i)]
    exact simplex_weight_le_one _ hy i
  have hg i : MemLp (fun y=>g y i) 2 (γFin d):=cellWeight_memLp B h i
  have hgM i : Measurable (fun y=>g y i):=cellWeight_measurable B h i
  have hd i : MemLp (fun y=>f y i-g y i) 2 (γFin d):=(hf i).sub (hg i)
  have hdM i : Measurable (fun y=>f y i-g y i):=(hfM i).sub (hgM i)
  let a : FSC.Coord d → Fin (n+2) → ℝ:=fun x i=>
    actualResidual τ χ (referenceScale n•R,0) (B,h) u i x
  let Q : (Fin d → ℝ) → Fin (n+2) → ℝ:=fun y i=>
    gaussianAverage (-r) (highModes 2 (fun z=>g z i)) y-
      gaussianAverage (τ*χ) (gaussianAverage (τ*χ) (oddHighModes (fun z=>f z i-g z i))) y
  have hQ i : MemLp (fun y=>Q y i) 2 (γFin d) :=
    (gaussianAverage_memLp_signed (-r) hra _ (highModes_measurable 2 _ (hgM i))
      (highModes_memLp 2 _ (hg i))).sub
      (gaussianAverage_memLp_signed (τ*χ) hsa _
        (gaussianAverage_measurable (τ*χ) _ (oddHighModes_measurable _ (hdM i)))
        (gaussianAverage_memLp_signed (τ*χ) hsa _ (oddHighModes_measurable _ (hdM i))
          (oddHighModes_memLp _ (hd i))))
  have hpotential (x : FSC.Coord d) (i : Fin (n+2)) :
      correctedRegularPotential R r a x i=1/((n:ℝ)+2)+Q x.ofLp i := by
    have hh:=correctedPotential_actualResidual n hn R hG (B,h) σ hσ hB
      τ χ hτ hτ1 hχ hχ1 u x i
    change correctedRegularPotential R r a x i=
      1/((n:ℝ)+2)+gaussianAverage (-r) (highModes 2 (fun z=>g z i)) x.ofLp-
        ambientAverage (τ*χ) (actualOddSource (τ*χ) f B h i) x at hh
    rw [actualOddSource_second_average] at hh
    dsimp only [Q]
    linarith
  have hBInj : Function.Injective B := by
    intro i j he
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hB i j hij he
  have hveq : pairForcing R D h r a=v :=
    pairForcing_eq_residualWeightedForcing R D h τ χ (referenceScale n•R,0) (B,h) u
  have hroute := integral_routing_potential_lower hn hmean R D hG h hBInj r hr hrhalf a Q
    (1/((n:ℝ)+2)) hpotential hQ f hfM hfs hmoment hmass (by rwa [hveq])
  rw [hveq] at hroute
  have hnoise := actual_reference_ou_lower_bound (τ*χ) hs hs1 f g hfM hgM hf hg hmass
  change r*centroidResidual f g+_+2*(r*centroidRouting f g+
    ∑ i,∫ y,(f y i-g y i)*Q y i ∂γFin d) ≤ _ at hnoise
  linarith

open NegativeVotingStructuredSwitchingMoments NegativeVotingStructuredSwitchingAmplitude
  NegativeVotingNearBalancedStructuredCap NegativeVotingBoundaryHighChaosTrace
  NegativeVotingSmoothErrorMoment NegativeVotingStructuredSwitchingAllAmplitudes
  NegativeVotingSwitchingModerateIntegral

/-- The literal residual cap is integrable, with a threshold before dimension.
This is derived from the actual common-smoothed forcing moments and does not
use a claimed cap-integral inequality to infer integrability. -/
theorem exists_dimension_uniform_actual_cap_integrable (A K : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ,N ≤ n → ∀ d : ℕ,∀ R D : Fin (n+2) → FSC.Coord d,
      (∀ i,‖R i‖ ≤ 1) → ∀ h : Fin (n+2) → ℝ,∀ η τ χ : ℝ,
      0 < τ → τ < 1 → 0 < χ → χ < 1 → (τ*χ)^2 ≤ 1/((n:ℝ)+1) →
      0 ≤ η → η ≤ K*((τ*χ)^2)^2*logScale n → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ p₀ p₁ : Parameters d (Fin (n+2)),∀ σ₀ σ₁ : ℝ,0 < σ₀ → 0 < σ₁ →
      CenteredSingularLowerBound p₀.1 σ₀ → CenteredSingularLowerBound p₁.1 σ₁ →
      ∀ u : Fin (n+2) → FSC.Coord d → ℝ,
      (∀ i,Measurable (u i)) → (∀ i,MemLp (u i) 2 (stdGaussian (FSC.Coord d))) →
      Integrable (closedCellCap p₁.1 h (residualWeightedForcing R D h η τ χ p₀ p₁ u) 1)
        (stdGaussian (FSC.Coord d)) := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_weightedForcing_sum_norm_sq_le A K hA hK
  refine ⟨N,?_⟩
  intro n hn d R D hR h η τ χ hτ hτ1 hχ hχ1 hrange hη hηupper hqτ
    p₀ p₁ σ₀ σ₁ hσ₀ hσ₁ hp₀ hp₁ u huM hu
  let fD:=cellSource τ χ p₀ p₁
  let fu:=fun i=>highSource χ (u i)
  let v:=weightedForcing R D h η ((τ*χ)^2) τ fD fu
  have hfDM i : Measurable (fD i):=cellSource_measurable τ χ p₀ p₁ i
  have hfuM i : Measurable (fu i):=ambientAverage_measurable χ (u i) (huM i)
  have hfD i : MemLp (fD i) 2 (stdGaussian (FSC.Coord d)):=cellSource_memLp τ χ hτ hτ1 hχ hχ1 p₀ p₁ i
  have hfu i : MemLp (fu i) 2 (stdGaussian (FSC.Coord d)):=
    (ambientAverage_euclidean_memLp_and_decay hχ hχ1 (u i) (huM i) (hu i) 0 (fun b hb=>by omega)).1
  have hvq:∀ i,MemLp (fun x=>v x i) (ENNReal.ofReal (A*logScale n)) (stdGaussian (FSC.Coord d)):=
    (hN n hn d R D h hR ((τ*χ)^2) η τ (sq_pos_of_pos (mul_pos hτ hχ)) hrange
      hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu).1
  have hq : (1:ENNReal) ≤ ENNReal.ofReal (A*logScale n) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [logScale_one_le n]
  have hv i : Integrable (fun x=>v x i) (stdGaussian (FSC.Coord d)):=
    (hvq i).integrable hq
  have hvM i : Measurable (fun x=>v x i):=
    weightedForcing_measurable R D h η ((τ*χ)^2) τ fD fu hfDM hfuM i
  have hB : Function.Injective p₁.1 := by
    intro i j he
    by_contra hij
    exact centered_singular_rows_ne p₁.1 σ₁ hσ₁ hp₁ i j hij he
  have hmajor:=separatedMarginMajorant_integrable p₁.1 h v 1 hv
  have hle:=closedCellCap_le_separated_ae p₁.1 hB h v 1
  have hcap : Integrable (closedCellCap p₁.1 h v 1) (stdGaussian (FSC.Coord d)) := by
    apply hmajor.mono' (measurable_closedCellCap p₁.1 h v 1 hvM).aestronglyMeasurable
    filter_upwards [hle] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (closedCellCap_nonneg p₁.1 h v 1 x)]
    exact hx
  have heq:=residualWeightedForcing_eq_factored_ae R D h η τ χ hτ hτ1 hχ hχ1
    p₀ p₁ σ₀ σ₁ hσ₀ hσ₁ hp₀ hp₁ u hu
  apply hcap.congr
  filter_upwards [heq] with x hx
  exact (closedCellCap_weight_congr _ _ _ _ _ _ _ (fun i=>by simpa using hx i)).symm

end NegativeVotingOwnCentroidLocalReplacement
