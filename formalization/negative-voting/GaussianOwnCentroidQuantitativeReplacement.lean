import GaussianOwnCentroidLocalReplacement

/-! Quantitative replacement of an actual fractional assignment by its
mass-matching own-centroid fan. The threshold precedes dimension; the literal
cap and its integrability are derived, and half the odd residual is retained.
This does not compare the selected affine fan to the regular fan. -/
noncomputable section
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace Classical Topology
namespace NegativeVotingOwnCentroidQuantitativeReplacement
open NegativeVoting NegativeVotingAffine NegativeVotingModern NegativeVotingFan
  NegativeVotingFanScore NegativeVotingFanTestedCells NegativeVotingCapTail
  NegativeVotingOwnCentroidRoutingCap NegativeVotingOwnCentroidSpectralReplacement
  NegativeVotingOwnCentroidLocalReplacement NegativeVotingQuadraticMomentPadding
  NegativeVotingBalancedReference NegativeVotingStructuredResidualInputs
  NegativeVotingActualFacetOUTrace NegativeVotingProjection NegativeVotingRareLabelHighChaos
  NegativeVotingHypercontractivity NegativeVotingSwitchingOrdered NegativeVotingDisintegration
  NegativeVotingCellOUContinuity NegativeVotingFacetDegree NegativeVotingNearBalancedActualCap
  NegativeVotingStructuredAmplitudeBound NegativeVotingSmoothErrorMoment
  NegativeVotingNearRegularBalancedGeometry NegativeVotingRegularReferenceNormalization
  NegativeVotingFanSelectedOffsets NegativeVotingFanInverse NegativeVotingNearBalancedSourceInputs
  NegativeVotingNearBalancedStructuredCap NegativeVotingStructuredSwitchingMoments
variable {d : ℕ}

theorem cellWeight_integral_eq_mass {ι : Type*} [Fintype ι] [Nonempty ι]
    (B : ι → FSC.Coord d) (hB : Function.Injective B) (h : ι → ℝ) (i : ι) :
    (∫ y,cellWeight B h i y ∂γFin d)=mass B h i := by
  change (∫ y,(winningCell B h i).indicator (fun _ => (1:ℝ))
    ((MeasurableEquiv.toLp 2 (Fin d→ℝ)) y) ∂γFin d)=_
  rw [(NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d).integral_comp'
    ((winningCell B h i).indicator (fun _ => (1:ℝ)))]
  rw [integral_indicator (winningCell_measurable B h i),integral_const,mass_eq_winningCell B hB]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]

/-- Scalar absorption, uniform in every subsequent dimension and assignment. -/
theorem exists_odd_absorption_threshold (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ,∀ n : ℕ,N ≤ n → ∀ r : ℝ,0 ≤ r → r ≤ 2/((n:ℝ)+2) →
      2*C*(logScale n)^10*r^2 ≤ 1/2 := by
  have hlim:=((tendsto_const_nhds : Tendsto (fun _ : ℕ => 8*C) atTop (𝓝 (8*C)))).mul
    ((NegativeVoting.logarithmic_remainder_tendsto_zero (10:ℕ) 2 (by norm_num) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun m:ℕ=>(m:ℝ)) atTop atTop))
  simp only [mul_zero] at hlim
  obtain ⟨N,hN⟩:=eventually_atTop.mp (hlim.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)))
  refine ⟨N,?_⟩
  intro n hn r hr hrange
  have hh:=hN (n+2) (by omega)
  simp only [Function.comp_def,Real.rpow_natCast] at hh
  have hh' : 8*C*(logScale n)^10/((n:ℝ)+2)^2 ≤ 1/2 := by
    simpa only [logScale,Nat.cast_add,Nat.cast_ofNat,mul_div_assoc,Real.rpow_two] using hh.le
  calc
    _ ≤ 2*C*(logScale n)^10*(2/((n:ℝ)+2))^2 := by gcongr
    _ = 8*C*(logScale n)^10/((n:ℝ)+2)^2 := by rw [div_pow];ring
    _ ≤ _ := hh'

/-- No cap estimate, residual estimate, winner assumption, or offset bound is
assumed. The actual masses determine the selected fan and the actual centroids
determine its scores. The unabsorbed error is explicitly cubic in correlation. -/
theorem exists_dimension_uniform_own_centroid_replacement
    (A e H B : ℝ) (hA : 8192 ≤ A) (he : 0 < e) (hH : 0 ≤ H) (hBsize : 0 ≤ B) :
    ∃ N : ℕ,∀ n : ℕ,N ≤ n →
      1 ≤ NegativeVotingGaussianMaximum.maximumMean n →
      ∀ d : ℕ,∀ R D : Fin (n+2) → FSC.Coord d,
      (∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) →
      (∑ i,‖D i‖^2) ≤ (referenceScale n)^2/256 →
      e*Real.sqrt (logScale n)/((n:ℝ)+2) ≤ referenceScale n/2 →
      referenceScale n ≤ H*Real.sqrt (logScale n)/((n:ℝ)+2) →
      ∀ v : centeredGauge (Fin (n+2)),
      (∀ i,|(v:Fin (n+2)→ℝ) i| ≤ 1/(2*((n:ℝ)+2))) →
      (∑ i,‖D i‖^2)+(∑ i,((v:Fin (n+2)→ℝ) i)^2) ≤ B/((n:ℝ)+2) →
      ∀ τ χ : ℝ,0 < τ → 0 < χ → χ < 1 → τ^2=1/(4*A*logScale n-1) →
      (τ*χ)^2 ≤ 1/((n:ℝ)+1) →
      ∀ f : (Fin d→ℝ) → Fin (n+2) → ℝ,
      (∀ i,Measurable (fun y=>f y i)) →
      (∀ᵐ y ∂γFin d,SimplexWeights (f y)) →
      (∀ i j,momentMatrix f i j=((referenceScale n•R+D) i).ofLp j) →
      (∀ i,(∫ y,f y i ∂γFin d)=((n:ℝ)+2)⁻¹+(v:Fin (n+2)→ℝ) i) →
      let r:ℝ:=(τ*χ)^2
      let p:Fin (n+2)→ℝ:=(fun _=>((n:ℝ)+2)⁻¹)+(v:Fin (n+2)→ℝ)
      let h:Fin (n+2)→ℝ:=selectedOffsets (referenceScale n•R+D) p
      let g:(Fin d→ℝ)→Fin (n+2)→ℝ:=fun y i=>cellWeight (referenceScale n•R+D) h i y
      r*centroidResidual f g+
        (∑ i,∫ y,(gaussianAverage (τ*χ) (oddHighModes (fun z=>f z i-g z i)) y)^2 ∂γFin d)/2-
        2*actualCapConstant A e H*(logScale n)^10*r^3*
          ((∑ i,‖D i‖^2)+(∑ i,((v:Fin (n+2)→ℝ) i)^2)) ≤
        gaussianNoiseStability (-r) f-gaussianNoiseStability (-r) g := by
  have hK : 0 ≤ dampingSizeConstant:=dampingSizeConstant_nonneg
  have hC : 0 ≤ actualCapConstant A e H:=by
    exact mul_nonneg (capConstant_nonneg A e he)
      (amplitude_bases_nonneg A 4 (4*A) e H (by norm_num) (by linarith) he).2.2.2
  obtain ⟨N₁,hN₁⟩:=exists_dimension_uniform_actual_cap A dampingSizeConstant e H B hA hK he hH hBsize
  obtain ⟨N₂,hN₂⟩:=exists_dimension_uniform_actual_cap_integrable A dampingSizeConstant (by linarith) hK
  obtain ⟨N₃,hN₃⟩:=exists_common_smoothing_threshold A e hA he
  obtain ⟨N₄,hN₄⟩:=exists_odd_absorption_threshold (actualCapConstant A e H) hC
  refine ⟨N₁+N₂+N₃+N₄+2,?_⟩
  intro n hn hmean d R D hG hD hscale hupper v hv hsize τ χ hτ hχ hχ1 ht hrange f hfM hfs hmoment hmass r p h g
  have hn0 : 0 < n:=by omega
  have hm0 : 0 < (n:ℝ)+2:=by positivity
  have hα : 0 < referenceScale n:=referenceScale_pos n
  have hG' : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hscale' : e*Real.sqrt (logScale n)/(n+2:ℕ) ≤ referenceScale n/2:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hscale
  obtain ⟨_,_,hτ2,_,hnative,_⟩:=hN₃ n (by omega) (referenceScale n) τ hα hscale' ht
  have hτ1 : τ < 1:=by nlinarith
  have hs : 0 < τ*χ:=mul_pos hτ hχ
  have hs1 : τ*χ < 1:=(mul_lt_mul_of_pos_left hχ1 hτ).trans (by simpa using hτ1)
  have hsa : |τ*χ| ≤ 1:=by rw [abs_of_pos hs];exact hs1.le
  have hr : 0 < r:=sq_pos_of_pos hs
  have hrhalf : r ≤ 1/2:=by
    apply hrange.trans
    apply (div_le_iff₀ (show 0 < (n:ℝ)+1 by positivity)).mpr
    have hh : (1:ℝ) ≤ n:=by exact_mod_cast (show 1≤n by omega)
    nlinarith
  have hr2 : r ≤ 2/((n:ℝ)+2):=by
    apply hrange.trans
    apply (div_le_div_iff₀ (show 0 < (n:ℝ)+1 by positivity) hm0).mpr
    nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hη : 0 ≤ dampingEta n r:=dampingEta_nonneg n r
  have hηupper : dampingEta n r ≤ dampingSizeConstant*r^2*logScale n:=dampingEta_le n r hr hrhalf
  have hcur : CenteredSingularLowerBound (referenceScale n•R+D) (referenceScale n/2):=by
    simpa only [one_smul] using
      (segment_geometry (show 3 ≤ n+2 by omega) R D hG' (referenceScale n) hα hD 1 ⟨by norm_num,le_rfl⟩).1
  have hreg := regular_scaled_singular R hG' (referenceScale n)
  have hInj : Function.Injective (referenceScale n•R+D):=by
    intro i j hh
    by_contra hij
    exact centered_singular_rows_ne _ (referenceScale n/2) (by positivity) hcur i j hij hh
  have hp0 i : 0 < p i:=by
    have hi: -(1/(2*((n:ℝ)+2))) ≤ (v:Fin (n+2)→ℝ) i:=(abs_le.mp (hv i)).1
    change 0 < ((n:ℝ)+2)⁻¹+(v:Fin (n+2)→ℝ) i
    have hh : 0 < 1/(2*((n:ℝ)+2)):=by positivity
    have heq : ((n:ℝ)+2)⁻¹=2*(1/(2*((n:ℝ)+2))):=by field_simp
    rw [heq];linarith
  have hp1 : ∑i,p i=1:=by
    have hv0 : ∑i,(v:Fin (n+2)→ℝ) i=0:=v.property
    simp only [p,Pi.add_apply,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat,hv0,add_zero]
    exact mul_inv_cancel₀ hm0.ne'
  have hgMass i : (∫y,g y i ∂γFin d)=p i:=by
    rw [cellWeight_integral_eq_mass _ hInj,show mass _ h=p from selectedOffsets_mass _ hInj p hp0 hp1]
  have hmatch i : (∫y,f y i ∂γFin d)=∫y,g y i ∂γFin d:=by rw [hgMass];exact hmass i
  have hf i : MemLp (fun y=>f y i) 2 (γFin d):=by
    apply MemLp.of_bound (hfM i).aestronglyMeasurable 1
    filter_upwards [hfs] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (hy.1 i)]
    exact simplex_weight_le_one _ hy i
  let u:=actualOddSource (τ*χ) f (referenceScale n•R+D) h
  have huM i : Measurable (u i):=(actualOddSource_memLp_and_square (τ*χ) hsa f _ h hfM hf i).1
  have hu i : MemLp (u i) 2 (stdGaussian (FSC.Coord d)):=
    (actualOddSource_memLp_and_square (τ*χ) hsa f _ h hfM hf i).2.1
  have huEq : (∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (u i))^2)=
      ∑i,∫y,(gaussianAverage (τ*χ) (oddHighModes (fun z=>f z i-g z i)) y)^2 ∂γFin d:=by
    apply Finset.sum_congr rfl
    intro i _
    exact (actualOddSource_memLp_and_square (τ*χ) hsa f _ h hfM hf i).2.2
  let F : Fin (n+2)→FSC.Coord d→ℝ:=fun i x=>f x.ofLp i
  let G : Fin (n+2)→FSC.Coord d→ℝ:=fun i x=>g x.ofLp i
  have hFM i : Measurable (F i):=(hfM i).comp (by fun_prop)
  have hGM i : Measurable (G i):=(cellWeight_measurable _ h i).comp (by fun_prop)
  have hFA : ∀ᵐ x ∂stdGaussian (FSC.Coord d),(∀i,0≤F i x∧F i x≤1)∧∑i,F i x=1:=by
    have hh:=(NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d).symm.quasiMeasurePreserving.ae hfs
    filter_upwards [hh] with x hx
    exact ⟨fun i=>⟨hx.1 i,simplex_weight_le_one _ hx i⟩,hx.2⟩
  have hGA : ∀ᵐ x ∂stdGaussian (FSC.Coord d),(∀i,0≤G i x∧G i x≤1)∧∑i,G i x=1:=by
    have hh:=(NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d).symm.quasiMeasurePreserving.ae
      (cellWeight_simplex_ae _ hInj h)
    filter_upwards [hh] with x hx
    exact ⟨fun i=>⟨hx.1 i,simplex_weight_le_one _ hx i⟩,hx.2⟩
  have hsqrt : Real.sqrt ((τ*χ)^2)=τ*χ:=Real.sqrt_sq hs.le
  have hzero : (selectedOffsets (referenceScale n•R) (fun _=>((n:ℝ)+2)⁻¹):Fin (n+2)→ℝ)=0:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using selected_regular_scaled_zero R hG' (referenceScale n) hα
  let w:=residualWeightedForcing R D h (dampingEta n r) τ χ (referenceScale n•R,0) (referenceScale n•R+D,h) u
  have hcap:=hN₁ n (by omega) d R D hG (referenceScale n) hα hD hscale hupper v hv hsize
    (dampingEta n r) τ χ hτ hχ hχ1 ht hrange hη hηupper F G hFM hGM hFA hGA
  have hcap' : (∫x,closedCellCap (referenceScale n•R+D) h w 1 x ∂stdGaussian (FSC.Coord d)) ≤
      actualCapConstant A e H*(logScale n)^10*(r^2*((∑i,‖D i‖^2)+(∑i,((v:Fin (n+2)→ℝ) i)^2))+
        r*(∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (u i))^2)):=by
    simp only [hsqrt,hzero] at hcap
    exact hcap
  have hInt := hN₂ n (by omega) d R D (regular_row_norm_le R hG') h (dampingEta n r) τ χ
    hτ hτ1 hχ hχ1 hrange hη hηupper hnative (referenceScale n•R,0) (referenceScale n•R+D,h)
    (referenceScale n) (referenceScale n/2) hα (by positivity) hreg hcur u huM hu
  have hrep:=own_centroid_replacement_cap_lower hn0 hmean R D hG h (referenceScale n/2)
    (by positivity) hcur τ χ hτ hτ1 hχ hχ1 hrhalf f hfM hfs hmoment hmatch hInt
  have habs:=hN₄ n (by omega) r hr.le hr2
  rw [huEq] at hcap'
  have hU0 : 0 ≤ ∑i,∫y,(gaussianAverage (τ*χ) (oddHighModes (fun z=>f z i-g z i)) y)^2 ∂γFin d:=
    Finset.sum_nonneg fun i _=>integral_nonneg fun y=>sq_nonneg _
  have hsub:=mul_le_mul_of_nonneg_right habs hU0
  have hcapmul:=mul_le_mul_of_nonneg_left hcap' (show 0≤2*r by positivity)
  change r*centroidResidual f g+_ -2*r*(∫x,closedCellCap _ h w 1 x ∂stdGaussian (FSC.Coord d)) ≤ _ at hrep
  nlinarith only [hrep,hcapmul,hsub]

/-- Every correlation in the entire voting range admits the common smoothing
parameters. No lower bound on the correlation is imposed. -/
theorem exists_smoothing_parameters_threshold (A : ℝ) (hA : 8192 ≤ A) :
    ∃ N : ℕ,∀ n : ℕ,N ≤ n → ∀ r : ℝ,0 < r → r ≤ 1/((n:ℝ)+1) →
      ∃ τ χ : ℝ,0 < τ ∧ 0 < χ ∧ χ < 1 ∧
        τ^2=1/(4*A*logScale n-1) ∧ τ*χ=Real.sqrt r := by
  have hlim:=((tendsto_const_nhds : Tendsto (fun _ : ℕ=>4*A) atTop (𝓝 (4*A)))).mul
    ((NegativeVoting.logarithmic_remainder_tendsto_zero (1:ℕ) 1 (by norm_num) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun m:ℕ=>(m:ℝ)) atTop atTop))
  simp only [mul_zero] at hlim
  obtain ⟨N,hN⟩:=eventually_atTop.mp (hlim.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)))
  refine ⟨N,?_⟩
  intro n hn r hr hrange
  have hrate:=hN (n+2) (by omega)
  have hrate' : 4*A*logScale n/((n:ℝ)+2)<1:=by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one,pow_one,
      Nat.cast_add,Nat.cast_ofNat,logScale,mul_div_assoc] using hrate
  have hgrowth : 4*A*logScale n<(n:ℝ)+2:=by
    exact (div_lt_iff₀ (show 0<(n:ℝ)+2 by positivity)).mp hrate' |>.trans_eq (one_mul _)
  have hden : 0<4*A*logScale n-1:=by nlinarith [logScale_one_le n]
  have hcorr : r<1/(4*A*logScale n-1):=hrange.trans_lt
    (one_div_lt_one_div_of_lt hden (by linarith))
  let τ:=Real.sqrt (1/(4*A*logScale n-1))
  have hτ : 0<τ:=Real.sqrt_pos.mpr (one_div_pos.mpr hden)
  have hτ2 : τ^2=1/(4*A*logScale n-1):=Real.sq_sqrt (by positivity)
  have hs : Real.sqrt r<τ:=by nlinarith [Real.sq_sqrt hr.le,Real.sqrt_nonneg r]
  refine ⟨τ,Real.sqrt r/τ,hτ,div_pos (Real.sqrt_pos.mpr hr) hτ,(div_lt_one hτ).mpr hs,hτ2,?_⟩
  field_simp

/-- Full voting-range version of the local replacement theorem, with every
auxiliary smoothing parameter eliminated. The dimension-first threshold is
uniform down to arbitrarily small positive correlation. -/
theorem exists_dimension_uniform_voting_replacement
    (A e H B : ℝ) (hA : 8192 ≤ A) (he : 0 < e) (hH : 0 ≤ H) (hBsize : 0 ≤ B) :
    ∃ N : ℕ,∀ n : ℕ,N ≤ n →
      1 ≤ NegativeVotingGaussianMaximum.maximumMean n →
      ∀ d : ℕ,∀ R D : Fin (n+2) → FSC.Coord d,
      (∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) →
      (∑ i,‖D i‖^2) ≤ (referenceScale n)^2/256 →
      e*Real.sqrt (logScale n)/((n:ℝ)+2) ≤ referenceScale n/2 →
      referenceScale n ≤ H*Real.sqrt (logScale n)/((n:ℝ)+2) →
      ∀ v : centeredGauge (Fin (n+2)),
      (∀ i,|(v:Fin (n+2)→ℝ) i| ≤ 1/(2*((n:ℝ)+2))) →
      (∑ i,‖D i‖^2)+(∑ i,((v:Fin (n+2)→ℝ) i)^2) ≤ B/((n:ℝ)+2) →
      ∀ r : ℝ,0 < r → r ≤ 1/((n:ℝ)+1) →
      ∀ f : (Fin d→ℝ) → Fin (n+2) → ℝ,
      (∀ i,Measurable (fun y=>f y i)) →
      (∀ᵐ y ∂γFin d,SimplexWeights (f y)) →
      (∀ i j,momentMatrix f i j=((referenceScale n•R+D) i).ofLp j) →
      (∀ i,(∫ y,f y i ∂γFin d)=((n:ℝ)+2)⁻¹+(v:Fin (n+2)→ℝ) i) →
      let p:Fin (n+2)→ℝ:=(fun _=>((n:ℝ)+2)⁻¹)+(v:Fin (n+2)→ℝ)
      let h:Fin (n+2)→ℝ:=selectedOffsets (referenceScale n•R+D) p
      let g:(Fin d→ℝ)→Fin (n+2)→ℝ:=fun y i=>cellWeight (referenceScale n•R+D) h i y
      r*centroidResidual f g+
        (∑ i,∫ y,(gaussianAverage (Real.sqrt r) (oddHighModes (fun z=>f z i-g z i)) y)^2 ∂γFin d)/2-
        2*actualCapConstant A e H*(logScale n)^10*r^3*
          ((∑ i,‖D i‖^2)+(∑ i,((v:Fin (n+2)→ℝ) i)^2)) ≤
        gaussianNoiseStability (-r) f-gaussianNoiseStability (-r) g := by
  obtain ⟨N₁,hN₁⟩:=exists_dimension_uniform_own_centroid_replacement A e H B hA he hH hBsize
  obtain ⟨N₂,hN₂⟩:=exists_smoothing_parameters_threshold A hA
  refine ⟨max N₁ N₂,?_⟩
  intro n hn hmean d R D hG hD hscale hupper v hv hsize r hr hrange f hfM hfs hmoment hmass p h g
  obtain ⟨τ,χ,hτ,hχ,hχ1,ht,hprod⟩:=hN₂ n ((le_max_right _ _).trans hn) r hr hrange
  have hrEq : (τ*χ)^2=r:=by rw [hprod,Real.sq_sqrt hr.le]
  have hh:=hN₁ n ((le_max_left _ _).trans hn) hmean d R D hG hD hscale hupper v hv hsize
    τ χ hτ hχ hχ1 ht (by rwa [hrEq]) f hfM hfs hmoment hmass
  simpa only [hprod,Real.sq_sqrt hr.le] using hh

end NegativeVotingOwnCentroidQuantitativeReplacement
