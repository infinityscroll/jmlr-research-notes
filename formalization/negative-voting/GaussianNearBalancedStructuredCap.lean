import GaussianStructuredSwitchingAllAmplitudes
import GaussianNearBalancedHighTailComparison

/-! The all-amplitude cap on actual near-regular selected cells. The concrete
geometric and source-integrability premises are proved, not supplied as cap
or normal-trace assumptions. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingNearBalancedStructuredCap
open NegativeVotingStructuredSwitchingAllAmplitudes NegativeVotingStructuredSwitchingAmplitude
  NegativeVotingStructuredSwitchingMoments NegativeVotingNearBalancedHighTailComparison
  NegativeVotingNearBalancedSourceInputs NegativeVotingNearRegularBalancedGeometry
  NegativeVotingStructuredResidualInputs NegativeVotingFanSelectedOffsets
  NegativeVotingFan NegativeVotingDisintegration NegativeVotingWeightedFacet NegativeVotingFanJacobian
  NegativeVotingCapTail NegativeVotingFacetDegree NegativeVotingSmoothErrorMoment
  NegativeVotingStructuredSwitchingFacetEnergy NegativeVotingActualFacetOUTrace
  NegativeVotingBoundaryHighChaosTrace NegativeVotingConditionalSecondMoment
  NegativeVotingSwitchingOrdered
variable {d n : ℕ}

theorem two_sqrt_log_le (m : ℝ) (hm : 4 ≤ m) : 2*Real.sqrt (1+Real.log m) ≤ m := by
  have hm0 : 0 < m:=by linarith
  have hL0 : 0 ≤ 1+Real.log m:=by positivity [Real.log_nonneg (by linarith : 1 ≤ m)]
  have hLm : 1+Real.log m ≤ m:=by linarith [Real.log_le_sub_one_of_pos hm0]
  have hs:=Real.sq_sqrt hL0
  have hm2 : 4*m ≤ m^2:=by nlinarith
  nlinarith [Real.sqrt_nonneg (1+Real.log m)]

/-- A single alphabet threshold supplies the deliberately loose geometric
bounds used only to absorb the tiny-cap errors. -/
theorem exists_coarse_scale_threshold (e H : ℝ) (he : 0<e) (hH : 0 ≤ H) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      4 ≤ (n:ℝ)+2 ∧
      ∀ α : ℝ, 0<α → e*Real.sqrt (logScale n)/((n:ℝ)+2) ≤ α/2 →
        α ≤ H*Real.sqrt (logScale n)/((n:ℝ)+2) →
        2*α ≤ 1 ∧ 1/(α/2) ≤ ((n:ℝ)+2)^2 := by
  obtain ⟨N,hN⟩:=exists_nat_gt (4*H^2+1/e+4)
  refine ⟨N,?_⟩
  intro n hn
  have hnn : (N:ℝ) ≤ n:=by exact_mod_cast hn
  have hm4 : 4 ≤ (n:ℝ)+2:=by have hh:=sq_nonneg H; have hp:=one_div_pos.mpr he; linarith
  have hH2 : 4*H^2 ≤ (n:ℝ)+2:=by have hp:=one_div_pos.mpr he; linarith
  have hem : 1 ≤ e*((n:ℝ)+2):=by
    have hh : 1/e ≤ (n:ℝ)+2:=by have hh:=sq_nonneg H; linarith
    have hm:=mul_le_mul_of_nonneg_left hh he.le
    rw [mul_one_div_cancel he.ne'] at hm
    exact hm
  refine ⟨hm4,?_⟩
  intro α hα hscale hupper
  have hm0 : 0 < (n:ℝ)+2:=by positivity
  have hL0 : 0 ≤ logScale n:=by linarith [logScale_one_le n]
  have hLm : logScale n ≤ (n:ℝ)+2:=by unfold logScale; linarith [Real.log_le_sub_one_of_pos hm0]
  have hsqrt1 : 1 ≤ Real.sqrt (logScale n):=by apply Real.le_sqrt_of_sq_le; simpa using logScale_one_le n
  have hprod : 4*H^2*logScale n ≤ ((n:ℝ)+2)^2:=by
    have hh:=mul_le_mul hH2 hLm hL0 hm0.le
    nlinarith only [hh]
  have hsquare : (2*H*Real.sqrt (logScale n))^2=4*H^2*logScale n:=by
    have hs:=Real.sq_sqrt hL0
    nlinarith only [hs]
  have hroot : 2*H*Real.sqrt (logScale n) ≤ (n:ℝ)+2:=by nlinarith [sq_nonneg ((n:ℝ)+2)]
  have hαmul := (le_div_iff₀ hm0).mp hupper
  have hsmall : 2*α ≤ 1:=by
    apply (mul_le_mul_iff_right₀ hm0).mp
    nlinarith only [hαmul,hroot]
  have hσlower : 1/((n:ℝ)+2)^2 ≤ α/2:=by
    calc
      _ ≤ e/((n:ℝ)+2) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hm0) hm0).mpr
        nlinarith [mul_le_mul_of_nonneg_right hem hm0.le]
      _ ≤ e*Real.sqrt (logScale n)/((n:ℝ)+2) :=
        div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hsqrt1 he.le]) hm0.le
      _ ≤ _ := hscale
  refine ⟨hsmall,?_⟩
  apply (div_le_iff₀ (by positivity : 0<α/2)).mpr
  have hh:=(div_le_iff₀ (sq_pos_of_pos hm0)).mp hσlower
  nlinarith only [hh]

/-- Concrete selected-cell geometry discharges every premise of the actual
all-amplitude cap; no facet probability or normal control is assumed. -/
theorem exists_near_balanced_selected_cap (A K e H : ℝ) (hA : 8192 ≤ A) (hK : 0 ≤ K)
    (he : 0<e) (hH : 0 ≤ H) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (R D : Fin (n+2)→FSC.Coord d),
      (∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) →
      ∀ α : ℝ, 0<α → (∑i,‖D i‖^2) ≤ α^2/256 →
      e*Real.sqrt (logScale n)/((n:ℝ)+2) ≤ α/2 → α ≤ H*Real.sqrt (logScale n)/((n:ℝ)+2) →
      ∀ p : Fin (n+2)→ℝ, (∑i,p i)=1 →
      (∀i,1/(2*((n:ℝ)+2)) ≤ p i) → (∀i,p i ≤ 2/((n:ℝ)+2)) →
      ∀ r η τ : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η → η ≤ K*r^2*logScale n →
      0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ fD fu : Fin (n+2)→FSC.Coord d→ℝ,
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      let h : Fin (n+2)→ℝ:=selectedOffsets (α•R+D) p
      let θ:=structuredAmplitude A 4 r τ D h fD fu
      θ ≤ ((n:ℝ)+2)^(-(5:ℝ)/4) →
      (∫x,closedCellCap (α•R+D) h (weightedForcing R D h η r τ fD fu) 1 x ∂stdGaussian (FSC.Coord d)) ≤
        capConstant A e 2 (massDegree e)*θ^2 := by
  obtain ⟨N₁,hN₁⟩:=exists_dimension_uniform_structured_cap A K 4 e 2 (massDegree e)
    hA hK (by norm_num) he (by norm_num) (massDegree_pos e he).le
  obtain ⟨N₂,hN₂⟩:=exists_coarse_scale_threshold e H he hH
  refine ⟨N₁+N₂+2,?_⟩
  intro n hn d R D hGram α hα hD hscale hupper p hs hlo hup r η τ hr hrange hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu h θ hθceil
  have hm : 3 ≤ n+2:=by omega
  have hm0 : 0 < (n:ℝ)+2:=by positivity
  have hGram' : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hGram
  have hp : ∀i,0<p i:=fun i=>lt_of_lt_of_le (by positivity) (hlo i)
  have hg:=segment_geometry hm R D hGram' α hα hD 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hg
  obtain ⟨hm4,hcoarse⟩:=hN₂ n (by omega)
  obtain ⟨hdiam,hσinv⟩:=hcoarse α hα hscale hupper
  have hinj : Function.Injective (α•R+D):=fun i j hh=>by
    by_contra hij
    exact centered_singular_rows_ne _ (α/2) (by positivity) hg.1 i j hij hh
  have hmass i : mass (α•R+D) h i=p i:=by
    exact congrFun (selectedOffsets_mass _ hinj p hp hs) i
  have hoff i j (hij:i≠j) : |pairOffset (α•R+D) h i j| ≤ 2*Real.sqrt (logScale n):=by
    have hh:=near_mass_pairOffset hm R D hGram' α hα hD p hp hs
      (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hlo) i j hij
    simpa only [Nat.cast_add,Nat.cast_ofNat,logScale] using hh
  apply hN₁ n (by omega) d (α•R+D) R D h (regular_row_norm_le R hGram')
    (α/2) α (by positivity) hα hg.1 hscale hg.2.1 hg.2.2.1
    (fun i j hij=>hg.2.2.2.1 j i hij) (fun i=>(hmass i).le.trans (hup i))
    (fun i j=>(hg.2.2.2.2 i j).trans hdiam) hσinv
    (fun i j hij=>(one_div_le_one_div_of_le (by positivity : 0<α/2)
      (centered_singular_pair_norm_lower _ (α/2) (by positivity) hg.1 i j hij)).trans hσinv)
    (fun i j hij=>(hoff i j hij).trans (two_sqrt_log_le _ hm4))
    (fun i j hij=>by
      have hh:=near_mass_probability hm R D hGram' α hα hD p hp hs
        (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hlo) i j hij
      simpa only [Nat.cast_add,Nat.cast_ofNat] using hh)
    (fun i j hij=>by
      have hh:=pow_le_pow_left₀ (abs_nonneg _) (hoff i j hij) 2
      have hsq:=Real.sq_sqrt (show 0 ≤ logScale n by linarith [logScale_one_le n])
      nlinarith [sq_abs (pairOffset (α•R+D) h i j)])
    (fun i=>by
      have hh:=near_mass_degree hm R D hGram' α hα hD e he
        (by simpa only [Nat.cast_add,Nat.cast_ofNat,logScale] using hscale) p hp hs
        (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hup) i
      exact hh)
    r η τ hr hrange hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu hθceil


/-- Ambient OU composition for the actual raw L2 input. The all-normal
parameter version remains available from the residual-input module. -/
theorem ambientAverage_comp_ae (τ χ : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hχ : 0<χ) (hχ1 : χ<1)
    (u : FSC.Coord d→ℝ) (hu : MemLp u 2 (stdGaussian (FSC.Coord d))) :
    NegativeVotingActualFacetOUTrace.ambientAverage τ (highSource χ u)=ᵐ[stdGaussian (FSC.Coord d)]
      NegativeVotingActualFacetOUTrace.ambientAverage (τ*χ) u := by
  let T:=MeasurableEquiv.toLp 2 (Fin d→ℝ)
  have hT:=gaussian_toLp_measurePreserving d
  have hh:=NegativeVotingSmoothingComposition.gaussianAverage_comp_ae hτ hτ1 hχ hχ1
    (fun x:Fin d→ℝ=>u (T x)) (hu.comp_measurePreserving hT)
  rw [←hT.map_eq,←MeasurableEquiv.map_ae]
  change ∀ᵐ x ∂GaussianFin.γFin d, ambientAverage τ (highSource χ u) (T x)=ambientAverage (τ*χ) u (T x)
  filter_upwards [hh] with x hx
  have hi : (fun y:Fin d→ℝ=>highSource χ u (WithLp.toLp 2 y))=
      NegativeVotingHypercontractivity.gaussianAverage χ (fun y=>u (T y)):=by
    funext y
    exact ambientAverage_eq_gaussianAverage χ u (WithLp.toLp 2 y)
  rw [ambientAverage_eq_gaussianAverage,hi,ambientAverage_eq_gaussianAverage]
  exact hx

def residualWeightedForcing (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (η τ χ : ℝ) (p₀ p₁ : NegativeVotingFanScore.Parameters d (Fin (n+2)))
    (u : Fin (n+2)→FSC.Coord d→ℝ) (x : FSC.Coord d) (i : Fin (n+2)) : ℝ :=
  NegativeVotingReciprocalDampingTube.inverseKappa η (fun j=>inner ℝ (R j) x)*
    (NegativeVotingRegularPairCoefficient.smoothPairError n ((τ*χ)^2) (fun j=>inner ℝ (R j) x)*
      |inner ℝ (D i) x+h i|+|actualResidual τ χ p₀ p₁ u i x|/((τ*χ)^2))

/-- The common-smoothed cap is the literal residual cap almost everywhere;
this identity is proved from OU composition, not a replacement of inputs. -/
theorem residualWeightedForcing_eq_factored_ae
    (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ) (η τ χ : ℝ)
    (hτ : 0<τ) (hτ1 : τ<1) (hχ : 0<χ) (hχ1 : χ<1)
    (p₀ p₁ : NegativeVotingFanScore.Parameters d (Fin (n+2))) (s₀ s₁ : ℝ) (hs₀ : 0<s₀) (hs₁ : 0<s₁)
    (h₀ : CenteredSingularLowerBound p₀.1 s₀) (h₁ : CenteredSingularLowerBound p₁.1 s₁)
    (u : Fin (n+2)→FSC.Coord d→ℝ) (hu : ∀i,MemLp (u i) 2 (stdGaussian (FSC.Coord d))) :
    ∀ᵐ x ∂stdGaussian (FSC.Coord d), ∀i,
      residualWeightedForcing R D h η τ χ p₀ p₁ u x i=
        weightedForcing R D h η ((τ*χ)^2) τ (cellSource τ χ p₀ p₁) (fun i=>highSource χ (u i)) x i := by
  have hall : ∀ᵐ x ∂stdGaussian (FSC.Coord d),∀i,
      NegativeVotingActualFacetOUTrace.ambientAverage τ (highSource χ (u i)) x=
        NegativeVotingActualFacetOUTrace.ambientAverage (τ*χ) (u i) x:=
    ae_all_iff.mpr (fun i=>ambientAverage_comp_ae τ χ hτ hτ1 hχ hχ1 (u i) (hu i))
  filter_upwards [hall] with x hx
  intro i
  unfold residualWeightedForcing weightedForcing actualResidual
  rw [cellSource_factorization p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i τ χ hτ hτ1 hχ hχ1,hx i]

/-- Actual near-balanced residual cap, with the cell sources and their
integrability constructed from the selected cells themselves. -/
theorem exists_near_balanced_actualResidual_cap (A K e H : ℝ) (hA : 8192 ≤ A) (hK : 0 ≤ K)
    (he : 0<e) (hH : 0 ≤ H) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (R D : Fin (n+2)→FSC.Coord d),
      (∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2)) →
      ∀ α : ℝ, 0<α → (∑i,‖D i‖^2) ≤ α^2/256 →
      e*Real.sqrt (logScale n)/((n:ℝ)+2) ≤ α/2 → α ≤ H*Real.sqrt (logScale n)/((n:ℝ)+2) →
      ∀ p : Fin (n+2)→ℝ, (∑i,p i)=1 →
      (∀i,1/(2*((n:ℝ)+2)) ≤ p i) → (∀i,p i ≤ 2/((n:ℝ)+2)) →
      ∀ η τ χ : ℝ, 0<τ → τ<1 → 0<χ → χ<1 →
      (τ*χ)^2 ≤ 1/((n:ℝ)+1) → 0 ≤ η → η ≤ K*((τ*χ)^2)^2*logScale n →
      4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ u : Fin (n+2)→FSC.Coord d→ℝ, (∀i,Measurable (u i)) →
      (∀i,MemLp (u i) 2 (stdGaussian (FSC.Coord d))) →
      let h : Fin (n+2)→ℝ:=selectedOffsets (α•R+D) p
      let p₀ : NegativeVotingFanScore.Parameters d (Fin (n+2)) :=
        (α•R,selectedOffsets (α•R) (fun _=>((n:ℝ)+2)⁻¹))
      let p₁ : NegativeVotingFanScore.Parameters d (Fin (n+2)) := (α•R+D,h)
      let fD:=cellSource τ χ p₀ p₁
      let fu:=fun i=>highSource χ (u i)
      let θ:=structuredAmplitude A 4 ((τ*χ)^2) τ D h fD fu
      θ ≤ ((n:ℝ)+2)^(-(5:ℝ)/4) →
      (∫x,closedCellCap (α•R+D) h (residualWeightedForcing R D h η τ χ p₀ p₁ u) 1 x ∂stdGaussian (FSC.Coord d)) ≤
        capConstant A e 2 (massDegree e)*θ^2 := by
  obtain ⟨N,hN⟩:=exists_near_balanced_selected_cap A K e H hA hK he hH
  refine ⟨N+1,?_⟩
  intro n hn d R D hGram α hα hD hscale hupper p hs hlo hup η τ χ hτ hτ1 hχ hχ1 hrange hη hηupper hqτ
    u huM hu h p₀ p₁ fD fu θ hθceil
  have hfDM i : Measurable (fD i):=cellSource_measurable τ χ p₀ p₁ i
  have hfuM i : Measurable (fu i):=NegativeVotingActualFacetOUTrace.ambientAverage_measurable χ (u i) (huM i)
  have hfD i : MemLp (fD i) 2 (stdGaussian (FSC.Coord d)):=cellSource_memLp τ χ hτ hτ1 hχ hχ1 p₀ p₁ i
  have hfu i : MemLp (fu i) 2 (stdGaussian (FSC.Coord d)):=
    (ambientAverage_euclidean_memLp_and_decay hχ hχ1 (u i) (huM i) (hu i) 0 (fun b hb=>by omega)).1
  have hbound:=hN n (by omega) d R D hGram α hα hD hscale hupper p hs hlo hup ((τ*χ)^2) η τ
    (sq_pos_of_pos (mul_pos hτ hχ)) hrange hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu hθceil
  have hGram' : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(n+2:ℕ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hGram
  have hreg : CenteredSingularLowerBound p₀.1 α:=regular_scaled_singular R hGram' α
  have hcur : CenteredSingularLowerBound p₁.1 (α/2):=by
    have hh:=(segment_geometry (show 3 ≤ n+2 by omega) R D hGram' α hα hD 1 ⟨by norm_num,le_rfl⟩).1
    simpa only [one_smul] using hh
  have heq:=residualWeightedForcing_eq_factored_ae R D h η τ χ hτ hτ1 hχ hχ1 p₀ p₁ α (α/2)
    hα (by positivity) hreg hcur u hu
  have hcapEq : (∫x,closedCellCap (α•R+D) h (residualWeightedForcing R D h η τ χ p₀ p₁ u) 1 x ∂stdGaussian (FSC.Coord d))=
      ∫x,closedCellCap (α•R+D) h (weightedForcing R D h η ((τ*χ)^2) τ fD fu) 1 x ∂stdGaussian (FSC.Coord d):=by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    exact closedCellCap_weight_congr _ _ _ _ _ _ _ (fun i=>by simpa using hx i)
  rw [hcapEq]
  exact hbound

end NegativeVotingNearBalancedStructuredCap
