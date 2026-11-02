import GaussianSwitchingTinyPolynomialBounds

/-! One cap estimate for the literal structured forcing at every amplitude.
The logarithmic moment exponent is fixed before the forcing amplitude. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingStructuredSwitchingAllAmplitudes
open NegativeVotingStructuredSwitchingAmplitude NegativeVotingStructuredSwitchingCap
  NegativeVotingStructuredSwitchingMoments NegativeVotingStructuredSwitchingFacetEnergy
  NegativeVotingSwitchingTinyPolynomialBounds NegativeVotingSwitchingTiny NegativeVotingSwitchingPair
  NegativeVotingSwitchingOrdered NegativeVotingSwitchingModerateIntegral NegativeVotingSwitchingModerate
  NegativeVotingFan NegativeVotingWeightedFacet NegativeVotingFanJacobian NegativeVotingSmoothErrorMoment
  NegativeVotingDisintegration
variable {d n : ℕ}

theorem closedCellCap_weight_congr {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : V→FSC.Coord d) (h : V→ℝ) (v w : FSC.Coord d→V→ℝ) (θ η : ℝ) (x : FSC.Coord d)
    (he : ∀i,θ*v x i=η*w x i) : closedCellCap B h v θ x=closedCellCap B h w η x := by
  unfold closedCellCap
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x∈affineCell B h i
  · simp only [Set.indicator_of_mem hx]
    have hh : (fun j=>if j=i then 0 else orderedReward (fun k=>affineScore B h k x) (v x) θ i j)=
        (fun j=>if j=i then 0 else orderedReward (fun k=>affineScore B h k x) (w x) η i j):=by
      funext j
      simp only [orderedReward,mul_add,he i,he j]
    exact congrArg NegativeVoting.maxScore hh
  · simp only [Set.indicator_of_notMem hx]

theorem closedCellCap_at_zero {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : V→FSC.Coord d) (h : V→ℝ) (v : FSC.Coord d→V→ℝ) (x : FSC.Coord d) :
    closedCellCap B h v 0 x=0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hx : x∈affineCell B h i
  · simp only [Set.indicator_of_mem hx]
    exact NegativeVotingSwitchingSeparation.switchingCap_zero_on_winner _ _ _ hx
  · exact Set.indicator_of_notMem hx _

theorem closedCellCap_normalized (B R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (η r τ θ : ℝ) (hθ : θ≠0) (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (x : FSC.Coord d) :
    closedCellCap B h (weightedForcing R D h η r τ fD fu) 1 x=
      closedCellCap B h (normalizedForcing R D h η r τ θ fD fu) θ x := by
  apply closedCellCap_weight_congr
  intro i
  simp only [normalizedForcing,one_mul]
  field_simp

/-- Zero computed amplitude means zero actual forcing almost everywhere;
normalization is never used to discard a nonzero input at this endpoint. -/
theorem exists_dimension_uniform_zero_amplitude (A K : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ), (∀i,‖R i‖ ≤ 1) →
      ∀ r η τ b : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η → η ≤ K*r^2*logScale n →
      0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      structuredAmplitude A b r τ D h fD fu=0 →
      (∫x,closedCellCap B h (weightedForcing R D h η r τ fD fu) 1 x ∂stdGaussian (FSC.Coord d))=0 := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_forcing_common_moments A K hA hK
  refine ⟨N,?_⟩
  intro n hn d B R D h hR r η τ b hr hrange hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu hzero
  obtain ⟨hκ,hε⟩:=hN n hn d R hR r η hr hrange hη hηupper
  have hq : 1 ≤ A*logScale n:=by nlinarith [logScale_one_le n]
  have ha := amplitude_full_bound A b r τ D h fD fu
  rw [hzero] at ha
  have hc i : fullLabelMajorant A r τ D h fD fu i ≤ 0:=by
    have hi:=label_le_sqrt_sum_sq (fullLabelMajorant A r τ D h fD fu) i
    linarith [Real.sqrt_nonneg (∑i,(fullLabelMajorant A r τ D h fD fu i)^2)]
  have hlabel i := weightedForcing_label_norm_le R D h η r τ (A*logScale n)
    dampingMomentConstant (errorMomentCoefficient A n) hr hτ hτ1 hq hqτ
    dampingMomentConstant_nonneg (errorMomentCoefficient_nonneg A (by linarith) n)
    hκ hε fD fu hfDM hfuM hfD hfu i
  have hz i : (fun x=>weightedForcing R D h η r τ fD fu x i)=ᵐ[stdGaussian (FSC.Coord d)] 0:=by
    apply (eLpNorm_eq_zero_iff (show ENNReal.ofReal (A*logScale n)≠0 by positivity)).mp
    have ht : (eLpNorm (fun x=>weightedForcing R D h η r τ fD fu x i) (ENNReal.ofReal (A*logScale n)) (stdGaussian (FSC.Coord d))).toReal=0:=
      le_antisymm ((hlabel i).2.trans (hc i)) ENNReal.toReal_nonneg
    rw [←ENNReal.ofReal_toReal (hlabel i).1.eLpNorm_ne_top,ht,ENNReal.ofReal_zero]
  have hall : ∀ᵐ x ∂stdGaussian (FSC.Coord d),∀i,weightedForcing R D h η r τ fD fu x i=0:=by
    exact ae_all_iff.mpr hz
  calc
    _ = ∫x,(0:ℝ) ∂stdGaussian (FSC.Coord d) := integral_congr_ae (by
      filter_upwards [hall] with x hx
      calc
        _ = closedCellCap B h (weightedForcing R D h η r τ fD fu) 0 x :=
          closedCellCap_weight_congr _ _ _ _ _ _ _ (fun i=>by simp [hx i])
        _ = 0 := closedCellCap_at_zero _ _ _ _)
    _ = 0 := integral_zero _ _


def capConstant (A e C₀ G : ℝ) : ℝ :=
  G*Real.exp 1/2+(moderateMarginConstant e C₀+1)*Real.exp (513/A)+2

/-- The literal weighted structured forcing satisfies one quadratic cap bound
for every amplitude from zero to the stated ceiling. The threshold precedes
both dimensions, the source functions, and their amplitude. All moments,
normal envelopes, and the tiny error coefficients are derived. -/
theorem exists_dimension_uniform_structured_cap
    (A K b e C₀ G : ℝ) (hA : 8192 ≤ A) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (he : 0<e) (hC₀ : 0 ≤ C₀) (hG : 0 ≤ G) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ), (∀i,‖R i‖ ≤ 1) →
      ∀ σ α : ℝ, 0<σ → 0<α → NegativeVotingCapTail.CenteredSingularLowerBound B σ →
      e*Real.sqrt (logScale n)/((n:ℝ)+2) ≤ σ →
      (∀i,α^2/2 ≤ inner ℝ (B i) (B i)) → (∀i,inner ℝ (B i) (B i) ≤ 2*α^2) →
      (∀i j,j≠i→inner ℝ (B j) (B i) ≤ α^2/4) →
      (∀i,mass B h i ≤ C₀/((n:ℝ)+2)) →
      (∀i j,‖B i-B j‖ ≤ 1) → 1/σ ≤ ((n:ℝ)+2)^2 →
      (∀i j,i≠j→1/‖B i-B j‖ ≤ ((n:ℝ)+2)^2) →
      (∀i j,i≠j→|pairOffset B h i j| ≤ (n:ℝ)+2) →
      (∀i j,i≠j→((n:ℝ)+2)^(-4096:ℝ) ≤
        (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal) →
      (∀i j,i≠j→(pairOffset B h i j)^2 ≤ b*logScale n) →
      (∀i,(∑j∈Finset.univ.erase i,facetWeight B h i j) ≤ G) →
      ∀ r η τ : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η → η ≤ K*r^2*logScale n →
      0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      let θ:=structuredAmplitude A b r τ D h fD fu
      θ ≤ ((n:ℝ)+2)^(-(5:ℝ)/4) →
      (∫x,closedCellCap B h (weightedForcing R D h η r τ fD fu) 1 x ∂stdGaussian (FSC.Coord d)) ≤
        capConstant A e C₀ G*θ^2 := by
  obtain ⟨N₁,hN₁⟩:=exists_dimension_uniform_normalized_ambient A K (by linarith) hK
  obtain ⟨N₂,hN₂⟩:=exists_dimension_uniform_normalized_facet A K hA hK
  obtain ⟨N₃,hN₃⟩:=exists_dimension_uniform_normalized_pair A K (by linarith) hK
  obtain ⟨N₄,hN₄⟩:=exists_dimension_uniform_normalized_slice A K (by linarith) hK
  obtain ⟨N₅,hN₅⟩:=exists_dimension_uniform_zero_amplitude A K (by linarith) hK
  obtain ⟨N₆,hN₆⟩:=exists_uniform_tiny_cap
  refine ⟨N₁+N₂+N₃+N₄+N₅+N₆,?_⟩
  intro n hn d B R D h hR σ α hσ hα hlower hScale hDiagLower hDiagUpper hCross hmass hdiam hσinv
    hellinv haCoarse hp ha hdegree r η τ hr hrange hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu θ hθceil
  have hθ0 : 0 ≤ θ:=structuredAmplitude_nonneg A b r τ D h fD fu
  by_cases hzero : θ=0
  · have hcapzero:=hN₅ n (by omega) d B R D h hR r η τ b hr hrange hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu hzero
    rw [hcapzero,hzero]
    simp
  have hθ : 0<θ:=lt_of_le_of_ne hθ0 (Ne.symm hzero)
  let v:=normalizedForcing R D h η r τ θ fD fu
  have hinj : Function.Injective B:=by
    intro i j hh
    by_contra hij
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B σ hσ hlower i j hij hh
  have hBne i j (hij:i≠j) : B i≠B j:=fun hh=>hij (hinj hh)
  obtain ⟨hvM,hvmem,hvnorm,hvsum,hvpair⟩:=hN₁ n (by omega) d R D h hR r η τ b hr hrange hη hηupper
    hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu hθ
  have hCapEq : (fun x=>closedCellCap B h (weightedForcing R D h η r τ fD fu) 1 x)=closedCellCap B h v θ:=by
    funext x
    exact closedCellCap_normalized B R D h η r τ θ hzero fD fu x
  rw [hCapEq]
  have hm : (1:ℝ) ≤ (n:ℝ)+2:=by have hh : 0 ≤ (n:ℝ):=Nat.cast_nonneg n; linarith
  have hlog : Real.log ((n:ℝ)+2) ≤ logScale n:=by unfold logScale; linarith
  have hq : 2 ≤ A*logScale n:=by nlinarith [logScale_one_le n]
  by_cases htiny : θ ≤ ((n:ℝ)+2)^(-256:ℝ)
  · have hfacet:=hN₂ n (by omega) d B R D h hinj hR r η τ b G hr hrange hη hηupper hb hG
      hτ hτ1 hqτ hp ha hdegree fD fu hfDM hfuM hfD hfu hθ
    have hslice i j k (hij:i≠j):=hN₄ n (by omega) d B R D h hR r η τ b θ hr hrange hη hηupper hb
      hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu i j k (hBne i j hij) (ha i j hij)
    have hF : totalFacetCoefficient B h v ≤ G*Real.exp 1/2:=by
      have hh:=totalFacetCoefficient_le_two_energy B h hinj v hvM hslice
      linarith
    have hpair i j (hij:i≠j):=hN₃ n (by omega) d B R D h hR r η τ b hr hrange hη hηupper hb
      hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu hθ i j (hBne i j hij) (ha i j hij)
    let W (i j:Fin (n+2)) : ((ℝ ∙ (B i-B j))ᗮ)→ℝ :=
      if hij:i=j then fun _=>0 else (hpair i j hij).choose
    have hW i j (hij:i≠j) :
        Measurable (W i j) ∧ (∀y,0 ≤ W i j y) ∧ MemLp (W i j) 32 (stdGaussian _) ∧
        realLp (stdGaussian _) 32 (W i j) ≤ 1 ∧
        ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
          ContinuousOn (pairPlaneForcing B h i j v y) (Icc (0:ℝ) 1) ∧
          (∀z∈Icc (0:ℝ) 1,pairPlaneForcing B h i j v y z ≤ W i j y) ∧
          (∀z∈Icc (0:ℝ) 1,|pairPlaneForcing B h i j v y z-pairPlaneForcing B h i j v y 0| ≤ W i j y*z):=by
      simpa only [W,dif_neg hij] using (hpair i j hij).choose_spec
    have hcap:=hN₆ (Fin (n+2)) (by simpa using (show N₆ ≤ n+2 by omega)) d B h σ 1
      (by simp) hσ hlower hdiam (by norm_num) le_rfl
      (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] using hellinv)
      (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] using hσinv)
      (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] using haCoarse)
      v hvM (fun i j _=>(hvpair i j).1) (fun i j _=>(hvpair i j).2) W
      (fun i j hij=>(hW i j hij).1) (fun i j hij=>(hW i j hij).2.2.1)
      (fun i j hij=>(hW i j hij).2.2.2.1) (fun i j hij=>(hW i j hij).2.1)
      (fun i j hij=>(hW i j hij).2.2.2.2) θ (G*Real.exp 1/2) hθ
      (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] using htiny) hF
    refine hcap.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg θ))
    unfold capConstant
    have hC : 0 ≤ moderateMarginConstant e C₀+1:=by unfold moderateMarginConstant; positivity
    nlinarith [mul_nonneg hC (Real.exp_pos (513/A)).le]
  · have hW0 i : 0 ≤ fullLabelMajorant A r τ D h fD fu i/θ:=div_nonneg
      (fullLabelMajorant_nonneg A b r τ (by linarith) hr hτ D h fD fu i) hθ.le
    have hcap:=integral_closedCellCap_le_lq_of_initial_gram B h σ α hσ hα hlower e ((n:ℝ)+2)
      (logScale n) C₀ he hm (logScale_one_le n) hlog hC₀ hScale hDiagLower hDiagUpper hCross hmass
      v θ (A*logScale n) (1/2) (fun i=>fullLabelMajorant A r τ D h fD fu i/θ)
      hθ.le hq hW0 (by norm_num) hvsum hvM hvmem hvnorm
    have hC : 0 ≤ moderateMarginConstant e C₀+1:=by unfold moderateMarginConstant; positivity
    have hscalar:=moderate_cap_bound ((n:ℝ)+2) θ (A*logScale n) A 256
      (moderateMarginConstant e C₀+1) (1/4) hm hθ hq (by linarith) (by norm_num) hC
      (mul_le_mul_of_nonneg_left hlog (by linarith)) (by norm_num)
      (by nlinarith [logScale_one_le n]) (le_of_not_ge htiny)
      (by convert hθceil using 1 <;> norm_num)
    have hcap' : (∫x,closedCellCap B h v θ x ∂stdGaussian (FSC.Coord d)) ≤
        ((moderateMarginConstant e C₀+1)*Real.exp (513/A)+1)*θ^2:=by
      have hh : 2*θ*(1/2)=θ:=by ring
      simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,hh] at hcap
      exact hcap.trans (by convert hscalar using 1 <;> norm_num)
    refine hcap'.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg θ))
    unfold capConstant
    nlinarith [mul_nonneg hG (Real.exp_pos (1:ℝ)).le]

end NegativeVotingStructuredSwitchingAllAmplitudes
