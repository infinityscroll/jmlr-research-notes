import GaussianStructuredSwitchingCap

/-! A literal amplitude computed from the row/offset and residual-input
majorants.  Normalizing by it introduces no positive amplitude floor. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingStructuredSwitchingAmplitude
open NegativeVotingStructuredSwitchingCap NegativeVotingStructuredSwitchingTube
  NegativeVotingStructuredSwitchingMoments NegativeVotingStructuredSwitchingFacet
  NegativeVotingStructuredSwitchingFacetEnergy NegativeVotingNormalTrace NegativeVotingNormalDerivatives
  NegativeVotingSmoothErrorMoment NegativeVotingDisintegration NegativeVotingActualFacetOUTrace
  NegativeVotingReciprocalDampingTube NegativeVotingRegularPairCoefficient
  NegativeVotingFan NegativeVotingWeightedFacet NegativeVotingFanJacobian NegativeVotingSwitchingPair
variable {d n : ℕ}

def fullLabelMajorant (A r τ : ℝ) (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (i : Fin (n+2)) : ℝ :=
  dampingMomentConstant*(r*errorMomentCoefficient A n*τ⁻¹*(‖D i‖+|h i|)+
    (realLp (stdGaussian (FSC.Coord d)) 2 (fD i)+realLp (stdGaussian (FSC.Coord d)) 2 (fu i))/r)

def uniformTubeMajorant (A b r τ : ℝ) (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (i : Fin (n+2)) : ℝ :=
  4*planeDampingCoefficient b*(r*tubeErrorCoefficient A b n*
    (τ⁻¹*((1+Real.sqrt (b*logScale n))*‖D i‖+|h i|)+‖D i‖)+
    normalOUCoefficient τ (Real.sqrt (b*logScale n))*
      (realLp (stdGaussian (FSC.Coord d)) 2 (fD i)+realLp (stdGaussian (FSC.Coord d)) 2 (fu i))/r)

def structuredAmplitude (A b r τ : ℝ) (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) : ℝ :=
  2*(Real.sqrt (∑i,(fullLabelMajorant A r τ D h fD fu i)^2)+
    Real.sqrt (∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2)+
    Real.sqrt (∑i,(uniformTubeMajorant A b r τ D h fD fu i)^2))

theorem structuredAmplitude_nonneg (A b r τ : ℝ) (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) : 0 ≤ structuredAmplitude A b r τ D h fD fu := by
  unfold structuredAmplitude
  positivity

section Finite
variable {ι : Type*} [Fintype ι]

theorem label_le_sqrt_sum_sq (c : ι→ℝ) (i : ι) : c i ≤ Real.sqrt (∑j,(c j)^2) := by
  apply le_trans (le_abs_self _) (Real.le_sqrt_of_sq_le _)
  simpa only [sq_abs] using Finset.single_le_sum (fun j (_:j∈Finset.univ)=>sq_nonneg (c j)) (Finset.mem_univ i)

theorem normalized_sum_sq_le_quarter (c : ι→ℝ) (θ : ℝ) (hθ : 0<θ)
    (hbound : 2*Real.sqrt (∑i,(c i)^2) ≤ θ) :
    (∑i,(c i/θ)^2) ≤ (1/2:ℝ)^2 := by
  have hs : 0 ≤ ∑i,(c i)^2:=Finset.sum_nonneg fun i _=>sq_nonneg _
  rw [show (∑i,(c i/θ)^2)=(∑i,(c i)^2)/θ^2 by simp only [div_pow,Finset.sum_div]]
  apply (div_le_iff₀ (sq_pos_of_pos hθ)).mpr
  have hh:=Real.sq_sqrt hs
  have hp:=Real.sqrt_nonneg (∑i,(c i)^2)
  nlinarith
end Finite

theorem amplitude_full_bound (A b r τ : ℝ) (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) :
    2*Real.sqrt (∑i,(fullLabelMajorant A r τ D h fD fu i)^2) ≤ structuredAmplitude A b r τ D h fD fu := by
  unfold structuredAmplitude
  linarith [Real.sqrt_nonneg (∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2),
    Real.sqrt_nonneg (∑i,(uniformTubeMajorant A b r τ D h fD fu i)^2)]

theorem amplitude_facet_bound (A b r τ : ℝ) (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) :
    2*Real.sqrt (∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2) ≤ structuredAmplitude A b r τ D h fD fu := by
  unfold structuredAmplitude
  linarith [Real.sqrt_nonneg (∑i,(fullLabelMajorant A r τ D h fD fu i)^2),
    Real.sqrt_nonneg (∑i,(uniformTubeMajorant A b r τ D h fD fu i)^2)]

theorem amplitude_tube_bound (A b r τ : ℝ) (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) :
    2*Real.sqrt (∑i,(uniformTubeMajorant A b r τ D h fD fu i)^2) ≤ structuredAmplitude A b r τ D h fD fu := by
  unfold structuredAmplitude
  linarith [Real.sqrt_nonneg (∑i,(fullLabelMajorant A r τ D h fD fu i)^2),
    Real.sqrt_nonneg (∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2)]

theorem normalOUCoefficient_mono {τ a amax : ℝ} (hτ : τ^2<1) (hamax : 0 ≤ amax) (ha : |a| ≤ amax) :
    normalOUCoefficient τ a ≤ normalOUCoefficient τ amax := by
  have hA : 0 ≤ amax+1:=by linarith
  have ht : |(|a|+1)| ≤ amax+1:=by rw [abs_of_nonneg (by positivity : 0 ≤ |a|+1)]; linarith
  unfold normalOUCoefficient
  rw [abs_of_nonneg hamax]
  exact add_le_add (Real.sqrt_le_sqrt (normalRowSquare_mono_abs hA ht))
    (Real.sqrt_le_sqrt (normalDerivativeRowSquare_mono_abs hτ hA ht))

theorem tubeLabelMajorant_le_uniform (A b r τ a : ℝ) (hA : 0 ≤ A) (hr : 0<r) (hτ : 0<τ) (hτ1 : τ<1)
    (w : FSC.Coord d) (hw : ‖w‖=1) (ha : a^2 ≤ b*logScale n)
    (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (i : Fin (n+2)) :
    tubeLabelMajorant A b r τ a w D h fD fu i ≤ uniformTubeMajorant A b r τ D h fD fu i := by
  have habs : |a| ≤ Real.sqrt (b*logScale n):=by apply Real.le_sqrt_of_sq_le; simpa only [sq_abs] using ha
  have hinner : |inner ℝ (D i) w| ≤ ‖D i‖:=by simpa only [hw,mul_one] using abs_real_inner_le_norm (D i) w
  have hgap : ‖D i‖+|a*inner ℝ (D i) w+h i| ≤
      (1+Real.sqrt (b*logScale n))*‖D i‖+|h i|:=by
    have hh:=mul_le_mul habs hinner (abs_nonneg _) (Real.sqrt_nonneg _)
    have had:=abs_add_le (a*inner ℝ (D i) w) (h i)
    rw [abs_mul] at had
    nlinarith only [hh,had]
  have hE : 0 ≤ tubeErrorCoefficient A b n:=by
    have hc:=NegativeVotingSmoothErrorTube.tubeConstant_nonneg (4*A) (by positivity)
    have hl:0 ≤ logScale n:=by linarith [logScale_one_le n]
    unfold tubeErrorCoefficient
    positivity
  have hC:=normalOUCoefficient_mono (by nlinarith : τ^2<1) (Real.sqrt_nonneg _) habs
  unfold tubeLabelMajorant uniformTubeMajorant
  apply mul_le_mul_of_nonneg_left _ (by unfold planeDampingCoefficient; positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hr.le hE)
    exact add_le_add (mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr hτ.le)) hinner
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC
      (add_nonneg (realLp_nonneg _ _) (realLp_nonneg _ _))) hr.le

theorem weightedForcing_measurable (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (η r τ : ℝ) (fD fu : Fin (n+2)→FSC.Coord d→ℝ)
    (hfDM : ∀i,Measurable (fD i)) (hfuM : ∀i,Measurable (fu i)) (i : Fin (n+2)) :
    Measurable (fun x=>weightedForcing R D h η r τ fD fu x i) := by
  have hκ : Measurable (fun x:FSC.Coord d=>inverseKappa η (fun j=>inner ℝ (R j) x)):=by
    simp only [inverseKappa_eq_exp,scoreEnergy]
    fun_prop
  have hε : Measurable (fun x:FSC.Coord d=>smoothPairError n r (fun j=>inner ℝ (R j) x)):=
    (smoothPairError_contDiff n r).continuous.measurable.comp (by fun_prop)
  have hd:=ambientAverage_measurable τ (fD i) (hfDM i)
  have hu:=ambientAverage_measurable τ (fu i) (hfuM i)
  unfold weightedForcing
  fun_prop


def normalizedForcing (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (η r τ θ : ℝ) (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (x : FSC.Coord d) (i : Fin (n+2)) : ℝ :=
  weightedForcing R D h η r τ fD fu x i/θ

theorem fullLabelMajorant_nonneg (A b r τ : ℝ) (hA : 0 ≤ A) (hr : 0<r) (hτ : 0<τ)
    (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (i : Fin (n+2)) :
    0 ≤ fullLabelMajorant A r τ D h fD fu i := by
  have he:=errorMomentCoefficient_nonneg A hA n
  have hk:=dampingMomentConstant_nonneg
  unfold fullLabelMajorant
  exact mul_nonneg hk (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hr.le he)
    (inv_nonneg.mpr hτ.le)) (add_nonneg (norm_nonneg _) (abs_nonneg _)))
    (div_nonneg (add_nonneg (realLp_nonneg _ _) (realLp_nonneg _ _)) hr.le))

/-- The computed amplitude supplies the exact vector moment hypothesis of the
moderate cap and the full-space L32 hypothesis of the tiny cap. -/
theorem exists_dimension_uniform_normalized_ambient (A K : ℝ) (hA : 32 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ), (∀i,‖R i‖ ≤ 1) →
      ∀ r η τ b : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η → η ≤ K*r^2*logScale n →
      0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      let θ:=structuredAmplitude A b r τ D h fD fu
      let v:=normalizedForcing R D h η r τ θ fD fu
      0<θ →
      (∀i,Measurable (fun x=>v x i)) ∧
      (∀i,MemLp (fun x=>v x i) (ENNReal.ofReal (A*logScale n)) (stdGaussian (FSC.Coord d))) ∧
      (∀i,eLpNorm (fun x=>v x i) (ENNReal.ofReal (A*logScale n)) (stdGaussian (FSC.Coord d)) ≤
        ENNReal.ofReal (fullLabelMajorant A r τ D h fD fu i/θ)) ∧
      (∑i,(fullLabelMajorant A r τ D h fD fu i/θ)^2) ≤ (1/2:ℝ)^2 ∧
      (∀i j,MemLp (fun x=>v x i+v x j) 32 (stdGaussian (FSC.Coord d)) ∧
        realLp (stdGaussian (FSC.Coord d)) 32 (fun x=>v x i+v x j) ≤ 1) := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_forcing_common_moments A K (by linarith) hK
  refine ⟨N,?_⟩
  intro n hn d R D h hR r η τ b hr hrange hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu θ v hθ
  obtain ⟨hκ,hε⟩:=hN n hn d R hR r η hr hrange hη hηupper
  have hq : 1 ≤ A*logScale n:=by nlinarith [logScale_one_le n]
  have hq32 : (32:ℝ≥0∞) ≤ ENNReal.ofReal (A*logScale n):=by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (32:ℝ) ≤ A*logScale n by nlinarith [logScale_one_le n])
  have hC0 i : 0 ≤ fullLabelMajorant A r τ D h fD fu i:=
    fullLabelMajorant_nonneg A b r τ (by linarith) hr hτ D h fD fu i
  have hlabel i := weightedForcing_label_norm_le R D h η r τ (A*logScale n)
    dampingMomentConstant (errorMomentCoefficient A n) hr hτ hτ1 hq hqτ
    dampingMomentConstant_nonneg (errorMomentCoefficient_nonneg A (by linarith) n)
    hκ hε fD fu hfDM hfuM hfD hfu i
  have he i : (fun x=>v x i)=(fun x=>θ⁻¹*weightedForcing R D h η r τ fD fu x i):=by
    funext x
    dsimp [v,normalizedForcing]
    ring
  have hmem i : MemLp (fun x=>v x i) (ENNReal.ofReal (A*logScale n)) (stdGaussian (FSC.Coord d)):=by
    rw [he]
    exact (hlabel i).1.const_mul θ⁻¹
  have hnorm i : eLpNorm (fun x=>v x i) (ENNReal.ofReal (A*logScale n)) (stdGaussian (FSC.Coord d)) ≤
      ENNReal.ofReal (fullLabelMajorant A r τ D h fD fu i/θ):=by
    have hrn : realLp (stdGaussian (FSC.Coord d)) (ENNReal.ofReal (A*logScale n)) (fun x=>v x i) ≤
        fullLabelMajorant A r τ D h fD fu i/θ:=by
      rw [he,realLp_const_mul,abs_of_pos (inv_pos.mpr hθ)]
      exact (mul_le_mul_of_nonneg_left (hlabel i).2 (inv_nonneg.mpr hθ.le)).trans_eq (by dsimp [fullLabelMajorant]; ring)
    rw [←ENNReal.ofReal_toReal (hmem i).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hrn
  have hCθ i : fullLabelMajorant A r τ D h fD fu i/θ ≤ 1/2:=by
    have hh:=(label_le_sqrt_sum_sq (fullLabelMajorant A r τ D h fD fu) i)
    have ha:=amplitude_full_bound A b r τ D h fD fu
    apply (div_le_iff₀ hθ).mpr
    change _ ≤ θ at ha
    linarith
  refine ⟨fun i=>(weightedForcing_measurable R D h η r τ fD fu hfDM hfuM i).div_const θ,
    hmem,hnorm,normalized_sum_sq_le_quarter _ θ hθ (amplitude_full_bound A b r τ D h fD fu),?_⟩
  intro i j
  have hi:=(hmem i).mono_exponent hq32
  have hj:=(hmem j).mono_exponent hq32
  have hnri : realLp (stdGaussian (FSC.Coord d)) 32 (fun x=>v x i) ≤ fullLabelMajorant A r τ D h fD fu i/θ:=by
    have hb:=(eLpNorm_le_eLpNorm_of_exponent_le hq32).trans (hnorm i)
    simpa only [realLp,ENNReal.toReal_ofReal (div_nonneg (hC0 i) hθ.le)] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  have hnrj : realLp (stdGaussian (FSC.Coord d)) 32 (fun x=>v x j) ≤ fullLabelMajorant A r τ D h fD fu j/θ:=by
    have hb:=(eLpNorm_le_eLpNorm_of_exponent_le hq32).trans (hnorm j)
    simpa only [realLp,ENNReal.toReal_ofReal (div_nonneg (hC0 j) hθ.le)] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  refine ⟨hi.add hj,?_⟩
  exact (realLp_add_le (by norm_num : (1:ℝ≥0∞) ≤ 32) hi hj).trans
    ((add_le_add hnri hnrj).trans (by linarith [hCθ i,hCθ j]))


/-- Exact quadratic scaling of the genuine weighted facet energy. -/
theorem affineWeightedFacetEnergy_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι→FSC.Coord d) (h : ι→ℝ) (f : ι→FSC.Coord d→ℝ) (θ : ℝ) :
    affineWeightedFacetEnergy B h (fun i x=>f i x/θ)=affineWeightedFacetEnergy B h f/θ^2 := by
  unfold affineWeightedFacetEnergy orderedFacetEnergy
  simp only [div_pow,integral_div,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The facet normalization uses the actual label majorant square sum. -/
theorem exists_dimension_uniform_normalized_facet (A K : ℝ) (hA : 8192 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ),
      Function.Injective B → (∀i,‖R i‖ ≤ 1) →
      ∀ r η τ b G : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n → 0 ≤ b → 0 ≤ G →
        0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      (∀i j,i≠j→((n:ℝ)+2)^(-4096:ℝ) ≤
        (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal) →
      (∀i j,i≠j→(pairOffset B h i j)^2 ≤ b*logScale n) →
      (∀i,(∑j∈Finset.univ.erase i,facetWeight B h i j) ≤ G) →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      let θ:=structuredAmplitude A b r τ D h fD fu
      0<θ → affineWeightedFacetEnergy B h (fun i x=>normalizedForcing R D h η r τ θ fD fu x i) ≤
        G*Real.exp 1/4 := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_weightedForcing_facet_energy_le A K hA hK
  refine ⟨N,?_⟩
  intro n hn d B R D h hinj hR r η τ b G hr hrange hη hηupper hb hG hτ hτ1 hqτ hp ha hdegree
    fD fu hfDM hfuM hfD hfu θ hθ
  have hbound:=hN n hn d B R D h hinj hR r η τ b G hr hrange hη hηupper hb hG hτ hτ1 hqτ
    hp ha hdegree fD fu hfDM hfuM hfD hfu
  have hs:=normalized_sum_sq_le_quarter (forcingLabelMajorant A b r τ D h fD fu) θ hθ
    (amplitude_facet_bound A b r τ D h fD fu)
  rw [show (∑i,(forcingLabelMajorant A b r τ D h fD fu i/θ)^2)=
      (∑i,(forcingLabelMajorant A b r τ D h fD fu i)^2)/θ^2 by simp only [div_pow,Finset.sum_div]] at hs
  change affineWeightedFacetEnergy B h (fun i x=>weightedForcing R D h η r τ fD fu x i/θ) ≤ _
  rw [affineWeightedFacetEnergy_div]
  have hh:=div_le_div_of_nonneg_right hbound (sq_nonneg θ)
  refine hh.trans ?_
  have hh':=mul_le_mul_of_nonneg_left hs (mul_nonneg hG (Real.exp_pos (1:ℝ)).le)
  convert hh' using 1 <;> ring

/-- Every actual pair envelope has L32 norm at most one after normalization
by the computed amplitude. No unproved polynomial bound is used here. -/
theorem exists_dimension_uniform_normalized_pair (A K : ℝ) (hA : 32 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ), (∀i,‖R i‖ ≤ 1) →
      ∀ r η τ b : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n → 0 ≤ b →
        0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      let θ:=structuredAmplitude A b r τ D h fD fu
      let v:=normalizedForcing R D h η r τ θ fD fu
      0<θ → ∀i j,B i≠B j → (pairOffset B h i j)^2 ≤ b*logScale n →
      ∃ W : ((ℝ ∙ (B i-B j))ᗮ)→ℝ,
      Measurable W ∧ (∀y,0 ≤ W y) ∧ MemLp W 32 (stdGaussian _) ∧
      realLp (stdGaussian _) 32 W ≤ 1 ∧
      ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
        ContinuousOn (pairPlaneForcing B h i j v y) (Icc 0 1) ∧
        (∀t∈Icc (0:ℝ) 1,pairPlaneForcing B h i j v y t ≤ W y) ∧
        (∀t∈Icc (0:ℝ) 1,|pairPlaneForcing B h i j v y t-pairPlaneForcing B h i j v y 0| ≤ W y*t) := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_pair_control A K hA hK
  refine ⟨N,?_⟩
  intro n hn d B R D h hR r η τ b hr hrange hη hηupper hb hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu θ v hθ i j hij ha
  obtain ⟨W,hWM,hW0,hWmem,hWnorm,hWcontrol⟩:=hN n hn d B R D h hR r η τ b θ hr hrange
    hη hηupper hb hθ hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu i j hij ha
  have hbound k : tubeLabelMajorant A b r τ (pairOffset B h i j) (pairNormal B i j) D h fD fu k ≤ θ/2:=by
    have h1:=tubeLabelMajorant_le_uniform A b r τ (pairOffset B h i j) (by linarith) hr hτ hτ1
      (pairNormal B i j) (pairNormal_norm B i j hij) ha D h fD fu k
    have h2:=label_le_sqrt_sum_sq (uniformTubeMajorant A b r τ D h fD fu) k
    have h3:=amplitude_tube_bound A b r τ D h fD fu
    change _ ≤ θ at h3
    linarith
  refine ⟨W,hWM,hW0,hWmem,?_,hWcontrol⟩
  refine hWnorm.trans ((div_le_one hθ).mpr ?_)
  linarith [hbound i,hbound j]


/-- The normalized literal forcing is square-integrable on every actual
slice and hence on every facet; this is a trace theorem, not restriction
of an ambient almost-everywhere identity. -/
theorem exists_dimension_uniform_normalized_slice (A K : ℝ) (hA : 2 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ), (∀i,‖R i‖ ≤ 1) →
      ∀ r η τ b θ : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n → 0 ≤ b →
        0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      ∀i j k,B i≠B j → (pairOffset B h i j)^2 ≤ b*logScale n →
        MemLp (fun x=>normalizedForcing R D h η r τ θ fD fu x k) 2
          ((FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)).restrict (affineFacet B h i j)) := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_weightedForcing_plane_norm_le A K (by linarith) hK
  refine ⟨N,?_⟩
  intro n hn d B R D h hR r η τ b θ hr hrange hη hηupper hb hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu i j k hij ha
  have hm:=(hN n hn d _ R D h hR (pairNormal B i j) (canonicalTangentCoordinates _)
    (pairNormal_norm B i j hij) r η τ (pairOffset B h i j) b hr hrange hη hηupper hb ha
    hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu k).1
  have hq : (2:ℝ≥0∞) ≤ ENNReal.ofReal (A*logScale n):=by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (2:ℝ) ≤ A*logScale n by nlinarith [logScale_one_le n])
  have hslice : MemLp (fun x=>weightedForcing R D h η r τ fD fu x k) 2
      (FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)):=by
    rw [NegativeVotingPolynomialFacetGeometricTrace.sliceLaw_eq_facetChart_map B h i j hij]
    apply (memLp_map_measure_iff (weightedForcing_measurable R D h η r τ fD fu hfDM hfuM k).aestronglyMeasurable
      (by unfold facetChart; fun_prop)).mpr
    exact hm.mono_exponent hq
  have he : (fun x=>normalizedForcing R D h η r τ θ fD fu x k)=
      (fun x=>θ⁻¹*weightedForcing R D h η r τ fD fu x k):=by
    funext x
    unfold normalizedForcing
    ring
  rw [he]
  exact (hslice.const_mul θ⁻¹).restrict _

end NegativeVotingStructuredSwitchingAmplitude
