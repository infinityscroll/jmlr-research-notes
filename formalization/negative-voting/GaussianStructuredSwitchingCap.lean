import GaussianStructuredSwitchingTube
import GaussianStructuredSwitchingFacetEnergy
import GaussianSwitchingTinyScale
import GaussianSwitchingModerateIntegral
import GaussianSwitchingModerateScale

/-! The literal pair-plane cap conventions are connected to the actual
weighted forcing traces and normal envelopes before scalar scale joining. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingStructuredSwitchingCap
open NegativeVotingFan NegativeVotingDisintegration NegativeVotingWeightedFacet
  NegativeVotingSwitchingPair NegativeVotingSwitchingCell NegativeVotingSwitchingTiny
  NegativeVotingSwitchingOrdered NegativeVotingFanJacobian NegativeVotingTensorFacetAggregation
  NegativeVotingStructuredSwitchingTube NegativeVotingStructuredSwitchingMoments
  NegativeVotingStructuredSwitchingFacet NegativeVotingStructuredSwitchingFacetEnergy
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingFacetDegree NegativeVotingSmoothErrorMoment

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Equality of the actual pair-plane and slice Gaussian laws. -/
theorem pairPlane_map_law (B : ι→FSC.Coord d) (h : ι→ℝ) (i j : ι) (hij : B i≠B j) :
    (stdGaussian ((ℝ ∙ (B i-B j))ᗮ)).map (fun y:((ℝ ∙ (B i-B j))ᗮ)=>pairPlaneBase B h i j+(y:FSC.Coord d))=
      FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) := by
  let e:=LinearIsometryEquiv.ofEq ((ℝ ∙ (B i-B j))ᗮ) (tangentSpace (pairNormal B i j))
    (tangentSpace_pairNormal B i j hij).symm
  rw [sliceLaw_eq_facetChart_map B h i j hij,←stdGaussian_map e,
    Measure.map_map (by unfold facetChart; fun_prop) e.continuous.measurable]
  congr 1
  funext y
  dsimp [facetChart,pairPlaneBase,e]
  exact add_comm _ _

/-- The tiny-cap leading term is an actual ambient facet integral. -/
theorem pairFacetCoefficient_eq_ambient (B : ι→FSC.Coord d) (h : ι→ℝ)
    (v : FSC.Coord d→ι→ℝ) (hvM : ∀i,Measurable (fun x=>v x i)) (i j : ι) (hij:B i≠B j) :
    pairFacetCoefficient B h v i j=
      gaussianPDFReal 0 1 (pairOffset B h i j)/(2*‖B i-B j‖)*
        ∫x in affineFacet B h i j,(max (v x i+v x j) 0)^2
          ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j) := by
  rw [←pairPlane_map_law B h i j hij,
    setIntegral_map (isClosed_affineFacet B h i j).measurableSet
      (by exact (((hvM i).add (hvM j)).max measurable_const).pow_const 2 |>.aestronglyMeasurable)
      (by unfold pairPlaneBase; fun_prop)]
  simp only [pairFacetCoefficient,pairPlaneForcing,zero_smul,add_zero,pairPlaneFacet]
  rfl

/-- An oriented ambient facet-square contribution. -/
def labelFacetEnergy (B : ι→FSC.Coord d) (h : ι→ℝ) (f : FSC.Coord d→ℝ) (i j : ι) : ℝ :=
  gaussianPDFReal 0 1 (pairOffset B h i j)/‖B i-B j‖*
    ∫x in affineFacet B h i j,(f x)^2 ∂FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)

theorem labelFacetEnergy_reverse (B : ι→FSC.Coord d) (h : ι→ℝ) (f : FSC.Coord d→ℝ) (i j : ι) :
    labelFacetEnergy B h f j i=labelFacetEnergy B h f i j := by
  unfold labelFacetEnergy
  rw [pairNormal_reverse B i j,pairOffset_reverse B h i j,norm_sub_rev (B j) (B i),affineFacet_reverse]
  have hp : gaussianPDFReal 0 1 (-pairOffset B h i j)=gaussianPDFReal 0 1 (pairOffset B h i j):=
    NegativeVotingMassCentroid.normalPDF_even _
  rw [hp]
  simp only [FSC.sliceLaw,neg_smul,smul_neg,neg_neg,inner_neg_left]

theorem pairFacetCoefficient_le_labelEnergy (B : ι→FSC.Coord d) (h : ι→ℝ)
    (v : FSC.Coord d→ι→ℝ) (hvM : ∀i,Measurable (fun x=>v x i)) (i j : ι) (hij:B i≠B j)
    (hi : MemLp (fun x=>v x i) 2 ((FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)).restrict (affineFacet B h i j)))
    (hj : MemLp (fun x=>v x j) 2 ((FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)).restrict (affineFacet B h i j))) :
    pairFacetCoefficient B h v i j ≤ labelFacetEnergy B h (fun x=>v x i) i j+
      labelFacetEnergy B h (fun x=>v x j) i j := by
  rw [pairFacetCoefficient_eq_ambient B h v hvM i j hij]
  have hpoint (x:FSC.Coord d) : (max (v x i+v x j) 0)^2 ≤ 2*((v x i)^2+(v x j)^2):=by
    by_cases hp : 0 ≤ v x i+v x j
    · rw [max_eq_left hp]
      nlinarith [sq_nonneg (v x i-v x j)]
    · rw [max_eq_right (le_of_not_ge hp)]
      nlinarith [sq_nonneg (v x i),sq_nonneg (v x j)]
  have hright : Integrable (fun x=>2*((v x i)^2+(v x j)^2))
      ((FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)).restrict (affineFacet B h i j)):=
    (hi.integrable_sq.add hj.integrable_sq).const_mul 2
  have hint : Integrable (fun x=>(max (v x i+v x j) 0)^2)
      ((FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)).restrict (affineFacet B h i j)):=by
    apply hright.mono' (((hvM i).add (hvM j)).max measurable_const |>.pow_const 2 |>.aestronglyMeasurable)
    filter_upwards with x
    simpa only [Pi.add_apply,Real.norm_eq_abs,abs_pow,sq_abs] using hpoint x
  have hb:=integral_mono hint hright hpoint
  rw [integral_const_mul,integral_add hi.integrable_sq hj.integrable_sq] at hb
  have hc : 0 ≤ gaussianPDFReal 0 1 (pairOffset B h i j)/(2*‖B i-B j‖):=
    div_nonneg (gaussianPDFReal_nonneg _ _ _) (mul_nonneg (by norm_num) (norm_nonneg _))
  refine (mul_le_mul_of_nonneg_left hb hc).trans_eq ?_
  unfold labelFacetEnergy
  ring

/-- This measurable version permits actual smoothed L2 representatives. -/
theorem labelFacetEnergy_sum_eq_intrinsic (B : ι→FSC.Coord d) (h : ι→ℝ)
    (hinj : Function.Injective B) (v : FSC.Coord d→ι→ℝ)
    (hvM : ∀i,Measurable (fun x=>v x i)) :
    (∑i,∑j∈Finset.univ.erase i,labelFacetEnergy B h (fun x=>v x i) i j)=
      affineWeightedFacetEnergy B h (fun i x=>v x i) := by
  unfold labelFacetEnergy affineWeightedFacetEnergy orderedFacetEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij : B i≠B j:=fun he=>(Finset.mem_erase.mp hj).1 (hinj he).symm
  rw [sliceLaw_eq_facetChart_map B h i j hij,
    setIntegral_map (isClosed_affineFacet B h i j).measurableSet
      ((hvM i).pow_const 2).aestronglyMeasurable (by unfold facetChart; fun_prop)]
  rfl

/-- The leading pair coefficient costs only two actual weighted label energies. -/
theorem totalFacetCoefficient_le_two_energy (B : ι→FSC.Coord d) (h : ι→ℝ)
    (hinj : Function.Injective B) (v : FSC.Coord d→ι→ℝ)
    (hvM : ∀i,Measurable (fun x=>v x i))
    (hv : ∀i j k,i≠j→MemLp (fun x=>v x k) 2
      ((FSC.sliceLaw (pairNormal B i j) (pairOffset B h i j)).restrict (affineFacet B h i j))) :
    totalFacetCoefficient B h v ≤ 2*affineWeightedFacetEnergy B h (fun i x=>v x i) := by
  have hh : totalFacetCoefficient B h v ≤
      (∑i,∑j∈Finset.univ.erase i,labelFacetEnergy B h (fun x=>v x i) i j)+
      (∑i,∑j∈Finset.univ.erase i,labelFacetEnergy B h (fun x=>v x j) j i) := by
    simp only [totalFacetCoefficient,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have hij : i≠j:=(Finset.mem_erase.mp hj).1.symm
    rw [labelFacetEnergy_reverse B h (fun x=>v x j) i j]
    exact pairFacetCoefficient_le_labelEnergy B h v hvM i j (fun he=>hij (hinj he))
      (hv i j i hij) (hv i j j hij)
  have hswap : (∑i,∑j∈Finset.univ.erase i,labelFacetEnergy B h (fun x=>v x j) j i)=
      ∑i,∑j∈Finset.univ.erase i,labelFacetEnergy B h (fun x=>v x i) i j := by
    simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    rw [Finset.sum_sub_distrib,Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
  rw [hswap,labelFacetEnergy_sum_eq_intrinsic B h hinj v hvM] at hh
  linarith


def tubeLabelMajorant {n : ℕ} (A b r τ a : ℝ) (w : FSC.Coord d)
    (D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (i : Fin (n+2)) : ℝ :=
  4*planeDampingCoefficient b*(r*tubeErrorCoefficient A b n*
    (τ⁻¹*(‖D i‖+|a*inner ℝ (D i) w+h i|)+|inner ℝ (D i) w|)+
    normalOUCoefficient τ a*(realLp (stdGaussian (FSC.Coord d)) 2 (fD i)+
      realLp (stdGaussian (FSC.Coord d)) 2 (fu i))/r)

/-- The literal tiny-cap pair-plane control, derived for normalized actual
weighted forcing. The parameter θ has no positive lower bound. -/
theorem exists_dimension_uniform_pair_control (A K : ℝ) (hA : 32 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (B R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ), (∀i,‖R i‖ ≤ 1) →
      ∀ r η τ b θ : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n → 0 ≤ b → 0<θ →
        0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      ∀ i j : Fin (n+2), B i≠B j → (pairOffset B h i j)^2 ≤ b*logScale n →
      ∃ W : ((ℝ ∙ (B i-B j))ᗮ)→ℝ,
      Measurable W ∧ (∀y,0 ≤ W y) ∧ MemLp W 32 (stdGaussian _) ∧
      realLp (stdGaussian _) 32 W ≤
        (tubeLabelMajorant A b r τ (pairOffset B h i j) (pairNormal B i j) D h fD fu i+
          tubeLabelMajorant A b r τ (pairOffset B h i j) (pairNormal B i j) D h fD fu j)/θ ∧
      ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
        ContinuousOn (pairPlaneForcing B h i j (fun x k=>weightedForcing R D h η r τ fD fu x k/θ) y) (Icc 0 1) ∧
        (∀t∈Icc (0:ℝ) 1,pairPlaneForcing B h i j
          (fun x k=>weightedForcing R D h η r τ fD fu x k/θ) y t ≤ W y) ∧
        (∀t∈Icc (0:ℝ) 1,|pairPlaneForcing B h i j
          (fun x k=>weightedForcing R D h η r τ fD fu x k/θ) y t-
          pairPlaneForcing B h i j (fun x k=>weightedForcing R D h η r τ fD fu x k/θ) y 0| ≤ W y*t) := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_weightedForcing_tube_control A K (by linarith) hK
  refine ⟨N,?_⟩
  intro n hn d B R D h hR r η τ b θ hr hrange hη hηupper hb hθ hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu i j hij ha
  let w:=pairNormal B i j
  let a:=pairOffset B h i j
  let e:=canonicalTangentCoordinates w
  have hw : ‖w‖=1:=pairNormal_norm B i j hij
  obtain ⟨Wi,hWiM,hWi0,hWimem,hWinorm,hWicontrol⟩:=hN n hn d _ R D h hR w e hw r η τ a b
    hr hrange hη hηupper hb ha hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu i
  obtain ⟨Wj,hWjM,hWj0,hWjmem,hWjnorm,hWjcontrol⟩:=hN n hn d _ R D h hR w e hw r η τ a b
    hr hrange hη hηupper hb ha hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu j
  let T:=LinearIsometryEquiv.ofEq ((ℝ ∙ (B i-B j))ᗮ) (tangentSpace w)
    (tangentSpace_pairNormal B i j hij).symm
  have hmp : MeasurePreserving T (stdGaussian ((ℝ ∙ (B i-B j))ᗮ)) (stdGaussian (tangentSpace w)):=
    ⟨T.continuous.measurable,stdGaussian_map T⟩
  have hq : (32:ℝ≥0∞) ≤ ENNReal.ofReal (A*logScale n):=by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (32:ℝ) ≤ A*logScale n by nlinarith [logScale_one_le n])
  have him : MemLp (Wi ∘ T) 32 (stdGaussian ((ℝ ∙ (B i-B j))ᗮ)):=
    (hWimem.mono_exponent hq).comp_measurePreserving hmp
  have hjm : MemLp (Wj ∘ T) 32 (stdGaussian ((ℝ ∙ (B i-B j))ᗮ)):=
    (hWjmem.mono_exponent hq).comp_measurePreserving hmp
  have hin : realLp (stdGaussian ((ℝ ∙ (B i-B j))ᗮ)) 32 (Wi ∘ T) ≤
      tubeLabelMajorant A b r τ a w D h fD fu i := by
    unfold realLp
    rw [eLpNorm_comp_measurePreserving hWiM.aestronglyMeasurable hmp]
    exact (ENNReal.toReal_mono hWimem.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hq)).trans hWinorm
  have hjn : realLp (stdGaussian ((ℝ ∙ (B i-B j))ᗮ)) 32 (Wj ∘ T) ≤
      tubeLabelMajorant A b r τ a w D h fD fu j := by
    unfold realLp
    rw [eLpNorm_comp_measurePreserving hWjM.aestronglyMeasurable hmp]
    exact (ENNReal.toReal_mono hWjmem.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hq)).trans hWjnorm
  let W:=fun y:((ℝ ∙ (B i-B j))ᗮ)=>(Wi (T y)+Wj (T y))/θ
  have hWeq : W=(fun y=>θ⁻¹*((Wi ∘ T) y+(Wj ∘ T) y)):=by funext y; dsimp [W]; ring
  refine ⟨W,by dsimp [W]; fun_prop,fun y=>div_nonneg (add_nonneg (hWi0 _) (hWj0 _)) hθ.le,?_,?_,?_⟩
  · rw [hWeq]
    exact (him.add hjm).const_mul θ⁻¹
  · rw [hWeq,realLp_const_mul,abs_of_pos (inv_pos.mpr hθ)]
    have hh:=(realLp_add_le (by norm_num : (1:ℝ≥0∞) ≤ 32) him hjm).trans (add_le_add hin hjn)
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hθ.le)).trans_eq (by ring)
  · filter_upwards [hmp.quasiMeasurePreserving.ae hWicontrol,hmp.quasiMeasurePreserving.ae hWjcontrol] with y hiy hjy
    have hh:=(hiy.add hjy).const_mul θ⁻¹
    rw [abs_of_pos (inv_pos.mpr hθ)] at hh
    have hx (t:ℝ) : pairPlaneBase B h i j+(y:FSC.Coord d)+t • pairNormal B i j=
        ((T y:tangentSpace w):FSC.Coord d)+(a+t) • w:=by
      dsimp [T,a,w,pairPlaneBase]
      simp only [add_smul]
      module
    have he : (fun t=>θ⁻¹*(weightedForcing R D h η r τ fD fu (((T y:tangentSpace w):FSC.Coord d)+(a+t) • w) i+
        weightedForcing R D h η r τ fD fu (((T y:tangentSpace w):FSC.Coord d)+(a+t) • w) j))=
        pairPlaneForcing B h i j (fun x k=>weightedForcing R D h η r τ fD fu x k/θ) y := by
      funext t
      dsimp only [pairPlaneForcing]
      rw [hx]
      ring
    rw [he] at hh
    have hc : IntervalControl (pairPlaneForcing B h i j
        (fun x k=>weightedForcing R D h η r τ fD fu x k/θ) y) (W y):=by
      convert hh using 1
      dsimp [W]
      ring
    exact ⟨hc.continuous,fun t ht=>(le_abs_self _).trans (hc.bound t ht),hc.increment⟩

end NegativeVotingStructuredSwitchingCap
