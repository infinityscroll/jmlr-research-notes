import GaussianRegularPairCoefficient

/-! Quantitative bounds on the actual continuous divided regular-noise
coefficient. The envelope depends on score range, not ambient norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingRegularPairCoefficient
open NegativeVoting NegativeVotingFan NegativeVotingFanJacobian
  NegativeVotingRegularMassSeparation NegativeVotingRegularMassSymmetry
  NegativeVotingFacetConditionalPlane NegativeVotingCenteredParseval
  NegativeVotingRegularScoreProjection NegativeVotingRegularNoisePair
  NegativeVotingBalancedReference NegativeVotingRegularFacetRange
variable {n d : ℕ}

def rangeExponent (n : ℕ) (R : ℝ) : ℝ :=
  rangeFacetConstant*(R*Real.sqrt (1+Real.log ((n:ℝ)+2))+R^2)

theorem rangeExponent_nonneg (n : ℕ) (R : ℝ) (hR : 0 ≤ R) : 0 ≤ rangeExponent n R := by
  have hc := rangeFacetConstant_pos
  unfold rangeExponent
  positivity

theorem rangeExponent_mono (n : ℕ) (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) :
    rangeExponent n R ≤ rangeExponent n S := by
  unfold rangeExponent
  apply mul_le_mul_of_nonneg_left _ rangeFacetConstant_pos.le
  have h1 := mul_le_mul_of_nonneg_right hRS (Real.sqrt_nonneg (1+Real.log ((n:ℝ)+2)))
  have h2 := mul_nonneg (sub_nonneg.mpr hRS) (show 0 ≤ S+R by linarith)
  nlinarith

section Finite
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem laplacian_pair_upper (w : V → V → ℝ) (a Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hw : ∀k l,k≠l → w k l ≤ a) (i j : V) (hij : i≠j) :
    (∑k,w i k*(pairVelocity i j Δ i-pairVelocity i j Δ k))-
      (∑k,w j k*(pairVelocity i j Δ j-pairVelocity i j Δ k)) ≤
        (Fintype.card V:ℝ)*a*Δ := by
  have hh := laplacian_pair_lower (fun k l => -w k l) (-a) Δ hΔ
    (fun k l hkl => neg_le_neg (hw k l hkl)) i j hij
  simp only [neg_mul,Finset.sum_neg_distrib] at hh
  nlinarith
end Finite

theorem pairSlope_range_bounds (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) (h : FSC.Coord d) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    referenceScale n*Real.exp (-rangeExponent n (utilityRange (scoreOffsets B h))) ≤
      pairSlope B i j h t ∧ pairSlope B i j h t ≤
        referenceScale n*Real.exp (rangeExponent n (utilityRange (scoreOffsets B h))) := by
  let Q := rangeExponent n (utilityRange (scoreOffsets B h))
  let w0 := referenceScale n/((n:ℝ)+2)
  have hw0 : 0 ≤ w0 := (div_pos (referenceScale_pos n) (by positivity)).le
  have hm : (n:ℝ)+2≠0 := by positivity
  have hG' : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hlower := centered_singular_one B hG'
  have hw (k l : Fin (n+2)) (hkl : k≠l) :
      w0*Real.exp (-Q) ≤ facetWeight B (scoreOffsets B (pairPath B i j h t)) k l ∧
      facetWeight B (scoreOffsets B (pairPath B i j h t)) k l ≤ w0*Real.exp Q := by
    have hh := regular_facetWeight_range_bounds hn hmean B hG (pairPath B i j h t) k l hkl
    have hq := rangeExponent_mono n _ _
      (utilityRange_nonneg (scoreOffsets B (pairPath B i j h t)))
      (pairPath_utilityRange_le B hG i j hij h t ht)
    constructor
    · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hq)) hw0).trans hh.1
    · exact hh.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hq) hw0)
  unfold pairSlope
  rw [massDerivative_apply B 1 (by norm_num) hlower,
    massDerivative_apply B 1 (by norm_num) hlower]
  constructor
  · have hh := laplacian_pair_lower (fun k l => facetWeight B
      (scoreOffsets B (pairPath B i j h t)) k l) (w0*Real.exp (-Q)) 1
      (by norm_num) (fun k l hkl => (hw k l hkl).1) i j hij
    have he : (Fintype.card (Fin (n+2)):ℝ)*(w0*Real.exp (-Q))*1=
        referenceScale n*Real.exp (-Q) := by
      simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,mul_one,w0]
      field_simp
    rw [he] at hh
    exact hh
  · have hh := laplacian_pair_upper (fun k l => facetWeight B
      (scoreOffsets B (pairPath B i j h t)) k l) (w0*Real.exp Q) 1
      (by norm_num) (fun k l hkl => (hw k l hkl).2) i j hij
    have he : (Fintype.card (Fin (n+2)):ℝ)*(w0*Real.exp Q)*1=
        referenceScale n*Real.exp Q := by
      simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,mul_one,w0]
      field_simp
    rw [he] at hh
    exact hh

theorem averagePairSlope_range_bounds (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) (h : FSC.Coord d) :
    referenceScale n*Real.exp (-rangeExponent n (utilityRange (scoreOffsets B h))) ≤
      averagePairSlope B i j h ∧ averagePairSlope B i j h ≤
        referenceScale n*Real.exp (rangeExponent n (utilityRange (scoreOffsets B h))) := by
  have hc : IntervalIntegrable (pairSlope B i j h) volume 0 1 :=
    (pairSlope_fixed_continuous B hG i j h).intervalIntegrable 0 1
  constructor
  · have hh := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (continuous_const.intervalIntegrable 0 1) hc
      (fun t ht => (pairSlope_range_bounds hn hmean B hG i j hij h t ht).1)
    simpa only [intervalIntegral.integral_const,sub_zero,one_smul,averagePairSlope] using hh
  · have hh := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      hc (continuous_const.intervalIntegrable 0 1)
      (fun t ht => (pairSlope_range_bounds hn hmean B hG i j hij h t ht).2)
    simpa only [intervalIntegral.integral_const,sub_zero,one_smul,averagePairSlope] using hh

theorem negativePairCoefficient_range_bounds (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hr1 : r<1) (x : FSC.Coord d)
    (i j : Fin (n+2)) (hij : i≠j) :
    let τ := r/Real.sqrt (1-r^2)
    let Q := rangeExponent n (τ*utilityRange (scoreOffsets B x))
    (Real.sqrt (1-r^2))⁻¹*Real.exp (-Q) ≤ negativePairCoefficient B r x i j ∧
      negativePairCoefficient B r x i j ≤ (Real.sqrt (1-r^2))⁻¹*Real.exp Q := by
  dsimp only
  have hs := NegativeVotingRegularOU.negative_noise_scale_pos r hr hr1
  have hτ : 0<r/Real.sqrt (1-r^2) := div_pos hr hs
  have hG' : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hR : utilityRange (scoreOffsets B (-(r/Real.sqrt (1-r^2)) • frameOperator B x))=
      (r/Real.sqrt (1-r^2))*utilityRange (scoreOffsets B x) := by
    rw [scoreOffsets_frame_smul B hG']
    have he : scoreOffsets B (-(r/Real.sqrt (1-r^2)) • x)=
        (fun k => -(r/Real.sqrt (1-r^2))*scoreOffsets B x k) := by
      funext k
      simp only [scoreOffsets,real_inner_smul_right]
    rw [he]
    exact utilityRange_neg_mul_pos _ _ hτ
  have hh := averagePairSlope_range_bounds hn hmean B hG j i (Ne.symm hij)
    (-(r/Real.sqrt (1-r^2)) • frameOperator B x)
  rw [hR] at hh
  have hf : 0 ≤ (referenceScale n*Real.sqrt (1-r^2))⁻¹ :=
    (inv_pos.mpr (mul_pos (referenceScale_pos n) hs)).le
  have he (a : ℝ) : (referenceScale n*Real.sqrt (1-r^2))⁻¹*(referenceScale n*a)=
      (Real.sqrt (1-r^2))⁻¹*a := by field_simp [(referenceScale_pos n).ne',hs.ne']
  constructor
  · have hl := mul_le_mul_of_nonneg_left hh.1 hf
    rw [he] at hl
    exact hl
  · have hu := mul_le_mul_of_nonneg_left hh.2 hf
    rw [he] at hu
    exact hu

theorem negativePairCoefficient_pos (hn : 0<n)
    (hmean : 1 ≤ NegativeVotingGaussianMaximum.maximumMean n)
    (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hr1 : r<1) (x : FSC.Coord d)
    (i j : Fin (n+2)) (hij : i≠j) : 0<negativePairCoefficient B r x i j := by
  have hs := NegativeVotingRegularOU.negative_noise_scale_pos r hr hr1
  exact (mul_pos (inv_pos.mpr hs) (Real.exp_pos _)).trans_le
    (negativePairCoefficient_range_bounds hn hmean B hG r hr hr1 x i j hij).1

end NegativeVotingRegularPairCoefficient
