import GaussianRegularFacetSeed

/-! Dimension-independent actual conditional first moments on regular facets. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory WeakSimplex Set Filter
open scoped BigOperators RealInnerProductSpace Classical ENNReal
namespace NegativeVotingRegularFacetMean
open NegativeVotingRegularFacetSeed NegativeVotingBalancedReference
  NegativeVotingFacetDegree NegativeVotingDisintegration NegativeVotingWeightedFacet
  NegativeVotingFan NegativeVotingGaussianMaximum NegativeVotingGaussianMaximumMean
  NegativeVotingRegularSecondGap

section ConditionalMean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Any measurable Gaussian set of probability at least m^-2 has a
conditional mean bounded independently of the ambient dimension. -/
theorem gaussian_set_conditional_mean_bound (s : Set E) (hs : MeasurableSet s)
    (m : ℝ) (hm : 1 ≤ m) (hp : 0 < (stdGaussian E s).toReal)
    (hlower : 1/m^2 ≤ (stdGaussian E s).toReal) :
    ‖((stdGaussian E s).toReal)⁻¹ • (∫ x in s,x ∂stdGaussian E)‖ ≤
      2*Real.sqrt (Real.log m)+(Real.sqrt (2*Real.pi))⁻¹ := by
  let p := (stdGaussian E s).toReal
  have hp' : 0 < p := hp
  have hm0 : 0 < m := by linarith
  have hp1 : p ≤ 1 := by
    exact measureReal_le_one
  have hN : 1 ≤ 1/p := (le_div_iff₀ hp').mpr (by simpa using hp1)
  have he : p=1/(1/p) := by field_simp
  have hh := set_centroid_norm_le_logarithmic_mass_bound s hs (1/p) 1 hN he.le
  have hN2 : 1/p ≤ m^2 := by
    apply (div_le_iff₀ hp').mpr
    have hh' := (div_le_iff₀ (sq_pos_of_pos hm0)).mp hlower
    nlinarith
  have hlog : Real.log (1/p) ≤ 2*Real.log m := by
    have hh' := Real.log_le_log (div_pos zero_lt_one hp') hN2
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh'
  have hsq : Real.sqrt (2*Real.log (1/p)) ≤ 2*Real.sqrt (Real.log m) := by
    calc
      _ ≤ Real.sqrt (4*Real.log m) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]; norm_num
  have hnorm : ‖p⁻¹ • (∫ x in s,x ∂stdGaussian E)‖=
      ‖∫ x in s,x ∂stdGaussian E‖/p := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp']
    ring
  change ‖p⁻¹ • (∫ x in s,x ∂stdGaussian E)‖ ≤ _
  rw [hnorm]
  apply (div_le_iff₀ hp').mpr
  simp only [one_mul,div_eq_mul_inv,one_mul,inv_inv] at hh
  have hh' := mul_le_mul_of_nonneg_right (add_le_add_right hsq ((Real.sqrt (2*Real.pi))⁻¹)) hp'.le
  simp only [one_div] at hh'
  nlinarith

end ConditionalMean
variable {n d : ℕ}

theorem normalPDF_zero_le_one : gaussianPDFReal 0 1 0 ≤ 1 := by
  have hsq : 1 ≤ Real.sqrt (2*Real.pi) := by
    have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    have hn := Real.sqrt_nonneg (2*Real.pi)
    nlinarith [Real.pi_gt_three]
  have hp : 0 < Real.sqrt (2*Real.pi) := lt_of_lt_of_le zero_lt_one hsq
  have hpdf : gaussianPDFReal 0 1 0=(Real.sqrt (2*Real.pi))⁻¹ := by
    simp [gaussianPDFReal]
  rw [hpdf,inv_eq_one_div]
  exact (div_le_one hp).mpr hsq

/-- An explicit polynomial lower bound for the genuine regular facet mass. -/
theorem regular_intrinsicFacet_mass_lower (hn : 0<n)
    (hmean : 1 ≤ maximumMean n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    1/((n:ℝ)+2)^2 ≤
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B 0 i j)).toReal := by
  rw [regular_intrinsicFacet_mass hn B hG i j hij]
  have hm : 0 < (n:ℝ)+2 := by positivity
  have hm1 : 0 < (n:ℝ)+1 := by positivity
  have hφ : 0 < gaussianPDFReal 0 1 0 := gaussianPDFReal_pos 0 1 0 (by norm_num)
  have hα := referenceScale_pos n
  have hs : 1 ≤ Real.sqrt (2:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have ha : referenceScale n*((n:ℝ)+1)=maximumMean n := by
    unfold referenceScale
    field_simp
  have ham : 1 ≤ referenceScale n*((n:ℝ)+2) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right ham (Real.sqrt_nonneg (2:ℝ))
  have hbound : gaussianPDFReal 0 1 0 ≤ referenceScale n*((n:ℝ)+2)*Real.sqrt 2 := by
    linarith [normalPDF_zero_le_one]
  apply (div_le_div_iff₀ (sq_pos_of_pos hm) (mul_pos hm hφ)).mpr
  have hh := mul_le_mul_of_nonneg_left hbound hm.le
  nlinarith

/-- The actual normalized regular-facet first moment has O(sqrt(log m))
norm, with an explicit dimension-independent bound. -/
theorem regular_facet_conditional_mean_bound (hn : 0<n)
    (hmean : 1 ≤ maximumMean n) (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) :
    ‖((stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B 0 i j)).toReal)⁻¹ •
      (∫ y in intrinsicFacet B 0 i j,y ∂stdGaussian (tangentSpace (pairNormal B i j)))‖ ≤
        2*Real.sqrt (Real.log ((n:ℝ)+2))+(Real.sqrt (2*Real.pi))⁻¹ := by
  have hl := regular_intrinsicFacet_mass_lower hn hmean B hG i j hij
  have hp : 0 < (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B 0 i j)).toReal :=
    lt_of_lt_of_le (by positivity) hl
  apply gaussian_set_conditional_mean_bound _ (isClosed_intrinsicFacet B 0 i j).measurableSet
    ((n:ℝ)+2) (by have hh:=Nat.cast_nonneg (α:=ℝ) n; linarith) hp hl

/-- One threshold precedes the dimension, regular realization and facet. -/
theorem eventually_regular_facet_conditional_mean_bound :
    ∀ᶠ n : ℕ in atTop,∀ (d : ℕ) (B : Fin (n+2) → FSC.Coord d)
      (hG : ∀ i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
      (i j : Fin (n+2)) (hij : i≠j),
      ‖((stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B 0 i j)).toReal)⁻¹ •
        (∫ y in intrinsicFacet B 0 i j,y ∂stdGaussian (tangentSpace (pairNormal B i j)))‖ ≤
          2*Real.sqrt (Real.log ((n:ℝ)+2))+(Real.sqrt (2*Real.pi))⁻¹ := by
  filter_upwards [eventually_gt_atTop (0:ℕ),eventually_maximum_mean_sq_ge_one] with n hn hsq
  intro d B hG i j hij
  have hmean : 1 ≤ maximumMean n :=
    (sq_le_sq₀ (by norm_num : (0:ℝ)≤1) (maximumMean_pos n).le).mp (by simpa using hsq)
  exact regular_facet_conditional_mean_bound hn hmean B hG i j hij

end NegativeVotingRegularFacetMean
