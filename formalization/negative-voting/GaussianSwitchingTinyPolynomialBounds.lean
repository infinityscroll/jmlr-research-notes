import GaussianStructuredSwitchingAmplitude

/-! Explicit polynomial bounds for the error terms of the actual tiny cap.
The powers are deliberately loose. No error coefficient is assumed small. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingSwitchingTinyPolynomialBounds
open NegativeVotingSwitchingTiny NegativeVotingSwitchingPair NegativeVotingFan
  NegativeVotingWeightedFacet NegativeVotingStructuredSwitchingMoments
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem ordered_sum_le_card_sq (f : V→V→ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀i j,i≠j→f i j ≤ C) :
    (∑i,∑j∈Finset.univ.erase i,f i j) ≤ (Fintype.card V:ℝ)^2*C := by
  calc
    _ ≤ ∑i,∑j∈Finset.univ.erase i,C := Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j hj=>hf i j (Finset.mem_erase.mp hj).1.symm
    _ ≤ ∑i,∑j:V,C := Finset.sum_le_sum fun i _=>Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _=>hC)
    _ = _ := by simp; ring

theorem integral_abs_pow32_le_one {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X→ℝ) (hf : MemLp f 32 μ) (hn : realLp μ 32 f ≤ 1) :
    (∫x,|f x|^32 ∂μ) ≤ 1 := by
  have he:=NegativeVotingSwitchingLp.integral_abs_rpow_eq_norm (32:ℝ) (by norm_num) (by simpa using hf)
  have hp:=pow_le_pow_left₀ (realLp_nonneg 32 f) hn 32
  have he' : (∫x,|f x|^32 ∂μ)=realLp μ 32 f ^ (32:ℕ):=by simpa [realLp] using he
  rw [he']
  simpa only [one_pow] using hp

theorem totalNormalCoefficient_le_card_sq
    (B : V→FSC.Coord d) (W : ∀i j,((ℝ ∙ (B i-B j))ᗮ)→ℝ)
    (hW : ∀i j,i≠j→MemLp (W i j) 32 (stdGaussian _))
    (hn : ∀i j,i≠j→ realLp (stdGaussian _) 32 (W i j) ≤ 1) :
    totalNormalCoefficient B W ≤ (Fintype.card V:ℝ)^2 := by
  unfold totalNormalCoefficient
  simpa using ordered_sum_le_card_sq (fun i j=>∫y,(W i j y)^32 ∂stdGaussian _) 1 (by norm_num)
    (fun i j hij=>by simpa only [Even.pow_abs (by decide : Even (32:ℕ))] using integral_abs_pow32_le_one _ (W i j) (hW i j hij) (hn i j hij))

theorem pairAmbientCoefficient_le (B : V→FSC.Coord d) (v : FSC.Coord d→V→ℝ)
    (m : ℝ) (hm : 0 ≤ m) (i j : V)
    (hell : 1/‖B i-B j‖ ≤ m^2)
    (hv : MemLp (fun x=>v x i+v x j) 32 (stdGaussian _))
    (hn : realLp (stdGaussian _) 32 (fun x=>v x i+v x j) ≤ 1) :
    pairAmbientCoefficient B v i j ≤ m^62 := by
  have hnum:=integral_abs_pow32_le_one _ _ hv hn
  have hpow:=pow_le_pow_left₀ (by positivity : 0 ≤ 1/‖B i-B j‖) hell 31
  unfold pairAmbientCoefficient
  calc
    _ ≤ 1/‖B i-B j‖^31 := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (m^2)^31 := by simpa only [div_pow,one_pow] using hpow
    _ = _ := by ring

theorem totalAmbientCoefficient_le_card_pow64 (B : V→FSC.Coord d) (v : FSC.Coord d→V→ℝ)
    (hell : ∀i j,i≠j→1/‖B i-B j‖ ≤ (Fintype.card V:ℝ)^2)
    (hv : ∀i j,i≠j→MemLp (fun x=>v x i+v x j) 32 (stdGaussian _))
    (hn : ∀i j,i≠j→ realLp (stdGaussian _) 32 (fun x=>v x i+v x j) ≤ 1) :
    totalAmbientCoefficient B v ≤ (Fintype.card V:ℝ)^64 := by
  unfold totalAmbientCoefficient
  have hh:=ordered_sum_le_card_sq (pairAmbientCoefficient B v) ((Fintype.card V:ℝ)^62) (by positivity)
    (fun i j hij=>pairAmbientCoefficient_le B v _ (by positivity) i j (hell i j hij) (hv i j hij) (hn i j hij))
  convert hh using 1 <;> ring

theorem pairCubicCoefficient_le (B : V→FSC.Coord d) (h : V→ℝ) (σ D m : ℝ)
    (hm : 2 ≤ m) (hcard : (Fintype.card V:ℝ) ≤ m) (hσ : 0<σ) (hD : 0 ≤ D) (hD1 : D ≤ 1)
    (i j : V) (hell : 0<‖B i-B j‖) (hellinv : 1/‖B i-B j‖ ≤ m^2)
    (hσinv : 1/σ ≤ m^2) (ha : |pairOffset B h i j| ≤ m) :
    pairCubicCoefficient B h σ D i j ≤ 4*m^7 := by
  have hm0 : 0 ≤ m:=by linarith
  have hm1 : 1 ≤ m:=by linarith
  have hpi : 1 ≤ Real.sqrt (2*Real.pi):=by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have hthree : 1 ≤ Real.sqrt (3/2:ℝ):=by apply Real.le_sqrt_of_sq_le; norm_num
  have hden : 2*‖B i-B j‖^2*σ ≤ 2*‖B i-B j‖^2*(Real.sqrt (2*Real.pi)*σ*Real.sqrt (3/2)):=by
    have hh:=mul_le_mul hpi hthree (by norm_num : (0:ℝ)≤1) (Real.sqrt_nonneg _)
    have hmul:=mul_le_mul_of_nonneg_left hh hσ.le
    have hmul':=mul_le_mul_of_nonneg_left hmul (show 0 ≤ 2*‖B i-B j‖^2 by positivity)
    nlinarith only [hmul']
  have hnum : ((Fintype.card V-2:ℕ):ℝ)*D ≤ m:=by
    have hc : ((Fintype.card V-2:ℕ):ℝ) ≤ (Fintype.card V:ℝ):=by exact_mod_cast Nat.sub_le (Fintype.card V) 2
    exact (mul_le_mul_of_nonneg_left hD1 (by positivity)).trans (by simpa using hc.trans hcard)
  have hfirst : ((Fintype.card V-2:ℕ):ℝ)*D /
      (2*‖B i-B j‖^2*(Real.sqrt (2*Real.pi)*σ*Real.sqrt (3/2))) ≤ m^7:=by
    have hpow:=pow_le_pow_left₀ (by positivity : 0 ≤ 1/‖B i-B j‖) hellinv 2
    have hmuls:=mul_le_mul hpow hσinv (by positivity : 0 ≤ 1/σ) (by positivity : 0 ≤ (m^2)^2)
    calc
      _ ≤ m/(2*‖B i-B j‖^2*σ) := div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = (m/2)*((1/‖B i-B j‖)^2*(1/σ)) := by ring
      _ ≤ (m/2)*((m^2)^2*m^2) := mul_le_mul_of_nonneg_left hmuls (by positivity)
      _ ≤ m^7 := by nlinarith [pow_nonneg hm0 7]
  have hsecond : (2+|pairOffset B h i j|)/‖B i-B j‖^2 ≤ 3*m^7:=by
    have hpow:=pow_le_pow_left₀ (by positivity : 0 ≤ 1/‖B i-B j‖) hellinv 2
    have hm5 : m^5 ≤ m^7:=pow_le_pow_right₀ hm1 (by norm_num)
    calc
      _ = (2+|pairOffset B h i j|)*(1/‖B i-B j‖)^2 := by ring
      _ ≤ (3*m)*(m^2)^2 := mul_le_mul (by linarith) hpow (by positivity) (by positivity)
      _ ≤ 3*m^7 := by nlinarith only [hm5]
  have hpdf : gaussianPDFReal 0 1 (pairOffset B h i j) ≤ 1:=
    (NegativeVotingMovingCap.normalPDF_le_zero _).trans NegativeVotingRegularFacetMean.normalPDF_zero_le_one
  unfold pairCubicCoefficient
  exact (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (gaussianPDFReal_nonneg _ _ _)).trans
    (by nlinarith [mul_le_mul_of_nonneg_right hpdf (show 0 ≤ 4*m^7 by positivity)])

theorem totalCubicCoefficient_le_card_pow9 (B : V→FSC.Coord d) (h : V→ℝ) (σ D : ℝ)
    (hm : 2 ≤ Fintype.card V) (hσ : 0<σ) (hD : 0 ≤ D) (hD1 : D ≤ 1)
    (hell : ∀i j,i≠j→0<‖B i-B j‖)
    (hellinv : ∀i j,i≠j→1/‖B i-B j‖ ≤ (Fintype.card V:ℝ)^2)
    (hσinv : 1/σ ≤ (Fintype.card V:ℝ)^2)
    (ha : ∀i j,i≠j→|pairOffset B h i j| ≤ (Fintype.card V:ℝ)) :
    totalCubicCoefficient B h σ D ≤ 4*(Fintype.card V:ℝ)^9 := by
  unfold totalCubicCoefficient
  have hh:=ordered_sum_le_card_sq (pairCubicCoefficient B h σ D) (4*(Fintype.card V:ℝ)^7) (by positivity)
    (fun i j hij=>pairCubicCoefficient_le B h σ D _ (by exact_mod_cast hm) le_rfl hσ hD hD1 i j
      (hell i j hij) (hellinv i j hij) hσinv (ha i j hij))
  convert hh using 1 <;> ring


/-- Concrete geometry bounds all three summed errors by one fixed polynomial. -/
theorem totalErrors_le_card_pow64 (B : V→FSC.Coord d) (h : V→ℝ) (σ D : ℝ)
    (hm : 2 ≤ Fintype.card V) (hσ : 0<σ) (hD : 0 ≤ D) (hD1 : D ≤ 1)
    (hell : ∀i j,i≠j→0<‖B i-B j‖)
    (hellinv : ∀i j,i≠j→1/‖B i-B j‖ ≤ (Fintype.card V:ℝ)^2)
    (hσinv : 1/σ ≤ (Fintype.card V:ℝ)^2)
    (ha : ∀i j,i≠j→|pairOffset B h i j| ≤ (Fintype.card V:ℝ))
    (v : FSC.Coord d→V→ℝ)
    (hv : ∀i j,i≠j→MemLp (fun x=>v x i+v x j) 32 (stdGaussian _))
    (hvn : ∀i j,i≠j→ realLp (stdGaussian _) 32 (fun x=>v x i+v x j) ≤ 1)
    (W : ∀i j,((ℝ ∙ (B i-B j))ᗮ)→ℝ)
    (hW : ∀i j,i≠j→MemLp (W i j) 32 (stdGaussian _))
    (hWn : ∀i j,i≠j→ realLp (stdGaussian _) 32 (W i j) ≤ 1) :
    totalCubicCoefficient B h σ D+totalNormalCoefficient B W+totalAmbientCoefficient B v ≤
      6*(Fintype.card V:ℝ)^64 := by
  have hc:=totalCubicCoefficient_le_card_pow9 B h σ D hm hσ hD hD1 hell hellinv hσinv ha
  have hn:=totalNormalCoefficient_le_card_sq B W hW hWn
  have ha':=totalAmbientCoefficient_le_card_pow64 B v hellinv hv hvn
  have hm1 : 1 ≤ (Fintype.card V:ℝ):=by exact_mod_cast (show 1 ≤ Fintype.card V by omega)
  have h9 : (Fintype.card V:ℝ)^9 ≤ (Fintype.card V:ℝ)^64:=pow_le_pow_right₀ hm1 (by norm_num)
  have h2 : (Fintype.card V:ℝ)^2 ≤ (Fintype.card V:ℝ)^64:=pow_le_pow_right₀ hm1 (by norm_num)
  linarith

/-- The prescribed cutoff lies inside the actual unit normal tube, uniformly
at every smaller positive amplitude. -/
theorem tinyCutoff_geometry (m θ ell a : ℝ) (hm : 2 ≤ m) (hθ : 0<θ)
    (hθm : θ ≤ m^(-256:ℝ)) (hell : 0<ell) (hellinv : 1/ell ≤ m^2) (ha : |a| ≤ m) :
    θ*tinyCutoff θ/ell ≤ 1 ∧ (1+|a|)*(θ*tinyCutoff θ/ell) ≤ 1/2 := by
  have hm0 : 0 < m:=by linarith
  have hm1 : 1 ≤ m:=by linarith
  have hwidth : θ*tinyCutoff θ ≤ 1/m^5:=by
    rw [tinyCutoff_width θ hθ]
    calc
      _ ≤ (m^(-256:ℝ))^((7:ℝ)/8) := Real.rpow_le_rpow hθ.le hθm (by norm_num)
      _ = m^(-224:ℝ) := by rw [←Real.rpow_mul hm0.le]; norm_num
      _ ≤ m^(-5:ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = 1/m^5 := by rw [Real.rpow_neg hm0.le]; norm_num
  have hw : θ*tinyCutoff θ/ell ≤ 1/m^3:=by
    calc
      _ = (θ*tinyCutoff θ)*(1/ell) := by ring
      _ ≤ (1/m^5)*(m^2) := mul_le_mul hwidth hellinv (by positivity) (by positivity)
      _ = 1/m^3 := by field_simp
  have hm3 : 1 ≤ m^3:=one_le_pow₀ hm1
  refine ⟨hw.trans ((div_le_one (by positivity)).mpr hm3),?_⟩
  calc
    _ ≤ (1+m)*(1/m^3) := mul_le_mul (by linarith) hw (div_nonneg (mul_nonneg hθ.le (tinyCutoff_pos θ hθ).le) hell.le) (by positivity)
    _ ≤ 1/2 := by
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : 0 < m^3)).mpr
      nlinarith [mul_nonneg (show 0 ≤ m-2 by linarith) (show 0 ≤ m^2+2*m+2 by positivity)]


/-- Uniform tiny-cap integration with all error coefficients derived from
geometry and normalized moments. Only the actual leading facet energy is
left visible for its separate trace estimate. -/
theorem exists_uniform_tiny_cap : ∃ N : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V],
    N ≤ Fintype.card V → ∀ d : ℕ,
    ∀ (B : V→FSC.Coord d) (h : V→ℝ) (σ D : ℝ),
    2 ≤ Fintype.card V → 0<σ →
    NegativeVotingCapTail.CenteredSingularLowerBound B σ →
    (∀i j,‖B i-B j‖ ≤ D) → 0 ≤ D → D ≤ 1 →
    (∀i j,i≠j→1/‖B i-B j‖ ≤ (Fintype.card V:ℝ)^2) →
    1/σ ≤ (Fintype.card V:ℝ)^2 →
    (∀i j,i≠j→|pairOffset B h i j| ≤ (Fintype.card V:ℝ)) →
    ∀ (v : FSC.Coord d→V→ℝ),
    (∀i,Measurable (fun x=>v x i)) →
    (∀i j,i≠j→MemLp (fun x=>v x i+v x j) 32 (stdGaussian _)) →
    (∀i j,i≠j→ realLp (stdGaussian _) 32 (fun x=>v x i+v x j) ≤ 1) →
    ∀ (W : ∀i j,((ℝ ∙ (B i-B j))ᗮ)→ℝ),
    (∀i j,i≠j→Measurable (W i j)) →
    (∀i j,i≠j→MemLp (W i j) 32 (stdGaussian _)) →
    (∀i j,i≠j→ realLp (stdGaussian _) 32 (W i j) ≤ 1) →
    (∀i j,i≠j→∀y,0 ≤ W i j y) →
    (∀i j,i≠j→∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
      ContinuousOn (pairPlaneForcing B h i j v y) (Icc (0:ℝ) 1) ∧
      (∀z∈Icc (0:ℝ) 1,pairPlaneForcing B h i j v y z ≤ W i j y) ∧
      (∀z∈Icc (0:ℝ) 1,|pairPlaneForcing B h i j v y z-pairPlaneForcing B h i j v y 0| ≤ W i j y*z)) →
    ∀ θ F : ℝ, 0<θ → θ ≤ (Fintype.card V:ℝ)^(-256:ℝ) → totalFacetCoefficient B h v ≤ F →
      (∫x,NegativeVotingSwitchingOrdered.closedCellCap B h v θ x ∂stdGaussian (FSC.Coord d)) ≤ (F+1)*θ^2 := by
  obtain ⟨N,hN⟩:=exists_uniform_tiny_threshold 6 64 256 (by norm_num) (by norm_num)
  refine ⟨N,?_⟩
  intro V _ _ _ hn d B h σ D hm hσ hlower hdiam hD hD1 hellinv hσinv ha v hvM hv hvn W hWM hW hWn hW0 hcontrol θ F hθ hθm hF
  have hell i j (hij:i≠j) : 0<‖B i-B j‖:=norm_pos_iff.mpr (sub_ne_zero.mpr
    (NegativeVotingFacetDegree.centered_singular_rows_ne B σ hσ hlower i j hij))
  have hm' : (2:ℝ) ≤ Fintype.card V:=by exact_mod_cast hm
  have hgeom i j (hij:i≠j):=tinyCutoff_geometry (Fintype.card V) θ ‖B i-B j‖ (pairOffset B h i j)
    hm' hθ hθm (hell i j hij) (hellinv i j hij) (ha i j hij)
  have hcap:=integral_closedCellCap_scaled B h σ D hσ hlower hdiam v hvM hv θ (tinyCutoff θ) hθ.le
    (tinyCutoff_pos θ hθ) (fun i j hij=>(hgeom i j hij).1) (fun i j hij=>(hgeom i j hij).2)
    W hWM hW hW0 hcontrol
  have hθ1 : θ ≤ 1:=hθm.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num))
  have herr:=tinyCutoff_errors θ (totalCubicCoefficient B h σ D) (totalNormalCoefficient B W)
    (totalAmbientCoefficient B v) hθ hθ1 (totalNormalCoefficient_nonneg B W) (totalAmbientCoefficient_nonneg B v)
  have hpoly:=totalErrors_le_card_pow64 B h σ D hm hσ hD hD1 hell hellinv hσinv ha v hv hvn W hW hWn
  have habsorb:= (hN (Fintype.card V) hn).2 θ hθ hθm
  have habsorb' : (6*(Fintype.card V:ℝ)^64)*θ^((5:ℝ)/8) ≤ 1:=by simpa using habsorb
  have hmain : (∫x,NegativeVotingSwitchingOrdered.closedCellCap B h v θ x ∂stdGaussian (FSC.Coord d)) ≤
      F*θ^2+(6*(Fintype.card V:ℝ)^64)*θ^((21:ℝ)/8):=by
    have hprod:=mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hθ.le ((21:ℝ)/8))
    have hlead:=mul_le_mul_of_nonneg_left hF (sq_nonneg θ)
    linarith
  exact hmain.trans (tiny_error_absorbed θ F (6*(Fintype.card V:ℝ)^64) hθ habsorb')

end NegativeVotingSwitchingTinyPolynomialBounds
