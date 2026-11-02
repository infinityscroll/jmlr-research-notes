import GaussianDiagonalHazardDifferentiation
import WeakSimplexConjectureLean.Normal.TiltFunctions
import Mathlib.Analysis.Calculus.MeanValue

/-! Global polynomial envelopes for the actual diagonal Gaussian hazards.
These are integrability bounds; they do not assert the rare-event uniform
moment estimates needed for the summed row-payment theorem. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped BigOperators Topology Classical
namespace NegativeVotingHazardPolynomialBounds
open WeakSimplex NegativeVotingDiagonalHazardDifferentiation

lemma normal_hazard_derivative_bound (x : ℝ) : ‖-r x*H x‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_mul,abs_neg,abs_of_pos (r_pos x),abs_of_pos (H_pos x)]
  have hh := H_deriv_pos x
  dsimp [H]
  nlinarith

lemma normal_hazard_abs_sub_le (x y : ℝ) : |r y-r x| ≤ |y-x| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s:=Set.univ) (C:=(1:ℝ)) (fun t _=>(hasDerivAt_r t).hasDerivWithinAt)
    (fun t _=>normal_hazard_derivative_bound t) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma normal_hazard_linear_growth (x : ℝ) : r x ≤ r 0+|x| := by
  have hh := normal_hazard_abs_sub_le 0 x
  simp only [sub_zero] at hh
  linarith [le_abs_self (r x-r 0)]

lemma gaussianHazard_eq_scaled (σ h x : ℝ) :
    gaussianHazard σ h x=r ((x-h)/σ)/σ := by
  unfold gaussianHazard gaussianDensity gaussianCDF r
  ring

lemma gaussianHazard_linear_growth (σ h x : ℝ) (hσ : 0 < σ) :
    gaussianHazard σ h x ≤ r 0/σ+(|x|+|h|)/σ^2 := by
  rw [gaussianHazard_eq_scaled]
  have hh := div_le_div_of_nonneg_right (normal_hazard_linear_growth ((x-h)/σ)) hσ.le
  rw [abs_div,abs_of_pos hσ] at hh
  calc
    _ ≤ (r 0+|x-h|/σ)/σ := hh
    _ ≤ (r 0+(|x|+|h|)/σ)/σ := by
      gcongr
      simpa using abs_sub_le x 0 h
    _ = _ := by ring

lemma gaussianHazard_uniform_linear_growth (σ h x s H₀ : ℝ)
    (hs : 0 < s) (hσ : s ≤ σ) (hh : |h| ≤ H₀) :
    gaussianHazard σ h x ≤ r 0/s+(|x|+H₀)/s^2 := by
  have hσ0 := hs.trans_le hσ
  have hH : 0 ≤ H₀ := (abs_nonneg _).trans hh
  have hσ2 : s^2 ≤ σ^2 := pow_le_pow_left₀ hs.le hσ 2
  calc
    _ ≤ r 0/σ+(|x|+|h|)/σ^2 := gaussianHazard_linear_growth σ h x hσ0
    _ ≤ r 0/s+(|x|+H₀)/s^2 := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left (r_pos 0).le hs hσ
      · exact (div_le_div_of_nonneg_right (add_le_add (le_refl |x|) hh) (sq_nonneg σ)).trans
          (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hs) hσ2)

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma productCDF_nonneg (σ h : V → ℝ) (x : ℝ) : 0 ≤ productCDF σ h x :=
  Finset.prod_nonneg fun i _=>(gaussianCDF_pos _ _ _).le

lemma productCDF_le_coordinate (σ h : V → ℝ) (x : ℝ) (i : V) :
    productCDF σ h x ≤ gaussianCDF (σ i) (h i) x := by
  have he := Finset.prod_erase_mul Finset.univ (fun j=>gaussianCDF (σ j) (h j) x) (Finset.mem_univ i)
  have hprod : (∏j∈Finset.univ.erase i,gaussianCDF (σ j) (h j) x) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _=>(gaussianCDF_pos _ _ _).le) (fun j _=>(normalCDF_lt_one _).le)
  unfold productCDF
  rw [←he]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (gaussianCDF_pos _ _ _).le

lemma hazardPairDensity_nonneg (σ h : V → ℝ) (hσ : ∀ i,0 < σ i) (x : ℝ) (i j : V) :
    0 ≤ hazardPairDensity σ h x i j :=
  mul_nonneg (mul_nonneg (productCDF_nonneg _ _ _) (gaussianHazard_pos _ _ _ (hσ i)).le)
    (gaussianHazard_pos _ _ _ (hσ j)).le

/-- Both i=j and i≠j are covered. A full product is retained until the
 density/hazard cancellation; no inverse tiny cell probability appears. -/
lemma hazardPairDensity_le_density_hazard (σ h : V → ℝ) (hσ : ∀ i,0 < σ i)
    (x : ℝ) (i j : V) :
    hazardPairDensity σ h x i j ≤ gaussianDensity (σ i) (h i) x*gaussianHazard (σ j) (h j) x := by
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (productCDF_le_coordinate σ h x i)
      (gaussianHazard_pos (σ i) (h i) x (hσ i)).le) (gaussianHazard_pos (σ j) (h j) x (hσ j)).le
  have hc : gaussianCDF (σ i) (h i) x*gaussianHazard (σ i) (h i) x=
      gaussianDensity (σ i) (h i) x := by
    dsimp [gaussianHazard]
    field_simp [(gaussianCDF_pos (σ i) (h i) x).ne']
  rw [hc] at hh
  exact hh

lemma hazardPairDensity_polynomial_bound (σ h : V → ℝ) (s H₀ x : ℝ)
    (hs : 0 < s) (hσ : ∀ i,s ≤ σ i) (hh : ∀ i,|h i| ≤ H₀) (i j : V) :
    hazardPairDensity σ h x i j ≤
      gaussianDensity (σ i) (h i) x*(r 0/s+(|x|+H₀)/s^2) := by
  exact (hazardPairDensity_le_density_hazard σ h (fun k=>hs.trans_le (hσ k)) x i j).trans
    (mul_le_mul_of_nonneg_left (gaussianHazard_uniform_linear_growth _ _ _ s H₀ hs (hσ j) (hh j))
      (gaussianDensity_pos _ _ _ (hs.trans_le (hσ i))).le)

end NegativeVotingHazardPolynomialBounds
