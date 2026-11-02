import GaussianFanCycleAnalyticBridge
import GaussianFanCycleDeficit

/-! Literal surface second moments in the cycle normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace NegativeVotingFanCycleQuadratic
open NegativeVotingFanCycle NegativeVotingFanCycleBridge NegativeVotingFanHessian
  NegativeVotingPolyhedral

/-- Polynomial expansion under a finite measure, with all moments justified. -/
theorem integral_square_add_const {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (c : ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, (f x+c)^2 ∂μ) = (∫ x, (f x)^2 ∂μ)+2*c*(∫ x, f x ∂μ)+c^2*μ.real Set.univ := by
  have he : (fun x => (f x+c)^2) = (fun x => (f x)^2+2*c*f x+c^2) := by funext x; ring
  rw [he]
  have ha : (∫ x, (f x)^2+2*c*f x+c^2 ∂μ) =
      (∫ x, (f x)^2+2*c*f x ∂μ)+(∫ _ : X, c^2 ∂μ) :=
    integral_add (hf2.add (hf.const_mul (2*c))) (integrable_const (c^2))
  have hb : (∫ x, (f x)^2+2*c*f x ∂μ) =
      (∫ x, (f x)^2 ∂μ)+(∫ x, 2*c*f x ∂μ) :=
    integral_add hf2 (hf.const_mul (2*c))
  rw [ha,hb,integral_const_mul,integral_const]
  simp only [smul_eq_mul]
  ring

/-- The exact variance decomposition, without a normalized-measure placeholder. -/
theorem integral_square_centering {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (c : ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ)
    (hp : 0 < μ.real Set.univ) :
    (∫ x, (f x+c)^2 ∂μ) =
      (∫ x, (f x-(∫ y, f y ∂μ)/μ.real Set.univ)^2 ∂μ)+
      μ.real Set.univ*((∫ y, f y ∂μ)/μ.real Set.univ+c)^2 := by
  simp only [sub_eq_add_neg]
  rw [integral_square_add_const μ f c hf hf2,
    integral_square_add_const μ f (-((∫ y, f y ∂μ)/μ.real Set.univ)) hf hf2]
  field_simp [ne_of_gt hp]
  <;> ring

variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- An ambient linear score has its actual square integrable in every intrinsic cap. -/
theorem coordinateEmbed_pairing_square_integrable (b : AffineBasis V ℝ (FSC.Coord d))
    (h : V → ℝ) (S : Set V) (i : V) (v : FSC.Coord d) :
    Integrable (fun x => (inner ℝ v (coordinateEmbed b h S x))^2)
      ((stdGaussian (FaceCoordinates b S)).restrict (coordinateCap b h S i)) := by
  classical
  have hh := cap_centered_square_integrable (coordinateCapNormal b S i)
    (intrinsicCapOffset b h S i) (coordinateDual b S v) (-inner ℝ v (faceAnchor b h S))
  apply hh.congr
  filter_upwards with x
  rw [coordinateEmbed_pairing]
  ring

/-- Exact surface second moment in terms of the same Gaussian means and variances
used by the cycle factorization. -/
theorem surfaceIntegral_affine_square (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i ≠ j) (v : FSC.Coord d) (c : ℝ) :
    surfaceIntegral b h i j (fun x => (inner ℝ v x+c)^2) =
      cycleEdgeWeight b h i j * (stratumDirectionalVariance b h {i,j} i v+
        (stratumMeanPairing b h {i,j} i v+c)^2) := by
  let μ := (stdGaussian (FaceCoordinates b ({i,j}:Set V))).restrict (coordinateCap b h {i,j} i)
  have hmass : μ.real Set.univ = FSC.capMass (coordinateCapNormal b {i,j} i)
      (intrinsicCapOffset b h {i,j} i) := by
    simp [μ,Measure.real,coordinateCap,FSC.capMass]
  have hp : 0 < μ.real Set.univ := by
    rw [hmass]
    exact coordinateCap_mass_pos b h {i,j} i (by simp)
  have hcenter := integral_square_centering μ
    (fun x => inner ℝ v (coordinateEmbed b h {i,j} x)) c
    (coordinateEmbed_pairing_integrable b h {i,j} i v)
    (coordinateEmbed_pairing_square_integrable b h {i,j} i v) hp
  rw [hmass] at hcenter
  rw [surfaceIntegral_eq_stratum b h i j hij (fun x => (inner ℝ v x+c)^2) (by fun_prop)]
  rw [hcenter]
  rw [cycleEdgeWeight,if_neg hij]
  have halg (D ell I p a c : ℝ) (hp : p ≠ 0) :
      D/ell*(I+p*(a+c)^2) = D*p/ell*(I/p+(a+c)^2) := by
    field_simp [hp]
  exact halg _ _ _ _ _ _ (ne_of_gt (coordinateCap_mass_pos b h {i,j} i (by simp)))

end NegativeVotingFanCycleQuadratic
