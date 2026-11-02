import GaussianCapCovariance
import Mathlib.MeasureTheory.Function.L2Space

/-! A dimension-free lower bound for the probability of a translated actual
Gaussian polyhedron. This supplies the shift step in explicit facet witnesses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace ENNReal
namespace NegativeVotingCapShiftLower
open NegativeVotingPolyhedral
variable {d : ℕ} {ι : Type*} [Fintype ι]

private theorem integral_product_sq_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  have hf2 : Integrable (fun x => (f x)^2) μ := by
    simpa only [sq,Pi.mul_def] using hf.integrable_mul hf
  have hg2 : Integrable (fun x => (g x)^2) μ := by
    simpa only [sq,Pi.mul_def] using hg.integrable_mul hg
  have hfg : Integrable (fun x => f x*g x) μ := by
    simpa only [Pi.mul_def] using hf.integrable_mul hg
  have hpoly (t : ℝ) : 0 ≤ (∫ x, (f x)^2 ∂μ)*(t*t)+
      (2*(∫ x, f x*g x ∂μ))*t+(∫ x, (g x)^2 ∂μ) := by
    have hnon : 0 ≤ ∫ x, (t*f x+g x)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have he : (fun x => (t*f x+g x)^2) =
        (fun x => t^2*(f x)^2+(2*t)*(f x*g x)+(g x)^2) := by funext x;ring
    have hl : Integrable (fun x => t^2*(f x)^2+(2*t)*(f x*g x)) μ :=
      (hf2.const_mul (t^2)).add (hfg.const_mul (2*t))
    rw [he,integral_add hl hg2,
      integral_add (hf2.const_mul (t^2)) (hfg.const_mul (2*t)),integral_const_mul,
      integral_const_mul] at hnon
    nlinarith
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  nlinarith

theorem exp_inner_sq (v x : FSC.Coord d) (t : ℝ) :
    (Real.exp (t*inner ℝ v x))^2 = Real.exp ((2*t)*inner ℝ v x) := by
  rw [sq,← Real.exp_add]
  congr 1
  ring

theorem memLp_exp_inner_restrict (v : FSC.Coord d) (t : ℝ)
    (s : Set (FSC.Coord d)) :
    MemLp (fun x => Real.exp (t*inner ℝ v x)) 2 ((stdGaussian (FSC.Coord d)).restrict s) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [exp_inner_sq] using integrable_exp_inner_restrict v (2*t) s

theorem integral_exp_inner (v : FSC.Coord d) (t : ℝ) :
    (∫ x, Real.exp (t*inner ℝ v x) ∂stdGaussian (FSC.Coord d)) =
      Real.exp (t^2*‖v‖^2/2) := by
  have hh := cap_mgf_translate (fun _ : Fin 0 => (0 : FSC.Coord d))
    (fun _ => 0) v t
  simpa [mgf,FSC.cap,FSC.capMass] using hh

/-- The bound holds for every cap, including zero-probability caps, and every
translation, without positivity, independence or dimension assumptions. -/
theorem cap_shift_mass_lower (w : ι → FSC.Coord d) (b : ι → ℝ)
    (v : FSC.Coord d) (t : ℝ) :
    (FSC.capMass w b)^2 * Real.exp (-(t^2*‖v‖^2)) ≤
      FSC.capMass w (fun j => b j-t*inner ℝ (w j) v) := by
  let μ := (stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)
  have hc := integral_product_sq_le μ
    (fun x => Real.exp ((t/2)*inner ℝ v x))
    (fun x => Real.exp ((-t/2)*inner ℝ v x))
    (memLp_exp_inner_restrict v (t/2) _) (memLp_exp_inner_restrict v (-t/2) _)
  have hp : (fun x : FSC.Coord d => Real.exp ((t/2)*inner ℝ v x)*
      Real.exp ((-t/2)*inner ℝ v x)) = fun _ => (1 : ℝ) := by
    funext x
    rw [← Real.exp_add]
    convert Real.exp_zero using 2 <;> ring
  have he1 : (fun x : FSC.Coord d => (Real.exp ((t/2)*inner ℝ v x))^2) =
      fun x => Real.exp (t*inner ℝ v x) := by
    funext x
    rw [exp_inner_sq]
    congr 1
    ring
  have he2 : (fun x : FSC.Coord d => (Real.exp ((-t/2)*inner ℝ v x))^2) =
      fun x => Real.exp ((-t)*inner ℝ v x) := by
    funext x
    rw [exp_inner_sq]
    congr 1
    ring
  rw [hp,he1,he2] at hc
  have hi : (∫ _ : FSC.Coord d, (1 : ℝ) ∂μ) = FSC.capMass w b := by
    simp [μ,FSC.capMass,Measure.real]
  rw [hi] at hc
  have hm : (∫ x, Real.exp (t*inner ℝ v x) ∂μ) =
      Real.exp (t^2*‖v‖^2/2)*FSC.capMass w (fun j => b j-t*inner ℝ (w j) v) :=
    cap_mgf_translate w b v t
  have hbnd : (∫ x, Real.exp ((-t)*inner ℝ v x) ∂μ) ≤
      Real.exp (t^2*‖v‖^2/2) := by
    calc
      _ ≤ (∫ x, Real.exp ((-t)*inner ℝ v x) ∂stdGaussian (FSC.Coord d)) :=
        integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun x => (Real.exp_pos ((-t)*inner ℝ v x)).le)
          (integrable_exp_inner v (-t))
      _ = _ := by rw [integral_exp_inner,neg_sq]
  have hpos : 0 ≤ ∫ x, Real.exp (t*inner ℝ v x) ∂μ :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have hh := hc.trans (mul_le_mul_of_nonneg_left hbnd hpos)
  rw [hm] at hh
  have hex : Real.exp (t^2*‖v‖^2/2)*Real.exp (t^2*‖v‖^2/2) =
      Real.exp (t^2*‖v‖^2) := by rw [← Real.exp_add];congr 1;ring
  have hmul := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(t^2*‖v‖^2))).le
  have hcancel : Real.exp (t^2*‖v‖^2)*Real.exp (-(t^2*‖v‖^2)) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  calc
    _ ≤ _ := hmul
    _ = FSC.capMass w (fun j => b j-t*inner ℝ (w j) v) *
        (Real.exp (t^2*‖v‖^2/2)*Real.exp (t^2*‖v‖^2/2))*
        Real.exp (-(t^2*‖v‖^2)) := by ring
    _ = _ := by rw [hex,mul_assoc,hcancel,mul_one]

end NegativeVotingCapShiftLower
