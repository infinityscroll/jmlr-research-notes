import GaussianMassCentroid
import GaussianMaximumLocalization

/-! Exact global quadratic mass-profile envelope from the Gaussian threshold principle. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory WeakSimplex Set
open scoped ENNReal NNReal BigOperators
namespace NegativeVotingMassProfileEnvelope
open NegativeVotingMassCentroid NegativeVotingGaussianMaximum
  NegativeVotingGaussianTail NegativeVotingGaussianMaximumLocalization

theorem gaussianMassProfile_nonneg (p : ℝ) : 0≤gaussianMassProfile p := by
  unfold gaussianMassProfile
  split_ifs
  · exact (normalPDF_pos _).le
  · exact le_rfl

/-- The profile is attained by a literal Gaussian half-line, with constant
weights supplying the exact p=0 and p=1 endpoints. -/
theorem gaussianMassProfile_attained (p : ℝ) (hp:p∈Icc (0:ℝ) 1) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x,0≤f x ∧ f x≤1) ∧
      (∫ x,f x ∂gaussianReal 0 1)=p ∧
      (∫ x,f x*x ∂gaussianReal 0 1)=gaussianMassProfile p := by
  by_cases h0 : p=0
  · subst p
    refine ⟨fun _=>0,measurable_const,?_,?_,?_⟩ <;> simp [gaussianMassProfile]
  by_cases h1 : p=1
  · subst p
    refine ⟨fun _=>1,measurable_const,?_,?_,?_⟩ <;>
      simp [gaussianMassProfile,integral_id_gaussianReal]
  have hp0 : 0<p := lt_of_le_of_ne hp.1 (Ne.symm h0)
  have hp1 : p<1 := lt_of_le_of_ne hp.2 h1
  refine ⟨upperIndicator (fun x:ℝ=>x) (-normalQuantile p),
    measurable_const.indicator measurableSet_Ioi,?_,?_,?_⟩
  · intro x
    by_cases hx : -normalQuantile p<x <;> simp [upperIndicator,hx]
  · rw [gaussian_upper_mass,normalCDF_neg,normalCDF_normalQuantile hp0 hp1]
    ring
  · have he : (fun x:ℝ=>upperIndicator (fun y:ℝ=>y) (-normalQuantile p) x*x)=
        (Ioi (-normalQuantile p)).indicator (fun x:ℝ=>x) := by
      funext x
      by_cases hx : -normalQuantile p<x <;> simp [upperIndicator,hx]
    rw [he,integral_indicator measurableSet_Ioi,gaussian_upper_first_moment,normalPDF_even]
    simp only [gaussianMassProfile,ite_eq_left (show 0<p ∧ p<1 from ⟨hp0,hp1⟩)]

/-- A global supporting affine bound, obtained from actual Gaussian integrals.
No concavity or inverse-CDF derivative premise is supplied. -/
theorem gaussianMassProfile_threshold_tangent (p t : ℝ) (hp:p∈Icc (0:ℝ) 1) :
    gaussianMassProfile p ≤ normalPDF t+t*(p-(1-normalCDF t)) := by
  obtain ⟨f,hf,h01,hm,hM⟩ := gaussianMassProfile_attained p hp
  have hh := remainder_bound_of_gaussian_score (gaussianReal 0 1) f (fun x:ℝ=>x) t
    hf.aemeasurable measurable_id (by simp) (ae_of_all _ h01)
  rwa [hm,hM] at hh

theorem gaussianMassProfile_uniform (n : ℕ) :
    gaussianMassProfile (1/((n:ℝ)+2))=normalPDF (upperQuantile n) := by
  have h0 : 0<1/((n:ℝ)+2) := by positivity
  have h1 : 1/((n:ℝ)+2)<1 :=
    (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  simp only [gaussianMassProfile,ite_eq_left (show 0<1/((n:ℝ)+2) ∧ 1/((n:ℝ)+2)<1 from ⟨h0,h1⟩),
    upperQuantile,normalPDF_even]

/-- The exact quantile-squared coefficient suffices globally, including both endpoints. -/
theorem gaussianMassProfile_square_quantile_envelope (n : ℕ) (p : ℝ)
    (hp:p∈Icc (0:ℝ) 1) :
    gaussianMassProfile p^2 ≤ gaussianMassProfile (1/((n:ℝ)+2))^2+
      (2*upperQuantile n*normalPDF (upperQuantile n))*(p-1/((n:ℝ)+2))+
      upperQuantile n^2*(p-1/((n:ℝ)+2))^2 := by
  have ht : 1-normalCDF (upperQuantile n)=1/((n:ℝ)+2) := by
    rw [←normalCDF_neg,upperQuantile_tail]
  have hT := gaussianMassProfile_threshold_tangent p (upperQuantile n) hp
  rw [ht,←gaussianMassProfile_uniform] at hT
  have hI := gaussianMassProfile_nonneg p
  have hS := mul_self_le_mul_self hI hT
  calc
    _ ≤ (gaussianMassProfile (1/((n:ℝ)+2))+
        upperQuantile n*(p-1/((n:ℝ)+2)))^2 := by simpa only [sq] using hS
    _ = _ := by rw [gaussianMassProfile_uniform]; ring

/-- The manuscript's curvatureBound follows from the stronger exact bound for
every n>0, without a sufficiently-large-n or p-away-from-endpoints condition. -/
theorem gaussianMassProfile_square_envelope (n : ℕ) (hn:0<n) (p : ℝ)
    (hp:p∈Icc (0:ℝ) 1) :
    gaussianMassProfile p^2 ≤ gaussianMassProfile (1/((n:ℝ)+2))^2+
      (2*upperQuantile n*normalPDF (upperQuantile n))*(p-1/((n:ℝ)+2))+
      curvatureBound n*(p-1/((n:ℝ)+2))^2 := by
  have hq : upperQuantile n^2≤curvatureBound n := by
    have hlog := upperQuantile_sq_le_log n hn
    have hmax := le_max_left (2*Real.log ((n:ℝ)+2)+1) (6:ℝ)
    unfold curvatureBound
    linarith
  exact (gaussianMassProfile_square_quantile_envelope n p hp).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hq (sq_nonneg _)))

end NegativeVotingMassProfileEnvelope
