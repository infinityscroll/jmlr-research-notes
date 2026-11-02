import GaussianPolynomialTiltDerivatives
import GaussianCapSecondMoment

/-! Polynomial Gaussian Stein identities on genuine polyhedra, obtained by
differentiating the already proved fixed-face exponential-tilt identity.
All mixed moments and derivatives are derived from actual Gaussian laws. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace BigOperators ENNReal Topology Classical
namespace NegativeVotingCapPolynomialStein
open NegativeVotingPolyhedral NegativeVotingPolynomialTilt
variable {d : ℕ} {ι : Type*} [Fintype ι]

 def capTiltMoment (w : ι→FSC.Coord d) (b : ι→ℝ) (v : FSC.Coord d) (k : ℕ) (t : ℝ) : ℝ :=
   ∫ x in FSC.cap w b,(inner ℝ v x)^k*Real.exp (t*inner ℝ v x) ∂stdGaussian (FSC.Coord d)

 def faceTiltMoment (w : ι→FSC.Coord d) (b : ι→ℝ) (j : ι)
    (v : FSC.Coord d) (k : ℕ) (t : ℝ) : ℝ :=
   ∫ x in faceEvent w b j,(inner ℝ v x)^k*Real.exp (t*inner ℝ v x) ∂FSC.sliceLaw (w j) (b j)

 def capMixedTiltMoment (w : ι→FSC.Coord d) (b : ι→ℝ) (u v : FSC.Coord d)
    (k : ℕ) (t : ℝ) : ℝ :=
   ∫ x in FSC.cap w b,inner ℝ u x*(inner ℝ v x)^k*Real.exp (t*inner ℝ v x)
     ∂stdGaussian (FSC.Coord d)

 theorem hasDerivAt_capTiltMoment (w : ι→FSC.Coord d) (b : ι→ℝ)
    (v : FSC.Coord d) (k : ℕ) (t : ℝ) :
    HasDerivAt (capTiltMoment w b v k) (capTiltMoment w b v (k+1) t) t := by
  have ht : t∈interior (integrableExpSet (fun x:FSC.Coord d=>inner ℝ v x)
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b))) := by
    rw [cap_integrableExpSet,interior_univ]
    trivial
  exact hasDerivAt_integral_pow_mul_exp_real ht k

 theorem hasDerivAt_faceTiltMoment (w : ι→FSC.Coord d) (b : ι→ℝ) (j : ι)
    (v : FSC.Coord d) (k : ℕ) (t : ℝ) :
    HasDerivAt (faceTiltMoment w b j v k) (faceTiltMoment w b j v (k+1) t) t := by
  have ht : t∈interior (integrableExpSet (fun x:FSC.Coord d=>inner ℝ v x)
      ((FSC.sliceLaw (w j) (b j)).restrict (faceEvent w b j))) := by
    rw [face_integrableExpSet,interior_univ]
    trivial
  exact hasDerivAt_integral_pow_mul_exp_real ht k

 theorem hasDerivAt_capMixedTiltMoment (w : ι→FSC.Coord d) (b : ι→ℝ)
    (u v : FSC.Coord d) (k : ℕ) (t : ℝ) :
    HasDerivAt (capMixedTiltMoment w b u v k) (capMixedTiltMoment w b u v (k+1) t) t := by
  apply hasDerivAt_weighted_power_exp
  · exact (IsGaussian.memLp_two_id.const_inner (𝕜:=ℝ) u).restrict _
  · fun_prop
  · exact cap_integrableExpSet w b v

 theorem capMixedTiltMoment_zero (w : ι→FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι→ℝ) (hb : FSC.NoCoincident w b) (u v : FSC.Coord d) (t : ℝ) :
    capMixedTiltMoment w b u v 0 t=t*inner ℝ u v*capTiltMoment w b v 0 t-
      ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v 0 t := by
  simpa only [capMixedTiltMoment,capTiltMoment,faceTiltMoment,faceMGF,mgf,
    pow_zero,mul_one,one_mul] using cap_tilt_first_moment_boundary w hw b hb u v t

/-- The whole polynomial hierarchy at every tilt, derived inductively from
actual derivatives. The normals/supports and Gaussian face measures stay fixed. -/
 theorem capMixedTiltMoment_successor (w : ι→FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι→ℝ) (hb : FSC.NoCoincident w b) (u v : FSC.Coord d) (k : ℕ) :
    ∀ t : ℝ,capMixedTiltMoment w b u v (k+1) t=
      t*inner ℝ u v*capTiltMoment w b v (k+1) t+
      ((k+1:ℕ):ℝ)*inner ℝ u v*capTiltMoment w b v k t-
      ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v (k+1) t := by
  induction k with
  | zero =>
    intro t
    have hprod := ((hasDerivAt_id t).mul_const (inner ℝ u v)).mul
      (hasDerivAt_capTiltMoment w b v 0 t)
    have hsum : HasDerivAt
        (fun s:ℝ=>∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v 0 s)
        (∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v 1 t) t := by
      apply HasDerivAt.fun_sum
      intro j _
      exact (hasDerivAt_faceTiltMoment w b j v 0 t).const_mul _
    have hr := hprod.sub hsum
    have hfunc : (fun s:ℝ=>capMixedTiltMoment w b u v 0 s)=
        fun s=>s*inner ℝ u v*capTiltMoment w b v 0 s-
          ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v 0 s :=
      funext (capMixedTiltMoment_zero w hw b hb u v)
    change HasDerivAt (fun s=>s*inner ℝ u v*capTiltMoment w b v 0 s-
      ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v 0 s) _ t at hr
    rw [←hfunc] at hr
    have he := (hasDerivAt_capMixedTiltMoment w b u v 0 t).unique hr
    convert he using 1 <;> simp only [Nat.cast_one,Nat.cast_add,Nat.cast_zero,id_eq] <;> ring
  | succ k ih =>
    intro t
    have hprod := ((hasDerivAt_id t).mul_const (inner ℝ u v)).mul
      (hasDerivAt_capTiltMoment w b v (k+1) t)
    have hterm := (hasDerivAt_capTiltMoment w b v k t).const_mul
      (((k+1:ℕ):ℝ)*inner ℝ u v)
    have hsum : HasDerivAt
        (fun s:ℝ=>∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v (k+1) s)
        (∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v (k+1+1) t) t := by
      apply HasDerivAt.fun_sum
      intro j _
      exact (hasDerivAt_faceTiltMoment w b j v (k+1) t).const_mul _
    have hr := (hprod.add hterm).sub hsum
    have hfunc : (fun s:ℝ=>capMixedTiltMoment w b u v (k+1) s)=
        fun s=>s*inner ℝ u v*capTiltMoment w b v (k+1) s+
          ((k+1:ℕ):ℝ)*inner ℝ u v*capTiltMoment w b v k s-
          ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v (k+1) s :=
      funext ih
    change HasDerivAt (fun s=>s*inner ℝ u v*capTiltMoment w b v (k+1) s+
      ((k+1:ℕ):ℝ)*inner ℝ u v*capTiltMoment w b v k s-
      ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*faceTiltMoment w b j v (k+1) s) _ t at hr
    rw [←hfunc] at hr
    have he := (hasDerivAt_capMixedTiltMoment w b u v (k+1) t).unique hr
    convert he using 1 <;> simp only [Nat.cast_succ,Nat.cast_add,Nat.cast_one,id_eq] <;> ring

/-- Actual Gaussian polynomial integration by parts with its literal face term. -/
 theorem gaussian_cap_power_stein (w : ι→FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι→ℝ) (hb : FSC.NoCoincident w b) (u v : FSC.Coord d) (k : ℕ) :
    (∫ x in FSC.cap w b,inner ℝ u x*(inner ℝ v x)^(k+1) ∂stdGaussian (FSC.Coord d))=
      ((k+1:ℕ):ℝ)*inner ℝ u v*
        (∫ x in FSC.cap w b,(inner ℝ v x)^k ∂stdGaussian (FSC.Coord d))-
      ∑ j,(WeakSimplex.normalPDF (b j)*inner ℝ (w j) u)*
        (∫ x in faceEvent w b j,(inner ℝ v x)^(k+1) ∂FSC.sliceLaw (w j) (b j)) := by
  simpa only [capMixedTiltMoment,capTiltMoment,faceTiltMoment,zero_mul,Real.exp_zero,
    mul_one,zero_add] using capMixedTiltMoment_successor w hw b hb u v k 0

end NegativeVotingCapPolynomialStein
