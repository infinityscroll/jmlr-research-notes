import GaussianFanSecondVariation

/-! Actual Gaussian surface quadratic minimization over one global offset
vector. Orthogonality is derived from zero derivatives of actual cell masses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped InnerProductSpace BigOperators
namespace NegativeVotingFanOffsetMinimization
open NegativeVotingFan NegativeVotingFanScore NegativeVotingFanHessian
  NegativeVotingFacetDegree NegativeVotingFanJacobian NegativeVotingWeightedFacet NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Additivity is derived from the actual differentiated expected maximum. -/
theorem mixedForm_add_left (B D F E : ι → FSC.Coord d) (h v w e : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    mixedForm B h (D+F) (v+w) E e = mixedForm B h D v E e+mixedForm B h F w E e := by
  rw [← secondDerivative_apply_eq_mixedForm B (D+F) E h (v+w) e σ hσ hlower,
    ← secondDerivative_apply_eq_mixedForm B D E h v e σ hσ hlower,
    ← secondDerivative_apply_eq_mixedForm B F E h w e σ hσ hlower]
  exact (secondDerivative B h E e).map_add (D,v) (F,w)

theorem mixedForm_add_right (B D E F : ι → FSC.Coord d) (h v e w : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    mixedForm B h D v (E+F) (e+w) = mixedForm B h D v E e+mixedForm B h D v F w := by
  rw [mixedForm_symm B D (E+F) h v (e+w),
    mixedForm_add_left B E F D h e w v σ hσ hlower,
    mixedForm_symm B E D h e v,mixedForm_symm B F D h w v]

/-- Homogeneity comes from the proved derivative, with no kernel estimate assumed. -/
theorem mixedForm_smul_left (B D E : ι → FSC.Coord d) (h v e : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (c : ℝ) :
    mixedForm B h (c•D) (c•v) E e = c*mixedForm B h D v E e := by
  rw [← secondDerivative_apply_eq_mixedForm B (c•D) E h (c•v) e σ hσ hlower,
    ← secondDerivative_apply_eq_mixedForm B D E h v e σ hσ hlower]
  simpa only [Prod.smul_mk,smul_eq_mul] using (secondDerivative B h E e).map_smul c (D,v)

theorem mixedForm_smul_right (B D E : ι → FSC.Coord d) (h v e : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (c : ℝ) :
    mixedForm B h D v (c•E) (c•e) = c*mixedForm B h D v E e := by
  rw [mixedForm_symm B D (c•E) h v (c•e),
    mixedForm_smul_left B E D h e v σ hσ hlower c,mixedForm_symm B E D h e v]

theorem quadraticForm_smul (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (c : ℝ) :
    quadraticForm B h (c•D) (c•v) = c^2*quadraticForm B h D v := by
  rw [← mixedForm_self B (c•D) h (c•v),
    mixedForm_smul_left B D (c•D) h v (c•v) σ hσ hlower c,
    mixedForm_smul_right B D D h v v σ hσ hlower c,mixedForm_self]
  ring

/-- Exact expansion of the literal Gaussian square-facet form. -/
theorem quadraticForm_add (B D E : ι → FSC.Coord d) (h v e : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) :
    quadraticForm B h (D+E) (v+e) = quadraticForm B h D v+
      2*mixedForm B h D v E e+quadraticForm B h E e := by
  rw [← mixedForm_self B (D+E) h (v+e),
    mixedForm_add_left B D E (D+E) h v e (v+e) σ hσ hlower,
    mixedForm_add_right B D D E h v v e σ hσ hlower,
    mixedForm_add_right B E D E h e v e σ hσ hlower,
    mixedForm_self B D h v,mixedForm_self B E h e,mixedForm_symm B E D h e v]
  ring

/-- The literal cell-mass derivative is a coordinate of the actual
mixed Gaussian surface form. -/
theorem hasDerivAt_mass_line (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ) (i : ι) :
    HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i)
      (mixedForm B h D v 0 (Pi.single i 1)) 0 := by
  have hg := hasDerivAt_jointDerivative_line_mixedForm B D 0 h v (Pi.single i 1) σ hσ hlower
  have he : (fun t : ℝ => jointDerivative (B+t•D) (h+t•v) (0,Pi.single i 1)) =
      fun t : ℝ => mass (B+t•D) (h+t•v) i := by
    funext t
    simp [jointDerivative_apply,Pi.single_apply]
  simpa only [he] using hg

/-- Calculus adapter for the actual joint mass derivative constructed by
the moving-cell theorem. A zero tangent vector gives all literal scalar
mass derivatives used by the minimization theorem. -/
theorem mass_derivatives_zero_of_joint_derivative (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (L : Parameters d ι →L[ℝ] (ι → ℝ))
    (hL : HasFDerivAt (fun p : Parameters d ι => mass p.1 p.2) L (B,h))
    (hz : L (D,v)=0) :
    ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0 := by
  have hline : HasDerivAt (fun t : ℝ => (B+t•D,h+t•v)) (D,v) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).smul_const D).const_add B).prodMk
      (((hasDerivAt_id (0:ℝ)).smul_const v).const_add h)
  have hL' : HasFDerivAt (fun p : Parameters d ι => mass p.1 p.2) L (B+(0:ℝ)•D,h+(0:ℝ)•v) := by
    simpa using hL
  have hp := hL'.comp_hasDerivAt 0 hline
  rw [hz] at hp
  intro i
  simpa only [Function.comp_def,ContinuousLinearMap.proj_apply,Pi.zero_apply] using
    (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt 0 hp

/-- A zero derivative of each actual Gaussian cell mass kills every
mixed variation with a single common offset-test vector. -/
theorem mixedForm_offset_eq_zero_of_mass_derivatives (B D : ι → FSC.Coord d)
    (h v k : ι → ℝ) (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0) :
    mixedForm B h D v 0 k = 0 := by
  have hg := hasDerivAt_jointDerivative_line_mixedForm B D 0 h v k σ hσ hlower
  have he : (fun t : ℝ => jointDerivative (B+t•D) (h+t•v) (0,k)) =
      fun t : ℝ => ∑ i, mass (B+t•D) (h+t•v) i*k i := by
    funext t
    rw [jointDerivative_apply]
    simp only [Pi.zero_apply,inner_zero_left,zero_add]
  rw [he] at hg
  have hz : HasDerivAt (fun t : ℝ => ∑ i, mass (B+t•D) (h+t•v) i*k i) 0 0 := by
    simpa using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hm i).mul_const (k i))
  exact hg.unique hz

/-- For every competing offset, the excess surface energy is exactly the
actual positive semidefinite offset-Jacobian energy. -/
theorem quadraticForm_offset_remainder (B D : ι → FSC.Coord d) (h v w : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0) :
    quadraticForm B h D w = quadraticForm B h D v+quadraticForm B h 0 (w-v) := by
  have he := quadraticForm_add B D 0 h v (w-v) σ hσ hlower
  rw [mixedForm_offset_eq_zero_of_mass_derivatives B D h v (w-v) σ hσ hlower hm] at he
  simpa using he

/-- The one global mass-preserving offset minimizes the actual Gaussian
surface quadratic form over all offset vectors. -/
theorem quadraticForm_offset_minimizes (B D : ι → FSC.Coord d) (h v : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0)
    (w : ι → ℝ) : quadraticForm B h D v ≤ quadraticForm B h D w := by
  rw [quadraticForm_offset_remainder B D h v w σ hσ hlower hm]
  exact le_add_of_nonneg_right (quadraticForm_nonneg B 0 h (w-v))

/-- Every minimizing offset differs from the mass-preserving offset by a
constant, using the actual Gaussian Jacobian kernel theorem. -/
theorem quadraticForm_offset_eq_iff_constant (B D : ι → FSC.Coord d) (h v w : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0) :
    quadraticForm B h D w=quadraticForm B h D v ↔ ∃ c : ℝ, ∀ i, w i-v i=c := by
  rw [quadraticForm_offset_remainder B D h v w σ hσ hlower hm,
    add_eq_left,quadraticForm_offsets]
  exact offsetJacobian_energy_zero_iff B (affineIndependent_of_centered_lower B σ hσ hlower) h (w-v)

/-- Fixing the zero-sum gauge makes the minimizing offset unique. -/
theorem quadraticForm_offset_eq_iff_of_centered (B D : ι → FSC.Coord d) (h v w : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0)
    (hv : ∑ i, v i=0) (hw : ∑ i, w i=0) :
    quadraticForm B h D w=quadraticForm B h D v ↔ w=v := by
  constructor
  · intro he
    obtain ⟨c,hc⟩ := (quadraticForm_offset_eq_iff_constant B D h v w σ hσ hlower hm).mp he
    have hs : (∑ i, (w i-v i))=0 := by rw [Finset.sum_sub_distrib,hw,hv,sub_self]
    have hsc : (Fintype.card ι : ℝ)*c=0 := by
      simpa only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs
    have hc0 : c=0 := (mul_eq_zero.mp hsc).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    exact funext fun i => sub_eq_zero.mp ((hc i).trans hc0)
  · rintro rfl
    rfl

/-- Exact Jacobian form of the remainder, with no supplied Schur matrix. -/
theorem quadraticForm_offset_remainder_jacobian (B D : ι → FSC.Coord d) (h v w : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hm : ∀ i, HasDerivAt (fun t : ℝ => mass (B+t•D) (h+t•v) i) 0 0) :
    quadraticForm B h D w = quadraticForm B h D v+(w-v) ⬝ᵥ (offsetJacobian B h *ᵥ (w-v)) := by
  rw [quadraticForm_offset_remainder B D h v w σ hσ hlower hm,quadraticForm_offsets]
  rfl

end NegativeVotingFanOffsetMinimization
