import GaussianFanMassJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Uniqueness and inverse regularity of actual Gaussian fan offsets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped RealInnerProductSpace BigOperators Topology Classical

namespace NegativeVotingFanInverse
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingCapTail
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Differentiation of the actual mass map along a line, paired with its direction. -/
theorem hasDerivAt_mass_line_pairing (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i, v i * mass B (h + s • v) i)
      (v ⬝ᵥ (offsetJacobian B (h + t • v) *ᵥ v)) t := by
  have hline : HasDerivAt (fun s : ℝ => h + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add h
  have hi (i : ι) : HasDerivAt (fun s : ℝ => v i * mass B (h + s • v) i)
      (v i * (offsetJacobian B (h + t • v) *ᵥ v) i) t := by
    have he := ((hasFDerivAt_mass B σ hσ hlower (h + t • v) i).comp_hasDerivAt t hline).const_mul (v i)
    simpa only [Function.comp_def, massDerivative_eq_offsetJacobian B σ hσ hlower] using he
  exact HasDerivAt.fun_sum (fun i _ => hi i)

/-- Equality of actual Gaussian masses forces equality of centered offsets. -/
theorem centered_offsets_unique (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h k : ι → ℝ)
    (hh : ∑ i, h i = 0) (hk : ∑ i, k i = 0) (hm : mass B h = mass B k) : h = k := by
  by_contra hne
  let v : ι → ℝ := k - h
  have hv : ∑ i, v i = 0 := by simp [v, Finset.sum_sub_distrib, hh, hk]
  have hv0 : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hmono : StrictMono (fun s : ℝ => ∑ i, v i * mass B (h + s • v) i) :=
    strictMono_of_hasDerivAt_pos
      (hasDerivAt_mass_line_pairing B σ hσ hlower h v)
      (fun t => offsetJacobian_pos_centered_of_lower B σ hσ hlower (h + t • v) v hv hv0)
  have ht := hmono (by norm_num : (0 : ℝ) < 1)
  have hlast : h + (1 : ℝ) • v = k := by simp [v]
  dsimp only at ht
  rw [hlast] at ht
  simp only [zero_smul, add_zero] at ht
  rw [hm] at ht
  exact (lt_irrefl _) ht

/-- Existence from coercive Gaussian optimization and uniqueness from the
actual positive Jacobian combine into a genuine unique centered offset. -/
theorem existsUnique_offsets_with_prescribed_masses (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃! h : ι → ℝ, (∑ i, h i = 0) ∧ mass B h = p := by
  have hinj : Function.Injective B := fun i j he => by
    by_contra hij
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B σ hσ hlower i j hij he
  obtain ⟨h, hh, hm⟩ := exists_offsets_with_prescribed_masses B hinj p hp hs
  refine ⟨h, ⟨hh, funext hm⟩, ?_⟩
  intro k hk
  exact centered_offsets_unique B σ hσ hlower k h hk.1 hh (hk.2.trans (funext hm).symm)

/-- The literal zero-sum offset/mass tangent space. -/
def centeredGauge (ι : Type*) [Fintype ι] : Submodule ℝ (ι → ℝ) where
  carrier := {v | ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw; simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib]; rw [hv, hw, add_zero]
  smul_mem' := by intro c v hv; simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; rw [hv, mul_zero]

@[simp] theorem mem_centeredGauge (v : ι → ℝ) : v ∈ centeredGauge ι ↔ ∑ i, v i = 0 := Iff.rfl

def centeringLinear : (ι → ℝ) →ₗ[ℝ] centeredGauge ι where
  toFun v := ⟨fun i => v i - (∑ j, v j) / (Fintype.card ι : ℝ), by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    change ∑ i, (v i - (∑ j, v j) / (Fintype.card ι : ℝ)) = 0
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    change (v + w) i - (∑ j, (v + w) j) / (Fintype.card ι : ℝ) =
      (v i - (∑ j, v j) / (Fintype.card ι : ℝ)) +
        (w i - (∑ j, w j) / (Fintype.card ι : ℝ))
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c v := by
    apply Subtype.ext
    funext i
    change (c • v) i - (∑ j, (c • v) j) / (Fintype.card ι : ℝ) =
      c * (v i - (∑ j, v j) / (Fintype.card ι : ℝ))
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    ring

def centering : (ι → ℝ) →L[ℝ] centeredGauge ι := centeringLinear.toContinuousLinearMap

@[simp] theorem centering_apply (v : ι → ℝ) (i : ι) :
    (centering v : ι → ℝ) i = v i - (∑ j, v j) / (Fintype.card ι : ℝ) := rfl

@[simp] theorem centering_centered (v : centeredGauge ι) : centering (v : ι → ℝ) = v := by
  apply Subtype.ext
  funext i
  have hv : ∑ j, (v : ι → ℝ) j = 0 := v.property
  simp [hv]

theorem centering_eq_zero_iff (v : ι → ℝ) : centering v = 0 ↔ ∃ c : ℝ, ∀ i, v i = c := by
  constructor
  · intro hv
    refine ⟨(∑ j, v j) / (Fintype.card ι : ℝ), fun i => ?_⟩
    have he := congrArg (fun w : centeredGauge ι => (w : ι → ℝ) i) hv
    simpa only [centering_apply, ZeroMemClass.coe_zero, Pi.zero_apply, sub_eq_zero] using he
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    funext i
    have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [centering_apply, hc, hn]

/-- The actual mass map, translated from the affine probability hyperplane
into the zero-sum tangent space by a fixed linear projection. -/
def centeredMass (B : ι → FSC.Coord d) : centeredGauge ι → centeredGauge ι :=
  fun h => centering (mass B (h : ι → ℝ))

@[simp] theorem centeredMass_apply (B : ι → FSC.Coord d) (h : centeredGauge ι) (i : ι) :
    (centeredMass B h : ι → ℝ) i = mass B (h : ι → ℝ) i - 1 / (Fintype.card ι : ℝ) := by
  simp [centeredMass, mass_sum]

/-- The derivative is obtained by composing the actual checked mass derivative. -/
def centeredMassDerivative (B : ι → FSC.Coord d) (h : centeredGauge ι) :
    centeredGauge ι →L[ℝ] centeredGauge ι :=
  centering.comp ((ContinuousLinearMap.pi (massDerivative B (h : ι → ℝ))).comp
    (centeredGauge ι).subtypeL)

theorem hasFDerivAt_centeredMass (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : centeredGauge ι) :
    HasFDerivAt (centeredMass B) (centeredMassDerivative B h) h := by
  exact (centering.hasFDerivAt.comp h
    ((hasFDerivAt_mass_vector B σ hσ hlower (h : ι → ℝ)).comp h
      (centeredGauge ι).subtypeL.hasFDerivAt))

theorem contDiff_centeredMass (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) : ContDiff ℝ 1 (centeredMass B) := by
  change ContDiff ℝ 1 (centering ∘ mass B ∘ (centeredGauge ι).subtypeL)
  exact (centering : (ι → ℝ) →L[ℝ] centeredGauge ι).contDiff.comp
    ((contDiff_mass_vector B σ hσ hlower).comp (centeredGauge ι).subtypeL.contDiff)

/-- Strict quadratic positivity proves injectivity of the actual derivative
on the gauge, even before using its finite-dimensional surjectivity. -/
theorem centeredMassDerivative_injective (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : centeredGauge ι) :
    Function.Injective (centeredMassDerivative B h) := by
  have hk : (centeredMassDerivative B h).ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hz : centering (fun i => massDerivative B (h : ι → ℝ) i (v : ι → ℝ)) = 0 := hv
    obtain ⟨c, hc⟩ := (centering_eq_zero_iff _).mp hz
    simp only [massDerivative_eq_offsetJacobian B σ hσ hlower] at hc
    have hsum : ∑ i, (v : ι → ℝ) i = 0 := v.property
    have hq : (v : ι → ℝ) ⬝ᵥ (offsetJacobian B (h : ι → ℝ) *ᵥ (v : ι → ℝ)) = 0 := by
      simp only [dotProduct, hc, ← Finset.sum_mul, hsum, zero_mul]
    by_contra hvne
    have hp := offsetJacobian_pos_centered_of_lower B σ hσ hlower (h : ι → ℝ)
      (v : ι → ℝ) hsum (fun he => hvne (Subtype.ext he))
    exact (not_lt_of_ge (le_of_eq hq)) hp
  exact LinearMap.ker_eq_bot.mp hk

/-- Surjectivity is derived from finite dimension; the inverse is a genuine
continuous linear equivalence, not a supplied inverse matrix. -/
def centeredMassDerivativeEquiv (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : centeredGauge ι) :
    centeredGauge ι ≃L[ℝ] centeredGauge ι :=
  ContinuousLinearEquiv.ofBijective (centeredMassDerivative B h)
    (LinearMap.ker_eq_bot.mpr (centeredMassDerivative_injective B σ hσ hlower h))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp
      (centeredMassDerivative_injective B σ hσ hlower h)))

@[simp] theorem centeredMassDerivativeEquiv_coe (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : centeredGauge ι) :
    (centeredMassDerivativeEquiv B σ hσ hlower h : centeredGauge ι →L[ℝ] centeredGauge ι) =
      centeredMassDerivative B h := rfl

/-- The inverse function theorem applies to the actual Gaussian mass map.
The local inverse is C1 and has the inverse of the derived Jacobian. -/
theorem exists_local_C1_mass_inverse (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (h : centeredGauge ι) :
    ∃ e : OpenPartialHomeomorph (centeredGauge ι) (centeredGauge ι),
      (⇑e = centeredMass B) ∧ h ∈ e.source ∧
      ContDiffAt ℝ 1 e.symm (centeredMass B h) ∧
      HasFDerivAt e.symm
        ((centeredMassDerivativeEquiv B σ hσ hlower h).symm :
          centeredGauge ι →L[ℝ] centeredGauge ι) (centeredMass B h) := by
  let L := centeredMassDerivativeEquiv B σ hσ hlower h
  have hc : ContDiffAt ℝ 1 (centeredMass B) h :=
    (contDiff_centeredMass B σ hσ hlower).contDiffAt
  have hd : HasFDerivAt (centeredMass B) (L : centeredGauge ι →L[ℝ] centeredGauge ι) h :=
    hasFDerivAt_centeredMass B σ hσ hlower h
  let e := hc.toOpenPartialHomeomorph (centeredMass B) hd (by norm_num)
  refine ⟨e, rfl, hc.mem_toOpenPartialHomeomorph_source hd (by norm_num), ?_, ?_⟩
  · exact hc.to_localInverse hd (by norm_num)
  · exact (hc.hasStrictFDerivAt' hd (by norm_num)).to_localInverse.hasFDerivAt

/-- Any chart constructed for the actual map has a C1 inverse on its whole
open target: derivative invertibility has been proved at every source point. -/
theorem mass_chart_inverse_contDiffOn (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ)
    (e : OpenPartialHomeomorph (centeredGauge ι) (centeredGauge ι))
    (he : ⇑e = centeredMass B) : ContDiffOn ℝ 1 e.symm e.target := by
  intro q hq
  let L := centeredMassDerivativeEquiv B σ hσ hlower (e.symm q)
  have hd : HasFDerivAt e (L : centeredGauge ι →L[ℝ] centeredGauge ι) (e.symm q) := by
    rw [he]
    exact hasFDerivAt_centeredMass B σ hσ hlower (e.symm q)
  have hc : ContDiffAt ℝ 1 e (e.symm q) := by
    rw [he]
    exact (contDiff_centeredMass B σ hσ hlower).contDiffAt
  exact (e.contDiffAt_symm hq hd hc).contDiffWithinAt

/-- The inverse chart realizes literal Gaussian probabilities, after the
explicit translation from the centered tangent coordinates. -/
theorem mass_chart_inverse_realizes (B : ι → FSC.Coord d)
    (e : OpenPartialHomeomorph (centeredGauge ι) (centeredGauge ι))
    (he : ⇑e = centeredMass B) (q : centeredGauge ι) (hq : q ∈ e.target) :
    mass B (e.symm q : ι → ℝ) = fun i => (q : ι → ℝ) i + 1 / (Fintype.card ι : ℝ) := by
  have hh : centeredMass B (e.symm q) = q := by rw [← he]; exact e.right_inv hq
  funext i
  have hi := congrArg (fun x : centeredGauge ι => (x : ι → ℝ) i) hh
  rw [centeredMass_apply] at hi
  linarith

/-- Every positive probability vector has its unique centered Gaussian offset
and a genuine local C1 inverse on an open neighborhood in the probability
hyperplane. Neither inverse existence nor differentiability is an input. -/
theorem exists_prescribed_mass_C1_chart (B : ι → FSC.Coord d) (σ : ℝ) (hσ : 0 < σ)
    (hlower : CenteredSingularLowerBound B σ) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ h : centeredGauge ι, mass B (h : ι → ℝ) = p ∧
      ∃ e : OpenPartialHomeomorph (centeredGauge ι) (centeredGauge ι),
        (⇑e = centeredMass B) ∧ h ∈ e.source ∧ centering p ∈ e.target ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
        ∀ q ∈ e.target, mass B (e.symm q : ι → ℝ) =
          fun i => (q : ι → ℝ) i + 1 / (Fintype.card ι : ℝ) := by
  obtain ⟨h, ⟨hh, hm⟩, _⟩ := existsUnique_offsets_with_prescribed_masses B σ hσ hlower p hp hs
  let h₀ : centeredGauge ι := ⟨h, hh⟩
  obtain ⟨e, he, hsource, _, _⟩ := exists_local_C1_mass_inverse B σ hσ hlower h₀
  have hpoint : e h₀ = centering p := by
    rw [he]
    change centering (mass B h) = centering p
    rw [hm]
  have htarget := e.map_source hsource
  rw [hpoint] at htarget
  exact ⟨h₀, hm, e, he, hsource, htarget,
    mass_chart_inverse_contDiffOn B σ hσ hlower e he,
    fun q hq => mass_chart_inverse_realizes B e he q hq⟩

end NegativeVotingFanInverse
