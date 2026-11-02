import GaussianCovarianceOffsets
import Mathlib.Analysis.Convex.Deriv

/-! Actual Gaussian mass-value concavity, including boundary probabilities,
and the nonpositive pure mass second derivative at positive covariance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingFanMassConcavity
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanValue
  NegativeVotingFanJointValue NegativeVotingFanJointInverse NegativeVotingFanSelectedOffsets
  NegativeVotingFanCovarianceValue NegativeVotingCovarianceConcavity
  NegativeVotingPositiveCovariance NegativeVotingAffineBasisLower
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def probabilityVectors (V : Type*) [Fintype V] : Set (V → ℝ) :=
  {p | (∀ i,0≤p i) ∧ ∑ i,p i=1}

theorem probabilityVectors_convex : Convex ℝ (probabilityVectors V) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i)),?_⟩
  change (∑ i, (a*p i+b*q i))=1
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hp.2,hq.2]
  simpa using hab

theorem potential_affine_masses (B : V → FSC.Coord d) (p q h : V → ℝ)
    (a b : ℝ) (hab : a+b=1) :
    potential B (a • p+b • q) h=a*potential B p h+b*potential B q h := by
  unfold potential
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib]
  simp_rw [mul_assoc,←Finset.mul_sum]
  nlinarith [congrArg (fun x : ℝ => x*expectedMax B h) hab]

/-- Infima of the actual affine Gaussian potentials give concavity on the
whole probability simplex; rank and strict positivity are unnecessary. -/
theorem optimizedValue_mass_concave (B : V → FSC.Coord d) :
    ConcaveOn ℝ (probabilityVectors V) (optimizedValue B) := by
  refine ⟨probabilityVectors_convex,?_⟩
  intro p hp q hq a b ha hb hab
  change a*optimizedValue B p+b*optimizedValue B q≤optimizedValue B (a • p+b • q)
  apply le_csInf (Set.range_nonempty _)
  rintro z ⟨h,rfl⟩
  change a*optimizedValue B p+b*optimizedValue B q ≤ potential B (a • p+b • q) h
  rw [potential_affine_masses B p q h a b hab]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (optimizedValue_le_potential B p hp.1 hp.2 h) ha)
    (mul_le_mul_of_nonneg_left (optimizedValue_le_potential B q hq.1 hq.2 h) hb)

/-- A local concavity consequence uses actual derivatives, including the
standard total derivative convention when a second derivative is absent. -/
theorem second_deriv_nonpos_of_concave_near (f : ℝ → ℝ) (S : Set ℝ)
    (hconc : ConcaveOn ℝ S f) (hS : S∈𝓝 (0:ℝ)) (hc : ContDiffAt ℝ 1 f 0) :
    deriv (deriv f) 0≤0 := by
  have he : ∀ᶠ t : ℝ in 𝓝 0,t∈S ∧ DifferentiableAt ℝ f t :=
    (show ∀ᶠ t : ℝ in 𝓝 0,t∈S from hS).and
      ((hc.eventually (by decide)).mono (fun t ht => ht.differentiableAt_one))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  have hcc := hconc.subset (fun t ht => (hball ht).1) (convex_ball (0:ℝ) r)
  have hm := hcc.antitoneOn_deriv (fun t ht => (hball ht).2)
  have hh := hm.derivWithin_nonpos (x := (0:ℝ))
  rwa [derivWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) hr)] at hh

/-- Concavity along every centered mass line through a positive probability. -/
theorem optimizedValue_mass_line_second_nonpos (B : V → FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : NegativeVotingCapTail.CenteredSingularLowerBound B σ)
    (p v : V → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hv : ∑ i,v i=0) :
    deriv (deriv (fun t : ℝ => optimizedValue B (p+t • v))) 0≤0 := by
  let u : centeredGauge V := ⟨v,hv⟩
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact NegativeVotingFacetDegree.centered_singular_rows_ne B σ hσ hlower i j hij he
  let h₀ := selectedOffsets B p
  have hmass : mass B h₀=p := selectedOffsets_mass B hB p hp hs
  have hV := (jointValue_C1_and_derivative B h₀ σ hσ hlower (by simpa only [hmass] using hp)).1
  rw [hmass] at hV
  have hQ : ContDiffAt ℝ 1 (fun t : ℝ => (B,t • u)) 0 :=
    contDiffAt_const.prodMk (contDiffAt_id.smul contDiffAt_const)
  have hV' : ContDiffAt ℝ 1 (fun q : JointCoordinates d V => optimizedValue q.1 (p+(q.2 : V → ℝ)))
      (B,(0:ℝ) • u) := by simpa only [zero_smul] using hV
  have hc : ContDiffAt ℝ 1 (fun t : ℝ => optimizedValue B (p+t • v)) 0 := by
    simpa only [Function.comp_def,Submodule.coe_smul,u] using hV'.comp 0 hQ
  let A : ℝ →ᵃ[ℝ] (V → ℝ) := AffineMap.lineMap p (p+v)
  have hA (t : ℝ) : A t=p+t • v := by
    simp only [A,AffineMap.lineMap_apply_module]
    module
  have hconc := ConcaveOn.comp_affineMap A (optimizedValue_mass_concave B)
  have hpos : ∀ᶠ t : ℝ in 𝓝 0,∀ i,0<p i+t*v i := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℝ => p i+t*v i) 0 := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (by simpa using hp i))
  have hS : A ⁻¹' probabilityVectors V∈𝓝 (0:ℝ) := by
    filter_upwards [hpos] with t ht
    change A t∈probabilityVectors V
    rw [hA]
    refine ⟨fun i => (ht i).le,?_⟩
    change (∑ i, (p i+t*v i))=1
    rw [Finset.sum_add_distrib,←Finset.mul_sum,hs,hv]
    ring
  have hc' : ContDiffAt ℝ 1 ((optimizedValue B) ∘ A) 0 := by
    simpa only [Function.comp_def,hA] using hc
  simpa only [Function.comp_def,hA] using second_deriv_nonpos_of_concave_near _ _ hconc hS hc'

variable {m : ℕ} [NeZero m]

theorem covarianceValue_mass_concave (G : Matrix (Fin m) (Fin m) ℝ) :
    ConcaveOn ℝ (probabilityVectors (Fin m)) (covarianceValue G) :=
  optimizedValue_mass_concave (covarianceRows G)

theorem operatorValue_mass_concave (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) :
    ConcaveOn ℝ (probabilityVectors (Fin m)) (fun p => operatorValue b p C) :=
  covarianceValue_mass_concave (gramVelocity b C)

/-- No pure-mass curvature hypothesis is supplied for the actual covariance
functional: it follows from the mass-dual concavity and genuine C1 chart. -/
theorem operatorValue_mass_line_second_nonpos (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈pdCone)
    (p v : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hv : ∑ i,v i=0) :
    deriv (deriv (fun t : ℝ => operatorValue b (p+t • v) C)) 0≤0 := by
  obtain ⟨R,hR,_,hRC⟩ := exists_positive_factor C hC
  let bR := mappedBasis b R
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound bR
  have hg : Matrix.gram ℝ bR=gramVelocity b C := factor_gram b C R hR hRC
  have hh := optimizedValue_mass_line_second_nonpos bR σ hσ hlower p v hp hs hv
  simpa only [operatorValue,←hg,covarianceValue_gram] using hh

end NegativeVotingFanMassConcavity
