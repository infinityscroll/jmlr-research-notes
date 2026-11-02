import GaussianRegularScoreLaw

/-! Actual assignment-independent second-chaos lower bounds, with zero-mass
and zero-centroid cases included. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology Classical RealInnerProductSpace
namespace NegativeVotingSecondChaosLower
open NegativeVoting NegativeVotingModern NegativeVotingFractionalMass
  NegativeVotingMassCentroid OAI.MinUncut.GaussianHermite

/-- Weighted Jensen/Cauchy follows from nonnegativity of the actual integrated
quadratic polynomial. No positive-mass division is used. -/
theorem fractional_weighted_cauchy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f g : X → ℝ)
    (hf : AEMeasurable f μ) (h01 : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1)
    (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, f x ∂μ)*(∫ x, f x*(g x)^2 ∂μ) := by
  have hfI := fractional_integrable μ f hf h01
  have hfg := fractional_mul_integrable μ f g hf h01 (hg.integrable (by norm_num))
  have hfg2 := fractional_mul_integrable μ f (fun x => (g x)^2) hf h01
    (by simpa only [sq,Pi.mul_def] using hg.integrable_mul hg)
  have hpoly (t : ℝ) : 0 ≤ (∫ x, f x ∂μ)*(t*t)+
      (-2*(∫ x, f x*g x ∂μ))*t+(∫ x, f x*(g x)^2 ∂μ) := by
    have hnon : 0 ≤ ∫ x, f x*(g x-t)^2 ∂μ :=
      integral_nonneg_of_ae (h01.mono fun x hx => mul_nonneg hx.1 (sq_nonneg _))
    have he : (fun x => f x*(g x-t)^2)=
        (fun x => (f x*(g x)^2-(2*t)*(f x*g x))+t^2*f x) := by funext x; ring
    have hsub : Integrable (fun x => f x*(g x)^2-(2*t)*(f x*g x)) μ :=
      hfg2.sub (hfg.const_mul (2*t))
    rw [he,integral_add hsub (hfI.const_mul (t^2)),
      integral_sub hfg2 (hfg.const_mul _),integral_const_mul,integral_const_mul] at hnon
    nlinarith
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  nlinarith

variable {κ : Type*} [Fintype κ]

def linearObservable (u : EuclideanSpace ℝ κ) (x : κ → ℝ) : ℝ := ∑ j, u j*x j

def firstMomentVector (f : (κ → ℝ) → ℝ) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun j => ∫ x, x j*f x ∂standardGaussian κ)

def centroidDirection (f : (κ → ℝ) → ℝ) : EuclideanSpace ℝ κ :=
  ‖firstMomentVector f‖⁻¹ • firstMomentVector f

theorem linearObservable_memLp (u : EuclideanSpace ℝ κ) :
    MemLp (linearObservable u) 2 (standardGaussian κ) := by
  unfold linearObservable
  apply memLp_finsetSum Finset.univ
  intro j _
  have h : MemLp (fun x : κ → ℝ => x j) 2 (standardGaussian κ) := by
    simpa only [MvPolynomial.eval_X] using memLp_mvpoly (MvPolynomial.X j : MvPolynomial κ ℝ)
  exact h.const_mul (u j)

theorem firstMomentVector_norm_sq (f : (κ → ℝ) → ℝ) :
    ‖firstMomentVector f‖^2=∑ j, (∫ x, x j*f x ∂standardGaussian κ)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem centroidDirection_norm_le_one (f : (κ → ℝ) → ℝ) : ‖centroidDirection f‖ ≤ 1 := by
  by_cases hb : firstMomentVector f=0
  · simp [centroidDirection,hb]
  · have hn : ‖firstMomentVector f‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    simp [centroidDirection,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),hn]

theorem centroidDirection_inner (f : (κ → ℝ) → ℝ) :
    inner ℝ (centroidDirection f) (firstMomentVector f)=‖firstMomentVector f‖ := by
  by_cases hb : firstMomentVector f=0
  · simp [centroidDirection,hb]
  · have hn : ‖firstMomentVector f‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    simp only [centroidDirection,real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp

theorem weighted_linearObservable_integral (f : (κ → ℝ) → ℝ)
    (hf : AEMeasurable f (standardGaussian κ))
    (h01 : ∀ᵐ x ∂standardGaussian κ, 0 ≤ f x ∧ f x ≤ 1) (u : EuclideanSpace ℝ κ) :
    (∫ x, f x*linearObservable u x ∂standardGaussian κ)=inner ℝ u (firstMomentVector f) := by
  have hcoord (j : κ) : Integrable (fun x => x j*f x) (standardGaussian κ) := by
    simpa only [mul_comm] using fractional_mul_integrable (standardGaussian κ) f (fun x => x j)
      hf h01 (gaussian_product_coordinate_integrable (fun _ => 0) (fun _ => 1) j)
  have he : (fun x => f x*linearObservable u x)=
      (fun x => ∑ j, u j*(x j*f x)) := by
    funext x
    simp only [linearObservable,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,integral_finsetSum Finset.univ (fun j _ => (hcoord j).const_mul _),PiLp.inner_apply]
  simp only [integral_const_mul,firstMomentVector,Real.inner_apply]

theorem centroidDirection_weighted_second (f : (κ → ℝ) → ℝ)
    (hf : AEMeasurable f (standardGaussian κ))
    (h01 : ∀ᵐ x ∂standardGaussian κ, 0 ≤ f x ∧ f x ≤ 1) :
    ‖firstMomentVector f‖^2 ≤ (∫ x, f x ∂standardGaussian κ)*
      ∫ x, f x*(linearObservable (centroidDirection f) x)^2 ∂standardGaussian κ := by
  have h := fractional_weighted_cauchy (standardGaussian κ) f
    (linearObservable (centroidDirection f)) hf h01 (linearObservable_memLp _)
  rwa [weighted_linearObservable_integral f hf h01,centroidDirection_inner] at h

theorem rankOne_quadratic_polynomial (u : EuclideanSpace ℝ κ) (x : κ → ℝ) :
    (∑ j, ∑ k, u j*u k*quadraticCoordinate j k x)=(linearObservable u x)^2-‖u‖^2 := by
  simp only [quadraticCoordinate,mul_sub,Finset.sum_sub_distrib]
  rw [EuclideanSpace.real_norm_sq_eq]
  congr 1
  · unfold linearObservable
    rw [sq]
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    simp [mul_ite,pow_two]

theorem rankOne_tensor_sq (p : ℝ) (u : EuclideanSpace ℝ κ) :
    (∑ j, ∑ k, (p*u j*u k)^2)=p^2*(‖u‖^2)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [mul_pow,←Finset.mul_sum,←Finset.sum_mul]
  ring

/-- The actual rank-one quadratic test is expressed as its weighted directional
second moment, including the centered Gaussian correction. -/
theorem rankOne_quadratic_pairing (f : (κ → ℝ) → ℝ)
    (hf : AEMeasurable f (standardGaussian κ))
    (h01 : ∀ᵐ x ∂standardGaussian κ, 0 ≤ f x ∧ f x ≤ 1)
    (p : ℝ) (u : EuclideanSpace ℝ κ) :
    (∑ j, ∑ k, (p*u j*u k)*quadraticMoment f j k)=
      p*((∫ x, f x*(linearObservable u x)^2 ∂standardGaussian κ)-
        (∫ x, f x ∂standardGaussian κ)*‖u‖^2) := by
  have hf2 : MemLp f 2 (standardGaussian κ) := by
    apply MemLp.of_bound hf.aestronglyMeasurable 1
    filter_upwards [h01] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have ht (j k : κ) : Integrable (fun x => (p*u j*u k)*(f x*quadraticCoordinate j k x))
      (standardGaussian κ) := (quadratic_moment_integrable hf2 j k).const_mul _
  have hfI := fractional_integrable (standardGaussian κ) f hf h01
  have hu := linearObservable_memLp u
  have hf2I := fractional_mul_integrable (standardGaussian κ) f
    (fun x => (linearObservable u x)^2) hf h01
    (by simpa only [sq,Pi.mul_def] using hu.integrable_mul hu)
  calc
    _ = ∫ x, ∑ j, ∑ k, (p*u j*u k)*(f x*quadraticCoordinate j k x) ∂standardGaussian κ := by
      rw [integral_finsetSum Finset.univ
        (fun j _ => integrable_finsetSum _ (fun k _ => ht j k))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum Finset.univ (fun k _ => ht j k)]
      simp only [integral_const_mul,quadraticMoment]
    _ = ∫ x, p*(f x*(linearObservable u x)^2-f x*‖u‖^2) ∂standardGaussian κ := by
      apply integral_congr_ae
      filter_upwards with x
      calc
        _ = p*f x*(∑ j, ∑ k, u j*u k*quadraticCoordinate j k x) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [rankOne_quadratic_polynomial]; ring
    _ = _ := by rw [integral_const_mul,integral_sub hf2I (hfI.mul_const _),integral_mul_const]


variable {ι : Type*} [Fintype ι]

def assignmentMassSquares (f : (κ → ℝ) → ι → ℝ) : ℝ :=
  ∑ i, (assignmentMass f i)^2

def centroidTestTensor (f : (κ → ℝ) → ι → ℝ) (i : ι) (j k : κ) : ℝ :=
  assignmentMass f i * centroidDirection (fun x => f x i) j *
    centroidDirection (fun x => f x i) k

theorem assignmentMassSquares_pos (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    0 < assignmentMassSquares f := by
  by_contra! h
  have hz (i : ι) : assignmentMass f i=0 := by
    have hs : (assignmentMass f i)^2 ≤ assignmentMassSquares f := by
      unfold assignmentMassSquares
      exact Finset.single_le_sum (fun j _ => sq_nonneg (assignmentMass f j)) (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp (le_antisymm (hs.trans h) (sq_nonneg _))
  have hs := assignmentMass_sum f hf hp
  simp only [hz,Finset.sum_const_zero] at hs
  norm_num at hs

theorem centroid_test_tensor_norm_bound (f : (κ → ℝ) → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, (centroidTestTensor f i j k)^2) ≤ assignmentMassSquares f := by
  apply Finset.sum_le_sum
  intro i _
  change (∑ j, ∑ k, (assignmentMass f i*centroidDirection (fun x => f x i) j*
    centroidDirection (fun x => f x i) k)^2) ≤ (assignmentMass f i)^2
  rw [rankOne_tensor_sq]
  have hunit := centroidDirection_norm_le_one (fun x => f x i)
  have hunit0 := norm_nonneg (centroidDirection (fun x => f x i))
  have hsq : ‖centroidDirection (fun x => f x i)‖^2 ≤ 1 := by nlinarith
  have hsq2 : (‖centroidDirection (fun x => f x i)‖^2)^2 ≤ 1 := by
    nlinarith [sq_nonneg ‖centroidDirection (fun x => f x i)‖]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq2 (sq_nonneg (assignmentMass f i))

theorem centroid_test_pairing_lower (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    assignmentFirstEnergy f-assignmentMassSquares f ≤
      ∑ i, ∑ j, ∑ k, centroidTestTensor f i j k*quadraticMoment (fun x => f x i) j k := by
  have hcell (i : ι) : ‖firstMomentVector (fun x => f x i)‖^2-(assignmentMass f i)^2 ≤
      ∑ j, ∑ k, centroidTestTensor f i j k*quadraticMoment (fun x => f x i) j k := by
    have hb := fractional_coordinate_bounds f hp i
    have hJ := centroidDirection_weighted_second (fun x => f x i) (hf i) hb
    have hunit : ‖centroidDirection (fun x => f x i)‖^2 ≤ 1 := by
      have h := centroidDirection_norm_le_one (fun x => f x i)
      nlinarith [norm_nonneg (centroidDirection (fun x => f x i))]
    have hscale := mul_le_mul_of_nonneg_left hunit (sq_nonneg (assignmentMass f i))
    unfold centroidTestTensor
    rw [rankOne_quadratic_pairing (fun x => f x i) (hf i) hb]
    change ‖firstMomentVector (fun x => f x i)‖^2 ≤ assignmentMass f i*
      (∫ x, f x i*(linearObservable (centroidDirection (fun x => f x i)) x)^2 ∂standardGaussian κ) at hJ
    change ‖firstMomentVector (fun x => f x i)‖^2-(assignmentMass f i)^2 ≤
      assignmentMass f i*((∫ x, f x i*(linearObservable (centroidDirection (fun x => f x i)) x)^2
        ∂standardGaussian κ)-assignmentMass f i*‖centroidDirection (fun x => f x i)‖^2)
    nlinarith
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcell i)
  simpa only [Finset.sum_sub_distrib,firstMomentVector_norm_sq,assignmentFirstEnergy,assignmentMassSquares] using h

/-- A genuine second-chaos lower bound for all fractional assignments. The
positive part handles W <= P, and centroid normalization handles zero rows. -/
theorem secondChaos_positive_part_mul (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    (max (assignmentFirstEnergy f-assignmentMassSquares f) 0)^2 ≤
      2*chaosEnergy f 2*assignmentMassSquares f := by
  letI : LinearOrder κ := LinearOrder.lift' (Fintype.equivFin κ) (Fintype.equivFin κ).injective
  letI : DecidableEq κ := Classical.decEq κ
  have hA := chaosEnergy_nonneg f 2
  have hP := assignmentMassSquares_pos f hf hp
  have hCS := (quadratic_moment_tensor_cauchy f (centroidTestTensor f)).trans
    (mul_le_mul_of_nonneg_left (centroid_test_tensor_norm_bound f) (by positivity))
  have hL := centroid_test_pairing_lower f hf hp
  by_cases hW : assignmentFirstEnergy f-assignmentMassSquares f ≤ 0
  · rw [max_eq_right hW,zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hz : 0 ≤ assignmentFirstEnergy f-assignmentMassSquares f := (lt_of_not_ge hW).le
    rw [max_eq_left hz]
    have hs : 0 ≤ ∑ i, ∑ j, ∑ k,
        centroidTestTensor f i j k*quadraticMoment (fun x => f x i) j k := hz.trans hL
    exact ((sq_le_sq₀ hz hs).2 hL).trans hCS

theorem secondChaos_positive_part_lower (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x)) :
    (max (assignmentFirstEnergy f-assignmentMassSquares f) 0)^2/
      (2*assignmentMassSquares f) ≤ chaosEnergy f 2 := by
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) (assignmentMassSquares_pos f hf hp))).2
  nlinarith [secondChaos_positive_part_mul f hf hp]

/-- Every supporting affine tangent of the positive-part perspective is valid
globally, including cells with zero mass and competitors with W <= P. -/
theorem secondChaos_affine_tangent (f : (κ → ℝ) → ι → ℝ)
    (hf : ∀ i, AEMeasurable (fun x => f x i) (standardGaussian κ))
    (hp : ∀ᵐ x ∂standardGaussian κ, SimplexWeights (f x))
    (ell : ℝ) (hell : 0 ≤ ell) :
    ell*assignmentFirstEnergy f-ell*(ell+2)/2*assignmentMassSquares f ≤ chaosEnergy f 2 := by
  let z := max (assignmentFirstEnergy f-assignmentMassSquares f) 0
  have hP := assignmentMassSquares_pos f hf hp
  have hz : assignmentFirstEnergy f-assignmentMassSquares f ≤ z := le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hz hell
  have hbound := secondChaos_positive_part_mul f hf hp
  change z^2 ≤ 2*chaosEnergy f 2*assignmentMassSquares f at hbound
  have hpoly := sq_nonneg (z-ell*assignmentMassSquares f)
  have ht : 2*assignmentMassSquares f*
      (ell*assignmentFirstEnergy f-ell*(ell+2)/2*assignmentMassSquares f) ≤
      2*assignmentMassSquares f*chaosEnergy f 2 := by
    have h := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ 2*assignmentMassSquares f)
    nlinarith
  exact (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ)<2) hP)).mp
    (by simpa only [mul_comm] using ht)

end NegativeVotingSecondChaosLower
