import GaussianBoundaryTraceAggregation
import GaussianOUResidualMoment
import GaussianConditionalSecondMoment

/-! Actual high-chaos Gaussian boundary restriction. Composition is transported
on each normal slice using its all-normal-parameters theorem; ambient AE equality
is never restricted to a measure-zero hyperplane. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open NegativeVotingHypercontractivity NegativeVotingSmoothingComposition
open NegativeVotingDisintegration NegativeVotingNormalTrace
open NegativeVotingPolynomialFacetGeometricTrace NegativeVotingActualFacetOUTrace
open NegativeVotingChaosDecay OAI.MinUncut.GaussianHermite
open scoped ENNReal BigOperators

namespace NegativeVotingBoundaryHighChaosTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {n : ℕ}

theorem reconstruct_measurePreserving (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (reconstructLinear w e) (γFin (n+1)) (stdGaussian E) := by
  refine ⟨?_,reconstructLinear_map w hw e⟩
  change Measurable (fun x => coordinateReconstruct w e (normalCoordinates x))
  unfold coordinateReconstruct
  fun_prop

/-- Exact intertwining in a finite normal/tangent coordinate system. -/
theorem ambientAverage_reconstruct (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : ℝ) (f : E → ℝ) (hfM : Measurable f) (x : Fin (n+1) → ℝ) :
    ambientAverage ρ f (reconstructLinear w e x) =
      gaussianAverage ρ (fun y => f (reconstructLinear w e y)) x := by
  change ambientAverage ρ f (coordinateReconstruct w e (normalCoordinates x)) = _
  rw [ambientAverage_coordinateReconstruct w hw e ρ f hfM]
  have h := gaussianAverage_normalCoordinates ρ (fun y => f (reconstructLinear w e y))
    (normalCoordinates x)
  rw [normalCoordinates.symm_apply_apply] at h
  have hl : normalLift (fun y => f (reconstructLinear w e y)) =
      fun z => f (coordinateReconstruct w e z) := by
    funext z
    simp only [normalLift, Function.comp_apply, reconstructLinear_apply,
      normalCoordinates.apply_symm_apply]
  rw [hl] at h
  exact h.symm

/-- Semigroup composition is valid on every fixed affine plane, with respect
to its own Gaussian measure. This is stronger than ambient AE composition. -/
theorem ambientAverage_comp_on_plane_ae (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {τ σ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (f : E → ℝ) (hfM : Measurable f) (hf : MemLp f 2 (stdGaussian E)) (a : ℝ) :
    ∀ᵐ (y : tangentSpace w) ∂stdGaussian (tangentSpace w),
      ambientAverage τ (ambientAverage σ f) ((y:E)+a • w) =
        ambientAverage (τ*σ) f ((y:E)+a • w) := by
  let g := fun x => f (reconstructLinear w e x)
  have hgm : MemLp g 2 (γFin (n+1)) := hf.comp_measurePreserving (reconstruct_measurePreserving w hw e)
  have hinner : (fun x => ambientAverage σ f (reconstructLinear w e x)) = gaussianAverage σ g := by
    funext x
    exact ambientAverage_reconstruct w hw e σ f hfM x
  have hprod1 : τ*σ < 1 := (mul_lt_mul_of_pos_left hσ1 hτ).trans (by simpa using hτ1)
  have hτsq : τ^2 < 1 := by nlinarith
  have hprodsq : (τ*σ)^2 < 1 := by nlinarith [mul_pos hτ hσ]
  have hgm' := gaussianAverage_memLp_two hσ hσ1 g hgm
  have hfinite : ∀ᵐ y ∂γFin n,
      ambientAverage τ (ambientAverage σ f) ((tangentCoordinatesInverse w e y:E)+a • w) =
        ambientAverage (τ*σ) f ((tangentCoordinatesInverse w e y:E)+a • w) := by
    filter_upwards [normalTrace_smoothing_comp_ae_all_parameters hτ hτ1 hσ hσ1 g hgm,
      normalTrace_normalCoordinates_ae_all_parameters hτsq (gaussianAverage σ g) hgm',
      normalTrace_normalCoordinates_ae_all_parameters hprodsq g hgm] with y hc hl hr
    have hcoord : reconstructLinear w e (normalCoordinates.symm (y,a)) =
        (tangentCoordinatesInverse w e y:E)+a • w := by
      simp only [reconstructLinear_apply,normalCoordinates.apply_symm_apply]
      rfl
    rw [←hcoord, ambientAverage_reconstruct w hw e τ (ambientAverage σ f)
      (ambientAverage_measurable σ f hfM),hinner,
      ambientAverage_reconstruct w hw e (τ*σ) f hfM]
    exact (hl a).symm.trans ((hc a).trans (hr a))
  rw [←tangentCoordinatesInverse_map w e]
  apply (ae_map_iff (show AEMeasurable (tangentCoordinatesInverse w e) (γFin n) from by
    apply Measurable.aemeasurable
    unfold tangentCoordinatesInverse
    fun_prop) ?_).mpr hfinite
  apply measurableSet_eq_fun
  · exact (ambientAverage_measurable τ (ambientAverage σ f)
      (ambientAverage_measurable σ f hfM)).comp (by fun_prop)
  · exact (ambientAverage_measurable (τ*σ) f hfM).comp (by fun_prop)

theorem ambientAverage_euclidean_memLp_and_decay {d : ℕ} {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (f : FSC.Coord d → ℝ)
    (hfM : Measurable f) (hf : MemLp f 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ b, degree b < k →
      coeff (fun x : Fin d → ℝ => f (WithLp.toLp 2 x)) b = 0) :
    MemLp (ambientAverage σ f) 2 (stdGaussian (FSC.Coord d)) ∧
    (∫ x,(ambientAverage σ f x)^2 ∂stdGaussian (FSC.Coord d)) ≤
      (σ^2)^k * ∫ x,(f x)^2 ∂stdGaussian (FSC.Coord d) := by
  let T := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hT := NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d
  have hf' : MemLp (f ∘ T) 2 (γFin d) := hf.comp_measurePreserving hT
  have he : (ambientAverage σ f) ∘ T = gaussianAverage σ (f ∘ T) := by
    funext x
    exact ambientAverage_eq_gaussianAverage σ f (T x)
  have hmem := gaussianAverage_memLp_two hσ hσ1 (f ∘ T) hf'
  have hmem' : MemLp (ambientAverage σ f) 2 (stdGaussian (FSC.Coord d)) := by
    rw [←hT.map_eq]
    apply (memLp_map_measure_iff
      ((ambientAverage_measurable σ f hfM).aestronglyMeasurable) hT.aemeasurable).mpr
    rwa [he]
  refine ⟨hmem',?_⟩
  have h := gaussianAverage_integral_sq_decay σ hσ hσ1 (f ∘ T) hf' k hvanish
  have hi : (∫ x,(gaussianAverage σ (f ∘ T) x)^2 ∂γFin d) =
      ∫ x,(ambientAverage σ f x)^2 ∂stdGaussian (FSC.Coord d) := by
    rw [←he]
    exact hT.integral_comp' (fun x => (ambientAverage σ f x)^2)
  have hfint : (∫ x,((f ∘ T) x)^2 ∂γFin d) =
      ∫ x,(f x)^2 ∂stdGaussian (FSC.Coord d) :=
    hT.integral_comp' (fun x => (f x)^2)
  rwa [hi,hfint] at h

/-- High-degree gain for the literal Gaussian noise evaluated on an actual
affine plane. Coefficient vanishing is in the original Euclidean coordinates. -/
theorem plane_surface_highChaos_square_le {d n : ℕ}
    (w : FSC.Coord d) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (τ σ q a : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1))
    (F : Set (tangentSpace w)) (hF : MeasurableSet F)
    (f : FSC.Coord d → ℝ) (hfM : Measurable f)
    (hf : MemLp f 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ b, degree b < k →
      coeff (fun x : Fin d → ℝ => f (WithLp.toLp 2 x)) b=0) :
    gaussianPDFReal 0 1 a *
      (∫ y in F,(ambientAverage (τ*σ) f ((y:FSC.Coord d)+a • w))^2
        ∂stdGaussian (tangentSpace w)) ≤
      2*(gaussianPDFReal 0 1 a*(stdGaussian (tangentSpace w) F).toReal)^(1-1/q)*
        (σ^2)^k * ∫ x,(f x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hτsq : τ^2 < 1 := by
    rw [ht]
    apply (div_lt_one (by linarith : 0<2*q-1)).mpr
    linarith
  have hτ1 : τ<1 := by nlinarith
  have hdec := ambientAverage_euclidean_memLp_and_decay hσ hσ1 f hfM hf k hvanish
  have h := plane_surface_square_le w hw e τ q a hτ hq ht F hF
    (ambientAverage σ f) (ambientAverage_measurable σ f hfM) hdec.1
  have he := ambientAverage_comp_on_plane_ae w hw e hτ hτ1 hσ hσ1 f hfM hf a
  have hi := integral_congr_ae (μ := (stdGaussian (tangentSpace w)).restrict F)
    ((ae_restrict_of_ae he).mono (fun y hy => congrArg (fun z : ℝ => z^2) hy))
  rw [hi] at h
  have hmass : 0 ≤ gaussianPDFReal 0 1 a*(stdGaussian (tangentSpace w) F).toReal :=
    mul_nonneg (gaussianPDFReal_nonneg _ _ _) ENNReal.toReal_nonneg
  have hh := mul_le_mul_of_nonneg_left hdec.2
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hmass (1-1/q)))
  exact h.trans (by nlinarith only [hh])

open NegativeVotingBoundaryTraceAggregation

/-- Full ordered-edge trace with the genuine high-degree gain. In the
paper's notation s=τ σ and Λ=τ⁻², so (σ²)^k=(s²Λ)^k. -/
theorem ambient_ordered_highChaos_trace_energy_le {d : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ι → ℕ}
    (w : ι → ι → FSC.Coord d) (a ell : ι → ι → ℝ)
    (F : ∀ i j, Set (tangentSpace (w i j)))
    (e : ∀ i j, i≠j → tangentSpace (w i j) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i j)))
    (τ σ q ell0 G : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1)) (hell0 : 0 < ell0) (hG : 0 ≤ G)
    (hw : ∀ i j, i≠j → ‖w i j‖=1)
    (hF : ∀ i j, i≠j → MeasurableSet (F i j))
    (hell : ∀ i j, i≠j → ell0 ≤ ell i j)
    (hμsym : ∀ i j, planeSurfaceMass w a F i j=planeSurfaceMass w a F j i)
    (hellsym : ∀ i j, ell i j=ell j i)
    (hdegree : ∀ i, (∑ j ∈ Finset.univ.erase i, planeSurfaceMass w a F i j/ell i j) ≤ G)
    (f : ι → FSC.Coord d → ℝ) (hfM : ∀ i, Measurable (f i))
    (hf : ∀ i, MemLp (f i) 2 (stdGaussian (FSC.Coord d)))
    (k : ℕ) (hvanish : ∀ i b, degree b < k →
      coeff (fun x : Fin d → ℝ => f i (WithLp.toLp 2 x)) b=0) :
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      gaussianPDFReal 0 1 (a i j)/ell i j *
        ∫ y in F i j, (ambientAverage (τ*σ) (fun x => f i x-f j x)
          ((y:FSC.Coord d)+(a i j) • w i j))^2 ∂stdGaussian (tangentSpace (w i j))) ≤
      8*traceCoefficient (ι := ι) ell0 G q*(σ^2)^k *
        ∑ i, ∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d) := by
  let energy := fun i => ∫ x,(f i x)^2 ∂stdGaussian (FSC.Coord d)
  let T := fun i j => gaussianPDFReal 0 1 (a i j) *
    ∫ y in F i j, (ambientAverage (τ*σ) (fun x => f i x-f j x)
      ((y:FSC.Coord d)+(a i j) • w i j))^2 ∂stdGaussian (tangentSpace (w i j))
  have henergy i : 0 ≤ energy i := integral_nonneg (fun _ => sq_nonneg _)
  have hμ i j (_hij : i≠j) : 0 ≤ planeSurfaceMass w a F i j :=
    mul_nonneg (gaussianPDFReal_nonneg _ _ _) ENNReal.toReal_nonneg
  have hdiff i j : (∫ x,(f i x-f j x)^2 ∂stdGaussian (FSC.Coord d)) ≤
      2*(energy i+energy j) := by
    have h := integral_mono ((hf i).sub (hf j)).integrable_sq
      (((hf i).integrable_sq.add (hf j).integrable_sq).const_mul 2)
      (fun x => by
        simp only [Pi.sub_apply,Pi.add_apply]
        nlinarith [sq_nonneg (f i x+f j x)])
    simp only [Pi.sub_apply,Pi.add_apply] at h
    rw [integral_const_mul,integral_add (hf i).integrable_sq (hf j).integrable_sq] at h
    exact h
  have hfFin i : MemLp (fun x : Fin d → ℝ => f i (WithLp.toLp 2 x)) 2 (γFin d) :=
    (hf i).comp_measurePreserving
      (NegativeVotingConditionalSecondMoment.gaussian_toLp_measurePreserving d)
  have htrace i j (hij : i≠j) : T i j ≤
      (4*(σ^2)^k)*(planeSurfaceMass w a F i j)^(1-1/q)*(energy i+energy j) := by
    have hlow b (hb : degree b<k) :
        coeff (fun x : Fin d → ℝ => f i (WithLp.toLp 2 x)-f j (WithLp.toLp 2 x)) b=0 := by
      rw [NegativeVotingAffine.coeff_sub (hfFin i) (hfFin j),
        hvanish i b hb,hvanish j b hb,sub_self]
    have h := plane_surface_highChaos_square_le (w i j) (hw i j hij) (e i j hij)
      τ σ q (a i j) hτ hσ hσ1 hq ht (F i j) (hF i j hij) (fun x => f i x-f j x)
      ((hfM i).sub (hfM j)) ((hf i).sub (hf j)) k hlow
    change T i j ≤ 2*(planeSurfaceMass w a F i j)^(1-1/q)*(σ^2)^k*
      ∫ x,(f i x-f j x)^2 ∂stdGaussian (FSC.Coord d) at h
    have hh := mul_le_mul_of_nonneg_left (hdiff i j)
      (show 0 ≤ 2*(planeSurfaceMass w a F i j)^(1-1/q)*(σ^2)^k from
        mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (hμ i j hij) _))
          (pow_nonneg (sq_nonneg σ) k))
    exact h.trans (by nlinarith only [hh])
  have h := ordered_trace_energy_le T (planeSurfaceMass w a F) ell energy ell0 G q (4*(σ^2)^k)
    hell0 hG (by linarith) (by positivity) henergy hμ hell hμsym hellsym hdegree htrace
  convert h using 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold T
    ring
  · unfold energy
    ring

end NegativeVotingBoundaryHighChaosTrace
