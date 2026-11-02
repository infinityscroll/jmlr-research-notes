import GaussianStructuredSwitchingMoments
import GaussianPathSmoothedComparison
import GaussianCellOUContinuity

/-!
Actual common-smoothed inputs for the structured switching residual.
The cell input is a literal selected-cell difference; its fully discharged
quantitative endpoint below concerns uniform selected masses. Extending the
path bound to nonuniform near-balanced masses remains a separate obligation.
-/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set
open scoped BigOperators ENNReal RealInnerProductSpace Classical
namespace NegativeVotingStructuredResidualInputs
open NegativeVotingFan NegativeVotingDisintegration NegativeVotingActualFacetOUTrace
  NegativeVotingBoundaryHighChaosTrace NegativeVotingPathSmoothedComparison
  NegativeVotingHypercontractivity NegativeVotingProjection NegativeVotingRareLabelHighChaos
  NegativeVotingOUResidualMoment NegativeVotingSmoothingComposition NegativeVotingCellOUContinuity
  NegativeVotingNormalTrace NegativeVotingChaosDecay NegativeVotingStructuredSwitchingMoments
  NegativeVotingBoundedOUCellTests NegativeVotingConditionalSecondMoment
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingNearRegularBalancedGeometry
  NegativeVotingFanScore NegativeVotingFacetDegree NegativeVotingFanJacobian
  NegativeVotingQuadraticMomentPadding NegativeVotingCapTail
  NegativeVotingFanSelectedOffsets NegativeVotingPolynomialFacetLogBound
  NegativeVotingAffine
  OAI.MinUncut.GaussianHermite
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem gaussianAverage_highModes_comp_ae (τ ν : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hν : |ν| ≤ 1)
    (k : ℕ) (f : (Fin d → ℝ) → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (γFin d)) :
    gaussianAverage τ (gaussianAverage ν (highModes k f)) =ᵐ[γFin d]
      gaussianAverage (τ*ν) (highModes k f) := by
  have hτa : |τ| ≤ 1 := by rw [abs_of_pos hτ]; exact hτ1.le
  have hp : |τ*ν| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hτa hν (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hpm := highModes_measurable k f hfm
  have hpf := highModes_memLp k f hf
  have hn := gaussianAverage_memLp_signed ν hν _ hpm hpf
  have hnm := gaussianAverage_measurable ν _ hpm
  apply ae_eq_of_coeff_eq _ _ (gaussianAverage_memLp_signed τ hτa _ hnm hn)
    (gaussianAverage_memLp_signed (τ*ν) hp _ hpm hpf)
  intro b
  rw [gaussianAverage_coefficient τ hτa _ hnm hn,
    gaussianAverage_coefficient ν hν _ hpm hpf,
    gaussianAverage_coefficient (τ*ν) hp _ hpm hpf,mul_pow]
  ring

theorem gaussianAverage_sub_bounded (ρ : ℝ) (f g : (Fin d → ℝ) → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (M N : ℝ)
    (hf : ∀ x, |f x| ≤ M) (hg : ∀ x, |g x| ≤ N) :
    gaussianAverage ρ (f-g)=gaussianAverage ρ f-gaussianAverage ρ g := by
  funext x
  apply integral_sub
  · apply Integrable.of_bound (hfm.comp (by fun_prop)).aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs,Function.comp_def] using hf _
  · apply Integrable.of_bound (hgm.comp (by fun_prop)).aestronglyMeasurable N
    exact Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs,Function.comp_def] using hg _

def coordinateCellDifference (p₀ p₁ : Parameters d ι) (i : ι) : (Fin d → ℝ) → ℝ :=
  fun x => cellDifference p₀ p₁ i (WithLp.toLp 2 x)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem coordinateCellDifference_eq (p₀ p₁ : Parameters d ι) (i : ι) :
    coordinateCellDifference p₀ p₁ i=cellWeight p₁.1 p₁.2 i-cellWeight p₀.1 p₀.2 i := rfl

omit [DecidableEq ι] in
theorem coordinateCellDifference_measurable (p₀ p₁ : Parameters d ι) (i : ι) :
    Measurable (coordinateCellDifference p₀ p₁ i) :=
  (cellDifference_measurable p₀ p₁ i).comp (by fun_prop)

omit [DecidableEq ι] in
theorem coordinateCellDifference_memLp (p₀ p₁ : Parameters d ι) (i : ι) :
    MemLp (coordinateCellDifference p₀ p₁ i) 2 (γFin d) :=
  (cellDifference_memLp p₀ p₁ i).comp_measurePreserving (gaussian_toLp_measurePreserving d)

theorem coordinateCellDifference_abs_le (p₀ p₁ : Parameters d ι) (i : ι) (x : Fin d → ℝ) :
    |coordinateCellDifference p₀ p₁ i x| ≤ 2 := by
  exact (abs_sub _ _).trans (by simpa only [cellWeight,one_add_one_eq_two] using
    (add_le_add (cellWeight_abs_le p₁.1 p₁.2 i x) (cellWeight_abs_le p₀.1 p₀.2 i x)))

theorem gaussianAverage_cellDifference_continuous (p₀ p₁ : Parameters d ι)
    (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (h₀ : CenteredSingularLowerBound p₀.1 s₀) (h₁ : CenteredSingularLowerBound p₁.1 s₁)
    (i : ι) (ρ : ℝ) (hρ : |ρ| < 1) :
    Continuous (gaussianAverage ρ (coordinateCellDifference p₀ p₁ i)) := by
  rw [coordinateCellDifference_eq,gaussianAverage_sub_bounded ρ _ _
    (cellWeight_measurable p₁.1 p₁.2 i) (cellWeight_measurable p₀.1 p₀.2 i)
    1 1 (cellWeight_abs_le p₁.1 p₁.2 i) (cellWeight_abs_le p₀.1 p₀.2 i)]
  exact (gaussianAverage_cellWeight_continuous p₁.1 s₁ hs₁ h₁ p₁.2 i ρ hρ).sub
    (gaussianAverage_cellWeight_continuous p₀.1 s₀ hs₀ h₀ p₀.2 i ρ hρ)

/-- Cell-difference composition is pointwise, hence can subsequently be used
on every comparison plane without restricting an ambient AE identity. -/
theorem cellDifference_highModes_comp (p₀ p₁ : Parameters d ι)
    (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (h₀ : CenteredSingularLowerBound p₀.1 s₀) (h₁ : CenteredSingularLowerBound p₁.1 s₁)
    (i : ι) (τ ν : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hν : |ν| < 1)
    (k : ℕ) (hk : k ≤ 3) :
    gaussianAverage τ (gaussianAverage ν (highModes k (coordinateCellDifference p₀ p₁ i)))=
      gaussianAverage (τ*ν) (highModes k (coordinateCellDifference p₀ p₁ i)) := by
  let f := coordinateCellDifference p₀ p₁ i
  have hfm := coordinateCellDifference_measurable p₀ p₁ i
  have hf := coordinateCellDifference_memLp p₀ p₁ i
  have hp : |τ*ν| < 1 := by
    rw [abs_mul,abs_of_pos hτ]
    calc
      _ ≤ τ*1 := mul_le_mul_of_nonneg_left hν.le hτ.le
      _ < 1 := by simpa using hτ1
  have hcν := gaussianAverage_cellDifference_continuous p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i ν hν
  obtain ⟨hc, C,hC,hbound⟩ := highModes_continuous_quadratic_of_average ν hν.le k hk
    f hfm hcν 2 (by norm_num) (coordinateCellDifference_abs_le p₀ p₁ i)
  have hl := gaussianAverage_continuous_quadratic τ _ hc C hC hbound
  have hr' := highModes_continuous_quadratic_of_average (τ*ν) hp.le k hk f hfm
    (gaussianAverage_cellDifference_continuous p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i (τ*ν) hp)
    2 (by norm_num) (coordinateCellDifference_abs_le p₀ p₁ i)
  have hr : Continuous (gaussianAverage (τ*ν) (highModes k f)) :=
    hr'.1.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  let : (gaussianReal 0 1).IsOpenPosMeasure := GaussianFin.instIsOpenPosMeasureγ
  let : (γFin d).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure (fun _ : Fin d => gaussianReal 0 1)
  exact (Continuous.ae_eq_iff_eq (γFin d) hl hr).mp
    (gaussianAverage_highModes_comp_ae τ ν hτ hτ1 hν.le k f hfm hf)

/-- Literal common-smoothed cell source, at r=(τχ)². -/
def cellSource (τ χ : ℝ) (p₀ p₁ : Parameters d ι) (i : ι) : FSC.Coord d → ℝ :=
  smoothedHighModes (-(τ*χ^2)) 2 (cellDifference p₀ p₁ i)

/-- Literal common-smoothed high-degree source. -/
def highSource (χ : ℝ) (u : FSC.Coord d → ℝ) : FSC.Coord d → ℝ := ambientAverage χ u

omit [DecidableEq ι] in
theorem cellSource_measurable (τ χ : ℝ) (p₀ p₁ : Parameters d ι) (i : ι) :
    Measurable (cellSource τ χ p₀ p₁ i) :=
  ambientAverage_measurable _ _ (ambientHighModes_measurable 2 _ (cellDifference_measurable p₀ p₁ i))

omit [DecidableEq ι] in
theorem cellSource_memLp (τ χ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hχ : 0 < χ) (hχ1 : χ < 1) (p₀ p₁ : Parameters d ι) (i : ι) :
    MemLp (cellSource τ χ p₀ p₁ i) 2 (stdGaussian (FSC.Coord d)) := by
  apply smoothedHighModes_memLp _ _ 2 _ (cellDifference_measurable p₀ p₁ i)
    (cellDifference_memLp p₀ p₁ i)
  rw [abs_neg,abs_of_nonneg (by positivity)]
  nlinarith

theorem cellSource_factorization (p₀ p₁ : Parameters d ι)
    (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (h₀ : CenteredSingularLowerBound p₀.1 s₀) (h₁ : CenteredSingularLowerBound p₁.1 s₁)
    (i : ι) (τ χ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hχ : 0 < χ) (hχ1 : χ < 1) :
    ambientAverage τ (cellSource τ χ p₀ p₁ i)=
      smoothedHighModes (-((τ*χ)^2)) 2 (cellDifference p₀ p₁ i) := by
  have hν : |-(τ*χ^2)| < 1 := by
    rw [abs_neg,abs_of_nonneg (by positivity)]
    nlinarith
  have hh := cellDifference_highModes_comp p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i τ (-(τ*χ^2))
    hτ hτ1 hν 2 (by norm_num)
  have he : τ*(-(τ*χ^2))=-((τ*χ)^2) := by ring
  rw [he] at hh
  funext x
  rw [ambientAverage_eq_gaussianAverage]
  have hi : (fun y : Fin d → ℝ => cellSource τ χ p₀ p₁ i (WithLp.toLp 2 y)) =
      gaussianAverage (-(τ*χ^2)) (highModes 2 (coordinateCellDifference p₀ p₁ i)) := by
    funext y
    exact ambientAverage_eq_gaussianAverage _ _ (WithLp.toLp 2 y)
  rw [hi,hh]
  exact (ambientAverage_eq_gaussianAverage (-((τ*χ)^2))
    (ambientHighModes 2 (cellDifference p₀ p₁ i)) x).symm

theorem realLp_two_sq_eq_integral {f : FSC.Coord d → ℝ}
    (hf : MemLp f 2 (stdGaussian (FSC.Coord d))) :
    (realLp (stdGaussian (FSC.Coord d)) 2 f)^2=∫ x,(f x)^2 ∂stdGaussian (FSC.Coord d) := by
  rw [realLp,eLpNorm_two_eq_sqrt_integral_sq hf,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

theorem smoothedHighModes_neg_integral_sq (ρ : ℝ) (k : ℕ) (f : FSC.Coord d → ℝ) :
    (∫ x,(smoothedHighModes (-ρ) k f x)^2 ∂stdGaussian (FSC.Coord d))=
      ∫ x,(smoothedHighModes ρ k f x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hT := gaussian_toLp_measurePreserving d
  rw [← hT.integral_comp' (fun x => (smoothedHighModes (-ρ) k f x)^2),
    ← hT.integral_comp' (fun x => (smoothedHighModes ρ k f x)^2)]
  have he (s : ℝ) : (fun x : Fin d → ℝ => smoothedHighModes s k f (WithLp.toLp 2 x))=
      gaussianAverage s (highModes k (fun y => f (WithLp.toLp 2 y))) := by
    funext x
    exact ambientAverage_eq_gaussianAverage s (ambientHighModes k f) (WithLp.toLp 2 x)
  change (∫ x,((fun y : Fin d → ℝ => smoothedHighModes (-ρ) k f (WithLp.toLp 2 y)) x)^2 ∂γFin d)=_
  rw [he (-ρ)]
  change _=∫ x,((fun y : Fin d → ℝ => smoothedHighModes ρ k f (WithLp.toLp 2 y)) x)^2 ∂γFin d
  rw [he ρ,gaussianAverage_neg]
  simpa only [Function.comp_def] using
    (gaussian_neg_measurePreserving d).integral_comp
      (Homeomorph.neg (Fin d → ℝ)).measurableEmbedding
      (fun x => (gaussianAverage ρ (highModes k (fun y => f (WithLp.toLp 2 y))) x)^2)

/-- The cell-source amplitude is derived from the actual selected balanced
path theorem, not supplied as an L2 estimate. -/
theorem selected_balanced_cellSource_sum_norm_sq_le {m : ℕ} [NeZero m]
    (hm : 3 ≤ m) (R D : Fin m → FSC.Coord d)
    (hGram : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (α : ℝ) (hα : 0 < α) (hD : ∑ i,‖D i‖^2 ≤ α^2/256)
    (e : ℝ) (he : 0 < e) (hscale : e*Real.sqrt (1+Real.log (m:ℝ))/(m:ℝ) ≤ α/2)
    (τ χ q : ℝ) (hτ : 0 < τ) (hχ : 0 < χ) (hχ1 : χ < 1)
    (hq : 2 ≤ q) (ht : τ^2=1/(2*q-1)) (hqlog : Real.log ((m:ℝ)/(α/2)) ≤ q) :
    (∑ i,(realLp (stdGaussian (FSC.Coord d)) 2
      (cellSource τ χ
        (α•R,selectedOffsets (α•R) (fun _ => (m:ℝ)⁻¹))
        (α•R+D,selectedOffsets (α•R+D) (fun _ => (m:ℝ)⁻¹)) i))^2) ≤
      32*Real.exp 1*max 1 (32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)*
        (32*(Real.sqrt 2+(Real.sqrt (2*Real.pi))⁻¹)/e)*quarticLogConstant 2*
          (1+Real.log (m:ℝ))^4*χ^8*∑ i,‖D i‖^2 := by
  have hτ1 : τ < 1 := by
    have : 1/(2*q-1) < 1 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
    nlinarith
  have hχsq : χ^2 < 1 := by nlinarith
  have hh := near_regular_selected_smoothed_difference_l2_sq_le hm R D hGram α hα hD e he hscale
    τ (χ^2) q hτ (sq_pos_of_pos hχ) hχsq hq ht hqlog 2 (by norm_num)
  simp_rw [realLp_two_sq_eq_integral (cellSource_memLp τ χ hτ hτ1 hχ hχ1 _ _ _)]
  unfold cellSource
  calc
    _ = ∑ i,∫ x,(smoothedHighModes (τ*χ^2) 2
        (cellDifference (α•R,selectedOffsets (α•R) (fun _ => (m:ℝ)⁻¹))
          (α•R+D,selectedOffsets (α•R+D) (fun _ => (m:ℝ)⁻¹)) i) x)^2
          ∂stdGaussian (FSC.Coord d) := by
      apply Finset.sum_congr rfl
      intro i _
      exact smoothedHighModes_neg_integral_sq _ _ _
    _ ≤ _ := by
      convert hh using 1
      ring

omit [DecidableEq ι] [Nonempty ι] in
/-- The high-degree source has a true cubic decay, with labelwise squared
norms summed after the scalar contraction. No reverse Minkowski step occurs. -/
theorem highSource_sum_norm_sq_le (χ : ℝ) (hχ : 0 < χ) (hχ1 : χ < 1)
    (u : ι → FSC.Coord d → ℝ) (huM : ∀ i, Measurable (u i))
    (hu : ∀ i, MemLp (u i) 2 (stdGaussian (FSC.Coord d)))
    (hu3 : ∀ i b, degree b < 3 → coeff (fun x : Fin d → ℝ => u i (WithLp.toLp 2 x)) b=0) :
    (∀ i, MemLp (highSource χ (u i)) 2 (stdGaussian (FSC.Coord d))) ∧
    (∑ i,(realLp (stdGaussian (FSC.Coord d)) 2 (highSource χ (u i)))^2) ≤
      χ^6*∑ i,(realLp (stdGaussian (FSC.Coord d)) 2 (u i))^2 := by
  have hh i := ambientAverage_euclidean_memLp_and_decay hχ hχ1 (u i) (huM i) (hu i) 3 (hu3 i)
  refine ⟨fun i => (hh i).1,?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  unfold highSource
  rw [realLp_two_sq_eq_integral (hh i).1,realLp_two_sq_eq_integral (hu i)]
  convert (hh i).2 using 1
  ring

/-- Positive OU composition on one full-measure tangent set for EVERY normal
parameter. In particular the subsequent unit tube is covered by the same set. -/
theorem ambientAverage_comp_on_plane_all_parameters (w : FSC.Coord d) (hw : ‖w‖=1)
    {n : ℕ} (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (τ χ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hχ : 0 < χ) (hχ1 : χ < 1)
    (u : FSC.Coord d → ℝ) (huM : Measurable u) (hu : MemLp u 2 (stdGaussian (FSC.Coord d))) :
    ∀ᵐ y : tangentSpace w ∂stdGaussian (tangentSpace w), ∀ a : ℝ,
      ambientAverage τ (highSource χ u) ((y:FSC.Coord d)+a•w)=
        ambientAverage (τ*χ) u ((y:FSC.Coord d)+a•w) := by
  let g := fun x => u (reconstructLinear w e x)
  have hgm : MemLp g 2 (γFin (n+1)) := hu.comp_measurePreserving (reconstruct_measurePreserving w hw e)
  have hinner : (fun x => ambientAverage χ u (reconstructLinear w e x))=gaussianAverage χ g := by
    funext x
    exact ambientAverage_reconstruct w hw e χ u huM x
  have hp : τ*χ < 1 := (mul_lt_mul_of_pos_left hχ1 hτ).trans (by simpa using hτ1)
  have ht : τ^2 < 1 := by nlinarith
  have hpsq : (τ*χ)^2 < 1 := by nlinarith [mul_pos hτ hχ]
  have hg' := gaussianAverage_memLp_two hχ hχ1 g hgm
  have hfinite : ∀ᵐ y ∂γFin n,∀ a : ℝ,
      ambientAverage τ (highSource χ u) ((tangentCoordinatesInverse w e y:FSC.Coord d)+a•w)=
        ambientAverage (τ*χ) u ((tangentCoordinatesInverse w e y:FSC.Coord d)+a•w) := by
    filter_upwards [normalTrace_smoothing_comp_ae_all_parameters hτ hτ1 hχ hχ1 g hgm,
      normalTrace_normalCoordinates_ae_all_parameters ht (gaussianAverage χ g) hg',
      normalTrace_normalCoordinates_ae_all_parameters hpsq g hgm] with y hc hl hr
    intro a
    have hcoord : reconstructLinear w e (normalCoordinates.symm (y,a))=
        (tangentCoordinatesInverse w e y:FSC.Coord d)+a•w := by
      simp only [reconstructLinear_apply,normalCoordinates.apply_symm_apply]
      rfl
    change ambientAverage τ (ambientAverage χ u) _=_
    rw [← hcoord,ambientAverage_reconstruct w hw e τ (ambientAverage χ u)
      (ambientAverage_measurable χ u huM),hinner,
      ambientAverage_reconstruct w hw e (τ*χ) u huM]
    exact (hl a).symm.trans ((hc a).trans (hr a))
  let T := NegativeVotingStructuredSwitchingNormal.tangentCoordinateEquiv w e
  have hmap : (γFin n).map T=stdGaussian (tangentSpace w) := tangentCoordinatesInverse_map w e
  rw [← hmap,← MeasurableEquiv.map_ae]
  exact hfinite

/-- The literal odd part; this definition does not truncate the infinite
Hermite expansion. -/
def oddPart (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := (f x-f (-x))/2

theorem oddPart_measurable (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (oddPart f) := (hf.sub (hf.comp measurable_neg)).div_const 2

theorem oddPart_memLp (f : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 (γFin d)) :
    MemLp (oddPart f) 2 (γFin d) := by
  have he : oddPart f=fun x => (1/2)*(f x-f (-x)) := by funext x; unfold oddPart; ring
  rw [he]
  simpa only [Pi.sub_apply,Function.comp_def] using
    (hf.sub (hf.comp_measurePreserving (gaussian_neg_measurePreserving d))).const_mul (1/2)

theorem oddPart_neg (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : oddPart f (-x) = -oddPart f x := by
  simp only [oddPart,neg_neg]
  ring

theorem coeff_reflect (f : (Fin d → ℝ) → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 (γFin d)) (b : Fin d → ℕ) :
    coeff (fun x => f (-x)) b=(-1:ℝ)^(degree b)*coeff f b := by
  have he : gaussianAverage (-1) f=fun x => f (-x) := by
    funext x
    simp only [gaussianAverage,neg_sq,one_pow,sub_self,Real.sqrt_zero,zero_mul,add_zero,
      neg_one_mul,integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
    rfl
  rw [← he]
  exact gaussianAverage_coefficient (-1) (by norm_num) f hfm hf b

theorem coeff_real_mul (c : ℝ) (f : (Fin d → ℝ) → ℝ) (b : Fin d → ℕ) :
    coeff (fun x => c*f x) b=c*coeff f b := by
  unfold coeff
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem coeff_oddPart (f : (Fin d → ℝ) → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 (γFin d)) (b : Fin d → ℕ) :
    coeff (oddPart f) b=(1-(-1:ℝ)^(degree b))/2*coeff f b := by
  have he : oddPart f=fun x => (1/2)*(f x-f (-x)) := by funext x; unfold oddPart; ring
  rw [he,coeff_real_mul]
  have hc := coeff_sub hf (hf.comp_measurePreserving (gaussian_neg_measurePreserving d)) b
  simp only [Function.comp_def] at hc
  rw [hc,coeff_reflect f hfm hf b]
  ring

theorem oddPart_integral_sq_le (f : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 (γFin d)) :
    (∫ x,(oddPart f x)^2 ∂γFin d) ≤ ∫ x,(f x)^2 ∂γFin d := by
  have hn : MemLp (fun x => f (-x)) 2 (γFin d) :=
    hf.comp_measurePreserving (gaussian_neg_measurePreserving d)
  have hr : (∫ x,(f (-x))^2 ∂γFin d)=∫ x,(f x)^2 ∂γFin d :=
    (gaussian_neg_measurePreserving d).integral_comp
      (Homeomorph.neg (Fin d → ℝ)).measurableEmbedding (fun x => (f x)^2)
  calc
    _ ≤ ∫ x,((f x)^2+(f (-x))^2)/2 ∂γFin d := by
      apply integral_mono (oddPart_memLp f hf).integrable_sq ((hf.integrable_sq.add hn.integrable_sq).div_const 2)
      intro x
      dsimp only [oddPart,Pi.add_apply]
      nlinarith [sq_nonneg (f x+f (-x))]
    _ = _ := by rw [integral_div,integral_add hf.integrable_sq hn.integrable_sq,hr]; ring

def oddHighModes (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := oddPart (highModes 3 f)

theorem oddHighModes_measurable (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (oddHighModes f) := oddPart_measurable _ (highModes_measurable 3 f hf)

theorem oddHighModes_memLp (f : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 (γFin d)) :
    MemLp (oddHighModes f) 2 (γFin d) := oddPart_memLp _ (highModes_memLp 3 f hf)

theorem oddHighModes_coeff_vanish (f : (Fin d → ℝ) → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 (γFin d)) (b : Fin d → ℕ) (hb : degree b < 3) :
    coeff (oddHighModes f) b=0 := by
  rw [oddHighModes,coeff_oddPart _ (highModes_measurable 3 f hfm) (highModes_memLp 3 f hf),
    highModes_coeff_vanish 3 f hf b hb,mul_zero]

theorem coeff_oddHighModes (f : (Fin d → ℝ) → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 (γFin d)) (b : Fin d → ℕ) :
    coeff (oddHighModes f) b=if degree b < 3 ∨ Even (degree b) then 0 else coeff f b := by
  rw [oddHighModes,coeff_oddPart _ (highModes_measurable 3 f hfm) (highModes_memLp 3 f hf),
    coeff_highModes 3 f hf]
  by_cases hb : degree b < 3
  · simp only [ite_eq_left hb,mul_zero,ite_eq_left (Or.inl hb)]
  · rw [ite_eq_right hb,neg_one_pow_eq_ite]
    by_cases he : Even (degree b)
    · simp only [ite_eq_left he,sub_self,zero_div,zero_mul,ite_eq_left (Or.inr he)]
    · simp only [ite_eq_right he,ite_eq_right (not_or.mpr ⟨hb,he⟩)]
      ring

theorem oddHighModes_integral_sq_le (f : (Fin d → ℝ) → ℝ) (hf : MemLp f 2 (γFin d)) :
    (∫ x,(oddHighModes f x)^2 ∂γFin d) ≤ ∫ x,(f x)^2 ∂γFin d :=
  (oddPart_integral_sq_le _ (highModes_memLp 3 f hf)).trans (highModes_integral_sq_le 3 f hf)

def ambientOddHighModes (f : FSC.Coord d → ℝ) (x : FSC.Coord d) : ℝ :=
  oddHighModes (fun y => f (WithLp.toLp 2 y)) x.ofLp

def projectedOddResidual (s : ℝ) (f : FSC.Coord d → ℝ) : FSC.Coord d → ℝ :=
  ambientAverage s (ambientOddHighModes f)

theorem ambientOddHighModes_measurable (f : FSC.Coord d → ℝ) (hfm : Measurable f) :
    Measurable (ambientOddHighModes f) :=
  (oddHighModes_measurable _ (hfm.comp (by fun_prop))).comp (by fun_prop)

theorem ambientOddHighModes_memLp_and_norm (f : FSC.Coord d → ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 (stdGaussian (FSC.Coord d))) :
    MemLp (ambientOddHighModes f) 2 (stdGaussian (FSC.Coord d)) ∧
    (∫ x,(ambientOddHighModes f x)^2 ∂stdGaussian (FSC.Coord d)) ≤
      ∫ x,(f x)^2 ∂stdGaussian (FSC.Coord d) := by
  have hT := gaussian_toLp_measurePreserving d
  have hfin := hf.comp_measurePreserving hT
  have hm := oddHighModes_memLp _ hfin
  have hn := oddHighModes_integral_sq_le _ hfin
  constructor
  · rw [← hT.map_eq]
    apply (memLp_map_measure_iff (ambientOddHighModes_measurable f hfm).aestronglyMeasurable
      hT.aemeasurable).mpr
    exact hm
  · rw [← hT.integral_comp' (fun x => (ambientOddHighModes f x)^2),
      ← hT.integral_comp' (fun x => (f x)^2)]
    exact hn

theorem projectedOddResidual_measurable (s : ℝ) (f : FSC.Coord d → ℝ) (hfm : Measurable f) :
    Measurable (projectedOddResidual s f) :=
  ambientAverage_measurable s _ (ambientOddHighModes_measurable f hfm)

/-- Both low-degree vanishing and the r^(3/2) source gain are derived for
the literal odd, degree-at-least-three smoothed residual. -/
theorem projectedOddResidual_memLp_decay (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (f : FSC.Coord d → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (stdGaussian (FSC.Coord d))) :
    MemLp (projectedOddResidual s f) 2 (stdGaussian (FSC.Coord d)) ∧
    (∀ b,degree b < 3 → coeff (fun x : Fin d → ℝ => projectedOddResidual s f (WithLp.toLp 2 x)) b=0) ∧
    (realLp (stdGaussian (FSC.Coord d)) 2 (projectedOddResidual s f))^2 ≤
      s^6*(realLp (stdGaussian (FSC.Coord d)) 2 f)^2 := by
  have hT := gaussian_toLp_measurePreserving d
  have hfin := hf.comp_measurePreserving hT
  have hfinM : Measurable (fun x : Fin d → ℝ => f (WithLp.toLp 2 x)) := hfm.comp (by fun_prop)
  have hodd := ambientOddHighModes_memLp_and_norm f hfm hf
  have hv b hb : coeff (fun x : Fin d → ℝ => ambientOddHighModes f (WithLp.toLp 2 x)) b=0 :=
    oddHighModes_coeff_vanish _ hfinM hfin b hb
  have hh := ambientAverage_euclidean_memLp_and_decay hs hs1 _
    (ambientOddHighModes_measurable f hfm) hodd.1 3 hv
  refine ⟨hh.1,?_,?_⟩
  · intro b hb
    have he : (fun x : Fin d → ℝ => projectedOddResidual s f (WithLp.toLp 2 x))=
        gaussianAverage s (oddHighModes (fun y => f (WithLp.toLp 2 y))) := by
      funext x
      exact ambientAverage_eq_gaussianAverage s (ambientOddHighModes f) (WithLp.toLp 2 x)
    rw [he,gaussianAverage_coefficient s (by rw [abs_of_pos hs]; exact hs1.le)
      _ (oddHighModes_measurable _ hfinM) (oddHighModes_memLp _ hfin),
      oddHighModes_coeff_vanish _ hfinM hfin b hb,mul_zero]
  · unfold projectedOddResidual
    rw [realLp_two_sq_eq_integral hh.1,realLp_two_sq_eq_integral hf]
    exact (hh.2.trans (mul_le_mul_of_nonneg_left hodd.2 (by positivity))).trans_eq (by ring)

omit [DecidableEq ι] [Nonempty ι] in
/-- The source difference is the actual fractional residual. The bound two
is proved from the two simplex laws, before any projection or smoothing. -/
theorem fractional_difference_sum_sq_le (f g : ι → FSC.Coord d → ℝ)
    (hfm : ∀ i, Measurable (f i)) (hgm : ∀ i, Measurable (g i))
    (hf : ∀ᵐ x ∂stdGaussian (FSC.Coord d), (∀ i,0 ≤ f i x ∧ f i x ≤ 1) ∧ ∑ i,f i x=1)
    (hg : ∀ᵐ x ∂stdGaussian (FSC.Coord d), (∀ i,0 ≤ g i x ∧ g i x ≤ 1) ∧ ∑ i,g i x=1) :
    (∀ i,MemLp (f i-g i) 2 (stdGaussian (FSC.Coord d))) ∧
    (∑ i,(realLp (stdGaussian (FSC.Coord d)) 2 (f i-g i))^2) ≤ 2 := by
  have hF i : MemLp (f i) 2 (stdGaussian (FSC.Coord d)) := by
    apply MemLp.of_bound (hfm i).aestronglyMeasurable 1
    filter_upwards [hf] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hx.1 i).1] using (hx.1 i).2
  have hG i : MemLp (g i) 2 (stdGaussian (FSC.Coord d)) := by
    apply MemLp.of_bound (hgm i).aestronglyMeasurable 1
    filter_upwards [hg] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hx.1 i).1] using (hx.1 i).2
  have hv i := (hF i).sub (hG i)
  refine ⟨hv,?_⟩
  simp_rw [realLp_two_sq_eq_integral (hv _)]
  rw [← integral_finsetSum _ (fun i _ => (hv i).integrable_sq)]
  have hle : ∀ᵐ x ∂stdGaussian (FSC.Coord d),∑ i,((f i-g i) x)^2 ≤ 2 := by
    filter_upwards [hf,hg] with x hx hy
    calc
      _ ≤ ∑ i,(f i x+g i x) := by
        apply Finset.sum_le_sum
        intro i _
        have h1 := (hx.1 i).1
        have h2 := (hx.1 i).2
        have h3 := (hy.1 i).1
        have h4 := (hy.1 i).2
        dsimp only [Pi.sub_apply]
        nlinarith [mul_nonneg h1 h3]
      _ = 2 := by rw [Finset.sum_add_distrib,hx.2,hy.2]; norm_num
  exact (integral_mono_ae (integrable_finsetSum _ (fun i _ => (hv i).integrable_sq))
    (integrable_const (2:ℝ)) hle).trans_eq (by simp)

omit [DecidableEq ι] [Nonempty ι] in
/-- For the literal projected odd residual of fractional assignments,
the full label-source energy is at most 2s^6. -/
theorem fractional_projectedOddResidual_sum_norm_sq_le (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (f g : ι → FSC.Coord d → ℝ)
    (hfm : ∀ i, Measurable (f i)) (hgm : ∀ i, Measurable (g i))
    (hf : ∀ᵐ x ∂stdGaussian (FSC.Coord d), (∀ i,0 ≤ f i x ∧ f i x ≤ 1) ∧ ∑ i,f i x=1)
    (hg : ∀ᵐ x ∂stdGaussian (FSC.Coord d), (∀ i,0 ≤ g i x ∧ g i x ≤ 1) ∧ ∑ i,g i x=1) :
    (∀ i,MemLp (projectedOddResidual s (f i-g i)) 2 (stdGaussian (FSC.Coord d))) ∧
    (∀ i b,degree b < 3 → coeff (fun x : Fin d → ℝ =>
      projectedOddResidual s (f i-g i) (WithLp.toLp 2 x)) b=0) ∧
    (∑ i,(realLp (stdGaussian (FSC.Coord d)) 2 (projectedOddResidual s (f i-g i)))^2) ≤ 2*s^6 := by
  have hv := fractional_difference_sum_sq_le f g hfm hgm hf hg
  have hh i := projectedOddResidual_memLp_decay s hs hs1 _ ((hfm i).sub (hgm i)) (hv.1 i)
  refine ⟨fun i => (hh i).1,fun i => (hh i).2.1,?_⟩
  calc
    _ ≤ ∑ i,s^6*(realLp (stdGaussian (FSC.Coord d)) 2 (f i-g i))^2 :=
      Finset.sum_le_sum fun i _ => (hh i).2.2
    _ = s^6*∑ i,(realLp (stdGaussian (FSC.Coord d)) 2 (f i-g i))^2 := by rw [Finset.mul_sum]
    _ ≤ s^6*2 := mul_le_mul_of_nonneg_left hv.2 (by positivity)
    _ = _ := by ring

def actualResidual (τ χ : ℝ) (p₀ p₁ : Parameters d ι)
    (u : ι → FSC.Coord d → ℝ) (i : ι) (x : FSC.Coord d) : ℝ :=
  smoothedHighModes (-((τ*χ)^2)) 2 (cellDifference p₀ p₁ i) x-ambientAverage (τ*χ) (u i) x

/-- Exact actual residual identification on a common tangent full-measure
set for every normal parameter. The first source identity is pointwise. -/
theorem actualResidual_factorization_on_plane_all_parameters
    (p₀ p₁ : Parameters d ι) (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (h₀ : CenteredSingularLowerBound p₀.1 s₀) (h₁ : CenteredSingularLowerBound p₁.1 s₁)
    (i : ι) (τ χ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hχ : 0 < χ) (hχ1 : χ < 1)
    (u : ι → FSC.Coord d → ℝ) (huM : Measurable (u i))
    (hu : MemLp (u i) 2 (stdGaussian (FSC.Coord d)))
    (w : FSC.Coord d) (hw : ‖w‖=1) {n : ℕ}
    (e : tangentSpace w ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ y : tangentSpace w ∂stdGaussian (tangentSpace w),∀ a : ℝ,
      actualResidual τ χ p₀ p₁ u i ((y:FSC.Coord d)+a•w)=
        ambientAverage τ (cellSource τ χ p₀ p₁ i) ((y:FSC.Coord d)+a•w)-
          ambientAverage τ (highSource χ (u i)) ((y:FSC.Coord d)+a•w) := by
  filter_upwards [ambientAverage_comp_on_plane_all_parameters w hw e τ χ hτ hτ1 hχ hχ1 (u i) huM hu]
    with y hy
  intro a
  rw [cellSource_factorization p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i τ χ hτ hτ1 hχ hχ1,hy a]
  rfl

/-- Exact pointwise linearity for the two actual cell high-mode potentials.
This identifies the first term with q_B-q_0 even on Gaussian-null facets. -/
theorem smoothed_cellDifference_eq_potential_difference
    (p₀ p₁ : Parameters d ι) (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (h₀ : CenteredSingularLowerBound p₀.1 s₀) (h₁ : CenteredSingularLowerBound p₁.1 s₁)
    (i : ι) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    smoothedHighModes (-r) 2 (cellDifference p₀ p₁ i)=
      smoothedHighModes (-r) 2 ((winningCell p₁.1 p₁.2 i).indicator (fun _ => 1))-
        smoothedHighModes (-r) 2 ((winningCell p₀.1 p₀.2 i).indicator (fun _ => 1)) := by
  have hra : |-r| < 1 := by rwa [abs_neg,abs_of_pos hr]
  let f := cellWeight p₁.1 p₁.2 i
  let g := cellWeight p₀.1 p₀.2 i
  have hfM := cellWeight_measurable p₁.1 p₁.2 i
  have hgM := cellWeight_measurable p₀.1 p₀.2 i
  have hf := cellWeight_memLp p₁.1 p₁.2 i
  have hg := cellWeight_memLp p₀.1 p₀.2 i
  have hcD := highModes_continuous_quadratic_of_average (-r) hra.le 2 (by norm_num)
    (coordinateCellDifference p₀ p₁ i) (coordinateCellDifference_measurable p₀ p₁ i)
    (gaussianAverage_cellDifference_continuous p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i (-r) hra)
    2 (by norm_num) (coordinateCellDifference_abs_le p₀ p₁ i)
  have hcf := highModes_continuous_quadratic_of_average (-r) hra.le 2 (by norm_num) f hfM
    (gaussianAverage_cellWeight_continuous p₁.1 s₁ hs₁ h₁ p₁.2 i (-r) hra)
    1 (by norm_num) (cellWeight_abs_le p₁.1 p₁.2 i)
  have hcg := highModes_continuous_quadratic_of_average (-r) hra.le 2 (by norm_num) g hgM
    (gaussianAverage_cellWeight_continuous p₀.1 s₀ hs₀ h₀ p₀.2 i (-r) hra)
    1 (by norm_num) (cellWeight_abs_le p₀.1 p₀.2 i)
  have hleft : Continuous (gaussianAverage (-r) (highModes 2 (f-g))) :=
    hcD.1.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))
  have hright : Continuous (gaussianAverage (-r) (highModes 2 f)-gaussianAverage (-r) (highModes 2 g)) :=
    (hcf.1.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))).sub
      (hcg.1.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)))
  let : (gaussianReal 0 1).IsOpenPosMeasure := GaussianFin.instIsOpenPosMeasureγ
  let : (γFin d).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure (fun _ : Fin d => gaussianReal 0 1)
  have he := (Continuous.ae_eq_iff_eq (γFin d) hleft hright).mp
    (negative_highModes_difference_ae hr hr1 2 f g hf hg)
  funext x
  have hx := congrFun he x.ofLp
  change gaussianAverage (-r) (highModes 2 (coordinateCellDifference p₀ p₁ i)) x.ofLp=
    gaussianAverage (-r) (highModes 2 (cellWeight p₁.1 p₁.2 i)) x.ofLp-
      gaussianAverage (-r) (highModes 2 (cellWeight p₀.1 p₀.2 i)) x.ofLp at hx
  change ambientAverage (-r) (ambientHighModes 2 (cellDifference p₀ p₁ i)) x=
    ambientAverage (-r) (ambientHighModes 2 ((winningCell p₁.1 p₁.2 i).indicator (fun _ => 1))) x-
      ambientAverage (-r) (ambientHighModes 2 ((winningCell p₀.1 p₀.2 i).indicator (fun _ => 1))) x
  simp only [ambientAverage_eq_gaussianAverage]
  exact hx

theorem actualResidual_eq_cell_potentials
    (p₀ p₁ : Parameters d ι) (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (h₀ : CenteredSingularLowerBound p₀.1 s₀) (h₁ : CenteredSingularLowerBound p₁.1 s₁)
    (i : ι) (τ χ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hχ : 0 < χ) (hχ1 : χ < 1)
    (u : ι → FSC.Coord d → ℝ) (x : FSC.Coord d) :
    actualResidual τ χ p₀ p₁ u i x=
      smoothedHighModes (-((τ*χ)^2)) 2 ((winningCell p₁.1 p₁.2 i).indicator (fun _ => 1)) x-
        smoothedHighModes (-((τ*χ)^2)) 2 ((winningCell p₀.1 p₀.2 i).indicator (fun _ => 1)) x-
          ambientAverage (τ*χ) (u i) x := by
  have hp : τ*χ < 1 := (mul_lt_mul_of_pos_left hχ1 hτ).trans (by simpa using hτ1)
  unfold actualResidual
  rw [smoothed_cellDifference_eq_potential_difference p₀ p₁ s₀ s₁ hs₀ hs₁ h₀ h₁ i
    ((τ*χ)^2) (by positivity) (by nlinarith [mul_pos hτ hχ])]
  rfl

end NegativeVotingStructuredResidualInputs
