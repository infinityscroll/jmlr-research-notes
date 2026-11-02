import GaussianExteriorRoutingGeometry
import GaussianExteriorActualComparison
import GaussianExteriorRelativeAlgebra

/-! Actual entire signed high-tail comparison, transferred to the Euclidean
centroid geometry. This covers all high Hermite degrees, not a truncation. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter
open scoped BigOperators RealInnerProductSpace Classical ENNReal
namespace NegativeVotingExteriorSignedTailRelative
open NegativeVoting NegativeVotingFan NegativeVotingAssignmentDuality
  NegativeVotingCentroidOptimization NegativeVotingBalancedReference NegativeVotingProcrustes
  NegativeVotingExteriorRoutingMargin NegativeVotingExteriorRoutingGeometry
  NegativeVotingExteriorActualComparison NegativeVotingExteriorRelativeAlgebra
  NegativeVotingSignedHighTailComparison NegativeVotingRegularReferenceNormalization
  NegativeVotingDisintegration NegativeVotingActualFacetOUTrace NegativeVotingConditionalSecondMoment
variable {n d e : ℕ}

def rawCoordinate (f:FSC.Coord e→Fin (n+2)→ℝ) (i:Fin (n+2)) (x:Fin e→ℝ) : ℝ :=
  f (WithLp.toLp 2 x) i

theorem rawCoordinate_measurable (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ)
    (hf:Feasible p f) (i:Fin (n+2)) : AEMeasurable (rawCoordinate f i) (γFin e) :=
  ((hf.1 i).aestronglyMeasurable.comp_measurePreserving (gaussian_toLp_measurePreserving e)).aemeasurable

theorem rawCoordinate_simplex (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ)
    (hf:Feasible p f) :
    ∀ᵐx ∂γFin e,(∀i,0 ≤ rawCoordinate f i x ∧ rawCoordinate f i x ≤ 1) ∧
      ∑i,rawCoordinate f i x=1 := by
  filter_upwards [(gaussian_toLp_measurePreserving e).quasiMeasurePreserving.ae hf.2.1] with x hx
  exact ⟨fun i=>⟨hx.1 i,simplex_weight_le_one _ hx i⟩,hx.2⟩

theorem rawCoordinate_absoluteMass (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ)
    (hf:Feasible p f) (i:Fin (n+2)) : absoluteMass (rawCoordinate f i)=p i := by
  change (∫x,|f (WithLp.toLp 2 x) i| ∂standardGaussian (Fin e))=p i
  rw [integral_standardGaussian_eq_euclidean]
  calc
    _ = ∫x,f x i ∂stdGaussian (FSC.Coord e) := by
      apply integral_congr_ae
      filter_upwards [hf.2.1] with x hx
      simp only [WithLp.toLp_ofLp,abs_of_nonneg (hx.1 i)]
    _ = p i := hf.2.2 i

theorem fan_feasible (R:Fin (n+2)→FSC.Coord e) : Feasible (mass R 0) (weights R 0) :=
  ⟨fun i=>(weights_measurable R 0 i).aemeasurable,
    Filter.Eventually.of_forall (weights_simplex R 0),fun _=>rfl⟩

theorem scaled_regular_mass (R:Fin (n+2)→FSC.Coord e) (hR:ScaledRegularGram n R) (i:Fin (n+2)) :
    mass R 0 i=1/((n:ℝ)+2) := by
  let U := (referenceScale n)⁻¹•R
  have hU : ∀i j,inner ℝ (U i) (U j)=
      (if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using scaled_regular_normalized_gram R hR
  have heq : R=referenceScale n•U := by
    simp only [U,smul_smul,mul_inv_cancel₀ (ne_of_gt (referenceScale_pos n)),one_smul]
  rw [heq,regular_scaled_mass_zero U hU (referenceScale n) (referenceScale_pos n)]
  simp only [Nat.cast_add,Nat.cast_ofNat,one_div]

theorem raw_mismatch_eq (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ)
    (hf:Feasible p f) (R:Fin (n+2)→FSC.Coord e) :
    (∑i,absoluteMass (rawCoordinate f i-rawCoordinate (weights R 0) i))=
      ∫x,mismatch R f x ∂stdGaussian (FSC.Coord e) := by
  have he (i:Fin (n+2)) : absoluteMass (rawCoordinate f i-rawCoordinate (weights R 0) i)=
      ∫x,|f x i-weights R 0 x i| ∂stdGaussian (FSC.Coord e) := by
    change (∫x,|f (WithLp.toLp 2 x) i-weights R 0 (WithLp.toLp 2 x) i| ∂standardGaussian (Fin e))=_
    rw [integral_standardGaussian_eq_euclidean]
  simp_rw [he]
  change _ = ∫x,(∑i,|f x i-weights R 0 x i|) ∂stdGaussian (FSC.Coord e)
  rw [integral_finsetSum]
  intro i _
  convert ((feasible_coordinate_integrable p f hf i).sub (weights_integrable R 0 i)).norm using 1

def signedTailDifference (r:ℝ) (f g:FSC.Coord e→Fin (n+2)→ℝ) : ℝ :=
  ∑i,(energyPairing (-r) 3 (rawCoordinate f i)-energyPairing (-r) 3 (rawCoordinate g i))

/-- Literal full cubic high-tail estimate for any feasible competitor with
rare label masses and a genuine scaled regular comparison rule. -/
theorem actual_cubic_tail (hn:0 < n) (r:ℝ) (hr:0 < r)
    (hrL:4*r*(1+Real.log ((n:ℝ)+2)) < 1)
    (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ) (hf:Feasible p f)
    (hp:∀i,p i ≤ 3/(2*((n:ℝ)+2)))
    (R:Fin (n+2)→FSC.Coord e) (hR:ScaledRegularGram n R) :
    |signedTailDifference r f (weights R 0)| ≤
      768*Real.exp (1/2)*r^3*(1+Real.log ((n:ℝ)+2))^3*
        Real.sqrt (∫x,mismatch R f x ∂stdGaussian (FSC.Coord e))/((n:ℝ)+2) := by
  have hm : (3:ℝ) ≤ (n:ℝ)+2 := by exact_mod_cast (show 3 ≤ n+2 by omega)
  have hg := fan_feasible R
  have hgp (i:Fin (n+2)) : absoluteMass (rawCoordinate (weights R 0) i) ≤ 3/(2*((n:ℝ)+2)) := by
    rw [rawCoordinate_absoluteMass _ _ hg,scaled_regular_mass R hR]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hh := ae_fractional_cubic_tail_abs_le (Fin (n+2)) ((n:ℝ)+2) r hm hr hrL
    (rawCoordinate f) (rawCoordinate (weights R 0))
    (rawCoordinate_measurable p f hf) (rawCoordinate_measurable _ _ hg)
    (rawCoordinate_simplex p f hf) (rawCoordinate_simplex _ _ hg)
    (fun i=>by rw [rawCoordinate_absoluteMass p f hf];exact hp i) hgp
  rw [raw_mismatch_eq p f hf R] at hh
  exact hh


def exteriorMismatchConstant (A:ℝ) : ℝ :=
  2*(regularMarginConstant+1)*Real.sqrt (1+2*A)

def exteriorHighTailConstant (A c:ℝ) : ℝ :=
  768*Real.exp (1/2)*Real.sqrt (exteriorMismatchConstant A)*c^(-3/4:ℝ)

/-- Full signed high-tail control relative to the exterior deficit. The
curvature/orbit and mass premises refer to actual Gaussian quantities and are
provided by the already formalized competitive-localization theorems. -/
theorem exists_regular_relative_signed_tail
    (hn:0 < n) (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x) (hde:d≤e)
    (hscale:Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2) ≤ referenceScale n)
    (p:Fin (n+2)→ℝ) (f:FSC.Coord e→Fin (n+2)→ℝ) (hf:Feasible p f)
    (hp:∀i,p i ≤ 3/(2*((n:ℝ)+2)))
    (r:ℝ) (hr:0 < r) (hrL:4*r*(1+Real.log ((n:ℝ)+2)) < 1)
    (J A c:ℝ) (hJ:0 ≤ J) (hA:0 ≤ A) (hc:0 < c)
    (hdef:NegativeVotingGaussianMaximumMean.referenceFirstWeight n-centroidEnergy f ≤ J)
    (hd:0 < regularOrbitDistance n (centroidRows f))
    (hdist:(regularOrbitDistance n (centroidRows f))^2 ≤
      A*(((n:ℝ)+2)*Real.sqrt ((n:ℝ)+2))*(1+Real.log ((n:ℝ)+2))*J)
    (hfloor:c/(((n:ℝ)+2)^3*Real.sqrt (1+Real.log ((n:ℝ)+2))) ≤ J) :
    ∃R:Fin (n+2)→FSC.Coord e,ScaledRegularGram n R ∧
      |signedTailDifference r f (weights R 0)| ≤
        exteriorHighTailConstant A c*r^3*((n:ℝ)+2)^(15/8:ℝ)*
          (1+Real.log ((n:ℝ)+2))^4*J := by
  let m:ℝ := (n:ℝ)+2
  let L:ℝ := 1+Real.log m
  have hm : 1 ≤ m := by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hL : 1 ≤ L := by dsimp [L];linarith [Real.log_nonneg hm]
  obtain ⟨R,hR,hmis⟩ := exists_regular_mismatch_bound b hG hP hde hscale p f hf
    J A L hJ hA hL hdef hd hdist
  let E := ∫x,mismatch R f x ∂stdGaussian (FSC.Coord e)
  have hE : 0 ≤ E := integral_nonneg fun x=>Finset.sum_nonneg fun i _=>abs_nonneg _
  have hC : 0 ≤ exteriorMismatchConstant A := by
    unfold exteriorMismatchConstant
    have hK := regularMarginConstant_ge_one
    positivity
  have hmis' : E ≤ exteriorMismatchConstant A*Real.sqrt (m^2*Real.sqrt m*L*J) := by
    refine hmis.trans_eq ?_
    change 2*(regularMarginConstant+1)*Real.sqrt ((1+2*A)*m^2*Real.sqrt m*L*J)=_
    rw [show (1+2*A)*m^2*Real.sqrt m*L*J=(1+2*A)*(m^2*Real.sqrt m*L*J) by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 1+2*A)]
    unfold exteriorMismatchConstant
    ring
  have hH := actual_cubic_tail hn r hr hrL p f hf hp R hR
  exact ⟨R,hR,cubic_tail_relative (exteriorMismatchConstant A) (768*Real.exp (1/2))
    m L c J E (signedTailDifference r f (weights R 0)) r hC (by positivity)
    hm hL hc hE hr.le hfloor hmis' hH⟩

end NegativeVotingExteriorSignedTailRelative
