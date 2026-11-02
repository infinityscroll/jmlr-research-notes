import GaussianRegularPairRange
import GaussianRegularFacetRangeEnvelope
import GaussianRegularNoisePair

/-! The actual divided regular-noise coefficient, defined by a continuous
integral of the Gaussian mass Jacobian rather than division by a score gap.
It is therefore defined on reference ties and in arbitrary ambient dimension. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingRegularPairCoefficient
open NegativeVoting NegativeVotingFan NegativeVotingFanJacobian
  NegativeVotingRegularMassSeparation NegativeVotingRegularMassSymmetry
  NegativeVotingFacetConditionalPlane NegativeVotingCenteredParseval
  NegativeVotingRegularScoreProjection NegativeVotingRegularNoisePair
  NegativeVotingBalancedReference NegativeVotingRegularFacetRange
variable {n d : ℕ}

def pairSlope (B : Fin (n+2) → FSC.Coord d) (i j : Fin (n+2))
    (h : FSC.Coord d) (t : ℝ) : ℝ :=
  massDerivative B (scoreOffsets B (pairPath B i j h t)) i (pairVelocity i j 1)-
    massDerivative B (scoreOffsets B (pairPath B i j h t)) j (pairVelocity i j 1)

def averagePairSlope (B : Fin (n+2) → FSC.Coord d) (i j : Fin (n+2))
    (h : FSC.Coord d) : ℝ := ∫t in (0:ℝ)..1,pairSlope B i j h t

def negativePairCoefficient (B : Fin (n+2) → FSC.Coord d) (r : ℝ)
    (x : FSC.Coord d) (i j : Fin (n+2)) : ℝ :=
  (referenceScale n*Real.sqrt (1-r^2))⁻¹*
    averagePairSlope B j i (-(r/Real.sqrt (1-r^2)) • frameOperator B x)

theorem regular_massDerivative_continuous (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i : Fin (n+2)) : Continuous (fun h => massDerivative B h i) := by
  have hG' : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hlower := centered_singular_one B hG'
  have hc := contDiff_pi.mp (contDiff_mass_vector B 1 (by norm_num) hlower) i
  have he : (fun h => massDerivative B h i)=fderiv ℝ (fun h => mass B h i) := by
    funext h
    exact (hasFDerivAt_mass B 1 (by norm_num) hlower h i).fderiv.symm
  rw [he]
  exact hc.continuous_fderiv (by norm_num)

theorem pairSlope_continuous (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) :
    Continuous (fun p : FSC.Coord d × ℝ => pairSlope B i j p.1 p.2) := by
  have hp : Continuous (fun p : FSC.Coord d × ℝ =>
      scoreOffsets B (pairPath B i j p.1 p.2)) := by
    apply continuous_pi
    intro k
    simp only [scoreOffsets,pairPath,pairComponent,inner_add_right,inner_sub_right,
      real_inner_smul_right]
    fun_prop
  exact (((regular_massDerivative_continuous B hG i).comp hp).clm_apply continuous_const).sub
    (((regular_massDerivative_continuous B hG j).comp hp).clm_apply continuous_const)

set_option maxHeartbeats 200000 in
theorem pairSlope_fixed_continuous (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (h : FSC.Coord d) :
    Continuous (fun t : ℝ => pairSlope B i j h t) := by
  have hc : Continuous ((fun p : FSC.Coord d × ℝ => pairSlope B i j p.1 p.2) ∘
      (fun t : ℝ => (h,t))) :=
    (pairSlope_continuous B hG i j).comp
      ((continuous_const : Continuous (fun _ : ℝ => h)).prodMk continuous_id)
  simpa only [Function.comp_def] using hc

theorem pairVelocity_scale (i j : Fin (n+2)) (a : ℝ) :
    pairVelocity i j a=a • pairVelocity i j 1 := by
  funext k
  simp only [pairVelocity,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

theorem pairMassDerivative_eq_gap_mul_slope (B : Fin (n+2) → FSC.Coord d)
    (i j : Fin (n+2)) (h : FSC.Coord d) (t : ℝ) :
    pairMassDerivative B i j h t=inner ℝ (B i-B j) h*pairSlope B i j h t := by
  rw [pairMassDerivative,pairVelocity_scale]
  simp only [map_smul,smul_eq_mul,pairSlope]
  ring

theorem averagePairSlope_continuous (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) : Continuous (averagePairSlope B i j) := by
  have hh : Continuous (fun h => ∫t in Icc (0:ℝ) 1,pairSlope B i j h t) :=
    continuous_parametric_integral_of_continuous (pairSlope_continuous B hG i j) isCompact_Icc
  have he : averagePairSlope B i j=(fun h => ∫t in Icc (0:ℝ) 1,pairSlope B i j h t) := by
    funext h
    rw [averagePairSlope,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Icc_eq_integral_Ioc]
  rw [he]
  exact hh

/-- Exact FTC representation of the actual Gaussian probability difference,
with no sign restriction on the original score gap. -/
theorem mass_pair_difference_eq_gap_mul_average (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i j : Fin (n+2)) (hij : i≠j) (h : FSC.Coord d) :
    mass B (scoreOffsets B h) i-mass B (scoreOffsets B h) j=
      inner ℝ (B i-B j) h*averagePairSlope B i j h := by
  have hd : Continuous (pairMassDerivative B i j h) := by
    have he : pairMassDerivative B i j h=(fun t => inner ℝ (B i-B j) h*pairSlope B i j h t) :=
      funext (pairMassDerivative_eq_gap_mul_slope B i j h)
    rw [he]
    exact (pairSlope_fixed_continuous B hG i j h).const_mul _
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t∈uIcc (0:ℝ) 1) => pairMassDifference_hasDerivAt B hG i j hij h t)
    (hd.intervalIntegrable 0 1)
  have hz : pairMassDifference B i j h 0=0 := by
    apply sub_eq_zero.mpr
    exact regular_mass_eq_of_offset_eq B (1/((n:ℝ)+2)) hG
      (scoreOffsets B (pairPath B i j h 0)) i j (pairPath_zero_equal_scores B hG i j hij h)
  have h1 : pairMassDifference B i j h 1=
      mass B (scoreOffsets B h) i-mass B (scoreOffsets B h) j := by
    simp only [pairMassDifference,pairPath,one_smul,sub_add_cancel]
  rw [h1,hz,sub_zero] at hh
  simp_rw [pairMassDerivative_eq_gap_mul_slope] at hh
  rw [intervalIntegral.integral_const_mul] at hh
  exact hh.symm

theorem negativePairCoefficient_continuous (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (i j : Fin (n+2)) :
    Continuous (fun x => negativePairCoefficient B r x i j) := by
  exact ((averagePairSlope_continuous B hG j i).comp
    ((frameOperator B).continuous.const_smul (-(r/Real.sqrt (1-r^2))))).const_mul _

/-- Actual divided-pair identity at every point, including score ties. The
normalization is r times the reference centroid score gap alpha*(s_i-s_j). -/
theorem negativePairCoefficient_gap_identity (B : Fin (n+2) → FSC.Coord d)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0<r) (hr1 : r<1) (x : FSC.Coord d)
    (i j : Fin (n+2)) (hij : i≠j) :
    gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x.ofLp j-
      gaussianNoiseOperator (-r) (regularAssignment (fun k => (B k).ofLp)) x.ofLp i=
      r*negativePairCoefficient B r x i j*(referenceScale n*inner ℝ (B i-B j) x) := by
  have hG' : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  let τ := r/Real.sqrt (1-r^2)
  let H := -τ • frameOperator B x
  have hs : inner ℝ (B j-B i) H=τ*inner ℝ (B i-B j) x := by
    simp only [H,real_inner_smul_right,inner_sub_left,frame_preserves_scores B hG']
    ring
  rw [gaussianNoiseOperator_negative_projected B hG' r hr hr1 x,
    mass_pair_difference_eq_gap_mul_average B hG j i (Ne.symm hij),hs]
  have ha := NegativeVotingRegularOU.negative_noise_scale_pos r hr hr1
  change (r/Real.sqrt (1-r^2))*inner ℝ (B i-B j) x*averagePairSlope B j i H=
    r*((referenceScale n*Real.sqrt (1-r^2))⁻¹*averagePairSlope B j i H)*
      (referenceScale n*inner ℝ (B i-B j) x)
  field_simp [(referenceScale_pos n).ne',ha.ne']

end NegativeVotingRegularPairCoefficient
