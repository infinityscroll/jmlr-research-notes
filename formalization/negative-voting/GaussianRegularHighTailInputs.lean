import GaussianRegularCellReflection
import GaussianRegularReferenceNormalization

/-! Actual regular-cell rare representatives for the signed cross term.
Mass, source norm, pointwise factorization and reflection are derived. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter
open scoped BigOperators RealInnerProductSpace Classical ENNReal Topology
namespace NegativeVotingRegularHighTailInputs
open NegativeVotingRegularCellReflection NegativeVotingRareLabelHighChaos
  NegativeVotingCellOUContinuity NegativeVotingBoundedOUCellTests NegativeVotingHypercontractivity
  NegativeVotingQuadraticMomentPadding NegativeVotingFan NegativeVotingNearRegularBalancedGeometry
  NegativeVotingRegularReferenceNormalization NegativeVotingFacetConditionalPlane
  NegativeVotingActualFacetOUTrace NegativeVotingDisintegration NegativeVotingProjection
  NegativeVotingOUResidualMoment
variable {d m : ℕ} [NeZero m]

 theorem gaussianAverage_sub_pointwise (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ<1)
    (f g : (Fin d→ℝ)→ℝ) (hf : MemLp f 2 (γFin d)) (hg : MemLp g 2 (γFin d))
    (hfc : Continuous (fun x:FSC.Coord d=>f x.ofLp))
    (hgc : Continuous (fun x:FSC.Coord d=>g x.ofLp))
    (Cf Cg : ℝ) (hCf : 0≤Cf) (hCg : 0≤Cg)
    (hfb : ∀x:FSC.Coord d,|f x.ofLp|≤Cf*(1+‖x‖^2))
    (hgb : ∀x:FSC.Coord d,|g x.ofLp|≤Cg*(1+‖x‖^2)) :
    gaussianAverage ρ (f-g)=gaussianAverage ρ f-gaussianAverage ρ g := by
  have hbc (x:FSC.Coord d) : |(f-g) x.ofLp|≤(Cf+Cg)*(1+‖x‖^2) := by
    exact (abs_sub _ _).trans (by simpa only [add_mul] using add_le_add (hfb x) (hgb x))
  have hc := gaussianAverage_continuous_quadratic ρ (f-g) (hfc.sub hgc)
    (Cf+Cg) (add_nonneg hCf hCg) hbc
  have hc' := (gaussianAverage_continuous_quadratic ρ f hfc Cf hCf hfb).sub
    (gaussianAverage_continuous_quadratic ρ g hgc Cg hCg hgb)
  letI : (gaussianReal 0 1).IsOpenPosMeasure := GaussianFin.instIsOpenPosMeasureγ
  letI : (γFin d).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure (fun _ : Fin d=>gaussianReal 0 1)
  exact (Continuous.ae_eq_iff_eq (γFin d) hc hc').mp (gaussianAverage_sub_ae hρ hρ1 f g hf hg)

 theorem regular_raw_cell_measure (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ)) (i : Fin m) :
    γFin d ((WithLp.toLp 2) ⁻¹' winningCell R 0 i)=ENNReal.ofReal (1/(m:ℝ)) := by
  have hinj : Function.Injective R := by
    intro j k h
    by_contra hne
    exact regular_gram_rows_ne R (1/(m:ℝ)) hG j k hne h
  have hm := congrFun (regular_mass_zero R hG) i
  rw [mass_eq_winningCell R hinj] at hm
  have he : γFin d ((WithLp.toLp 2) ⁻¹' winningCell R 0 i)=
      stdGaussian (FSC.Coord d) (winningCell R 0 i) := by
    rw [←map_pi_eq_stdGaussian,Measure.map_apply (by fun_prop) (winningCell_measurable R 0 i)]
    rfl
  rw [he]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1/(m:ℝ))]
  simpa only [Measure.real,one_div] using hm

 theorem regular_rareRepresentative_norm (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (τ σ C : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hσ : 0<σ) (hσ1 : σ<1)
    (hscale : τ^2*Real.log (m:ℝ)≤C) (i : Fin m) :
    eLpNorm (rareRepresentative τ σ 3 (cellWeight R 0 i)) 2 (γFin d) ≤
      ENNReal.ofReal (σ^3*(Real.exp C/(m:ℝ))) := by
  have hm : (1:ℝ) ≤ m := by exact_mod_cast (NeZero.one_le : 1 ≤ m)
  have hE : MeasurableSet ((WithLp.toLp 2) ⁻¹' winningCell R 0 i) :=
    (winningCell_measurable R 0 i).preimage (by fun_prop)
  have hh := rareRepresentative_uniform_cell_bound τ σ (m:ℝ) C hτ hτ1 hσ hσ1 hm hscale
    3 ((WithLp.toLp 2) ⁻¹' winningCell R 0 i) hE (regular_raw_cell_measure R hG i)
  have he : (((WithLp.toLp 2) ⁻¹' winningCell R 0 i).indicator (fun _=>1))=cellWeight R 0 i := by
    funext x
    simp only [cellWeight,Set.indicator_comp_right]
    rfl
  rw [he] at hh
  exact hh

 theorem regular_rareRepresentative_regular (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (τ σ : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hσ : 0<σ) (hσ1 : σ<1) (i : Fin m) :
    Measurable (rareRepresentative τ σ 3 (cellWeight R 0 i)) ∧
    MemLp (rareRepresentative τ σ 3 (cellWeight R 0 i)) 2 (γFin d) ∧
    Continuous (fun x:FSC.Coord d=>rareRepresentative τ σ 3 (cellWeight R 0 i) x.ofLp) ∧
    ∃ C:ℝ,0≤C ∧ ∀x:FSC.Coord d,
      |rareRepresentative τ σ 3 (cellWeight R 0 i) x.ofLp|≤C*(1+‖x‖^2) := by
  have hτa : |τ|<1 := by rwa [abs_of_pos hτ]
  have hσa : |-σ|≤1 := by rw [abs_neg,abs_of_pos hσ];exact hσ1.le
  have hlower : NegativeVotingCapTail.CenteredSingularLowerBound R 1 := by
    simpa only [one_smul] using regular_scaled_singular R hG 1
  have hfM := cellWeight_measurable R 0 i
  have hf := cellWeight_memLp R 0 i
  have hsM := gaussianAverage_measurable τ _ hfM
  have hs := gaussianAverage_memLp_signed τ hτa.le _ hfM hf
  have hc := gaussianAverage_cellWeight_continuous R 1 (by norm_num) hlower 0 i τ hτa
  have hb := gaussianAverage_abs_le_bounded τ (cellWeight R 0 i) 1 (cellWeight_abs_le R 0 i)
  have hquad := gaussianAverage_highModes_continuous_quadratic (-σ) hσa 3 (by rfl)
    (gaussianAverage τ (cellWeight R 0 i)) hc 1 (by norm_num) hb
  exact ⟨gaussianAverage_measurable (-σ) _ (highModes_measurable 3 _ hsM),
    gaussianAverage_memLp_signed (-σ) hσa _ (highModes_measurable 3 _ hsM) (highModes_memLp 3 _ hs),hquad⟩

def regularGapInput (R : Fin m→FSC.Coord d) (τ σ : ℝ) (i j : Fin m) (x : FSC.Coord d) : ℝ :=
  rareRepresentative τ σ 3 (cellWeight R 0 i) x.ofLp-
    rareRepresentative τ σ 3 (cellWeight R 0 j) x.ofLp

 theorem regularGapInput_memLp_norm (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (τ σ C : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hσ : 0<σ) (hσ1 : σ<1)
    (hscale : τ^2*Real.log (m:ℝ)≤C) (i j : Fin m) :
    Measurable (regularGapInput R τ σ i j) ∧
    MemLp (regularGapInput R τ σ i j) 2 (stdGaussian (FSC.Coord d)) ∧
    eLpNorm (regularGapInput R τ σ i j) 2 (stdGaussian (FSC.Coord d)) ≤
      ENNReal.ofReal (2*σ^3*(Real.exp C/(m:ℝ))) := by
  have hi := regular_rareRepresentative_regular R hG τ σ hτ hτ1 hσ hσ1 i
  have hj := regular_rareRepresentative_regular R hG τ σ hτ hτ1 hσ hσ1 j
  have hmp : MeasurePreserving (fun x:FSC.Coord d=>x.ofLp) (stdGaussian (FSC.Coord d)) (γFin d) :=
    ⟨by fun_prop,gaussian_coordinate_isometry_map (LinearIsometryEquiv.refl ℝ (FSC.Coord d))⟩
  have hm := (hi.2.1.sub hj.2.1).comp_measurePreserving hmp
  have hM : Measurable (regularGapInput R τ σ i j) := (hi.1.sub hj.1).comp (by fun_prop)
  refine ⟨hM,hm,?_⟩
  change eLpNorm ((rareRepresentative τ σ 3 (cellWeight R 0 i)-
    rareRepresentative τ σ 3 (cellWeight R 0 j)) ∘ (fun x:FSC.Coord d=>x.ofLp)) 2
    (stdGaussian (FSC.Coord d)) ≤ _
  rw [eLpNorm_comp_measurePreserving (hi.2.1.sub hj.2.1).aestronglyMeasurable hmp]
  have hh := eLpNorm_sub_le (f := rareRepresentative τ σ 3 (cellWeight R 0 i))
    (g := rareRepresentative τ σ 3 (cellWeight R 0 j)) (μ := γFin d) (by norm_num : (1:ℝ≥0∞) ≤ 2)
  change eLpNorm (fun x=>rareRepresentative τ σ 3 (cellWeight R 0 i) x-
    rareRepresentative τ σ 3 (cellWeight R 0 j) x) 2 (γFin d)≤_
  calc
    _ ≤ _ := by
      convert hh using 1
    _ ≤ ENNReal.ofReal (σ^3*(Real.exp C/(m:ℝ)))+ENNReal.ofReal (σ^3*(Real.exp C/(m:ℝ))) :=
      add_le_add (regular_rareRepresentative_norm R hG τ σ C hτ hτ1 hσ hσ1 hscale i)
        (regular_rareRepresentative_norm R hG τ σ C hτ hτ1 hσ hσ1 hscale j)
    _ = _ := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)];congr 1;ring

 theorem regularGapInput_average (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (τ σ : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hσ : 0<σ) (hσ1 : σ<1)
    (i j : Fin m) (x : FSC.Coord d) :
    ambientAverage τ (regularGapInput R τ σ i j) x=
      gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight R 0 i)) x.ofLp-
        gaussianAverage (-(τ^2*σ)) (highModes 3 (cellWeight R 0 j)) x.ofLp := by
  have hi := regular_rareRepresentative_regular R hG τ σ hτ hτ1 hσ hσ1 i
  have hj := regular_rareRepresentative_regular R hG τ σ hτ hτ1 hσ hσ1 j
  obtain ⟨Ci,hCi,hbi⟩ := hi.2.2.2
  obtain ⟨Cj,hCj,hbj⟩ := hj.2.2.2
  have hsub := gaussianAverage_sub_pointwise τ hτ hτ1 _ _ hi.2.1 hj.2.1
    hi.2.2.1 hj.2.2.1 Ci Cj hCi hCj hbi hbj
  have hlower : NegativeVotingCapTail.CenteredSingularLowerBound R 1 := by
    simpa only [one_smul] using regular_scaled_singular R hG 1
  rw [ambientAverage_eq_gaussianAverage]
  change gaussianAverage τ (rareRepresentative τ σ 3 (cellWeight R 0 i)-
    rareRepresentative τ σ 3 (cellWeight R 0 j)) x.ofLp=_
  rw [hsub,Pi.sub_apply,rareRepresentative_cell_factorization R 1 (by norm_num) hlower 0 i τ σ hτ hτ1 hσ hσ1 3 (by rfl),
    rareRepresentative_cell_factorization R 1 (by norm_num) hlower 0 j τ σ hτ hτ1 hσ hσ1 3 (by rfl)]

 theorem regularGapInput_average_odd (R : Fin m→FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (τ σ : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (hσ : 0<σ) (hσ1 : σ<1)
    (i j : Fin m) (hij : i≠j) (x : FSC.Coord d) :
    ambientAverage τ (regularGapInput R τ σ i j) (labelReflection R i j x)=
      -ambientAverage τ (regularGapInput R τ σ i j) x := by
  rw [regularGapInput_average R hG τ σ hτ hτ1 hσ hσ1,
    regularGapInput_average R hG τ σ hτ hτ1 hσ hσ1]
  exact highModes_average_gap_odd R (1/(m:ℝ)) hG i j hij (-(τ^2*σ)) x.ofLp
end NegativeVotingRegularHighTailInputs
