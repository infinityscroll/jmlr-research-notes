import GaussianBoundedOUCellTests
import GaussianQuadraticMomentPadding

/-! Pointwise continuous OU representatives for actual Gaussian winning
cells. This permits subsequent use on facets without restricting an
ambient almost-everywhere identity. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Filter Set
open scoped ENNReal BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingCellOUContinuity
open NegativeVoting NegativeVotingFan NegativeVotingFanJacobian NegativeVotingCapTail
  NegativeVotingFacetDegree NegativeVotingQuadraticMomentPadding
  NegativeVotingBoundedOUCellTests NegativeVotingHypercontractivity
  NegativeVotingProjection NegativeVotingRareLabelHighChaos
  OAI.MinUncut.GaussianHermite NegativeVotingModern
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem gaussianAverage_euclidean (ρ : ℝ) (f : (Fin d→ℝ)→ℝ) (x : FSC.Coord d) :
    gaussianAverage ρ f (fun j=>x j)=
      ∫ y : FSC.Coord d,f (fun j=>(ρ•x+Real.sqrt (1-ρ^2)•y) j) ∂stdGaussian (FSC.Coord d) := by
  unfold gaussianAverage
  change (∫ y,f (fun j=>ρ*x j+Real.sqrt (1-ρ^2)*y j) ∂NegativeVoting.standardGaussian (Fin d))=_
  rw [integral_standardGaussian_eq_euclidean]
  rfl

theorem cellWeight_affine (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι)
    (ρ s : ℝ) (hs : 0 < s) (x y : FSC.Coord d) :
    cellWeight B h i (fun j=>(ρ•x+s•y) j)=
      (winningCell B (fun j=>(h j+ρ*inner ℝ (B j) x)/s) i).indicator (fun _=>1) y := by
  have hm : (ρ•x+s•y)∈winningCell B h i ↔
      y∈winningCell B (fun j=>(h j+ρ*inner ℝ (B j) x)/s) i := by
    simp only [winningCell,Set.mem_setOf_eq,scores,inner_add_right,inner_smul_right]
    constructor <;> intro hy j
    · have hj := hy j
      apply (mul_le_mul_iff_left₀ hs).mp
      field_simp
      linarith
    · have hj := hy j
      have hh := (mul_le_mul_iff_left₀ hs).mpr hj
      field_simp at hh
      linarith
  unfold cellWeight
  have hx : WithLp.toLp 2 (fun j=>(ρ•x+s•y) j)=ρ•x+s•y := rfl
  rw [hx]
  by_cases hy : y∈winningCell B (fun j=>(h j+ρ*inner ℝ (B j) x)/s) i
  · simp only [Set.indicator_of_mem hy,Set.indicator_of_mem (hm.mpr hy)]
  · simp only [Set.indicator_of_notMem hy,Set.indicator_of_notMem (fun hh=>hy (hm.mp hh))]

theorem gaussianAverage_cellWeight_eq_mass (B : ι→FSC.Coord d) (hB : Function.Injective B)
    (h : ι→ℝ) (i : ι) (ρ : ℝ) (hρ : |ρ| < 1) (x : FSC.Coord d) :
    gaussianAverage ρ (cellWeight B h i) (fun j=>x j)=
      mass B (fun j=>(h j+ρ*inner ℝ (B j) x)/Real.sqrt (1-ρ^2)) i := by
  have hs : 0 < Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr (by
    have hh := abs_lt.mp hρ;nlinarith)
  rw [gaussianAverage_euclidean]
  simp only [cellWeight_affine B h i ρ _ hs x]
  rw [integral_indicator (winningCell_measurable B _ i),integral_const]
  rw [mass_eq_winningCell B hB]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]

theorem gaussianAverage_cellWeight_continuous (B : ι→FSC.Coord d)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (h : ι→ℝ) (i : ι) (ρ : ℝ) (hρ : |ρ| < 1) :
    Continuous (gaussianAverage ρ (cellWeight B h i)) := by
  have hB : Function.Injective B := fun i j he=>by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  have hmass : Continuous (fun h':ι→ℝ=>mass B h' i) :=
    continuous_iff_continuousAt.mpr (fun h'=>(hasFDerivAt_mass B σ hσ hlower h' i).continuousAt)
  have he : gaussianAverage ρ (cellWeight B h i)=fun x:Fin d→ℝ=>
      mass B (fun j=>(h j+ρ*inner ℝ (B j) (WithLp.toLp 2 x))/Real.sqrt (1-ρ^2)) i := by
    funext x
    exact gaussianAverage_cellWeight_eq_mass B hB h i ρ hρ (WithLp.toLp 2 x)
  rw [he]
  exact hmass.comp (by fun_prop)

/-- Continuous quadratically growing functions remain continuous under the
literal OU integral. Only this qualitative step may use a dimension-dependent
dominating function; subsequent quantitative estimates use the trace theorem. -/
theorem gaussianAverage_continuous_quadratic (ρ : ℝ) (f : (Fin d→ℝ)→ℝ)
    (hf : Continuous (fun x:FSC.Coord d=>f (fun j=>x j)))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x:FSC.Coord d,|f (fun j=>x j)| ≤ C*(1+‖x‖^2)) :
    Continuous (gaussianAverage ρ f) := by
  have he : (fun x:FSC.Coord d=>gaussianAverage ρ f (fun j=>x j))=
      fun x:FSC.Coord d=>∫ y:FSC.Coord d,
        f (fun j=>(ρ•x+Real.sqrt (1-ρ^2)•y) j) ∂stdGaussian (FSC.Coord d) :=
    funext (gaussianAverage_euclidean ρ f)
  have hc : Continuous (fun x:FSC.Coord d=>gaussianAverage ρ f (fun j=>x j)) := by
    rw [he]
    apply continuous_iff_continuousAt.mpr
    intro x₀
    let a := |ρ| *(‖x₀‖+1)
    let s := Real.sqrt (1-ρ^2)
    let g : FSC.Coord d→ℝ := fun y=>C*(1+2*a^2+2*s^2*‖y‖^2)
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hi : Integrable (fun y:FSC.Coord d=>‖y‖^2) (stdGaussian (FSC.Coord d)) :=
      IsGaussian.memLp_two_id.integrable_norm_pow'
    apply continuousAt_of_dominated (bound:=g)
    · exact Filter.Eventually.of_forall (fun x=>
        (hf.comp (by fun_prop)).measurable.aestronglyMeasurable)
    · have hx : ∀ᶠ x:FSC.Coord d in 𝓝 x₀,‖x‖ < ‖x₀‖+1 :=
        continuous_norm.continuousAt.eventually (gt_mem_nhds (by linarith))
      filter_upwards [hx] with x hx
      exact Filter.Eventually.of_forall (fun y=>by
        have hn : ‖ρ•x+s•y‖ ≤ a+s*‖y‖ := by
          calc
            _ ≤ ‖ρ•x‖+‖s•y‖ := norm_add_le _ _
            _ = |ρ| *‖x‖+s*‖y‖ := by simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
            _ ≤ a+s*‖y‖ := by dsimp [a];gcongr
        have ha : 0 ≤ a := by dsimp [a];positivity
        have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        have hq : ‖ρ•x+s•y‖^2 ≤ 2*a^2+2*s^2*‖y‖^2 := by
          nlinarith [sq_nonneg (a-s*‖y‖)]
        have hb := (hbound (ρ•x+s•y)).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hq) hC)
        simpa only [g,s,Real.norm_eq_abs,add_assoc] using hb)
    · exact ((integrable_const (1+2*a^2)).add (hi.const_mul (2*s^2))).const_mul C
    · exact Filter.Eventually.of_forall (fun y=>(hf.comp (by fun_prop)).continuousAt)
  have hh := hc.comp (PiLp.continuous_toLp 2 (fun _ : Fin d=>ℝ))
  exact hh

/-- Low-mode subtraction is pointwise, so an actual continuous OU average of
a bounded measurable input supplies a continuous quadratic test. -/
theorem highModes_continuous_quadratic_of_average (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (k : ℕ) (hk : k ≤ 3) (f : (Fin d→ℝ)→ℝ) (hfM : Measurable f)
    (hc : Continuous (gaussianAverage ρ f)) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x,|f x| ≤ M) :
    Continuous (fun x:FSC.Coord d=>gaussianAverage ρ (highModes k f) (fun j=>x j)) ∧
    ∃ C:ℝ,0 ≤ C ∧ ∀ x:FSC.Coord d,
      |gaussianAverage ρ (highModes k f) (fun j=>x j)| ≤ C*(1+‖x‖^2) := by
  have he := gaussianAverage_highModes_bounded ρ hρ k f hfM M hM
  have hg : Continuous (gaussianAverage ρ (highModes k f)) := by
    have hh : Continuous (fun x:Fin d→ℝ=>gaussianAverage ρ f x-
        ∑ b∈lowerModes k,ρ^(degree b)*coeff f b*psi b x) := hc.sub (continuous_finsetSum (lowerModes k)
      (fun b _=>continuous_const.mul (continuous_psi b)))
    convert hh using 1
    funext x
    exact he x
  refine ⟨hg.comp (by fun_prop),?_⟩
  let C := M+∑ b∈lowerModes k,|ρ^(degree b)*coeff f b|
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro x
  rw [he]
  have hp : |∑ b∈lowerModes k,ρ^(degree b)*coeff f b*psi b (fun j=>x j)| ≤
      (∑ b∈lowerModes k,|ρ^(degree b)*coeff f b|)*(1+‖x‖^2) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b hb
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (psi_low_degree_growth b (lt_of_lt_of_le ((mem_lowerModes_iff k b).mp hb) hk) x)
      (abs_nonneg _)
  have hb := gaussianAverage_abs_le_bounded ρ f M hM (fun j=>x j)
  have ha := abs_sub (gaussianAverage ρ f (fun j=>x j))
    (∑ b∈lowerModes k,ρ^(degree b)*coeff f b*psi b (fun j=>x j))
  dsimp only [C]
  nlinarith [mul_nonneg hM0 (sq_nonneg ‖x‖)]

theorem cellWeight_measurable (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) :
    Measurable (cellWeight B h i) :=
  (measurable_const.indicator (winningCell_measurable B h i)).comp (by fun_prop)

theorem cellWeight_abs_le (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) (x : Fin d→ℝ) :
    |cellWeight B h i x| ≤ 1 := by
  unfold cellWeight
  by_cases hx : WithLp.toLp 2 x∈winningCell B h i <;> simp [hx]

theorem cellWeight_memLp (B : ι→FSC.Coord d) (h : ι→ℝ) (i : ι) :
    MemLp (cellWeight B h i) 2 (γFin d) := by
  apply MemLp.of_bound (cellWeight_measurable B h i).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x=>by simpa only [Real.norm_eq_abs] using cellWeight_abs_le B h i x)

/-- The rare-label factorization is an equality at EVERY point for actual
nondegenerate winning cells, hence safe to use on any current facet. -/
theorem rareRepresentative_cell_factorization (B : ι→FSC.Coord d)
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (hlower : CenteredSingularLowerBound B σ₀)
    (h : ι→ℝ) (i : ι) (τ σ : ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hσ : 0 < σ) (hσ1 : σ < 1)
    (k : ℕ) (hk : k ≤ 3) :
    gaussianAverage τ (rareRepresentative τ σ k (cellWeight B h i))=
      gaussianAverage (-(τ^2*σ)) (highModes k (cellWeight B h i)) := by
  let f := cellWeight B h i
  have hfM := cellWeight_measurable B h i
  have hf := cellWeight_memLp B h i
  have hτa : |τ| < 1 := by rwa [abs_of_pos hτ]
  have hσa : |-σ| ≤ 1 := by rw [abs_neg,abs_of_pos hσ];exact hσ1.le
  have hpa : |-(τ^2*σ)| < 1 := by
    rw [abs_neg,abs_of_nonneg (by positivity)]
    nlinarith [mul_pos (sq_pos_of_pos hτ) hσ]
  have hcτ := gaussianAverage_cellWeight_continuous B σ₀ hσ₀ hlower h i τ hτa
  have hτbound : ∀ x,|gaussianAverage τ f x| ≤ 1 :=
    gaussianAverage_abs_le_bounded τ f 1 (cellWeight_abs_le B h i)
  have hv := gaussianAverage_highModes_continuous_quadratic (-σ) hσa k hk
    (gaussianAverage τ f) hcτ 1 (by norm_num) hτbound
  obtain ⟨C,hC,hCv⟩ := hv.2
  have hleft : Continuous (gaussianAverage τ (rareRepresentative τ σ k f)) :=
    gaussianAverage_continuous_quadratic τ _ hv.1 C hC hCv
  have hright' := highModes_continuous_quadratic_of_average (-(τ^2*σ)) hpa.le k hk f hfM
    (gaussianAverage_cellWeight_continuous B σ₀ hσ₀ hlower h i _ hpa)
    1 (by norm_num) (cellWeight_abs_le B h i)
  have hright : Continuous (gaussianAverage (-(τ^2*σ)) (highModes k f)) :=
    hright'.1.comp (PiLp.continuous_toLp 2 (fun _ : Fin d=>ℝ))
  letI : (gaussianReal 0 1).IsOpenPosMeasure := GaussianFin.instIsOpenPosMeasureγ
  letI : (γFin d).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure (fun _ : Fin d=>gaussianReal 0 1)
  exact (Continuous.ae_eq_iff_eq (γFin d) hleft hright).mp
    (rareRepresentative_factorization τ σ hτ hτ1 hσ hσ1 k f hfM hf)

end NegativeVotingCellOUContinuity
