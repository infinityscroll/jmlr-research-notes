import GaussianFanRetainedGap
import GaussianTailRatio

/-! The retained facet-coefficient ceiling follows from actual cell masses,
edge lengths and the literal intrinsic Gaussian facet normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace ENNReal NNReal
namespace NegativeVotingFanRetained
open NegativeVotingFan NegativeVotingFanJacobian NegativeVotingFanBoundary
  NegativeVotingFanCycle NegativeVotingFanCycleBridge NegativeVotingWeightedFacet
  NegativeVotingFanCovarianceEnvelope NegativeVotingFanCanonicalOffset
  NegativeVotingCovarianceMixed NegativeVotingFan NegativeVotingFacetDegree
  NegativeVotingCapTail NegativeVotingGaussianTail WeakSimplex NegativeVotingDisintegration
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem gaussian_unit_lower_halfspace (w : FSC.Coord d) (hw : ‖w‖=1) (q : ℝ) :
    (stdGaussian (FSC.Coord d) {x | inner ℝ w x  ≤  q}).toReal=normalCDF q := by
  have hm : (stdGaussian (FSC.Coord d)).map (fun x => inner ℝ w x)=gaussianReal 0 1 := by
    simpa only [hw,one_pow,Real.toNNReal_one] using gaussian_inner_map w
  have he : stdGaussian (FSC.Coord d) {x | inner ℝ w x  ≤  q}=gaussianReal 0 1 (Iic q) := by
    rw [← hm,Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  rw [he,← normalCDF_eq_measure_Iic,ENNReal.toReal_ofReal (normalCDF_pos q).le]

/-- A winning cell is contained in its genuine comparison halfspace. -/
theorem cell_mass_le_pair_tail (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (i j : V) (hij : i≠j) :
    mass B h i  ≤  normalCDF (-pairOffset B h i j) := by
  have hs : winningCell B h i ⊆
      {x | inner ℝ (pairNormal B j i) x  ≤  pairOffset B h j i} := by
    intro x hx
    exact (cell_halfspace_iff_score B h i ⟨j,hij.symm⟩ (hinj.ne hij.symm) x).mpr (hx j)
  calc
    _ = (stdGaussian (FSC.Coord d) (winningCell B h i)).toReal :=
      mass_eq_winningCell B hinj h i
    _  ≤  (stdGaussian (FSC.Coord d)
        {x | inner ℝ (pairNormal B j i) x  ≤  pairOffset B h j i}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hs)
    _ = normalCDF (pairOffset B h j i) :=
      gaussian_unit_lower_halfspace _ (pairNormal_norm B j i (hinj.ne hij.symm)) _
    _ = _ := by rw [pairOffset_reverse]

/-- Both cell-mass lower bounds control the actual normalized pair offset. -/
theorem pairOffset_sq_le_log_mass (B : V → FSC.Coord d) (h : V → ℝ)
    (hinj : Function.Injective B) (p0 : ℝ) (hp0 : 0<p0)
    (hmass : ∀i,p0  ≤  mass B h i) (i j : V) (hij : i≠j) :
    (pairOffset B h i j)^2  ≤  2*Real.log (1/p0) := by
  let q := pairOffset B h i j
  have hm : p0  ≤  normalCDF (-|q|) := by
    by_cases hq : 0  ≤  q
    · simpa only [abs_of_nonneg hq] using (hmass i).trans (cell_mass_le_pair_tail B h hinj i j hij)
    · have hh := (hmass j).trans (cell_mass_le_pair_tail B h hinj j i hij.symm)
      rw [pairOffset_reverse B h i j,neg_neg] at hh
      change p0  ≤  normalCDF q at hh
      simpa only [abs_of_neg (lt_of_not_ge hq),neg_neg] using hh
  have ht := hm.trans (normalTail_le_half_exp |q| (abs_nonneg q))
  have he : p0  ≤  Real.exp (-q^2/2) := by
    rw [sq_abs] at ht
    nlinarith [Real.exp_pos (-q^2/2)]
  have hl := Real.log_le_log hp0 he
  rw [Real.log_exp] at hl
  rw [one_div,Real.log_inv]
  change q^2  ≤  _
  nlinarith

/-- The coordinate-cap probability in the refined Hessian has exactly the
same density normalization as the actual analytic facet weight. -/
theorem facetWeight_eq_cycle_density (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) (hij : i≠j) :
    facetWeight b h i j = gaussianPDFReal 0 1 (pairOffset b h i j)/‖b i-b j‖*
      cycleIntrinsicProbability b h i j := by
  rw [← cycleEdgeWeight_eq_facetWeight b h i j hij,cycleEdgeWeight,if_neg hij,
    stratumMassAt,stratumDensityFactor_pair b h i j hij]
  unfold cycleIntrinsicProbability
  ring

theorem cycleProbability_eq_intrinsic_facet (b : AffineBasis V ℝ (FSC.Coord d))
    (h : V → ℝ) (i j : V) (hij : i≠j) :
    cycleIntrinsicProbability b h i j =
      (stdGaussian (tangentSpace (pairNormal b i j)) (intrinsicFacet b h i j)).toReal := by
  have hp : gaussianPDFReal 0 1 (pairOffset b h i j)≠0 := (normalPDF_pos _).ne'
  have he : ‖b i-b j‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (b.ind.injective.ne hij))
  apply mul_left_cancel₀ (div_ne_zero hp he)
  rw [← facetWeight_eq_cycle_density b h i j hij]
  rfl

/-- A retained intrinsic facet has a quantitatively positive true Gaussian
probability; this uses the actual density ceiling, not an assumed facet mass. -/
theorem retained_intrinsic_probability_lower (B : V → FSC.Coord d) (h : V → ℝ)
    (τ ellMin : ℝ) (hτ : 0<τ) (hell : 0<ellMin) (i j : V)
    (hedge : ellMin  ≤  ‖B i-B j‖) (hret : τ  ≤  facetWeight B h i j) :
    Real.sqrt (2*Real.pi)*τ*ellMin  ≤ 
      (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal := by
  let p := (stdGaussian (tangentSpace (pairNormal B i j)) (intrinsicFacet B h i j)).toReal
  let c := Real.sqrt (2*Real.pi)
  have hc : 0<c := by dsimp [c];positivity
  have he : 0<‖B i-B j‖ := hell.trans_le hedge
  have hd : gaussianPDFReal 0 1 (pairOffset B h i j)  ≤  c⁻¹ := by
    simpa only [NNReal.coe_one,mul_one,c] using gaussian_density_le_normalizer 0 1 (pairOffset B h i j)
  have hp : 0  ≤  p := ENNReal.toReal_nonneg
  have hr : τ  ≤  gaussianPDFReal 0 1 (pairOffset B h i j)*p/‖B i-B j‖ := by
    convert hret using 1 <;> unfold facetWeight p <;> ring
  have hb := (le_div_iff₀ he).mp hr
  have hm := mul_le_mul_of_nonneg_right hd hp
  have hl := mul_le_mul_of_nonneg_left hedge hτ.le
  have hpc : τ*ellMin  ≤  p/c := by
    rw [div_eq_mul_inv]
    nlinarith
  have hh := (le_div_iff₀ hc).mp hpc
  change c*τ*ellMin  ≤  p
  nlinarith


/-- A nonnegative explicit ceiling; the logarithmic clips vanish on the
small-mass regime. They avoid assuming that some edge is retained merely
to certify the sign of the global scalar constant. -/
def retainedCoefficientCeiling (p0 τ ellMin : ℝ) : ℝ :=
  2*Real.exp 4*(1+2*max (Real.log (1/(Real.sqrt (2*Real.pi)*τ*ellMin))) 0)+
    2*max (Real.log (1/p0)) 0

theorem retainedCoefficientCeiling_pos (p0 τ ellMin : ℝ) :
    0<retainedCoefficientCeiling p0 τ ellMin := by
  unfold retainedCoefficientCeiling
  positivity

theorem inverse_facetLogCoefficient (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ)
    (i j : V) :
    1/facetLogCoefficient b h i j =
      2*Real.exp 4*(1+2*Real.log (1/cycleIntrinsicProbability b h i j)) := by
  simp only [facetLogCoefficient,one_div,inv_div,div_eq_mul_inv,Real.exp_neg,mul_inv_rev,inv_inv,one_mul]
  ring

/-- The exact coefficient appearing in the refined covariance Hessian has
an explicit ceiling obtained from actual masses, edge lengths and retention. -/
theorem actual_retained_coefficient_le
    (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ) (hcard : 3 ≤ Fintype.card V)
    (p0 τ ellMin : ℝ) (hp0 : 0<p0) (hτ : 0<τ) (hell : 0<ellMin)
    (hmass : ∀i,p0 ≤ mass b h i) (hedge : ∀i j,i≠j→ellMin ≤ ‖b i-b j‖)
    (i j : V) (hij : i≠j) (hret : τ ≤ facetWeight b h i j) :
    1/facetLogCoefficient b h i j+(pairOffset b h i j)^2 ≤ 
      retainedCoefficientCeiling p0 τ ellMin := by
  let a := Real.sqrt (2*Real.pi)*τ*ellMin
  have ha : 0<a := by dsimp [a];positivity
  have hp := cycleIntrinsicProbability_mem_Ioo b h hcard i j
  have hlower : a ≤ cycleIntrinsicProbability b h i j := by
    rw [cycleProbability_eq_intrinsic_facet b h i j hij]
    exact retained_intrinsic_probability_lower b h τ ellMin hτ hell i j (hedge i j hij) hret
  have hlog : Real.log (1/cycleIntrinsicProbability b h i j) ≤ max (Real.log (1/a)) 0 :=
    (Real.log_le_log (one_div_pos.mpr hp.1)
      (one_div_le_one_div_of_le ha hlower)).trans (le_max_left _ _)
  have hq := pairOffset_sq_le_log_mass b h b.ind.injective p0 hp0 hmass i j hij
  have hq' : (pairOffset b h i j)^2 ≤ 2*max (Real.log (1/p0)) 0 :=
    hq.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  rw [inverse_facetLogCoefficient]
  unfold retainedCoefficientCeiling
  change 2*Real.exp 4*(1+2*Real.log (1/cycleIntrinsicProbability b h i j))+
    (pairOffset b h i j)^2 ≤ 2*Real.exp 4*(1+2*max (Real.log (1/a)) 0)+
      2*max (Real.log (1/p0)) 0
  nlinarith [Real.exp_pos 4]

/-- Fully concrete mixed-curvature control: neither a retained spectral gap
nor a facet-coefficient ceiling is supplied as a premise. Only actual cell,
edge, degree and threshold bounds remain to be specialized to the mass window. -/
theorem canonicalOffset_control_from_mass_edge_geometry
    (b : AffineBasis V ℝ (FSC.Coord d)) (h : V → ℝ) (hcard : 3 ≤ Fintype.card V)
    (H : FSC.Coord d →L[ℝ] FSC.Coord d) (p0 ellMin ellMax τ D : ℝ)
    (hp0 : 0<p0) (hmin : 0<ellMin) (hmax : 0<ellMax) (hτ : 0<τ) (hDpos : 0<D)
    (hmass : ∀i,p0 ≤ mass b h i)
    (hedgeMin : ∀i j,i≠j→ellMin ≤ ‖b i-b j‖)
    (hedgeMax : ∀i j,i≠j→‖b i-b j‖ ≤ ellMax)
    (hD : ∀i,(∑j,facetWeight b h i j) ≤ D)
    (ht : τ*(Fintype.card V:ℝ) ≤ (p0/(2*Real.pi*ellMax))/2) :
    retainedGapCoefficient p0 ellMax D*
      (∑i,(canonicalOffsetVariation b h (rowsOfOperator b H) i/2)^2) ≤ 
        retainedCoefficientCeiling p0 τ ellMin*(-covarianceHessianValue b h H) :=
  canonicalOffset_control_from_actual_graph b h hcard H p0 ellMax τ D _
    hp0.le hmax hτ.le hDpos (retainedCoefficientCeiling_pos p0 τ ellMin).le
    hmass hedgeMax hD ht
    (actual_retained_coefficient_le b h hcard p0 τ ellMin hp0 hτ hmin hmass hedgeMin)

end NegativeVotingFanRetained
