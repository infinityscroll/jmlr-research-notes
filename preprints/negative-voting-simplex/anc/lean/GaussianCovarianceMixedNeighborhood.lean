import GaussianCovarianceUniformMixed
import GaussianCovarianceJointValueC2

/-! Actual open mixed-curvature control near each small-floor optimizer.
Degrees are intrinsic Price derivatives, so no factor-continuity or facet-
continuity hypothesis is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace NNReal
namespace NegativeVotingCovarianceMixedNeighborhood
open NegativeVotingCovarianceUniformMixed NegativeVotingOptimizerConstants
  NegativeVotingCovarianceBoundary NegativeVotingCovarianceOptimizer
  NegativeVotingPositiveCovariance NegativeVotingLocalCovarianceFactor
  NegativeVotingFanInverse NegativeVotingCovarianceJointValueC2
  NegativeVotingCovarianceConcavity NegativeVotingCovarianceStrict
  NegativeVotingCovarianceOffsets NegativeVotingCovariancePrice
  NegativeVotingCovarianceOptimizerDegree NegativeVotingFanMassContinuity
  NegativeVotingFanSelectedOffsets NegativeVotingFanJacobian
variable {m d : ℕ} [NeZero m]

abbrev CovarianceMassCoordinates (m d : ℕ) :=
  SymmetricOperators (FSC.Coord d) × centeredGauge (Fin m)

def chartValue (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (q : CovarianceMassCoordinates m d) : ℝ :=
  operatorValue b (p+(q.2 : Fin m→ℝ)) q.1

def labelRankOne (b : Fin m→FSC.Coord d) (i : Fin m) : SymmetricOperators (FSC.Coord d) :=
  ⟨rankOne (b i),ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (rankOne_psd (b i)).1⟩

def chartDegree (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (q : CovarianceMassCoordinates m d) (i : Fin m) : ℝ :=
  2*(fderiv ℝ (chartValue b p) q) (labelRankOne b i,0)

/-- Positive definiteness is open in the actual symmetric covariance space.
The smooth row factor is used only here to obtain local invertibility. -/
theorem eventually_pdCone (C0 : SymmetricOperators (FSC.Coord d))
    (hC0 : (C0 : FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone) :
    ∀ᶠ C : SymmetricOperators (FSC.Coord d) in 𝓝 C0,
      (C : FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone := by
  obtain ⟨R,A,hR,hRi,hRC,hA0,hAC,hGram⟩ := exists_local_smooth_covariance_factor C0 hC0
  have hunit0 : IsUnit (A C0) := by
    rw [hA0]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr R.bijective
  have hu : ∀ᶠ C in 𝓝 C0,IsUnit (A C) := hAC.continuousAt.eventually (Units.isOpen.mem_nhds hunit0)
  filter_upwards [hu,hGram] with C hU hGramC
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp C.property,?_⟩
  intro x hx
  rw [←hGramC x x,real_inner_self_eq_norm_sq]
  apply sq_pos_of_ne_zero
  apply norm_ne_zero_iff.mpr
  intro hAx
  apply hx
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hU).1
  simpa using hAx

theorem chartDegree_continuousAt
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (q : CovarianceMassCoordinates m d)
    (hF : ContDiffAt ℝ 2 (chartValue b p) q) (i : Fin m) :
    ContinuousAt (fun z => chartDegree b p z i) q := by
  have hc := hF.continuousAt_fderiv (by norm_num)
  exact continuousAt_const.mul (hc.clm_apply continuousAt_const)

/-- A literal facet degree equals twice the covariance derivative of Γ in
its reference rank-one direction. The identity holds for every symmetric
invertible factor with the prescribed square. -/
theorem chartDegree_eq_facetDegree
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (p : Fin m→ℝ) (q : CovarianceMassCoordinates m d)
    (hp : ∀ i,0 < (p+(q.2 : Fin m→ℝ)) i)
    (hs : ∑ i,(p+(q.2 : Fin m→ℝ)) i=1)
    (hF : DifferentiableAt ℝ (chartValue b p) q)
    (R : FSC.Coord d≃L[ℝ]FSC.Coord d)
    (hR : R.toLinearMap.IsSymmetric) (hRi : R.symm.toLinearMap.IsSymmetric)
    (hRC : R.toContinuousLinearMap.comp R.toContinuousLinearMap=(q.1 : FSC.Coord d→L[ℝ]FSC.Coord d))
    (i : Fin m) :
    chartDegree b p q i=∑ j,facetWeight (mappedBasis b R)
      (selectedOffsets (mappedBasis b R) (p+(q.2 : Fin m→ℝ))) i j := by
  let D := labelRankOne b i
  let l : ℝ → CovarianceMassCoordinates m d := fun t => (q.1+t • D,q.2)
  have hl : HasDerivAt l (D,0) 0 := by
    simpa only [l,one_smul,id_eq] using
      (((hasDerivAt_id (0:ℝ)).smul_const D).const_add q.1).prodMk (hasDerivAt_const (0:ℝ) q.2)
  have hFD : HasFDerivAt (chartValue b p) (fderiv ℝ (chartValue b p) q) (l 0) := by
    simpa only [l,zero_smul,add_zero,Prod.eta] using hF.hasFDerivAt
  have hh := hFD.comp_hasDerivAt 0 hl
  have hd : HasDerivAt
      (fun t : ℝ => operatorValue b (p+(q.2 : Fin m→ℝ))
        ((q.1 : FSC.Coord d→L[ℝ]FSC.Coord d)+t • rankOne (b i)))
      ((fderiv ℝ (chartValue b p) q) (D,0)) 0 := by
    simpa only [chartValue,l,D,labelRankOne,Function.comp_def,Submodule.coe_add,Submodule.coe_smul] using hh
  have hpD := hasDerivAt_operatorValue_factor b _ hp hs q.1 (rankOne (b i)) R hR hRi hRC (rankOne_psd (b i)).1
  have heq := hd.unique hpD
  have hsum := parseval_rankOne_edge_degree b hG (mappedBasis b R)
    (selectedOffsets (mappedBasis b R) (p+(q.2 : Fin m→ℝ))) i
  change 2*((fderiv ℝ (chartValue b p) q) (D,0))=_
  rw [heq]
  linarith

/-- Every actual small-floor optimizer has a neighborhood where the same
absolute logarithmic-square mixed bound holds for all symmetric directions.
The neighborhood is in covariance and centered-mass coordinates jointly. -/
theorem uniform_optimizer_mixed_neighborhood
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (hG : ∀ i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/(m:ℝ))
    (hP : ∀ x,(∑ i,inner ℝ (b i) x • b i)=x)
    (hdim : 2 ≤ d) (hm : numericThreshold ≤ m) :
    ∃ δ : ℝ,0 < δ ∧ ∀ ε : ℝ,0 < ε → ε < δ →
      ∀ p : PositiveMassVector (Fin m),p∈positiveMassBox (actualMassLower (m:ℝ)) (2/(m:ℝ)) →
      ∀ C0 : SymmetricOperators (FSC.Coord d),
      (C0 : FSC.Coord d→L[ℝ]FSC.Coord d)∈lowerCovarianceCone ε →
      IsMaxOn (penalizedValue b p) (lowerCovarianceCone ε) (C0 : FSC.Coord d→L[ℝ]FSC.Coord d) →
      ∀ᶠ q : CovarianceMassCoordinates m d in 𝓝 (C0,0),
        (∀ i,0 < ((p:Fin m→ℝ)+(q.2 : Fin m→ℝ)) i) ∧
        (q.1 : FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone ∧
        ∀ A : FSC.Coord d→L[ℝ]FSC.Coord d,A.toLinearMap.IsSymmetric →
          (∑ i,(deriv (fun t : ℝ => (operatorOffsets b ((p:Fin m→ℝ)+(q.2 : Fin m→ℝ))
            ((q.1 : FSC.Coord d→L[ℝ]FSC.Coord d)+t • A) : Fin m→ℝ)) 0 i)^2) ≤
          mixedConstant*(1+Real.log (m:ℝ))^2 *
            (-deriv (deriv (fun t : ℝ => operatorValue b ((p:Fin m→ℝ)+(q.2 : Fin m→ℝ))
              ((q.1 : FSC.Coord d→L[ℝ]FSC.Coord d)+t • A))) 0) := by
  obtain ⟨hm3,_,_⟩ := numericThreshold_spec m hm
  have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : 0 < (m:ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hpActual : 0 < actualMassLower (m:ℝ) := by unfold actualMassLower; positivity
  have hpRelax : 0 < massLower (m:ℝ) := (scalar_positive (m:ℝ) hm0).1
  have hslack : massLower (m:ℝ) < actualMassLower (m:ℝ) := by
    unfold massLower actualMassLower
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  have hminEq : edgeLower (m:ℝ)=Real.sqrt (2*Real.pi)*(actualMassLower (m:ℝ))^2/2 := by
    dsimp [edgeLower,actualMassLower]
    field_simp
    <;> ring
  obtain ⟨δ,hδ,hgeometry⟩ := uniform_small_floor_edge_bounds b hG hP hdim
    (actualMassLower (m:ℝ)) (m:ℝ) 2 hpActual hm1 (by norm_num)
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ p hp C0 hC0 hopt
  have hpd : (C0 : FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone := lowerCovarianceCone_subset_pd hε hC0
  have hF : ContDiffAt ℝ 2 (chartValue b p) (C0,0) := operatorValue_joint_C2 b p p.property.1 p.property.2 C0 hpd
  have hdiff : ∀ᶠ q in 𝓝 (C0,(0:centeredGauge (Fin m))),DifferentiableAt ℝ (chartValue b p) q :=
    (hF.eventually (by norm_num)).mono (fun q hq => (hq.of_le (m:=1) (by norm_num)).differentiableAt_one)
  have hpdNear : ∀ᶠ q : CovarianceMassCoordinates m d in 𝓝 (C0,0),
      (q.1 : FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone :=
    (continuous_fst.tendsto (C0,(0:centeredGauge (Fin m)))).eventually (eventually_pdCone C0 hpd)
  let Cpsd : PSDCovariance d := ⟨C0,pdCone_subset_psdCone hpd⟩
  let εnn : ℝ≥0 := ⟨ε,hε.le⟩
  have hs0 : IsOptimizerState b (εnn,(p,Cpsd)) := ⟨hC0,hopt⟩
  have hedges0 := hgeometry εnn hεδ p hp Cpsd hs0
  obtain ⟨R0,hR0,hRi0,hRC0,hdegree0⟩ := exists_optimizer_factor_degree_le_one b hG p
    p.property.1 p.property.2 ε hε C0 hC0 hopt
  have hdeg0 (i : Fin m) : chartDegree b p (C0,0) i ≤ 1 := by
    have he := chartDegree_eq_facetDegree b hG p (C0,0)
      (by simpa using p.property.1) (by simpa using p.property.2)
      ((hF.of_le (m:=1) (by norm_num)).differentiableAt_one) R0 hR0 hRi0 hRC0 i
    simp only [Submodule.coe_zero,add_zero] at he
    exact he.trans_le (hdegree0 i)
  have hdegrees : ∀ᶠ q in 𝓝 (C0,(0:centeredGauge (Fin m))),∀ i,chartDegree b p q i < 2 := by
    apply eventually_all.mpr
    intro i
    exact (chartDegree_continuousAt b p (C0,0) hF i).eventually (Iio_mem_nhds (lt_of_le_of_lt (hdeg0 i) (by norm_num)))
  have hmasses : ∀ᶠ q : CovarianceMassCoordinates m d in 𝓝 (C0,0),
      ∀ i,massLower (m:ℝ) < ((p:Fin m→ℝ)+(q.2 : Fin m→ℝ)) i := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun q : CovarianceMassCoordinates m d =>
        ((p:Fin m→ℝ)+(q.2 : Fin m→ℝ)) i) (C0,0) := by fun_prop
    exact hc.eventually (Ioi_mem_nhds (by simpa using hslack.trans_le (hp i).1))
  have hedges : ∀ᶠ q : CovarianceMassCoordinates m d in 𝓝 (C0,0),
      ∀ i j,i≠j → edgeLower (m:ℝ) < operatorEdgeLength b q.1 i j ∧
        operatorEdgeLength b q.1 i j < edgeUpper (m:ℝ) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i=j
    · exact Eventually.of_forall (fun q h => False.elim (h hij))
    have hlo : edgeLower (m:ℝ) < operatorEdgeLength b C0 i j := by
      rw [hminEq]
      exact (hedges0 i j hij).1
    have hhi : operatorEdgeLength b C0 i j < edgeUpper (m:ℝ) := (hedges0 i j hij).2
    have hc : ContinuousAt (fun q : CovarianceMassCoordinates m d => operatorEdgeLength b q.1 i j) (C0,0) :=
      (continuous_operatorEdgeLength b i j).continuousAt.comp (continuousAt_subtype_val.comp continuousAt_fst)
    filter_upwards [hc.eventually (Ioo_mem_nhds hlo hhi)] with q hq
    exact fun _ => hq
  filter_upwards [hdiff,hpdNear,hdegrees,hmasses,hedges] with q hd hqpd hdeg hmass hedge
  have hpq : ∀ i,0 < ((p:Fin m→ℝ)+(q.2 : Fin m→ℝ)) i := fun i => hpRelax.trans (hmass i)
  have hsq : ∑ i,((p:Fin m→ℝ)+(q.2 : Fin m→ℝ)) i=1 := by
    have hz : ∑ i,(q.2 : Fin m→ℝ) i=0 := q.2.property
    simp only [Pi.add_apply,Finset.sum_add_distrib,p.property.2,hz,add_zero]
  refine ⟨hpq,hqpd,?_⟩
  intro A hA
  obtain ⟨R,hR,hRi,hRC⟩ := exists_positive_factor (q.1 : FSC.Coord d→L[ℝ]FSC.Coord d) hqpd
  have hnorm (i j : Fin m) : operatorEdgeLength b q.1 i j=‖mappedBasis b R i-mappedBasis b R j‖ :=
    operatorEdgeLength_eq_symmetric_factor_norm b q.1 R.toContinuousLinearMap hR hRC i j
  apply offset_derivative_bound_of_relaxed_geometry b hm _ hpq hsq q.1 A hA R hR hRi hRC
  · exact fun i => (hmass i).le
  · intro i j hij
    rw [←hnorm]
    exact (hedge i j hij).1.le
  · intro i j hij
    rw [←hnorm]
    exact (hedge i j hij).2.le
  · intro i
    rw [←chartDegree_eq_facetDegree b hG p q hpq hsq hd R hR hRi hRC i]
    exact (hdeg i).le

end NegativeVotingCovarianceMixedNeighborhood
