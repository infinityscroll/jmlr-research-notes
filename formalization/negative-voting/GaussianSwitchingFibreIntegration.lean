import GaussianSwitchingFibreGeometry

/-! Measurable Gaussian integration of actual old-cell switching fibres. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace BigOperators Classical ENNReal
namespace NegativeVotingSwitchingFibreIntegration
open NegativeVotingFan NegativeVotingSmallCap NegativeVotingSwitchingFibre
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual cell membership is part of the integrand, including its boundary. -/
theorem unitCellReward_measurable (B : V → E) (h : V → ℝ) (i j : V) (p n : E)
    (u : ((ℝ ∙ (B i-B j))ᗮ) → ℝ → ℝ) (a θ ell : ℝ)
    (hu : Measurable (Function.uncurry u)) :
    Measurable (fun y : ((ℝ ∙ (B i-B j))ᗮ) => unitCellReward B h i (p+(y:E)) n (u y) a θ ell) := by
  let T := (ℝ ∙ (B i-B j))ᗮ
  have hc : MeasurableSet {q : T×ℝ | p+(q.1:E)+q.2 • n ∈ affineCell B h i} :=
    ((isClosed_affineCell B h i).preimage (by fun_prop)).measurableSet
  have hp : Measurable (fun q : T×ℝ => gaussianPDFReal 0 1 (a+q.2)) := by
    have : Continuous (fun q : T×ℝ => gaussianPDFReal 0 1 (a+q.2)) := by
      unfold gaussianPDFReal
      fun_prop
    exact this.measurable
  have hu' : Measurable (fun q : T×ℝ => u q.1 q.2) := hu
  have hr : Measurable (fun q : T×ℝ =>
      gaussianPDFReal 0 1 (a+q.2)*fibreReward (θ*u q.1 q.2) ell q.2) := by
    unfold fibreReward
    exact hp.mul (((measurable_const.mul hu').sub
      (measurable_const.mul measurable_snd)).max measurable_const)
  have hi : Measurable (fun q : T×ℝ =>
      (cellFibreSet B h i (p+(q.1:E)) n).indicator (gaussianReward (u q.1) a θ ell) q.2) := by
    change Measurable (fun q : T×ℝ => if p+(q.1:E)+q.2 • n ∈ affineCell B h i then
      gaussianPDFReal 0 1 (a+q.2)*fibreReward (θ*u q.1 q.2) ell q.2 else 0)
    exact hr.ite hc measurable_const
  have hm := hi.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) 1))
  simpa only [unitCellReward,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hm.measurable

theorem unitCellReward_nonneg (B : V → E) (h : V → ℝ) (i : V) (p n : E)
    (u : ℝ → ℝ) (a θ ell : ℝ) :
    0 ≤ unitCellReward B h i p n u a θ ell := by
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num)
  intro z
  by_cases hz : z ∈ cellFibreSet B h i p n
  · simpa only [Set.indicator_of_mem hz] using gaussianReward_nonneg u a θ ell z
  · simp only [Set.indicator_of_notMem hz,le_refl]

theorem unitCellReward_le_supremum (B : V → E) (h : V → ℝ) (i : V) (p n : E)
    (u : ℝ → ℝ) (a θ W ell : ℝ) (hθ : 0 ≤ θ) (hW : 0 ≤ W) (hell : 0 ≤ ell)
    (hu : ContinuousOn u (Icc (0:ℝ) 1))
    (hsup : ∀ z ∈ Icc (0:ℝ) 1, u z ≤ W) :
    unitCellReward B h i p n u a θ ell ≤ θ*W := by
  exact (restricted_reward_le_full u a θ ell hu (cellFibreSet B h i p n)
    (measurableSet_cellFibreSet B h i p n)).trans
      (gaussian_unit_fibre_le_supremum u a θ W ell hθ hW hell hu hsup)

/-- The full Gaussian fibre integral exists from the actual normal envelope.
The continuity and envelope conditions are only almost-everywhere conditions. -/
theorem unitCellReward_integrable (B : V → E) (h : V → ℝ) (i j : V) (p n : E)
    (u : ((ℝ ∙ (B i-B j))ᗮ) → ℝ → ℝ) (a θ ell : ℝ) (hθ : 0 ≤ θ) (hell : 0 ≤ ell)
    (hu : Measurable (Function.uncurry u))
    (W : ((ℝ ∙ (B i-B j))ᗮ) → ℝ) (hW : MemLp W 32 (stdGaussian _))
    (hW0 : ∀ y, 0 ≤ W y)
    (hcontrol : ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
      ContinuousOn (u y) (Icc (0:ℝ) 1) ∧ ∀ z ∈ Icc (0:ℝ) 1, u y z ≤ W y) :
    Integrable (fun y : ((ℝ ∙ (B i-B j))ᗮ) => unitCellReward B h i (p+(y:E)) n (u y) a θ ell) (stdGaussian _) := by
  apply ((hW.integrable (by norm_num)).const_mul θ).mono'
    (unitCellReward_measurable B h i j p n u a θ ell hu).aestronglyMeasurable
  filter_upwards [hcontrol] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (unitCellReward_nonneg B h i (p+(y:E)) n (u y) a θ ell)]
  exact unitCellReward_le_supremum B h i (p+(y:E)) n (u y) a θ (W y) ell
    hθ (hW0 y) hell hy.1 hy.2

/-- Actual Gaussian integration of good and bad old-cell fibres. The main
term uses the true facet trace, while the escape term uses the whole tangent
plane probability. The normal-envelope hypotheses hold only almost everywhere. -/
theorem integral_unit_cell_reward_bound
    (B : V → E) (h : V → ℝ) (i j : V) (p n : E)
    (u : ((ℝ ∙ (B i-B j))ᗮ) → ℝ → ℝ) (a θ M ell : ℝ)
    (hθ : 0 ≤ θ) (hM : 0 < M) (hell : 0 < ell)
    (hη1 : θ*M/ell ≤ 1) (hsmall : (1+|a|)*(θ*M/ell) ≤ 1/2)
    (hu : Measurable (Function.uncurry u))
    (W : ((ℝ ∙ (B i-B j))ᗮ) → ℝ) (hWM : Measurable W)
    (hW : MemLp W 32 (stdGaussian _)) (hW0 : ∀ y, 0 ≤ W y)
    (hcontrol : ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
      ContinuousOn (u y) (Icc (0:ℝ) 1) ∧
      (∀ z ∈ Icc (0:ℝ) 1, u y z ≤ W y) ∧
      (∀ z ∈ Icc (0:ℝ) 1, |u y z-u y 0| ≤ W y*z)) :
    (∫ y : ((ℝ ∙ (B i-B j))ᗮ),
      unitCellReward B h i (p+(y:E)) n (u y) a θ ell ∂stdGaussian _) ≤
      (gaussianPDFReal 0 1 a*θ^2/(2*ell))*
        (∫ y in {y : ((ℝ ∙ (B i-B j))ᗮ) | p+(y:E) ∈ affineFacet B h i j},
          (max (u y 0) 0)^2 ∂stdGaussian _) +
      (gaussianPDFReal 0 1 a*θ^2/(2*ell))*M^2*
        (stdGaussian ((ℝ ∙ (B i-B j))ᗮ) (projectedEscape B h i j p n (θ*M/ell))).toReal +
      gaussianPDFReal 0 1 a*(2+|a|)*θ^3*M^3/ell^2 +
      θ*(M^31)⁻¹*(∫ y, W y^32 ∂stdGaussian _) := by
  let T := (ℝ ∙ (B i-B j))ᗮ
  let μ := stdGaussian T
  let A : Set T := {y | p+(y:E) ∈ affineFacet B h i j}
  let S : Set T := projectedEscape B h i j p n (θ*M/ell)
  let D : Set T := {y | M < W y}
  let c := gaussianPDFReal 0 1 a*θ^2/(2*ell)
  let e := gaussianPDFReal 0 1 a*(2+|a|)*θ^3*M^3/ell^2
  let f : T → ℝ := fun y => unitCellReward B h i (p+(y:E)) n (u y) a θ ell
  let g : T → ℝ := A.indicator (fun y => c*(max (u y 0) 0)^2)
  let q : T → ℝ := S.indicator (fun _ => c*M^2)
  let b : T → ℝ := D.indicator (fun y => θ*W y)
  have hpdf : 0 ≤ gaussianPDFReal 0 1 a := gaussianPDFReal_nonneg _ _ _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hA : MeasurableSet A :=
    ((isClosed_affineFacet B h i j).preimage (by fun_prop)).measurableSet
  have hS : MeasurableSet S := measurableSet_projectedEscape B h i j p n (θ*M/ell)
  have hD : MeasurableSet D := measurableSet_lt measurable_const hWM
  have hU : Measurable (fun y : T => max (u y 0) 0) := by
    exact (hu.comp (measurable_id.prodMk measurable_const)).max measurable_const
  have hU2 : MemLp (fun y : T => max (u y 0) 0) 2 μ := by
    apply (hW.mono_exponent (by norm_num : (2:ℝ≥0∞) ≤ 32)).mono' hU.aestronglyMeasurable
    filter_upwards [hcontrol] with y hy
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact max_le (hy.2.1 0 ⟨le_rfl,by norm_num⟩) (hW0 y)
  have hfi : Integrable f μ := unitCellReward_integrable B h i j p n u a θ ell hθ hell.le hu W hW hW0
    (hcontrol.mono fun y hy => ⟨hy.1,hy.2.1⟩)
  have hgi : Integrable g μ := (hU2.integrable_sq.const_mul c).indicator hA
  have hqi : Integrable q μ := (integrable_const (c*M^2)).indicator hS
  have hbi : Integrable b μ := ((hW.integrable (by norm_num)).const_mul θ).indicator hD
  have hg0 (y : T) : 0 ≤ g y := by
    by_cases hy : y ∈ A
    · simpa only [g,Set.indicator_of_mem hy] using mul_nonneg hc (sq_nonneg (max (u y 0) 0))
    · simp only [g,Set.indicator_of_notMem hy,le_refl]
  have hq0 (y : T) : 0 ≤ q y := by
    by_cases hy : y ∈ S
    · simpa only [q,Set.indicator_of_mem hy] using mul_nonneg hc (sq_nonneg M)
    · simp only [q,Set.indicator_of_notMem hy,le_refl]
  have hbound : ∀ᵐ y ∂μ, f y ≤ g y+q y+e+b y := by
    filter_upwards [hcontrol] with y hy
    by_cases hgood : W y ≤ M
    · have hb := good_unit_cell_reward B h i j p n y (u y) a θ M ell hθ hM.le hell hη1 hsmall hy.1
        (fun z hz => (hy.2.1 z hz).trans hgood)
        (fun z hz => (hy.2.2 z ⟨hz.1,hz.2.trans hη1⟩).trans
          (mul_le_mul_of_nonneg_right hgood hz.1))
      have hg : (if p+(y:E) ∈ affineFacet B h i j then
          gaussianPDFReal 0 1 a*(θ*max (u y 0) 0)^2/(2*ell) else 0)=g y := by
        by_cases ha : y ∈ A
        · have ha' : p+(y:E) ∈ affineFacet B h i j := ha
          simp only [ha',ite_true,g,Set.indicator_of_mem ha]
          dsimp [c]
          ring
        · have ha' : p+(y:E) ∉ affineFacet B h i j := ha
          simp only [ha',ite_false,g,Set.indicator_of_notMem ha]
      have hq : (if y ∈ projectedEscape B h i j p n (θ*M/ell) then
          gaussianPDFReal 0 1 a*(θ*M)^2/(2*ell) else 0)=q y := by
        by_cases hs : y ∈ S
        · have hs' : y ∈ projectedEscape B h i j p n (θ*M/ell) := hs
          simp only [hs',ite_true,q,Set.indicator_of_mem hs]
          dsimp [c]
          ring
        · have hs' : y ∉ projectedEscape B h i j p n (θ*M/ell) := hs
          simp only [hs',ite_false,q,Set.indicator_of_notMem hs]
      have hb0 : b y=0 := Set.indicator_of_notMem (not_lt.mpr hgood) _
      rw [hg,hq] at hb
      simpa only [f,e,hb0,add_zero] using hb
    · have hb1 : b y=θ*W y := Set.indicator_of_mem (lt_of_not_ge hgood) _
      have hf := unitCellReward_le_supremum B h i (p+(y:E)) n (u y) a θ (W y) ell
        hθ (hW0 y) hell.le hy.1 hy.2.1
      change f y ≤ _ at hf
      rw [hb1]
      linarith [hg0 y,hq0 y]
  have hgq : Integrable (fun y => g y+q y) μ := hgi.add hqi
  have hgqe : Integrable (fun y => g y+q y+e) μ := hgq.add (integrable_const e)
  have hmono := integral_mono_ae (g := fun y => g y+q y+e+b y) hfi (hgqe.add hbi) hbound
  have heval : (∫ y, g y+q y+e+b y ∂μ)=
      c*(∫ y in A, (max (u y 0) 0)^2 ∂μ)+c*M^2*(μ S).toReal+e+
        θ*(∫ y in D, W y ∂μ) := by
    rw [integral_add (f := fun y => g y+q y+e) (g := b) hgqe hbi,
      integral_add (f := fun y => g y+q y) (g := fun _ => e) hgq (integrable_const e),
      integral_add hgi hqi]
    change (∫ y, A.indicator (fun y => c*(max (u y 0) 0)^2) y ∂μ)+
      (∫ y, S.indicator (fun _ => c*M^2) y ∂μ)+(∫ _, e ∂μ)+
      (∫ y, D.indicator (fun y => θ*W y) y ∂μ)=_
    rw [integral_indicator hA,integral_indicator hS,integral_indicator hD]
    simp only [integral_const_mul,integral_const,Measure.real,Measure.restrict_apply_univ,
      measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul]
    ring
  rw [heval] at hmono
  have hbad := mul_le_mul_of_nonneg_left (bad_set_first_moment_from_L32 μ W M hM hW hW0) hθ
  change (∫ y, f y ∂μ) ≤ c*(∫ y in A,(max (u y 0) 0)^2 ∂μ)+
    c*M^2*(μ S).toReal+e+θ*(M^31)⁻¹*(∫ y,W y^32 ∂μ)
  change θ*(∫ y in D,W y ∂μ) ≤ _ at hbad
  nlinarith only [hmono,hbad]

/-- The entire-plane escape probability is discharged by the actual Gaussian third-label cover. -/
theorem integral_unit_cell_reward_explicit_bound
    (B : V → E) (h : V → ℝ) (i j : V) (p n : E)
    (u : ((ℝ ∙ (B i-B j))ᗮ) → ℝ → ℝ) (a θ M ell : ℝ)
    (σ D : ℝ) (hσ : 0 < σ) (hlower : NegativeVotingCapTail.CenteredSingularLowerBound B σ)
    (hij : i ≠ j) (hn : ‖n‖ ≤ 1)
    (hp : affineScore B h i p=affineScore B h j p)
    (hD : ∀ k ∈ thirdLabels i j, ‖B i-B k‖ ≤ D)
    (hθ : 0 ≤ θ) (hM : 0 < M) (hell : 0 < ell)
    (hη1 : θ*M/ell ≤ 1) (hsmall : (1+|a|)*(θ*M/ell) ≤ 1/2)
    (hu : Measurable (Function.uncurry u))
    (W : ((ℝ ∙ (B i-B j))ᗮ) → ℝ) (hWM : Measurable W)
    (hW : MemLp W 32 (stdGaussian _)) (hW0 : ∀ y, 0 ≤ W y)
    (hcontrol : ∀ᵐ y ∂stdGaussian ((ℝ ∙ (B i-B j))ᗮ),
      ContinuousOn (u y) (Icc (0:ℝ) 1) ∧
      (∀ z ∈ Icc (0:ℝ) 1, u y z ≤ W y) ∧
      (∀ z ∈ Icc (0:ℝ) 1, |u y z-u y 0| ≤ W y*z)) :
    (∫ y : ((ℝ ∙ (B i-B j))ᗮ),
      unitCellReward B h i (p+(y:E)) n (u y) a θ ell ∂stdGaussian _) ≤
      (gaussianPDFReal 0 1 a*θ^2/(2*ell))*
        (∫ y in {y : ((ℝ ∙ (B i-B j))ᗮ) | p+(y:E) ∈ affineFacet B h i j},
          (max (u y 0) 0)^2 ∂stdGaussian _) +
      (gaussianPDFReal 0 1 a*θ^2/(2*ell))*M^2*
        (((Fintype.card V-2:ℕ):ℝ)*((θ*M/ell)*D)/
          (Real.sqrt (2*Real.pi)*σ*Real.sqrt (3/2))) +
      gaussianPDFReal 0 1 a*(2+|a|)*θ^3*M^3/ell^2 +
      θ*(M^31)⁻¹*(∫ y, W y^32 ∂stdGaussian _) := by
  have hb := integral_unit_cell_reward_bound B h i j p n u a θ M ell hθ hM hell hη1 hsmall
    hu W hWM hW hW0 hcontrol
  have hx := projectedEscape_gaussian_bound B h σ D hσ hlower i j hij p n (θ*M/ell)
    (by positivity) hn hp hD
  have hpdf : 0 ≤ gaussianPDFReal 0 1 a := gaussianPDFReal_nonneg _ _ _
  have hc : 0 ≤ (gaussianPDFReal 0 1 a*θ^2/(2*ell))*M^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hx hc
  linarith only [hb,hm]

end NegativeVotingSwitchingFibreIntegration
