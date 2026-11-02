import GaussianRegularHighTailCross
import GaussianRegularCrossPlaneOU

/-! Actual two-normal OU trace and its odd quotient on a different affine
plane. All parameter substitutions are made after a common tangential
full-measure statement, never by restricting an ambient AE equality. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped ENNReal NNReal RealInnerProductSpace
namespace NegativeVotingRegularHighTailCrossPlane
open NegativeVotingNormalTrace NegativeVotingNormalDerivatives
  NegativeVotingRegularHighTailCrossKernel NegativeVotingRegularHighTailCross
  NegativeVotingRegularCrossPlaneGeometry NegativeVotingRegularCrossPlaneOU
  NegativeVotingSmoothingComposition NegativeVotingActualFacetOUTrace
variable {n : ℕ}

def pairShift (τ a b : ℝ) (y : ℝ×ℝ) : ℝ×ℝ :=
  (τ*a+Real.sqrt (1-τ^2)*y.1,τ*b+Real.sqrt (1-τ^2)*y.2)

theorem pairShift_measurePreserving (τ : ℝ) (hτ : τ^2 < 1) (a b : ℝ) :
    MeasurePreserving (pairShift τ a b) pairGaussian
      ((gaussianReal (τ*a) (normalVariance τ)).prod
        (gaussianReal (τ*b) (normalVariance τ))) := by
  exact (show MeasurePreserving (fun y:ℝ=>τ*a+Real.sqrt (1-τ^2)*y)
    (gaussianReal 0 1) (gaussianReal (τ*a) (normalVariance τ)) from
    ⟨by fun_prop,normalShift_map hτ a⟩).prod
      ⟨by fun_prop,normalShift_map hτ b⟩

theorem pairKernel_nonneg (τ a b : ℝ) (y : ℝ×ℝ) : 0 ≤ pairKernel τ a b y :=
  mul_nonneg (normalKernel_nonneg τ a y.1) (normalKernel_nonneg τ b y.2)

theorem pairKernel_le (τ : ℝ) (hτ : τ^2 < 1) (a b : ℝ) (y : ℝ×ℝ) :
    pairKernel τ a b y ≤ normalRowBound τ a*normalRowBound τ b :=
  mul_le_mul (normalKernel_le_rowBound hτ a y.1) (normalKernel_le_rowBound hτ b y.2)
    (normalKernel_nonneg τ b y.2) (by unfold normalRowBound;positivity)

theorem pairKernel_withDensity (τ : ℝ) (hτ : τ^2 < 1) (a b : ℝ) :
    pairGaussian.withDensity (fun y=>ENNReal.ofReal (pairKernel τ a b y))=
      (gaussianReal (τ*a) (normalVariance τ)).prod
        (gaussianReal (τ*b) (normalVariance τ)) := by
  rw [←normalKernel_withDensity hτ a,←normalKernel_withDensity hτ b,
    prod_withDensity ((normalKernel_measurable τ a).ennreal_ofReal)
      ((normalKernel_measurable τ b).ennreal_ofReal)]
  congr 1
  funext y
  exact ENNReal.ofReal_mul (normalKernel_nonneg τ a y.1)

theorem integral_pairKernel_eq_shift (τ : ℝ) (hτ : τ^2 < 1) (a b : ℝ)
    (g : ℝ×ℝ→ℝ) (hg : Measurable g) :
    (∫ y,pairKernel τ a b y*g y ∂pairGaussian)=
      ∫ y,g (pairShift τ a b y) ∂pairGaussian := by
  have hs := pairShift_measurePreserving τ hτ a b
  rw [←integral_map hs.measurable.aemeasurable hg.aestronglyMeasurable,hs.map_eq,
    ←pairKernel_withDensity τ hτ a b,
    integral_withDensity_eq_integral_toReal_smul
      ((pairKernel_measurable τ a b).ennreal_ofReal)
      (Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (pairKernel_nonneg τ a b _),smul_eq_mul]

theorem integrable_pair_shifted_product (τ : ℝ) (hτ : τ^2 < 1) (a b : ℝ)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hf : MemLp f 2 ((γFin n).prod pairGaussian)) :
    Integrable f ((γFin n).prod ((gaussianReal (τ*a) (normalVariance τ)).prod
      (gaussianReal (τ*b) (normalVariance τ)))) := by
  rw [←pairKernel_withDensity τ hτ a b,
    prod_withDensity_right ((pairKernel_measurable τ a b).ennreal_ofReal)]
  rw [integrable_withDensity_iff_integrable_smul'
    (f:=fun p:(Fin n→ℝ)×(ℝ×ℝ)=>ENNReal.ofReal (pairKernel τ a b p.2))
    (((pairKernel_measurable τ a b).ennreal_ofReal).comp measurable_snd)
    (Filter.Eventually.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (pairKernel_nonneg τ a b _),smul_eq_mul]
  refine (hf.integrable (by norm_num)).bdd_mul (c:=normalRowBound τ a*normalRowBound τ b)
    (((pairKernel_measurable τ a b).comp measurable_snd).aestronglyMeasurable) ?_
  filter_upwards with p
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pairKernel_nonneg τ a b _)] using
    pairKernel_le τ hτ a b p.2

/-- Literal two-normal product OU formula on one common tangential AE set. -/
theorem pairTrace_eq_product_ae_all_parameters (τ : ℝ) (hτ : τ^2 < 1)
    (f : (Fin n→ℝ)×(ℝ×ℝ)→ℝ) (hfm : Measurable f)
    (hf : MemLp f 2 ((γFin n).prod pairGaussian)) :
    ∀ᵐ x ∂γFin n,∀ a b : ℝ,pairTrace τ a b f x=
      ∫ z,f (pairMix τ (Real.sqrt (1-τ^2)) (x,(a,b)) z)
        ∂(γFin n).prod pairGaussian := by
  have hv : 0 ≤ 1-τ^2 := by linarith
  have hmix : MeasurePreserving (mixCLM (n:=n) τ (Real.sqrt (1-τ^2)))
      ((γFin n).prod (γFin n)) (γFin n) :=
    ⟨(mixCLM (n:=n) τ (Real.sqrt (1-τ^2))).continuous.measurable,
      ou_kernel_map_coeff _ _ (by rw [Real.sq_sqrt hv];ring)⟩
  have hpull := hf.comp_measurePreserving
    ((hmix.prod (MeasurePreserving.id pairGaussian)).comp
      (measurePreserving_prodAssoc (γFin n) (γFin n) pairGaussian).symm)
  have hsec : ∀ᵐ x ∂γFin n,MemLp (fun z:(Fin n→ℝ)×(ℝ×ℝ)=>
      f ((fun j=>τ*x j+Real.sqrt (1-τ^2)*z.1 j),z.2)) 2
        ((γFin n).prod pairGaussian) := by
    filter_upwards [hpull.aestronglyMeasurable.prodMk_left,hpull.integrable_sq.prod_right_ae]
      with x hxm hxi
    exact (memLp_two_iff_integrable_sq hxm).mpr hxi
  filter_upwards [hsec] with x hx
  intro a b
  have hi := ((MeasurePreserving.id (γFin n)).prod
    (pairShift_measurePreserving τ hτ a b)).integrable_comp_of_integrable
      (integrable_pair_shifted_product τ hτ a b _ hx)
  calc
    pairTrace τ a b f x=∫ z,∫ y,
      f ((fun j=>τ*x j+Real.sqrt (1-τ^2)*z j),pairShift τ a b y)
        ∂pairGaussian ∂γFin n := by
      apply integral_congr_ae
      filter_upwards with z
      exact integral_pairKernel_eq_shift τ hτ a b _ (hfm.comp (by fun_prop))
    _ = _ := (integral_prod _ hi).symm

section ActualPlane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open NegativeVotingDisintegration

/-- The product trace agrees with the literal ambient OU potential on a
single full-measure tangential set before all normal-coordinate choices. -/
theorem ae_pairTrace_eq_ambient (w : E) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (c s : ℝ) (hcs : c^2+s^2=1) (τ : ℝ) (hτ : τ^2 < 1)
    (f : E→ℝ) (hfm : Measurable f) (hf : MemLp f 2 (stdGaussian E)) :
    ∀ᵐ t ∂γFin n,∀ a b : ℝ,
      pairTrace τ a b (fun p=>f (rotatedReconstruct w v e c s p)) t=
        ambientAverage τ f (rotatedReconstruct w v e c s (t,(a,b))) := by
  have hfm' := hfm.comp (rotatedReconstruct_measurable w v e c s)
  have hf' := (rotatedReconstruct_memLp_norm w hw v hv e c s hcs f 2 hf).1
  filter_upwards [pairTrace_eq_product_ae_all_parameters τ hτ _ hfm' hf'] with t ht
  intro a b
  simp only [Function.comp_def] at ht
  rw [ht a b,ambientAverage_rotatedReconstruct w hw v hv e c s hcs τ f hfm]

/-- An odd actual OU potential factors by its regular normal coordinate on
any current affine plane. The quotient is measurable and has the explicit
dimension-free Lq bound. Oddness is required only of the final smoothed
potential, not of its possibly merely measurable L2 input representative. -/
theorem exists_actual_odd_plane_quotient (w : E) (hw : ‖w‖=1)
    (v : tangentSpace w) (hv : ‖v‖=1)
    (e : tangentSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (c s : ℝ) (hcs : c^2+s^2=1) (τ q A : ℝ) (hτ : 0 < τ)
    (hq : 2 ≤ q) (hqt : q*τ^2 ≤ 1/2)
    (f : E→ℝ) (hfm : Measurable f) (hf : MemLp f 2 (stdGaussian E))
    (hodd : ∀ x:E,ambientAverage τ f
      (x-(2*inner ℝ (c • w+s • (v:E)) x) • (c • w+s • (v:E)))=
        -ambientAverage τ f x) :
    ∃ Q : (Fin n→ℝ)×ℝ→ℝ,Measurable Q ∧
      MemLp Q (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)) ∧
      eLpNorm Q (ENNReal.ofReal q) ((γFin n).prod (gaussianReal 0 1)) ≤
        ENNReal.ofReal (Real.sqrt (8*τ^2)*Real.exp (τ^2*A^2/2))*(ENNReal.ofReal 2)^(1/q)*
          eLpNorm f 2 (stdGaussian E) ∧
      ∀ᵐ p ∂(γFin n).prod (gaussianReal 0 1),
        ambientAverage τ f (planeReconstruct w v e A p)=
          inner ℝ (c • w+s • (v:E)) (planeReconstruct w v e A p)*Q p := by
  have hs : τ^2 < 1 := by nlinarith [sq_nonneg τ]
  let g : (Fin n→ℝ)×(ℝ×ℝ)→ℝ := fun p=>f (rotatedReconstruct w v e c s p)
  have hgm : Measurable g := hfm.comp (rotatedReconstruct_measurable w v e c s)
  have hg := rotatedReconstruct_memLp_norm w hw v hv e c s hcs f 2 hf
  let a : ℝ→ℝ := fun z=>c*A+s*z
  let b : ℝ→ℝ := fun z=>-s*A+c*z
  let Q : (Fin n→ℝ)×ℝ→ℝ := fun p=>quotientTrace τ (a p.2) (b p.2) g p.1
  have hQm : Measurable Q := (quotientTrace_joint_measurable τ hs g hgm).comp
    (show Measurable (fun p:(Fin n→ℝ)×ℝ=>(p.1,(a p.2,b p.2))) by
      dsimp [a,b];fun_prop)
  have hnorm := quotientTrace_plane_norm_le τ q A hτ hq hqt a b (by dsimp [a];fun_prop)
    (by dsimp [b];fun_prop) (fun z=>(rotated_plane_radius c s A z hcs).le) g hgm hg.1
  refine ⟨Q,hQm,hnorm.1,?_,?_⟩
  · exact hnorm.2.trans_eq (congrArg (fun r:ℝ≥0∞=>
      ENNReal.ofReal (Real.sqrt (8*τ^2)*Real.exp (τ^2*A^2/2))*(ENNReal.ofReal 2)^(1/q)*r) hg.2)
  · have hcommon : ∀ᵐ t ∂γFin n,∀ a b : ℝ,
        a*quotientTrace τ a b g t=ambientAverage τ f (rotatedReconstruct w v e c s (t,(a,b))) := by
      filter_upwards [ae_quotientTrace_mul τ hs g hgm hg.1,
        ae_pairTrace_eq_ambient w hw v hv e c s hcs τ hs f hfm hf] with t ht hp
      intro a b
      rw [ht a b,hp a b,hp (-a) b]
      have ho := hodd (rotatedReconstruct w v e c s (t,(a,b)))
      rw [inner_rotated_normal w hw v hv e c s hcs] at ho
      rw [rotatedReconstruct_reflect,ho]
      ring
    have hprod := (Measure.quasiMeasurePreserving_fst (μ:=γFin n)
      (ν:=gaussianReal 0 1)).ae hcommon
    filter_upwards [hprod] with p hp
    have hx := hp (a p.2) (b p.2)
    have hcoord := rotatedReconstruct_on_plane w v e c s hcs A p.2 p.1
    have hi := inner_rotated_normal w hw v hv e c s hcs (p.1,(a p.2,b p.2))
    change inner ℝ (c • w+s • (v:E)) (rotatedReconstruct w v e c s
      (p.1,(c*A+s*p.2,-s*A+c*p.2)))=a p.2 at hi
    rw [hcoord] at hi
    dsimp only [a,b] at hx
    rw [hcoord] at hx
    rw [hi]
    exact hx.symm

end ActualPlane
end NegativeVotingRegularHighTailCrossPlane
