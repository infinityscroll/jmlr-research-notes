import GaussianStructuredSwitchingNormal
import GaussianDimensionUniformErrorBounds
import GaussianReciprocalDampingTube
import GaussianQuadraticBulkNorm

/-! Labelwise Gaussian moments for the literal weighted switching forcing.
All products are estimated in ell²(Lq), not inferred from Lq(ell²). -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingStructuredSwitchingMoments
open NegativeVotingFan NegativeVotingDisintegration NegativeVotingActualFacetOUTrace
  NegativeVotingBoundaryHighChaosTrace NegativeVotingPolynomialFacetGeometricTrace
  NegativeVotingPolynomialFacetTrace NegativeVotingFiniteHermite NegativeVotingPolynomialDegree
  NegativeVotingSmoothingComposition NegativeVotingHypercontractivity NegativeVotingQuadraticBulkNorm
  NegativeVotingConditionalSecondMoment NegativeVotingReciprocalDampingTube
  NegativeVotingSmoothErrorMoment NegativeVotingRegularPairCoefficient
  OAI.MinUncut.GaussianHermite
variable {d n : ℕ}

theorem polynomial_lq_le {k : ℕ} {f : (Fin d→ℝ)→ℝ}
    (hf : f∈polynomialSpace k) (τ : ℝ) (hτ : 0<τ) (hτ1 : τ<1) :
    eLpNorm f (ENNReal.ofReal (1+(τ^2)⁻¹)) (γFin d) ≤
      ENNReal.ofReal ((τ^k)⁻¹)*eLpNorm f 2 (γFin d) := by
  obtain ⟨c,rfl⟩:=exists_normalized_expansion hf
  let S:=NegativeVotingProjection.lowerModes (κ:=Fin d) (k+1)
  have hdeg a (ha:a∈S) : degree a ≤ k:=by
    exact Nat.lt_succ_iff.mp ((NegativeVotingProjection.mem_lowerModes_iff (k+1) a).mp ha)
  have hi : MemLp (inverseOUSum S c τ) 2 (γFin d):=hermiteSum_memLp S _
  have he : gaussianAverage τ (inverseOUSum S c τ)=hermiteSum S c:=
    funext (inverseOUSum_gaussianAverage S c τ hτ hτ1)
  have hh:=memLp_gaussian_average_l2_to_lq τ hτ hτ1 (inverseOUSum S c τ) hi
  rw [he] at hh
  exact hh.trans (inverseOUSum_eLpNorm_le S c k hdeg τ hτ hτ1.le)

/-- Genuine ambient OU hypercontractivity in Euclidean coordinates. -/
theorem ambientAverage_lq_le (τ : ℝ) (hτ : 0<τ) (hτ1 : τ<1)
    (f : FSC.Coord d→ℝ) (hfM : Measurable f) (hf : MemLp f 2 (stdGaussian (FSC.Coord d))) :
    MemLp (ambientAverage τ f) (ENNReal.ofReal (1+(τ^2)⁻¹)) (stdGaussian (FSC.Coord d)) ∧
      eLpNorm (ambientAverage τ f) (ENNReal.ofReal (1+(τ^2)⁻¹)) (stdGaussian (FSC.Coord d)) ≤
        eLpNorm f 2 (stdGaussian (FSC.Coord d)) := by
  let T:=MeasurableEquiv.toLp 2 (Fin d→ℝ)
  have hT:=gaussian_toLp_measurePreserving d
  have hf':=hf.comp_measurePreserving hT
  have he : (ambientAverage τ f) ∘ T=gaussianAverage τ (f ∘ T):=by
    funext x
    exact ambientAverage_eq_gaussianAverage τ f (T x)
  have hh:=memLp_gaussian_average_l2_to_lq τ hτ hτ1 (f ∘ T) hf'
  have hnorm : eLpNorm (ambientAverage τ f) (ENNReal.ofReal (1+(τ^2)⁻¹))
      (stdGaussian (FSC.Coord d)) ≤ eLpNorm f 2 (stdGaussian (FSC.Coord d)):=by
    rw [←eLpNorm_comp_measurePreserving (ambientAverage_measurable τ f hfM).aestronglyMeasurable hT,
      he,←eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hT]
    exact hh
  exact ⟨hnorm.trans_lt hf,hnorm⟩

/-- Affine Gaussian scores have the needed variable-exponent norm bound,
with no dimension factor. -/
theorem affineScore_lq_le (τ : ℝ) (hτ : 0<τ) (hτ1 : τ<1)
    (v : FSC.Coord d) (c : ℝ) :
    MemLp (fun x:FSC.Coord d=>inner ℝ v x+c) (ENNReal.ofReal (1+(τ^2)⁻¹))
      (stdGaussian (FSC.Coord d)) ∧
    eLpNorm (fun x:FSC.Coord d=>inner ℝ v x+c) (ENNReal.ofReal (1+(τ^2)⁻¹))
      (stdGaussian (FSC.Coord d)) ≤ ENNReal.ofReal (τ⁻¹*(‖v‖+|c|)) := by
  let f:=fun x:Fin d→ℝ=>inner ℝ v (WithLp.toLp 2 x)+c
  have hpoly : f∈polynomialSpace 1:=by
    have hc: (fun _:Fin d→ℝ=>c)∈polynomialSpace 1:=by
      simpa only [Pi.smul_def,smul_eq_mul,mul_one] using (polynomialSpace 1).smul_mem c (one_mem (κ:=Fin d) 1)
    exact (polynomialSpace 1).add_mem (inner_mem (toEuclideanLinear (d:=d)) v) hc
  have hf : MemLp f 2 (γFin d):=polynomial_memLp hpoly
  have hnorm2 : eLpNorm f 2 (γFin d) ≤ ENNReal.ofReal (‖v‖+|c|):=by
    have hi:=norm2_inner v
    have hn:=norm2_add_le (polynomial_memLp (inner_mem (toEuclideanLinear (d:=d)) v))
      (memLp_const c)
    have hconst : norm2 (fun _:Fin d→ℝ=>c)=|c|:=by
      rw [norm2_eq_sqrt (memLp_const c)]
      simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,
        Real.sqrt_sq_eq_abs]
    change norm2 f ≤ norm2 (fun x=>inner ℝ v (WithLp.toLp 2 x))+norm2 (fun _:Fin d→ℝ=>c) at hn
    rw [hi,hconst] at hn
    change (eLpNorm f 2 (γFin d)).toReal ≤ ‖v‖+|c| at hn
    exact (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal (add_nonneg (norm_nonneg _) (abs_nonneg _))] using hn)
  have hh:=(polynomial_lq_le hpoly τ hτ hτ1).trans (mul_le_mul' le_rfl hnorm2)
  simp only [pow_one,←ENNReal.ofReal_mul (inv_nonneg.mpr hτ.le)] at hh
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d):=map_pi_eq_stdGaussian
  have hqnorm : eLpNorm (fun x:FSC.Coord d=>inner ℝ v x+c) (ENNReal.ofReal (1+(τ^2)⁻¹))
      (stdGaussian (FSC.Coord d)) ≤ ENNReal.ofReal (τ⁻¹*(‖v‖+|c|)):=by
    rw [←hmap,eLpNorm_map_measure (by fun_prop) (by fun_prop)]
    exact hh
  exact ⟨hqnorm.trans_lt ENNReal.ofReal_lt_top,hqnorm⟩

theorem holder_double (q : ℝ) (hq : 0<q) :
    ENNReal.HolderTriple (ENNReal.ofReal (2*q)) (ENNReal.ofReal (2*q)) (ENNReal.ofReal q) := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (show 0≤2*q by positivity),
    ENNReal.toReal_ofReal hq.le]
  field_simp
  <;> ring

section RealNorm
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def realLp (μ : Measure X) (p : ℝ≥0∞) (f : X→ℝ) : ℝ := (eLpNorm f p μ).toReal

theorem realLp_nonneg (p : ℝ≥0∞) (f : X→ℝ) : 0 ≤ realLp μ p f:=ENNReal.toReal_nonneg

theorem realLp_mul_le {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : X→ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    realLp μ r (fun x=>f x*g x) ≤ realLp μ p f*realLp μ q g := by
  have hh:=ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top)
    (eLpNorm_smul_le_mul_eLpNorm (r:=r) hf.aestronglyMeasurable hg.aestronglyMeasurable)
  simpa only [realLp,Pi.smul_def,smul_eq_mul,Pi.mul_def,ENNReal.toReal_mul] using hh

theorem realLp_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : X→ℝ}
    (hf : MemLp f p μ) (hg : MemLp g p μ) :
    realLp μ p (fun x=>f x+g x) ≤ realLp μ p f+realLp μ p g := by
  have hh:=ENNReal.toReal_mono (by finiteness : eLpNorm f p μ+eLpNorm g p μ≠∞)
    (eLpNorm_add_le (f:=f) (g:=g) hp)
  simpa only [realLp,Pi.add_def,ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using hh

theorem realLp_const_mul (p : ℝ≥0∞) (c : ℝ) (f : X→ℝ) :
    realLp μ p (fun x=>c*f x)=|c| *realLp μ p f := by
  change (eLpNorm (c • f) p μ).toReal=_
  rw [eLpNorm_const_smul,ENNReal.toReal_mul,Real.enorm_eq_ofReal_abs,ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

theorem realLp_abs {p : ℝ≥0∞} {f : X→ℝ} (hf : MemLp f p μ) :
    realLp μ p (fun x=>|f x|)=realLp μ p f := by
  simpa only [realLp,Real.norm_eq_abs] using congrArg ENNReal.toReal (eLpNorm_norm f hf.aestronglyMeasurable)

theorem realLp_sub_le {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : X→ℝ}
    (hf : MemLp f p μ) (hg : MemLp g p μ) :
    realLp μ p (fun x=>f x-g x) ≤ realLp μ p f+realLp μ p g := by
  have hh:=realLp_add_le hp hf hg.neg
  simpa only [sub_eq_add_neg,realLp,eLpNorm_neg,Pi.neg_apply] using hh

end RealNorm

/-- Literal nonnegative weighted forcing, with the two genuine smoothed
inputs retained. Its later identification with the path residual is separate. -/
def weightedForcing (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (η r τ : ℝ) (fD fu : Fin (n+2)→FSC.Coord d→ℝ) (x : FSC.Coord d) (i : Fin (n+2)) : ℝ :=
  inverseKappa η (fun j=>inner ℝ (R j) x)*
    (smoothPairError n r (fun j=>inner ℝ (R j) x)*|inner ℝ (D i) x+h i|+
      |ambientAverage τ (fD i) x-ambientAverage τ (fu i) x|/r)

/-- Quantitative labelwise bound for the literal weighted forcing. The two
assumptions concern the actual common damping and smooth error, and are supplied
by their existing uniform-noise theorems. The smoothed inputs are genuine L2
functions; no pointwise or planewise OU value is postulated. -/
theorem weightedForcing_label_norm_le
    (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (η r τ q Kκ Kε : ℝ) (hr : 0<r) (hτ : 0<τ) (hτ1 : τ<1)
    (hq : 1 ≤ q) (hqτ : 4*q ≤ 1+(τ^2)⁻¹) (hKκ : 0 ≤ Kκ) (hKε : 0 ≤ Kε)
    (hκ : eLpNorm (fun x:FSC.Coord d=>inverseKappa η (fun j=>inner ℝ (R j) x))
      (ENNReal.ofReal (2*q)) (stdGaussian (FSC.Coord d)) ≤ ENNReal.ofReal Kκ)
    (hε : eLpNorm (fun x:FSC.Coord d=>smoothPairError n r (fun j=>inner ℝ (R j) x)/r)
      (ENNReal.ofReal (4*q)) (stdGaussian (FSC.Coord d)) ≤ ENNReal.ofReal Kε)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ)
    (hfDM : ∀i,Measurable (fD i)) (hfuM : ∀i,Measurable (fu i))
    (hfD : ∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d)))
    (hfu : ∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) (i : Fin (n+2)) :
    MemLp (fun x=>weightedForcing R D h η r τ fD fu x i)
      (ENNReal.ofReal q) (stdGaussian (FSC.Coord d)) ∧
    realLp (stdGaussian (FSC.Coord d)) (ENNReal.ofReal q)
      (fun x=>weightedForcing R D h η r τ fD fu x i) ≤
      Kκ*(r*Kε*τ⁻¹*(‖D i‖+|h i|)+
        (realLp (stdGaussian (FSC.Coord d)) 2 (fD i)+
          realLp (stdGaussian (FSC.Coord d)) 2 (fu i))/r) := by
  let μ:=stdGaussian (FSC.Coord d)
  let κ:=fun x:FSC.Coord d=>inverseKappa η (fun j=>inner ℝ (R j) x)
  let ε:=fun x:FSC.Coord d=>smoothPairError n r (fun j=>inner ℝ (R j) x)/r
  let l:=fun x:FSC.Coord d=>inner ℝ (D i) x+h i
  let a:=fun x:FSC.Coord d=>ambientAverage τ (fD i) x-ambientAverage τ (fu i) x
  let p:=ENNReal.ofReal q
  let p2:=ENNReal.ofReal (2*q)
  let p4:=ENNReal.ofReal (4*q)
  have hq0 : 0<q:=by linarith
  haveI : ENNReal.HolderTriple p2 p2 p:=holder_double q hq0
  haveI : ENNReal.HolderTriple p4 p4 p2:=by
    convert holder_double (2*q) (by positivity) using 1 <;> dsimp [p4,p2] <;> congr 1 <;> ring
  have hp2 : 1 ≤ p2:=by exact_mod_cast ENNReal.ofReal_le_ofReal (show (1:ℝ) ≤ 2*q by linarith)
  have hp4native : p4 ≤ ENNReal.ofReal (1+(τ^2)⁻¹):=ENNReal.ofReal_le_ofReal hqτ
  have hp2native : p2 ≤ ENNReal.ofReal (1+(τ^2)⁻¹):=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hκm : MemLp κ p2 μ:=hκ.trans_lt ENNReal.ofReal_lt_top
  have hεm : MemLp ε p4 μ:=hε.trans_lt ENNReal.ofReal_lt_top
  have hκr : realLp μ p2 κ ≤ Kκ:=by
    simpa only [realLp,ENNReal.toReal_ofReal hKκ] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hκ
  have hεr : realLp μ p4 ε ≤ Kε:=by
    simpa only [realLp,ENNReal.toReal_ofReal hKε] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hε
  have hll:=affineScore_lq_le τ hτ hτ1 (D i) (h i)
  have hlm : MemLp l p4 μ:=hll.1.mono_exponent hp4native
  have hlr : realLp μ p4 l ≤ τ⁻¹*(‖D i‖+|h i|):=by
    have hh:=(eLpNorm_le_eLpNorm_of_exponent_le hp4native).trans hll.2
    simpa only [realLp,ENNReal.toReal_ofReal (by positivity : 0 ≤ τ⁻¹*(‖D i‖+|h i|))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  have hd:=ambientAverage_lq_le τ hτ hτ1 (fD i) (hfDM i) (hfD i)
  have hu:=ambientAverage_lq_le τ hτ hτ1 (fu i) (hfuM i) (hfu i)
  have hdm : MemLp (ambientAverage τ (fD i)) p2 μ:=hd.1.mono_exponent hp2native
  have hum : MemLp (ambientAverage τ (fu i)) p2 μ:=hu.1.mono_exponent hp2native
  have hdr : realLp μ p2 (ambientAverage τ (fD i)) ≤ realLp μ 2 (fD i):=
    ENNReal.toReal_mono (hfD i).eLpNorm_ne_top ((eLpNorm_le_eLpNorm_of_exponent_le hp2native).trans hd.2)
  have hur : realLp μ p2 (ambientAverage τ (fu i)) ≤ realLp μ 2 (fu i):=
    ENNReal.toReal_mono (hfu i).eLpNorm_ne_top ((eLpNorm_le_eLpNorm_of_exponent_le hp2native).trans hu.2)
  have ham : MemLp a p2 μ:=hdm.sub hum
  have har : realLp μ p2 a ≤ realLp μ 2 (fD i)+realLp μ 2 (fu i):=
    (realLp_sub_le hp2 hdm hum).trans (add_le_add hdr hur)
  have hlabs : MemLp (fun x=>|l x|) p4 μ:=by simpa only [Real.norm_eq_abs] using hlm.norm
  have haabs : MemLp (fun x=>|a x|) p2 μ:=by simpa only [Real.norm_eq_abs] using ham.norm
  have hel : MemLp (fun x=>ε x*|l x|) p2 μ:=hεm.fun_mul hlabs
  have hsum : MemLp (fun x=>r*(ε x*|l x|)+r⁻¹*|a x|) p2 μ:=
    (hel.const_mul r).add (haabs.const_mul r⁻¹)
  have heq : (fun x=>weightedForcing R D h η r τ fD fu x i)=
      (fun x=>κ x*(r*(ε x*|l x|)+r⁻¹*|a x|)):=by
    funext x
    dsimp only [weightedForcing,κ,ε,l,a]
    field_simp
    <;> ring
  rw [heq]
  refine ⟨hκm.fun_mul hsum,?_⟩
  have heprod := realLp_mul_le (r:=p2) hεm hlabs
  rw [realLp_abs hlm] at heprod
  have heprod' : realLp μ p2 (fun x=>ε x*|l x|) ≤ Kε*(τ⁻¹*(‖D i‖+|h i|)):=
    heprod.trans (mul_le_mul hεr hlr (realLp_nonneg _ _) hKε)
  have hs:=realLp_add_le hp2 (hel.const_mul r) (haabs.const_mul r⁻¹)
  rw [realLp_const_mul,realLp_const_mul,abs_of_pos hr,abs_of_pos (inv_pos.mpr hr),realLp_abs ham] at hs
  have hs' : realLp μ p2 (fun x=>r*(ε x*|l x|)+r⁻¹*|a x|) ≤
      r*Kε*τ⁻¹*(‖D i‖+|h i|)+(realLp μ 2 (fD i)+realLp μ 2 (fu i))/r := by
    refine hs.trans ((add_le_add (mul_le_mul_of_nonneg_left heprod' hr.le)
      (mul_le_mul_of_nonneg_left har (inv_nonneg.mpr hr.le))).trans_eq ?_)
    ring
  exact (realLp_mul_le (r:=p) hκm hsum).trans (mul_le_mul hκr hs' (realLp_nonneg _ _) hKκ)

private theorem four_term_square (K a b x y z w : ℝ) :
    (K*(a*(x+y)+b*(z+w)))^2 ≤ 4*K^2*(a^2*(x^2+y^2)+b^2*(z^2+w^2)) := by
  have h1:=add_sq_le (a:=a*(x+y)) (b:=b*(z+w))
  have h2:=mul_le_mul_of_nonneg_left (add_sq_le (a:=x) (b:=y)) (sq_nonneg a)
  have h3:=mul_le_mul_of_nonneg_left (add_sq_le (a:=z) (b:=w)) (sq_nonneg b)
  have hs : (a*(x+y)+b*(z+w))^2 ≤ 4*(a^2*(x^2+y^2)+b^2*(z^2+w^2)) := by
    nlinarith only [h1,h2,h3]
  convert mul_le_mul_of_nonneg_left hs (sq_nonneg K) using 1 <;> ring

theorem weightedForcing_sum_norm_sq_le
    (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (η r τ q Kκ Kε : ℝ) (hr : 0<r) (hτ : 0<τ) (hτ1 : τ<1)
    (hq : 1 ≤ q) (hqτ : 4*q ≤ 1+(τ^2)⁻¹) (hKκ : 0 ≤ Kκ) (hKε : 0 ≤ Kε)
    (hκ : eLpNorm (fun x:FSC.Coord d=>inverseKappa η (fun j=>inner ℝ (R j) x))
      (ENNReal.ofReal (2*q)) (stdGaussian (FSC.Coord d)) ≤ ENNReal.ofReal Kκ)
    (hε : eLpNorm (fun x:FSC.Coord d=>smoothPairError n r (fun j=>inner ℝ (R j) x)/r)
      (ENNReal.ofReal (4*q)) (stdGaussian (FSC.Coord d)) ≤ ENNReal.ofReal Kε)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ)
    (hfDM : ∀i,Measurable (fD i)) (hfuM : ∀i,Measurable (fu i))
    (hfD : ∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d)))
    (hfu : ∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) :
    (∀i,MemLp (fun x=>weightedForcing R D h η r τ fD fu x i)
      (ENNReal.ofReal q) (stdGaussian (FSC.Coord d))) ∧
    (∑i,(realLp (stdGaussian (FSC.Coord d)) (ENNReal.ofReal q)
      (fun x=>weightedForcing R D h η r τ fD fu x i))^2) ≤
      4*Kκ^2*(r*Kε*τ⁻¹)^2*((∑i,‖D i‖^2)+(∑i,(h i)^2))+
      4*Kκ^2*(r⁻¹)^2*((∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (fD i))^2)+
        (∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (fu i))^2)) := by
  have hi:=weightedForcing_label_norm_le R D h η r τ q Kκ Kε hr hτ hτ1 hq hqτ
    hKκ hKε hκ hε fD fu hfDM hfuM hfD hfu
  refine ⟨fun i=>(hi i).1,?_⟩
  have hs i := (pow_le_pow_left₀ (realLp_nonneg _ _) (hi i).2 2).trans
    (by simpa only [div_eq_mul_inv,mul_comm (r⁻¹)] using
      (four_term_square Kκ (r*Kε*τ⁻¹) (r⁻¹) ‖D i‖ |h i|
        (realLp (stdGaussian (FSC.Coord d)) 2 (fD i))
        (realLp (stdGaussian (FSC.Coord d)) 2 (fu i))))
  have hb:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hs i)
  refine hb.trans_eq ?_
  simp only [sq_abs,mul_add,Finset.sum_add_distrib,←Finset.mul_sum]
  ring


def dampingMomentConstant : ℝ := 2 * Real.exp 1 * Real.exp (3/2)

def errorMomentCoefficient (A : ℝ) (n : ℕ) : ℝ :=
  momentConstant (4*A) * logScale n * Real.sqrt (logScale n) * Real.exp 1

theorem dampingMomentConstant_nonneg : 0 ≤ dampingMomentConstant := by
  unfold dampingMomentConstant
  positivity

theorem errorMomentCoefficient_nonneg (A : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    0 ≤ errorMomentCoefficient A n := by
  have hC:=momentConstant_nonneg (4*A) (by positivity)
  have hL : 0 ≤ logScale n := by linarith [logScale_one_le n]
  unfold errorMomentCoefficient
  positivity

/-- The common factors in the literal weighted forcing satisfy the required
moments at one dimension-first threshold; no moment bound is assumed. -/
theorem exists_dimension_uniform_forcing_common_moments
    (A K : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (R : Fin (n+2)→FSC.Coord d), (∀i,‖R i‖ ≤ 1) →
      ∀ r η : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n →
      eLpNorm (fun x:FSC.Coord d=>inverseKappa η (fun j=>inner ℝ (R j) x))
        (ENNReal.ofReal (2*(A*logScale n))) (stdGaussian (FSC.Coord d)) ≤
        ENNReal.ofReal dampingMomentConstant ∧
      eLpNorm (fun x:FSC.Coord d=>smoothPairError n r (fun j=>inner ℝ (R j) x)/r)
        (ENNReal.ofReal (4*(A*logScale n))) (stdGaussian (FSC.Coord d)) ≤
        ENNReal.ofReal (errorMomentCoefficient A n) := by
  obtain ⟨Nε,hNε⟩:=NegativeVotingDimensionUniformErrorBounds.exists_dimension_uniform_error_moments
    (4*A) (by linarith)
  obtain ⟨Nκ,hNκ⟩:=exists_dimension_uniform_damping_tube (2*A) K (by linarith) hK
  refine ⟨max Nε Nκ,?_⟩
  intro n hn d R hR r η hr hrange hη hηupper
  have hnε : Nε ≤ n := (le_max_left _ _).trans hn
  have hnκ : Nκ ≤ n := (le_max_right _ _).trans hn
  obtain ⟨W,hWM,hW0,hWmem,hWnorm,hWt⟩:=hNκ n hnκ d R hR (fun _=>0) 0
    (le_refl 0) (by intro i; simp)
  have hκW x : inverseKappa η (fun j=>inner ℝ (R j) x) ≤ W x := by
    have hh:=((hWt r η hr hrange hη hηupper (fun _=>0) (by intro i; norm_num) x).2
      0 (by constructor <;> norm_num)).1
    simpa using hh
  have hκM : Measurable (fun x:FSC.Coord d=>inverseKappa η (fun j=>inner ℝ (R j) x)) := by
    simp only [inverseKappa_eq_exp, scoreEnergy]
    fun_prop
  have hκnorm := (eLpNorm_mono (p:=ENNReal.ofReal ((2*A)*logScale n))
    (μ:=stdGaussian (FSC.Coord d)) hκM.aestronglyMeasurable (fun x=>by
      simpa only [Real.norm_eq_abs,abs_of_pos (inverseKappa_pos _ _),abs_of_nonneg (hW0 x)]
        using hκW x)).trans hWnorm
  have he:=hNε n hnε d R hR (fun _=>0) (fun _=>0) 0 r (le_refl 0)
    (by intro i; simp) (by intro i; norm_num) hr hrange
  constructor
  · convert hκnorm using 1
    · congr 2; ring
    · simp only [dampingMomentConstant]
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num
  · have he':=he.2.1
    convert he' using 1
    · simp only [zero_add]
      congr 2
      ring
    · simp only [errorMomentCoefficient,zero_div,add_zero]
      rw [ENNReal.ofReal_mul (by
        have hC:=momentConstant_nonneg (4*A) (by linarith)
        have hL:0 ≤ logScale n := by linarith [logScale_one_le n]
        positivity)]

/-- Dimension-uniform ell²(Lq) estimate for the literal weighted forcing, with
the actual damping and error bounds discharged.  The remaining inputs are the
two measurable L2 residuals before their common OU smoothing. -/
theorem exists_dimension_uniform_weightedForcing_sum_norm_sq_le
    (A K : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ,
      ∀ (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ),
      (∀i,‖R i‖ ≤ 1) → ∀ r η τ : ℝ,
      0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η → η ≤ K*r^2*logScale n →
      0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fun x=>weightedForcing R D h η r τ fD fu x i)
        (ENNReal.ofReal (A*logScale n)) (stdGaussian (FSC.Coord d))) ∧
      (∑i,(realLp (stdGaussian (FSC.Coord d)) (ENNReal.ofReal (A*logScale n))
        (fun x=>weightedForcing R D h η r τ fD fu x i))^2) ≤
        4*dampingMomentConstant^2*(r*errorMomentCoefficient A n*τ⁻¹)^2*
          ((∑i,‖D i‖^2)+(∑i,(h i)^2))+
        4*dampingMomentConstant^2*(r⁻¹)^2*
          ((∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (fD i))^2)+
            (∑i,(realLp (stdGaussian (FSC.Coord d)) 2 (fu i))^2)) := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_forcing_common_moments A K hA hK
  refine ⟨N,?_⟩
  intro n hn d R D h hR r η τ hr hrange hη hηupper hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu
  obtain ⟨hκ,hε⟩:=hN n hn d R hR r η hr hrange hη hηupper
  have hq : 1 ≤ A*logScale n := by nlinarith [logScale_one_le n]
  exact weightedForcing_sum_norm_sq_le R D h η r τ (A*logScale n)
    dampingMomentConstant (errorMomentCoefficient A n) hr hτ hτ1 hq hqτ
    dampingMomentConstant_nonneg (errorMomentCoefficient_nonneg A (by linarith) n)
    hκ hε fD fu hfDM hfuM hfD hfu

end NegativeVotingStructuredSwitchingMoments
