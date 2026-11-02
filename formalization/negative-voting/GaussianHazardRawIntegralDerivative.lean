import GaussianHazardKernelPathDerivative
import GaussianHazardMomentEnvelope

/-! Gaussian-box domination for raw threshold hazard derivatives. The
bounds retain every label and cover the analytic diagonal. They provide
actual dominated integral differentiation along C1 parameter paths. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WeakSimplex
open scoped BigOperators ENNReal Classical Topology
namespace NegativeVotingHazardRawIntegralDerivative
open NegativeVotingDiagonalHazardDifferentiation NegativeVotingHazardPolynomialBounds
  NegativeVotingHazardIntegrability NegativeVotingDensityMomentBounds
  NegativeVotingHazardMomentEnvelope NegativeVotingHazardKernelPathDerivative
variable {m : ℕ}

/-- One common integrable Gaussian envelope on a positive scale/offset box. -/
theorem gaussianDensity_box_envelope (σ h x s S H₀ : ℝ)
    (hs : 0<s) (hσ : s≤σ) (hS : σ≤S) (hh : |h|≤H₀) :
    gaussianDensity σ h x≤
      (normalPDF 0/s*Real.exp (H₀^2/(2*S^2)))*Real.exp (-(1/2:ℝ)*(x/S)^2/2) := by
  have hσ0:=hs.trans_le hσ
  have hS0:=hσ0.trans_le hS
  have hH0:0≤H₀:=(abs_nonneg _).trans hh
  have hσ2:σ^2≤S^2:=pow_le_pow_left₀ hσ0.le hS 2
  have hhh:h^2≤H₀^2:=by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg h) hh 2
  have hfirst : (x-h)^2/S^2≤(x-h)^2/σ^2:=
    div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hσ0) hσ2
  have hsecond : x^2/2-H₀^2≤(x-h)^2:=by nlinarith [sq_nonneg (x-2*h)]
  have hineq:-( (x-h)/σ)^2/2≤H₀^2/(2*S^2)-(1/2:ℝ)*(x/S)^2/2:=by
    have hd:=div_le_div_of_nonneg_right hsecond (sq_nonneg S)
    have hh:=mul_le_mul_of_nonneg_right (neg_le_neg (hd.trans hfirst)) (by norm_num : (0:ℝ)≤1/2)
    convert hh using 1 <;> simp only [div_pow] <;> ring
  rw [gaussianDensity,NegativeVotingGaussianTail.normalPDF_ratio 0 ((x-h)/σ)]
  simp only [zero_pow (by norm_num : 2≠0),zero_sub]
  have he:=Real.exp_le_exp.mpr hineq
  rw [Real.exp_sub] at he
  calc
    _≤(normalPDF 0/s)*Real.exp (-((x-h)/σ)^2/2):=by
      have hd:=div_le_div_of_nonneg_left (normalPDF_pos 0).le hs hσ
      convert mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le using 1 <;> ring
    _≤(normalPDF 0/s)*(Real.exp (H₀^2/(2*S^2))/Real.exp ((1/2:ℝ)*(x/S)^2/2)):=
      mul_le_mul_of_nonneg_left he (by positivity [normalPDF_pos 0])
    _=_:=by
      have hn:-(1/2:ℝ)*(x/S)^2/2= -((1/2:ℝ)*(x/S)^2/2):=by ring
      rw [hn,Real.exp_neg]
      ring

def transportSize (σ h ζ η : ℝ) : ℝ := |η-h*ζ/σ|+|ζ/σ|
def densitySize (σ h ζ η : ℝ) : ℝ :=
  |-ζ/σ-h*η/σ^2+h^2*ζ/σ^3|+|η/σ^2-2*h*ζ/σ^3|+|ζ/σ^3|

theorem transportSpeed_polynomial (σ h ζ η x : ℝ) :
    |transportSpeed σ h ζ η x|≤transportSize σ h ζ η*(1+|x|) := by
  have he:transportSpeed σ h ζ η x=(η-h*ζ/σ)+(ζ/σ)*x:=by unfold transportSpeed;ring
  rw [he]
  have hh:=abs_add_le (η-h*ζ/σ) ((ζ/σ)*x)
  rw [abs_mul] at hh
  unfold transportSize
  nlinarith [mul_nonneg (abs_nonneg (η-h*ζ/σ)) (abs_nonneg x),abs_nonneg (ζ/σ)]

theorem densityLogDerivative_polynomial (σ h ζ η x : ℝ) :
    |densityLogDerivative σ h ζ η x|≤densitySize σ h ζ η*(1+|x|)^2 := by
  let a:=-ζ/σ-h*η/σ^2+h^2*ζ/σ^3
  let b:=η/σ^2-2*h*ζ/σ^3
  let c:=ζ/σ^3
  have he:densityLogDerivative σ h ζ η x=a+b*x+c*x^2:=by dsimp [densityLogDerivative,a,b,c];ring
  have h1:1≤(1+|x|)^2:=by nlinarith [abs_nonneg x]
  have h2:|x|≤(1+|x|)^2:=by nlinarith [abs_nonneg x]
  have h3:x^2≤(1+|x|)^2:=by nlinarith [abs_nonneg x,sq_abs x]
  have hh:|a+b*x+c*x^2|≤|a|+|b| *|x|+|c| *x^2:=by
    have hh:=(abs_add_le (a+b*x) (c*x^2)).trans (add_le_add (abs_add_le a (b*x)) (le_refl |c*x^2|))
    simpa only [abs_mul,abs_of_nonneg (sq_nonneg x)] using hh
  rw [he]
  have hA:=mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have hB:=mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
  have hC:=mul_le_mul_of_nonneg_left h3 (abs_nonneg c)
  change |a+b*x+c*x^2|≤(|a|+|b|+|c|)*(1+|x|)^2
  nlinarith

@[fun_prop] theorem hazardPairLogDerivative_continuous (σ h ζ η : Fin m→ℝ) (i j : Fin m) :
    Continuous (fun x=>hazardPairLogDerivative σ h ζ η x i j) := by
  unfold hazardPairLogDerivative totalHazardFlux densityLogDerivative transportSpeed
  have hc k:=continuous_gaussianHazard (σ k) (h k)
  fun_prop

theorem hazardPairLogDerivative_polynomial (σ h ζ η : Fin m→ℝ)
    (s H₀ x : ℝ) (hs : 0<s) (hσ : ∀k,s≤σ k) (hh : ∀k,|h k|≤H₀)
    (B D : Fin m→ℝ) (hB : ∀k,transportSize (σ k) (h k) (ζ k) (η k)≤B k)
    (hD : ∀k,densitySize (σ k) (h k) (ζ k) (η k)≤D k) (i j : Fin m) :
    |hazardPairLogDerivative σ h ζ η x i j|≤
      (D i+D j+linearHazardConstant s H₀*(B i+B j+∑k,B k))*(1+|x|)^2 := by
  let P:=1+|x|
  let C:=linearHazardConstant s H₀
  have hP:0≤P:=by dsimp [P];positivity
  have hB0 k:0≤B k:=((by unfold transportSize;positivity : 0≤transportSize (σ k) (h k) (ζ k) (η k))).trans (hB k)
  have hD0 k:0≤D k:=((by unfold densitySize;positivity : 0≤densitySize (σ k) (h k) (ζ k) (η k))).trans (hD k)
  have hC:0≤C:=linearHazardConstant_nonneg s H₀ hs ((abs_nonneg (h i)).trans (hh i))
  have ha k:|gaussianHazard (σ k) (h k) x|≤C*P:=by
    rw [abs_of_pos (gaussianHazard_pos _ _ _ (hs.trans_le (hσ k)))]
    exact uniform_hazard_polynomial _ _ _ s H₀ hs (hσ k) ((abs_nonneg _).trans (hh k)) (hh k)
  have hb k:|transportSpeed (σ k) (h k) (ζ k) (η k) x|≤B k*P:=
    (transportSpeed_polynomial _ _ _ _ _).trans (mul_le_mul_of_nonneg_right (hB k) hP)
  have hd k:|densityLogDerivative (σ k) (h k) (ζ k) (η k) x|≤D k*P^2:=
    (densityLogDerivative_polynomial _ _ _ _ _).trans (mul_le_mul_of_nonneg_right (hD k) (sq_nonneg P))
  have hab k:|gaussianHazard (σ k) (h k) x*transportSpeed (σ k) (h k) (ζ k) (η k) x|≤C*B k*P^2:=by
    rw [abs_mul]
    exact (mul_le_mul (ha k) (hb k) (abs_nonneg _) (mul_nonneg hC hP)).trans_eq (by ring)
  have hsum:|totalHazardFlux σ h ζ η x|≤C*(∑k,B k)*P^2:=by
    unfold totalHazardFlux
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hh:=Finset.sum_le_sum (fun k (_:k∈Finset.univ)=>hab k)
    simpa only [Finset.sum_mul,Finset.mul_sum,mul_assoc] using hh
  unfold hazardPairLogDerivative
  have h1:|densityLogDerivative (σ i) (h i) (ζ i) (η i) x+
      densityLogDerivative (σ j) (h j) (ζ j) (η j) x|≤D i*P^2+D j*P^2:=
    (abs_add_le _ _).trans (add_le_add (hd i) (hd j))
  have h2:=(abs_add_le _ (gaussianHazard (σ i) (h i) x*transportSpeed (σ i) (h i) (ζ i) (η i) x)).trans (add_le_add h1 (hab i))
  have h3:=(abs_add_le _ (gaussianHazard (σ j) (h j) x*transportSpeed (σ j) (h j) (ζ j) (η j) x)).trans (add_le_add h2 (hab j))
  have h4:=(abs_sub _ (totalHazardFlux σ h ζ η x)).trans (add_le_add h3 hsum)
  convert h4 using 1 <;> dsimp [C,P] <;> ring

theorem raw_derivative_box_bound (σ h ζ η : Fin m→ℝ)
    (s S H₀ x : ℝ) (hs : 0<s) (hσ : ∀k,s≤σ k) (hS : ∀k,σ k≤S)
    (hh : ∀k,|h k|≤H₀) (B D : Fin m→ℝ)
    (hB : ∀k,transportSize (σ k) (h k) (ζ k) (η k)≤B k)
    (hD : ∀k,densitySize (σ k) (h k) (ζ k) (η k)≤D k) (i j : Fin m) :
    |hazardPairDensity σ h x i j*hazardPairLogDerivative σ h ζ η x i j|≤
      ((normalPDF 0/s*Real.exp (H₀^2/(2*S^2)))*linearHazardConstant s H₀*
        (D i+D j+linearHazardConstant s H₀*(B i+B j+∑k,B k)))*
        (Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^3) := by
  have hH0:0≤H₀:=(abs_nonneg _).trans (hh i)
  have hc:=linearHazardConstant_nonneg s H₀ hs hH0
  have hr:hazardPairDensity σ h x i j≤
      ((normalPDF 0/s*Real.exp (H₀^2/(2*S^2)))*Real.exp (-(1/2:ℝ)*(x/S)^2/2))*
        (linearHazardConstant s H₀*(1+|x|)):=by
    exact (hazardPairDensity_le_density_hazard σ h (fun k=>hs.trans_le (hσ k)) x i j).trans
      (mul_le_mul (gaussianDensity_box_envelope _ _ _ s S H₀ hs (hσ i) (hS i) (hh i))
        (uniform_hazard_polynomial _ _ _ s H₀ hs (hσ j) hH0 (hh j))
        (gaussianHazard_pos _ _ _ (hs.trans_le (hσ j))).le (by positivity [normalPDF_pos 0]))
  rw [abs_mul,abs_of_nonneg (hazardPairDensity_nonneg σ h (fun k=>hs.trans_le (hσ k)) x i j)]
  have hp:=hazardPairLogDerivative_polynomial σ h ζ η s H₀ x hs hσ hh B D hB hD i j
  exact (mul_le_mul hr hp (abs_nonneg _) (by positivity [normalPDF_pos 0])).trans_eq (by ring)

/-- The raw threshold integral has its literal rho times log-derivative
integrand. All local box and polynomial domination are derived from C1. -/
theorem hazardPairIntegral_raw_hasDerivAt (σ h : ℝ→Fin m→ℝ) (t : ℝ)
    (hσ : ∀k,ContDiffAt ℝ 1 (fun z=>σ z k) t)
    (hh : ∀k,ContDiffAt ℝ 1 (fun z=>h z k) t)
    (hpos : ∀k,0<σ t k) (i j : Fin m) :
    HasDerivAt (fun z=>∫x,hazardPairDensity (σ z) (h z) x i j)
      (∫x,hazardPairDensity (σ t) (h t) x i j*
        hazardPairLogDerivative (σ t) (h t) (pathDerivative σ t) (pathDerivative h t) x i j) t := by
  letI : Nonempty (Fin m):=⟨i⟩
  obtain ⟨i₀,hi₀,hmin⟩:=Finset.exists_min_image Finset.univ (σ t) Finset.univ_nonempty
  let s:=σ t i₀/2
  let S:=(∑k,|σ t k|)+1
  let H₀:=(∑k,|h t k|)+1
  let B:=fun k=>transportSize (σ t k) (h t k) (pathDerivative σ t k) (pathDerivative h t k)+1
  let D:=fun k=>densitySize (σ t k) (h t k) (pathDerivative σ t k) (pathDerivative h t k)+1
  have hs:0<s:=by dsimp [s];exact half_pos (hpos i₀)
  have hS0:0<S:=by dsimp [S];positivity
  have hcσ k:ContinuousAt (fun z=>σ z k) t:=(hσ k).continuousAt
  have hch k:ContinuousAt (fun z=>h z k) t:=(hh k).continuousAt
  have hcdσ k:=pathDerivative_continuousAt σ t hσ k
  have hcdh k:=pathDerivative_continuousAt h t hh k
  have hlow:∀ᶠ z in 𝓝 t,∀k,s≤σ z k:=by
    rw [Filter.eventually_all]
    intro k
    have hk:=hmin k (Finset.mem_univ k)
    have hst:s<σ t k:=by dsimp [s];linarith [hpos i₀]
    exact ((hcσ k).eventually (lt_mem_nhds hst)).mono fun z hz=>hz.le
  have hupp:∀ᶠ z in 𝓝 t,∀k,σ z k≤S:=by
    rw [Filter.eventually_all]
    intro k
    have hk:|σ t k|≤∑l,|σ t l|:=Finset.single_le_sum (f:=fun l=>|σ t l|) (fun l _=>abs_nonneg _) (Finset.mem_univ k)
    have hst:σ t k<S:=by dsimp [S];linarith [le_abs_self (σ t k)]
    exact ((hcσ k).eventually (gt_mem_nhds hst)).mono fun z hz=>hz.le
  have hhoff:∀ᶠ z in 𝓝 t,∀k,|h z k|≤H₀:=by
    rw [Filter.eventually_all]
    intro k
    have hk:|h t k|≤∑l,|h t l|:=Finset.single_le_sum (f:=fun l=>|h t l|) (fun l _=>abs_nonneg _) (Finset.mem_univ k)
    have hst:|h t k|<H₀:=by dsimp [H₀];linarith
    exact ((hch k).abs.eventually (gt_mem_nhds hst)).mono fun z hz=>hz.le
  have hB:∀ᶠ z in 𝓝 t,∀k,transportSize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)≤B k:=by
    rw [Filter.eventually_all]
    intro k
    have hc:ContinuousAt (fun z=>transportSize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)) t:=by
      unfold transportSize
      fun_prop (disch:=exact (hpos k).ne')
    exact (hc.eventually (gt_mem_nhds (by dsimp [B];linarith))).mono fun z hz=>hz.le
  have hD:∀ᶠ z in 𝓝 t,∀k,densitySize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)≤D k:=by
    rw [Filter.eventually_all]
    intro k
    have hc:ContinuousAt (fun z=>densitySize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)) t:=by
      unfold densitySize
      fun_prop (disch:=first | exact (hpos k).ne' | exact pow_ne_zero _ (hpos k).ne')
    exact (hc.eventually (gt_mem_nhds (by dsimp [D];linarith))).mono fun z hz=>hz.le
  let G:={z | (∀k,s≤σ z k) ∧ (∀k,σ z k≤S) ∧ (∀k,|h z k|≤H₀) ∧
    (∀k,transportSize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)≤B k) ∧
    (∀k,densitySize (σ z k) (h z k) (pathDerivative σ z k) (pathDerivative h z k)≤D k) ∧
    (∀k,HasDerivAt (fun q=>σ q k) (pathDerivative σ z k) z) ∧
    (∀k,HasDerivAt (fun q=>h q k) (pathDerivative h z k) z)}
  have hG:G∈𝓝 t:=hlow.and (hupp.and (hhoff.and (hB.and (hD.and
    ((eventually_path_hasDerivAt σ t hσ).and (eventually_path_hasDerivAt h t hh))))))
  let C:=(normalPDF 0/s*Real.exp (H₀^2/(2*S^2)))*linearHazardConstant s H₀*
    (D i+D j+linearHazardConstant s H₀*(B i+B j+∑k,B k))
  have hbase:Integrable (fun x=>hazardPairDensity (σ t) (h t) x i j) volume:=by
    simpa using integrable_hazardPairDensity_polynomial (σ t) (h t) hpos i j 0
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=G) (bound:=fun x:ℝ=>C*(Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^3))
    (F:=fun z x=>hazardPairDensity (σ z) (h z) x i j)
    (F':=fun z x=>hazardPairDensity (σ z) (h z) x i j*
      hazardPairLogDerivative (σ z) (h z) (pathDerivative σ z) (pathDerivative h z) x i j)
    hG (by filter_upwards with z;exact (continuous_hazardPairDensity _ _ i j).aestronglyMeasurable)
    hbase (by exact ((continuous_hazardPairDensity _ _ i j).mul
      (hazardPairLogDerivative_continuous _ _ _ _ i j)).aestronglyMeasurable)
    ?_ ?_ ?_).2
  · filter_upwards with x
    intro z hz
    simpa only [Real.norm_eq_abs,C] using raw_derivative_box_bound (σ z) (h z) (pathDerivative σ z) (pathDerivative h z)
      s S H₀ x hs hz.1 hz.2.1 hz.2.2.1 B D hz.2.2.2.1 hz.2.2.2.2.1 i j
  · have hi:Integrable (fun x:ℝ=>Real.exp (-(1/2:ℝ)*(x/S)^2/2)*(1+|x|)^3) volume:=by
      simpa only [sub_zero] using integrable_gaussian_exp_kernel_polynomial S 0 (1/2) hS0 (by norm_num) 3
    exact hi.const_mul C
  · filter_upwards with x
    intro z hz
    exact hazardPairDensity_hasDerivAt (fun k q=>σ q k) (fun k q=>h q k) z x
      (pathDerivative σ z) (pathDerivative h z) hz.2.2.2.2.2.1 hz.2.2.2.2.2.2 (fun k=>hs.trans_le (hz.1 k)) i j

end NegativeVotingHazardRawIntegralDerivative
