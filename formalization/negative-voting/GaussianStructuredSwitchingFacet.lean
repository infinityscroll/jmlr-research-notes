import GaussianStructuredSwitchingMoments

/-! Actual affine-plane factors and Gaussian restrictions for the weighted
switching forcing. Gaussian coordinates are transported before taking traces;
no ambient almost-everywhere identity is restricted to a null hyperplane. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set
open scoped BigOperators RealInnerProductSpace ENNReal Classical
namespace NegativeVotingStructuredSwitchingFacet
open NegativeVotingDisintegration NegativeVotingPolynomialFacetGeometricTrace
  NegativeVotingActualFacetOUTrace NegativeVotingStructuredSwitchingNormal
  NegativeVotingStructuredSwitchingMoments NegativeVotingNormalTrace
  NegativeVotingSmoothingComposition NegativeVotingReciprocalDampingTube
  NegativeVotingSmoothErrorMoment NegativeVotingRegularPairCoefficient

section Products
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weighted_product_norm_le (q r Kκ Kε Kl Ku Kv : ℝ) (hq : 1 ≤ q) (hr : 0<r)
    (hKκ : 0 ≤ Kκ) (hKε : 0 ≤ Kε) (hKl : 0 ≤ Kl) (hKu : 0 ≤ Ku) (hKv : 0 ≤ Kv)
    (κ ε l u v : X→ℝ)
    (hκ : eLpNorm κ (ENNReal.ofReal (2*q)) μ ≤ ENNReal.ofReal Kκ)
    (hε : eLpNorm ε (ENNReal.ofReal (4*q)) μ ≤ ENNReal.ofReal Kε)
    (hl : eLpNorm l (ENNReal.ofReal (4*q)) μ ≤ ENNReal.ofReal Kl)
    (hu : eLpNorm u (ENNReal.ofReal (2*q)) μ ≤ ENNReal.ofReal Ku)
    (hv : eLpNorm v (ENNReal.ofReal (2*q)) μ ≤ ENNReal.ofReal Kv) :
    MemLp (fun x=>κ x*(r*ε x*|l x|+|u x-v x|/r)) (ENNReal.ofReal q) μ ∧
    realLp μ (ENNReal.ofReal q) (fun x=>κ x*(r*ε x*|l x|+|u x-v x|/r)) ≤
      Kκ*(r*Kε*Kl+(Ku+Kv)/r) := by
  let p:=ENNReal.ofReal q
  let p2:=ENNReal.ofReal (2*q)
  let p4:=ENNReal.ofReal (4*q)
  have hq0 : 0<q := by linarith
  haveI : ENNReal.HolderTriple p2 p2 p:=holder_double q hq0
  haveI : ENNReal.HolderTriple p4 p4 p2:=by
    convert holder_double (2*q) (by positivity) using 1 <;> dsimp [p2,p4] <;> congr 1 <;> ring
  have hp2 : 1 ≤ p2:=by simpa only [p2,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1:ℝ) ≤ 2*q by linarith)
  have hκm : MemLp κ p2 μ:=hκ.trans_lt ENNReal.ofReal_lt_top
  have hεm : MemLp ε p4 μ:=hε.trans_lt ENNReal.ofReal_lt_top
  have hlm : MemLp l p4 μ:=hl.trans_lt ENNReal.ofReal_lt_top
  have hum : MemLp u p2 μ:=hu.trans_lt ENNReal.ofReal_lt_top
  have hvm : MemLp v p2 μ:=hv.trans_lt ENNReal.ofReal_lt_top
  have hκr : realLp μ p2 κ ≤ Kκ:=by
    simpa only [realLp,ENNReal.toReal_ofReal hKκ] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hκ
  have hεr : realLp μ p4 ε ≤ Kε:=by
    simpa only [realLp,ENNReal.toReal_ofReal hKε] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hε
  have hlr : realLp μ p4 l ≤ Kl:=by
    simpa only [realLp,ENNReal.toReal_ofReal hKl] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
  have hur : realLp μ p2 u ≤ Ku:=by
    simpa only [realLp,ENNReal.toReal_ofReal hKu] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  have hvr : realLp μ p2 v ≤ Kv:=by
    simpa only [realLp,ENNReal.toReal_ofReal hKv] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
  have hlabs : MemLp (fun x=>|l x|) p4 μ:=by simpa only [Real.norm_eq_abs] using hlm.norm
  have hprod : MemLp (fun x=>ε x*|l x|) p2 μ:=hεm.mul hlabs
  have heprod : realLp μ p2 (fun x=>ε x*|l x|) ≤ Kε*Kl:=by
    exact (realLp_mul_le (r:=p2) hεm hlabs).trans
      (by rw [realLp_abs hlm]; exact mul_le_mul hεr hlr (realLp_nonneg _ _) hKε)
  have ham : MemLp (fun x=>|u x-v x|) p2 μ:=by simpa only [Real.norm_eq_abs,Pi.sub_apply] using (hum.sub hvm).norm
  have har : realLp μ p2 (fun x=>|u x-v x|) ≤ Ku+Kv:=by
    have heabs : realLp μ p2 (fun x=>|u x-v x|)=realLp μ p2 (fun x=>u x-v x):=by
      simpa only [Pi.sub_def] using realLp_abs (hum.sub hvm)
    rw [heabs]
    exact (realLp_sub_le hp2 hum hvm).trans (add_le_add hur hvr)
  have hsum : MemLp (fun x=>r*(ε x*|l x|)+r⁻¹*|u x-v x|) p2 μ:=
    (hprod.const_mul r).add (ham.const_mul r⁻¹)
  have hs:=realLp_add_le hp2 (hprod.const_mul r) (ham.const_mul r⁻¹)
  have hs' : realLp μ p2 (fun x=>r*(ε x*|l x|)+r⁻¹*|u x-v x|) ≤ r*Kε*Kl+(Ku+Kv)/r:=by
    rw [realLp_const_mul,realLp_const_mul,abs_of_pos hr,abs_of_pos (inv_pos.mpr hr)] at hs
    refine hs.trans ((add_le_add (mul_le_mul_of_nonneg_left heprod hr.le)
      (mul_le_mul_of_nonneg_left har (inv_nonneg.mpr hr.le))).trans_eq ?_)
    ring
  have hfinal : MemLp (fun x=>κ x*(r*(ε x*|l x|)+r⁻¹*|u x-v x|)) p μ:=hκm.mul hsum
  have hn:=(realLp_mul_le (r:=p) hκm hsum).trans
    (mul_le_mul hκr hs' (realLp_nonneg _ _) hKκ)
  have he : (fun x=>κ x*(r*(ε x*|l x|)+r⁻¹*|u x-v x|))=
      (fun x=>κ x*(r*ε x*|l x|+|u x-v x|/r)):=by funext x; ring
  rw [he] at hfinal hn
  exact ⟨hfinal,hn⟩
end Products

section Plane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k n : ℕ}

def projectedRow (w : E) (e : tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k) (v : E) : FSC.Coord k :=
  e ((tangentSpace w).orthogonalProjectionOnto v)

theorem projectedRow_norm_le (w : E) (e : tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k) (v : E) :
    ‖projectedRow w e v‖ ≤ ‖v‖ := by
  unfold projectedRow
  rw [e.norm_map]
  exact (tangentSpace w).norm_orthogonalProjectionOnto_apply_le v

theorem projectedRow_inner (w : E) (e : tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k)
    (v : E) (x : FSC.Coord k) :
    inner ℝ (projectedRow w e v) x = inner ℝ v ((e.symm x : tangentSpace w):E) := by
  calc
    _ = inner ℝ (e ((tangentSpace w).orthogonalProjectionOnto v)) (e (e.symm x)) := by
      rw [e.apply_symm_apply]
      rfl
    _ = inner ℝ ((tangentSpace w).orthogonalProjectionOnto v) (e.symm x) := e.inner_map_map _ _
    _ = _ := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (e.symm x) v

/-- The exact variable-exponent OU restriction norm on a literal ambient plane. -/
theorem ambient_plane_lq_le (w : E) (hw : ‖w‖=1)
    (e : tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k)
    {τ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (a : ℝ)
    (f : E→ℝ) (hfM : Measurable f) (hf : MemLp f 2 (stdGaussian E)) :
    eLpNorm (fun y:tangentSpace w=>ambientAverage τ f ((y:E)+a • w))
      (ENNReal.ofReal (1+(τ^2)⁻¹)) (stdGaussian (tangentSpace w)) ≤
      ENNReal.ofReal (Real.sqrt (normalRowSquare τ a))*eLpNorm f 2 (stdGaussian E) := by
  let T:=tangentCoordinateEquiv w e
  have hmap : (γFin k).map T=stdGaussian (tangentSpace w):=tangentCoordinatesInverse_map w e
  let g:=fun z:(Fin k→ℝ)×ℝ=>f (coordinateReconstruct w e z)
  have hgn:=coordinateReconstruct_memLp_and_norm w hw e f 2 hf
  have hh:=actual_product_normalTrace_lq_bound_sharp hτ hτ1 a g hgn.1
  rw [←hmap,eLpNorm_map_measure (by
    exact ((ambientAverage_measurable τ f hfM).comp (by fun_prop)).aestronglyMeasurable)
    T.measurable.aemeasurable]
  have he (y:Fin k→ℝ) : ambientAverage τ f (((T y:tangentSpace w):E)+a • w)=
      productGaussianAverage τ g (y,a):=ambientAverage_coordinateReconstruct w hw e τ f hfM (y,a)
  simp only [Function.comp_def]
  simp_rw [he]
  exact hh.trans_eq (congrArg (fun z:ℝ≥0∞=>_ * z) hgn.2)

/-- An affine score on the actual plane, retaining its offset exactly. -/
theorem affine_plane_lq_le (w : E) (e : tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k)
    (τ : ℝ) (hτ : 0<τ) (hτ1 : τ<1) (a c : ℝ) (v : E) :
    eLpNorm (fun y:tangentSpace w=>inner ℝ v ((y:E)+a • w)+c)
      (ENNReal.ofReal (1+(τ^2)⁻¹)) (stdGaussian (tangentSpace w)) ≤
      ENNReal.ofReal (τ⁻¹*(‖v‖+|a*inner ℝ v w+c|)) := by
  have hmp : MeasurePreserving e.symm (stdGaussian (FSC.Coord k)) (stdGaussian (tangentSpace w)):=
    ⟨e.symm.continuous.measurable,stdGaussian_map e.symm⟩
  rw [←eLpNorm_comp_measurePreserving (by fun_prop) hmp]
  have he x : inner ℝ v (((e.symm x:tangentSpace w):E)+a • w)+c=
      inner ℝ (projectedRow w e v) x+(a*inner ℝ v w+c):=by
    rw [inner_add_right,inner_smul_right,projectedRow_inner]
    ring
  simp only [Function.comp_def]
  simp_rw [he]
  exact (affineScore_lq_le τ hτ hτ1 (projectedRow w e v) (a*inner ℝ v w+c)).2.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (add_le_add (projectedRow_norm_le w e v) le_rfl) (inv_nonneg.mpr hτ.le)))

/-- Uniform common-factor moments on genuine Gaussian comparison planes.
The threshold is chosen before both ambient and tangent dimensions. -/
theorem exists_dimension_uniform_plane_common_moments
    (A K : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d k : ℕ,
      ∀ (R : Fin (n+2)→FSC.Coord d), (∀i,‖R i‖ ≤ 1) →
      ∀ (w:FSC.Coord d) (e:tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k), ‖w‖=1 →
      ∀ r η a D : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n → 0 ≤ D → a^2 ≤ D*logScale n →
      eLpNorm (fun y:tangentSpace w=>inverseKappa η (fun j=>inner ℝ (R j) ((y:FSC.Coord d)+a • w)))
        (ENNReal.ofReal (2*(A*logScale n))) (stdGaussian (tangentSpace w)) ≤
        ENNReal.ofReal (2*Real.exp 1*Real.exp (1+(2*D+2)/4)) ∧
      eLpNorm (fun y:tangentSpace w=>smoothPairError n r
        (fun j=>inner ℝ (R j) ((y:FSC.Coord d)+a • w))/r)
        (ENNReal.ofReal (4*(A*logScale n))) (stdGaussian (tangentSpace w)) ≤
        ENNReal.ofReal (momentConstant (4*A)*logScale n*Real.sqrt (logScale n)*Real.exp (1+D/4)) := by
  obtain ⟨Nε,hNε⟩:=NegativeVotingDimensionUniformErrorBounds.exists_dimension_uniform_error_moments
    (4*A) (by linarith)
  obtain ⟨Nκ,hNκ⟩:=exists_dimension_uniform_damping_tube (2*A) K (by linarith) hK
  refine ⟨max Nε Nκ,?_⟩
  intro n hn d k R hR w e hw r η a D hr hrange hη hηupper hD ha
  let P:=fun i=>projectedRow w e (R i)
  let c:=fun i=>a*inner ℝ (R i) w
  have hP i : ‖P i‖ ≤ 1 := (projectedRow_norm_le w e (R i)).trans (hR i)
  have hc i : (c i)^2 ≤ D*logScale n := by
    have hi : |inner ℝ (R i) w| ≤ 1 := (abs_real_inner_le_norm _ _).trans (by rw [hw,mul_one]; exact hR i)
    have hs : (inner ℝ (R i) w)^2 ≤ 1 := by
      simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) hi 2
    calc
      _=a^2*(inner ℝ (R i) w)^2:=by dsimp [c]; ring
      _≤a^2*1:=mul_le_mul_of_nonneg_left hs (sq_nonneg a)
      _≤D*logScale n:=by simpa using ha
  have hmp : MeasurePreserving e.symm (stdGaussian (FSC.Coord k)) (stdGaussian (tangentSpace w)):=
    ⟨e.symm.continuous.measurable,stdGaussian_map e.symm⟩
  have he (x:FSC.Coord k) (j:Fin (n+2)) :
      inner ℝ (R j) (((e.symm x:tangentSpace w):FSC.Coord d)+a • w)=c j+inner ℝ (P j) x := by
    dsimp [c,P]
    rw [inner_add_right,inner_smul_right,projectedRow_inner]
    ring
  obtain ⟨W,hWM,hW0,hWmem,hWnorm,hWt⟩:=hNκ n ((le_max_right _ _).trans hn) k P hP c D hD hc
  have hκM : Measurable (fun x:FSC.Coord k=>inverseKappa η (fun j=>c j+inner ℝ (P j) x)):=by
    simp only [inverseKappa_eq_exp,scoreEnergy]
    fun_prop
  have hκW x : inverseKappa η (fun j=>c j+inner ℝ (P j) x) ≤ W x := by
    have hh:=((hWt r η hr hrange hη hηupper (fun _=>0) (by intro i; norm_num) x).2
      0 (by constructor <;> norm_num)).1
    simpa using hh
  have hκnorm := (eLpNorm_mono (p:=ENNReal.ofReal ((2*A)*logScale n))
    (μ:=stdGaussian (FSC.Coord k)) hκM.aestronglyMeasurable (fun x=>by
      simpa only [Real.norm_eq_abs,abs_of_pos (inverseKappa_pos _ _),abs_of_nonneg (hW0 x)]
        using hκW x)).trans hWnorm
  have hε:=hNε n ((le_max_left _ _).trans hn) k P hP c (fun _=>0) D r hD hc
    (by intro i; norm_num) hr hrange
  constructor
  · rw [←eLpNorm_comp_measurePreserving (by
      simp only [inverseKappa_eq_exp,scoreEnergy]; fun_prop) hmp]
    simp only [Function.comp_def]
    simp_rw [he]
    convert hκnorm using 1
    · congr 2; ring
    · rw [ENNReal.ofReal_mul (by positivity)]
  · rw [←eLpNorm_comp_measurePreserving (by
      exact ((smoothPairError_contDiff n r).continuous.measurable.comp (by fun_prop)).div_const r |>.aestronglyMeasurable) hmp]
    simp only [Function.comp_def]
    simp_rw [he]
    convert hε.2.1 using 1
    · congr 2; ring
    · rw [ENNReal.ofReal_mul (by
        have hC:=momentConstant_nonneg (4*A) (by linarith)
        have hL:0 ≤ logScale n:=by linarith [logScale_one_le n]
        positivity)]


/-- The literal forcing restricted to a comparison plane. The OU row factor
is explicit and is paid only at the common smoothing correlation. -/
theorem weightedForcing_plane_label_norm_le {d : ℕ}
    (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ)
    (w : FSC.Coord d) (hw : ‖w‖=1) (e : tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k)
    (η r τ q a Kκ Kε : ℝ) (hr : 0<r) (hτ : 0<τ) (hτ1 : τ<1)
    (hq : 1 ≤ q) (hqτ : 4*q ≤ 1+(τ^2)⁻¹) (hKκ : 0 ≤ Kκ) (hKε : 0 ≤ Kε)
    (hκ : eLpNorm (fun y:tangentSpace w=>inverseKappa η (fun j=>inner ℝ (R j) ((y:FSC.Coord d)+a • w)))
      (ENNReal.ofReal (2*q)) (stdGaussian (tangentSpace w)) ≤ ENNReal.ofReal Kκ)
    (hε : eLpNorm (fun y:tangentSpace w=>smoothPairError n r
      (fun j=>inner ℝ (R j) ((y:FSC.Coord d)+a • w))/r)
      (ENNReal.ofReal (4*q)) (stdGaussian (tangentSpace w)) ≤ ENNReal.ofReal Kε)
    (fD fu : Fin (n+2)→FSC.Coord d→ℝ)
    (hfDM : ∀i,Measurable (fD i)) (hfuM : ∀i,Measurable (fu i))
    (hfD : ∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d)))
    (hfu : ∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) (i : Fin (n+2)) :
    MemLp (fun y:tangentSpace w=>weightedForcing R D h η r τ fD fu ((y:FSC.Coord d)+a • w) i)
      (ENNReal.ofReal q) (stdGaussian (tangentSpace w)) ∧
    realLp (stdGaussian (tangentSpace w)) (ENNReal.ofReal q)
      (fun y:tangentSpace w=>weightedForcing R D h η r τ fD fu ((y:FSC.Coord d)+a • w) i) ≤
      Kκ*(r*Kε*τ⁻¹*(‖D i‖+|a*inner ℝ (D i) w+h i|)+
        Real.sqrt (normalRowSquare τ a)*
          (realLp (stdGaussian (FSC.Coord d)) 2 (fD i)+
            realLp (stdGaussian (FSC.Coord d)) 2 (fu i))/r) := by
  let μ:=stdGaussian (tangentSpace w)
  let μ0:=stdGaussian (FSC.Coord d)
  let C:=Real.sqrt (normalRowSquare τ a)
  let κ:=fun y:tangentSpace w=>inverseKappa η (fun j=>inner ℝ (R j) ((y:FSC.Coord d)+a • w))
  let ε:=fun y:tangentSpace w=>smoothPairError n r (fun j=>inner ℝ (R j) ((y:FSC.Coord d)+a • w))/r
  let l:=fun y:tangentSpace w=>inner ℝ (D i) ((y:FSC.Coord d)+a • w)+h i
  let u:=fun y:tangentSpace w=>ambientAverage τ (fD i) ((y:FSC.Coord d)+a • w)
  let v:=fun y:tangentSpace w=>ambientAverage τ (fu i) ((y:FSC.Coord d)+a • w)
  have hq0 : 0<q:=by linarith
  have hp4 : ENNReal.ofReal (4*q) ≤ ENNReal.ofReal (1+(τ^2)⁻¹):=ENNReal.ofReal_le_ofReal hqτ
  have hp2 : ENNReal.ofReal (2*q) ≤ ENNReal.ofReal (1+(τ^2)⁻¹):=ENNReal.ofReal_le_ofReal (by linarith)
  have hl := (eLpNorm_le_eLpNorm_of_exponent_le (μ:=μ) (f:=l) hp4).trans
    (affine_plane_lq_le w e τ hτ hτ1 a (h i) (D i))
  have hu : eLpNorm u (ENNReal.ofReal (2*q)) μ ≤ ENNReal.ofReal (C*realLp μ0 2 (fD i)) := by
    have hb := (eLpNorm_le_eLpNorm_of_exponent_le (μ:=μ) (f:=u) hp2).trans
      (ambient_plane_lq_le w hw e hτ hτ1 a (fD i) (hfDM i) (hfD i))
    refine hb.trans_eq ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),realLp,ENNReal.ofReal_toReal (hfD i).eLpNorm_ne_top]
  have hv : eLpNorm v (ENNReal.ofReal (2*q)) μ ≤ ENNReal.ofReal (C*realLp μ0 2 (fu i)) := by
    have hb := (eLpNorm_le_eLpNorm_of_exponent_le (μ:=μ) (f:=v) hp2).trans
      (ambient_plane_lq_le w hw e hτ hτ1 a (fu i) (hfuM i) (hfu i))
    refine hb.trans_eq ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),realLp,ENNReal.ofReal_toReal (hfu i).eLpNorm_ne_top]
  have hh := weighted_product_norm_le q r Kκ Kε
    (τ⁻¹*(‖D i‖+|a*inner ℝ (D i) w+h i|))
    (C*realLp μ0 2 (fD i)) (C*realLp μ0 2 (fu i)) hq hr hKκ hKε
    (by positivity) (mul_nonneg (Real.sqrt_nonneg _) (realLp_nonneg _ _))
    (mul_nonneg (Real.sqrt_nonneg _) (realLp_nonneg _ _)) κ ε l u v hκ hε hl hu hv
  have he : (fun y:tangentSpace w=>κ y*(r*ε y*|l y|+|u y-v y|/r))=
      (fun y:tangentSpace w=>weightedForcing R D h η r τ fD fu ((y:FSC.Coord d)+a • w) i) := by
    funext y
    dsimp [κ,ε,l,u,v,weightedForcing]
    field_simp
  rw [he] at hh
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  dsimp [C,μ0]
  ring


def planeDampingCoefficient (b : ℝ) : ℝ := 2*Real.exp 1*Real.exp (1+(2*b+2)/4)
def planeErrorCoefficient (A b : ℝ) (n : ℕ) : ℝ :=
  momentConstant (4*A)*logScale n*Real.sqrt (logScale n)*Real.exp (1+b/4)

/-- Actual weighted-forcing moments on every comparison plane, with both
common-factor moment estimates derived at a dimension-first noise threshold. -/
theorem exists_dimension_uniform_weightedForcing_plane_norm_le
    (A K : ℝ) (hA : 1 ≤ A) (hK : 0 ≤ K) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d k : ℕ,
      ∀ (R D : Fin (n+2)→FSC.Coord d) (h : Fin (n+2)→ℝ), (∀i,‖R i‖ ≤ 1) →
      ∀ (w:FSC.Coord d) (e:tangentSpace w ≃ₗᵢ[ℝ] FSC.Coord k), ‖w‖=1 →
      ∀ r η τ a b : ℝ, 0<r → r ≤ 1/((n:ℝ)+1) → 0 ≤ η →
        η ≤ K*r^2*logScale n → 0 ≤ b → a^2 ≤ b*logScale n →
        0<τ → τ<1 → 4*(A*logScale n) ≤ 1+(τ^2)⁻¹ →
      ∀ (fD fu : Fin (n+2)→FSC.Coord d→ℝ),
      (∀i,Measurable (fD i)) → (∀i,Measurable (fu i)) →
      (∀i,MemLp (fD i) 2 (stdGaussian (FSC.Coord d))) →
      (∀i,MemLp (fu i) 2 (stdGaussian (FSC.Coord d))) →
      ∀ i : Fin (n+2),
      MemLp (fun y:tangentSpace w=>weightedForcing R D h η r τ fD fu ((y:FSC.Coord d)+a • w) i)
        (ENNReal.ofReal (A*logScale n)) (stdGaussian (tangentSpace w)) ∧
      realLp (stdGaussian (tangentSpace w)) (ENNReal.ofReal (A*logScale n))
        (fun y:tangentSpace w=>weightedForcing R D h η r τ fD fu ((y:FSC.Coord d)+a • w) i) ≤
        planeDampingCoefficient b*(r*planeErrorCoefficient A b n*τ⁻¹*
          (‖D i‖+|a*inner ℝ (D i) w+h i|)+Real.sqrt (normalRowSquare τ a)*
          (realLp (stdGaussian (FSC.Coord d)) 2 (fD i)+
            realLp (stdGaussian (FSC.Coord d)) 2 (fu i))/r) := by
  obtain ⟨N,hN⟩:=exists_dimension_uniform_plane_common_moments A K hA hK
  refine ⟨N,?_⟩
  intro n hn d k R D h hR w e hw r η τ a b hr hrange hη hηupper hb ha hτ hτ1 hqτ fD fu hfDM hfuM hfD hfu i
  obtain ⟨hκ,hε⟩:=hN n hn d k R hR w e hw r η a b hr hrange hη hηupper hb ha
  have hq : 1 ≤ A*logScale n:=by nlinarith [logScale_one_le n]
  have hC : 0 ≤ planeErrorCoefficient A b n:=by
    have hC:=momentConstant_nonneg (4*A) (by linarith)
    have hL:0 ≤ logScale n:=by linarith [logScale_one_le n]
    unfold planeErrorCoefficient
    positivity
  exact weightedForcing_plane_label_norm_le R D h w hw e η r τ (A*logScale n) a
    (planeDampingCoefficient b) (planeErrorCoefficient A b n) hr hτ hτ1 hq hqτ
    (by unfold planeDampingCoefficient; positivity) hC hκ hε fD fu hfDM hfuM hfD hfu i

/-- Restriction of a real Lq bound to the actual measurable facet event. -/
theorem restricted_square_le_of_realLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (F : Set X) (q C : ℝ) (hq : 2 ≤ q)
    (v : X→ℝ) (hv : MemLp v (ENNReal.ofReal q) μ)
    (hn : realLp μ (ENNReal.ofReal q) v ≤ C) :
    (∫ x in F,(v x)^2 ∂μ) ≤ C^2*(μ F).toReal^(1-2/q) := by
  have h := NegativeVotingNormalTraceAllExponents.set_integral_sq_le_l2q μ F (q/2)
    (by linarith) v (by simpa only [show 2*(q/2)=q by ring] using hv)
  simp only [show 2*(q/2)=q by ring,show 1-1/(q/2)=1-2/q by ring] at h
  exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (realLp_nonneg _ _) hn 2)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _))

/-- Polynomially probable facets cost only a fixed constant when the Lq
exponent is a fixed logarithmic multiple. -/
theorem probability_rpow_gain {p q L : ℝ} (hp : 0<p) (hq : 0<q)
    (hlog : -Real.log p ≤ 4096*L) (hscale : 8192*L ≤ q) :
    p^(1-2/q) ≤ Real.exp 1*p := by
  have he : Real.log p*(1-2/q) ≤ Real.log p+1 := by
    have hh : -(2*Real.log p) ≤ q:=by linarith
    have hd : -(2*Real.log p)/q ≤ 1 := (div_le_one hq).mpr hh
    calc
      _=Real.log p+(-(2*Real.log p)/q):=by ring
      _≤Real.log p+1:=add_le_add le_rfl hd
  calc
    _=Real.exp (Real.log p*(1-2/q)):=Real.rpow_def_of_pos hp _
    _≤Real.exp (Real.log p+1):=Real.exp_le_exp.mpr he
    _=Real.exp 1*p:=by rw [Real.exp_add,Real.exp_log hp]; ring

end Plane

end NegativeVotingStructuredSwitchingFacet
