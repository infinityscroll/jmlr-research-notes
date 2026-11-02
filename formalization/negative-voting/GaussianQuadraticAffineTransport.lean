import GaussianCapPolarizedStein
import GaussianQuadraticMovingCap
import GaussianAffineOperatorDerivative

/-! Actual coherent affine transport of quadratic Gaussian cell tests.
The bulk expression is derived from literal moving-facet integrals and
proved polynomial Stein identities, not supplied as a transport premise. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory WeakSimplex Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology ENNReal
namespace NegativeVotingQuadraticAffineTransport
open NegativeVotingMovingCap NegativeVotingPolyhedral NegativeVotingDisintegration
  NegativeVotingFanScore NegativeVotingAffineCapDerivative NegativeVotingAffineOperatorDerivative
  NegativeVotingCapPolarizedStein
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem gaussian_bilinear_memLp_two (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (v y : FSC.Coord d) : MemLp (fun x=>inner ℝ v x*inner ℝ y x) 2 μ := by
  haveI : ENNReal.HolderTriple (4:ℝ≥0∞) 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
    norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩
  have hv := (IsGaussian.memLp_id μ 4 (by norm_num)).const_inner (𝕜:=ℝ) v
  have hy := (IsGaussian.memLp_id μ 4 (by norm_num)).const_inner (𝕜:=ℝ) y
  simpa only [Pi.mul_def,id_eq] using hv.mul (r:=2) hy

 theorem gaussian_trilinear_integrable (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (v y a : FSC.Coord d) : Integrable (fun x=>inner ℝ v x*inner ℝ y x*inner ℝ a x) μ := by
  simpa only [Pi.mul_def,id_eq] using (gaussian_bilinear_memLp_two μ v y).integrable_mul
    (IsGaussian.memLp_two_id.const_inner (𝕜:=ℝ) a)

 theorem bilinear_growth (v y x : FSC.Coord d) :
    |inner ℝ v x*inner ℝ y x|≤(‖v‖*‖y‖)*(1+‖x‖^2) := by
  rw [abs_mul]
  calc
    _ ≤ (‖v‖*‖x‖)*(‖y‖*‖x‖) := mul_le_mul (abs_real_inner_le_norm v x)
      (abs_real_inner_le_norm y x) (abs_nonneg _) (by positivity)
    _ = (‖v‖*‖y‖)*‖x‖^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

 theorem capJointDerivative_bilinear_ambient (w : ι→FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι→ℝ) (v y : FSC.Coord d) (δ : Parameters d ι) :
    capJointDerivative w b (fun x=>inner ℝ v x*inner ℝ y x) δ=
      ∑ j,normalPDF (b j)*∫ x in faceEvent w b j,
        (inner ℝ v x*inner ℝ y x)*(δ.2 j-inner ℝ (δ.1 j) x)
          ∂FSC.sliceLaw (w j) (b j) := by
  rw [NegativeVotingQuadraticMovingCap.capJointDerivative_apply w hw b _ (by fun_prop)
    (‖v‖*‖y‖) (by positivity) (bilinear_growth v y)]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact tangentFace_integral_eq_slice w b j (hw j)
    (fun x=>(inner ℝ v x*inner ℝ y x)*(δ.2 j-inner ℝ (δ.1 j) x)) (by fun_prop)

 theorem face_bilinear_affine_integral (w : ι→FSC.Coord d) (b : ι→ℝ) (j : ι)
    (v y u a z : FSC.Coord d) :
    (∫ x in faceEvent w b j,(inner ℝ v x*inner ℝ y x)*
      (-inner ℝ (w j) z-inner ℝ (w j) u*inner ℝ a x) ∂FSC.sliceLaw (w j) (b j))=
      -inner ℝ (w j) z*(∫ x in faceEvent w b j,inner ℝ v x*inner ℝ y x
        ∂FSC.sliceLaw (w j) (b j))-
      inner ℝ (w j) u*(∫ x in faceEvent w b j,inner ℝ v x*inner ℝ y x*inner ℝ a x
        ∂FSC.sliceLaw (w j) (b j)) := by
  letI := sliceLaw_isGaussian (w j) (b j)
  have hF := ((gaussian_bilinear_memLp_two (FSC.sliceLaw (w j) (b j)) v y).integrable
    (by norm_num : (1:ℝ≥0∞)≤2)).restrict (s:=faceEvent w b j)
  have hFA := (gaussian_trilinear_integrable (FSC.sliceLaw (w j) (b j)) v y a).restrict
    (s:=faceEvent w b j)
  have he : (fun x:FSC.Coord d=>(inner ℝ v x*inner ℝ y x)*
      (-inner ℝ (w j) z-inner ℝ (w j) u*inner ℝ a x))=
      fun x=>(-inner ℝ (w j) z)*(inner ℝ v x*inner ℝ y x)-
        inner ℝ (w j) u*(inner ℝ v x*inner ℝ y x*inner ℝ a x) := by funext x; ring
  rw [he,integral_sub (hF.const_mul _) (hFA.const_mul _),integral_const_mul,integral_const_mul]

/-- The actual quadratic transport rule for a single rank-one affine field.
Every bulk and face integral is literal; no regularity of offset selection
or acceleration is an input. -/
 theorem capJointDerivative_bilinear_rankOne (w : ι→FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι→ℝ) (hb : FSC.NoCoincident w b)
    (v y u a z : FSC.Coord d) :
    capJointDerivative w b (fun x=>inner ℝ v x*inner ℝ y x)
      (affineRankOneVelocity w u a z)=
      (∫ x in FSC.cap w b,inner ℝ u x*(inner ℝ v x*inner ℝ y x*inner ℝ a x)
        ∂stdGaussian (FSC.Coord d))-
      (∫ x in FSC.cap w b,inner ℝ u v*(inner ℝ y x*inner ℝ a x)+
        inner ℝ u y*(inner ℝ v x*inner ℝ a x)+inner ℝ u a*(inner ℝ v x*inner ℝ y x)
        ∂stdGaussian (FSC.Coord d))+
      (∫ x in FSC.cap w b,inner ℝ z x*(inner ℝ v x*inner ℝ y x)
        ∂stdGaussian (FSC.Coord d))-
      (∫ x in FSC.cap w b,inner ℝ z v*inner ℝ y x+inner ℝ z y*inner ℝ v x
        ∂stdGaussian (FSC.Coord d)) := by
  have h2 := gaussian_cap_bilinear_stein w hw b hb z v y
  have h3 := gaussian_cap_trilinear_stein w hw b hb u v y a
  calc
    _ = ∑ j,(-(normalPDF (b j)*inner ℝ (w j) z)*
          (∫ x in faceEvent w b j,inner ℝ v x*inner ℝ y x ∂FSC.sliceLaw (w j) (b j))-
        (normalPDF (b j)*inner ℝ (w j) u)*
          (∫ x in faceEvent w b j,inner ℝ v x*inner ℝ y x*inner ℝ a x ∂FSC.sliceLaw (w j) (b j))) := by
      rw [capJointDerivative_bilinear_ambient w hw b]
      apply Finset.sum_congr rfl
      intro j _
      simp only [affineRankOneVelocity,real_inner_smul_left]
      rw [face_bilinear_affine_integral]
      ring
    _ = _ := by
      simp only [neg_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
      linarith

theorem gaussian_quadrilinear_integrable (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (u v y a : FSC.Coord d) :
    Integrable (fun x=>inner ℝ u x*(inner ℝ v x*inner ℝ y x*inner ℝ a x)) μ := by
  have hh := (gaussian_bilinear_memLp_two μ u v).integrable_mul
    (gaussian_bilinear_memLp_two μ y a)
  apply hh.congr
  filter_upwards with x
  change (inner ℝ u x*inner ℝ v x)*(inner ℝ y x*inner ℝ a x)=_
  ring

 def rankOneBulk (v y u a z x : FSC.Coord d) : ℝ :=
   inner ℝ u x*(inner ℝ v x*inner ℝ y x*inner ℝ a x)-
     (inner ℝ u v*(inner ℝ y x*inner ℝ a x)+inner ℝ u y*(inner ℝ v x*inner ℝ a x)+
       inner ℝ u a*(inner ℝ v x*inner ℝ y x))+
     inner ℝ z x*(inner ℝ v x*inner ℝ y x)-
     (inner ℝ z v*inner ℝ y x+inner ℝ z y*inner ℝ v x)

 theorem rankOneBulk_integrable (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (v y u a z : FSC.Coord d) : Integrable (rankOneBulk v y u a z) μ := by
  have h2 (p q:FSC.Coord d) := (gaussian_bilinear_memLp_two μ p q).integrable
    (by norm_num : (1:ℝ≥0∞)≤2)
  have h1 (p:FSC.Coord d) := IsGaussian.integrable_dual μ (innerSL ℝ p)
  have h3 : Integrable (fun x=>inner ℝ z x*(inner ℝ v x*inner ℝ y x)) μ := by
    simpa only [mul_assoc] using gaussian_trilinear_integrable μ z v y
  exact (((gaussian_quadrilinear_integrable μ u v y a).sub
    (((h2 y a).const_mul _).add ((h2 v a).const_mul _)|>.add ((h2 v y).const_mul _))).add h3).sub
      (((h1 y).const_mul _).add ((h1 v).const_mul _))

 theorem capJointDerivative_bilinear_rankOne_bulk (w : ι→FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι→ℝ) (hb : FSC.NoCoincident w b)
    (v y u a z : FSC.Coord d) :
    capJointDerivative w b (fun x=>inner ℝ v x*inner ℝ y x)
      (affineRankOneVelocity w u a z)=
      ∫ x in FSC.cap w b,rankOneBulk v y u a z x ∂stdGaussian (FSC.Coord d) := by
  have h2 (p q:FSC.Coord d) := ((gaussian_bilinear_memLp_two (stdGaussian (FSC.Coord d)) p q).integrable
    (by norm_num : (1:ℝ≥0∞)≤2)).restrict (s:=FSC.cap w b)
  have h1 (p:FSC.Coord d) := (IsGaussian.integrable_dual (stdGaussian (FSC.Coord d))
    (innerSL ℝ p)).restrict (s:=FSC.cap w b)
  have h3 : Integrable (fun x=>inner ℝ z x*(inner ℝ v x*inner ℝ y x))
      ((stdGaussian (FSC.Coord d)).restrict (FSC.cap w b)) := by
    simpa only [mul_assoc] using (gaussian_trilinear_integrable (stdGaussian (FSC.Coord d)) z v y).restrict
      (s:=FSC.cap w b)
  have h4 := (gaussian_quadrilinear_integrable (stdGaussian (FSC.Coord d)) u v y a).restrict
    (s:=FSC.cap w b)
  have hG := (((h2 y a).const_mul (inner ℝ u v)).add ((h2 v a).const_mul (inner ℝ u y))).add
    ((h2 v y).const_mul (inner ℝ u a))
  have hL := ((h1 y).const_mul (inner ℝ z v)).add ((h1 v).const_mul (inner ℝ z y))
  have hs := integral_sub ((h4.sub hG).add h3) hL
  have ha := integral_add (h4.sub hG) h3
  have hs' := integral_sub h4 hG
  simp only [Pi.sub_def,Pi.add_def,innerSL_apply_apply] at hs ha hs'
  unfold rankOneBulk
  rw [capJointDerivative_bilinear_rankOne w hw b hb,hs,ha,hs']

 def affineBulk (v y : FSC.Coord d) (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z x : FSC.Coord d) : ℝ :=
    (inner ℝ v x*inner ℝ y x)*(inner ℝ x (A x)+inner ℝ z x-
      LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap)-
      inner ℝ v (A x+z)*inner ℝ y x-inner ℝ v x*inner ℝ y (A x+z)

 theorem affineBulk_decomposition (v y : FSC.Coord d)
    (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z x : FSC.Coord d) :
    affineBulk v y A z x=(∑ a:Fin d,rankOneBulk v y
      (A (EuclideanSpace.basisFun (Fin d) ℝ a)) (EuclideanSpace.basisFun (Fin d) ℝ a) 0 x)+
      rankOneBulk v y 0 0 z x := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hinner (r:FSC.Coord d) :
      (∑ a:Fin d,inner ℝ (A (e a)) r*inner ℝ (e a) x)=inner ℝ r (A x) := by
    have hh := congrArg (fun z:FSC.Coord d=>inner ℝ z r) (congrArg A (e.sum_repr' x))
    simpa only [map_sum,map_smul,sum_inner,real_inner_smul_left,real_inner_smul_right,mul_comm,real_inner_comm] using hh
  simp only [rankOneBulk,inner_zero_left,inner_zero_right,zero_mul,mul_zero,add_zero,sub_zero,
    zero_sub,zero_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hQ := basis_quadratic_sum A x
  have hT := basis_trace_sum A
  have hV := hinner v
  have hY := hinner y
  have h1 : (∑ a:Fin d,inner ℝ (A (e a)) x*(inner ℝ v x*inner ℝ y x*inner ℝ (e a) x))=
      (inner ℝ v x*inner ℝ y x)*inner ℝ x (A x) := by
    rw [←hQ,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h2 : (∑ a:Fin d,inner ℝ (A (e a)) v*(inner ℝ y x*inner ℝ (e a) x))=
      inner ℝ v (A x)*inner ℝ y x := by
    rw [←hV,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h3 : (∑ a:Fin d,inner ℝ (A (e a)) y*(inner ℝ v x*inner ℝ (e a) x))=
      inner ℝ v x*inner ℝ y (A x) := by
    rw [←hY,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have h4 : (∑ a:Fin d,inner ℝ (A (e a)) (e a)*(inner ℝ v x*inner ℝ y x))=
      LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap*(inner ℝ v x*inner ℝ y x) := by
    rw [←hT,Finset.sum_mul]
  change affineBulk v y A z x=_
  rw [h1,h2,h3,h4]
  simp only [affineBulk,inner_add_right,real_inner_comm z v,real_inner_comm z y]
  ring

 theorem affineBulk_integrable (μ : Measure (FSC.Coord d)) [IsGaussian μ]
    (v y : FSC.Coord d) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    Integrable (affineBulk v y A z) μ := by
  have hh := (integrable_finsetSum Finset.univ (fun a _=>rankOneBulk_integrable μ v y
    (A (EuclideanSpace.basisFun (Fin d) ℝ a)) (EuclideanSpace.basisFun (Fin d) ℝ a) 0)).add
      (rankOneBulk_integrable μ v y 0 0 z)
  apply hh.congr
  filter_upwards with x
  exact (affineBulk_decomposition v y A z x).symm

/-- The actual quadratic-test affine transport rule, for an arbitrary linear
field A and translation z, including nonsymmetric A and zero-mass caps. -/
 theorem capJointDerivative_bilinear_affine_bulk (w : ι→FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι→ℝ) (hb : FSC.NoCoincident w b)
    (v y : FSC.Coord d) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    capJointDerivative w b (fun x=>inner ℝ v x*inner ℝ y x) (affineVelocity w A z)=
      ∫ x in FSC.cap w b,affineBulk v y A z x ∂stdGaussian (FSC.Coord d) := by
  rw [affineVelocity_decomposition,map_add,map_sum]
  simp_rw [capJointDerivative_bilinear_rankOne_bulk w hw b hb]
  rw [←integral_finsetSum Finset.univ (fun a _=>(rankOneBulk_integrable
    (stdGaussian (FSC.Coord d)) v y (A (EuclideanSpace.basisFun (Fin d) ℝ a))
      (EuclideanSpace.basisFun (Fin d) ℝ a) 0).restrict)]
  rw [←integral_add (integrable_finsetSum Finset.univ (fun a _=>(rankOneBulk_integrable
    (stdGaussian (FSC.Coord d)) v y (A (EuclideanSpace.basisFun (Fin d) ℝ a))
      (EuclideanSpace.basisFun (Fin d) ℝ a) 0).restrict))
    (rankOneBulk_integrable (stdGaussian (FSC.Coord d)) v y 0 0 z).restrict]
  apply integral_congr_ae
  filter_upwards with x
  exact (affineBulk_decomposition v y A z x).symm

/-- Actual differentiation of the Gaussian quadratic integral on the affine
pullback of the original cap. This is a literal integral-valued endpoint. -/
 theorem hasDerivAt_affine_bilinear_gaussian_integral (w : ι→FSC.Coord d)
    (hw : ∀ j,‖w j‖=1) (b : ι→ℝ) (hb : FSC.NoCoincident w b)
    (v y : FSC.Coord d) (A : FSC.Coord d→L[ℝ] FSC.Coord d) (z : FSC.Coord d) :
    HasDerivAt (fun t:ℝ=>∫ x in (fun x=>x+t•A x+t•z) ⁻¹' FSC.cap w b,
      inner ℝ v x*inner ℝ y x ∂stdGaussian (FSC.Coord d))
      (∫ x in FSC.cap w b,affineBulk v y A z x ∂stdGaussian (FSC.Coord d)) 0 := by
  let δ := affineVelocity w A z
  have hF := NegativeVotingQuadraticMovingCap.hasFDerivAt_capTest w hw b hb
    (fun x=>inner ℝ v x*inner ℝ y x) (by fun_prop) (‖v‖*‖y‖) (by positivity) (bilinear_growth v y)
  have hp : HasDerivAt (fun t:ℝ=>(w,b)+t•δ) δ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const δ).const_add (w,b)
  have hF' : HasFDerivAt
      (fun p:Parameters d ι=>capTest p (fun x=>inner ℝ v x*inner ℝ y x))
      (capJointDerivative w b (fun x=>inner ℝ v x*inner ℝ y x)) ((w,b)+(0:ℝ)•δ) := by
    simpa using hF
  have hh := hF'.comp_hasDerivAt (0:ℝ) hp
  have he (t:ℝ) : capTest ((w,b)+t•δ) (fun x=>inner ℝ v x*inner ℝ y x)=
      ∫ x in (fun x=>x+t•A x+t•z) ⁻¹' FSC.cap w b,
        inner ℝ v x*inner ℝ y x ∂stdGaussian (FSC.Coord d) := by
    unfold capTest
    have hp' : ((w,b)+t•δ).2=fun j=>b j-t*inner ℝ (w j) z := by
      funext j
      simp [δ,affineVelocity,sub_eq_add_neg,mul_neg]
    rw [hp']
    change (∫ x in FSC.cap (fun j=>w j+t•A.adjoint (w j)) _,
      inner ℝ v x*inner ℝ y x ∂stdGaussian (FSC.Coord d))=_
    rw [affine_cap_eq_preimage]
  change HasDerivAt (fun t:ℝ=>capTest ((w,b)+t•δ) (fun x=>inner ℝ v x*inner ℝ y x))
    (capJointDerivative w b (fun x=>inner ℝ v x*inner ℝ y x) δ) 0 at hh
  simp_rw [he] at hh
  simpa only [δ,capJointDerivative_bilinear_affine_bulk w hw b hb v y A z] using hh

end NegativeVotingQuadraticAffineTransport
