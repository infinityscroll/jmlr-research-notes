import GaussianCovarianceOptimizerContinuity

/-! Finite-dimensional stability tools for the actual penalized covariance
optimizer. Differentiability of the optimizing point is never assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace NegativeVotingOptimizerStability
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem maximizer_directional_nonpos {f : E→ℝ} {S : Set E} {x y : E} {L : E→L[ℝ]ℝ}
    (hs : Convex ℝ S) (hx : x∈S) (hy : y∈S) (hmax : IsMaxOn f S x)
    (hd : HasFDerivAt f L x) : L (y-x)≤0 :=
  hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hs.segment_subset hx hy))

/-- Two genuine variational inequalities plus a strong gradient decrease
and a parameter-gradient bound force the optimizer distance estimate. -/
theorem optimizer_distance_of_gradients {f : P→E→ℝ} {S : Set E}
    {p q : P} {x y : E} {Lx Ly M : E→L[ℝ]ℝ} {κ K : ℝ}
    (hs : Convex ℝ S) (hx : x∈S) (hy : y∈S)
    (hxp : IsMaxOn (f p) S x) (hyq : IsMaxOn (f q) S y)
    (hdx : HasFDerivAt (f p) Lx x) (hdy : HasFDerivAt (f q) M y)
    (hκ : 0<κ) (hK : 0≤K)
    (hstrong : (Lx-Ly) (x-y)≤-κ*‖x-y‖^2)
    (hvariation : ‖Ly-M‖≤K*‖p-q‖) : ‖x-y‖≤(K/κ)*‖p-q‖ := by
  have h1:=maximizer_directional_nonpos hs hx hy hxp hdx
  have h2:=maximizer_directional_nonpos hs hy hx hyq hdy
  have h1' : 0≤Lx (x-y) := by
    have he : y-x=-(x-y) := by abel
    rw [he,map_neg] at h1
    linarith
  have hquad : κ*‖x-y‖^2≤(Ly-M) (x-y) := by
    simp only [ContinuousLinearMap.sub_apply] at hstrong ⊢
    linarith
  have hup : (Ly-M) (x-y)≤(K*‖p-q‖)*‖x-y‖ :=
    (le_abs_self _).trans ((ContinuousLinearMap.le_opNorm (Ly-M) (x-y)).trans
      (mul_le_mul_of_nonneg_right hvariation (norm_nonneg _)))
  by_cases hzero : x-y=0
  · simp only [hzero,norm_zero]
    positivity
  · have hn : 0<‖x-y‖:=norm_pos_iff.mpr hzero
    have hh : κ*‖x-y‖≤K*‖p-q‖ := by
      apply (mul_le_mul_iff_right₀ hn).mp
      nlinarith [hquad.trans hup]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hκ).mpr
    nlinarith

/-- Strict negativity of a continuous quadratic form in finite dimensions
has an actual uniform norm-square constant. -/
theorem negative_quadratic_uniform [FiniteDimensional ℝ E]
    (L : E→L[ℝ]E→L[ℝ]ℝ) (hneg : ∀ x:E,x≠0→L x x<0) :
    ∃ κ:ℝ,0<κ ∧ ∀ x:E,L x x≤-κ*‖x‖^2 := by
  rcases subsingleton_or_nontrivial E with ht|ht
  · letI:=ht
    refine ⟨1,by norm_num,?_⟩
    intro x
    have hx : x=0:=Subsingleton.elim _ _
    simp [hx]
  · letI:=ht
    have hc : Continuous (fun x:E=>-L x x):=(L.continuous.clm_apply continuous_id).neg
    obtain ⟨v,hv,hmin⟩:=(isCompact_sphere (0:E) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ)≤1)) hc.continuousOn
    have hvn : ‖v‖=1:=by simpa [Metric.mem_sphere,dist_zero_right] using hv
    have hv0 : v≠0:=by intro he; simpa [he] using hvn
    refine ⟨-L v v,by linarith [hneg v hv0],?_⟩
    intro x
    by_cases hx : x=0
    · simp [hx]
    · have hn : ‖x‖≠0:=norm_ne_zero_iff.mpr hx
      let u:E:=‖x‖⁻¹ • x
      have hu : u∈Metric.sphere (0:E) 1:=by
        simp [u,Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg x),hn]
      have hrep : ‖x‖ • u=x:=by simp [u,smul_smul,hn]
      have hval : L u u≤L v v:=neg_le_neg_iff.mp (hmin hu)
      calc
        L x x=L (‖x‖ • u) (‖x‖ • u):=by rw [hrep]
        _=‖x‖^2*(L u u):=by simp [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul];ring
        _≤‖x‖^2*(L v v):=mul_le_mul_of_nonneg_left hval (sq_nonneg _)
        _=-(-L v v)*‖x‖^2:=by ring

theorem bilinear_apply_le_norm (L : E→L[ℝ]E→L[ℝ]ℝ) (v : E) :
    L v v≤‖L‖*‖v‖^2 := by
  calc
    L v v≤‖L v v‖:=by simpa only [Real.norm_eq_abs] using le_abs_self (L v v)
    _≤‖L v‖*‖v‖:=(L v).le_opNorm v
    _≤(‖L‖*‖v‖)*‖v‖:=mul_le_mul_of_nonneg_right (L.le_opNorm v) (norm_nonneg v)
    _=‖L‖*‖v‖^2:=by ring

theorem eventually_uniform_negative {X : Type*} [TopologicalSpace X]
    {A : X→E→L[ℝ]E→L[ℝ]ℝ} {x₀ : X} {κ : ℝ}
    (hA : ContinuousAt A x₀) (hκ : 0<κ)
    (hbase : ∀ v:E,A x₀ v v≤-κ*‖v‖^2) :
    ∀ᶠ x in 𝓝 x₀,∀ v:E,A x v v≤-(κ/2)*‖v‖^2 := by
  have hnear:=hA.eventually (Metric.ball_mem_nhds (A x₀) (half_pos hκ))
  filter_upwards [hnear] with x hx
  intro v
  have he : dist (A x) (A x₀)=‖A x-A x₀‖:=dist_eq_norm (A x) (A x₀)
  have hn : ‖A x-A x₀‖≤κ/2:=le_of_lt (by simpa only [Metric.mem_ball,he] using hx)
  have hb:=bilinear_apply_le_norm (A x-A x₀) v
  simp only [ContinuousLinearMap.sub_apply] at hb
  have hmul:=mul_le_mul_of_nonneg_right hn (sq_nonneg ‖v‖)
  linarith [hbase v]

/-- Uniform negative derivative quadratic forms imply actual strong
monotonic decrease of the gradient on every convex segment. -/
theorem gradient_strong_decrease {G : E→E→L[ℝ]ℝ}
    {A : E→E→L[ℝ]E→L[ℝ]ℝ} {S : Set E} {κ : ℝ}
    (hs : Convex ℝ S) (hD : ∀ z∈S,HasFDerivAt G (A z) z)
    (hA : ∀ z∈S,∀ v:E,A z v v≤-κ*‖v‖^2)
    {x y:E} (hx:x∈S) (hy:y∈S) :
    (G x-G y) (x-y)≤-κ*‖x-y‖^2 := by
  let v:=x-y
  let l:ℝ→E:=fun t=>y+t • v
  let φ:ℝ→ℝ:=fun t=>G (l t) v
  have hl (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : l t∈S := by
    have hh:=hs hy hx (sub_nonneg.mpr ht.2) ht.1 (show (1-t)+t=1 by ring)
    convert hh using 1 <;> dsimp [l,v] <;> module
  have hd (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : HasDerivAt φ (A (l t) v v) t := by
    have hlD : HasDerivAt l v t:=by
      simpa only [l,one_smul,id_eq] using ((hasDerivAt_id t).smul_const v).const_add y
    have hg:HasDerivAt (fun t=>G (l t)) (A (l t) v) t:=
      (hD (l t) (hl t ht)).comp_hasDerivAt t hlD
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt t hg
  have hc : ContinuousOn φ (Icc (0:ℝ) 1):=fun t ht=>(hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (interior (Icc (0:ℝ) 1)):=
    fun t ht=>(hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hb (t:ℝ) (ht:t∈interior (Icc (0:ℝ) 1)) : deriv φ t≤-κ*‖v‖^2 := by
    rw [(hd t (interior_subset ht)).deriv]
    exact hA (l t) (hl t (interior_subset ht)) v
  have hh:=Convex.image_sub_le_mul_sub_of_deriv_le
    (convex_Icc 0 1 : Convex ℝ (Icc (0:ℝ) 1)) hc hdiff hb
    0 (by norm_num) 1 (by norm_num) (by norm_num)
  simpa [φ,l,v,ContinuousLinearMap.sub_apply] using hh

def firstGradient (F : E×P→ℝ) (z : E×P) : E→L[ℝ]ℝ :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ E P)

def secondGradient (F : E×P→ℝ) (z : E×P) : E→L[ℝ]E→L[ℝ]ℝ :=
  (fderiv ℝ (firstGradient F) z).comp (ContinuousLinearMap.inl ℝ E P)

theorem firstGradient_C1 {F : E×P→ℝ} {z : E×P} (hf : ContDiffAt ℝ 2 F z) :
    ContDiffAt ℝ 1 (firstGradient F) z := by
  exact (hf.fderiv_right (m:=1) (by norm_num)).clm_comp contDiffAt_const

theorem secondGradient_continuousAt {F : E×P→ℝ} {z : E×P} (hf : ContDiffAt ℝ 2 F z) :
    ContinuousAt (secondGradient F) z := by
  exact ((firstGradient_C1 hf).continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const

/-- A continuous selection of true constrained maximizers is locally
Lipschitz when the actual objective is C2 and its state Hessian is negative
definite. This applies even when the maximum lies on the constraint boundary. -/
theorem local_optimizer_lipschitz [FiniteDimensional ℝ E]
    (F : E×P→ℝ) (a : P→E) (p₀ : P) (S : Set E)
    (hs : Convex ℝ S) (ha : ContinuousAt a p₀)
    (hf : ContDiffAt ℝ 2 F (a p₀,p₀))
    (hneg : ∀ v:E,v≠0→secondGradient F (a p₀,p₀) v v<0)
    (hm : ∀ᶠ p in 𝓝 p₀,a p∈S ∧ IsMaxOn (fun x:E=>F (x,p)) S (a p)) :
    ∃ K:NNReal,∃ T∈𝓝 p₀,LipschitzOnWith K a T := by
  let G:=firstGradient F
  let A:=secondGradient F
  have hG : ContDiffAt ℝ 1 G (a p₀,p₀):=firstGradient_C1 hf
  obtain ⟨κ,hκ,hκbound⟩:=negative_quadratic_uniform (A (a p₀,p₀)) hneg
  have hcurv : ∀ᶠ z in 𝓝 (a p₀,p₀),∀ v:E,A z v v≤-(κ/2)*‖v‖^2 :=
    eventually_uniform_negative (secondGradient_continuousAt hf) hκ hκbound
  have hDF : ∀ᶠ z in 𝓝 (a p₀,p₀),HasFDerivAt F (fderiv ℝ F z) z :=
    (hf.eventually (by norm_num)).mono (fun z hz=>(hz.of_le (m:=1) (by norm_num)).differentiableAt_one.hasFDerivAt)
  have hDG : ∀ᶠ z in 𝓝 (a p₀,p₀),HasFDerivAt G (fderiv ℝ G z) z :=
    (hG.eventually (by norm_num)).mono (fun z hz=>hz.differentiableAt_one.hasFDerivAt)
  obtain ⟨K,U,hU,hLip⟩:=hG.exists_lipschitzOnWith
  let W : Set (E×P):={z | z∈U ∧ (∀ v:E,A z v v≤-(κ/2)*‖v‖^2) ∧
    HasFDerivAt F (fderiv ℝ F z) z ∧ HasFDerivAt G (fderiv ℝ G z) z}
  have hW : W∈𝓝 (a p₀,p₀):=by
    filter_upwards [hU,hcurv,hDF,hDG] with z hu hc hd hg
    exact ⟨hu,hc,hd,hg⟩
  obtain ⟨δ,hδ,hδsub⟩:=Metric.mem_nhds_iff.mp hW
  let T : Set P:={p | a p∈Metric.ball (a p₀) (δ/2) ∧ p∈Metric.ball p₀ (δ/2) ∧
    a p∈S ∧ IsMaxOn (fun x:E=>F (x,p)) S (a p)}
  have hT : T∈𝓝 p₀:=by
    have hbp : ∀ᶠ p in 𝓝 p₀,p∈Metric.ball p₀ (δ/2):=Metric.ball_mem_nhds _ (half_pos hδ)
    exact (ha.eventually (Metric.ball_mem_nhds _ (half_pos hδ))).and (hbp.and hm)
  have hpoint {x:E} {p:P} (hx:x∈Metric.ball (a p₀) (δ/2)) (hp:p∈Metric.ball p₀ (δ/2)) :
      (x,p)∈W := by
    apply hδsub
    change max (dist x (a p₀)) (dist p p₀)<δ
    exact max_lt_iff.mpr ⟨lt_trans hx (half_lt_self hδ),lt_trans hp (half_lt_self hδ)⟩
  let R:Set E:=S∩Metric.ball (a p₀) (δ/2)
  have hR:Convex ℝ R:=hs.inter (convex_ball _ _)
  let K':NNReal:=⟨(K:ℝ)/(κ/2),by positivity⟩
  refine ⟨K',T,hT,lipschitzOnWith_iff_norm_sub_le.mpr ?_⟩
  intro p hp q hq
  have hxp : a p∈R:=⟨hp.2.2.1,hp.1⟩
  have hxq : a q∈R:=⟨hq.2.2.1,hq.1⟩
  have hmaxp : IsMaxOn (fun x:E=>F (x,p)) R (a p):=fun x hx=>hp.2.2.2 hx.1
  have hmaxq : IsMaxOn (fun x:E=>F (x,q)) R (a q):=fun x hx=>hq.2.2.2 hx.1
  have hline (x:E) (p:P) : HasFDerivAt (fun y:E=>(y,p)) (ContinuousLinearMap.inl ℝ E P) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const p x)
  have hderF {x:E} {p:P} (hw:(x,p)∈W) :
      HasFDerivAt (fun y:E=>F (y,p)) (G (x,p)) x :=
    hw.2.2.1.comp x (hline x p)
  have hstrong : (G (a p,p)-G (a q,p)) (a p-a q)≤-(κ/2)*‖a p-a q‖^2 := by
    apply gradient_strong_decrease hR (G:=fun x:E=>G (x,p)) (κ:=κ/2) (A:=fun x:E=>A (x,p)) ?_ ?_ hxp hxq
    · intro x hx
      exact (hpoint hx.2 hp.2.1).2.2.2.comp x (hline x p)
    · intro x hx v
      exact (hpoint hx.2 hp.2.1).2.1 v
  have hvar : ‖G (a q,p)-G (a q,q)‖≤(K:ℝ)*‖p-q‖ := by
    have hh:=(lipschitzOnWith_iff_norm_sub_le.mp hLip)
      (hpoint hq.1 hp.2.1).1 (hpoint hq.1 hq.2.1).1
    simpa [Prod.norm_def] using hh
  exact optimizer_distance_of_gradients (f:=fun r:P=>fun x:E=>F (x,r))
    (p:=p) (q:=q) hR hxp hxq hmaxp hmaxq
    (hderF (hpoint hp.1 hp.2.1)) (hderF (hpoint hq.1 hq.2.1))
    (half_pos hκ) K.coe_nonneg hstrong hvar

/-- The full state-Hessian quadratic form is the literal second derivative
of the actual scalar restriction to a straight line. -/
theorem secondGradient_line_second {F : E×P→ℝ} {x:E} {p:P}
    (hf : ContDiffAt ℝ 2 F (x,p)) (v:E) :
    HasDerivAt (deriv (fun t:ℝ=>F (x+t • v,p))) (secondGradient F (x,p) v v) 0 := by
  let l:ℝ→E×P:=fun t=>(x+t • v,p)
  have hlD (t:ℝ) : HasDerivAt l (v,0) t:=by
    simpa only [l,one_smul,id_eq] using
      (((hasDerivAt_id t).smul_const v).const_add x).prodMk (hasDerivAt_const t p)
  have hl0:l 0=(x,p):=by simp [l]
  have hF : ∀ᶠ z in 𝓝 (x,p),HasFDerivAt F (fderiv ℝ F z) z:=
    (hf.eventually (by norm_num)).mono (fun z hz=>(hz.of_le (m:=1) (by norm_num)).differentiableAt_one.hasFDerivAt)
  have heq : (deriv (fun t:ℝ=>F (l t)))=ᶠ[𝓝 (0:ℝ)]
      (fun t=>firstGradient F (l t) v) := by
    have hlC : Tendsto l (𝓝 (0:ℝ)) (𝓝 (x,p)):=by simpa only [hl0] using (hlD 0).continuousAt.tendsto
    have he : ∀ᶠ t in 𝓝 (0:ℝ),HasFDerivAt F (fderiv ℝ F (l t)) (l t):=
      hlC.eventually hF
    filter_upwards [he] with t ht
    exact (ht.comp_hasDerivAt t (hlD t)).deriv
  have hG:=((firstGradient_C1 hf).differentiableAt_one.hasFDerivAt)
  have hG' : HasFDerivAt (firstGradient F) (fderiv ℝ (firstGradient F) (x,p)) (l 0):=by simpa [hl0] using hG
  have hg:=hG'.comp_hasDerivAt 0 (hlD 0)
  have hh:=(ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt 0 hg
  exact hh.congr_of_eventuallyEq heq

theorem line_second_affine_penalty {f:ℝ→ℝ} {q a b c:ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ),DifferentiableAt ℝ f t)
    (hd : HasDerivAt (deriv f) q 0) :
    HasDerivAt (deriv (fun t:ℝ=>a*f t-(b+t*c))) (a*q) 0 := by
  have heq : deriv (fun t:ℝ=>a*f t-(b+t*c))=ᶠ[𝓝 (0:ℝ)]
      (fun t=>a*deriv f t-c) := by
    filter_upwards [hf] with t ht
    have hl : HasDerivAt (fun u:ℝ=>b+u*c) c t:=by
      simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const c).const_add b
    exact ((ht.hasDerivAt.const_mul a).sub hl).deriv
  exact ((hd.const_mul a).sub_const c).congr_of_eventuallyEq heq

end NegativeVotingOptimizerStability
