import GaussianOptimizerStability
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! A mixed-Hessian estimate gives joint semiconcavity, and partial
maximization over a fixed convex set preserves the corrected concavity. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace NegativeVotingValueSemiconcavity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def fullHessian (F:E→ℝ) (x:E) : E→L[ℝ]E→L[ℝ]ℝ:=fderiv ℝ (fderiv ℝ F) x

theorem scalar_schur_bound {a b K t:ℝ} (hK:0<K) (hb:b^2≤K*(-a)) :
    a+2*t*b≤K*t^2 := by
  have hm : K*(a+2*t*b-K*t^2)≤0:=by nlinarith [sq_nonneg (b-K*t)]
  have hh : a+2*t*b-K*t^2≤0:=by
    apply (mul_le_mul_iff_right₀ hK).mp
    nlinarith [hm]
  linarith

theorem block_quadratic (H:(E×ℝ)→L[ℝ](E×ℝ)→L[ℝ]ℝ)
    (hsym:∀u v,H u v=H v u) (D:E) (t:ℝ) :
    H (D,t) (D,t)=H (D,0) (D,0)+2*t*H (D,0) (0,1)+t^2*H (0,1) (0,1) := by
  have he:(D,t)=(D,0)+t • (0,1):=by ext <;>simp
  conv_lhs=>rw [he]
  simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [hsym (0,1) (D,0)]
  ring

/-- The mixed bound is applied to the actual full Hessian, whose symmetry
is a consequence of C2 regularity. -/
theorem fullHessian_bound {F:E×ℝ→ℝ} {z:E×ℝ} {K:ℝ}
    (hf:ContDiffAt ℝ 2 F z) (hK:0<K)
    (htime:fullHessian F z (0,1) (0,1)≤0)
    (hmix:∀D:E,(fullHessian F z (D,0) (0,1))^2≤K*(-fullHessian F z (D,0) (D,0)))
    (v:E×ℝ) : fullHessian F z v v≤K*v.2^2 := by
  have hsym:∀u w,fullHessian F z u w=fullHessian F z w u:=
    fun u w=>(hf.isSymmSndFDerivAt (by norm_num)).eq u w
  have he:=block_quadratic (fullHessian F z) hsym v.1 v.2
  have hb:=scalar_schur_bound (t:=v.2) hK (hmix v.1)
  have ht:=mul_nonpos_of_nonneg_of_nonpos (sq_nonneg v.2) htime
  simpa only [Prod.mk.eta] using (show fullHessian F z (v.1,v.2) (v.1,v.2)≤K*v.2^2 by linarith)

theorem line_second (F:E→ℝ) (a v:E) (t:ℝ)
    (hf:ContDiffAt ℝ 2 F (a+t • v)) :
    HasDerivAt (deriv (fun u:ℝ=>F (a+u • v))) (fullHessian F (a+t • v) v v) t := by
  let l:ℝ→E:=fun u=>a+u • v
  have hlD (u:ℝ):HasDerivAt l v u:=by
    simpa only [l,id_eq,one_smul] using ((hasDerivAt_id u).smul_const v).const_add a
  have hF : ∀ᶠ x in 𝓝 (l t),HasFDerivAt F (fderiv ℝ F x) x:=
    (hf.eventually (by norm_num)).mono (fun x hx=>(hx.of_le (m:=1) (by norm_num)).differentiableAt_one.hasFDerivAt)
  have heq : deriv (fun u:ℝ=>F (l u))=ᶠ[𝓝 t] (fun u=>(fderiv ℝ F (l u)) v):=by
    filter_upwards [(hlD t).continuousAt.tendsto.eventually hF] with u hu
    exact (hu.comp_hasDerivAt u (hlD u)).deriv
  have hG:HasFDerivAt (fderiv ℝ F) (fullHessian F (l t)) (l t):=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hh:=(ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt t
    (hG.comp_hasDerivAt t (hlD t))
  exact hh.congr_of_eventuallyEq heq

theorem line_second_quadratic_penalty {f:ℝ→ℝ} {q K a c t:ℝ}
    (hf:∀ᶠ u in 𝓝 t,DifferentiableAt ℝ f u)
    (hd:HasDerivAt (deriv f) q t) :
    HasDerivAt (deriv (fun u:ℝ=>f u-K/2*(a+u*c)^2)) (q-K*c^2) t := by
  have hpoly (u:ℝ):HasDerivAt (fun s:ℝ=>K/2*(a+s*c)^2) (K*(a+u*c)*c) u:=by
    have hl:HasDerivAt (fun s:ℝ=>a+s*c) c u:=by
      simpa only [id_eq,one_mul] using ((hasDerivAt_id u).mul_const c).const_add a
    convert (hl.pow 2).const_mul (K/2) using 1 <;>simp <;>ring
  have heq:deriv (fun u:ℝ=>f u-K/2*(a+u*c)^2)=ᶠ[𝓝 t]
      (fun u=>deriv f u-K*(a+u*c)*c):=by
    filter_upwards [hf] with u hu
    exact (hu.hasDerivAt.sub (hpoly u)).deriv
  have hl:HasDerivAt (fun u:ℝ=>K*(a+u*c)*c) (K*c^2) t:=by
    have hh:HasDerivAt (fun u:ℝ=>a+u*c) c t:=by
      simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const c).const_add a
    convert (hh.const_mul K).mul_const c using 1 <;>ring
  exact (hd.sub hl).congr_of_eventuallyEq heq

/-- A segment-by-segment second-derivative criterion, with first
regularity retained explicitly. -/
theorem concaveOn_of_segment_jets (F:E→ℝ) (S:Set E) (hs:Convex ℝ S)
    (hc:ContinuousOn F S)
    (hd:∀x∈S,∀y∈S,∀t∈interior (Icc (0:ℝ) 1),
      DifferentiableAt ℝ (fun u:ℝ=>F (x+u • (y-x))) t)
    (h2:∀x∈S,∀y∈S,∀t∈interior (Icc (0:ℝ) 1),
      ∃q:ℝ,HasDerivAt (deriv (fun u:ℝ=>F (x+u • (y-x)))) q t ∧ q≤0) :
    ConcaveOn ℝ S F := by
  have hseg (x:E) (hx:x∈S) (y:E) (hy:y∈S) (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : x+t • (y-x)∈S:=by
    have hh:=hs hx hy (sub_nonneg.mpr ht.2) ht.1 (show (1-t)+t=1 by ring)
    convert hh using 1 <;>module
  have hline (x:E) (hx:x∈S) (y:E) (hy:y∈S) :
      ConcaveOn ℝ (Icc (0:ℝ) 1) (fun t:ℝ=>F (x+t • (y-x))) := by
    apply concaveOn_of_deriv2_nonpos (convex_Icc 0 1)
      (hc.comp (by fun_prop) (hseg x hx y hy))
    · exact fun t ht=>(hd x hx y hy t ht).differentiableWithinAt
    · intro t ht
      obtain ⟨q,hq,_⟩:=h2 x hx y hy t ht
      exact hq.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨q,hq,hq0⟩:=h2 x hx y hy t ht
      simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply,Function.comp_def,hq.deriv] using hq0
  refine ⟨hs,?_⟩
  intro x hx y hy a c ha hc hac
  have hh:=(hline x hx y hy).2 (show (0:ℝ)∈Icc 0 1 by constructor <;>norm_num)
    (show (1:ℝ)∈Icc 0 1 by constructor <;>norm_num) ha hc hac
  have he:x+c • (y-x)=a • x+c • y:=by
    have he':a=1-c:=by linarith
    rw [he'];module
  simpa [he] using hh

/-- The quadratic correction makes the actual objective jointly concave
in state and time on any convex region where the mixed estimate holds. -/
theorem joint_penalty_concaveOn (F:E×ℝ→ℝ) (S:Set (E×ℝ)) (hs:Convex ℝ S)
    (K:ℝ) (hK:0<K) (hC:∀z∈S,ContDiffAt ℝ 2 F z)
    (htime:∀z∈S,fullHessian F z (0,1) (0,1)≤0)
    (hmix:∀z∈S,∀D:E,(fullHessian F z (D,0) (0,1))^2≤K*(-fullHessian F z (D,0) (D,0))) :
    ConcaveOn ℝ S (fun z=>F z-K/2*z.2^2) := by
  let G:E×ℝ→ℝ:=fun z=>F z-K/2*z.2^2
  have hGC (z:E×ℝ) (hz:z∈S):ContDiffAt ℝ 2 G z:=
    (hC z hz).sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))
  have hseg (x:E×ℝ) (hx:x∈S) (y:E×ℝ) (hy:y∈S) (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : x+t • (y-x)∈S:=by
    have hh:=hs hx hy (sub_nonneg.mpr ht.2) ht.1 (show (1-t)+t=1 by ring)
    convert hh using 1 <;>module
  apply concaveOn_of_segment_jets G S hs (fun z hz=>(hGC z hz).continuousAt.continuousWithinAt)
  · intro x hx y hy t ht
    have hL:ContDiffAt ℝ 2 (fun u:ℝ=>x+u • (y-x)) t:=by fun_prop
    exact ((hGC _ (hseg x hx y hy t (interior_subset ht))).comp
      (f:=fun u:ℝ=>x+u • (y-x)) t hL).differentiableAt (by norm_num)
  · intro x hx y hy t ht
    let v:=y-x
    let z:=x+t • v
    have hz:z∈S:=hseg x hx y hy t (interior_subset ht)
    have hL:ContDiffAt ℝ 2 (fun u:ℝ=>x+u • v) t:=by fun_prop
    have hFC:ContDiffAt ℝ 2 (fun u:ℝ=>F (x+u • v)) t:=
      (hC z hz).comp (f:=fun u:ℝ=>x+u • v) t hL
    have hf:∀ᶠ u in 𝓝 t,DifferentiableAt ℝ (fun s:ℝ=>F (x+s • v)) u:=
      (hFC.eventually (by norm_num)).mono (fun u hu=>(hu.of_le (m:=1) (by norm_num)).differentiableAt_one)
    have hj:=line_second_quadratic_penalty (K:=K) (a:=x.2) (c:=v.2) hf
      (line_second F x v t (hC z hz))
    refine ⟨fullHessian F z v v-K*v.2^2,?_,?_⟩
    · exact hj
    · have hb:=fullHessian_bound (hC z hz) hK (htime z hz) (hmix z hz) v
      linarith

/-- Partial maximization of a jointly concave function over a fixed convex
state set is concave. The maxima here are actual attained maxima. -/
theorem partial_maximum_concaveOn (F:E×ℝ→ℝ) (S:Set E) (I:Set ℝ)
    (a:ℝ→E) (hs:Convex ℝ S) (hi:Convex ℝ I)
    (hF:ConcaveOn ℝ (S×ˢI) F) (ha:∀t∈I,a t∈S)
    (hmax:∀t∈I,IsMaxOn (fun x:E=>F (x,t)) S (a t)) :
    ConcaveOn ℝ I (fun t=>F (a t,t)) := by
  refine ⟨hi,?_⟩
  intro s hs' t ht α β hα hβ hab
  have hh:=hF.2 (show (a s,s)∈S×ˢI from ⟨ha s hs',hs'⟩)
    (show (a t,t)∈S×ˢI from ⟨ha t ht,ht⟩) hα hβ hab
  exact hh.trans (hmax _ (hi hs' ht hα hβ hab) (hs (ha s hs') (ha t ht) hα hβ hab))

theorem penalty_maximum_concaveOn (F:E×ℝ→ℝ) (S:Set E) (I:Set ℝ)
    (a:ℝ→E) (hs:Convex ℝ S) (hi:Convex ℝ I) (K:ℝ) (hK:0<K)
    (hC:∀z∈S×ˢI,ContDiffAt ℝ 2 F z)
    (htime:∀z∈S×ˢI,fullHessian F z (0,1) (0,1)≤0)
    (hmix:∀z∈S×ˢI,∀D:E,(fullHessian F z (D,0) (0,1))^2≤K*(-fullHessian F z (D,0) (D,0)))
    (ha:∀t∈I,a t∈S) (hmax:∀t∈I,IsMaxOn (fun x:E=>F (x,t)) S (a t)) :
    ConcaveOn ℝ I (fun t=>F (a t,t)-K/2*t^2) := by
  apply partial_maximum_concaveOn (fun z=>F z-K/2*z.2^2) S I a hs hi
    (joint_penalty_concaveOn F _ (hs.prod hi) K hK hC htime hmix) ha
  intro t ht x hx
  have hh:F (x,t)≤F (a t,t):=hmax t ht hx
  exact sub_le_sub_right hh _

/-- Open geometric slack near a continuous family of actual constrained
maxima suffices for local semiconcavity of the optimized value. -/
theorem local_penalty_value_concave (F:E×ℝ→ℝ) (S:Set E) (hs:Convex ℝ S)
    (a:ℝ→E) (t₀ K:ℝ) (hK:0<K) (ha:ContinuousAt a t₀)
    (hmax:∀ᶠ t in 𝓝 t₀,a t∈S ∧ IsMaxOn (fun x:E=>F (x,t)) S (a t))
    (hN:∀ᶠ z:E×ℝ in 𝓝 (a t₀,t₀),ContDiffAt ℝ 2 F z ∧
      fullHessian F z (0,1) (0,1)≤0 ∧
      ∀D:E,(fullHessian F z (D,0) (0,1))^2≤K*(-fullHessian F z (D,0) (D,0))) :
    ∃η:ℝ,0<η ∧ ConcaveOn ℝ (Metric.ball t₀ η) (fun t=>F (a t,t)-K/2*t^2) := by
  let N:Set (E×ℝ):={z | ContDiffAt ℝ 2 F z ∧ fullHessian F z (0,1) (0,1)≤0 ∧
    ∀D:E,(fullHessian F z (D,0) (0,1))^2≤K*(-fullHessian F z (D,0) (D,0))}
  have hN':N∈𝓝 (a t₀,t₀):=hN
  obtain ⟨δ,hδ,hδsub⟩:=Metric.mem_nhds_iff.mp hN'
  let J:Set ℝ:={t | a t∈Metric.ball (a t₀) (δ/2) ∧ t∈Metric.ball t₀ (δ/2) ∧
    a t∈S ∧ IsMaxOn (fun x:E=>F (x,t)) S (a t)}
  have hJ:J∈𝓝 t₀:=by
    have ht:∀ᶠ t in 𝓝 t₀,t∈Metric.ball t₀ (δ/2):=Metric.ball_mem_nhds _ (half_pos hδ)
    exact (ha.eventually (Metric.ball_mem_nhds _ (half_pos hδ))).and (ht.and hmax)
  obtain ⟨η,hη,hηsub⟩:=Metric.mem_nhds_iff.mp hJ
  let R:Set E:=S∩Metric.ball (a t₀) (δ/2)
  let I:Set ℝ:=Metric.ball t₀ η
  have hpoint {z:E×ℝ} (hz:z∈R×ˢI):z∈N:=by
    apply hδsub
    change max (dist z.1 (a t₀)) (dist z.2 t₀)<δ
    exact max_lt_iff.mpr ⟨lt_trans hz.1.2 (half_lt_self hδ),
      lt_trans (hηsub hz.2).2.1 (half_lt_self hδ)⟩
  refine ⟨η,hη,penalty_maximum_concaveOn F R I a
    (hs.inter (convex_ball _ _)) (convex_ball _ _) K hK
    (fun z hz=>(hpoint hz).1) (fun z hz=>(hpoint hz).2.1)
    (fun z hz=>(hpoint hz).2.2) ?_ ?_⟩
  · intro t ht
    exact ⟨(hηsub ht).2.2.1,(hηsub ht).1⟩
  · intro t ht x hx
    exact (hηsub ht).2.2.2 hx.1

end NegativeVotingValueSemiconcavity
