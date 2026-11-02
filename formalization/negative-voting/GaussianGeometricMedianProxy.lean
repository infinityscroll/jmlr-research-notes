import GaussianNearRegularBalancedGeometry
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Chebyshev

/-! A centered equal-length proxy constructed by an actual geometric median.
All constants are absolute; the construction stays in the original row span. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped BigOperators RealInnerProductSpace Topology Classical
namespace NegativeVotingGeometricMedianProxy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def unitDirection (x : E) : E := ‖x‖⁻¹ • x

def radialError (B : V→E) (β : ℝ) : ℝ := ∑i,(‖B i‖-β)^2

def medianPotential (B : V→E) (c : E) : ℝ := ∑i,‖B i-c‖

theorem unitDirection_norm (x : E) (hx : x≠0) : ‖unitDirection x‖=1 := by
  simp only [unitDirection,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem norm_smul_unitDirection (x : E) : ‖x‖ • unitDirection x=x := by
  by_cases hx : x=0
  · simp [hx,unitDirection]
  · simp [unitDirection,smul_smul,norm_ne_zero_iff.mpr hx]

theorem unitDirection_inner_self (x : E) : inner ℝ (unitDirection x) x=‖x‖ := by
  by_cases hx : x=0
  · simp [hx]
  · rw [unitDirection,real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr hx]

theorem norm_remainder_lower (b c : E) (β : ℝ) (hβ : 0<β) (hb : b≠0)
    (hbup : ‖b‖ ≤ 2*β) (hc : ‖c‖ ≤ β/4) :
    ‖c‖^2-(inner ℝ (unitDirection b) c)^2 ≤
      8*β*(‖b-c‖-‖b‖+inner ℝ (unitDirection b) c) := by
  let t:=inner ℝ (unitDirection b) c
  have ht : |t| ≤ ‖c‖:=by
    simpa only [unitDirection_norm b hb,one_mul] using abs_real_inner_le_norm (unitDirection b) c
  have hi : inner ℝ b c=‖b‖*t:=by
    dsimp [t,unitDirection]
    rw [real_inner_smul_left]
    field_simp [norm_ne_zero_iff.mpr hb]
  have hid : ‖b-c‖^2=(‖b‖-t)^2+(‖c‖^2-t^2):=by
    rw [norm_sub_sq_real,hi]
    ring
  have hdiff : 0 ≤ ‖b-c‖-‖b‖+t:=by
    have hh:=real_inner_le_norm (unitDirection b) (b-c)
    rw [inner_sub_right,unitDirection_inner_self,unitDirection_norm b hb,one_mul] at hh
    linarith
  have hden : ‖b-c‖+‖b‖-t ≤ 8*β:=by
    have hh:=norm_sub_le b c
    linarith [(abs_le.mp ht).1]
  have hh:=mul_nonneg hdiff (sub_nonneg.mpr hden)
  change ‖c‖^2-t^2 ≤ _
  nlinarith only [hh,hid]

theorem potential_strong_lower (B : V→E) (β : ℝ) (hβ : 0<β)
    (hB : ∀i,B i≠0) (hup : ∀i,‖B i‖ ≤ 2*β)
    (hcov : ∀x:E,∑i,(inner ℝ (unitDirection (B i)) x)^2 ≤ (Fintype.card V:ℝ)/2*‖x‖^2)
    (c : E) (hc : ‖c‖ ≤ β/4) :
    (Fintype.card V:ℝ)*‖c‖^2 ≤
      16*β*(medianPotential B c-medianPotential B 0+‖∑i,unitDirection (B i)‖*‖c‖) := by
  have hh:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>norm_remainder_lower (B i) c β hβ (hB i) (hup i) hc)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ←Finset.mul_sum,←sum_inner] at hh
  have hi:=real_inner_le_norm (∑i,unitDirection (B i)) c
  have hcv:=hcov c
  have hzero : medianPotential B 0=∑i,‖B i‖:=by simp [medianPotential]
  rw [hzero]
  change _ ≤ 16*β*((∑i,‖B i-c‖)-(∑i,‖B i‖)+‖∑i,unitDirection (B i)‖*‖c‖)
  nlinarith [mul_le_mul_of_nonneg_left hi (show 0 ≤ 8*β by positivity)]

theorem centered_direction_identity (B : V→E) (β : ℝ) (hcenter : ∑i,B i=0) :
    β • (∑i,unitDirection (B i))=∑i,(β-‖B i‖) • unitDirection (B i) := by
  rw [Finset.smul_sum]
  simp_rw [sub_smul,norm_smul_unitDirection]
  rw [Finset.sum_sub_distrib,hcenter,sub_zero]

theorem centered_direction_bounds (B : V→E) (β : ℝ) (hβ : 0<β)
    (hcenter : ∑i,B i=0) (hclose : ∀i,|‖B i‖-β| ≤ β/256) :
    (∀i,B i≠0) ∧ (∀i,‖B i‖ ≤ 2*β) ∧
    ‖∑i,unitDirection (B i)‖ ≤ (Fintype.card V:ℝ)/256 ∧
    β^2*‖∑i,unitDirection (B i)‖^2 ≤ (Fintype.card V:ℝ)*radialError B β := by
  have hlow i : β/2 ≤ ‖B i‖:=by have hh:=(abs_le.mp (hclose i)).1; linarith
  have hB i : B i≠0:=norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hlow i))
  have hup i : ‖B i‖ ≤ 2*β:=by have hh:=(abs_le.mp (hclose i)).2; linarith
  have hs : β*‖∑i,unitDirection (B i)‖ ≤ ∑i,|‖B i‖-β|:=by
    have hh:=norm_sum_le Finset.univ (fun i=>(β-‖B i‖) • unitDirection (B i))
    rw [←centered_direction_identity B β hcenter,norm_smul,Real.norm_eq_abs,abs_of_pos hβ] at hh
    simpa only [norm_smul,Real.norm_eq_abs,unitDirection_norm _ (hB _),mul_one,abs_sub_comm] using hh
  have hsmall : (∑i,|‖B i‖-β|) ≤ (Fintype.card V:ℝ)*(β/256):=by
    simpa using Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hclose i)
  have hsquare := pow_le_pow_left₀ (mul_nonneg hβ.le (norm_nonneg _)) hs 2
  have hcauchy : (∑i,|‖B i‖-β|)^2 ≤ (Fintype.card V:ℝ)*radialError B β:=by
    simpa only [Finset.card_univ,sq_abs,radialError] using
      (sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun i=>|‖B i‖-β|))
  refine ⟨hB,hup,?_,?_⟩
  · apply (mul_le_mul_iff_right₀ hβ).mp
    nlinarith only [hs,hsmall]
  · simpa only [mul_pow] using hsquare.trans hcauchy


theorem norm_line_hasDerivAt (b c v : E) (hbc : b-c≠0) :
    HasDerivAt (fun t:ℝ=>‖b-(c+t • v)‖) (-inner ℝ (unitDirection (b-c)) v) 0 := by
  have hf : HasDerivAt (fun t:ℝ=>b-(c+t • v)) (-v) 0:=by
    simpa only [Pi.sub_def,Pi.add_def,zero_sub,zero_add,one_smul,id_eq] using (hasDerivAt_const (0:ℝ) b).sub
      ((hasDerivAt_const (0:ℝ) c).add ((hasDerivAt_id (0:ℝ)).smul_const v))
  have hh:=hf.norm_sq.sqrt (by simpa using pow_ne_zero 2 (norm_ne_zero_iff.mpr hbc))
  convert hh using 1
  · funext t
    simp
  · simp only [zero_smul,add_zero,inner_neg_right,Real.sqrt_sq_eq_abs,abs_norm,
      unitDirection,real_inner_smul_left]
    ring

theorem medianPotential_line_hasDerivAt (B : V→E) (c v : E) (hB : ∀i,B i-c≠0) :
    HasDerivAt (fun t:ℝ=>medianPotential B (c+t • v))
      (-inner ℝ (∑i,unitDirection (B i-c)) v) 0 := by
  have hh:=HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>norm_line_hasDerivAt (B i) c v (hB i))
  simpa only [medianPotential,Finset.sum_neg_distrib,sum_inner] using hh

theorem stationary_is_global_min (B : V→E) (c : E) (hB : ∀i,B i-c≠0)
    (hstationary : ∑i,unitDirection (B i-c)=0) (x : E) :
    medianPotential B c ≤ medianPotential B x := by
  have hp i : ‖B i-c‖+inner ℝ (unitDirection (B i-c)) (c-x) ≤ ‖B i-x‖:=by
    have hh:=real_inner_le_norm (unitDirection (B i-c)) (B i-x)
    rw [unitDirection_norm _ (hB i),one_mul] at hh
    have he : B i-x=(B i-c)+(c-x):=by abel
    have hi : inner ℝ (unitDirection (B i-c)) (B i-x)=‖B i-c‖+inner ℝ (unitDirection (B i-c)) (c-x):=by
      rw [he,inner_add_right,unitDirection_inner_self]
    rw [hi] at hh
    exact hh
  have hs:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hp i)
  simpa only [Finset.sum_add_distrib,←sum_inner,hstationary,inner_zero_left,add_zero,medianPotential] using hs

/-- The geometric median is constructed by compact minimization on a fixed
small ball and is then proved to be a global minimizer. -/
theorem exists_small_geometric_median [FiniteDimensional ℝ E]
    (B : V→E) (β : ℝ) (hβ : 0<β) (hcenter : ∑i,B i=0)
    (hclose : ∀i,|‖B i‖-β| ≤ β/256)
    (hcov : ∀x:E,∑i,(inner ℝ (unitDirection (B i)) x)^2 ≤ (Fintype.card V:ℝ)/2*‖x‖^2) :
    ∃ c : E, ‖c‖ < β/4 ∧ (∀i,B i-c≠0) ∧ (∑i,unitDirection (B i-c))=0 ∧
      (∀x,medianPotential B c ≤ medianPotential B x) ∧
      (Fintype.card V:ℝ)*‖c‖^2 ≤ 256*radialError B β := by
  obtain ⟨hB,hup,hg,hgsq⟩:=centered_direction_bounds B β hβ hcenter hclose
  have hm : 0 < (Fintype.card V:ℝ):=by exact_mod_cast Fintype.card_pos
  have hcont : Continuous (medianPotential B):=by unfold medianPotential; fun_prop
  have hzero : (0:E)∈Metric.closedBall 0 (β/4):=by simp; positivity
  obtain ⟨c,hc,hmin⟩:=(isCompact_closedBall (0:E) (β/4)).exists_isMinOn ⟨0,hzero⟩ hcont.continuousOn
  have hcnorm : ‖c‖ ≤ β/4:=by simpa only [Metric.mem_closedBall,dist_zero_right] using hc
  have hvalue : medianPotential B c ≤ medianPotential B 0:=hmin hzero
  have hstrong:=potential_strong_lower B β hβ hB hup hcov c hcnorm
  have hquad : (Fintype.card V:ℝ)*‖c‖^2 ≤ 16*β*‖∑i,unitDirection (B i)‖*‖c‖:=by
    nlinarith [mul_le_mul_of_nonneg_left hvalue (show 0 ≤ 16*β by positivity)]
  have hlin : (Fintype.card V:ℝ)*‖c‖ ≤ 16*β*‖∑i,unitDirection (B i)‖:=by
    by_cases hz : ‖c‖=0
    · rw [hz,mul_zero]; positivity
    · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg c) (Ne.symm hz))).mp
      nlinarith only [hquad]
  have hsmall : ‖c‖ ≤ β/16:=by
    apply (mul_le_mul_iff_left₀ hm).mp
    have hh:=mul_le_mul_of_nonneg_left hg (show 0 ≤ 16*β by positivity)
    nlinarith only [hlin,hh]
  have hcint : ‖c‖ < β/4:=by linarith
  have hBc i : B i-c≠0:=by
    intro hh
    have he:=sub_eq_zero.mp hh
    have hl:=(abs_le.mp (hclose i)).1
    rw [he] at hl
    linarith
  have hlocal : IsLocalMin (medianPotential B) c:=hmin.isLocalMin
    (Metric.closedBall_mem_nhds_of_mem (by simpa only [Metric.mem_ball,dist_zero_right] using hcint))
  let v:=∑i,unitDirection (B i-c)
  have hlocalLine : IsLocalMin (fun t:ℝ=>medianPotential B (c+t • v)) 0:=by
    have hh : IsLocalMin (medianPotential B) ((fun t:ℝ=>c+t • v) 0):=by simpa using hlocal
    exact hh.comp_continuous (g:=fun t:ℝ=>c+t • v) (by fun_prop)
  have hder:=medianPotential_line_hasDerivAt B c v hBc
  have hstat : (∑i,unitDirection (B i-c))=0:=by
    have hz:=hlocalLine.hasDerivAt_eq_zero hder
    have hn : ‖v‖^2=0:=by
      change -inner ℝ v v=0 at hz
      rw [real_inner_self_eq_norm_sq] at hz
      linarith
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hdisp : (Fintype.card V:ℝ)*‖c‖^2 ≤ 256*radialError B β:=by
    have hh:=pow_le_pow_left₀ (mul_nonneg hm.le (norm_nonneg c)) hlin 2
    have h1:=mul_le_mul_of_nonneg_left hgsq (show (0:ℝ) ≤ 256 by norm_num)
    apply (mul_le_mul_iff_left₀ hm).mp
    nlinarith only [hh,h1]
  exact ⟨c,hcint,hBc,hstat,stationary_is_global_min B c hBc hstat,hdisp⟩


/-- Stationarity forces the constructed median into the original row span. -/
theorem stationary_mem_rowSpan (B : V→E) (c : E) (hB : ∀i,B i-c≠0)
    (hstationary : ∑i,unitDirection (B i-c)=0) : c∈Submodule.span ℝ (Set.range B) := by
  let w : V→ℝ:=fun i=>‖B i-c‖⁻¹
  have hw i : 0<w i:=inv_pos.mpr (norm_pos_iff.mpr (hB i))
  have hwpos : 0<∑i,w i:=Finset.sum_pos (fun i _=>hw i) Finset.univ_nonempty
  have he : (∑i,w i) • c=∑i,w i • B i:=by
    have hh:=hstationary
    simp only [unitDirection,smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul] at hh
    exact (sub_eq_zero.mp hh).symm
  have hmem : (∑i,w i) • c∈Submodule.span ℝ (Set.range B):=by
    rw [he]
    exact Submodule.sum_mem _ (fun i _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  have hh:=Submodule.smul_mem (Submodule.span ℝ (Set.range B)) (∑i,w i)⁻¹ hmem
  simpa only [smul_smul,inv_mul_cancel₀ hwpos.ne',one_smul] using hh

def equalRowProxy (B : V→E) (β : ℝ) (c : E) (i : V) : E := β • unitDirection (B i-c)

theorem equalRowProxy_point_error (B : V→E) (β : ℝ) (c : E) (i : V) (hB : B i-c≠0) :
    ‖equalRowProxy B β c i-B i‖ ≤ |‖B i‖-β|+2*‖c‖ := by
  have he : equalRowProxy B β c i-B i=(β-‖B i-c‖) • unitDirection (B i-c)-c:=by
    rw [sub_smul,norm_smul_unitDirection]
    unfold equalRowProxy
    abel
  have hd : |‖B i-c‖-‖B i‖| ≤ ‖c‖:=by
    have hh:=abs_norm_sub_norm_le (B i-c) (B i)
    have heq : B i-c-B i=-c:=by abel
    simpa only [heq,norm_neg] using hh
  have hβ : |β-‖B i-c‖| ≤ |‖B i‖-β|+‖c‖:=by
    have hh:=abs_sub_le β ‖B i‖ ‖B i-c‖
    rw [abs_sub_comm β ‖B i‖,abs_sub_comm ‖B i‖ ‖B i-c‖] at hh
    linarith
  rw [he]
  have hn:=norm_sub_le ((β-‖B i-c‖) • unitDirection (B i-c)) c
  rw [norm_smul,Real.norm_eq_abs,unitDirection_norm _ hB,mul_one] at hn
  linarith

theorem equalRowProxy_error_sq (B : V→E) (β : ℝ) (c : E) (hB : ∀i,B i-c≠0) :
    (∑i,‖equalRowProxy B β c i-B i‖^2) ≤
      2*radialError B β+8*(Fintype.card V:ℝ)*‖c‖^2 := by
  have hp i : ‖equalRowProxy B β c i-B i‖^2 ≤ 2*(‖B i‖-β)^2+8*‖c‖^2:=by
    have hh:=pow_le_pow_left₀ (norm_nonneg _) (equalRowProxy_point_error B β c i (hB i)) 2
    have hs:=sq_nonneg (|‖B i‖-β|-2*‖c‖)
    have he:=sq_abs (‖B i‖-β)
    nlinarith only [hh,hs,he]
  have hh:=Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hp i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  dsimp [radialError]
  convert hh using 1 <;> ring

/-- Centered, exactly equal-length rows with a quantitative absolute-error
bound, constructed from a genuine global geometric median. -/
theorem exists_centered_equalRowProxy [FiniteDimensional ℝ E]
    (B : V→E) (β : ℝ) (hβ : 0<β) (hcenter : ∑i,B i=0)
    (hclose : ∀i,|‖B i‖-β| ≤ β/256)
    (hcov : ∀x:E,∑i,(inner ℝ (unitDirection (B i)) x)^2 ≤ (Fintype.card V:ℝ)/2*‖x‖^2) :
    ∃ c : E, c∈Submodule.span ℝ (Set.range B) ∧ ‖c‖<β/4 ∧
      (∀i,B i-c≠0) ∧ (∀x,medianPotential B c ≤ medianPotential B x) ∧
      (∑i,equalRowProxy B β c i)=0 ∧ (∀i,‖equalRowProxy B β c i‖=β) ∧
      (∀i,equalRowProxy B β c i∈Submodule.span ℝ (Set.range B)) ∧
      (∑i,‖equalRowProxy B β c i-B i‖^2) ≤ 4096*radialError B β := by
  obtain ⟨c,hc,hBc,hstat,hmin,hdisp⟩:=exists_small_geometric_median B β hβ hcenter hclose hcov
  have hspan:=stationary_mem_rowSpan B c hBc hstat
  refine ⟨c,hspan,hc,hBc,hmin,?_,?_,?_,?_⟩
  · simp only [equalRowProxy,←Finset.smul_sum,hstat,smul_zero]
  · intro i
    simp only [equalRowProxy,norm_smul,Real.norm_eq_abs,abs_of_pos hβ,unitDirection_norm _ (hBc i),mul_one]
  · intro i
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.subset_span ⟨i,rfl⟩) hspan))
  · have hh:=equalRowProxy_error_sq B β c hBc
    have hE : 0 ≤ radialError B β:=Finset.sum_nonneg (fun i _=>sq_nonneg _)
    linarith


/-- An ordinary row-operator bound supplies the normalized directional
covariance hypothesis, without a dimension or rank factor. -/
theorem direction_covariance_of_row_covariance (B : V→E) (β : ℝ) (hβ : 0<β)
    (hlower : ∀i,β/2 ≤ ‖B i‖)
    (hcov : ∀x:E,∑i,(inner ℝ (B i) x)^2 ≤ ((Fintype.card V:ℝ)*β^2/8)*‖x‖^2) :
    ∀x:E,∑i,(inner ℝ (unitDirection (B i)) x)^2 ≤ (Fintype.card V:ℝ)/2*‖x‖^2 := by
  intro x
  have hinv i : ‖B i‖⁻¹ ≤ 2/β:=by
    have hh:=one_div_le_one_div_of_le (show 0<β/2 by positivity) (hlower i)
    simpa only [one_div,inv_div,div_one] using hh
  have hp i : (inner ℝ (unitDirection (B i)) x)^2 ≤ (2/β)^2*(inner ℝ (B i) x)^2:=by
    rw [unitDirection,real_inner_smul_left,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (hinv i) 2) (sq_nonneg _)
  calc
    _ ≤ ∑i,(2/β)^2*(inner ℝ (B i) x)^2 := Finset.sum_le_sum (fun i _=>hp i)
    _ = (2/β)^2*(∑i,(inner ℝ (B i) x)^2) := by rw [Finset.mul_sum]
    _ ≤ (2/β)^2*(((Fintype.card V:ℝ)*β^2/8)*‖x‖^2) := mul_le_mul_of_nonneg_left (hcov x) (sq_nonneg _)
    _ = _ := by field_simp; ring

/-- The same construction from a raw row covariance bound, suitable for
specialization to actual centroid rows after scalar normalization. -/
theorem exists_centered_equalRowProxy_of_row_covariance [FiniteDimensional ℝ E]
    (B : V→E) (β : ℝ) (hβ : 0<β) (hcenter : ∑i,B i=0)
    (hclose : ∀i,|‖B i‖-β| ≤ β/256)
    (hcov : ∀x:E,∑i,(inner ℝ (B i) x)^2 ≤ ((Fintype.card V:ℝ)*β^2/8)*‖x‖^2) :
    ∃ c : E, c∈Submodule.span ℝ (Set.range B) ∧ ‖c‖<β/4 ∧
      (∀i,B i-c≠0) ∧ (∀x,medianPotential B c ≤ medianPotential B x) ∧
      (∑i,equalRowProxy B β c i)=0 ∧ (∀i,‖equalRowProxy B β c i‖=β) ∧
      (∀i,equalRowProxy B β c i∈Submodule.span ℝ (Set.range B)) ∧
      (∑i,‖equalRowProxy B β c i-B i‖^2) ≤ 4096*radialError B β := by
  apply exists_centered_equalRowProxy B β hβ hcenter hclose
  apply direction_covariance_of_row_covariance B β hβ _ hcov
  intro i
  have hh:=(abs_le.mp (hclose i)).1
  linarith

end NegativeVotingGeometricMedianProxy
