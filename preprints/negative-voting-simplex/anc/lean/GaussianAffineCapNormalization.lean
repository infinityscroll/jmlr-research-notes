import GaussianAffineLogMassBound

/-! Exact cap normalization under injective affine score transport. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Classical
namespace NegativeVotingAffineCapNormalization
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def transportedNormals (w : ι → FSC.Coord d) (T : FSC.Coord d →L[ℝ] FSC.Coord d)
    (j : ι) : FSC.Coord d := ‖T (w j)‖⁻¹ • T (w j)

def transportedSupports (w : ι → FSC.Coord d) (b : ι → ℝ)
    (T : FSC.Coord d →L[ℝ] FSC.Coord d) (v : FSC.Coord d) (j : ι) : ℝ :=
  (b j-inner ℝ (w j) v)/‖T (w j)‖

theorem transported_norm_pos (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (T : FSC.Coord d →L[ℝ] FSC.Coord d) (hT : Function.Injective T) (j : ι) :
    0 < ‖T (w j)‖ := by
  apply norm_pos_iff.mpr
  intro he
  have hz : w j=0 := hT (by simpa only [map_zero] using he)
  have hh := hw j
  rw [hz,norm_zero] at hh
  norm_num at hh

theorem transportedNormals_unit (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (T : FSC.Coord d →L[ℝ] FSC.Coord d) (hT : Function.Injective T) (j : ι) :
    ‖transportedNormals w T j‖=1 := by
  simp only [transportedNormals,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
  exact inv_mul_cancel₀ (ne_of_gt (transported_norm_pos w hw T hT j))

theorem transportedNormals_eq_iff (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (T : FSC.Coord d →L[ℝ] FSC.Coord d) (hT : Function.Injective T) (j k : ι) :
    transportedNormals w T j=transportedNormals w T k ↔ w j=w k := by
  constructor
  · intro he
    have hh : T (‖T (w j)‖⁻¹ • w j)=T (‖T (w k)‖⁻¹ • w k) := by
      simpa only [transportedNormals,map_smul] using he
    have hv := hT hh
    have hn := congrArg norm hv
    simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,hw,mul_one] at hn
    have hn' : ‖T (w j)‖=‖T (w k)‖ := inv_injective hn
    rw [hn'] at hv
    have hm := congrArg (fun x : FSC.Coord d=>‖T (w k)‖ • x) hv
    simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt (transported_norm_pos w hw T hT k)),one_smul] using hm
  · intro he
    simp only [transportedNormals,he]

theorem transportedNormals_eq_neg_iff (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (T : FSC.Coord d →L[ℝ] FSC.Coord d) (hT : Function.Injective T) (j k : ι) :
    transportedNormals w T j= -transportedNormals w T k ↔ w j= -w k := by
  constructor
  · intro he
    have hh : T (‖T (w j)‖⁻¹ • w j)=T (-(‖T (w k)‖⁻¹ • w k)) := by
      simpa only [transportedNormals,map_smul,map_neg] using he
    have hv := hT hh
    have hn := congrArg norm hv
    simp only [norm_smul,norm_neg,Real.norm_eq_abs,abs_inv,abs_norm,hw,mul_one] at hn
    have hn' : ‖T (w j)‖=‖T (w k)‖ := inv_injective hn
    rw [hn'] at hv
    have hm := congrArg (fun x : FSC.Coord d=>‖T (w k)‖ • x) hv
    simpa only [smul_neg,smul_smul,mul_inv_cancel₀ (ne_of_gt (transported_norm_pos w hw T hT k)),one_smul] using hm
  · intro he
    simp [transportedNormals,he]

theorem transported_noCoincident (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (hb : FSC.NoCoincident w b)
    (T : FSC.Coord d →L[ℝ] FSC.Coord d) (hT : Function.Injective T) (v : FSC.Coord d) :
    FSC.NoCoincident (transportedNormals w T) (transportedSupports w b T v) := by
  intro j k hjk
  constructor
  · intro he hsup
    have hj := (transportedNormals_eq_iff w hw T hT j k).mp he
    apply (hb j k hjk).1 hj
    dsimp [transportedSupports] at hsup
    rw [hj] at hsup
    have hh := (div_left_inj' (ne_of_gt (transported_norm_pos w hw T hT k))).mp hsup
    linarith
  · intro he hsup
    have hj := (transportedNormals_eq_neg_iff w hw T hT j k).mp he
    apply (hb j k hjk).2 hj
    dsimp [transportedSupports] at hsup
    rw [hj,map_neg,norm_neg,inner_neg_left] at hsup
    have hh : b j+inner ℝ (w k) v= -(b k-inner ℝ (w k) v) := by
      apply (div_left_inj' (ne_of_gt (transported_norm_pos w hw T hT k))).mp
      simpa only [sub_neg_eq_add,neg_div] using hsup
    linarith

theorem transported_cap (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (T : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hT : Function.Injective T) (v : FSC.Coord d) :
    FSC.cap (transportedNormals w T) (transportedSupports w b T v)=
      FSC.cap (fun j=>T (w j)) (fun j=>b j-inner ℝ (w j) v) := by
  ext x
  simp only [FSC.cap,Set.mem_setOf_eq,transportedNormals,transportedSupports,real_inner_smul_left]
  apply forall_congr'
  intro j
  rw [show ‖T (w j)‖⁻¹*inner ℝ (T (w j)) x=inner ℝ (T (w j)) x/‖T (w j)‖ by ring]
  exact div_le_div_iff_of_pos_right (transported_norm_pos w hw T hT j)

/-- Exact preservation of the actual affine pullback cap under unit-normal
renormalization, including the transported support offsets. -/
theorem transported_adjoint_cap_eq_preimage (w : ι → FSC.Coord d) (hw : ∀ j,‖w j‖=1)
    (b : ι → ℝ) (M : FSC.Coord d →L[ℝ] FSC.Coord d)
    (hM : Function.Injective M.adjoint) (v : FSC.Coord d) :
    FSC.cap (transportedNormals w M.adjoint) (transportedSupports w b M.adjoint v)=
      (fun x=>M x+v) ⁻¹' FSC.cap w b := by
  rw [transported_cap w hw b _ hM v]
  ext x
  simp only [FSC.cap,Set.mem_setOf_eq,Set.mem_preimage,inner_add_right,ContinuousLinearMap.adjoint_inner_left]
  apply forall_congr'
  intro j
  exact le_sub_iff_add_le

end NegativeVotingAffineCapNormalization
