import GaussianDiagonalUniformOffsetBound
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.MeanValue

/-! First-exit continuation of actual selected balancing offsets along the
square-root variance path. The final short-interval box is a conclusion. -/
noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical Topology RealInnerProductSpace
namespace NegativeVotingDiagonalOffsetContinuation
open NegativeVotingDiagonalUniformOffsetBound NegativeVotingDiagonalOffsetComponentBound
  NegativeVotingDiagonalWinnerIntegral NegativeVotingDiagonalBalancedDerivative
  NegativeVotingFanSelectedOffsets NegativeVotingFanInverse NegativeVotingRegularDiagonalBalance
  NegativeVotingBalancedReference NegativeVotingHazardUniformMoments NegativeVotingHazardMomentEnvelope
  NegativeVotingHazardQuantileAsymptotics NegativeVotingGaussianMaximum
  NegativeVotingDiagonalHazardDifferentiation

/-- A closed-box derivative estimate propagates without assuming the box on
the whole path. The contradiction occurs at the first closed-box exit. -/
theorem norm_first_exit_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (T R D : ℝ) (hT : 0 ≤ T) (hR : 0 < R) (hD : 0 ≤ D)
    (hf : ContinuousOn f (Icc 0 T)) (hzero : f 0=0) (hsmall : D*T < R)
    (hderiv : ∀ t∈Icc 0 T,‖f t‖ ≤ R → ∃ v,HasDerivAt f v t ∧ ‖v‖ ≤ D) :
    (∀ t∈Icc 0 T,‖f t‖ < R) ∧ (∀ t∈Icc 0 T,‖f t‖ ≤ D*t) := by
  have hbox : ∀ t∈Icc 0 T,‖f t‖ < R := by
    by_contra hfail
    push_neg at hfail
    obtain ⟨t,ht,hbad⟩ := hfail
    let S : Set ℝ := Icc 0 T ∩ (fun s => ‖f s‖) ⁻¹' Ici R
    have hclosed : IsClosed S := hf.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
    obtain ⟨s,hs⟩ := hcompact.exists_isLeast ⟨t,ht,hbad⟩
    have hsrange : s∈Icc 0 T := hs.1.1
    have hsbad : R ≤ ‖f s‖ := hs.1.2
    have hspos : 0 < s := by
      have hn : s≠0 := by intro he;rw [he,hzero,norm_zero] at hsbad;linarith
      exact lt_of_le_of_ne hsrange.1 (Ne.symm hn)
    have hbefore (u : ℝ) (hu : u∈Ico 0 s) : ‖f u‖ ≤ R := by
      by_contra hn
      have hn' : R ≤ ‖f u‖ := (lt_of_not_ge hn).le
      have hus : u∈S := ⟨⟨hu.1,hu.2.le.trans hsrange.2⟩,hn'⟩
      have hsu := hs.2 hus
      linarith [hu.2]
    have hlocal (u : ℝ) (hu : u∈Ico 0 s) :
        HasDerivAt f (deriv f u) u ∧ ‖deriv f u‖ ≤ D := by
      obtain ⟨v,hv,hvb⟩ := hderiv u ⟨hu.1,hu.2.le.trans hsrange.2⟩ (hbefore u hu)
      rw [hv.deriv]
      exact ⟨hv,hvb⟩
    have hsub : Icc (0:ℝ) s ⊆ Icc 0 T := fun u hu => ⟨hu.1,hu.2.trans hsrange.2⟩
    have hmean := norm_image_sub_le_of_norm_deriv_right_le_segment (hf.mono hsub)
      (fun u hu => (hlocal u hu).1.hasDerivWithinAt) (fun u hu => (hlocal u hu).2)
      s ⟨hspos.le,le_rfl⟩
    rw [hzero,sub_zero,sub_zero] at hmean
    have hmul := mul_le_mul_of_nonneg_left hsrange.2 hD
    linarith
  refine ⟨hbox,?_⟩
  have hlocal (u : ℝ) (hu : u∈Ico 0 T) :
      HasDerivAt f (deriv f u) u ∧ ‖deriv f u‖ ≤ D := by
    obtain ⟨v,hv,hvb⟩ := hderiv u ⟨hu.1,hu.2.le⟩ (hbox u ⟨hu.1,hu.2.le⟩).le
    rw [hv.deriv]
    exact ⟨hv,hvb⟩
  have hmean := norm_image_sub_le_of_norm_deriv_right_le_segment hf
    (fun u hu => (hlocal u hu).1.hasDerivWithinAt) (fun u hu => (hlocal u hu).2)
  intro t ht
  simpa only [hzero,sub_zero] using hmean t ht

variable {n : ℕ}

def varianceSigma (ξ : Fin (n+2) → ℝ) (t : ℝ) (i : Fin (n+2)) : ℝ := Real.sqrt (1+t*ξ i)

def varianceOffsets (n : ℕ) (ξ : Fin (n+2) → ℝ) (t : ℝ) : centeredGauge (Fin (n+2)) :=
  selectedOffsets (diagonalRows (varianceSigma ξ t)) (uniformMass n)

def varianceOffsetVector (n : ℕ) (ξ : Fin (n+2) → ℝ) (t : ℝ) : Fin (n+2) → ℝ :=
  varianceOffsets n ξ t

lemma meanAbs_le (ξ : Fin (n+2) → ℝ) (A : ℝ) (hA : ∀ i,|ξ i| ≤ A) : meanAbs ξ ≤ A := by
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hA i)
  unfold meanAbs
  have hm : (0:ℝ) < Fintype.card (Fin (n+2)) := by simp;positivity
  apply (div_le_iff₀ hm).mpr
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hs

lemma varianceSigma_box (ξ : Fin (n+2) → ℝ) (A a t : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1/16) (ht : 0 ≤ t) (htA : t*A ≤ a)
    (hξ : ∀ i,|ξ i| ≤ A) :
    (∀ i,1-a ≤ varianceSigma ξ t i) ∧ (∀ i,varianceSigma ξ t i ≤ 1+a) ∧
      (∀ i,0 < 1+t*ξ i) := by
  have hb (i : Fin (n+2)) : |t*ξ i| ≤ a := by
    rw [abs_mul,abs_of_nonneg ht]
    exact (mul_le_mul_of_nonneg_left (hξ i) ht).trans htA
  have hpos (i : Fin (n+2)) : 0 < 1+t*ξ i := by have hh := (abs_le.mp (hb i)).1;linarith
  have hsq (i : Fin (n+2)) : (varianceSigma ξ t i)^2=1+t*ξ i := Real.sq_sqrt (hpos i).le
  have hnon (i : Fin (n+2)) : 0 ≤ varianceSigma ξ t i := Real.sqrt_nonneg _
  refine ⟨?_,?_,hpos⟩
  · intro i
    have hh := (abs_le.mp (hb i)).1
    have ha2 : 0 ≤ a*(1-a) := mul_nonneg ha.le (by linarith)
    nlinarith [hsq i,hnon i]
  · intro i
    have hh := (abs_le.mp (hb i)).2
    nlinarith [hsq i,hnon i,sq_nonneg a]

lemma varianceSigma_hasDerivAt (ξ : Fin (n+2) → ℝ) (t : ℝ)
    (hpos : ∀ i,0 < 1+t*ξ i) :
    HasDerivAt (varianceSigma ξ) (fun i => ξ i/(2*varianceSigma ξ t i)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hp : HasDerivAt (fun s : ℝ => 1+s*ξ i) (ξ i) t := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id t).mul_const (ξ i)).const_add 1
  have hq := Real.hasDerivAt_sqrt (ne_of_gt (hpos i))
  change HasDerivAt (fun s => Real.sqrt (1+s*ξ i)) (ξ i/(2*Real.sqrt (1+t*ξ i))) t
  convert hq.comp t hp using 1
  · rfl
  · ring

lemma varianceSigma_speed_ratio (ξ : Fin (n+2) → ℝ) (t : ℝ)
    (hσ : ∀ i,(1/2:ℝ) ≤ varianceSigma ξ t i) (i : Fin (n+2)) :
    |(ξ i/(2*varianceSigma ξ t i))/varianceSigma ξ t i| ≤ 2*|ξ i| := by
  have hp : 0 < varianceSigma ξ t i := by linarith [hσ i]
  have he : |(ξ i/(2*varianceSigma ξ t i))/varianceSigma ξ t i|=
      |ξ i|/(2*(varianceSigma ξ t i)^2) := by
    rw [abs_div,abs_div,abs_mul,abs_of_pos hp]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  rw [he]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(varianceSigma ξ t i)^2)).mpr
  have hsq : (1/4:ℝ) ≤ (varianceSigma ξ t i)^2 := by nlinarith [hσ i]
  have hh := mul_le_mul_of_nonneg_right hsq (abs_nonneg (ξ i))
  nlinarith

lemma varianceOffsetVector_zero (n : ℕ) (ξ : Fin (n+2) → ℝ) : varianceOffsetVector n ξ 0=0 := by
  have h0 := standard_selectedOffsets_zero n
  have he : varianceSigma ξ 0=(fun _ => (1:ℝ)) := by funext i;simp [varianceSigma]
  change (selectedOffsets (diagonalRows (varianceSigma ξ 0)) (uniformMass n) : Fin (n+2) → ℝ)=0
  rw [he]
  change (selectedOffsets (diagonalRows (fun _ : Fin (n+2) => (1:ℝ)))
    (fun _ => 1/((n:ℝ)+2)) : Fin (n+2) → ℝ)=0
  simp_rw [one_div]
  exact congrArg (fun h : centeredGauge (Fin (n+2)) => (h : Fin (n+2) → ℝ)) h0

lemma varianceOffsetVector_continuousAt (ξ : Fin (n+2) → ℝ) (t : ℝ)
    (hσ : ∀ i,0 < varianceSigma ξ t i) : ContinuousAt (varianceOffsetVector n ξ) t := by
  have hsel := (selected_diagonal_parameters_contDiffAt (varianceSigma ξ t) hσ
    (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)).continuousAt
  have hpath : ContinuousAt (varianceSigma ξ) t := by unfold varianceSigma;fun_prop
  exact (centeredGauge (Fin (n+2))).subtypeL.continuous.continuousAt.comp (hsel.comp hpath)

/-- Literal uniform moment information retained with the continuation box. -/
def MomentBoxControl (n : ℕ) (a η : ℝ) (P Q : ℕ) : Prop :=
  ∀ (p q : ℕ), p ≤ P → q ≤ Q → ∀ (σ h : Fin (n+2) → ℝ),
    (∀ i,1-a ≤ σ i) → (∀ i,σ i ≤ 1+a) → (∀ i,|h i| ≤ a*upperQuantile n) →
    ∀ i j : Fin (n+2),
    ((n:ℝ)+2)^(-2-η/2) ≤ (∫x,hazardPairDensity σ h x i j) ∧
    (∫x,momentDensity σ h p q i j x) ≤ ((n:ℝ)+2)^(-2+η/2) ∧
    (∫x,momentDensity σ h p q i j x)/(∫x,hazardPairDensity σ h x i j) ≤ ((n:ℝ)+2)^η

/-- One uniform short interval works for every bounded variance direction.
The offset box is proved, not assumed; all finite moments needed by the later
second-derivative estimate are retained in that same box. No centering of the
variance direction is needed for this continuation statement. -/
theorem exists_uniform_variance_offset_continuation (η A : ℝ) (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/16 ∧
      ∀ᶠ n : ℕ in atTop, MomentBoxControl n a η 2 8 ∧
        ∀ (ξ : Fin (n+2) → ℝ), (∀ i,|ξ i| ≤ A) →
        ∀ t∈Icc 0 (((n:ℝ)+2)^(-30*η)),
          (∀ i,1-a ≤ varianceSigma ξ t i ∧ varianceSigma ξ t i ≤ 1+a) ∧
          (∀ i,|varianceOffsetVector n ξ t i| < a*upperQuantile n) ∧
          (∀ i,|varianceOffsetVector n ξ t i| ≤ 2*A*((n:ℝ)+2)^(3*η)*t) ∧
          ∃ k : centeredGauge (Fin (n+2)),
            HasDerivAt (varianceOffsets n ξ) k t ∧
            ∀ i,|(k : Fin (n+2) → ℝ) i| ≤ ((n:ℝ)+2)^(3*η)*(|ξ i|+meanAbs ξ) := by
  obtain ⟨a₀,ha₀,ha₀1,hderiv⟩ := exists_uniform_selected_offset_bound η hη
  obtain ⟨a₁,ha₁,ha₁1,hmom⟩ := exists_uniform_box_moment_family η hη 2 8
  let a := min a₀ a₁
  have ha : 0 < a := lt_min ha₀ ha₁
  have haa₀ : a ≤ a₀ := min_le_left _ _
  have haa₁ : a ≤ a₁ := min_le_right _ _
  have ha1 : a ≤ 1/16 := haa₀.trans ha₀1
  have hsmall := eventually_rpow_quantile_polynomial_le (4*A/a) (by positivity)
    0 (-27*η) 0 (by nlinarith)
  refine ⟨a,ha,ha1,?_⟩
  filter_upwards [hderiv,hmom,hsmall,upperQuantile_tendsto.eventually_ge_atTop 1]
    with n hd hmom_n hsmall_n hb
  let m : ℝ := (n:ℝ)+2
  let b := upperQuantile n
  let T : ℝ := m^(-30*η)
  let D : ℝ := 2*A*m^(3*η)
  have hm0 : 0 < m := by dsimp [m];positivity
  have hm1 : 1 ≤ m := by dsimp [m];linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hb0 : 0 ≤ b := by dsimp [b];linarith
  have hT : 0 ≤ T := Real.rpow_nonneg hm0.le _
  have hD : 0 ≤ D := by dsimp [D];positivity
  have hR : 0 < a*b := mul_pos ha (by dsimp [b];linarith)
  have hpow1 : 1 ≤ m^(3*η) := Real.one_le_rpow hm1 (by positivity)
  have hsmall_n' : (4*A/a)*m^(-27*η) ≤ 1 := by
    simpa only [pow_zero,mul_one,Real.rpow_zero,m] using hsmall_n
  have hDT : D*T ≤ a/2 := by
    have he : D*T=(a/2)*((4*A/a)*m^(-27*η)) := by
      dsimp [D,T]
      rw [mul_assoc,←Real.rpow_add hm0,show 3*η+(-30*η)=(-27*η) by ring]
      field_simp
      <;> ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hsmall_n' (by positivity)).trans_eq (by ring)
  have hAT : A*T ≤ a := by
    have hAD : A ≤ D := by dsimp [D];nlinarith [mul_nonneg hA (sub_nonneg.mpr hpow1)]
    exact (mul_le_mul_of_nonneg_right hAD hT).trans (hDT.trans (by linarith))
  have hsmallDT : D*T < a*b := by
    have hab : a ≤ a*b := by have h := mul_le_mul_of_nonneg_left hb ha.le;simpa only [mul_one,b] using h
    linarith
  have hmoment : MomentBoxControl n a η 2 8 := by
    intro p q hp hq σ h hσlo hσhi hh i j
    apply hmom_n p q hp hq σ h
    · intro k;linarith [hσlo k]
    · intro k;linarith [hσhi k]
    · intro k
      exact (hh k).trans (mul_le_mul_of_nonneg_right haa₁ hb0)
  refine ⟨hmoment,?_⟩
  intro ξ hξ
  have hsig (t : ℝ) (ht : t∈Icc 0 T) :
      (∀ i,1-a ≤ varianceSigma ξ t i) ∧ (∀ i,varianceSigma ξ t i ≤ 1+a) ∧
      (∀ i,0 < 1+t*ξ i) := by
    apply varianceSigma_box ξ A a t ha ha1 ht.1 _ hξ
    have hh := mul_le_mul_of_nonneg_right ht.2 hA
    nlinarith only [hh,hAT]
  have hsigpos (t : ℝ) (ht : t∈Icc 0 T) : ∀ i,0 < varianceSigma ξ t i :=
    fun i => lt_of_lt_of_le (by linarith) ((hsig t ht).1 i)
  have hactual (t : ℝ) (ht : t∈Icc 0 T) (hbox : ‖varianceOffsetVector n ξ t‖ ≤ a*b) :
      ∃ k : centeredGauge (Fin (n+2)),HasDerivAt (varianceOffsets n ξ) k t ∧
        ∀ i,|(k : Fin (n+2) → ℝ) i| ≤ m^(3*η)*(|ξ i|+meanAbs ξ) := by
    let ζ := fun i => ξ i/(2*varianceSigma ξ t i)
    have hz : ∀ i,|ζ i/varianceSigma ξ t i| ≤ 2*|ξ i| :=
      varianceSigma_speed_ratio ξ t (fun i => by have hh := (hsig t ht).1 i;linarith)
    have hh : ∀ i,|(selectedOffsets (diagonalRows (varianceSigma ξ t)) (uniformMass n) : Fin (n+2) → ℝ) i| ≤ a₀*upperQuantile n := by
      intro i
      have hi := norm_le_pi_norm (varianceOffsetVector n ξ t) i
      rw [Real.norm_eq_abs] at hi
      exact (hi.trans hbox).trans (mul_le_mul_of_nonneg_right haa₀ hb0)
    obtain ⟨k,hk,hkb⟩ := hd (varianceSigma ξ t) ζ ξ (uniformMass n)
      (uniformMass_pos n) (uniformMass_sum n)
      (fun i => by have hh := (hsig t ht).1 i;linarith)
      (fun i => by have hh := (hsig t ht).2.1 i;linarith) hh hz
    have hpath := varianceSigma_hasDerivAt ξ t (hsig t ht).2.2
    exact ⟨k,selected_derivative_of_path (varianceSigma ξ) ζ t (hsigpos t ht) hpath
      (uniformMass n) (uniformMass_pos n) (uniformMass_sum n) k hk,hkb⟩
  have hcont : ContinuousOn (varianceOffsetVector n ξ) (Icc 0 T) :=
    fun t ht => (varianceOffsetVector_continuousAt ξ t (hsigpos t ht)).continuousWithinAt
  have hderiv_norm (t : ℝ) (ht : t∈Icc 0 T) (hbox : ‖varianceOffsetVector n ξ t‖ ≤ a*b) :
      ∃ v,HasDerivAt (varianceOffsetVector n ξ) v t ∧ ‖v‖ ≤ D := by
    obtain ⟨k,hk,hkb⟩ := hactual t ht hbox
    refine ⟨(k : Fin (n+2) → ℝ),?_,?_⟩
    · exact (centeredGauge (Fin (n+2))).subtypeL.hasFDerivAt.comp_hasDerivAt t hk
    · apply (pi_norm_le_iff_of_nonneg hD).mpr
      intro i
      rw [Real.norm_eq_abs]
      have hmean := meanAbs_le ξ A hξ
      have hh := mul_le_mul_of_nonneg_left (show |ξ i|+meanAbs ξ ≤ 2*A by linarith [hξ i])
        (Real.rpow_nonneg hm0.le (3*η))
      exact (hkb i).trans (hh.trans_eq (by dsimp [D];ring))
  have hboot := norm_first_exit_bound (varianceOffsetVector n ξ) T (a*b) D hT hR hD
    hcont (varianceOffsetVector_zero n ξ) hsmallDT hderiv_norm
  intro t ht
  have ht' : t∈Icc 0 T := ht
  refine ⟨fun i => ⟨(hsig t ht').1 i,(hsig t ht').2.1 i⟩,?_,?_,?_⟩
  · intro i
    have hh := norm_le_pi_norm (varianceOffsetVector n ξ t) i
    rw [Real.norm_eq_abs] at hh
    exact hh.trans_lt (hboot.1 t ht')
  · intro i
    have hh := norm_le_pi_norm (varianceOffsetVector n ξ t) i
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (hboot.2 t ht')
  · exact hactual t ht' (hboot.1 t ht').le

end NegativeVotingDiagonalOffsetContinuation
