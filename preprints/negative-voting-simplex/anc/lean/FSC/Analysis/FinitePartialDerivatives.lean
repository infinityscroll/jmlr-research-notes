import FSC.Analysis.PartialDerivatives
import Mathlib.Data.Finset.Piecewise
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! Finite coordinate partial derivatives assembled into a genuine Frechet derivative. -/

noncomputable section

open Filter Asymptotics
open scoped Topology Convex

namespace FSC

/-
The following variable-slice lemma is adapted narrowly from
Mathlib/Analysis/Calculus/FDeriv/Partial.lean, lines 31-50, at mathlib revision
fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Its original declaration is not public.
Copyright (c) 2025 A Tucker. All rights reserved.
Released under Apache 2.0 license as described in the pinned mathlib LICENSE.
Authors: A Tucker
Changes: declaration renamed and private to this adapter; proof and hypotheses preserved.
This notice applies to the adapted lemma, not a new-work license for this project.
-/
private theorem variable_slice_remainder
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : E} {v w : α → E} {l : Filter α} (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E := Set.univ) (seg : ∀ᶠ χ in l, [w χ -[ℝ] v χ] ⊆ s := by simp)
    {f : α → E → F} {f' : α → E → E →L[𝕜] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[𝕜] F} (cf' : Tendsto (Function.uncurry f') (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l] (fun χ => v χ - w χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace df' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], HasFDerivWithinAt (f χ) (f' χ z) s z :=
    df'.segment_of_prod_nhdsWithin hw hv seg
  replace cf' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], ‖f' χ z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, df', cf'] with χ seg df' cf'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (df' z hz).mono seg) (fun z hz => (cf' z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite coordinate derivative assembled in the original index space. -/
def piGradient (p : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, p i • ContinuousLinearMap.proj i

omit [DecidableEq ι] in
@[simp] theorem piGradient_apply (p h : ι → ℝ) : piGradient p h = ∑ i, p i * h i := by
  simp [piGradient]

omit [Fintype ι] in
private theorem continuous_partialIncrement (x : ι → ℝ) (s : Finset ι) :
    Continuous (fun h : ι → ℝ ↦ s.piecewise (x + h) x) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ s
  · simpa only [Finset.piecewise_eq_of_mem s _ _ hi, Pi.add_apply] using!
      continuous_const.add (continuous_apply i)
  · simpa only [Finset.piecewise_eq_of_notMem s _ _ hi] using!
      (continuous_const : Continuous (fun _ : ι → ℝ ↦ x i))

omit [Fintype ι] in
private theorem tendsto_partialIncrement (x : ι → ℝ) (s : Finset ι) :
    Tendsto (fun h : ι → ℝ ↦ s.piecewise (x + h) x) (𝓝 0) (𝓝 x) := by
  simpa [Finset.piecewise_same] using! (continuous_partialIncrement x s).tendsto (0 : ι → ℝ)

private theorem coordinate_remainder_isLittleO
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (i : ι) (s : Finset ι) (hi : i ∉ s)
    (hp : ∀ᶠ y in 𝓝 x,
      HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ContinuousAt (fun y ↦ p y i) x) :
    (fun h : ι → ℝ ↦
      f ((insert i s).piecewise (x + h) x) - f (s.piecewise (x + h) x) - p x i * h i)
      =o[𝓝 0] (fun h ↦ h) := by
  let z : (ι → ℝ) × ℝ → (ι → ℝ) :=
    fun ha ↦ Function.update (s.piecewise (x + ha.1) x) i ha.2
  let D : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  have hz : Tendsto z ((𝓝 (0 : ι → ℝ)) ×ˢ 𝓝 (x i)) (𝓝 x) := by
    have h := ((tendsto_partialIncrement x s).comp tendsto_fst).update i
      (tendsto_snd : Tendsto Prod.snd ((𝓝 (0 : ι → ℝ)) ×ˢ 𝓝 (x i)) (𝓝 (x i)))
    simpa [z] using! h
  have hdf : ∀ᶠ ha in ((𝓝 (0 : ι → ℝ)) ×ˢ 𝓝 (x i)),
      HasFDerivWithinAt
        (fun a : ℝ ↦ f (Function.update (s.piecewise (x + ha.1) x) i a))
        (D (p (z ha) i)) Set.univ ha.2 := by
    filter_upwards [hz.eventually hp] with ha hha
    simpa only [z, D, Function.update_self, Function.update_idem] using!
      hha.hasFDerivAt.hasFDerivWithinAt
  have hcf : Tendsto (fun ha : (ι → ℝ) × ℝ ↦ D (p (z ha) i))
      ((𝓝 (0 : ι → ℝ)) ×ˢ 𝓝 (x i)) (𝓝 (D (p x i))) :=
    (D.continuous.tendsto (p x i)).comp (hcp.tendsto.comp hz)
  have hv : Tendsto (fun h : ι → ℝ ↦ (x + h) i) (𝓝 0) (𝓝 (x i)) := by
    simpa using! (continuous_const.add (continuous_apply i)).tendsto (0 : ι → ℝ)
  have ht := variable_slice_remainder (𝕜 := ℝ)
    (f := fun h a ↦ f (Function.update (s.piecewise (x + h) x) i a))
    (f' := fun h a ↦ D (p (z (h, a)) i))
    (s := Set.univ)
    (df' := by simpa only [nhdsWithin_univ] using! hdf)
    (cf' := by simpa only [nhdsWithin_univ] using! hcf)
    (φ := D (p x i)) hv (tendsto_const_nhds (x := x i))
  have hsmall : (fun h : ι → ℝ ↦
      f ((insert i s).piecewise (x + h) x) - f (s.piecewise (x + h) x) - p x i * h i)
      =o[𝓝 0] (fun h ↦ h i) := by
    simpa [Finset.piecewise_insert, Finset.update_piecewise_of_notMem s _ _ hi,
      D, mul_comm] using! ht
  exact hsmall.trans_isBigO
    ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).isBigO_comp (fun h ↦ h) (𝓝 0))

/-- Continuous partial derivatives at the base assemble across any finite index type. -/
theorem hasFDerivAt_pi_of_partials
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hp : ∀ i, ∀ᶠ y in 𝓝 x,
      HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ∀ i, ContinuousAt (fun y ↦ p y i) x) :
    HasFDerivAt f (piGradient (p x)) x := by
  have hsmall (s : Finset ι) :
      (fun h : ι → ℝ ↦ f (s.piecewise (x + h) x) - f x - ∑ i ∈ s, p x i * h i)
        =o[𝓝 0] (fun h ↦ h) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have h := (coordinate_remainder_isLittleO i s hi (hp i) (hcp i)).add ih
      convert! h using 1
      ext h
      rw [Finset.sum_insert hi]
      ring
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  simpa using! hsmall Finset.univ

/-- Local partial witnesses give the assembled derivative throughout a neighborhood. -/
theorem eventually_hasFDerivAt_pi_of_partials
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hp : ∀ i, ∀ᶠ y in 𝓝 x,
      HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ∀ i, ∀ᶠ y in 𝓝 x, ContinuousAt (fun z ↦ p z i) y) :
    ∀ᶠ y in 𝓝 x, HasFDerivAt f (piGradient (p y)) y := by
  have hdf := (eventually_all.mpr hp).eventually_nhds
  filter_upwards [hdf, eventually_all.mpr hcp] with y hdy hcy
  exact hasFDerivAt_pi_of_partials (eventually_all.mp hdy) hcy

/-- Local continuous partial fields give C1 near the actual support, allowing ties elsewhere. -/
theorem contDiffAt_one_pi_of_partials
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hp : ∀ i, ∀ᶠ y in 𝓝 x,
      HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ∀ i, ∀ᶠ y in 𝓝 x, ContinuousAt (fun z ↦ p z i) y) :
    ContDiffAt ℝ 1 f x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
  refine ⟨fun y ↦ piGradient (p y), ?_, ?_⟩
  · exact ⟨_, eventually_hasFDerivAt_pi_of_partials hp hcp, fun _ hy ↦ hy⟩
  · apply contDiffAt_zero.mpr
    refine ⟨{y | ∀ i, ContinuousAt (fun z ↦ p z i) y}, eventually_all.mpr hcp, ?_⟩
    intro y hy
    have h : ContinuousAt (fun z ↦ piGradient (p z)) y := by
      unfold piGradient
      exact tendsto_finsetSum Finset.univ fun i _ ↦ (hy i).smul continuousAt_const
    exact h.continuousWithinAt

/-- Local C1 partial fields give C2 at the actual support. -/
theorem contDiffAt_two_pi_of_partials
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ} {x : ι → ℝ}
    (hp : ∀ i, ∀ᶠ y in 𝓝 x,
      HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ∀ i, ContDiffAt ℝ 1 (fun y ↦ p y i) x) : ContDiffAt ℝ 2 f x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun y ↦ piGradient (p y), ?_, ?_⟩
  · have hc : ∀ i, ∀ᶠ y in 𝓝 x, ContinuousAt (fun z ↦ p z i) y :=
      fun i ↦ ((hcp i).eventually (by norm_num)).mono fun _ hy ↦ hy.continuousAt
    exact ⟨_, eventually_hasFDerivAt_pi_of_partials hp hc, fun _ hy ↦ hy⟩
  · exact ContDiffAt.sum fun i _ ↦ (hcp i).smul contDiffAt_const

/-- Global slice witnesses specialize the local finite-coordinate theorem. -/
theorem hasFDerivAt_pi_of_partials_global
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ}
    (hp : ∀ i y, HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ∀ i, Continuous (fun y ↦ p y i)) (x : ι → ℝ) :
    HasFDerivAt f (piGradient (p x)) x :=
  hasFDerivAt_pi_of_partials (fun i ↦ Eventually.of_forall (hp i))
    (fun i ↦ (hcp i).continuousAt)

/-- Continuous partial fields give C1 in the original finite coordinate domain. -/
theorem contDiff_one_pi_of_partials
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ}
    (hp : ∀ i y, HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ∀ i, Continuous (fun y ↦ p y i)) : ContDiff ℝ 1 f := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ piGradient (p x), ?_, hasFDerivAt_pi_of_partials_global hp hcp⟩
  exact continuous_finsetSum Finset.univ fun i _ ↦ (hcp i).smul continuous_const

/-- C1 partial fields give C2, without changing finite coordinate conventions. -/
theorem contDiff_two_pi_of_partials
    {f : (ι → ℝ) → ℝ} {p : (ι → ℝ) → ι → ℝ}
    (hp : ∀ i y, HasDerivAt (fun a : ℝ ↦ f (Function.update y i a)) (p y i) (y i))
    (hcp : ∀ i, ContDiff ℝ 1 (fun y ↦ p y i)) : ContDiff ℝ 2 f := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ piGradient (p x), ?_,
    hasFDerivAt_pi_of_partials_global hp (fun i ↦ (hcp i).continuous)⟩
  exact ContDiff.sum fun i _ ↦ (hcp i).smul contDiff_const

end FSC
