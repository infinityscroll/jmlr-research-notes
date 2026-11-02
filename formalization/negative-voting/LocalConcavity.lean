import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-! A bounded local-to-global concavity principle.  Its minimum principle uses a
strict concave quadratic perturbation, so no differentiability is required. -/

open Set Filter Metric
open scoped Topology

namespace NegativeVotingLocalConcavity

theorem sub_affine {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f)
    (s c : ℝ) : ConcaveOn ℝ S (fun x => f x - (s * x + c)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy α β hα hβ hsum
  have h := hf.2 hx hy hα hβ hsum
  simp only [smul_eq_mul] at *
  have he : s * (α * x + β * y) + c =
      α * (s * x + c) + β * (s * y + c) := by
    linear_combination -c * hsum
  rw [he]
  linarith

/-- A continuous locally concave function on an interval lies above the smaller
endpoint value, expressed here after translating that value to zero. -/
theorem nonneg_of_locally_concave {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (ha : 0 ≤ f a) (hb : 0 ≤ f b)
    (hlocal : ∀ x ∈ Ioo a b, ∃ S : Set ℝ, S ∈ 𝓝 x ∧ ConcaveOn ℝ S f) :
    ∀ x ∈ Icc a b, 0 ≤ f x := by
  intro t ht
  by_contra hbad
  have hneg : f t < 0 := lt_of_not_ge hbad
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt (neg_pos.mpr hneg) ((t-a)*(b-t))
  let g : ℝ → ℝ := fun x => f x + ε * ((x-a)*(b-x))
  have hgcont : ContinuousOn g (Icc a b) :=
    hcont.add (by fun_prop)
  have hgt : g t < 0 := by dsimp [g]; linarith
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨t, ht⟩ hgcont
  have hgx : g x < 0 := lt_of_le_of_lt (hmin ht) hgt
  have hax : a < x := by
    apply lt_of_le_of_ne hx.1
    intro he
    subst x
    apply hgx.not_ge
    simpa [g] using ha
  have hxb : x < b := by
    apply lt_of_le_of_ne hx.2
    intro he
    subst x
    apply hgx.not_ge
    simpa [g] using hb
  obtain ⟨S, hSn, hSc⟩ := hlocal x ⟨hax, hxb⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hSn
  let δ := min r (min (x-a) (b-x)) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by
    have := min_le_left r (min (x-a) (b-x))
    dsimp [δ]; linarith
  have hδa : δ < x-a := by
    have := (min_le_right r (min (x-a) (b-x))).trans (min_le_left (x-a) (b-x))
    dsimp [δ]; linarith
  have hδb : δ < b-x := by
    have := (min_le_right r (min (x-a) (b-x))).trans (min_le_right (x-a) (b-x))
    dsimp [δ]; linarith
  have hymem : x-δ ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hzmem : x+δ ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hydist : dist (x-δ) x = δ := by
    rw [Real.dist_eq, show x-δ-x = -δ by ring, abs_neg, abs_of_pos hδ]
  have hzdist : dist (x+δ) x = δ := by
    rw [Real.dist_eq, show x+δ-x = δ by ring, abs_of_pos hδ]
  have hyS : x-δ ∈ S := hball (Metric.mem_ball.mpr (by rw [hydist]; exact hδr))
  have hzS : x+δ ∈ S := hball (Metric.mem_ball.mpr (by rw [hzdist]; exact hδr))
  have hmid := hSc.2 hyS hzS (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at hmid
  rw [show (1/2:ℝ)*(x-δ)+(1/2)*(x+δ)=x by ring] at hmid
  have hymin := hmin hymem
  have hzmin := hmin hzmem
  have hstrict : 0 < ε * δ^2 := mul_pos hε (sq_pos_of_pos hδ)
  dsimp [g] at hymin hzmin
  nlinarith

/-- Local concavity at every interior point, together with continuity at the
endpoints, gives concavity on the entire closed interval. -/
theorem concaveOn_Icc_of_locally_concave {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hlocal : ∀ x ∈ Ioo a b, ∃ S : Set ℝ, S ∈ 𝓝 x ∧ ConcaveOn ℝ S f) :
    ConcaveOn ℝ (Icc a b) f := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc a b)
  intro x y z hx hz hxy hyz
  have hxz : x < z := hxy.trans hyz
  let s := (f z - f x) / (z-x)
  let c := f x - s*x
  let g : ℝ → ℝ := fun u => f u - (s*u+c)
  have hsub : Icc x z ⊆ Icc a b := Icc_subset_Icc hx.1 hz.2
  have hgcont : ContinuousOn g (Icc x z) := (hcont.mono hsub).sub (by fun_prop)
  have hgx : g x = 0 := by dsimp [g,c]; ring
  have hgz : g z = 0 := by
    dsimp [g,c,s]
    field_simp [ne_of_gt (sub_pos.mpr hxz)]
    ring
  have hglocal : ∀ u ∈ Ioo x z, ∃ S : Set ℝ, S ∈ 𝓝 u ∧ ConcaveOn ℝ S g := by
    intro u hu
    obtain ⟨S, hSn, hSc⟩ := hlocal u
      ⟨lt_of_le_of_lt hx.1 hu.1, lt_of_lt_of_le hu.2 hz.2⟩
    exact ⟨S, hSn, sub_affine hSc s c⟩
  have hgy := nonneg_of_locally_concave hgcont (by rw [hgx]) (by rw [hgz])
    hglocal y ⟨hxy.le, hyz.le⟩
  have hchord : (f z-f x)*(y-x)/(z-x) ≤ f y-f x := by
    have he : (f z-f x)*(y-x)/(z-x) = s*y-s*x := by dsimp [s]; ring
    rw [he]
    dsimp [g,c] at hgy
    linarith
  have hcross := (div_le_iff₀ (sub_pos.mpr hxz)).mp hchord
  apply (div_le_div_iff₀ (sub_pos.mpr hyz) (sub_pos.mpr hxy)).mpr
  nlinarith

end NegativeVotingLocalConcavity
