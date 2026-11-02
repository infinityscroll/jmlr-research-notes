import GaussianFanOffsetCovarianceLaw
import GaussianRegularFacetCylinder
import NegativeVoting.RegularSimplexMoments

/-! Exact equal-offset mass symmetry of an actual regular Gaussian fan,
using score-Gram invariance and pointwise symmetric tie splitting. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace NegativeVotingRegularMassSymmetry
open NegativeVoting NegativeVotingFan NegativeVotingFanOffsetCovarianceLaw
  NegativeVotingFacetConditionalPlane
variable {d : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem mass_permuted_rows_offsets (B : V → FSC.Coord d) (h : V → ℝ)
    (e : Equiv.Perm V) (i : V) :
    mass (fun j => B (e j)) (fun j => h (e j)) i=mass B h (e i) := by
  unfold mass
  apply integral_congr_ae
  filter_upwards with x
  change maxWeights (fun j => scores B h x (e j)) i=maxWeights (scores B h x) (e i)
  exact maxWeights_perm _ e i

theorem regular_mass_permuted_offsets (B : V → FSC.Coord d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (h : V → ℝ) (e : Equiv.Perm V) (i : V) :
    mass B (fun j => h (e j)) i=mass B h (e i) := by
  have hinj : Function.Injective B := by
    intro j k he
    by_contra hne
    exact regular_gram_rows_ne B a hG j k hne he
  have hGram : ∀j k,inner ℝ (B j) (B k)=inner ℝ (B (e j)) (B (e k)) := by
    intro j k
    simp only [hG,e.injective.eq_iff]
  calc
    mass B (fun j => h (e j)) i=mass (fun j => B (e j)) (fun j => h (e j)) i :=
      congrFun (mass_eq_of_gram B _ hinj hGram (fun j => h (e j))) i
    _=mass B h (e i) := mass_permuted_rows_offsets B h e i

/-- Equal offsets have exactly equal actual Gaussian masses. No full affine
basis or ambient-span premise is needed. -/
theorem regular_mass_eq_of_offset_eq (B : V → FSC.Coord d) (a : ℝ)
    (hG : ∀i j,inner ℝ (B i) (B j)=(if i=j then 1 else 0)-a)
    (h : V → ℝ) (i j : V) (hh : h i=h j) :
    mass B h i=mass B h j := by
  have he : (fun k => h (Equiv.swap i j k))=h := by
    funext k
    by_cases hki : k=i
    · subst k
      simpa only [Equiv.swap_apply_left] using hh.symm
    by_cases hkj : k=j
    · subst k
      simpa only [Equiv.swap_apply_right] using hh
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hm := regular_mass_permuted_offsets B a hG h (Equiv.swap i j) i
  simpa only [he,Equiv.swap_apply_left] using hm

end NegativeVotingRegularMassSymmetry
