import GaussianFanCovarianceLaw
import GaussianFanMassInverse

/-! Actual prescribed offsets are intrinsic to the Gaussian score Gram matrix,
including when its full-rank realizations use different ambient dimensions. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace NegativeVotingFanOffsetCovarianceLaw
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanCovarianceLaw
  NegativeVotingCapTail NegativeVotingFacetDegree
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {d e : ℕ}

theorem injective_of_gram (B : V → FSC.Coord d) (C : V → FSC.Coord e)
    (hB : Function.Injective B)
    (hGram : ∀ i j, inner ℝ (B i) (B j)=inner ℝ (C i) (C j)) : Function.Injective C := by
  intro i j he
  apply hB
  apply sub_eq_zero.mp
  have hz : inner ℝ (B i-B j) (B i-B j)=0 := by
    simp only [inner_sub_left,inner_sub_right,hGram,he,sub_self]
  exact inner_self_eq_zero.mp hz

/-- Equality of literal Gaussian masses is obtained by differentiating the
same expected-maximum function, not by assuming a factor-invariance rule. -/
theorem mass_eq_of_gram (B : V → FSC.Coord d) (C : V → FSC.Coord e)
    (hB : Function.Injective B)
    (hGram : ∀ i j, inner ℝ (B i) (B j)=inner ℝ (C i) (C j)) (h : V → ℝ) :
    mass B h=mass C h := by
  have hC := injective_of_gram B C hB hGram
  funext i
  let v : V → ℝ := Pi.single i 1
  have hfun : (fun t : ℝ => expectedMax B (fun j => h j+t*v j)) =
      (fun t : ℝ => expectedMax C (fun j => h j+t*v j)) :=
    funext (fun t => expectedMax_eq_of_gram B C hGram (fun j => h j+t*v j))
  have hdB := hasDerivAt_expectedMax B hB h v
  have hdC := hasDerivAt_expectedMax C hC h v
  rw [hfun] at hdB
  simpa [v,Pi.single_apply] using hdB.unique hdC

/-- Centering fixes the offset gauge, so two full-rank realizations of one
covariance and one prescribed mass vector have literally equal offsets. -/
theorem centered_offsets_eq_of_gram (B : V → FSC.Coord d) (C : V → FSC.Coord e)
    (σ : ℝ) (hσ : 0 < σ) (hlower : CenteredSingularLowerBound B σ)
    (hGram : ∀ i j, inner ℝ (B i) (B j)=inner ℝ (C i) (C j))
    (h k : V → ℝ) (hh : ∑ i, h i=0) (hk : ∑ i, k i=0)
    (hm : mass B h=mass C k) : h=k := by
  have hB : Function.Injective B := fun i j he => by
    by_contra hij
    exact centered_singular_rows_ne B σ hσ hlower i j hij he
  exact centered_offsets_unique B σ hσ hlower h k hh hk
    (hm.trans (mass_eq_of_gram B C hB hGram k).symm)

end NegativeVotingFanOffsetCovarianceLaw
