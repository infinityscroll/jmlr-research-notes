import GaussianAssignmentEquality
import NegativeVoting.MainGoal
import NegativeVoting.RegularSimplexExistence

/-! Exact final quantifier and equality-class assembly. The sole remaining
premise is explicitly eventual actual competitive rigidity; this module does
not assert that premise or the full theorem unconditionally. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped BigOperators Topology Classical
namespace NegativeVotingMainGoalAssembly
open NegativeVoting NegativeVotingRegularScoreLaw NegativeVotingAssignmentEquality
  NegativeVotingRegularCovarianceDeficit NegativeVotingCentroidOptimization

def EventualCompetitiveRigidity : Prop :=
  ∀ᶠ n:ℕ in atTop,∀ d:ℕ,n+1 ≤ d →
    ∀ Ref:Fin (n+2)→Fin d→ℝ,RegularSimplexGram Ref →
    ∀ f:(Fin d→ℝ)→Fin (n+2)→ℝ,
      (∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d))) →
      (∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) →
    ∀ r:ℝ,0<r → r ≤ 1/((n:ℝ)+1) →
      gaussianNoiseStability (-r) f ≤ gaussianNoiseStability (-r) (regularAssignment Ref) →
      regularCovarianceDeficit n (centroidRows (fun x:FSC.Coord d=>f x.ofLp))=0

lemma noise_eq_of_ae_regular {n d:ℕ} (ρ:ℝ) (hρ:|ρ| ≤ 1)
    (Ref:Fin (n+2)→Fin d→ℝ) (hRef:RegularSimplexGram Ref)
    (f:(Fin d→ℝ)→Fin (n+2)→ℝ)
    (hreg:∃rows:Fin (n+2)→Fin d→ℝ,RegularSimplexGram rows ∧
      ∀ᵐx ∂standardGaussian (Fin d),f x=regularAssignment rows x) :
    gaussianNoiseStability ρ f=gaussianNoiseStability ρ (regularAssignment Ref) := by
  obtain ⟨rows,hrows,hAE⟩:=hreg
  rw [gaussianNoiseStability_congr_ae ρ hρ f (regularAssignment rows) hAE,
    regularAssignment_noise_eq_canonical n rows hrows ρ,
    regularAssignment_noise_eq_canonical n Ref hRef ρ]

/-- The exact original target follows from the actual rigidity endpoint.
The label threshold comes before the ambient dimension, noise and rule, and
the existential regular reference is constructed in every allowed dimension. -/
theorem fullStatement_of_eventual_competitive_rigidity (H:EventualCompetitiveRigidity) :
    FullNegativeVotingStatement := by
  obtain ⟨N,hN⟩:=Filter.eventually_atTop.mp H
  unfold FullNegativeVotingStatement
  refine ⟨max (N+2) 3,by omega,?_⟩
  intro m hm
  have hm3:3 ≤ m:=(le_max_right _ _).trans hm
  obtain ⟨k,rfl⟩:(∃k:ℕ,m=k+2):=⟨m-2,by omega⟩
  intro d hdim
  obtain ⟨Ref,hRef⟩:=exists_regularSimplexGram_main_dimensions hm3 hdim
  refine ⟨Ref,hRef,?_⟩
  intro ρ hρlo hρhi f hf hp
  have hk:0<k:=by omega
  have hkN:N ≤ k:=by omega
  have hdim':k+1 ≤ d+1:=by omega
  have hr: -ρ ≤ 1/((k:ℝ)+1):=by
    simp only [Nat.cast_add,Nat.cast_ofNat] at hρlo
    have he:(k:ℝ)+2-1=(k:ℝ)+1:=by ring
    rw [he] at hρlo
    linarith
  have hρabs:|ρ| ≤ 1:=by
    rw [abs_of_neg hρhi]
    apply hr.trans
    apply (div_le_one (by positivity : (0:ℝ)<(k:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hclass (hcomp:gaussianNoiseStability ρ f ≤ gaussianNoiseStability ρ (regularAssignment Ref)) :
      ∃rows:Fin (k+2)→Fin (d+1)→ℝ,RegularSimplexGram rows ∧
        ∀ᵐx ∂standardGaussian (Fin (d+1)),f x=regularAssignment rows x:=by
    apply product_regular_of_zero_covariance_deficit hk f hf hp
    have hz:=hN k hkN (d+1) hdim' Ref hRef f hf hp (-ρ) (by linarith) hr
      (by simpa only [neg_neg] using hcomp)
    exact hz
  constructor
  · by_cases hcomp:gaussianNoiseStability ρ f ≤ gaussianNoiseStability ρ (regularAssignment Ref)
    · exact (noise_eq_of_ae_regular ρ hρabs Ref hRef f (hclass hcomp)).ge
    · exact (lt_of_not_ge hcomp).le
  · constructor
    · intro heq;exact hclass heq.le
    · intro hreg;exact noise_eq_of_ae_regular ρ hρabs Ref hRef f hreg

end NegativeVotingMainGoalAssembly
