import GaussianRegularizedMassConcavity
import GaussianBalancedFloorAnchor

/-! The uniform quadratic prescribed-mass bound for the actual Gaussian
covariance objective, with the stationary balanced anchor discharged. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators RealInnerProductSpace
namespace NegativeVotingMassSemiconcavity
open NegativeVotingRegularizedMassConcavity NegativeVotingBalancedFloorAnchor
  NegativeVotingBalancedReference NegativeVotingBalancedMaximum
  NegativeVotingGaussianMaximumMean NegativeVotingOptimizerConstants
  NegativeVotingCovarianceOptimizer NegativeVotingCovarianceOptimizerContinuity
  NegativeVotingCovarianceOptimizerLipschitz NegativeVotingCovarianceConcavity
  NegativeVotingCovarianceStrict NegativeVotingCovarianceCoercivity
  NegativeVotingPositiveCovariance NegativeVotingLocalCovarianceFactor
  NegativeVotingFanInverse
variable {n d:ℕ}

def massValueUpperBound (n:ℕ) (p:Fin (n+2)→ℝ):ℝ:=
  referenceFirstWeight n+mixedConstant*(1+Real.log ((n:ℝ)+2))^2*
    ∑i,(p i-uniformMass n i)^2

theorem uniformMass_mem_window (n:ℕ) :
    ∀i,uniformMass n i∈Icc (actualMassLower ((n+2:ℕ):ℝ)) (2/((n+2:ℕ):ℝ)) := by
  intro i
  have hm:0<(n:ℝ)+2:=by positivity
  simp only [actualMassLower,uniformMass,Nat.cast_add,Nat.cast_ofNat]
  constructor
  · apply one_div_le_one_div_of_le hm
    nlinarith
  · exact div_le_div_of_nonneg_right (by norm_num) hm.le

/-- For every sufficiently small positive covariance floor, the actual
objective is bounded on the whole floor cone, uniformly over the first mass
window. The constant and alphabet threshold are absolute. -/
theorem uniform_positive_floor_mass_bound
    (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hG:∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (hP:∀x,(∑i,inner ℝ (b i) x • b i)=x)
    (hdim : 2 ≤ d) (hm : numericThreshold ≤ n+2) :
    ∃δ:ℝ,0<δ ∧ ∀ε:ℝ,0<ε → ε<δ → ∀p:Fin (n+2)→ℝ,
      (∑i,p i=1) →
      (∀i,p i∈Icc (actualMassLower ((n+2:ℕ):ℝ)) (2/((n+2:ℕ):ℝ))) →
      ∀C:FSC.Coord d→L[ℝ]FSC.Coord d,C∈lowerCovarianceCone ε →
        penalizedValue b p C≤ massValueUpperBound n p := by
  have hG':∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  obtain ⟨δ0,hδ0,hConc⟩:=uniform_regularized_path_concavity b hG' hP hdim hm
  have hn:0<n:=by
    have hh:3 ≤ n+2:=(numericThreshold_spec (n+2) hm).1
    omega
  let δ:=min δ0 ((referenceScale n)^2)
  have hδ:0<δ:=lt_min hδ0 (sq_pos_of_pos (referenceScale_pos n))
  refine ⟨δ,hδ,?_⟩
  intro ε hε hεδ p hs hbox C hC
  have hεδ0:ε<δ0:=lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεa:ε<(referenceScale n)^2:=lt_of_lt_of_le hεδ (min_le_right _ _)
  have hmreal:0<((n+2:ℕ):ℝ):=by positivity
  have hlo:0<actualMassLower ((n+2:ℕ):ℝ):=by unfold actualMassLower;positivity
  have hp:∀i,0<p i:=fun i=>hlo.trans_le (hbox i).1
  let pp:PositiveProbability (n+2):=⟨p,hp,hs⟩
  let p0:=balancedProbability n
  let v:centeredGauge (Fin (n+2)):=⟨p-uniformMass n,by
    change ∑i,(p i-uniformMass n i)=0
    rw [Finset.sum_sub_distrib,hs,uniformMass_sum n,sub_self]⟩
  have hline:∀t∈Icc (0:ℝ) 1,∀i,
      actualMassLower ((n+2:ℕ):ℝ)≤((p0:Fin (n+2)→ℝ)+t • (v:Fin (n+2)→ℝ)) i ∧
      ((p0:Fin (n+2)→ℝ)+t • (v:Fin (n+2)→ℝ)) i≤2/((n+2:ℕ):ℝ):=
    mass_segment_mem_window (uniformMass n) p _ _ (uniformMass_mem_window n) hbox
  let L:=mixedConstant*(1+Real.log ((n:ℝ)+2))^2
  have hc:ConcaveOn ℝ (Icc (0:ℝ) 1)
      (fun t=>regularizedPathValue b ε hε p0 v t-(L*∑i,((v:Fin (n+2)→ℝ) i)^2)*t^2):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat,L] using hConc ε hε hεδ0 p0 v 0 1 hline
  have hd:HasDerivAt (regularizedPathValue b ε hε p0 v) 0 0:=by
    exact selected_balanced_path_derivative_zero hn b hG hP ε hε hεa v
  have hb:=regularized_path_bound_of_stationary_anchor b ε hε p0 v L hc hd
  have hProb0:pathProbability p0 v 0=p0:=by
    simp only [pathProbability,zero_smul,probabilityChart_zero]
  have he1:(p0:Fin (n+2)→ℝ)+(1:ℝ) • (v:Fin (n+2)→ℝ)=p:=by
    change uniformMass n+(1:ℝ) • (p-uniformMass n)=p
    simp only [one_smul]
    abel
  have hp1:∀i,0<((p0:Fin (n+2)→ℝ)+(1:ℝ) • (v:Fin (n+2)→ℝ)) i:=by
    rw [he1]
    exact hp
  have hProb1:pathProbability p0 v 1=pp:=by
    apply Subtype.ext
    rw [pathProbability_coe p0 v 1 hp1,he1]
  have hVal0:regularizedPathValue b ε hε p0 v 0=referenceFirstWeight n:=by
    rw [regularizedPathValue,hProb0]
    exact selected_balanced_value hn b hG hP ε hε hεa
  have hVal1:regularizedPathValue b ε hε p0 v 1=
      penalizedValue b p (selectedCovariance b ε hε pp):=by
    rw [regularizedPathValue,hProb1]
  rw [hVal0,hVal1] at hb
  have hb':penalizedValue b p (selectedCovariance b ε hε pp)≤ massValueUpperBound n p:=by
    exact hb
  exact (selectedCovariance_isMaxOn b ε hε pp hC).trans hb'

end NegativeVotingMassSemiconcavity
