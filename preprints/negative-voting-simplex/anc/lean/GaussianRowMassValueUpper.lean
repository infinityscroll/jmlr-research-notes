import GaussianUniformMassBound
import GaussianCovarianceZeroFloorBound
import GaussianCovarianceRealization

/-! The actual row-level mass upper bound, including rectangular and
singular row systems. No row-energy normalization is required. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingRowMassValueUpper
open NegativeVotingMassSemiconcavity NegativeVotingCenteredParseval
  NegativeVotingOptimizerConstants NegativeVotingCovarianceZeroFloorBound
  NegativeVotingCovarianceRealization NegativeVotingCentroidOptimization
  NegativeVotingAssignmentDuality
variable {n e:ℕ}

theorem rowObjective_bound_in_mass_window (hm:numericThreshold≤ n+2)
    (B:Fin (n+2)→FSC.Coord e) (hB:(∑i,B i)=0) (p:Fin (n+2)→ℝ)
    (hs:∑i,p i=1)
    (hwindow:∀i,p i∈Icc ((1/100:ℝ)/((n:ℝ)+2)) (2/((n:ℝ)+2))):
    rowObjective B p≤ massValueUpperBound n p:=by
  obtain ⟨b,hcenter,hG,hP⟩:=exists_centered_parseval_affineBasis (n+2) (by omega)
  have hG':∀i j,inner ℝ (b i) (b j)=(if i=j then 1 else 0)-1/((n:ℝ)+2):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hG
  have hdim:2≤ n+2-1:=by
    have hh:3≤ n+2:=(numericThreshold_spec (n+2) hm).1
    omega
  obtain ⟨δ,hδ,hbound⟩:=uniform_positive_floor_mass_bound b hG' hP hdim hm
  have hbox:∀i,p i∈Icc (actualMassLower ((n+2:ℕ):ℝ)) (2/((n+2:ℕ):ℝ)):=by
    simpa only [actualMassLower,Nat.cast_add,Nat.cast_ofNat,div_div] using hwindow
  have hlo:0< actualMassLower ((n+2:ℕ):ℝ):=by unfold actualMassLower;positivity
  have hmass:∀i,0< p i:=fun i=>hlo.trans_le (hbox i).1
  have hh:=covariance_bound_of_small_floors b p hmass hs (massValueUpperBound n p) δ hδ
    (fun ε hε hεδ C hC _=>hbound ε hε hεδ p hs hbox C hC)
    (rowCovariance b B) (rowCovariance_psd b B)
  rwa [rowCovariance_objective b hG hP B hB p] at hh

/-- One alphabet threshold precedes every ambient dimension and every
centered row system, with no full-rank or distinctness hypothesis. -/
theorem eventually_uniform_rowObjective_bound:
    ∀ᶠn:ℕ in atTop,∀(e:ℕ)(B:Fin (n+2)→FSC.Coord e)(hB:(∑i,B i)=0)
      (p:Fin (n+2)→ℝ)(hs:∑i,p i=1),
      (∀i,p i∈Icc ((1/100:ℝ)/((n:ℝ)+2)) (2/((n:ℝ)+2)))→
      rowObjective B p≤ massValueUpperBound n p:=by
  filter_upwards [eventually_ge_atTop numericThreshold] with n hn
  intro e B hB p hs hwindow
  exact rowObjective_bound_in_mass_window (by omega) B hB p hs hwindow

end NegativeVotingRowMassValueUpper
