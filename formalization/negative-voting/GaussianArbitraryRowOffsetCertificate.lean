import GaussianBoundedOffsetLimit
import GaussianPSDAffineApproximation
import GaussianCovarianceRealization
import GaussianCenteredParsevalBasis

/-! The actual balanced optimal-dual offset certificate for arbitrary
rectangular centered rows, including rank loss and duplicate sites. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingArbitraryOffsetCertificate
open NegativeVotingBoundedOffsetCertificate NegativeVotingBoundedOffsetLimit
open NegativeVotingPSDAffineApproximation NegativeVotingFan NegativeVotingFanInverse
open NegativeVotingFanValue NegativeVotingBalancedReference NegativeVotingRegularCovarianceDeficit
open NegativeVotingOptimizerConstants NegativeVotingCovarianceRealization
open NegativeVotingCenteredParseval NegativeVotingPositiveCovariance
open NegativeVotingFanCovarianceLaw NegativeVotingFanCovarianceValue
variable {n e:ℕ}

/-- The offset is constructed from actual Gaussian dual minimizers. No rank,
distinctness, approximation, selected inverse, or offset-vector premise remains. -/
theorem exists_balanced_optimal_dual_with_energy_bound (hn:numericThreshold≤ n+2)
    (B:Fin (n+2)→FSC.Coord e) (hc:(∑i,B i)=0)
    (hB:∀i,‖B i‖≤4*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)):
    ∃h:centeredGauge (Fin (n+2)),
      potential B (uniformMass n) h=optimizedValue B (uniformMass n)∧
      (∑i,((h:Fin (n+2)→ℝ) i)^2)≤
        4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2*regularCovarianceDeficit n B:=by
  classical
  obtain ⟨b,hcenter,hG,hP⟩:=exists_centered_parseval_affineBasis (n+2) (by omega)
  let C:=rowCovariance b B
  obtain ⟨S,hS,hSq⟩:=exists_psd_factor C (rowCovariance_psd b B)
  let B0:Fin (n+2)→FSC.Coord (n+2-1):=fun i=>S (b i)
  have hGram:Matrix.gram ℝ B0=Matrix.gram ℝ B:=by
    ext i j
    change inner ℝ (S (b i)) (S (b j))=inner ℝ (B i) (B j)
    calc
      _=inner ℝ (b i) (S (S (b j))):=hS.1 (b i) (S (b j))
      _=inner ℝ (b i) (C (b j)):=by
        exact congrArg (inner ℝ (b i)) (congrArg (fun T:FSC.Coord (n+2-1)→L[ℝ]FSC.Coord (n+2-1)=>T (b j)) hSq)
      _=inner ℝ (reconstruction b B (b i)) (reconstruction b B (b j)):=
        ContinuousLinearMap.adjoint_inner_right (reconstruction b B) (b i) (reconstruction b B (b j))
      _=inner ℝ (B i) (B j):=by rw [reconstruction_row b B hG hc i,reconstruction_row b B hG hc j]
  have hnorm (i:Fin (n+2)):‖S (b i)‖=‖B i‖:=by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hh:=congrFun (congrFun hGram i) i
    simpa only [Matrix.gram_apply,real_inner_self_eq_norm_sq] using hh
  have hu:∀i,‖b i‖≤1:=by
    intro i
    have hh:=hG i i
    simp only [ite_true,real_inner_self_eq_norm_sq] at hh
    have hp:0≤1/((n+2:ℕ):ℝ):=by positivity
    nlinarith [norm_nonneg (b i)]
  let R:ℝ:=4*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)
  have hR:0< R:=by
    dsimp [R]
    have hl:0≤ Real.log ((n:ℝ)+2):=Real.log_nonneg (by have hh:0≤(n:ℝ):=Nat.cast_nonneg n;linarith)
    positivity
  have hrow:∀i,‖S (b i)‖≤ R:=by intro i;rw [hnorm i];exact hB i
  obtain ⟨a,hac,hacap,hat⟩:=exists_bounded_affine_approximation b hcenter hu S hS R hR hrow
  have hcap:∀k i,‖a k i‖≤8*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2):=by
    intro k i
    have hh:=hacap k i
    dsimp [R] at hh
    convert hh using 1 <;> ring
  obtain ⟨h,hpot,henergy⟩:=exists_limiting_balanced_dual hn B0 a hac hcap hat
  have hvalue:optimizedValue B0 (uniformMass n)=optimizedValue B (uniformMass n):=
    optimizedValue_eq_of_gram B0 B (fun i j=>congrFun (congrFun hGram i) j) (uniformMass n)
  have hpotential:potential B0 (uniformMass n) h=potential B (uniformMass n) h:=
    potential_eq_of_gram B0 B (fun i j=>congrFun (congrFun hGram i) j) (uniformMass n) h
  have hdef:regularCovarianceDeficit n B0=regularCovarianceDeficit n B:=by
    unfold regularCovarianceDeficit
    rw [rowEnergy_eq_of_gram B0 B hGram,hvalue]
  refine ⟨h,?_,?_⟩
  · rw [hpotential,hvalue] at hpot
    exact hpot
  · simpa only [hdef] using henergy

end NegativeVotingArbitraryOffsetCertificate
