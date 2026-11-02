import GaussianFanJointValueC2
import GaussianLocalCovarianceFactor
import GaussianCovarianceConcavity

/-! Genuine joint C2 regularity in all symmetric covariance entries and all
centered mass increments, obtained from an actual smooth factor and fan dual. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology BigOperators RealInnerProductSpace
namespace NegativeVotingCovarianceJointValueC2
open NegativeVotingLocalCovarianceFactor NegativeVotingPositiveCovariance
  NegativeVotingCovarianceConcavity NegativeVotingFanCovarianceValue
  NegativeVotingFanJointValueC2 NegativeVotingFanInverse NegativeVotingFan
  NegativeVotingAffineBasisLower NegativeVotingFanJointInverse
variable {m d : ℕ} [NeZero m]

theorem operatorValue_joint_C2
    (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m→ℝ)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C₀ : SymmetricOperators (FSC.Coord d))
    (hC₀ : (C₀ : FSC.Coord d→L[ℝ]FSC.Coord d)∈pdCone) :
    ContDiffAt ℝ 2
      (fun q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) =>
        operatorValue b (p+(q.2 : Fin m→ℝ)) (q.1 : FSC.Coord d→L[ℝ]FSC.Coord d)) (C₀,0) := by
  obtain ⟨R,B,hR,hRi,hRR,hB₀,hBC,hGram⟩:=exists_local_smooth_rows (b : Fin m→FSC.Coord d) C₀ hC₀
  let bR:=mappedBasis b R
  obtain ⟨σ,hσ,hlower⟩:=exists_centeredSingularLowerBound bR
  have hV:=jointValue_C2 (bR : Fin m→FSC.Coord d) σ hσ hlower p hp hs
  let Q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m)→JointCoordinates d (Fin m):=
    fun q=>(B q.1,q.2)
  have hQ₀ : Q (C₀,0)=((bR : Fin m→FSC.Coord d),0) := by
    apply Prod.ext
    · exact hB₀
    · rfl
  have hQ : ContDiffAt ℝ 2 Q (C₀,0) :=
    ((hBC.of_le (by simp)).comp (C₀,0) contDiffAt_fst).prodMk contDiffAt_snd
  have hcomp : ContDiffAt ℝ 2 (fun q => NegativeVotingFanValue.optimizedValue
      (Q q).1 (p+((Q q).2 : Fin m→ℝ))) (C₀,0) := by
    have hV' : ContDiffAt ℝ 2 (fun q : JointCoordinates d (Fin m)=>
        NegativeVotingFanValue.optimizedValue q.1 (p+(q.2 : Fin m→ℝ))) (Q (C₀,0)) := by
      rw [hQ₀]
      exact hV
    exact hV'.comp (C₀,0) hQ
  have hnear : ∀ᶠ q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) in 𝓝 (C₀,0),
      ∀ i j,inner ℝ (B q.1 i) (B q.1 j)=inner ℝ (b i) ((q.1 : FSC.Coord d→L[ℝ]FSC.Coord d) (b j)) :=
    (continuous_fst.tendsto (C₀,(0 : centeredGauge (Fin m)))).eventually hGram
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnear] with q hq
  have hg : Matrix.gram ℝ (B q.1)=gramVelocity b (q.1 : FSC.Coord d→L[ℝ]FSC.Coord d) := by
    ext i j
    exact hq i j
  unfold operatorValue
  rw [←hg,covarianceValue_gram]

end NegativeVotingCovarianceJointValueC2
