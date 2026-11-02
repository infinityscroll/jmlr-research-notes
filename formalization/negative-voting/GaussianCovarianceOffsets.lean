import GaussianFanSelectedOffsets
import GaussianCovarianceJointValue

/-! Intrinsic centered Gaussian offsets and the actual mass derivative,
with joint C1 regularity in every symmetric covariance and mass coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingCovarianceOffsets
open NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanSelectedOffsets
  NegativeVotingFanMassValueGradient NegativeVotingFanJointInverse NegativeVotingFanJointMass
  NegativeVotingFanCovarianceValue NegativeVotingFanCovarianceEnvelope
  NegativeVotingPositiveCovariance NegativeVotingCovarianceConcavity
  NegativeVotingLocalCovarianceFactor NegativeVotingAffineBasisLower
variable {m d : ℕ} [NeZero m]

def covarianceOffsets (G : Matrix (Fin m) (Fin m) ℝ) (p : Fin m → ℝ) : centeredGauge (Fin m) :=
  selectedOffsets (covarianceRows G) p

theorem covarianceOffsets_gram (B : Fin m → FSC.Coord d)
    (σ : ℝ) (hσ : 0<σ) (hlower : NegativeVotingCapTail.CenteredSingularLowerBound B σ)
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) :
    covarianceOffsets (Matrix.gram ℝ B) p=selectedOffsets B p := by
  symm
  apply selectedOffsets_eq_of_gram B _ σ hσ hlower _ p hp hs
  intro i j
  exact (congrFun (congrFun (covarianceRows_gram (Matrix.gram ℝ B)
    (Matrix.posSemidef_gram ℝ B)) i) j).symm

def operatorOffsets (b : AffineBasis (Fin m) ℝ (FSC.Coord d)) (p : Fin m → ℝ)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) : centeredGauge (Fin m) :=
  covarianceOffsets (gramVelocity b C) p

/-- All covariance coordinates vary simultaneously. The actual global
selection is identified with a constructed smooth local factor and inverse. -/
theorem operatorOffsets_joint_C1 (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C₀ : SymmetricOperators (FSC.Coord d))
    (hC₀ : (C₀ : FSC.Coord d →L[ℝ] FSC.Coord d)∈pdCone) :
    ContDiffAt ℝ 1 (fun q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) =>
      operatorOffsets b (p+(q.2 : Fin m → ℝ)) q.1) (C₀,0) := by
  obtain ⟨R,B,_,_,_,hB₀,hBC,hGram⟩ := exists_local_smooth_rows (b : Fin m → FSC.Coord d) C₀ hC₀
  let bR := mappedBasis b R
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound bR
  let Q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) → JointCoordinates d (Fin m) :=
    fun q => (B q.1,q.2)
  have hQ₀ : Q (C₀,0)=((bR : Fin m → FSC.Coord d),0) := by
    apply Prod.ext
    · exact hB₀
    · rfl
  have hQ : ContDiffAt ℝ 1 Q (C₀,0) :=
    ((hBC.of_le (by simp)).comp (C₀,0) contDiffAt_fst).prodMk contDiffAt_snd
  have hsel := selectedOffsets_joint_C1 bR σ hσ hlower p hp hs
  have hsel' : ContDiffAt ℝ 1 (fun q : JointCoordinates d (Fin m) =>
      selectedOffsets q.1 (p+(q.2 : Fin m → ℝ))) (Q (C₀,0)) := by
    rw [hQ₀]
    exact hsel
  have hc := hsel'.comp (C₀,0) hQ
  have hnear : ∀ᶠ q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) in 𝓝 (C₀,0),
      ∀ i j,inner ℝ (B q.1 i) (B q.1 j)=inner ℝ (b i) ((q.1 : FSC.Coord d →L[ℝ] FSC.Coord d) (b j)) :=
    (continuous_fst.tendsto (C₀,(0 : centeredGauge (Fin m)))).eventually hGram
  have hlow : ∀ᶠ q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) in 𝓝 (C₀,0),
      NegativeVotingCapTail.CenteredSingularLowerBound (B q.1) (σ/2) := by
    have ht : ContinuousAt (fun q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) =>
        (B q.1,(0 : Fin m → ℝ))) (C₀,0) :=
      (hBC.continuousAt.comp continuousAt_fst).prodMk continuousAt_const
    have he : ∀ᶠ z : NegativeVotingFanScore.Parameters d (Fin m) in 𝓝 (B C₀,0),
        NegativeVotingCapTail.CenteredSingularLowerBound z.1 (σ/2) := by
      rw [show B C₀=(bR : Fin m → FSC.Coord d) from hB₀]
      exact eventually_centeredSingularLowerBound bR 0 σ hσ hlower
    exact ht.eventually he
  have hpos : ∀ᶠ q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) in 𝓝 (C₀,0),
      ∀ i,0<(p+(q.2 : Fin m → ℝ)) i := by
    apply eventually_all.mpr
    intro i
    let Z : (SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m)) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp ((centeredGauge (Fin m)).subtypeL.comp
        (ContinuousLinearMap.snd ℝ _ _))
    have ht : ContinuousAt (fun q => p i+Z q) (C₀,0) := continuousAt_const.add Z.continuous.continuousAt
    exact ht.eventually (Ioi_mem_nhds (by simpa [Z] using hp i))
  apply hc.congr_of_eventuallyEq
  filter_upwards [hnear,hlow,hpos] with q hq hl hpq
  have hg : Matrix.gram ℝ (B q.1)=gramVelocity b (q.1 : FSC.Coord d →L[ℝ] FSC.Coord d) := by
    ext i j
    exact hq i j
  have hz : ∑ i,(q.2 : Fin m → ℝ) i=0 := q.2.property
  have hsq : ∑ i,(p+(q.2 : Fin m → ℝ)) i=1 := by simp [Finset.sum_add_distrib,hs,hz]
  unfold operatorOffsets
  rw [←hg,covarianceOffsets_gram (B q.1) (σ/2) (by positivity) hl _ hpq hsq]
  rfl

/-- The exact mass derivative of the intrinsic covariance functional. -/
theorem hasFDerivAt_operatorValue_mass (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hs : ∑ i,p i=1) (u : centeredGauge (Fin m))
    (hp : ∀ i,0<(p+(u : Fin m → ℝ)) i)
    (C : FSC.Coord d →L[ℝ] FSC.Coord d) (hC : C∈pdCone) :
    HasFDerivAt (fun v : centeredGauge (Fin m) => operatorValue b (p+(v : Fin m → ℝ)) C)
      (massDerivative (operatorOffsets b (p+(u : Fin m → ℝ)) C)) u := by
  obtain ⟨R,hR,_,hRC⟩ := exists_positive_factor C hC
  let bR := mappedBasis b R
  obtain ⟨σ,hσ,hlower⟩ := exists_centeredSingularLowerBound bR
  have hg : Matrix.gram ℝ bR=gramVelocity b C := factor_gram b C R hR hRC
  have hd := selected_mass_derivative bR σ hσ hlower p u hp hs
  have hz : ∑ i,(u : Fin m → ℝ) i=0 := u.property
  have hsu : ∑ i,(p+(u : Fin m → ℝ)) i=1 := by simp [Finset.sum_add_distrib,hs,hz]
  simpa only [operatorValue,operatorOffsets,←hg,covarianceValue_gram,
    covarianceOffsets_gram bR σ hσ hlower _ hp hsu] using hd

/-- The offset pairing is a smooth map into the actual continuous dual. -/
theorem contDiff_massDerivative :
    ContDiff ℝ ⊤ (massDerivative : (Fin m → ℝ) → (centeredGauge (Fin m) →L[ℝ] ℝ)) := by
  letI : IsBoundedSMul ℝ (centeredGauge (Fin m) →L[ℝ] ℝ) :=
    .of_norm_smul_le (fun c L => ContinuousLinearMap.opNorm_smul_le c L)
  unfold massDerivative
  apply ContDiff.neg
  apply ContDiff.sum
  intro i _
  exact (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).contDiff.smul contDiff_const

/-- The intrinsic mass gradient is C1 jointly with covariance, as a linear
functional, rather than merely after evaluation in a chosen direction. -/
theorem operatorMassGradient_joint_C1 (b : AffineBasis (Fin m) ℝ (FSC.Coord d))
    (p : Fin m → ℝ) (hp : ∀ i,0<p i) (hs : ∑ i,p i=1)
    (C₀ : SymmetricOperators (FSC.Coord d))
    (hC₀ : (C₀ : FSC.Coord d →L[ℝ] FSC.Coord d)∈pdCone) :
    ContDiffAt ℝ 1 (fun q : SymmetricOperators (FSC.Coord d)×centeredGauge (Fin m) =>
      massDerivative (operatorOffsets b (p+(q.2 : Fin m → ℝ)) q.1 : Fin m → ℝ)) (C₀,0) := by
  have hc := operatorOffsets_joint_C1 b p hp hs C₀ hC₀
  have hr := (centeredGauge (Fin m)).subtypeL.contDiff.contDiffAt.comp (C₀,0) hc
  exact (contDiff_massDerivative.of_le (by simp)).contDiffAt.comp (C₀,0) hr

end NegativeVotingCovarianceOffsets
