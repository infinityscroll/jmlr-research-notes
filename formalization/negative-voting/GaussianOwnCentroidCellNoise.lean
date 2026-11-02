import GaussianOwnCentroidPrimalGap
import GaussianExteriorNoiseAssembly
import GaussianNearBalancedHighTailComparison

/-! Exact spectral accounting for the literal own-centroid cell rule. The
infinite signed tail and the actual second-chaos tensor are identified, so
subsequent inequalities refer to the concrete Gaussian noise stability. -/
noncomputable section
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingOwnCentroidCellNoise
open NegativeVoting NegativeVotingAffine NegativeVotingModern NegativeVotingFan
  NegativeVotingFanTestedCells NegativeVotingFanQuadraticMoments NegativeVotingCellOUContinuity
  NegativeVotingOwnCentroidLocalReplacement NegativeVotingOwnCentroidSpectralReplacement
  NegativeVotingOwnCentroidQuantitativeReplacement NegativeVotingOwnCentroidPrimalGap
  NegativeVotingExteriorNoiseAssembly NegativeVotingNearBalancedHighTailComparison
  NegativeVotingFractionalMass NegativeVotingBalancedReference NegativeVotingRegularScoreLaw
  NegativeVotingReferenceSecondEnergy NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumLocalization
  NegativeVotingSignedHighTailComparison NegativeVotingRegularReferenceNormalization
  NegativeVotingQuadraticMomentPadding NegativeVotingExteriorActualComparison
variable {d n : ℕ}

def cellRule {ι : Type*} (B : ι→FSC.Coord d) (h : ι→ℝ) : (Fin d→ℝ)→ι→ℝ :=
  fun x i=>cellWeight B h i x

lemma cellRule_weights_ae {ι : Type*} [Fintype ι] [Nonempty ι]
    (B : ι→FSC.Coord d) (hB : Function.Injective B) (h : ι→ℝ) :
    cellRule B h=ᵐ[γFin d]fun x=>weights B h (WithLp.toLp 2 x) := by
  have hm : MeasurePreserving (WithLp.toLp 2) (γFin d) (stdGaussian (FSC.Coord d)) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have he:∀i,∀ᵐx ∂γFin d,weights B h (WithLp.toLp 2 x) i=cellRule B h x i:=by
    intro i
    exact hm.quasiMeasurePreserving.ae (weights_eq_winningCell_indicator_ae B hB h i)
  filter_upwards [ae_all_iff.mpr he] with x hx
  funext i
  exact (hx i).symm

lemma cellRule_chaosEnergy_two {ι : Type*} [Fintype ι] [Nonempty ι]
    (B : ι→FSC.Coord d) (hB : Function.Injective B) (h : ι→ℝ) :
    chaosEnergy (cellRule B h) 2=secondEnergy B h := by
  rw [secondEnergy_eq_actual_chaos B hB h]
  exact gaussian_chaosEnergy_congr_ae _ _ (cellRule_weights_ae B hB h) 2

lemma cellRule_scaled_regular_ae (R : Fin (n+2)→FSC.Coord d)
    (hR : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (α : ℝ) (hα : 0<α) :
    cellRule (α•R) 0=ᵐ[γFin d]regularAssignment (coordinateRows R) := by
  have he:∀i,∀ᵐx ∂γFin d,cellRule (α•R) 0 x i=regularAssignment (coordinateRows R) x i:=by
    intro i
    have hs:cellWeight (α•R) 0 i=cellWeight R 0 i:=by
      funext x
      unfold cellWeight
      rw [winningCell_scaled_zero R α hα]
    filter_upwards [(regularAssignment_eq_cellWeight_ae n R hR i).symm] with x hx
    change cellWeight (α•R) 0 i x=_
    rw [hs]
    exact hx
  filter_upwards [ae_all_iff.mpr he] with x hx
  exact funext hx

/-- Exact cell-rule noise difference against any actual regular reference. -/
theorem cell_noise_difference_eq (hn : 0<n)
    (Ref : Fin (n+2)→Fin d→ℝ) (hRef : RegularSimplexGram Ref)
    (R : Fin (n+2)→FSC.Coord d)
    (hR : ∀i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (α : ℝ) (hα : 0<α)
    (B : Fin (n+2)→FSC.Coord d) (hB : Function.Injective B) (h : Fin (n+2)→ℝ)
    (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    gaussianNoiseStability (-r) (cellRule B h)-gaussianNoiseStability (-r) (regularAssignment Ref)=
      massDeficit n (cellRule B h)+r*(referenceFirstWeight n-assignmentFirstEnergy (cellRule B h))+
        r^2*(secondEnergy B h-referenceSecondWeight n)+
        (cellTailEnergy (-r) 3 (B,h)-cellTailEnergy (-r) 3 (α•R,0)) := by
  let U:=coordinateRows R
  have hU:RegularSimplexGram U:=coordinateRows_gram R hR
  have hg:∀i,AEMeasurable (fun x=>cellRule B h x i) (standardGaussian (Fin d)):=
    fun i=>(cellWeight_measurable B h i).aemeasurable
  have hgs:∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (cellRule B h x):=
    cellWeight_simplex_ae B hB h
  have hUM:∀i,AEMeasurable (fun x=>regularAssignment U x i) (standardGaussian (Fin d)):=
    fun i=>(regularAssignment_measurable U i).aemeasurable
  have hUS:=ae_of_all (standardGaussian (Fin d)) (regularAssignment_simplex U)
  have he:=negative_noise_pairing_expansion r hr hr1 (regularAssignment U) hUM hUS
  have hmass:(∑i,(assignmentMass (regularAssignment U) i)^2)=1/((n:ℝ)+2):=by
    simpa only [chaosEnergy_zero,assignmentMass] using regular_chaosEnergy_zero n U hU
  have hfirst:assignmentFirstEnergy (regularAssignment U)=referenceFirstWeight n:=by
    simpa only [chaosEnergy_one,assignmentFirstEnergy] using regular_chaosEnergy_one_eq_reference n hn U hU
  rw [hmass,hfirst,regular_chaosEnergy_two_eq_reference n hn U hU] at he
  have htail:(∑i,energyPairing (-r) 3 (fun x=>regularAssignment U x i))=
      cellTailEnergy (-r) 3 (α•R,0):=by
    apply Finset.sum_congr rfl
    intro i _
    exact energyPairing_congr_ae r hr hr1 3
      ((cellRule_scaled_regular_ae R hR α hα).symm.mono fun x hx=>congrFun hx i)
  rw [htail] at he
  have hnoise:gaussianNoiseStability (-r) (regularAssignment Ref)=
      gaussianNoiseStability (-r) (regularAssignment U):=by
    rw [regularAssignment_noise_eq_canonical n Ref hRef,regularAssignment_noise_eq_canonical n U hU]
  rw [hnoise,he,negative_noise_pairing_expansion r hr hr1 _ hg hgs,
    cellRule_chaosEnergy_two B hB h,massDeficit_eq n _ hg hgs]
  change (∑i,assignmentMass (cellRule B h) i^2)-r*assignmentFirstEnergy (cellRule B h)+
    r^2*secondEnergy B h+(∑i,energyPairing (-r) 3 (cellWeight B h i))-_=_
  unfold cellTailEnergy
  ring

end NegativeVotingOwnCentroidCellNoise
