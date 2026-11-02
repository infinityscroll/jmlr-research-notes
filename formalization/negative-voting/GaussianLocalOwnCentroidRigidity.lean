import GaussianLocalOwnCentroidGeometry
import GaussianOwnCentroidCellNoise
import GaussianNearBalancedEnergyMixedBound
import GaussianNearBalancedTailUniform
import GaussianNearBalancedNoiseAbsorption
import GaussianLocalNoiseAbsorption

/-! Actual local own-centroid noise assembly. The sole analytic input retained
is the explicitly named eventual balanced second-chaos loss. All mass-changing
fans, replacement, signed tails, geometry and scalar absorption are derived. -/
noncomputable section
set_option maxHeartbeats 7500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set Filter
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingLocalOwnCentroidRigidity
open NegativeVoting NegativeVotingAffine NegativeVotingModern NegativeVotingFan
  NegativeVotingFanInverse NegativeVotingFanSelectedOffsets NegativeVotingFanQuadraticMoments
  NegativeVotingFanScore NegativeVotingFanTestedCells NegativeVotingQuadraticMomentPadding
  NegativeVotingCellOUContinuity NegativeVotingHypercontractivity NegativeVotingStructuredResidualInputs
  NegativeVotingOwnCentroidQuantitativeReplacement NegativeVotingOwnCentroidPrimalGap
  NegativeVotingOwnCentroidCellNoise NegativeVotingLocalOwnCentroidGeometry
  NegativeVotingAssignmentCoordinateBridge NegativeVotingAssignmentDuality
  NegativeVotingCentroidOptimization NegativeVotingFractionalMass
  NegativeVotingBalancedReference NegativeVotingRegularCovarianceDeficit NegativeVotingProcrustes
  NegativeVotingGlobalCovarianceDeficit NegativeVotingCompetitiveTightMassWindow
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumLocalization
  NegativeVotingNearBalancedEnergyComparison NegativeVotingNearBalancedEnergyMixedBound
  NegativeVotingNearBalancedTailUniform NegativeVotingNearBalancedTailLogBound
  NegativeVotingNearBalancedHighTailComparison NegativeVotingNearBalancedNoiseAbsorption
  NegativeVotingLocalNoiseAbsorption NegativeVotingNearRegularBalancedGeometry
  NegativeVotingRegularReferenceNormalization NegativeVotingFacetDegree NegativeVotingCapTail
  NegativeVotingNearBalancedActualCap NegativeVotingStructuredAmplitudeBound
  NegativeVotingNearBalancedStructuredCap NegativeVotingOptimizerConstants
  NegativeVotingBoundedOffsetCertificate NegativeVotingOwnCentroidLocalReplacement

/-- This displayed input is the remaining balanced local second-chaos theorem;
it contains actual selected offsets and the actual covariance deficit. -/
def EventualLocalBalancedSecondLoss (C : ℝ) (k : ℕ) : Prop :=
  ∀ᶠ n:ℕ in atTop,∀ d:ℕ,n+1 ≤ d →∀B:Fin (n+2)→FSC.Coord d,
    (∑i,B i)=0 → 0<regularCovarianceDeficit n B → regularOrbitDistance n B ≤ 1/((n:ℝ)+2) →
    referenceSecondWeight n-secondEnergy B (selectedOffsets B (uniformMass n)) ≤
      C*(1+Real.log ((n:ℝ)+2))^k*Real.sqrt ((n:ℝ)+2)*regularCovarianceDeficit n B

def localCapConstant : ℝ:=actualCapConstant 8192 (1/2) 10
def localMassConstant : ℝ:=massAdjointBase (1/2) 10
def localTailConstant : ℝ:=tailLogConstant+2*localCapConstant

lemma local_constants_nonneg : 0≤localCapConstant ∧ 0≤localMassConstant ∧ 0≤localTailConstant := by
  have hc:0≤localCapConstant:=by
    exact mul_nonneg (capConstant_nonneg 8192 (1/2) (by norm_num))
      (amplitude_bases_nonneg 8192 4 (4*8192) (1/2) 10 (by norm_num) (by norm_num) (by norm_num)).2.2.2
  have hm:0≤localMassConstant:=(mass_bases_nonneg (1/2) 10 (by norm_num)).2.2.2.2.2
  refine ⟨hc,hm,?_⟩
  dsimp [localTailConstant]
  positivity [base_pos.2.2.2.2.2.2]

/-- Conditional local rigidity for measurable representatives, with the entire
voting interval and an alphabet threshold preceding every ambient dimension. -/
theorem eventually_local_rigidity_measurable_of_balanced_loss
    (C : ℝ) (k : ℕ) (hC : 0≤C) (hbalanced : EventualLocalBalancedSecondLoss C k) :
    ∀ᶠ n:ℕ in atTop,∀ d:ℕ,n+1 ≤ d →
    ∀Ref:Fin (n+2)→Fin d→ℝ,RegularSimplexGram Ref →
    ∀f:(Fin d→ℝ)→Fin (n+2)→ℝ,
      (∀i,Measurable (fun x=>f x i)) →
      (∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) →
    ∀r:ℝ,0<r → r≤1/((n:ℝ)+1) →
      gaussianNoiseStability (-r) f≤gaussianNoiseStability (-r) (regularAssignment Ref) →
      regularOrbitDistance n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f))≤1/((n:ℝ)+2) →
      regularCovarianceDeficit n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f))=0 := by
  obtain ⟨Nrep,hrepN⟩:=exists_dimension_uniform_voting_replacement 8192 (1/2) 10 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Nmass,hmassN⟩:=exists_dimension_uniform_mass_energy_mixed_log
  have hP:0≤96/globalRadius:=by positivity [globalRadius_bounds.1]
  have hM:=local_constants_nonneg.2.1
  have hT:=local_constants_nonneg.2.2
  have hH:0≤4*certificateQuadraticConstant:=by
    have hh:=certificateQuadraticConstant_ge_thirtytwo
    positivity
  have hsmall:=eventually_uniform_local_coefficients (96/globalRadius) localMassConstant C
    localTailConstant (4*certificateQuadraticConstant) k hP hM hC hT hH
  filter_upwards [hbalanced,eventually_local_own_centroid_data,
    eventually_reference_near_balanced_signed_tail_log_le,hsmall,
    eventually_uniform_competitive_half_mass_window,
    eventually_ge_atTop (Nrep+Nmass+numericThreshold+2)] with n hbal hdata htailN hsmallN hwindow hn
  intro d hd Ref hRef f hf hp r hr hrange hcomp hlocal
  have hn1:1≤n:=by omega
  have hn0:0<n:=by omega
  have hfAE:∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)):=fun i=>(hf i).aemeasurable
  let B:=centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)
  let Rdef:=regularCovarianceDeficit n B
  let Z:=massDeficit n f
  let m:ℝ:=(n:ℝ)+2
  let L:ℝ:=1+Real.log m
  have hfeas:=coordinateRule_feasible (LinearIsometryEquiv.refl ℝ _) f hfAE hp
  have hcenter:(∑i,B i)=0:=centroidRows_sum_zero _ _ hfeas
  have hR0:0≤Rdef:=regularCovarianceDeficit_nonneg hn0 B hcenter
  by_contra hne
  have hR:0<Rdef:=lt_of_le_of_ne hR0 (Ne.symm hne)
  have hw:=hwindow (Fin d) Ref hRef f hfAE hp r hr.le hrange hcomp
  obtain ⟨q⟩:=hdata d hd f hfAE hp hR hlocal hw
  let b:Fin (n+2)→FSC.Coord d:=referenceScale n•q.R+q.D
  let p:Fin (n+2)→ℝ:=(fun _=>m⁻¹)+(q.v:Fin (n+2)→ℝ)
  let h:Fin (n+2)→ℝ:=selectedOffsets b p
  let g:=cellRule b h
  let F:ℝ:=∑i,‖q.D i‖^2
  let P:ℝ:=(96/globalRadius)*m*L
  let M:ℝ:=localMassConstant*L^13
  let BC:ℝ:=C*L^k*Real.sqrt m
  let TC:ℝ:=localTailConstant*L^10
  let HC:ℝ:=(4*certificateQuadraticConstant)*L^2
  have hB:b=B:=q.rows
  have hα:0<referenceScale n:=referenceScale_pos n
  have hm:0 < m:=by dsimp [m];positivity
  have hL:0≤L:=by dsimp [L,m];positivity [Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])]
  have hF:0≤F:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hZ:0≤Z:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hGreg:∀i j,inner ℝ (q.R i) (q.R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using q.regular
  have hgeom:=segment_geometry (show 3≤n+2 by omega) q.R q.D hGreg (referenceScale n) hα q.rowSmall 1 ⟨by norm_num,le_rfl⟩
  simp only [one_smul] at hgeom
  have hinj:Function.Injective b:=by
    intro i j heq
    by_contra hij
    exact centered_singular_rows_ne b (referenceScale n/2) (by positivity) hgeom.1 i j hij heq
  have hpEq:p=assignmentMass f:=q.masses.symm
  have hppos:∀i,0<p i:=by
    intro i
    rw [hpEq]
    exact lt_of_lt_of_le (by positivity) (hw i).1
  have hpsum:∑i,p i=1:=by rw [hpEq];exact assignmentMass_sum f hfAE hp
  have hgmass:assignmentMass g=assignmentMass f:=by
    funext i
    change (∫x,cellWeight b h i x ∂γFin d)=assignmentMass f i
    rw [cellWeight_integral_eq_mass b hinj h i]
    change mass b (selectedOffsets b p) i=_
    rw [selectedOffsets_mass b hinj p hppos hpsum,hpEq]
  have hg:∀i,AEMeasurable (fun x=>g x i) (standardGaussian (Fin d)):=
    fun i=>(cellWeight_measurable b h i).aemeasurable
  have hgp:∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (g x):=cellWeight_simplex_ae b hinj h
  have hmoment i j:momentMatrix f i j=(b i).ofLp j:=by
    rw [hB]
    exact (coordinate_centroid_apply f hfAE hp i j).symm
  have hfmass i:(∫x,f x i ∂γFin d)=m⁻¹+(q.v:Fin (n+2)→ℝ) i:=by
    change assignmentMass f i=_
    exact congrFun q.masses i
  have hrep:=hrepN n (by omega) q.meanLower d q.R q.D q.regular q.rowSmall q.scaleLower q.scaleUpper
    q.v q.massBound q.size r hr hrange f hf hp hmoment hfmass
  have hprimal:=own_centroid_first_gap_lower (by omega) f g hfAE hp hg hgp hgmass
    (fun i=>(hw i).2.trans (by
      have hm0:0<(n:ℝ)+2:=by positivity
      apply (div_le_div_iff₀ (by positivity) hm0).mpr
      nlinarith))
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn0
  have hr1:r<1:=hrange.trans_lt ((div_lt_one (by positivity : 0<(n:ℝ)+1)).mpr (by linarith))
  have hnoise:=cell_noise_difference_eq hn0 Ref hRef q.R q.regular (referenceScale n) hα b hinj h r hr hr1
  have hdefmass:massDeficit n g=Z:=by unfold massDeficit;rw [hgmass];rfl
  rw [hdefmass] at hnoise
  have hbal':referenceSecondWeight n-secondEnergy b (selectedOffsets b (uniformMass n))≤BC*Rdef:=by
    rw [hB]
    exact hbal d hd B hcenter hR hlocal
  have hmix:=hmassN n (by omega) d q.R q.D hGreg (referenceScale n) (1/2) 10 hα
    (by norm_num) (by norm_num) q.rowSmall (by simpa only [Nat.cast_add,Nat.cast_ofNat] using q.scaleLower)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using q.scaleUpper) q.v
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using q.massBound)
  simp only [Nat.cast_add,Nat.cast_ofNat] at hmix
  rw [q.massEnergy] at hmix
  have hum : uniformMass n=(fun _ : Fin (n+2)=>((n:ℝ)+2)⁻¹) := by
    funext i
    simp [NegativeVotingBalancedReference.uniformMass,one_div]
  have hmix':|secondEnergy b h-secondEnergy b (selectedOffsets b (uniformMass n))|≤Real.sqrt (M*(F+Z)*Z):=by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt (by dsimp [M];positivity),hum]
    simpa only [b,h,p,M,F,Z,localMassConstant,m,L,uniformMass,Nat.cast_add,Nat.cast_ofNat,one_div] using hmix
  have he2:referenceSecondWeight n-secondEnergy b h≤BC*Rdef+Real.sqrt (M*(F+Z)*Z):=by
    have hh:=neg_le_of_abs_le hmix'
    linarith
  have hdim:2≤Module.finrank ℝ (FSC.Coord d):=by simpa using (show 2≤d by omega)
  have htail:=htailN d q.R q.D hGreg hdim q.rowSmall q.v
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using q.massBound) r hr hrange
  simp only [Nat.cast_add,Nat.cast_ofNat] at htail
  have hzero:(selectedOffsets (referenceScale n•q.R) (fun _=>((n:ℝ)+2)⁻¹):Fin (n+2)→ℝ)=0:=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using selected_regular_scaled_zero q.R hGreg (referenceScale n) hα
  rw [hzero,q.massEnergy] at htail
  have htail':|cellTailEnergy (-r) 3 (b,h)-cellTailEnergy (-r) 3 (referenceScale n•q.R,0)|≤
      tailLogConstant*L^10*r^3*(F+Z):=by
    simpa only [b,h,p,m,L,F,Z] using htail
  have hsmall:=hsmallN r hr.le hrange
  change r*HC≤1/2 ∧ r*BC≤1/8 ∧ r^2*Real.sqrt M≤1/16 ∧
    4*r^3*M*P≤1/8 ∧ TC*r^2*P≤1/8 ∧ TC*r^3≤1/16 at hsmall
  let U:ℝ:=∑i,∫x,(gaussianAverage (Real.sqrt r) (oddHighModes (fun z=>f z i-g z i)) x)^2 ∂γFin d
  have hU:0≤U:=Finset.sum_nonneg fun i _=>integral_nonneg fun x=>sq_nonneg _
  change r*centroidResidual f g+_/2-2*localCapConstant*L^10*r^3*(F+(∑i,((q.v:Fin (n+2)→ℝ) i)^2))≤
    gaussianNoiseStability (-r) f-gaussianNoiseStability (-r) g at hrep
  rw [q.massEnergy] at hrep
  change r*centroidResidual f g+U/2-2*localCapConstant*L^10*r^3*(F+Z)≤
    gaussianNoiseStability (-r) f-gaussianNoiseStability (-r) g at hrep
  change gaussianNoiseStability (-r) g-gaussianNoiseStability (-r) (regularAssignment Ref)=
    Z+r*(referenceFirstWeight n-assignmentFirstEnergy g)+r^2*(secondEnergy b h-referenceSecondWeight n)+
    (cellTailEnergy (-r) 3 (b,h)-cellTailEnergy (-r) 3 (referenceScale n•q.R,0)) at hnoise
  change centroidResidual f g+referenceFirstWeight n-assignmentFirstEnergy g≥Rdef-HC*Z at hprimal
  have hpR:=mul_le_mul_of_nonneg_left hprimal hr.le
  have hHZ:=mul_le_mul_of_nonneg_right hsmall.1 hZ
  have he2r:=mul_le_mul_of_nonneg_left he2 (sq_nonneg r)
  have htlo:=neg_le_of_abs_le htail'
  have hgap:r*Rdef+Z/2-r^2*BC*Rdef-r^2*Real.sqrt (M*(F+Z)*Z)-TC*r^3*(F+Z)≤
      gaussianNoiseStability (-r) f-gaussianNoiseStability (-r) (regularAssignment Ref):=by
    dsimp only [TC,localTailConstant]
    nlinarith only [hrep,hU,hnoise,hpR,hHZ,he2r,htlo]
  have hout:=local_noise_absorption r Rdef F Z P M BC TC
    (gaussianNoiseStability (-r) f-gaussianNoiseStability (-r) (regularAssignment Ref))
    hr.le hR.le hF hZ (by dsimp [M];positivity) (by dsimp [TC];positivity)
    q.rowPaid hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2.1 hsmall.2.2.2.2.1 hsmall.2.2.2.2.2 hgap
  have hposmul:=mul_pos hr hR
  nlinarith only [hout,hcomp,hposmul,hZ]

lemma actual_centroidRows_congr_ae {d n:ℕ}
    (f g:(Fin d→ℝ)→Fin (n+2)→ℝ)
    (hfg:f=ᵐ[standardGaussian (Fin d)]g) :
    centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)=
      centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) g) := by
  have hm:=coordinate_map_measurePreserving (LinearIsometryEquiv.refl ℝ (FSC.Coord d))
  have he:=hm.quasiMeasurePreserving.ae_eq_comp hfg
  funext i
  unfold centroidRows NegativeVotingMassCentroid.gaussianCentroid
  apply integral_congr_ae
  filter_upwards [he] with x hx
  exact congrArg (fun z:Fin (n+2)→ℝ=>z i • x) hx

/-- Completed-measurable fractional local rigidity. This is conditional only
on the named actual balanced E2 input; no measurable-representative or
mass-changing fan premise remains in the final quantifiers. -/
theorem eventually_local_rigidity_of_balanced_loss
    (C : ℝ) (k : ℕ) (hC : 0≤C) (hbalanced : EventualLocalBalancedSecondLoss C k) :
    ∀ᶠ n:ℕ in atTop,∀ d:ℕ,n+1 ≤ d →
    ∀Ref:Fin (n+2)→Fin d→ℝ,RegularSimplexGram Ref →
    ∀f:(Fin d→ℝ)→Fin (n+2)→ℝ,
      (∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d))) →
      (∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) →
    ∀r:ℝ,0<r → r≤1/((n:ℝ)+1) →
      gaussianNoiseStability (-r) f≤gaussianNoiseStability (-r) (regularAssignment Ref) →
      regularOrbitDistance n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f))≤1/((n:ℝ)+2) →
      regularCovarianceDeficit n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f))=0 := by
  filter_upwards [eventually_local_rigidity_measurable_of_balanced_loss C k hC hbalanced]
    with n hn
  intro d hd Ref hRef f hf hp r hr hrange hcomp hlocal
  obtain ⟨g,hg,hgp,hfg,hnoise⟩:=gaussian_simplex_representative f hf hp
  have hr1:r≤1:=hrange.trans ((div_le_one₀ (by positivity)).mpr
    (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have habs:|-r|≤1:=by simpa only [abs_neg,abs_of_pos hr] using hr1
  have he:=actual_centroidRows_congr_ae f g hfg
  have hgcomp:gaussianNoiseStability (-r) g≤gaussianNoiseStability (-r) (regularAssignment Ref):=by
    rw [←hnoise (-r) habs]
    exact hcomp
  have hglocal:regularOrbitDistance n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) g))≤1/((n:ℝ)+2):=by
    rw [←he]
    exact hlocal
  rw [he]
  exact hn d hd Ref hRef g hg (ae_of_all _ hgp) r hr hrange hgcomp hglocal

end NegativeVotingLocalOwnCentroidRigidity
