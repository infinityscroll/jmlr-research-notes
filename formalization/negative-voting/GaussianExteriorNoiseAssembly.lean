import GaussianExteriorTailAbsorption
import GaussianSecondChaosAbsorption
import GaussianOwnCentroidSpectralReplacement
import GaussianReferenceSecondEnergy
import GaussianActualRowPayment

/-! Exact signed-noise assembly for the actual exterior branch. The high
tail is the full infinite Hermite remainder. No positivity of its summands,
or pointwise representative assumption on the competitor, is used. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingExteriorNoiseAssembly
open NegativeVoting NegativeVotingModern NegativeVotingAffine
  NegativeVotingOwnCentroidSpectralReplacement NegativeVotingSignedHighTailComparison
  NegativeVotingExteriorActualComparison NegativeVotingExteriorSignedTailRelative
  NegativeVotingBalancedReference NegativeVotingProcrustes NegativeVotingRegularScoreLaw
  NegativeVotingReferenceSecondEnergy NegativeVotingFractionalMass NegativeVotingCompetitiveDeficit
  NegativeVotingAssignmentCoordinateBridge NegativeVotingHypercontractivity
  NegativeVotingGaussianMaximumMean NegativeVotingGaussianMaximumLocalization
  NegativeVotingActualRowPayment NegativeVotingSecondChaosAbsorption
  NegativeVotingCompetitiveSecondChaosComparison NegativeVotingGlobalCovarianceDeficit
  NegativeVotingCompetitiveCovarianceTransfer NegativeVotingExteriorTailAbsorption
  NegativeVotingCentroidOptimization
  OAI.MinUncut.GaussianHermite
variable {n d : ℕ}

/-- Identification of the literal high-mode pairing, including completed
Gaussian measurable assignments. -/
theorem sum_energyPairing_eq_tail (r : ℝ) (hr : 0<r) (hr1 : r<1) (k : ℕ)
    (f : (Fin d→ℝ)→Fin (n+2)→ℝ)
    (hf : ∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) :
    (∑i,energyPairing (-r) k (fun x=>f x i))=
      ∑'j:ℕ,(-r)^(j+k)*chaosEnergy f (j+k) := by
  obtain ⟨g,hg,hgs,hfg,_⟩:=gaussian_simplex_representative f hf hp
  have hmem:=simplex_component_memLp g hg (fun x=>(hgs x).1) (fun x=>(hgs x).2)
  have he:=highMode_cross_eq_tail (-r) (by simpa [abs_of_pos hr] using hr1.le)
    k g g hg hmem hmem
  have hcross (j:ℕ) : chaosCrossEnergy g g j=chaosEnergy g j:=by
    simp only [chaosCrossEnergy,chaosEnergy,labelCoefficientEnergy,pow_two]
  simp_rw [hcross] at he
  calc
    _ = ∑i,energyPairing (-r) k (fun x=>g x i):=by
      apply Finset.sum_congr rfl
      intro i _
      exact energyPairing_congr_ae r hr hr1 k (hfg.mono fun x hx=>congrFun hx i)
    _ = ∑'j:ℕ,(-r)^(j+k)*chaosEnergy g (j+k):=he
    _ = _:=by
      apply tsum_congr
      intro j
      rw [gaussian_chaosEnergy_congr_ae f g hfg]

theorem negative_noise_pairing_expansion (r : ℝ) (hr : 0<r) (hr1 : r<1)
    (f : (Fin d→ℝ)→Fin (n+2)→ℝ)
    (hf : ∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) :
    gaussianNoiseStability (-r) f=(∑i,(assignmentMass f i)^2)-r*assignmentFirstEnergy f+
      r^2*chaosEnergy f 2+∑i,energyPairing (-r) 3 (fun x=>f x i) := by
  rw [sum_energyPairing_eq_tail r hr hr1 3 f hf hp]
  exact gaussianNoiseStability_negative_expansion r (by simpa [abs_of_pos hr] using hr1.le) f hf hp

/-- Normalize the physical regular orbit without changing its assignment. -/
theorem scaled_regular_raw_assignment (R : Fin (n+2)→FSC.Coord d)
    (hR : ScaledRegularGram n R) :
    ∃U:Fin (n+2)→Fin d→ℝ,RegularSimplexGram U ∧
      (fun x i=>rawCoordinate (NegativeVotingFan.weights R 0) i x)=regularAssignment U := by
  let S:Fin (n+2)→FSC.Coord d:=(referenceScale n)⁻¹•R
  have hS:∀i j,inner ℝ (S i) (S j)=(if i=j then 1 else 0)-1/((n:ℝ)+2):=by
    simpa only [S,Nat.cast_add,Nat.cast_ofNat] using
      NegativeVotingExteriorRoutingGeometry.scaled_regular_normalized_gram R hR
  refine ⟨coordinateRows S,coordinateRows_gram S hS,?_⟩
  have he:R=referenceScale n•S:=by
    simp only [S,smul_smul,mul_inv_cancel₀ (ne_of_gt (referenceScale_pos n)),one_smul]
  funext x i
  change NegativeVotingFan.weights R 0 (WithLp.toLp 2 x) i=_
  rw [he]
  exact (scaled_weights_zero S (referenceScale n) (referenceScale_pos n) _ i).trans
    (zero_weights_eq_regular S _ i)

/-- The exact deficit identity uses the same concrete regular rule as the
signed-tail estimate; the reference may be in any regular orbit position. -/
theorem noise_difference_eq_deficit (hn : 0<n) (r : ℝ) (hr : 0<r) (hr1 : r<1)
    (Ref : Fin (n+2)→Fin d→ℝ) (hRef : RegularSimplexGram Ref)
    (f : (Fin d→ℝ)→Fin (n+2)→ℝ)
    (hf : ∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x))
    (R : Fin (n+2)→FSC.Coord d) (hR : ScaledRegularGram n R) :
    gaussianNoiseStability (-r) f-gaussianNoiseStability (-r) (regularAssignment Ref)=
      competitiveDeficit n r f-r^2*(referenceSecondWeight n-chaosEnergy f 2)+
        signedTailDifference r (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)
          (NegativeVotingFan.weights R 0) := by
  obtain ⟨U,hU,hraw⟩:=scaled_regular_raw_assignment R hR
  have hg:∀i,AEMeasurable (fun x=>regularAssignment U x i) (standardGaussian (Fin d)):=
    fun i=>(regularAssignment_measurable U i).aemeasurable
  have hs:=ae_of_all (standardGaussian (Fin d)) (regularAssignment_simplex U)
  have he:=negative_noise_pairing_expansion r hr hr1 (regularAssignment U) hg hs
  have hmass:(∑i,(assignmentMass (regularAssignment U) i)^2)=1/((n:ℝ)+2):=by
    simpa only [chaosEnergy_zero,assignmentMass] using regular_chaosEnergy_zero n U hU
  have hfirst:assignmentFirstEnergy (regularAssignment U)=referenceFirstWeight n:=by
    simpa only [chaosEnergy_one,assignmentFirstEnergy] using regular_chaosEnergy_one_eq_reference n hn U hU
  rw [hmass,hfirst,regular_chaosEnergy_two_eq_reference n hn U hU] at he
  have hnoise:gaussianNoiseStability (-r) (regularAssignment Ref)=
      gaussianNoiseStability (-r) (regularAssignment U):=by
    rw [regularAssignment_noise_eq_canonical n Ref hRef,regularAssignment_noise_eq_canonical n U hU]
  rw [hnoise,he,negative_noise_pairing_expansion r hr hr1 f hf hp]
  have ht:signedTailDifference r (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)
      (NegativeVotingFan.weights R 0)=
      (∑i,energyPairing (-r) 3 (fun x=>f x i))-
        ∑i,energyPairing (-r) 3 (fun x=>regularAssignment U x i):=by
    simp only [signedTailDifference,Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext x
    exact congrFun (congrFun hraw x) i
  rw [ht,competitiveDeficit,massDeficit_eq n f hf hp]
  ring

/-- The actual small-power row payment is enough for exterior second-chaos
absorption. All row geometry, coefficient moments and cutoff errors have been
paid before this statement; the only branch hypothesis is the literal orbit
distance defining the exterior. -/
theorem eventually_exterior_second_loss_absorbed :
    ∀ᶠ n:ℕ in atTop,∀(d:ℕ) (hd:n+1≤d)
      (Ref:Fin (n+2)→Fin d→ℝ) (hRef:RegularSimplexGram Ref)
      (f:(Fin d→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
      (hp:∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x))
      (r:ℝ) (hr0:0<r) (hr:r≤1/((n:ℝ)+1))
      (hcomp:gaussianNoiseStability (-r) f≤gaussianNoiseStability (-r) (regularAssignment Ref)),
      1/((n:ℝ)+2)<regularOrbitDistance n
        (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)) →
      r^2*(referenceSecondWeight n-chaosEnergy f 2)≤competitiveDeficit n r f/4 := by
  filter_upwards [eventually_actual_competitive_row_payment (1/10000) (by norm_num),
    eventually_second_chaos_of_radial_payment,
    eventually_uniform_payment_small (16386*96) (3/1000) (1/1920)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_cutoff_tail_paid (globalRadius/240) (1/8)
      (by have hh:=globalRadius_bounds.1;positivity) (by norm_num),
    eventually_uniform_actual_competitive_exterior_bounds,
    eventually_uniform_actual_covariance_deficit_transfer,
    NegativeVotingUniformMassBound.eventually_uniform_competitive_deficit_bounds] with
    n hpay hsecond hsmall hcut hext htransfer hdef
  intro d hd Ref hRef f hf hp r hr0 hr hcomp hout
  let J:ℝ:=competitiveDeficit n r f/r
  let m:ℝ:=(n:ℝ)+2
  let K:ℝ:=96*m^(3/1000:ℝ)
  have hK:0≤K:=by dsimp [K,m];positivity
  have hpaid:=hpay (Fin d) Ref hRef f hf hp r hr0 hr hcomp d (LinearIsometryEquiv.refl ℝ _)
  norm_num only [show (30:ℝ)*(1/10000)=3/1000 by norm_num] at hpaid
  have hE:=hsecond d Ref hRef f hf hp r hr0 hr hcomp K hK hpaid
  have hx:=hext (Fin d) Ref hRef f hf hp r hr0 hr hcomp d hd
    (LinearIsometryEquiv.refl ℝ _) hout
  have htr:=(htransfer (Fin d) Ref hRef f hf hp r hr0 hr hcomp d
    (LinearIsometryEquiv.refl ℝ _)).1
  have hfloor:(globalRadius/240)/(m^3*Real.sqrt (1+Real.log m))≤J:=by
    simpa only [J,m,div_div,mul_assoc] using hx.1.trans htr
  have hT:=hcut J hfloor
  have hD:0≤competitiveDeficit n r f:=
    (hdef (Fin d) Ref hRef f hf hp r hr0.le hr hcomp).1
  have hJ:0≤J:=div_nonneg hD hr0.le
  have hA:r*(240*(1+Real.log m)*(1+16386*K))≤(1/4:ℝ)/2:=by
    have hh:=mul_le_mul_of_nonneg_left (hsmall r hr0.le hr).le
      (by norm_num : (0:ℝ)≤240)
    dsimp [K,m]
    nlinarith only [hh]
  have hr1:r≤1:=hr.trans ((div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have heq:competitiveDeficit n r f=r*J:=by dsimp [J];field_simp
  have hh:=second_loss_absorption r J (competitiveDeficit n r f)
    (240*(1+Real.log m)*(1+16386*K))
    (2160*(1+Real.log m)*Real.exp (-16*(1+Real.log m)))
    (referenceSecondWeight n-chaosEnergy f 2) (1/4)
    hr0.le hr1 hJ (by norm_num) heq hE hA (by norm_num [m] at hT ⊢;exact hT)
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh

/-- Every actual competitor lies in the regular score ball. This excludes
the exterior for the entire negative voting interval, including arbitrarily
small correlations; no final noise or second-energy bound is assumed. -/
theorem eventually_competitive_orbit_distance_le :
    ∀ᶠ n:ℕ in atTop,∀(d:ℕ) (hd:n+1≤d)
      (Ref:Fin (n+2)→Fin d→ℝ) (hRef:RegularSimplexGram Ref)
      (f:(Fin d→ℝ)→Fin (n+2)→ℝ)
      (hf:∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
      (hp:∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x))
      (r:ℝ) (hr0:0<r) (hr:r≤1/((n:ℝ)+1))
      (hcomp:gaussianNoiseStability (-r) f≤gaussianNoiseStability (-r) (regularAssignment Ref)),
      regularOrbitDistance n (centroidRows
        (coordinateRule (LinearIsometryEquiv.refl ℝ _) f))≤1/((n:ℝ)+2) := by
  filter_upwards [eventually_exterior_second_loss_absorbed,
    eventually_uniform_exterior_tail_absorption (1/4) (by norm_num),
    eventually_uniform_actual_competitive_exterior_bounds,
    eventually_uniform_actual_covariance_deficit_transfer,eventually_gt_atTop (0:ℕ)] with
    n hsecond htail hext htransfer hn
  intro d hd Ref hRef f hf hp r hr0 hr hcomp
  by_contra hnot
  have hout:=lt_of_not_ge hnot
  have hE:=hsecond d hd Ref hRef f hf hp r hr0 hr hcomp hout
  obtain ⟨R,hR,hH⟩:=htail (Fin d) Ref hRef f hf hp r hr0 hr hcomp d hd
    (LinearIsometryEquiv.refl ℝ _) hout
  have hx:=hext (Fin d) Ref hRef f hf hp r hr0 hr hcomp d hd
    (LinearIsometryEquiv.refl ℝ _) hout
  have htr:=(htransfer (Fin d) Ref hRef f hf hp r hr0 hr hcomp d
    (LinearIsometryEquiv.refl ℝ _)).1
  have hRad:=globalRadius_bounds.1
  have hlog:=Real.log_nonneg (show (1:ℝ)≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hJ:0<competitiveDeficit n r f/r:=lt_of_lt_of_le (by positivity) (hx.1.trans htr)
  have hD:0<competitiveDeficit n r f:= (div_pos_iff_of_pos_right hr0).mp hJ
  have hr1:r<1:=hr.trans_lt ((div_lt_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    (by exact_mod_cast (show 1<n+1 by omega)))
  have he:=noise_difference_eq_deficit hn r hr0 hr1 Ref hRef f hf hp R hR
  have hHlower':= (abs_le.mp hH).1
  linarith

end NegativeVotingExteriorNoiseAssembly
