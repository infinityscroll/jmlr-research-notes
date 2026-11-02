import GaussianOwnCentroidQuantitativeReplacement
import GaussianPrimalDualDeficit

/-! Exact first-chaos accounting for the own-centroid replacement. A genuine
balanced dual certificate pays the mass perturbation without introducing an
uncontrolled row-error term. No optimality of the comparison rule is assumed. -/
noncomputable section
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix GaussianFin
open scoped BigOperators RealInnerProductSpace Classical Topology
namespace NegativeVotingOwnCentroidPrimalGap
open NegativeVoting NegativeVotingAffine NegativeVotingModern
  NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanValue
  NegativeVotingMassCentroid NegativeVotingAssignmentDuality NegativeVotingCentroidOptimization
  NegativeVotingAssignmentCoordinateBridge NegativeVotingFractionalMass
  NegativeVotingBalancedReference NegativeVotingRegularCovarianceDeficit
  NegativeVotingArbitraryOffsetCertificate NegativeVotingBoundedOffsetCertificate
  NegativeVotingPrimalDualDeficit NegativeVotingOptimizerConstants NegativeVotingGaussianMaximumMean
variable {d n : ℕ}

lemma coordinate_centroid_apply {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : (Fin d→ℝ)→ι→ℝ)
    (hf : ∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x)) (i : ι) (j : Fin d) :
    (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f) i).ofLp j=momentMatrix f i j := by
  have hfeas:=coordinateRule_feasible (LinearIsometryEquiv.refl ℝ _) f hf hp
  have hh:=inner_gaussianCentroid
    (fun x:FSC.Coord d=>coordinateRule (LinearIsometryEquiv.refl ℝ _) f x i)
    (EuclideanSpace.basisFun (Fin d) ℝ j) (hfeas.1 i)
    (feasible_coordinate_bounds _ _ hfeas i)
  simp only [EuclideanSpace.basisFun_inner] at hh
  have hi:=coordinate_integral (LinearIsometryEquiv.refl ℝ _)
    (fun y:Fin d→ℝ=>f y i*y j)
    ((hf i).aestronglyMeasurable.mul (measurable_pi_apply j).aestronglyMeasurable)
  change _=∫y,y j*f y i ∂standardGaussian (Fin d)
  calc
    _ = ∫x:FSC.Coord d,coordinateRule (LinearIsometryEquiv.refl ℝ _) f x i*x j
        ∂stdGaussian (FSC.Coord d):=hh
    _ = ∫y:Fin d→ℝ,f y i*y j ∂standardGaussian (Fin d):=hi
    _ = _:=by apply integral_congr_ae;filter_upwards with x;ring

lemma centroidResidual_eq_rowEnergy {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : (Fin d→ℝ)→ι→ℝ)
    (hf : ∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x))
    (hg : ∀i,AEMeasurable (fun x=>g x i) (standardGaussian (Fin d)))
    (hgp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (g x)) :
    centroidResidual f g=rowEnergy
      (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f)-
        centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) g)) := by
  unfold centroidResidual rowEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply,PiLp.sub_apply,coordinate_centroid_apply f hf hp,
    coordinate_centroid_apply g hg hgp,sub_sq_comm]

/-- Actual primal square completion, including arbitrary fractional comparison
rules with the same masses. The only row hypothesis is the competitive row cap,
which itself follows from the actual mass window. -/
theorem own_centroid_first_gap_lower
    (hn : numericThreshold ≤ n+2)
    (f g : (Fin d→ℝ)→Fin (n+2)→ℝ)
    (hf : ∀i,AEMeasurable (fun x=>f x i) (standardGaussian (Fin d)))
    (hp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (f x))
    (hg : ∀i,AEMeasurable (fun x=>g x i) (standardGaussian (Fin d)))
    (hgp : ∀ᵐx ∂standardGaussian (Fin d),SimplexWeights (g x))
    (hmass : assignmentMass g=assignmentMass f)
    (hwindow : ∀i,assignmentMass f i ≤ 2/((n:ℝ)+2)) :
    centroidResidual f g+referenceFirstWeight n-assignmentFirstEnergy g ≥
      regularCovarianceDeficit n (centroidRows (coordinateRule (LinearIsometryEquiv.refl ℝ _) f))-
        4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2*massDeficit n f := by
  let F:=coordinateRule (LinearIsometryEquiv.refl ℝ _) f
  let G:=coordinateRule (LinearIsometryEquiv.refl ℝ _) g
  let B:=centroidRows F
  let p:=assignmentMass f
  let z:Fin (n+2)→ℝ:=p-uniformMass n
  let H:ℝ:=4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2
  have hF:Feasible p F:=coordinateRule_feasible _ f hf hp
  have hG:Feasible p G:=by
    have hh:=coordinateRule_feasible (LinearIsometryEquiv.refl ℝ _) g hg hgp
    rw [hmass] at hh
    exact hh
  have hc:(∑i,B i)=0:=centroidRows_sum_zero p F hF
  have hcap:∀i,‖B i‖≤4*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2):=
    feasible_centroid_norm_le p F hF hwindow
  obtain ⟨h,hpot,henergy⟩:=exists_balanced_optimal_dual_with_energy_bound hn B hc hcap
  have hH:0<H:=by
    have hh:=certificateQuadraticConstant_ge_thirtytwo
    have hl:0 ≤ Real.log ((n:ℝ)+2):=Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    dsimp [H]
    positivity
  have he:∑i,((h:Fin (n+2)→ℝ) i)^2 ≤ H*regularCovarianceDeficit n B:=by
    simpa only [H,mul_assoc] using henergy
  have hval:=assignmentValue_le_potential B p h G hG
  rw [dual_mass_shift B p h,hpot] at hval
  have hsquare:=assignment_square_completion B p G hG
  have hE:centroidEnergy G=assignmentFirstEnergy g:=coordinateRule_centroidEnergy _ g hg hgp
  have hres:centroidResidual f g=rowEnergy (B-centroidRows G):=
    centroidResidual_eq_rowEnergy f g hf hp hg hgp
  have hZ:(∑i,(z i)^2)=massDeficit n f:=rfl
  have hs:0 ≤ ∑i,((h:Fin (n+2)→ℝ) i+H*z i)^2:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hexp:(∑i,((h:Fin (n+2)→ℝ) i+H*z i)^2)=
      (∑i,((h:Fin (n+2)→ℝ) i)^2)+2*H*((h:Fin (n+2)→ℝ) ⬝ᵥ z)+H^2*(∑i,(z i)^2):=by
    have ht (i:Fin (n+2)) : ((h:Fin (n+2)→ℝ) i+H*z i)^2 =
      ((h:Fin (n+2)→ℝ) i)^2+2*H*((h:Fin (n+2)→ℝ) i*z i)+H^2*(z i)^2:=by ring
    simp only [ht,Finset.sum_add_distrib,←Finset.mul_sum,dotProduct]
  rw [hexp] at hs
  have hdot:-(regularCovarianceDeficit n B)-H*massDeficit n f ≤ 2*((h:Fin (n+2)→ℝ) ⬝ᵥ z):=by
    have hz:=mul_le_mul_of_nonneg_left he hH.le
    have ht:H*(-(regularCovarianceDeficit n B)-H*massDeficit n f) ≤
        H*(2*((h:Fin (n+2)→ℝ) ⬝ᵥ z)):=by rw [←hZ];nlinarith only [hs,he]
    exact (mul_le_mul_iff_right₀ hH).mp ht
  have hdef:2*regularCovarianceDeficit n B=
      referenceFirstWeight n+rowEnergy B-2*optimizedValue B (uniformMass n):=by
    unfold regularCovarianceDeficit
    ring
  change assignmentValue B G ≤ optimizedValue B (uniformMass n)-(h:Fin (n+2)→ℝ) ⬝ᵥ z at hval
  rw [hE,←hres] at hsquare
  change _ ≥ regularCovarianceDeficit n B-H*massDeficit n f
  linarith only [hsquare,hval,hdot,hdef]

end NegativeVotingOwnCentroidPrimalGap
