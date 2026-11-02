import GaussianBoundedMassTaylor
import GaussianRowMassValueUpper
import GaussianFanOffsetRange
import GaussianRegularCovarianceDeficit

/-! A deficit-relative energy certificate for actual balanced dual offsets.
The row energy is not normalized. The singular/duplicate-site extension is
performed by a separate actual dual compactness argument. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped BigOperators Topology RealInnerProductSpace
namespace NegativeVotingBoundedOffsetCertificate
open NegativeVotingBoundedOffsetResponse NegativeVotingBoundedMassTaylor
open NegativeVotingRowMassValueUpper NegativeVotingFan NegativeVotingFanInverse
open NegativeVotingFanSelectedOffsets NegativeVotingFanValue NegativeVotingBalancedReference
open NegativeVotingConditionedFacet NegativeVotingOptimizerConstants
open NegativeVotingMassSemiconcavity NegativeVotingRegularCovarianceDeficit
open NegativeVotingCentroidOptimization NegativeVotingAssignmentDuality
variable {n d:ℕ}

def certificateQuadraticConstant:ℝ:=mixedConstant+32768*Real.pi^2

theorem certificateQuadraticConstant_ge_thirtytwo:32≤ certificateQuadraticConstant:=by
  unfold certificateQuadraticConstant
  nlinarith [mixedConstant_pos,Real.pi_gt_three]

theorem energy_of_box_variations {V:Type*} [Fintype V] [DecidableEq V]
    (h:centeredGauge V) (m T R:ℝ) (hm:0< m) (hT:0< T)
    (hcap:∀i,|(h:V→ℝ) i|≤ T/m)
    (hvar:∀v:centeredGauge V,(∀i,|(v:V→ℝ) i|≤1/(2*m))→
      -((h:V→ℝ) ⬝ᵥ (v:V→ℝ))≤ R+T*(∑i,((v:V→ℝ) i)^2)):
    (∑i,((h:V→ℝ) i)^2)≤4*T*R:=by
  let a:ℝ:=1/(2*T)
  have ha:0< a:=by dsimp [a];positivity
  let v:centeredGauge V:=(-a) • h
  have hv (i:V):(v:V→ℝ) i=-a*(h:V→ℝ) i:=rfl
  have hb:∀i,|(v:V→ℝ) i|≤1/(2*m):=by
    intro i
    rw [hv,abs_mul,abs_neg,abs_of_pos ha]
    calc
      _≤ a*(T/m):=mul_le_mul_of_nonneg_left (hcap i) ha.le
      _=1/(2*m):=by dsimp [a];field_simp
  have hh:=hvar v hb
  have hpair:-((h:V→ℝ) ⬝ᵥ (v:V→ℝ))=a*(∑i,((h:V→ℝ) i)^2):=by
    simp only [dotProduct,hv,Finset.mul_sum,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs:(∑i,((v:V→ℝ) i)^2)=a^2*(∑i,((h:V→ℝ) i)^2):=by
    simp only [hv,mul_pow,neg_sq,Finset.mul_sum]
  rw [hpair,hs] at hh
  have hmul:=mul_le_mul_of_nonneg_left hh (show 0≤4*T by positivity)
  have hl:4*T*(a*(∑i,((h:V→ℝ) i)^2))=2*(∑i,((h:V→ℝ) i)^2):=by
    dsimp [a]
    field_simp
    ring
  have hr:4*T*(R+T*(a^2*(∑i,((h:V→ℝ) i)^2)))=
      4*T*R+(∑i,((h:V→ℝ) i)^2):=by
    dsimp [a]
    field_simp
    ring
  rw [hl,hr] at hmul
  linarith

theorem balanced_selected_offset_abs_bound (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hB:∀i,‖b i‖≤8*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)) (i:Fin (n+2)):
    |(selectedOffsets b (uniformMass n):Fin (n+2)→ℝ) i|≤
      32*(1+Real.log ((n:ℝ)+2))/((n:ℝ)+2):=by
  let m:ℝ:=(n:ℝ)+2
  let L:ℝ:=1+Real.log m
  have hm:1≤ m:=by dsimp [m];have hh:0≤(n:ℝ):=Nat.cast_nonneg n;linarith
  have hmp:0< m:=by linarith
  have hL:0≤ L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hmass:=selectedOffsets_mass b b.ind.injective (uniformMass n) (uniformMass_pos n) (uniformMass_sum n)
  have hedge:∀i j,‖b i-b j‖≤16*Real.sqrt L/m:=by
    intro i j
    have hh:‖b i-b j‖≤‖b i‖+‖b j‖:=norm_sub_le _ _
    have hi:=hB i
    have hj:=hB j
    change ‖b i‖≤8*Real.sqrt L/m at hi
    change ‖b j‖≤8*Real.sqrt L/m at hj
    calc
      _≤‖b i‖+‖b j‖:=hh
      _≤8*Real.sqrt L/m+8*Real.sqrt L/m:=add_le_add hi hj
      _=16*Real.sqrt L/m:=by ring
  have hsmall:∀i,1/(2*(Fintype.card (Fin (n+2)):ℝ))≤
      mass b (selectedOffsets b (uniformMass n)) i:=by
    intro j
    rw [hmass]
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,uniformMass]
    exact one_div_le_one_div_of_le hmp (by change m≤2*m;linarith)
  have hh:=centered_offsets_le_of_cell_masses b (selectedOffsets b (uniformMass n))
    b.ind.injective (16*Real.sqrt L/m) (by positivity) hedge
    (selectedOffsets b (uniformMass n)).property hsmall i
  have hlog:Real.log (2*m)≤ L:=by
    rw [Real.log_mul (by norm_num) hmp.ne']
    have htwo:Real.log 2≤1:=by have hh:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num);linarith
    dsimp [L]
    linarith
  have hroot:Real.sqrt (2*Real.log (2*m))≤2*Real.sqrt L:=by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hL,Real.sq_sqrt (by have h:=Real.log_nonneg (show (1:ℝ)≤2*m by linarith);positivity)]
    nlinarith
  have hu:=mul_le_mul_of_nonneg_left hroot (show 0≤16*Real.sqrt L/m by positivity)
  have he:(16*Real.sqrt L/m)*(2*Real.sqrt L)=32*L/m:=by
    have hs:=Real.sq_sqrt hL
    field_simp
    nlinarith
  rw [he] at hu
  exact hh.trans (by simpa only [offsetRadius,Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat] using hu)

theorem actual_balanced_box_variation (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hn:numericThreshold≤ n+2) (hc:(∑i,b i)=0)
    (hB:∀i,‖b i‖≤8*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2))
    (v:centeredGauge (Fin (n+2)))
    (hv:∀i,|(v:Fin (n+2)→ℝ) i|≤1/(2*((n:ℝ)+2))):
    -((selectedOffsets b (uniformMass n):Fin (n+2)→ℝ) ⬝ᵥ (v:Fin (n+2)→ℝ))≤
      regularCovarianceDeficit n b+
      certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2*
        (∑i,((v:Fin (n+2)→ℝ) i)^2):=by
  let m:ℝ:=(n:ℝ)+2
  let L:ℝ:=1+Real.log m
  have hm:1≤ m:=by dsimp [m];have hh:0≤(n:ℝ):=Nat.cast_nonneg n;linarith
  have hmp:0< m:=by linarith
  have hL:1≤ L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hbox:∀t∈Icc (0:ℝ) 1,∀i,1/(2*m)≤ massLine (uniformMass n) v t i∧
      massLine (uniformMass n) v t i≤(3/2)/m:=by
    intro t ht i
    have ha:|t*(v:Fin (n+2)→ℝ) i|≤1/(2*m):=by
      rw [abs_mul,abs_of_nonneg ht.1]
      calc
        _≤1*|(v:Fin (n+2)→ℝ) i|:=mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
        _≤_:=by simpa only [one_mul] using hv i
    have hb:=abs_le.mp ha
    change 1/(2*m)≤1/m+t*(v:Fin (n+2)→ℝ) i∧1/m+t*(v:Fin (n+2)→ℝ) i≤(3/2)/m
    constructor <;> linarith [show 1/m=2*(1/(2*m)) by field_simp,
      show (3/2)/m=3*(1/(2*m)) by field_simp]
  have hTaylor:=mass_value_lower_taylor b (uniformMass n) v (uniformMass_sum n) m hm hB hbox
  have hs:∑i,(uniformMass n+(v:Fin (n+2)→ℝ)) i=1:=by
    simpa only [massLine,one_smul] using massLine_sum (uniformMass n) v (uniformMass_sum n) 1
  have hwindow:∀i,(uniformMass n+(v:Fin (n+2)→ℝ)) i∈Icc ((1/100:ℝ)/m) (2/m):=by
    intro i
    have hi:=hbox 1 (by norm_num) i
    simp only [massLine,one_smul] at hi
    have hlo:(1/100:ℝ)/m≤1/(2*m):=by
      have hh:=div_le_div_of_nonneg_right (show (1/100:ℝ)≤1/2 by norm_num) hmp.le
      convert hh using 1 <;> field_simp
    exact ⟨hlo.trans hi.1,hi.2.trans (div_le_div_of_nonneg_right (by norm_num) hmp.le)⟩
  have hUpper:=rowObjective_bound_in_mass_window hn b hc
    (uniformMass n+(v:Fin (n+2)→ℝ)) hs hwindow
  unfold rowObjective massValueUpperBound at hUpper
  simp only [Pi.add_apply,add_sub_cancel_left] at hUpper
  change 2*optimizedValue b (uniformMass n+(v:Fin (n+2)→ℝ))-rowEnergy b≤
    NegativeVotingGaussianMaximumMean.referenceFirstWeight n+
    mixedConstant*L^2*(∑i,((v:Fin (n+2)→ℝ) i)^2) at hUpper
  change optimizedValue b (uniformMass n)-
    ((selectedOffsets b (uniformMass n):Fin (n+2)→ℝ) ⬝ᵥ (v:Fin (n+2)→ℝ))-
    16384*Real.pi^2*L*(∑i,((v:Fin (n+2)→ℝ) i)^2)≤
      optimizedValue b (uniformMass n+(v:Fin (n+2)→ℝ)) at hTaylor
  have hcoef:16384*Real.pi^2*L+(mixedConstant/2)*L^2≤ certificateQuadraticConstant*L^2:=by
    have hls:L≤ L^2:=by nlinarith
    have ha:=mul_le_mul_of_nonneg_left hls (show 0≤16384*Real.pi^2 by positivity)
    have hb:16384*Real.pi^2+mixedConstant/2≤ certificateQuadraticConstant:=by
      unfold certificateQuadraticConstant
      nlinarith [mixedConstant_pos,sq_nonneg Real.pi]
    calc
      _≤16384*Real.pi^2*L^2+(mixedConstant/2)*L^2:=add_le_add ha le_rfl
      _=(16384*Real.pi^2+mixedConstant/2)*L^2:=by ring
      _≤_:=mul_le_mul_of_nonneg_right hb (sq_nonneg L)
  have ht:=mul_le_mul_of_nonneg_right hcoef
    (show 0≤∑i,((v:Fin (n+2)→ℝ) i)^2 from Finset.sum_nonneg (fun i _=>sq_nonneg _))
  change _≤ regularCovarianceDeficit n b+certificateQuadraticConstant*L^2*_
  unfold regularCovarianceDeficit
  nlinarith

/-- The deficit controls the literal selected balanced offset, with no
normalization of rowEnergy and no conditioning constant. -/
theorem actual_balanced_offset_energy (b:AffineBasis (Fin (n+2)) ℝ (FSC.Coord d))
    (hn:numericThreshold≤ n+2) (hc:(∑i,b i)=0)
    (hB:∀i,‖b i‖≤8*Real.sqrt (1+Real.log ((n:ℝ)+2))/((n:ℝ)+2)):
    (∑i,((selectedOffsets b (uniformMass n):Fin (n+2)→ℝ) i)^2)≤
      4*certificateQuadraticConstant*(1+Real.log ((n:ℝ)+2))^2*regularCovarianceDeficit n b:=by
  let m:ℝ:=(n:ℝ)+2
  let L:ℝ:=1+Real.log m
  have hm:1≤ m:=by dsimp [m];have hh:0≤(n:ℝ):=Nat.cast_nonneg n;linarith
  have hmp:0< m:=by linarith
  have hL:1≤ L:=by dsimp [L];linarith [Real.log_nonneg hm]
  have hC:0< certificateQuadraticConstant:=lt_of_lt_of_le (by norm_num) certificateQuadraticConstant_ge_thirtytwo
  have hcap:∀i,|(selectedOffsets b (uniformMass n):Fin (n+2)→ℝ) i|≤
      (certificateQuadraticConstant*L^2)/m:=by
    intro i
    apply (balanced_selected_offset_abs_bound b hB i).trans
    apply div_le_div_of_nonneg_right _ hmp.le
    have hh:=mul_le_mul_of_nonneg_right certificateQuadraticConstant_ge_thirtytwo (sq_nonneg L)
    have hl:32*L≤32*L^2:=by nlinarith
    exact hl.trans hh
  have hh:=energy_of_box_variations (selectedOffsets b (uniformMass n)) m
    (certificateQuadraticConstant*L^2) (regularCovarianceDeficit n b) hmp (by positivity) hcap
    (actual_balanced_box_variation b hn hc hB)
  simpa only [mul_assoc] using hh

end NegativeVotingBoundedOffsetCertificate
