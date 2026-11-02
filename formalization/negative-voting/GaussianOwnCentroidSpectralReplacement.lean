import GaussianOwnCentroidRoutingCap
import GaussianSignedHighTailComparison

/-! Exact spectral identifications for the own-centroid replacement.  The
signed tail and the full odd residual are identified with actual Gaussian
pairings; no routing or final noise comparison is assumed. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped BigOperators ENNReal RealInnerProductSpace Classical
namespace NegativeVotingOwnCentroidSpectralReplacement
open NegativeVotingAffine NegativeVotingModern NegativeVotingProjection
  NegativeVotingPathSmoothedComparison NegativeVotingRareLabelHighChaos
  NegativeVotingStructuredResidualInputs NegativeVotingSignedHighTailComparison
  NegativeVotingOUResidualMoment NegativeVotingHypercontractivity
  OAI.MinUncut.GaussianHermite SlowEquilibration.GaussianMaximalCorrelation
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem highMode_cross_hasSum (ρ : ℝ) (hρ : |ρ| ≤ 1) (k : ℕ)
    (f g : (Fin d → ℝ) → ι → ℝ)
    (hgM : ∀ i, Measurable (fun x => g x i))
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γFin d))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (γFin d)) :
    HasSum (fun j : ℕ => if j < k then 0 else ρ^j * chaosCrossEnergy f g j)
      (∑ i, ∫ x, f x i * gaussianAverage ρ (highModes k (fun y => g y i)) x ∂γFin d) := by
  have hs (i : ι) := coefficient_pairing_hasSum (fun x => f x i)
    (gaussianAverage ρ (highModes k (fun x => g x i))) (hf i)
    (gaussianAverage_memLp_signed ρ hρ _ (highModes_measurable k _ (hgM i))
      (highModes_memLp k _ (hg i)))
  have hh := (hasSum_sum (s := Finset.univ) (fun i _ => hs i)).tsum_fiberwise degree
  convert hh using 1
  funext j
  change (if j < k then 0 else ρ^j * chaosCrossEnergy f g j) =
    ∑' a : {a : Fin d → ℕ // degree a = j}, ∑ i,
      coeff (fun x => f x i) a.1 *
        coeff (gaussianAverage ρ (highModes k (fun x => g x i))) a.1
  simp_rw [gaussianAverage_coefficient ρ hρ _ (highModes_measurable k _ (hgM _))
    (highModes_memLp k _ (hg _)), coeff_highModes k _ (hg _)]
  by_cases hj : j < k
  · simp only [ite_eq_left hj]
    symm
    have hz (a : {a : Fin d → ℕ // degree a = j}) :
        (∑ i, coeff (fun x => f x i) a.1 * (ρ ^ degree a.1 *
          (if degree a.1 < k then 0 else coeff (fun x => g x i) a.1)))=0 := by
      simp only [a.property, ite_eq_left hj, mul_zero, Finset.sum_const_zero]
    simp only [hz, tsum_zero]
  · simp only [ite_eq_right hj, chaosCrossEnergy, ← tsum_mul_left]
    apply tsum_congr
    intro a
    simp only [a.property, ite_eq_right hj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem highMode_cross_eq_tail (ρ : ℝ) (hρ : |ρ| ≤ 1) (k : ℕ)
    (f g : (Fin d → ℝ) → ι → ℝ)
    (hgM : ∀ i, Measurable (fun x => g x i))
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γFin d))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (γFin d)) :
    (∑ i, ∫ x, f x i * gaussianAverage ρ (highModes k (fun y => g y i)) x ∂γFin d) =
      ∑' j : ℕ, ρ^(j+k) * chaosCrossEnergy f g (j+k) := by
  have hs := highMode_cross_hasSum ρ hρ k f g hgM hf hg
  have ht := hs.summable.sum_add_tsum_nat_add k
  have hz : (∑ j ∈ Finset.range k, if j < k then (0 : ℝ) else ρ^j * chaosCrossEnergy f g j)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [ite_eq_left (Finset.mem_range.mp hj)]
  rw [hz, zero_add, hs.tsum_eq] at ht
  rw [← ht]
  apply tsum_congr
  intro j
  simp only [ite_eq_right (show ¬ j+k < k by omega)]

theorem signedCrossTail_eq_pairing (r : ℝ) (hr : |r| ≤ 1)
    (f g : (Fin d → ℝ) → ι → ℝ)
    (hgM : ∀ i, Measurable (fun x => g x i))
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γFin d))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (γFin d)) :
    signedCrossTail r f g =
      ∑ i, ∫ x, f x i * gaussianAverage (-r) (highModes 2 (fun y => g y i)) x ∂γFin d := by
  exact (highMode_cross_eq_tail (-r) (by simpa using hr) 2 f g hgM hf hg).symm

theorem oddSquare_hasSum (s : ℝ) (hs : |s| ≤ 1)
    (f : (Fin d → ℝ) → ι → ℝ)
    (hfM : ∀ i, Measurable (fun x => f x i))
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γFin d)) :
    HasSum (fun j : ℕ => if j < 3 ∨ Even j then 0 else (s^2)^j * chaosEnergy f j)
      (∑ i, ∫ x, (gaussianAverage s (oddHighModes (fun y => f y i)) x)^2 ∂γFin d) := by
  have hi (i : ι) := NegativeVotingChaosDecay.coefficient_energy_hasSum_of_memLp
    (gaussianAverage_memLp_signed s hs _ (oddHighModes_measurable _ (hfM i))
      (oddHighModes_memLp _ (hf i)))
  have hiFin (i : ι) : HasSum (fun a => (coeff (gaussianAverage s (oddHighModes (fun x => f x i))) a)^2)
      (∫ x, (gaussianAverage s (oddHighModes (fun y => f y i)) x)^2 ∂γFin d) := hi i
  have hh := (hasSum_sum (s := Finset.univ) (fun i _ => hiFin i)).tsum_fiberwise degree
  convert hh using 1
  funext j
  change (if j < 3 ∨ Even j then 0 else (s^2)^j * chaosEnergy f j) =
    ∑' a : {a : Fin d → ℕ // degree a = j}, ∑ i,
      (coeff (gaussianAverage s (oddHighModes (fun x => f x i))) a.1)^2
  simp_rw [gaussianAverage_coefficient s hs _ (oddHighModes_measurable _ (hfM _))
    (oddHighModes_memLp _ (hf _)), coeff_oddHighModes _ (hfM _) (hf _)]
  by_cases hj : j < 3 ∨ Even j
  · simp only [ite_eq_left hj]
    symm
    have hz (a : {a : Fin d → ℕ // degree a = j}) :
        (∑ i, (s ^ degree a.1 * (if degree a.1 < 3 ∨ Even (degree a.1) then 0
          else coeff (fun x => f x i) a.1))^2)=0 := by
      simp only [a.property, ite_eq_left hj, mul_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    simp only [hz, tsum_zero]
  · simp only [ite_eq_right hj, chaosEnergy, ← tsum_mul_left]
    apply tsum_congr
    intro a
    simp only [a.property, ite_eq_right hj, labelCoefficientEnergy, Finset.mul_sum, mul_pow]
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 j]

theorem oddResidual_eq_square (s : ℝ) (hs : |s| ≤ 1)
    (f : (Fin d → ℝ) → ι → ℝ)
    (hfM : ∀ i, Measurable (fun x => f x i))
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γFin d)) :
    oddResidual (s^2) f =
      ∑ i, ∫ x, (gaussianAverage s (oddHighModes (fun y => f y i)) x)^2 ∂γFin d := by
  let a : ℕ → ℝ := fun j => if j < 3 ∨ Even j then 0 else (s^2)^j * chaosEnergy f j
  have ha : HasSum a _ := oddSquare_hasSum s hs f hfM hf
  have he := ha.summable.comp_injective (show Function.Injective (fun k : ℕ => 2*k) from fun _ _ h => by dsimp only at h; omega)
  have ho := ha.summable.comp_injective (show Function.Injective (fun k : ℕ => 2*k+1) from fun _ _ h => by dsimp only at h; omega)
  have hsplit := tsum_even_add_odd (f := a) he ho
  have hz : (∑' k : ℕ, a (2*k))=0 := by
    have hz (k : ℕ) : a (2*k)=0 := by
      simp only [a, ite_eq_left (Or.inr (show Even (2*k) from ⟨k, by omega⟩))]
    simp only [hz, tsum_zero]
  rw [hz, zero_add, ha.tsum_eq] at hsplit
  have hshift := ho.sum_add_tsum_nat_add 1
  simp only [Function.comp_apply] at hshift
  have hfirst : (∑ k ∈ Finset.range 1, a (2*k+1))=0 := by simp [a]
  rw [hfirst, zero_add] at hshift
  rw [← hsplit, ← hshift, oddResidual, ← tsum_mul_left]
  apply tsum_congr
  intro k
  have hk : ¬ (2*(k+1)+1 < 3 ∨ Even (2*(k+1)+1)) := by
    apply not_or.mpr
    constructor
    · omega
    · intro he
      obtain ⟨b, hb⟩ := he
      omega
  simp only [a, ite_eq_right hk]
  rw [show 2*(k+1)+1=2*k+3 by omega, pow_add]
  ring

/-- The odd source is an orthogonal projection before smoothing, so its
second smoothing paired with the original function is exactly its L2 square. -/
theorem odd_pairing_eq_square (s : ℝ) (hs : |s| ≤ 1)
    (f : (Fin d → ℝ) → ℝ) (hfM : Measurable f) (hf : MemLp f 2 (γFin d)) :
    (∫ x, f x * gaussianAverage s (gaussianAverage s (oddHighModes f)) x ∂γFin d) =
      ∫ x, (gaussianAverage s (oddHighModes f) x)^2 ∂γFin d := by
  have hop := oddHighModes_memLp f hf
  have hopM := oddHighModes_measurable f hfM
  have hu := gaussianAverage_memLp_signed s hs _ hopM hop
  have huM := gaussianAverage_measurable s _ hopM
  have hv := gaussianAverage_memLp_signed s hs _ huM hu
  have hl := coefficient_pairing_hasSum f _ hf hv
  have hr : HasSum (fun a => (coeff (gaussianAverage s (oddHighModes f)) a)^2)
      (∫ x, (gaussianAverage s (oddHighModes f) x)^2 ∂γFin d) :=
    NegativeVotingChaosDecay.coefficient_energy_hasSum_of_memLp hu
  apply hl.unique
  convert hr using 1
  funext b
  rw [gaussianAverage_coefficient s hs _ huM hu,
    gaussianAverage_coefficient s hs _ hopM hop, coeff_oddHighModes f hfM hf]
  split_ifs <;> ring

/-- Literal retained-square comparison, now entirely in actual OU pairings.
The only removed term is the nonnegative even residual. -/
theorem actual_reference_ou_lower_bound (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (f g : (Fin d → ℝ) → ι → ℝ)
    (hfM : ∀ i, Measurable (fun x => f x i))
    (hgM : ∀ i, Measurable (fun x => g x i))
    (hf : ∀ i, MemLp (fun x => f x i) 2 (γFin d))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (γFin d))
    (hmass : ∀ i, (∫ x, f x i ∂γFin d) = ∫ x, g x i ∂γFin d) :
    s^2 * centroidResidual f g +
      (∑ i, ∫ x, (gaussianAverage s (oddHighModes (fun y => f y i-g y i)) x)^2 ∂γFin d) +
      2 * (s^2 * centroidRouting f g +
        ∑ i, ∫ x, (f x i-g x i) *
          (gaussianAverage (-(s^2)) (highModes 2 (fun y => g y i)) x-
            gaussianAverage s (gaussianAverage s (oddHighModes (fun y => f y i-g y i))) x) ∂γFin d) ≤
      NegativeVoting.gaussianNoiseStability (-(s^2)) f-
        NegativeVoting.gaussianNoiseStability (-(s^2)) g := by
  have hsa : |s| ≤ 1 := by rw [abs_of_pos hs]; exact hs1.le
  have hsqa : |s^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hneg : |-(s^2)| ≤ 1 := by simpa only [abs_neg] using hsqa
  have hv i : MemLp (fun x => f x i-g x i) 2 (γFin d) := (hf i).sub (hg i)
  have hvM i : Measurable (fun x => f x i-g x i) := (hfM i).sub (hgM i)
  have hId := actual_reference_difference (s^2) hsqa f g hfM hgM hf hg hmass
  have he := evenResidual_nonneg (s^2) (sq_nonneg _) (difference f g)
  have hodd := oddResidual_eq_square s hsa (difference f g) hvM hv
  have hcross := signedCrossTail_eq_pairing (s^2) hsqa (difference f g) g hgM hv hg
  have hp : (∑ i, ∫ x, (f x i-g x i) *
      (gaussianAverage (-(s^2)) (highModes 2 (fun y => g y i)) x-
        gaussianAverage s (gaussianAverage s (oddHighModes (fun y => f y i-g y i))) x) ∂γFin d) =
      signedCrossTail (s^2) (difference f g) g-oddResidual (s^2) (difference f g) := by
    rw [hcross,hodd,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [difference]
    rw [← odd_pairing_eq_square s hsa _ (hvM i) (hv i)]
    simp only [mul_sub]
    apply integral_sub
    · exact (hv i).integrable_mul (gaussianAverage_memLp_signed _ hneg _
        (highModes_measurable 2 _ (hgM i)) (highModes_memLp 2 _ (hg i)))
    · exact (hv i).integrable_mul (gaussianAverage_memLp_signed s hsa _
        (gaussianAverage_measurable s _ (oddHighModes_measurable _ (hvM i)))
        (gaussianAverage_memLp_signed s hsa _ (oddHighModes_measurable _ (hvM i))
          (oddHighModes_memLp _ (hv i))))
  rw [hp]
  change _ + (∑ i, ∫ x, (gaussianAverage s (oddHighModes (fun y => difference f g y i)) x)^2 ∂γFin d) + _ ≤ _
  rw [← hodd]
  linarith

/-- An exact finite description of the constant and linear Hermite modes. -/
theorem lowerModes_two : lowerModes (κ := Fin d) 2 =
    insert 0 (Finset.univ.image (fun j : Fin d => Pi.single j 1)) := by
  ext b
  rw [mem_lowerModes_iff, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro hb
    have hdeg : degree b=0 ∨ degree b=1 := by omega
    rcases hdeg with h0 | h1
    · exact Or.inl ((degree_zero_iff b).mp h0)
    · obtain ⟨j,hj⟩ := (degree_one_iff b).mp h1
      exact Or.inr ⟨j,Finset.mem_univ _,hj.symm⟩
  · rintro (rfl | ⟨j,_,rfl⟩)
    · simp [degree]
    · rw [degree_single_one]; norm_num

theorem psi_single_one (j : Fin d) (x : Fin d → ℝ) : psi (Pi.single j 1) x=x j := by
  unfold psi
  rw [Finset.prod_eq_single j]
  · simp [H,he_one]
  · intro k _ hkj
    simp [hkj,H]
  · simp

theorem lowModes_two_sum (ρ : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    (∑ b ∈ lowerModes 2, ρ^(degree b)*coeff f b*psi b x) =
      (∫ y,f y ∂γFin d)+ρ*∑ j,(∫ y,y j*f y ∂γFin d)*x j := by
  have hzero : (0 : Fin d → ℕ) ∉ Finset.univ.image (fun j : Fin d => Pi.single j 1) := by
    simp only [Finset.mem_image,not_exists,not_and]
    intro j _ he
    have hh := congrFun he j
    simp at hh
  have hinj : Function.Injective (fun j : Fin d => (Pi.single j 1 : Fin d → ℕ)) := by
    intro j k hjk
    by_contra hne
    have hh := congrFun hjk j
    simp [hne] at hh
  rw [lowerModes_two,Finset.sum_insert hzero,Finset.sum_image (fun j _ k _ h => hinj h)]
  simp only [degree_single_one,pow_one,psi_single_one,coefficient_single_degree,
    coefficient_zero_degree]
  have hpsi : psi (0 : Fin d → ℕ) x=1 := by simp [psi,H]
  rw [show degree (0 : Fin d → ℕ)=0 by simp [degree],pow_zero,hpsi,one_mul,mul_one,
    Finset.mul_sum]
  simp only [mul_assoc, show γpi (Fin d)=γFin d from rfl]

theorem gaussianAverage_highModes_two_bounded (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (f : (Fin d → ℝ) → ℝ) (hfM : Measurable f) (M : ℝ)
    (hM : ∀ x, |f x| ≤ M) (x : Fin d → ℝ) :
    gaussianAverage ρ (highModes 2 f) x=gaussianAverage ρ f x-
      (∫ y,f y ∂γFin d)-ρ*∑ j,(∫ y,y j*f y ∂γFin d)*x j := by
  rw [NegativeVotingBoundedOUCellTests.gaussianAverage_highModes_bounded ρ hρ 2 f hfM M hM,
    lowModes_two_sum]
  ring

open NegativeVoting NegativeVotingBalancedReference NegativeVotingRegularMaximum
  NegativeVotingRegularScoreLaw NegativeVotingOwnCentroidRoutingCap

/-- The regular potential used by the routing coefficient is exactly the
actual high-mode potential plus its common constant. -/
theorem regular_highModes_two (n : ℕ) (hn : 0 < n)
    (R : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : |r| ≤ 1) (x : FSC.Coord d) (i : Fin (n+2)) :
    gaussianAverage (-r) (highModes 2 (fun y => regularAssignment (coordinateRows R) y i)) x.ofLp =
      correctedRegularPotential R r (fun _ _ => 0) x i-1/((n:ℝ)+2) := by
  have hm : ∀ y, |regularAssignment (coordinateRows R) y i| ≤ 1 := by
    intro y
    rw [abs_of_nonneg ((regularAssignment_simplex (coordinateRows R) y).1 i)]
    exact simplex_weight_le_one _ (regularAssignment_simplex (coordinateRows R) y) i
  rw [gaussianAverage_highModes_two_bounded (-r) (by simpa only [abs_neg] using hr)
    _ (regularAssignment_measurable _ i) 1 hm]
  have hmass : (∫ y,regularAssignment (coordinateRows R) y i ∂γFin d)=1/((n:ℝ)+2) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,show standardGaussian (Fin d)=γFin d from rfl] using
      regularAssignment_mass (coordinateRows R) (coordinateRows_gram R hG) i
  have hmoment (j : Fin d) : (∫ y,y j*regularAssignment (coordinateRows R) y i ∂γFin d)=
      referenceScale n*(R i).ofLp j := by
    have hh := regularAssignment_first_moment (coordinateRows R) (coordinateRows_gram R hG)
      (by omega : 3 ≤ n+2) i j
    rw [regular_maximum_mean_eq_canonical n _ (coordinateRows_gram R hG)] at hh
    simpa only [referenceScale,coordinateRows,Nat.cast_add,Nat.cast_ofNat,
      show standardGaussian (Fin d)=γFin d from rfl, show (n:ℝ)+2-1=(n:ℝ)+1 by ring] using hh
  rw [hmass]
  simp_rw [hmoment]
  have hsum : (∑ j,(referenceScale n*(R i).ofLp j)*x.ofLp j)=
      referenceScale n*inner ℝ (R i) x := by
    simp only [PiLp.inner_apply,Real.inner_apply,Finset.mul_sum,mul_assoc]
  rw [hsum]
  have hnoise : gaussianAverage (-r) (fun y => regularAssignment (coordinateRows R) y i) x.ofLp=
      gaussianNoiseOperator (-r) (regularAssignment (fun k => (R k).ofLp)) x.ofLp i := rfl
  rw [hnoise]
  unfold correctedRegularPotential
  ring

open NegativeVotingFan NegativeVotingFanTestedCells NegativeVotingQuadraticMomentPadding
  NegativeVotingCellOUContinuity NegativeVotingRegularOU NegativeVotingCenteredParseval

theorem regularAssignment_eq_cellWeight_ae (n : ℕ)
    (R : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (i : Fin (n+2)) :
    (fun y => regularAssignment (coordinateRows R) y i)=ᵐ[γFin d]cellWeight R 0 i := by
  have hR : Function.Injective R := by
    intro j k he
    by_contra hjk
    have hd := hG j j
    have ho := hG j k
    rw [← he] at ho
    simp only [ite_true] at hd
    simp only [ite_eq_right hjk] at ho
    linarith
  have hm : MeasurePreserving (WithLp.toLp 2) (γFin d) (stdGaussian (FSC.Coord d)) :=
    ⟨by fun_prop,map_pi_eq_stdGaussian⟩
  have hh := hm.quasiMeasurePreserving.ae (weights_eq_winningCell_indicator_ae R hR 0 i)
  filter_upwards [hh] with y hy
  simpa only [zero_weights_eq_regular,WithLp.ofLp_toLp,cellWeight] using hy

/-- The same identity for the literal closed-cell representative used by the
structured cap. The OU identity is pointwise, despite the raw tie convention. -/
theorem regular_cell_highModes_two (n : ℕ) (hn : 0 < n)
    (R : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (x : FSC.Coord d) (i : Fin (n+2)) :
    gaussianAverage (-r) (highModes 2 (cellWeight R 0 i)) x.ofLp =
      correctedRegularPotential R r (fun _ _ => 0) x i-1/((n:ℝ)+2) := by
  have hra : |-r| < 1 := by rw [abs_neg,abs_of_pos hr];exact hr1
  have hae := regularAssignment_eq_cellWeight_ae n R hG i
  have hc (b : Fin d → ℕ) : coeff (fun y => regularAssignment (coordinateRows R) y i) b=
      coeff (cellWeight R 0 i) b := by
    apply integral_congr_ae
    filter_upwards [hae] with y hy
    exact congrArg (fun z => psi b y*z) hy
  have hR : Function.Injective R := by
    intro j k he
    by_contra hjk
    have hd := hG j j
    have ho := hG j k
    rw [← he] at ho
    simp only [ite_true] at hd
    simp only [ite_eq_right hjk] at ho
    linarith
  have hnoise : gaussianAverage (-r) (cellWeight R 0 i) x.ofLp=
      gaussianAverage (-r) (fun y => regularAssignment (coordinateRows R) y i) x.ofLp := by
    rw [gaussianAverage_cellWeight_eq_mass R hR 0 i (-r) hra x]
    have he := gaussianAverage_negative_regularAssignment R r hr hr1 x i
    change gaussianAverage (-r) (fun y => regularAssignment (coordinateRows R) y i) x.ofLp=_ at he
    rw [he]
    congr 1
    funext j
    simp only [Pi.zero_apply,zero_add,NegativeVotingFacetConditionalPlane.scoreOffsets,
      real_inner_smul_right,neg_sq]
    ring
  have hb : ∀ y, |regularAssignment (coordinateRows R) y i| ≤ 1 := by
    intro y
    rw [abs_of_nonneg ((regularAssignment_simplex (coordinateRows R) y).1 i)]
    exact simplex_weight_le_one _ (regularAssignment_simplex (coordinateRows R) y) i
  rw [← regular_highModes_two n hn R hG r (by rw [abs_of_pos hr];exact hr1.le) x i]
  rw [NegativeVotingBoundedOUCellTests.gaussianAverage_highModes_bounded (-r) hra.le
    2 _ (cellWeight_measurable R 0 i) 1 (cellWeight_abs_le R 0 i),
    NegativeVotingBoundedOUCellTests.gaussianAverage_highModes_bounded (-r) hra.le
    2 _ (regularAssignment_measurable _ i) 1 hb,hnoise]
  simp_rw [hc]

open NegativeVotingFanMovingCells NegativeVotingFanScore NegativeVotingCapTail NegativeVotingActualFacetOUTrace
  NegativeVotingRegularReferenceNormalization

/-- Exact cancellation of the regular potential inside the literal residual.
This is a pointwise equality, usable before integration on any normal plane. -/
theorem correctedPotential_actualResidual (n : ℕ) (hn : 0 < n)
    (R : Fin (n+2) → FSC.Coord d)
    (hG : ∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n:ℝ)+2))
    (p : Parameters d (Fin (n+2))) (σ : ℝ) (hσ : 0 < σ)
    (hp : CenteredSingularLowerBound p.1 σ)
    (τ χ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hχ : 0 < χ) (hχ1 : χ < 1)
    (u : Fin (n+2) → FSC.Coord d → ℝ) (x : FSC.Coord d) (i : Fin (n+2)) :
    correctedRegularPotential R ((τ*χ)^2)
        (fun y j => actualResidual τ χ (referenceScale n•R,0) p u j y) x i =
      1/((n:ℝ)+2)+gaussianAverage (-((τ*χ)^2)) (highModes 2 (cellWeight p.1 p.2 i)) x.ofLp-
        ambientAverage (τ*χ) (u i) x := by
  have hs : 0 < τ*χ := mul_pos hτ hχ
  have hs1 : τ*χ < 1 := (mul_lt_mul_of_pos_left hχ1 hτ).trans (by simpa using hτ1)
  have hres := actualResidual_eq_cell_potentials (referenceScale n•R,0) p
    (referenceScale n) σ (referenceScale_pos n) hσ
    (scaled_centered_singular R hG (referenceScale n)) hp i τ χ hτ hτ1 hχ hχ1 u x
  have hc : NegativeVotingFan.winningCell (referenceScale n•R) 0 i=winningCell R 0 i :=
    winningCell_scaled_zero R (referenceScale n) (referenceScale_pos n) i
  rw [hc] at hres
  simp only [smoothedHighModes,ambientAverage_eq_gaussianAverage,ambientHighModes] at hres
  rw [← ambientAverage_eq_gaussianAverage (τ*χ) (u i) x] at hres
  change actualResidual τ χ (referenceScale n•R,0) p u i x=
    gaussianAverage (-((τ*χ)^2)) (highModes 2 (cellWeight p.1 p.2 i)) x.ofLp-
      gaussianAverage (-((τ*χ)^2)) (highModes 2 (cellWeight R 0 i)) x.ofLp-
        ambientAverage (τ*χ) (u i) x at hres
  rw [regular_cell_highModes_two n hn R hG ((τ*χ)^2) (sq_pos_of_pos hs)
    (by nlinarith) x i] at hres
  unfold correctedRegularPotential at hres ⊢
  linarith

end NegativeVotingOwnCentroidSpectralReplacement
