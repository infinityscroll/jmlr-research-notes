import GaussianEqualRowMaximumComparison
import GaussianSecondChaos
import GaussianRegularSpectatorRepresentation

/-! The literal equal-row quadratic test tensor and its sharp regular
upper denominator. No inverse Gram matrix or full-rank hypothesis is used. -/
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators Classical RealInnerProductSpace
namespace NegativeVotingEqualRowQuadraticCertificate
open NegativeVoting NegativeVotingModern NegativeVotingRegularSpectatorRepresentation
variable {m : ℕ} [NeZero m] {κ : Type*} [Fintype κ] [DecidableEq κ]

def equalRowTensor (Z : Fin m→κ→ℝ) (i : Fin m) (j k : κ) : ℝ :=
  Z i j*Z i k-(∑ l,Z l j*Z l k)/(m:ℝ)

def rowDot (Z : Fin m→κ→ℝ) (i l : Fin m) : ℝ := ∑ j,Z i j*Z l j

def tensorSquare (Z : Fin m→κ→ℝ) : ℝ := ∑ i,∑ j,∑ k,(equalRowTensor Z i j k)^2

def gramSquare (Z : Fin m→κ→ℝ) : ℝ := ∑ i,∑ l,(rowDot Z i l)^2

theorem scalar_centered_square (a : Fin m→ℝ) :
    (m:ℝ)*(∑ i,(a i-(∑ l,a l)/(m:ℝ))^2)=
      (m:ℝ)*(∑ i,(a i)^2)-(∑ i,a i)^2 := by
  have hm0 : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_mul,←Finset.mul_sum]
  field_simp
  <;> ring

theorem rankOne_cross_square (Z : Fin m→κ→ℝ) (i l : Fin m) :
    (∑ j,∑ k,(Z i j*Z i k)*(Z l j*Z l k))=(rowDot Z i l)^2 := by
  unfold rowDot
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem covariance_square_eq_gram_square (Z : Fin m→κ→ℝ) :
    (∑ j,∑ k,(∑ i,Z i j*Z i k)^2)=gramSquare Z := by
  simp_rw [pow_two,Finset.sum_mul,Finset.mul_sum]
  calc
    _ = ∑ j,∑ i,∑ k,∑ l,(Z i j*Z i k)*(Z l j*Z l k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i,∑ j,∑ l,∑ k,(Z i j*Z i k)*(Z l j*Z l k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i,∑ l,∑ j,∑ k,(Z i j*Z i k)*(Z l j*Z l k) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [rankOne_cross_square];rfl

theorem tensor_square_identity (Z : Fin m→κ→ℝ) (q : ℝ)
    (hZ : ∀ i,∑ j,(Z i j)^2=q) :
    (m:ℝ)*tensorSquare Z=(m:ℝ)^2*q^2-gramSquare Z := by
  have hreorder : tensorSquare Z=∑ j,∑ k,∑ i,(equalRowTensor Z i j k)^2 := by
    unfold tensorSquare
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  have he : (∑ j,∑ k,∑ i,(Z i j*Z i k)^2)=(m:ℝ)*q^2 := by
    calc
      _ = ∑ j,∑ i,∑ k,(Z i j*Z i k)^2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = ∑ i,∑ j,∑ k,(Z i j*Z i k)^2 := by rw [Finset.sum_comm]
      _ = _ := by
        have hi (i:Fin m) : (∑ j,∑ k,(Z i j*Z i k)^2)=q^2 := by
          simp_rw [mul_pow,←Finset.mul_sum,hZ,←Finset.sum_mul,hZ]
          ring
        simp_rw [hi]
        simp
  calc
    _ = ∑ j,∑ k,(m:ℝ)*(∑ i,(equalRowTensor Z i j k)^2) := by
      rw [hreorder,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j,∑ k,((m:ℝ)*(∑ i,(Z i j*Z i k)^2)-(∑ i,Z i j*Z i k)^2) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact scalar_centered_square (fun i=>Z i j*Z i k)
    _ = (m:ℝ)*(∑ j,∑ k,∑ i,(Z i j*Z i k)^2)-gramSquare Z := by
      simp_rw [Finset.sum_sub_distrib]
      rw [covariance_square_eq_gram_square]
      simp_rw [←Finset.mul_sum]
    _ = _ := by rw [he];ring

theorem gram_square_lower (hm : 2 ≤ m) (Z : Fin m→κ→ℝ) (q : ℝ)
    (hZ : ∀ i,∑ j,(Z i j)^2=q) (hcenter : ∀ j,∑ i,Z i j=0) :
    (m:ℝ)^2*q^2 ≤ ((m:ℝ)-1)*gramSquare Z := by
  have hdiag i : rowDot Z i i=q := by simpa only [rowDot,←pow_two] using hZ i
  have hrow i : ∑ l,rowDot Z i l=0 := by
    unfold rowDot
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum,hcenter,mul_zero]
    simp
  have hoff i : (∑ l∈Finset.univ.erase i,rowDot Z i l)=-q := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) (fun l=>rowDot Z i l) (Finset.mem_univ i)
    rw [hrow,hdiag] at he
    linarith
  have hrowSq i : q^2 ≤ ((m:ℝ)-1)*(∑ l∈Finset.univ.erase i,(rowDot Z i l)^2) := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase i)
      (fun _ : Fin m=>(1:ℝ)) (fun l=>rowDot Z i l)
    simp only [one_mul,one_pow,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,hoff,neg_sq] at hh
    convert hh using 1
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    simp
  have hs := Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hrowSq i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  rw [←Finset.mul_sum] at hs
  have he : gramSquare Z=(m:ℝ)*q^2+∑ i,∑ l∈Finset.univ.erase i,(rowDot Z i l)^2 := by
    unfold gramSquare
    have hi i : (∑ l,(rowDot Z i l)^2)=q^2+∑ l∈Finset.univ.erase i,(rowDot Z i l)^2 := by
      rw [←Finset.sum_erase_add _ _ (Finset.mem_univ i),hdiag]
      ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib]
    simp
  rw [he]
  nlinarith only [hs]

theorem tensor_square_sharp (hm : 2 ≤ m) (Z : Fin m→κ→ℝ) (q : ℝ)
    (hZ : ∀ i,∑ j,(Z i j)^2=q) (hcenter : ∀ j,∑ i,Z i j=0) :
    tensorSquare Z ≤ (m:ℝ)*((m:ℝ)-2)*q^2/((m:ℝ)-1) := by
  have hm0 : (0:ℝ)< m := by exact_mod_cast (by omega : 0< m)
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by
    have : (2:ℝ)≤ m := by exact_mod_cast hm
    linarith
  apply (le_div_iff₀ hm1).mpr
  apply (mul_le_mul_iff_right₀ hm0).mp
  have hi := congrArg (fun t:ℝ=>((m:ℝ)-1)*t) (tensor_square_identity Z q hZ)
  have hg := gram_square_lower hm Z q hZ hcenter
  nlinarith only [hi,hg]

def regularDenominator (m : ℕ) (α : ℝ) : ℝ :=
  α^4*((m:ℝ)-1)*((m:ℝ)-2)/(m:ℝ)

theorem regularDenominator_pos (hm : 3 ≤ m) (α : ℝ) (hα : 0<α) :
    0<regularDenominator m α := by
  have hm' : (3:ℝ)≤ m := by exact_mod_cast hm
  have h1 : (0:ℝ)<(m:ℝ)-1 := by linarith
  have h2 : (0:ℝ)<(m:ℝ)-2 := by linarith
  have h0 : (0:ℝ)< m := by linarith
  unfold regularDenominator
  positivity

theorem tensor_square_le_regular (hm : 3 ≤ m) (Z : Fin m→κ→ℝ) (α : ℝ)
    (hZ : ∀ i,∑ j,(Z i j)^2=α^2*(1-1/(m:ℝ)))
    (hcenter : ∀ j,∑ i,Z i j=0) :
    tensorSquare Z ≤ regularDenominator m α := by
  have hh := tensor_square_sharp (by omega) Z _ hZ hcenter
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
  have hm1 : (m:ℝ)-1≠0 := by
    have : (3:ℝ)≤ m := by exact_mod_cast hm
    linarith
  convert hh using 1
  unfold regularDenominator
  field_simp
  <;> ring

def centeredRowTest (z : κ→ℝ) (x : κ→ℝ) : ℝ :=
  ∑ j,∑ k,z j*z k*quadraticCoordinate j k x

theorem centeredRowTest_formula (z x : κ→ℝ) :
    centeredRowTest z x=(∑ j,z j*x j)^2-∑ j,(z j)^2 := by
  unfold centeredRowTest quadraticCoordinate
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  congr 1
  · rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp [←pow_two]

theorem centeredRowTest_integrable (z : κ→ℝ) :
    Integrable (centeredRowTest z) (γpi κ) := by
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  exact ((quadraticCoordinate_memLp j k).integrable (by norm_num)).const_mul _

theorem centeredRowTest_integral (z : κ→ℝ) :
    (∫ x,centeredRowTest z x ∂γpi κ)=0 := by
  have ht j k : Integrable (fun x=>z j*z k*quadraticCoordinate j k x) (γpi κ) :=
    ((quadraticCoordinate_memLp j k).integrable (by norm_num)).const_mul _
  unfold centeredRowTest
  rw [integral_finsetSum _ (fun j _=>integrable_finsetSum _ (fun k _=>ht j k))]
  simp_rw [integral_finsetSum _ (fun k _=>ht _ k),integral_const_mul,
    quadraticCoordinate_integral_zero,mul_zero,Finset.sum_const_zero]

theorem weighted_centeredRowTest_integrable (f : (κ→ℝ)→ℝ)
    (hf : MemLp f 2 (γpi κ)) (z : κ→ℝ) :
    Integrable (fun x=>f x*centeredRowTest z x) (γpi κ) := by
  have he (x:κ→ℝ) : f x*centeredRowTest z x=
      ∑ j,∑ k,(z j*z k)*(f x*quadraticCoordinate j k x) := by
    simp only [centeredRowTest,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun j _=>integrable_finsetSum _
    (fun k _=>(quadratic_moment_integrable hf j k).const_mul _))

theorem equalRowTensor_test (Z : Fin m→κ→ℝ) (i : Fin m) (x : κ→ℝ) :
    (∑ j,∑ k,equalRowTensor Z i j k*quadraticCoordinate j k x)=
      centeredRowTest (Z i) x-(∑ l,centeredRowTest (Z l) x)/(m:ℝ) := by
  simp_rw [equalRowTensor,sub_mul,Finset.sum_sub_distrib]
  unfold centeredRowTest
  congr 1
  simp_rw [div_mul_eq_mul_div,←Finset.sum_div,Finset.sum_mul]
  congr 1
  calc
    _ = ∑ j,∑ l,∑ k,(Z l j*Z l k)*quadraticCoordinate j k x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

def weightedRowSquare (Z : Fin m→κ→ℝ) (f : (κ→ℝ)→Fin m→ℝ) (x : κ→ℝ) : ℝ :=
  ∑ i,f x i*(∑ j,Z i j*x j)^2

theorem weightedRowSquare_integrable (Z : Fin m→κ→ℝ)
    (f : (κ→ℝ)→Fin m→ℝ) (hf : ∀ i,MemLp (fun x=>f x i) 2 (γpi κ)) :
    Integrable (weightedRowSquare Z f) (γpi κ) := by
  apply integrable_finsetSum
  intro i _
  have he (x:κ→ℝ) : f x i*(∑ j,Z i j*x j)^2=
      f x i*centeredRowTest (Z i) x+(∑ j,(Z i j)^2)*f x i := by
    rw [centeredRowTest_formula]
    ring
  simp_rw [he]
  exact (weighted_centeredRowTest_integrable _ (hf i) _).add
    (((hf i).integrable (by norm_num)).const_mul _)

theorem equalRowTensor_pairing (Z : Fin m→κ→ℝ) (q : ℝ)
    (hZ : ∀ i,∑ j,(Z i j)^2=q)
    (f : (κ→ℝ)→Fin m→ℝ) (hf : ∀ i,MemLp (fun x=>f x i) 2 (γpi κ))
    (hsum : ∀ᵐ x ∂γpi κ,∑ i,f x i=1) :
    quadraticTestPairing f (equalRowTensor Z)=
      (∫ x,weightedRowSquare Z f x ∂γpi κ)-q := by
  have he (x:κ→ℝ) (hx:∑ i,f x i=1) :
      (∑ i,∑ j,∑ k,equalRowTensor Z i j k*(f x i*quadraticCoordinate j k x))=
        weightedRowSquare Z f x-q-(∑ l,centeredRowTest (Z l) x)/(m:ℝ) := by
    calc
      _ = ∑ i,f x i*(∑ j,∑ k,equalRowTensor Z i j k*quadraticCoordinate j k x) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ i,f x i*(centeredRowTest (Z i) x-(∑ l,centeredRowTest (Z l) x)/(m:ℝ)) := by
        simp_rw [equalRowTensor_test]
      _ = (∑ i,f x i*centeredRowTest (Z i) x)-(∑ l,centeredRowTest (Z l) x)/(m:ℝ) := by
        simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hx,one_mul]
      _ = _ := by
        simp_rw [centeredRowTest_formula,hZ,mul_sub,Finset.sum_sub_distrib]
        rw [←Finset.sum_mul,hx,one_mul]
        rfl
  have hmean : Integrable (fun x=>(∑ l,centeredRowTest (Z l) x)/(m:ℝ)) (γpi κ) :=
    (integrable_finsetSum _ (fun l _=>centeredRowTest_integrable (Z l))).div_const _
  have hmeanz : (∫ x,(∑ l,centeredRowTest (Z l) x)/(m:ℝ) ∂γpi κ)=0 := by
    rw [integral_div,integral_finsetSum _ (fun l _=>centeredRowTest_integrable (Z l))]
    simp only [centeredRowTest_integral,Finset.sum_const_zero,zero_div]
  rw [quadraticTestPairing]
  calc
    _ = ∫ x,weightedRowSquare Z f x-q-(∑ l,centeredRowTest (Z l) x)/(m:ℝ) ∂γpi κ := by
      apply integral_congr_ae
      filter_upwards [hsum] with x hx
      exact he x hx
    _ = _ := by
      have hb : Integrable (fun x=>weightedRowSquare Z f x-q) (γpi κ) :=
        (weightedRowSquare_integrable Z f hf).sub (integrable_const q)
      rw [integral_sub hb hmean,
        integral_sub (weightedRowSquare_integrable Z f hf) (integrable_const q),hmeanz]
      simp

/-- The actual second-chaos certificate, with the regular denominator even
when the equal-row test tensor is degenerate. The exterior geometric proxy
and calibrated row-payment estimate are not assumed or encoded here. -/
theorem equal_row_quadratic_certificate [LinearOrder κ]
    (hm : 3 ≤ m) (Z : Fin m→κ→ℝ) (α : ℝ) (hα : 0<α)
    (hZ : ∀ i,∑ j,(Z i j)^2=α^2*(1-1/(m:ℝ)))
    (hcenter : ∀ j,∑ i,Z i j=0)
    (f : (κ→ℝ)→Fin m→ℝ) (hf : ∀ i,MemLp (fun x=>f x i) 2 (γpi κ))
    (hsum : ∀ᵐ x ∂γpi κ,∑ i,f x i=1) :
    (max ((∫ x,weightedRowSquare Z f x ∂γpi κ)-α^2*(1-1/(m:ℝ))) 0)^2 /
      (2*regularDenominator m α) ≤ chaosEnergy f 2 := by
  have hp := quadratic_test_pairing_bound f hf (equalRowTensor Z)
  rw [equalRowTensor_pairing Z _ hZ f hf hsum] at hp
  change _ ≤ 2*chaosEnergy f 2*tensorSquare Z at hp
  have hT := tensor_square_le_regular hm Z α hZ hcenter
  have hA := chaosEnergy_nonneg f 2
  have hden := regularDenominator_pos hm α hα
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hden)).mpr
  have hmax (t:ℝ) : (max t 0)^2≤t^2 := by
    by_cases ht : 0≤t
    · rw [max_eq_left ht]
    · rw [max_eq_right (le_of_not_ge ht)]
      simpa using sq_nonneg t
  have hc := mul_le_mul_of_nonneg_left hT (mul_nonneg (by norm_num : (0:ℝ)≤2) hA)
  nlinarith [hmax ((∫ x,weightedRowSquare Z f x ∂γpi κ)-α^2*(1-1/(m:ℝ)))]

/-- Measurable fractional assignments need no separate Gaussian moment input. -/
theorem ae_simplex_equal_row_quadratic_certificate [LinearOrder κ]
    (hm : 3 ≤ m) (Z : Fin m→κ→ℝ) (α : ℝ) (hα : 0<α)
    (hZ : ∀ i,∑ j,(Z i j)^2=α^2*(1-1/(m:ℝ)))
    (hcenter : ∀ j,∑ i,Z i j=0)
    (f : (κ→ℝ)→Fin m→ℝ) (hf : ∀ i,AEMeasurable (fun x=>f x i) (γpi κ))
    (h0 : ∀ᵐ x ∂γpi κ,∀ i,0≤f x i)
    (hsum : ∀ᵐ x ∂γpi κ,∑ i,f x i=1) :
    (max ((∫ x,weightedRowSquare Z f x ∂γpi κ)-α^2*(1-1/(m:ℝ))) 0)^2 /
      (2*regularDenominator m α) ≤ chaosEnergy f 2 := by
  have hf2 i : MemLp (fun x=>f x i) 2 (γpi κ) := by
    refine MemLp.of_bound (hf i).aestronglyMeasurable 1 ?_
    filter_upwards [h0,hsum] with x hx0 hxsum
    rw [Real.norm_eq_abs,abs_of_nonneg (hx0 i)]
    calc
      f x i ≤ ∑ j,f x j := Finset.single_le_sum (fun j _=>hx0 j) (Finset.mem_univ i)
      _ = 1 := hxsum
  exact equal_row_quadratic_certificate hm Z α hα hZ hcenter f hf2 hsum

/-- Coordinate-free equal-row hypotheses on the actual Euclidean proxy.
The finite coordinates only express its literal Gaussian linear observables. -/
theorem ae_simplex_equal_row_certificate_euclidean [LinearOrder κ]
    (hm : 3 ≤ m) (Z : Fin m→EuclideanSpace ℝ κ) (α : ℝ) (hα : 0<α)
    (hZ : ∀ i,‖Z i‖^2=α^2*(1-1/(m:ℝ))) (hcenter : ∑ i,Z i=0)
    (f : (κ→ℝ)→Fin m→ℝ) (hf : ∀ i,AEMeasurable (fun x=>f x i) (γpi κ))
    (h0 : ∀ᵐ x ∂γpi κ,∀ i,0≤f x i)
    (hsum : ∀ᵐ x ∂γpi κ,∑ i,f x i=1) :
    (max ((∫ x,∑ i,f x i*(∑ j,Z i j*x j)^2 ∂γpi κ)-α^2*(1-1/(m:ℝ))) 0)^2 /
      (2*regularDenominator m α) ≤ chaosEnergy f 2 := by
  apply ae_simplex_equal_row_quadratic_certificate hm (fun i j=>Z i j) α hα
    (fun i=>by simpa only [EuclideanSpace.real_norm_sq_eq] using hZ i) ?_ f hf h0 hsum
  intro j
  have hh := congrArg (fun z:EuclideanSpace ℝ κ=>z j) hcenter
  simpa using hh

end NegativeVotingEqualRowQuadraticCertificate
