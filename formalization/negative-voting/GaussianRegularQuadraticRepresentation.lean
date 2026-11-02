import GaussianRegularQuadraticSymmetry
import GaussianSecondChaosFacetGradient

/-! Exact canonical regular quadratic tensor and score differences, derived
from actual Gaussian stabilizer invariance, trace zero and row sums. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical

namespace NegativeVotingRegularQuadraticRepresentation

private theorem sum_one_special {m : ℕ} (i : Fin m) (f : Fin m→ℝ) (c : ℝ)
    (hc : ∀ j,j≠i→f j=c) : (∑ j,f j)=f i+((m:ℝ)-1)*c := by
  have hm : 1 ≤ m := by have hi := i.isLt; omega
  have hs : (∑ j∈Finset.univ.erase i,f j)=((m:ℝ)-1)*c := by
    calc
      _ = ∑ j∈Finset.univ.erase i,c :=
        Finset.sum_congr rfl (fun j hj=>hc j (Finset.mem_erase.mp hj).1)
      _ = _ := by simp [Finset.card_erase_of_mem,Nat.cast_sub hm,nsmul_eq_mul]
  have hsplit := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  rw [hs] at hsplit
  linarith

private theorem sum_two_special {m : ℕ} (hm : 2 ≤ m) (i a : Fin m) (hia : i≠a)
    (f : Fin m→ℝ) (c : ℝ) (hc : ∀ j,j≠i→j≠a→f j=c) :
    (∑ j,f j)=f i+f a+((m:ℝ)-2)*c := by
  let s := (Finset.univ.erase i).erase a
  have ha : a∈Finset.univ.erase i := by simp [hia.symm]
  have hcard : s.card=m-2 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem ha,Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp [Nat.sub_sub]
  have hsum : (∑ j∈s,f j)=((m:ℝ)-2)*c := by
    calc
      _ = ∑ j∈s,c := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hc j (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
          (Finset.mem_erase.mp hj).1
      _ = _ := by simp [hcard,Nat.cast_sub hm,nsmul_eq_mul]
  have h1 := Finset.sum_erase_add (Finset.univ.erase i) f ha
  have h2 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  change (∑ j∈s,f j)+f a=∑ j∈Finset.univ.erase i,f j at h1
  rw [hsum] at h1
  linarith

def centeredCoordinate (m : ℕ) (i a : Fin m) : ℝ :=
  (if i=a then 1 else 0)-1/(m:ℝ)

/-- Full entry formula. Unlike the Frobenius corollary, this retains the
rank-one test and its common projection term. -/
theorem entries_of_stabilizer {m : ℕ} (hm : 3 ≤ m) (i : Fin m)
    (q : Fin m→Fin m→ℝ) (hsym : ∀ a b,q a b=q b a)
    (hrow : ∀ a,∑ b,q a b=0) (htrace : ∑ a,q a a=0)
    (hinv : ∀ a b,a≠i→b≠i→∀ j k,q (Equiv.swap a b j) (Equiv.swap a b k)=q j k)
    (a b : Fin m) :
    q a b=((m:ℝ)^2*q i i/(((m:ℝ)-1)*((m:ℝ)-2)))*
      (centeredCoordinate m i a*centeredCoordinate m i b-
        ((if a=b then 1 else 0)-1/(m:ℝ))/(m:ℝ)) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have h0 : (m:ℝ)≠0 := by linarith
  have h1 : (m:ℝ)-1≠0 := by linarith
  have h2 : (m:ℝ)-2≠0 := by linarith
  have hdiag_const (a b : Fin m) (ha : a≠i) (hb : b≠i) : q a a=q b b := by
    simpa only [Equiv.swap_apply_left] using (hinv a b ha hb a a).symm
  have hrow_const (a b : Fin m) (ha : a≠i) (hb : b≠i) : q i a=q i b := by
    simpa only [Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm,Equiv.swap_apply_left]
      using (hinv a b ha hb i a).symm
  have hdiag (a : Fin m) (ha : a≠i) : q a a= -q i i/((m:ℝ)-1) := by
    have he := sum_one_special i (fun k=>q k k) (q a a) (fun k hk=>hdiag_const k a hk ha)
    rw [htrace] at he
    apply (eq_div_iff h1).mpr
    nlinarith
  have hrowi (a : Fin m) (ha : a≠i) : q i a= -q i i/((m:ℝ)-1) := by
    have he := sum_one_special i (fun k=>q i k) (q i a) (fun k hk=>hrow_const k a hk ha)
    rw [hrow i] at he
    apply (eq_div_iff h1).mpr
    nlinarith
  have hoff (a b : Fin m) (ha : a≠i) (hb : b≠i) (hab : a≠b) :
      q a b=2*q i i/(((m:ℝ)-1)*((m:ℝ)-2)) := by
    have hc (k : Fin m) (hk : k≠i) (hka : k≠a) : q a k=q a b := by
      simpa only [Equiv.swap_apply_of_ne_of_ne hab hka.symm,Equiv.swap_apply_left]
        using hinv b k hb hk a b
    have he := sum_two_special (by omega : 2 ≤ m) i a ha.symm (fun k=>q a k) (q a b) hc
    rw [hrow a,hdiag a ha,hsym a i,hrowi a ha] at he
    apply (eq_div_iff (mul_ne_zero h1 h2)).mpr
    field_simp [h1] at he
    nlinarith
  by_cases hai : a=i
  · subst a
    by_cases hbi : b=i
    · subst b
      simp only [centeredCoordinate,eq_self_iff_true,ite_true]
      field_simp [h0,h1,h2]
      ring
    · rw [hrowi b hbi]
      simp only [centeredCoordinate,eq_self_iff_true,ite_true,
        if_neg (Ne.symm hbi)]
      field_simp [h0,h1,h2]
      ring
  · by_cases hbi : b=i
    · subst b
      rw [hsym a i,hrowi a hai]
      simp only [centeredCoordinate,eq_self_iff_true,ite_true,
        if_neg hai,if_neg (Ne.symm hai)]
      field_simp [h0,h1,h2]
      ring
    · by_cases hab : a=b
      · subst b
        rw [hdiag a hai]
        simp only [centeredCoordinate,eq_self_iff_true,ite_true,if_neg (Ne.symm hai)]
        field_simp [h0,h1,h2]
        ring
      · rw [hoff a b hai hbi hab]
        simp only [centeredCoordinate,if_neg (Ne.symm hai),if_neg (Ne.symm hbi),if_neg hab]
        field_simp [h0,h1,h2]
        ring

open NegativeVotingRegularQuadratic

def momentCoefficient (n : ℕ) : ℝ :=
  ((n+2:ℕ):ℝ)^2*moment n 0 0 0/((((n+2:ℕ):ℝ)-1)*(((n+2:ℕ):ℝ)-2))

/-- The invariant entry formula is applied to the actual Gaussian moments;
all finite algebra hypotheses are discharged by geometric theorems. -/
theorem moment_entry_formula (n : ℕ) (hn : 1≤n) (i a b : Fin (n+2)) :
    moment n i a b=momentCoefficient n*
      (centeredCoordinate (n+2) i a*centeredCoordinate (n+2) i b-
        ((if a=b then 1 else 0)-1/((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)) := by
  have hh := entries_of_stabilizer (by omega : 3≤n+2) i (moment n i)
    (moment_symm n i) (moment_row_sum_zero n i) (moment_trace_zero n i)
    (moment_swap_invariant n i) a b
  rw [moment_distinguished_eq n i 0] at hh
  exact hh

def momentScore (n : ℕ) (i : Fin (n+2)) (x : Fin (n+2)→ℝ) : ℝ :=
  ∑ a,∑ b,moment n i a b*(x a*x b-(if a=b then 1 else 0))

theorem momentScore_eq_raw (n : ℕ) (i : Fin (n+2)) (x : Fin (n+2)→ℝ) :
    momentScore n i x=∑ a,∑ b,moment n i a b*(x a*x b) := by
  unfold momentScore
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  have ht : (∑ a,∑ b,moment n i a b*(if a=b then 1 else 0))=0 := by
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    exact moment_trace_zero n i
  rw [ht,sub_zero]

theorem centeredCoordinate_dot {m : ℕ} (i : Fin m) (x : Fin m→ℝ) :
    (∑ a,centeredCoordinate m i a*x a)=x i-(∑ a,x a)/(m:ℝ) := by
  simp only [centeredCoordinate,sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,←Finset.mul_sum]
  ring

theorem rank_one_form {m : ℕ} (u x : Fin m→ℝ) :
    (∑ a,∑ b,u a*u b*(x a*x b))=(∑ a,u a*x a)^2 := by
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Actual canonical quadratic score gaps are differences of centered
coordinate squares. The common projection term and trace term cancel. -/
theorem momentScore_difference (n : ℕ) (hn : 1≤n) (i j : Fin (n+2))
    (x : Fin (n+2)→ℝ) :
    momentScore n i x-momentScore n j x=
      momentCoefficient n*((x i-(∑ a,x a)/((n+2:ℕ):ℝ))^2-
        (x j-(∑ a,x a)/((n+2:ℕ):ℝ))^2) := by
  rw [momentScore_eq_raw,momentScore_eq_raw]
  calc
    _ = momentCoefficient n*
        ((∑ a,∑ b,centeredCoordinate (n+2) i a*centeredCoordinate (n+2) i b*(x a*x b))-
         (∑ a,∑ b,centeredCoordinate (n+2) j a*centeredCoordinate (n+2) j b*(x a*x b))) := by
      simp only [Finset.mul_sum,mul_sub,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [moment_entry_formula n hn i a b,moment_entry_formula n hn j a b]
      ring
    _ = _ := by rw [rank_one_form,rank_one_form,centeredCoordinate_dot,centeredCoordinate_dot]

open NegativeVotingFanQuadraticMoments NegativeVotingSecondChaosFacetGradient
  NegativeVotingFan NegativeVotingFanTestedCells NegativeVotingRegularMaximum
  NegativeVoting NegativeVotingModern OAI.MinUncut.GaussianHermite

/-- The product-coordinate moments are the actual Euclidean winning-cell
second-chaos tensor, including its centering correction. -/
theorem unitRows_secondMomentTensor (n : ℕ) (i a b : Fin (n+2)) :
    secondMomentTensor (unitRows n) (fun _=>0) i a b=moment n i a b := by
  unfold NegativeVotingRegularQuadratic.moment quadraticMoment
  change _=(∫ x,maxWeights x i*quadraticCoordinate a b x
    ∂standardGaussian (Fin (n+2)))
  rw [integral_standardGaussian_eq_euclidean]
  simp only [quadraticCoordinate]
  simp_rw [←unitRows_weights n]
  rw [integral_weights_mul_eq_cell _ (unitRows_injective n)]
  rfl

theorem unitRows_quadraticLabelTest (n : ℕ) (i : Fin (n+2)) (x : FSC.Coord (n+2)) :
    quadraticLabelTest (unitRows n) (fun _=>0) i x=momentScore n i x.ofLp := by
  simp only [quadraticLabelTest,unitRows_secondMomentTensor,tensorTest,momentScore]

/-- Literal tested-cell score identity, with all Gaussian moments discharged. -/
theorem unitRows_quadraticLabelTest_difference (n : ℕ) (hn : 1≤n)
    (i j : Fin (n+2)) (x : FSC.Coord (n+2)) :
    quadraticLabelTest (unitRows n) (fun _=>0) i x-
        quadraticLabelTest (unitRows n) (fun _=>0) j x=
      momentCoefficient n*((x i-(∑ a,x a)/((n+2:ℕ):ℝ))^2-
        (x j-(∑ a,x a)/((n+2:ℕ):ℝ))^2) := by
  rw [unitRows_quadraticLabelTest,unitRows_quadraticLabelTest]
  exact momentScore_difference n hn i j x.ofLp

/-- Centered canonical rows as actual Euclidean vectors. -/
def canonicalEuclideanRows (n : ℕ) (i : Fin (n+2)) : FSC.Coord (n+2) :=
  WithLp.toLp 2 (canonicalRows n i)

theorem canonicalEuclideanRows_inner (n : ℕ) (i : Fin (n+2))
    (x : FSC.Coord (n+2)) :
    inner ℝ (canonicalEuclideanRows n i) x=
      x i-(∑ a,x a)/((n+2:ℕ):ℝ) := by
  simpa only [canonicalEuclideanRows,PiLp.inner_apply,WithLp.ofLp_toLp,
    Real.inner_apply,coordinateMean,Nat.cast_add,Nat.cast_ofNat]
    using canonicalRows_score n i x.ofLp

theorem canonicalEuclideanRows_winningCell (n : ℕ) (i : Fin (n+2)) :
    winningCell (canonicalEuclideanRows n) (fun _=>0) i=
      winningCell (unitRows n) (fun _=>0) i := by
  ext x
  simp only [winningCell,Set.mem_setOf_eq,scores,add_zero,
    canonicalEuclideanRows_inner,unitRows,EuclideanSpace.inner_single_left]
  simp only [sub_le_sub_iff_right,map_one,one_mul]

theorem canonicalEuclideanRows_secondMomentTensor (n : ℕ) (i a b : Fin (n+2)) :
    secondMomentTensor (canonicalEuclideanRows n) (fun _=>0) i a b=moment n i a b := by
  rw [←unitRows_secondMomentTensor]
  simp only [secondMomentTensor,canonicalEuclideanRows_winningCell]

/-- The centered regular realization has the literal score-gap formula in
its own row scores. No tensor representation is assumed in this statement. -/
theorem canonicalEuclideanRows_quadraticLabelTest_difference (n : ℕ) (hn : 1≤n)
    (i j : Fin (n+2)) (x : FSC.Coord (n+2)) :
    quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) i x-
        quadraticLabelTest (canonicalEuclideanRows n) (fun _=>0) j x=
      momentCoefficient n*((inner ℝ (canonicalEuclideanRows n i) x)^2-
        (inner ℝ (canonicalEuclideanRows n j) x)^2) := by
  rw [canonicalEuclideanRows_inner,canonicalEuclideanRows_inner]
  simp only [quadraticLabelTest,canonicalEuclideanRows_secondMomentTensor,tensorTest]
  exact momentScore_difference n hn i j x.ofLp

end NegativeVotingRegularQuadraticRepresentation
