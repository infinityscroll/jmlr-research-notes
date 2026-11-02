import GaussianPolynomialFacetGeometricTrace
import GaussianRareLabelHighChaos
import GaussianBoundedOUCellTests

/-! Pointwise covariance of the actual low-degree Hermite projection under
Gaussian-preserving linear involutions. No projection-commutation axiom. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin
open scoped BigOperators RealInnerProductSpace Classical ENNReal
namespace NegativeVotingLowModeIsometry
open NegativeVotingProjection NegativeVotingPolynomialDegree NegativeVotingFiniteHermite
  NegativeVotingPolynomialFacetGeometricTrace NegativeVotingRareLabelHighChaos
  NegativeVotingModern NegativeVotingAffine OAI.MinUncut.GaussianHermite
variable {d : ℕ}

theorem psi_single_one (i : Fin d) (x : Fin d→ℝ) : psi (Pi.single i 1) x=x i := by
  unfold psi
  rw [Finset.prod_eq_single i]
  · simp [H,he_one]
  · intro j _ hji
    simp [hji,H]
  · simp

theorem linear_coordinate_mem (T : (Fin d→ℝ)→ₗ[ℝ](Fin d→ℝ)) (i : Fin d) :
    (fun x=>T x i) ∈ polynomialSpace 1 := by
  simpa only [mul_one,LinearMap.comp_apply,LinearMap.proj_apply] using linear_mul_mem (one_mem (κ:=Fin d) 0)
    ((LinearMap.proj i).comp T)

theorem linear_quadratic_mem (T : (Fin d→ℝ)→ₗ[ℝ](Fin d→ℝ)) (i j : Fin d) :
    (fun x=>T x i*T x j) ∈ polynomialSpace 2 :=
  linear_mul_mem (linear_coordinate_mem T j) ((LinearMap.proj i).comp T)

/-- Linear substitution preserves all actual Hermite polynomials of degree
at most two; the low cutoff is verified from their explicit formulas. -/
theorem psi_comp_linear_low_mem (T : (Fin d→ℝ)→ₗ[ℝ](Fin d→ℝ))
    (a : Fin d→ℕ) (ha : degree a<3) :
    (fun x=>psi a (T x)) ∈ polynomialSpace 2 := by
  by_cases h0 : degree a=0
  · rw [(degree_zero_iff a).mp h0]
    simpa [psi,H] using one_mem (κ:=Fin d) 2
  by_cases h1 : degree a=1
  · obtain ⟨i,rfl⟩ := (degree_one_iff a).mp h1
    simp only [psi_single_one]
    exact polynomialSpace_mono (by decide : 1≤2) (linear_coordinate_mem T i)
  have h2 : degree a=2 := by omega
  have hh (z : Sym2 (Fin d)) : (fun x=>psi (degreeTwoEquiv z).1 (T x)) ∈ polynomialSpace 2 := by
    induction z using Sym2.inductionOn with
    | hf i j =>
      rw [degreeTwoEquiv_pair]
      by_cases hij : i=j
      · subst j
        have he : (Pi.single i 1+Pi.single i 1 : Fin d→ℕ)=Pi.single i 2 := by
          funext l
          by_cases hl : l=i <;> simp [hl]
        rw [he]
        simp only [psi_single_two]
        convert (polynomialSpace 2).smul_mem (Real.sqrt 2)⁻¹
          ((polynomialSpace 2).sub_mem (linear_quadratic_mem T i i) (one_mem 2)) using 1
        funext x
        simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,quadraticCoordinate,ite_true]
        ring
      · simp only [psi_two_distinct i j hij]
        simpa only [quadraticCoordinate,if_neg hij,sub_zero] using linear_quadratic_mem T i j
  simpa only [degreeTwoEquiv.apply_symm_apply] using hh (degreeTwoEquiv.symm ⟨a,h2⟩)

theorem projectModes_comp_linear_mem (T : (Fin d→ℝ)→ₗ[ℝ](Fin d→ℝ))
    (f : (Fin d→ℝ)→ℝ) :
    (fun x=>projectModes (lowerModes 3) f (T x)) ∈ polynomialSpace 2 := by
  have hh := (polynomialSpace 2).sum_mem (fun a (ha:a∈lowerModes 3)=>
    (polynomialSpace 2).smul_mem (coeff f a)
      (psi_comp_linear_low_mem T a ((mem_lowerModes_iff 3 a).mp ha)))
  convert hh using 1
  funext x
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,projectModes]

theorem projectModes_polynomial_eq (p : (Fin d→ℝ)→ℝ) (hp : p∈polynomialSpace 2) :
    projectModes (lowerModes 3) p=p := by
  obtain ⟨c,rfl⟩ := exists_normalized_expansion hp
  funext x
  change (∑ a∈lowerModes 3,coeff (hermiteSum (lowerModes 3) c) a*psi a x)=
    ∑ a∈lowerModes 3,c a*psi a x
  apply Finset.sum_congr rfl
  intro a ha
  rw [coeff_hermiteSum,if_pos ha]

theorem low_polynomial_highModes_pairing_zero (p f : (Fin d→ℝ)→ℝ)
    (hp : p∈polynomialSpace 2) (hf : MemLp f 2 (γFin d)) :
    (∫ x,p x*highModes 3 f x ∂γFin d)=0 := by
  obtain ⟨c,rfl⟩ := exists_normalized_expansion hp
  simp only [hermiteSum,Finset.sum_mul]
  have hint (a : Fin d→ℕ) : Integrable (fun x=>c a*psi a x*highModes 3 f x) (γFin d) := by
    change Integrable (fun x=>c a*psi a x*highModes 3 f x) (γpi (Fin d))
    simpa only [Pi.mul_apply,mul_assoc] using
      ((memLp_psi a).integrable_mul (highModes_memLp 3 f hf)).const_mul (c a)
  rw [integral_finsetSum (lowerModes 3) (fun a _=>hint a)]
  apply Finset.sum_eq_zero
  intro a ha
  rw [show (fun x=>c a*psi a x*highModes 3 f x)=fun x=>c a*(psi a x*highModes 3 f x) by funext x;ring,
    integral_const_mul]
  change c a*coeff (highModes 3 f) a=0
  rw [highModes_coeff_vanish 3 f hf a ((mem_lowerModes_iff 3 a).mp ha),mul_zero]

/-- The actual finite projection commutes pointwise, not just in the L2 quotient. -/
theorem projectModes_comp_involution (T : (Fin d→ℝ)→ₗ[ℝ](Fin d→ℝ))
    (hT : MeasurePreserving T (γFin d) (γFin d)) (hinv : Function.Involutive T)
    (f : (Fin d→ℝ)→ℝ) (hf : MemLp f 2 (γFin d)) :
    projectModes (lowerModes 3) (fun x=>f (T x))=
      fun x=>projectModes (lowerModes 3) f (T x) := by
  let p := fun x=>projectModes (lowerModes 3) f (T x)
  have hp := projectModes_comp_linear_mem T f
  have hpm : MemLp p 2 (γFin d) := (projectModes_memLp (lowerModes 3) f).comp_measurePreserving hT
  have hfm : MemLp (fun x=>f (T x)) 2 (γFin d) := hf.comp_measurePreserving hT
  have hc (a : Fin d→ℕ) (ha:a∈lowerModes 3) : coeff (fun x=>f (T x)) a=coeff p a := by
    have hzero := low_polynomial_highModes_pairing_zero (fun x=>psi a (T x)) f
      (psi_comp_linear_low_mem T a ((mem_lowerModes_iff 3 a).mp ha)) hf
    have hg : Integrable (fun x=>psi a x*highModes 3 f (T x)) (γFin d) :=
      (memLp_psi a).integrable_mul ((highModes_memLp 3 f hf).comp_measurePreserving hT)
    have hi := hT.integral_comp (T.continuous_of_finiteDimensional.measurableEmbedding hinv.injective)
      (fun x=>psi a x*highModes 3 f (T x))
    try simp only [Function.comp_def,hinv] at hi
    have hz : (∫ x,psi a x*(f (T x)-p x) ∂γFin d)=0 := by
      change (∫ x,psi a x*highModes 3 f (T x) ∂γFin d)=0
      calc
        _ = ∫ x,psi a (T x)*highModes 3 f (T (T x)) ∂γFin d := hi.symm
        _ = ∫ x,psi a (T x)*highModes 3 f x ∂γFin d := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hinv x]
        _ = 0 := hzero
    have hd := coeff_sub hfm hpm a
    change (∫ x,psi a x*(f (T x)-p x) ∂γFin d)=_ at hd
    rw [hz] at hd
    linarith only [hd]
  calc
    _ = projectModes (lowerModes 3) p := by
      funext x
      unfold projectModes
      exact Finset.sum_congr rfl (fun a ha=>by rw [hc a ha])
    _ = _ := projectModes_polynomial_eq p hp

 theorem highModes_comp_involution (T : (Fin d→ℝ)→ₗ[ℝ](Fin d→ℝ))
    (hT : MeasurePreserving T (γFin d) (γFin d)) (hinv : Function.Involutive T)
    (f : (Fin d→ℝ)→ℝ) (hf : MemLp f 2 (γFin d)) :
    highModes 3 (fun x=>f (T x))=fun x=>highModes 3 f (T x) := by
  unfold highModes removeModes
  rw [projectModes_comp_involution T hT hinv f hf]
end NegativeVotingLowModeIsometry
