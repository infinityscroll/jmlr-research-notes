import GaussianPolynomialFacetGeometricTrace
import GaussianOperatorHSNorm
import GaussianCovarianceCoercivity

/-! Dimension-free ambient estimates for the literal Gaussian affine transport
scores. The trace cancellation is established for the actual Gaussian integral. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Classical ENNReal
open OAI.MinUncut.GaussianHermite NegativeVotingModern
open NegativeVotingPolynomialDegree NegativeVotingPolynomialFacetTrace
open NegativeVotingPolynomialFacetGeometricTrace NegativeVotingFiniteHermite
open NegativeVotingChaosDecay NegativeVotingProjection NegativeVotingHypercontractivity
open NegativeVotingSmoothingComposition NegativeVotingNormalTrace GaussianFin
open NegativeVotingAffineLogMassBound NegativeVotingAffineNormControl

namespace NegativeVotingQuadraticBulkNorm
variable {d : ℕ}

def toEuclideanLinear : (Fin d→ℝ)→ₗ[ℝ] FSC.Coord d where
  toFun := WithLp.toLp 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def quadraticScore (A : FSC.Coord d→L[ℝ] FSC.Coord d) (x : FSC.Coord d) : ℝ :=
  inner ℝ x (A x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap

theorem quadraticScore_degree (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    (fun x => quadraticScore A (WithLp.toLp 2 x)) ∈ polynomialSpace 2 := by
  simpa only [quadraticScore,toEuclideanLinear,LinearMap.coe_mk,AddHom.coe_mk,
    inner_zero_left,add_zero] using massBulk_expression_mem
    (toEuclideanLinear (d:=d)) A 0

theorem secondChaos_le_integral_sq {f : (Fin d→ℝ)→ℝ} (hf : MemLp f 2 (γFin d)) :
    chaosEnergy (fun x (_:Unit) => f x) 2 ≤ ∫ x, f x^2 ∂γFin d := by
  have hs := coefficient_energy_hasSum_of_memLp hf
  have hh := Summable.tsum_le_tsum_of_inj
    (fun a : {a : Fin d→ℕ // degree a=2} => a.1) Subtype.coe_injective
    (fun a _ => sq_nonneg (coeff f a)) (fun a => le_rfl)
    (hs.summable.subtype (fun a => degree a=2)) hs.summable
  rw [hs.tsum_eq] at hh
  simpa only [chaosEnergy,labelCoefficientEnergy,Fintype.sum_unique,γFin,γpi,
    Gaussian1D.γ] using hh

/-- Centered quadratic Gaussian variance is bounded by twice the squared
Hilbert--Schmidt norm; no symmetry of A is required. -/
theorem quadraticScore_integral_sq_le (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    (∫ x, quadraticScore A x^2 ∂stdGaussian (FSC.Coord d)) ≤
      2*(operatorHilbertSchmidt A)^2 := by
  let f : (Fin d→ℝ)→ℝ := fun x => quadraticScore A (WithLp.toLp 2 x)
  have hf : MemLp f 2 (γFin d) := polynomial_memLp (quadraticScore_degree A)
  have he (x : Fin d→ℝ) :
      (∑ j,∑ k,operatorEntries A j k*quadraticCoordinate j k x)=f x := by
    simpa only [f,quadraticScore,quadraticCoordinate] using
      (quadratic_score_eq_entries A (WithLp.toLp 2 x)).symm
  have hpair := quadratic_test_pairing_bound (fun x (_:Unit) => f x)
    (fun _ => hf) (fun (_:Unit) => operatorEntries A)
  have hp : quadraticTestPairing (fun x (_:Unit) => f x)
      (fun (_:Unit) => operatorEntries A) = ∫ x,f x^2 ∂γFin d := by
    simp only [quadraticTestPairing,Fintype.sum_unique]
    apply integral_congr_ae
    filter_upwards with x
    calc
      _ = f x*(∑ j,∑ k,operatorEntries A j k*quadraticCoordinate j k x) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [he,pow_two]
  rw [hp] at hpair
  simp only [Fintype.sum_unique] at hpair
  have hHS : (∑ j,∑ k,operatorEntries A j k^2)=(operatorHilbertSchmidt A)^2 := by
    rw [operatorHilbertSchmidt,Real.sq_sqrt]
    positivity
  rw [hHS] at hpair
  have hs := secondChaos_le_integral_sq hf
  have hE : 0 ≤ ∫ x,f x^2 ∂γFin d := integral_nonneg (fun _=>sq_nonneg _)
  have hbound : (∫ x,f x^2 ∂γFin d) ≤ 2*(operatorHilbertSchmidt A)^2 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2))
      (sq_nonneg (operatorHilbertSchmidt A))
    nlinarith
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  rw [←hmap,integral_map (by fun_prop) (by unfold quadraticScore; fun_prop)]
  exact hbound

/-- Fixed-degree polynomials have dimension-free L4/L2 control, from the
already proved OU integral and exact finite Hermite inversion. -/
theorem polynomial_l4_le {k : ℕ} {f : (Fin d→ℝ)→ℝ}
    (hf : f ∈ polynomialSpace k) :
    eLpNorm f 4 (γFin d) ≤ ENNReal.ofReal ((2:ℝ)^k)*eLpNorm f 2 (γFin d) := by
  obtain ⟨c,rfl⟩ := exists_normalized_expansion hf
  let S := lowerModes (κ:=Fin d) (k+1)
  have hdeg (a) (ha : a∈S) : degree a≤k := by
    exact Nat.lt_succ_iff.mp ((mem_lowerModes_iff (k+1) a).mp ha)
  have hi : MemLp (inverseOUSum S c (1/2)) 2 (γFin d) := hermiteSum_memLp S _
  have hh := memLp_gaussian_average_l2_to_lq (1/2) (by norm_num) (by norm_num)
    (inverseOUSum S c (1/2)) hi
  have he : gaussianAverage (1/2) (inverseOUSum S c (1/2))=hermiteSum S c :=
    funext (inverseOUSum_gaussianAverage S c (1/2) (by norm_num) (by norm_num))
  rw [he] at hh
  norm_num at hh
  have h45 : eLpNorm (hermiteSum S c) 4 (γFin d) ≤
      eLpNorm (hermiteSum S c) 5 (γFin d) :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hinv := inverseOUSum_eLpNorm_le S c k hdeg (1/2) (by norm_num) (by norm_num)
  have hn : ((1/2:ℝ)^k)⁻¹=2^k := by simp [inv_pow]
  rw [hn] at hinv
  exact h45.trans (hh.trans hinv)

def norm2 (f : (Fin d→ℝ)→ℝ) : ℝ := (eLpNorm f 2 (γFin d)).toReal

theorem norm2_nonneg (f : (Fin d→ℝ)→ℝ) : 0 ≤ norm2 f := ENNReal.toReal_nonneg

theorem norm2_eq_sqrt {f : (Fin d→ℝ)→ℝ} (hf : MemLp f 2 (γFin d)) :
    norm2 f=Real.sqrt (∫ x,f x^2 ∂γFin d) := by
  rw [norm2,eLpNorm_two_eq_sqrt_integral_sq hf,ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

theorem norm2_sq {f : (Fin d→ℝ)→ℝ} (hf : MemLp f 2 (γFin d)) :
    norm2 f^2=∫ x,f x^2 ∂γFin d := by
  rw [norm2_eq_sqrt hf,Real.sq_sqrt (integral_nonneg (fun _=>sq_nonneg _))]

theorem norm2_add_le {f g : (Fin d→ℝ)→ℝ}
    (hf : MemLp f 2 (γFin d)) (hg : MemLp g 2 (γFin d)) :
    norm2 (fun x=>f x+g x) ≤ norm2 f+norm2 g := by
  have hh := ENNReal.toReal_mono (show eLpNorm f 2 (γFin d)+eLpNorm g 2 (γFin d)≠⊤ by finiteness)
    (eLpNorm_add_le (f:=f) (g:=g) (by norm_num : (1:ℝ≥0∞)≤2))
  simpa only [norm2,Pi.add_def,ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using hh

theorem norm2_sub_le {f g : (Fin d→ℝ)→ℝ}
    (hf : MemLp f 2 (γFin d)) (hg : MemLp g 2 (γFin d)) :
    norm2 (fun x=>f x-g x) ≤ norm2 f+norm2 g := by
  have hh := norm2_add_le hf hg.neg
  simpa only [sub_eq_add_neg,Pi.neg_apply,norm2,eLpNorm_neg] using hh

theorem polynomial_memLp_four {k : ℕ} {f : (Fin d→ℝ)→ℝ}
    (hf : f ∈ polynomialSpace k) : MemLp f 4 (γFin d) := by
  apply (polynomial_l4_le hf).trans_lt
  have h := polynomial_memLp hf
  finiteness

private instance holder442 : ENNReal.HolderTriple (4:ℝ≥0∞) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add,ENNReal.toReal_inv]⟩

theorem norm2_product_le {k l : ℕ} {f g : (Fin d→ℝ)→ℝ}
    (hf : f ∈ polynomialSpace k) (hg : g ∈ polynomialSpace l) :
    norm2 (fun x=>f x*g x) ≤ (2:ℝ)^(k+l)*norm2 f*norm2 g := by
  have hh : eLpNorm (fun x=>f x*g x) 2 (γFin d) ≤
      (ENNReal.ofReal ((2:ℝ)^k)*eLpNorm f 2 (γFin d))*
        (ENNReal.ofReal ((2:ℝ)^l)*eLpNorm g 2 (γFin d)) := by
    exact (eLpNorm_smul_le_mul_eLpNorm
      (p:=(4:ℝ≥0∞)) (q:=(4:ℝ≥0∞)) (r:=(2:ℝ≥0∞))
      (polynomial_continuous hf).aestronglyMeasurable
      (polynomial_continuous hg).aestronglyMeasurable).trans
        (mul_le_mul' (polynomial_l4_le hf) (polynomial_l4_le hg))
  have h := polynomial_memLp hf
  have h' := polynomial_memLp hg
  have hr := ENNReal.toReal_mono (by finiteness) hh
  simpa only [norm2,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2^k),
    ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2^l),pow_add,mul_assoc,mul_left_comm,mul_comm] using hr

theorem norm2_inner (v : FSC.Coord d) :
    norm2 (fun x=>inner ℝ v (WithLp.toLp 2 x))=‖v‖ := by
  have hf := polynomial_memLp (inner_mem (toEuclideanLinear (d:=d)) v)
  change MemLp (fun x=>inner ℝ v (WithLp.toLp 2 x)) 2 (γFin d) at hf
  rw [norm2_eq_sqrt hf]
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  have hi := NegativeVotingCovarianceCoercivity.integral_inner_sq v
  rw [←hmap,integral_map (by fun_prop) (by fun_prop)] at hi
  rw [hi,Real.sqrt_sq (norm_nonneg _)]

theorem norm2_quadraticScore_le (A : FSC.Coord d→L[ℝ] FSC.Coord d) :
    norm2 (fun x=>quadraticScore A (WithLp.toLp 2 x)) ≤ 2*operatorHilbertSchmidt A := by
  have hf := polynomial_memLp (quadraticScore_degree A)
  rw [norm2_eq_sqrt hf]
  have hh := quadraticScore_integral_sq_le A
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  rw [←hmap,integral_map (by fun_prop) (by unfold quadraticScore; fun_prop)] at hh
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity [operatorHilbertSchmidt_nonneg A],by nlinarith [sq_nonneg (operatorHilbertSchmidt A)]⟩

theorem norm2_const (c : ℝ) : norm2 (fun _ : Fin d→ℝ => c)=|c| := by
  rw [norm2_eq_sqrt (memLp_const c)]
  simp [Real.sqrt_sq_eq_abs]

theorem norm2_affine_score_le (v : FSC.Coord d) (c : ℝ) :
    norm2 (fun x=>inner ℝ v (WithLp.toLp 2 x)+c) ≤ ‖v‖+|c| := by
  have hf : MemLp (fun x=>inner ℝ v (WithLp.toLp 2 x)) 2 (γFin d) :=
    polynomial_memLp (inner_mem (toEuclideanLinear (d:=d)) v)
  simpa only [norm2_inner,norm2_const] using norm2_add_le hf (memLp_const c)

theorem norm2_linear_field_score_le (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z v : FSC.Coord d) :
    norm2 (fun x=>inner ℝ v (A (WithLp.toLp 2 x)+z)) ≤
      ‖v‖*(operatorHilbertSchmidt A+‖z‖) := by
  have he : (fun x : Fin d→ℝ => inner ℝ v (A (WithLp.toLp 2 x)+z)) =
      fun x => inner ℝ (A.adjoint v) (WithLp.toLp 2 x)+inner ℝ v z := by
    funext x
    rw [inner_add_right,ContinuousLinearMap.adjoint_inner_left]
  rw [he]
  have hn : ‖A.adjoint v‖ ≤ operatorHilbertSchmidt A*‖v‖ := by
    exact (A.adjoint.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (by simpa only [LinearIsometryEquiv.norm_map] using
        operator_norm_le_HilbertSchmidt A) (norm_nonneg _))
  calc
    _ ≤ ‖A.adjoint v‖+|inner ℝ v z| := norm2_affine_score_le _ _
    _ ≤ operatorHilbertSchmidt A*‖v‖+‖v‖*‖z‖ := add_le_add hn (abs_real_inner_le_norm _ _)
    _ = _ := by ring

theorem linear_field_score_degree (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z v : FSC.Coord d) :
    (fun x : Fin d→ℝ => inner ℝ v (A (WithLp.toLp 2 x)+z)) ∈ polynomialSpace 1 := by
  have hh := affine_score_mem (toEuclideanLinear (d:=d)) (A.adjoint v) (inner ℝ v z)
  simpa only [toEuclideanLinear,LinearMap.coe_mk,AddHom.coe_mk,
    ContinuousLinearMap.adjoint_inner_left,←inner_add_right] using hh

theorem norm2_massBulk_expression_le (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z : FSC.Coord d) :
    norm2 (fun x : Fin d→ℝ => inner ℝ (WithLp.toLp 2 x) (A (WithLp.toLp 2 x))+
      inner ℝ z (WithLp.toLp 2 x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap) ≤
      2*operatorHilbertSchmidt A+‖z‖ := by
  have hh := norm2_add_le (polynomial_memLp (quadraticScore_degree A))
    (polynomial_memLp (inner_mem (toEuclideanLinear (d:=d)) z))
  have he : (fun x : Fin d→ℝ => inner ℝ (WithLp.toLp 2 x) (A (WithLp.toLp 2 x))+
      inner ℝ z (WithLp.toLp 2 x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap) =
      fun x => quadraticScore A (WithLp.toLp 2 x)+inner ℝ z (WithLp.toLp 2 x) := by
    funext x
    unfold quadraticScore
    ring
  rw [he]
  exact hh.trans (add_le_add (norm2_quadraticScore_le A) (norm2_inner z).le)

open NegativeVotingQuadraticAffineTransport

theorem norm2_affineBulk_le (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z v y : FSC.Coord d) :
    norm2 (fun x : Fin d→ℝ => affineBulk v y A z (WithLp.toLp 2 x)) ≤
      144*‖v‖*‖y‖*(operatorHilbertSchmidt A+‖z‖) := by
  let q : (Fin d→ℝ)→ℝ := fun x => inner ℝ v (WithLp.toLp 2 x)*inner ℝ y (WithLp.toLp 2 x)
  let s : (Fin d→ℝ)→ℝ := fun x => inner ℝ (WithLp.toLp 2 x) (A (WithLp.toLp 2 x))+
    inner ℝ z (WithLp.toLp 2 x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap
  let fv : (Fin d→ℝ)→ℝ := fun x => inner ℝ v (A (WithLp.toLp 2 x)+z)
  let fy : (Fin d→ℝ)→ℝ := fun x => inner ℝ y (A (WithLp.toLp 2 x)+z)
  let lv : (Fin d→ℝ)→ℝ := fun x => inner ℝ v (WithLp.toLp 2 x)
  let ly : (Fin d→ℝ)→ℝ := fun x => inner ℝ y (WithLp.toLp 2 x)
  have hq : q∈polynomialSpace 2 := quadratic_mem (toEuclideanLinear (d:=d)) v y
  have hs : s∈polynomialSpace 2 := massBulk_expression_mem (toEuclideanLinear (d:=d)) A z
  have hv : fv∈polynomialSpace 1 := linear_field_score_degree A z v
  have hy : fy∈polynomialSpace 1 := linear_field_score_degree A z y
  have hlv : lv∈polynomialSpace 1 := inner_mem (toEuclideanLinear (d:=d)) v
  have hly : ly∈polynomialSpace 1 := inner_mem (toEuclideanLinear (d:=d)) y
  have hqm : MemLp (fun x=>q x*s x) 2 (γFin d) :=
    (polynomial_memLp_four hq).mul (polynomial_memLp_four hs)
  have hvm : MemLp (fun x=>fv x*ly x) 2 (γFin d) :=
    (polynomial_memLp_four hv).mul (polynomial_memLp_four hly)
  have hym : MemLp (fun x=>lv x*fy x) 2 (γFin d) :=
    (polynomial_memLp_four hlv).mul (polynomial_memLp_four hy)
  have hqbd : norm2 q ≤ 4*‖v‖*‖y‖ := by
    simpa only [q,lv,ly,norm2_inner,show (2:ℝ)^(1+1)=4 by norm_num] using norm2_product_le hlv hly
  have hsbd : norm2 s ≤ 2*operatorHilbertSchmidt A+‖z‖ := norm2_massBulk_expression_le A z
  have hfirst : norm2 (fun x=>q x*s x) ≤
      16*(4*‖v‖*‖y‖)*(2*operatorHilbertSchmidt A+‖z‖) := by
    have hh := norm2_product_le hq hs
    norm_num only at hh
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left hqbd (by norm_num)) hsbd
      (norm2_nonneg s) (by positivity))
  have hsecond : norm2 (fun x=>fv x*ly x) ≤
      4*(‖v‖*(operatorHilbertSchmidt A+‖z‖))*‖y‖ := by
    have hh := norm2_product_le hv hly
    norm_num only at hh
    exact hh.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (norm2_linear_field_score_le A z v) (by norm_num))
      (norm2_inner y).le (norm2_nonneg ly) (by positivity [operatorHilbertSchmidt_nonneg A]))
  have hthird : norm2 (fun x=>lv x*fy x) ≤
      4*‖v‖*(‖y‖*(operatorHilbertSchmidt A+‖z‖)) := by
    have hh := norm2_product_le hlv hy
    norm_num only at hh
    exact hh.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (norm2_inner v).le (by norm_num))
      (norm2_linear_field_score_le A z y) (norm2_nonneg fy) (by positivity))
  have htotal := (norm2_sub_le (hqm.sub hvm) hym).trans
    (add_le_add (norm2_sub_le hqm hvm) le_rfl)
  change norm2 (fun x=>(q x*s x-fv x*ly x)-lv x*fy x) ≤ _
  refine htotal.trans ?_
  have hh := add_le_add (add_le_add hfirst hsecond) hthird
  refine hh.trans ?_
  have hA := operatorHilbertSchmidt_nonneg A
  nlinarith [mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg y)) hA,
    mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg y)) (norm_nonneg z)]

/-- Actual ambient Gaussian L2 energy of the quartic affine transport bulk.
The explicit constant is uniform in dimension, with no symmetry restriction. -/
theorem affineBulk_integral_sq_le (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z v y : FSC.Coord d) :
    (∫ x, affineBulk v y A z x^2 ∂stdGaussian (FSC.Coord d)) ≤
      41472*‖v‖^2*‖y‖^2*((operatorHilbertSchmidt A)^2+‖z‖^2) := by
  let f : (Fin d→ℝ)→ℝ := fun x => affineBulk v y A z (WithLp.toLp 2 x)
  have hf : MemLp f 2 (γFin d) := polynomial_memLp
    (affineBulk_mem (toEuclideanLinear (d:=d)) v y A z)
  have hh := pow_le_pow_left₀ (norm2_nonneg f) (norm2_affineBulk_le A z v y) 2
  have hs : (operatorHilbertSchmidt A+‖z‖)^2 ≤
      2*((operatorHilbertSchmidt A)^2+‖z‖^2) := by
    nlinarith [sq_nonneg (operatorHilbertSchmidt A-‖z‖)]
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  rw [←hmap,integral_map (by fun_prop) (by unfold affineBulk; fun_prop)]
  change (∫ x,f x^2 ∂γFin d) ≤ _
  rw [←norm2_sq hf]
  calc
    _ ≤ (144*‖v‖*‖y‖*(operatorHilbertSchmidt A+‖z‖))^2 := hh
    _ = (20736*‖v‖^2*‖y‖^2)*(operatorHilbertSchmidt A+‖z‖)^2 := by ring
    _ ≤ (20736*‖v‖^2*‖y‖^2)*(2*((operatorHilbertSchmidt A)^2+‖z‖^2)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- The constant-test transport score, as a literal expression, has an actual
Gaussian squared-integral bound with the same Hilbert--Schmidt scale. -/
theorem massBulk_integral_sq_le (A : FSC.Coord d→L[ℝ] FSC.Coord d)
    (z : FSC.Coord d) :
    (∫ x, (inner ℝ x (A x)+inner ℝ z x-
      LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap)^2 ∂stdGaussian (FSC.Coord d)) ≤
      8*((operatorHilbertSchmidt A)^2+‖z‖^2) := by
  let f : (Fin d→ℝ)→ℝ := fun x => inner ℝ (WithLp.toLp 2 x) (A (WithLp.toLp 2 x))+
    inner ℝ z (WithLp.toLp 2 x)-LinearMap.trace ℝ (FSC.Coord d) A.toLinearMap
  have hf : MemLp f 2 (γFin d) := polynomial_memLp
    (massBulk_expression_mem (toEuclideanLinear (d:=d)) A z)
  have hh := pow_le_pow_left₀ (norm2_nonneg f) (norm2_massBulk_expression_le A z) 2
  have hmap : (γFin d).map (WithLp.toLp 2)=stdGaussian (FSC.Coord d) := map_pi_eq_stdGaussian
  rw [←hmap,integral_map (by fun_prop) (by fun_prop)]
  change (∫ x,f x^2 ∂γFin d) ≤ _
  rw [←norm2_sq hf]
  nlinarith [sq_nonneg (2*operatorHilbertSchmidt A-‖z‖),sq_nonneg ‖z‖]

end NegativeVotingQuadraticBulkNorm
