import GaussianRegularDiagonalBalance
import GaussianDiagonalHazardQuadraticForm

/-! Exact all-label hazard coefficient at the regular point. The analytic
 diagonal is retained. This module evaluates the integrated pointwise
 derivative; differentiation under the integral is proved separately. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter WeakSimplex
open scoped BigOperators Classical Topology
namespace NegativeVotingRegularHazardCoefficient
open NegativeVotingRegularTieLaw NegativeVotingRegularTieVariance
  NegativeVotingRegularDiagonalBalance NegativeVotingDiagonalHazardDifferentiation
  NegativeVotingDiagonalHazardQuadraticForm NegativeVotingBalancedReference

def regularLogHazardSpeed (n : ℕ) (x : ℝ) : ℝ := (x+r x)*(x-tieMean n)-1

theorem regular_totalHazardFlux (n : ℕ) (ξ : Fin (n+2)→ℝ) (hξ : ∑i,ξ i=0) (x : ℝ) :
    totalHazardFlux (fun _=>1) (fun _=>0) (fun i=>ξ i/2)
      (fun i=>-tieMean n*(ξ i/2)) x=0 := by
  unfold totalHazardFlux transportSpeed gaussianHazard gaussianDensity gaussianCDF
  simp only [sub_zero,div_one]
  have he (i:Fin (n+2)) : normalPDF x/normalCDF x*(-tieMean n*(ξ i/2)+(ξ i/2)*x)=
      (normalPDF x/normalCDF x*(x-tieMean n)/2)*ξ i:=by ring
  simp_rw [he]
  rw [←Finset.mul_sum,hξ,mul_zero]

theorem regular_hazardPairLogDerivative (n : ℕ) (ξ : Fin (n+2)→ℝ)
    (hξ : ∑i,ξ i=0) (x : ℝ) (i j : Fin (n+2)) :
    hazardPairLogDerivative (fun _=>1) (fun _=>0) (fun k=>ξ k/2)
      (fun k=>-tieMean n*(ξ k/2)) x i j=
      regularLogHazardSpeed n x*(ξ i+ξ j)/2 := by
  unfold hazardPairLogDerivative
  rw [regular_totalHazardFlux n ξ hξ]
  unfold densityLogDerivative transportSpeed gaussianHazard gaussianDensity gaussianCDF regularLogHazardSpeed r
  simp only [sub_zero,div_one,one_pow]
  ring

theorem regular_hazardRowSum (n : ℕ) (x : ℝ) (i : Fin (n+2)) :
    hazardRowSum (fun _=>1) (fun _=>0) x i=((n:ℝ)+2)*tieWeight n x := by
  simp [hazardRowSum,regular_hazardPairDensity,Nat.cast_add,Nat.cast_ofNat]

theorem regular_hazardRowSum_integral (n : ℕ) (hn : 0<n) (i : Fin (n+2)) :
    (∫x,hazardRowSum (fun _=>1) (fun _=>0) x i)=referenceScale n := by
  simp_rw [regular_hazardRowSum]
  rw [integral_const_mul]
  change ((n:ℝ)+2)*tieMass n=referenceScale n
  rw [tieMass_eq_referenceScale n hn]
  field_simp

theorem regular_rowDerivative_sum (n : ℕ) (ξ : Fin (n+2)→ℝ)
    (hξ : ∑i,ξ i=0) (x : ℝ) (i : Fin (n+2)) :
    (∑j,hazardPairDensity (fun _=>1) (fun _=>0) x i j*
      hazardPairLogDerivative (fun _=>1) (fun _=>0) (fun k=>ξ k/2)
        (fun k=>-tieMean n*(ξ k/2)) x i j)=
      (((n:ℝ)+2)*ξ i/2)*(tieWeight n x*regularLogHazardSpeed n x) := by
  simp_rw [regular_hazardPairDensity,regular_hazardPairLogDerivative n ξ hξ]
  have he (j:Fin (n+2)) : tieWeight n x*(regularLogHazardSpeed n x*(ξ i+ξ j)/2)=
      (tieWeight n x*regularLogHazardSpeed n x/2)*(ξ i+ξ j):=by ring
  simp_rw [he]
  rw [←Finset.mul_sum,Finset.sum_add_distrib,hξ,add_zero]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  ring

theorem regular_logHazard_weighted_integrable (n : ℕ) :
    Integrable (fun x=>tieWeight n x*regularLogHazardSpeed n x) volume := by
  have hh:=(((weighted_x_sq_integrable n).sub ((weighted_x_integrable n).mul_const (tieMean n))).add
    ((weighted_x_r_integrable n).sub ((weighted_r_integrable n).mul_const (tieMean n)))).sub (tieWeight_integrable n)
  convert hh using 1
  funext x
  simp only [Pi.add_apply,Pi.sub_apply]
  unfold regularLogHazardSpeed
  ring

theorem regular_logHazard_expectation (n : ℕ) :
    (∫x,regularLogHazardSpeed n x ∂tieLaw n)=tieVariance n+tieHazardCovariance n-1 := by
  have hx:Integrable (fun x:ℝ=>x) (tieLaw n):=(tieLaw_memLp_id n).integrable (by norm_num)
  have hr:Integrable r (tieLaw n):=(tieLaw_memLp_r n).integrable (by norm_num)
  have hxx:Integrable (fun x:ℝ=>x^2) (tieLaw n):=integrable_tieLaw_of_weighted n _ (weighted_x_sq_integrable n)
  have hxr:Integrable (fun x:ℝ=>x*r x) (tieLaw n):=integrable_tieLaw_of_weighted n _ (weighted_x_r_integrable n)
  have he : regularLogHazardSpeed n=fun x=>(x^2-x*tieMean n)+(x*r x-r x*tieMean n)-1:=by
    funext x;unfold regularLogHazardSpeed;ring
  have h1 : Integrable (fun x=>x^2-x*tieMean n) (tieLaw n):=hxx.sub (hx.mul_const _)
  have h2 : Integrable (fun x=>x*r x-r x*tieMean n) (tieLaw n):=hxr.sub (hr.mul_const _)
  have h3 : Integrable (fun x=>(x^2-x*tieMean n)+(x*r x-r x*tieMean n)) (tieLaw n):=h1.add h2
  rw [he,integral_sub h3 (integrable_const _),
    integral_add h1 h2,
    integral_sub hxx (hx.mul_const _),integral_sub hxr (hr.mul_const _),integral_mul_const,integral_mul_const]
  unfold tieVariance tieHazardCovariance tieMean
  rw [variance_eq_sub (tieLaw_memLp_id n),covariance_eq_sub (tieLaw_memLp_id n) (tieLaw_memLp_r n)]
  simp only [Pi.pow_apply,Pi.mul_apply,integral_const,probReal_univ,one_smul]
  ring

theorem regular_logHazard_integral (n : ℕ) (hn : 0<n) :
    (∫x,tieWeight n x*regularLogHazardSpeed n x)= -2*tieMass n*eta n := by
  have he:=regular_logHazard_expectation n
  rw [integral_tieLaw] at he
  have hi:=tieLaw_covariance_identity n
  have hn0:(n:ℝ)≠0:=by exact_mod_cast hn.ne'
  have hcoef : tieVariance n+tieHazardCovariance n-1= -2*eta n:=by
    unfold eta
    field_simp [hn0]
    nlinarith
  rw [hcoef] at he
  have hm:tieMass n≠0:=(tieMass_pos n).ne'
  have hh:=(div_eq_iff hm).mp he
  nlinarith

/-- Exact integral of the actual all-label pointwise derivative. This is
not by itself a differentiation-under-the-integral theorem. -/
theorem regular_rowDerivative_integral (n : ℕ) (hn : 0<n) (ξ : Fin (n+2)→ℝ)
    (hξ : ∑i,ξ i=0) (i : Fin (n+2)) :
    (∫x,∑j,hazardPairDensity (fun _=>1) (fun _=>0) x i j*
      hazardPairLogDerivative (fun _=>1) (fun _=>0) (fun k=>ξ k/2)
        (fun k=>-tieMean n*(ξ k/2)) x i j)= -referenceScale n*eta n*ξ i := by
  simp_rw [regular_rowDerivative_sum n ξ hξ]
  rw [integral_const_mul,regular_logHazard_integral n hn,tieMass_eq_referenceScale n hn]
  field_simp

end NegativeVotingRegularHazardCoefficient
