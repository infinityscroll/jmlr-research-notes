import GaussianDiagonalFrameRealization

/-! Exact scalar accounting for the diagonal supporting hyperplane.
Analytic Taylor estimates remain explicit until supplied by the actual
selected-offset path; this file does not assert those estimates. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Classical
namespace NegativeVotingDiagonalSupportAlgebra
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def diagonalSupportWeight (d κ t : ℝ) (ξ : V→ℝ) (i : V) : ℝ := 2*d+(1+t)*κ*ξ i

lemma diagonal_support_expansion (α η d κ t : ℝ) (ξ e : V→ℝ) (hξ : ∑i,ξ i=0) :
    (1/2:ℝ)*(∑i,(α-α*η*t*ξ i+e i)*diagonalSupportWeight d κ t ξ i)=
      α*d*(Fintype.card V:ℝ)-α*η*t*κ*(1+t)/2*(∑i,(ξ i)^2)+
        (1/2:ℝ)*(∑i,e i*diagonalSupportWeight d κ t ξ i) := by
  have he (i:V):(α-α*η*t*ξ i+e i)*diagonalSupportWeight d κ t ξ i=
      2*α*d+(α*(1+t)*κ-2*α*η*t*d)*ξ i-α*η*t*κ*(1+t)*(ξ i)^2+
        e i*diagonalSupportWeight d κ t ξ i := by
    unfold diagonalSupportWeight
    ring
  simp only [he,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [←Finset.mul_sum,hξ,mul_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,add_zero]
  ring

lemma support_remainder_le (d κ t U : ℝ) (ξ e : V→ℝ) (hU : 0 ≤ U)
    (hW : ∀i,|diagonalSupportWeight d κ t ξ i| ≤ U) :
    (1/2:ℝ)*(∑i,e i*diagonalSupportWeight d κ t ξ i) ≤ U/2*(∑i,|e i|) := by
  have hterm (i:V):e i*diagonalSupportWeight d κ t ξ i ≤ |e i| *U:=by
    calc
      _ ≤ |e i*diagonalSupportWeight d κ t ξ i|:=le_abs_self _
      _ = |e i| *|diagonalSupportWeight d κ t ξ i|:=abs_mul _ _
      _ ≤ _:=mul_le_mul_of_nonneg_left (hW i) (abs_nonneg _)
  have hh:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>hterm i
  rw [←Finset.sum_mul] at hh
  nlinarith

/-- A summed quadratic Taylor remainder is sufficient; no per-coordinate
remainder estimate is needed. The smallness test is explicit and scalar. -/
theorem covariance_gap_of_support_remainder (α η d κ t U E Γ : ℝ)
    (ξ e : V→ℝ) (hξ : ∑i,ξ i=0) (hα : 0 ≤ α) (hη : (1/4:ℝ) ≤ η)
    (hκ : (1/3:ℝ) ≤ κ) (ht : 0 ≤ t) (hU : 0 ≤ U)
    (hW : ∀i,|diagonalSupportWeight d κ t ξ i| ≤ U)
    (he : (∑i,|e i|) ≤ E*α*t^2*(∑i,(ξ i)^2))
    (hsmall : U*E*t ≤ 1/24)
    (hsupport : Γ ≤ (1/2:ℝ)*(∑i,(α-α*η*t*ξ i+e i)*diagonalSupportWeight d κ t ξ i)) :
    α*t/48*(∑i,(ξ i)^2) ≤ α*d*(Fintype.card V:ℝ)-Γ := by
  have hQ:0 ≤ ∑i,(ξ i)^2:=Finset.sum_nonneg fun i _=>sq_nonneg _
  have hcoef:α*η*t*κ*(1+t)/2*(∑i,(ξ i)^2) ≥ α*t/24*(∑i,(ξ i)^2) := by
    have hη0:0 ≤ η:=by linarith
    have hκ0:0 ≤ κ:=by linarith
    have hk: (1/12:ℝ) ≤ η*κ:=by nlinarith [mul_le_mul hη hκ (by norm_num : (0:ℝ) ≤ 1/3) hη0]
    have htcoef: (1/12:ℝ) ≤ η*κ*(1+t):=by nlinarith [mul_nonneg (mul_nonneg hη0 hκ0) ht]
    have hh:=mul_le_mul_of_nonneg_left htcoef (show 0 ≤ α*t*(∑i,(ξ i)^2)/2 by positivity)
    nlinarith
  have herror:U/2*(E*α*t^2*(∑i,(ξ i)^2)) ≤ α*t/48*(∑i,(ξ i)^2) := by
    have hh:=mul_le_mul_of_nonneg_right hsmall (show 0 ≤ α*t*(∑i,(ξ i)^2)/2 by positivity)
    nlinarith
  have hr:=(support_remainder_le d κ t U ξ e hU hW).trans
    (mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ U/2))
  rw [diagonal_support_expansion α η d κ t ξ e hξ] at hsupport
  linarith

lemma squared_radius_error_le_squared_energy_error (x y : ℝ) (hx : 0 ≤ x) (hy : 0<y) :
    (Real.sqrt x-Real.sqrt y)^2 ≤ (x-y)^2/y := by
  have hxs:0 ≤ Real.sqrt x:=Real.sqrt_nonneg _
  have hys:0 ≤ Real.sqrt y:=Real.sqrt_nonneg _
  have hxy:0 ≤ Real.sqrt x*Real.sqrt y:=mul_nonneg hxs hys
  apply (le_div_iff₀ hy).mpr
  have hnorm: (x-y)^2=(Real.sqrt x-Real.sqrt y)^2*(Real.sqrt x+Real.sqrt y)^2 := by
    calc
      _ = ((Real.sqrt x)^2-(Real.sqrt y)^2)^2:=by rw [Real.sq_sqrt hx,Real.sq_sqrt hy.le]
      _ = _:=by ring
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith [Real.sq_sqrt hx,Real.sq_sqrt hy.le]

end NegativeVotingDiagonalSupportAlgebra
