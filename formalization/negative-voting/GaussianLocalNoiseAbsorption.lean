import GaussianLocalRectangleAbsorption

/-! Scalar assembly preserving the mixed mass-error cancellation at zero
mass displacement. Inputs are displayed for the actual-noise wrapper. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Set
open scoped Topology
namespace NegativeVotingLocalNoiseAbsorption

lemma mixed_root_le (M F Z : ℝ) (hM : 0 ≤ M) (hF : 0 ≤ F) (hZ : 0 ≤ Z) :
    Real.sqrt (M*(F+Z)*Z) ≤ Real.sqrt M*(Real.sqrt F*Real.sqrt Z+Z) := by
  have hsqM := Real.sq_sqrt hM
  have hsqF := Real.sq_sqrt hF
  have hsqZ := Real.sq_sqrt hZ
  have hsq := Real.sq_sqrt (show 0 ≤ M*(F+Z)*Z by positivity)
  have heq : (Real.sqrt M*(Real.sqrt F*Real.sqrt Z+Z))^2=
      M*(F+Z)*Z+2*M*Z*Real.sqrt F*Real.sqrt Z := by
    calc
      _ = (Real.sqrt M)^2*((Real.sqrt F)^2*(Real.sqrt Z)^2+
          2*Z*Real.sqrt F*Real.sqrt Z+Z^2) := by ring
      _ = _ := by rw [hsqM,hsqF,hsqZ];ring
  have hn : 0 ≤ 2*M*Z*Real.sqrt F*Real.sqrt Z := by positivity
  have hrhs : 0 ≤ Real.sqrt M*(Real.sqrt F*Real.sqrt Z+Z) := by positivity
  nlinarith [Real.sqrt_nonneg (M*(F+Z)*Z)]

lemma mixed_mass_absorption (r M F Z : ℝ) (hM : 0 ≤ M) (hF : 0 ≤ F) (hZ : 0 ≤ Z)
    (hsmall : r^2*Real.sqrt M ≤ 1/16) :
    r^2*Real.sqrt (M*(F+Z)*Z) ≤ Z/8+4*r^4*M*F := by
  have hh := mul_le_mul_of_nonneg_left (mixed_root_le M F Z hM hF hZ) (sq_nonneg r)
  have hsq := sq_nonneg (2*r^2*Real.sqrt M*Real.sqrt F-Real.sqrt Z/4)
  have heq : (2*r^2*Real.sqrt M*Real.sqrt F-Real.sqrt Z/4)^2=
      4*r^4*M*F+Z/16-r^2*Real.sqrt M*Real.sqrt F*Real.sqrt Z := by
    have hM2 := Real.sq_sqrt hM
    have hF2 := Real.sq_sqrt hF
    have hZ2 := Real.sq_sqrt hZ
    calc
      _ = 4*r^4*(Real.sqrt M)^2*(Real.sqrt F)^2+(Real.sqrt Z)^2/16-
          r^2*Real.sqrt M*Real.sqrt F*Real.sqrt Z := by ring
      _ = _ := by rw [hM2,hF2,hZ2]
  rw [heq] at hsq
  have hz := mul_le_mul_of_nonneg_right hsmall hZ
  nlinarith only [hh,hsq,hz]

theorem local_noise_absorption (r R F Z P M B C gap : ℝ)
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hF : 0 ≤ F) (hZ : 0 ≤ Z)
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hpaid : F ≤ P*R)
    (hbalanced : r*B ≤ 1/8)
    (hmassZ : r^2*Real.sqrt M ≤ 1/16)
    (hmassR : 4*r^3*M*P ≤ 1/8)
    (htailR : C*r^2*P ≤ 1/8) (htailZ : C*r^3 ≤ 1/16)
    (hgap : r*R+Z/2-r^2*B*R-r^2*Real.sqrt (M*(F+Z)*Z)-C*r^3*(F+Z) ≤ gap) :
    r*R/2+Z/4 ≤ gap := by
  have hmix := mixed_mass_absorption r M F Z hM hF hZ hmassZ
  have hp := mul_le_mul_of_nonneg_left hpaid (show 0 ≤ 4*r^4*M by positivity)
  have hm := mul_le_mul_of_nonneg_right hmassR (mul_nonneg hr hR)
  have hb := mul_le_mul_of_nonneg_right hbalanced (mul_nonneg hr hR)
  have htf := mul_le_mul_of_nonneg_left hpaid (show 0 ≤ C*r^3 by positivity)
  have htr := mul_le_mul_of_nonneg_right htailR (mul_nonneg hr hR)
  have htz := mul_le_mul_of_nonneg_right htailZ hZ
  have hrR := mul_nonneg hr hR
  nlinarith only [hgap,hmix,hp,hm,hb,htf,htr,htz,hrR,hZ]

end NegativeVotingLocalNoiseAbsorption
