import GaussianNearRegularEnergyComparison
import GaussianRegularCoefficientBound

/-! A fixed logarithmic bound for the actual near-regular second-chaos energy
coefficient. The threshold depends only on the already established scalar
regular moment estimate and is chosen before the ambient dimension. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology

namespace NegativeVotingNearRegularEnergyLogBound
open NegativeVotingNearRegularEnergyComparison NegativeVotingNearRegularNormalizedBounds
  NegativeVotingNearRegularGraphGap NegativeVotingPolynomialFacetLogBound
  NegativeVotingRegularQuadraticRepresentation NegativeVotingRegularCoefficientBound
  NegativeVotingFan NegativeVotingFanSelectedOffsets NegativeVotingFanQuadraticMoments

def traceBase (e : ℝ) : ℝ := degreeBound e*quarticLogConstant 2
def gapBase (e A : ℝ) : ℝ := 512*Real.pi^2*degreeBound e*A^2
def offsetBase (e A : ℝ) : ℝ := 4*traceBase e*gapBase e A
def momentBase (e : ℝ) : ℝ := 16*(traceBase e)^2
def ratioBase (e : ℝ) : ℝ := 30/e
def adjointBase (e A : ℝ) : ℝ :=
  (512*traceBase e*(ratioBase e)^2*(1+offsetBase e A)+8*traceBase e*momentBase e)*gapBase e A

def energyLogConstant (e A B : ℝ) : ℝ :=
  momentBase e+
    8192*traceBase e*ratioBase e*(1+(B/e)*(1+offsetBase e A))*(1+offsetBase e A)+
    520*traceBase e*(B/e)*(1+momentBase e+adjointBase e A)*(1+offsetBase e A)

theorem base_nonneg (e A B : ℝ) (he : 0<e) (hB : 0≤B) :
    0 ≤ traceBase e ∧ 0 ≤ gapBase e A ∧ 0 ≤ offsetBase e A ∧
    0 ≤ momentBase e ∧ 0 ≤ ratioBase e ∧ 0 ≤ adjointBase e A ∧ 0 ≤ energyLogConstant e A B := by
  dsimp [traceBase,gapBase,offsetBase,momentBase,ratioBase,adjointBase,energyLogConstant,
    quarticLogConstant,degreeBound]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> positivity

theorem one_add_bound {L O O₀ : ℝ} (hL : 1≤L) (_hO₀ : 0≤O₀) (hO : O≤O₀*L^5) :
    1+O≤(1+O₀)*L^5 := by
  have hpow : (1:ℝ)≤L^5 := one_le_pow₀ hL
  nlinarith

theorem sqrt_one_add_bound {L O O₀ : ℝ} (hL : 1≤L) (_hO : 0≤O) (hO₀ : 0≤O₀)
    (hbound : O≤O₀*L^5) : Real.sqrt (1+O)≤(1+O₀)*L^3 := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hb := one_add_bound hL hO₀ hbound
  have hp : L^5≤L^6 := pow_le_pow_right₀ hL (by omega)
  have h₁ := mul_le_mul_of_nonneg_left hp (show 0≤1+O₀ by positivity)
  have h₂ := mul_le_mul_of_nonneg_right (show 1+O₀≤(1+O₀)^2 by nlinarith) (by positivity : 0≤L^6)
  nlinarith only [hb,h₁,h₂]

theorem sqrt_sum_bound {L M A M₀ A₀ : ℝ} (hL : 1≤L) (hM₀ : 0≤M₀) (hA₀ : 0≤A₀)
    (hM : M≤M₀*L^8) (hA : A≤A₀*L^13) :
    Real.sqrt (M+A)≤(1+M₀+A₀)*L^7 := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hp₈ : L^8≤L^14 := pow_le_pow_right₀ hL (by omega)
  have hp₁₃ : L^13≤L^14 := pow_le_pow_right₀ hL (by omega)
  have hb₁ := mul_le_mul_of_nonneg_left hp₈ hM₀
  have hb₂ := mul_le_mul_of_nonneg_left hp₁₃ hA₀
  have hb₃ := mul_le_mul_of_nonneg_right
    (show M₀+A₀≤(1+M₀+A₀)^2 by nlinarith) (by positivity : 0≤L^14)
  nlinarith only [hM,hA,hb₁,hb₂,hb₃]

theorem sqrt_product_div_le {X F d V : ℝ} (hX : 0≤X) (_hd : 0<d)
    (hV : Real.sqrt F/d≤V) : Real.sqrt (X*F)/d≤Real.sqrt X*V := by
  rw [Real.sqrt_mul hX]
  calc
    _=Real.sqrt X*(Real.sqrt F/d) := by ring
    _≤_ := mul_le_mul_of_nonneg_left hV (Real.sqrt_nonneg _)

/-- Pure scalar bookkeeping, retaining the actual coefficient's square roots
and both normalization denominators. -/
theorem coefficient_from_bounds {n : ℕ} {α e F L T O₀ M₀ U A₀ V : ℝ}
    (hα : 0<α) (he : 0<e) (hL : 1≤L)
    (hT : 0≤T) (hO₀ : 0≤O₀) (hM₀ : 0≤M₀) (hU : 0≤U) (hA₀ : 0≤A₀) (hV : 0≤V)
    (hK : traceCoefficient (n+2) e≤T*L^4)
    (hO : offsetCoefficient (n+2) α e≤O₀*L^5)
    (hM : momentComparisonCoefficient (n+2) e≤M₀*L^8)
    (hA : adjointCoefficient n α e≤A₀*L^13)
    (hγ : |momentCoefficient n/α|≤U*L)
    (hF : Real.sqrt F/(α/2)≤V) :
    energyComparisonCoefficient n α e F≤
      (M₀+8192*T*U*(1+V*(1+O₀))*(1+O₀)+520*T*V*(1+M₀+A₀)*(1+O₀))*L^16 := by
  let O := offsetCoefficient (n+2) α e
  let M := momentComparisonCoefficient (n+2) e
  let A := adjointCoefficient n α e
  have hOpos : 0≤O := offsetCoefficient_nonneg (n+2) α e hα he
  have hMpos : 0≤M := momentComparisonCoefficient_nonneg (n+2) e
  have hApos : 0≤A := adjointCoefficient_nonneg n α e hα he
  have ho : 1+O≤(1+O₀)*L^5 := one_add_bound hL hO₀ hO
  have hs := (sqrt_product_div_le (show 0≤1+O by positivity) (show 0<α/2 by positivity) hF).trans
    (mul_le_mul_of_nonneg_right (sqrt_one_add_bound hL hOpos hO₀ hO) hV)
  have hroot : 1+Real.sqrt ((1+O)*F)/(α/2)≤(1+V*(1+O₀))*L^3 := by
    have hp : (1:ℝ)≤L^3 := one_le_pow₀ hL
    nlinarith only [hs,hp]
  have hs' := (sqrt_product_div_le (show 0≤M+A by positivity) (show 0<α/2 by positivity) hF).trans
    (mul_le_mul_of_nonneg_right (sqrt_sum_bound hL hM₀ hA₀ hM hA) hV)
  have hfirst : 8192*traceCoefficient (n+2) e*|momentCoefficient n/α| *
      (1+Real.sqrt ((1+O)*F)/(α/2))*(1+O)≤
      8192*(T*L^4)*(U*L)*((1+V*(1+O₀))*L^3)*((1+O₀)*L^5) := by
    gcongr
  have hlast : (520*traceCoefficient (n+2) e/(α/2))*Real.sqrt ((M+A)*F)*(1+O)≤
      520*(T*L^4)*((1+M₀+A₀)*L^7*V)*((1+O₀)*L^5) := by
    calc
      _=520*traceCoefficient (n+2) e*(Real.sqrt ((M+A)*F)/(α/2))*(1+O) := by ring
      _≤_ := by gcongr
  have hp₈ := pow_le_pow_right₀ hL (show 8≤16 by omega)
  have hp₁₃ := pow_le_pow_right₀ hL (show 13≤16 by omega)
  have hmid := mul_le_mul_of_nonneg_left hp₁₃
    (show 0≤8192*T*U*(1+V*(1+O₀))*(1+O₀) by positivity)
  have hlow := mul_le_mul_of_nonneg_left hp₈ hM₀
  dsimp only [energyComparisonCoefficient]
  change M+_+_≤_
  nlinarith only [hM,hfirst,hlast,hmid,hlow]

/-- Normalization cancels both inverse regular scales. The numerical moment
bound is explicit here; the next endpoint discharges it eventually. -/
theorem coefficient_log_le_of_moment_bound (n : ℕ) (hn : 1≤n)
    (α e A B F : ℝ) (hα : 0<α) (he : 0<e) (hA : 0≤A) (hB : 0≤B) (_hF : 0≤F)
    (hlower : e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)≤α/2)
    (hupper : α≤A*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ))
    (hsize : F≤B^2/((n+2:ℕ):ℝ)^2)
    (hγ : |momentCoefficient n|≤30*(1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)) :
    energyComparisonCoefficient n α e F≤energyLogConstant e A B*(1+Real.log ((n+2:ℕ):ℝ))^16 := by
  let m : ℝ := (n+2:ℕ)
  let L := 1+Real.log m
  have hm : (1:ℝ) ≤ m := by dsimp [m]; exact_mod_cast (show 1≤n+2 by omega)
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hL : 1≤L := by dsimp [L]; linarith [Real.log_nonneg hm]
  have hL0 : 0≤L := by linarith
  have hs : 1≤Real.sqrt L := (Real.le_sqrt (by norm_num) hL0).mpr (by simpa using hL)
  have hsmall : e/m≤α/2 := by
    have h₁ : e/m≤e*Real.sqrt L/m := div_le_div_of_nonneg_right
      (by nlinarith : e≤e*Real.sqrt L) hmpos.le
    exact h₁.trans hlower
  have hsmall' : e/m≤α := hsmall.trans (by linarith)
  have hu : |momentCoefficient n/α|≤ratioBase e*L := by
    rw [abs_div,abs_of_pos hα]
    calc
      _≤(30*L/m)/α := div_le_div_of_nonneg_right hγ hα.le
      _≤(30*L/m)/(e/m) := div_le_div_of_nonneg_left (by positivity) (div_pos he hmpos) hsmall'
      _=ratioBase e*L := by dsimp [ratioBase]; field_simp
  have hsqrt : Real.sqrt F≤B/m := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨div_nonneg hB hmpos.le,?_⟩
    simpa only [div_pow] using hsize
  have hv : Real.sqrt F/(α/2)≤B/e := by
    calc
      _≤(B/m)/(α/2) := div_le_div_of_nonneg_right hsqrt (by positivity)
      _≤(B/m)/(e/m) := div_le_div_of_nonneg_left (div_nonneg hB hmpos.le) (div_pos he hmpos) hsmall
      _=B/e := by field_simp
  have hb := base_nonneg e A B he hB
  have hT0 := hb.1
  have hJ0 := hb.2.1
  have hO0 := hb.2.2.1
  have hM0 := hb.2.2.2.1
  have hU0 := hb.2.2.2.2.1
  have hAdj0 := hb.2.2.2.2.2.1
  have hOff0 := offsetCoefficient_nonneg (n+2) α e hα he
  have hgap : (nearGap (n+2) α e)⁻¹≤gapBase e A*L := by
    exact nearGap_inv_le α e A hα he hA (by omega) hupper
  have hK : traceCoefficient (n+2) e=traceBase e*L^4 := rfl
  have hO : offsetCoefficient (n+2) α e≤offsetBase e A*L^5 := by
    calc
      _=(4*traceBase e*L^4)*(nearGap (n+2) α e)⁻¹ := by
        dsimp [offsetCoefficient,traceBase,L,m]; ring
      _≤(4*traceBase e*L^4)*(gapBase e A*L) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _=offsetBase e A*L^5 := by dsimp [offsetBase]; ring
  have hM : momentComparisonCoefficient (n+2) e=momentBase e*L^8 := by
    dsimp [momentComparisonCoefficient,momentBase,traceBase,L,m]; ring
  have ho : 1+offsetCoefficient (n+2) α e≤(1+offsetBase e A)*L^5 :=
    one_add_bound hL hb.2.2.1 hO
  have hγsq : (momentCoefficient n/α)^2≤(ratioBase e*L)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hu 2
  have hAdj : adjointCoefficient n α e≤adjointBase e A*L^13 := by
    have hgap0 : 0≤(nearGap (n+2) α e)⁻¹ := (inv_pos.mpr (nearGap_pos α e hα he)).le
    calc
      _=(512*(traceBase e*L^4)*(momentCoefficient n/α)^2*(1+offsetCoefficient (n+2) α e)+
          8*(traceBase e*L^4)*(momentBase e*L^8))*(nearGap (n+2) α e)⁻¹ := by
        dsimp [adjointCoefficient,momentBase,traceBase,L,m,momentComparisonCoefficient]; ring
      _≤(512*(traceBase e*L^4)*(ratioBase e*L)^2*((1+offsetBase e A)*L^5)+
          8*(traceBase e*L^4)*(momentBase e*L^8))*(gapBase e A*L) := by gcongr
      _=(512*traceBase e*(ratioBase e)^2*(1+offsetBase e A)*gapBase e A)*L^12+
          (8*traceBase e*momentBase e*gapBase e A)*L^13 := by ring
      _≤(512*traceBase e*(ratioBase e)^2*(1+offsetBase e A)*gapBase e A)*L^13+
          (8*traceBase e*momentBase e*gapBase e A)*L^13 := by
        have hh := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hL (show 12≤13 by omega))
          (show 0≤512*traceBase e*(ratioBase e)^2*(1+offsetBase e A)*gapBase e A by positivity)
        linarith only [hh]
      _=adjointBase e A*L^13 := by dsimp [adjointBase]; ring
  have hh := coefficient_from_bounds hα he hL hb.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1
    hb.2.2.2.2.2.1 (div_nonneg hB he.le) hK.le hO hM.le hAdj hu hv
  exact hh

/-- One scalar threshold works for every choice of the scale parameters. -/
theorem exists_threshold_coefficient_log_le :
    ∃ N : ℕ,∀ n≥N,∀ α e A B F : ℝ,
      0<α → 0<e → 0≤A → 0≤B → 0≤F →
      e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)≤α/2 →
      α≤A*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) →
      F≤B^2/((n+2:ℕ):ℝ)^2 →
      energyComparisonCoefficient n α e F≤energyLogConstant e A B*(1+Real.log ((n+2:ℕ):ℝ))^16 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp eventually_momentCoefficient_log_bound
  refine ⟨max N 1,?_⟩
  intro n hn α e A B F hα he hA hB hF hlower hupper hsize
  apply coefficient_log_le_of_moment_bound n (le_trans (le_max_right _ _) hn)
    α e A B F hα he hA hB hF hlower hupper hsize
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hN n (le_trans (le_max_left _ _) hn)

/-- Full actual finite second-chaos comparison with a fixed logarithmic
coefficient. The threshold precedes the ambient dimension, the regular Gram
family and the scale parameters. No analytic derivative/trace/adjoint bound
is supplied as a hypothesis. -/
theorem exists_threshold_selected_energy_log_le :
    ∃ N : ℕ,∀ n≥N,∀ d : ℕ,∀ R D : Fin (n+2)→FSC.Coord d,
      (∀ i j,inner ℝ (R i) (R j)=(if i=j then 1 else 0)-1/((n+2:ℕ):ℝ)) →
      ∀ α e A B : ℝ,0<α → 0<e → 0≤A → 0≤B →
      (∑ i,‖D i‖^2)≤α^2/256 →
      e*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ)≤α/2 →
      α≤A*Real.sqrt (1+Real.log ((n+2:ℕ):ℝ))/((n+2:ℕ):ℝ) →
      (∑ i,‖D i‖^2)≤B^2/((n+2:ℕ):ℝ)^2 →
      |secondEnergy (α•R+D) (selectedOffsets (α•R+D) (fun _=>((n+2:ℕ):ℝ)⁻¹))-
        secondEnergy R 0|≤energyLogConstant e A B*(1+Real.log ((n+2:ℕ):ℝ))^16*(∑ i,‖D i‖^2) := by
  obtain ⟨N,hN⟩ := exists_threshold_coefficient_log_le
  refine ⟨max N 1,?_⟩
  intro n hn d R D hGram α e A B hα he hA hB hD hlower hupper hsize
  have hn1 : 1≤n := le_trans (le_max_right _ _) hn
  have hF : 0≤∑ i,‖D i‖^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hh := near_regular_selected_energy_abs_le hn1 R D hGram α hα hD e he hlower
  exact hh.trans (mul_le_mul_of_nonneg_right
    (hN n (le_trans (le_max_left _ _) hn) α e A B _ hα he hA hB hF hlower hupper hsize) hF)

end NegativeVotingNearRegularEnergyLogBound
