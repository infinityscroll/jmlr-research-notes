import GaussianRareLabelHighChaos
import GaussianFanQuadraticMoments

/-! Bounded continuous Gaussian tests after removal of modes below degree
three are genuine continuous quadratically growing moving-cell tests. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory GaussianFin Set
open scoped ENNReal BigOperators RealInnerProductSpace Classical
namespace NegativeVotingBoundedOUCellTests
open NegativeVotingHypercontractivity NegativeVotingProjection NegativeVotingModern
  NegativeVotingRareLabelHighChaos OAI.MinUncut.GaussianHermite
variable {d : ℕ}

theorem coordinate_abs_le_norm (x : FSC.Coord d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have hh := Finset.single_le_sum (fun j (_:j∈Finset.univ)=>sq_nonneg (x j)) (Finset.mem_univ i)
  rw [←EuclideanSpace.real_norm_sq_eq] at hh
  nlinarith [sq_abs (x i),abs_nonneg (x i),norm_nonneg x]

theorem quadraticCoordinate_growth (i j : Fin d) (x : FSC.Coord d) :
    |quadraticCoordinate i j (fun k=>x k)| ≤ 1+‖x‖^2 := by
  unfold quadraticCoordinate
  have hmul : |x i*x j| ≤ ‖x‖^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (coordinate_abs_le_norm x i) (coordinate_abs_le_norm x j)
      (abs_nonneg _) (norm_nonneg _)
  have hite : |(if i=j then 1 else 0 : ℝ)| ≤ 1 := by split_ifs <;> norm_num
  exact (abs_sub _ _).trans (by linarith)

theorem psi_degree_two_growth (b : Fin d→ℕ) (hb : degree b=2) (x : FSC.Coord d) :
    |psi b (fun j=>x j)| ≤ 1+‖x‖^2 := by
  have hh (s : Sym2 (Fin d)) : |psi (degreeTwoEquiv s).1 (fun j=>x j)| ≤ 1+‖x‖^2 := by
    induction s using Sym2.inductionOn with
    | hf i j =>
      rw [degreeTwoEquiv_pair]
      by_cases hij : i=j
      · subst j
        have hs : (Pi.single i 1+Pi.single i 1 : Fin d→ℕ)=Pi.single i 2 := by
          funext l
          by_cases hl : l=i <;> simp [hl]
        rw [hs,psi_single_two,abs_div,abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))]
        apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))).mpr
        have hr : 1 ≤ Real.sqrt 2 := by norm_num
        have hq := quadraticCoordinate_growth i i x
        nlinarith [sq_nonneg ‖x‖]
      · rw [psi_two_distinct i j hij]
        exact quadraticCoordinate_growth i j x
  have he := (degreeTwoEquiv.apply_symm_apply ⟨b,hb⟩)
  simpa only [he] using hh (degreeTwoEquiv.symm ⟨b,hb⟩)

theorem psi_low_degree_growth (b : Fin d→ℕ) (hb : degree b<3) (x : FSC.Coord d) :
    |psi b (fun j=>x j)| ≤ 1+‖x‖^2 := by
  by_cases h0 : degree b=0
  · rw [(degree_zero_iff b).mp h0]
    simp only [psi,Pi.zero_apply,H,he_zero,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,
      div_one,Finset.prod_const_one,abs_one]
    exact le_add_of_nonneg_right (sq_nonneg _)
  by_cases h1 : degree b=1
  · obtain ⟨j,rfl⟩ := (degree_one_iff b).mp h1
    have he : psi (Pi.single j 1) (fun l=>x l)=x j := by
      unfold psi
      rw [Finset.prod_eq_single j]
      · simp [H,he_one]
      · intro l _ hlj
        simp [hlj,H]
      · simp
    rw [he]
    have hh := coordinate_abs_le_norm x j
    nlinarith [sq_nonneg (‖x‖-1)]
  exact psi_degree_two_growth b (by omega) x

theorem integrable_psi_affine (ρ s : ℝ) (b : Fin d→ℕ) (x : Fin d→ℝ) :
    Integrable (fun y=>psi b (fun i=>ρ*x i+s*y i)) (γFin d) := by
  exact Integrable.fintype_prod (fun i=>(integrable_he_affine (b i) (ρ*x i) s).div_const
    (Real.sqrt ((b i).factorial:ℝ)))

theorem gaussianAverage_projectModes (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (S : Finset (Fin d→ℕ)) (f : (Fin d→ℝ)→ℝ) (x : Fin d→ℝ) :
    gaussianAverage ρ (projectModes S f) x=
      ∑ b∈S,ρ^(degree b)*coeff f b*psi b x := by
  have hsq : 0 ≤ 1-ρ^2 := by nlinarith [(abs_le.mp hρ).1,(abs_le.mp hρ).2]
  unfold gaussianAverage projectModes
  rw [integral_finsetSum S (fun b _=>
    (integrable_psi_affine ρ (Real.sqrt (1-ρ^2)) b x).const_mul (coeff f b))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul]
  have he := psi_noise ρ (Real.sqrt (1-ρ^2))
    (by rw [Real.sq_sqrt hsq];ring) b x
  change (∫ y,psi b (fun i=>ρ*x i+Real.sqrt (1-ρ^2)*y i) ∂γFin d)=
    ρ^(degree b)*psi b x at he
  rw [he]
  ring

theorem gaussianAverage_highModes_bounded (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (k : ℕ) (f : (Fin d→ℝ)→ℝ) (hfM : Measurable f)
    (M : ℝ) (hM : ∀ x,|f x| ≤ M) (x : Fin d→ℝ) :
    gaussianAverage ρ (highModes k f) x=gaussianAverage ρ f x-
      ∑ b∈lowerModes k,ρ^(degree b)*coeff f b*psi b x := by
  have hfi : Integrable (fun y=>f (fun i=>ρ*x i+Real.sqrt (1-ρ^2)*y i)) (γFin d) :=
    Integrable.of_bound (hfM.comp (by fun_prop)).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun y=>by simpa only [Real.norm_eq_abs] using hM _))
  have hpi : Integrable (fun y=>projectModes (lowerModes k) f
      (fun i=>ρ*x i+Real.sqrt (1-ρ^2)*y i)) (γFin d) :=
    integrable_finsetSum (lowerModes k) (fun b _=>
      (integrable_psi_affine ρ (Real.sqrt (1-ρ^2)) b x).const_mul (coeff f b))
  change (∫ y,f (fun i=>ρ*x i+Real.sqrt (1-ρ^2)*y i)-
    projectModes (lowerModes k) f (fun i=>ρ*x i+Real.sqrt (1-ρ^2)*y i) ∂γFin d)=_
  rw [integral_sub hfi hpi]
  change gaussianAverage ρ f x-gaussianAverage ρ (projectModes (lowerModes k) f) x=_
  rw [gaussianAverage_projectModes ρ hρ]

theorem gaussianAverage_continuous_bounded (ρ : ℝ) (f : (Fin d→ℝ)→ℝ)
    (hf : Continuous f) (M : ℝ) (hM : ∀ x,|f x| ≤ M) :
    Continuous (gaussianAverage ρ f) := by
  apply continuous_of_dominated (bound:=fun _ : Fin d→ℝ=>M)
  · intro x
    exact (hf.measurable.comp (by fun_prop)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y=>by simpa only [Real.norm_eq_abs] using hM _)
  · exact integrable_const M
  · exact Filter.Eventually.of_forall (fun y=>hf.comp (by fun_prop))

theorem gaussianAverage_abs_le_bounded (ρ : ℝ) (f : (Fin d→ℝ)→ℝ)
    (M : ℝ) (hM : ∀ x,|f x| ≤ M) (x : Fin d→ℝ) :
    |gaussianAverage ρ f x| ≤ M := by
  have hh := norm_integral_le_of_norm_le_const (μ:=γFin d)
    (f:=fun y=>f (fun i=>ρ*x i+Real.sqrt (1-ρ^2)*y i))
    (Filter.Eventually.of_forall (fun y=>by simpa only [Real.norm_eq_abs] using hM _))
  simpa only [gaussianAverage,Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs] using hh

/-- These are actual smooth-noise representatives, not arbitrary AE versions
restricted to a measure-zero facet. -/
theorem gaussianAverage_highModes_continuous_quadratic (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (k : ℕ) (hk : k ≤ 3) (f : (Fin d→ℝ)→ℝ)
    (hf : Continuous f) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x,|f x| ≤ M) :
    Continuous (fun x : FSC.Coord d=>gaussianAverage ρ (highModes k f) (fun j=>x j)) ∧
    ∃ C : ℝ,0 ≤ C ∧ ∀ x : FSC.Coord d,
      |gaussianAverage ρ (highModes k f) (fun j=>x j)| ≤ C*(1+‖x‖^2) := by
  have he := gaussianAverage_highModes_bounded ρ hρ k f hf.measurable M hM
  have hc : Continuous (fun x : Fin d→ℝ=>
      gaussianAverage ρ f x-∑ b∈lowerModes k,ρ^(degree b)*coeff f b*psi b x) :=
    (gaussianAverage_continuous_bounded ρ f hf M hM).sub
      (continuous_finsetSum _ (fun b _=>continuous_const.mul (continuous_psi b)))
  constructor
  · have hg : Continuous (gaussianAverage ρ (highModes k f)) := by
      convert hc using 1
      funext x
      exact he x
    exact hg.comp (by fun_prop)
  let C := M+∑ b∈lowerModes k,|ρ^(degree b)*coeff f b|
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro x
  rw [he]
  have hp : |∑ b∈lowerModes k,ρ^(degree b)*coeff f b*psi b (fun j=>x j)| ≤
      (∑ b∈lowerModes k,|ρ^(degree b)*coeff f b|)*(1+‖x‖^2) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b hb
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (psi_low_degree_growth b (lt_of_lt_of_le ((mem_lowerModes_iff k b).mp hb) hk) x)
      (abs_nonneg _)
  have hb := gaussianAverage_abs_le_bounded ρ f M hM (fun j=>x j)
  have ha := abs_sub (gaussianAverage ρ f (fun j=>x j))
    (∑ b∈lowerModes k,ρ^(degree b)*coeff f b*psi b (fun j=>x j))
  dsimp only [C]
  nlinarith [mul_nonneg hM0 (sq_nonneg ‖x‖)]

end NegativeVotingBoundedOUCellTests
