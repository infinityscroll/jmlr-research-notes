import GaussianFanOptimizedValue
import GaussianRegularMaximumMoments
import GaussianMassCentroid

/-! Actual finite Gaussian assignment duality, including duplicate score rows.
The primal rule is constructed by grouping identical rows and splitting each
group's realized Gaussian mass in the requested fixed proportions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Classical RealInnerProductSpace
namespace NegativeVotingAssignmentDuality
open NegativeVoting NegativeVotingFan NegativeVotingFanInverse NegativeVotingFanValue
  NegativeVotingMassCentroid NegativeVotingRegularMaximum

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

def assignmentValue (B : ι → FSC.Coord d) (f : FSC.Coord d → ι → ℝ) : ℝ :=
  ∫ x, ∑ i, f x i*inner ℝ (B i) x ∂stdGaussian (FSC.Coord d)

def Feasible (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ) : Prop :=
  (∀ i, AEMeasurable (fun x => f x i) (stdGaussian (FSC.Coord d))) ∧
  (∀ᵐ x ∂stdGaussian (FSC.Coord d), SimplexWeights (f x)) ∧
  ∀ i, (∫ x, f x i ∂stdGaussian (FSC.Coord d))=p i

theorem feasible_coordinate_bounds (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i : ι) :
    ∀ᵐ x ∂stdGaussian (FSC.Coord d), 0 ≤ f x i ∧ f x i ≤ 1 :=
  hf.2.1.mono (fun x hx => ⟨hx.1 i,simplex_weight_le_one (f x) hx i⟩)

theorem feasible_coordinate_integrable (p : ι → ℝ) (f : FSC.Coord d → ι → ℝ)
    (hf : Feasible p f) (i : ι) :
    Integrable (fun x => f x i) (stdGaussian (FSC.Coord d)) :=
  fractional_integrable _ _ (hf.1 i) (feasible_coordinate_bounds p f hf i)

theorem assignmentValue_integrable (B : ι → FSC.Coord d) (p : ι → ℝ)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f) :
    Integrable (fun x => ∑ i, f x i*inner ℝ (B i) x) (stdGaussian (FSC.Coord d)) := by
  apply integrable_finsetSum
  intro i _
  exact fractional_mul_integrable _ _ _ (hf.1 i) (feasible_coordinate_bounds p f hf i)
    (IsGaussian.integrable_dual _ (innerSL ℝ (B i)))

theorem feasible_weighted_scores_integrable (B : ι → FSC.Coord d) (p h : ι → ℝ)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f) :
    Integrable (fun x => ∑ i, f x i*scores B h x i) (stdGaussian (FSC.Coord d)) := by
  apply integrable_finsetSum
  intro i _
  exact fractional_mul_integrable _ _ _ (hf.1 i) (feasible_coordinate_bounds p f hf i)
    (score_integrable B h i)

theorem integral_weighted_scores_eq (B : ι → FSC.Coord d) (p h : ι → ℝ)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f) :
    (∫ x, ∑ i, f x i*scores B h x i ∂stdGaussian (FSC.Coord d))=
      assignmentValue B f+∑ i, p i*h i := by
  have he : (fun x => ∑ i, f x i*scores B h x i)=
      (fun x => (∑ i, f x i*inner ℝ (B i) x)+(∑ i, f x i*h i)) := by
    funext x
    simp only [scores,mul_add,Finset.sum_add_distrib]
  have ho : Integrable (fun x => ∑ i, f x i*h i) (stdGaussian (FSC.Coord d)) :=
    integrable_finsetSum _ (fun i _ => (feasible_coordinate_integrable p f hf i).mul_const _)
  rw [he,integral_add (assignmentValue_integrable B p f hf) ho,
    integral_finsetSum Finset.univ (fun i _ => (feasible_coordinate_integrable p f hf i).mul_const _)]
  simp only [integral_mul_const,hf.2.2,assignmentValue]

/-- Every actual feasible fractional assignment lies below every dual offset. -/
theorem assignmentValue_le_potential (B : ι → FSC.Coord d) (p h : ι → ℝ)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f) :
    assignmentValue B f ≤ potential B p h := by
  have hpw : ∀ᵐ x ∂stdGaussian (FSC.Coord d),
      (∑ i, f x i*scores B h x i) ≤ maxScore (scores B h x) := by
    filter_upwards [hf.2.1] with x hx
    calc
      _ ≤ ∑ i, f x i*maxScore (scores B h x) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (Finset.le_sup' (f:=scores B h x) (Finset.mem_univ i)) (hx.1 i))
      _ = _ := by rw [←Finset.sum_mul,hx.2,one_mul]
  have hi := integral_mono_ae (feasible_weighted_scores_integrable B p h f hf)
    (max_integrable B h) hpw
  rw [integral_weighted_scores_eq B p h f hf] at hi
  change assignmentValue B f+∑ i, p i*h i ≤ expectedMax B h at hi
  unfold potential
  linarith

theorem assignmentValue_le_optimizedValue (B : ι → FSC.Coord d) (p : ι → ℝ)
    (f : FSC.Coord d → ι → ℝ) (hf : Feasible p f) :
    assignmentValue B f ≤ optimizedValue B p := by
  apply le_csInf (Set.range_nonempty _)
  rintro z ⟨h,rfl⟩
  exact assignmentValue_le_potential B p h f hf

theorem potential_centering (B : ι → FSC.Coord d) (p h : ι → ℝ)
    (hs : ∑ i, p i=1) : potential B p (centering h)=potential B p h := by
  let c := (∑ i, h i)/(Fintype.card ι:ℝ)
  have hm (x : FSC.Coord d) : maxScore (scores B (centering h) x)=maxScore (scores B h x)-c := by
    have he : scores B (centering h) x=fun i => scores B h x i-c := by
      funext i
      simp only [scores,centering_apply,c]
      ring
    rw [he]
    exact maxScore_sub_const _ c
  have hE : expectedMax B (centering h)=expectedMax B h-c := by
    unfold expectedMax
    simp_rw [hm]
    rw [integral_sub (max_integrable B h) (integrable_const c)]
    simp
  have hP : (∑ i, p i*(centering h : ι → ℝ) i)=(∑ i, p i*h i)-c := by
    simp only [centering_apply,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hs,one_mul,c]
  unfold potential
  rw [hE,hP]
  ring

abbrev Sites (B : ι → FSC.Coord d) := Set.range B

def site (B : ι → FSC.Coord d) (i : ι) : Sites B := ⟨B i,Set.mem_range_self i⟩

theorem site_surjective (B : ι → FSC.Coord d) : Function.Surjective (site B) := by
  rintro ⟨x,⟨i,rfl⟩⟩
  exact ⟨i,rfl⟩

noncomputable instance sitesFintype (B : ι → FSC.Coord d) : Fintype (Sites B) :=
  Fintype.ofSurjective (site B) (site_surjective B)

instance sitesNonempty (B : ι → FSC.Coord d) : Nonempty (Sites B) :=
  ⟨site B (Classical.choice inferInstance)⟩

def groupMass (B : ι → FSC.Coord d) (p : ι → ℝ) (s : Sites B) : ℝ :=
  ∑ i, if site B i=s then p i else 0

theorem groupMass_sum (B : ι → FSC.Coord d) (p : ι → ℝ) :
    (∑ s : Sites B, groupMass B p s)=∑ i, p i := by
  unfold groupMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem groupMass_pos (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (s : Sites B) : 0 < groupMass B p s := by
  obtain ⟨i,hi⟩ := site_surjective B s
  unfold groupMass
  apply lt_of_lt_of_le (hp i)
  have h : (if site B i=s then p i else 0) ≤
      ∑ j, if site B j=s then p j else 0 := Finset.single_le_sum
    (f:=fun j => if site B j=s then p j else 0)
    (fun j (_ : j ∈ Finset.univ) => by
      split_ifs
      · exact (hp j).le
      · exact le_rfl)
    (Finset.mem_univ i)
  simpa only [hi,ite_true] using h

/-- Summation over duplicate labels cancels their exact group mass. -/
theorem grouped_distributed_sum (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (g : Sites B → ℝ) :
    (∑ i, (p i/groupMass B p (site B i))*g (site B i))=∑ s, g s := by
  calc
    _ = ∑ s : Sites B, ∑ i, if site B i=s then (p i/groupMass B p s)*g s else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = ∑ s : Sites B, (groupMass B p s/groupMass B p s)*g s := by
      apply Finset.sum_congr rfl
      intro s _
      unfold groupMass
      rw [Finset.sum_div,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [div_self (groupMass_pos B p hp s).ne',one_mul]

theorem maxScore_pullback (B : ι → FSC.Coord d) (s : Sites B → ℝ) :
    maxScore (fun i => s (site B i))=maxScore s := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    exact Finset.le_sup' (f:=s) (Finset.mem_univ (site B i))
  · apply Finset.sup'_le
    intro a _
    obtain ⟨i,rfl⟩ := site_surjective B a
    exact Finset.le_sup' (f:=fun i => s (site B i)) (Finset.mem_univ i)


def distributedRule (B : ι → FSC.Coord d) (p : ι → ℝ) (h : Sites B → ℝ)
    (x : FSC.Coord d) (i : ι) : ℝ :=
  (p i/groupMass B p (site B i))*weights (fun s : Sites B => s.val) h x (site B i)

def pulledOffsets (B : ι → FSC.Coord d) (h : Sites B → ℝ) (i : ι) : ℝ := h (site B i)

theorem distributedRule_measurable (B : ι → FSC.Coord d) (p : ι → ℝ)
    (h : Sites B → ℝ) (i : ι) : Measurable (fun x => distributedRule B p h x i) :=
  (weights_measurable (fun s : Sites B => s.val) h (site B i)).const_mul _

theorem distributedRule_simplex (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (h : Sites B → ℝ) (x : FSC.Coord d) :
    SimplexWeights (distributedRule B p h x) := by
  constructor
  · intro i
    exact mul_nonneg (div_nonneg (hp i).le (groupMass_pos B p hp (site B i)).le)
      ((weights_simplex (fun s : Sites B => s.val) h x).1 (site B i))
  · exact (grouped_distributed_sum B p hp (weights (fun s : Sites B => s.val) h x)).trans
      (weights_simplex (fun s : Sites B => s.val) h x).2

theorem distributedRule_mass (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (h : Sites B → ℝ)
    (hm : ∀ s, mass (fun s : Sites B => s.val) h s=groupMass B p s) (i : ι) :
    (∫ x, distributedRule B p h x i ∂stdGaussian (FSC.Coord d))=p i := by
  unfold distributedRule
  rw [integral_const_mul]
  change (p i/groupMass B p (site B i))*mass (fun s : Sites B => s.val) h (site B i)=p i
  rw [hm]
  field_simp [(groupMass_pos B p hp (site B i)).ne']

theorem distributedRule_feasible (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (h : Sites B → ℝ)
    (hm : ∀ s, mass (fun s : Sites B => s.val) h s=groupMass B p s) :
    Feasible p (distributedRule B p h) :=
  ⟨fun i => (distributedRule_measurable B p h i).aemeasurable,
    ae_of_all _ (distributedRule_simplex B p hp h),distributedRule_mass B p hp h hm⟩

theorem distributedRule_weighted_score (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (h : Sites B → ℝ) (x : FSC.Coord d) :
    (∑ i, distributedRule B p h x i*scores B (pulledOffsets B h) x i)=
      maxScore (scores B (pulledOffsets B h) x) := by
  let Q : Sites B → FSC.Coord d := fun s => s.val
  have hs (i : ι) : scores B (pulledOffsets B h) x i=scores Q h x (site B i) := rfl
  calc
    _ = ∑ i, (p i/groupMass B p (site B i))*
        (weights Q h x (site B i)*scores Q h x (site B i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hs]
      simp only [distributedRule,Q]
      ring
    _ = ∑ s, weights Q h x s*scores Q h x s :=
      grouped_distributed_sum B p hp (fun s => weights Q h x s*scores Q h x s)
    _ = maxScore (scores Q h x) := maxWeights_score_identity _
    _ = _ := by
      rw [←maxScore_pullback B (scores Q h x)]
      rfl

theorem distributedRule_value_eq_potential (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (h : Sites B → ℝ)
    (hm : ∀ s, mass (fun s : Sites B => s.val) h s=groupMass B p s) :
    assignmentValue B (distributedRule B p h)=potential B p (pulledOffsets B h) := by
  have hf := distributedRule_feasible B p hp h hm
  have he : (∫ x, ∑ i, distributedRule B p h x i*scores B (pulledOffsets B h) x i
      ∂stdGaussian (FSC.Coord d))=expectedMax B (pulledOffsets B h) :=
    integral_congr_ae (ae_of_all _ (distributedRule_weighted_score B p hp h))
  rw [integral_weighted_scores_eq B p (pulledOffsets B h) (distributedRule B p h) hf] at he
  unfold potential
  linarith

/-- Actual primal and dual attainment for every finite row system, including
duplicate rows. The constructed fractional rule is Borel and pointwise simplex. -/
theorem exists_assignment_and_offsets (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1) :
    ∃ (h : centeredGauge ι) (f : FSC.Coord d → ι → ℝ),
      (∀ i, Measurable (fun x => f x i)) ∧ (∀ x, SimplexWeights (f x)) ∧
      (∀ i, (∫ x, f x i ∂stdGaussian (FSC.Coord d))=p i) ∧
      assignmentValue B f=optimizedValue B p ∧ optimizedValue B p=potential B p h := by
  let Q : Sites B → FSC.Coord d := fun s => s.val
  have hQ : Function.Injective Q := Subtype.val_injective
  obtain ⟨h,_,hm⟩ := exists_offsets_with_prescribed_masses Q hQ (groupMass B p)
    (groupMass_pos B p hp) ((groupMass_sum B p).trans hs)
  let f := distributedRule B p h
  let k := centering (pulledOffsets B h)
  have hf : Feasible p f := distributedRule_feasible B p hp h hm
  have hpot : assignmentValue B f=potential B p k :=
    (distributedRule_value_eq_potential B p hp h hm).trans (potential_centering B p _ hs).symm
  have hvalue : assignmentValue B f=optimizedValue B p := by
    apply le_antisymm (assignmentValue_le_optimizedValue B p f hf)
    have hu := optimizedValue_le_potential B p (fun i => (hp i).le) hs k
    rwa [←hpot] at hu
  exact ⟨k,f,distributedRule_measurable B p h,distributedRule_simplex B p hp h,
    distributedRule_mass B p hp h hm,hvalue,hvalue.symm.trans hpot⟩

def feasibleValues (B : ι → FSC.Coord d) (p : ι → ℝ) : Set ℝ :=
  {v | ∃ f : FSC.Coord d → ι → ℝ, Feasible p f ∧ assignmentValue B f=v}

/-- The literal optimized Gaussian dual value is the attained greatest value
among all completed-measurable fractional assignments with the actual masses. -/
theorem optimizedValue_isGreatest (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1) :
    IsGreatest (feasibleValues B p) (optimizedValue B p) := by
  obtain ⟨h,f,hf,hfp,hfm,hv,_⟩ := exists_assignment_and_offsets B p hp hs
  refine ⟨⟨f,⟨fun i => (hf i).aemeasurable,ae_of_all _ hfp,hfm⟩,hv⟩,?_⟩
  rintro v ⟨g,hg,rfl⟩
  exact assignmentValue_le_optimizedValue B p g hg

theorem optimizedValue_eq_sSup (B : ι → FSC.Coord d) (p : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i=1) :
    optimizedValue B p=sSup (feasibleValues B p) :=
  (optimizedValue_isGreatest B p hp hs).csSup_eq.symm

end NegativeVotingAssignmentDuality
