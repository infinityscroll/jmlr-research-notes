import GaussianDiagonalHazardDifferentiation

/-! Literal second derivatives of diagonal Gaussian pair densities.
These are pointwise identities. No integral differentiation, selected-offset
regularity, or uniform moment bound is inferred from them. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped BigOperators Topology Classical
namespace NegativeVotingHazardSecondDifferentiation
open NegativeVotingDiagonalHazardDifferentiation

def transportAcceleration (σ h σ₁ h₁ σ₂ h₂ x : ℝ) : ℝ :=
  h₂+(σ₂/σ-σ₁^2/σ^2)*(x-h)-σ₁*h₁/σ

def densityLogAcceleration (σ h σ₁ h₁ σ₂ h₂ x : ℝ) : ℝ :=
  -σ₂/σ+σ₁^2/σ^2+(x-h)*h₂/σ^2-h₁^2/σ^2-
  4*(x-h)*h₁*σ₁/σ^3+(x-h)^2*σ₂/σ^3-3*(x-h)^2*σ₁^2/σ^4

lemma transportSpeed_hasDerivAt (σ h σ₁ h₁ : ℝ→ℝ) (t σ₂ h₂ x : ℝ)
    (hσ : HasDerivAt σ (σ₁ t) t) (hh : HasDerivAt h (h₁ t) t)
    (hσ₁ : HasDerivAt σ₁ σ₂ t) (hh₁ : HasDerivAt h₁ h₂ t) (hpos : 0<σ t) :
    HasDerivAt (fun z=>transportSpeed (σ z) (h z) (σ₁ z) (h₁ z) x)
      (transportAcceleration (σ t) (h t) (σ₁ t) (h₁ t) σ₂ h₂ x) t := by
  have hd:=hh₁.add ((hσ₁.div hσ hpos.ne').mul ((hasDerivAt_const t x).sub hh))
  convert hd using 1
  · funext z; rfl
  · dsimp [transportAcceleration]; field_simp; ring

lemma densityLogDerivative_hasDerivAt (σ h σ₁ h₁ : ℝ→ℝ) (t σ₂ h₂ x : ℝ)
    (hσ : HasDerivAt σ (σ₁ t) t) (hh : HasDerivAt h (h₁ t) t)
    (hσ₁ : HasDerivAt σ₁ σ₂ t) (hh₁ : HasDerivAt h₁ h₂ t) (hpos : 0<σ t) :
    HasDerivAt (fun z=>densityLogDerivative (σ z) (h z) (σ₁ z) (h₁ z) x)
      (densityLogAcceleration (σ t) (h t) (σ₁ t) (h₁ t) σ₂ h₂ x) t := by
  have hu:HasDerivAt (fun z=>x-h z) (-h₁ t) t:=by
    convert (hasDerivAt_const t x).sub hh using 1 <;> simp
  have hd:=((hσ₁.neg.div hσ hpos.ne').add
    ((hu.mul hh₁).div (hσ.pow 2) (pow_ne_zero 2 hpos.ne'))).add
    (((hu.pow 2).mul hσ₁).div (hσ.pow 3) (pow_ne_zero 3 hpos.ne'))
  convert hd using 1
  · funext z; rfl
  · dsimp [densityLogAcceleration]; field_simp; ring

variable {V : Type*} [Fintype V] [DecidableEq V]

def hazardFluxAcceleration (σ h σ₁ h₁ σ₂ h₂ : V→ℝ) (x : ℝ) (k : V) : ℝ :=
  gaussianHazard (σ k) (h k) x*
    ((densityLogDerivative (σ k) (h k) (σ₁ k) (h₁ k) x+
      gaussianHazard (σ k) (h k) x*transportSpeed (σ k) (h k) (σ₁ k) (h₁ k) x)*
      transportSpeed (σ k) (h k) (σ₁ k) (h₁ k) x+
      transportAcceleration (σ k) (h k) (σ₁ k) (h₁ k) (σ₂ k) (h₂ k) x)

def hazardPairLogAcceleration (σ h σ₁ h₁ σ₂ h₂ : V→ℝ) (x : ℝ) (i j : V) : ℝ :=
  densityLogAcceleration (σ i) (h i) (σ₁ i) (h₁ i) (σ₂ i) (h₂ i) x+
  densityLogAcceleration (σ j) (h j) (σ₁ j) (h₁ j) (σ₂ j) (h₂ j) x+
  hazardFluxAcceleration σ h σ₁ h₁ σ₂ h₂ x i+
  hazardFluxAcceleration σ h σ₁ h₁ σ₂ h₂ x j-
  ∑k,hazardFluxAcceleration σ h σ₁ h₁ σ₂ h₂ x k

lemma hazardFlux_hasDerivAt (σ h σ₁ h₁ : V→ℝ→ℝ) (t x : ℝ) (σ₂ h₂ : V→ℝ)
    (hσ : ∀i,HasDerivAt (σ i) (σ₁ i t) t) (hh : ∀i,HasDerivAt (h i) (h₁ i t) t)
    (hσ₁ : ∀i,HasDerivAt (σ₁ i) (σ₂ i) t) (hh₁ : ∀i,HasDerivAt (h₁ i) (h₂ i) t)
    (hpos : ∀i,0<σ i t) (k : V) :
    HasDerivAt (fun z=>gaussianHazard (σ k z) (h k z) x*
      transportSpeed (σ k z) (h k z) (σ₁ k z) (h₁ k z) x)
      (hazardFluxAcceleration (fun i=>σ i t) (fun i=>h i t)
        (fun i=>σ₁ i t) (fun i=>h₁ i t) σ₂ h₂ x k) t := by
  have hd:=(gaussianHazard_hasDerivAt (σ k) (h k) t (σ₁ k t) (h₁ k t) x
    (hσ k) (hh k) (hpos k)).mul
    (transportSpeed_hasDerivAt (σ k) (h k) (σ₁ k) (h₁ k) t (σ₂ k) (h₂ k) x
      (hσ k) (hh k) (hσ₁ k) (hh₁ k) (hpos k))
  convert hd using 1
  · dsimp [hazardFluxAcceleration]; ring

lemma hazardPairLogDerivative_hasDerivAt (σ h σ₁ h₁ : V→ℝ→ℝ) (t x : ℝ) (σ₂ h₂ : V→ℝ)
    (hσ : ∀i,HasDerivAt (σ i) (σ₁ i t) t) (hh : ∀i,HasDerivAt (h i) (h₁ i t) t)
    (hσ₁ : ∀i,HasDerivAt (σ₁ i) (σ₂ i) t) (hh₁ : ∀i,HasDerivAt (h₁ i) (h₂ i) t)
    (hpos : ∀i,0<σ i t) (i j : V) :
    HasDerivAt (fun z=>hazardPairLogDerivative (fun k=>σ k z) (fun k=>h k z)
      (fun k=>σ₁ k z) (fun k=>h₁ k z) x i j)
      (hazardPairLogAcceleration (fun k=>σ k t) (fun k=>h k t)
        (fun k=>σ₁ k t) (fun k=>h₁ k t) σ₂ h₂ x i j) t := by
  have hD (k:V):=densityLogDerivative_hasDerivAt (σ k) (h k) (σ₁ k) (h₁ k)
    t (σ₂ k) (h₂ k) x (hσ k) (hh k) (hσ₁ k) (hh₁ k) (hpos k)
  have hF (k:V):=hazardFlux_hasDerivAt σ h σ₁ h₁ t x σ₂ h₂ hσ hh hσ₁ hh₁ hpos k
  have hS:=HasDerivAt.fun_sum (u:=Finset.univ) (fun k _=>hF k)
  exact ((((hD i).add (hD j)).add (hF i)).add (hF j)).sub hS

/-- The exact second derivative, including the all-label flux and diagonal
analytic pair. This theorem does not differentiate an integral. -/
theorem hazardPairDensity_second_hasDerivAt (σ h σ₁ h₁ : V→ℝ→ℝ) (t x : ℝ) (σ₂ h₂ : V→ℝ)
    (hσ : ∀i,HasDerivAt (σ i) (σ₁ i t) t) (hh : ∀i,HasDerivAt (h i) (h₁ i t) t)
    (hσ₁ : ∀i,HasDerivAt (σ₁ i) (σ₂ i) t) (hh₁ : ∀i,HasDerivAt (h₁ i) (h₂ i) t)
    (hpos : ∀i,0<σ i t) (i j : V) :
    HasDerivAt (fun z=>hazardPairDensity (fun k=>σ k z) (fun k=>h k z) x i j*
      hazardPairLogDerivative (fun k=>σ k z) (fun k=>h k z)
        (fun k=>σ₁ k z) (fun k=>h₁ k z) x i j)
      (hazardPairDensity (fun k=>σ k t) (fun k=>h k t) x i j*
        ((hazardPairLogDerivative (fun k=>σ k t) (fun k=>h k t)
          (fun k=>σ₁ k t) (fun k=>h₁ k t) x i j)^2+
        hazardPairLogAcceleration (fun k=>σ k t) (fun k=>h k t)
          (fun k=>σ₁ k t) (fun k=>h₁ k t) σ₂ h₂ x i j)) t := by
  have hd:=(hazardPairDensity_hasDerivAt σ h t x (fun k=>σ₁ k t) (fun k=>h₁ k t)
    hσ hh hpos i j).mul
    (hazardPairLogDerivative_hasDerivAt σ h σ₁ h₁ t x σ₂ h₂ hσ hh hσ₁ hh₁ hpos i j)
  convert hd using 1 <;> ring

end NegativeVotingHazardSecondDifferentiation
