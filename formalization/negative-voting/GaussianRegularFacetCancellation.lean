import GaussianFanCover
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Exact regular-quadratic cancellations on the current affine comparison
plane.  The regular quadratic is explicit here; identification with actual
Gaussian second moments is a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped RealInnerProductSpace
namespace NegativeVotingRegularFacetCancellation
open NegativeVotingFan
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def regularJump (r : ι → E) (γ : ℝ) (i j : ι) (x : E) : ℝ :=
  γ*((inner ℝ (r i) x)^2-(inner ℝ (r j) x)^2)

def rowError (B r : ι → E) (α : ℝ) (i : ι) : E := B i-α • r i

def errorGap (B r : ι → E) (h : ι → ℝ) (α : ℝ) (i j : ι) (x : E) : ℝ :=
  inner ℝ (rowError B r α i-rowError B r α j) x+h i-h j

/-- The score difference of the reference rows equals minus the perturbation
on the current facet, not just on the reference facet. -/
theorem reference_gap_on_facet (B r : ι → E) (h : ι → ℝ) (α : ℝ)
    (i j : ι) (x : E) (hx : x ∈ affineFacet B h i j) :
    α*(inner ℝ (r i) x-inner ℝ (r j) x) = -errorGap B r h α i j x := by
  have hh := hx.1
  simp only [affineScore] at hh
  simp only [errorGap,rowError,inner_sub_left,real_inner_smul_left]
  linarith

/-- The regular quadratic jump has a literal row-error factor on each
current affine facet. This is the cancellation needed before absolute values. -/
theorem regularJump_on_facet (B r : ι → E) (h : ι → ℝ) (α γ : ℝ)
    (hα : α ≠ 0) (i j : ι) (x : E) (hx : x ∈ affineFacet B h i j) :
    regularJump r γ i j x = -(γ/α)*errorGap B r h α i j x*
      (inner ℝ (r i) x+inner ℝ (r j) x) := by
  have hh := reference_gap_on_facet B r h α i j x hx
  have he : errorGap B r h α i j x = -α*(inner ℝ (r i) x-inner ℝ (r j) x) := by linarith
  rw [he]
  unfold regularJump
  field_simp
  ring

/-- Exact directional derivative of the explicit quadratic jump. -/
theorem hasDerivAt_regularJump_line (r : ι → E) (γ : ℝ) (i j : ι) (x V : E) :
    HasDerivAt (fun t : ℝ => regularJump r γ i j (x+t • V))
      (2*γ*(inner ℝ (r i) x*inner ℝ (r i) V-
        inner ℝ (r j) x*inner ℝ (r j) V)) 0 := by
  have hi : HasDerivAt (fun t : ℝ => inner ℝ (r i) x+t*inner ℝ (r i) V)
      (inner ℝ (r i) V) 0 := by
    simpa only [one_mul,id_eq] using ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ (r i) V)).const_add
      (inner ℝ (r i) x)
  have hj : HasDerivAt (fun t : ℝ => inner ℝ (r j) x+t*inner ℝ (r j) V)
      (inner ℝ (r j) V) 0 := by
    simpa only [one_mul,id_eq] using ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ (r j) V)).const_add
      (inner ℝ (r j) x)
  convert ((hi.pow 2).sub (hj.pow 2)).const_mul γ using 1
  · ext t
    simp [regularJump,inner_add_right,inner_smul_right]
  · simp
    ring

/-- Material derivative cancellation with the negative transport convention
of the moving-cell formula. No inverse singular-value estimate is used. -/
theorem regularJump_material_on_facet (B r : ι → E) (h : ι → ℝ)
    (α γ ℓ : ℝ) (hα : α ≠ 0) (i j : ι) (x V : E)
    (hx : x ∈ affineFacet B h i j) (hV : inner ℝ (B i-B j) V = -ℓ) :
    2*γ*(inner ℝ (r i) x*inner ℝ (r i) V-
      inner ℝ (r j) x*inner ℝ (r j) V) =
    -(γ/α)*((inner ℝ (r i) x+inner ℝ (r j) x)*ℓ+
      (inner ℝ (r i) x+inner ℝ (r j) x)*
        inner ℝ (rowError B r α i-rowError B r α j) V+
      errorGap B r h α i j x*inner ℝ (r i+r j) V) := by
  have hg := reference_gap_on_facet B r h α i j x hx
  have hv : α*(inner ℝ (r i) V-inner ℝ (r j) V) =
      -ℓ-inner ℝ (rowError B r α i-rowError B r α j) V := by
    simp only [rowError,inner_sub_left,real_inner_smul_left] at *
    linarith
  have he : errorGap B r h α i j x = -α*(inner ℝ (r i) x-inner ℝ (r j) x) := by linarith
  have heV : inner ℝ (rowError B r α i-rowError B r α j) V =
      -ℓ-α*(inner ℝ (r i) V-inner ℝ (r j) V) := by linarith
  rw [he,heV,inner_add_left]
  field_simp
  ring

end NegativeVotingRegularFacetCancellation
