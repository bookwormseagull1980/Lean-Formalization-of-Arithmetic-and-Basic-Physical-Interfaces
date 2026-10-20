module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Hermitian frame comparison upstream of the two source branches

Hermitian chart transitions and orthonormal matrix coordinates are general
mathematics. Their comparison hypotheses remain explicit. Each branch must
construct its own actual fibre and frames before using these results; this
module introduces no bundle or frame as a root input.
-/

@[expose] public section

noncomputable section

open scoped Bundle

namespace GeneratedFoundations.Geometry.HermitianFrames

section BundleFrames

variable {M H : Type*} [TopologicalSpace M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)] [TopologicalSpace (Bundle.TotalSpace H E)]

variable (e f k : Bundle.Trivialization H (π H E))
  [e.IsLinear ℂ] [f.IsLinear ℂ] [k.IsLinear ℂ]

/-- The Hermitian condition concerns the actual fiber metric on each chart. -/
def IsHermitianChart : Prop :=
  ∀ (x : M) (hx : x ∈ e.baseSet) (u v : E x),
    inner ℂ (e.linearEquivAt ℂ x hx u) (e.linearEquivAt ℂ x hx v) = inner ℂ u v

def frame (he : IsHermitianChart e) (x : M) (hx : x ∈ e.baseSet) :
    H ≃ₗᵢ[ℂ] E x :=
  (e.linearEquivAt ℂ x hx).symm.isometryOfInner (by
    intro u v
    have h := he x hx ((e.linearEquivAt ℂ x hx).symm u)
      ((e.linearEquivAt ℂ x hx).symm v)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm)

@[simp] theorem frame_apply (he : IsHermitianChart e) (x : M)
    (hx : x ∈ e.baseSet) (v : H) :
    frame e he x hx v = (e.linearEquivAt ℂ x hx).symm v := rfl

@[simp] theorem frame_symm_apply (he : IsHermitianChart e) (x : M)
    (hx : x ∈ e.baseSet) (v : E x) :
    (frame e he x hx).symm v = e.linearEquivAt ℂ x hx v := rfl

/-- If `e' = e g`, the change `g` sends new components to old components. -/
def transition (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) : H ≃ₗᵢ[ℂ] H :=
  (frame f hf x hy).trans (frame e he x hx).symm

theorem frame_transition (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (v : H) :
    frame e he x hx (transition e f he hf x hx hy v) = frame f hf x hy v :=
  (frame e he x hx).apply_symm_apply (frame f hf x hy v)

theorem transition_unique (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet)
    (g : H ≃ₗᵢ[ℂ] H)
    (hg : ∀ v, frame e he x hx (g v) = frame f hf x hy v) :
    g = transition e f he hf x hx hy := by
  ext v
  apply (frame e he x hx).injective
  rw [frame_transition]
  exact hg v

theorem passive_components (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (v : E x) :
    (frame f hf x hy).symm v =
      (transition e f he hf x hx hy).symm ((frame e he x hx).symm v) :=
  (congrArg (frame f hf x hy).symm ((frame e he x hx).apply_symm_apply v)).symm

@[simp] theorem transition_self (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) : transition e e he he x hx hx = 1 := by
  ext v
  simp [transition]

theorem transition_inverse (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    (transition e f he hf x hx hy).symm = transition f e hf he x hy hx := by
  ext v
  simp [transition]

theorem transition_cocycle (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (hk : IsHermitianChart k) (x : M)
    (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (hz : x ∈ k.baseSet) :
    transition e f he hf x hx hy * transition f k hf hk x hy hz =
      transition e k he hk x hx hz := by
  apply LinearIsometryEquiv.ext
  intro v
  exact congrArg (frame e he x hx).symm
    ((frame f hf x hy).apply_symm_apply (frame k hk x hz v))

/-- The bundle coordinate change is defined off the overlap by the library's
identity extension. Its geometric meaning is used only on the overlap. -/
def overlapOperator (x : M) : H →L[ℂ] H := f.coordChangeL ℂ e x

theorem overlapOperator_eq_transition (he : IsHermitianChart e)
    (hf : IsHermitianChart f) (x : M)
    (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    overlapOperator e f x =
      (transition e f he hf x hx hy).toContinuousLinearEquiv.toContinuousLinearMap := by
  ext v
  change f.coordChangeL ℂ e x v = _
  rw [Bundle.Trivialization.coe_coordChangeL f e ⟨hy, hx⟩]
  rfl

theorem overlapOperator_inner (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (u v : H) :
    inner ℂ (overlapOperator e f x u) (overlapOperator e f x v) = inner ℂ u v := by
  rw [overlapOperator_eq_transition e f he hf x hx hy]
  exact (transition e f he hf x hx hy).inner_map_map u v

theorem overlapOperator_continuousOn [FiberBundle H E] [VectorBundle ℂ H E]
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    ContinuousOn (overlapOperator e f) (e.baseSet ∩ f.baseSet) := by
  unfold overlapOperator
  rw [Set.inter_comm]
  exact continuousOn_coordChange (R := ℂ) f e

end BundleFrames

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ H)

def frameMatrix (g : H ≃ₗᵢ[ℂ] H) : Matrix (Fin n) (Fin n) ℂ :=
  g.toMatrix b.toBasis b.toBasis

omit [FiniteDimensional ℂ H] in
theorem frameMatrix_unitary (g : H ≃ₗᵢ[ℂ] H) :
    frameMatrix b g ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  g.toMatrix_mem_unitaryGroup b b

theorem matrixOperator_unitary (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (LinearMap.toMatrixOrthonormal b).symm M ∈ unitary (Module.End ℂ H) := by
  apply Unitary.mem_iff.mpr
  constructor
  · simpa only [map_mul, map_star, map_one] using
      congrArg (LinearMap.toMatrixOrthonormal b).symm (Unitary.star_mul_self_of_mem hM)
  · simpa only [map_mul, map_star, map_one] using
      congrArg (LinearMap.toMatrixOrthonormal b).symm (Unitary.mul_star_self_of_mem hM)

/-- Every unitary coordinate matrix is realized by a frame change of the actual fiber. -/
def frameOfMatrix (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin n) ℂ) : H ≃ₗᵢ[ℂ] H := by
  let A := (LinearMap.toMatrixOrthonormal b).symm M
  have hA := matrixOperator_unitary b M hM
  have hleft : A.adjoint * A = 1 := Unitary.star_mul_self_of_mem hA
  have hright : A * A.adjoint = 1 := Unitary.mul_star_self_of_mem hA
  let e : H ≃ₗ[ℂ] H := LinearEquiv.ofLinearMap A A.adjoint hright hleft
  exact e.isometryOfInner (by
    intro x y
    change inner ℂ (A x) (A y) = inner ℂ x y
    rw [← LinearMap.adjoint_inner_right]
    have hy : A.adjoint (A y) = y := LinearMap.congr_fun hleft y
    rw [hy])

@[simp] theorem frameMatrix_frameOfMatrix (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    frameMatrix b (frameOfMatrix b M hM) = M := by
  change (LinearMap.toMatrixOrthonormal b) ((LinearMap.toMatrixOrthonormal b).symm M) = M
  exact (LinearMap.toMatrixOrthonormal b).apply_symm_apply M

theorem frameMatrix_injective : Function.Injective (frameMatrix b) := by
  intro g h hgh
  have he : g.toLinearMap = h.toLinearMap := (LinearMap.toMatrixOrthonormal b).injective hgh
  ext v
  exact LinearMap.congr_fun he v

theorem frameMatrix_existsUnique (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃! g : H ≃ₗᵢ[ℂ] H, frameMatrix b g = M := by
  refine ⟨frameOfMatrix b M hM, frameMatrix_frameOfMatrix b M hM, ?_⟩
  intro g hg
  apply frameMatrix_injective b
  rw [hg, frameMatrix_frameOfMatrix]

omit [FiniteDimensional ℂ H] in
theorem frameMatrix_specialUnitary_iff (g : H ≃ₗᵢ[ℂ] H) :
    frameMatrix b g ∈ Matrix.specialUnitaryGroup (Fin n) ℂ ↔
      (frameMatrix b g).det = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact and_iff_right (frameMatrix_unitary b g)

end Coordinates

end GeneratedFoundations.Geometry.HermitianFrames
