module

public import GeneratedFoundations.Arithmetic.HistoryEffectiveFrames

/-!
# The complete Hilbert space of effective arithmetic responses

Every matrix coefficient on the actual history--phase/source carrier is retained.
Flattening the pair of indices supplies the Hilbert--Schmidt inner product;
the coordinate equivalence below proves that it is exactly the already defined
trace pairing. In particular, this construction does not replace a matrix by
its diagonal, trace, or elementary part.

The effective source group acts by the same complete conjugation as before.
Its action is now realized as a faithful unitary representation of the full
response Hilbert space. The quotient removes the simultaneous source sign
from operator responses; the original state representation still retains it.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryEffectiveResponseSpace

open HistoryCliffordAction HistoryElementaryConnector HistoryEffectiveFrames

abbrev ResponseSpace (N : ℕ) := EuclideanSpace ℂ (Index N × Index N)

/-- Coordinates include both matrix indices, including all off-diagonal ones. -/
def matrixEquiv (N : ℕ) : ResponseSpace N ≃ₗ[ℂ] Algebra N where
  toFun x i j := x (i, j)
  invFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  left_inv x := by ext ⟨i, j⟩; rfl
  right_inv A := by ext i j; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem matrixEquiv_apply (N : ℕ) (x : ResponseSpace N) (i j : Index N) :
    matrixEquiv N x i j = x (i, j) := rfl

/-- The full coordinate inner product is the full matrix trace pairing. -/
theorem inner_eq_responseInner (N : ℕ) (x y : ResponseSpace N) :
    inner ℂ x y = responseInner N (matrixEquiv N x) (matrixEquiv N y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply',
    responseInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, matrixEquiv_apply]
  change (∑ ij : Index N × Index N, star (x ij) * y ij) =
    ∑ i : Index N, ∑ j : Index N, star (x (j, i)) * y (j, i)
  rw [Fintype.sum_prod_type, Finset.sum_comm]

def linearResponse (N : ℕ) (q : EffectiveFrame) :
    ResponseSpace N →ₗ[ℂ] ResponseSpace N where
  toFun x := (matrixEquiv N).symm (effectiveConjugation N q (matrixEquiv N x))
  map_add' x y := by
    apply (matrixEquiv N).injective
    induction q using Quotient.inductionOn' with
    | h g =>
      simp only [map_add, LinearEquiv.apply_symm_apply]
      change conjugate N g (matrixEquiv N x + matrixEquiv N y) =
        conjugate N g (matrixEquiv N x) + conjugate N g (matrixEquiv N y)
      exact conjugate_add N g _ _
  map_smul' c x := by
    apply (matrixEquiv N).injective
    induction q using Quotient.inductionOn' with
    | h g =>
      simp only [map_smul, LinearEquiv.apply_symm_apply, RingHom.id_apply]
      change conjugate N g (c • matrixEquiv N x) = c • conjugate N g (matrixEquiv N x)
      exact conjugate_smul N g c _

@[simp] theorem matrix_linearResponse (N : ℕ) (q : EffectiveFrame)
    (x : ResponseSpace N) :
    matrixEquiv N (linearResponse N q x) =
      effectiveConjugation N q (matrixEquiv N x) :=
  (matrixEquiv N).apply_symm_apply _

def representation (N : ℕ) : EffectiveFrame →* Module.End ℂ (ResponseSpace N) where
  toFun := linearResponse N
  map_one' := by
    apply LinearMap.ext
    intro x
    apply (matrixEquiv N).injective
    simp
  map_mul' q r := by
    apply LinearMap.ext
    intro x
    apply (matrixEquiv N).injective
    simp only [Module.End.mul_apply, matrix_linearResponse, map_mul,
      Equiv.Perm.mul_apply]

theorem representation_inner (N : ℕ) (q : EffectiveFrame) (x y : ResponseSpace N) :
    inner ℂ (representation N q x) (representation N q y) = inner ℂ x y := by
  rw [inner_eq_responseInner, inner_eq_responseInner N x y]
  change responseInner N (matrixEquiv N (linearResponse N q x))
    (matrixEquiv N (linearResponse N q y)) = _
  rw [matrix_linearResponse, matrix_linearResponse, effectiveConjugation_inner]

def unitaryAction (N : ℕ) (q : EffectiveFrame) :
    ResponseSpace N ≃ₗᵢ[ℂ] ResponseSpace N :=
  (Operations.UnitaryRepresentation.representationLinearEquiv
    (representation N) q).isometryOfInner (representation_inner N q)

@[simp] theorem unitaryAction_apply (N : ℕ) (q : EffectiveFrame)
    (x : ResponseSpace N) : unitaryAction N q x = representation N q x := rfl

@[simp] theorem unitaryAction_symm_apply (N : ℕ) (q : EffectiveFrame)
    (x : ResponseSpace N) : (unitaryAction N q).symm x = representation N q⁻¹ x := rfl

def unitaryRepresentation (N : ℕ) :
    EffectiveFrame →* (ResponseSpace N ≃ₗᵢ[ℂ] ResponseSpace N) where
  toFun := unitaryAction N
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change representation N 1 x = x
    rw [map_one]
    rfl
  map_mul' q r := by
    apply LinearIsometryEquiv.ext
    intro x
    change representation N (q * r) x = representation N q (representation N r x)
    rw [map_mul]
    rfl

theorem representation_faithful (N : ℕ) : Function.Injective (representation N) := by
  intro q r he
  apply effectiveConjugation_faithful N
  apply Equiv.ext
  intro A
  obtain ⟨x, rfl⟩ := (matrixEquiv N).surjective A
  have hx := congrArg (fun K : Module.End ℂ (ResponseSpace N) =>
    matrixEquiv N (K x)) he
  exact hx

theorem unitaryRepresentation_faithful (N : ℕ) :
    Function.Injective (unitaryRepresentation N) := by
  intro q r he
  apply representation_faithful N
  apply LinearMap.ext
  intro x
  exact congrArg (fun U : ResponseSpace N ≃ₗᵢ[ℂ] ResponseSpace N => U x) he

theorem representation_adjoint (N : ℕ) (q : EffectiveFrame) :
    (representation N q).adjoint = representation N q⁻¹ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have h := representation_inner N q (representation N q⁻¹ x) y
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply] using h.symm

theorem representation_mem_unitary (N : ℕ) (q : EffectiveFrame) :
    representation N q ∈ unitary (Module.End ℂ (ResponseSpace N)) :=
  Operations.UnitaryRepresentation.representation_mem_unitary_of_adjoint
    (representation N) (representation_adjoint N) q

theorem representation_norm (N : ℕ) (q : EffectiveFrame) (x : ResponseSpace N) :
    ‖representation N q x‖ = ‖x‖ := (unitaryAction N q).norm_map x

/-- Quotient representatives act on the actual complete matrix, with no new
response coefficients or comparison choices. -/
theorem unitaryRepresentation_quotient (N : ℕ) (g : Frame)
    (x : ResponseSpace N) :
    matrixEquiv N (unitaryRepresentation N
      (Geometry.SourceFrameQuotient.quotientMap g) x) =
      conjugate N g (matrixEquiv N x) := matrix_linearResponse N _ x

theorem unitaryRepresentation_unique (N : ℕ)
    (R : EffectiveFrame →* (ResponseSpace N ≃ₗᵢ[ℂ] ResponseSpace N))
    (hR : ∀ g x, matrixEquiv N (R (Geometry.SourceFrameQuotient.quotientMap g) x) =
      conjugate N g (matrixEquiv N x)) : R = unitaryRepresentation N := by
  apply MonoidHom.ext
  intro q
  apply LinearIsometryEquiv.ext
  intro x
  apply (matrixEquiv N).injective
  induction q using Quotient.inductionOn' with
  | h g => exact (hR g x).trans (unitaryRepresentation_quotient N g x).symm

structure Conclusions : Prop where
  full_trace_pairing : ∀ N (x y : ResponseSpace N),
    inner ℂ x y = responseInner N (matrixEquiv N x) (matrixEquiv N y)
  faithful_effective_action : ∀ N, Function.Injective (unitaryRepresentation N)
  actual_adjoint : ∀ N q,
    (representation N q).adjoint = representation N q⁻¹
  norm_preservation : ∀ N q (x : ResponseSpace N), ‖representation N q x‖ = ‖x‖
  all_matrix_entries : ∀ N g (x : ResponseSpace N),
    matrixEquiv N (unitaryRepresentation N
      (Geometry.SourceFrameQuotient.quotientMap g) x) = conjugate N g (matrixEquiv N x)

theorem generated : Conclusions where
  full_trace_pairing := inner_eq_responseInner
  faithful_effective_action := unitaryRepresentation_faithful
  actual_adjoint := representation_adjoint
  norm_preservation := representation_norm
  all_matrix_entries := unitaryRepresentation_quotient

end GeneratedFoundations.Arithmetic.HistoryEffectiveResponseSpace
