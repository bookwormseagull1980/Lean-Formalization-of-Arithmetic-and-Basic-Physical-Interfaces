module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Unitary realizations of an actual algebraic group response

An algebraic response already determines its inverse. When its Hilbert
adjoint is that inverse, it also determines the isometry and preserves every
sesquilinear observation. The carrier and group in these comparison lemmas
are instantiated separately by each generated branch.
-/

@[expose] public section

namespace GeneratedFoundations.Operations.UnitaryRepresentation

/-- The coordinate pairing used before any block rearrangement. -/
def vectorInner {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ := star x ⬝ᵥ y

theorem vectorInner_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) (x y : ι → ℂ) :
    vectorInner (A.mulVec x) (A.mulVec y) = vectorInner x y := by
  have ha : A.conjTranspose * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  simp only [vectorInner, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ha, Matrix.vecMul_one]

/-- Transport retains the whole endomorphism, including its off-diagonal
coefficients. The equivalence is a comparison of realizations. -/
def transportRepresentation {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (ρ : G →* Module.End ℂ F) : G →* Module.End ℂ E :=
  (e.symm.conjAlgEquiv ℂ).toAlgHom.toMonoidHom.comp ρ

theorem conjugate_intertwines {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (A : Module.End ℂ F) (x : E) :
    e ((e.symm.conjAlgEquiv ℂ) A x) = A (e x) := e.apply_symm_apply _

theorem conjugate_eq_one_iff {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (A : Module.End ℂ F) :
    (e.symm.conjAlgEquiv ℂ) A = 1 ↔ A = 1 := by
  constructor
  · intro h
    exact (e.symm.conjAlgEquiv ℂ).injective (h.trans (map_one (e.symm.conjAlgEquiv ℂ)).symm)
  · rintro rfl
    exact map_one (e.symm.conjAlgEquiv ℂ)

theorem transportRepresentation_intertwines {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (ρ : G →* Module.End ℂ F) (g : G) (x : E) :
    e (transportRepresentation e ρ g x) = ρ g (e x) := conjugate_intertwines e (ρ g) x

theorem transportRepresentation_eq_one_iff {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (ρ : G →* Module.End ℂ F) (g : G) :
    transportRepresentation e ρ g = 1 ↔ ρ g = 1 := conjugate_eq_one_iff e (ρ g)

theorem transportRepresentation_intertwines_linear {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (ρ : G →* Module.End ℂ F) (g : G) :
    e.toLinearMap.comp (transportRepresentation e ρ g) = (ρ g).comp e.toLinearMap := by
  apply LinearMap.ext
  exact transportRepresentation_intertwines e ρ g

def representationLinearEquiv {G E : Type*} [Group G]
    [AddCommGroup E] [Module ℂ E] (ρ : G →* Module.End ℂ E) (g : G) : E ≃ₗ[ℂ] E :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    ((ρ.map_mul g g⁻¹).symm.trans ((congrArg ρ (mul_inv_cancel g)).trans ρ.map_one))
    ((ρ.map_mul g⁻¹ g).symm.trans ((congrArg ρ (inv_mul_cancel g)).trans ρ.map_one))

theorem linearIsometryEquiv_eq_one_iff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (U : E ≃ₗᵢ[ℂ] E) :
    U = 1 ↔ U.toLinearEquiv.toLinearMap = 1 := by
  constructor
  · intro h
    exact congrArg (fun V : E ≃ₗᵢ[ℂ] E => V.toLinearEquiv.toLinearMap) h
  · intro h
    apply LinearIsometryEquiv.ext
    intro x
    exact LinearMap.congr_fun h x

theorem algebraEquiv_mul_eq_of_images {A B : Type*}
    [Semiring A] [Algebra ℂ A] [Semiring B] [Algebra ℂ B]
    (e : A ≃ₐ[ℂ] B) (a b c d : A) (h : e a * e b = e c * e d) : a * b = c * d :=
  e.injective ((map_mul e a b).trans (h.trans (map_mul e c d).symm))

theorem conjugate_of_intertwines {G A : Type*} [Group G] [Monoid A]
    (ρ : G →* A) (g : G) (a b : A) (h : ρ g * a = b * ρ g) :
    ρ g * a * ρ g⁻¹ = b := by
  rw [h, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem representation_mem_unitary_of_adjoint {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : G →* Module.End ℂ E) (hρ : ∀ g, (ρ g).adjoint = ρ g⁻¹) (g : G) :
    ρ g ∈ unitary (Module.End ℂ E) := by
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, hρ]
  constructor <;> rw [← map_mul]
  · rw [inv_mul_cancel, map_one]
  · rw [mul_inv_cancel, map_one]

theorem representation_inner_of_adjoint {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : G →* Module.End ℂ E) (hρ : ∀ g, (ρ g).adjoint = ρ g⁻¹)
    (g : G) (x y : E) : inner ℂ (ρ g x) (ρ g y) = inner ℂ x y := by
  rw [← LinearMap.adjoint_inner_right, hρ]
  change inner ℂ x ((ρ g⁻¹ * ρ g) y) = _
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

end GeneratedFoundations.Operations.UnitaryRepresentation
