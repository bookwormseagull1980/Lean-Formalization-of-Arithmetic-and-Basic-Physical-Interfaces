module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite orthonormal coordinate constructions

These basis constructions are shared by the Gaussian/Hermite realizations
of the arithmetic and physical source carriers. They preserve the complete
finite basis; no diagonal restriction or scalar readout is involved.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Operations.OrthonormalCoordinates

theorem orthonormalBasis_equivFun {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : OrthonormalBasis ι ℂ E) (i : ι) :
    e.toBasis.equivFun (e i) = Pi.single i 1 := by
  funext j
  simp [Pi.single_apply, eq_comm]

theorem basis_equivFun_inner {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : OrthonormalBasis ι ℂ E) (x : E) (i : ι) :
    e.toBasis.equivFun x i = inner ℂ (e i) x := by
  change (e.repr x).ofLp i = _
  exact e.repr_apply_apply x i

theorem orthonormal_constr_basis {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : OrthonormalBasis ι ℂ E)
    (v : ι → F) (i : ι) : e.toBasis.constr ℂ v (e i) = v i :=
  e.toBasis.constr_basis ℂ v i

def orthonormalLinearIsometry {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : OrthonormalBasis ι ℂ E) (f : E →ₗ[ℂ] F)
    (hf : Orthonormal ℂ (f ∘ e)) : E →ₗᵢ[ℂ] F :=
  f.isometryOfOrthonormal (v := e.toBasis) e.orthonormal hf

theorem orthonormalBasis_linearMap_ext {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : OrthonormalBasis ι ℂ E)
    (f g : E →ₗ[ℂ] F) (h : ∀ i, f (e i) = g (e i)) : f = g :=
  e.toBasis.ext h

theorem orthonormalBasis_map_expansion {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : OrthonormalBasis ι ℂ E)
    (f : E →ₗ[ℂ] F) (x : E) : f x = ∑ i, e.repr x i • f (e i) := by
  conv_lhs => rw [← e.sum_repr x]
  simp only [map_sum, map_smul]

end GeneratedFoundations.Operations.OrthonormalCoordinates
