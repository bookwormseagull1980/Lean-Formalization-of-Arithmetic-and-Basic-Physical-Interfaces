module

public import GeneratedFoundations.Operations.EigenbasisClosure
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# A finite coefficient multiplier on the original Hilbert space

The domain is exactly the algebraic span of a given Hilbert basis.  A real
coefficient function defines a linear multiplier on this domain, independently
of any differential operator.  Its symmetry and basis action imply that its
closure is the unique self-adjoint extension, with the full weighted-square
summability domain.

Identifying this finite multiplier with an independently defined differential
operator is a separate statement; no such identification is assumed here.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate LinearPMap

namespace GeneratedFoundations.Operations.FiniteEigenbasisCore

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

variable (B : HilbertBasis ι ℂ E)

section AlgebraicCore

omit [CompleteSpace E]

def finiteSpan : Submodule ℂ E := Submodule.span ℂ (Set.range B)

def finiteBasis : Module.Basis ι ℂ (finiteSpan B) :=
  Module.Basis.span B.orthonormal.linearIndependent

@[simp] theorem finiteBasis_coe (i : ι) : (finiteBasis B i : E) = B i :=
  Module.Basis.coe_span_apply B.orthonormal.linearIndependent i

/-- A finite sum of the actual basis vectors in the original Hilbert space. -/
def linearCombination : (ι →₀ ℂ) →ₗ[ℂ] E := Finsupp.linearCombination ℂ B

theorem linearCombination_apply (c : ι →₀ ℂ) :
    linearCombination B c = c.sum (fun i a => a • B i) := rfl

private theorem finiteBasis_sum_coe (c : ι →₀ ℂ) :
    (Finsupp.linearCombination ℂ (finiteBasis B) c : E) = linearCombination B c := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum,
    Submodule.coe_smul, finiteBasis_coe, linearCombination]

variable (eigenvalue : ι → ℝ)

/-- The finite coefficient multiplier, with domain equal to the algebraic
span rather than an assumed differential-operator domain. -/
def finiteMultiplier : E →ₗ.[ℂ] E where
  domain := finiteSpan B
  toFun := (finiteBasis B).constr ℂ (fun i => (eigenvalue i : ℂ) • B i)

theorem domain_eq : (finiteMultiplier B eigenvalue).domain =
    Submodule.span ℂ (Set.range B) := rfl

theorem basis_mem_domain (i : ι) : B i ∈ (finiteMultiplier B eigenvalue).domain :=
  Submodule.subset_span (Set.mem_range_self i)

theorem basis_action (i : ι) :
    finiteMultiplier B eigenvalue ⟨B i, basis_mem_domain B eigenvalue i⟩ =
      (eigenvalue i : ℂ) • B i := by
  have hi : finiteBasis B i =
      (⟨B i, basis_mem_domain B eigenvalue i⟩ : finiteSpan B) :=
    Subtype.ext (finiteBasis_coe B i)
  exact (congrArg ((finiteBasis B).constr ℂ (fun j => (eigenvalue j : ℂ) • B j))
    hi).symm.trans ((finiteBasis B).constr_basis ℂ _ i)

theorem sum_mem_domain (c : ι →₀ ℂ) :
    linearCombination B c ∈ (finiteMultiplier B eigenvalue).domain := by
  rw [domain_eq, ← Finsupp.range_linearCombination]
  exact ⟨c, rfl⟩

/-- Every vector in the core is an actual finite linear combination. -/
theorem exists_linearCombination (x : (finiteMultiplier B eigenvalue).domain) :
    ∃ c : ι →₀ ℂ, linearCombination B c = (x : E) := by
  refine ⟨(finiteBasis B).repr x, ?_⟩
  rw [← finiteBasis_sum_coe]
  exact congrArg (fun y : finiteSpan B => (y : E))
    ((finiteBasis B).linearCombination_repr x)

theorem finiteMultiplier_sum (c : ι →₀ ℂ) :
    finiteMultiplier B eigenvalue ⟨linearCombination B c, sum_mem_domain B eigenvalue c⟩ =
      c.sum (fun i a => a • ((eigenvalue i : ℂ) • B i)) := by
  have hx : (⟨linearCombination B c, sum_mem_domain B eigenvalue c⟩ : finiteSpan B) =
      Finsupp.linearCombination ℂ (finiteBasis B) c := by
    apply Subtype.ext
    exact (finiteBasis_sum_coe B c).symm
  calc
    _ = (finiteBasis B).constr ℂ (fun i => (eigenvalue i : ℂ) • B i)
        (Finsupp.linearCombination ℂ (finiteBasis B) c) :=
      congrArg ((finiteBasis B).constr ℂ (fun i => (eigenvalue i : ℂ) • B i)) hx
    _ = _ := by rw [Module.Basis.constr_apply, Module.Basis.repr_linearCombination]

/-- Coefficients are computed using the original Hilbert inner product. -/
theorem coefficients (x : (finiteMultiplier B eigenvalue).domain) (i : ι) :
    inner ℂ (B i) (finiteMultiplier B eigenvalue x) =
      (eigenvalue i : ℂ) * inner ℂ (B i) (x : E) := by
  classical
  have hmaps : (innerSL ℂ (B i)).toLinearMap.comp
      ((finiteMultiplier B eigenvalue).toFun : finiteSpan B →ₗ[ℂ] E) =
      (eigenvalue i : ℂ) • ((innerSL ℂ (B i)).toLinearMap.comp (finiteSpan B).subtype) := by
    apply (finiteBasis B).ext
    intro j
    change inner ℂ (B i) (finiteMultiplier B eigenvalue (finiteBasis B j)) =
      (eigenvalue i : ℂ) * inner ℂ (B i) (finiteBasis B j : E)
    have haction : finiteMultiplier B eigenvalue (finiteBasis B j) =
        (eigenvalue j : ℂ) • B j :=
      (finiteBasis B).constr_basis ℂ _ j
    rw [haction, finiteBasis_coe, inner_smul_right]
    rw [orthonormal_iff_ite.mp B.orthonormal i j]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  exact LinearMap.congr_fun hmaps x

end AlgebraicCore

variable (eigenvalue : ι → ℝ)

omit [CompleteSpace E] in
theorem symmetric : (finiteMultiplier B eigenvalue).IsFormalAdjoint
    (finiteMultiplier B eigenvalue) := by
  intro x y
  rw [← B.tsum_inner_mul_inner (finiteMultiplier B eigenvalue x) (y : E),
    ← B.tsum_inner_mul_inner (x : E) (finiteMultiplier B eigenvalue y)]
  apply tsum_congr
  intro i
  rw [← inner_conj_symm (finiteMultiplier B eigenvalue x) (B i),
    coefficients B eigenvalue x i, map_mul, Complex.conj_ofReal,
    inner_conj_symm, coefficients B eigenvalue y i]
  ring

omit [CompleteSpace E] in
theorem domain_dense : Dense ((finiteMultiplier B eigenvalue).domain : Set E) :=
  EigenbasisClosure.domain_dense B (finiteMultiplier B eigenvalue)
    (basis_mem_domain B eigenvalue)

theorem closure_eq_adjoint : (finiteMultiplier B eigenvalue).closure =
    (finiteMultiplier B eigenvalue).adjoint :=
  EigenbasisClosure.closure_eq_adjoint B (finiteMultiplier B eigenvalue) eigenvalue
    (basis_mem_domain B eigenvalue) (basis_action B eigenvalue) (symmetric B eigenvalue)

theorem le_closure : finiteMultiplier B eigenvalue ≤ (finiteMultiplier B eigenvalue).closure := by
  rw [closure_eq_adjoint]
  exact EigenbasisClosure.le_adjoint B (finiteMultiplier B eigenvalue)
    (basis_mem_domain B eigenvalue) (symmetric B eigenvalue)

theorem closure_selfAdjoint : IsSelfAdjoint (finiteMultiplier B eigenvalue).closure :=
  EigenbasisClosure.closure_selfAdjoint B (finiteMultiplier B eigenvalue) eigenvalue
    (basis_mem_domain B eigenvalue) (basis_action B eigenvalue) (symmetric B eigenvalue)

theorem selfAdjoint_extension_unique (S : E →ₗ.[ℂ] E) (hS : IsSelfAdjoint S)
    (hcore : finiteMultiplier B eigenvalue ≤ S) :
    S = (finiteMultiplier B eigenvalue).closure :=
  EigenbasisClosure.selfAdjoint_extension_unique B (finiteMultiplier B eigenvalue) eigenvalue
    (basis_mem_domain B eigenvalue) (basis_action B eigenvalue) (symmetric B eigenvalue)
    S hS hcore

theorem existsUnique_selfAdjoint_extension : ∃! S : E →ₗ.[ℂ] E,
    IsSelfAdjoint S ∧ finiteMultiplier B eigenvalue ≤ S := by
  refine ⟨(finiteMultiplier B eigenvalue).closure,
    ⟨closure_selfAdjoint B eigenvalue, le_closure B eigenvalue⟩, ?_⟩
  intro S hS
  exact selfAdjoint_extension_unique B eigenvalue S hS.1 hS.2

theorem closure_domain_iff_memℓp (x : E) :
    x ∈ (finiteMultiplier B eigenvalue).closure.domain ↔
      Memℓp (fun i => (eigenvalue i : ℂ) * inner ℂ (B i) x) 2 := by
  rw [closure_eq_adjoint]
  exact EigenbasisClosure.adjoint_domain_iff_memℓp B (finiteMultiplier B eigenvalue) eigenvalue
    (basis_mem_domain B eigenvalue) (basis_action B eigenvalue) (symmetric B eigenvalue) x

/-- This is the full closed-operator domain, not just its finite core. -/
theorem closure_domain_iff_summable (x : E) :
    x ∈ (finiteMultiplier B eigenvalue).closure.domain ↔
      Summable (fun i => eigenvalue i ^ 2 * ‖inner ℂ (B i) x‖ ^ 2) := by
  rw [closure_eq_adjoint]
  exact EigenbasisClosure.adjoint_domain_iff_summable B (finiteMultiplier B eigenvalue) eigenvalue
    (basis_mem_domain B eigenvalue) (basis_action B eigenvalue) (symmetric B eigenvalue) x

theorem closure_coefficients (x : (finiteMultiplier B eigenvalue).closure.domain) (i : ι) :
    inner ℂ (B i) ((finiteMultiplier B eigenvalue).closure x) =
      (eigenvalue i : ℂ) * inner ℂ (B i) (x : E) := by
  have heq := closure_eq_adjoint B eigenvalue
  have h : ∀ y : (finiteMultiplier B eigenvalue).adjoint.domain,
      inner ℂ (B i) ((finiteMultiplier B eigenvalue).adjoint y) =
        (eigenvalue i : ℂ) * inner ℂ (B i) (y : E) := fun y =>
    EigenbasisClosure.adjoint_coefficients B (finiteMultiplier B eigenvalue) eigenvalue
      (basis_mem_domain B eigenvalue) (basis_action B eigenvalue) y i
  generalize (finiteMultiplier B eigenvalue).closure = S at x heq ⊢
  subst S
  exact h x

end GeneratedFoundations.Operations.FiniteEigenbasisCore
