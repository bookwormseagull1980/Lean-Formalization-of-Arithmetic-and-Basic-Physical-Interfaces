module

public import GeneratedFoundations.Arithmetic.HistoryHaarCoupledAction
public import GeneratedFoundations.Arithmetic.HistoryHaarHeatGenerator
public import GeneratedFoundations.Operations.HilbertBasisProduct
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Complete operator of the joint arithmetic Haar response

The original matrix-valued coclosed fields and the full homogeneous state
fibre form one Hilbert product. Its complete basis is the orthogonal union
of their actual bases. The second variation of the coupled action fixes
the two multipliers; the mixed vacuum block was derived from that action.
The closure, its uniqueness and its exact domain are proved here, together
with the component formula. The finite state factor imposes no additional
unbounded-operator domain condition.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap

namespace GeneratedFoundations.Arithmetic.HistoryHaarJointHessian

open Operations

abbrev State (N : ℕ) := HistoryCliffordAction.Space N
abbrev Space (N : ℕ) := WithLp 2 (HistoryHaarClosedHessian.Fields N × State N)
abbrev Index (N : ℕ) := HistoryHaarClosedHessian.BasisIndex N ⊕ HistoryCliffordAction.Index N

def stateBasis (N : ℕ) : HilbertBasis (HistoryCliffordAction.Index N) ℂ (State N) :=
  (EuclideanSpace.basisFun (HistoryCliffordAction.Index N) ℂ).toHilbertBasis

def basis (N : ℕ) : HilbertBasis (Index N) ℂ (Space N) :=
  HilbertBasisProduct.basis (HistoryHaarClosedHessian.basis N) (stateBasis N)

def eigenvalue (N : ℕ) : Index N → ℝ :=
  Sum.elim (HistoryHaarClosedHessian.eigenvalue N)
    (fun _ => HistoryDefiningResponse.coefficient N)

def finiteOperator (N : ℕ) : Space N →ₗ.[ℂ] Space N :=
  FiniteEigenbasisCore.finiteMultiplier (basis N) (eigenvalue N)

def operator (N : ℕ) : Space N →ₗ.[ℂ] Space N := (finiteOperator N).closure

theorem finiteOperator_le_operator (N : ℕ) : finiteOperator N ≤ operator N :=
  FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)

theorem operator_selfAdjoint (N : ℕ) : IsSelfAdjoint (operator N) :=
  FiniteEigenbasisCore.closure_selfAdjoint (basis N) (eigenvalue N)

theorem operator_closed (N : ℕ) : (operator N).IsClosed :=
  (operator_selfAdjoint N).isClosed

theorem operator_domain_dense (N : ℕ) :
    Dense ((operator N).domain : Set (Space N)) :=
  (operator_selfAdjoint N).dense_domain

theorem operator_unique (N : ℕ) (S : Space N →ₗ.[ℂ] Space N)
    (hS : IsSelfAdjoint S) (hcore : finiteOperator N ≤ S) : S = operator N :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique (basis N) (eigenvalue N) S hS hcore

theorem operator_domain (N : ℕ) (x : Space N) :
    x ∈ (operator N).domain ↔ Summable (fun i : Index N =>
      eigenvalue N i ^ 2 * ‖inner ℂ (basis N i) x‖ ^ 2) :=
  FiniteEigenbasisCore.closure_domain_iff_summable (basis N) (eigenvalue N) x

@[simp] theorem coefficient_inl (N : ℕ) (i : HistoryHaarClosedHessian.BasisIndex N)
    (x : Space N) : inner ℂ (basis N (.inl i)) x =
      inner ℂ (HistoryHaarClosedHessian.basis N i) x.fst :=
  HilbertBasisProduct.coefficient_inl _ _ i x

@[simp] theorem coefficient_inr (N : ℕ) (i : HistoryCliffordAction.Index N)
    (x : Space N) : inner ℂ (basis N (.inr i)) x = inner ℂ (stateBasis N i) x.snd :=
  HilbertBasisProduct.coefficient_inr _ _ i x

/-- Exact full domain: only the Haar component is unbounded. -/
theorem domain_iff (N : ℕ) (x : Space N) :
    x ∈ (operator N).domain ↔ x.fst ∈ (HistoryHaarClosedHessian.operator N).domain := by
  rw [operator_domain, HistoryHaarClosedHessian.operator_domain]
  constructor
  · intro h
    have hl := h.comp_injective (Sum.inl_injective : Function.Injective
      (Sum.inl : HistoryHaarClosedHessian.BasisIndex N → Index N))
    simpa only [Function.comp_def, eigenvalue, Sum.elim_inl, coefficient_inl] using hl
  · intro h
    apply Summable.sum
    · simpa only [Function.comp_def, eigenvalue, Sum.elim_inl, coefficient_inl] using h
    · exact (hasSum_fintype _).summable

theorem operator_coefficient (N : ℕ) (x : (operator N).domain) (i : Index N) :
    inner ℂ (basis N i) (operator N x) =
      (eigenvalue N i : ℂ) * inner ℂ (basis N i) (x : Space N) :=
  FiniteEigenbasisCore.closure_coefficients (basis N) (eigenvalue N) x i

/-- The closure is the actual differential operator paired with the
already calculated defining-state response. -/
theorem operator_components (N : ℕ) (x : (operator N).domain) :
    operator N x = WithLp.toLp 2
      (HistoryHaarClosedHessian.operator N
        ⟨(x : Space N).fst, (domain_iff N x.val).mp x.property⟩,
       HistoryDefiningResponse.response N (x : Space N).snd) := by
  apply EigenbasisClosure.eq_of_coefficients (basis N)
  intro i
  rw [operator_coefficient]
  cases i with
  | inl a =>
    rw [coefficient_inl, coefficient_inl]
    exact (HistoryHaarHeatGenerator.operator_coefficients N
      ⟨(x : Space N).fst, (domain_iff N x.val).mp x.property⟩ a).symm
  | inr a =>
    rw [coefficient_inr, coefficient_inr, HistoryDefiningResponse.response_eq]
    change (HistoryDefiningResponse.coefficient N : ℂ) *
      inner ℂ (stateBasis N a) (x : Space N).snd =
      inner ℂ (stateBasis N a)
        ((HistoryDefiningResponse.coefficient N : ℂ) • (x : Space N).snd)
    rw [inner_smul_right]

theorem eigenvalue_lower (N : ℕ) (i : Index N) : (15 / 8 : ℝ) ≤ eigenvalue N i := by
  cases i with
  | inl a =>
    exact (by norm_num : (15 / 8 : ℝ) ≤ 4).trans
      (HistoryHaarHeatFlow.eigenvalue_ge_four N a)
  | inr a => exact HistoryDefiningResponse.coefficient_lower N

theorem eigenvalue_pos (N : ℕ) (i : Index N) : 0 < eigenvalue N i :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15 / 8) (eigenvalue_lower N i)

theorem complete_coercivity (N : ℕ) (x : (operator N).domain) :
    (15 / 8 : ℝ) * ‖(x : Space N)‖ ^ 2 ≤
      (inner ℂ (x : Space N) (operator N x)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound (basis N) (eigenvalue N)
    (15 / 8) (eigenvalue_lower N) x

def gapSq (N : ℕ) : ℝ := min 4 (HistoryDefiningResponse.coefficient N)

theorem gapSq_lower (N : ℕ) : (15 / 8 : ℝ) ≤ gapSq N :=
  le_min (by norm_num) (HistoryDefiningResponse.coefficient_lower N)

theorem eigenvalue_ge_gap (N : ℕ) (i : Index N) : gapSq N ≤ eigenvalue N i := by
  cases i with
  | inl a => exact (min_le_left _ _).trans (HistoryHaarHeatFlow.eigenvalue_ge_four N a)
  | inr a => exact min_le_right _ _

theorem sharp_coercivity (N : ℕ) (x : (operator N).domain) :
    gapSq N * ‖(x : Space N)‖ ^ 2 ≤ (inner ℂ (x : Space N) (operator N x)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound (basis N) (eigenvalue N)
    (gapSq N) (eigenvalue_ge_gap N) x

def minimizingIndex (N : ℕ) : Index N :=
  if 4 ≤ HistoryDefiningResponse.coefficient N then
    .inl (HistoryHaarClosedHessian.minimizingIndex N)
  else .inr (HistoryCliffordAction.historyPoint N, Sum.inl 0)

theorem eigenvalue_minimizingIndex (N : ℕ) :
    eigenvalue N (minimizingIndex N) = gapSq N := by
  by_cases h : 4 ≤ HistoryDefiningResponse.coefficient N
  · simp only [minimizingIndex, ite_eq_left h, eigenvalue, Sum.elim_inl,
      HistoryHaarClosedHessian.eigenvalue_minimizingIndex, gapSq, min_eq_left h]
  · simp only [minimizingIndex, ite_eq_right h, eigenvalue, Sum.elim_inr,
      gapSq, min_eq_right (le_of_not_ge h)]

theorem basis_mem_domain (N : ℕ) (i : Index N) : basis N i ∈ (operator N).domain :=
  (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1
    (FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) i)

theorem operator_basis (N : ℕ) (i : Index N) :
    operator N ⟨basis N i, basis_mem_domain N i⟩ =
      (eigenvalue N i : ℂ) • basis N i := by
  have h := (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).2
    (x := ⟨basis N i, FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) i⟩)
    (y := ⟨basis N i, basis_mem_domain N i⟩) rfl
  exact h.symm.trans (FiniteEigenbasisCore.basis_action (basis N) (eigenvalue N) i)

theorem gap_attained (N : ℕ) : ∃ x : (operator N).domain,
    (x : Space N) ≠ 0 ∧ operator N x = (gapSq N : ℂ) • (x : Space N) := by
  refine ⟨⟨basis N (minimizingIndex N), basis_mem_domain N _⟩,
    (basis N).orthonormal.ne_zero _, ?_⟩
  simpa only [eigenvalue_minimizingIndex] using operator_basis N (minimizingIndex N)

def corePair (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N) (ψ : State N) : Space N :=
  WithLp.toLp 2 (A.val, ψ)

theorem corePair_mem_domain (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N)
    (ψ : State N) : corePair N A ψ ∈ (operator N).domain := by
  apply (domain_iff N _).mpr
  exact (FiniteEigenbasisCore.le_closure (HistoryHaarClosedHessian.basis N)
    (HistoryHaarClosedHessian.eigenvalue N)).1 A.property

theorem action_secondDeriv (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N)
    (ψ : State N) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarCoupledAction.action N
        ((s : ℂ) • HistoryHaarClosedHessian.coefficients N A) ((s : ℂ) • ψ)) t)
      (inner ℂ (corePair N A ψ)
        (operator N ⟨corePair N A ψ, corePair_mem_domain N A ψ⟩)).re 0 := by
  have he : (inner ℂ (corePair N A ψ)
      (operator N ⟨corePair N A ψ, corePair_mem_domain N A ψ⟩)).re =
      HistoryHaarCoupledAction.quadratic N
        (HistoryHaarClosedHessian.coefficients N A) ψ := by
    rw [operator_components, WithLp.prod_inner_apply, Complex.add_re,
      HistoryHaarCoupledAction.hessian_operator]
    congr 1
    have h := (FiniteEigenbasisCore.le_closure (HistoryHaarClosedHessian.basis N)
      (HistoryHaarClosedHessian.eigenvalue N)).2
      (x := A)
      (y := ⟨A.val, (FiniteEigenbasisCore.le_closure (HistoryHaarClosedHessian.basis N)
        (HistoryHaarClosedHessian.eigenvalue N)).1 A.property⟩) rfl
    exact congrArg (fun y => (inner ℂ A.val y).re) h.symm
  rw [he]
  exact HistoryHaarCoupledAction.secondDeriv_zero N _ ψ

structure Conclusions : Prop where
  complete_basis : ∀ N, (Submodule.span ℂ (Set.range (basis N)))ᗮ = ⊥
  self_adjoint : ∀ N, IsSelfAdjoint (operator N)
  unique_extension : ∀ N S, IsSelfAdjoint S → finiteOperator N ≤ S → S = operator N
  exact_domain : ∀ N x,
    x ∈ (operator N).domain ↔ x.fst ∈ (HistoryHaarClosedHessian.operator N).domain
  actual_components : ∀ N (x : (operator N).domain),
    operator N x = WithLp.toLp 2
      (HistoryHaarClosedHessian.operator N
        ⟨(x : Space N).fst, (domain_iff N x.val).mp x.property⟩,
       HistoryDefiningResponse.response N (x : Space N).snd)
  uniform_bound : ∀ N (x : (operator N).domain),
    (15 / 8 : ℝ) * ‖(x : Space N)‖ ^ 2 ≤ (inner ℂ (x : Space N) (operator N x)).re
  sharp_bound : ∀ N (x : (operator N).domain),
    gapSq N * ‖(x : Space N)‖ ^ 2 ≤ (inner ℂ (x : Space N) (operator N x)).re
  attained_lower_edge : ∀ N, ∃ x : (operator N).domain,
    (x : Space N) ≠ 0 ∧ operator N x = (gapSq N : ℂ) • (x : Space N)

theorem generated : Conclusions where
  complete_basis N := by
    simpa only [basis, HilbertBasisProduct.basis, HilbertBasis.coe_mkOfOrthogonalEqBot]
      using HilbertBasisProduct.span_orthogonal
        (HistoryHaarClosedHessian.basis N) (stateBasis N)
  self_adjoint := operator_selfAdjoint
  unique_extension := operator_unique
  exact_domain := domain_iff
  actual_components := operator_components
  uniform_bound := complete_coercivity
  sharp_bound := sharp_coercivity
  attained_lower_edge := gap_attained

end GeneratedFoundations.Arithmetic.HistoryHaarJointHessian
