module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionHessian
public import GeneratedFoundations.Operations.HilbertBasisProduct
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The joint closed Hessian of the position-dependent history action

The original matrix-valued coclosed connection and every scalar history
section retain their original Haar metrics. Both factors have unbounded
kinetic operators. The domain therefore requires both weighted coefficient
conditions. The operator pairing is identified with the second derivative
of `HistoryHaarSectionAction`; its zero mixed vacuum block is a consequence
of that same action, not an assumption on independent response sectors.
-/

@[expose] public section
noncomputable section
open scoped LinearPMap

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionJointHessian

open Operations

abbrev Space (N : ℕ) := WithLp 2
  (HistoryHaarClosedHessian.Fields N × HistoryHaarSectionHessian.Space N)
abbrev Index (N : ℕ) :=
  HistoryHaarClosedHessian.BasisIndex N ⊕ HistoryHaarSectionHessian.Index N

def basis (N : ℕ) : HilbertBasis (Index N) ℂ (Space N) :=
  HilbertBasisProduct.basis (HistoryHaarClosedHessian.basis N)
    (HistoryHaarSectionHessian.basis N)

def eigenvalue (N : ℕ) : Index N → ℝ :=
  Sum.elim (HistoryHaarClosedHessian.eigenvalue N) (HistoryHaarSectionHessian.eigenvalue N)

def finiteOperator (N : ℕ) : Space N →ₗ.[ℂ] Space N :=
  FiniteEigenbasisCore.finiteMultiplier (basis N) (eigenvalue N)

def operator (N : ℕ) : Space N →ₗ.[ℂ] Space N := (finiteOperator N).closure

theorem operator_selfAdjoint (N : ℕ) : IsSelfAdjoint (operator N) :=
  FiniteEigenbasisCore.closure_selfAdjoint (basis N) (eigenvalue N)

theorem operator_closed (N : ℕ) : (operator N).IsClosed :=
  (operator_selfAdjoint N).isClosed

theorem operator_domain_dense (N : ℕ) : Dense ((operator N).domain : Set (Space N)) :=
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

@[simp] theorem coefficient_inr (N : ℕ) (i : HistoryHaarSectionHessian.Index N)
    (x : Space N) : inner ℂ (basis N (.inr i)) x =
      inner ℂ (HistoryHaarSectionHessian.basis N i) x.snd :=
  HilbertBasisProduct.coefficient_inr _ _ i x

/-- Both original factors are unbounded; neither weighted domain may be
replaced by unrestricted Hilbert membership. -/
theorem domain_iff (N : ℕ) (x : Space N) :
    x ∈ (operator N).domain ↔
      x.fst ∈ (HistoryHaarClosedHessian.operator N).domain ∧
      x.snd ∈ (HistoryHaarSectionHessian.operator N).domain := by
  rw [operator_domain, HistoryHaarClosedHessian.operator_domain,
    HistoryHaarSectionHessian.operator_domain]
  constructor
  · intro h
    constructor
    · simpa only [Function.comp_def, eigenvalue, Sum.elim_inl, coefficient_inl] using
        h.comp_injective (Sum.inl_injective : Function.Injective
          (Sum.inl : HistoryHaarClosedHessian.BasisIndex N → Index N))
    · simpa only [Function.comp_def, eigenvalue, Sum.elim_inr, coefficient_inr] using
        h.comp_injective (Sum.inr_injective : Function.Injective
          (Sum.inr : HistoryHaarSectionHessian.Index N → Index N))
  · rintro ⟨hA, hψ⟩
    apply Summable.sum
    · simpa only [Function.comp_def, eigenvalue, Sum.elim_inl, coefficient_inl] using hA
    · simpa only [Function.comp_def, eigenvalue, Sum.elim_inr, coefficient_inr] using hψ

theorem operator_coefficient (N : ℕ) (x : (operator N).domain) (i : Index N) :
    inner ℂ (basis N i) (operator N x) =
      (eigenvalue N i : ℂ) * inner ℂ (basis N i) (x : Space N) :=
  FiniteEigenbasisCore.closure_coefficients (basis N) (eigenvalue N) x i

theorem operator_components (N : ℕ) (x : (operator N).domain) :
    operator N x = WithLp.toLp 2
      (HistoryHaarClosedHessian.operator N
        ⟨(x : Space N).fst, ((domain_iff N x.val).mp x.property).1⟩,
       HistoryHaarSectionHessian.operator N
        ⟨(x : Space N).snd, ((domain_iff N x.val).mp x.property).2⟩) := by
  apply EigenbasisClosure.eq_of_coefficients (basis N)
  intro i
  rw [operator_coefficient]
  cases i with
  | inl a =>
    rw [coefficient_inl, coefficient_inl]
    exact (HistoryHaarClosedHessian.operator_coefficients N
      ⟨(x : Space N).fst, ((domain_iff N x.val).mp x.property).1⟩ a).symm
  | inr a =>
    rw [coefficient_inr, coefficient_inr]
    exact (HistoryHaarSectionHessian.operator_coefficient N
      ⟨(x : Space N).snd, ((domain_iff N x.val).mp x.property).2⟩ a).symm

theorem eigenvalue_lower (N : ℕ) (i : Index N) : (15 / 8 : ℝ) ≤ eigenvalue N i := by
  cases i with
  | inl a =>
    exact (by norm_num : (15 / 8 : ℝ) ≤ 4).trans
      (HistoryHaarClosedHessian.eigenvalue_lower N a)
  | inr a =>
    exact (HistoryDefiningResponse.coefficient_lower N).trans
      (HistoryHaarSectionHessian.eigenvalue_lower N a)

theorem complete_coercivity (N : ℕ) (x : (operator N).domain) :
    (15 / 8 : ℝ) * ‖(x : Space N)‖ ^ 2 ≤
      (inner ℂ (x : Space N) (operator N x)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound (basis N) (eigenvalue N)
    (15 / 8) (eigenvalue_lower N) x

def gapSq (N : ℕ) : ℝ := min 4 (HistoryDefiningResponse.coefficient N)

theorem eigenvalue_ge_gap (N : ℕ) (i : Index N) : gapSq N ≤ eigenvalue N i := by
  cases i with
  | inl a => exact (min_le_left _ _).trans (HistoryHaarClosedHessian.eigenvalue_lower N a)
  | inr a => exact (min_le_right _ _).trans (HistoryHaarSectionHessian.eigenvalue_lower N a)

theorem sharp_coercivity (N : ℕ) (x : (operator N).domain) :
    gapSq N * ‖(x : Space N)‖ ^ 2 ≤ (inner ℂ (x : Space N) (operator N x)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound (basis N) (eigenvalue N)
    (gapSq N) (eigenvalue_ge_gap N) x

def minimizingIndex (N : ℕ) : Index N :=
  if 4 ≤ HistoryDefiningResponse.coefficient N then
    .inl (HistoryHaarClosedHessian.minimizingIndex N)
  else .inr (HistoryHaarSectionHessian.minimizingIndex N)

theorem eigenvalue_minimizingIndex (N : ℕ) : eigenvalue N (minimizingIndex N) = gapSq N := by
  by_cases h : 4 ≤ HistoryDefiningResponse.coefficient N
  · simp only [minimizingIndex, ite_eq_left h, eigenvalue, Sum.elim_inl,
      HistoryHaarClosedHessian.eigenvalue_minimizingIndex, gapSq, min_eq_left h]
  · simp only [minimizingIndex, ite_eq_right h, eigenvalue, Sum.elim_inr,
      HistoryHaarSectionHessian.eigenvalue_minimizingIndex,
      gapSq, min_eq_right (le_of_not_ge h)]

theorem basis_mem_domain (N : ℕ) (i : Index N) : basis N i ∈ (operator N).domain :=
  (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1
    (FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) i)

theorem operator_basis (N : ℕ) (i : Index N) :
    operator N ⟨basis N i, basis_mem_domain N i⟩ = (eigenvalue N i : ℂ) • basis N i := by
  have h := (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).2
    (x := ⟨basis N i, FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) i⟩)
    (y := ⟨basis N i, basis_mem_domain N i⟩) rfl
  exact h.symm.trans (FiniteEigenbasisCore.basis_action (basis N) (eigenvalue N) i)

theorem gap_attained (N : ℕ) : ∃ x : (operator N).domain,
    (x : Space N) ≠ 0 ∧ operator N x = (gapSq N : ℂ) • (x : Space N) := by
  refine ⟨⟨basis N (minimizingIndex N), basis_mem_domain N _⟩,
    (basis N).orthonormal.ne_zero _, ?_⟩
  simpa only [eigenvalue_minimizingIndex] using operator_basis N (minimizingIndex N)

def corePair (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N)
    (ψ : HistoryHaarSectionAction.Sections N) : Space N :=
  WithLp.toLp 2 (A.val, HistoryHaarSectionAction.sectionField N ψ)

theorem corePair_mem_domain (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N)
    (ψ : HistoryHaarSectionAction.Sections N) : corePair N A ψ ∈ (operator N).domain := by
  apply (domain_iff N _).mpr
  exact ⟨(HistoryHaarClosedHessian.finiteOperator_le_operator N).1 A.property,
    (HistoryHaarSectionHessian.closedInclusion N ψ).property⟩

/-- The whole joint operator is obtained by differentiating the same
position-dependent nonlinear action on arbitrary finite fields and sections. -/
theorem action_secondDeriv (N : ℕ) (A : HistoryHaarClosedHessian.FieldCore N)
    (ψ : HistoryHaarSectionAction.Sections N) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarSectionAction.action N
        ((s : ℂ) • HistoryHaarClosedHessian.coefficients N A) ((s : ℂ) • ψ)) t)
      (inner ℂ (corePair N A ψ)
        (operator N ⟨corePair N A ψ, corePair_mem_domain N A ψ⟩)).re 0 := by
  have hA := (HistoryHaarClosedHessian.finiteOperator_le_operator N).2
    (x := A)
    (y := ⟨A.val, (HistoryHaarClosedHessian.finiteOperator_le_operator N).1 A.property⟩) rfl
  have hψ := HistoryHaarSectionHessian.closed_operator_core N ψ
  have he : (inner ℂ (corePair N A ψ)
      (operator N ⟨corePair N A ψ, corePair_mem_domain N A ψ⟩)).re =
      HistoryHaarSectionAction.quadratic N
        (HistoryHaarClosedHessian.coefficients N A) ψ := by
    rw [operator_components, WithLp.prod_inner_apply, Complex.add_re]
    change (inner ℂ A.val (HistoryHaarClosedHessian.operator N
      ⟨A.val, (HistoryHaarClosedHessian.finiteOperator_le_operator N).1 A.property⟩)).re +
      (inner ℂ (HistoryHaarSectionAction.sectionField N ψ)
        (HistoryHaarSectionHessian.operator N
          (HistoryHaarSectionHessian.closedInclusion N ψ))).re = _
    rw [← hA, hψ, HistoryHaarClosedHessian.finiteOperator_energy,
      HistoryHaarSectionHessian.finite_operator_pairing]
    simp [HistoryHaarSectionAction.quadratic, Complex.add_re, Complex.mul_re,
      inner_self_eq_norm_sq_to_K, pow_two]
    ring
  rw [he]
  exact HistoryHaarSectionAction.secondDeriv_zero N _ ψ

structure Conclusions : Prop where
  self_adjoint : ∀ N, IsSelfAdjoint (operator N)
  unique_extension : ∀ N S, IsSelfAdjoint S → finiteOperator N ≤ S → S = operator N
  exact_joint_domain : ∀ N x, x ∈ (operator N).domain ↔
    x.fst ∈ (HistoryHaarClosedHessian.operator N).domain ∧
    x.snd ∈ (HistoryHaarSectionHessian.operator N).domain
  actual_joint_variation : ∀ N A ψ,
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarSectionAction.action N
        ((s : ℂ) • HistoryHaarClosedHessian.coefficients N A) ((s : ℂ) • ψ)) t)
      (inner ℂ (corePair N A ψ)
        (operator N ⟨corePair N A ψ, corePair_mem_domain N A ψ⟩)).re 0
  original_joint_metric : ∀ N (x : (operator N).domain),
    (15 / 8 : ℝ) * ‖(x : Space N)‖ ^ 2 ≤
      (inner ℂ (x : Space N) (operator N x)).re
  sharp_joint_bound : ∀ N (x : (operator N).domain),
    gapSq N * ‖(x : Space N)‖ ^ 2 ≤ (inner ℂ (x : Space N) (operator N x)).re
  attained_joint_edge : ∀ N, ∃ x : (operator N).domain,
    (x : Space N) ≠ 0 ∧ operator N x = (gapSq N : ℂ) • (x : Space N)

theorem generated : Conclusions where
  self_adjoint := operator_selfAdjoint
  unique_extension := operator_unique
  exact_joint_domain := domain_iff
  actual_joint_variation := action_secondDeriv
  original_joint_metric := complete_coercivity
  sharp_joint_bound := sharp_coercivity
  attained_joint_edge := gap_attained

end GeneratedFoundations.Arithmetic.HistoryHaarSectionJointHessian
