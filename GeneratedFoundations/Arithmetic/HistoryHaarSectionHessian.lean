module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionAction
public import GeneratedFoundations.Geometry.SourceScalarKineticOperator
public import GeneratedFoundations.Operations.FiniteEigenbasisCore
public import GeneratedFoundations.Operations.SpectralFormLowerBound

/-!
# The closed Hessian on complete position-dependent history sections

Every original arithmetic history coordinate carries the complete scalar
Haar coefficient space. The kinetic form is the actual differentiated
form, including cross-row pairings, and its restoring coefficient is the
previously calculated defining Casimir. The Green identity identifies the
finite multiplier with that form before taking its unique self-adjoint
closure. The full weighted domain is retained.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate LinearPMap

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionHessian

open Geometry.SourceQuotientHilbert Geometry.SourceScalarResolution
open Geometry.SourceScalarKineticOperator
open Operations

abbrev Space (N : ℕ) := HistoryHaarSectionAction.StateFields N
abbrev Label (N : ℕ) := HistoryHaarMatrixCurvature.Index N
abbrev Index (N : ℕ) := Label N × EvenIndex

def singleLift (N : ℕ) (i : Label N) : QuotientL2 →ₗ[ℂ] Space N where
  toFun f := PiLp.single 2 i f
  map_add' f g := by
    classical
    exact PiLp.single_add 2 i
  map_smul' z f := by
    classical
    apply (WithLp.equiv 2 (Label N → QuotientL2)).injective
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp

def vector (N : ℕ) (a : Index N) : Space N := singleLift N a.1 (quotientBasisVector a.2)

theorem single_inner (N : ℕ) (i : Label N) (f : QuotientL2) (x : Space N) :
    inner ℂ (singleLift N i f) x = inner ℂ f (x i) := by
  classical
  change (∑ j : Label N, inner ℂ ((PiLp.single 2 i f : Space N) j) (x j)) = _
  rw [Finset.sum_eq_single i]
  · simp only [PiLp.single_eq_same]
  · intro j _ hji
    simp only [PiLp.single_eq_of_ne _ hji, inner_zero_left]
  · simp

theorem vector_orthonormal (N : ℕ) : Orthonormal ℂ (vector N) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp only [vector, single_inner]
    simpa only [singleLift, LinearMap.coe_mk,
      AddHom.coe_mk, PiLp.single_eq_same, Prod.mk.injEq, true_and] using
      orthonormal_iff_ite.mp quotientBasisVector_orthonormal a b
  · have hp : (i, a) ≠ (j, b) := fun h => hij (congrArg Prod.fst h)
    simp only [vector, single_inner]
    simp only [singleLift, LinearMap.coe_mk, AddHom.coe_mk,
      PiLp.single_eq_of_ne _ hij, inner_zero_right, ite_eq_right hp]

theorem span_orthogonal (N : ℕ) :
    (Submodule.span ℂ (Set.range (vector N)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hall (i : Label N) (a : EvenIndex) : inner ℂ (quotientBasisVector a) (x i) = 0 := by
    have h := (Submodule.mem_orthogonal _ x).mp hx (vector N (i, a))
      (Submodule.subset_span (Set.mem_range_self (i, a)))
    simpa only [vector, single_inner] using h
  have hz (i : Label N) : x i = 0 := by
    apply quotientBasis.repr.injective
    apply lp.ext
    funext a
    simp only [HilbertBasis.repr_apply_apply, quotientBasis_apply, hall, inner_zero_right]
  change x = 0
  apply (WithLp.equiv 2 (Label N → QuotientL2)).injective
  exact funext hz

def basis (N : ℕ) : HilbertBasis (Index N) ℂ (Space N) :=
  HilbertBasis.mkOfOrthogonalEqBot (vector_orthonormal N) (span_orthogonal N)

@[simp] theorem basis_apply (N : ℕ) (a : Index N) : basis N a = vector N a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot (vector_orthonormal N) (span_orthogonal N)) a

def eigenvalue (N : ℕ) (a : Index N) : ℝ :=
  Geometry.SourceCasimirClosure.energy a.2.val.1 + HistoryDefiningResponse.coefficient N

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
    x ∈ (operator N).domain ↔ Summable (fun a : Index N =>
      eigenvalue N a ^ 2 * ‖inner ℂ (basis N a) x‖ ^ 2) :=
  FiniteEigenbasisCore.closure_domain_iff_summable (basis N) (eigenvalue N) x

theorem operator_coefficient (N : ℕ) (x : (operator N).domain) (a : Index N) :
    inner ℂ (basis N a) (operator N x) =
      (eigenvalue N a : ℂ) * inner ℂ (basis N a) (x : Space N) :=
  FiniteEigenbasisCore.closure_coefficients (basis N) (eigenvalue N) x a

def rowCore (N : ℕ) (i : Label N) :
    ScalarCore →ₗ[ℂ] (finiteOperator N).domain :=
  scalarBasis.constr ℂ (fun a =>
    ⟨basis N (i, a), FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) (i, a)⟩)

theorem rowCore_coe (N : ℕ) (i : Label N) (f : ScalarCore) :
    (rowCore N i f : Space N) = singleLift N i (includeScalar f) := by
  have h : (finiteOperator N).domain.subtype.comp (rowCore N i) =
      (singleLift N i).comp includeScalar := by
    apply scalarBasis.ext
    intro a
    simp only [LinearMap.comp_apply, rowCore, Module.Basis.constr_basis,
      Submodule.subtype_apply, basis_apply, vector, includeScalar_basis]
  exact LinearMap.congr_fun h f

theorem rowCore_operator (N : ℕ) (i : Label N) (f : ScalarCore) :
    finiteOperator N (rowCore N i f) = singleLift N i
      (includeScalar (coreLaplacian f) +
        (HistoryDefiningResponse.coefficient N : ℂ) • includeScalar f) := by
  have h : (finiteOperator N).toFun.comp (rowCore N i) =
      (singleLift N i).comp
        (includeScalar.comp coreLaplacian +
          (HistoryDefiningResponse.coefficient N : ℂ) • includeScalar) := by
    apply scalarBasis.ext
    intro a
    simp only [LinearMap.comp_apply, rowCore, Module.Basis.constr_basis,
      LinearPMap.toFun_eq_coe, LinearMap.add_apply, LinearMap.smul_apply,
      coreLaplacian_basis, map_smul, includeScalar_basis]
    calc
      finiteOperator N _ = (eigenvalue N (i, a) : ℂ) • basis N (i, a) :=
        FiniteEigenbasisCore.basis_action (basis N) (eigenvalue N) (i, a)
      _ = _ := ?_
    simp only [eigenvalue, basis_apply, vector, Complex.ofReal_add,
      add_smul, map_add, map_smul]
  exact LinearMap.congr_fun h f

def coreInclusion (N : ℕ) :
    HistoryHaarSectionAction.Sections N →ₗ[ℂ] (finiteOperator N).domain :=
  ∑ i : Label N, (rowCore N i).comp (LinearMap.proj i)

theorem coreInclusion_coe (N : ℕ) (ψ : HistoryHaarSectionAction.Sections N) :
    (coreInclusion N ψ : Space N) = HistoryHaarSectionAction.sectionField N ψ := by
  classical
  apply (WithLp.equiv 2 (Label N → QuotientL2)).injective
  funext i
  change (coreInclusion N ψ : Space N) i = includeScalar (ψ i)
  simp only [coreInclusion, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, rowCore_coe]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  change (∑ j : Label N, (PiLp.single 2 j (includeScalar (ψ j)) : Space N) i) = _
  rw [Finset.sum_eq_single i]
  · simp only [PiLp.single_eq_same]
  · intro j _ hji
    exact PiLp.single_eq_of_ne _ (Ne.symm hji) _
  · simp

theorem finite_operator_component (N : ℕ) (ψ : HistoryHaarSectionAction.Sections N)
    (i : Label N) :
    finiteOperator N (coreInclusion N ψ) i = includeScalar (coreLaplacian (ψ i)) +
      (HistoryDefiningResponse.coefficient N : ℂ) • includeScalar (ψ i) := by
  classical
  change ((finiteOperator N).toFun (coreInclusion N ψ)) i = _
  simp only [coreInclusion, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    map_sum, LinearPMap.toFun_eq_coe, rowCore_operator]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  change (∑ j : Label N, (PiLp.single 2 j _ : Space N) i) = _
  rw [Finset.sum_eq_single i]
  · simp only [PiLp.single_eq_same]
  · intro j _ hji
    exact PiLp.single_eq_of_ne _ (Ne.symm hji) _
  · simp

/-- The pairing of the complete finite multiplier is the actual kinetic
plus restoring form on arbitrary source sections. -/
theorem finite_operator_pairing (N : ℕ)
    (ψ ξ : HistoryHaarSectionAction.Sections N) :
    inner ℂ (HistoryHaarSectionAction.sectionField N ψ)
      (finiteOperator N (coreInclusion N ξ)) =
      inner ℂ (HistoryHaarSectionAction.gradient N ψ) (HistoryHaarSectionAction.gradient N ξ) +
        (HistoryDefiningResponse.coefficient N : ℂ) *
          inner ℂ (HistoryHaarSectionAction.sectionField N ψ)
            (HistoryHaarSectionAction.sectionField N ξ) := by
  change (∑ i : Label N, inner ℂ (includeScalar (ψ i))
    (finiteOperator N (coreInclusion N ξ) i)) = _
  simp only [finite_operator_component, inner_add_right, inner_smul_right (𝕜 := ℂ),
    ← green_identity, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

def closedInclusion (N : ℕ) (ψ : HistoryHaarSectionAction.Sections N) :
    (operator N).domain :=
  ⟨HistoryHaarSectionAction.sectionField N ψ, by
    rw [← coreInclusion_coe N ψ]
    exact (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1
      (coreInclusion N ψ).property⟩

theorem closed_operator_core (N : ℕ) (ψ : HistoryHaarSectionAction.Sections N) :
    operator N (closedInclusion N ψ) = finiteOperator N (coreInclusion N ψ) := by
  have h := (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).2
    (x := coreInclusion N ψ) (y := closedInclusion N ψ) (coreInclusion_coe N ψ)
  exact h.symm

/-- The operator pairing is identified with a derivative of the same
nonlinear action, rather than declared to be its Hessian. -/
theorem action_secondDeriv (N : ℕ) (ψ : HistoryHaarSectionAction.Sections N) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarSectionAction.action N 0 ((s : ℂ) • ψ)) t)
      (inner ℂ (HistoryHaarSectionAction.sectionField N ψ)
        (operator N (closedInclusion N ψ))).re 0 := by
  have he : (inner ℂ (HistoryHaarSectionAction.sectionField N ψ)
      (operator N (closedInclusion N ψ))).re =
      HistoryHaarSectionAction.quadratic N 0 ψ := by
    rw [closed_operator_core, finite_operator_pairing]
    simp [HistoryHaarSectionAction.quadratic, inner_self_eq_norm_sq_to_K,
      pow_two, Complex.mul_re]
  rw [he]
  simpa only [smul_zero] using HistoryHaarSectionAction.secondDeriv_zero N 0 ψ

theorem eigenvalue_lower (N : ℕ) (a : Index N) :
    HistoryDefiningResponse.coefficient N ≤ eigenvalue N a :=
  le_add_of_nonneg_left (Geometry.SourceCasimirClosure.energy_nonneg _)

theorem complete_coercivity (N : ℕ) (x : (operator N).domain) :
    HistoryDefiningResponse.coefficient N * ‖(x : Space N)‖ ^ 2 ≤
      (inner ℂ (x : Space N) (operator N x)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound (basis N) (eigenvalue N)
    (HistoryDefiningResponse.coefficient N) (eigenvalue_lower N) x

theorem basis_mem_domain (N : ℕ) (a : Index N) : basis N a ∈ (operator N).domain :=
  (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1
    (FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) a)

theorem operator_basis (N : ℕ) (a : Index N) :
    operator N ⟨basis N a, basis_mem_domain N a⟩ = (eigenvalue N a : ℂ) • basis N a := by
  have h := (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).2
    (x := ⟨basis N a, FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) a⟩)
    (y := ⟨basis N a, basis_mem_domain N a⟩) rfl
  exact h.symm.trans (FiniteEigenbasisCore.basis_action (basis N) (eigenvalue N) a)

def minimizingIndex (N : ℕ) : Index N :=
  ((HistoryCliffordAction.historyPoint N, Sum.inl 0), ⟨⟨0, 0, 0⟩, by decide⟩)

theorem eigenvalue_minimizingIndex (N : ℕ) :
    eigenvalue N (minimizingIndex N) = HistoryDefiningResponse.coefficient N := by
  simp [eigenvalue, minimizingIndex, Geometry.SourceCasimirClosure.energy]

theorem gap_attained (N : ℕ) : ∃ x : (operator N).domain,
    (x : Space N) ≠ 0 ∧ operator N x =
      (HistoryDefiningResponse.coefficient N : ℂ) • (x : Space N) := by
  refine ⟨⟨basis N (minimizingIndex N), basis_mem_domain N _⟩,
    (basis N).orthonormal.ne_zero _, ?_⟩
  simpa only [eigenvalue_minimizingIndex] using operator_basis N (minimizingIndex N)

structure Conclusions : Prop where
  complete_source_basis : ∀ N, (Submodule.span ℂ (Set.range (vector N)))ᗮ = ⊥
  actual_kinetic_pairing : ∀ N ψ ξ,
    inner ℂ (HistoryHaarSectionAction.sectionField N ψ) (finiteOperator N (coreInclusion N ξ)) =
      inner ℂ (HistoryHaarSectionAction.gradient N ψ) (HistoryHaarSectionAction.gradient N ξ) +
        (HistoryDefiningResponse.coefficient N : ℂ) *
          inner ℂ (HistoryHaarSectionAction.sectionField N ψ)
            (HistoryHaarSectionAction.sectionField N ξ)
  self_adjoint : ∀ N, IsSelfAdjoint (operator N)
  unique_extension : ∀ N S, IsSelfAdjoint S → finiteOperator N ≤ S → S = operator N
  exact_domain : ∀ N x, x ∈ (operator N).domain ↔ Summable (fun a : Index N =>
    eigenvalue N a ^ 2 * ‖inner ℂ (basis N a) x‖ ^ 2)
  actual_action_second_derivative : ∀ N ψ,
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarSectionAction.action N 0 ((s : ℂ) • ψ)) t)
      (inner ℂ (HistoryHaarSectionAction.sectionField N ψ)
        (operator N (closedInclusion N ψ))).re 0
  original_metric_bound : ∀ N (x : (operator N).domain),
    HistoryDefiningResponse.coefficient N * ‖(x : Space N)‖ ^ 2 ≤
      (inner ℂ (x : Space N) (operator N x)).re
  attained_lower_edge : ∀ N, ∃ x : (operator N).domain,
    (x : Space N) ≠ 0 ∧ operator N x =
      (HistoryDefiningResponse.coefficient N : ℂ) • (x : Space N)

theorem generated : Conclusions where
  complete_source_basis := span_orthogonal
  actual_kinetic_pairing := finite_operator_pairing
  self_adjoint := operator_selfAdjoint
  unique_extension := operator_unique
  exact_domain := operator_domain
  actual_action_second_derivative := action_secondDeriv
  original_metric_bound := complete_coercivity
  attained_lower_edge := gap_attained

end GeneratedFoundations.Arithmetic.HistoryHaarSectionHessian
