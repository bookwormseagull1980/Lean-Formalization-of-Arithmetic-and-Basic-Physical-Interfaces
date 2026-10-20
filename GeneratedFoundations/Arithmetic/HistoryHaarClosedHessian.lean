module

public import GeneratedFoundations.Arithmetic.HistoryHaarMatrixCurvature

/-!
# The closed Hessian on complete arithmetic matrix-valued Haar fields

The carrier is the full Hilbert product of original coclosed Haar fields,
indexed by every pair of arithmetic history--phase/source labels. Its
basis retains all source rows and all cross-history matrix coefficients.
The finite Hessian is identified with the twice-curl differential on each
actual coefficient before taking its unique self-adjoint closure.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate LinearPMap

namespace GeneratedFoundations.Arithmetic.HistoryHaarClosedHessian

open Geometry.SourceOneFormClosedHodge Geometry.SourceOneFormCoclosedSpectrum
open Geometry.SourceOneFormHodgeLaplacian Geometry.SourceOneFormHodgeEnergy
open Operations

abbrev Label (N : ℕ) := HistoryHaarMatrixCurvature.Index N × HistoryHaarMatrixCurvature.Index N
abbrev Fields (N : ℕ) := PiLp 2 (fun _ : Label N => coclosedField)
abbrev BasisIndex (N : ℕ) := Label N × CoclosedIndex

def vector (N : ℕ) (a : BasisIndex N) : Fields N :=
  PiLp.single 2 a.1 (coclosedHilbertBasis a.2)

theorem single_inner (N : ℕ) (a : Label N) (v : coclosedField) (x : Fields N) :
    inner ℂ (PiLp.single 2 a v : Fields N) x = inner ℂ v (x a) := by
  classical
  change (∑ i : Label N, inner ℂ ((PiLp.single 2 a v : Fields N) i) (x i)) = _
  rw [Finset.sum_eq_single a]
  · simp only [PiLp.single_eq_same]
  · intro i _ hia
    simp only [PiLp.single_eq_of_ne _ hia, inner_zero_left]
  · simp

theorem vector_orthonormal (N : ℕ) : Orthonormal ℂ (vector N) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    simpa only [vector, single_inner, PiLp.single_eq_same, Prod.mk.injEq, true_and]
      using orthonormal_iff_ite.mp coclosedHilbertBasis.orthonormal i j
  · have hpair : (a, i) ≠ (b, j) := fun h => hab (congrArg Prod.fst h)
    simp only [vector, single_inner, PiLp.single_eq_of_ne _ hab,
      inner_zero_right, ite_eq_right hpair]

theorem span_orthogonal (N : ℕ) :
    (Submodule.span ℂ (Set.range (vector N)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hall (a : Label N) (i : CoclosedIndex) :
      inner ℂ (coclosedHilbertBasis i) (x a) = 0 := by
    have h := (Submodule.mem_orthogonal _ x).mp hx (vector N (a, i))
      (Submodule.subset_span (Set.mem_range_self (a, i)))
    simpa only [vector, single_inner] using h
  have hz (a : Label N) : x a = 0 := by
    apply coclosedHilbertBasis.repr.injective
    apply lp.ext
    funext i
    simp only [HilbertBasis.repr_apply_apply, hall, inner_zero_right]
  change x = 0
  apply (WithLp.equiv 2 (Label N → coclosedField)).injective
  exact funext hz

def basis (N : ℕ) : HilbertBasis (BasisIndex N) ℂ (Fields N) :=
  HilbertBasis.mkOfOrthogonalEqBot (vector_orthonormal N) (span_orthogonal N)

@[simp] theorem basis_apply (N : ℕ) (a : BasisIndex N) : basis N a = vector N a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot (vector_orthonormal N) (span_orthogonal N)) a

abbrev FieldCore (N : ℕ) := FiniteEigenbasisCore.finiteSpan (basis N)

def eigenvalue (N : ℕ) (a : BasisIndex N) : ℝ := hodgeEigenvalue a.2

def finiteOperator (N : ℕ) : Fields N →ₗ.[ℂ] Fields N :=
  FiniteEigenbasisCore.finiteMultiplier (basis N) (eigenvalue N)

theorem component_mem_core (N : ℕ) (x : FieldCore N) (j : Label N) : x.val j ∈ Core := by
  classical
  refine Submodule.span_induction (fun y hy => ?_) ?_ ?_ ?_ x.property
  · rcases hy with ⟨⟨a, i⟩, rfl⟩
    by_cases h : j = a
    · subst j
      simp only [basis_apply, vector, PiLp.single_eq_same]
      exact Submodule.subset_span (Set.mem_range_self i)
    · simp only [basis_apply, vector, PiLp.single_eq_of_ne _ h]
      exact Submodule.zero_mem _
  · exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    exact Submodule.smul_mem _ c hy

def coreComponent (N : ℕ) (j : Label N) : FieldCore N →ₗ[ℂ] Core where
  toFun x := ⟨x.val j, component_mem_core N x j⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def component (N : ℕ) (j : Label N) : Fields N →ₗ[ℂ] coclosedField where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coreComponent_basis (N : ℕ) (a : BasisIndex N) (j : Label N) :
    coreComponent N j (FiniteEigenbasisCore.finiteBasis (basis N) a) =
      if j = a.1 then coreBasis a.2 else 0 := by
  classical
  by_cases h : j = a.1
  · rw [ite_eq_left h]
    apply Subtype.ext
    change (FiniteEigenbasisCore.finiteBasis (basis N) a : Fields N) j =
      (coreBasis a.2 : coclosedField)
    rw [FiniteEigenbasisCore.finiteBasis_coe, basis_apply]
    simp [vector, h, coreBasis, FiniteEigenbasisCore.finiteBasis_coe]
  · rw [ite_eq_right h]
    apply Subtype.ext
    change (FiniteEigenbasisCore.finiteBasis (basis N) a : Fields N) j = 0
    rw [FiniteEigenbasisCore.finiteBasis_coe, basis_apply]
    simp [vector, h]

theorem finiteOperator_component (N : ℕ) (x : FieldCore N) (j : Label N) :
    finiteOperator N x j = finiteHodge (coreComponent N j x) := by
  classical
  have he : (component N j).comp (finiteOperator N).toFun =
      finiteHodge.toFun.comp (coreComponent N j) := by
    apply (FiniteEigenbasisCore.finiteBasis (basis N)).ext
    intro a
    change component N j (finiteOperator N (FiniteEigenbasisCore.finiteBasis (basis N) a)) =
      finiteHodge (coreComponent N j (FiniteEigenbasisCore.finiteBasis (basis N) a))
    rw [coreComponent_basis]
    have ha : finiteOperator N (FiniteEigenbasisCore.finiteBasis (basis N) a) =
        (eigenvalue N a : ℂ) • basis N a :=
      (FiniteEigenbasisCore.finiteBasis (basis N)).constr_basis ℂ _ a
    rw [ha]
    change (eigenvalue N a : ℂ) • ((basis N a : Fields N) j) = _
    rw [basis_apply]
    by_cases h : j = a.1
    · subst j
      simp only [vector, PiLp.single_eq_same, ite_true, eigenvalue]
      have hb : finiteHodge (coreBasis a.2) =
          (hodgeEigenvalue a.2 : ℂ) • coclosedHilbertBasis a.2 :=
        (FiniteEigenbasisCore.finiteBasis coclosedHilbertBasis).constr_basis ℂ _ a.2
      exact hb.symm
    · simp only [vector, PiLp.single_eq_of_ne _ h, smul_zero, ite_eq_right h]
      exact (map_zero finiteHodge.toFun).symm
  exact LinearMap.congr_fun he x

def coefficients (N : ℕ) (x : FieldCore N) : HistoryHaarMatrixCurvature.Coefficients N :=
  fun i j => coreComponent N (i, j) x

theorem finiteOperator_energy (N : ℕ) (x : FieldCore N) :
    (inner ℂ (x : Fields N) (finiteOperator N x)).re =
      ‖HistoryHaarMatrixCurvature.differentiated N (coefficients N x)‖ ^ 2 := by
  rw [HistoryHaarMatrixCurvature.differentiated_normSq]
  change (∑ j : Label N, inner ℂ (x.val j) (finiteOperator N x j)).re = _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [finiteOperator_component]
  exact finiteHodge_energy (coreComponent N j x)

theorem action_secondDeriv (N : ℕ) (x : FieldCore N) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarMatrixCurvature.action N ((s : ℂ) • coefficients N x)) t)
      (inner ℂ (x : Fields N) (finiteOperator N x)).re 0 := by
  rw [finiteOperator_energy]
  exact HistoryHaarMatrixCurvature.secondDeriv_zero N (coefficients N x)

def operator (N : ℕ) : Fields N →ₗ.[ℂ] Fields N := (finiteOperator N).closure

theorem operator_selfAdjoint (N : ℕ) : IsSelfAdjoint (operator N) :=
  FiniteEigenbasisCore.closure_selfAdjoint (basis N) (eigenvalue N)

theorem finiteOperator_le_operator (N : ℕ) : finiteOperator N ≤ operator N :=
  FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)

theorem operator_closed (N : ℕ) : (operator N).IsClosed :=
  (operator_selfAdjoint N).isClosed

theorem operator_domain_dense (N : ℕ) :
    Dense ((operator N).domain : Set (Fields N)) :=
  (operator_selfAdjoint N).dense_domain

theorem operator_unique (N : ℕ) (S : Fields N →ₗ.[ℂ] Fields N)
    (hS : IsSelfAdjoint S) (hcore : finiteOperator N ≤ S) : S = operator N :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique (basis N) (eigenvalue N) S hS hcore

theorem operator_domain (N : ℕ) (x : Fields N) :
    x ∈ (operator N).domain ↔ Summable (fun a : BasisIndex N =>
      eigenvalue N a ^ 2 * ‖inner ℂ (basis N a) x‖ ^ 2) :=
  FiniteEigenbasisCore.closure_domain_iff_summable (basis N) (eigenvalue N) x

/-- The weighted coefficient condition is also the exact operator domain,
not merely a sufficient decay condition. -/
theorem operator_domain_iff_memℓp (N : ℕ) (x : Fields N) :
    x ∈ (operator N).domain ↔ Memℓp (fun a : BasisIndex N =>
      (eigenvalue N a : ℂ) * inner ℂ (basis N a) x) 2 :=
  FiniteEigenbasisCore.closure_domain_iff_memℓp (basis N) (eigenvalue N) x

theorem operator_coefficients (N : ℕ) (x : (operator N).domain) (a : BasisIndex N) :
    inner ℂ (basis N a) (operator N x) =
      (eigenvalue N a : ℂ) * inner ℂ (basis N a) (x : Fields N) :=
  FiniteEigenbasisCore.closure_coefficients (basis N) (eigenvalue N) x a

theorem eigenvalue_lower (N : ℕ) (a : BasisIndex N) : 4 ≤ eigenvalue N a :=
  coclosed_eigenvalue_sq_ge_four a.2

theorem eigenvalue_pos (N : ℕ) (a : BasisIndex N) : 0 < eigenvalue N a :=
  lt_of_lt_of_le (by norm_num) (eigenvalue_lower N a)

theorem complete_coercivity (N : ℕ) (x : (operator N).domain) :
    4 * ‖(x : Fields N)‖ ^ 2 ≤ (inner ℂ (x : Fields N) (operator N x)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound (basis N) (eigenvalue N) 4
    (fun a => coclosed_eigenvalue_sq_ge_four a.2) x

theorem basis_mem_domain (N : ℕ) (a : BasisIndex N) :
    basis N a ∈ (operator N).domain :=
  (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).1
    (FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) a)

theorem operator_basis (N : ℕ) (a : BasisIndex N) :
    operator N ⟨basis N a, basis_mem_domain N a⟩ =
      (eigenvalue N a : ℂ) • basis N a := by
  have h := (FiniteEigenbasisCore.le_closure (basis N) (eigenvalue N)).2
    (x := ⟨basis N a, FiniteEigenbasisCore.basis_mem_domain (basis N) (eigenvalue N) a⟩)
    (y := ⟨basis N a, basis_mem_domain N a⟩) rfl
  exact h.symm.trans (FiniteEigenbasisCore.basis_action (basis N) (eigenvalue N) a)

def minimizingIndex (N : ℕ) : BasisIndex N :=
  let i : HistoryHaarMatrixCurvature.Index N :=
    (HistoryCliffordAction.historyPoint N, Sum.inl 0)
  ((i, i), lowestIndex)

theorem eigenvalue_minimizingIndex (N : ℕ) : eigenvalue N (minimizingIndex N) = 4 :=
  hodgeEigenvalue_lowest

theorem gap_attained (N : ℕ) : ∃ x : (operator N).domain,
    (x : Fields N) ≠ 0 ∧ operator N x = (4 : ℂ) • (x : Fields N) := by
  refine ⟨⟨basis N (minimizingIndex N), basis_mem_domain N _⟩, ?_, ?_⟩
  · exact (basis N).orthonormal.ne_zero _
  · simpa only [eigenvalue_minimizingIndex, Complex.ofReal_ofNat]
      using operator_basis N (minimizingIndex N)

structure Conclusions : Prop where
  complete_basis : ∀ N, (Submodule.span ℂ (Set.range (vector N)))ᗮ = ⊥
  actual_differential : ∀ N (x : FieldCore N) j,
    finiteOperator N x j = finiteHodge (coreComponent N j x)
  actual_hessian : ∀ N (x : FieldCore N),
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ =>
      HistoryHaarMatrixCurvature.action N ((s : ℂ) • coefficients N x)) t)
      (inner ℂ (x : Fields N) (finiteOperator N x)).re 0
  self_adjoint : ∀ N, IsSelfAdjoint (operator N)
  closed_operator : ∀ N, (operator N).IsClosed
  dense_domain : ∀ N, Dense ((operator N).domain : Set (Fields N))
  unique_extension : ∀ N S, IsSelfAdjoint S → finiteOperator N ≤ S → S = operator N
  exact_domain : ∀ N x, x ∈ (operator N).domain ↔ Summable (fun a : BasisIndex N =>
    eigenvalue N a ^ 2 * ‖inner ℂ (basis N a) x‖ ^ 2)
  all_coefficient_equations : ∀ N (x : (operator N).domain) a,
    inner ℂ (basis N a) (operator N x) =
      (eigenvalue N a : ℂ) * inner ℂ (basis N a) (x : Fields N)
  complete_bound : ∀ N (x : (operator N).domain),
    4 * ‖(x : Fields N)‖ ^ 2 ≤ (inner ℂ (x : Fields N) (operator N x)).re
  attained_lower_edge : ∀ N, ∃ x : (operator N).domain,
    (x : Fields N) ≠ 0 ∧ operator N x = (4 : ℂ) • (x : Fields N)

theorem generated : Conclusions where
  complete_basis := span_orthogonal
  actual_differential := finiteOperator_component
  actual_hessian := action_secondDeriv
  self_adjoint := operator_selfAdjoint
  closed_operator := operator_closed
  dense_domain := operator_domain_dense
  unique_extension := operator_unique
  exact_domain := operator_domain
  all_coefficient_equations := operator_coefficients
  complete_bound := complete_coercivity
  attained_lower_edge := gap_attained

end GeneratedFoundations.Arithmetic.HistoryHaarClosedHessian
