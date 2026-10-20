module

public import GeneratedFoundations.Arithmetic.HistoryChargedReconstruction
public import GeneratedFoundations.Operations.FiniteDefiningResponse

/-!
# Defining response of the actual phase-detail subspace

The detail space is the range of the existing orthogonal phase residual.
Every history multiplicity is retained. Centred operations on this whole
subspace are extended by zero to its orthogonal complement; their complete
quadratic sum fixes the response coefficient. An orthonormal basis is only
a coordinate device: the resulting operator is independent of that choice.

The dimension is `n * card (History (n+1))`. It is not replaced by a physical
colour dimension, and no colour coefficient is supplied to the construction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryDetailCasimir

open HistoryModuleRepresentation (Space)
open HistoryPhaseProjection (projection residual)
open Operations

abbrev Detail (n : ℕ) := LinearMap.range (residual n)
abbrev BasisIndex (n : ℕ) := Fin (Module.finrank ℂ (Detail n))

def retained (n : ℕ) : Space n →ₗ[ℂ] Detail n where
  toFun x := ⟨residual n x, ⟨x, rfl⟩⟩
  map_add' x y := Subtype.ext (map_add (residual n) x y)
  map_smul' c x := Subtype.ext (map_smul (residual n) c x)

theorem retained_subtype (n : ℕ) (x : Detail n) : retained n x.val = x := by
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change residual n x.val = x.val
  rw [← hy]
  exact LinearMap.congr_fun (HistoryPhaseProjection.residual_idempotent n) y

def extend (n : ℕ) : Module.End ℂ (Detail n) →ₗ[ℂ] Module.End ℂ (Space n) where
  toFun A := (Detail n).subtype.comp (A.comp (retained n))
  map_add' A B := by ext x; rfl
  map_smul' c A := by ext x; rfl

theorem extend_mul (n : ℕ) (A B : Module.End ℂ (Detail n)) :
    extend n (A * B) = extend n A * extend n B := by
  apply LinearMap.ext
  intro x
  change (A (B (retained n x)) : Space n) =
    (A (retained n (B (retained n x)).val) : Space n)
  rw [retained_subtype]

theorem extend_one (n : ℕ) : extend n 1 = residual n := by ext x; rfl

/-- The extension is along the actual orthogonal phase decomposition. -/
theorem retained_inner (n : ℕ) (x : Space n) (y : Detail n) :
    inner ℂ (retained n x) y = inner ℂ x y.val := by
  change inner ℂ (residual n x) y.val = inner ℂ x y.val
  have hy : residual n y.val = y.val :=
    congrArg Subtype.val (retained_subtype n y)
  have h := LinearMap.adjoint_inner_left (residual n) y.val x
  simpa only [HistoryChargedReconstruction.residual_adjoint, hy] using h

set_option maxHeartbeats 1000000 in
theorem extend_adjoint (n : ℕ) (A : Module.End ℂ (Detail n)) :
    (extend n A).adjoint =
      extend n (LinearMap.adjoint (𝕜 := ℂ) (E := Detail n) (F := Detail n) A) := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  let Astar : Module.End ℂ (Detail n) :=
    LinearMap.adjoint (𝕜 := ℂ) (E := Detail n) (F := Detail n) A
  change inner ℂ ((Astar (retained n x)).val) y =
    inner ℂ x (A (retained n y) : Space n)
  rw [← inner_conj_symm ((Astar (retained n x)).val) y,
    ← retained_inner n y (Astar (retained n x))]
  have h := LinearMap.adjoint_inner_right (𝕜 := ℂ) (E := Detail n) (F := Detail n)
    A (retained n y) (retained n x)
  change inner ℂ (retained n y) (Astar (retained n x)) = _ at h
  rw [h, inner_conj_symm, retained_inner]

def basis (n : ℕ) : OrthonormalBasis (BasisIndex n) ℂ (Detail n) :=
  stdOrthonormalBasis ℂ (Detail n)

def generator (n : ℕ) (i j : BasisIndex n) : Module.End ℂ (Space n) :=
  extend n (FiniteDefiningResponse.generator (basis n) i j)

def response (n : ℕ) : Module.End ℂ (Space n) :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, generator n i j * generator n j i

def coefficient (n : ℕ) : ℝ := FiniteDefiningResponse.coefficient (Detail n)

theorem response_eq (n : ℕ) : response n = (coefficient n : ℂ) • residual n := by
  have h := congrArg (extend n) (FiniteDefiningResponse.response_intrinsic (basis n))
  simpa only [FiniteDefiningResponse.response, response, generator,
    map_smul, map_sum, extend_mul, extend_one, coefficient] using h

theorem response_any_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (b : OrthonormalBasis ι ℂ (Detail n)) :
    extend n (FiniteDefiningResponse.response b) = response n := by
  rw [FiniteDefiningResponse.response_intrinsic, map_smul, extend_one, response_eq]
  rfl

theorem detail_finrank (n : ℕ) : Module.finrank ℂ (Detail n) =
    n * Fintype.card (CompleteHistory.History (n + 1)) := by
  have h := (LinearMap.IsIdempotentElem.isProj_range _
    (HistoryPhaseProjection.residual_idempotent n)).trace
  rw [HistoryPhaseProjection.residual_trace] at h
  have hr : Module.finrank ℂ (Detail n) =
      Fintype.card (CompleteHistory.History (n + 1)) * n := by
    exact_mod_cast h.symm
  simpa only [Nat.mul_comm] using hr

theorem coefficient_eq (n : ℕ) : coefficient n =
    (((n * Fintype.card (CompleteHistory.History (n + 1)) : ℕ) : ℝ) -
      ((n * Fintype.card (CompleteHistory.History (n + 1)) : ℕ) : ℝ)⁻¹) / 2 := by
  unfold coefficient FiniteDefiningResponse.coefficient
  rw [detail_finrank]

theorem coefficient_nonneg (n : ℕ) : 0 ≤ coefficient n := by
  change 0 ≤ FiniteDefiningResponse.coefficient (Detail n)
  exact FiniteDefiningResponse.coefficient_nonneg (E := Detail n)

theorem coefficient_pos {n : ℕ} (hn : 2 ≤ n) : 0 < coefficient n := by
  change 0 < FiniteDefiningResponse.coefficient (Detail n)
  apply FiniteDefiningResponse.coefficient_pos (E := Detail n)
  rw [detail_finrank]
  have hH : 1 ≤ Fintype.card (CompleteHistory.History (n + 1)) :=
    Fintype.card_pos_iff.mpr inferInstance
  nlinarith

theorem response_symmetric (n : ℕ) (x y : Space n) :
    inner ℂ (response n x) y = inner ℂ x (response n y) := by
  rw [response_eq]
  change inner ℂ ((coefficient n : ℂ) • residual n x) y =
    inner ℂ x ((coefficient n : ℂ) • residual n y)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  congr 1
  simpa only [HistoryChargedReconstruction.residual_adjoint] using
    LinearMap.adjoint_inner_left (residual n) y x

theorem response_adjoint (n : ℕ) : (response n).adjoint = response n := by
  symm
  exact (LinearMap.eq_adjoint_iff _ _).mpr (response_symmetric n)

theorem quadratic_eq (n : ℕ) (x : Space n) :
    (inner ℂ x (response n x)).re = coefficient n * ‖residual n x‖ ^ 2 := by
  have hi : inner ℂ x (residual n x) = inner ℂ (residual n x) (residual n x) := by
    calc
      _ = inner ℂ (projection n x + residual n x) (residual n x) :=
        congrArg (fun y => inner ℂ y (residual n x))
          (HistoryPhaseProjection.full_reconstruction n x).symm
      _ = _ := by rw [inner_add_left, HistoryPhaseProjection.projection_residual_inner, zero_add]
  rw [response_eq]
  change (inner ℂ x ((coefficient n : ℂ) • residual n x)).re = _
  rw [inner_smul_right, hi, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, pow_two]

theorem quadratic_nonneg (n : ℕ) (x : Space n) :
    0 ≤ (inner ℂ x (response n x)).re := by
  rw [quadratic_eq]
  exact mul_nonneg (coefficient_nonneg n) (sq_nonneg _)

theorem response_zero_iff {n : ℕ} (hn : 2 ≤ n) (x : Space n) :
    response n x = 0 ↔ residual n x = 0 := by
  rw [response_eq]
  change (coefficient n : ℂ) • residual n x = 0 ↔ _
  have hc : (coefficient n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (coefficient_pos hn).ne'
  simp only [smul_eq_zero, hc, false_or]

theorem response_invariant_zero (n : ℕ) : response n * projection n = 0 := by
  rw [response_eq, smul_mul_assoc, HistoryPhaseProjection.residual_projection, smul_zero]

structure Conclusions : Prop where
  complete_quadratic_sum : ∀ n, response n = (coefficient n : ℂ) • residual n
  actual_dimension : ∀ n, Module.finrank ℂ (Detail n) =
    n * Fintype.card (CompleteHistory.History (n + 1))
  positive_response : ∀ n x, 0 ≤ (inner ℂ x (response n x)).re
  self_adjoint : ∀ n, (response n).adjoint = response n
  exact_kernel : ∀ n, 2 ≤ n → ∀ x, response n x = 0 ↔ residual n x = 0
  retained_invariant : ∀ n, response n * projection n = 0

theorem generated : Conclusions where
  complete_quadratic_sum := response_eq
  actual_dimension := detail_finrank
  positive_response := quadratic_nonneg
  self_adjoint := response_adjoint
  exact_kernel := fun _ => response_zero_iff
  retained_invariant := response_invariant_zero

end GeneratedFoundations.Arithmetic.HistoryDetailCasimir
