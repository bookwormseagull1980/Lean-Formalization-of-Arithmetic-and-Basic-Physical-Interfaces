module

public import GeneratedFoundations.Geometry.SourceHermitianReadout
public import Mathlib.Tactic.FinCases

/-!
# The spatial slice of the same Hermitian source readout

The three-coordinate carrier is the zero-trace-coordinate subspace of the
already constructed four-coordinate determinant readout. Its coordinates,
dimension and negative determinant form are computed on that subspace;
no additional vector space is supplied to the generated source.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.SourceSpatialCarrier

open SourceHermitianReadout

abbrev Coordinates := Fin 3 → ℝ

def slice : Submodule ℝ RealCoordinates where
  carrier := {q | q 0 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro q r hq hr
    change q 0 = 0 at hq
    change r 0 = 0 at hr
    change q 0 + r 0 = 0
    rw [hq, hr, add_zero]
  smul_mem' := by
    intro a q hq
    change q 0 = 0 at hq
    change a * q 0 = 0
    rw [hq, mul_zero]

def embed (x : Coordinates) : RealCoordinates := ![0, x 0, x 1, x 2]

theorem embed_mem (x : Coordinates) : embed x ∈ slice := rfl

theorem trace_hermitian (q : RealCoordinates) :
    Matrix.trace (hermitianMatrix q) = ((2 * q 0 : ℝ) : ℂ) := by
  simp [Matrix.trace, Fin.sum_univ_two, hermitianMatrix]
  ring

/-- The slice is intrinsically the traceless Hermitian part of the
original two-mode algebra in its generated coordinates. -/
theorem mem_slice_iff_trace_zero (q : RealCoordinates) :
    q ∈ slice ↔ Matrix.trace (hermitianMatrix q) = 0 := by
  change q 0 = 0 ↔ Matrix.trace (hermitianMatrix q) = 0
  rw [trace_hermitian]
  constructor
  · intro h
    simp [h]
  · intro h
    have h' : (2 : ℝ) * q 0 = 0 := by exact_mod_cast h
    linarith

def coordinates : Coordinates ≃ₗ[ℝ] slice where
  toFun x := ⟨embed x, embed_mem x⟩
  invFun q := ![q.1 1, q.1 2, q.1 3]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact q.property.symm
    · rfl
    · rfl
    · rfl
  map_add' x y := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [embed]
  map_smul' r x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [embed]

theorem slice_finrank : Module.finrank ℝ slice = 3 := by
  rw [← coordinates.finrank_eq]
  simp [Coordinates, Module.finrank_fintype_fun_eq_card]

theorem determinant_embed (x : Coordinates) :
    determinantForm (embed x) = -(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  simp [determinantForm, embed]
  ring

theorem determinant_nonpos (q : slice) : determinantForm q ≤ 0 := by
  obtain ⟨x, rfl⟩ := coordinates.surjective q
  change determinantForm (embed x) ≤ 0
  rw [determinant_embed]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

theorem determinant_eq_zero_iff (q : slice) :
    determinantForm q = 0 ↔ q = 0 := by
  obtain ⟨x, rfl⟩ := coordinates.surjective q
  change determinantForm (embed x) = 0 ↔ coordinates x = 0
  rw [determinant_embed]
  constructor
  · intro h
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 2)]
    have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have hx : x = 0 := by funext i; fin_cases i <;> assumption
    simp [hx]
  · intro h
    have hx : x = 0 := coordinates.injective (h.trans (map_zero coordinates).symm)
    simp [hx]

structure Conclusions : Prop where
  actual_dimension : Module.finrank ℝ slice = 3
  actual_subspace : ∀ q : RealCoordinates,
    q ∈ slice ↔ Matrix.trace (hermitianMatrix q) = 0
  negative_form : ∀ q : slice, determinantForm q ≤ 0
  definite_form : ∀ q : slice, determinantForm q = 0 ↔ q = 0
  complete_coordinates : Function.Bijective coordinates

theorem generated : Conclusions where
  actual_dimension := slice_finrank
  actual_subspace := mem_slice_iff_trace_zero
  negative_form := determinant_nonpos
  definite_form := determinant_eq_zero_iff
  complete_coordinates := coordinates.bijective

end GeneratedFoundations.Geometry.SourceSpatialCarrier
