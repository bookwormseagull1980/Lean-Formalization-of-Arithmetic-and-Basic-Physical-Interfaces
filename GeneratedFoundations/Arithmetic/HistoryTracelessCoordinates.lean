module

public import GeneratedFoundations.Arithmetic.HistoryLieAlgebra

/-!
# Unique coordinates for complete traceless arithmetic operations

One diagonal entry is eliminated using the actual distinguished source
history. All other matrix entries remain. The omitted entry is reconstructed
from the trace equation. This yields unique coordinates, in contrast to the
redundant centred-unit spanning family. No dimension-three colour corner is
substituted for the full arithmetic algebra.

The reconstructed coefficient metric retains the contribution of that
diagonal entry. It is not the unweighted sum of the retained entries alone.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace GeneratedFoundations.Arithmetic.HistoryTracelessCoordinates

open HistoryCliffordAction (Index Algebra historyPoint)

def pivot (N : ℕ) : Index N := (historyPoint N, Sum.inl 0)

abbrev CoordinateIndex (N : ℕ) := {a : Index N × Index N // a ≠ (pivot N, pivot N)}
abbrev Coordinates (N : ℕ) := CoordinateIndex N → ℂ

def diagonal (N : ℕ) (c : Coordinates N) (i : Index N) : ℂ :=
  if hi : i = pivot N then 0 else c ⟨(i, i), fun h => hi (congrArg Prod.fst h)⟩

def matrix (N : ℕ) (c : Coordinates N) : Algebra N :=
  fun i j => if h : (i, j) = (pivot N, pivot N) then -∑ k, diagonal N c k
    else c ⟨(i, j), h⟩

def coordinates (N : ℕ) (X : Algebra N) : Coordinates N := fun a => X a.val.1 a.val.2

theorem matrix_diagonal (N : ℕ) (c : Coordinates N) (i : Index N) :
    matrix N c i i = diagonal N c i - if i = pivot N then ∑ k, diagonal N c k else 0 := by
  by_cases hi : i = pivot N
  · subst i
    simp [matrix, diagonal]
  · simp [matrix, diagonal, hi, Prod.mk.injEq]

theorem matrix_trace (N : ℕ) (c : Coordinates N) : Matrix.trace (matrix N c) = 0 := by
  change (∑ i, matrix N c i i) = 0
  simp_rw [matrix_diagonal]
  rw [Finset.sum_sub_distrib]
  simp

theorem coordinates_matrix (N : ℕ) (c : Coordinates N) :
    coordinates N (matrix N c) = c := by
  funext a
  exact dite_eq_right a.property

theorem diagonal_coordinates (N : ℕ) (X : Algebra N) :
    (∑ i, diagonal N (coordinates N X) i) = Matrix.trace X - X (pivot N) (pivot N) := by
  have hs : Matrix.trace X = X (pivot N) (pivot N) + ∑ i,
      diagonal N (coordinates N X) i := by
    calc
      _ = ∑ i, ((if i = pivot N then X (pivot N) (pivot N) else 0) +
          diagonal N (coordinates N X) i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = pivot N <;> simp [diagonal, coordinates, hi]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linear_combination -hs

theorem matrix_coordinates (N : ℕ) (X : Algebra N) (hX : Matrix.trace X = 0) :
    matrix N (coordinates N X) = X := by
  ext i j
  by_cases hij : (i, j) = (pivot N, pivot N)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
    simp [matrix, diagonal_coordinates, hX]
  · simp [matrix, hij, coordinates]

theorem matrix_injective (N : ℕ) : Function.Injective (matrix N) := by
  intro c d h
  simpa only [coordinates_matrix] using congrArg (coordinates N) h

theorem coordinates_add (N : ℕ) (X Y : Algebra N) :
    coordinates N (X + Y) = coordinates N X + coordinates N Y := rfl

theorem coordinates_smul (N : ℕ) (t : ℂ) (X : Algebra N) :
    coordinates N (t • X) = t • coordinates N X := rfl

theorem coordinates_injective_on (N : ℕ) (X Y : Algebra N)
    (hX : Matrix.trace X = 0) (hY : Matrix.trace Y = 0)
    (h : coordinates N X = coordinates N Y) : X = Y := by
  rw [← matrix_coordinates N X hX, ← matrix_coordinates N Y hY, h]

theorem matrix_add (N : ℕ) (c d : Coordinates N) :
    matrix N (c + d) = matrix N c + matrix N d := by
  apply coordinates_injective_on N _ _ (matrix_trace N _)
    (by rw [Matrix.trace_add, matrix_trace, matrix_trace, add_zero])
  rw [coordinates_add, coordinates_matrix, coordinates_matrix, coordinates_matrix]

theorem matrix_smul (N : ℕ) (t : ℂ) (c : Coordinates N) :
    matrix N (t • c) = t • matrix N c := by
  apply coordinates_injective_on N _ _ (matrix_trace N _)
    (by rw [Matrix.trace_smul, matrix_trace, smul_zero])
  rw [coordinates_smul, coordinates_matrix, coordinates_matrix]

theorem matrix_neg (N : ℕ) (c : Coordinates N) : matrix N (-c) = -matrix N c := by
  simpa only [neg_one_smul] using matrix_smul N (-1) c

def adjointCoordinates (N : ℕ) (c : Coordinates N) : Coordinates N :=
  coordinates N (matrix N c).conjTranspose

theorem matrix_adjoint (N : ℕ) (c : Coordinates N) :
    matrix N (adjointCoordinates N c) = (matrix N c).conjTranspose := by
  apply matrix_coordinates
  simp [Matrix.trace_conjTranspose, matrix_trace]

theorem adjointCoordinates_square (N : ℕ) (c : Coordinates N) :
    adjointCoordinates N (adjointCoordinates N c) = c := by
  apply matrix_injective N
  rw [matrix_adjoint, matrix_adjoint, Matrix.conjTranspose_conjTranspose]

/-- Reality of the Lie connection is the transported adjoint condition.
It is not imposed by declaring all retained matrix entries to be real. -/
theorem matrix_isLie_iff (N : ℕ) (c : Coordinates N) :
    HistoryLieAlgebra.IsLie N (matrix N c) ↔ adjointCoordinates N c = -c := by
  constructor
  · intro hc
    apply matrix_injective N
    rw [matrix_adjoint, matrix_neg]
    exact hc.1
  · intro hc
    refine ⟨?_, matrix_trace N c⟩
    rw [← matrix_adjoint, hc, matrix_neg]

/-- The real form is an adjoint constraint on the complete complex
coordinates. It does not require each original matrix entry to be real. -/
abbrev RealCoordinates (N : ℕ) :=
  {c : Coordinates N // adjointCoordinates N c = -c}

def realCoordinateEquiv (N : ℕ) :
    {X : Algebra N // HistoryLieAlgebra.IsLie N X} ≃ RealCoordinates N where
  toFun X := ⟨coordinates N X.val, (matrix_isLie_iff N _).mp
    (by rw [matrix_coordinates N X.val X.property.2]; exact X.property)⟩
  invFun c := ⟨matrix N c.val, (matrix_isLie_iff N _).mpr c.property⟩
  left_inv X := Subtype.ext (matrix_coordinates N X.val X.property.2)
  right_inv c := Subtype.ext (coordinates_matrix N c.val)

theorem real_coordinates_skew (N : ℕ) (c : RealCoordinates N) :
    (matrix N c.val).conjTranspose = -matrix N c.val :=
  ((matrix_isLie_iff N _).mpr c.property).1

theorem real_coordinates_unique (N : ℕ) (X : Algebra N)
    (hX : HistoryLieAlgebra.IsLie N X) :
    ∃! c : RealCoordinates N, matrix N c.val = X := by
  refine ⟨realCoordinateEquiv N ⟨X, hX⟩, ?_, ?_⟩
  · change matrix N (coordinates N X) = X
    exact matrix_coordinates N X hX.2
  · intro c hc
    apply Subtype.ext
    change c.val = coordinates N X
    exact matrix_injective N (hc.trans (matrix_coordinates N X hX.2).symm)

def traceless (N : ℕ) : Submodule ℂ (Algebra N) :=
  LinearMap.ker (Matrix.traceLinearMap (Index N) ℂ ℂ)

def coordinateMap (N : ℕ) : traceless N →ₗ[ℂ] Coordinates N where
  toFun X := coordinates N X.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinateMap_bijective (N : ℕ) : Function.Bijective (coordinateMap N) := by
  constructor
  · intro X Y h
    apply Subtype.ext
    have hx : Matrix.trace X.val = 0 := X.property
    have hy : Matrix.trace Y.val = 0 := Y.property
    have he := congrArg (matrix N) h
    exact (matrix_coordinates N X.val hx).symm.trans
      (he.trans (matrix_coordinates N Y.val hy))
  · intro c
    exact ⟨⟨matrix N c, matrix_trace N c⟩, coordinates_matrix N c⟩

def coordinateEquiv (N : ℕ) : traceless N ≃ₗ[ℂ] Coordinates N :=
  LinearEquiv.ofBijective (coordinateMap N) (coordinateMap_bijective N)

theorem coordinate_count (N : ℕ) :
    Fintype.card (CoordinateIndex N) = HistoryAdjointCasimir.dimension N ^ 2 - 1 := by
  simp [CoordinateIndex, HistoryAdjointCasimir.dimension, pow_two]

/-- The trace metric in unique coordinates contains the coherent diagonal
return. Its cross-coordinate terms are part of the metric. -/
def gram (N : ℕ) (c d : Coordinates N) : ℂ :=
  ∑ a, star (c a) * d a + star (∑ i, diagonal N c i) * ∑ i, diagonal N d i

theorem trace_pair (N : ℕ) (c d : Coordinates N) :
    Matrix.trace ((matrix N c).conjTranspose * matrix N d) = gram N c d := by
  let f : Index N × Index N → ℂ := fun a =>
    star (matrix N c a.1 a.2) * matrix N d a.1 a.2
  have hs : (∑ a, f a) = f (pivot N, pivot N) +
      ∑ a : CoordinateIndex N, f a :=
    Fintype.sum_eq_add_sum_subtype_ne f (pivot N, pivot N)
  have heq : f (pivot N, pivot N) =
      star (∑ i, diagonal N c i) * ∑ i, diagonal N d i := by
    simp [f, matrix]
  have hne : (∑ a : CoordinateIndex N, f a) = ∑ a, star (c a) * d a := by
    apply Finset.sum_congr rfl
    intro a _
    simp [f, matrix, a.property]
  rw [heq, hne] at hs
  change (∑ i, ∑ j, star (matrix N c j i) * matrix N d j i) = _
  rw [Finset.sum_comm]
  change (∑ i, ∑ j, f (i, j)) = _
  rw [← Fintype.sum_prod_type]
  exact hs.trans (add_comm _ _)

theorem trace_hermitian_pair (N : ℕ) (c d : Coordinates N) :
    Matrix.trace (matrix N c * matrix N d) = gram N (adjointCoordinates N c) d := by
  rw [← trace_pair, matrix_adjoint, Matrix.conjTranspose_conjTranspose]

theorem gram_norm_eq (N : ℕ) (c : Coordinates N) :
    (gram N c c).re = ∑ a, ‖c a‖ ^ 2 + ‖∑ i, diagonal N c i‖ ^ 2 := by
  have hp (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    change ((starRingEnd ℂ) z * z).re = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rfl
  simp only [gram, Complex.add_re, Complex.re_sum, hp]

theorem trace_norm_formula (N : ℕ) (c : Coordinates N) :
    (Matrix.trace ((matrix N c).conjTranspose * matrix N c)).re =
      ∑ a, ‖c a‖ ^ 2 + ‖∑ i, diagonal N c i‖ ^ 2 := by
  rw [trace_pair, gram_norm_eq]

theorem gram_positive {N : ℕ} {c : Coordinates N} (hc : c ≠ 0) :
    0 < (gram N c c).re := by
  have hz : ∃ a, c a ≠ 0 := by
    by_contra h
    apply hc
    funext a
    exact not_not.mp (not_exists.mp h a)
  obtain ⟨a, ha⟩ := hz
  have hs : 0 < ∑ a, ‖c a‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ a, by positivity⟩
  rw [gram_norm_eq]
  exact add_pos_of_pos_of_nonneg hs (sq_nonneg _)

def bracket (N : ℕ) (c d : Coordinates N) : Coordinates N :=
  coordinates N (matrix N c * matrix N d - matrix N d * matrix N c)

theorem matrix_bracket (N : ℕ) (c d : Coordinates N) :
    matrix N (bracket N c d) = matrix N c * matrix N d - matrix N d * matrix N c := by
  apply matrix_coordinates
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

theorem bracket_smul (N : ℕ) (s t : ℂ) (c d : Coordinates N) :
    bracket N (s • c) (t • d) = (s * t) • bracket N c d := by
  apply matrix_injective N
  rw [matrix_bracket, matrix_smul, matrix_smul, matrix_smul, matrix_bracket]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, mul_comm t s]

theorem bracket_add_left (N : ℕ) (c d e : Coordinates N) :
    bracket N (c + d) e = bracket N c e + bracket N d e := by
  apply matrix_injective N
  rw [matrix_bracket, matrix_add, matrix_add, matrix_bracket, matrix_bracket,
    add_mul, mul_add]
  abel

theorem coordinateEquiv_unique (N : ℕ) (e : traceless N ≃ₗ[ℂ] Coordinates N)
    (he : ∀ X a, e X a = X.val a.val.1 a.val.2) : e = coordinateEquiv N := by
  apply LinearEquiv.ext
  intro X
  funext a
  exact he X a

structure Conclusions : Prop where
  reconstruction : ∀ N X, Matrix.trace X = 0 → matrix N (coordinates N X) = X
  unique_coordinates : ∀ N, Function.Injective (matrix N)
  complete_coordinates : ∀ N, Function.Bijective (coordinateMap N)
  actual_dimension : ∀ N,
    Fintype.card (CoordinateIndex N) = HistoryAdjointCasimir.dimension N ^ 2 - 1
  full_trace_metric : ∀ N c d,
    Matrix.trace ((matrix N c).conjTranspose * matrix N d) = gram N c d
  positive_metric : ∀ N c, c ≠ 0 → 0 < (gram N c c).re
  exact_commutator : ∀ N c d,
    matrix N (bracket N c d) = matrix N c * matrix N d - matrix N d * matrix N c
  adjoint_transport : ∀ N c,
    matrix N (adjointCoordinates N c) = (matrix N c).conjTranspose
  actual_real_condition : ∀ N c,
    HistoryLieAlgebra.IsLie N (matrix N c) ↔ adjointCoordinates N c = -c

theorem generated : Conclusions where
  reconstruction := matrix_coordinates
  unique_coordinates := matrix_injective
  complete_coordinates := coordinateMap_bijective
  actual_dimension := coordinate_count
  full_trace_metric := trace_pair
  positive_metric := fun _ _ => gram_positive
  exact_commutator := matrix_bracket
  adjoint_transport := matrix_adjoint
  actual_real_condition := matrix_isLie_iff

end GeneratedFoundations.Arithmetic.HistoryTracelessCoordinates
