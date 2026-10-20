module

public import GeneratedFoundations.Arithmetic.HistoryModuleRepresentation

/-!
# Faithful phase transport on each complete arithmetic fibre

The phase group is the actual finite kernel above the positive generated
root. Its translations permute the existing history--phase labels and hence
act unitarily on the complete coefficient space. The permutation matrix,
Hilbert action and coefficient response are identified entry by entry.

There is no imposed physical charge lattice or prescribed quotient order.
The actual kernel of this arithmetic action is trivial, and its trace is
computed from its fixed points. Averaging real observations is compatible
with the existing generated phase projection.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryPhaseAction

open HistoryPhaseBundle HistoryModuleRepresentation

def unitary (n : ℕ) (q : ZMod (n + 1)) : Space n ≃ₗᵢ[ℂ] Space n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (translate q)

@[simp] theorem unitary_apply (n : ℕ) (q : ZMod (n + 1)) (x : Space n)
    (h : CompleteHistory.History (n + 1)) (a : ZMod (n + 1)) :
    unitary n q x (h, a) = x (h, a - q) := rfl

theorem unitary_zero (n : ℕ) (x : Space n) : unitary n 0 x = x := by
  ext ⟨h, a⟩
  simp

theorem unitary_add (n : ℕ) (p q : ZMod (n + 1)) (x : Space n) :
    unitary n p (unitary n q x) = unitary n (p + q) x := by
  ext ⟨h, a⟩
  simp [sub_sub]

theorem unitary_inner (n : ℕ) (q : ZMod (n + 1)) (x y : Space n) :
    inner ℂ (unitary n q x) (unitary n q y) = inner ℂ x y :=
  (unitary n q).inner_map_map x y

def matrix (n : ℕ) (q : ZMod (n + 1)) : Algebra n :=
  fun i j => if i = translate q j then 1 else 0

theorem matrix_action (n : ℕ) (q : ZMod (n + 1)) (x : Space n) :
    representation n (matrix n q) x = unitary n q x := by
  ext i
  simp only [representation_apply, matrix, ← Equiv.symm_apply_eq,
    ite_mul, one_mul, zero_mul]
  simp
  rfl

theorem matrix_faithful (n : ℕ) : Function.Injective (matrix n) := by
  intro p q hpq
  by_contra hne
  have hc := congrArg (fun A : Algebra n =>
    A ((base n).1, p) ((base n).1, 0)) hpq
  simp [matrix, translate, hne] at hc

theorem unitary_faithful (n : ℕ) : Function.Injective (unitary n) := by
  intro p q hpq
  apply matrix_faithful n
  apply representation_injective n
  apply LinearMap.ext
  intro x
  rw [matrix_action, matrix_action, hpq]

theorem matrix_zero (n : ℕ) : matrix n 0 = 1 := by
  ext i j
  simp [matrix, translate, Matrix.one_apply]

theorem matrix_add (n : ℕ) (p q : ZMod (n + 1)) :
    matrix n (p + q) = matrix n p * matrix n q := by
  apply representation_injective n
  rw [map_mul]
  apply LinearMap.ext
  intro x
  change representation n (matrix n (p + q)) x =
    representation n (matrix n p) (representation n (matrix n q) x)
  rw [matrix_action, matrix_action, matrix_action, unitary_add]

theorem matrix_kernel (n : ℕ) (q : ZMod (n + 1)) : matrix n q = 1 ↔ q = 0 := by
  rw [← matrix_zero n]
  exact (matrix_faithful n).eq_iff

theorem matrix_trace (n : ℕ) (q : ZMod (n + 1)) :
    Matrix.trace (matrix n q) = if q = 0 then (Fintype.card (Index n) : ℂ) else 0 := by
  by_cases hq : q = 0
  · subst q
    simp [matrix_zero]
  · simp only [ite_eq_right hq, Matrix.trace, Matrix.diag]
    apply Finset.sum_eq_zero
    rintro ⟨h, a⟩ _
    simp [matrix, translate, hq]

theorem probability_transport (n : ℕ) (q : ZMod (n + 1)) (x : Fiber n) :
    probability (translate q x) = probability x := rfl

theorem real_average_transport (n : ℕ) (q : ZMod (n + 1)) (f : Fiber n → ℝ) :
    phaseAverage (fun x => f (translate q x)) = phaseAverage f :=
  phaseAverage_translate f q

structure Conclusions : Prop where
  faithful_action : ∀ n, Function.Injective (unitary n)
  actual_matrix_action : ∀ n q (x : Space n),
    representation n (matrix n q) x = unitary n q x
  trivial_kernel : ∀ n q, matrix n q = 1 ↔ q = 0
  actual_character : ∀ n q,
    Matrix.trace (matrix n q) = if q = 0 then (Fintype.card (Index n) : ℂ) else 0
  same_probability : ∀ n q (x : Fiber n), probability (translate q x) = probability x

theorem generated : Conclusions where
  faithful_action := unitary_faithful
  actual_matrix_action := matrix_action
  trivial_kernel := matrix_kernel
  actual_character := matrix_trace
  same_probability := probability_transport

end GeneratedFoundations.Arithmetic.HistoryPhaseAction
