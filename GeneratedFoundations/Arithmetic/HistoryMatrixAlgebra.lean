module

public import GeneratedFoundations.Arithmetic.HistoryPhaseBundle
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Full matrix operations on the actual history--phase fibres

The finite index is the generated fibre, with every history and residue phase
retained. Its coordinate vectors provide the full operation algebra, not a
diagonal substitute. Evaluating an operation on these vectors recovers every
matrix entry and proves both faithfulness and unique reconstruction.

This is a coefficient-space construction. No assertion of unitary transport
between the Neumann and Hermite differential operators is made here.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryMatrixAlgebra

abbrev Index (n : ℕ) := HistoryPhaseBundle.Fiber n
abbrev Space (n : ℕ) := Index n → ℂ
abbrev Algebra (n : ℕ) := Matrix (Index n) (Index n) ℂ

noncomputable instance (n : ℕ) : DecidableEq (Index n) := Classical.decEq _

def representation (n : ℕ) : Algebra n ≃ₐ[ℂ] Module.End ℂ (Space n) :=
  Matrix.toLinAlgEquiv'

def basisVector {n : ℕ} (j : Index n) : Space n := Pi.single j 1

theorem representation_apply {n : ℕ} (A : Algebra n) (v : Space n) (i : Index n) :
    representation n A v i = ∑ j, A i j * v j := rfl

theorem coefficient {n : ℕ} (A : Algebra n) (i j : Index n) :
    representation n A (basisVector j) i = A i j := by
  classical
  simp [representation_apply, basisVector, Pi.single_apply]

theorem faithful (n : ℕ) : Function.Injective (representation n) :=
  (representation n).injective

theorem full (n : ℕ) : Function.Surjective (representation n) :=
  (representation n).surjective

theorem reconstruct {n : ℕ} (F : Module.End ℂ (Space n)) :
    ∃! A : Algebra n, representation n A = F :=
  (representation n).bijective.existsUnique F

theorem tomography {n : ℕ} (A B : Algebra n) :
    (∀ i j, representation n A (basisVector j) i =
      representation n B (basisVector j) i) ↔ A = B := by
  simp only [coefficient]
  constructor
  · exact fun h => Matrix.ext h
  · rintro rfl i j
    rfl

theorem composition {n : ℕ} (A B : Algebra n) :
    representation n (A * B) = representation n A * representation n B :=
  (representation n).map_mul A B

theorem identity (n : ℕ) : representation n 1 = 1 := (representation n).map_one

structure Conclusions : Prop where
  faithful_action : ∀ n, Function.Injective (representation n)
  full_action : ∀ n, Function.Surjective (representation n)
  unique_reconstruction : ∀ {n : ℕ} (F : Module.End ℂ (Space n)),
    ∃! A : Algebra n, representation n A = F
  all_entries : ∀ {n : ℕ} (A : Algebra n) (i j : Index n),
    representation n A (basisVector j) i = A i j
  composition_preserved : ∀ {n : ℕ} (A B : Algebra n),
    representation n (A * B) = representation n A * representation n B

theorem generated : Conclusions where
  faithful_action := faithful
  full_action := full
  unique_reconstruction := reconstruct
  all_entries := coefficient
  composition_preserved := composition

end GeneratedFoundations.Arithmetic.HistoryMatrixAlgebra
