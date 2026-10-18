module

public import GeneratedFoundations.Arithmetic.CompleteHistorySource
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The complete finite natural fibre

The scalar root is only the evaluation coordinate of a generated natural
object.  Its complete finite fibre retains the ordered history and the
canonical phase kernel at that root.  This is the first information-preserving
completion after the scalar semiring; no Fourier transform or signed
arithmetic observation is used in its construction.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.CompleteNaturalObject

open GeneratedFoundations.Arithmetic.CompleteHistory

/-- The canonical finite phase coordinate at a positive root. -/
abbrev PhaseFiber (k : ℕ) [NeZero k] := ZMod k

/-- The phase coordinate is exactly the kernel of the `k`-fold circle map. -/
noncomputable def phaseKernelEquiv (k : ℕ) [NeZero k] :
    PhaseFiber k ≃ rootsOfUnity k Circle :=
  Equiv.ofBijective (ZMod.rootsOfUnityAddChar k)
    (bijective_rootsOfUnityAddChar k)

theorem phaseFiber_card (k : ℕ) [NeZero k] :
    Fintype.card (PhaseFiber k) = k := by
  simp [PhaseFiber]

/-- A complete positive natural point: one ordered construction history and
one point of the phase kernel at the same generated root. -/
abbrev CompleteFiber (k : ℕ) [NeZero k] := History k × PhaseFiber k

theorem completeFiber_card (k : ℕ) [NeZero k] :
    Fintype.card (CompleteFiber k) = Fintype.card (History k) * k := by
  simp [CompleteFiber]

/-- Forgetting the retained history and phase returns the scalar root. -/
def rootValue {k : ℕ} [NeZero k] (_x : CompleteFiber k) : ℕ := k

@[simp] theorem rootValue_eq {k : ℕ} [NeZero k] (x : CompleteFiber k) :
    rootValue x = k := rfl

/-- The complete-fibre construction and its phase-kernel interpretation. -/
structure Conclusions : Prop where
  phase_kernel : ∀ (k : ℕ) [NeZero k],
    Nonempty (PhaseFiber k ≃ rootsOfUnity k Circle)
  phase_cardinality : ∀ (k : ℕ) [NeZero k],
    Fintype.card (PhaseFiber k) = k
  complete_cardinality : ∀ (k : ℕ) [NeZero k],
    Fintype.card (CompleteFiber k) = Fintype.card (History k) * k
  scalar_forgetting : ∀ {k : ℕ} [NeZero k] (x : CompleteFiber k),
    rootValue x = k

theorem completeNaturalObjectConclusions : Conclusions where
  phase_kernel := fun k => ⟨phaseKernelEquiv k⟩
  phase_cardinality := phaseFiber_card
  complete_cardinality := completeFiber_card
  scalar_forgetting := rootValue_eq

end GeneratedFoundations.Arithmetic.CompleteNaturalObject
