module

public import GeneratedFoundations.Arithmetic.HistoryCliffordAction
public import GeneratedFoundations.Operations.SourceDeterminantCompensation

/-!
# Determinant compensation on every retained arithmetic label

The original Gaussian two-mode source, at its generated unit covariance,
is repeated on the complete arithmetic history--phase label set. Tensoring
with its determinant line retains a determinant character on each label.
The unique inverse character recovers the original action simultaneously
on all labels; neither a history quotient nor a determinant-one restriction
is taken. Invertibility specifies the domain of the group action, not a
condition on the generated root.
-/

@[expose] public section
noncomputable section
namespace GeneratedFoundations.Arithmetic.HistoryDeterminantCompensation

open Operations.SourceSpinCorner
open Operations.SourceVacuumTransport
open Source.CanonicalRealization

abbrev SourceFibre := V width_pos
abbrev TwistedFibre := TwistedCarrier width_pos
abbrev Label (N : ℕ) := HistoryCliffordAction.HistoryLabel N
abbrev Space (N : ℕ) := Label N → TwistedFibre

def transport (N : ℕ) (x : Label N → SourceFibre) : Space N :=
  fun i => Operations.SourceVacuumTransport.transport width_pos (x i)

def relativeAction (N : ℕ) (M : Mat2) (x : Space N) : Space N :=
  fun i => Operations.SourceDeterminantCompensation.relativeAction width_pos M (x i)

theorem complete_transport (N : ℕ) (M : Mat2) (hM : M.det ≠ 0)
    (x : Label N → SourceFibre) :
    relativeAction N M (transport N x) =
      transport N (fun i => sourceAction width_pos M (x i)) := by
  funext i
  exact Operations.SourceDeterminantCompensation.relativeAction_transport width_pos M hM (x i)

theorem relativeAction_mul (N : ℕ) (M K : Mat2) (hM : M.det ≠ 0) (hK : K.det ≠ 0)
    (x : Space N) :
    relativeAction N (M * K) x = relativeAction N M (relativeAction N K x) := by
  funext i
  exact LinearMap.congr_fun
    (Operations.SourceDeterminantCompensation.relativeAction_mul width_pos M K hM hK) (x i)

theorem correction_unique (N : ℕ) (M : Mat2) (hM : M.det ≠ 0) (z : ℂ)
    (hz : ∀ (x : Space N) i,
      z • twistedAction width_pos M (x i) = conjugatedAction width_pos M (x i)) :
    z = M.det⁻¹ := by
  apply Operations.SourceDeterminantCompensation.scalar_correction_unique width_pos M hM z
  apply LinearMap.ext
  intro v
  exact hz (fun _ => v) (HistoryCliffordAction.historyPoint N)

structure Conclusions : Prop where
  all_histories : ∀ N M, M.det ≠ 0 → ∀ x,
    relativeAction N M (transport N x) =
      transport N (fun i => sourceAction width_pos M (x i))
  unique_correction : ∀ N M, M.det ≠ 0 → ∀ z,
    (∀ (x : Space N) i,
      z • twistedAction width_pos M (x i) = conjugatedAction width_pos M (x i)) →
    z = M.det⁻¹

theorem generated : Conclusions where
  all_histories := complete_transport
  unique_correction := correction_unique

end GeneratedFoundations.Arithmetic.HistoryDeterminantCompensation
