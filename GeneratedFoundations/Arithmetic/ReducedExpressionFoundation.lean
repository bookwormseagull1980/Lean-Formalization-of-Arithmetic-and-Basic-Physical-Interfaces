module

public import GeneratedFoundations.Arithmetic.GeneratedFoundation
public import GeneratedFoundations.Arithmetic.ReducedExpressionTransport

/-!
# Reduced-expression resolution from minimal unbiased compositional change

This module exposes the expression-resolution interface at the root of the
library.  Its only root argument is the existing minimal-unbiased-change
datum.  Widths and orientations are universally quantified realizations of
that datum; they are not additional fields or closure assumptions.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Source
open GeneratedFoundations.Source.CarrierOrientation

namespace GeneratedFoundations.Arithmetic.ReducedExpression

open TypedSourceModes

/-- The finite-fiber expression-resolution properties of an actual generated
source-mode family. -/
structure IsGeneratedResolution
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
    (L : ℝ) [Fact (0 < L)] (o : OrientationOnCarrier d) : Prop where
  onto : Function.Surjective (evalTyped d h L o)
  finite : ∀ u : Mode d h L o, Set.Finite {x : Expr | evalTyped d h L o x = u}
  add : ∀ x y, evalTyped d h L o (x + y) =
    evalTyped d h L o x + evalTyped d h L o y
  mul : ∀ x y, evalTyped d h L o (x * y) =
    evalTyped d h L o x * evalTyped d h L o y

theorem generatedResolution
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
    (L : ℝ) [Fact (0 < L)] (o : OrientationOnCarrier d) :
    IsGeneratedResolution d h L o where
  onto := evalTyped_surjective d h L o
  finite := finite_typed_fiber d h L o
  add := evalTyped_add d h L o
  mul := evalTyped_mul d h L o

open GeneratedFoundation
open GeneratedFoundations.Spectral

set_option linter.style.haveILetI false

/-- The expression resolution requires no root input beyond the existing
minimal-unbiased-compositional-change datum. -/
theorem resolution_fromMinimalUnbiasedChange
    (source : MinimalUnbiasedChange.Datum) :
    ∀ (o : OrientationOnCarrier source.change) (b : ℝ) (hb : 0 < b),
      letI : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
      IsGeneratedResolution source.change source.minimal (windowLengthGenerated b) o := by
  intro o b hb
  haveI : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
  exact generatedResolution source.change source.minimal (windowLengthGenerated b) o

/-- For a single root datum, every pair of its derived scales and orientations
uses the same reduced expression and commutes with the canonical transport. -/
theorem transport_fromMinimalUnbiasedChange
    (source : MinimalUnbiasedChange.Datum) :
    ∀ (o p : OrientationOnCarrier source.change)
      (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (x : Expr),
      letI : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
      letI : Fact (0 < windowLengthGenerated c) := ⟨windowLengthGenerated_pos hc⟩
      GeneratedTransport.transport source.change source.minimal
          (windowLengthGenerated b) o source.change source.minimal
          (windowLengthGenerated c) p
          (evalTyped source.change source.minimal (windowLengthGenerated b) o x) =
        evalTyped source.change source.minimal (windowLengthGenerated c) p x := by
  intro o p b c hb hc x
  haveI : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
  haveI : Fact (0 < windowLengthGenerated c) := ⟨windowLengthGenerated_pos hc⟩
  exact evalTyped_transport source.change source.minimal (windowLengthGenerated b) o
    source.change source.minimal (windowLengthGenerated c) p x

end GeneratedFoundations.Arithmetic.ReducedExpression
