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

/-- The complete algebraic resolution of the generated natural-mode family.

The ordered expression syntax is reduced only by the six displayed unit and
zero laws.  Evaluation then supplies a second quotient.  The fields below
record that its two operations descend from the syntax itself and that the
resulting quotient is exactly the generated native arithmetic.  Thus the
semiring structure is not transported back after an unrelated identification.
-/
structure IsGeneratedResolution
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
    (L : ℝ) [Fact (0 < L)] (o : OrientationOnCarrier d) : Prop where
  normal_form : ∀ e : RawExpr,
    ∃! f : RawExpr, f.IsReduced ∧ ReductionEq e f
  initial : ∀ (A : Type) (T : Target A),
    ∃! F : Target.Hom T, ∀ e, F e = Target.interpret T e
  eval_congruence_add : ∀ {e e' f f' : Expr},
    EvalEq e e' → EvalEq f f' → EvalEq (e + f) (e' + f')
  eval_congruence_mul : ∀ {e e' f f' : Expr},
    EvalEq e e' → EvalEq f f' → EvalEq (e * f) (e' * f')
  quotient_native : Function.Bijective quotientEval
  quotient_add_descends : ∀ q r : EvalQuotient, q + r = quotientAdd q r
  quotient_mul_descends : ∀ q r : EvalQuotient, q * r = quotientMul q r
  eval_classification : ∀ e f : Expr, EvalEq e f ↔ evalNat e = evalNat f
  finite_value_fibers : ∀ n : ℕ, Set.Finite {x : Expr | evalNat x = n}
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
  normal_form := normalForm_existsUnique
  initial := fun _ T => Target.hom_existsUnique T
  eval_congruence_add := fun he hf => evalEq_add he hf
  eval_congruence_mul := fun he hf => evalEq_mul he hf
  quotient_native := evalQuotientEquiv.bijective
  quotient_add_descends := evalQuotient_add_eq_descended
  quotient_mul_descends := evalQuotient_mul_eq_descended
  eval_classification := evalEq_iff_evalNat_eq
  finite_value_fibers := finite_fiber
  onto := evalTyped_surjective d h L o
  finite := finite_typed_fiber d h L o
  add := evalTyped_add d h L o
  mul := evalTyped_mul d h L o

open GeneratedFoundation
open GeneratedFoundations.Spectral

set_option linter.style.haveILetI false

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
