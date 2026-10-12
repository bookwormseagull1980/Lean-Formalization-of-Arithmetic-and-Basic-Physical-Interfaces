module

public import GeneratedFoundations.Arithmetic.ReducedExpressionSyntax
public import GeneratedFoundations.Arithmetic.NativePeano

/-!
# Evaluation of reduced expressions

The ordered expression object is evaluated in the already generated natural
circle modes.  Equality of evaluations supplies a second, coarser quotient:
its classes are canonically equivalent to the native natural-mode semiring.
No relation is added to the expression syntax itself.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.ReducedExpression

open NativeModes

/-- The comparison target carried by the ordinary natural numbers. -/
def natTarget : Target ℕ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_zero_right := Nat.add_zero
  add_zero_left := Nat.zero_add
  mul_one_right := Nat.mul_one
  mul_one_left := Nat.one_mul
  mul_zero_right := Nat.mul_zero
  mul_zero_left := Nat.zero_mul

/-- The comparison target carried by the already generated circle modes. -/
def nativeTarget : Target Mode where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_zero_right := add_zero
  add_zero_left := zero_add
  mul_one_right := mul_one
  mul_one_left := one_mul
  mul_zero_right := mul_zero
  mul_zero_left := zero_mul

/-- Natural-number value of a reduced ordered expression. -/
def evalNat : Expr → ℕ := Target.interpret natTarget

/-- Native circle mode represented by a reduced ordered expression. -/
def evalNative : Expr → Mode := Target.interpret nativeTarget

@[simp] theorem evalNat_zero : evalNat 0 = 0 := rfl
@[simp] theorem evalNat_one : evalNat 1 = 1 := rfl
@[simp] theorem evalNative_zero : evalNative 0 = 0 := rfl
@[simp] theorem evalNative_one : evalNative 1 = 1 := rfl

@[simp] theorem evalNat_add (e f : Expr) : evalNat (e + f) = evalNat e + evalNat f :=
  (Target.canonicalHom natTarget).map_add e f

@[simp] theorem evalNat_mul (e f : Expr) : evalNat (e * f) = evalNat e * evalNat f :=
  (Target.canonicalHom natTarget).map_mul e f

@[simp] theorem evalNative_add (e f : Expr) :
    evalNative (e + f) = evalNative e + evalNative f :=
  (Target.canonicalHom nativeTarget).map_add e f

@[simp] theorem evalNative_mul (e f : Expr) :
    evalNative (e * f) = evalNative e * evalNative f :=
  (Target.canonicalHom nativeTarget).map_mul e f

/-- The canonical reduced expression for a natural numeral. -/
def numeral : ℕ → Expr
  | 0 => 0
  | n + 1 => numeral n + 1

/-- Right insertion of the distinguished unit expression. -/
def successorExpr (e : Expr) : Expr := e + 1

@[simp] theorem evalNat_successorExpr (e : Expr) :
    evalNat (successorExpr e) = evalNat e + 1 := by
  simp [successorExpr]

theorem successorExpr_injective : Function.Injective successorExpr := by
  intro e f h
  rcases e with ⟨e, he⟩
  rcases f with ⟨f, hf⟩
  have hv := congrArg Subtype.val h
  change (RawExpr.normalize (.add e .one)) =
    (RawExpr.normalize (.add f .one)) at hv
  change RawExpr.reducedAdd e.normalize .one =
    RawExpr.reducedAdd f.normalize .one at hv
  rw [he, hf] at hv
  apply Expr.ext
  change e = f
  cases e <;> cases f <;>
    simp_all [RawExpr.reducedAdd]

@[simp] theorem evalNat_numeral (n : ℕ) : evalNat (numeral n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, ih]

private def powerOfNatEvaluation : Target.Hom nativeTarget where
  toFun e := powerMode (evalNat e)
  map_zero := powerMode_zero
  map_one := powerMode_one
  map_add e f := by
    rw [evalNat_add, powerMode_add]
    rfl
  map_mul e f := by
    rw [evalNat_mul, powerMode_mul]
    rfl

/-- Evaluation in native modes is exactly the generated power mode indexed by
the natural value of the expression. -/
theorem evalNative_eq_powerMode_evalNat (e : Expr) :
    evalNative e = powerMode (evalNat e) := by
  have h := congrArg (fun F : Target.Hom nativeTarget => F e)
    (Target.hom_unique (Target.canonicalHom nativeTarget) powerOfNatEvaluation)
  exact h

@[simp] theorem evalNative_numeral (n : ℕ) : evalNative (numeral n) = powerMode n := by
  rw [evalNative_eq_powerMode_evalNat, evalNat_numeral]

theorem evalNative_surjective : Function.Surjective evalNative := by
  intro u
  exact ⟨numeral (index u), by simp⟩

/-- Equality after evaluation in the generated native modes. -/
def EvalEq (e f : Expr) : Prop := evalNative e = evalNative f

theorem evalEq_equivalence : Equivalence EvalEq := by
  exact ⟨fun _ => rfl, fun {_ _} h => h.symm,
    fun {_ _ _} h₁ h₂ => h₁.trans h₂⟩

theorem evalEq_add {e e' f f' : Expr} (he : EvalEq e e') (hf : EvalEq f f') :
    EvalEq (e + f) (e' + f') := by
  simpa only [EvalEq, evalNative_add] using congrArg₂ (· + ·) he hf

theorem evalEq_mul {e e' f f' : Expr} (he : EvalEq e e') (hf : EvalEq f f') :
    EvalEq (e * f) (e' * f') := by
  simpa only [EvalEq, evalNative_mul] using congrArg₂ (· * ·) he hf

def evalSetoid : Setoid Expr where
  r := EvalEq
  iseqv := evalEq_equivalence

/-- Expressions modulo equality of their generated natural-mode values. -/
def EvalQuotient := Quotient evalSetoid

/-- Addition descending directly from ordered-expression addition. -/
def quotientAdd : EvalQuotient → EvalQuotient → EvalQuotient :=
  Quotient.map₂ (· + ·) (fun _ _ he _ _ hf => evalEq_add he hf)

/-- Multiplication descending directly from ordered-expression cascade. -/
def quotientMul : EvalQuotient → EvalQuotient → EvalQuotient :=
  Quotient.map₂ (· * ·) (fun _ _ he _ _ hf => evalEq_mul he hf)

/-- Evaluation descends to the evaluation quotient. -/
def quotientEval : EvalQuotient → Mode :=
  Quotient.lift evalNative (fun _ _ h => h)

@[simp] theorem quotientEval_quotientAdd (q r : EvalQuotient) :
    quotientEval (quotientAdd q r) = quotientEval q + quotientEval r := by
  refine Quotient.inductionOn₂ q r ?_
  intro e f
  exact evalNative_add e f

@[simp] theorem quotientEval_quotientMul (q r : EvalQuotient) :
    quotientEval (quotientMul q r) = quotientEval q * quotientEval r := by
  refine Quotient.inductionOn₂ q r ?_
  intro e f
  exact evalNative_mul e f

/-- The numeral representative supplies the canonical inverse section. -/
def quotientSection (u : Mode) : EvalQuotient :=
  Quotient.mk evalSetoid (numeral (index u))

@[simp] theorem quotientEval_section (u : Mode) :
    quotientEval (quotientSection u) = u := by
  change evalNative (numeral (index u)) = u
  simp

@[simp] theorem quotientSection_eval (q : EvalQuotient) :
    quotientSection (quotientEval q) = q := by
  refine Quotient.inductionOn q ?_
  intro e
  apply Quotient.sound
  change evalNative (numeral (index (evalNative e))) = evalNative e
  simp

/-- The evaluation quotient is canonically the previously generated native
natural-mode family. -/
def evalQuotientEquiv : EvalQuotient ≃ Mode where
  toFun := quotientEval
  invFun := quotientSection
  left_inv := quotientSection_eval
  right_inv := quotientEval_section

noncomputable instance instCommSemiringEvalQuotient : CommSemiring EvalQuotient :=
  evalQuotientEquiv.commSemiring

/-- The transported semiring addition is the operation descended from the
expression syntax, rather than an independently chosen operation. -/
theorem evalQuotient_add_eq_descended (q r : EvalQuotient) :
    q + r = quotientAdd q r := by
  apply evalQuotientEquiv.injective
  calc
    evalQuotientEquiv (q + r) = evalQuotientEquiv q + evalQuotientEquiv r := by
      change evalQuotientEquiv
        (evalQuotientEquiv.symm (evalQuotientEquiv q + evalQuotientEquiv r)) = _
      exact evalQuotientEquiv.apply_symm_apply _
    _ = evalQuotientEquiv (quotientAdd q r) :=
      (quotientEval_quotientAdd q r).symm

/-- The transported semiring multiplication is the operation descended from
the expression syntax, rather than an independently chosen operation. -/
theorem evalQuotient_mul_eq_descended (q r : EvalQuotient) :
    q * r = quotientMul q r := by
  apply evalQuotientEquiv.injective
  calc
    evalQuotientEquiv (q * r) = evalQuotientEquiv q * evalQuotientEquiv r := by
      change evalQuotientEquiv
        (evalQuotientEquiv.symm (evalQuotientEquiv q * evalQuotientEquiv r)) = _
      exact evalQuotientEquiv.apply_symm_apply _
    _ = evalQuotientEquiv (quotientMul q r) :=
      (quotientEval_quotientMul q r).symm

/-- Evaluation is a semiring equivalence after quotienting precisely by equal
generated values. -/
def evalQuotientRingEquiv : EvalQuotient ≃+* Mode where
  toEquiv := evalQuotientEquiv
  map_add' x y := by
    change evalQuotientEquiv
      (evalQuotientEquiv.symm (evalQuotientEquiv x + evalQuotientEquiv y)) = _
    exact evalQuotientEquiv.apply_symm_apply _
  map_mul' x y := by
    change evalQuotientEquiv
      (evalQuotientEquiv.symm (evalQuotientEquiv x * evalQuotientEquiv y)) = _
    exact evalQuotientEquiv.apply_symm_apply _

theorem evalEq_iff_evalNat_eq (e f : Expr) : EvalEq e f ↔ evalNat e = evalNat f := by
  rw [EvalEq, evalNative_eq_powerMode_evalNat, evalNative_eq_powerMode_evalNat]
  exact powerMode_injective.eq_iff

end GeneratedFoundations.Arithmetic.ReducedExpression
