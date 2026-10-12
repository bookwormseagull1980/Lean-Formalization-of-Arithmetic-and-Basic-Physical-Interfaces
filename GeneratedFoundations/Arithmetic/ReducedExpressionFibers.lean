module

public import GeneratedFoundations.Arithmetic.ReducedExpressionEvaluation
public import Mathlib.Data.Finset.NAry

/-!
# Finite fibers of reduced-expression evaluation

Every finite value has only finitely many ordered reduced expressions.  The
proof is intrinsic to the generated syntax: normalization bounds the tree
depth by the natural value, and bounded-depth raw syntax is finite.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.ReducedExpression

namespace RawExpr

/-- Root depth of an ordered raw expression. -/
def depth : RawExpr → ℕ
  | zero | one => 0
  | add e f | mul e f => Nat.max e.depth f.depth + 1

/-- All raw expressions of depth at most the displayed bound. -/
def upToDepth : ℕ → Finset RawExpr
  | 0 => {zero, one}
  | n + 1 =>
      let s := upToDepth n
      {zero, one} ∪ Finset.image₂ add s s ∪ Finset.image₂ mul s s

theorem mem_upToDepth_of_depth_le (e : RawExpr) :
    ∀ n, e.depth ≤ n → e ∈ upToDepth n := by
  induction e with
  | zero =>
      intro n _
      cases n <;> simp [upToDepth]
  | one =>
      intro n _
      cases n <;> simp [upToDepth]
  | add e f he hf =>
      intro n h
      cases n with
      | zero => simp [depth] at h
      | succ n =>
          have hed : e.depth ≤ n := by
            simp [depth] at h
            omega
          have hfd : f.depth ≤ n := by
            simp [depth] at h
            omega
          simp [upToDepth, he n hed, hf n hfd]
  | mul e f he hf =>
      intro n h
      cases n with
      | zero => simp [depth] at h
      | succ n =>
          have hed : e.depth ≤ n := by
            simp [depth] at h
            omega
          have hfd : f.depth ≤ n := by
            simp [depth] at h
            omega
          simp [upToDepth, he n hed, hf n hfd]

end RawExpr

/-- Natural evaluation before normalization. -/
def evalRawNat : RawExpr → ℕ := Target.interpretRaw natTarget

theorem evalRawNat_normalize (e : RawExpr) :
    evalRawNat e.normalize = evalRawNat e :=
  Target.interpret_normalize natTarget e

theorem normalize_eq_zero_iff_evalRawNat_eq_zero (e : RawExpr) :
    e.normalize = .zero ↔ evalRawNat e = 0 := by
  constructor
  · intro h
    rw [← evalRawNat_normalize e, h]
    rfl
  · intro h
    induction e with
    | zero => rfl
    | one => contradiction
    | add e f he hf =>
        change evalRawNat e + evalRawNat f = 0 at h
        have he0 : evalRawNat e = 0 := by omega
        have hf0 : evalRawNat f = 0 := by omega
        simp [RawExpr.normalize, he he0, hf hf0, RawExpr.reducedAdd]
    | mul e f he hf =>
        change evalRawNat e * evalRawNat f = 0 at h
        rcases Nat.mul_eq_zero.mp h with he0 | hf0
        · simp [RawExpr.normalize, he he0, RawExpr.reducedMul]
        · rw [RawExpr.normalize, hf hf0]
          exact RawExpr.reducedMul_zero_right _

theorem normalize_eq_one_iff_evalRawNat_eq_one (e : RawExpr) :
    e.normalize = .one ↔ evalRawNat e = 1 := by
  constructor
  · intro h
    rw [← evalRawNat_normalize e, h]
    rfl
  · intro h
    induction e with
    | zero => contradiction
    | one => rfl
    | add e f he hf =>
        change evalRawNat e + evalRawNat f = 1 at h
        rcases (show (evalRawNat e = 0 ∧ evalRawNat f = 1) ∨
            (evalRawNat e = 1 ∧ evalRawNat f = 0) by omega) with h01 | h10
        · have he0 := (normalize_eq_zero_iff_evalRawNat_eq_zero e).2 h01.1
          simp [RawExpr.normalize, he0, hf h01.2, RawExpr.reducedAdd]
        · have hf0 := (normalize_eq_zero_iff_evalRawNat_eq_zero f).2 h10.2
          simp [RawExpr.normalize, he h10.1, hf0, RawExpr.reducedAdd]
    | mul e f he hf =>
        change evalRawNat e * evalRawNat f = 1 at h
        have hepos : 0 < evalRawNat e := by
          by_contra hn
          have he0 : evalRawNat e = 0 := by omega
          simp [he0] at h
        have hfpos : 0 < evalRawNat f := by
          by_contra hn
          have hf0 : evalRawNat f = 0 := by omega
          simp [hf0] at h
        have he1 : evalRawNat e = 1 := by nlinarith
        have hf1 : evalRawNat f = 1 := by nlinarith
        simp [RawExpr.normalize, he he1, hf hf1, RawExpr.reducedMul]

private theorem reducedAdd_eq_add {x y : RawExpr}
    (hx : x ≠ .zero) (hy : y ≠ .zero) : RawExpr.reducedAdd x y = .add x y := by
  cases x <;> cases y <;> simp_all [RawExpr.reducedAdd]

private theorem reducedMul_eq_mul {x y : RawExpr}
    (hx0 : x ≠ .zero) (hy0 : y ≠ .zero)
    (hx1 : x ≠ .one) (hy1 : y ≠ .one) : RawExpr.reducedMul x y = .mul x y := by
  cases x <;> cases y <;> simp_all [RawExpr.reducedMul]

private theorem normalized_binary_depth_bound
    (x y : RawExpr) (a b : ℕ)
    (hx : x.depth ≤ a) (hy : y.depth ≤ b)
    (hx0 : x = .zero ↔ a = 0) (hy0 : y = .zero ↔ b = 0)
    (hx1 : x = .one ↔ a = 1) (hy1 : y = .one ↔ b = 1) :
    (RawExpr.reducedAdd x y).depth ≤ a + b ∧
      (RawExpr.reducedMul x y).depth ≤ a * b := by
  constructor
  · by_cases ha0 : a = 0
    · have hxe : x = .zero := hx0.2 ha0
      subst x
      simpa [RawExpr.reducedAdd, ha0] using hy
    · by_cases hb0 : b = 0
      · have hye : y = .zero := hy0.2 hb0
        subst y
        rw [RawExpr.reducedAdd_zero_right]
        simpa [hb0] using hx
      · have hxn : x ≠ .zero := fun h => ha0 (hx0.1 h)
        have hyn : y ≠ .zero := fun h => hb0 (hy0.1 h)
        rw [reducedAdd_eq_add hxn hyn]
        simp only [RawExpr.depth]
        apply Nat.succ_le_iff.mpr
        rw [Nat.max_lt]
        constructor <;> omega
  · by_cases ha0 : a = 0
    · have hxe : x = .zero := hx0.2 ha0
      subst x
      simp [RawExpr.reducedMul, ha0, RawExpr.depth]
    · by_cases hb0 : b = 0
      · have hye : y = .zero := hy0.2 hb0
        subst y
        rw [RawExpr.reducedMul_zero_right]
        simp [hb0, RawExpr.depth]
      · by_cases ha1 : a = 1
        · have hxe : x = .one := hx1.2 ha1
          subst x
          rw [RawExpr.reducedMul_one_left]
          simpa [ha1] using hy
        · by_cases hb1 : b = 1
          · have hye : y = .one := hy1.2 hb1
            subst y
            rw [RawExpr.reducedMul_one_right]
            simpa [hb1] using hx
          · have hxn0 : x ≠ .zero := fun h => ha0 (hx0.1 h)
            have hyn0 : y ≠ .zero := fun h => hb0 (hy0.1 h)
            have hxn1 : x ≠ .one := fun h => ha1 (hx1.1 h)
            have hyn1 : y ≠ .one := fun h => hb1 (hy1.1 h)
            have ha2 : 2 ≤ a := by omega
            have hb2 : 2 ≤ b := by omega
            rw [reducedMul_eq_mul hxn0 hyn0 hxn1 hyn1]
            simp only [RawExpr.depth]
            apply Nat.succ_le_iff.mpr
            rw [Nat.max_lt]
            constructor <;> nlinarith

/-- Normalization cannot produce a tree deeper than its natural value. -/
theorem depth_normalize_le_evalRawNat (e : RawExpr) :
    e.normalize.depth ≤ evalRawNat e := by
  induction e with
  | zero => rfl
  | one => simp [RawExpr.normalize, RawExpr.depth, evalRawNat, Target.interpretRaw]
  | add e f he hf =>
      rw [RawExpr.normalize]
      exact (normalized_binary_depth_bound e.normalize f.normalize
        (evalRawNat e) (evalRawNat f) he hf
        (normalize_eq_zero_iff_evalRawNat_eq_zero e)
        (normalize_eq_zero_iff_evalRawNat_eq_zero f)
        (normalize_eq_one_iff_evalRawNat_eq_one e)
        (normalize_eq_one_iff_evalRawNat_eq_one f)).1
  | mul e f he hf =>
      rw [RawExpr.normalize]
      exact (normalized_binary_depth_bound e.normalize f.normalize
        (evalRawNat e) (evalRawNat f) he hf
        (normalize_eq_zero_iff_evalRawNat_eq_zero e)
        (normalize_eq_zero_iff_evalRawNat_eq_zero f)
        (normalize_eq_one_iff_evalRawNat_eq_one e)
        (normalize_eq_one_iff_evalRawNat_eq_one f)).2

theorem expr_depth_le_evalNat (e : Expr) : e.1.depth ≤ evalNat e := by
  rw [← e.2]
  exact depth_normalize_le_evalRawNat e.1

/-- The reduced ordered expressions with a fixed natural value. -/
def Fiber (n : ℕ) := {e : Expr // evalNat e = n}

private def fiberEmbedding (n : ℕ) :
    Fiber n ↪ {e : RawExpr // e ∈ RawExpr.upToDepth n} where
  toFun e := ⟨e.1.1, RawExpr.mem_upToDepth_of_depth_le e.1.1 n (by
    calc
      e.1.1.depth ≤ evalNat e.1 := expr_depth_le_evalNat e.1
      _ = n := e.2)⟩
  inj' := by
    intro e f h
    have hraw : e.1.1 = f.1.1 :=
      congrArg (fun z : {r : RawExpr // r ∈ RawExpr.upToDepth n} => z.1) h
    apply Subtype.ext
    apply Expr.ext
    exact hraw

instance finiteFiber (n : ℕ) : Finite (Fiber n) :=
  Finite.of_injective (fiberEmbedding n) (fiberEmbedding n).injective

/-- Each generated natural value has only finitely many reduced ordered
expression representatives. -/
theorem finite_fiber (n : ℕ) : Set.Finite {e : Expr | evalNat e = n} := by
  change Finite (Fiber n)
  exact finiteFiber n

end GeneratedFoundations.Arithmetic.ReducedExpression
