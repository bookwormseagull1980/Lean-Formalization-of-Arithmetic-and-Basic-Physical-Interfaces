module

public import GeneratedFoundations.Arithmetic.NativeModes

/-!
# Ordered reduced expressions over the native arithmetic signature

This module retains the ordered binary expression assembled from the two
distinguished native modes and the two native operations.  Only the unit laws
and the absorbing-zero laws are removed.  Associativity, commutativity and
distributivity are deliberately not imposed at the expression level.

The construction has no datum beyond the already generated arithmetic
signature.  Its universal property quantifies over comparison targets; those
targets are not fields of the minimal-change source datum.
-/

@[expose] public section

namespace GeneratedFoundations.Arithmetic.ReducedExpression

/-- Raw finite ordered terms in the two-operation arithmetic signature. -/
inductive RawExpr where
  | zero : RawExpr
  | one : RawExpr
  | add : RawExpr → RawExpr → RawExpr
  | mul : RawExpr → RawExpr → RawExpr
  deriving DecidableEq, Repr

namespace RawExpr

/-- Assemble an additive node, deleting only additive units. -/
def reducedAdd : RawExpr → RawExpr → RawExpr
  | zero, y => y
  | x, zero => x
  | x, y => add x y

/-- Assemble a multiplicative node, deleting units and absorbing zeros. -/
def reducedMul : RawExpr → RawExpr → RawExpr
  | zero, _ => zero
  | _, zero => zero
  | one, y => y
  | x, one => x
  | x, y => mul x y

@[simp] theorem reducedAdd_zero_right (x : RawExpr) : reducedAdd x zero = x := by
  cases x <;> rfl

@[simp] theorem reducedAdd_zero_left (x : RawExpr) : reducedAdd zero x = x := rfl

@[simp] theorem reducedMul_zero_right (x : RawExpr) : reducedMul x zero = zero := by
  cases x <;> rfl

@[simp] theorem reducedMul_zero_left (x : RawExpr) : reducedMul zero x = zero := rfl

@[simp] theorem reducedMul_one_right (x : RawExpr) : reducedMul x one = x := by
  cases x <;> rfl

@[simp] theorem reducedMul_one_left (x : RawExpr) : reducedMul one x = x := by
  cases x <;> rfl

/-- Recursive normalization by the displayed unit and absorbing-zero rules. -/
def normalize : RawExpr → RawExpr
  | zero => zero
  | one => one
  | add x y => reducedAdd (normalize x) (normalize y)
  | mul x y => reducedMul (normalize x) (normalize y)

theorem normalize_reducedAdd (x y : RawExpr) :
    normalize (reducedAdd x y) = reducedAdd (normalize x) (normalize y) := by
  cases x <;> cases y <;> try rfl
  all_goals exact (reducedAdd_zero_right _).symm

theorem normalize_reducedMul (x y : RawExpr) :
    normalize (reducedMul x y) = reducedMul (normalize x) (normalize y) := by
  cases x with
  | zero => cases y <;> rfl
  | one =>
      cases y with
      | zero => rfl
      | one => rfl
      | add a b => exact (reducedMul_one_left _).symm
      | mul a b => exact (reducedMul_one_left _).symm
  | add a b =>
      cases y with
      | zero => exact (reducedMul_zero_right _).symm
      | one => exact (reducedMul_one_right _).symm
      | add c d => rfl
      | mul c d => rfl
  | mul a b =>
      cases y with
      | zero => exact (reducedMul_zero_right _).symm
      | one => exact (reducedMul_one_right _).symm
      | add c d => rfl
      | mul c d => rfl

@[simp] theorem normalize_idempotent (e : RawExpr) :
    normalize (normalize e) = normalize e := by
  induction e with
  | zero => rfl
  | one => rfl
  | add x y hx hy =>
      simp only [normalize, normalize_reducedAdd, hx, hy]
  | mul x y hx hy =>
      simp only [normalize, normalize_reducedMul, hx, hy]

/-- A raw term contains no removable unit or absorbing-zero node. -/
def IsReduced (e : RawExpr) : Prop := normalize e = e

@[simp] theorem normalize_isReduced (e : RawExpr) : IsReduced (normalize e) :=
  normalize_idempotent e

theorem isReduced_iff (e : RawExpr) : IsReduced e ↔ normalize e = e := Iff.rfl

end RawExpr

/-- Canonical representatives of the unit/zero reduction congruence. -/
def Expr := {e : RawExpr // e.IsReduced}

namespace Expr

/-- The canonical reduced representative of a raw expression. -/
def ofRaw (e : RawExpr) : Expr := ⟨e.normalize, RawExpr.normalize_isReduced e⟩

@[simp] theorem val_ofRaw (e : RawExpr) : (ofRaw e).1 = e.normalize := rfl

@[simp] theorem ofRaw_val (e : Expr) : ofRaw e.1 = e := by
  apply Subtype.ext
  exact e.2

@[ext] theorem ext {e f : Expr} (h : e.1 = f.1) : e = f := Subtype.ext h

def zero : Expr := ⟨.zero, rfl⟩
def one : Expr := ⟨.one, rfl⟩

def add (e f : Expr) : Expr := ofRaw (.add e.1 f.1)
def mul (e f : Expr) : Expr := ofRaw (.mul e.1 f.1)

instance : Zero Expr := ⟨zero⟩
instance : One Expr := ⟨one⟩
instance : Add Expr := ⟨add⟩
instance : Mul Expr := ⟨mul⟩

@[simp] theorem ofRaw_zero : ofRaw .zero = 0 := rfl
@[simp] theorem ofRaw_one : ofRaw .one = 1 := rfl

@[simp] theorem ofRaw_add (e f : RawExpr) :
    ofRaw (.add e f) = ofRaw e + ofRaw f := by
  apply Subtype.ext
  change RawExpr.reducedAdd e.normalize f.normalize =
    RawExpr.reducedAdd (e.normalize.normalize) (f.normalize.normalize)
  simp

@[simp] theorem ofRaw_mul (e f : RawExpr) :
    ofRaw (.mul e f) = ofRaw e * ofRaw f := by
  apply Subtype.ext
  change RawExpr.reducedMul e.normalize f.normalize =
    RawExpr.reducedMul (e.normalize.normalize) (f.normalize.normalize)
  simp

@[simp] theorem add_zero (e : Expr) : e + 0 = e := by
  apply Subtype.ext
  change RawExpr.reducedAdd e.1.normalize .zero = e.1
  rw [RawExpr.reducedAdd_zero_right, e.2]

@[simp] theorem zero_add (e : Expr) : 0 + e = e := by
  apply Subtype.ext
  change RawExpr.reducedAdd .zero e.1.normalize = e.1
  rw [RawExpr.reducedAdd_zero_left, e.2]

@[simp] theorem mul_one (e : Expr) : e * 1 = e := by
  apply Subtype.ext
  change RawExpr.reducedMul e.1.normalize .one = e.1
  rw [RawExpr.reducedMul_one_right, e.2]

@[simp] theorem one_mul (e : Expr) : 1 * e = e := by
  apply Subtype.ext
  change RawExpr.reducedMul .one e.1.normalize = e.1
  rw [RawExpr.reducedMul_one_left, e.2]

@[simp] theorem mul_zero (e : Expr) : e * 0 = 0 := by
  apply Subtype.ext
  change RawExpr.reducedMul e.1.normalize .zero = .zero
  exact RawExpr.reducedMul_zero_right _

@[simp] theorem zero_mul (e : Expr) : 0 * e = 0 := by
  apply Subtype.ext
  change RawExpr.reducedMul .zero e.1.normalize = .zero
  exact RawExpr.reducedMul_zero_left _

end Expr

/-- A congruence on raw terms that contains exactly the displayed comparison
laws required of a target.  This structure is used only to state the leastness
theorem; it is not source data. -/
structure AdmissibleCongruence (R : RawExpr → RawExpr → Prop) : Prop where
  refl : ∀ e, R e e
  symm : ∀ {e f}, R e f → R f e
  trans : ∀ {e f g}, R e f → R f g → R e g
  add : ∀ {e e' f f'}, R e e' → R f f' → R (.add e f) (.add e' f')
  mul : ∀ {e e' f f'}, R e e' → R f f' → R (.mul e f) (.mul e' f')
  add_zero_right : ∀ e, R (.add e .zero) e
  add_zero_left : ∀ e, R (.add .zero e) e
  mul_one_right : ∀ e, R (.mul e .one) e
  mul_one_left : ∀ e, R (.mul .one e) e
  mul_zero_right : ∀ e, R (.mul e .zero) .zero
  mul_zero_left : ∀ e, R (.mul .zero e) .zero

/-- Equality of normal forms is the reduction congruence. -/
def ReductionEq (e f : RawExpr) : Prop := e.normalize = f.normalize

theorem reductionEq_equivalence : Equivalence ReductionEq := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · exact fun {_ _} h => h.symm
  · exact fun {_ _ _} h₁ h₂ => h₁.trans h₂

theorem reductionEq_admissible : AdmissibleCongruence ReductionEq := by
  refine ⟨fun _ => rfl, fun {_ _} h => h.symm,
    fun {_ _ _} h₁ h₂ => h₁.trans h₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e e' f f' he hf
    simp only [ReductionEq, RawExpr.normalize]
    rw [he, hf]
  · intro e e' f f' he hf
    simp only [ReductionEq, RawExpr.normalize]
    rw [he, hf]
  · intro e
    exact RawExpr.reducedAdd_zero_right _
  · intro e
    exact RawExpr.reducedAdd_zero_left _
  · intro e
    exact RawExpr.reducedMul_one_right _
  · intro e
    exact RawExpr.reducedMul_one_left _
  · intro e
    exact RawExpr.reducedMul_zero_right _
  · intro e
    exact RawExpr.reducedMul_zero_left _

private theorem reducedAdd_related {R : RawExpr → RawExpr → Prop}
    (hR : AdmissibleCongruence R) (x y : RawExpr) :
    R (.add x y) (RawExpr.reducedAdd x y) := by
  cases x <;> cases y <;>
    first | exact hR.add_zero_left _ | exact hR.add_zero_right _ | exact hR.refl _

private theorem reducedMul_related {R : RawExpr → RawExpr → Prop}
    (hR : AdmissibleCongruence R) (x y : RawExpr) :
    R (.mul x y) (RawExpr.reducedMul x y) := by
  cases x <;> cases y <;>
    first
    | exact hR.mul_zero_left _
    | exact hR.mul_zero_right _
    | exact hR.mul_one_left _
    | exact hR.mul_one_right _
    | exact hR.refl _

theorem related_normalize {R : RawExpr → RawExpr → Prop}
    (hR : AdmissibleCongruence R) (e : RawExpr) : R e e.normalize := by
  induction e with
  | zero => exact hR.refl _
  | one => exact hR.refl _
  | add x y hx hy =>
      exact hR.trans (hR.add hx hy) (reducedAdd_related hR x.normalize y.normalize)
  | mul x y hx hy =>
      exact hR.trans (hR.mul hx hy) (reducedMul_related hR x.normalize y.normalize)

/-- The normal-form congruence is the least congruence containing the six
unit and absorbing-zero laws. -/
theorem reductionEq_least {R : RawExpr → RawExpr → Prop}
    (hR : AdmissibleCongruence R) {e f : RawExpr} (hef : ReductionEq e f) : R e f := by
  exact hR.trans (related_normalize hR e)
    (hR.trans (hef ▸ hR.refl f.normalize) (hR.symm (related_normalize hR f)))

/-- Two reduced representatives in the reduction congruence are identical. -/
theorem reduced_unique {e f : RawExpr} (he : e.IsReduced) (hf : f.IsReduced)
    (hef : ReductionEq e f) : e = f := by
  rw [RawExpr.isReduced_iff] at he hf
  rw [ReductionEq, he, hf] at hef
  exact hef

/-- Structural normalization terminates at the unique reduced representative.
Together with `reductionEq_least`, this is the normalization/confluence
statement for the six displayed rules. -/
theorem normalForm_existsUnique (e : RawExpr) :
    ∃! f : RawExpr, f.IsReduced ∧ ReductionEq e f := by
  refine ⟨e.normalize, ⟨RawExpr.normalize_isReduced e, ?_⟩, ?_⟩
  · exact (RawExpr.normalize_idempotent e).symm
  · intro f hf
    apply reduced_unique hf.1 (RawExpr.normalize_isReduced e)
    show f.normalize = e.normalize.normalize
    rw [RawExpr.normalize_idempotent]
    exact hf.2.symm

/-- A comparison algebra for the universal property.  It contains only the
laws already removed by normalization. -/
structure Target (A : Type*) where
  zero : A
  one : A
  add : A → A → A
  mul : A → A → A
  add_zero_right : ∀ a, add a zero = a
  add_zero_left : ∀ a, add zero a = a
  mul_one_right : ∀ a, mul a one = a
  mul_one_left : ∀ a, mul one a = a
  mul_zero_right : ∀ a, mul a zero = zero
  mul_zero_left : ∀ a, mul zero a = zero

namespace Target

def interpretRaw {A : Type*} (T : Target A) : RawExpr → A
  | .zero => T.zero
  | .one => T.one
  | .add e f => T.add (interpretRaw T e) (interpretRaw T f)
  | .mul e f => T.mul (interpretRaw T e) (interpretRaw T f)

private theorem interpret_reducedAdd {A : Type*} (T : Target A) (e f : RawExpr) :
    interpretRaw T (RawExpr.reducedAdd e f) = T.add (interpretRaw T e) (interpretRaw T f) := by
  cases e <;> cases f <;>
    simp [RawExpr.reducedAdd, interpretRaw, T.add_zero_left, T.add_zero_right]

private theorem interpret_reducedMul {A : Type*} (T : Target A) (e f : RawExpr) :
    interpretRaw T (RawExpr.reducedMul e f) = T.mul (interpretRaw T e) (interpretRaw T f) := by
  cases e <;> cases f <;>
    simp [RawExpr.reducedMul, interpretRaw, T.mul_one_left, T.mul_one_right,
      T.mul_zero_left, T.mul_zero_right]

theorem interpret_normalize {A : Type*} (T : Target A) (e : RawExpr) :
    interpretRaw T e.normalize = interpretRaw T e := by
  induction e with
  | zero => rfl
  | one => rfl
  | add e f he hf =>
      simp only [RawExpr.normalize, interpret_reducedAdd, interpretRaw, he, hf]
  | mul e f he hf =>
      simp only [RawExpr.normalize, interpret_reducedMul, interpretRaw, he, hf]

def interpret {A : Type*} (T : Target A) (e : Expr) : A := interpretRaw T e.1

structure Hom {A : Type*} (T : Target A) where
  toFun : Expr → A
  map_zero : toFun 0 = T.zero
  map_one : toFun 1 = T.one
  map_add : ∀ e f, toFun (e + f) = T.add (toFun e) (toFun f)
  map_mul : ∀ e f, toFun (e * f) = T.mul (toFun e) (toFun f)

instance {A : Type*} {T : Target A} : CoeFun (Hom T) (fun _ => Expr → A) :=
  ⟨Hom.toFun⟩

@[ext] theorem Hom.ext {A : Type*} {T : Target A} {F G : Hom T}
    (h : ∀ e, F e = G e) : F = G := by
  cases F with
  | mk f f0 f1 fa fm =>
      cases G with
      | mk g g0 g1 ga gm =>
          have hfg : f = g := funext h
          subst g
          rfl

def canonicalHom {A : Type*} (T : Target A) : Hom T where
  toFun := interpret T
  map_zero := rfl
  map_one := rfl
  map_add e f := by
    change interpretRaw T (RawExpr.normalize (.add e.1 f.1)) = _
    rw [interpret_normalize]
    rfl
  map_mul e f := by
    change interpretRaw T (RawExpr.normalize (.mul e.1 f.1)) = _
    rw [interpret_normalize]
    rfl

private theorem hom_ofRaw {A : Type*} {T : Target A} (F : Hom T) (e : RawExpr) :
    F (Expr.ofRaw e) = interpretRaw T e := by
  induction e with
  | zero => exact F.map_zero
  | one => exact F.map_one
  | add e f he hf =>
      rw [Expr.ofRaw_add, F.map_add, he, hf]
      rfl
  | mul e f he hf =>
      rw [Expr.ofRaw_mul, F.map_mul, he, hf]
      rfl

theorem hom_apply {A : Type*} {T : Target A} (F : Hom T) (e : Expr) :
    F e = interpret T e := by
  rw [← Expr.ofRaw_val e, hom_ofRaw]
  exact (interpret_normalize T e.1).symm

theorem hom_unique {A : Type*} {T : Target A} (F G : Hom T) : F = G := by
  apply Hom.ext
  intro e
  exact (hom_apply F e).trans (hom_apply G e).symm

/-- The reduced expression object is initial in the exact ordered two-operation
comparison class used in the manuscript. -/
theorem hom_existsUnique {A : Type*} (T : Target A) :
    ∃! F : Hom T, ∀ e, F e = interpret T e := by
  refine ⟨canonicalHom T, fun _ => rfl, ?_⟩
  intro F _
  exact hom_unique F (canonicalHom T)

end Target

end GeneratedFoundations.Arithmetic.ReducedExpression
