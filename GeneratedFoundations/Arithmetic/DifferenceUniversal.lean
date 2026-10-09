module

public import GeneratedFoundations.Arithmetic.DifferenceRing

/-!
# Universal properties of the native difference ring

Every additive map from the native modes to an additive commutative group
extends uniquely across the actual quotient of mode pairs. Its value on
`[a,b]` is `f a - f b`. When the target is a commutative ring and the original
map is a semiring homomorphism, the same extension is a ring homomorphism.
No comparison with the standard integers is used in either construction.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.NativeModes.Differences

section Additive

variable {A : Type*} [AddCommGroup A]

theorem additive_difference_respects_relation (f : Mode →+ A)
    {p q : Mode × Mode} (h : Related p q) :
    f p.1 - f p.2 = f q.1 - f q.2 := by
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [map_add] using congrArg f h

/-- The group-completion extension, defined on the actual pair quotient. -/
def liftAdditive (f : Mode →+ A) : Difference →+ A where
  toFun := Quotient.lift (fun p : Mode × Mode => f p.1 - f p.2)
    (fun _ _ h => additive_difference_respects_relation f h)
  map_zero' := by
    change f 0 - f 0 = 0
    exact sub_self _
  map_add' x y := by
    induction x, y using Quotient.inductionOn₂ with | _ p q =>
      change f (p.1 + q.1) - f (p.2 + q.2) =
        (f p.1 - f p.2) + (f q.1 - f q.2)
      simp only [map_add, sub_eq_add_neg, neg_add_rev]
      ac_rfl

@[simp] theorem liftAdditive_pair (f : Mode →+ A) (a b : Mode) :
    liftAdditive f (pair a b) = f a - f b := rfl

@[simp] theorem liftAdditive_ofMode (f : Mode →+ A) (a : Mode) :
    liftAdditive f (ofMode a) = f a := by
  change f a - f 0 = f a
  simp

@[simp] theorem liftAdditive_comp_ofMode (f : Mode →+ A) :
    (liftAdditive f).comp ofMode.toAddMonoidHom = f := by
  ext a
  exact liftAdditive_ofMode f a

/-- An additive map out of the completion is determined by its values on modes. -/
theorem difference_addHom_ext {F G : Difference →+ A}
    (h : ∀ a : Mode, F (ofMode a) = G (ofMode a)) : F = G := by
  ext x
  apply difference_induction (P := fun x => F x = G x) ?_ x
  intro a b
  simp only [map_sub, h]

theorem liftAdditive_unique (f : Mode →+ A) (F : Difference →+ A)
    (hF : F.comp ofMode.toAddMonoidHom = f) : F = liftAdditive f := by
  apply difference_addHom_ext
  intro a
  exact (DFunLike.congr_fun hF a).trans (liftAdditive_ofMode f a).symm

/-- The universal property of additive Grothendieck completion. -/
theorem additive_extension_existsUnique (f : Mode →+ A) :
    ∃! F : Difference →+ A, F.comp ofMode.toAddMonoidHom = f :=
  ⟨liftAdditive f, liftAdditive_comp_ofMode f, fun F hF => liftAdditive_unique f F hF⟩

end Additive

section Ring

variable {R : Type*} [CommRing R]

/-- The same pair formula extends a semiring map as a ring homomorphism. -/
def liftRing (f : Mode →+* R) : Difference →+* R where
  __ := liftAdditive f.toAddMonoidHom
  map_one' := by
    change f 1 - f 0 = 1
    simp
  map_mul' x y := by
    induction x, y using Quotient.inductionOn₂ with | _ p q =>
      change f (p.1 * q.1 + p.2 * q.2) - f (p.1 * q.2 + p.2 * q.1) =
        (f p.1 - f p.2) * (f q.1 - f q.2)
      simp only [map_add, map_mul]
      ring

@[simp] theorem liftRing_pair (f : Mode →+* R) (a b : Mode) :
    liftRing f (pair a b) = f a - f b := rfl

@[simp] theorem liftRing_ofMode (f : Mode →+* R) (a : Mode) :
    liftRing f (ofMode a) = f a :=
  liftAdditive_ofMode f.toAddMonoidHom a

@[simp] theorem liftRing_comp_ofMode (f : Mode →+* R) :
    (liftRing f).comp ofMode = f := by
  ext a
  exact liftRing_ofMode f a

theorem difference_ringHom_ext {F G : Difference →+* R}
    (h : ∀ a : Mode, F (ofMode a) = G (ofMode a)) : F = G := by
  ext x
  exact DFunLike.congr_fun (difference_addHom_ext
    (F := F.toAddMonoidHom) (G := G.toAddMonoidHom) h) x

theorem liftRing_unique (f : Mode →+* R) (F : Difference →+* R)
    (hF : F.comp ofMode = f) : F = liftRing f := by
  apply difference_ringHom_ext
  intro a
  exact (DFunLike.congr_fun hF a).trans (liftRing_ofMode f a).symm

/-- The quotient is the universal ring receiving the native mode semiring. -/
theorem ring_extension_existsUnique (f : Mode →+* R) :
    ∃! F : Difference →+* R, F.comp ofMode = f :=
  ⟨liftRing f, liftRing_comp_ofMode f, fun F hF => liftRing_unique f F hF⟩

end Ring

end GeneratedFoundations.Arithmetic.NativeModes.Differences
