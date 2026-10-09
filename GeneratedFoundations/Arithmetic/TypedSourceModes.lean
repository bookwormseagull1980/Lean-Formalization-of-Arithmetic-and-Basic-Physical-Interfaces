module

public import GeneratedFoundations.Arithmetic.GeneratedModes
public import GeneratedFoundations.Source.GeneratedSpectralCircle
public import Mathlib.Algebra.Group.TransferInstance

/-!
# Typed orientation reversal of the original source modes

The two carriers below are copies of the original change group, indexed by
their actual carrier orientations. Their coordinates are the phase characters
already derived from the original oriented flow. The comparison between them
forgets and reinstates this orientation tag; its coordinate reversal is a
theorem about that flow, not a new choice of a circle or a source family.

A mode is an actual continuous endomorphism of its typed carrier. Membership
requires that its coordinate conjugate be the oriented lift of an eigenvector
of the original Neumann operator. Pointwise multiplication and composition
are defined on these endomorphisms. Reversal preserves the entire coordinate
map, hence the very same source witnesses. No negative-power family with
untyped composition is used. The negative Hardy pullback is a separate
analytic comparison.
-/

@[expose] public section

noncomputable section

open scoped Topology Manifold ContDiff
open GeneratedFoundations.Source GeneratedFoundations.Spectral
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Source.GeneratedSpectralCircle

namespace GeneratedFoundations.Arithmetic.TypedSourceModes

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)

local instance : IsTopologicalGroup d.Changes :=
  topologicalGroup_of_lieGroup (𝓡 d.groupDimension) ∞

/-- An orientation-indexed copy of the actual original group, not a new circle. -/
structure Carrier (h : MinimalCarrier.IsMinimal d) (o : OrientationOnCarrier d) where
  change : d.Changes

/-- The orientation tag changes no underlying source point. -/
def carrierEquiv (o : OrientationOnCarrier d) : Carrier d h o ≃ d.Changes where
  toFun := Carrier.change
  invFun := Carrier.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance (o : OrientationOnCarrier d) : Group (Carrier d h o) :=
  (carrierEquiv d h o).group

instance (o : OrientationOnCarrier d) : TopologicalSpace (Carrier d h o) :=
  TopologicalSpace.induced (Carrier.change : Carrier d h o → d.Changes) inferInstance

theorem continuous_change (o : OrientationOnCarrier d) :
    Continuous (Carrier.change : Carrier d h o → d.Changes) := continuous_induced_dom

/-- This equivalence retains the actual original topology and multiplication. -/
def forget (o : OrientationOnCarrier d) : Carrier d h o ≃ₜ* d.Changes where
  toEquiv := carrierEquiv d h o
  map_mul' _ _ := rfl
  continuous_toFun := continuous_change d h o
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance (o : OrientationOnCarrier d) : IsTopologicalGroup (Carrier d h o) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : Carrier d h o × Carrier d h o => p.1.change * p.2.change)
    exact ((continuous_change d h o).comp continuous_fst).mul
      ((continuous_change d h o).comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x : Carrier d h o => x.change⁻¹)
    exact (continuous_change d h o).inv

/-- The coordinate is fixed by the original oriented integral curve. -/
def coordinate (o : OrientationOnCarrier d) : Carrier d h o ≃ₜ* Circle :=
  (forget d h o).trans (phaseCharacter d h o)

@[simp] theorem coordinate_apply (o : OrientationOnCarrier d) (x : Carrier d h o) :
    coordinate d h o x = phaseCharacter d h o x.change := rfl

theorem carrier_mul_comm (o : OrientationOnCarrier d) (x y : Carrier d h o) :
    x * y = y * x := by
  apply (coordinate d h o).injective
  simp only [map_mul, mul_comm]

/-- Commutativity is proved from the original classification, without changing
any group operations. The minimality proof is explicit at use sites. -/
instance carrierCommGroup (o : OrientationOnCarrier d) : CommGroup (Carrier d h o) where
  toGroup := inferInstance
  mul_comm := carrier_mul_comm d h o

/-- The same source change, now with the reversed orientation as target type. -/
def reversal (o : OrientationOnCarrier d) : Carrier d h o ≃ₜ* Carrier d h (-o) :=
  (forget d h o).trans (forget d h (-o)).symm

@[simp] theorem reversal_change (o : OrientationOnCarrier d) (x : Carrier d h o) :
    (reversal d h o x).change = x.change := rfl

/-- This is derived from `phaseCharacter_reverse` on the original group. -/
theorem coordinate_reversal (o : OrientationOnCarrier d) (x : Carrier d h o) :
    coordinate d h (-o) (reversal d h o x) = (coordinate d h o x)⁻¹ :=
  phaseCharacter_reverse d h o x.change

/-- The original integral curve on the typed carrier; no independent flow is chosen. -/
def typedFlow (o : OrientationOnCarrier d) (t : ℝ) : Carrier d h o :=
  (forget d h o).symm (orientedFlow d h o t)

@[simp] theorem forget_typedFlow (o : OrientationOnCarrier d) (t : ℝ) :
    forget d h o (typedFlow d h o t) = orientedFlow d h o t :=
  (forget d h o).apply_symm_apply _

theorem coordinate_typedFlow (o : OrientationOnCarrier d) (t : ℝ) :
    coordinate d h o (typedFlow d h o t) = Circle.exp t := by
  change phaseCharacter d h o (orientedFlow d h o t) = Circle.exp t
  exact phaseCharacter_flow d h o t

/-- Reversing orientation preserves the source curve and reverses its parameter. -/
theorem reversal_typedFlow (o : OrientationOnCarrier d) (t : ℝ) :
    reversal d h o (typedFlow d h o t) = typedFlow d h (-o) (-t) := by
  apply (forget d h (-o)).injective
  change orientedFlow d h o t = orientedFlow d h (-o) (-t)
  rw [orientedFlow_reverse, neg_neg]

section Conjugation

variable {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Conjugation of actual continuous endomorphisms, with source and target types. -/
def conjugate (e : G ≃ₜ* H) (u : G →ₜ* G) : H →ₜ* H :=
  (e : G →ₜ* H).comp (u.comp (e.symm : H →ₜ* G))

@[simp] theorem conjugate_apply (e : G ≃ₜ* H) (u : G →ₜ* G) (x : H) :
    conjugate e u x = e (u (e.symm x)) := rfl

@[simp] theorem conjugate_symm_conjugate (e : G ≃ₜ* H) (u : G →ₜ* G) :
    conjugate e.symm (conjugate e u) = u := by
  ext x
  simp only [conjugate_apply, ContinuousMulEquiv.symm_symm,
    ContinuousMulEquiv.symm_apply_apply]

@[simp] theorem conjugate_conjugate_symm (e : G ≃ₜ* H) (u : H →ₜ* H) :
    conjugate e (conjugate e.symm u) = u := by
  ext x
  simp only [conjugate_apply, ContinuousMulEquiv.symm_symm,
    ContinuousMulEquiv.apply_symm_apply]

@[simp] theorem conjugate_one (e : G ≃ₜ* H) : conjugate e 1 = 1 := by
  ext x
  simp [conjugate_apply]

@[simp] theorem conjugate_id (e : G ≃ₜ* H) :
    conjugate e (ContinuousMonoidHom.id G) = ContinuousMonoidHom.id H := by
  ext x
  simp [conjugate_apply]

theorem conjugate_comp (e : G ≃ₜ* H) (u v : G →ₜ* G) :
    conjugate e (u.comp v) = (conjugate e u).comp (conjugate e v) := by
  ext x
  simp [conjugate_apply]

end Conjugation

section CommutativeConjugation

variable {G H : Type*} [CommGroup G] [CommGroup H]
  [TopologicalSpace G] [TopologicalSpace H] [ContinuousMul G] [ContinuousMul H]

theorem conjugate_mul (e : G ≃ₜ* H) (u v : G →ₜ* G) :
    conjugate e (u * v) = conjugate e u * conjugate e v := by
  ext x
  simp [conjugate_apply, map_mul]

end CommutativeConjugation

/-- The actual coordinate endomorphism whose original spectral source is tested. -/
def coordinateEnd (o : OrientationOnCarrier d) (u : Carrier d h o →ₜ* Carrier d h o) :
    Circle →ₜ* Circle := conjugate (coordinate d h o) u

def fromCoordinateEnd (o : OrientationOnCarrier d) (u : Circle →ₜ* Circle) :
    Carrier d h o →ₜ* Carrier d h o := conjugate (coordinate d h o).symm u

/-- Forgetting the type tag recovers the earlier endomorphism on the original
change group, with exactly the same phase character in both slots. -/
theorem fromCoordinateEnd_change (o : OrientationOnCarrier d)
    (u : Circle →ₜ* Circle) (x : Carrier d h o) :
    (fromCoordinateEnd d h o u x).change =
      transportEndomorphism d h o u x.change := rfl

@[simp] theorem coordinateEnd_fromCoordinateEnd (o : OrientationOnCarrier d)
    (u : Circle →ₜ* Circle) :
    coordinateEnd d h o (fromCoordinateEnd d h o u) = u :=
  conjugate_conjugate_symm _ u

@[simp] theorem fromCoordinateEnd_coordinateEnd (o : OrientationOnCarrier d)
    (u : Carrier d h o →ₜ* Carrier d h o) :
    fromCoordinateEnd d h o (coordinateEnd d h o u) = u :=
  conjugate_symm_conjugate _ u

theorem coordinateEnd_injective (o : OrientationOnCarrier d) :
    Function.Injective (coordinateEnd d h o) := by
  intro u v huv
  simpa only [fromCoordinateEnd_coordinateEnd] using
    congrArg (fromCoordinateEnd d h o) huv

/-- A stronger statement than index preservation: the complete coordinate
endomorphism is unchanged, for every continuous group endomorphism. -/
theorem coordinateEnd_reversal (o : OrientationOnCarrier d)
    (u : Carrier d h o →ₜ* Carrier d h o) :
    coordinateEnd d h (-o) (conjugate (reversal d h o) u) = coordinateEnd d h o u := by
  ext z
  obtain ⟨y, rfl⟩ := (coordinate d h (-o)).surjective z
  obtain ⟨x, rfl⟩ := (reversal d h o).surjective y
  simp only [coordinateEnd, conjugate_apply, ContinuousMulEquiv.symm_apply_apply]
  rw [coordinate_reversal, coordinate_reversal]
  simp only [map_inv, ContinuousMulEquiv.symm_apply_apply]

theorem coordinateEnd_reversal_symm (o : OrientationOnCarrier d)
    (u : Carrier d h (-o) →ₜ* Carrier d h (-o)) :
    coordinateEnd d h o (conjugate (reversal d h o).symm u) =
      coordinateEnd d h (-o) u := by
  have heq := coordinateEnd_reversal d h o (conjugate (reversal d h o).symm u)
  rw [conjugate_conjugate_symm] at heq
  exact heq.symm

variable (L : ℝ) [hL : Fact (0 < L)]

/-- Membership retains the original interval eigenvector, endpoint phase,
normalization and almost-everywhere oriented-lift witness. -/
def Mode (o : OrientationOnCarrier d) :=
  {u : Carrier d h o →ₜ* Carrier d h o //
    OrientedLift.IsLiftedSourceMode L (coordinateEnd d h o u)}

instance (o : OrientationOnCarrier d) :
    CoeFun (Mode d h L o) (fun _ => Carrier d h o → Carrier d h o) := ⟨fun u => u.val⟩

@[ext] theorem ext {o : OrientationOnCarrier d} {u v : Mode d h L o}
    (heq : ∀ x, u x = v x) : u = v := by
  apply Subtype.ext
  exact DFunLike.ext _ _ heq

def toGenerated (o : OrientationOnCarrier d) (u : Mode d h L o) :
    GeneratedModes.SourceMode L := ⟨coordinateEnd d h o u.val, u.property⟩

def fromGenerated (o : OrientationOnCarrier d) (u : GeneratedModes.SourceMode L) :
    Mode d h L o :=
  ⟨fromCoordinateEnd d h o u.val, by
    simpa only [coordinateEnd_fromCoordinateEnd] using u.property⟩

@[simp] theorem toGenerated_val (o : OrientationOnCarrier d) (u : Mode d h L o) :
    (toGenerated d h L o u).val = coordinateEnd d h o u.val := rfl

/-- The typed source mode is the existing transported source endomorphism,
not just a map with the same arithmetic label. -/
theorem mode_change (o : OrientationOnCarrier d) (u : Mode d h L o)
    (x : Carrier d h o) :
    (u x).change = transportEndomorphism d h o (toGenerated d h L o u).val x.change := by
  have heq := congrArg (fun v : Carrier d h o →ₜ* Carrier d h o => (v x).change)
    (fromCoordinateEnd_coordinateEnd d h o u.val)
  exact heq.symm

@[simp] theorem toGenerated_fromGenerated (o : OrientationOnCarrier d)
    (u : GeneratedModes.SourceMode L) :
    toGenerated d h L o (fromGenerated d h L o u) = u := by
  apply Subtype.ext
  exact coordinateEnd_fromCoordinateEnd d h o u.val

@[simp] theorem fromGenerated_toGenerated (o : OrientationOnCarrier d)
    (u : Mode d h L o) : fromGenerated d h L o (toGenerated d h L o u) = u := by
  apply Subtype.ext
  exact fromCoordinateEnd_coordinateEnd d h o u.val

theorem toGenerated_injective (o : OrientationOnCarrier d) :
    Function.Injective (toGenerated d h L o) := by
  intro u v huv
  exact Subtype.ext (coordinateEnd_injective d h o (congrArg Subtype.val huv))

def zeroMode (o : OrientationOnCarrier d) : Mode d h L o :=
  ⟨1, by
    change OrientedLift.IsLiftedSourceMode L (conjugate (coordinate d h o) 1)
    rw [conjugate_one]
    exact (0 : GeneratedModes.SourceMode L).property⟩

def unitMode (o : OrientationOnCarrier d) : Mode d h L o :=
  ⟨ContinuousMonoidHom.id (Carrier d h o), by
    change OrientedLift.IsLiftedSourceMode L
      (conjugate (coordinate d h o) (ContinuousMonoidHom.id (Carrier d h o)))
    rw [conjugate_id]
    exact (1 : GeneratedModes.SourceMode L).property⟩

/-- Modulation is defined on the actual typed maps. -/
def modulate (o : OrientationOnCarrier d) (u v : Mode d h L o) : Mode d h L o :=
  ⟨u.val * v.val, by
    change OrientedLift.IsLiftedSourceMode L
      (conjugate (coordinate d h o) (u.val * v.val))
    rw [conjugate_mul]
    exact (toGenerated d h L o u + toGenerated d h L o v).property⟩

/-- Cascade is composition with matching source and target carrier. -/
def compose (o : OrientationOnCarrier d) (u v : Mode d h L o) : Mode d h L o :=
  ⟨u.val.comp v.val, by
    change OrientedLift.IsLiftedSourceMode L
      (conjugate (coordinate d h o) (u.val.comp v.val))
    rw [conjugate_comp]
    exact (toGenerated d h L o u * toGenerated d h L o v).property⟩

instance (o : OrientationOnCarrier d) : Zero (Mode d h L o) := ⟨zeroMode d h L o⟩
instance (o : OrientationOnCarrier d) : One (Mode d h L o) := ⟨unitMode d h L o⟩
instance (o : OrientationOnCarrier d) : Add (Mode d h L o) := ⟨modulate d h L o⟩
instance (o : OrientationOnCarrier d) : Mul (Mode d h L o) := ⟨compose d h L o⟩

@[simp] theorem zero_apply (o : OrientationOnCarrier d) (x : Carrier d h o) :
    (0 : Mode d h L o) x = 1 := rfl
@[simp] theorem one_apply (o : OrientationOnCarrier d) (x : Carrier d h o) :
    (1 : Mode d h L o) x = x := rfl
@[simp] theorem add_apply (o : OrientationOnCarrier d) (u v : Mode d h L o)
    (x : Carrier d h o) : (u + v) x = u x * v x := rfl
@[simp] theorem mul_apply (o : OrientationOnCarrier d) (u v : Mode d h L o)
    (x : Carrier d h o) : (u * v) x = u (v x) := rfl

@[simp] theorem toGenerated_zero (o : OrientationOnCarrier d) :
    toGenerated d h L o 0 = 0 := by
  apply Subtype.ext
  exact conjugate_one _

@[simp] theorem toGenerated_one (o : OrientationOnCarrier d) :
    toGenerated d h L o 1 = 1 := by
  apply Subtype.ext
  exact conjugate_id _

@[simp] theorem toGenerated_add (o : OrientationOnCarrier d) (u v : Mode d h L o) :
    toGenerated d h L o (u + v) = toGenerated d h L o u + toGenerated d h L o v := by
  apply Subtype.ext
  exact conjugate_mul _ u.val v.val

@[simp] theorem toGenerated_mul (o : OrientationOnCarrier d) (u v : Mode d h L o) :
    toGenerated d h L o (u * v) = toGenerated d h L o u * toGenerated d h L o v := by
  apply Subtype.ext
  exact conjugate_comp _ u.val v.val

instance (o : OrientationOnCarrier d) : CommSemiring (Mode d h L o) where
  add_assoc u v w := by ext x; simp only [add_apply, mul_assoc]
  zero_add u := by ext x; simp only [add_apply, zero_apply, one_mul]
  add_zero u := by ext x; simp only [add_apply, zero_apply, mul_one]
  add_comm u v := by ext x; simp only [add_apply, mul_comm]
  nsmul := nsmulRec
  mul_assoc u v w := by ext x; rfl
  one_mul u := by ext x; rfl
  mul_one u := by ext x; rfl
  npow := npowRec
  left_distrib u v w := by apply ext; intro x; exact u.val.map_mul (v x) (w x)
  right_distrib u v w := by ext x; rfl
  zero_mul u := by ext x; rfl
  mul_zero u := by apply ext; intro x; exact u.val.map_one
  mul_comm u v := by
    apply toGenerated_injective d h L o
    simp only [toGenerated_mul, mul_comm]
  natCast n := fromGenerated d h L o (n : GeneratedModes.SourceMode L)
  natCast_zero := by
    apply toGenerated_injective d h L o
    simp only [Nat.cast_zero, toGenerated_fromGenerated, toGenerated_zero]
  natCast_succ n := by
    apply toGenerated_injective d h L o
    simp only [Nat.cast_succ, toGenerated_fromGenerated, toGenerated_add, toGenerated_one]

/-- This comparison preserves the underlying coordinate map, not just its index. -/
def generatedEquiv (o : OrientationOnCarrier d) :
    Mode d h L o ≃+* GeneratedModes.SourceMode L where
  toFun := toGenerated d h L o
  invFun := fromGenerated d h L o
  left_inv := fromGenerated_toGenerated d h L o
  right_inv := toGenerated_fromGenerated d h L o
  map_add' := toGenerated_add d h L o
  map_mul' := toGenerated_mul d h L o

/-- The same existential source certificate applies after typed conjugation. -/
theorem source_membership_reversal (o : OrientationOnCarrier d)
    (u : Carrier d h o →ₜ* Carrier d h o) :
    OrientedLift.IsLiftedSourceMode L
      (coordinateEnd d h (-o) (conjugate (reversal d h o) u)) ↔
    OrientedLift.IsLiftedSourceMode L (coordinateEnd d h o u) := by
  rw [coordinateEnd_reversal]

def reverseMode (o : OrientationOnCarrier d) (u : Mode d h L o) : Mode d h L (-o) :=
  ⟨conjugate (reversal d h o) u.val, (source_membership_reversal d h L o u.val).mpr u.property⟩

/-- The target scalar observation, pulled back to the original carrier, is
inverted. This is a scalar-observation formula, not untyped negative composition. -/
theorem reverseMode_observation_pullback (o : OrientationOnCarrier d)
    (u : Mode d h L o) (x : Carrier d h o) :
    coordinate d h (-o) (reverseMode d h L o u (reversal d h o x)) =
      (coordinate d h o (u x))⁻¹ := by
  change coordinate d h (-o)
    (reversal d h o (u ((reversal d h o).symm (reversal d h o x)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, coordinate_reversal]

def unreverseMode (o : OrientationOnCarrier d) (u : Mode d h L (-o)) : Mode d h L o :=
  ⟨conjugate (reversal d h o).symm u.val, by
    simpa only [coordinateEnd_reversal_symm] using u.property⟩

@[simp] theorem toGenerated_reverseMode (o : OrientationOnCarrier d) (u : Mode d h L o) :
    toGenerated d h L (-o) (reverseMode d h L o u) = toGenerated d h L o u := by
  apply Subtype.ext
  exact coordinateEnd_reversal d h o u.val

@[simp] theorem toGenerated_unreverseMode (o : OrientationOnCarrier d)
    (u : Mode d h L (-o)) :
    toGenerated d h L o (unreverseMode d h L o u) = toGenerated d h L (-o) u := by
  apply Subtype.ext
  exact coordinateEnd_reversal_symm d h o u.val

/-- Both directions are actual carrier conjugations and keep the same source. -/
def reversalEquiv (o : OrientationOnCarrier d) : Mode d h L o ≃+* Mode d h L (-o) where
  toFun := reverseMode d h L o
  invFun := unreverseMode d h L o
  left_inv u := by apply Subtype.ext; exact conjugate_symm_conjugate _ u.val
  right_inv u := by apply Subtype.ext; exact conjugate_conjugate_symm _ u.val
  map_add' u v := by apply Subtype.ext; exact conjugate_mul _ u.val v.val
  map_mul' u v := by apply Subtype.ext; exact conjugate_comp _ u.val v.val

@[simp] theorem reversalEquiv_apply (o : OrientationOnCarrier d) (u : Mode d h L o)
    (x : Carrier d h (-o)) :
    reversalEquiv d h L o u x = reversal d h o (u ((reversal d h o).symm x)) := rfl

@[simp] theorem reversalEquiv_symm_apply (o : OrientationOnCarrier d)
    (u : Mode d h L (-o)) (x : Carrier d h o) :
    (reversalEquiv d h L o).symm u x = (reversal d h o).symm (u (reversal d h o x)) := rfl

@[simp] theorem reversalEquiv_zero (o : OrientationOnCarrier d) :
    reversalEquiv d h L o 0 = 0 := map_zero _

@[simp] theorem reversalEquiv_one (o : OrientationOnCarrier d) :
    reversalEquiv d h L o 1 = 1 := map_one _

def successor (o : OrientationOnCarrier d) (u : Mode d h L o) : Mode d h L o := u + 1

@[simp] theorem reversalEquiv_successor (o : OrientationOnCarrier d) (u : Mode d h L o) :
    reversalEquiv d h L o (successor d h L o u) =
      successor d h L (-o) (reversalEquiv d h L o u) := by
  simp only [successor, map_add, map_one]

/-- Every individual original interval witness has literally the same lift
equation after reversal; its eigenvalue, norm and endpoint phase are unchanged. -/
theorem source_lift_equation_reversal (o : OrientationOnCarrier d)
    (u : Carrier d h o →ₜ* Carrier d h o) (f : ComplexIntervalL2 0 L) :
    (OrientedLift.lift L f =ᵐ[AddCircle.haarAddCircle]
      OrientedLift.endomorphismRepresentative L
        (coordinateEnd d h (-o) (conjugate (reversal d h o) u))) ↔
    (OrientedLift.lift L f =ᵐ[AddCircle.haarAddCircle]
      OrientedLift.endomorphismRepresentative L (coordinateEnd d h o u)) := by
  rw [coordinateEnd_reversal]

/-- Even the canonical original interval representative is unchanged. -/
theorem representative_reversal (o : OrientationOnCarrier d) (u : Mode d h L o) :
    GeneratedModes.representative L
      (toGenerated d h L (-o) (reverseMode d h L o u)) =
    GeneratedModes.representative L (toGenerated d h L o u) := by
  rw [toGenerated_reverseMode]

end GeneratedFoundations.Arithmetic.TypedSourceModes
