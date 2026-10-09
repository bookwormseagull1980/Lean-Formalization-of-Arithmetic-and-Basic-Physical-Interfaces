module

public import GeneratedFoundations.Arithmetic.TypedSourceModes
public import GeneratedFoundations.Arithmetic.GeneratedFactorTransport

/-!
# Recursion and factorization on the original generated carrier

The elements remain continuous endomorphisms of the original, oriented
change group. Their existing coordinate equivalence preserves the complete
maps and both native operations. It transports the internal recursion and
factorization proofs, without using natural-number factorization.

The canonical comparison between two scales and orientations is characterized
among all functions by preservation of zero and successor. Prime profiles
are finite functions on these actual endomorphisms, and their reindexing is
part of the same comparison.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Source
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Arithmetic.TypedSourceModes
open GeneratedFoundations.Spectral
open scoped NNReal

namespace GeneratedFoundations.Arithmetic.TypedArithmetic

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
variable (L : ℝ) [Fact (0 < L)] (o : OrientationOnCarrier d)

@[simp] theorem toGenerated_successor (u : Mode d h L o) :
    toGenerated d h L o (successor d h L o u) =
      GeneratedModes.successor L (toGenerated d h L o u) := by
  simp only [successor, GeneratedModes.successor, toGenerated_add, toGenerated_one]

theorem fromGenerated_successor (u : GeneratedModes.SourceMode L) :
    fromGenerated d h L o (GeneratedModes.successor L u) =
      successor d h L o (fromGenerated d h L o u) := by
  apply toGenerated_injective d h L o
  simp only [toGenerated_fromGenerated, toGenerated_successor]

theorem successor_injective : Function.Injective (successor d h L o) := by
  intro u v huv
  apply toGenerated_injective d h L o
  apply GeneratedModes.successor_injective L
  simpa only [toGenerated_successor] using congrArg (toGenerated d h L o) huv

theorem successor_ne_zero (u : Mode d h L o) : successor d h L o u ≠ 0 := by
  intro hu
  apply GeneratedModes.successor_ne_zero L (toGenerated d h L o u)
  simpa only [toGenerated_successor, toGenerated_zero] using
    congrArg (toGenerated d h L o) hu

theorem successor_induction {P : Mode d h L o → Prop} (hzero : P 0)
    (hstep : ∀ u, P u → P (successor d h L o u)) : ∀ u, P u := by
  have hz : fromGenerated d h L o (0 : GeneratedModes.SourceMode L) = 0 :=
    (generatedEquiv d h L o).symm.map_zero
  have hp : ∀ v : GeneratedModes.SourceMode L, P (fromGenerated d h L o v) :=
    GeneratedModes.successor_induction L (by simpa only [hz] using hzero)
      (fun v hv => by
        simpa only [fromGenerated_successor] using
          (hstep (fromGenerated d h L o v) hv))
  intro u
  simpa only [fromGenerated_toGenerated] using hp (toGenerated d h L o u)

def fold {X : Type*} (xzero : X) (step : X → X) (u : Mode d h L o) : X :=
  GeneratedModes.fold L xzero step (toGenerated d h L o u)

@[simp] theorem fold_zero {X : Type*} (xzero : X) (step : X → X) :
    fold d h L o xzero step 0 = xzero := by
  simp only [fold, toGenerated_zero, GeneratedModes.fold_zero]

@[simp] theorem fold_successor {X : Type*} (xzero : X) (step : X → X)
    (u : Mode d h L o) :
    fold d h L o xzero step (successor d h L o u) =
      step (fold d h L o xzero step u) := by
  simp only [fold, toGenerated_successor, GeneratedModes.fold_successor]

/-- The recursion function is unique on the actual original-group maps. -/
theorem recursion_existsUnique {X : Type*} (xzero : X) (step : X → X) :
    ∃! f : Mode d h L o → X, f 0 = xzero ∧
      ∀ u, f (successor d h L o u) = step (f u) := by
  refine ⟨fold d h L o xzero step,
    ⟨fold_zero d h L o _ _, fold_successor d h L o _ _⟩, ?_⟩
  intro f hf
  funext u
  apply successor_induction d h L o (P := fun v => f v = fold d h L o xzero step v) ?_ ?_ u
  · simpa only [fold_zero] using hf.1
  · intro v hv
    rw [hf.2, fold_successor, hv]

instance : LinearOrder (Mode d h L o) :=
  LinearOrder.lift' (toGenerated d h L o) (toGenerated_injective d h L o)

theorem le_iff_coordinate (u v : Mode d h L o) :
    u ≤ v ↔ toGenerated d h L o u ≤ toGenerated d h L o v := Iff.rfl

def CompositionIrreducible (p : Mode d h L o) : Prop :=
  p ≠ 0 ∧ p ≠ 1 ∧ ∀ a b : Mode d h L o, p = a * b → a = 1 ∨ b = 1

theorem irreducible_iff_coordinate (p : Mode d h L o) :
    CompositionIrreducible d h L o p ↔
      GeneratedModes.SourceIrreducible L (toGenerated d h L o p) := by
  let e := generatedEquiv d h L o
  constructor
  · rintro ⟨hp0, hp1, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      exact hp0 (e.injective (hz.trans e.map_zero.symm))
    · intro hz
      exact hp1 (e.injective (hz.trans e.map_one.symm))
    · intro a b hab
      have hh : p = e.symm a * e.symm b := by
        apply e.injective
        simpa only [map_mul, RingEquiv.apply_symm_apply] using
          (show e p = a * b from hab)
      rcases hp (e.symm a) (e.symm b) hh with ha | hb
      · left
        simpa only [RingEquiv.apply_symm_apply, map_one] using congrArg e ha
      · right
        simpa only [RingEquiv.apply_symm_apply, map_one] using congrArg e hb
  · rintro ⟨hp0, hp1, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      apply hp0
      simp only [hz, toGenerated_zero]
    · intro hz
      apply hp1
      simp only [hz, toGenerated_one]
    · intro a b hab
      have hh : e p = e a * e b := by rw [hab, map_mul]
      rcases hp (e a) (e b) hh with ha | hb
      · exact Or.inl (e.injective (ha.trans e.map_one.symm))
      · exact Or.inr (e.injective (hb.trans e.map_one.symm))

def IsPrimeProfile (x : Mode d h L o) (f : Mode d h L o →₀ ℕ) : Prop :=
  (∀ p ∈ f.support, CompositionIrreducible d h L o p) ∧
    f.prod (fun p n => p ^ n) = x

def coordinateProfile : (Mode d h L o →₀ ℕ) ≃+ (GeneratedModes.SourceMode L →₀ ℕ) :=
  Finsupp.domCongr (generatedEquiv d h L o).toEquiv

@[simp] theorem coordinateProfile_apply (f : Mode d h L o →₀ ℕ) (p : Mode d h L o) :
    coordinateProfile d h L o f (toGenerated d h L o p) = f p := by
  change f ((generatedEquiv d h L o).symm ((generatedEquiv d h L o) p)) = f p
  rw [RingEquiv.symm_apply_apply]

theorem coordinateProfile_prod (f : Mode d h L o →₀ ℕ) :
    (coordinateProfile d h L o f).prod (fun p n => p ^ n) =
      toGenerated d h L o (f.prod (fun p n => p ^ n)) := by
  change (Finsupp.equivMapDomain (generatedEquiv d h L o).toEquiv f).prod
    (fun p n => p ^ n) = (generatedEquiv d h L o) (f.prod (fun p n => p ^ n))
  rw [Finsupp.prod_equivMapDomain, map_finsuppProd]
  apply Finsupp.prod_congr
  intro p hp
  exact (map_pow (generatedEquiv d h L o) p (f p)).symm

theorem primeProfile_coordinate_iff (x : Mode d h L o) (f : Mode d h L o →₀ ℕ) :
    IsPrimeProfile d h L o x f ↔
      GeneratedFactorTransport.IsPrimeProfile L (toGenerated d h L o x)
        (coordinateProfile d h L o f) := by
  have hsupport (p : Mode d h L o) :
      toGenerated d h L o p ∈ (coordinateProfile d h L o f).support ↔ p ∈ f.support := by
    simp only [Finsupp.mem_support_iff, coordinateProfile_apply]
  constructor
  · rintro ⟨hf, hx⟩
    refine ⟨?_, ?_⟩
    · intro q hq
      obtain ⟨p, rfl⟩ := (generatedEquiv d h L o).surjective q
      exact (irreducible_iff_coordinate d h L o p).mp (hf p ((hsupport p).mp hq))
    · rw [coordinateProfile_prod, hx]
  · rintro ⟨hf, hx⟩
    refine ⟨fun p hp => (irreducible_iff_coordinate d h L o p).mpr
      (hf _ ((hsupport p).mpr hp)), ?_⟩
    apply toGenerated_injective d h L o
    rwa [← coordinateProfile_prod]

/-- The profile is indexed by original endomorphisms, with internal composition
as multiplication. Its uniqueness comes from the internal Euclidean proof. -/
theorem primeProfile_existsUnique {x : Mode d h L o} (hx : x ≠ 0) :
    ∃! f : Mode d h L o →₀ ℕ, IsPrimeProfile d h L o x f := by
  have hx' : toGenerated d h L o x ≠ 0 := by
    intro hz
    apply hx
    apply toGenerated_injective d h L o
    simpa only [toGenerated_zero] using hz
  obtain ⟨g, hg, huniq⟩ := GeneratedModes.exponentProfile_existsUnique L hx'
  refine ⟨(coordinateProfile d h L o).symm g, ?_, ?_⟩
  · apply (primeProfile_coordinate_iff d h L o x _).mpr
    simpa only [AddEquiv.apply_symm_apply, GeneratedFactorTransport.IsPrimeProfile] using hg
  · intro f hf
    apply (coordinateProfile d h L o).injective
    rw [AddEquiv.apply_symm_apply]
    exact huniq _ ((primeProfile_coordinate_iff d h L o x f).mp hf)

def primeProfile (x : Mode d h L o) (hx : x ≠ 0) : Mode d h L o →₀ ℕ :=
  Classical.choose (primeProfile_existsUnique d h L o hx).exists

theorem primeProfile_spec (x : Mode d h L o) (hx : x ≠ 0) :
    IsPrimeProfile d h L o x (primeProfile d h L o x hx) :=
  Classical.choose_spec (primeProfile_existsUnique d h L o hx).exists

theorem irreducibles_infinite :
    Set.Infinite {p : Mode d h L o | CompositionIrreducible d h L o p} := by
  refine Set.infinite_of_injOn_mapsTo (f := fromGenerated d h L o) ?_ ?_
    (GeneratedFactorTransport.sourceIrreducibles_infinite L)
  · intro p hp q hq hpq
    simpa only [toGenerated_fromGenerated] using congrArg (toGenerated d h L o) hpq
  · intro p hp
    apply (irreducible_iff_coordinate d h L o _).mpr
    change GeneratedModes.SourceIrreducible L p at hp
    simpa only [toGenerated_fromGenerated] using hp

variable (M : ℝ) [Fact (0 < M)] (p : OrientationOnCarrier d)

def transport : Mode d h L o ≃+* Mode d h M p :=
  ((generatedEquiv d h L o).trans (GeneratedModes.transport L M)).trans
    (generatedEquiv d h M p).symm

@[simp] theorem toGenerated_transport (u : Mode d h L o) :
    toGenerated d h M p (transport d h L o M p u) =
      GeneratedModes.transport L M (toGenerated d h L o u) :=
  (generatedEquiv d h M p).apply_symm_apply _

theorem transport_coordinateEnd (u : Mode d h L o) :
    coordinateEnd d h p (transport d h L o M p u).val = coordinateEnd d h o u.val := by
  exact congrArg Subtype.val (toGenerated_transport d h L o M p u)

theorem transport_representative (u : Mode d h L o) :
    NeumannScaleTransport.unitary L M
        (GeneratedModes.representative L (toGenerated d h L o u) : ComplexIntervalL2 0 L) =
      (GeneratedModes.representative M
        (toGenerated d h M p (transport d h L o M p u)) : ComplexIntervalL2 0 M) := by
  rw [toGenerated_transport]
  exact GeneratedModes.transport_representative L M _

theorem transport_normalized_energy (u : Mode d h L o) :
    NeumannSpectralProjections.energy M
        (GeneratedModes.component M (toGenerated d h M p (transport d h L o M p u))) /
        NeumannScaleTransport.energyUnit M =
      NeumannSpectralProjections.energy L
        (GeneratedModes.component L (toGenerated d h L o u)) /
        NeumannScaleTransport.energyUnit L := by
  rw [toGenerated_transport]
  exact GeneratedModes.transport_normalized_energy L M _

theorem transport_response (u : Mode d h L o) (t : ℝ≥0) :
    NeumannSpectralProjections.response M
        (GeneratedModes.component M (toGenerated d h M p (transport d h L o M p u)))
        (NeumannScaleTransport.changeParameter L M t) =
      NeumannSpectralProjections.response L
        (GeneratedModes.component L (toGenerated d h L o u)) t := by
  rw [toGenerated_transport]
  exact GeneratedModes.transport_response L M _ t

@[simp] theorem transport_successor (u : Mode d h L o) :
    transport d h L o M p (successor d h L o u) =
      successor d h M p (transport d h L o M p u) := by
  simp only [successor, map_add, map_one]

theorem transport_existsUnique :
    ∃! f : Mode d h L o → Mode d h M p,
      f 0 = 0 ∧ ∀ u, f (successor d h L o u) = successor d h M p (f u) := by
  refine ⟨transport d h L o M p, ⟨map_zero _, transport_successor d h L o M p⟩, ?_⟩
  intro f hf
  funext u
  apply successor_induction d h L o (P := fun v => f v = transport d h L o M p v) ?_ ?_ u
  · simpa only [map_zero] using hf.1
  · intro v hv
    rw [hf.2, transport_successor, hv]

theorem transport_le_iff (u v : Mode d h L o) :
    transport d h L o M p u ≤ transport d h L o M p v ↔ u ≤ v := by
  rw [le_iff_coordinate, le_iff_coordinate, toGenerated_transport, toGenerated_transport]
  exact GeneratedModes.transport_le_iff L M _ _

theorem transport_irreducible_iff (u : Mode d h L o) :
    CompositionIrreducible d h M p (transport d h L o M p u) ↔
      CompositionIrreducible d h L o u := by
  rw [irreducible_iff_coordinate, irreducible_iff_coordinate, toGenerated_transport]
  exact GeneratedModes.transport_irreducible_iff L M _

def transportProfile : (Mode d h L o →₀ ℕ) ≃+ (Mode d h M p →₀ ℕ) :=
  Finsupp.domCongr (transport d h L o M p).toEquiv

@[simp] theorem transportProfile_apply (f : Mode d h L o →₀ ℕ) (u : Mode d h L o) :
    transportProfile d h L o M p f (transport d h L o M p u) = f u := by
  change f ((transport d h L o M p).symm ((transport d h L o M p) u)) = f u
  rw [RingEquiv.symm_apply_apply]

theorem transportProfile_prod (f : Mode d h L o →₀ ℕ) :
    (transportProfile d h L o M p f).prod (fun u n => u ^ n) =
      transport d h L o M p (f.prod (fun u n => u ^ n)) := by
  change (Finsupp.equivMapDomain (transport d h L o M p).toEquiv f).prod
    (fun u n => u ^ n) = _
  rw [Finsupp.prod_equivMapDomain, map_finsuppProd]
  apply Finsupp.prod_congr
  intro u hu
  exact (map_pow (transport d h L o M p) u (f u)).symm

theorem transportProfile_spec {x : Mode d h L o} {f : Mode d h L o →₀ ℕ}
    (hf : IsPrimeProfile d h L o x f) :
    IsPrimeProfile d h M p (transport d h L o M p x) (transportProfile d h L o M p f) := by
  constructor
  · intro q hq
    obtain ⟨u, rfl⟩ := (transport d h L o M p).surjective q
    apply (transport_irreducible_iff d h L o M p u).mpr
    apply hf.1 u
    simpa only [Finsupp.mem_support_iff, transportProfile_apply] using hq
  · rw [transportProfile_prod, hf.2]

theorem transport_ne_zero {x : Mode d h L o} (hx : x ≠ 0) :
    transport d h L o M p x ≠ 0 := by
  intro hz
  apply hx
  apply (transport d h L o M p).injective
  simpa only [map_zero] using hz

theorem primeProfile_transport (x : Mode d h L o) (hx : x ≠ 0) :
    primeProfile d h M p (transport d h L o M p x) (transport_ne_zero d h L o M p hx) =
      transportProfile d h L o M p (primeProfile d h L o x hx) :=
  (primeProfile_existsUnique d h M p (transport_ne_zero d h L o M p hx)).unique
    (primeProfile_spec d h M p _ _) (transportProfile_spec d h L o M p
      (primeProfile_spec d h L o x hx))

/-- At reversed orientation the canonical arithmetic comparison is the
already constructed conjugation of the original source and target carriers. -/
theorem transport_reversal (u : Mode d h L o) :
    transport d h L o L (-o) u = reversalEquiv d h L o u := by
  apply toGenerated_injective d h L (-o)
  rw [toGenerated_transport]
  change GeneratedModes.transport L L (toGenerated d h L o u) =
    toGenerated d h L (-o) (reverseMode d h L o u)
  rw [toGenerated_reverseMode]
  rfl

end GeneratedFoundations.Arithmetic.TypedArithmetic
