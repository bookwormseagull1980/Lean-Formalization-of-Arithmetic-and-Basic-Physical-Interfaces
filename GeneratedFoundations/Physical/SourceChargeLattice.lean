module

public import GeneratedFoundations.Physical.SourceMinimalRepresentation
public import GeneratedFoundations.Physical.SourcePhaseLift
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Divisibility.Units
public import Mathlib.Data.Int.GCD
public import Mathlib.LinearAlgebra.Trace

/-!
# Primitive characters of the retained source decomposition

The relative character is classified among all integer scalar weights on
the actual three-dimensional and one-dimensional source summands. Its
trace and its action on the joint source carrier are computed before an
orientation is chosen. Primitivity means that every common integer divisor
is a unit, rather than that a particular weight has already been set to one.

For the residual charge, the right generator has weights `1/2` and `-1/2`
and is zero on the left copy. Integral competitors are classified from
these data and pointwise fixation of either scalar vacuum weight. The
integer lattice calculation is separate from the identification of its
weight spaces with a full chiral Hilbert realization. In particular, no
arbitrary orthonormal spin basis is identified with the source number
eigenbasis here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup

namespace GeneratedFoundations.Physical.SourceChargeLattice

open SourceJointResponse SourceMinimalRepresentation

def PrimitivePair (a b : ℤ) : Prop :=
  ∀ d : ℤ, d ∣ a → d ∣ b → IsUnit d

theorem primitivePair_iff_gcd_eq_one (a b : ℤ) :
    PrimitivePair a b ↔ Int.gcd a b = 1 := by
  constructor
  · intro h
    have hu := h (Int.gcd a b) (Int.gcd_dvd_left a b) (Int.gcd_dvd_right a b)
    simpa using Int.isUnit_iff_natAbs_eq.mp hu
  · intro h d hda hdb
    apply isUnit_iff_dvd_one.mpr
    have hd := Int.dvd_coe_gcd hda hdb
    simpa [h] using hd

def TraceFree (a b : ℤ) : Prop := 3 * a + b = 0

/-- Integer relative characters act on the actual source summands. -/
def relativeColour (a b : ℤ) : SplitColour :=
  ((a : ℂ) • (1 : Module.End ℂ W), (b : ℂ) • (1 : Module.End ℂ L))

theorem relativeColour_trace (a b : ℤ) :
    LinearMap.trace ℂ W (relativeColour a b).1 +
        LinearMap.trace ℂ L (relativeColour a b).2 = ((3 * a + b : ℤ) : ℂ) := by
  simp [relativeColour, map_smul, LinearMap.trace_one, W, L,
    hilbertCarrier_finrank]
  ring

theorem relativeColour_trace_zero_iff (a b : ℤ) :
    LinearMap.trace ℂ W (relativeColour a b).1 +
        LinearMap.trace ℂ L (relativeColour a b).2 = 0 ↔ TraceFree a b := by
  rw [relativeColour_trace]
  unfold TraceFree
  norm_cast

theorem primitive_traceFree_iff (a b : ℤ) :
    PrimitivePair a b ∧ TraceFree a b ↔
      (a = 1 ∧ b = -3) ∨ (a = -1 ∧ b = 3) := by
  constructor
  · rintro ⟨hp, ht⟩
    have hb : b = a * (-3) := by dsimp [TraceFree] at ht; linarith
    have ha : IsUnit a := hp a dvd_rfl ⟨-3, hb⟩
    rcases Int.isUnit_iff.mp ha with ha | ha
    · left
      exact ⟨ha, by rw [ha] at hb; simpa using hb⟩
    · right
      exact ⟨ha, by rw [ha] at hb; norm_num at hb ⊢; exact hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨?_, by norm_num [TraceFree]⟩
      intro d hd _
      exact isUnit_of_dvd_one hd
    · refine ⟨?_, by norm_num [TraceFree]⟩
      intro d hd _
      exact isUnit_of_dvd_unit hd (Int.isUnit_iff.mpr (Or.inr rfl))

theorem oriented_relative_unique {a b : ℤ} (hp : PrimitivePair a b)
    (ht : TraceFree a b) (ha : 0 < a) : a = 1 ∧ b = -3 := by
  rcases (primitive_traceFree_iff a b).mp ⟨hp, ht⟩ with h | h
  · exact h
  · exfalso
    linarith [h.1]

theorem oriented_relative_existsUnique :
    ∃! p : ℤ × ℤ, PrimitivePair p.1 p.2 ∧ TraceFree p.1 p.2 ∧ 0 < p.1 := by
  refine ⟨(1, -3), ?_, ?_⟩
  · exact ⟨((primitive_traceFree_iff 1 (-3)).mpr (Or.inl ⟨rfl, rfl⟩)).1,
      by norm_num [TraceFree], by norm_num⟩
  · intro p hp
    exact Prod.ext (oriented_relative_unique hp.1 hp.2.1 hp.2.2).1
      (oriented_relative_unique hp.1 hp.2.1 hp.2.2).2

def relativeSource (a b : ℤ) : Module.End ℂ SourceCarrier :=
  sourceCarrierRepresentation (colourResponse (relativeColour a b))

theorem relativeSource_apply (a b : ℤ) (x : SourceCarrier) :
    WithLp.ofLp (relativeSource a b x) =
      ((a : ℂ) • (WithLp.ofLp x).1, (b : ℂ) • (WithLp.ofLp x).2) := by
  rw [relativeSource, sourceCarrierRepresentation_apply]
  simp [colourResponse, relativeColour, TensorProduct.map_smul_left]

def primitiveRelativeSource : Module.End ℂ SourceCarrier := relativeSource 1 (-3)

theorem relativeSource_oriented_unique {a b : ℤ} (hp : PrimitivePair a b)
    (ht : TraceFree a b) (ha : 0 < a) :
    relativeSource a b = primitiveRelativeSource := by
  obtain ⟨rfl, rfl⟩ := oriented_relative_unique hp ht ha
  rfl

inductive ColourSector where
  | coloured
  | scalar
  deriving DecidableEq

instance : Fintype ColourSector where
  elems := {.coloured, .scalar}
  complete x := by cases x <;> simp

inductive SpinSector where
  | left
  | upper
  | lower
  deriving DecidableEq

instance : Fintype SpinSector where
  elems := {.left, .upper, .lower}
  complete x := by cases x <;> simp

abbrev Sector := ColourSector × SpinSector

def relativeWeight (a b : ℤ) : ColourSector → ℤ
  | .coloured => a
  | .scalar => b

def baseRelativeWeight : ColourSector → ℤ := relativeWeight 1 (-3)

/-- Twice the inherited right-spin generator, with zero left action. -/
def twiceRightWeight : SpinSector → ℤ
  | .left => 0
  | .upper => 1
  | .lower => -1

/-- Here `r = α/2` in the standard right-spin normalization. -/
def chargeWeight (r β : ℤ) (p : Sector) : ℤ :=
  r * twiceRightWeight p.2 + β * baseRelativeWeight p.1

def generatedCharge : Sector → ℤ := chargeWeight 3 1

def PrimitiveWeights (w : Sector → ℤ) : Prop :=
  ∀ d : ℤ, (∀ p, d ∣ w p) → IsUnit d

def PrimitiveCharge (r β : ℤ) : Prop := PrimitiveWeights (chargeWeight r β)

@[simp] theorem charge_coloured_left (r β : ℤ) :
    chargeWeight r β (.coloured, .left) = β := by
  simp [chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]

@[simp] theorem charge_scalar_left (r β : ℤ) :
    chargeWeight r β (.scalar, .left) = -3 * β := by
  simp [chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]
  ring

@[simp] theorem charge_coloured_upper (r β : ℤ) :
    chargeWeight r β (.coloured, .upper) = r + β := by
  simp [chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]

@[simp] theorem charge_coloured_lower (r β : ℤ) :
    chargeWeight r β (.coloured, .lower) = -r + β := by
  simp [chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]

@[simp] theorem charge_scalar_upper (r β : ℤ) :
    chargeWeight r β (.scalar, .upper) = r - 3 * β := by
  simp [chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]
  ring

@[simp] theorem charge_scalar_lower (r β : ℤ) :
    chargeWeight r β (.scalar, .lower) = -r - 3 * β := by
  simp [chargeWeight, twiceRightWeight, baseRelativeWeight, relativeWeight]
  ring

theorem chargeWeight_scaled (r β : ℤ) (p : Sector) :
    chargeWeight (r * β) β p = β * chargeWeight r 1 p := by
  dsimp [chargeWeight]
  ring

theorem primitiveCharge_iff_primitivePair (r β : ℤ) :
    PrimitiveCharge r β ↔ PrimitivePair r β := by
  constructor
  · intro hp d hdr hdβ
    apply hp d
    intro p
    exact dvd_add (dvd_mul_of_dvd_left hdr _) (dvd_mul_of_dvd_left hdβ _)
  · intro hp d hd
    have hβ : d ∣ β := by simpa using hd (.coloured, .left)
    have hu : d ∣ r + β := by simpa using hd (.coloured, .upper)
    have hr : d ∣ r := by simpa using dvd_sub hu hβ
    exact hp d hr hβ

theorem primitiveCharge_iff_gcd_eq_one (r β : ℤ) :
    PrimitiveCharge r β ↔ Int.gcd r β = 1 :=
  (primitiveCharge_iff_primitivePair r β).trans (primitivePair_iff_gcd_eq_one r β)

theorem primitiveCharge_of_unit (r : ℤ) {β : ℤ} (hβ : IsUnit β) :
    PrimitiveCharge r β := by
  intro d hd
  exact isUnit_of_dvd_unit (by simpa using hd (.coloured, .left)) hβ

theorem primitiveCharge_fixedUpper_iff (r β : ℤ)
    (hv : chargeWeight r β (.scalar, .upper) = 0) :
    PrimitiveCharge r β ↔ IsUnit β := by
  have hr : r = 3 * β := by rw [charge_scalar_upper] at hv; linarith
  constructor
  · intro hp
    apply hp β
    intro p
    rw [hr, chargeWeight_scaled]
    exact dvd_mul_right _ _
  · exact primitiveCharge_of_unit r

theorem primitiveCharge_fixedLower_iff (r β : ℤ)
    (hv : chargeWeight r β (.scalar, .lower) = 0) :
    PrimitiveCharge r β ↔ IsUnit β := by
  have hr : r = (-3) * β := by rw [charge_scalar_lower] at hv; linarith
  constructor
  · intro hp
    apply hp β
    intro p
    rw [hr, chargeWeight_scaled]
    exact dvd_mul_right _ _
  · exact primitiveCharge_of_unit r

theorem oriented_fixedUpper_unique {r β : ℤ} (hp : PrimitiveCharge r β)
    (hv : chargeWeight r β (.scalar, .upper) = 0) (hβ : 0 < β) :
    r = 3 ∧ β = 1 := by
  have hu := (primitiveCharge_fixedUpper_iff r β hv).mp hp
  rcases Int.isUnit_iff.mp hu with hb | hb
  · refine ⟨?_, hb⟩
    rw [charge_scalar_upper] at hv
    linarith
  · exfalso
    linarith

theorem oriented_fixedUpper_existsUnique :
    ∃! p : ℤ × ℤ, PrimitiveCharge p.1 p.2 ∧
      chargeWeight p.1 p.2 (.scalar, .upper) = 0 ∧ 0 < p.2 := by
  refine ⟨(3, 1), ?_, ?_⟩
  · exact ⟨primitiveCharge_of_unit 3 isUnit_one, by norm_num, by norm_num⟩
  · intro p hp
    exact Prod.ext (oriented_fixedUpper_unique hp.1 hp.2.1 hp.2.2).1
      (oriented_fixedUpper_unique hp.1 hp.2.1 hp.2.2).2

/-- The two vacuum lines differ by the right Weyl reflection. The remaining
common sign is the orientation of the primitive circle. -/
theorem primitive_vacuum_classification (r β : ℤ) :
    PrimitiveCharge r β ∧
        (chargeWeight r β (.scalar, .upper) = 0 ∨
          chargeWeight r β (.scalar, .lower) = 0) ↔
      (β = 1 ∨ β = -1) ∧ (r = 3 * β ∨ r = -3 * β) := by
  constructor
  · rintro ⟨hp, hv | hv⟩
    · refine ⟨Int.isUnit_iff.mp ((primitiveCharge_fixedUpper_iff r β hv).mp hp),
        Or.inl ?_⟩
      rw [charge_scalar_upper] at hv
      linarith
    · refine ⟨Int.isUnit_iff.mp ((primitiveCharge_fixedLower_iff r β hv).mp hp),
        Or.inr ?_⟩
      rw [charge_scalar_lower] at hv
      linarith
  · rintro ⟨hβ, hr | hr⟩
    · refine ⟨primitiveCharge_of_unit r (Int.isUnit_iff.mpr hβ), Or.inl ?_⟩
      rw [charge_scalar_upper, hr]
      ring
    · refine ⟨primitiveCharge_of_unit r (Int.isUnit_iff.mpr hβ), Or.inr ?_⟩
      rw [charge_scalar_lower, hr]
      ring

def weyl : SpinSector → SpinSector
  | .left => .left
  | .upper => .lower
  | .lower => .upper

theorem chargeWeight_weyl (r β : ℤ) (c : ColourSector) (s : SpinSector) :
    chargeWeight (-r) β (c, s) = chargeWeight r β (c, weyl s) := by
  cases s <;> simp [chargeWeight, twiceRightWeight, weyl]

theorem chargeWeight_orientation (r β : ℤ) (p : Sector) :
    chargeWeight (-r) (-β) p = -chargeWeight r β p := by
  dsimp [chargeWeight]
  ring

theorem generatedCharge_primitive : PrimitiveWeights generatedCharge :=
  primitiveCharge_of_unit 3 isUnit_one

theorem generatedCharge_values :
    generatedCharge (.coloured, .left) = 1 ∧
    generatedCharge (.scalar, .left) = -3 ∧
    generatedCharge (.coloured, .upper) = 4 ∧
    generatedCharge (.coloured, .lower) = -2 ∧
    generatedCharge (.scalar, .upper) = 0 ∧
    generatedCharge (.scalar, .lower) = -6 := by
  norm_num [generatedCharge, chargeWeight, twiceRightWeight,
    baseRelativeWeight, relativeWeight]

theorem generatedCharge_zero_iff (p : Sector) :
    generatedCharge p = 0 ↔ p = (.scalar, .upper) := by
  rcases p with ⟨c, s⟩
  cases c <;> cases s <;>
    norm_num [generatedCharge, chargeWeight, twiceRightWeight,
      baseRelativeWeight, relativeWeight]

def hypercharge (p : Sector) : ℚ := (generatedCharge p : ℚ) / 6

theorem hypercharge_from_generators (p : Sector) :
    hypercharge p = (twiceRightWeight p.2 : ℚ) / 2 +
      (baseRelativeWeight p.1 : ℚ) / 6 := by
  dsimp [hypercharge, generatedCharge, chargeWeight]
  push_cast
  ring

def realCharge (α β : ℝ) (p : Sector) : ℝ :=
  (α / 2) * (twiceRightWeight p.2 : ℝ) + β * (baseRelativeWeight p.1 : ℝ)

def IntegralRealization (α β : ℝ) (w : Sector → ℤ) : Prop :=
  ∀ p, (w p : ℝ) = realCharge α β p

/-- Integrality of all matter weights forces the integer parameters; it is
not assumed as a separate restriction on real competing generators. -/
theorem integral_parameters {α β : ℝ} {w : Sector → ℤ}
    (hw : IntegralRealization α β w) :
    ∃ r b : ℤ, α = 2 * (r : ℝ) ∧ β = (b : ℝ) := by
  have hl := hw (.coloured, .left)
  have hu := hw (.coloured, .upper)
  norm_num [realCharge, twiceRightWeight, baseRelativeWeight, relativeWeight] at hl hu
  refine ⟨w (.coloured, .upper) - w (.coloured, .left), w (.coloured, .left), ?_,
    hl.symm⟩
  push_cast
  linarith

theorem integralRealization_eq {r b : ℤ} {w : Sector → ℤ}
    (hw : IntegralRealization (2 * (r : ℝ)) (b : ℝ) w) : w = chargeWeight r b := by
  funext p
  apply Int.cast_injective (α := ℝ)
  have h := hw p
  dsimp [realCharge, chargeWeight] at h ⊢
  push_cast
  nlinarith [h]

theorem oriented_real_vacuum_unique {α β : ℝ} {w : Sector → ℤ}
    (hw : IntegralRealization α β w) (hp : PrimitiveWeights w)
    (hv : realCharge α β (.scalar, .upper) = 0) (hβ : 0 < β) :
    α = 6 ∧ β = 1 ∧ w = generatedCharge := by
  obtain ⟨r, b, hα, hb⟩ := integral_parameters hw
  have hw' : IntegralRealization (2 * (r : ℝ)) (b : ℝ) w := by
    simpa only [hα, hb] using hw
  have he := integralRealization_eq hw'
  have hp' : PrimitiveCharge r b := by simpa only [PrimitiveCharge, he] using hp
  have hv' : chargeWeight r b (.scalar, .upper) = 0 := by
    have h := hw (.scalar, .upper)
    rw [hv, he] at h
    exact_mod_cast h
  have hb' : 0 < b := by exact_mod_cast (show 0 < (b : ℝ) by rwa [hb] at hβ)
  obtain ⟨hr, hb1⟩ := oriented_fixedUpper_unique hp' hv' hb'
  refine ⟨?_, ?_, ?_⟩
  · norm_num [hr] at hα ⊢
    exact hα
  · norm_num [hb1] at hb ⊢
    exact hb
  · simpa only [hr, hb1, generatedCharge] using he

/-- This is the scalar character of an arbitrary relative weight, prior
to the primitive trace-free classification. -/
def relativeRightScalar (b : ℤ) (g : SU2) (z : Circle) : Mat2 :=
  (z : ℂ) ^ b • (g : Mat2)

theorem relativeRightScalar_oriented_unique {a b : ℤ}
    (hp : PrimitivePair a b) (ht : TraceFree a b) (ha : 0 < a)
    (g : SU2) (z : Circle) :
    relativeRightScalar b g z = SourcePhaseLift.rightScalarMatrix g z := by
  obtain ⟨_, rfl⟩ := oriented_relative_unique hp ht ha
  simp [relativeRightScalar, SourcePhaseLift.rightScalarMatrix, zpow_neg]

/-- The primitive lattice supplies the weight minus three used in the
independent source-vacuum stabilizer calculation. -/
theorem relativeRightScalar_fixesVacuum_iff {a b : ℤ}
    (hp : PrimitivePair a b) (ht : TraceFree a b) (ha : 0 < a)
    (g : SU2) (z : Circle) :
    (relativeRightScalar b g z).mulVec ![1, 0] = ![1, 0] ↔
      g = SourcePhaseLift.stabilizerFrame z := by
  rw [relativeRightScalar_oriented_unique hp ht ha]
  exact SourcePhaseLift.fixesVacuum_iff g z

theorem relativeRightScalar_lift_spec {a b : ℤ}
    (hp : PrimitivePair a b) (ht : TraceFree a b) (ha : 0 < a) (t : ℝ) :
    relativeRightScalar b (SourcePhaseLift.lift t).1 (SourcePhaseLift.lift t).2 =
      Operations.SourceNumberFlow.numberFlowMatrix t := by
  rw [relativeRightScalar_oriented_unique hp ht ha]
  exact SourcePhaseLift.lift_spec t

/-- The two scalar weights of a residual integer generator. -/
def scalarChargeMatrix (r β : ℤ) (z : Circle) : Mat2 :=
  Matrix.diagonal ![(z : ℂ) ^ chargeWeight r β (.scalar, .upper),
    (z : ℂ) ^ chargeWeight r β (.scalar, .lower)]

theorem scalarChargeMatrix_generated (z : Circle) :
    scalarChargeMatrix 3 1 z =
      SourcePhaseLift.rightScalarMatrix (SourcePhaseLift.stabilizerFrame z) z := by
  rw [SourcePhaseLift.rightScalarMatrix_stabilizerFrame]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarChargeMatrix, zpow_neg]

end GeneratedFoundations.Physical.SourceChargeLattice
