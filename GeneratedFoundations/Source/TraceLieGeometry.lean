module

public import GeneratedFoundations.Source.RepresentationDifferential
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.Orientation

/-!
# The representation trace inner product and oriented unit generators

The underlying vectors are those of the original Lie algebra. A separate
wrapper carries the inner product induced by the actual representation
trace form, so the norm and atlas used in the original manifold derivatives
are unchanged. The identity on vectors is proved to be a continuous linear
equivalence between the two normed spaces.

The phase differential gives an isometry with the real line. Its positive
and negative unit vectors determine the two orientations of this line;
each orientation selects a unit generator with actual representation image
equal to one of the two quarter-turns. This construction does not assert an
exponential-map identity or change the original group's smooth structure.
-/

@[expose] public section

noncomputable section

open Function Module
open scoped Manifold ContDiff RealInnerProductSpace

namespace GeneratedFoundations.Source.TraceLieGeometry

open RepresentationDifferential

/-- The original Lie-algebra vectors, with their representation trace norm
kept separate from the norm of the original chart model. -/
structure TraceLieSpace (d : MinimalCarrier.OrthogonalChangeDatum)
    (h : MinimalCarrier.IsMinimal d) where
  tangent : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)

def underlyingEquiv : TraceLieSpace d h ≃
    GroupLieAlgebra (𝓡 d.groupDimension) d.Changes where
  toFun := TraceLieSpace.tangent
  invFun := TraceLieSpace.mk
  left_inv := by intro X; cases X; rfl
  right_inv := by intro X; rfl

instance instAddCommGroupTraceLieSpace : AddCommGroup (TraceLieSpace d h) :=
  (underlyingEquiv d h).addCommGroup

def underlyingAddEquiv : TraceLieSpace d h ≃+
    GroupLieAlgebra (𝓡 d.groupDimension) d.Changes :=
  (underlyingEquiv d h).addEquiv

instance instModuleTraceLieSpace : Module ℝ (TraceLieSpace d h) :=
  (underlyingAddEquiv d h).module ℝ

def underlyingLinearEquiv : TraceLieSpace d h ≃ₗ[ℝ]
    GroupLieAlgebra (𝓡 d.groupDimension) d.Changes :=
  (underlyingAddEquiv d h).linearEquiv ℝ

@[simp]
theorem underlyingLinearEquiv_apply (X : TraceLieSpace d h) :
    underlyingLinearEquiv d h X = X.tangent := rfl

instance instFiniteDimensionalTraceLieSpace : FiniteDimensional ℝ (TraceLieSpace d h) := by
  let : FiniteDimensional ℝ (GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :=
    (tangentSpaceCastModel (𝓡 d.groupDimension) (1 : d.Changes)).symm.toLinearEquiv.finiteDimensional
  exact (underlyingLinearEquiv d h).symm.finiteDimensional

/-- The inner product is defined by the actual trace formula. Coordinates
are used only to verify its inner-product axioms. -/
@[instance_reducible]
def traceCore : InnerProductSpace.Core ℝ (TraceLieSpace d h) := by
  refine
    { inner := fun X Y => traceMetric d X.tangent Y.tangent
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_
      definite := ?_ }
  all_goals obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  · intro X Y
    simpa using traceMetric_symmetric d e χ hχ haction Y.tangent X.tangent
  · intro X
    change 0 ≤ traceMetric d X.tangent X.tangent
    rw [traceMetric_eq_phase d e χ hχ haction]
    exact mul_self_nonneg _
  · intro X Y Z
    change traceMetric d (X.tangent + Y.tangent) Z.tangent = _
    simp only [traceMetric_eq_phase d e χ hχ haction, map_add, add_mul]
  · intro X Y r
    change traceMetric d (r • X.tangent) Y.tangent = r * _
    simp only [traceMetric_eq_phase d e χ hχ haction, map_smul, smul_eq_mul, mul_assoc]
  · intro X hz
    apply (underlyingEquiv d h).injective
    change X.tangent = 0
    by_contra hX
    exact (ne_of_gt (traceMetric_positive d e χ hχ haction X.tangent hX)) hz

instance instNormedAddCommGroupTraceLieSpace : NormedAddCommGroup (TraceLieSpace d h) :=
  (traceCore d h).toNormedAddCommGroup

instance instInnerProductSpaceTraceLieSpace : InnerProductSpace ℝ (TraceLieSpace d h) :=
  InnerProductSpace.ofCore _

@[simp]
theorem inner_eq_trace (X Y : TraceLieSpace d h) :
    ⟪X, Y⟫ = traceMetric d X.tangent Y.tangent := rfl

theorem norm_sq_eq_trace (X : TraceLieSpace d h) :
    ‖X‖ ^ 2 = traceMetric d X.tangent X.tangent := by
  simpa only [inner_eq_trace, RCLike.re_to_real] using
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) X)

/-- Equivalence of the two normed vector-space topologies does not install
a new norm on the original tangent-space type. -/
def underlyingContinuousLinearEquiv : TraceLieSpace d h ≃L[ℝ]
    GroupLieAlgebra (𝓡 d.groupDimension) d.Changes :=
  (underlyingLinearEquiv d h).toContinuousLinearEquiv

@[simp]
theorem underlyingContinuousLinearEquiv_apply (X : TraceLieSpace d h) :
    underlyingContinuousLinearEquiv d h X = X.tangent := rfl

variable (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle)
  (hχ : Continuous χ)

def phaseLinearEquiv : TraceLieSpace d h ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective
    ((phaseDifferential d χ).toLinearMap.comp (underlyingLinearEquiv d h).toLinearMap)
    ⟨(phaseDifferential_injective d χ hχ).comp (underlyingLinearEquiv d h).injective,
      (phaseDifferential_surjective d χ h hχ).comp (underlyingLinearEquiv d h).surjective⟩

@[simp]
theorem phaseLinearEquiv_apply (X : TraceLieSpace d h) :
    phaseLinearEquiv d h χ hχ X = phaseDifferential d χ X.tangent := rfl

def phaseIsometry
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ :=
  (phaseLinearEquiv d h χ hχ).isometryOfInner fun X Y => by
    change phaseDifferential d χ Y.tangent * phaseDifferential d χ X.tangent =
      traceMetric d X.tangent Y.tangent
    rw [traceMetric_eq_phase d e χ hχ haction, mul_comm]

@[simp]
theorem phaseIsometry_apply
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) (X : TraceLieSpace d h) :
    phaseIsometry d h e χ hχ haction X = phaseDifferential d χ X.tangent := rfl

include hχ in
theorem norm_eq_abs_phase
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) (X : TraceLieSpace d h) :
    ‖X‖ = |phaseDifferential d χ X.tangent| := by
  simpa only [Real.norm_eq_abs, phaseIsometry_apply] using
    (phaseIsometry d h e χ hχ haction).norm_map X |>.symm

/-- The unit generator positive in the coordinate supplied by the same
faithful character. -/
def positiveUnit : TraceLieSpace d h := (phaseLinearEquiv d h χ hχ).symm 1

@[simp]
theorem phase_positiveUnit :
    phaseDifferential d χ (positiveUnit d h χ hχ).tangent = 1 :=
  (phaseLinearEquiv d h χ hχ).apply_symm_apply 1

theorem positiveUnit_norm
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    ‖positiveUnit d h χ hχ‖ = 1 := by
  rw [norm_eq_abs_phase d h e χ hχ haction, phase_positiveUnit, abs_one]

theorem positiveUnit_image
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    endomorphism d (positiveUnit d h χ hχ).tangent = PlaneGenerator.generator e := by
  rw [endomorphism_eq_smul_generator d e χ hχ haction, phase_positiveUnit, one_smul]

theorem norm_one_iff
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) (X : TraceLieSpace d h) :
    ‖X‖ = 1 ↔ X = positiveUnit d h χ hχ ∨ X = -positiveUnit d h χ hχ := by
  constructor
  · intro hnorm
    have hs : phaseDifferential d χ X.tangent = 1 ∨
        phaseDifferential d χ X.tangent = -1 := by
      have ht := norm_sq_eq_trace d h X
      rw [hnorm, traceMetric_eq_phase d e χ hχ haction] at ht
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      nlinarith
    rcases hs with hs | hs
    · left
      apply (phaseLinearEquiv d h χ hχ).injective
      simpa only [phaseLinearEquiv_apply, phase_positiveUnit] using hs
    · right
      apply (phaseLinearEquiv d h χ hχ).injective
      simpa only [map_neg, phaseLinearEquiv_apply, phase_positiveUnit] using hs
  · rintro (rfl | rfl)
    · exact positiveUnit_norm d h e χ hχ haction
    · simpa only [norm_neg] using positiveUnit_norm d h e χ hχ haction

include hχ in
theorem positiveUnit_existsUnique
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) :
    ∃! X : TraceLieSpace d h, ‖X‖ = 1 ∧ 0 < phaseDifferential d χ X.tangent := by
  refine ⟨positiveUnit d h χ hχ,
    ⟨positiveUnit_norm d h e χ hχ haction, by rw [phase_positiveUnit]; norm_num⟩, ?_⟩
  intro X hX
  rcases (norm_one_iff d h e χ hχ haction X).mp hX.1 with hp | hn
  · exact hp
  · subst X
    have hz : phaseDifferential d χ (-positiveUnit d h χ hχ).tangent = -1 := by
      change phaseLinearEquiv d h χ hχ (-positiveUnit d h χ hχ) = -1
      rw [map_neg, phaseLinearEquiv_apply, phase_positiveUnit]
    rw [hz] at hX
    norm_num at hX

def phaseBasis : Basis (Fin 1) ℝ (TraceLieSpace d h) :=
  (Basis.singleton (Fin 1) ℝ).map (phaseLinearEquiv d h χ hχ).symm

@[simp]
theorem phaseBasis_apply (i : Fin 1) :
    phaseBasis d h χ hχ i = positiveUnit d h χ hχ := by
  simp [phaseBasis, positiveUnit]

def phaseOrientation : Orientation ℝ (TraceLieSpace d h) (Fin 1) :=
  (phaseBasis d h χ hχ).orientation

theorem orientation_cases (o : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    o = phaseOrientation d h χ hχ ∨ o = -phaseOrientation d h χ hχ :=
  (phaseBasis d h χ hχ).orientation_eq_or_eq_neg o

theorem phaseOrientation_ne_negative :
    phaseOrientation d h χ hχ ≠ -phaseOrientation d h χ hχ :=
  Module.Ray.ne_neg_self _

/-- The basis adjusted to the requested orientation retains unit length. -/
def orientedBasis (o : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    Basis (Fin 1) ℝ (TraceLieSpace d h) :=
  (phaseBasis d h χ hχ).adjustToOrientation o

def orientedUnit (o : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    TraceLieSpace d h := orientedBasis d h χ hχ o 0

theorem orientedBasis_orientation (o : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    (orientedBasis d h χ hχ o).orientation = o :=
  (phaseBasis d h χ hχ).orientation_adjustToOrientation o

theorem orientedUnit_eq_or_neg (o : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    orientedUnit d h χ hχ o = positiveUnit d h χ hχ ∨
      orientedUnit d h χ hχ o = -positiveUnit d h χ hχ := by
  simpa only [orientedUnit, orientedBasis, phaseBasis_apply] using
    (phaseBasis d h χ hχ).adjustToOrientation_apply_eq_or_eq_neg o 0

@[simp]
theorem orientedUnit_phaseOrientation :
    orientedUnit d h χ hχ (phaseOrientation d h χ hχ) = positiveUnit d h χ hχ := by
  classical
  simp [orientedUnit, orientedBasis, Basis.adjustToOrientation, phaseOrientation]

@[simp]
theorem orientedUnit_negativeOrientation :
    orientedUnit d h χ hχ (-phaseOrientation d h χ hχ) = -positiveUnit d h χ hχ := by
  classical
  have hne := phaseOrientation_ne_negative d h χ hχ
  change (phaseBasis d h χ hχ).orientation ≠ -phaseOrientation d h χ hχ at hne
  have hi : Classical.arbitrary (Fin 1) = 0 := Subsingleton.elim _ _
  simp only [orientedUnit, orientedBasis, Basis.adjustToOrientation]
  rw [ite_eq_right hne]
  simp [Basis.unitsSMul_apply, hi]

theorem orientedUnit_injective : Function.Injective (orientedUnit d h χ hχ) := by
  intro o₁ o₂ heq
  have hb : orientedBasis d h χ hχ o₁ = orientedBasis d h χ hχ o₂ := by
    apply DFunLike.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi, orientedUnit] using heq
  have ho := congrArg Basis.orientation hb
  simpa only [orientedBasis_orientation] using ho

theorem orientedUnit_reverse (o : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    orientedUnit d h χ hχ (-o) = -orientedUnit d h χ hχ o := by
  rcases orientation_cases d h χ hχ o with rfl | rfl
  · simp only [orientedUnit_negativeOrientation, orientedUnit_phaseOrientation]
  · calc
      orientedUnit d h χ hχ (- -phaseOrientation d h χ hχ) =
          orientedUnit d h χ hχ (phaseOrientation d h χ hχ) :=
        congrArg (orientedUnit d h χ hχ) (neg_neg (phaseOrientation d h χ hχ))
      _ = -orientedUnit d h χ hχ (-phaseOrientation d h χ hχ) := by
        rw [orientedUnit_phaseOrientation, orientedUnit_negativeOrientation, neg_neg]

theorem orientedUnit_norm
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (o : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    ‖orientedUnit d h χ hχ o‖ = 1 :=
  (norm_one_iff d h e χ hχ haction _).mpr (orientedUnit_eq_or_neg d h χ hχ o)

/-- The two orientations and the two trace-unit Lie vectors correspond
bijectively. No sign is preferred in the absence of an orientation choice. -/
theorem unit_orientation_existsUnique
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (X : TraceLieSpace d h) (hX : ‖X‖ = 1) :
    ∃! o : Orientation ℝ (TraceLieSpace d h) (Fin 1), orientedUnit d h χ hχ o = X := by
  rcases (norm_one_iff d h e χ hχ haction X).mp hX with rfl | rfl
  · refine ⟨phaseOrientation d h χ hχ, orientedUnit_phaseOrientation d h χ hχ, ?_⟩
    intro o ho
    apply orientedUnit_injective d h χ hχ
    simpa only [orientedUnit_phaseOrientation] using ho
  · refine ⟨-phaseOrientation d h χ hχ, orientedUnit_negativeOrientation d h χ hχ, ?_⟩
    intro o ho
    apply orientedUnit_injective d h χ hχ
    simpa only [orientedUnit_negativeOrientation] using ho

theorem orientedUnit_image
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v)
    (o : Orientation ℝ (TraceLieSpace d h) (Fin 1)) :
    endomorphism d (orientedUnit d h χ hχ o).tangent = PlaneGenerator.generator e ∨
      endomorphism d (orientedUnit d h χ hχ o).tangent = -PlaneGenerator.generator e := by
  apply unit_endomorphism_eq d e χ h hχ haction
  rw [← norm_sq_eq_trace d h, orientedUnit_norm d h e χ hχ haction]
  norm_num

end GeneratedFoundations.Source.TraceLieGeometry
