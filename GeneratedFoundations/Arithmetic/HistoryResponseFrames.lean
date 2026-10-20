module

public import GeneratedFoundations.Arithmetic.HistoryEffectiveResponseSpace

/-!
# Relative source frames of the complete arithmetic response

The effective source group acts on the already constructed Hilbert space of
all arithmetic matrix entries. Relative transitions below are induced by that
faithful unitary action. Their cocycle and uniqueness hold for every choice
of observation frames in this source image; they do not classify arbitrary
unitaries of the larger response space as source transformations.

The concrete total space has the actual arithmetic history--phase labels as
base. Its canonical frame is the identity. Other frame fields describe
coordinates of the same responses and are not extra data for the source.
The quotient action concerns responses; the sign-sensitive state carrier
remains the separate carrier constructed in HistoryEffectiveFrames.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryResponseFrames

open HistoryCliffordAction (HistoryLabel)
open HistoryElementaryConnector (Frame)
open HistoryEffectiveFrames (EffectiveFrame)
open HistoryEffectiveResponseSpace (ResponseSpace unitaryRepresentation)
open Geometry.EffectiveActionCocycle (CocycleOn)

abbrev Base (N : ℕ) := HistoryLabel N
abbrev Total (N : ℕ) := Base N × ResponseSpace N
abbrev FrameField (N : ℕ) := Base N → EffectiveFrame
abbrev Section (N : ℕ) := Base N → ResponseSpace N

/-- The base counts the actual history--phase labels of every admitted root. -/
theorem base_card (N : ℕ) :
    Fintype.card (Base N) =
      ∑ b : HistoryRootSectors.Roots N, HistoryRootSectors.size N b :=
  Fintype.card_sigma

def canonicalFrame (N : ℕ) : FrameField N := fun _ => 1

def projection (N : ℕ) (v : Total N) : HistoryLabel N := v.1

def fibreCoordinate (N : ℕ) (v : Total N) : ResponseSpace N := v.2

def globalCoordinates (N : ℕ) : Total N ≃ Base N × ResponseSpace N := Equiv.refl _

/-- Both coordinates are already generated; a map preserving them is fixed. -/
theorem globalCoordinates_unique (N : ℕ) (F : Total N → Base N × ResponseSpace N)
    (hbase : ∀ v, (F v).1 = projection N v)
    (hfibre : ∀ v, (F v).2 = fibreCoordinate N v) :
    F = globalCoordinates N := by
  funext v
  exact Prod.ext (hbase v) (hfibre v)

def changeFrame (N : ℕ) (f : FrameField N) (v : Total N) : Total N :=
  (v.1, unitaryRepresentation N (f v.1) v.2)

theorem changeFrame_projection (N : ℕ) (f : FrameField N) (v : Total N) :
    projection N (changeFrame N f v) = projection N v := rfl

theorem changeFrame_canonical (N : ℕ) (v : Total N) :
    changeFrame N (canonicalFrame N) v = v := by
  simp [changeFrame, canonicalFrame]

theorem changeFrame_inverse (N : ℕ) (f : FrameField N) (v : Total N) :
    changeFrame N (fun h => (f h)⁻¹) (changeFrame N f v) = v := by
  apply Prod.ext
  · rfl
  · change unitaryRepresentation N (f v.1)⁻¹
        (unitaryRepresentation N (f v.1) v.2) = v.2
    rw [map_inv]
    exact (unitaryRepresentation N (f v.1)).symm_apply_apply v.2

theorem changeFrame_norm (N : ℕ) (f : FrameField N) (v : Total N) :
    ‖(changeFrame N f v).2‖ = ‖v.2‖ :=
  (unitaryRepresentation N (f v.1)).norm_map _

section RelativeFrames

variable {ι X : Type*}

def unitaryFrames (N : ℕ) (f : ι → X → EffectiveFrame) (i : ι) (x : X) :
    ResponseSpace N ≃ₗᵢ[ℂ] ResponseSpace N := unitaryRepresentation N (f i x)

def relativeTransition (f : ι → X → EffectiveFrame) (i j : ι) (x : X) :
    EffectiveFrame := (f i x)⁻¹ * f j x

@[simp] theorem relativeTransition_self (f : ι → X → EffectiveFrame) (i : ι) (x : X) :
    relativeTransition f i i x = 1 := by simp [relativeTransition]

theorem relativeTransition_inverse (f : ι → X → EffectiveFrame) (i j : ι) (x : X) :
    (relativeTransition f i j x)⁻¹ = relativeTransition f j i x := by
  simp [relativeTransition]

theorem relativeTransition_comp (f : ι → X → EffectiveFrame) (i j k : ι) (x : X) :
    relativeTransition f i j x * relativeTransition f j k x = relativeTransition f i k x := by
  simp [relativeTransition, mul_assoc]

theorem relativeTransition_cocycle (f : ι → X → EffectiveFrame) (U : ι → Set X) :
    CocycleOn U (relativeTransition f) := by
  intro i j k x _ _ _
  exact relativeTransition_comp f i j k x

theorem relativeTransition_representation (N : ℕ) (f : ι → X → EffectiveFrame)
    (i j : ι) (x : X) :
    unitaryRepresentation N (relativeTransition f i j x) =
      (unitaryFrames N f i x)⁻¹ * unitaryFrames N f j x := by
  simp only [relativeTransition, unitaryFrames, map_mul, map_inv]

theorem relativeTransition_action (N : ℕ) (f : ι → X → EffectiveFrame)
    (i j : ι) (x : X) (v : ResponseSpace N) :
    unitaryFrames N f i x (unitaryRepresentation N (relativeTransition f i j x) v) =
      unitaryFrames N f j x v := by
  rw [relativeTransition_representation]
  exact (unitaryFrames N f i x).apply_symm_apply _

theorem relativeTransition_unitary_cocycle (N : ℕ) (f : ι → X → EffectiveFrame)
    (U : ι → Set X) :
    CocycleOn U (fun i j x => unitaryRepresentation N (relativeTransition f i j x)) :=
  (Geometry.EffectiveActionCocycle.map_cocycle_iff (unitaryRepresentation N)
    (HistoryEffectiveResponseSpace.unitaryRepresentation_faithful N)
    U (relativeTransition f)).mp (relativeTransition_cocycle f U)

/-- The comparison is with every element of the actual effective source group. -/
theorem relativeTransition_unique (N : ℕ) (f : ι → X → EffectiveFrame)
    (i j : ι) (x : X) (q : EffectiveFrame)
    (hq : ∀ v : ResponseSpace N,
      unitaryFrames N f i x (unitaryRepresentation N q v) = unitaryFrames N f j x v) :
    q = relativeTransition f i j x := by
  apply HistoryEffectiveResponseSpace.unitaryRepresentation_faithful N
  apply LinearIsometryEquiv.ext
  intro v
  apply (unitaryFrames N f i x).injective
  exact (hq v).trans (relativeTransition_action N f i j x v).symm

def components (N : ℕ) (f : ι → X → EffectiveFrame) (i : ι) (x : X)
    (v : ResponseSpace N) : ResponseSpace N := (unitaryFrames N f i x).symm v

theorem relativeTransition_components (N : ℕ) (f : ι → X → EffectiveFrame)
    (i j : ι) (x : X) (v : ResponseSpace N) :
    components N f i x v = unitaryRepresentation N (relativeTransition f i j x)
      (components N f j x v) := by
  apply (unitaryFrames N f i x).injective
  rw [relativeTransition_action]
  simp only [components, LinearIsometryEquiv.apply_symm_apply]

/-- The same overlap law holds for sections of the concrete arithmetic bundle. -/
theorem section_components_transition (N : ℕ) (f : ι → Base N → EffectiveFrame)
    (i j : ι) (x : Base N) (s : Section N) :
    components N f i x (s x) = unitaryRepresentation N (relativeTransition f i j x)
      (components N f j x (s x)) :=
  relativeTransition_components N f i j x (s x)

theorem relativeTransition_passive (N : ℕ) (f : ι → X → EffectiveFrame)
    (i j : ι) (x : X) (v : ResponseSpace N) :
    components N f j x v = (unitaryRepresentation N (relativeTransition f i j x)).symm
      (components N f i x v) := by
  apply (unitaryRepresentation N (relativeTransition f i j x)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (relativeTransition_components N f i j x v).symm

theorem components_inner (N : ℕ) (f : ι → X → EffectiveFrame)
    (i : ι) (x : X) (v w : ResponseSpace N) :
    inner ℂ (components N f i x v) (components N f i x w) = inner ℂ v w :=
  (unitaryFrames N f i x).symm.inner_map_map v w

end RelativeFrames

structure Conclusions : Prop where
  actual_base_card : ∀ N, Fintype.card (Base N) =
    ∑ b : HistoryRootSectors.Roots N, HistoryRootSectors.size N b
  unique_coordinates : ∀ N (F : Total N → Base N × ResponseSpace N),
    (∀ v, (F v).1 = projection N v) →
    (∀ v, (F v).2 = fibreCoordinate N v) → F = globalCoordinates N
  canonical_total_frame : ∀ N (v : Total N), changeFrame N (canonicalFrame N) v = v
  total_norm : ∀ N f (v : Total N), ‖(changeFrame N f v).2‖ = ‖v.2‖
  full_response_faithful : ∀ N, Function.Injective (unitaryRepresentation N)
  transition_unique : ∀ N (f : ℕ → HistoryLabel N → EffectiveFrame) i j x q,
    (∀ v : ResponseSpace N,
      unitaryFrames N f i x (unitaryRepresentation N q v) = unitaryFrames N f j x v) →
        q = relativeTransition f i j x
  actual_cocycle : ∀ N (f : ℕ → HistoryLabel N → EffectiveFrame)
    (U : ℕ → Set (HistoryLabel N)), CocycleOn U (relativeTransition f)

theorem generated : Conclusions where
  actual_base_card := base_card
  unique_coordinates := globalCoordinates_unique
  canonical_total_frame := changeFrame_canonical
  total_norm := changeFrame_norm
  full_response_faithful := HistoryEffectiveResponseSpace.unitaryRepresentation_faithful
  transition_unique := fun N => relativeTransition_unique N
  actual_cocycle := fun _ => relativeTransition_cocycle

end GeneratedFoundations.Arithmetic.HistoryResponseFrames
