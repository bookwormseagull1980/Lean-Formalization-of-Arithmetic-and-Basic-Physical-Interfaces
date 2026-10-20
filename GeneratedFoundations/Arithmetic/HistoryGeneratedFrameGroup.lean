module

public import GeneratedFoundations.Arithmetic.HistoryEffectiveFrames
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Minimal closure of the actual arithmetic source-frame action

Both source factors act on every history and phase coefficient. Their
generated group is the image of that action, and is proved equal to the
subgroup closure of the two factor images. No independent group or kernel
is supplied. On states the representation is faithful. On response
operators the already computed simultaneous central sign is quotiented.

This is the generated source-frame group. It does not identify the two
source factors with all unitary operations on the arithmetic carrier, or
with the separately constructed charge flow.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryGeneratedFrameGroup

open HistoryCliffordAction HistoryElementaryConnector HistoryEffectiveFrames

abbrev SourceFactor := Operations.SourceSpinCornerGroup.SU2
abbrev StateUnitary (N : ℕ) := Space N ≃ₗᵢ[ℂ] Space N

def leftInclusion : SourceFactor →* Frame where
  toFun g := (g, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

def rightInclusion : SourceFactor →* Frame where
  toFun g := (1, g)
  map_one' := rfl
  map_mul' _ _ := by simp

theorem presentation_factorization (g : Frame) :
    leftInclusion g.1 * rightInclusion g.2 = g := by
  simp [leftInclusion, rightInclusion]

theorem presentation_factorization_unique (g h : SourceFactor) (k : Frame)
    (he : leftInclusion g * rightInclusion h = k) : g = k.1 ∧ h = k.2 := by
  simpa [leftInclusion, rightInclusion, Prod.ext_iff] using he

def leftOperators (N : ℕ) : SourceFactor →* StateUnitary N :=
  (unitaryRepresentation N).comp leftInclusion

def rightOperators (N : ℕ) : SourceFactor →* StateUnitary N :=
  (unitaryRepresentation N).comp rightInclusion

abbrev GeneratedGroup (N : ℕ) := (unitaryRepresentation N).range

def sourceFactorClosure (N : ℕ) : Subgroup (StateUnitary N) :=
  Subgroup.closure (Set.range (leftOperators N) ∪ Set.range (rightOperators N))

theorem left_mem_generated (N : ℕ) (g : SourceFactor) :
    leftOperators N g ∈ GeneratedGroup N := ⟨leftInclusion g, rfl⟩

theorem right_mem_generated (N : ℕ) (g : SourceFactor) :
    rightOperators N g ∈ GeneratedGroup N := ⟨rightInclusion g, rfl⟩

theorem sourceFactorClosure_eq_generated (N : ℕ) :
    sourceFactorClosure N = GeneratedGroup N := by
  apply le_antisymm
  · apply (Subgroup.closure_le (GeneratedGroup N)).2
    rintro U (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact left_mem_generated N g
    · exact right_mem_generated N g
  · rintro U ⟨g, rfl⟩
    have hl : leftOperators N g.1 ∈ sourceFactorClosure N :=
      Subgroup.subset_closure (Or.inl ⟨g.1, rfl⟩)
    have hr : rightOperators N g.2 ∈ sourceFactorClosure N :=
      Subgroup.subset_closure (Or.inr ⟨g.2, rfl⟩)
    have hm := (sourceFactorClosure N).mul_mem hl hr
    change unitaryRepresentation N g ∈ sourceFactorClosure N
    simpa only [leftOperators, rightOperators, MonoidHom.comp_apply,
      ← map_mul, presentation_factorization] using hm

theorem generated_least (N : ℕ) (H : Subgroup (StateUnitary N))
    (hl : ∀ g, leftOperators N g ∈ H) (hr : ∀ g, rightOperators N g ∈ H) :
    GeneratedGroup N ≤ H := by
  rw [← sourceFactorClosure_eq_generated]
  apply (Subgroup.closure_le H).2
  rintro U (⟨g, rfl⟩ | ⟨g, rfl⟩)
  · exact hl g
  · exact hr g

theorem factorization_unique (N : ℕ) (g h : Frame)
    (he : leftOperators N g.1 * rightOperators N g.2 =
      leftOperators N h.1 * rightOperators N h.2) : g = h := by
  apply unitaryRepresentation_faithful N
  simpa only [leftOperators, rightOperators, MonoidHom.comp_apply,
    ← map_mul, presentation_factorization] using he

def stateEquivRange (N : ℕ) : Frame ≃* GeneratedGroup N :=
  MulEquiv.ofBijective (unitaryRepresentation N).rangeRestrict
    ⟨fun _ _ h => unitaryRepresentation_faithful N (congrArg Subtype.val h),
      by rintro ⟨U, g, rfl⟩; exact ⟨g, rfl⟩⟩

theorem response_kernel (N : ℕ) (g : Frame) :
    conjugation N g = 1 ↔
      g = 1 ∨ g = Geometry.SourceFrameQuotient.centralSign := by
  rw [conjugation_kernel, Geometry.SourceFrameQuotient.mem_response_kernel]

structure Conclusions : Prop where
  generated_closure : ∀ N, sourceFactorClosure N = GeneratedGroup N
  least_closure : ∀ N (H : Subgroup (StateUnitary N)),
    (∀ g, leftOperators N g ∈ H) → (∀ g, rightOperators N g ∈ H) →
      GeneratedGroup N ≤ H
  faithful_state_presentation : ∀ N, Function.Bijective (stateEquivRange N)
  computed_response_kernel : ∀ N g, conjugation N g = 1 ↔
    g = 1 ∨ g = Geometry.SourceFrameQuotient.centralSign

theorem generated : Conclusions where
  generated_closure := sourceFactorClosure_eq_generated
  least_closure := generated_least
  faithful_state_presentation := fun N => (stateEquivRange N).bijective
  computed_response_kernel := response_kernel

end GeneratedFoundations.Arithmetic.HistoryGeneratedFrameGroup
