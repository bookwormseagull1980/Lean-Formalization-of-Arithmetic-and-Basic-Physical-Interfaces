module

public import GeneratedFoundations.Arithmetic.HistoryReversalIsometry
public import GeneratedFoundations.Arithmetic.HistoryEffectiveFrames
public import GeneratedFoundations.Geometry.HermitianFrames

/-!
# Local antiunitaries of the complete arithmetic state carrier

The reversal is the source operation already constructed on every retained
history--phase label and both source sectors. Hermitian comparison charts
transport this fixed antiunitary. Equality on an overlap is equivalent to
commutation of the complete transition with that reversal.

All generated source frames satisfy this criterion. The converse does not
identify every reversal-preserving unitary of the larger history carrier
with a uniform two-mode source frame. Uniqueness below is uniqueness of the
transported antiunitary on a fibre, not a classification of that larger group.
-/

@[expose] public section

noncomputable section

open scoped Bundle

namespace GeneratedFoundations.Arithmetic.HistoryReversalCharts

open HistoryCliffordAction (Space)
open HistoryReversalIsometry (fullAntiunitary fullReversal)
open Geometry.HermitianFrames

def Intertwines (N : ℕ) (g : Space N ≃ₗᵢ[ℂ] Space N) : Prop :=
  ∀ v, g (fullAntiunitary N v) = fullAntiunitary N (g v)

theorem source_frames_intertwine (N : ℕ) (g : HistoryElementaryConnector.Frame) :
    Intertwines N (HistoryEffectiveFrames.stateUnitary N g) :=
  HistoryReversalIsometry.frame_intertwines N g

variable {N : ℕ} {M : Type*} [TopologicalSpace M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (Space N) E)]
  (e f k : Bundle.Trivialization (Space N) (π (Space N) E))
  [e.IsLinear ℂ] [f.IsLinear ℂ] [k.IsLinear ℂ]

def localReversal (he : IsHermitianChart e) (x : M) (hx : x ∈ e.baseSet) :
    E x ≃ₗᵢ⋆[ℂ] E x :=
  ((frame e he x hx).symm.trans (fullAntiunitary N)).trans (frame e he x hx)

@[simp] theorem localReversal_apply (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (v : E x) :
    localReversal e he x hx v =
      frame e he x hx (fullAntiunitary N ((frame e he x hx).symm v)) := rfl

theorem localReversal_inner (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (u v : E x) :
    inner ℂ (localReversal e he x hx u) (localReversal e he x hx v) = inner ℂ v u := by
  rw [localReversal_apply, localReversal_apply, LinearIsometryEquiv.inner_map_map]
  change inner ℂ (fullReversal N ((frame e he x hx).symm u))
    (fullReversal N ((frame e he x hx).symm v)) = _
  rw [HistoryReversalIsometry.fullReversal_inner, LinearIsometryEquiv.inner_map_map]

@[simp] theorem localReversal_square (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (v : E x) :
    localReversal e he x hx (localReversal e he x hx v) = -v := by
  rw [localReversal_apply, localReversal_apply, LinearIsometryEquiv.symm_apply_apply]
  change frame e he x hx (fullReversal N (fullReversal N ((frame e he x hx).symm v))) = _
  rw [HistoryReversalIsometry.fullReversal_square, map_neg,
    LinearIsometryEquiv.apply_symm_apply]

@[simp] theorem localReversal_frame (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (v : Space N) :
    localReversal e he x hx (frame e he x hx v) =
      frame e he x hx (fullAntiunitary N v) := by
  rw [localReversal_apply, LinearIsometryEquiv.symm_apply_apply]

theorem localReversal_other_frame (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (v : Space N) :
    localReversal e he x hx (frame f hf x hy v) =
      frame e he x hx (fullAntiunitary N (transition e f he hf x hx hy v)) := rfl

theorem localReversal_eq_iff_intertwines (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    localReversal e he x hx = localReversal f hf x hy ↔
      Intertwines N (transition e f he hf x hx hy) := by
  constructor
  · intro h v
    have hv := congrArg (fun J : E x ≃ₗᵢ⋆[ℂ] E x => J (frame f hf x hy v)) h
    rw [localReversal_other_frame, localReversal_frame] at hv
    apply (frame e he x hx).injective
    rw [frame_transition]
    exact hv.symm
  · intro hg
    apply LinearIsometryEquiv.ext
    intro w
    obtain ⟨v, rfl⟩ := (frame f hf x hy).surjective w
    rw [localReversal_other_frame, localReversal_frame, ← hg v, frame_transition]

theorem overlapOperator_reversal_iff (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) :
    (∀ v, overlapOperator e f x (fullAntiunitary N v) =
      fullAntiunitary N (overlapOperator e f x v)) ↔
        localReversal e he x hx = localReversal f hf x hy := by
  rw [overlapOperator_eq_transition e f he hf x hx hy]
  exact (localReversal_eq_iff_intertwines e f he hf x hx hy).symm

theorem transition_intertwines_trans
    (he : IsHermitianChart e) (hf : IsHermitianChart f) (hk : IsHermitianChart k)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet) (hz : x ∈ k.baseSet)
    (hef : Intertwines N (transition e f he hf x hx hy))
    (hfk : Intertwines N (transition f k hf hk x hy hz)) :
    Intertwines N (transition e k he hk x hx hz) :=
  (localReversal_eq_iff_intertwines e k he hk x hx hz).mp
    (((localReversal_eq_iff_intertwines e f he hf x hx hy).mpr hef).trans
      ((localReversal_eq_iff_intertwines f k hf hk x hy hz).mpr hfk))

theorem localReversal_unique (he : IsHermitianChart e)
    (x : M) (hx : x ∈ e.baseSet) (J : E x ≃ₗᵢ⋆[ℂ] E x)
    (hJ : ∀ v, J (frame e he x hx v) = frame e he x hx (fullAntiunitary N v)) :
    J = localReversal e he x hx := by
  apply LinearIsometryEquiv.ext
  intro w
  obtain ⟨v, rfl⟩ := (frame e he x hx).surjective w
  exact (hJ v).trans (localReversal_frame e he x hx v).symm

theorem commonReversal_existsUnique
    (he : IsHermitianChart e) (hf : IsHermitianChart f)
    (x : M) (hx : x ∈ e.baseSet) (hy : x ∈ f.baseSet)
    (hg : Intertwines N (transition e f he hf x hx hy)) :
    ∃! J : E x ≃ₗᵢ⋆[ℂ] E x,
      (∀ v, J (frame e he x hx v) = frame e he x hx (fullAntiunitary N v)) ∧
      (∀ v, J (frame f hf x hy v) = frame f hf x hy (fullAntiunitary N v)) := by
  have heq := (localReversal_eq_iff_intertwines e f he hf x hx hy).mpr hg
  refine ⟨localReversal e he x hx, ⟨localReversal_frame e he x hx, ?_⟩, ?_⟩
  · intro v
    rw [heq]
    exact localReversal_frame f hf x hy v
  · intro J hJ
    exact localReversal_unique e he x hx J hJ.1

end GeneratedFoundations.Arithmetic.HistoryReversalCharts
