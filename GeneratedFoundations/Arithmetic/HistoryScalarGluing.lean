module

public import GeneratedFoundations.Arithmetic.HistoryEffectiveFrames

/-!
# Scalar responses on the generated effective overlaps

The response kernel is the two-element kernel already calculated on the
complete arithmetic operation algebra. A change of lift in that kernel
leaves the scalar doublet and its complete elementary operator unchanged.
The corresponding statement for state vectors is deliberately different:
the simultaneous sign remains visible on states.

Triple-overlap consistency below requires precisely that the actual defect
belong to this response kernel. No global lift or strict product-group
cocycle is needed for the response gluing law.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryScalarGluing

open HistoryElementaryConnector (Frame Spinor scalarConnector scalarConnector_injective
  scalarConnector_covariant CompatibleDoublets CompatibleConnectors
  compatibleConnectors_iff_doublets)
open HistoryEffectiveFrames (conjugation unitaryRepresentation unitaryRepresentation_faithful
  LiftData CentralDefects centralRelift)
open Geometry.SourceScalarResponse (frameDoublet sourceMatrix frameSpin doubletLift
  frameSpin_doubletLift sourceMatrix_doubletLift)
open Operations.ReversalRealConnector (reversal connectorOfDoublet_firstColumn
  connectorOfDoublet_secondColumn)

theorem doublet_eq_of_response_eq (N : ℕ) {g k : Frame}
    (h : conjugation N g = conjugation N k) (v : Spinor) :
    frameDoublet g v = frameDoublet k v := by
  apply scalarConnector_injective N
  exact (scalarConnector_covariant N g v).symm.trans
    ((Equiv.congr_fun h (scalarConnector N v)).trans (scalarConnector_covariant N k v))

theorem doublet_eq_of_unitary_eq (N : ℕ) {g k : Frame}
    (h : unitaryRepresentation N g = unitaryRepresentation N k) (v : Spinor) :
    frameDoublet g v = frameDoublet k v := by
  rw [unitaryRepresentation_faithful N h]

theorem doublet_kernel_relift (z : Geometry.SourceFrameQuotient.response.ker)
    (g : Frame) (v : Spinor) :
    frameDoublet ((z : Frame) * g) v = frameDoublet g v :=
  Equiv.congr_fun
    (Geometry.EffectiveActionCocycle.kernel_relift
      Geometry.SourceFrameQuotient.response (z : Frame) g z.property) v

theorem connector_kernel_relift (N : ℕ)
    (z : Geometry.SourceFrameQuotient.response.ker) (g : Frame) (v : Spinor) :
    scalarConnector N (frameDoublet ((z : Frame) * g) v) =
      scalarConnector N (frameDoublet g v) := by
  rw [doublet_kernel_relift]

theorem transformed_columns (g : Frame) (v : Spinor) :
    (fun i => sourceMatrix (frameSpin g (doubletLift v)) i 0) =
        reversal (frameDoublet g v) ∧
      (fun i => sourceMatrix (frameSpin g (doubletLift v)) i 1) =
        frameDoublet g v := by
  rw [frameSpin_doubletLift, sourceMatrix_doubletLift]
  exact ⟨connectorOfDoublet_firstColumn _, funext (connectorOfDoublet_secondColumn _)⟩

section Local

variable {ι X : Type*}

theorem doublet_two_routes {U : ι → Set X} {g : LiftData ι X}
    (hg : CentralDefects U g) (i j k : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) (v : Spinor) :
    frameDoublet (g i j x) (frameDoublet (g j k x) v) =
      frameDoublet (g i k x) v :=
  Equiv.congr_fun
    ((Geometry.EffectiveActionCocycle.kernelDefects_iff_actionCocycle
      Geometry.SourceFrameQuotient.response U g).mp hg i j k x hi hj hk) v

theorem centralRelift_doublets_iff (U : ι → Set X)
    (z : ι → ι → X → Geometry.SourceFrameQuotient.response.ker)
    (g : LiftData ι X) (v : ι → X → Spinor) :
    CompatibleDoublets U (centralRelift z g) v ↔ CompatibleDoublets U g v := by
  simp only [CompatibleDoublets, centralRelift, doublet_kernel_relift]

theorem centralRelift_connectors_iff (N : ℕ) (U : ι → Set X)
    (z : ι → ι → X → Geometry.SourceFrameQuotient.response.ker)
    (g : LiftData ι X) (v : ι → X → Spinor) :
    CompatibleConnectors N U (centralRelift z g) (fun i x => scalarConnector N (v i x)) ↔
      CompatibleConnectors N U g (fun i x => scalarConnector N (v i x)) := by
  rw [compatibleConnectors_iff_doublets, compatibleConnectors_iff_doublets]
  exact centralRelift_doublets_iff U z g v

end Local

structure Conclusions : Prop where
  effective_response : ∀ N (g k : Frame), conjugation N g = conjugation N k →
    ∀ v, frameDoublet g v = frameDoublet k v
  relift_invariant : ∀ (z : Geometry.SourceFrameQuotient.response.ker) g v,
    frameDoublet ((z : Frame) * g) v = frameDoublet g v
  local_two_routes : ∀ {ι X : Type} (U : ι → Set X) (g : LiftData ι X),
    CentralDefects U g → ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → ∀ v,
      frameDoublet (g i j x) (frameDoublet (g j k x) v) = frameDoublet (g i k x) v
  compatible_relifts : ∀ {ι X : Type} (U : ι → Set X)
    (z : ι → ι → X → Geometry.SourceFrameQuotient.response.ker) g v,
      CompatibleDoublets U (centralRelift z g) v ↔ CompatibleDoublets U g v

theorem generated : Conclusions where
  effective_response := doublet_eq_of_response_eq
  relift_invariant := doublet_kernel_relift
  local_two_routes := fun _U _g hg => doublet_two_routes hg
  compatible_relifts := centralRelift_doublets_iff

end GeneratedFoundations.Arithmetic.HistoryScalarGluing
