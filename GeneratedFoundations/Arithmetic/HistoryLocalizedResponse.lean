module

public import GeneratedFoundations.Arithmetic.HistoryResponseFrames
public import GeneratedFoundations.Geometry.HermitianFrames

/-!
# Local charts of the complete arithmetic response carrier

The canonical total space and its source frames are constructed in
`HistoryResponseFrames`. Here the model fibre remains that same complete
matrix Hilbert space. Comparison charts are Hermitian charts of that fibre;
their compatibility with source transitions is stated explicitly and is not
an additional input to the canonical source.

Compatible lifts force the overlap cocycle. The ambiguity of a lift is the
computed simultaneous source sign, whereas the effective transition is
unique. The complete matrix-coordinate equivalence then transports overlap
relations to the actual arithmetic operators. Elementary responses determine
their local doublets, including their gluing and uniqueness on the patches.
-/

@[expose] public section

noncomputable section

open scoped Bundle

namespace GeneratedFoundations.Arithmetic.HistoryLocalizedResponse

open HistoryCliffordAction (Algebra)
open HistoryElementaryConnector (Frame Spinor Elementary scalarConnector)
open HistoryEffectiveFrames (EffectiveFrame LiftData quotientTransition)
open HistoryEffectiveResponseSpace (ResponseSpace matrixEquiv unitaryRepresentation)
open Geometry.HermitianFrames
open Geometry.EffectiveActionCocycle (CocycleOn)

variable {N : ℕ} {ι M : Type*} [TopologicalSpace M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ResponseSpace N) E)]
  (e : ι → Bundle.Trivialization (ResponseSpace N) (π (ResponseSpace N) E))
  [∀ i, (e i).IsLinear ℂ]
  (he : ∀ i, IsHermitianChart (e i))

def liftUnitary (g : LiftData ι M) (i j : ι) (x : M) :
    ResponseSpace N ≃ₗᵢ[ℂ] ResponseSpace N :=
  unitaryRepresentation N (quotientTransition g i j x)

def CompatibleLifts (g : LiftData ι M) : Prop :=
  ∀ i j x (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet),
    liftUnitary (N := N) g i j x = transition (e i) (e j) (he i) (he j) x hi hj

theorem compatibleLifts_iff (g : LiftData ι M) : CompatibleLifts e he g ↔
    ∀ i j x (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet),
      liftUnitary (N := N) g i j x = transition (e i) (e j) (he i) (he j) x hi hj := Iff.rfl

theorem lift_eq_transition {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    liftUnitary (N := N) g i j x = transition (e i) (e j) (he i) (he j) x hi hj :=
  hg i j x hi hj

theorem compatible_unitaryCocycle {g : LiftData ι M} (hg : CompatibleLifts e he g) :
    CocycleOn (fun i => (e i).baseSet) (liftUnitary (N := N) g) := by
  intro i j k x hi hj hk
  rw [hg i j x hi hj, hg j k x hj hk, hg i k x hi hk]
  exact transition_cocycle (e i) (e j) (e k) (he i) (he j) (he k) x hi hj hk

theorem compatible_effectiveCocycle {g : LiftData ι M} (hg : CompatibleLifts e he g) :
    CocycleOn (fun i => (e i).baseSet) (quotientTransition g) :=
  (Geometry.EffectiveActionCocycle.map_cocycle_iff (unitaryRepresentation N)
    (HistoryEffectiveResponseSpace.unitaryRepresentation_faithful N)
    _ (quotientTransition g)).mpr (compatible_unitaryCocycle e he hg)

theorem compatible_centralDefects {g : LiftData ι M} (hg : CompatibleLifts e he g) :
    HistoryEffectiveFrames.CentralDefects (fun i => (e i).baseSet) g :=
  (HistoryEffectiveFrames.centralDefects_iff_quotientCocycle _ g).mpr
    (compatible_effectiveCocycle e he hg)

theorem compatible_effective_unique {g k : LiftData ι M}
    (hg : CompatibleLifts e he g) (hk : CompatibleLifts e he k)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    quotientTransition g i j x = quotientTransition k i j x := by
  apply HistoryEffectiveResponseSpace.unitaryRepresentation_faithful N
  exact (hg i j x hi hj).trans (hk i j x hi hj).symm

/-- The lift ambiguity is two-valued on this response carrier, not a copied
charged-matter phase kernel. -/
theorem compatible_lifts_two_signs {g k : LiftData ι M}
    (hg : CompatibleLifts e he g) (hk : CompatibleLifts e he k)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    g i j x = k i j x ∨
      g i j x = Geometry.SourceFrameQuotient.centralSign * k i j x := by
  have hq := compatible_effective_unique e he hg hk i j x hi hj
  have ha := (Geometry.EffectiveActionCocycle.quotient_eq_iff_action
    Geometry.SourceFrameQuotient.response _ _).mp hq
  have hker : g i j x * (k i j x)⁻¹ ∈ Geometry.SourceFrameQuotient.response.ker := by
    exact (Geometry.EffectiveActionCocycle.mapped_mul_inv_eq_one_iff
      Geometry.SourceFrameQuotient.response _ _).mpr ha
  rcases (Geometry.SourceFrameQuotient.mem_response_kernel _).mp hker with hp | hm
  · exact Or.inl (mul_inv_eq_one.mp hp)
  · exact Or.inr ((mul_inv_eq_iff_eq_mul).mp hm)

theorem effective_transition_unique {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet)
    (q : EffectiveFrame)
    (hq : unitaryRepresentation N q = transition (e i) (e j) (he i) (he j) x hi hj) :
    q = quotientTransition g i j x := by
  apply HistoryEffectiveResponseSpace.unitaryRepresentation_faithful N
  exact hq.trans (hg i j x hi hj).symm

theorem centralRelift_compatible {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (z : ι → ι → M → Geometry.SourceFrameQuotient.response.ker) :
    CompatibleLifts e he (HistoryEffectiveFrames.centralRelift z g) := by
  intro i j x hi hj
  change unitaryRepresentation N
    (quotientTransition (HistoryEffectiveFrames.centralRelift z g) i j x) = _
  rw [HistoryEffectiveFrames.centralRelift_quotient]
  exact hg i j x hi hj

theorem passive_components_from_lift {g : LiftData ι M}
    (hg : CompatibleLifts e he g) (i j : ι) (x : M)
    (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) (v : E x) :
    (frame (e j) (he j) x hj).symm v =
      (liftUnitary (N := N) g i j x).symm ((frame (e i) (he i) x hi).symm v) := by
  rw [hg i j x hi hj]
  exact passive_components (e i) (e j) (he i) (he j) x hi hj v

theorem overlapOperator_from_lift {g : LiftData ι M}
    (hg : CompatibleLifts e he g) (i j : ι) (x : M)
    (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    overlapOperator (e i) (e j) x =
      (liftUnitary (N := N) g i j x).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [hg i j x hi hj]
  exact overlapOperator_eq_transition (e i) (e j) (he i) (he j) x hi hj

def CompatibleChartConnectors (C : ι → M → Module.End ℂ (ResponseSpace N)) : Prop :=
  ∀ i j x (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet),
    C i x = (transition (e i) (e j) (he i) (he j) x hi hj).toLinearEquiv.toLinearMap *
      C j x * (transition (e i) (e j) (he i) (he j) x hi hj).symm.toLinearEquiv.toLinearMap

omit [TopologicalSpace M] in
theorem liftUnitary_linear (g : LiftData ι M) (i j : ι) (x : M) :
    (liftUnitary (N := N) g i j x).toLinearEquiv.toLinearMap =
      HistoryEffectiveResponseSpace.representation N (quotientTransition g i j x) := rfl

omit [TopologicalSpace M] in
theorem liftUnitary_symm_linear (g : LiftData ι M) (i j : ι) (x : M) :
    (liftUnitary (N := N) g i j x).symm.toLinearEquiv.toLinearMap =
      HistoryEffectiveResponseSpace.representation N (quotientTransition g i j x)⁻¹ := rfl

theorem transition_linear {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    (transition (e i) (e j) (he i) (he j) x hi hj).toLinearEquiv.toLinearMap =
      HistoryEffectiveResponseSpace.representation N (quotientTransition g i j x) :=
  congrArg (fun U : ResponseSpace N ≃ₗᵢ[ℂ] ResponseSpace N =>
    U.toLinearEquiv.toLinearMap) (hg i j x hi hj).symm

theorem transition_symm_linear {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    (transition (e i) (e j) (he i) (he j) x hi hj).symm.toLinearEquiv.toLinearMap =
      HistoryEffectiveResponseSpace.representation N (quotientTransition g i j x)⁻¹ :=
  congrArg (fun U : ResponseSpace N ≃ₗᵢ[ℂ] ResponseSpace N =>
    U.symm.toLinearEquiv.toLinearMap) (hg i j x hi hj).symm

theorem chartConnector_conjugate {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet)
    (C : Module.End ℂ (ResponseSpace N)) :
    (transition (e i) (e j) (he i) (he j) x hi hj).toLinearEquiv.toLinearMap * C *
      (transition (e i) (e j) (he i) (he j) x hi hj).symm.toLinearEquiv.toLinearMap =
    HistoryEffectiveResponseSpace.representation N (quotientTransition g i j x) * C *
      HistoryEffectiveResponseSpace.representation N (quotientTransition g i j x)⁻¹ :=
  congrArg₂ (fun A B : Module.End ℂ (ResponseSpace N) => A * C * B)
    (transition_linear e he hg i j x hi hj) (transition_symm_linear e he hg i j x hi hj)

theorem compatible_chartConnectors_iff {g : LiftData ι M}
    (hg : CompatibleLifts e he g) (C : ι → M → Module.End ℂ (ResponseSpace N)) :
    CompatibleChartConnectors e he C ↔
      ∀ i j x, x ∈ (e i).baseSet → x ∈ (e j).baseSet →
        C i x = HistoryEffectiveResponseSpace.representation N (quotientTransition g i j x) *
          C j x * HistoryEffectiveResponseSpace.representation N (quotientTransition g i j x)⁻¹ := by
  constructor <;> intro h i j x hi hj
  · exact (h i j x hi hj).trans (chartConnector_conjugate e he hg i j x hi hj (C j x))
  · exact (h i j x hi hj).trans (chartConnector_conjugate e he hg i j x hi hj (C j x)).symm

/-- Chart gluing of responses is equivalent to the original full-operator
gluing, including all history and phase matrix entries. -/
theorem compatible_responses_iff {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (A : ι → M → Algebra N) :
    (∀ i j x (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet),
      (matrixEquiv N).symm (A i x) =
        transition (e i) (e j) (he i) (he j) x hi hj ((matrixEquiv N).symm (A j x))) ↔
      HistoryElementaryConnector.CompatibleConnectors N (fun i => (e i).baseSet) g A := by
  constructor
  · intro h i j x hi hj
    have hv := congrArg (matrixEquiv N) (h i j x hi hj)
    rw [← hg i j x hi hj] at hv
    simpa only [liftUnitary, quotientTransition,
      HistoryEffectiveResponseSpace.unitaryRepresentation_quotient,
      LinearEquiv.apply_symm_apply, HistoryEffectiveFrames.conjugate] using hv
  · intro h i j x hi hj
    apply (matrixEquiv N).injective
    rw [← hg i j x hi hj]
    simpa only [liftUnitary, quotientTransition,
      HistoryEffectiveResponseSpace.unitaryRepresentation_quotient,
      LinearEquiv.apply_symm_apply, HistoryEffectiveFrames.conjugate] using h i j x hi hj

theorem local_elementary_doublets {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (A : ι → M → Algebra N)
    (hA : ∀ i x, x ∈ (e i).baseSet → Elementary N (A i x))
    (hglue : ∀ i j x (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet),
      (matrixEquiv N).symm (A i x) =
        transition (e i) (e j) (he i) (he j) x hi hj ((matrixEquiv N).symm (A j x))) :
    ∃ v : ι → M → Spinor,
      (∀ i x, x ∈ (e i).baseSet → A i x = scalarConnector N (v i x)) ∧
      HistoryElementaryConnector.CompatibleDoublets (fun i => (e i).baseSet) g v ∧
      ∀ w : ι → M → Spinor,
        (∀ i x, x ∈ (e i).baseSet → A i x = scalarConnector N (w i x)) →
        ∀ i x, x ∈ (e i).baseSet → w i x = v i x :=
  HistoryElementaryConnector.local_elementary_doublets N _ g A hA
    ((compatible_responses_iff e he hg A).mp hglue)

end GeneratedFoundations.Arithmetic.HistoryLocalizedResponse
