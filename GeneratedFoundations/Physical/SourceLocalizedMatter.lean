module

public import GeneratedFoundations.Physical.SourceLocalizedFrames
public import GeneratedFoundations.Physical.SourceGaugeCocycle
public import GeneratedFoundations.Physical.SourceScalarGaugeCovariance
public import GeneratedFoundations.Physical.SourcePhaseFrames
public import GeneratedFoundations.Physical.SourcePseudorealCharts
public import GeneratedFoundations.Physical.SourceFrameConnection

/-!
# Effective transitions on actual local matter frames

The Hermitian charts below belong to an arbitrary localized matter bundle.
Compatibility with the specified frame realization means that their actual
overlap maps act through the previously derived joint matter characters.
This is a restriction on the realization; an arbitrary Hermitian bundle is
not asserted to satisfy it.

Once compatible local factor lifts are supplied, their quotient cocycle
follows from the actual charts. No cocycle for the individual factors is
assumed. Different compatible lifts have precisely the diagonal sixth-root
ambiguity, while their effective transition is uniquely determined on each
overlap. Local matter components use the passive frame convention.
-/

@[expose] public section

noncomputable section

open scoped Bundle

namespace GeneratedFoundations.Physical.SourceLocalizedMatter

open SourceChiralCarrier (FullMatter)
open SourceLocalizedFrames
open SourceGaugeCocycle
open SourceGaugeUnitary (unitaryRepresentation effectiveUnitaryRepresentation)

variable {ι M : Type*} [TopologicalSpace M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace FullMatter E)]
  (e : ι → Bundle.Trivialization FullMatter (π FullMatter E))
  [∀ i, (e i).IsLinear ℂ]
  (he : ∀ i, IsHermitianChart (e i))

/-- The six characters are those already derived on the source carrier.
This condition records their compatibility with the given physical charts. -/
def CompatibleLifts (g : LiftData ι M) : Prop :=
  ∀ i j x (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) (v : FullMatter),
    SourceGaugeTransport.coordinates
        (transition (e i) (e j) (he i) (he j) x hi hj v) =
      GlobalGaugeKernel.representation (g i j x) (SourceGaugeTransport.coordinates v)

theorem lift_eq_transition {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    unitaryTransition g i j x = transition (e i) (e j) (he i) (he j) x hi hj := by
  apply LinearIsometryEquiv.ext
  intro v
  apply SourceGaugeTransport.coordinates.injective
  exact (SourceGaugeTransport.coordinates_intertwines (g i j x) v).trans
    (hg i j x hi hj v).symm

theorem compatibleLifts_iff {g : LiftData ι M} :
    CompatibleLifts e he g ↔
      ∀ i j x (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet),
        unitaryTransition g i j x = transition (e i) (e j) (he i) (he j) x hi hj := by
  constructor
  · exact fun hg => lift_eq_transition e he hg
  · intro hg i j x hi hj v
    rw [← hg i j x hi hj]
    exact SourceGaugeTransport.coordinates_intertwines (g i j x) v

/-- The cocycle is a consequence of the actual fiber charts. -/
theorem compatible_unitaryCocycle {g : LiftData ι M} (hg : CompatibleLifts e he g) :
    CocycleOn (fun i => (e i).baseSet) (unitaryTransition g) := by
  intro i j k x hi hj hk
  rw [lift_eq_transition e he hg i j x hi hj,
    lift_eq_transition e he hg j k x hj hk,
    lift_eq_transition e he hg i k x hi hk]
  exact transition_cocycle (e i) (e j) (e k) (he i) (he j) (he k) x hi hj hk

theorem compatible_centralDefects {g : LiftData ι M} (hg : CompatibleLifts e he g) :
    CentralDefects (fun i => (e i).baseSet) g :=
  (centralDefects_iff_unitaryCocycle _ g).mpr (compatible_unitaryCocycle e he hg)

theorem compatible_effectiveCocycle {g : LiftData ι M} (hg : CompatibleLifts e he g) :
    CocycleOn (fun i => (e i).baseSet) (quotientTransition g) :=
  (quotientCocycle_iff_unitaryCocycle _ g).mpr (compatible_unitaryCocycle e he hg)

/-- The ambiguity is local to the overlap and is not an additional field. -/
theorem compatible_lifts_differ_by_sixthRoot {g k : LiftData ι M}
    (hg : CompatibleLifts e he g) (hk : CompatibleLifts e he k)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    ∃ z : GlobalGaugeKernel.sixthRoots,
      GlobalGaugeKernel.centralEmbedding z * k i j x = g i j x := by
  apply (unitary_eq_iff_central_relift _ _).mp
  exact (lift_eq_transition e he hg i j x hi hj).trans
    (lift_eq_transition e he hk i j x hi hj).symm

theorem compatible_effective_unique {g k : LiftData ι M}
    (hg : CompatibleLifts e he g) (hk : CompatibleLifts e he k)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    quotientTransition g i j x = quotientTransition k i j x := by
  apply (quotient_eq_iff_unitary _ _).mpr
  exact (lift_eq_transition e he hg i j x hi hj).trans
    (lift_eq_transition e he hk i j x hi hj).symm

theorem effective_transition_action {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    effectiveUnitaryRepresentation (quotientTransition g i j x) =
      transition (e i) (e j) (he i) (he j) x hi hj :=
  (effectiveUnitary_quotientMap (g i j x)).trans (lift_eq_transition e he hg i j x hi hj)

/-- Faithfulness gives uniqueness against any proposed effective overlap map. -/
theorem effective_transition_unique {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet)
    (q : SourceGlobalGaugeGroup.EffectiveGroup)
    (hq : effectiveUnitaryRepresentation q =
      transition (e i) (e j) (he i) (he j) x hi hj) :
    q = quotientTransition g i j x := by
  apply SourceGaugeUnitary.effectiveUnitaryRepresentation_injective
  exact hq.trans (effective_transition_action e he hg i j x hi hj).symm

theorem centralRelift_compatible {g : LiftData ι M}
    (hg : CompatibleLifts e he g) (z : ι → ι → M → GlobalGaugeKernel.sixthRoots) :
    CompatibleLifts e he (centralRelift z g) := by
  apply (compatibleLifts_iff e he).mpr
  intro i j x hi hj
  rw [centralRelift_unitary]
  exact lift_eq_transition e he hg i j x hi hj

theorem passive_components_from_lift {g : LiftData ι M}
    (hg : CompatibleLifts e he g) (i j : ι) (x : M)
    (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) (v : E x) :
    (frame (e j) (he j) x hj).symm v =
      (unitaryTransition g i j x).symm ((frame (e i) (he i) x hi).symm v) := by
  rw [lift_eq_transition e he hg i j x hi hj]
  exact passive_components (e i) (e j) (he i) (he j) x hi hj v

/-- The effective action represents the library's actual overlap operator. -/
theorem overlapOperator_from_lift {g : LiftData ι M}
    (hg : CompatibleLifts e he g) (i j : ι) (x : M)
    (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    overlapOperator (e i) (e j) x =
      (unitaryTransition g i j x).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [lift_eq_transition e he hg i j x hi hj]
  exact overlapOperator_eq_transition (e i) (e j) (he i) (he j) x hi hj

/-- Operator gluing expressed through the actual Hermitian chart changes. -/
def CompatibleChartConnectors (C : ι → M → Module.End ℂ FullMatter) : Prop :=
  ∀ i j x (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet),
    C i x = (transition (e i) (e j) (he i) (he j) x hi hj).toLinearEquiv.toLinearMap *
      C j x * (transition (e i) (e j) (he i) (he j) x hi hj).symm.toLinearEquiv.toLinearMap

omit [TopologicalSpace M] in
theorem unitaryTransition_linear (g : LiftData ι M) (i j : ι) (x : M) :
    (unitaryTransition g i j x).toLinearEquiv.toLinearMap =
      SourceGaugeTransport.representation (g i j x) := by
  apply LinearMap.ext
  intro v
  exact SourceGaugeUnitary.unitaryAction_apply (g i j x) v

omit [TopologicalSpace M] in
theorem unitaryTransition_symm_linear (g : LiftData ι M) (i j : ι) (x : M) :
    (unitaryTransition g i j x).symm.toLinearEquiv.toLinearMap =
      SourceGaugeTransport.representation (g i j x)⁻¹ := by
  apply LinearMap.ext
  intro v
  exact SourceGaugeUnitary.unitaryAction_symm_apply (g i j x) v

theorem transition_linear {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    (transition (e i) (e j) (he i) (he j) x hi hj).toLinearEquiv.toLinearMap =
      SourceGaugeTransport.representation (g i j x) :=
  (congrArg (fun U : FullMatter ≃ₗᵢ[ℂ] FullMatter => U.toLinearEquiv.toLinearMap)
    (lift_eq_transition e he hg i j x hi hj).symm).trans (unitaryTransition_linear g i j x)

theorem transition_symm_linear {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet) :
    (transition (e i) (e j) (he i) (he j) x hi hj).symm.toLinearEquiv.toLinearMap =
      SourceGaugeTransport.representation (g i j x)⁻¹ :=
  (congrArg (fun U : FullMatter ≃ₗᵢ[ℂ] FullMatter => U.symm.toLinearEquiv.toLinearMap)
    (lift_eq_transition e he hg i j x hi hj).symm).trans (unitaryTransition_symm_linear g i j x)

theorem chartConnector_conjugate {g : LiftData ι M} (hg : CompatibleLifts e he g)
    (i j : ι) (x : M) (hi : x ∈ (e i).baseSet) (hj : x ∈ (e j).baseSet)
    (C : Module.End ℂ FullMatter) :
    (transition (e i) (e j) (he i) (he j) x hi hj).toLinearEquiv.toLinearMap * C *
        (transition (e i) (e j) (he i) (he j) x hi hj).symm.toLinearEquiv.toLinearMap =
      SourceGaugeTransport.representation (g i j x) * C *
        SourceGaugeTransport.representation (g i j x)⁻¹ :=
  congrArg₂ (fun A B : Module.End ℂ FullMatter => A * C * B)
    (transition_linear e he hg i j x hi hj) (transition_symm_linear e he hg i j x hi hj)

theorem compatible_chartConnectors_iff {g : LiftData ι M}
    (hg : CompatibleLifts e he g) (C : ι → M → Module.End ℂ FullMatter) :
    CompatibleChartConnectors e he C ↔
      SourceScalarGaugeCovariance.CompatibleConnectors (fun i => (e i).baseSet) g C := by
  constructor <;> intro h i j x hi hj
  · exact (h i j x hi hj).trans (chartConnector_conjugate e he hg i j x hi hj (C j x))
  · exact (h i j x hi hj).trans (chartConnector_conjugate e he hg i j x hi hj (C j x)).symm

/-- Arbitrary elementary blocks that glue in the actual charts determine
unique doublet components on those charts. No doublet is an input. -/
theorem local_elementary_doublets {g : LiftData ι M}
    (hg : CompatibleLifts e he g)
    (A : ι → M → Module.End ℂ SourceMinimalRepresentation.SourceCarrier)
    (hA : ∀ i x, x ∈ (e i).baseSet → SourceExchangeConnectorTransport.SplitElementary (A i x))
    (hglue : CompatibleChartConnectors e he
      (fun i x => SourceExchangeConnectorTransport.chiralConnector (A i x))) :
    ∃ H : ι → M → ReversalRealConnector.Spinor,
      (∀ i x, x ∈ (e i).baseSet →
        SourceExchangeConnectorTransport.chiralConnector (A i x) =
          SourceScalarConnector.scalarConnector (H i x)) ∧
      SourceScalarGaugeCovariance.CompatibleDoublets (fun i => (e i).baseSet) g H ∧
      ∀ K : ι → M → ReversalRealConnector.Spinor,
        (∀ i x, x ∈ (e i).baseSet →
          SourceExchangeConnectorTransport.chiralConnector (A i x) =
            SourceScalarConnector.scalarConnector (K i x)) →
        ∀ i x, x ∈ (e i).baseSet → K i x = H i x :=
  SourceScalarGaugeCovariance.local_elementary_doublets (fun i => (e i).baseSet) g A hA
    ((compatible_chartConnectors_iff e he hg _).mp hglue)

end GeneratedFoundations.Physical.SourceLocalizedMatter
