module

public import GeneratedFoundations.Physical.SourceGaugeUnitary
public import GeneratedFoundations.Geometry.EffectiveActionCocycle
public import GeneratedFoundations.Operations.UnitaryRepresentation

/-!
# Common-phase lifts and the effective gauge cocycle

A local lift has one colour frame, one weak frame and one phase. The same
phase acts in all six matter blocks. Its failure to satisfy a product-group
cocycle is invisible on the actual source matter exactly when the defect
belongs to the previously computed diagonal subgroup of order six.

For the passive frame convention `e_j = e_i g_ij`, the transition written
here sends components in chart `j` to components in chart `i`. Thus its
cocycle is `T_ij * T_jk = T_ik`, and compatible components obey
`psi_i = T_ij psi_j`, equivalently `psi_j = T_ij.symm psi_i`.

All statements are restricted to the indicated overlaps. The product-group
lifts themselves are not assumed to satisfy a cocycle, and no separate
global lift of any colour, weak or phase factor is assumed. The faithful
quotient and its unitary representation are the ones already derived on
`FullMatter`; their kernel and faithfulness are not extra hypotheses.

This file establishes the algebraic overlap and local-section compatibility
needed by the localization realization. It does not assert smoothness,
existence of arbitrary principal bundles, or a global trivialization.
-/

@[expose] public section

noncomputable section

open scoped Kronecker

namespace GeneratedFoundations.Physical.SourceGaugeCocycle

export GeneratedFoundations.Geometry.EffectiveActionCocycle (
  CocycleOn mapped_mul_inv_eq_one_iff map_cocycle_iff cocycleOn_self cocycleOn_inverse
)

open SourceChiralCarrier
open SourceGlobalGaugeGroup (centralSix EffectiveGroup)
open SourceGaugeUnitary (unitaryRepresentation effectiveUnitaryRepresentation)

abbrev GaugeGroup := GlobalGaugeKernel.GaugeGroup
abbrev MatterUnitary := FullMatter ≃ₗᵢ[ℂ] FullMatter

def quotientMap : GaugeGroup →* EffectiveGroup := QuotientGroup.mk' centralSix

export Operations.UnitaryRepresentation (linearIsometryEquiv_eq_one_iff)

theorem unitary_eq_one_iff_end (g : GaugeGroup) :
    unitaryRepresentation g = 1 ↔ SourceGaugeTransport.representation g = 1 :=
  linearIsometryEquiv_eq_one_iff (unitaryRepresentation g)

theorem unitary_eq_one_iff (g : GaugeGroup) :
    unitaryRepresentation g = 1 ↔ g ∈ centralSix := by
  rw [unitary_eq_one_iff_end]
  have hk : SourceGaugeTransport.representation.ker = centralSix :=
    SourceGaugeTransport.kernel_eq_zpowers
  rw [← hk]
  exact Iff.rfl

theorem unitaryRepresentation_kernel : unitaryRepresentation.ker = centralSix := by
  ext g
  exact unitary_eq_one_iff g

theorem centralSix_iff_sixthRoot (g : GaugeGroup) :
    g ∈ centralSix ↔
      ∃ z : GlobalGaugeKernel.sixthRoots, GlobalGaugeKernel.centralEmbedding z = g := by
  rw [← unitary_eq_one_iff, unitary_eq_one_iff_end,
    SourceGaugeTransport.representation_eq_one_iff,
    GlobalGaugeKernel.kernel_iff_exists_centralEmbedding]

theorem unitary_central (z : GlobalGaugeKernel.sixthRoots) :
    unitaryRepresentation (GlobalGaugeKernel.centralEmbedding z) = 1 :=
  (unitary_eq_one_iff _).mpr ((centralSix_iff_sixthRoot _).mpr ⟨z, rfl⟩)

/-- Centrality is checked in the actual three group factors. -/
theorem centralEmbedding_commutes (z : GlobalGaugeKernel.sixthRoots) (g : GaugeGroup) :
    Commute (GlobalGaugeKernel.centralEmbedding z) g := by
  change GlobalGaugeKernel.centralEmbedding z * g = g * GlobalGaugeKernel.centralEmbedding z
  apply Prod.ext
  · apply Subtype.ext
    change ((GlobalGaugeKernel.centralEmbedding z).1 : GlobalGaugeKernel.Mat3) *
        (g.1 : GlobalGaugeKernel.Mat3) =
      (g.1 : GlobalGaugeKernel.Mat3) *
        ((GlobalGaugeKernel.centralEmbedding z).1 : GlobalGaugeKernel.Mat3)
    rw [GlobalGaugeKernel.centralEmbedding_colour]
    simp
  · apply Prod.ext
    · apply Subtype.ext
      change ((GlobalGaugeKernel.centralEmbedding z).2.1 : Operations.SourceSpinCorner.Mat2) *
          (g.2.1 : Operations.SourceSpinCorner.Mat2) =
        (g.2.1 : Operations.SourceSpinCorner.Mat2) *
          ((GlobalGaugeKernel.centralEmbedding z).2.1 : Operations.SourceSpinCorner.Mat2)
      rw [GlobalGaugeKernel.centralEmbedding_weak]
      simp
    · exact mul_comm _ _

theorem effectiveUnitary_quotientMap (g : GaugeGroup) :
    effectiveUnitaryRepresentation (quotientMap g) = unitaryRepresentation g :=
  SourceGaugeUnitary.effectiveUnitaryRepresentation_mk g

theorem quotient_eq_iff_unitary (g h : GaugeGroup) :
    quotientMap g = quotientMap h ↔ unitaryRepresentation g = unitaryRepresentation h := by
  constructor
  · intro he
    exact (effectiveUnitary_quotientMap g).symm.trans
      ((congrArg effectiveUnitaryRepresentation he).trans (effectiveUnitary_quotientMap h))
  · intro he
    apply SourceGaugeUnitary.effectiveUnitaryRepresentation_injective
    exact (effectiveUnitary_quotientMap g).trans
      (he.trans (effectiveUnitary_quotientMap h).symm)

theorem unitary_eq_iff_central_difference (g h : GaugeGroup) :
    unitaryRepresentation g = unitaryRepresentation h ↔ g * h⁻¹ ∈ centralSix :=
  (mapped_mul_inv_eq_one_iff unitaryRepresentation g h).symm.trans
    (unitary_eq_one_iff (g * h⁻¹))

/-- Equality of actual transitions is precisely a diagonal sixth-root change of lift. -/
theorem unitary_eq_iff_central_relift (g h : GaugeGroup) :
    unitaryRepresentation g = unitaryRepresentation h ↔
      ∃ z : GlobalGaugeKernel.sixthRoots, GlobalGaugeKernel.centralEmbedding z * h = g := by
  constructor
  · intro he
    obtain ⟨z, hz⟩ := (centralSix_iff_sixthRoot _).mp
      ((unitary_eq_iff_central_difference g h).mp he)
    refine ⟨z, ?_⟩
    rw [hz, mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨z, rfl⟩
    exact (unitaryRepresentation.map_mul (GlobalGaugeKernel.centralEmbedding z) h).trans
      ((congrArg (fun U : MatterUnitary => U * unitaryRepresentation h) (unitary_central z)).trans
        (one_mul (unitaryRepresentation h)))

section Overlaps

variable {ι X : Type*}

/-- The same phase coordinate is shared by every matter role. -/
abbrev LiftData (ι X : Type*) := ι → ι → X → GaugeGroup

def quotientTransition (g : LiftData ι X) (i j : ι) (x : X) : EffectiveGroup :=
  quotientMap (g i j x)

/-- This transition sends chart-j components into chart-i components. -/
def unitaryTransition (g : LiftData ι X) (i j : ι) (x : X) : MatterUnitary :=
  unitaryRepresentation (g i j x)

def tripleDefect (g : LiftData ι X) (i j k : ι) (x : X) : GaugeGroup :=
  g i j x * g j k x * (g i k x)⁻¹

def CentralDefects (U : ι → Set X) (g : LiftData ι X) : Prop :=
  ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → tripleDefect g i j k x ∈ centralSix

theorem tripleDefect_mem_iff (g : LiftData ι X) (i j k : ι) (x : X) :
    tripleDefect g i j k x ∈ centralSix ↔
      unitaryTransition g i j x * unitaryTransition g j k x = unitaryTransition g i k x := by
  rw [← unitary_eq_one_iff]
  simp only [tripleDefect, unitaryTransition, map_mul, map_inv, mul_inv_eq_one]

theorem tripleDefect_phase (g : LiftData ι X) (i j k : ι) (x : X) :
    (tripleDefect g i j k x).2.2 =
      (g i j x).2.2 * (g j k x).2.2 * ((g i k x).2.2)⁻¹ := rfl

/-- The three factor defects are correlated by this single phase; none
of them is required to vanish separately. -/
theorem tripleDefect_shared_characters (g : LiftData ι X) (i j k : ι) (x : X) :
    let d := tripleDefect g i j k x
    d ∈ centralSix ↔ d.2.2 ^ 6 = 1 ∧
      (d.1 : GlobalGaugeKernel.Mat3) = (d.2.2 : ℂ) ^ 2 • (1 : GlobalGaugeKernel.Mat3) ∧
      (d.2.1 : Operations.SourceSpinCorner.Mat2) =
        (d.2.2 : ℂ) ^ 3 • (1 : Operations.SourceSpinCorner.Mat2) := by
  dsimp only
  rw [← unitary_eq_one_iff, unitary_eq_one_iff_end]
  exact SourceGaugeTransport.source_kernel_iff _ _ _

/-- A triple defect may be nonidentity in the product group: exactly six
central possibilities are invisible on the full matter carrier. -/
theorem tripleDefect_iff_six_powers (g : LiftData ι X) (i j k : ι) (x : X) :
    tripleDefect g i j k x ∈ centralSix ↔
      ∃ n : ℕ, n < 6 ∧ GlobalGaugeKernel.generator ^ n = tripleDefect g i j k x := by
  rw [← unitary_eq_one_iff, unitary_eq_one_iff_end,
    SourceGaugeTransport.kernel_iff_generator_power]

theorem centralDefects_iff_unitaryCocycle (U : ι → Set X) (g : LiftData ι X) :
    CentralDefects U g ↔ CocycleOn U (unitaryTransition g) := by
  unfold CentralDefects CocycleOn
  simp only [tripleDefect_mem_iff]

/-- Faithfulness of the already constructed quotient gives the converse. -/
theorem effectiveCocycle_iff_unitaryCocycle (U : ι → Set X)
    (q : ι → ι → X → EffectiveGroup) :
    CocycleOn U q ↔
      CocycleOn U (fun i j x => effectiveUnitaryRepresentation (q i j x)) :=
  map_cocycle_iff effectiveUnitaryRepresentation
    SourceGaugeUnitary.effectiveUnitaryRepresentation_injective U q

theorem quotientCocycle_iff_unitaryCocycle (U : ι → Set X) (g : LiftData ι X) :
    CocycleOn U (quotientTransition g) ↔ CocycleOn U (unitaryTransition g) := by
  have ht : (fun i j x => effectiveUnitaryRepresentation (quotientTransition g i j x)) =
      unitaryTransition g := by
    funext i j x
    exact effectiveUnitary_quotientMap (g i j x)
  exact (effectiveCocycle_iff_unitaryCocycle U (quotientTransition g)).trans
    (Iff.of_eq (congrArg (CocycleOn U) ht))

theorem centralDefects_iff_quotientCocycle (U : ι → Set X) (g : LiftData ι X) :
    CentralDefects U g ↔ CocycleOn U (quotientTransition g) :=
  (centralDefects_iff_unitaryCocycle U g).trans
    (quotientCocycle_iff_unitaryCocycle U g).symm

def centralRelift (z : ι → ι → X → GlobalGaugeKernel.sixthRoots)
    (g : LiftData ι X) : LiftData ι X :=
  fun i j x => GlobalGaugeKernel.centralEmbedding (z i j x) * g i j x

@[simp] theorem centralRelift_unitary (z : ι → ι → X → GlobalGaugeKernel.sixthRoots)
    (g : LiftData ι X) (i j : ι) (x : X) :
    unitaryTransition (centralRelift z g) i j x = unitaryTransition g i j x := by
  simp only [unitaryTransition, centralRelift, map_mul, unitary_central, one_mul]

@[simp] theorem centralRelift_quotient (z : ι → ι → X → GlobalGaugeKernel.sixthRoots)
    (g : LiftData ι X) (i j : ι) (x : X) :
    quotientTransition (centralRelift z g) i j x = quotientTransition g i j x := by
  apply (quotient_eq_iff_unitary _ _).mpr
  exact centralRelift_unitary z g i j x

theorem centralRelift_defects_iff (U : ι → Set X)
    (z : ι → ι → X → GlobalGaugeKernel.sixthRoots) (g : LiftData ι X) :
    CentralDefects U (centralRelift z g) ↔ CentralDefects U g := by
  rw [centralDefects_iff_unitaryCocycle, centralDefects_iff_unitaryCocycle]
  simp only [CocycleOn, centralRelift_unitary]

/-- The six blocks are evaluated with one and the same phase z. -/
theorem transition_common_phase (g3 : GlobalGaugeKernel.SU3)
    (gL : Operations.SourceSpinCornerGroup.SU2) (z : Circle) (v : FullMatter) :
    let x := SourceGaugeTransport.coordinates v
    SourceGaugeTransport.coordinates (unitaryRepresentation (g3, gL, z) v) =
      ( (((z : ℂ) • ((g3 : GlobalGaugeKernel.Mat3) ⊗ₖ
            (gL : Operations.SourceSpinCorner.Mat2))).mulVec x.1.1,
          (((z : ℂ) ^ 3)⁻¹ • (gL : Operations.SourceSpinCorner.Mat2)).mulVec x.1.2),
        ( ((((z : ℂ) ^ 4) • (g3 : GlobalGaugeKernel.Mat3)).mulVec x.2.1.1,
            (((z : ℂ) ^ 2)⁻¹ • (g3 : GlobalGaugeKernel.Mat3)).mulVec x.2.1.2),
          ((1 : GlobalGaugeKernel.Mat1).mulVec x.2.2.1,
            (((z : ℂ) ^ 6)⁻¹ • (1 : GlobalGaugeKernel.Mat1)).mulVec x.2.2.2))) := by
  exact (SourceGaugeTransport.coordinates_intertwines (g3, gL, z) v).trans
    (SourceGaugeUnitary.coordinate_action_blocks (g3, gL, z)
      (SourceGaugeTransport.coordinates v))

/-- The realized subgroup excludes arbitrary unitary operators outside the
specified gauge representation. -/
abbrev RealizedUnitary := effectiveUnitaryRepresentation.range

def effectiveEquivRealized : EffectiveGroup ≃* RealizedUnitary :=
  MonoidHom.ofInjective SourceGaugeUnitary.effectiveUnitaryRepresentation_injective

def quotientFromRealized (t : ι → ι → X → RealizedUnitary) : ι → ι → X → EffectiveGroup :=
  fun i j x => effectiveEquivRealized.symm (t i j x)

@[simp] theorem quotientFromRealized_action (t : ι → ι → X → RealizedUnitary)
    (i j : ι) (x : X) :
    effectiveUnitaryRepresentation (quotientFromRealized t i j x) = (t i j x : MatterUnitary) :=
  MonoidHom.apply_ofInjective_symm SourceGaugeUnitary.effectiveUnitaryRepresentation_injective _

theorem realizedCocycle_iff (U : ι → Set X) (t : ι → ι → X → RealizedUnitary) :
    CocycleOn U (quotientFromRealized t) ↔
      CocycleOn U (fun i j x => (t i j x : MatterUnitary)) := by
  simpa only [quotientFromRealized_action] using
    effectiveCocycle_iff_unitaryCocycle U (quotientFromRealized t)

theorem quotientFromRealized_unique (t : ι → ι → X → RealizedUnitary)
    (q : ι → ι → X → EffectiveGroup)
    (hq : ∀ i j x, effectiveUnitaryRepresentation (q i j x) = (t i j x : MatterUnitary)) :
    q = quotientFromRealized t := by
  funext i j x
  apply SourceGaugeUnitary.effectiveUnitaryRepresentation_injective
  exact (hq i j x).trans (quotientFromRealized_action t i j x).symm

def CompatibleSections (U : ι → Set X) (t : ι → ι → X → MatterUnitary)
    (s : ι → X → FullMatter) : Prop :=
  ∀ i j x, x ∈ U i → x ∈ U j → s i x = t i j x (s j x)

theorem transition_two_routes {U : ι → Set X} {g : LiftData ι X}
    (hg : CentralDefects U g) (i j k : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) (v : FullMatter) :
    unitaryTransition g i j x (unitaryTransition g j k x v) =
      unitaryTransition g i k x v :=
  congrArg (fun T : MatterUnitary => T v)
    ((centralDefects_iff_unitaryCocycle U g).mp hg i j k x hi hj hk)

theorem compatibleSections_passive {U : ι → Set X}
    {t : ι → ι → X → MatterUnitary} {s : ι → X → FullMatter}
    (hs : CompatibleSections U t s) (i j : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) :
    s j x = (t i j x).symm (s i x) := by
  rw [hs i j x hi hj]
  simp

theorem compatibleSections_inner {U : ι → Set X}
    {t : ι → ι → X → MatterUnitary} {s r : ι → X → FullMatter}
    (hs : CompatibleSections U t s) (hr : CompatibleSections U t r)
    (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
    inner ℂ (s i x) (r i x) = inner ℂ (s j x) (r j x) := by
  rw [hs i j x hi hj, hr i j x hi hj]
  exact (t i j x).inner_map_map _ _

theorem compatibleSections_norm {U : ι → Set X}
    {t : ι → ι → X → MatterUnitary} {s : ι → X → FullMatter}
    (hs : CompatibleSections U t s) (i j : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) : ‖s i x‖ = ‖s j x‖ := by
  rw [hs i j x hi hj]
  exact (t i j x).norm_map _

theorem centralRelift_sections_iff (U : ι → Set X)
    (z : ι → ι → X → GlobalGaugeKernel.sixthRoots) (g : LiftData ι X)
    (s : ι → X → FullMatter) :
    CompatibleSections U (unitaryTransition (centralRelift z g)) s ↔
      CompatibleSections U (unitaryTransition g) s := by
  simp only [CompatibleSections, centralRelift_unitary]

end Overlaps

end GeneratedFoundations.Physical.SourceGaugeCocycle
