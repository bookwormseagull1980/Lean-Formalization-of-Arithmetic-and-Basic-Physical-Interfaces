module

public import GeneratedFoundations.Physical.SourceGaugeTransport
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The effective global group on the source matter carrier

The complete source representation has the six-element central kernel
computed from all matter blocks. Its quotient acts faithfully on the
same sixteen-dimensional carrier. The isomorphism below identifies the
quotient with the group of invertible operators actually realized by
that representation; it does not assert a separate bundle trivialization.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceGlobalGaugeGroup

open SourceChiralCarrier

abbrev GaugeGroup := GlobalGaugeKernel.GaugeGroup

/-- Each group element acts invertibly; its inverse is the action of the inverse element. -/
def unitRepresentation : GaugeGroup →* (Module.End ℂ FullMatter)ˣ :=
  SourceGaugeTransport.representation.toHomUnits

@[simp] theorem unitRepresentation_val (g : GaugeGroup) :
    (unitRepresentation g : Module.End ℂ FullMatter) =
      SourceGaugeTransport.representation g := rfl

def centralSix : Subgroup GaugeGroup := Subgroup.zpowers GlobalGaugeKernel.generator

theorem unitRepresentation_kernel : unitRepresentation.ker = centralSix := by
  rw [unitRepresentation, MonoidHom.ker_toHomUnits]
  exact SourceGaugeTransport.kernel_eq_zpowers

instance centralSix_normal : centralSix.Normal := by
  rw [← unitRepresentation_kernel]
  infer_instance

theorem centralSix_card : Nat.card centralSix = 6 := by
  rw [centralSix, Nat.card_zpowers, GlobalGaugeKernel.generator_order]

/-- The quotient by the displayed diagonal central subgroup of order six. -/
abbrev EffectiveGroup := GaugeGroup ⧸ centralSix

def quotientToKernel : EffectiveGroup ≃* GaugeGroup ⧸ unitRepresentation.ker :=
  QuotientGroup.quotientMulEquivOfEq unitRepresentation_kernel.symm

def effectiveUnits : EffectiveGroup →* (Module.End ℂ FullMatter)ˣ :=
  (QuotientGroup.kerLift unitRepresentation).comp quotientToKernel.toMonoidHom

def effectiveRepresentation : EffectiveGroup →* Module.End ℂ FullMatter :=
  (Units.coeHom (Module.End ℂ FullMatter)).comp effectiveUnits

@[simp] theorem effectiveUnits_mk (g : GaugeGroup) :
    effectiveUnits (QuotientGroup.mk' centralSix g) = unitRepresentation g := by
  rfl

@[simp] theorem effectiveRepresentation_mk (g : GaugeGroup) :
    effectiveRepresentation (QuotientGroup.mk' centralSix g) =
      SourceGaugeTransport.representation g := rfl

theorem effectiveUnits_injective : Function.Injective effectiveUnits :=
  (QuotientGroup.kerLift_injective unitRepresentation).comp quotientToKernel.injective

theorem effectiveRepresentation_injective : Function.Injective effectiveRepresentation := by
  intro x y h
  apply effectiveUnits_injective
  apply Units.ext
  exact h

/-- The abstract quotient and the realized group of source operators are isomorphic. -/
def effectiveGroupEquivRange : EffectiveGroup ≃* unitRepresentation.range :=
  quotientToKernel.trans (QuotientGroup.quotientKerEquivRange unitRepresentation)

theorem effectiveGroupEquivRange_mk (g : GaugeGroup) :
    (effectiveGroupEquivRange (QuotientGroup.mk' centralSix g) :
      (Module.End ℂ FullMatter)ˣ) = unitRepresentation g := rfl

theorem effectiveRepresentation_unique
    (ρ : EffectiveGroup →* Module.End ℂ FullMatter)
    (hρ : ∀ g, ρ (QuotientGroup.mk' centralSix g) =
      SourceGaugeTransport.representation g) : ρ = effectiveRepresentation := by
  apply MonoidHom.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro g
  exact hρ g

end GeneratedFoundations.Physical.SourceGlobalGaugeGroup
