module

public import GeneratedFoundations.Physical.SourceChargedQuotient
public import Mathlib.Algebra.Exact.Basic

/-!
# The complete matter exact sequence

The generated matter carrier contains sixteen complex directions. Its unique
neutral source direction is retained as an actual subspace, and the charged
carrier is the canonical quotient by precisely that line. This file packages
the already derived carrier, charge and quotient results as a short exact
sequence and records the quotient universal property.

No direction is deleted by a coordinate convention: the left map is the
subspace inclusion, the right map is the canonical quotient, and exactness
identifies their common middle term intrinsically.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceCompleteMatterExactSequence

open SourceChiralCarrier SourceMatterCharge SourceChargedQuotient

/-- The canonical inclusion of the generated neutral line into complete
matter. -/
def neutralInclusion : neutralLine →ₗ[ℂ] FullMatter :=
  neutralLine.subtype

theorem neutralInclusion_injective : Function.Injective neutralInclusion := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The neutral inclusion and charged quotient are exact at complete matter. -/
theorem neutral_complete_charged_exact :
    Function.Exact neutralInclusion quotientMap := by
  change Function.Exact (Submodule.subtype neutralLine) (Submodule.mkQ neutralLine)
  exact LinearMap.exact_subtype_mkQ neutralLine

theorem neutral_complete_charged_comp_zero :
    quotientMap.comp neutralInclusion = 0 :=
  neutral_complete_charged_exact.linearMap_comp_eq_zero

/-- Any linear response that annihilates the generated neutral line factors
through the charged quotient. -/
def descend {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : FullMatter →ₗ[ℂ] W) (hf : neutralLine ≤ LinearMap.ker f) :
    ChargedMatter →ₗ[ℂ] W :=
  neutralLine.liftQ f hf

theorem descend_comp {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : FullMatter →ₗ[ℂ] W) (hf : neutralLine ≤ LinearMap.ker f) :
    (descend f hf).comp quotientMap = f := by
  exact Submodule.liftQ_mkQ neutralLine f hf

/-- The descended response is uniquely determined by its action on complete
matter. -/
theorem descend_unique {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : FullMatter →ₗ[ℂ] W) (hf : neutralLine ≤ LinearMap.ker f)
    (g : ChargedMatter →ₗ[ℂ] W) (hg : g.comp quotientMap = f) :
    g = descend f hf := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := quotientMap_surjective q
  exact (LinearMap.congr_fun hg x).trans
    (LinearMap.congr_fun (descend_comp f hf).symm x)

theorem descend_existsUnique {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : FullMatter →ₗ[ℂ] W) (hf : neutralLine ≤ LinearMap.ker f) :
    ∃! g : ChargedMatter →ₗ[ℂ] W, g.comp quotientMap = f := by
  refine ⟨descend f hf, descend_comp f hf, ?_⟩
  intro g hg
  exact descend_unique f hf g hg

/-- The complete generated matter carrier, its neutral kernel and its charged
quotient form one canonical short exact sequence with dimensions `1-16-15`. -/
structure Conclusions : Prop where
  neutral_injective : Function.Injective neutralInclusion
  middle_exact : Function.Exact neutralInclusion quotientMap
  charged_surjective : Function.Surjective quotientMap
  neutral_dimension : Module.finrank ℂ neutralLine = 1
  complete_dimension : Module.finrank ℂ FullMatter = 16
  charged_dimension : Module.finrank ℂ ChargedMatter = 15
  quotient_universal : ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
      (f : FullMatter →ₗ[ℂ] W), neutralLine ≤ LinearMap.ker f →
      ∃! g : ChargedMatter →ₗ[ℂ] W, g.comp quotientMap = f

theorem conclusions : Conclusions where
  neutral_injective := neutralInclusion_injective
  middle_exact := neutral_complete_charged_exact
  charged_surjective := quotientMap_surjective
  neutral_dimension := neutralLine_finrank
  complete_dimension := fullMatter_finrank
  charged_dimension := chargedQuotient_finrank
  quotient_universal := by
    intro W _ _ f hf
    exact descend_existsUnique f hf

end GeneratedFoundations.Physical.SourceCompleteMatterExactSequence
