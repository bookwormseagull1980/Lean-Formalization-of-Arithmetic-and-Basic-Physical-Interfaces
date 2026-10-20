module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Exact overlap laws for an effective action

The action is retained when a product-group lift is replaced by its quotient
class. An overlap cocycle can therefore hold even when the lifts have a
nonidentity triple defect. The defect must belong to the actual action
kernel. Faithfulness of the induced action gives the converse and the unique
effective transition.

These are comparison theorems for a specified group action. Each generated
branch separately constructs its carrier and proves that action's kernel.
-/

@[expose] public section

namespace GeneratedFoundations.Geometry.EffectiveActionCocycle

variable {ι X : Type*}

def CocycleOn {G : Type*} [Mul G] (U : ι → Set X) (t : ι → ι → X → G) : Prop :=
  ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → t i j x * t j k x = t i k x

theorem mapped_mul_inv_eq_one_iff {G H : Type*} [Group G] [Group H]
    (ρ : G →* H) (g h : G) : ρ (g * h⁻¹) = 1 ↔ ρ g = ρ h := by
  rw [map_mul, map_inv, mul_inv_eq_one]

theorem map_cocycle_iff {G H : Type*} [Monoid G] [Monoid H]
    (ρ : G →* H) (hρ : Function.Injective ρ) (U : ι → Set X)
    (q : ι → ι → X → G) : CocycleOn U q ↔ CocycleOn U (fun i j x => ρ (q i j x)) := by
  constructor
  · intro h i j k x hi hj hk
    exact (ρ.map_mul (q i j x) (q j k x)).symm.trans (congrArg ρ (h i j k x hi hj hk))
  · intro h i j k x hi hj hk
    exact hρ ((ρ.map_mul (q i j x) (q j k x)).trans (h i j k x hi hj hk))

theorem cocycleOn_self {G : Type*} [Group G] {U : ι → Set X}
    {t : ι → ι → X → G} (ht : CocycleOn U t) (i : ι) (x : X) (hi : x ∈ U i) :
    t i i x = 1 := by
  exact mul_left_cancel ((ht i i i x hi hi hi).trans (mul_one (t i i x)).symm)

theorem cocycleOn_inverse {G : Type*} [Group G] {U : ι → Set X}
    {t : ι → ι → X → G} (ht : CocycleOn U t) (i j : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) : t j i x = (t i j x)⁻¹ := by
  have he : t i j x * t j i x = t i j x * (t i j x)⁻¹ := by
    rw [ht i j i x hi hj hi, cocycleOn_self ht i x hi, mul_inv_cancel]
  exact mul_left_cancel he

section Action

variable {G H : Type*} [Group G] [Group H] (ρ : G →* H)

def tripleDefect (g : ι → ι → X → G) (i j k : ι) (x : X) : G :=
  g i j x * g j k x * (g i k x)⁻¹

theorem tripleDefect_mem_iff (g : ι → ι → X → G) (i j k : ι) (x : X) :
    tripleDefect g i j k x ∈ ρ.ker ↔
      ρ (g i j x) * ρ (g j k x) = ρ (g i k x) := by
  rw [MonoidHom.mem_ker]
  simp only [tripleDefect, map_mul, map_inv, mul_inv_eq_one]

theorem kernelDefects_iff_actionCocycle (U : ι → Set X) (g : ι → ι → X → G) :
    (∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      tripleDefect g i j k x ∈ ρ.ker) ↔
        CocycleOn U (fun i j x => ρ (g i j x)) := by
  unfold CocycleOn
  simp only [tripleDefect_mem_iff]

theorem quotient_eq_iff_action (g h : G) :
    QuotientGroup.mk' ρ.ker g = QuotientGroup.mk' ρ.ker h ↔ ρ g = ρ h := by
  constructor
  · intro he
    exact congrArg (QuotientGroup.kerLift ρ) he
  · intro he
    exact QuotientGroup.kerLift_injective ρ he

theorem quotientCocycle_iff_actionCocycle (U : ι → Set X) (g : ι → ι → X → G) :
    CocycleOn U (fun i j x => QuotientGroup.mk' ρ.ker (g i j x)) ↔
      CocycleOn U (fun i j x => ρ (g i j x)) := by
  have he := map_cocycle_iff (QuotientGroup.kerLift ρ)
    (QuotientGroup.kerLift_injective ρ) U
    (fun i j x => QuotientGroup.mk' ρ.ker (g i j x))
  exact he

theorem kernel_relift (c g : G) (hc : c ∈ ρ.ker) : ρ (c * g) = ρ g := by
  rw [map_mul, MonoidHom.mem_ker.mp hc, one_mul]

theorem quotient_relift (c g : G) (hc : c ∈ ρ.ker) :
    QuotientGroup.mk' ρ.ker (c * g) = QuotientGroup.mk' ρ.ker g :=
  (quotient_eq_iff_action ρ _ _).mpr (kernel_relift ρ c g hc)

end Action

section RealizedImage

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- A comparison realization is classified by the same complete operator
image. These premises describe the comparison class, not the generated root. -/
noncomputable def realizationEquiv (source : G →* H) (ρ : K →* H)
    (hin : ∀ k, ρ k ∈ source.range) (hfaithful : Function.Injective ρ)
    (hcomplete : Function.Surjective (ρ.codRestrict source.range hin)) :
    K ≃* source.range :=
  MulEquiv.ofBijective (ρ.codRestrict source.range hin)
    ⟨fun _ _ h => hfaithful (congrArg Subtype.val h), hcomplete⟩

@[simp] theorem realizationEquiv_apply (source : G →* H) (ρ : K →* H)
    (hin : ∀ k, ρ k ∈ source.range) (hfaithful : Function.Injective ρ)
    (hcomplete : Function.Surjective (ρ.codRestrict source.range hin)) (k : K) :
    (realizationEquiv source ρ hin hfaithful hcomplete k : H) = ρ k := rfl

theorem realizationEquiv_unique (source : G →* H) (ρ : K →* H)
    (hin : ∀ k, ρ k ∈ source.range) (hfaithful : Function.Injective ρ)
    (hcomplete : Function.Surjective (ρ.codRestrict source.range hin))
    (e : K ≃* source.range) (he : ∀ k, (e k : H) = ρ k) :
    e = realizationEquiv source ρ hin hfaithful hcomplete := by
  apply MulEquiv.ext
  intro k
  exact Subtype.ext (he k)

end RealizedImage

end GeneratedFoundations.Geometry.EffectiveActionCocycle
