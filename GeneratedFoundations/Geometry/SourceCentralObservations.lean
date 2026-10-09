module

public import GeneratedFoundations.Operations.SourceProcessAlgebra
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Continuous observations on the central quotient of source operations

The actual matrix topology makes the generated operation group compact.
Its two-element centre is closed, so the group quotient is compact Hausdorff.
Continuous functions invariant under the central sign descend uniquely to
this quotient, and pullback is an isometric star-algebra isomorphism onto
the invariant algebra. These observations identify exactly the two central
translates of each operation. Only central translation is averaged here;
conjugation invariance is not imposed.
-/

@[expose] public section

noncomputable section

open Topology
open scoped ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCorner (Mat2)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Operations.SourceProcessAlgebra
open GeneratedFoundations.Geometry.SourceSpinCentre

namespace GeneratedFoundations.Geometry.SourceCentralObservations

/-- Multiplication and inversion retain the topology of the original matrices. -/
instance sourceGroup_isTopologicalGroup : IsTopologicalGroup SU2 where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : SU2 × SU2 => (p.1 : Mat2) * (p.2 : Mat2))
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun U : SU2 => (U : Mat2).conjTranspose)
    exact continuous_subtype_val.matrix_conjTranspose

instance centre_isClosed : IsClosed (Subgroup.center SU2 : Set SU2) := by
  rw [centre_eq_pair]
  exact ((Set.finite_singleton negativeIdentity).insert (1 : SU2)).isClosed

theorem centralQuotient_compact : CompactSpace CentralQuotient := inferInstance

theorem centralQuotient_hausdorff : T2Space CentralQuotient := inferInstance

def quotientContinuous : C(SU2, CentralQuotient) :=
  ⟨quotientMap, QuotientGroup.continuous_mk⟩

theorem quotientContinuous_isQuotientMap : IsQuotientMap quotientContinuous :=
  QuotientGroup.isQuotientMap_mk (Subgroup.center SU2)

theorem quotientContinuous_surjective : Function.Surjective quotientContinuous :=
  quotientContinuous_isQuotientMap.surjective

theorem quotient_negative (U : SU2) :
    quotientContinuous (negativeIdentity * U) = quotientContinuous U :=
  (quotientMap_eq_iff _ _).mpr (Or.inr rfl)

def centralTranslation : C(SU2, SU2) :=
  ⟨fun U => negativeIdentity * U, continuous_const.mul continuous_id⟩

@[simp] theorem centralTranslation_twice (U : SU2) :
    centralTranslation (centralTranslation U) = U := by
  change negativeIdentity * (negativeIdentity * U) = U
  rw [← mul_assoc, negativeIdentity_sq, one_mul]

def IsCentralInvariant (f : C(SU2, ℂ)) : Prop :=
  ∀ U, f (negativeIdentity * U) = f U

/-- The complete invariant algebra uses every continuous central-invariant observation. -/
def invariantAlgebra : StarSubalgebra ℂ C(SU2, ℂ) where
  carrier := {f | IsCentralInvariant f}
  zero_mem' := by intro U; rfl
  one_mem' := by intro U; rfl
  add_mem' := by
    intro f g hf hg U
    change f (negativeIdentity * U) + g (negativeIdentity * U) = f U + g U
    rw [hf U, hg U]
  mul_mem' := by
    intro f g hf hg U
    change f (negativeIdentity * U) * g (negativeIdentity * U) = f U * g U
    rw [hf U, hg U]
  algebraMap_mem' := by intro c U; rfl
  star_mem' := by
    intro f hf U
    change star (f (negativeIdentity * U)) = star (f U)
    rw [hf U]

@[simp] theorem mem_invariantAlgebra (f : C(SU2, ℂ)) :
    f ∈ invariantAlgebra ↔ IsCentralInvariant f := Iff.rfl

theorem invariant_factorsThrough {f : C(SU2, ℂ)} (hf : IsCentralInvariant f) :
    Function.FactorsThrough f quotientContinuous := by
  intro U V h
  rcases (quotientMap_eq_iff U V).mp h with he | he
  · rw [he]
  · rw [he, hf V]

theorem invariant_iff_factorsThrough (f : C(SU2, ℂ)) :
    IsCentralInvariant f ↔ Function.FactorsThrough f quotientContinuous := by
  refine ⟨invariant_factorsThrough, ?_⟩
  intro h U
  exact h (quotient_negative U)

/-- Descent uses the quotient topology and the proved central fibres. -/
def descend (f : C(SU2, ℂ)) (hf : IsCentralInvariant f) : C(CentralQuotient, ℂ) :=
  quotientContinuous_isQuotientMap.lift f (invariant_factorsThrough hf)

theorem descend_comp (f : C(SU2, ℂ)) (hf : IsCentralInvariant f) :
    (descend f hf).comp quotientContinuous = f :=
  quotientContinuous_isQuotientMap.lift_comp f (invariant_factorsThrough hf)

@[simp] theorem descend_apply (f : C(SU2, ℂ)) (hf : IsCentralInvariant f) (U : SU2) :
    descend f hf (quotientContinuous U) = f U :=
  congrArg (fun g : C(SU2, ℂ) => g U) (descend_comp f hf)

theorem descend_unique (f : C(SU2, ℂ)) (hf : IsCentralInvariant f)
    (g : C(CentralQuotient, ℂ)) (hg : g.comp quotientContinuous = f) :
    g = descend f hf := by
  ext q
  obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
  rw [descend_apply]
  exact congrArg (fun k : C(SU2, ℂ) => k U) hg

def pullback (g : C(CentralQuotient, ℂ)) : invariantAlgebra :=
  ⟨g.comp quotientContinuous, by
    intro U
    change g (quotientContinuous (negativeIdentity * U)) = g (quotientContinuous U)
    rw [quotient_negative]⟩

@[simp] theorem pullback_apply (g : C(CentralQuotient, ℂ)) (U : SU2) :
    (pullback g : C(SU2, ℂ)) U = g (quotientContinuous U) := rfl

theorem pullback_descend (f : invariantAlgebra) :
    pullback (descend f.val f.property) = f := by
  apply Subtype.ext
  exact descend_comp f.val f.property

theorem descend_pullback (g : C(CentralQuotient, ℂ)) :
    descend (pullback g).val (pullback g).property = g := by
  exact (descend_unique (pullback g).val (pullback g).property g rfl).symm

/-- All continuous functions on the actual quotient, with their full algebraic structure. -/
def descentStarAlgEquiv : invariantAlgebra ≃⋆ₐ[ℂ] C(CentralQuotient, ℂ) where
  toFun f := descend f.val f.property
  invFun := pullback
  left_inv := pullback_descend
  right_inv := descend_pullback
  map_add' f g := by
    ext q
    obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
    simp only [ContinuousMap.add_apply]
    rfl
  map_mul' f g := by
    ext q
    obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
    simp only [ContinuousMap.mul_apply]
    rfl
  map_star' f := by
    ext q
    obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
    simp only [ContinuousMap.star_apply]
    rfl
  map_smul' c f := by
    ext q
    obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
    simp only [ContinuousMap.smul_apply]
    rfl

theorem pullback_norm (g : C(CentralQuotient, ℂ)) :
    ‖(pullback g : C(SU2, ℂ))‖ = ‖g‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro U
    exact g.norm_coe_le_norm (quotientContinuous U)
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro q
    obtain ⟨U, rfl⟩ := quotientContinuous_surjective q
    exact (pullback g : C(SU2, ℂ)).norm_coe_le_norm U

theorem descent_norm (f : invariantAlgebra) : ‖descentStarAlgEquiv f‖ = ‖f.val‖ := by
  have h := pullback_norm (descend f.val f.property)
  rw [pullback_descend] at h
  exact h.symm

/-- Distinct central orbits are separated by a continuous invariant source observation. -/
theorem invariant_separates_orbits {U V : SU2}
    (h : quotientContinuous U ≠ quotientContinuous V) :
    ∃ f : invariantAlgebra, f.val U ≠ f.val V := by
  obtain ⟨g, hg, hne⟩ := separatesPoints_continuous_of_t35Space h
  let G : C(CentralQuotient, ℂ) := ⟨fun q => (g q : ℂ), Complex.continuous_ofReal.comp hg⟩
  refine ⟨pullback G, ?_⟩
  change (g (quotientContinuous U) : ℂ) ≠ (g (quotientContinuous V) : ℂ)
  exact fun he => hne (Complex.ofReal_injective he)

/-- Complete invariant observations lose precisely the central sign and no other information. -/
theorem observations_equal_iff (U V : SU2) :
    (∀ f : invariantAlgebra, f.val U = f.val V) ↔
      quotientContinuous U = quotientContinuous V := by
  constructor
  · intro h
    by_contra hq
    obtain ⟨f, hf⟩ := invariant_separates_orbits hq
    exact hf (h f)
  · intro h f
    exact invariant_factorsThrough f.property h

theorem observations_equal_iff_central_pair (U V : SU2) :
    (∀ f : invariantAlgebra, f.val U = f.val V) ↔
      U = V ∨ U = negativeIdentity * V := by
  rw [observations_equal_iff]
  exact quotientMap_eq_iff U V

/-- The invariant observations remain in the completion of the generated coherent responses. -/
theorem invariant_mem_processCompletion {b : ℝ} (hb : 0 < b) (f : invariantAlgebra) :
    f.val ∈ (processAlgebra hb).topologicalClosure := by
  rw [processAlgebra_complete]
  exact StarSubalgebra.mem_top

def centralAverage (f : C(SU2, ℂ)) : C(SU2, ℂ) :=
  (1 / 2 : ℂ) • (f + f.comp centralTranslation)

@[simp] theorem centralAverage_apply (f : C(SU2, ℂ)) (U : SU2) :
    centralAverage f U = (f U + f (negativeIdentity * U)) / 2 := by
  change (1 / 2 : ℂ) * (f U + f (negativeIdentity * U)) = _
  ring

theorem centralAverage_invariant (f : C(SU2, ℂ)) :
    IsCentralInvariant (centralAverage f) := by
  intro U
  rw [centralAverage_apply, centralAverage_apply, ← mul_assoc, negativeIdentity_sq, one_mul]
  ring

theorem centralAverage_of_invariant {f : C(SU2, ℂ)} (hf : IsCentralInvariant f) :
    centralAverage f = f := by
  ext U
  rw [centralAverage_apply, hf U]
  ring

theorem centralAverage_fixed_iff (f : C(SU2, ℂ)) :
    centralAverage f = f ↔ IsCentralInvariant f := by
  refine ⟨fun h => ?_, centralAverage_of_invariant⟩
  rw [← h]
  exact centralAverage_invariant f

theorem centralAverage_idempotent (f : C(SU2, ℂ)) :
    centralAverage (centralAverage f) = centralAverage f :=
  centralAverage_of_invariant (centralAverage_invariant f)

theorem centralAverage_one : centralAverage 1 = 1 := by
  apply centralAverage_of_invariant
  intro U
  rfl

theorem centralAverage_add (f g : C(SU2, ℂ)) :
    centralAverage (f + g) = centralAverage f + centralAverage g := by
  ext U
  simp only [centralAverage_apply, ContinuousMap.add_apply]
  ring

theorem centralAverage_smul (c : ℂ) (f : C(SU2, ℂ)) :
    centralAverage (c • f) = c • centralAverage f := by
  ext U
  simp only [centralAverage_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem centralAverage_invariant_mul (g : invariantAlgebra) (f : C(SU2, ℂ)) :
    centralAverage (g.val * f) = g.val * centralAverage f := by
  ext U
  simp only [centralAverage_apply, ContinuousMap.mul_apply]
  rw [g.property U]
  ring

theorem centralAverage_norm_le (f : C(SU2, ℂ)) : ‖centralAverage f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro U
  calc
    ‖centralAverage f U‖ = ‖f U + f (negativeIdentity * U)‖ / 2 := by
      rw [centralAverage_apply, norm_div]
      norm_num
    _ ≤ (‖f U‖ + ‖f (negativeIdentity * U)‖) / 2 :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (‖f‖ + ‖f‖) / 2 :=
      div_le_div_of_nonneg_right
        (add_le_add (f.norm_coe_le_norm U) (f.norm_coe_le_norm (negativeIdentity * U)))
        (by norm_num)
    _ = ‖f‖ := by ring

/-- Averaging preserves pointwise nonnegative real responses. -/
theorem centralAverage_nonnegative (f : C(SU2, ℂ))
    (hf : ∀ U, 0 ≤ (f U).re ∧ (f U).im = 0) (U : SU2) :
    0 ≤ (centralAverage f U).re ∧ (centralAverage f U).im = 0 := by
  rw [centralAverage_apply]
  constructor
  · change 0 ≤ ((f U + f (negativeIdentity * U)) / ((2 : ℝ) : ℂ)).re
    rw [Complex.div_ofReal_re, Complex.add_re]
    exact div_nonneg (add_nonneg (hf U).1 (hf (negativeIdentity * U)).1)
      (show (0 : ℝ) ≤ 2 by norm_num)
  · change ((f U + f (negativeIdentity * U)) / ((2 : ℝ) : ℂ)).im = 0
    rw [Complex.div_ofReal_im, Complex.add_im, (hf U).2, (hf (negativeIdentity * U)).2]
    norm_num

end GeneratedFoundations.Geometry.SourceCentralObservations
