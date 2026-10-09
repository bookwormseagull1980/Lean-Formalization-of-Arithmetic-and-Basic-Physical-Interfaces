module

public import GeneratedFoundations.Geometry.SourceQuotientHilbert
public import GeneratedFoundations.Geometry.SourceCasimirResolvent
public import GeneratedFoundations.Geometry.SourceHeatSemigroup

/-!
# The Casimir on the central source quotient

The quotient operator is the closure of the finite descended matrix
coefficients. Its full domain is exactly the inverse image of the original
source Casimir domain under the actual Haar pullback. The operators
intertwine on that full domain. On the finite core this is the pointwise
second-order expression along the original trace-unit source curves, acting
on the pullbacks of continuous quotient observations.

The original source heat semigroup preserves the entire central fixed
space. Its descent is a strongly continuous self-adjoint contraction
semigroup whose right generator is the negative quotient Casimir, with
exactly the full domain above. No surjectivity or differential identity is
included as a hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology LinearPMap NNReal
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceCentralSpectralProjection
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceCasimirClosure (energy)
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceQuotientCasimir

/-- The algebraic core contains all finite combinations of descended coefficients. -/
def finiteCore : QuotientL2 →ₗ.[ℂ] QuotientL2 :=
  FiniteEigenbasisCore.finiteMultiplier quotientBasis (fun a => energy a.val.1)

def operator : QuotientL2 →ₗ.[ℂ] QuotientL2 := finiteCore.closure

theorem finiteCore_le_operator : finiteCore ≤ operator :=
  FiniteEigenbasisCore.le_closure quotientBasis (fun a => energy a.val.1)

theorem operator_selfAdjoint : IsSelfAdjoint operator :=
  FiniteEigenbasisCore.closure_selfAdjoint quotientBasis (fun a => energy a.val.1)

theorem operator_closed : operator.IsClosed := operator_selfAdjoint.isClosed

theorem operator_domain_dense : Dense (operator.domain : Set QuotientL2) :=
  operator_selfAdjoint.dense_domain

theorem selfAdjoint_extension_unique (T : QuotientL2 →ₗ.[ℂ] QuotientL2)
    (hT : IsSelfAdjoint T) (hcore : finiteCore ≤ T) : T = operator :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique quotientBasis
    (fun a => energy a.val.1) T hT hcore

theorem operator_domain_iff_memℓp (f : QuotientL2) :
    f ∈ operator.domain ↔
      Memℓp (fun a : EvenIndex =>
        (energy a.val.1 : ℂ) * inner ℂ (quotientBasisVector a) f) 2 := by
  simpa only [operator, finiteCore, quotientBasis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_memℓp quotientBasis
      (fun a => energy a.val.1) f

theorem operator_domain_iff_summable (f : QuotientL2) :
    f ∈ operator.domain ↔
      Summable (fun a : EvenIndex =>
        energy a.val.1 ^ 2 * ‖inner ℂ (quotientBasisVector a) f‖ ^ 2) := by
  simpa only [operator, finiteCore, quotientBasis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_summable quotientBasis
      (fun a => energy a.val.1) f

theorem operator_coefficients (f : operator.domain) (a : EvenIndex) :
    inner ℂ (quotientBasisVector a) (operator f) =
      (energy a.val.1 : ℂ) * inner ℂ (quotientBasisVector a) (f : QuotientL2) := by
  simpa only [operator, finiteCore, quotientBasis_apply] using
    FiniteEigenbasisCore.closure_coefficients quotientBasis
      (fun a => energy a.val.1) f a

/-- The full original differential closure preserves the central fixed space. -/
theorem source_operator_preserves_fixed (u : SourceCasimirClosure.operator.domain)
    (hu : averageL2 (u : SourceL2) = (u : SourceL2)) :
    averageL2 (SourceCasimirClosure.operator u) = SourceCasimirClosure.operator u := by
  apply (averageL2_fixed_iff _).mpr
  intro a ha
  rw [coefficients_apply, SourceCasimirClosure.operator_coefficients,
    ← coefficients_apply, (averageL2_fixed_iff _).mp hu a ha, mul_zero]

private theorem pullback_operator_coefficients (f : operator.domain) (a : Index) :
    coefficients (pullbackL2 (operator f)) a =
      (energy a.1 : ℂ) * coefficients (pullbackL2 (f : QuotientL2)) a := by
  rcases Nat.even_or_odd a.1 with ha | ha
  · simp only [coefficients_apply]
    rw [← quotientBasisVector_inner ⟨a, ha⟩,
      ← quotientBasisVector_inner ⟨a, ha⟩, operator_coefficients]
  · rw [pullbackL2_odd_coefficients _ a ha,
      pullbackL2_odd_coefficients _ a ha, mul_zero]

theorem pullback_mem_domain (f : operator.domain) :
    pullbackL2 (f : QuotientL2) ∈ SourceCasimirClosure.operator.domain := by
  apply (SourceCasimirResolvent.operator_domain_iff_memℓp _).mpr
  have h : (fun a : Index => (energy a.1 : ℂ) *
      inner ℂ (basisVector a) (pullbackL2 (f : QuotientL2))) =
      (fun a => coefficients (pullbackL2 (operator f)) a) := by
    funext a
    rw [pullback_operator_coefficients, coefficients_apply]
  rw [h]
  exact lp.memℓp (coefficients (pullbackL2 (operator f)))

/-- Intertwining is on the full closed-operator domain, not only on eigenvectors. -/
theorem pullback_operator (f : operator.domain) :
    pullbackL2 (operator f) =
      SourceCasimirClosure.operator
        ⟨pullbackL2 (f : QuotientL2), pullback_mem_domain f⟩ := by
  apply SourceCompleteCoefficients.eq_of_coefficients_eq
  intro a
  rw [← coefficients_apply, pullback_operator_coefficients,
    coefficients_apply, SourceCasimirClosure.operator_coefficients]

theorem mem_domain_of_pullback (f : QuotientL2)
    (hf : pullbackL2 f ∈ SourceCasimirClosure.operator.domain) : f ∈ operator.domain := by
  let u : SourceCasimirClosure.operator.domain := ⟨pullbackL2 f, hf⟩
  have hu := source_operator_preserves_fixed u (averageL2_pullback f)
  obtain ⟨g, hg, _⟩ := quotientClass_existsUnique (SourceCasimirClosure.operator u) hu
  apply (operator_domain_iff_memℓp f).mpr
  have h : (fun a : EvenIndex =>
      (energy a.val.1 : ℂ) * inner ℂ (quotientBasisVector a) f) =
      (fun a => quotientCoefficients g a) := by
    funext a
    rw [quotientCoefficients_apply, hg, coefficients_apply,
      SourceCasimirClosure.operator_coefficients, quotientBasisVector_inner]
  rw [h]
  exact lp.memℓp (quotientCoefficients g)

/-- The quotient domain is exactly the actual pullback of the original
closed differential domain; there is no hidden regularity assumption. -/
theorem operator_domain_pullback_iff (f : QuotientL2) :
    f ∈ operator.domain ↔ pullbackL2 f ∈ SourceCasimirClosure.operator.domain :=
  ⟨fun hf => pullback_mem_domain ⟨f, hf⟩, mem_domain_of_pullback f⟩

theorem operator_is_restriction (f : QuotientL2)
    (hf : pullbackL2 f ∈ SourceCasimirClosure.operator.domain) :
    ∃! g : QuotientL2,
      pullbackL2 g = SourceCasimirClosure.operator ⟨pullbackL2 f, hf⟩ := by
  refine ⟨operator ⟨f, mem_domain_of_pullback f hf⟩, pullback_operator _, ?_⟩
  intro g hg
  exact pullbackL2.injective
    (hg.trans (pullback_operator ⟨f, mem_domain_of_pullback f hf⟩).symm)

theorem basis_mem_domain (a : EvenIndex) : quotientBasisVector a ∈ operator.domain := by
  apply (operator_domain_pullback_iff _).mpr
  rw [pullbackL2_basisVector]
  exact SourceCasimirClosure.basis_mem_domain a.val

theorem operator_basis (a : EvenIndex) :
    operator ⟨quotientBasisVector a, basis_mem_domain a⟩ =
      (energy a.val.1 : ℂ) • quotientBasisVector a := by
  apply EigenbasisClosure.eq_of_coefficients quotientBasis
  intro j
  rw [quotientBasis_apply, operator_coefficients, inner_smul_right (𝕜 := ℂ),
    orthonormal_iff_ite.mp quotientBasisVector_orthonormal]
  by_cases h : j = a
  · subst j
    rfl
  · simp only [h, ite_false, mul_zero]

/-- The retained degrees are the even degrees of the source operator. -/
theorem even_energy (n : ℕ) : energy (2 * n) = (2 * (n : ℝ) + 1) ^ 2 - 1 := by
  simp only [energy, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Every nonzero eigenvector belongs to an even source degree. -/
theorem eigenvalue_iff (z : ℂ) :
    (∃ f : operator.domain, (f : QuotientL2) ≠ 0 ∧
      operator f = z • (f : QuotientL2)) ↔
      ∃ m : ℕ, Even m ∧ z = (energy m : ℂ) := by
  constructor
  · rintro ⟨f, hf, he⟩
    have hnonzero : ∃ a : EvenIndex,
        inner ℂ (quotientBasisVector a) (f : QuotientL2) ≠ 0 := by
      by_contra h
      push Not at h
      apply hf
      apply EigenbasisClosure.eq_of_coefficients quotientBasis
      intro a
      simpa only [quotientBasis_apply, inner_zero_right] using h a
    obtain ⟨a, ha⟩ := hnonzero
    refine ⟨a.val.1, a.property, ?_⟩
    have hc := operator_coefficients f a
    rw [he, inner_smul_right] at hc
    exact mul_right_cancel₀ ha hc
  · rintro ⟨m, hm, rfl⟩
    let a : EvenIndex := ⟨⟨m, 0, 0⟩, hm⟩
    exact ⟨⟨quotientBasisVector a, basis_mem_domain a⟩,
      quotientBasisVector_orthonormal.ne_zero a, operator_basis a⟩

theorem finiteCore_pullback_mem (f : finiteCore.domain) :
    pullbackL2 (f : QuotientL2) ∈ SourceCasimirClosure.finiteCore.domain := by
  suffices ∀ v ∈ Submodule.span ℂ (Set.range quotientBasis),
      pullbackL2 v ∈ SourceCasimirClosure.finiteCore.domain from this f f.property
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      rw [quotientBasis_apply, pullbackL2_basisVector]
      simpa only [SourceCasimirClosure.finiteCore, SourceCompleteCoefficients.basis_apply] using
        FiniteEigenbasisCore.basis_mem_domain SourceCompleteCoefficients.basis
          (fun a => energy a.1) a.val
  | zero => simpa only [map_zero] using SourceCasimirClosure.finiteCore.domain.zero_mem
  | add u v _ _ hu hv =>
      simpa only [map_add] using SourceCasimirClosure.finiteCore.domain.add_mem hu hv
  | smul c v _ hv =>
      simpa only [map_smul] using SourceCasimirClosure.finiteCore.domain.smul_mem c hv

theorem finiteCore_pullback (f : finiteCore.domain) :
    pullbackL2 (finiteCore f) =
      SourceCasimirClosure.finiteCore
        ⟨pullbackL2 (f : QuotientL2), finiteCore_pullback_mem f⟩ := by
  let u : operator.domain := ⟨f, finiteCore_le_operator.1 f.property⟩
  have hq : finiteCore f = operator u :=
    finiteCore_le_operator.2 (x := f) (y := u) rfl
  have hs := FiniteEigenbasisCore.le_closure SourceCompleteCoefficients.basis
    (fun a => energy a.1)
  rw [hq, pullback_operator]
  exact (hs.2
    (x := ⟨pullbackL2 (f : QuotientL2), finiteCore_pullback_mem f⟩)
    (y := ⟨pullbackL2 (u : QuotientL2), pullback_mem_domain u⟩) rfl).symm

private theorem continuous_invariant_of_pullback (F : C(SU2, ℂ)) (f : QuotientL2)
    (hF : ContinuousMap.toLp 2 sourceHaar ℂ F = pullbackL2 f) : IsCentralInvariant F := by
  apply (centralAverage_fixed_iff F).mp
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) sourceHaar
  rw [← averageL2_toLp, hF, averageL2_pullback]

private theorem descend_toLp_of_pullback (F : C(SU2, ℂ)) (f : QuotientL2)
    (hF : ContinuousMap.toLp 2 sourceHaar ℂ F = pullbackL2 f) :
    ContinuousMap.toLp 2 quotientHaar ℂ
      (descend F (continuous_invariant_of_pullback F f hF)) = f := by
  apply pullbackL2.injective
  rw [pullbackL2_toLp, descend_comp, hF]

/-- Both representatives are genuine continuous quotient observations. The
second-order expression is evaluated on their actual source pullbacks. -/
theorem finiteCore_is_roundCasimir (u : finiteCore.domain) :
    ∃ F H : C(CentralQuotient, ℂ),
      ContinuousMap.toLp 2 quotientHaar ℂ F = (u : QuotientL2) ∧
      ContinuousMap.toLp 2 quotientHaar ℂ H = finiteCore u ∧
      ∀ g : SU2, H (quotientContinuous g) =
        SourceAxisMetric.roundCasimir (F.comp quotientContinuous) g := by
  let v : SourceCasimirClosure.finiteCore.domain :=
    ⟨pullbackL2 (u : QuotientL2), finiteCore_pullback_mem u⟩
  obtain ⟨F, H, hF, hH, hd⟩ := SourceCasimirClosure.finiteCore_is_roundCasimir v
  have hF' : ContinuousMap.toLp 2 sourceHaar ℂ F = pullbackL2 (u : QuotientL2) := hF
  have hH' : ContinuousMap.toLp 2 sourceHaar ℂ H = pullbackL2 (finiteCore u) :=
    hH.trans (finiteCore_pullback u).symm
  refine ⟨descend F (continuous_invariant_of_pullback F _ hF'),
    descend H (continuous_invariant_of_pullback H _ hH'),
    descend_toLp_of_pullback F _ hF', descend_toLp_of_pullback H _ hH', ?_⟩
  intro g
  rw [descend_apply, descend_comp]
  exact hd g

theorem source_heat_preserves_fixed (t : ℝ≥0) (f : SourceL2)
    (hf : averageL2 f = f) :
    averageL2 (SourceHeatSemigroup.heat t f) = SourceHeatSemigroup.heat t f := by
  apply (averageL2_fixed_iff _).mpr
  intro a ha
  rw [coefficients_apply, SourceHeatSemigroup.heat_coefficient,
    ← coefficients_apply, (averageL2_fixed_iff _).mp hf a ha, mul_zero]

def heatValue (t : ℝ≥0) (f : QuotientL2) : QuotientL2 :=
  invariantEquiv.symm
    ⟨SourceHeatSemigroup.heat t (pullbackL2 f),
      source_heat_preserves_fixed t _ (averageL2_pullback f)⟩

private theorem pullback_heatValue (t : ℝ≥0) (f : QuotientL2) :
    pullbackL2 (heatValue t f) = SourceHeatSemigroup.heat t (pullbackL2 f) := by
  change (invariantEquiv (invariantEquiv.symm _) : SourceL2) = _
  rw [invariantEquiv.apply_symm_apply]

def heatLinear (t : ℝ≥0) : QuotientL2 →ₗ[ℂ] QuotientL2 where
  toFun := heatValue t
  map_add' f g := by
    apply pullbackL2.injective
    simp only [pullback_heatValue, map_add]
  map_smul' c f := by
    apply pullbackL2.injective
    simp only [pullback_heatValue, map_smul, RingHom.id_apply]

private theorem heatLinear_norm_le (t : ℝ≥0) (f : QuotientL2) :
    ‖heatLinear t f‖ ≤ ‖f‖ := by
  rw [← pullbackL2.norm_map (heatLinear t f), ← pullbackL2.norm_map f]
  change ‖pullbackL2 (heatValue t f)‖ ≤ _
  rw [pullback_heatValue]
  exact SourceHeatSemigroup.heat_norm_le t _

/-- Descent of the previously constructed original source heat semigroup. -/
def heat (t : ℝ≥0) : QuotientL2 →L[ℂ] QuotientL2 :=
  (heatLinear t).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using heatLinear_norm_le t f)

theorem pullback_heat (t : ℝ≥0) (f : QuotientL2) :
    pullbackL2 (heat t f) = SourceHeatSemigroup.heat t (pullbackL2 f) :=
  pullback_heatValue t f

@[simp] theorem heat_zero (f : QuotientL2) : heat 0 f = f := by
  apply pullbackL2.injective
  rw [pullback_heat, SourceHeatSemigroup.heat_zero]

theorem heat_add (s t : ℝ≥0) (f : QuotientL2) : heat (s + t) f = heat s (heat t f) := by
  apply pullbackL2.injective
  rw [pullback_heat, SourceHeatSemigroup.heat_add, pullback_heat, pullback_heat]

theorem heat_norm_le (t : ℝ≥0) (f : QuotientL2) : ‖heat t f‖ ≤ ‖f‖ :=
  heatLinear_norm_le t f

theorem heat_stronglyContinuous (f : QuotientL2) : Continuous (fun t : ℝ≥0 => heat t f) := by
  apply pullbackL2.comp_continuous_iff.mp
  simpa only [Function.comp_def, pullback_heat] using
    SourceHeatSemigroup.heat_stronglyContinuous (pullbackL2 f)

theorem heat_selfAdjoint (t : ℝ≥0) : IsSelfAdjoint (heat t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (SourceHeatSemigroup.heat_selfAdjoint t)
  change inner ℂ (heat t f) g = inner ℂ f (heat t g)
  rw [← pullbackL2.inner_map_map (heat t f) g,
    ← pullbackL2.inner_map_map f (heat t g), pullback_heat, pullback_heat]
  exact hs (pullbackL2 f) (pullbackL2 g)

theorem heat_basis (t : ℝ≥0) (a : EvenIndex) :
    heat t (quotientBasisVector a) =
      (SourceHeatSemigroup.decay t a.val.1 : ℂ) • quotientBasisVector a := by
  apply pullbackL2.injective
  rw [pullback_heat, pullbackL2_basisVector, SourceHeatSemigroup.heat_basis,
    map_smul, pullbackL2_basisVector]

def HasRightGenerator (f g : QuotientL2) : Prop :=
  Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) • (heat t f - f)) (𝓝[>] 0) (𝓝 g)

theorem rightGenerator_pullback_iff (f g : QuotientL2) :
    HasRightGenerator f g ↔
      SourceHeatSemigroup.HasRightGenerator (pullbackL2 f) (pullbackL2 g) := by
  unfold HasRightGenerator SourceHeatSemigroup.HasRightGenerator
  rw [pullbackL2.isometry.tendsto_nhds_iff]
  simp only [Function.comp_def, map_smul, map_sub, pullback_heat]

/-- The right generator has precisely the complete pulled-back differential
domain and the same sign as on the original source Haar space. -/
theorem rightGenerator_iff (f g : QuotientL2) :
    HasRightGenerator f g ↔ ∃ hf : f ∈ operator.domain, g = -(operator ⟨f, hf⟩) := by
  rw [rightGenerator_pullback_iff, SourceHeatSemigroup.rightGenerator_iff]
  constructor
  · rintro ⟨hf, hg⟩
    refine ⟨mem_domain_of_pullback f hf, ?_⟩
    apply pullbackL2.injective
    rw [map_neg, pullback_operator]
    exact hg
  · rintro ⟨hf, rfl⟩
    refine ⟨pullback_mem_domain ⟨f, hf⟩, ?_⟩
    rw [map_neg, pullback_operator]

end GeneratedFoundations.Geometry.SourceQuotientCasimir
