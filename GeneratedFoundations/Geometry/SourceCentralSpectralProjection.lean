module

public import GeneratedFoundations.Geometry.SourceCentralObservations
public import GeneratedFoundations.Geometry.SourceCompleteCoefficients

/-!
# Central averaging on the actual source coefficient blocks

The central sign acts on homogeneous source polynomials by degree parity.
This action determines central averaging on their continuous coefficients
and on the complete matrix-coefficient blocks in the original Haar space.
The Hilbert-space map is the average of the identity and the actual
measure-preserving central pullback. It is not defined by selecting indices.

Even continuous coefficients descend uniquely to the existing central
quotient. On the full source Haar space, the same averaging operator fixes
exactly the vectors whose odd-degree coefficients vanish. The construction
does not yet identify this range with a separately constructed quotient
Haar space or transport the differential Casimir to that quotient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceCoefficientProducts
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients

namespace GeneratedFoundations.Geometry.SourceCentralSpectralProjection

/-- Parity is inherited from the action on the original polynomial carrier. -/
theorem coefficient_centralTranslate (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ)
    (v : Carrier m) (U : SU2) :
    coefficient m φ v (negativeIdentity * U) =
      (-1 : ℂ) ^ m * coefficient m φ v U := by
  simp only [coefficient_apply, map_mul, Module.End.mul_apply,
    sourceRepresentation_centre, map_smul, smul_eq_mul]

theorem centralAverage_coefficient (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ)
    (v : Carrier m) :
    centralAverage (coefficient m φ v) =
      ((1 + (-1 : ℂ) ^ m) / 2) • coefficient m φ v := by
  apply ContinuousMap.ext
  intro U
  rw [centralAverage_apply, coefficient_centralTranslate]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem centralAverage_coefficient_even {m : ℕ} (hm : Even m)
    (φ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier m) :
    centralAverage (coefficient m φ v) = coefficient m φ v := by
  rw [centralAverage_coefficient, hm.neg_one_pow]
  norm_num

theorem centralAverage_coefficient_odd {m : ℕ} (hm : Odd m)
    (φ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier m) :
    centralAverage (coefficient m φ v) = 0 := by
  rw [centralAverage_coefficient, hm.neg_one_pow]
  norm_num

/-- The Hilbert realization retains the proved action of the same centre. -/
theorem unitaryAction_centre (m : ℕ) (v : HilbertCarrier m) :
    unitaryAction m negativeIdentity v = (-1 : ℂ) ^ m • v := by
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
  rw [unitaryAction_apply_carrier, sourceRepresentation_centre, map_smul]

theorem matrixCoefficient_centralTranslate (m : ℕ) (v a : HilbertCarrier m)
    (U : SU2) :
    matrixCoefficient m v a (negativeIdentity * U) =
      (-1 : ℂ) ^ m * matrixCoefficient m v a U := by
  simp only [matrixCoefficient_apply, action_mul, unitaryAction_centre]
  exact inner_smul_right (𝕜 := ℂ) v (unitaryAction m U a) ((-1 : ℂ) ^ m)

theorem matrixCoefficient_comp_centralTranslation (m : ℕ)
    (v a : HilbertCarrier m) :
    (matrixCoefficient m v a).comp centralTranslation =
      (-1 : ℂ) ^ m • matrixCoefficient m v a := by
  apply ContinuousMap.ext
  intro U
  exact matrixCoefficient_centralTranslate m v a U

theorem centralAverage_matrixCoefficient (m : ℕ) (v a : HilbertCarrier m) :
    centralAverage (matrixCoefficient m v a) =
      ((1 + (-1 : ℂ) ^ m) / 2) • matrixCoefficient m v a := by
  apply ContinuousMap.ext
  intro U
  rw [centralAverage_apply, matrixCoefficient_centralTranslate]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem centralAverage_matrixEntry_even {m : ℕ} (hm : Even m)
    (i j : Fin (m + 1)) : centralAverage (matrixEntry m i j) = matrixEntry m i j := by
  rw [matrixEntry, centralAverage_matrixCoefficient, hm.neg_one_pow]
  norm_num

theorem centralAverage_matrixEntry_odd {m : ℕ} (hm : Odd m)
    (i j : Fin (m + 1)) : centralAverage (matrixEntry m i j) = 0 := by
  rw [matrixEntry, centralAverage_matrixCoefficient, hm.neg_one_pow]
  norm_num

theorem matrixEntry_even_invariant {m : ℕ} (hm : Even m) (i j : Fin (m + 1)) :
    IsCentralInvariant (matrixEntry m i j) :=
  (centralAverage_fixed_iff _).mp (centralAverage_matrixEntry_even hm i j)

/-- Every even entry descends through the already constructed source quotient. -/
def quotientEntry {m : ℕ} (hm : Even m) (i j : Fin (m + 1)) :
    C(CentralQuotient, ℂ) := descend (matrixEntry m i j) (matrixEntry_even_invariant hm i j)

@[simp] theorem quotientEntry_apply {m : ℕ} (hm : Even m)
    (i j : Fin (m + 1)) (U : SU2) :
    quotientEntry hm i j (quotientContinuous U) = matrixEntry m i j U :=
  descend_apply _ _ U

theorem quotientEntry_unique {m : ℕ} (hm : Even m) (i j : Fin (m + 1))
    (g : C(CentralQuotient, ℂ)) (hg : g.comp quotientContinuous = matrixEntry m i j) :
    g = quotientEntry hm i j := descend_unique _ _ g hg

/-- Central translation preserves the original probability Haar measure. -/
theorem centralTranslation_measurePreserving :
    MeasurePreserving centralTranslation sourceHaar sourceHaar :=
  measurePreserving_mul_left sourceHaar negativeIdentity

def centralPullback : SourceL2 →ₗᵢ[ℂ] SourceL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ centralTranslation centralTranslation_measurePreserving

/-- The actual pullback agrees with composition of continuous representatives. -/
theorem centralPullback_toLp (f : C(SU2, ℂ)) :
    centralPullback (ContinuousMap.toLp 2 sourceHaar ℂ f) =
      ContinuousMap.toLp 2 sourceHaar ℂ (f.comp centralTranslation) := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 sourceHaar ℂ f) centralTranslation_measurePreserving
  have hf := centralTranslation_measurePreserving.quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar f)
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar
    (f.comp centralTranslation)
  filter_upwards [hcomp, hf, hr] with U hc hu hright
  exact hc.trans (hu.trans hright.symm)

theorem centralPullback_entry (m : ℕ) (i j : Fin (m + 1)) :
    centralPullback (entry m i j) = (-1 : ℂ) ^ m • entry m i j := by
  rw [entry, centralPullback_toLp, matrixEntry,
    matrixCoefficient_comp_centralTranslation, map_smul]

theorem centralPullback_basis (a : Index) :
    centralPullback (basisVector a) = (-1 : ℂ) ^ a.1 • basisVector a := by
  rw [basisVector, map_smul, centralPullback_entry]
  exact smul_comm _ _ _

theorem centralPullback_basis_even {a : Index} (ha : Even a.1) :
    centralPullback (basisVector a) = basisVector a := by
  rw [centralPullback_basis, ha.neg_one_pow, one_smul]

theorem centralPullback_basis_odd {a : Index} (ha : Odd a.1) :
    centralPullback (basisVector a) = -basisVector a := by
  rw [centralPullback_basis, ha.neg_one_pow, neg_one_smul]

theorem centralPullback_twice (f : SourceL2) :
    centralPullback (centralPullback f) = f := by
  have h : centralPullback.toContinuousLinearMap.comp
      centralPullback.toContinuousLinearMap = ContinuousLinearMap.id ℂ SourceL2 := by
    apply ContinuousLinearMap.ext_on matrixCoefficients_dense
    rintro _ ⟨a, rfl⟩
    change centralPullback (centralPullback (basisVector a)) = basisVector a
    rcases Nat.even_or_odd a.1 with ha | ha
    · rw [centralPullback_basis_even ha, centralPullback_basis_even ha]
    · rw [centralPullback_basis_odd ha, map_neg, centralPullback_basis_odd ha, neg_neg]
  exact congrArg (fun T : SourceL2 →L[ℂ] SourceL2 => T f) h

theorem centralPullback_inner (f g : SourceL2) :
    inner ℂ (centralPullback f) g = inner ℂ f (centralPullback g) := by
  have h := centralPullback.inner_map_map f (centralPullback g)
  simpa only [centralPullback_twice] using h

/-- Averaging is defined on genuine Haar classes by the central group action. -/
def averageL2 : SourceL2 →L[ℂ] SourceL2 :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ SourceL2 + centralPullback.toContinuousLinearMap)

@[simp] theorem averageL2_apply (f : SourceL2) :
    averageL2 f = (1 / 2 : ℂ) • (f + centralPullback f) := rfl

theorem averageL2_toLp (f : C(SU2, ℂ)) :
    averageL2 (ContinuousMap.toLp 2 sourceHaar ℂ f) =
      ContinuousMap.toLp 2 sourceHaar ℂ (centralAverage f) := by
  rw [averageL2_apply, centralPullback_toLp]
  simp only [centralAverage, map_smul, map_add]

theorem averageL2_basis_even {a : Index} (ha : Even a.1) :
    averageL2 (basisVector a) = basisVector a := by
  rw [basisVector, map_smul, entry, averageL2_toLp,
    centralAverage_matrixEntry_even ha]

theorem averageL2_basis_odd {a : Index} (ha : Odd a.1) :
    averageL2 (basisVector a) = 0 := by
  rw [basisVector, map_smul, entry, averageL2_toLp,
    centralAverage_matrixEntry_odd ha, map_zero, smul_zero]

/-- Central averaging fixes the full even block, with both matrix indices. -/
theorem averageL2_block_even {m : ℕ} (hm : Even m) {f : SourceL2}
    (hf : f ∈ blockSpace m) : averageL2 f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨ij, rfl⟩ := hf
      exact averageL2_basis_even hm
  | zero => exact map_zero averageL2
  | add f g _ _ hf hg => rw [map_add, hf, hg]
  | smul c f _ hf => rw [map_smul, hf]

/-- Central averaging annihilates the full odd block. -/
theorem averageL2_block_odd {m : ℕ} (hm : Odd m) {f : SourceL2}
    (hf : f ∈ blockSpace m) : averageL2 f = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨ij, rfl⟩ := hf
      exact averageL2_basis_odd hm
  | zero => exact map_zero averageL2
  | add f g _ _ hf hg => rw [map_add, hf, hg, add_zero]
  | smul c f _ hf => rw [map_smul, hf, smul_zero]

theorem averageL2_inner_even {a : Index} (ha : Even a.1) (f : SourceL2) :
    inner ℂ (basisVector a) (averageL2 f) = inner ℂ (basisVector a) f := by
  have h := centralPullback.inner_map_map (basisVector a) (centralPullback f)
  rw [centralPullback_basis_even ha, centralPullback_twice] at h
  rw [averageL2_apply, inner_smul_right, inner_add_right, ← h]
  ring

theorem averageL2_inner_odd {a : Index} (ha : Odd a.1) (f : SourceL2) :
    inner ℂ (basisVector a) (averageL2 f) = 0 := by
  have h := centralPullback.inner_map_map (basisVector a) (centralPullback f)
  rw [centralPullback_basis_odd ha, centralPullback_twice, inner_neg_left] at h
  rw [averageL2_apply, inner_smul_right, inner_add_right, ← h]
  ring

/-- The multiplier formula holds for every vector in the complete Haar space. -/
theorem averageL2_coefficients (f : SourceL2) (a : Index) :
    coefficients (averageL2 f) a = if Even a.1 then coefficients f a else 0 := by
  classical
  simp only [coefficients_apply]
  rcases Nat.even_or_odd a.1 with ha | ha
  · rw [ite_eq_left ha, averageL2_inner_even ha]
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ha), averageL2_inner_odd ha]

theorem averageL2_fixed_iff (f : SourceL2) :
    averageL2 f = f ↔ ∀ a : Index, Odd a.1 → coefficients f a = 0 := by
  constructor
  · intro hf a ha
    rw [← hf, coefficients_apply, averageL2_inner_odd ha]
  · intro hf
    apply eq_of_coefficients_eq
    intro a
    rcases Nat.even_or_odd a.1 with ha | ha
    · exact averageL2_inner_even ha f
    · rw [averageL2_inner_odd ha]
      exact ((coefficients_apply f a).symm.trans (hf a ha)).symm

theorem averageL2_idempotent (f : SourceL2) : averageL2 (averageL2 f) = averageL2 f := by
  apply (averageL2_fixed_iff _).mpr
  intro a ha
  rw [coefficients_apply, averageL2_inner_odd ha]

/-- Together with idempotence, this identifies the average as an orthogonal projection. -/
theorem averageL2_inner (f g : SourceL2) :
    inner ℂ (averageL2 f) g = inner ℂ f (averageL2 g) := by
  simp only [averageL2_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, centralPullback_inner,
    map_div₀, map_one, map_ofNat]

theorem averageL2_norm_le (f : SourceL2) : ‖averageL2 f‖ ≤ ‖f‖ := by
  rw [averageL2_apply, norm_smul]
  have hnorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hnorm]
  calc
    (1 / 2 : ℝ) * ‖f + centralPullback f‖ ≤
        (1 / 2 : ℝ) * (‖f‖ + ‖centralPullback f‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖f‖ := by rw [centralPullback.norm_map]; ring

end GeneratedFoundations.Geometry.SourceCentralSpectralProjection
