module

public import GeneratedFoundations.Geometry.SourceOneFormScalarCoordinates

/-!
# Kinetic energy of the original scalar source coefficients

The gradient uses the actual unit source derivatives. On each complete
source row it is identified with the differentiated gradient block in the
original Haar metric. Integration by parts and the derived Casimir give
the kinetic coefficient. Thus the nonconstant section kinetic indices
are calculated from differentiation, rather than copied from a spinor
position table or from a restoring mass.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceCentralSpectralProjection
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormHodgeBlock
open GeneratedFoundations.Geometry.SourceOneFormContinuousCore
open GeneratedFoundations.Geometry.SourceOneFormScalarCoordinates
open GeneratedFoundations.Geometry.SourceScalarResolution

namespace GeneratedFoundations.Geometry.SourceScalarKineticForm

def gradient : ScalarCore →ₗ[ℂ] OneFormL2 where
  toFun f := toHaar (fun j => derivative 1 j f)
  map_add' f g := by
    change toHaar (fun j => derivative 1 j (f + g)) = _
    simp only [map_add]
    rfl
  map_smul' c f := by
    change toHaar (fun j => derivative 1 j (c • f)) = _
    simp only [map_smul]
    rfl

theorem derivative_rowCoordinates {m : ℕ} (hm : Even m)
    (i : Fin (m + 1)) (j : Fin 3) (v : HilbertCarrier m) :
    derivative 1 j (rowCoordinates hm i v) =
      rowRepresentative hm i (SourceAxisMetric.unitHilbertAxis m j v) := by
  have h : (derivative 1 j).comp (rowCoordinates hm i) =
      (rowRepresentative hm i).comp (SourceAxisMetric.unitHilbertAxis m j) := by
    apply (sourceBasis m).toBasis.ext
    intro k
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis,
      rowCoordinates_basis, derivative, Module.Basis.constr_basis,
      SourceAxisMetric.unitHilbertAxis, LinearMap.smul_apply,
      map_smul, div_one]
    rfl
  exact LinearMap.congr_fun h v

/-- Equality is in the original one-form Haar space, with every component
and the original row normalization retained. -/
theorem gradient_rowCoordinates {m : ℕ} (hm : Even m)
    (i : Fin (m + 1)) (v : HilbertCarrier m) :
    gradient (rowCoordinates hm i v) =
      frameRowIsometry hm i (gradientOperator m v) := by
  apply (WithLp.equiv 2 (Fin 3 → QuotientL2)).injective
  funext j
  change ContinuousMap.toLp 2 quotientHaar ℂ
      (derivative 1 j (rowCoordinates hm i v)) = _
  rw [derivative_rowCoordinates, rowRepresentative_toLp]
  rfl

theorem gradient_row_pairing {m : ℕ} (hm : Even m)
    (i : Fin (m + 1)) (v w : HilbertCarrier m) :
    inner ℂ (gradient (rowCoordinates hm i v)) (gradient (rowCoordinates hm i w)) =
      ((m : ℂ) * ((m : ℂ) + 2)) * inner ℂ v w := by
  rw [gradient_rowCoordinates, gradient_rowCoordinates, LinearIsometry.inner_map_map,
    gradient_divergence_pairing, divergence_gradient]
  simpa only [inner_neg_right, neg_neg] using
    (inner_smul_right (𝕜 := ℂ) v w ((m : ℂ) * ((m : ℂ) + 2)))

theorem gradient_basis_energy (a : EvenIndex) :
    ‖gradient (scalarBasis a)‖ ^ 2 = SourceCasimirClosure.energy a.val.1 := by
  rcases a with ⟨⟨m, i, j⟩, hm⟩
  have h := gradient_row_pairing hm i (sourceBasis m j) (sourceBasis m j)
  rw [rowCoordinates_basis] at h
  simpa [inner_self_eq_norm_sq_to_K, (sourceBasis m).norm_eq_one,
    SourceCasimirClosure.energy, pow_two, Complex.mul_re] using congrArg Complex.re h

theorem coefficient_norm (a : EvenIndex) : ‖includeScalar (scalarBasis a)‖ = 1 := by
  rw [includeScalar_basis]
  exact quotientBasisVector_orthonormal.norm_eq_one a

/-- The constant source coefficient has zero gradient. Nonconstant rows
have their strictly positive, calculated kinetic contribution. -/
theorem gradient_basis_zero_iff (a : EvenIndex) :
    gradient (scalarBasis a) = 0 ↔ a.val.1 = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff, gradient_basis_energy,
    SourceCasimirClosure.energy]
  have hm : (0 : ℝ) ≤ a.val.1 := Nat.cast_nonneg _
  constructor
  · intro h
    have hz : (a.val.1 : ℝ) = 0 := by nlinarith
    exact_mod_cast hz
  · intro h
    simp [h]

/-- Successive kinetic positions of the actual even scalar source rows.
Both matrix-coefficient coordinates in each row remain independent. -/
def position (j : ℕ) : ℝ := SourceCasimirClosure.energy (2 * j)

theorem position_eq (j : ℕ) : position j = 4 * (j : ℝ) * ((j : ℝ) + 1) := by
  simp only [position, SourceCasimirClosure.energy, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem position_strictMono : StrictMono position := by
  intro j k hjk
  rw [position_eq, position_eq]
  have hlt : (j : ℝ) < k := by exact_mod_cast hjk
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  nlinarith

/-- A strict kinetic cutoff includes rows `0,...,m` precisely between
the last retained and first excluded positions. This is a support theorem,
not an assumption that the mathematical content has a fixed row count. -/
theorem position_plateau_iff (m : ℕ) (B : ℝ) :
    (∀ j, position j < B ↔ j < m + 1) ↔
      position m < B ∧ B ≤ position (m + 1) := by
  constructor
  · intro h
    refine ⟨(h m).mpr (by omega), ?_⟩
    exact le_of_not_gt (fun hb => (Nat.lt_irrefl (m + 1)) ((h _).mp hb))
  · rintro ⟨hlo, hhi⟩ j
    constructor
    · intro hj
      by_contra hnot
      have hm : m + 1 ≤ j := Nat.le_of_not_gt hnot
      exact not_lt_of_ge (le_trans hhi (position_strictMono.monotone hm)) hj
    · intro hj
      exact lt_of_le_of_lt (position_strictMono.monotone (by omega)) hlo

theorem first_position_plateau_iff (B : ℝ) :
    (∀ j, position j < B ↔ j = 0) ↔ 0 < B ∧ B ≤ 8 := by
  have h := position_plateau_iff 0 B
  norm_num [position_eq] at h ⊢
  exact h

end GeneratedFoundations.Geometry.SourceScalarKineticForm
