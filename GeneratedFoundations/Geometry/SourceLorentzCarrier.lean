module

public import GeneratedFoundations.Geometry.SourceHermitianReadout
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Lorentz carrier from the Hermitian source readout

The already constructed two-mode matrix algebra has a four-real-dimensional
Hermitian part.  Its determinant is the Minkowski quadratic form.  This file
adds the corresponding future-cone interface and proves that determinant-one
congruence preserves both the form and the positive-semidefinite realization
of that cone.  The distinguished future unit has stabilizer equation
`A Aᴴ = I`; no independent spacetime carrier or metric is introduced.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder Matrix
open GeneratedFoundations.Geometry.SourceHermitianReadout

namespace GeneratedFoundations.Geometry.SourceLorentzCarrier

abbrev SourceMat2 := GeneratedFoundations.Operations.SourceSpinCorner.Mat2

theorem realCoordinates_finrank : Module.finrank ℝ RealCoordinates = 4 := by
  simp [RealCoordinates]

/-- Euclidean square of the three spatial Hermitian coordinates. -/
def spatialSquare (q : RealCoordinates) : ℝ := q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2

theorem spatialSquare_nonneg (q : RealCoordinates) : 0 ≤ spatialSquare q := by
  unfold spatialSquare
  positivity

theorem determinantForm_eq (q : RealCoordinates) :
    determinantForm q = q 0 ^ 2 - spatialSquare q := by
  simp [determinantForm, spatialSquare]
  ring

/-- Closed future cone in the generated four-real Hermitian carrier. -/
def FutureCone (q : RealCoordinates) : Prop :=
  0 ≤ q 0 ∧ 0 ≤ determinantForm q

theorem futureCone_iff_sqrt_le (q : RealCoordinates) :
    FutureCone q ↔ Real.sqrt (spatialSquare q) ≤ q 0 := by
  rw [Real.sqrt_le_iff]
  simp only [FutureCone, determinantForm_eq]
  constructor
  · intro h
    exact ⟨h.1, by linarith⟩
  · intro h
    exact ⟨h.1, by linarith⟩

/-- Every positive-semidefinite Hermitian source readout lies in the future
cone. -/
theorem posSemidef_implies_futureCone {q : RealCoordinates}
    (hq : (hermitianMatrix q).PosSemidef) : FutureCone q := by
  have h00 : 0 ≤ q 0 + q 3 := by
    have h := hq.diag_nonneg (i := (0 : Fin 2))
    have hc : (0 : ℂ) ≤ ((q 0 + q 3 : ℝ) : ℂ) := by
      simpa [hermitianMatrix] using h
    exact Complex.zero_le_real.mp hc
  have h11 : 0 ≤ q 0 - q 3 := by
    have h := hq.diag_nonneg (i := (1 : Fin 2))
    have hc : (0 : ℂ) ≤ ((q 0 - q 3 : ℝ) : ℂ) := by
      simpa [hermitianMatrix] using h
    exact Complex.zero_le_real.mp hc
  have hdet : 0 ≤ determinantForm q := by
    have h := hq.det_nonneg
    rw [det_hermitianMatrix] at h
    exact Complex.zero_le_real.mp h
  exact ⟨by linarith, hdet⟩

/-- Lower-triangular square root of a future-cone matrix away from the
vanishing first principal entry. -/
def futureFactor (q : RealCoordinates) : SourceMat2 :=
  !![((Real.sqrt (q 0 + q 3) : ℝ) : ℂ), 0;
    ⟨q 1, -q 2⟩ / ((Real.sqrt (q 0 + q 3) : ℝ) : ℂ),
    ((Real.sqrt (determinantForm q / (q 0 + q 3)) : ℝ) : ℂ)]

private theorem futureCone_time_and_square {q : RealCoordinates}
    (hq : FutureCone q) :
    0 ≤ q 0 ∧ spatialSquare q ≤ q 0 ^ 2 := by
  have hs : 0 ≤ spatialSquare q := spatialSquare_nonneg q
  have hsqrt := Real.sq_sqrt hs
  have hroot : Real.sqrt (spatialSquare q) ≤ q 0 :=
    (futureCone_iff_sqrt_le q).mp hq
  constructor
  · exact (Real.sqrt_nonneg _).trans hroot
  · nlinarith [Real.sqrt_nonneg (spatialSquare q)]

private theorem futureFactor_mul_conjTranspose {q : RealCoordinates}
    (hq : FutureCone q) (ha : 0 < q 0 + q 3) :
    futureFactor q * (futureFactor q).conjTranspose = hermitianMatrix q := by
  have hsqrt : Real.sqrt (q 0 + q 3) ^ 2 = q 0 + q 3 :=
    Real.sq_sqrt ha.le
  have hdet : 0 ≤ determinantForm q := hq.2
  have hquot : 0 ≤ determinantForm q / (q 0 + q 3) :=
    div_nonneg hdet ha.le
  have hsqrtDet :
      Real.sqrt (determinantForm q / (q 0 + q 3)) ^ 2 =
        determinantForm q / (q 0 + q 3) := Real.sq_sqrt hquot
  have hsqrtR_ne : Real.sqrt (q 0 + q 3) ≠ 0 :=
    (Real.sqrt_pos.2 ha).ne'
  have hsqrt_ne : (Real.sqrt (q 0 + q 3) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrtR_ne
  have hsqrtDetExpanded :
      Real.sqrt ((q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2) /
          (q 0 + q 3)) ^ 2 =
        (q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2) / (q 0 + q 3) := by
    simpa only [determinantForm] using hsqrtDet
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext
  all_goals simp [futureFactor, hermitianMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  all_goals field_simp [hsqrtR_ne, hsqrt_ne]
  all_goals simp [hsqrt, determinantForm]
  rw [hsqrtDetExpanded]
  field_simp [ha.ne']
  ring

/-- The algebraic future cone is exactly the positive cone of the generated
Hermitian source algebra. -/
theorem futureCone_implies_posSemidef {q : RealCoordinates}
    (hq : FutureCone q) : (hermitianMatrix q).PosSemidef := by
  obtain ⟨ht, hsquare⟩ := futureCone_time_and_square hq
  have hzsq : q 3 ^ 2 ≤ q 0 ^ 2 := by
    dsimp [spatialSquare] at hsquare
    nlinarith [sq_nonneg (q 1), sq_nonneg (q 2)]
  have ha : 0 ≤ q 0 + q 3 := by
    nlinarith [sq_nonneg (q 0 + q 3)]
  rcases ha.eq_or_lt with ha0 | ha_pos
  · have hq3 : q 3 = -q 0 := by linarith
    have hq1 : q 1 = 0 := by
      dsimp [spatialSquare] at hsquare
      nlinarith [sq_nonneg (q 2)]
    have hq2 : q 2 = 0 := by
      dsimp [spatialSquare] at hsquare
      nlinarith [sq_nonneg (q 1)]
    have hm : hermitianMatrix q =
        Matrix.diagonal ![(0 : ℂ), ((2 * q 0 : ℝ) : ℂ)] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j
      all_goals simp [hermitianMatrix, hq3, hq1, hq2, Complex.ext_iff]
      all_goals ring
    rw [hm]
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp [Complex.nonneg_iff, ht]
  · rw [← futureFactor_mul_conjTranspose hq ha_pos]
    exact Matrix.posSemidef_self_mul_conjTranspose _

theorem posSemidef_iff_futureCone (q : RealCoordinates) :
    (hermitianMatrix q).PosSemidef ↔ FutureCone q :=
  ⟨posSemidef_implies_futureCone, futureCone_implies_posSemidef⟩

theorem congruence_posSemidef {A : SourceMat2} {q : RealCoordinates}
    (hq : (hermitianMatrix q).PosSemidef) :
    (congruence A (hermitianMatrix q)).PosSemidef :=
  hq.mul_mul_conjTranspose_same A

/-- Congruence preserves the positive realization and hence the generated
future cone; determinant one is needed separately for exact form invariance. -/
theorem coordinateTransform_futureCone_of_posSemidef
    {A : SourceMat2} {q : RealCoordinates}
    (hq : (hermitianMatrix q).PosSemidef) :
    FutureCone (coordinateTransform A q) := by
  apply posSemidef_implies_futureCone
  rw [hermitianMatrix_coordinateTransform]
  exact congruence_posSemidef hq

theorem coordinateTransform_preserves_form
    {A : SourceMat2} (hA : A.det = 1) (q : RealCoordinates) :
    determinantForm (coordinateTransform A q) = determinantForm q :=
  determinantForm_coordinateTransform A hA q

/-- Distinguished unit of the future cone. -/
def futureUnit : RealCoordinates := ![1, 0, 0, 0]

@[simp] theorem hermitianMatrix_futureUnit : hermitianMatrix futureUnit = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [futureUnit, hermitianMatrix]

theorem futureUnit_posDef : (hermitianMatrix futureUnit).PosDef := by
  rw [hermitianMatrix_futureUnit]
  exact Matrix.PosDef.one

theorem futureUnit_mem : FutureCone futureUnit := by
  norm_num [FutureCone, futureUnit, determinantForm]

theorem coordinateTransform_futureUnit_matrix (A : SourceMat2) :
    hermitianMatrix (coordinateTransform A futureUnit) = A * A.conjTranspose := by
  rw [hermitianMatrix_coordinateTransform, hermitianMatrix_futureUnit]
  simp [congruence]

/-- Fixing the generated future unit is exactly the special-unitary
stabilizer equation on a determinant-one matrix. -/
theorem coordinateTransform_futureUnit_iff {A : SourceMat2} (_hA : A.det = 1) :
    coordinateTransform A futureUnit = futureUnit ↔
      A * A.conjTranspose = 1 := by
  constructor
  · intro h
    have hm := congrArg hermitianMatrix h
    simpa only [coordinateTransform_futureUnit_matrix,
      hermitianMatrix_futureUnit] using hm
  · intro h
    have hm : hermitianMatrix (coordinateTransform A futureUnit) =
        hermitianMatrix futureUnit := by
      simpa only [coordinateTransform_futureUnit_matrix,
        hermitianMatrix_futureUnit] using h
    calc
      coordinateTransform A futureUnit =
          matrixCoordinates (hermitianMatrix (coordinateTransform A futureUnit)) :=
        (matrixCoordinates_hermitianMatrix _).symm
      _ = matrixCoordinates (hermitianMatrix futureUnit) := congrArg matrixCoordinates hm
      _ = futureUnit := matrixCoordinates_hermitianMatrix _

/-- The two central signs act identically on the Lorentz carrier. -/
theorem coordinateTransform_negativeIdentity (q : RealCoordinates) :
    coordinateTransform (-1 : SourceMat2) q = q := by
  have hm : hermitianMatrix (coordinateTransform (-1 : SourceMat2) q) =
      hermitianMatrix q := by
    rw [hermitianMatrix_coordinateTransform]
    simp [congruence]
  calc
    coordinateTransform (-1 : SourceMat2) q =
        matrixCoordinates (hermitianMatrix (coordinateTransform (-1 : SourceMat2) q)) :=
      (matrixCoordinates_hermitianMatrix _).symm
    _ = matrixCoordinates (hermitianMatrix q) := congrArg matrixCoordinates hm
    _ = q := matrixCoordinates_hermitianMatrix _

/-- Finite algebraic conclusions of the generated Lorentz carrier. -/
structure Properties : Prop where
  dimension : Module.finrank ℝ RealCoordinates = 4
  determinant_signature : ∀ q,
    (hermitianMatrix q).det = (determinantForm q : ℂ)
  cone_characterization : ∀ q,
    FutureCone q ↔ Real.sqrt (spatialSquare q) ≤ q 0
  positive_cone : ∀ q, (hermitianMatrix q).PosSemidef ↔ FutureCone q
  form_invariant : ∀ A, A.det = 1 → ∀ q,
    determinantForm (coordinateTransform A q) = determinantForm q
  positive_congruence : ∀ A q, (hermitianMatrix q).PosSemidef →
    (congruence A (hermitianMatrix q)).PosSemidef
  future_unit : FutureCone futureUnit ∧ (hermitianMatrix futureUnit).PosDef
  future_stabilizer : ∀ A, A.det = 1 →
    (coordinateTransform A futureUnit = futureUnit ↔ A * A.conjTranspose = 1)
  central_sign : ∀ q, coordinateTransform (-1 : SourceMat2) q = q

theorem properties : Properties where
  dimension := realCoordinates_finrank
  determinant_signature := det_hermitianMatrix
  cone_characterization := futureCone_iff_sqrt_le
  positive_cone := posSemidef_iff_futureCone
  form_invariant := fun _A hA q => coordinateTransform_preserves_form hA q
  positive_congruence := fun _A _q hq => congruence_posSemidef hq
  future_unit := ⟨futureUnit_mem, futureUnit_posDef⟩
  future_stabilizer := fun _A hA => coordinateTransform_futureUnit_iff hA
  central_sign := coordinateTransform_negativeIdentity

end GeneratedFoundations.Geometry.SourceLorentzCarrier
