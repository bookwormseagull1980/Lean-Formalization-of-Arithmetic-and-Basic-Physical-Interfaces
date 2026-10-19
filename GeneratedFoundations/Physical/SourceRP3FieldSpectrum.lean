module

public import GeneratedFoundations.Geometry.SourceSphereCapacity
public import GeneratedFoundations.Geometry.SourceLeftRightRepresentations
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega

/-!
# Representation-labelled field spectra on the generated projective three-space

The scalar part of this file is tied to the actual quotient Casimir already
constructed from minimal unbiased compositional change.  The remaining
formulae encode the representation-labelled round-space data used in Paper 4:
the coclosed one-form tower, the two spin structures of the Dirac tower and
the two transverse--traceless tensor branches.  Their parity, dimensions,
Casimir values, curvature shifts and lowest levels are proved here.

This is the finite representation-theoretic layer of the field-spectrum
argument.  The operator-level construction is carried out separately in
`Geometry.SourceOneForm*`, `Geometry.SourceSpinor*` and
`Geometry.SourceTensorTT*`: those modules construct the original Haar field
spaces, differential operators, closed domains and exhaustive spectral
bases.  The labels here are used to identify their spectra; they are not a
substitute for those operator theorems.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Geometry.SourceEndpointCasimir
open GeneratedFoundations.Geometry.SourceSphereCapacity
open GeneratedFoundations.Geometry.SourceLeftRightRepresentations

namespace GeneratedFoundations.Physical.SourceRP3FieldSpectrum

/-- The dimensionless scalar eigenvalue on the round three-sphere. -/
def scalarCasimir (l : ℕ) : ℝ := (l : ℝ) * ((l : ℝ) + 2)

/-- The scalar eigenvalue at radius `L`. -/
def scalarEigenvalue (L : ℝ) (l : ℕ) : ℝ := scalarCasimir l / L ^ 2

/-- The complete scalar multiplicity at degree `l`. -/
def scalarMultiplicity (l : ℕ) : ℕ := (l + 1) ^ 2

/-- Ordinary scalars descend through the antipodal quotient exactly at even degree. -/
def ScalarDegree (l : ℕ) : Prop := Even l

theorem scalarCasimir_eq_source_energy (l : ℕ) :
    scalarCasimir l = Geometry.SourceCasimirClosure.energy l := by
  simp only [scalarCasimir, Geometry.SourceCasimirClosure.energy]

theorem scalarEigenvalue_eq_source_scaled (L : ℝ) (l : ℕ) :
    scalarEigenvalue L l = scaledEnergy L l := by
  rw [scalarEigenvalue, scalarCasimir_eq_source_energy, scaledEnergy,
    inverseSquare_eq]
  ring

theorem scalarMultiplicity_eq_sphere (l : ℕ) :
    (scalarMultiplicity l : ℝ) = sphereMultiplicity 3 l := by
  rw [multiplicity_three]
  simp only [scalarMultiplicity, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-- The actual generated quotient eigenspace has the displayed scalar multiplicity. -/
theorem generated_scalar_eigenspace_finrank {b : ℝ} (hb : 0 < b)
    (l : ℕ) (hl : ScalarDegree l) :
    Module.finrank ℂ
      (Geometry.SourceEndpointSpectrum.eigenspace (radius b)
        ((scalarEigenvalue (radius b) l : ℝ) : ℂ)) = scalarMultiplicity l := by
  rw [scalarEigenvalue_eq_source_scaled]
  simpa only [scalarMultiplicity] using
    Geometry.SourceEndpointSpectrum.eigenspace_finrank (radius_pos hb).ne' l hl

/-- The scalar portion is anchored to the actual closed quotient operator
constructed from the source. It is separated from the later field-branch
labels so that the root interface contains no supplied field table. -/
structure GeneratedScalarProperties : Prop where
  spectral_anchor : ∀ L l, scalarEigenvalue L l = scaledEnergy L l
  eigenspace_dimension : ∀ {b : ℝ}, 0 < b → ∀ l, ScalarDegree l →
    Module.finrank ℂ
      (Geometry.SourceEndpointSpectrum.eigenspace (radius b)
        ((scalarEigenvalue (radius b) l : ℝ) : ℂ)) = scalarMultiplicity l

theorem generatedScalarProperties : GeneratedScalarProperties where
  spectral_anchor := scalarEigenvalue_eq_source_scaled
  eigenspace_dimension := fun hb l hl => generated_scalar_eigenspace_finrank hb l hl

/-- The dimensionless Hodge eigenvalue of the coclosed one-form tower. -/
def vectorCasimir (l : ℕ) : ℝ := ((l : ℝ) + 1) ^ 2

def vectorEigenvalue (L : ℝ) (l : ℕ) : ℝ := vectorCasimir l / L ^ 2

def vectorMultiplicity (l : ℕ) : ℕ := 2 * l * (l + 2)

/-- Ordinary one-forms descend at positive odd degree. -/
def VectorDegree (l : ℕ) : Prop := Odd l ∧ 1 ≤ l

@[simp] theorem vectorCasimir_one : vectorCasimir 1 = 4 := by
  norm_num [vectorCasimir]

@[simp] theorem vectorMultiplicity_one : vectorMultiplicity 1 = 6 := by
  norm_num [vectorMultiplicity]

theorem vectorEigenvalue_one (L : ℝ) : vectorEigenvalue L 1 = 4 / L ^ 2 := by
  norm_num [vectorEigenvalue, vectorCasimir]

theorem vectorCasimir_pos (l : ℕ) : 0 < vectorCasimir l := by
  unfold vectorCasimir
  positivity

theorem vectorEigenvalue_pos {L : ℝ} (hL : L ≠ 0) (l : ℕ) :
    0 < vectorEigenvalue L l := by
  exact div_pos (vectorCasimir_pos l) (sq_pos_of_ne_zero hL)

theorem vector_no_zero_mode {L : ℝ} (hL : L ≠ 0) (l : ℕ) :
    vectorEigenvalue L l ≠ 0 := ne_of_gt (vectorEigenvalue_pos hL l)

/-- Both vector branches are actual tensor products of generated source powers. -/
theorem generated_vector_branch_finrank {l : ℕ} (hl : 1 ≤ l) :
    Module.finrank ℂ (VectorPlusCarrier l) = vectorMultiplicity l / 2 ∧
      Module.finrank ℂ (VectorMinusCarrier l) = vectorMultiplicity l / 2 := by
  constructor
  · rw [vectorPlus_finrank hl]
    simp [vectorMultiplicity, Nat.mul_assoc]
  · rw [vectorMinus_finrank hl]
    simp [vectorMultiplicity, Nat.mul_assoc]

theorem generated_vector_branch_casimir {l : ℕ} (hl : 1 ≤ l) :
    casimirIndex (l + 1) (l - 1) = vectorCasimir l ∧
      casimirIndex (l - 1) (l + 1) = vectorCasimir l := by
  rw [vectorPlus_casimir hl, vectorMinus_casimir hl]
  constructor <;> rfl

theorem generated_vector_branches_descend {l : ℕ} (hl : Odd l) :
    representation (l + 1) (l - 1) rightCentral = 1 ∧
      representation (l - 1) (l + 1) rightCentral = 1 :=
  ⟨vectorPlus_rightCentral hl, vectorMinus_rightCentral hl⟩

/-- The two real half-spin labels of the positive TT branch. -/
def ttPlusLeft (k : ℕ) : ℝ := ((k : ℝ) + 2) / 2
def ttPlusRight (k : ℕ) : ℝ := ((k : ℝ) - 2) / 2

/-- The negative branch interchanges the two half-spin labels. -/
def ttMinusLeft (k : ℕ) : ℝ := ttPlusRight k
def ttMinusRight (k : ℕ) : ℝ := ttPlusLeft k

/-- The dimensionless `Spin(4)` Casimir in the normalization of Paper 4. -/
def spin4Casimir (jL jR : ℝ) : ℝ :=
  2 * (jL * (jL + 1) + jR * (jR + 1))

def ttCasimir (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 2) + 4

theorem tt_plus_Casimir (k : ℕ) :
    spin4Casimir (ttPlusLeft k) (ttPlusRight k) = ttCasimir k := by
  simp only [spin4Casimir, ttPlusLeft, ttPlusRight, ttCasimir]
  ring

theorem tt_minus_Casimir (k : ℕ) :
    spin4Casimir (ttMinusLeft k) (ttMinusRight k) = ttCasimir k := by
  simp only [ttMinusLeft, ttMinusRight, spin4Casimir, ttPlusLeft,
    ttPlusRight, ttCasimir]
  ring

/-- One of the two TT branches has this representation dimension. -/
def ttBranchMultiplicity (k : ℕ) : ℕ := (k - 1) * (k + 3)

/-- Both TT branches together give the complete labelled multiplicity. -/
def ttMultiplicity (k : ℕ) : ℕ := 2 * (k - 1) * (k + 3)

theorem ttMultiplicity_eq_two_branches (k : ℕ) :
    ttMultiplicity k = 2 * ttBranchMultiplicity k := by
  simp only [ttMultiplicity, ttBranchMultiplicity, Nat.mul_assoc]

/-- The positive rough TT Laplacian eigenvalue. -/
def ttRoughEigenvalue (L : ℝ) (k : ℕ) : ℝ :=
  (((k : ℝ) * ((k : ℝ) + 2)) - 2) / L ^ 2

/-- Ordinary rank-two tensors descend at even degree at least two. -/
def TTDegree (k : ℕ) : Prop := Even k ∧ 2 ≤ k

theorem ttRough_from_Casimir (L : ℝ) (k : ℕ) :
    ttRoughEigenvalue L k = (ttCasimir k - 6) / L ^ 2 := by
  simp only [ttRoughEigenvalue, ttCasimir]
  ring

@[simp] theorem ttBranchMultiplicity_two : ttBranchMultiplicity 2 = 5 := by
  norm_num [ttBranchMultiplicity]

@[simp] theorem ttMultiplicity_two : ttMultiplicity 2 = 10 := by
  norm_num [ttMultiplicity]

theorem ttRoughEigenvalue_two (L : ℝ) :
    ttRoughEigenvalue L 2 = 6 / L ^ 2 := by
  norm_num [ttRoughEigenvalue]

theorem ttRough_numerator_ge_six {k : ℕ} (hk : 2 ≤ k) :
    (6 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 2) - 2 := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [sq_nonneg ((k : ℝ) - 2)]

theorem ttRoughEigenvalue_ge_lowest {L : ℝ} (_hL : L ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    6 / L ^ 2 ≤ ttRoughEigenvalue L k := by
  exact div_le_div_of_nonneg_right (ttRough_numerator_ge_six hk) (sq_nonneg L)

theorem ttRoughEigenvalue_pos {L : ℝ} (hL : L ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    0 < ttRoughEigenvalue L k := by
  have h6 : 0 < 6 / L ^ 2 := div_pos (by norm_num) (sq_pos_of_ne_zero hL)
  exact lt_of_lt_of_le h6 (ttRoughEigenvalue_ge_lowest hL hk)

/-- Both TT branches are actual bidegree shifts of the generated source powers. -/
theorem generated_tt_branch_finrank {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (TTPlusCarrier k) = ttBranchMultiplicity k ∧
      Module.finrank ℂ (TTMinusCarrier k) = ttBranchMultiplicity k := by
  rw [ttPlus_finrank hk, ttMinus_finrank hk]
  constructor <;> rfl

theorem generated_tt_branch_casimir {k : ℕ} (hk : 2 ≤ k) :
    casimirIndex (k + 2) (k - 2) = ttCasimir k ∧
      casimirIndex (k - 2) (k + 2) = ttCasimir k := by
  rw [ttPlus_casimir hk, ttMinus_casimir hk]
  constructor <;> rfl

theorem generated_tt_branches_descend {k : ℕ} (hk : Even k) :
    representation (k + 2) (k - 2) rightCentral = 1 ∧
      representation (k - 2) (k + 2) rightCentral = 1 :=
  ⟨ttPlus_rightCentral hk, ttMinus_rightCentral hk⟩

/-- The Casimir-labelled TT operator with real shift `alpha`. -/
def ttShiftedEigenvalue (L alpha : ℝ) (k : ℕ) : ℝ :=
  (ttCasimir k + alpha) / L ^ 2

theorem ttShifted_eq_rough_add (L alpha : ℝ) (k : ℕ) :
    ttShiftedEigenvalue L alpha k =
      ttRoughEigenvalue L k + (alpha + 6) / L ^ 2 := by
  simp only [ttShiftedEigenvalue, ttRoughEigenvalue, ttCasimir]
  ring

theorem ttShifted_total (L alpha beta : ℝ) (k : ℕ) :
    ttShiftedEigenvalue L (alpha + beta) k =
      ttRoughEigenvalue L k + (alpha + beta + 6) / L ^ 2 := by
  simp only [ttShiftedEigenvalue, ttRoughEigenvalue, ttCasimir]
  ring

/-- Magnitude of the round Dirac eigenvalue. -/
def diracMagnitude (L : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 3 / 2) / L

def diracMultiplicity (k : ℕ) : ℕ := (k + 1) * (k + 2)

/-- The selected spin structure has positive even and negative odd labels. -/
def TauMinusPositiveDegree (k : ℕ) : Prop := Even k
def TauMinusNegativeDegree (k : ℕ) : Prop := Odd k

/-- The other spin structure interchanges the two parity assignments. -/
def TauPlusPositiveDegree (k : ℕ) : Prop := Odd k
def TauPlusNegativeDegree (k : ℕ) : Prop := Even k

theorem tauPlus_positive_iff_tauMinus_negative (k : ℕ) :
    TauPlusPositiveDegree k ↔ TauMinusNegativeDegree k := Iff.rfl

theorem tauPlus_negative_iff_tauMinus_positive (k : ℕ) :
    TauPlusNegativeDegree k ↔ TauMinusPositiveDegree k := Iff.rfl

@[simp] theorem diracMultiplicity_zero : diracMultiplicity 0 = 2 := by
  norm_num [diracMultiplicity]

theorem diracMagnitude_pos {L : ℝ} (hL : 0 < L) (k : ℕ) :
    0 < diracMagnitude L k := by
  unfold diracMagnitude
  positivity

theorem dirac_no_zero_mode {L : ℝ} (hL : 0 < L) (k : ℕ) :
    diracMagnitude L k ≠ 0 := ne_of_gt (diracMagnitude_pos hL k)

/-- The two signed spinor branches are actual adjacent generated bidegrees. -/
theorem generated_spinor_branch_finrank (k : ℕ) :
    Module.finrank ℂ (SpinorPlusCarrier k) = diracMultiplicity k ∧
      Module.finrank ℂ (SpinorMinusCarrier k) = diracMultiplicity k := by
  rw [spinorPlus_finrank, spinorMinus_finrank]
  constructor <;> rfl

theorem generated_tauMinus_parity (k : ℕ) :
    (Even k → representation (k + 1) k rightCentral = 1) ∧
      (Odd k → representation k (k + 1) rightCentral = 1) ∧
      (Odd k → representation (k + 1) k rightCentral =
        (-1 : ℂ) • (1 : Module.End ℂ (SpinorPlusCarrier k))) ∧
      (Even k → representation k (k + 1) rightCentral =
        (-1 : ℂ) • (1 : Module.End ℂ (SpinorMinusCarrier k))) :=
  ⟨spinorPlus_rightCentral_of_even,
    spinorMinus_rightCentral_of_odd,
    spinorPlus_rightCentral_of_odd,
    spinorMinus_rightCentral_of_even⟩

/-- Exactly the labels `0,2,4` lie below every cutoff in the displayed plateau. -/
theorem selected_dirac_plateau {c : ℝ} (hlo : 11 / 2 < c) (hhi : c < 15 / 2)
    (n : ℕ) (hn : Even n) :
    (n : ℝ) + 3 / 2 < c ↔ n = 0 ∨ n = 2 ∨ n = 4 := by
  constructor
  · intro hnc
    obtain ⟨m, rfl⟩ := hn
    have hm : m < 3 := by
      by_contra hnot
      have hm3 : 3 ≤ m := Nat.le_of_not_gt hnot
      have hm3r : (3 : ℝ) ≤ m := by exact_mod_cast hm3
      norm_num at hnc hhi
      linarith
    interval_cases m <;> simp
  · rintro (rfl | rfl | rfl) <;> norm_num at hlo ⊢ <;> linarith

/-- The exact Paper 4 field-spectrum formulae and their generated scalar anchor. -/
structure Properties : Prop where
  scalar_anchor : ∀ L l, scalarEigenvalue L l = scaledEnergy L l
  vector_lowest : ∀ L, vectorEigenvalue L 1 = 4 / L ^ 2
  vector_lowest_multiplicity : vectorMultiplicity 1 = 6
  vector_generated : ∀ l, 1 ≤ l →
    Module.finrank ℂ (VectorPlusCarrier l) = vectorMultiplicity l / 2 ∧
      Module.finrank ℂ (VectorMinusCarrier l) = vectorMultiplicity l / 2
  tt_plus_casimir : ∀ k, spin4Casimir (ttPlusLeft k) (ttPlusRight k) = ttCasimir k
  tt_minus_casimir : ∀ k, spin4Casimir (ttMinusLeft k) (ttMinusRight k) = ttCasimir k
  tt_rough_casimir : ∀ L k, ttRoughEigenvalue L k = (ttCasimir k - 6) / L ^ 2
  tt_lowest : ∀ L, ttRoughEigenvalue L 2 = 6 / L ^ 2
  tt_lowest_multiplicity : ttMultiplicity 2 = 10
  tt_generated : ∀ k, 2 ≤ k →
    Module.finrank ℂ (TTPlusCarrier k) = ttBranchMultiplicity k ∧
      Module.finrank ℂ (TTMinusCarrier k) = ttBranchMultiplicity k
  tt_shift : ∀ L alpha k, ttShiftedEigenvalue L alpha k =
    ttRoughEigenvalue L k + (alpha + 6) / L ^ 2
  spin_parity_exchange : ∀ k,
    (TauPlusPositiveDegree k ↔ TauMinusNegativeDegree k) ∧
    (TauPlusNegativeDegree k ↔ TauMinusPositiveDegree k)
  spinor_generated : ∀ k,
    Module.finrank ℂ (SpinorPlusCarrier k) = diracMultiplicity k ∧
      Module.finrank ℂ (SpinorMinusCarrier k) = diracMultiplicity k

theorem sourceRP3FieldSpectrumProperties : Properties where
  scalar_anchor := scalarEigenvalue_eq_source_scaled
  vector_lowest := vectorEigenvalue_one
  vector_lowest_multiplicity := vectorMultiplicity_one
  vector_generated := fun _ hl => generated_vector_branch_finrank hl
  tt_plus_casimir := tt_plus_Casimir
  tt_minus_casimir := tt_minus_Casimir
  tt_rough_casimir := ttRough_from_Casimir
  tt_lowest := ttRoughEigenvalue_two
  tt_lowest_multiplicity := ttMultiplicity_two
  tt_generated := fun _ hk => generated_tt_branch_finrank hk
  tt_shift := ttShifted_eq_rough_add
  spin_parity_exchange := fun k =>
    ⟨tauPlus_positive_iff_tauMinus_negative k,
      tauPlus_negative_iff_tauMinus_positive k⟩
  spinor_generated := generated_spinor_branch_finrank

end GeneratedFoundations.Physical.SourceRP3FieldSpectrum
