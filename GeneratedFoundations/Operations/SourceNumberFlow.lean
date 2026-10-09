module

public import GeneratedFoundations.Operations.SourceSpinCornerFlow
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The vacuum-preserving flow of the compressed Gaussian number operator

The generator is the product of the actual compressed differential raising
and lowering operators. Its two-mode matrix has eigenvalues zero and one.
The exponential acts on the original Hilbert space, fixes the Gaussian
vacuum and the orthogonal complement, and has least positive period `2π`.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix.Norms.Operator
open MeasureTheory
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.GaussianAffineLadder (embedding)
open GeneratedFoundations.Operations.HermiteFamily
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Operations.SourceSpinCornerFlow (exp_corner)

namespace GeneratedFoundations.Operations.SourceNumberFlow

def numberMatrix : Mat2 := !![0, 0; 0, 1]

theorem numberMatrix_eq_raising_mul_lowering :
    numberMatrix = raisingMatrix * loweringMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [numberMatrix, raisingMatrix, loweringMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The matrix represents the existing bounded differential compression on all of `L²`. -/
theorem compressedNumber_eq_corner {b : ℝ} (hb : 0 < b) :
    compressedNumber hb = corner hb numberMatrix := by
  change compressedRaising hb * compressedLowering hb = corner hb numberMatrix
  rw [numberMatrix_eq_raising_mul_lowering, corner_mul, corner_raising, corner_lowering]

theorem compressedNumber_apply {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    compressedNumber hb F = inner ℂ (firstState hb) F • firstState hb := by
  rw [compressedNumber_eq_corner, corner_apply]
  simp [numberMatrix]

theorem compressedNumber_eq_spin3 {b : ℝ} (hb : 0 < b) :
    compressedNumber hb = spin3 hb + (1 / 2 : ℂ) • projection hb := by
  change compressedRaising hb * compressedLowering hb =
    (compressedRaising hb * compressedLowering hb -
      (1 / 2 : ℂ) • projection hb) + (1 / 2 : ℂ) • projection hb
  abel

theorem numberMatrix_eq_spinMatrix3 :
    numberMatrix = spinMatrix3 + (1 / 2 : ℂ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [numberMatrix, spinMatrix3]

/-- Apply the differential number operator to the actual Schwartz representative of `PF`. -/
theorem number_compression {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    embedding (HermiteFamily.number b (projectedCore hb F)) = compressedNumber hb F := by
  simp only [projectedCore, map_add, map_smul, number_hermite, embedding_hermite]
  simp [state_one, compressedNumber_apply]

/-- The source representatives also retain their pointwise differential interpretation. -/
theorem number_representative_compression {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    corner hb numberMatrix (synthesis hb c) =ᵐ[volume]
      HermiteSource.raising b (HermiteSource.lowering b (representative b c)) := by
  rw [← compressedNumber_eq_corner]
  exact compressedNumber_differential hb c

@[simp] theorem compressedNumber_groundState {b : ℝ} (hb : 0 < b) :
    compressedNumber hb (groundState hb) = 0 := by
  simp [compressedNumber_apply, inner_first_ground hb]

@[simp] theorem compressedNumber_firstState {b : ℝ} (hb : 0 < b) :
    compressedNumber hb (firstState hb) = firstState hb := by
  simp [compressedNumber_apply, inner_self_eq_norm_sq_to_K, firstState_norm hb]

theorem compressedNumber_adjoint {b : ℝ} (hb : 0 < b) :
    (compressedNumber hb).adjoint = compressedNumber hb := by
  rw [compressedNumber_eq_corner, corner_adjoint]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [numberMatrix]

def numberFlowMatrix (t : ℝ) : Mat2 :=
  Matrix.diagonal ![1, Complex.exp (-Complex.I * (t : ℂ))]

theorem exp_numberMatrix (t : ℝ) :
    NormedSpace.exp ((-Complex.I * (t : ℂ)) • numberMatrix) = numberFlowMatrix t := by
  have h : (-Complex.I * (t : ℂ)) • numberMatrix =
      Matrix.diagonal ![0, -Complex.I * (t : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [numberMatrix]
  rw [h, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [numberFlowMatrix, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

theorem numberFlowMatrix_phase_spin (t : ℝ) :
    numberFlowMatrix t =
      Complex.exp (-Complex.I * (t : ℂ) / 2) • zRotation (-t) := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (1 : ℂ) = Complex.exp (-Complex.I * (t : ℂ) / 2) *
      Complex.exp (-Complex.I * ((-t : ℝ) : ℂ) / 2)
    rw [← Complex.exp_add,
      show -Complex.I * (t : ℂ) / 2 + -Complex.I * ((-t : ℝ) : ℂ) / 2 = 0 by
        push_cast
        ring,
      Complex.exp_zero]
  · simp [numberFlowMatrix, zRotation]
  · simp [numberFlowMatrix, zRotation]
  · change Complex.exp (-Complex.I * (t : ℂ)) =
      Complex.exp (-Complex.I * (t : ℂ) / 2) *
        Complex.exp (Complex.I * ((-t : ℝ) : ℂ) / 2)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

@[simp] theorem numberFlowMatrix_zero : numberFlowMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [numberFlowMatrix]

theorem numberFlowMatrix_add (s t : ℝ) :
    numberFlowMatrix (s + t) = numberFlowMatrix s * numberFlowMatrix t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [numberFlowMatrix, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  all_goals
    congr 1
    ring

theorem continuous_numberFlowMatrix : Continuous numberFlowMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp [numberFlowMatrix] <;> fun_prop

theorem numberFlowMatrix_mem_unitary (t : ℝ) :
    numberFlowMatrix t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [numberFlowMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Complex.conj_mul', Complex.norm_exp]

theorem numberFlowMatrix_det (t : ℝ) :
    Matrix.det (numberFlowMatrix t) = Complex.exp (-Complex.I * (t : ℂ)) := by
  simp [numberFlowMatrix]

/-- The controlled exponential of the actual compressed number operator. -/
def numberFlow {b : ℝ} (hb : 0 < b) (t : ℝ) : End :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • compressedNumber hb)

theorem numberFlow_control {b : ℝ} (hb : 0 < b) (t : ℝ) :
    numberFlow hb t = control hb (numberFlowMatrix t) := by
  rw [numberFlow, compressedNumber_eq_corner, ← map_smul, exp_corner, exp_numberMatrix]

/-- The ambient exponential changes only the first excited source coefficient. -/
theorem numberFlow_formula {b : ℝ} (hb : 0 < b) (t : ℝ) (F : ComplexL2) :
    numberFlow hb t F =
      F + (Complex.exp (-Complex.I * (t : ℂ)) - 1) • compressedNumber hb F := by
  rw [numberFlow_control]
  simp [SourceSpinCorner.control, projection_apply, corner_apply, numberFlowMatrix,
    compressedNumber_apply, smul_smul]
  module

theorem numberFlow_synthesis {b : ℝ} (hb : 0 < b) (t : ℝ) (c : Coordinates) :
    numberFlow hb t (synthesis hb c) =
      c 0 • groundState hb +
        (Complex.exp (-Complex.I * (t : ℂ)) * c 1) • firstState hb := by
  rw [numberFlow_formula, compressedNumber_synthesis]
  simp [synthesis, smul_smul]
  module

@[simp] theorem numberFlow_groundState {b : ℝ} (hb : 0 < b) (t : ℝ) :
    numberFlow hb t (groundState hb) = groundState hb := by
  simp [numberFlow_formula]

theorem numberFlow_firstState {b : ℝ} (hb : 0 < b) (t : ℝ) :
    numberFlow hb t (firstState hb) =
      Complex.exp (-Complex.I * (t : ℂ)) • firstState hb := by
  rw [numberFlow_formula, compressedNumber_firstState]
  module

theorem numberFlow_fixed_of_number_eq_zero {b : ℝ} (hb : 0 < b) (t : ℝ)
    (F : ComplexL2) (hF : compressedNumber hb F = 0) : numberFlow hb t F = F := by
  simp [numberFlow_formula, hF]

theorem numberFlow_mem_unitary {b : ℝ} (hb : 0 < b) (t : ℝ) :
    numberFlow hb t ∈ unitary End := by
  rw [numberFlow_control]
  exact control_mem_unitary hb _ (numberFlowMatrix_mem_unitary t)

def numberUnitary {b : ℝ} (hb : 0 < b) (t : ℝ) : unitary End :=
  ⟨numberFlow hb t, numberFlow_mem_unitary hb t⟩

@[simp] theorem numberFlow_zero {b : ℝ} (hb : 0 < b) : numberFlow hb 0 = 1 := by
  rw [numberFlow_control, numberFlowMatrix_zero, control_one]

theorem numberFlow_add {b : ℝ} (hb : 0 < b) (s t : ℝ) :
    numberFlow hb (s + t) = numberFlow hb s * numberFlow hb t := by
  rw [numberFlow_control, numberFlow_control, numberFlow_control,
    numberFlowMatrix_add, control_mul]

theorem number_phase_eq_circle (t : ℝ) :
    Complex.exp (-Complex.I * (t : ℂ)) = (Circle.exp (-t) : ℂ) := by
  rw [Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem number_phase_eq_one_iff (t : ℝ) :
    Complex.exp (-Complex.I * (t : ℂ)) = 1 ↔
      ∃ k : ℤ, t = k * (2 * Real.pi) := by
  rw [number_phase_eq_circle]
  constructor
  · intro h
    have hc : Circle.exp (-t) = 1 := Subtype.ext h
    obtain ⟨k, hk⟩ := Circle.exp_eq_one.mp hc
    refine ⟨-k, ?_⟩
    push_cast
    linarith
  · rintro ⟨k, hk⟩
    have hc : Circle.exp (-t) = 1 := Circle.exp_eq_one.mpr ⟨-k, by
      push_cast
      linarith⟩
    exact congrArg (fun z : Circle => (z : ℂ)) hc

theorem numberFlowMatrix_eq_one_iff (t : ℝ) :
    numberFlowMatrix t = 1 ↔ ∃ k : ℤ, t = k * (2 * Real.pi) := by
  rw [← number_phase_eq_one_iff]
  constructor
  · intro h
    simpa [numberFlowMatrix] using congrArg (fun M : Mat2 => M 1 1) h
  · intro h
    have h' : Complex.exp (-(Complex.I * (t : ℂ))) = 1 := by
      simpa only [neg_mul] using h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [numberFlowMatrix, h']

@[simp] theorem numberFlowMatrix_two_pi : numberFlowMatrix (2 * Real.pi) = 1 :=
  (numberFlowMatrix_eq_one_iff _).mpr ⟨1, by simp⟩

theorem numberFlowMatrix_periodic_iff (t : ℝ) :
    Function.Periodic numberFlowMatrix t ↔ ∃ k : ℤ, t = k * (2 * Real.pi) := by
  rw [← numberFlowMatrix_eq_one_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h s
    rw [numberFlowMatrix_add, h, mul_one]

theorem numberFlowMatrix_periodic :
    Function.Periodic numberFlowMatrix (2 * Real.pi) :=
  (numberFlowMatrix_periodic_iff _).mpr ⟨1, by simp⟩

theorem numberFlowMatrix_least_positive_period :
    IsLeast {t : ℝ | 0 < t ∧ Function.Periodic numberFlowMatrix t} (2 * Real.pi) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨⟨hp, numberFlowMatrix_periodic⟩, ?_⟩
  intro t ht
  obtain ⟨k, hk⟩ := (numberFlowMatrix_periodic_iff t).mp ht.2
  have hkpos : (0 : ℝ) < k := (mul_pos_iff_of_pos_right hp).mp (by
    rw [← hk]
    exact ht.1)
  have hkpos_int : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hkone_int : (1 : ℤ) ≤ k := by omega
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hkone_int
  calc
    2 * Real.pi = 1 * (2 * Real.pi) := (one_mul _).symm
    _ ≤ (k : ℝ) * (2 * Real.pi) := mul_le_mul_of_nonneg_right hkone hp.le
    _ = t := hk.symm

theorem numberFlow_eq_one_iff {b : ℝ} (hb : 0 < b) (t : ℝ) :
    numberFlow hb t = 1 ↔ ∃ k : ℤ, t = k * (2 * Real.pi) := by
  rw [numberFlow_control, ← numberFlowMatrix_eq_one_iff]
  constructor
  · intro h
    exact control_injective hb (h.trans (control_one hb).symm)
  · intro h
    rw [h, control_one]

@[simp] theorem numberFlow_two_pi {b : ℝ} (hb : 0 < b) :
    numberFlow hb (2 * Real.pi) = 1 :=
  (numberFlow_eq_one_iff hb _).mpr ⟨1, by simp⟩

theorem numberFlow_periodic_iff {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Function.Periodic (numberFlow hb) t ↔ ∃ k : ℤ, t = k * (2 * Real.pi) := by
  rw [← numberFlow_eq_one_iff hb]
  constructor
  · intro h
    simpa using h 0
  · intro h s
    rw [numberFlow_add, h, mul_one]

theorem numberFlow_least_positive_period {b : ℝ} (hb : 0 < b) :
    IsLeast {t : ℝ | 0 < t ∧ Function.Periodic (numberFlow hb) t} (2 * Real.pi) := by
  simpa only [numberFlow_periodic_iff, numberFlowMatrix_periodic_iff] using
    numberFlowMatrix_least_positive_period

end GeneratedFoundations.Operations.SourceNumberFlow
