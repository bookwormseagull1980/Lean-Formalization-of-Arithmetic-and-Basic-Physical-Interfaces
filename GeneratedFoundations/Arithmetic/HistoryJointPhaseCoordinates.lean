module

public import GeneratedFoundations.Arithmetic.HistoryJointPhaseFlow
public import GeneratedFoundations.Arithmetic.HistoryJointCircleAction
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral coordinates of the complete arithmetic charge flow

The basis diagonalizes the charge already acting on the original carrier.
It is not a prescribed spectrum or a replacement carrier. The matrix
exponential and the Hilbert-space exponential are compared by continuous
algebra equivalences, retaining all actual multiplicities.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryJointPhaseCoordinates

open HistoryJointCharge

abbrev Index (n : ℕ) := Fin (Module.finrank ℂ (Space n))
abbrev MatrixModel (n : ℕ) := Matrix (Index n) (Index n) ℂ

theorem symmetric (n : ℕ) : (generatedResponse n).IsSymmetric :=
  HistoryJointQuadraticResponse.response_symmetric n n 1

def basis (n : ℕ) : OrthonormalBasis (Index n) ℂ (Space n) :=
  (symmetric n).eigenvectorBasis rfl

def eigenvalue (n : ℕ) : Index n → ℝ := (symmetric n).eigenvalues rfl

def coordinates (n : ℕ) : Module.End ℂ (Space n) ≃⋆ₐ[ℂ] MatrixModel n :=
  LinearMap.toMatrixOrthonormal (basis n)

theorem generatedResponse_basis (n : ℕ) (i : Index n) :
    generatedResponse n (basis n i) = (eigenvalue n i : ℂ) • basis n i :=
  (symmetric n).apply_eigenvectorBasis rfl i

theorem charge_matrix (n : ℕ) :
    coordinates n (generatedResponse n) = Matrix.diagonal (fun i => (eigenvalue n i : ℂ)) :=
  (symmetric n).toMatrix_eigenvectorBasis rfl

theorem normalizedCharge_matrix (n : ℕ) :
    coordinates n (HistoryChargeContent.normalizedResponse n) =
      Matrix.diagonal (fun i => (eigenvalue n i : ℂ) / (2 * n)) := by
  rw [HistoryChargeContent.normalizedResponse, map_smul, charge_matrix,
    ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

abbrev End (n : ℕ) := HistoryJointPhaseFlow.End n

local instance (n : ℕ) : NormedRing (End n) := ContinuousLinearMap.toNormedRing
local instance (n : ℕ) : NormedAlgebra ℂ (End n) := ContinuousLinearMap.toNormedAlgebra
local instance (n : ℕ) : IsTopologicalRing (End n) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

def continuousCoordinates (n : ℕ) : End n ≃ₐ[ℂ] MatrixModel n :=
  (HistoryJointPhaseFlow.continuousModel n).symm.trans (coordinates n).toAlgEquiv

theorem continuousCoordinates_model (n : ℕ) (A : Module.End ℂ (Space n)) :
    continuousCoordinates n (HistoryJointPhaseFlow.continuousModel n A) =
      coordinates n A := by simp [continuousCoordinates]

theorem flow_matrix_eq_exp (n : ℕ) (t : ℝ) :
    coordinates n (HistoryJointPhaseFlow.flow n n 1 t) =
      NormedSpace.exp ((Complex.I * (t : ℂ)) • coordinates n (generatedResponse n)) := by
  have he := congrArg (continuousCoordinates n) (HistoryJointPhaseFlow.flow_eq_exp n n 1 t)
  have hc : Continuous (continuousCoordinates n) :=
    (continuousCoordinates n).toLinearMap.continuous_of_finiteDimensional
  have hm := Operations.FinitePhaseFlow.map_exp (continuousCoordinates n).toAlgHom hc
    ((Complex.I * (t : ℂ)) • HistoryJointPhaseFlow.continuousModel n (generatedResponse n))
  change continuousCoordinates n
    (HistoryJointPhaseFlow.continuousModel n (HistoryJointPhaseFlow.flow n n 1 t)) =
    continuousCoordinates n (NormedSpace.exp ((Complex.I * (t : ℂ)) •
      HistoryJointPhaseFlow.continuousModel n (generatedResponse n))) at he
  change continuousCoordinates n (NormedSpace.exp ((Complex.I * (t : ℂ)) •
      HistoryJointPhaseFlow.continuousModel n (generatedResponse n))) =
    NormedSpace.exp (continuousCoordinates n ((Complex.I * (t : ℂ)) •
      HistoryJointPhaseFlow.continuousModel n (generatedResponse n))) at hm
  rw [continuousCoordinates_model] at he
  exact he.trans (hm.trans (congrArg NormedSpace.exp (by
    rw [map_smul, continuousCoordinates_model])))

theorem flow_matrix (n : ℕ) (t : ℝ) :
    coordinates n (HistoryJointPhaseFlow.flow n n 1 t) =
      Matrix.diagonal (fun i => Complex.exp (Complex.I * (t : ℂ) * eigenvalue n i)) := by
  rw [flow_matrix_eq_exp, charge_matrix, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  simp [← Complex.exp_eq_exp_ℂ]

theorem flow_basis (n : ℕ) (t : ℝ) (i : Index n) :
    HistoryJointPhaseFlow.flow n n 1 t (basis n i) =
      Complex.exp (Complex.I * (t : ℂ) * eigenvalue n i) • basis n i := by
  apply (basis n).repr.injective
  apply PiLp.ext
  intro j
  have h := congrArg (fun A : MatrixModel n => A j i) (flow_matrix n t)
  simp only [coordinates, LinearMap.toMatrixOrthonormal_apply_apply,
    ← OrthonormalBasis.repr_apply_apply, map_smul, PiLp.smul_apply,
    OrthonormalBasis.repr_self, PiLp.single_apply, Matrix.diagonal_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero] at h ⊢
  by_cases hji : j = i <;> simpa only [hji, ite_true, ite_false] using h

/-- The normalized flow uses the charge normalization already fixed by
the primitive integer character. At root zero that normalization and the
flow are both trivial; no division hypothesis is suppressed. -/
def normalizedFlow (n : ℕ) (t : ℝ) : Module.End ℂ (Space n) :=
  HistoryJointPhaseFlow.flow n n 1 (t / (2 * n))

theorem normalizedFlow_matrix (n : ℕ) (t : ℝ) :
    coordinates n (normalizedFlow n t) = Matrix.diagonal (fun i =>
      Complex.exp (Complex.I * (t : ℂ) * ((eigenvalue n i : ℂ) / (2 * n)))) := by
  rw [normalizedFlow, flow_matrix]
  congr 1
  funext i
  congr 1
  push_cast
  ring

theorem normalizedFlow_matrix_eq_exp (n : ℕ) (t : ℝ) :
    coordinates n (normalizedFlow n t) = NormedSpace.exp
      ((Complex.I * (t : ℂ)) • coordinates n (HistoryChargeContent.normalizedResponse n)) := by
  rw [normalizedFlow_matrix, normalizedCharge_matrix,
    ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  simp [← Complex.exp_eq_exp_ℂ]

theorem normalizedFlow_basis (n : ℕ) (t : ℝ) (i : Index n) :
    normalizedFlow n t (basis n i) = Complex.exp
      (Complex.I * (t : ℂ) * ((eigenvalue n i : ℂ) / (2 * n))) • basis n i := by
  rw [normalizedFlow, flow_basis]
  congr 2
  push_cast
  ring

/-- The normalized period is determined by the actual primitive charge,
not by a restriction to the two source coordinates. -/
theorem normalizedFlow_eq_one_iff {n : ℕ} (hn : 0 < n) (t : ℝ) :
    normalizedFlow n t = 1 ↔ ∃ k : ℤ, t = k * (4 * n * Real.pi) := by
  have hn' : (2 * n : ℝ) ≠ 0 := by positivity
  rw [normalizedFlow, HistoryJointCircleAction.generatedFlow_eq_one_iff hn]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have he := (div_eq_iff hn').mp hk
    nlinarith [he]
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    apply (div_eq_iff hn').mpr
    ring

theorem normalizedFlow_add (n : ℕ) (s t : ℝ) :
    normalizedFlow n (s + t) = normalizedFlow n s * normalizedFlow n t := by
  simp only [normalizedFlow, add_div, HistoryJointPhaseFlow.flow_add]

theorem normalizedFlow_periodic_iff {n : ℕ} (hn : 0 < n) (t : ℝ) :
    Function.Periodic (normalizedFlow n) t ↔ ∃ k : ℤ, t = k * (4 * n * Real.pi) := by
  constructor
  · intro hp
    apply (normalizedFlow_eq_one_iff hn t).mp
    simpa only [zero_add, normalizedFlow, zero_div, HistoryJointPhaseFlow.flow_zero]
      using hp 0
  · intro hp s
    rw [normalizedFlow_add, (normalizedFlow_eq_one_iff hn t).mpr hp, mul_one]

theorem normalizedFlow_least_positive_period {n : ℕ} (hn : 0 < n) :
    IsLeast {t : ℝ | 0 < t ∧ Function.Periodic (normalizedFlow n) t}
      (4 * n * Real.pi) := by
  have hpos : (0 : ℝ) < 4 * n * Real.pi := by positivity
  refine ⟨⟨hpos, (normalizedFlow_periodic_iff hn _).mpr ⟨1, by simp⟩⟩, ?_⟩
  rintro t ⟨ht, hp⟩
  obtain ⟨k, rfl⟩ := (normalizedFlow_periodic_iff hn t).mp hp
  have hk : (0 : ℝ) < k := (mul_pos_iff_of_pos_right hpos).mp ht
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hk'' : (1 : ℝ) ≤ k := by exact_mod_cast hk'
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk'' hpos.le

structure Conclusions : Prop where
  actual_charge : ∀ n, coordinates n (generatedResponse n) =
    Matrix.diagonal (fun i => (eigenvalue n i : ℂ))
  actual_normalization : ∀ n, coordinates n (HistoryChargeContent.normalizedResponse n) =
    Matrix.diagonal (fun i => (eigenvalue n i : ℂ) / (2 * n))
  exact_flow_matrix : ∀ n t, coordinates n (HistoryJointPhaseFlow.flow n n 1 t) =
    Matrix.diagonal (fun i => Complex.exp (Complex.I * (t : ℂ) * eigenvalue n i))
  every_original_basis_vector : ∀ n t i,
    HistoryJointPhaseFlow.flow n n 1 t (basis n i) =
      Complex.exp (Complex.I * (t : ℂ) * eigenvalue n i) • basis n i
  normalized_exponential : ∀ n t,
    coordinates n (normalizedFlow n t) = NormedSpace.exp
      ((Complex.I * (t : ℂ)) • coordinates n (HistoryChargeContent.normalizedResponse n))
  actual_normalized_kernel : ∀ n, 0 < n → ∀ t,
    normalizedFlow n t = 1 ↔ ∃ k : ℤ, t = k * (4 * n * Real.pi)
  actual_normalized_period : ∀ n, 0 < n →
    IsLeast {t : ℝ | 0 < t ∧ Function.Periodic (normalizedFlow n) t}
      (4 * n * Real.pi)

theorem generated : Conclusions where
  actual_charge := charge_matrix
  actual_normalization := normalizedCharge_matrix
  exact_flow_matrix := flow_matrix
  every_original_basis_vector := flow_basis
  normalized_exponential := normalizedFlow_matrix_eq_exp
  actual_normalized_kernel := fun _ => normalizedFlow_eq_one_iff
  actual_normalized_period := fun _ => normalizedFlow_least_positive_period

end GeneratedFoundations.Arithmetic.HistoryJointPhaseCoordinates
