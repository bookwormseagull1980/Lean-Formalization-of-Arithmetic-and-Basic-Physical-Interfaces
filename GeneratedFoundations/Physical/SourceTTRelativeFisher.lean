module

public import GeneratedFoundations.Physical.SourceTTFrameComparison
public import GeneratedFoundations.Physical.SourceTTFrameRelativeResponse

/-!
# Relative response of the unchanged tensor vertex

The same tensor insertion is compared in the massive precision and in
its pure-kinetic reference precision. Their Fisher forms differ by a
scalar generalized eigenvalue. This relative form is exactly the kernel
already used in the finite spectral readout. No frequency-dependent
change of the tensor perturbation is made.

The first nonconstant scalar shell supplies an explicit realization in
the original nine-coordinate Gaussian law. The scalar precision formula
below also records the comparison for an arbitrary positive kinetic
precision, with the same source-gradient tensor insertion on both sides.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory

namespace GeneratedFoundations.Physical.SourceTTRelativeFisher

open SourceTTFrameComparison
open Geometry.SourceAxisTT
open Operations.FiniteMatrixGaussian

/-- All three original real adjoint rows are retained. -/
def tensorFisher (A b a₁ a₂ c₁ c₂ : ℝ) : ℝ :=
  3 * cov[score (vertex (ttMatrix a₁ a₂)),
    score (vertex (ttMatrix c₁ c₂)); law (precision (A + b))]

theorem tensorFisher_eq {A b : ℝ} (hA : 0 < A) (hb : 0 ≤ b)
    (a₁ a₂ c₁ c₂ : ℝ) :
    tensorFisher A b a₁ a₂ c₁ c₂ =
      48 / (A + b) ^ 2 * (a₁ * c₁ + a₂ * c₂) := by
  rw [tensorFisher, row_covariance (by linarith : 0 < A + b)]
  ring

/-- The entire bilinear form has this relative eigenvalue, including
mixed polarizations. No division by a zero polarization is needed. -/
theorem tensorFisher_relative_form {A b : ℝ} (hA : 0 < A) (hb : 0 ≤ b)
    (a₁ a₂ c₁ c₂ : ℝ) :
    tensorFisher A b a₁ a₂ c₁ c₂ =
      SourceTensorResponseEndpoint.ttKernel A b * tensorFisher A 0 a₁ a₂ c₁ c₂ := by
  rw [tensorFisher_eq hA hb, tensorFisher_eq hA (by norm_num)]
  unfold SourceTensorResponseEndpoint.ttKernel
  simp only [add_zero]
  field_simp [hA.ne']

/-- The Gram matrix is measured on the original unit plus and cross
polarizations. -/
def polarizationFisher (A b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![tensorFisher A b 1 0 1 0, tensorFisher A b 1 0 0 1;
    tensorFisher A b 0 1 1 0, tensorFisher A b 0 1 0 1]

theorem polarizationFisher_eq {A b : ℝ} (hA : 0 < A) (hb : 0 ≤ b) :
    polarizationFisher A b = (48 / (A + b) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [polarizationFisher, tensorFisher_eq hA hb]

theorem polarizationFisher_relative {A b : ℝ} (hA : 0 < A) (hb : 0 ≤ b) :
    polarizationFisher A b = SourceTensorResponseEndpoint.ttKernel A b •
      polarizationFisher A 0 := by
  rw [polarizationFisher_eq hA hb, polarizationFisher_eq hA (by norm_num)]
  simp only [add_zero, smul_smul]
  congr 1
  unfold SourceTensorResponseEndpoint.ttKernel
  field_simp [hA.ne']

/-- The relative response operator is uniquely determined by the two
actual source Fisher forms, rather than by a choice of polarization
coordinates or a newly assigned response coefficient. -/
theorem relative_operator_unique {A b : ℝ} (hA : 0 < A) (hb : 0 ≤ b)
    (T : Matrix (Fin 2) (Fin 2) ℝ) :
    polarizationFisher A 0 * T = polarizationFisher A b ↔
      T = SourceTensorResponseEndpoint.ttKernel A b • 1 := by
  rw [polarizationFisher_relative hA hb,
    polarizationFisher_eq hA (by norm_num)]
  simp only [add_zero, smul_mul_assoc, Matrix.one_mul]
  have hc : (48 / A ^ 2 : ℝ) ≠ 0 := by positivity
  rw [smul_comm]
  exact smul_right_inj hc

/-- The reference response uses the same actual tensor vertex at zero
mass insertion, rather than an independently specified scalar readout. -/
def referenceResponse (omega : ℝ) : ℝ := shellTensorResponse omega 0

theorem referenceResponse_eq (omega : ℝ) :
    referenceResponse omega = 96 / (omega ^ 2 + 8) ^ 2 := by
  rw [referenceResponse, shellTensorResponse_eq (by norm_num)]
  simp

theorem referenceResponse_pos (omega : ℝ) : 0 < referenceResponse omega := by
  rw [referenceResponse_eq]
  positivity

def referenceCalibration (omega : ℝ) : ℝ := (referenceResponse omega)⁻¹

theorem referenceCalibration_pos (omega : ℝ) : 0 < referenceCalibration omega :=
  inv_pos.mpr (referenceResponse_pos omega)

/-- Unit response of this fixed reference fixes its positive comparison
unit uniquely. The resulting frequency factor is calculated, not fitted. -/
theorem referenceCalibration_unique (omega κ : ℝ) :
    κ * referenceResponse omega = 1 ↔ κ = referenceCalibration omega := by
  have hn := (referenceResponse_pos omega).ne'
  have hi : referenceCalibration omega * referenceResponse omega = 1 := by
    exact inv_mul_cancel₀ hn
  constructor
  · intro h
    exact mul_right_cancel₀ hn (h.trans hi.symm)
  · intro h
    rw [h]
    exact hi

theorem referenceCalibration_eq (omega : ℝ) :
    referenceCalibration omega = (omega ^ 2 + 8) ^ 2 / 96 := by
  rw [referenceCalibration, referenceResponse_eq]
  simp

def relativeShellResponse (omega b : ℝ) : ℝ :=
  shellTensorResponse omega b / referenceResponse omega

theorem relativeShellResponse_eq {omega b : ℝ} (hb : 0 ≤ b) :
    relativeShellResponse omega b =
      SourceTensorResponseEndpoint.ttKernel (omega ^ 2 + 8) b := by
  rw [relativeShellResponse, shellTensorResponse_eq hb, referenceResponse_eq]
  unfold SourceTensorResponseEndpoint.ttKernel
  have hA : omega ^ 2 + 8 ≠ 0 := by positivity
  field_simp

/-- The previously used kinetic Gaussian comparison is the relative
response of this unchanged tensor vertex in the explicit source shell. -/
theorem relative_shell_eq_kinetic_comparison {omega b : ℝ} (hb : 0 ≤ b) :
    relativeShellResponse omega b =
      SourceTTResponseNormalization.gaussianModeResponse (omega ^ 2 + 8) b := by
  rw [relativeShellResponse_eq hb,
    SourceTTResponseNormalization.gaussianModeResponse_eq _ _ (by positivity)]

/-- The curvature is taken on the actual nonlinear frame path in the
same-source relative likelihood. The three original rows and the factor
two used in the existing response are both retained. -/
def shellRelativeKLHessian (omega b : ℝ) : ℝ :=
  3 * 2 * deriv (fun t => deriv
    (SourceTTFrameRelativeResponse.relativeResponse (shellPrecision omega b)) t) 0

theorem shellRelativeKLHessian_eq {omega b : ℝ} (hb : 0 ≤ b) :
    shellRelativeKLHessian omega b = shellTensorResponse omega b := by
  have hp : 4 < shellPrecision omega b := by
    unfold shellPrecision
    nlinarith [sq_nonneg omega]
  rw [shellRelativeKLHessian,
    (SourceTTFrameRelativeResponse.relativeResponse_secondDeriv_zero hp).deriv]
  exact SourceTTFrameRelativeResponse.shell_relative_hessian_eq_tensor_response hb

theorem complete_relative_KL_kernel {omega b : ℝ} (hb : 0 ≤ b) :
    shellRelativeKLHessian omega b / shellRelativeKLHessian omega 0 =
      SourceTensorResponseEndpoint.ttKernel (omega ^ 2 + 8) b := by
  rw [shellRelativeKLHessian_eq hb, shellRelativeKLHessian_eq (by norm_num)]
  exact relativeShellResponse_eq hb

theorem calibrated_original_response {omega b : ℝ} (hb : 0 ≤ b) :
    referenceCalibration omega * shellTensorResponse omega b =
      SourceTensorResponseEndpoint.ttKernel (omega ^ 2 + 8) b := by
  rw [← relativeShellResponse_eq hb, relativeShellResponse, referenceCalibration]
  ring

@[simp] theorem relativeShellResponse_zero (omega : ℝ) :
    relativeShellResponse omega 0 = 1 := by
  exact div_self (referenceResponse_pos omega).ne'

/-- The logarithmic mass variation acts on the actual relative tensor
response with its pure-kinetic reference fixed. -/
theorem relativeShellResponse_hasDerivAt {omega b : ℝ} (hb : 0 ≤ b) (z : ℝ) :
    HasDerivAt (fun t => relativeShellResponse omega (Real.exp t * b))
      (-2 * SourceTensorResponseEndpoint.massWeightedResponse
        (SourceTensorResponseEndpoint.massFraction (omega ^ 2 + 8) (Real.exp z * b))) z := by
  have hp : omega ^ 2 + 8 + Real.exp z * b ≠ 0 := by positivity
  apply (SourceTTResponseNormalization.logMassKernel_hasDerivAt
    (omega ^ 2 + 8) b z hp).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    relativeShellResponse_eq (mul_nonneg (Real.exp_pos t).le hb)

theorem relativeShellResponse_mass_capacity {omega b : ℝ} (hb : 0 ≤ b) (z : ℝ) :
    -(deriv (fun t => relativeShellResponse omega (Real.exp t * b)) z) / 2 =
      SourceTensorResponseEndpoint.massWeightedResponse
        (SourceTensorResponseEndpoint.massFraction (omega ^ 2 + 8) (Real.exp z * b)) := by
  rw [(relativeShellResponse_hasDerivAt hb z).deriv]
  ring

end GeneratedFoundations.Physical.SourceTTRelativeFisher
