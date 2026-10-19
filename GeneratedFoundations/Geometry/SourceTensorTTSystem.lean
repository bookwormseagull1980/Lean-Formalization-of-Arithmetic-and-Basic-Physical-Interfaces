module

public import GeneratedFoundations.Geometry.SourceTensorTTSpectrum

/-!
# The generated transverse--traceless differential system

The carrier, Koszul connection, Haar norm and weak differential constraints
all belong to the original generated source. The complete operator is the
unique self-adjoint closure of its differentiated finite core. This output
accepts no tensor carrier, connection, branch, spectral gap or boundary
parameter.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators LinearPMap
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceTensorCovariantDerivative
open GeneratedFoundations.Geometry.SourceTensorTTBlock
open GeneratedFoundations.Geometry.SourceTensorTTField
open GeneratedFoundations.Geometry.SourceTensorTTClosedSpectrum

namespace GeneratedFoundations.Geometry.SourceTensorTTSystem

structure Conclusions : Prop where
  original_covariant_derivative : ∀ m v H,
    ∀ i : Fin 3, covariant i (coefficientTensor m v H) =
      coefficientTensor m v (coefficientCovariant m i H)
  original_rough_derivative : ∀ m v H,
    rough (coefficientTensor m v H) = coefficientTensor m v (coefficientRough m H)
  tracefree_dimension : ∀ m,
    Module.finrank ℂ (SourceTensorTracefreeBlock.tracefreeSpace m) = 5 * (m + 1)
  tt_differential_identity : ∀ m (H : ttSpace m),
    ttRough m H = ttCurl m (ttCurl m H) - (3 : ℂ) • H
  complete_field_basis : finiteTTCoreᗮ = ⊥
  self_adjoint : IsSelfAdjoint closedRough
  unique_extension : ∀ (S : ttField →ₗ.[ℂ] ttField),
    IsSelfAdjoint S → finiteRough ≤ S → S = closedRough
  full_domain : ∀ H : ttField,
    H ∈ closedRough.domain ↔
      Summable (fun a : TTIndex => roughEigenvalue a ^ 2 * ‖inner ℂ (eigenfield a) H‖ ^ 2)
  full_spectrum : ∀ z : ℂ,
    z ∈ SourceTensorTTResolvent.spectrum ↔ ∃ k : ℕ, Even k ∧ 2 ≤ k ∧
      z = (((k : ℝ) * ((k : ℝ) + 2) - 2 : ℝ) : ℂ)
  full_domain_lower_bound : ∀ H : closedRough.domain,
    6 * ‖(H : ttField)‖ ^ 2 ≤ (inner ℂ (H : ttField) (closedRough H)).re
  attained_spectral_bottom : (6 : ℂ) ∈ SourceTensorTTResolvent.spectrum

theorem generated : Conclusions where
  original_covariant_derivative := fun m v H i => covariant_coefficientTensor m i v H
  original_rough_derivative := rough_coefficientTensor
  tracefree_dimension := SourceTensorTracefreeBlock.tracefree_finrank
  tt_differential_identity := ttRough_eq_curl_square
  complete_field_basis := finiteTTCore_orthogonal
  self_adjoint := closedRough_selfAdjoint
  unique_extension := closedRough_unique
  full_domain := closedRough_domain
  full_spectrum := SourceTensorTTSpectrum.spectrum_labels
  full_domain_lower_bound := closedRough_quadratic_lower
  attained_spectral_bottom := SourceTensorTTSpectrum.spectral_bottom.1

end GeneratedFoundations.Geometry.SourceTensorTTSystem
