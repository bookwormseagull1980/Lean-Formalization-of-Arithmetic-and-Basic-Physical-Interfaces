module

public import GeneratedFoundations.Geometry.SourceSpinorResolvent
public import GeneratedFoundations.Geometry.SourceSpinorCentralSectors
public import GeneratedFoundations.Geometry.SourceSpinorParitySpectrum
public import GeneratedFoundations.Geometry.SourceSpinorParityResolvent

/-!
# The generated spinor differential system

All carriers, frame derivatives, Haar measures and central operations in
this output are the constructions of the common source. The statement
accepts no connection, spectrum, spinor carrier or normalization parameter.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators LinearPMap
open GeneratedFoundations.Geometry.SourceSpinorConnection
open GeneratedFoundations.Geometry.SourceSpinorSpectralCore
open GeneratedFoundations.Geometry.SourceSpinorHaarBlock
open GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum
open GeneratedFoundations.Geometry.SourceSpinorCentralSectors

namespace GeneratedFoundations.Geometry.SourceSpinorSystem

structure Conclusions : Prop where
  connection_contraction :
    (∑ i : Fin 3, clifford i * spinConnection i) =
      (3 / 2 : ℂ) • (1 : Operations.SourceSpinCorner.Mat2)
  covariant_derivative : ∀ m,
    SourceSpinorDifferential.polynomialDirac m =
      ∑ i : Fin 3, (SourceSpinorDifferential.cliffordPair m i).comp
        (SourceSpinorCovariantDerivative.covariantPair m i)
  original_field_derivative : ∀ m i (A : SpinorBlock m),
    differential (normalizedSynthesis m i A) =
      normalizedSynthesis m i (diracBlock m A)
  block_multiplicities : ∀ m,
    SourceSpinorMultiplicity.plusMultiplicity m = m + 2 ∧
      SourceSpinorMultiplicity.minusMultiplicity m = m
  self_adjoint : IsSelfAdjoint closedDirac
  unique_extension : ∀ (S : SpinorL2 →ₗ.[ℂ] SpinorL2),
    IsSelfAdjoint S → finiteDirac ≤ S → S = closedDirac
  full_domain : ∀ F : SpinorL2,
    F ∈ closedDirac.domain ↔
      Summable (fun a : SpinIndex => eigenvalue a ^ 2 * ‖inner ℂ (eigenfield a) F‖ ^ 2)
  full_spectrum : ∀ z : ℂ,
    z ∈ SourceSpinorResolvent.spectrum ↔ ∃ k : ℕ,
      z = (((k : ℝ) + 3 / 2 : ℝ) : ℂ) ∨
        z = -(((k : ℝ) + 3 / 2 : ℝ) : ℂ)
  full_domain_gap : ∀ F : closedDirac.domain,
    (3 / 2 : ℝ) ^ 2 * ‖(F : SpinorL2)‖ ^ 2 ≤ ‖closedDirac F‖ ^ 2
  central_domain : ∀ F : closedDirac.domain,
    central (F : SpinorL2) ∈ closedDirac.domain
  central_commutation : ∀ F : closedDirac.domain,
    closedDirac ⟨central (F : SpinorL2), central_mem_closed_domain F⟩ =
      central (closedDirac F)
  sector_self_adjoint : ∀ odd,
    IsSelfAdjoint (SourceSpinorParitySpectrum.closedSectorDirac odd)
  sector_domain : ∀ odd (F : SourceSpinorParitySpectrum.sector odd),
    F ∈ (SourceSpinorParitySpectrum.closedSectorDirac odd).domain ↔
      (F : SpinorL2) ∈ closedDirac.domain
  sector_restriction : ∀ odd
      (F : (SourceSpinorParitySpectrum.closedSectorDirac odd).domain),
    ((SourceSpinorParitySpectrum.closedSectorDirac odd F :
      SourceSpinorParitySpectrum.sector odd) : SpinorL2) =
        closedDirac (SourceSpinorParitySpectrum.fullDomain odd F)
  sector_spectrum : ∀ odd (z : ℂ),
    z ∈ SourceSpinorParityResolvent.spectrum odd ↔ ∃ k : ℕ,
      (z = (((k : ℝ) + 3 / 2 : ℝ) : ℂ) ∧
        (-1 : ℂ) ^ k = SourceSpinorParitySpectrum.sign odd) ∨
      (z = -(((k : ℝ) + 3 / 2 : ℝ) : ℂ) ∧
        (-1 : ℂ) ^ (k + 1) = SourceSpinorParitySpectrum.sign odd)

theorem generated : Conclusions where
  connection_contraction := contracted_connection
  covariant_derivative := SourceSpinorCovariantDerivative.polynomialDirac_eq_contraction
  original_field_derivative := differential_normalizedSynthesis
  block_multiplicities := SourceSpinorMultiplicity.branch_multiplicities
  self_adjoint := closedDirac_selfAdjoint
  unique_extension := closedDirac_unique
  full_domain := closedDirac_domain
  full_spectrum := SourceSpinorResolvent.spectrum_half_integers
  full_domain_gap := closedDirac_norm_lower
  central_domain := central_mem_closed_domain
  central_commutation := closedDirac_central
  sector_self_adjoint := SourceSpinorParitySpectrum.closedSectorDirac_selfAdjoint
  sector_domain := SourceSpinorParitySpectrum.sector_domain_iff_full
  sector_restriction := SourceSpinorParitySpectrum.closedSectorDirac_is_restriction
  sector_spectrum := SourceSpinorParityResolvent.spectrum_labels

end GeneratedFoundations.Geometry.SourceSpinorSystem
