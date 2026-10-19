module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsFlow
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsFullReduction
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsFock
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsFrameResponse

/-!
# Source-generated Yang--Mills closure

The local theorem concerns the complete restoring potential, nonlinear
curvature and frame-relative connection response. All three are transported
under the same generated local frame change. Their actual second derivatives
give the radial coefficient and a zero radial--connection mixed term.

The spectral theorem concerns the radial mode and the full generated
representation-labelled coclosed tower. Its modal form has a unique
self-adjoint closure and an attained positive lower edge. The accompanying
`SourceHaarYangMillsHessian` construction differentiates the original Haar
fields and proves the actual action-to-operator identity on their complete
core. `CanonicalYangMills` assembles that differential realization at the
generated IR radius together with the nonlinear local response.

The earlier one-coordinate-per-shell truncations remain useful finite
witnesses.  They are identified below only as restrictions of the generated
eigenvalue law; they no longer carry the word `complete`.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsClosure

open SourceConformalResponse SourceInternalYangMillsResponse
open SourceRadialMassIntertwiner (scoreVariance)
open SourceFourDimensionalYangMills
open SourceGeneratedYangMillsGap SourceGeneratedYangMillsAction
open SourceGeneratedYangMillsEquation SourceGeneratedYangMillsCoercivity
open SourceGeneratedYangMillsFlow
open SourceGeneratedYangMillsResponseHessian
open SourceGeneratedYangMillsFrameResponse
open SourceGeneratedYangMillsPhysicalHessian
open SourceGeneratedYangMillsFullReduction
open SourceGeneratedYangMillsFock

/-- A finite shell witness combining the nonlinear local curvature density
with the canonical one-coordinate shell restriction.  This is not the
definition of the complete Hessian. -/
def finiteWitnessAction {N : ℕ} (L z : ℝ)
    (A : ColourConnectionJet) (x : SpectralConfiguration N) : ℝ :=
  (1 / 2 : ℝ) * euclideanCurvatureDensity A + spectralAction L z x

theorem finiteWitnessAction_nonneg {N : ℕ} {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) (A : ColourConnectionJet)
    (x : SpectralConfiguration N) :
    0 ≤ finiteWitnessAction L z A x := by
  unfold finiteWitnessAction
  exact add_nonneg
    (mul_nonneg (by norm_num) (euclideanCurvatureDensity_nonneg A))
    (spectralAction_nonneg hL hz x)

theorem finiteWitnessAction_coercive {N : ℕ} (L z : ℝ)
    (A : ColourConnectionJet) (x : SpectralConfiguration N) :
    (1 / 2 : ℝ) * euclideanCurvatureDensity A +
        (1 / 2 : ℝ) * generatedYangMillsGapSq L z *
          SpectralConfiguration.normSq x ≤
      finiteWitnessAction L z A x := by
  have hspec := spectralAction_coercive L z x
  unfold finiteWitnessAction
  nlinarith

/-- Framework-internal generated Yang--Mills theorem.  Every structural
constant belongs to the generated source.  `L` ranges over states of the
condensed branch; it is not a field of the root datum. -/
structure Conclusions : Prop where
  unique_condensed_branch : ∀ L (hL : criticalRadius < L),
    0 < condensedAmplitude L hL ∧
    completeResponse (condensedAmplitude L hL) = generatedTarget L ∧
    0 < generatedYangMillsGapSq L (condensedAmplitude L hL)
  nonlinear_local_gauge_invariance : ∀ z radial q A,
    localActionDensity z radial (transformMatrixConnectionJet q A) =
      localActionDensity z radial A
  common_frame_gauge_invariance : ∀ L z radial q A U,
    commonFrameResponseAction L z radial (transformMatrixConnectionJet q A)
        (transformFrameJet q U) = commonFrameResponseAction L z radial A U
  common_source_frame_restriction : ∀ L z radial A,
    commonFrameResponseAction L z radial (colourMatrixConnectionJet A) sourceFrame =
      sourceCommonResponseAction L z radial (colourMatrixConnectionJet A)
  nonlinear_common_second_derivative : ∀ {z : ℝ}, 0 < z → ∀ L radial A,
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ =>
      sourceCommonResponseAction L z (u * radial) (scaleMatrixConnectionJet u A)) t)
      (commonQuadraticSecondVariation L z radial A) 0
  nonlinear_mixed_second_derivative : ∀ L z radial A,
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      sourceCommonResponseAction L z (s * radial) (scaleMatrixConnectionJet t A)) 0)
      0 0
  common_local_mixed_hessian_zero : ∀ L z radial A,
    commonHessianPairing L z radial 0 zeroMatrixConnectionJet A = 0
  complete_modal_mixed_hessian_zero : ∀ L z r c mode,
    hessianPairing L z (radialCore r) (coclosedCore mode c) = 0
  complete_coclosed_from_source : ∀ L z mode,
    SourceGeneratedCoclosedOneForm.modeEigenvalue L z mode =
      SourceGeneratedCoclosedOneForm.branchCasimir mode / L ^ 2 +
        coclosedResponseShift L z
  complete_radial_from_source : ∀ z,
    normalizedRadialMassSq z =
      scoreVariance z * SourceConformalResponse.completeCurvature z
  complete_radial_restoring_derivative : ∀ {z : ℝ}, 0 < z →
    HasDerivAt (SourceGeneratedRadialVariation.sourceRadialForce z)
      (normalizedRadialMassSq z) 0
  complete_source_decomposition : ∀ L z x,
    hessianQuadratic L z x = sourceDecomposedQuadratic L z x
  complete_hessian_selfAdjoint : ∀ L z,
    IsSelfAdjoint (operator L z)
  complete_hessian_unique_closure : ∀ L z T,
    IsSelfAdjoint T → finiteCore L z ≤ T → T = operator L z
  complete_hessian_domain : ∀ L z f,
    f ∈ (operator L z).domain ↔
      Summable (fun mode : PhysicalMode =>
        physicalEigenvalue L z mode ^ 2 *
          ‖inner ℂ (physicalBasis mode) f‖ ^ 2)
  complete_hessian_coercive : ∀ L z x,
    generatedYangMillsGapSq L z * normSq x ≤ hessianQuadratic L z x
  complete_bottom_attained : ∀ L z,
    hessianQuadratic L z
        (Finsupp.single (minimizingMode L z) 1) =
      generatedYangMillsGapSq L z
  complete_condensed_gap_positive : ∀ L
      (hL : criticalRadius < L),
    0 < generatedYangMillsGapSq L (condensedAmplitude L hL)
  fock_vacuum_unique : ∀ {L z}, 0 < L → 0 < z → ∀ occupation,
    totalEnergy L z occupation = 0 ↔ occupation = vacuum
  fock_nonvacuum_gap : ∀ {L z}, 0 < L → 0 < z →
    ∀ {occupation}, occupation ≠ vacuum →
      generatedYangMillsGapSq L z ≤ totalEnergy L z occupation
  fock_gap_attained : ∀ L z,
    groundOccupation L z ≠ vacuum ∧
      totalEnergy L z (groundOccupation L z) = generatedYangMillsGapSq L z
  finite_witness_coercive : ∀ {N} L z A
      (x : SpectralConfiguration N),
    (1 / 2 : ℝ) * euclideanCurvatureDensity A +
        (1 / 2 : ℝ) * generatedYangMillsGapSq L z *
          SpectralConfiguration.normSq x ≤
      finiteWitnessAction L z A x
  finite_witness_semigroup : ∀ {N} L z s t
      (x : SpectralConfiguration N),
    spectralFlow L z s (spectralFlow L z t x) =
      spectralFlow L z (s + t) x

theorem conclusions : Conclusions where
  unique_condensed_branch := fun L hL => condensedAmplitude_spec L hL
  nonlinear_local_gauge_invariance := localActionDensity_gauge_invariant
  common_frame_gauge_invariance := commonFrameResponseAction_gauge_invariant
  common_source_frame_restriction := commonFrameResponseAction_sourceFrame
  nonlinear_common_second_derivative := sourceCommonResponseAction_secondDeriv
  nonlinear_mixed_second_derivative := sourceCommonResponseAction_mixed_secondDeriv_zero
  common_local_mixed_hessian_zero :=
    commonHessianPairing_radial_connection_zero
  complete_modal_mixed_hessian_zero :=
    hessianPairing_radial_coclosed_zero
  complete_coclosed_from_source :=
    SourceGeneratedCoclosedOneForm.modeEigenvalue_eq_sourceCasimir_add_shift
  complete_radial_from_source :=
    normalizedRadialMassSq_eq_scoreVariance_mul_completeCurvature
  complete_radial_restoring_derivative :=
    SourceGeneratedRadialVariation.sourceRadialForce_hasDerivAt_zero
  complete_source_decomposition :=
    hessianQuadratic_eq_sourceDecomposedQuadratic
  complete_hessian_selfAdjoint := operator_selfAdjoint
  complete_hessian_unique_closure :=
    SourceGeneratedYangMillsPhysicalHessian.selfAdjoint_extension_unique
  complete_hessian_domain := operator_domain_iff_summable
  complete_hessian_coercive := gap_mul_normSq_le_hessianQuadratic
  complete_bottom_attained := hessianQuadratic_minimizer
  complete_condensed_gap_positive := fun L hL =>
    (condensedAmplitude_spec L hL).2.2
  fock_vacuum_unique := totalEnergy_eq_zero_iff_vacuum
  fock_nonvacuum_gap := gap_le_totalEnergy_of_ne_vacuum
  fock_gap_attained := fun L z =>
    ⟨groundOccupation_ne_vacuum L z, totalEnergy_groundOccupation L z⟩
  finite_witness_coercive := finiteWitnessAction_coercive
  finite_witness_semigroup := flow_add_time

end GeneratedFoundations.Physical.SourceGeneratedYangMillsClosure
