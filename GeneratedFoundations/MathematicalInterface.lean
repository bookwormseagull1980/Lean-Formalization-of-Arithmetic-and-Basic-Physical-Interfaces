module

public import GeneratedFoundations.Source.CommonSource
public import GeneratedFoundations.Operations.SourceCoherentObservations
public import GeneratedFoundations.Operations.SourceResponseCapacity
public import GeneratedFoundations.Operations.SourceNumberFlow
public import GeneratedFoundations.Arithmetic.HistoryObservation
public import GeneratedFoundations.Arithmetic.HistoryPhaseBundle
public import GeneratedFoundations.Arithmetic.HistoryMatrixAlgebra
public import GeneratedFoundations.Arithmetic.OccupationResponse
public import GeneratedFoundations.Analysis.HistoryGibbsResponse
public import GeneratedFoundations.Analysis.HistoryCentralResponse
public import GeneratedFoundations.Analysis.HistoryResponseReduction
public import GeneratedFoundations.Analysis.HistoryPhaseResponse
public import GeneratedFoundations.Analysis.HistoryReactionForm
public import GeneratedFoundations.Analysis.HistoryReactionOperator
public import GeneratedFoundations.Analysis.HistoryReactionKernel
public import GeneratedFoundations.Analysis.HistoryReactionComplex
public import GeneratedFoundations.Analysis.HistoryReactionHodge
public import GeneratedFoundations.Analysis.HistoryReactionCovariance
public import GeneratedFoundations.Analysis.HistoryReactionFlow
public import GeneratedFoundations.Analysis.HistoryReactionHilbert
public import GeneratedFoundations.Analysis.HistoryReactionHilbertFlow
public import GeneratedFoundations.Analysis.HistoryReflectionFlow
public import GeneratedFoundations.Geometry.SourceOneFormSystem
public import GeneratedFoundations.Geometry.SourceSpinorSystem
public import GeneratedFoundations.Geometry.SourceTensorTTSystem
public import GeneratedFoundations.Analysis.CapacityRestoredWindowBudget

/-!
# The mathematical response interface of the canonical generated source

The common differential systems are mathematical constructions of the same
source, so they are reused directly.  The history, phase, Gibbs and reaction
outputs below instead instantiate the response methodology on the actual
arithmetic objects.  This entry imports no physical-branch conclusion.

Every field is a proved output.  The zero-argument theorem accepts neither a
carrier, bundle, rate, quadratic form nor positivity certificate from its
caller.  Observation indices remain universally quantified inside each
output. History matrix statements retain their finite fibres; the complete
reaction operator and its evolution act on the full history Hilbert space,
with their actual finite-cutoff limits included below.
-/

@[expose] public section

namespace GeneratedFoundations.MathematicalInterface

structure Conclusions : Prop where
  common_source : Source.CommonSource.Conclusions
  history_observations : Arithmetic.HistoryObservation.Conclusions
  history_phase_bundle : Arithmetic.HistoryPhaseBundle.Conclusions
  history_matrix_algebra : Arithmetic.HistoryMatrixAlgebra.Conclusions
  connected_history_response : Analysis.HistoryGibbsResponse.Conclusions
  central_history_response : Analysis.HistoryCentralResponse.Conclusions
  full_history_response_reduction : Analysis.HistoryResponseReduction.Conclusions
  complete_phase_response : Analysis.HistoryPhaseResponse.Conclusions
  common_reaction_form : Analysis.HistoryReactionForm.Conclusions
  actual_reaction_operator : Analysis.HistoryReactionOperator.Conclusions
  actual_reaction_kernel : Analysis.HistoryReactionKernel.Conclusions
  actual_reaction_complex : Analysis.HistoryReactionComplex.Conclusions
  orthogonal_reaction_reduction : Analysis.HistoryReactionHodge.Conclusions
  reaction_covariance : Analysis.HistoryReactionCovariance.Conclusions
  actual_reaction_flow : Analysis.HistoryReactionFlow.Conclusions
  complete_reaction_operator : Analysis.HistoryReactionHilbert.Conclusions
  complete_reaction_flow : Analysis.HistoryReactionHilbertFlow.Conclusions
  history_reflection_flow : Analysis.HistoryReflectionFlow.Conclusions
  complete_occupation_response : Arithmetic.OccupationResponse.Conclusions
  source_one_form_system : Geometry.SourceOneFormSystem.Conclusions
  source_spinor_system : Geometry.SourceSpinorSystem.Conclusions
  source_tensor_system : Geometry.SourceTensorTTSystem.Conclusions
  capacity_restored_window : Analysis.CapacityRestoredWindowBudget.Conclusions

theorem generated : Conclusions where
  common_source := Source.CommonSource.generated
  history_observations := Arithmetic.HistoryObservation.generated
  history_phase_bundle := Arithmetic.HistoryPhaseBundle.generated
  history_matrix_algebra := Arithmetic.HistoryMatrixAlgebra.generated
  connected_history_response := Analysis.HistoryGibbsResponse.generated
  central_history_response := Analysis.HistoryCentralResponse.generated
  full_history_response_reduction := Analysis.HistoryResponseReduction.generated
  complete_phase_response := Analysis.HistoryPhaseResponse.generated
  common_reaction_form := Analysis.HistoryReactionForm.generated
  actual_reaction_operator := Analysis.HistoryReactionOperator.generated
  actual_reaction_kernel := Analysis.HistoryReactionKernel.generated
  actual_reaction_complex := Analysis.HistoryReactionComplex.generated
  orthogonal_reaction_reduction := Analysis.HistoryReactionHodge.generated
  reaction_covariance := Analysis.HistoryReactionCovariance.generated
  actual_reaction_flow := Analysis.HistoryReactionFlow.generated
  complete_reaction_operator := Analysis.HistoryReactionHilbert.generated
  complete_reaction_flow := Analysis.HistoryReactionHilbertFlow.generated
  history_reflection_flow := Analysis.HistoryReflectionFlow.generated
  complete_occupation_response := Arithmetic.OccupationResponse.generated
  source_one_form_system := Geometry.SourceOneFormSystem.generated
  source_spinor_system := Geometry.SourceSpinorSystem.generated
  source_tensor_system := Geometry.SourceTensorTTSystem.generated
  capacity_restored_window := Analysis.CapacityRestoredWindowBudget.conclusions

end GeneratedFoundations.MathematicalInterface
