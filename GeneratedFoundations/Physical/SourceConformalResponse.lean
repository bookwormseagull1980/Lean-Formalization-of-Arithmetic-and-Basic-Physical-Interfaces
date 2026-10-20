module

public import GeneratedFoundations.Physical.SourceRP3FieldSpectrum
public import GeneratedFoundations.Geometry.SourceConformalResponse

/-! Compatibility exports of the common-source complete scalar response.
The shell spectrum, infinite sums, restoring root and response normalization
are constructed before either application branch. -/

@[expose] public section

namespace GeneratedFoundations.Physical.SourceConformalResponse

export GeneratedFoundations.Geometry.SourceConformalResponse (
  CompleteProperties
  FiniteProperties
  canonicalAmplitude
  canonicalAmplitude_spec
  canonicalAmplitude_unique
  canonicalDrive
  canonicalDrive_pos
  canonicalRadialGap
  canonicalRadialGap_le_massIndex
  canonicalRadialGap_pos
  canonicalScalarMassIndex
  canonicalScalarMassIndex_zero
  completeCurvature
  completeCurvature_pos
  completeProperties
  completeResponse
  completeResponse_continuousOn_Icc
  completeResponse_nonneg
  completeResponse_root_unique
  completeResponse_strictMonoOn
  completeResponse_unboundedAbove
  completeResponse_zero
  conformalIndex
  conformalIndex_eq_scalar_shift
  conformalIndex_lt_multiplicity
  conformalIndex_mono
  conformalIndex_pos
  conformalMultiplicity
  conformalMultiplicity_eq_scalar
  conformalMultiplicity_pos
  curvatureTerm
  curvatureTerm_le_pseries
  curvatureTerm_pos
  curvatureTerm_summable
  existsUnique_completeResponse_root
  existsUnique_root_with_scalarGap
  finiteCurvature
  finiteCurvature_pos
  finiteProperties
  finiteResponse
  finiteResponse_nonneg
  finiteResponse_root_unique
  finiteResponse_strictMonoOn
  finiteResponse_zero
  generatedRadialGap
  generatedRadialGap_le_massIndex
  generatedRadialGap_pos
  generatedScalarMassIndex
  generatedScalarMassIndex_zero
  half_le_responseTerm_at_shell
  half_shell_count_le_completeResponse
  oddCoordinate
  oddCoordinate_mono
  oddCoordinate_pos
  responseTerm
  responseTerm_continuousOn
  responseTerm_le_linear_curvature
  responseTerm_nonneg
  responseTerm_strictMonoOn
  responseTerm_sub
  responseTerm_summable
  responseTerm_zero
  scalarCasimir_even_nonneg
  succ_le_oddCoordinate
  succ_square_le_multiplicity
  three_quarters_multiplicity_le_index
)

end GeneratedFoundations.Physical.SourceConformalResponse
