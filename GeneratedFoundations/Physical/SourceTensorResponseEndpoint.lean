module

public import GeneratedFoundations.Physical.SourceTransverseTraceless
public import GeneratedFoundations.Geometry.SourceTensorResponse

/-! Compatibility exports of the common-source tensor construction.
The original branch imports are retained for downstream source compatibility. -/

@[expose] public section

namespace GeneratedFoundations.Physical.SourceTensorResponseEndpoint

export GeneratedFoundations.Geometry.SourceTensorResponse (
  Properties
  endpointResidual
  endpointResidual_eq_zero_iff
  endpointResidual_root
  endpointRoot
  endpointRoot_pos
  existsUnique_positive_endpoint
  massFraction
  massFraction_mem_unitInterval
  massWeightedResponse
  massWeightedResponse_eq_critical_iff
  massWeightedResponse_le
  massWeightedResponse_oneThird
  response_factorization
  sourceTensorResponseEndpointProperties
  ttInverseCovariance
  ttInverseCovariance_injective
  ttInverseCovariance_propagator
  ttInverseCovariance_zero_momentum
  ttKernel
  ttKernel_eq_massFraction
  ttKernel_le_one
  ttKernel_nonnegative
  ttPropagator
  tt_poleResidue_pos
  tt_simplePole_certificate
  unique_response_maximizer
)

end GeneratedFoundations.Physical.SourceTensorResponseEndpoint
