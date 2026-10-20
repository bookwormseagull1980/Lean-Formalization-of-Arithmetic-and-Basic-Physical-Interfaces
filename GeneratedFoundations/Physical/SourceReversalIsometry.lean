module

public import GeneratedFoundations.Geometry.SourceReversalIsometry

/-!
# Source reversal: physical compatibility interface

The Gaussian--Haar antiunitary, its square, fixed-frame classification and
independent-frame transport are common-source constructions. The physical
branch retains these exact names while both branches use the upstream proof.
-/

@[expose] public section

namespace GeneratedFoundations.Physical.SourceReversalIsometry

export GeneratedFoundations.Geometry.SourceReversalIsometry (
  IntertwinesReversal
  PseudorealFrameChange
  doubletMap
  doubletMap_apply
  framedCoordinates
  framedReversal
  framedReversal_apply
  framedReversal_changeFrame
  framedReversal_eq_coordinates
  framedReversal_inner
  framedReversal_square
  framedReversal_symm_apply
  framedReversal_transport
  gaussianReversal
  gaussianReversal_excitation
  gaussianReversal_intertwines
  gaussianReversal_vacuum
  intertwinesReversal_iff_unique_doublet
  intertwinesReversal_transport_iff
  pseudorealFrameChange_iff_specialUnitary
  sourceMatrix_unitary
  sourceReversal
  sourceReversal_apply
  sourceReversal_basis_one
  sourceReversal_basis_zero
  sourceReversal_inner
  sourceReversal_inner_conjugate
  sourceReversal_square
  sourceReversal_symm_apply
  sourceUnitary_pseudoreal
  spinCoordinates_basis
  transportConnector
  transportConnector_apply
  transportedReversal_inner
  transportedReversal_neg
  transportedReversal_norm
)

end GeneratedFoundations.Physical.SourceReversalIsometry
