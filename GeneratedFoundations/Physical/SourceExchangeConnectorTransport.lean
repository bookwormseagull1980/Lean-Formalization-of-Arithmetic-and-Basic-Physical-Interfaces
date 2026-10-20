module

public import GeneratedFoundations.Geometry.SourceQuadraticSplit
public import GeneratedFoundations.Geometry.SourceExchangeResponse
public import GeneratedFoundations.Physical.SourceScalarConnector
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Transport of elementary connectors through the source exchange split

The positive and negative exchange eigenspaces of the actual source tensor
square give the colour-three and retained-line carriers.  Their established
unitary identifications, composed with the orthogonal sum map, determine the
colour splitting used here.  Tensor distribution is proved to preserve the
sum inner product, so the full transport is a linear isometric equivalence.

Conjugation through this equivalence carries the pre-exchange spin lift to the
same spin response on both retained sectors.  Naturality still refers to both
independent source actions before exchange resolution.  It is not weakened to
the diagonal source group or to block-diagonal colour actions after splitting.

The P6 reversal condition and unique doublet coordinate are preserved under
this actual transport.  The two labelled chiral copies retain the P5/P6 scope;
no exclusion of multiple elementary scalar copies is asserted.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open GeneratedFoundations.Geometry.SourceQuadraticSplit
open GeneratedFoundations.Physical.SourceJointResponse (W L S sourceOperator)
open GeneratedFoundations.Physical.SourceMinimalRepresentation (SourceCarrier)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Physical.ReversalRealConnector (Spinor)

namespace GeneratedFoundations.Physical.SourceExchangeConnectorTransport

export GeneratedFoundations.Geometry.SourceExchangeResponse (
  C
  FullCarrier
  SplitColour
  splitTensorNormed
  splitTensorInner
  symm_apply_of_apply_eq
  colourSplit
  colourSplit_apply
  colourSplit_symmetric
  colourSplit_alternating
  splitTensorLinear
  splitTensorLinear_tmul
  splitTensorLinear_inner
  norm_eq_of_inner_eq
  splitTensorUnitary
  exchangeUnitary
  exchangeUnitary_tmul
  exchangeUnitary_symmetric_tmul
  exchangeUnitary_alternating_tmul
  exchangeUnitary_spinLift
  operatorTransport
  operatorTransport_apply
  operatorTransport_adjoint
  operatorTransport_spinLift
  operatorTransport_eq_spinOnSource_iff
  sourceNatural_iff_unique_transported_spinor
  SplitSourceNatural
  algebraEquiv_commutes_iff
  operatorTransport_commutes_iff
  splitSourceNatural_operatorTransport
  splitSourceNatural_iff_unique_spinor
  SplitElementary
  splitElementary_operatorTransport
  elementary_iff_unique_transported_doublet
  splitElementary_iff_unique_doublet
)

/-- The same transported block and its actual adjoint on the two P5 chiral labels. -/
def chiralConnector (A : Module.End ℂ SourceCarrier) :
    Module.End ℂ SourceChiralCarrier.FullMatter :=
  SourceChiralCarrier.diagonalBlocks A A.adjoint * SourceChiralCarrier.exchange

theorem chiralConnector_transport_spinLift (h : Module.End ℂ S) :
    chiralConnector (operatorTransport (SourcePreExchangeResponse.spinLift h)) =
      SourceChiralCarrier.connector h := by
  rw [operatorTransport_spinLift]
  unfold chiralConnector SourceChiralCarrier.connector
  exact congrArg (fun A : Module.End ℂ SourceCarrier =>
    SourceChiralCarrier.diagonalBlocks (SourceChiralCarrier.spinOnSource h) A *
      SourceChiralCarrier.exchange) (SourceChiralCarrier.spinOnSource_adjoint h)

theorem chiralConnector_transport_doublet (H : Spinor) :
    chiralConnector (operatorTransport
      (SourcePreExchangeResponse.spinLift (SourceScalarConnector.doubletLift H))) =
      SourceScalarConnector.scalarConnector H :=
  chiralConnector_transport_spinLift _

end GeneratedFoundations.Physical.SourceExchangeConnectorTransport
