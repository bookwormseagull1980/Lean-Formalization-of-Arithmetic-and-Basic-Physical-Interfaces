module

public import GeneratedFoundations.Physical.SourceReversalRealConnector
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Kronecker

public import GeneratedFoundations.Operations.ColourNaturalConnector

/-! Compatibility exports for the shared source and matrix-unit construction.
Its actual proof is upstream and contains no physical branch dependency. -/

@[expose] public section

namespace GeneratedFoundations.Physical.ColourNaturalConnector

export GeneratedFoundations.Operations.ColourNaturalConnector (
  Carrier
  ColourMatrix
  Connector
  Index
  Natural
  ReversalRealOnColours
  UnitNatural
  block
  block_spinLift_ne
  block_spinLift_same
  colourAction
  colourReversal
  colourReversal_square
  colourUnit_mul_apply
  doubletConnector
  doubletConnector_injective
  doubletEquivElementary
  elementarySpace
  elementarySpace_finrank
  mem_elementarySpace_iff
  mul_colourUnit_apply
  natural_iff_existsUnique_spinor
  natural_iff_unitNatural
  natural_reversalReal_iff_entries
  natural_reversalReal_iff_unique_doublet
  natural_reversalReal_iff_unique_quaternion
  natural_unitNatural
  spinLift
  spinLift_injective
  spinLift_mulVec
  spinLift_natural
  spinLift_reversalReal_iff
  unitNatural_diagonal_eq
  unitNatural_eq_spinLift
  unitNatural_offDiagonal
)

end GeneratedFoundations.Physical.ColourNaturalConnector
