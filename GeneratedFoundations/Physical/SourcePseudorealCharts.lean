module

public import GeneratedFoundations.Geometry.SourcePseudorealCharts

/-!
# Local source reversal: physical compatibility interface

The original Hermitian-chart theorems are proved in the common geometry
layer. Both branches retain the same source reversal and overlap criterion.
-/

@[expose] public section

namespace GeneratedFoundations.Physical.SourcePseudorealCharts

export GeneratedFoundations.Geometry.SourcePseudorealCharts (
  localReversal_eq_iff_specialUnitary
  sourceMatrix_eq_frameMatrix
  orthonormalCoordinates_frameMatrix
  localReversal_square
  localReversal
  overlapOperator_reversal_iff
  transition_specialUnitary_trans
  localReversal_other_frame
  commonReversal_existsUnique
  localReversal_frame
  localReversal_unique
  localReversal_inner
  localReversal_eq_iff_pseudoreal
  transition_pseudoreal_trans
  localReversal_apply
)

end GeneratedFoundations.Physical.SourcePseudorealCharts
