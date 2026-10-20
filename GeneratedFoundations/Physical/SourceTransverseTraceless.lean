module

public import GeneratedFoundations.Physical.SourceFourDimensionalGaugeKinematics
public import GeneratedFoundations.Geometry.SourceAxisTT

/-! Compatibility exports of the common-source tensor construction.
The original branch imports are retained for downstream source compatibility. -/

@[expose] public section

namespace GeneratedFoundations.Physical.SourceTransverseTraceless

export GeneratedFoundations.Geometry.SourceAxisTT (
  IsAxisTT
  Properties
  SpatialIndex
  SpatialTensor
  TTMode
  axisTT_eq_ttMatrix
  axisTT_second_diagonal
  axisTT_symmetric
  axisTT_third_row
  crossPolarization
  existsUnique_polarization
  pairToTT
  plusPolarization
  sourceTransverseTracelessProperties
  ttMatrix
  ttMatrix_add
  ttMatrix_injective
  ttMatrix_isAxisTT
  ttMatrix_smul
  ttMode_finrank
  ttPairEquiv
  ttSubmodule
  ttToPair
)

end GeneratedFoundations.Physical.SourceTransverseTraceless
