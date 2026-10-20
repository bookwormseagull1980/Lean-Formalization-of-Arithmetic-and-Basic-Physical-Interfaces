module

public import GeneratedFoundations.Operations.MatrixModuleClassification

/-! Compatibility names for the common matrix-unit classification. The proof
    is shared upstream; neither generated branch imports the other. -/

@[expose] public section

namespace GeneratedFoundations.Physical.MatrixModuleClassification

export GeneratedFoundations.Operations.MatrixModuleClassification (
  Nondegenerate
  nondegenerate_map_one
  nondegenerate_iff_map_one
  nondegenerateUnitalization
  nondegenerateUnitalization_apply
  Representation
  matrixUnit
  matrixUnit_comp_same
  matrixUnit_comp_ne
  sum_diagonal_matrixUnits
  sum_diagonal_matrixUnits_apply
  multiplicitySpace
  diagonal_fixes_multiplicity
  coordinate
  toCoordinates
  reconstruct
  reconstruct_toCoordinates
  toCoordinates_reconstruct
  multiplicityEquiv
  matrixUnit_mul_eq_row
  coordinate_intertwines
  finrank_eq_card_mul_multiplicity
  faithful_multiplicity_pos
  faithful_finrank_lowerBound
  minimal_finrank_iff_multiplicity_one
  factorAction
  factorAction_matrixUnit
  IsNatural
  reducedMap
  natural_single
  natural_apply
  natural_iff_existsUnique_reducedMap
)

end GeneratedFoundations.Physical.MatrixModuleClassification
