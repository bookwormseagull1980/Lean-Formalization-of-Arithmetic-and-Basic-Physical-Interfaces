import GeneratedFoundations.Operations.SourceCornerMinimality
import GeneratedFoundations.Geometry.SourceExchangeAverage
import GeneratedFoundations.Geometry.SourceScalarResponse
import GeneratedFoundations.Physical.SourcePhysicalInterface

/- The classification gives one coordinate for each connector. Every doublet
   has a connector in that class, so the class alone selects no single value. -/
theorem elementary_family_has_distinct_coordinates :
    ¬ ∃! H : GeneratedFoundations.Operations.ReversalRealConnector.Spinor,
      GeneratedFoundations.Geometry.SourceScalarResponse.Elementary
        (GeneratedFoundations.Geometry.SourcePreExchangeResponse.spinLift
          (GeneratedFoundations.Geometry.SourceScalarResponse.doubletLift H)) := by
  rintro ⟨H, _, huniq⟩
  have h0 := huniq 0
    (GeneratedFoundations.Geometry.SourceScalarResponse.canonical_elementary 0)
  have h1 := huniq (fun _ => 1)
    (GeneratedFoundations.Geometry.SourceScalarResponse.canonical_elementary (fun _ => 1))
  have h01 := congrFun (h0.trans h1.symm) 0
  norm_num at h01

#print axioms GeneratedFoundations.Operations.SourceCornerMinimality.firstVariation_differential
#print axioms GeneratedFoundations.Operations.SourceCornerMinimality.sourceSpace_isLeast
#print axioms GeneratedFoundations.Operations.SourceCornerMinimality.least_carrier_unique
#print axioms GeneratedFoundations.Geometry.SourceExchangeAverage.average_idempotent
#print axioms GeneratedFoundations.Geometry.SourceExchangeAverage.range_average
#print axioms GeneratedFoundations.Geometry.SourceExchangeAverage.average_unique
#print axioms elementary_family_has_distinct_coordinates
#print axioms GeneratedFoundations.Physical.SourcePhysicalInterface.generatedCore
#check GeneratedFoundations.Physical.SourcePhysicalInterface.generatedCore.matter.spectralResponse
