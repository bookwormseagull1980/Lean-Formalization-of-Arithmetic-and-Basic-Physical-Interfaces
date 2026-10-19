module

public import GeneratedFoundations.CommonFoundation

/-!
# Canonical generated world

This is the public zero-argument alias for the common-root theorem. It does
not package a family of widths or orientations: unit covariance and the
canonical complex rotation have already fixed the unique realization used by
the generated construction.
-/

@[expose] public section

namespace GeneratedFoundations.CanonicalClosedWorld

abbrev Conclusions : Prop := CommonFoundation.Conclusions

/-- The unique generated world from minimal unbiased compositional change. -/
theorem generated : Conclusions := CommonFoundation.generated

end GeneratedFoundations.CanonicalClosedWorld
