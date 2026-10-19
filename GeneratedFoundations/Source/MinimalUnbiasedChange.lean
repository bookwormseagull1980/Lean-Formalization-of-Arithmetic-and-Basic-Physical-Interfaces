module

public import GeneratedFoundations.Probability.GeneratedTangentLaw

/-!
# Minimal unbiased compositional change: the root datum

`Datum` contains exactly the minimal orthogonal change datum and its
compositional law on the original trace Lie line. The law satisfies probability
normalization, independent composition, square-root scaling, finite second
moment and unit covariance. These are the contents of minimal unbiased
compositional change; no Gaussian formula is a field of the datum.

Orientation and width variables occur in coordinate-level lemmas, but the
closed construction does not accept them as realization inputs. Unit covariance
and the original complex rotation fix their canonical values downstream.
Endpoint readouts, reflecting operators, arithmetic and physical response
objects are defined and proved downstream. Neither their values nor their
properties are fields here. Their internal definitions and the comparison
classes in uniqueness theorems remain explicit.

The source conditions, the characterizations of the fixed readout and
completion constructions, and the resulting calculated values have distinct
logical roles. No downstream characterization is an adjustable fitting
parameter, and packaging the root data does not remove those characterizations
from the corresponding uniqueness statements.

The existing existence theorem supplies a law for every minimal carrier.
Its uniqueness is at positive parameters, the domain constrained by the root
conditions. This does not claim that composition or scaling follows from
carrier minimality alone.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Probability

namespace GeneratedFoundations.Source.MinimalUnbiasedChange

/-- The sole root package; all fields precede the downstream constructions. -/
structure Datum where
  change : MinimalCarrier.OrthogonalChangeDatum
  minimal : MinimalCarrier.IsMinimal change
  law : ℝ → Measure (TraceLieGeometry.TraceLieSpace change minimal)
  compositional : HilbertCompositionalAxioms law

/-- A compatible law is constructed by the proved existence theorem. -/
def fromMinimalCarrier (d : MinimalCarrier.OrthogonalChangeDatum)
    (h : MinimalCarrier.IsMinimal d) : Datum where
  change := d
  minimal := h
  law := Classical.choose (GeneratedTangentLaw.exists_unique d h)
  compositional := (Classical.choose_spec (GeneratedTangentLaw.exists_unique d h)).1

/-- The root package has a concrete realization. -/
theorem datum_exists : Nonempty Datum :=
  ⟨fromMinimalCarrier MinimalCarrier.rotationDatum MinimalCarrier.rotationDatum_isMinimal⟩

/-- The probability law is not an additional free distribution at positive
parameters once its root conditions on the same carrier have been fixed. -/
theorem law_unique (source : Datum)
    (ν : ℝ → Measure (TraceLieGeometry.TraceLieSpace source.change source.minimal))
    (hν : HilbertCompositionalAxioms ν) (t : ℝ) (ht : 0 < t) :
    source.law t = ν t := by
  obtain ⟨μ, _, huniq⟩ := GeneratedTangentLaw.exists_unique source.change source.minimal
  exact (huniq source.law source.compositional t ht).symm.trans (huniq ν hν t ht)

end GeneratedFoundations.Source.MinimalUnbiasedChange
