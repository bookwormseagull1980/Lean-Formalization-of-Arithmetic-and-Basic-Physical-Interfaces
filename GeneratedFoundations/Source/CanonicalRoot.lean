module

public import GeneratedFoundations.Source.MinimalUnbiasedChange

/-!
# The canonical root completion

`MinimalUnbiasedChange.Datum` is the compatibility package used throughout the
existing library.  It stores both a minimal change carrier and one law
satisfying the compositional axioms.  The law is not free: the preceding
existence--uniqueness theorem constructs it from the carrier and identifies
every competing compositional law at every positive parameter.

This file separates the sole abstract root, minimal unbiased compositional
change, from its comparison presentations.  `MinimalCarrier` proves that every
minimal presentation is two-dimensional and orthogonally intertwines the
circle action.  `rotationDatum` is therefore used as the canonical
representative; it is not an additional root axiom.  The compositional law is
then constructed internally and is unique at every positive parameter.  A
general `Datum` remains only for representation-independence statements.  No
claim is made about unconstrained values of a real-indexed law at nonpositive
parameters.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Probability

namespace GeneratedFoundations.Source.CanonicalRoot

/-- A presentation of the intrinsic root in the declared comparison class,
together with its least-dimension proof.  Presentations are comparison
objects, not independent inputs to the closed construction. -/
structure Datum where
  change : MinimalCarrier.OrthogonalChangeDatum
  minimal : MinimalCarrier.IsMinimal change

/-- The unique positive-parameter compositional completion of a canonical
root, represented by the library's existing compatibility package. -/
def complete (root : Datum) : MinimalUnbiasedChange.Datum :=
  MinimalUnbiasedChange.fromMinimalCarrier root.change root.minimal

/-- The canonical representative of the sole minimal-change root.  Its carrier
and minimality are proved upstream; no carrier is supplied by a caller. -/
def canonical : Datum where
  change := MinimalCarrier.rotationDatum
  minimal := MinimalCarrier.rotationDatum_isMinimal

/-- The unique positive-parameter compositional completion used by the closed
generated world. -/
def generated : MinimalUnbiasedChange.Datum := complete canonical

@[simp] theorem canonical_change : canonical.change = MinimalCarrier.rotationDatum := rfl

@[simp] theorem generated_change : generated.change = MinimalCarrier.rotationDatum := rfl

@[simp] theorem complete_change (root : Datum) :
    (complete root).change = root.change := rfl

/-- Forgetting the stored law from another presentation leaves its underlying
minimal comparison presentation. -/
def ofLegacy (source : MinimalUnbiasedChange.Datum) : Datum where
  change := source.change
  minimal := source.minimal

@[simp] theorem ofLegacy_change (source : MinimalUnbiasedChange.Datum) :
    (ofLegacy source).change = source.change := rfl

/-- Every legacy root law agrees, at every positive parameter, with the law
constructed by canonical completion.  This is the precise no-free-law
statement; it deliberately does not identify unconstrained nonpositive
parameters. -/
theorem legacy_law_eq_complete (source : MinimalUnbiasedChange.Datum)
    (t : ℝ) (ht : 0 < t) :
    source.law t = (complete (ofLegacy source)).law t := by
  exact MinimalUnbiasedChange.law_unique source
    (complete (ofLegacy source)).law
    (complete (ofLegacy source)).compositional t ht

/-- Any compositional law on the same canonical carrier agrees with the
internally constructed completion at positive parameters. -/
theorem law_unique (root : Datum)
    (nu : ℝ → Measure
      (TraceLieGeometry.TraceLieSpace root.change root.minimal))
    (hnu : HilbertCompositionalAxioms nu) (t : ℝ) (ht : 0 < t) :
    (complete root).law t = nu t := by
  exact MinimalUnbiasedChange.law_unique (complete root) nu hnu t ht

/-- The canonical root has a concrete realization. -/
theorem datum_exists : Nonempty Datum := ⟨canonical⟩

end GeneratedFoundations.Source.CanonicalRoot
