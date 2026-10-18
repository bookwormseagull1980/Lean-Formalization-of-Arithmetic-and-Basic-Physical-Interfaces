module

public import GeneratedFoundations.Arithmetic.CompleteHistoryDynamics
public import GeneratedFoundations.Physical.SourcePhysicalInterface

/-!
# Common arithmetic and physical foundation

This module records the common-root statement.  One complete generated
natural-number system and the basic physical interfaces are parallel outputs
of one minimal unbiased compositional change datum.  Expression resolution and
complete histories belong to that single natural-number construction; they are
not alternative arithmetic branches.  Neither the mathematical nor the
physical branch is supplied as an assumption of the other, and no aggregate
physical realization premise is added.

The positive width and the carrier orientation are universally quantified
realization indices.  The correlation endpoints, reflecting closure,
expression quotient, source geometry and physical response interfaces are
constructed downstream.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Source
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Correlation
open GeneratedFoundations.Spectral
open GeneratedFoundations.Arithmetic
open GeneratedFoundations.Arithmetic.GeneratedFoundation
open GeneratedFoundations.Arithmetic.ReducedExpression
open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.CompleteNaturalObject
open GeneratedFoundations.Arithmetic.CompleteHistoryGeometry
open GeneratedFoundations.Arithmetic.CompleteHistoryTransport
open GeneratedFoundations.Arithmetic.CompleteHistoryDynamics
open GeneratedFoundations.Arithmetic.TypedSourceModes

namespace GeneratedFoundations.CommonFoundation

/-- One natural-number system, including its expression-history resolution,
and the basic physical interfaces generated from the same source datum. -/
structure Conclusions
    (source : MinimalUnbiasedChange.Datum)
    (o : OrientationOnCarrier source.change)
    (b : ℝ) (hb : 0 < b) : Prop where
  source_closure :
    SourceClosure source.change source.minimal o source.law b hb
  spectral_arithmetic :
    SpectralArithmeticClosure source.change source.minimal o b hb
  factorization :
    letI : Fact (0 < windowLengthGenerated b) :=
      ⟨windowLengthGenerated_pos hb⟩
    (∀ x : Mode source.change source.minimal (windowLengthGenerated b) o,
        x ≠ 0 →
          ∃! f : Mode source.change source.minimal (windowLengthGenerated b) o →₀ ℕ,
            TypedArithmetic.IsPrimeProfile source.change source.minimal
              (windowLengthGenerated b) o x f) ∧
      Set.Infinite {p : Mode source.change source.minimal
          (windowLengthGenerated b) o |
        TypedArithmetic.CompositionIrreducible source.change source.minimal
          (windowLengthGenerated b) o p}
  expression_resolution :
    letI : Fact (0 < windowLengthGenerated b) :=
      ⟨windowLengthGenerated_pos hb⟩
    IsGeneratedResolution source.change source.minimal
      (windowLengthGenerated b) o
  complete_history_source :
    CompleteHistory.Conclusions
  complete_natural_object :
    CompleteNaturalObject.Conclusions
  complete_history_geometry :
    CompleteHistoryGeometry.Conclusions
  complete_history_transport :
    CompleteHistoryTransport.Conclusions
  complete_history_dynamics :
    CompleteHistoryDynamics.Conclusions
  physical_interface :
    Physical.SourcePhysicalInterface.Conclusions source.change source.minimal
      o source.law b hb

/-- The single source datum generates both the natural-number branch and the
basic physical-interface branch. -/
theorem fromMinimalUnbiasedChange (source : MinimalUnbiasedChange.Datum) :
    ∀ (o : OrientationOnCarrier source.change) (b : ℝ) (hb : 0 < b),
      Conclusions source o b hb := by
  intro o b hb
  rcases GeneratedFoundation.minimalChange_to_nativeArithmeticWithFactorization
      source.change source.minimal o source.compositional hb with
    ⟨hsource, hspectral, hfactorization⟩
  refine {
    source_closure := hsource
    spectral_arithmetic := hspectral
    factorization := hfactorization
    expression_resolution := ?_
    complete_history_source := CompleteHistory.completeHistoryConclusions
    complete_natural_object := CompleteNaturalObject.completeNaturalObjectConclusions
    complete_history_geometry := CompleteHistoryGeometry.completeHistoryGeometryConclusions
    complete_history_transport := CompleteHistoryTransport.completeHistoryTransportConclusions
    complete_history_dynamics := CompleteHistoryDynamics.completeHistoryDynamicsConclusions
    physical_interface := Physical.SourcePhysicalInterface.minimalChange_physicalInterface
      source o b hb }
  exact @generatedResolution source.change source.minimal
    (windowLengthGenerated b) ⟨windowLengthGenerated_pos hb⟩ o

end GeneratedFoundations.CommonFoundation
