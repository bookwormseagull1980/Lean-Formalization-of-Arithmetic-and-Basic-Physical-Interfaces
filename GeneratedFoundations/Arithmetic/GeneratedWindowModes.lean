module

public import GeneratedFoundations.Arithmetic.TypedModeObservations
public import GeneratedFoundations.Spectral.PhysicalWindowModes

/-!
# Original source modes on the generated correlation window

An input mode is an actual endomorphism of the oriented original change
group. Its existing canonical Neumann vector is transported through the
actual interval-domain equivalence. The explicit translated Sobolev
representative gives a pointwise value on the retained interval; unit norm
and positive left trace uniquely determine its Hilbert-space value.

The positive lift is the observation of the same original endomorphism on
the generated spectral circle. Evaluation along the original spectral
coordinate recovers the original-group observation pointwise. Specializing
the interval to the correlation endpoints changes neither the mode family
nor its observation function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology
open GeneratedFoundations.Source GeneratedFoundations.Spectral
open GeneratedFoundations.Source.CarrierOrientation
open GeneratedFoundations.Source.GeneratedSpectralCircle

namespace GeneratedFoundations.Arithmetic.GeneratedWindowModes

open TypedSourceModes

variable (a L : ℝ) [hL : Fact (0 < L)]
variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)

/-- The label is read from the already classified original source map. -/
def modeIndex (o : OrientationOnCarrier d) (u : Mode d h L o) : ℕ :=
  NativeModes.index (GeneratedModes.toNative L (toGenerated d h L o u))

/-- A continuous observation on the original, untagged change group. -/
def sourceObservation (o : OrientationOnCarrier d) (u : Mode d h L o) :
    C(d.Changes, ℂ) where
  toFun g := TypedModeObservations.scalarObservation L d h o u ((forget d h o).symm g)
  continuous_toFun := (TypedModeObservations.scalarObservation L d h o u).continuous.comp
    (forget d h o).symm.continuous

theorem sourceObservation_apply (o : OrientationOnCarrier d) (u : Mode d h L o)
    (g : d.Changes) :
    sourceObservation L d h o u g =
      (phaseCharacter d h o (u ((forget d h o).symm g)).change : ℂ) := rfl

/-- The spectral observation is evaluated on the same original source point. -/
theorem positiveObservation_sourceCoordinate (o : OrientationOnCarrier d)
    (u : Mode d h L o) (g : d.Changes) :
    TypedModeObservations.positiveObservation L d h o u (spectralCoordinate d h L o g) =
      sourceObservation L d h o u g := by
  change TypedModeObservations.scalarObservation L d h o u
    (TypedModeObservations.spectralPoint L d h o (spectralCoordinate d h L o g)) = _
  rw [TypedModeObservations.spectralPoint_sourceCoordinate]
  rfl

/-- The canonical vector lies in the original translated Neumann domain. -/
abbrev representative (o : OrientationOnCarrier d) (u : Mode d h L o) :
    complexNeumannDomain a (a + L) :=
  PhysicalWindowModes.representative a L (toGenerated d h L o u)

/-- An explicit Sobolev representative, with its two actual weak derivatives. -/
def sobolevRepresentative (o : OrientationOnCarrier d) (u : Mode d h L o) :
    ComplexH2Representative a (a + L) :=
  translateBackRepresentative hL.out (neumannCosineRepresentative L (modeIndex L d h o u))

theorem sobolevRepresentative_neumann (o : OrientationOnCarrier d) (u : Mode d h L o) :
    IsComplexNeumann (sobolevRepresentative a L d h o u) :=
  translateBackNeumannRepresentative hL.out _ (neumannCosineRepresentative_neumann L _)

theorem sobolevRepresentative_toL2 (o : OrientationOnCarrier d) (u : Mode d h L o) :
    (sobolevRepresentative a L d h o u).toL2 =
      (representative a L d h o u : ComplexIntervalL2 a (a + L)) := by
  rw [sobolevRepresentative, translateBackRepresentative_toL2,
    neumannCosineRepresentative_toL2]
  exact (PhysicalWindowModes.representative_toL2 a L (toGenerated d h L o u)).symm

theorem representative_translate (o : OrientationOnCarrier d) (u : Mode d h L o) :
    translateNeumannDomainEquiv hL.out (representative a L d h o u) =
      TypedModeObservations.sourceRepresentative L d h o u :=
  PhysicalWindowModes.representative_translate a L (toGenerated d h L o u)

theorem representative_value (o : OrientationOnCarrier d) (u : Mode d h L o)
    {x : ℝ} (hx : x ∈ Icc a (a + L)) :
    (complexNeumannRepresentative (representative a L d h o u)).value x =
      (neumannCosineRepresentative L (modeIndex L d h o u)).value (x - a) := by
  have heq :
      (complexNeumannRepresentative (representative a L d h o u)).toL2 =
        (sobolevRepresentative a L d h o u).toL2 :=
    (complexNeumannRepresentative_spec (representative a L d h o u)).2.trans
      (sobolevRepresentative_toL2 a L d h o u).symm
  exact (ComplexH2Representative.trace_unique (by linarith [hL.out] : a < a + L) heq).1 hx

theorem representative_norm (o : OrientationOnCarrier d) (u : Mode d h L o) :
    ‖(representative a L d h o u : ComplexIntervalL2 a (a + L))‖ = 1 :=
  PhysicalWindowModes.representative_norm a L (toGenerated d h L o u)

theorem representative_endpoint_positive (o : OrientationOnCarrier d)
    (u : Mode d h L o) :
    ∃ r : ℝ, 0 < r ∧
      (complexNeumannRepresentative (representative a L d h o u)).value a = (r : ℂ) :=
  PhysicalWindowModes.representative_endpoint_positive a L (toGenerated d h L o u)

theorem representative_eigenvector (o : OrientationOnCarrier d) (u : Mode d h L o) :
    complexNeumannOperator (by linarith [hL.out] : a < a + L) (representative a L d h o u) =
      (neumannEigenvalue L (modeIndex L d h o u) : ℂ) •
        (representative a L d h o u : ComplexIntervalL2 a (a + L)) :=
  PhysicalWindowModes.representative_eigenvector a L (toGenerated d h L o u)

theorem representative_unique (o : OrientationOnCarrier d) (u : Mode d h L o)
    (f : complexNeumannDomain a (a + L))
    (heig : complexNeumannOperator (by linarith [hL.out] : a < a + L) f =
      (neumannEigenvalue L (modeIndex L d h o u) : ℂ) •
        (f : ComplexIntervalL2 a (a + L)))
    (hn : ‖(f : ComplexIntervalL2 a (a + L))‖ = 1)
    (hp : ∃ r : ℝ, 0 < r ∧ (complexNeumannRepresentative f).value a = (r : ℂ)) :
    f = representative a L d h o u :=
  PhysicalWindowModes.representative_unique a L (toGenerated d h L o u) f heig hn hp

theorem representative_positive_lift (o : OrientationOnCarrier d) (u : Mode d h L o) :
    PhysicalWindowModes.lift a L
        (representative a L d h o u : ComplexIntervalL2 a (a + L))
      =ᵐ[AddCircle.haarAddCircle] TypedModeObservations.positiveObservation L d h o u := by
  rw [TypedModeObservations.positiveObservation_eq]
  exact PhysicalWindowModes.representative_lifts a L (toGenerated d h L o u)

/-- The continuous observation is unique, not merely its almost-everywhere class. -/
theorem positiveObservation_unique (o : OrientationOnCarrier d) (u : Mode d h L o)
    (g : C(AddCircle (2 * L), ℂ))
    (hg : PhysicalWindowModes.lift a L
        (representative a L d h o u : ComplexIntervalL2 a (a + L))
      =ᵐ[AddCircle.haarAddCircle] g) :
    g = TypedModeObservations.positiveObservation L d h o u := by
  apply ContinuousMap.coe_injective
  exact MeasureTheory.Measure.eq_of_ae_eq
    (hg.symm.trans (representative_positive_lift a L d h o u))
    g.continuous (TypedModeObservations.positiveObservation L d h o u).continuous

theorem representative_reverse (o : OrientationOnCarrier d) (u : Mode d h L o) :
    representative a L d h (-o) (reverseMode d h L o u) =
      representative a L d h o u := by
  unfold representative
  rw [toGenerated_reverseMode]

omit hL in
/-- The constructed translation has its actual representative formula. -/
theorem canonicalTranslation_coe (f : ComplexIntervalL2 a (a + L)) :
    shiftCanonicalL2Equiv (a := a) (L := L) f =ᵐ[intervalMeasure 0 L]
      fun x => f (x + a) :=
  Lp.coeFn_compMeasurePreserving f (shiftRight_measurePreserving (a := a) (L := L))

omit hL in
theorem canonicalTranslation_unique
    (U : ComplexIntervalL2 a (a + L) ≃ₗᵢ[ℂ] ComplexIntervalL2 0 L)
    (hU : ∀ f, U f =ᵐ[intervalMeasure 0 L] fun x => f (x + a)) :
    U = shiftCanonicalL2Equiv (a := a) (L := L) := by
  apply LinearIsometryEquiv.ext
  intro f
  exact Lp.ext ((hU f).trans (canonicalTranslation_coe a L f).symm)

/-- The representative theorem uses the already constructed translation itself. -/
theorem canonical_source_modes (o : OrientationOnCarrier d) (u : Mode d h L o) :
    ∃! f : complexNeumannDomain a (a + L),
        complexNeumannOperator (by linarith [hL.out] : a < a + L) f =
            (neumannEigenvalue L (modeIndex L d h o u) : ℂ) •
              (f : ComplexIntervalL2 a (a + L)) ∧
          ‖(f : ComplexIntervalL2 a (a + L))‖ = 1 ∧
          (∃ r : ℝ, 0 < r ∧ (complexNeumannRepresentative f).value a = (r : ℂ)) ∧
          (∀ x ∈ Icc a (a + L), (complexNeumannRepresentative f).value x =
            (neumannCosineRepresentative L (modeIndex L d h o u)).value (x - a)) ∧
          OrientedLift.lift L (shiftCanonicalL2Equiv (a := a) (L := L) f)
            =ᵐ[AddCircle.haarAddCircle]
            TypedModeObservations.positiveObservation L d h o u := by
  refine ⟨representative a L d h o u, ?_, ?_⟩
  · exact ⟨representative_eigenvector a L d h o u, representative_norm a L d h o u,
      representative_endpoint_positive a L d h o u,
      fun _ hx => representative_value a L d h o u hx,
      representative_positive_lift a L d h o u⟩
  · intro f hf
    exact representative_unique a L d h o u f hf.1 hf.2.1 hf.2.2.1

/-- One actual translation works for every mode on the original change group. -/
theorem translated_source_modes (o : OrientationOnCarrier d) :
    ∃ U : ComplexIntervalL2 a (a + L) ≃ₗᵢ[ℂ] ComplexIntervalL2 0 L,
      (∀ f, U f =ᵐ[intervalMeasure 0 L] fun x => f (x + a)) ∧
      ∀ u : Mode d h L o, ∃! f : complexNeumannDomain a (a + L),
        complexNeumannOperator (by linarith [hL.out] : a < a + L) f =
            (neumannEigenvalue L (modeIndex L d h o u) : ℂ) •
              (f : ComplexIntervalL2 a (a + L)) ∧
          ‖(f : ComplexIntervalL2 a (a + L))‖ = 1 ∧
          (∃ r : ℝ, 0 < r ∧ (complexNeumannRepresentative f).value a = (r : ℂ)) ∧
          (∀ x ∈ Icc a (a + L), (complexNeumannRepresentative f).value x =
            (neumannCosineRepresentative L (modeIndex L d h o u)).value (x - a)) ∧
          OrientedLift.lift L (U f) =ᵐ[AddCircle.haarAddCircle]
            TypedModeObservations.positiveObservation L d h o u :=
  ⟨shiftCanonicalL2Equiv, canonicalTranslation_coe a L, canonical_source_modes a L d h o⟩

/-- The unique representatives and observations use the actual generated endpoints. -/
theorem generatedWindow_source_modes {b : ℝ} (hb : 0 < b) (o : OrientationOnCarrier d) :
    letI : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
    ∃ U : ComplexIntervalL2 (windowLeft b) (windowRight b) ≃ₗᵢ[ℂ]
        ComplexIntervalL2 0 (windowLengthGenerated b),
      (∀ f, U f =ᵐ[intervalMeasure 0 (windowLengthGenerated b)]
        fun x => f (x + windowLeft b)) ∧
      ∀ u : Mode d h (windowLengthGenerated b) o,
        ∃! f : complexNeumannDomain (windowLeft b) (windowRight b),
          complexNeumannOperator (sub_pos.mp (windowLengthGenerated_pos hb)) f =
              (neumannEigenvalue (windowLengthGenerated b)
                (modeIndex (windowLengthGenerated b) d h o u) : ℂ) •
                  (f : ComplexIntervalL2 (windowLeft b) (windowRight b)) ∧
            ‖(f : ComplexIntervalL2 (windowLeft b) (windowRight b))‖ = 1 ∧
            (∃ r : ℝ, 0 < r ∧
              (complexNeumannRepresentative f).value (windowLeft b) = (r : ℂ)) ∧
            (∀ x ∈ Icc (windowLeft b) (windowRight b),
              (complexNeumannRepresentative f).value x =
                (neumannCosineRepresentative (windowLengthGenerated b)
                  (modeIndex (windowLengthGenerated b) d h o u)).value (x - windowLeft b)) ∧
            OrientedLift.lift (windowLengthGenerated b) (U f) =ᵐ[AddCircle.haarAddCircle]
              TypedModeObservations.positiveObservation (windowLengthGenerated b) d h o u := by
  let : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
  have ha : windowLeft b < windowLeft b + windowLengthGenerated b := by
    linarith [windowLengthGenerated_pos hb]
  have h :
      ∃ U : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b) ≃ₗᵢ[ℂ]
          ComplexIntervalL2 0 (windowLengthGenerated b),
        (∀ f, U f =ᵐ[intervalMeasure 0 (windowLengthGenerated b)]
          fun x => f (x + windowLeft b)) ∧
        ∀ u : Mode d h (windowLengthGenerated b) o,
          ∃! f : complexNeumannDomain (windowLeft b) (windowLeft b + windowLengthGenerated b),
            complexNeumannOperator ha f =
                (neumannEigenvalue (windowLengthGenerated b)
                  (modeIndex (windowLengthGenerated b) d h o u) : ℂ) •
                    (f : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b)) ∧
              ‖(f : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b))‖ = 1 ∧
              (∃ r : ℝ, 0 < r ∧
                (complexNeumannRepresentative f).value (windowLeft b) = (r : ℂ)) ∧
              (∀ x ∈ Icc (windowLeft b) (windowLeft b + windowLengthGenerated b),
                (complexNeumannRepresentative f).value x =
                  (neumannCosineRepresentative (windowLengthGenerated b)
                    (modeIndex (windowLengthGenerated b) d h o u)).value (x - windowLeft b)) ∧
              OrientedLift.lift (windowLengthGenerated b) (U f) =ᵐ[AddCircle.haarAddCircle]
                TypedModeObservations.positiveObservation (windowLengthGenerated b) d h o u :=
    translated_source_modes (windowLeft b) (windowLengthGenerated b) d h o
  have heq := windowLeft_add_length hb
  generalize windowLeft b + windowLengthGenerated b = c at ha h heq
  subst c
  exact h

end GeneratedFoundations.Arithmetic.GeneratedWindowModes
