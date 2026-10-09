module

public import GeneratedFoundations.Spectral.PhysicalWindowSpectrum
public import GeneratedFoundations.Arithmetic.GeneratedModes

/-!
# Source-mode representatives on the original interval

The normalized source representative is transported through the actual
Sobolev-domain equivalence. Its endpoint condition is evaluated at the
original left endpoint, using the unique continuous representative.
The analytic lift commutes with interval translation. The construction
applies in particular to the generated window, whose right endpoint equals
its left endpoint plus its generated length.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Arithmetic

namespace GeneratedFoundations.Spectral.PhysicalWindowModes

variable (a L : ℝ) [hL : Fact (0 < L)]

def leftTrace (f : complexNeumannDomain a (a + L)) : ℂ :=
  (complexNeumannRepresentative f).value a

theorem leftTrace_translate (f : complexNeumannDomain a (a + L)) :
    neumannLeftTrace L (translateNeumannDomainEquiv hL.out f) = leftTrace a L f := by
  have heq :
      (complexNeumannRepresentative (translateNeumannDomainEquiv hL.out f)).toL2 =
        (translateRepresentative hL.out (complexNeumannRepresentative f)).toL2 := by
    rw [(complexNeumannRepresentative_spec (translateNeumannDomainEquiv hL.out f)).2]
    rfl
  have hv := (ComplexH2Representative.trace_unique hL.out heq).1
    (show (0 : ℝ) ∈ Set.Icc 0 L from ⟨le_rfl, hL.out.le⟩)
  simpa only [neumannLeftTrace, leftTrace, translateRepresentative, shiftRight, zero_add]
    using hv

def representative (u : GeneratedModes.SourceMode L) : complexNeumannDomain a (a + L) :=
  (translateNeumannDomainEquiv hL.out).symm (GeneratedModes.representative L u)

@[simp] theorem representative_translate (u : GeneratedModes.SourceMode L) :
    translateNeumannDomainEquiv hL.out (representative a L u) =
      GeneratedModes.representative L u :=
  (translateNeumannDomainEquiv hL.out).apply_symm_apply _

theorem representative_toL2 (u : GeneratedModes.SourceMode L) :
    (representative a L u : ComplexIntervalL2 a (a + L)) =
      (shiftCanonicalL2Equiv (a := a) (L := L)).symm
        (GeneratedModes.representative L u : ComplexIntervalL2 0 L) :=
  translateNeumannDomainEquiv_symm_toL2 a L _

theorem representative_norm (u : GeneratedModes.SourceMode L) :
    ‖(representative a L u : ComplexIntervalL2 a (a + L))‖ = 1 := by
  rw [representative_toL2, LinearIsometryEquiv.norm_map]
  exact GeneratedModes.representative_norm L u

theorem representative_endpoint_positive (u : GeneratedModes.SourceMode L) :
    ∃ r : ℝ, 0 < r ∧ leftTrace a L (representative a L u) = (r : ℂ) := by
  rw [← leftTrace_translate, representative_translate]
  exact GeneratedModes.representative_endpoint_positive L u

theorem representative_eigenvector (u : GeneratedModes.SourceMode L) :
    complexNeumannOperator (by linarith [hL.out] : a < a + L) (representative a L u) =
      (neumannEigenvalue L (NativeModes.index (GeneratedModes.toNative L u)) : ℂ) •
        (representative a L u : ComplexIntervalL2 a (a + L)) := by
  apply (shiftCanonicalL2Equiv (a := a) (L := L)).injective
  change shiftCanonicalL2Equiv
      ((complexNeumannOperator (by linarith [hL.out] : a < a + L)).toFun
        (representative a L u)) =
    shiftCanonicalL2Equiv
      ((neumannEigenvalue L (NativeModes.index (GeneratedModes.toNative L u)) : ℂ) •
        (representative a L u : ComplexIntervalL2 a (a + L)))
  rw [complexNeumannOperator_translate hL.out, representative_translate, map_smul,
    ← translateNeumannDomainEquiv_toL2 hL.out, representative_translate]
  exact complexNeumannOperator_cosine L _

theorem representative_unique (u : GeneratedModes.SourceMode L)
    (f : complexNeumannDomain a (a + L))
    (heig : complexNeumannOperator (by linarith [hL.out] : a < a + L) f =
      (neumannEigenvalue L (NativeModes.index (GeneratedModes.toNative L u)) : ℂ) •
        (f : ComplexIntervalL2 a (a + L)))
    (hn : ‖(f : ComplexIntervalL2 a (a + L))‖ = 1)
    (hp : ∃ r : ℝ, 0 < r ∧ leftTrace a L f = (r : ℂ)) :
    f = representative a L u := by
  apply (translateNeumannDomainEquiv hL.out).injective
  rw [representative_translate]
  apply neumannCanonicalMode_unique L _
  · have ht := congrArg (shiftCanonicalL2Equiv (a := a) (L := L)) heig
    change shiftCanonicalL2Equiv
        ((complexNeumannOperator (by linarith [hL.out] : a < a + L)).toFun f) =
      shiftCanonicalL2Equiv
        ((neumannEigenvalue L (NativeModes.index (GeneratedModes.toNative L u)) : ℂ) •
          (f : ComplexIntervalL2 a (a + L))) at ht
    rw [complexNeumannOperator_translate hL.out, map_smul,
      ← translateNeumannDomainEquiv_toL2 hL.out] at ht
    exact ht
  · rw [translateNeumannDomainEquiv_toL2, LinearIsometryEquiv.norm_map]
    exact hn
  · simpa only [leftTrace_translate] using hp

/-- The lift uses the same affine coordinate as the transported operator. -/
def lift : ComplexIntervalL2 a (a + L) →L[ℂ] HaarCircleL2 L :=
  (OrientedLift.lift L).comp
    (shiftCanonicalL2Equiv (a := a) (L := L)).toContinuousLinearEquiv.toContinuousLinearMap

theorem representative_lifts (u : GeneratedModes.SourceMode L) :
    lift a L (representative a L u : ComplexIntervalL2 a (a + L))
      =ᵐ[AddCircle.haarAddCircle] OrientedLift.endomorphismRepresentative L u.val := by
  change OrientedLift.lift L (shiftCanonicalL2Equiv
      (representative a L u : ComplexIntervalL2 a (a + L))) =ᵐ[_] _
  rw [← translateNeumannDomainEquiv_toL2 hL.out, representative_translate]
  exact GeneratedModes.representative_lifts L u

theorem lift_norm (f : ComplexIntervalL2 a (a + L)) : ‖lift a L f‖ = ‖f‖ := by
  change ‖OrientedLift.lift L (shiftCanonicalL2Equiv f)‖ = ‖f‖
  rw [OrientedLift.lift_norm, LinearIsometryEquiv.norm_map]

theorem translated_source_modes :
    ∃ U : ComplexIntervalL2 a (a + L) ≃ₗᵢ[ℂ] ComplexIntervalL2 0 L,
      ∀ u : GeneratedModes.SourceMode L,
        ∃! f : complexNeumannDomain a (a + L),
          complexNeumannOperator (by linarith [hL.out] : a < a + L) f =
              (neumannEigenvalue L (NativeModes.index (GeneratedModes.toNative L u)) : ℂ) •
                (f : ComplexIntervalL2 a (a + L)) ∧
            ‖(f : ComplexIntervalL2 a (a + L))‖ = 1 ∧
            (∃ r : ℝ, 0 < r ∧ (complexNeumannRepresentative f).value a = (r : ℂ)) ∧
            OrientedLift.lift L (U f) =ᵐ[AddCircle.haarAddCircle]
              OrientedLift.endomorphismRepresentative L u.val := by
  refine ⟨shiftCanonicalL2Equiv, ?_⟩
  intro u
  refine ⟨representative a L u, ?_, ?_⟩
  · exact ⟨representative_eigenvector a L u, representative_norm a L u,
      representative_endpoint_positive a L u, representative_lifts a L u⟩
  · intro f hf
    exact representative_unique a L u f hf.1 hf.2.1 hf.2.2.1

/-- The representative and its lift belong to the actual correlation window.
The same affine transport works for every source endomorphism. -/
theorem generatedWindow_source_modes {b : ℝ} (hb : 0 < b) :
    letI : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
    ∃ U : ComplexIntervalL2 (windowLeft b) (windowRight b) ≃ₗᵢ[ℂ]
        ComplexIntervalL2 0 (windowLengthGenerated b),
      ∀ u : GeneratedModes.SourceMode (windowLengthGenerated b),
        ∃! f : complexNeumannDomain (windowLeft b) (windowRight b),
          complexNeumannOperator (sub_pos.mp (windowLengthGenerated_pos hb)) f =
              (neumannEigenvalue (windowLengthGenerated b)
                (NativeModes.index (GeneratedModes.toNative (windowLengthGenerated b) u)) : ℂ) •
                  (f : ComplexIntervalL2 (windowLeft b) (windowRight b)) ∧
            ‖(f : ComplexIntervalL2 (windowLeft b) (windowRight b))‖ = 1 ∧
            (∃ r : ℝ, 0 < r ∧
              (complexNeumannRepresentative f).value (windowLeft b) = (r : ℂ)) ∧
            OrientedLift.lift (windowLengthGenerated b) (U f) =ᵐ[AddCircle.haarAddCircle]
              OrientedLift.endomorphismRepresentative (windowLengthGenerated b) u.val := by
  let : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
  have ha : windowLeft b < windowLeft b + windowLengthGenerated b := by
    linarith [windowLengthGenerated_pos hb]
  have h :
      ∃ U : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b) ≃ₗᵢ[ℂ]
          ComplexIntervalL2 0 (windowLengthGenerated b),
        ∀ u : GeneratedModes.SourceMode (windowLengthGenerated b),
          ∃! f : complexNeumannDomain (windowLeft b) (windowLeft b + windowLengthGenerated b),
            complexNeumannOperator ha f =
                (neumannEigenvalue (windowLengthGenerated b)
                  (NativeModes.index (GeneratedModes.toNative (windowLengthGenerated b) u)) : ℂ) •
                    (f : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b)) ∧
              ‖(f : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b))‖ = 1 ∧
              (∃ r : ℝ, 0 < r ∧
                (complexNeumannRepresentative f).value (windowLeft b) = (r : ℂ)) ∧
              OrientedLift.lift (windowLengthGenerated b) (U f) =ᵐ[AddCircle.haarAddCircle]
                OrientedLift.endomorphismRepresentative (windowLengthGenerated b) u.val :=
    translated_source_modes (windowLeft b) (windowLengthGenerated b)
  have heq := windowLeft_add_length hb
  generalize windowLeft b + windowLengthGenerated b = c at ha h heq
  subst c
  exact h

end GeneratedFoundations.Spectral.PhysicalWindowModes
