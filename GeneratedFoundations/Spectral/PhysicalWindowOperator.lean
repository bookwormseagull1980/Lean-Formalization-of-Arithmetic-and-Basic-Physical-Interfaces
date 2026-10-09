module

public import GeneratedFoundations.Spectral.PhysicalWindowEquiv
public import GeneratedFoundations.Correlation.PhysicalWindowCoordinate

/-!
# Operator transport across the generated window

The negative second derivative intertwines with the interval `L²` equivalence
on the full Neumann domain. Its action on a Sobolev representative is
independent of that representative by uniqueness of the second derivative
in `L²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

theorem generated_shiftLeft_coordinate (b x : ℝ) :
    shiftLeft (windowLeft b) x =
      Correlation.PhysicalWindowCoordinate.windowCoordinate b x := rfl

theorem generated_shiftRight_coordinateInv (b x : ℝ) :
    shiftRight (windowLeft b) x =
      Correlation.PhysicalWindowCoordinate.windowCoordinateInv b x := rfl

theorem complexNeumannOperator_translate {a L : ℝ} (hL : 0 < L)
    (u : complexNeumannDomain a (a + L)) :
    shiftCanonicalL2Equiv
        ((complexNeumannOperator (by linarith : a < a + L)).toFun u) =
      (complexNeumannOperator (by positivity : (0 : ℝ) < L)).toFun
        (translateNeumannDomainEquiv hL u) := by
  let f := complexNeumannRepresentative u
  have hf : IsComplexNeumann f := (complexNeumannRepresentative_spec u).1
  let g := translateRepresentative hL f
  have hg : IsComplexNeumann g := translateNeumannRepresentative hL f hf
  have hv : translateNeumannDomainEquiv hL u = ⟨g.toL2, g, hg, rfl⟩ := by
    apply Subtype.ext
    rfl
  calc
    shiftCanonicalL2Equiv
        ((complexNeumannOperator (by linarith : a < a + L)).toFun u) =
        shiftCanonicalL2Equiv (-f.secondL2) := rfl
    _ = -g.secondL2 := by
      rw [map_neg]
      exact congrArg Neg.neg (translateRepresentative_secondL2 hL f).symm
    _ = (complexNeumannOperator hL).toFun ⟨g.toL2, g, hg, rfl⟩ :=
      (complexNeumannOperator_on_representative hL g hg).symm
    _ = (complexNeumannOperator hL).toFun (translateNeumannDomainEquiv hL u) :=
      congrArg (complexNeumannOperator hL).toFun hv.symm

/-- The same generated endpoints determine the interval, its `L²` equivalence,
the Neumann domain equivalence and the intertwining of the differential operators. -/
theorem generatedWindow_neumann_transport {b : ℝ} (hb : 0 < b) :
    ∃ U : ComplexIntervalL2 (windowLeft b) (windowRight b) ≃ₗᵢ[ℂ]
        ComplexIntervalL2 0 (windowLengthGenerated b),
    ∃ T : complexNeumannDomain (windowLeft b) (windowRight b) ≃
        complexNeumannDomain 0 (windowLengthGenerated b),
      (∀ u, (T u : ComplexIntervalL2 0 (windowLengthGenerated b)) = U u) ∧
      (∀ u, U ((complexNeumannOperator
          (sub_pos.mp (windowLengthGenerated_pos hb))).toFun u) =
        (complexNeumannOperator (windowLengthGenerated_pos hb)).toFun (T u)) := by
  have hL : 0 < windowLengthGenerated b := windowLengthGenerated_pos hb
  have ha : windowLeft b < windowLeft b + windowLengthGenerated b := by linarith
  have h :
      ∃ U : ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b)
          ≃ₗᵢ[ℂ] ComplexIntervalL2 0 (windowLengthGenerated b),
      ∃ T : complexNeumannDomain (windowLeft b) (windowLeft b + windowLengthGenerated b)
          ≃ complexNeumannDomain 0 (windowLengthGenerated b),
        (∀ u, (T u : ComplexIntervalL2 0 (windowLengthGenerated b)) = U u) ∧
        (∀ u, U ((complexNeumannOperator ha).toFun u) =
          (complexNeumannOperator hL).toFun (T u)) := by
    refine ⟨shiftCanonicalL2Equiv, translateNeumannDomainEquiv hL, ?_, ?_⟩
    · intro u
      exact translateNeumannDomainEquiv_toL2 hL u
    · intro u
      exact complexNeumannOperator_translate hL u
  have heq := windowLeft_add_length hb
  generalize windowLeft b + windowLengthGenerated b = c at ha h heq
  subst c
  exact h

end GeneratedFoundations.Spectral
