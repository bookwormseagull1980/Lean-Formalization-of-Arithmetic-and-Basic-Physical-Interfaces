module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsFrameResponse

/-!
# Exact complexification of the generated colour coordinates

The eight matrices are the existing source generators. Their trace pairing
fixes the metric, and their proved expansion reconstructs every traceless
matrix. In particular the nonlinear commutator has unique coordinates in
these same directions. The complexification is used for the spectral
operator; real coordinates recover the original skew-Hermitian connection.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace GeneratedFoundations.Physical.SourceComplexColourCoordinates

open SourceColourCasimir
open SourceFourDimensionalYangMills
  (ColourCoordinates colourLieMatrix colourLieMatrix_conjTranspose)

abbrev Coordinates := Fin 8 → ℂ

def hermitianMatrix (c : Coordinates) : Mat3 := ∑ a, c a • generator a

def lieMatrix (c : Coordinates) : Mat3 := Complex.I • hermitianMatrix c

theorem hermitianMatrix_injective : Function.Injective hermitianMatrix := by
  intro c d h
  funext a
  have ht := congrArg (fun X : Mat3 => Matrix.trace (X * generator a)) h
  change Matrix.trace ((∑ b, c b • generator b) * generator a) =
    Matrix.trace ((∑ b, d b • generator b) * generator a) at ht
  rw [trace_combination, trace_combination] at ht
  exact (div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp ht

theorem lieMatrix_injective : Function.Injective lieMatrix := by
  intro c d h
  apply hermitianMatrix_injective
  have h' := congrArg (fun X : Mat3 => (-Complex.I) • X) h
  simpa [lieMatrix, smul_smul] using h'

theorem lieMatrix_trace (c : Coordinates) : Matrix.trace (lieMatrix c) = 0 := by
  simp [lieMatrix, hermitianMatrix, Matrix.trace_sum, Matrix.trace_smul, generator_trace]

def coordinates (X : Mat3) : Coordinates :=
  expansionCoefficient ((-Complex.I) • X)

/-- No colour component is dropped when the curvature is expanded. -/
theorem lieMatrix_coordinates (X : Mat3) (hX : Matrix.trace X = 0) :
    lieMatrix (coordinates X) = X := by
  have ht : Matrix.trace ((-Complex.I) • X) = 0 := by simp [Matrix.trace_smul, hX]
  unfold lieMatrix hermitianMatrix coordinates
  rw [generator_expansion _ ht]
  simp [smul_smul]

theorem coordinates_lieMatrix (c : Coordinates) : coordinates (lieMatrix c) = c :=
  lieMatrix_injective (lieMatrix_coordinates _ (lieMatrix_trace c))

def bracket (c d : Coordinates) : Coordinates :=
  coordinates (lieMatrix c * lieMatrix d - lieMatrix d * lieMatrix c)

/-- The coordinate operation is precisely the matrix commutator of the
generated colour action. It is not an independently chosen vertex. -/
theorem lieMatrix_bracket (c d : Coordinates) :
    lieMatrix (bracket c d) = lieMatrix c * lieMatrix d - lieMatrix d * lieMatrix c := by
  apply lieMatrix_coordinates
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

theorem hermitianMatrix_smul (t : ℂ) (c : Coordinates) :
    hermitianMatrix (t • c) = t • hermitianMatrix c := by
  simp [hermitianMatrix, Finset.smul_sum, smul_smul]

theorem lieMatrix_smul (t : ℂ) (c : Coordinates) :
    lieMatrix (t • c) = t • lieMatrix c := by
  unfold lieMatrix
  rw [hermitianMatrix_smul, smul_comm]

theorem bracket_smul (s t : ℂ) (c d : Coordinates) :
    bracket (s • c) (t • d) = (s * t) • bracket c d := by
  apply lieMatrix_injective
  rw [lieMatrix_bracket, lieMatrix_smul, lieMatrix_smul, lieMatrix_smul,
    lieMatrix_bracket]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, mul_comm t s]

theorem real_coordinates (c : ColourCoordinates) :
    lieMatrix (fun a => (c a : ℂ)) = colourLieMatrix c := by
  simp only [lieMatrix, hermitianMatrix, colourLieMatrix, Finset.smul_sum, smul_smul]

/-- The original real colour connection is retained by complexification. -/
theorem real_coordinates_skew (c : ColourCoordinates) :
    (lieMatrix (fun a => (c a : ℂ)))ᴴ = -lieMatrix (fun a => (c a : ℂ)) := by
  rw [real_coordinates]
  exact colourLieMatrix_conjTranspose c

theorem hermitianMatrix_conjTranspose (c : Coordinates) :
    (hermitianMatrix c)ᴴ = hermitianMatrix (fun a => conj (c a)) := by
  unfold hermitianMatrix
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, (generator_hermitian _).eq]
  rfl

theorem trace_hermitian_pair (c d : Coordinates) :
    Matrix.trace (hermitianMatrix c * hermitianMatrix d) =
      ((1 / 2 : ℝ) : ℂ) * ∑ a, c a * d a := by
  change Matrix.trace (hermitianMatrix c * (∑ b, d b • generator b)) = _
  simp only [Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have hc (a : Fin 8) : Matrix.trace (hermitianMatrix c * generator a) = c a / 2 :=
    trace_combination c a
  simp_rw [hc]
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  ring

/-- The complete complexified trace pairing has the same source metric as
the real connection; all cross-colour terms have been evaluated exactly. -/
theorem trace_lie_pair (c d : Coordinates) :
    Matrix.trace ((lieMatrix c)ᴴ * lieMatrix d) =
      ((1 / 2 : ℝ) : ℂ) * ∑ a, conj (c a) * d a := by
  calc
    Matrix.trace ((lieMatrix c)ᴴ * lieMatrix d) =
        Matrix.trace (hermitianMatrix (fun a => conj (c a)) * hermitianMatrix d) := by
      simp [lieMatrix, Matrix.conjTranspose_smul, hermitianMatrix_conjTranspose, smul_smul]
    _ = _ := trace_hermitian_pair _ _

theorem normalized_trace_norm (c : Coordinates) :
    2 * SourceGeneratedYangMillsFrameResponse.frameQuadratic (lieMatrix c) =
      ∑ a, ‖c a‖ ^ 2 := by
  have hc (a : Fin 8) : (conj (c a) * c a).re = ‖c a‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj']
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  have hs : (∑ a, conj (c a) * c a).re = ∑ a, ‖c a‖ ^ 2 := by
    calc
      _ = ∑ a, (conj (c a) * c a).re := map_sum Complex.reAddGroupHom _ _
      _ = _ := Finset.sum_congr rfl (fun a _ => hc a)
  rw [SourceGeneratedYangMillsFrameResponse.frameQuadratic, trace_lie_pair]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hs]
  ring

end GeneratedFoundations.Physical.SourceComplexColourCoordinates
