module

public import GeneratedFoundations.Geometry.SourceScalarResponse

/-!
# Positive amplitude of the generated source doublet

The determinant and both quadratic products of the reversal-real source
matrix give the same positive amplitude. Independent source frames preserve
it. This statement uses the original two-mode source and is common to both
branches; no physical charge assignment is part of its construction.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.SourceScalarAmplitude

open Operations.ReversalRealConnector
open SourceScalarResponse

def intensity (H : Spinor) : ℝ := Complex.normSq (H 0) + Complex.normSq (H 1)

theorem intensity_nonneg (H : Spinor) : 0 ≤ intensity H :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem intensity_eq_zero_iff (H : Spinor) : intensity H = 0 ↔ H = 0 := by
  constructor
  · intro h
    have h0 : Complex.normSq (H 0) = 0 := by
      dsimp [intensity] at h
      nlinarith [Complex.normSq_nonneg (H 0), Complex.normSq_nonneg (H 1)]
    have h1 : Complex.normSq (H 1) = 0 := by
      dsimp [intensity] at h
      nlinarith [Complex.normSq_nonneg (H 0), Complex.normSq_nonneg (H 1)]
    funext i
    fin_cases i
    · exact Complex.normSq_eq_zero.mp h0
    · exact Complex.normSq_eq_zero.mp h1
  · rintro rfl
    simp [intensity]

theorem intensity_pos_iff (H : Spinor) : 0 < intensity H ↔ H ≠ 0 :=
  (lt_iff_le_and_ne).trans ⟨fun h => by
    intro hH
    exact h.2 ((intensity_eq_zero_iff H).mpr hH).symm,
    fun h => ⟨intensity_nonneg H, fun he => h ((intensity_eq_zero_iff H).mp he.symm)⟩⟩

theorem det_connector (H : Spinor) :
    Matrix.det (connectorOfDoublet H) = (intensity H : ℂ) := by
  apply Complex.ext <;>
    simp [connectorOfDoublet, Matrix.det_fin_two, intensity, Complex.normSq_apply] <;> ring

theorem connector_mul_adjoint (H : Spinor) :
    connectorOfDoublet H * (connectorOfDoublet H).conjTranspose =
      (intensity H : ℂ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [connectorOfDoublet, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, intensity, Complex.normSq_apply] <;> ring

theorem adjoint_mul_connector (H : Spinor) :
    (connectorOfDoublet H).conjTranspose * connectorOfDoublet H =
      (intensity H : ℂ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [connectorOfDoublet, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, intensity, Complex.normSq_apply] <;> ring

theorem det_frameMatrix (g : Frame) (M : Mat2) :
    Matrix.det (frameMatrix g M) = Matrix.det M := by
  have hL := (Matrix.mem_specialUnitaryGroup_iff.mp g.1.property).2
  have hR := (Matrix.mem_specialUnitaryGroup_iff.mp g.2.property).2
  simp [frameMatrix, Matrix.det_mul, Matrix.det_conjTranspose, hL, hR]

theorem intensity_frameDoublet (g : Frame) (H : Spinor) :
    intensity (frameDoublet g H) = intensity H := by
  apply Complex.ofReal_injective
  rw [← det_connector, connectorOfDoublet_frameDoublet, det_frameMatrix, det_connector]

end GeneratedFoundations.Geometry.SourceScalarAmplitude
