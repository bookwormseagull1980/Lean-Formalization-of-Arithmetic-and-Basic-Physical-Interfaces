module

public import GeneratedFoundations.Arithmetic.HistoryElementaryConnector
public import GeneratedFoundations.Geometry.SourceScalarAmplitude

/-!
# Source amplitude on the complete arithmetic carrier

The classified elementary response acts uniformly on every retained history
and phase. Its full square, not a chosen diagonal compression, is the source
intensity times identity. This fixes its norm response on every vector and
retains arbitrary coherent superpositions of arithmetic labels.
-/

@[expose] public section

noncomputable section

open scoped Kronecker

namespace GeneratedFoundations.Arithmetic.HistoryScalarAmplitude

open HistoryCliffordAction HistoryElementaryConnector
open Geometry.SourceScalarAmplitude
open Operations.ReversalRealConnector (Mat2)

theorem scalarConnector_square (N : ℕ) (H : Spinor) :
    scalarConnector N H * scalarConnector N H = (intensity H : ℂ) • (1 : Algebra N) := by
  rw [scalarConnector, HistoryComplexConnector.connector_square,
    connector_mul_adjoint, adjoint_mul_connector]
  have hb : Matrix.fromBlocks ((intensity H : ℂ) • (1 : Mat2)) 0 0
      ((intensity H : ℂ) • (1 : Mat2)) =
      (intensity H : ℂ) • (1 : Operations.SourceCliffordConnector.ChiralMatrix) := by
    simpa only [smul_zero, Matrix.fromBlocks_one] using
      (Matrix.fromBlocks_smul (intensity H : ℂ) (1 : Mat2) 0 0 (1 : Mat2)).symm
  rw [hb, Matrix.kronecker_smul, Matrix.one_kronecker_one]
  ext i j
  simp [Matrix.one_apply]

theorem operator_square (N : ℕ) (H : Spinor) :
    action N (scalarConnector N H) * action N (scalarConnector N H) =
      (intensity H : ℂ) • (1 : Module.End ℂ (Space N)) := by
  rw [← map_mul, scalarConnector_square, map_smul, map_one]

theorem complete_inner (N : ℕ) (H : Spinor) (x y : Space N) :
    inner ℂ (action N (scalarConnector N H) x) (action N (scalarConnector N H) y) =
      (intensity H : ℂ) * inner ℂ x y := by
  have he : (action N (scalarConnector N H)).adjoint * action N (scalarConnector N H) =
      (intensity H : ℂ) • (1 : Module.End ℂ (Space N)) := by
    have ha : (action N (scalarConnector N H)).adjoint = action N (scalarConnector N H) := by
      simpa only [scalarConnector] using
        HistoryComplexConnector.action_adjoint_connector N
          (Operations.ReversalRealConnector.connectorOfDoublet H)
    rw [ha, operator_square]
  calc
    _ = inner ℂ x (((action N (scalarConnector N H)).adjoint *
        action N (scalarConnector N H)) y) := by
      rw [Module.End.mul_apply, LinearMap.adjoint_inner_right]
    _ = _ := by
      rw [he]
      change inner ℂ x ((intensity H : ℂ) • y) = _
      rw [inner_smul_right (𝕜 := ℂ)]

theorem norm_sq (N : ℕ) (H : Spinor) (x : Space N) :
    ‖action N (scalarConnector N H) x‖ ^ 2 = intensity H * ‖x‖ ^ 2 := by
  have he := congrArg Complex.re (complete_inner N H x x)
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_eq_complex_re] using he

theorem intensity_frame_invariant (g : Frame) (H : Spinor) :
    intensity (Geometry.SourceScalarResponse.frameDoublet g H) = intensity H :=
  intensity_frameDoublet g H

structure Conclusions : Prop where
  positive : ∀ H : Spinor, 0 < intensity H ↔ H ≠ 0
  full_square : ∀ N H,
    scalarConnector N H * scalarConnector N H = (intensity H : ℂ) • (1 : Algebra N)
  full_inner : ∀ N H (x y : Space N),
    inner ℂ (action N (scalarConnector N H) x) (action N (scalarConnector N H) y) =
      (intensity H : ℂ) * inner ℂ x y
  full_norm : ∀ N H (x : Space N),
    ‖action N (scalarConnector N H) x‖ ^ 2 = intensity H * ‖x‖ ^ 2
  frame_invariant : ∀ g H,
    intensity (Geometry.SourceScalarResponse.frameDoublet g H) = intensity H

theorem generated : Conclusions where
  positive := intensity_pos_iff
  full_square := scalarConnector_square
  full_inner := complete_inner
  full_norm := norm_sq
  frame_invariant := intensity_frame_invariant

end GeneratedFoundations.Arithmetic.HistoryScalarAmplitude
