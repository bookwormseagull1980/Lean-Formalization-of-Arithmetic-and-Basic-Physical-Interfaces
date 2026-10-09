module

public import GeneratedFoundations.Operations.FiniteHermiteCorner
public import GeneratedFoundations.Operations.FiniteWeylAverage

/-!
# Weyl preparation on the Gaussian Hermite corner

The first `n+1` Hermite states carry the finite shift and phase matrices.
Their extensions fix the orthogonal complement and belong to the ladder
operation algebra. Averaging their conjugations prepares the normalized
projection from every trace-one matrix on the corner.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteFamily
open GeneratedFoundations.Operations.SourceSpinCorner (End)

namespace GeneratedFoundations.Operations.SourceWeylPreparation

local instance positiveDimension (n : ℕ) : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩

def modes (n : ℕ) : FiniteWeylAverage.Index n → ℕ := ZMod.val

theorem modes_injective (n : ℕ) : Function.Injective (modes n) :=
  ZMod.val_injective (n + 1)

theorem modes_lt (n : ℕ) (i : FiniteWeylAverage.Index n) : modes n i < n + 1 := ZMod.val_lt i

def corner {b : ℝ} (hb : 0 < b) (n : ℕ) : FiniteWeylAverage.Mat n →ₗ[ℂ] End :=
  FiniteHermiteCorner.corner hb (modes n)

def projection {b : ℝ} (hb : 0 < b) (n : ℕ) : End := FiniteHermiteCorner.projection hb (modes n)

def sourceWeyl {b : ℝ} (hb : 0 < b) (n : ℕ) (a d : FiniteWeylAverage.Index n) : End :=
  FiniteHermiteCorner.control hb (modes n) (FiniteWeylAverage.weyl n a d)

theorem sourceWeyl_unitary {b : ℝ} (hb : 0 < b) (n : ℕ) (a d : FiniteWeylAverage.Index n) :
    sourceWeyl hb n a d ∈ unitary End :=
  FiniteHermiteCorner.control_mem_unitary hb (modes n) (modes_injective n) _
    (FiniteWeylAverage.weyl_unitary n a d)

theorem sourceWeyl_mem_ladder {b : ℝ} (hb : 0 < b) (n : ℕ) (a d : FiniteWeylAverage.Index n) :
    sourceWeyl hb n a d ∈ SourceMatrixUnits.ladderOperationAlgebra hb :=
  FiniteHermiteCorner.control_mem_ladder hb (modes n) _

theorem sourceWeyl_fixes_complement {b : ℝ} (hb : 0 < b) (n : ℕ)
    (a d : FiniteWeylAverage.Index n) (F : ComplexL2) (hF : projection hb n F = 0) :
    sourceWeyl hb n a d F = F :=
  FiniteHermiteCorner.control_fixed_complement hb (modes n) (modes_injective n) _ F hF

theorem sourceWeyl_conjugation {b : ℝ} (hb : 0 < b) (n : ℕ)
    (a d : FiniteWeylAverage.Index n) (X : FiniteWeylAverage.Mat n) :
    sourceWeyl hb n a d * corner hb n X * (sourceWeyl hb n a d).adjoint =
      corner hb n (FiniteWeylAverage.weyl n a d * X *
        (FiniteWeylAverage.weyl n a d).conjTranspose) :=
  FiniteHermiteCorner.control_conjugation hb (modes n) (modes_injective n) _ X

def sourceAverage {b : ℝ} (hb : 0 < b) (n : ℕ) (T : End) : End :=
  ((((n + 1 : ℕ) : ℂ) ^ 2)⁻¹) •
    (∑ a : FiniteWeylAverage.Index n, ∑ d : FiniteWeylAverage.Index n,
      sourceWeyl hb n a d * T * (sourceWeyl hb n a d).adjoint)

theorem sourceAverage_corner {b : ℝ} (hb : 0 < b) (n : ℕ)
    (X : FiniteWeylAverage.Mat n) :
    sourceAverage hb n (corner hb n X) = corner hb n (FiniteWeylAverage.average n X) := by
  simp only [sourceAverage, sourceWeyl_conjugation, FiniteWeylAverage.average, map_smul, map_sum]

theorem sourceAverage_eq_trace {b : ℝ} (hb : 0 < b) (n : ℕ)
    (X : FiniteWeylAverage.Mat n) :
    sourceAverage hb n (corner hb n X) =
      (Matrix.trace X / ((n + 1 : ℕ) : ℂ)) • projection hb n := by
  rw [sourceAverage_corner, FiniteWeylAverage.average_eq_trace, map_smul]
  rfl

theorem sourceAverage_of_trace_one {b : ℝ} (hb : 0 < b) (n : ℕ)
    (X : FiniteWeylAverage.Mat n) (hX : Matrix.trace X = 1) :
    sourceAverage hb n (corner hb n X) =
      (((n + 1 : ℕ) : ℂ)⁻¹) • projection hb n := by
  simp only [sourceAverage_eq_trace, hX, one_div]

def sourceTrace {b : ℝ} (hb : 0 < b) (n : ℕ) (T : End) : ℂ :=
  ∑ i : FiniteWeylAverage.Index n, inner ℂ (state hb (modes n i)) (T (state hb (modes n i)))

theorem sourceTrace_corner {b : ℝ} (hb : 0 < b) (n : ℕ)
    (X : FiniteWeylAverage.Mat n) :
    sourceTrace hb n (corner hb n X) = Matrix.trace X := by
  simp only [sourceTrace, corner,
    FiniteHermiteCorner.corner_entry hb (modes n) (modes_injective n)]
  rfl

/-- The normalized projection has unit trace in the selected source space. -/
theorem prepared_sourceTrace {b : ℝ} (hb : 0 < b) (n : ℕ) :
    sourceTrace hb n ((((n + 1 : ℕ) : ℂ)⁻¹) • projection hb n) = 1 := by
  have hcorner : (((n + 1 : ℕ) : ℂ)⁻¹) • projection hb n =
      corner hb n ((((n + 1 : ℕ) : ℂ)⁻¹) • (1 : FiniteWeylAverage.Mat n)) := by
    rw [map_smul]
    rfl
  rw [hcorner, sourceTrace_corner]
  simp only [Matrix.trace_smul, Matrix.trace_one, FiniteWeylAverage.Index, ZMod.card,
    smul_eq_mul, inv_mul_cancel₀ (FiniteWeylAverage.dimension_ne_zero n)]

end GeneratedFoundations.Operations.SourceWeylPreparation
