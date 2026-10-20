module

public import GeneratedFoundations.Operations.SourceReversalRealConnector
public import GeneratedFoundations.Operations.FiniteHermiteCornerExponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Clifford connectors in finite Hermite corners

A source quaternion gives a self-adjoint odd block on two labelled spinor
carriers. Its square and polarization use the normalized source trace
metric. Repetition on a finite colour factor is realized on the first
`4*d` actual Hermite states. The resulting operator belongs to the source
ladder algebra and has scalar square times the corner projection.

The colour-natural form is constructed here. Its characterization by a
naturality condition and its charged action are separate assertions.
-/

@[expose] public section

noncomputable section

open scoped Quaternion Kronecker RealInnerProductSpace Matrix.Norms.Operator
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Operations.ReversalRealConnector (Mat2)
open GeneratedFoundations.Operations.SourceSpinCorner (End)
open GeneratedFoundations.Operations.FiniteHermiteCorner
open GeneratedFoundations.Operations.FiniteHermiteCornerExponential
open GeneratedFoundations.Operations.SourceMatrixUnits (ladderOperationAlgebra)

namespace GeneratedFoundations.Operations.SourceCliffordConnector

abbrev ChiralIndex := Fin 2 ⊕ Fin 2
abbrev ChiralMatrix := Matrix ChiralIndex ChiralIndex ℂ

theorem matrixMap_real (r : ℝ) : matrixMap (r : ℍ) = r • (1 : Mat2) := by
  rw [matrixMap_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneratedFoundations.Operations.SourceSpinCornerGroup.canonical]

theorem matrixMap_mul_adjoint (q : ℍ) :
    matrixMap q * (matrixMap q).conjTranspose = Quaternion.normSq q • (1 : Mat2) := by
  rw [← matrixMap_star, ← map_mul, Quaternion.self_mul_star, matrixMap_real]

theorem matrixMap_adjoint_mul (q : ℍ) :
    (matrixMap q).conjTranspose * matrixMap q = Quaternion.normSq q • (1 : Mat2) := by
  rw [← matrixMap_star, ← map_mul, Quaternion.star_mul_self, matrixMap_real]

def clifford (q : ℍ) : ChiralMatrix :=
  Matrix.fromBlocks 0 (matrixMap q) (matrixMap q).conjTranspose 0

theorem clifford_adjoint (q : ℍ) : (clifford q).conjTranspose = clifford q := by
  simp [clifford, Matrix.fromBlocks_conjTranspose]

@[simp] theorem clifford_zero : clifford 0 = 0 := by
  simp [clifford]

theorem clifford_add (p q : ℍ) : clifford (p + q) = clifford p + clifford q := by
  simp [clifford, Matrix.fromBlocks_add]

theorem clifford_real_smul (r : ℝ) (q : ℍ) : clifford (r • q) = r • clifford q := by
  simp [clifford, Matrix.fromBlocks_smul]

def cliffordLinear : ℍ →ₗ[ℝ] ChiralMatrix where
  toFun := clifford
  map_add' := clifford_add
  map_smul' := clifford_real_smul

theorem clifford_injective : Function.Injective clifford := by
  intro p q hpq
  apply matrixMap_injective
  ext i j
  exact congrArg (fun M : ChiralMatrix => M (Sum.inl i) (Sum.inr j)) hpq

theorem clifford_square (q : ℍ) :
    clifford q * clifford q = Quaternion.normSq q • (1 : ChiralMatrix) := by
  simp only [clifford, Matrix.fromBlocks_multiply, mul_zero, zero_mul,
    zero_add, add_zero, matrixMap_mul_adjoint, matrixMap_adjoint_mul]
  have hOne : Matrix.fromBlocks (1 : Mat2) 0 0 (1 : Mat2) = (1 : ChiralMatrix) :=
    Matrix.fromBlocks_one
  simpa only [Matrix.fromBlocks_smul, smul_zero] using
    congrArg (fun M : ChiralMatrix => Quaternion.normSq q • M) hOne

theorem clifford_anticommutator (p q : ℍ) :
    clifford p * clifford q + clifford q * clifford p =
      (2 * inner ℝ p q) • (1 : ChiralMatrix) := by
  have hs := clifford_square (p + q)
  rw [clifford_add, add_mul, mul_add, mul_add, clifford_square, clifford_square,
    Quaternion.normSq_add, ← Quaternion.inner_def, add_smul, add_smul] at hs
  apply add_left_cancel (a := Quaternion.normSq p • (1 : ChiralMatrix) +
    Quaternion.normSq q • (1 : ChiralMatrix))
  calc
    _ = (Quaternion.normSq p • (1 : ChiralMatrix) + clifford p * clifford q) +
        (clifford q * clifford p + Quaternion.normSq q • (1 : ChiralMatrix)) := by abel
    _ = _ := hs

def grading : ChiralMatrix := Matrix.fromBlocks (1 : Mat2) 0 0 (-1 : Mat2)

theorem grading_adjoint : grading.conjTranspose = grading := by
  simp [grading, Matrix.fromBlocks_conjTranspose]

theorem grading_square : grading * grading = (1 : ChiralMatrix) := by
  simp [grading, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem clifford_odd (q : ℍ) : grading * clifford q + clifford q * grading = 0 := by
  simp [grading, clifford, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]

/-- The source trace supplies the Euclidean quadratic form used in the square relation. -/
theorem clifford_square_source_trace (q : ℍ) :
    clifford q * clifford q =
      ((Matrix.trace ((matrixMap q).conjTranspose * matrixMap q)).re / 2) •
        (1 : ChiralMatrix) := by
  rw [trace_normSq, clifford_square]

abbrev ColourIndex (d : ℕ) := Fin d × ChiralIndex
abbrev ColourMatrix (d : ℕ) := Matrix (ColourIndex d) (ColourIndex d) ℂ

def colourClifford (d : ℕ) (q : ℍ) : ColourMatrix d :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ clifford q

def colourGrading (d : ℕ) : ColourMatrix d :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ grading

theorem colourGrading_adjoint (d : ℕ) : (colourGrading d).conjTranspose = colourGrading d := by
  simp [colourGrading, Matrix.conjTranspose_kronecker, grading_adjoint]

theorem colourGrading_square (d : ℕ) : colourGrading d * colourGrading d = 1 := by
  rw [colourGrading, ← Matrix.mul_kronecker_mul, one_mul, grading_square,
    Matrix.one_kronecker_one]

theorem colourClifford_adjoint (d : ℕ) (q : ℍ) :
    (colourClifford d q).conjTranspose = colourClifford d q := by
  simp [colourClifford, Matrix.conjTranspose_kronecker, clifford_adjoint]

@[simp] theorem colourClifford_zero (d : ℕ) : colourClifford d 0 = 0 := by
  simp [colourClifford]

theorem colourClifford_square (d : ℕ) (q : ℍ) :
    colourClifford d q * colourClifford d q = Quaternion.normSq q • (1 : ColourMatrix d) := by
  rw [colourClifford, ← Matrix.mul_kronecker_mul, one_mul, clifford_square,
    Matrix.kronecker_smul, Matrix.one_kronecker_one]

theorem colourClifford_odd (d : ℕ) (q : ℍ) :
    colourGrading d * colourClifford d q + colourClifford d q * colourGrading d = 0 := by
  simp only [colourGrading, colourClifford, ← Matrix.mul_kronecker_mul, one_mul,
    ← Matrix.kronecker_add, clifford_odd, Matrix.kronecker_zero]

theorem colourClifford_injective (d : ℕ) [NeZero d] :
    Function.Injective (colourClifford d) := by
  intro p q hpq
  apply clifford_injective
  ext i j
  have h := congrArg (fun M : ColourMatrix d => M (0, i) (0, j)) hpq
  simpa only [colourClifford, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul] using h

/-- Left and right labels occupy consecutive pairs in each colour block. -/
def sourceMode {d : ℕ} (a : ColourIndex d) : ℕ :=
  4 * a.1.val + Sum.elim (fun i : Fin 2 => i.val) (fun i : Fin 2 => 2 + i.val) a.2

theorem sourceMode_injective (d : ℕ) : Function.Injective (sourceMode (d := d)) := by
  rintro ⟨a, i | i⟩ ⟨b, j | j⟩ h
  · have hab : a = b := Fin.ext (by dsimp [sourceMode] at h; omega)
    have hij : i = j := Fin.ext (by dsimp [sourceMode] at h; omega)
    cases hab
    cases hij
    rfl
  · dsimp [sourceMode] at h
    omega
  · dsimp [sourceMode] at h
    omega
  · have hab : a = b := Fin.ext (by dsimp [sourceMode] at h; omega)
    have hij : i = j := Fin.ext (by dsimp [sourceMode] at h; omega)
    cases hab
    cases hij
    rfl

theorem sourceMode_lt {d : ℕ} (a : ColourIndex d) : sourceMode a < 4 * d := by
  rcases a with ⟨a, i | i⟩ <;> dsimp [sourceMode] <;> omega

theorem mem_sourceMode_range (d k : ℕ) :
    k ∈ Set.range (sourceMode (d := d)) ↔ k < 4 * d := by
  constructor
  · rintro ⟨a, rfl⟩
    exact sourceMode_lt a
  · intro hk
    let a : Fin d := ⟨k / 4, by omega⟩
    by_cases hleft : k % 4 < 2
    · refine ⟨(a, Sum.inl ⟨k % 4, hleft⟩), ?_⟩
      dsimp [sourceMode, a]
      omega
    · have hright : k % 4 - 2 < 2 := by omega
      refine ⟨(a, Sum.inr ⟨k % 4 - 2, hright⟩), ?_⟩
      dsimp [sourceMode, a]
      omega

theorem colourIndex_card (d : ℕ) : Fintype.card (ColourIndex d) = 4 * d := by
  simp only [ColourIndex, ChiralIndex, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  omega

def sourceConnector {b : ℝ} (hb : 0 < b) (d : ℕ) (q : ℍ) : End :=
  corner hb sourceMode (colourClifford d q)

def sourceGrading {b : ℝ} (hb : 0 < b) (d : ℕ) : End :=
  corner hb sourceMode (colourGrading d)

theorem sourceGrading_adjoint {b : ℝ} (hb : 0 < b) (d : ℕ) :
    (sourceGrading hb d).adjoint = sourceGrading hb d := by
  rw [sourceGrading, corner_adjoint, colourGrading_adjoint]

theorem sourceGrading_square {b : ℝ} (hb : 0 < b) (d : ℕ) :
    sourceGrading hb d * sourceGrading hb d = projection hb (sourceMode (d := d)) := by
  rw [sourceGrading, ← corner_mul hb sourceMode (sourceMode_injective d), colourGrading_square]
  rfl

theorem sourceConnector_adjoint {b : ℝ} (hb : 0 < b) (d : ℕ) (q : ℍ) :
    (sourceConnector hb d q).adjoint = sourceConnector hb d q := by
  rw [sourceConnector, corner_adjoint, colourClifford_adjoint]

theorem sourceConnector_square {b : ℝ} (hb : 0 < b) (d : ℕ) (q : ℍ) :
    sourceConnector hb d q * sourceConnector hb d q =
      Quaternion.normSq q • projection hb (sourceMode (d := d)) := by
  rw [sourceConnector, ← corner_mul hb sourceMode (sourceMode_injective d),
    colourClifford_square, LinearMap.map_smul_of_tower]
  rfl

theorem sourceConnector_odd {b : ℝ} (hb : 0 < b) (d : ℕ) (q : ℍ) :
    sourceGrading hb d * sourceConnector hb d q +
      sourceConnector hb d q * sourceGrading hb d = 0 := by
  simp only [sourceGrading, sourceConnector,
    ← corner_mul hb sourceMode (sourceMode_injective d), ← map_add,
    colourClifford_odd, map_zero]

theorem sourceConnector_mem_ladder {b : ℝ} (hb : 0 < b) (d : ℕ) (q : ℍ) :
    sourceConnector hb d q ∈ ladderOperationAlgebra hb :=
  corner_mem_ladder hb sourceMode (colourClifford d q)

theorem sourceConnector_injective {b : ℝ} (hb : 0 < b) (d : ℕ) [NeZero d] :
    Function.Injective (sourceConnector hb d) :=
  (corner_injective hb sourceMode (sourceMode_injective d)).comp (colourClifford_injective d)

theorem sourceConnector_normal_ne_zero {b : ℝ} (hb : 0 < b) (d : ℕ) [NeZero d] :
    sourceConnector hb d 1 ≠ 0 := by
  intro h
  have hzero : sourceConnector hb d 0 = 0 := by simp [sourceConnector]
  exact one_ne_zero ((sourceConnector_injective hb d) (h.trans hzero.symm))

/-- Exponentiation takes place in the original Gaussian operator space. -/
theorem sourceConnector_exp {b : ℝ} (hb : 0 < b) (d : ℕ) (q : ℍ) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • sourceConnector hb d q) =
      control hb sourceMode (NormedSpace.exp ((Complex.I * (t : ℂ)) • colourClifford d q)) :=
  exp_smul_corner hb sourceMode (sourceMode_injective d) _ _

theorem sourceConnector_exp_mem_unitary {b : ℝ} (hb : 0 < b)
    (d : ℕ) (q : ℍ) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • sourceConnector hb d q) ∈ unitary End :=
  exp_smul_corner_mem_unitary hb sourceMode (colourClifford d q)
    (colourClifford_adjoint d q) t

theorem sourceConnector_exp_mem_ladder {b : ℝ} (hb : 0 < b)
    (d : ℕ) (q : ℍ) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • sourceConnector hb d q) ∈
      ladderOperationAlgebra hb :=
  exp_smul_corner_mem_ladder hb sourceMode (sourceMode_injective d) _ _

end GeneratedFoundations.Operations.SourceCliffordConnector
