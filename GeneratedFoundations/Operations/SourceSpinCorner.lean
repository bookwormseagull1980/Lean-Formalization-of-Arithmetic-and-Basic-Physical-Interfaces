module

public import GeneratedFoundations.Operations.HermitePhaseFlow
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Module

/-!
# The spin corner of the Gaussian differential source

The two-dimensional corner is represented on the original Lebesgue Hilbert
space by rank-one operators between its actual generated Gaussian modes.
The ladder compression determines the spin operators; their matrix coordinates
are consequences of this construction. The corner embedding has unit `P`,
not the identity of the ambient Hilbert space. Controlled operations act as
the identity on the orthogonal complement.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.GaussianAffineLadder
open GeneratedFoundations.Operations.GaussianLadderCore
open GeneratedFoundations.Operations.HermiteFamily

namespace GeneratedFoundations.Operations.SourceSpinCorner

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev End := ComplexL2 →L[ℂ] ComplexL2

def matrixUnit {b : ℝ} (hb : 0 < b) (i j : Fin 2) : End :=
  InnerProductSpace.rankOne ℂ (sourceModes hb i) (sourceModes hb j)

theorem modes_inner {b : ℝ} (hb : 0 < b) (i j : Fin 2) :
    inner ℂ (sourceModes hb i) (sourceModes hb j) = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (sourceModes_orthonormal hb) i j

theorem modes_norm {b : ℝ} (hb : 0 < b) (i : Fin 2) : ‖sourceModes hb i‖ = 1 :=
  (sourceModes_orthonormal hb).norm_eq_one i

def corner {b : ℝ} (hb : 0 < b) : Mat2 →ₗ[ℂ] End where
  toFun M := ∑ i, ∑ j, M i j • matrixUnit hb i j
  map_add' M N := by
    simp only [Fin.sum_univ_two, Matrix.add_apply]
    module
  map_smul' z M := by
    simp [smul_smul]

theorem corner_apply {b : ℝ} (hb : 0 < b) (M : Mat2) (F : ComplexL2) :
    corner hb M F =
      (M 0 0 * inner ℂ (groundState hb) F + M 0 1 * inner ℂ (firstState hb) F) •
        groundState hb +
      (M 1 0 * inner ℂ (groundState hb) F + M 1 1 * inner ℂ (firstState hb) F) •
        firstState hb := by
  simp [corner, matrixUnit, Fin.sum_univ_two, sourceModes,
    InnerProductSpace.rankOne_apply, smul_smul, add_smul]

theorem corner_mode {b : ℝ} (hb : 0 < b) (M : Mat2) (j : Fin 2) :
    corner hb M (sourceModes hb j) = ∑ i, M i j • sourceModes hb i := by
  fin_cases j <;>
    simp [corner, matrixUnit, InnerProductSpace.rankOne_apply, modes_inner, modes_norm]

theorem corner_entry {b : ℝ} (hb : 0 < b) (M : Mat2) (i j : Fin 2) :
    inner ℂ (sourceModes hb i) (corner hb M (sourceModes hb j)) = M i j := by
  rw [corner_mode]
  fin_cases i <;>
    simp [Fin.sum_univ_two, inner_add_right, inner_smul_right, modes_inner, modes_norm]

theorem corner_injective {b : ℝ} (hb : 0 < b) : Function.Injective (corner hb) := by
  intro M N h
  ext i j
  simpa only [corner_entry] using congrArg
    (fun T : End => inner ℂ (sourceModes hb i) (T (sourceModes hb j))) h

theorem corner_synthesis {b : ℝ} (hb : 0 < b) (M : Mat2) (c : Coordinates) :
    corner hb M (synthesis hb c) =
      synthesis hb (WithLp.toLp 2 (M.mulVec (fun i => c i))) := by
  simp [corner_apply, synthesis, inner_add_right, inner_smul_right,
    inner_ground_first hb, inner_first_ground hb, inner_self_eq_norm_sq_to_K,
    groundState_norm hb, firstState_norm hb, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem corner_mul {b : ℝ} (hb : 0 < b) (M N : Mat2) :
    corner hb (M * N) = corner hb M * corner hb N := by
  apply ContinuousLinearMap.ext
  intro F
  change corner hb (M * N) F = corner hb M (corner hb N F)
  simp [corner_apply, inner_add_right, inner_smul_right,
    inner_ground_first hb, inner_first_ground hb, inner_self_eq_norm_sq_to_K,
    groundState_norm hb, firstState_norm hb, Matrix.mul_apply, Fin.sum_univ_two]
  module

theorem corner_adjoint {b : ℝ} (hb : 0 < b) (M : Mat2) :
    (corner hb M).adjoint = corner hb M.conjTranspose := by
  simp [corner, matrixUnit, Fin.sum_univ_two, map_smulₛₗ, InnerProductSpace.adjoint_rankOne,
    Matrix.conjTranspose_apply]
  abel

def projection {b : ℝ} (hb : 0 < b) : End := corner hb 1

theorem projection_apply {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    projection hb F = inner ℂ (groundState hb) F • groundState hb +
      inner ℂ (firstState hb) F • firstState hb := by
  simp [projection, corner_apply]

theorem projection_synthesis {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    projection hb (synthesis hb c) = synthesis hb c := by
  simpa [projection] using corner_synthesis hb 1 c

theorem projection_mem {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    projection hb F ∈ sourceSpace hb := by
  refine ⟨WithLp.toLp 2 ![inner ℂ (groundState hb) F, inner ℂ (firstState hb) F], ?_⟩
  simp [synthesis, projection_apply]

theorem projection_eq_self_iff {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    projection hb F = F ↔ F ∈ sourceSpace hb := by
  constructor
  · intro h
    rw [← h]
    exact projection_mem hb F
  · rintro ⟨c, rfl⟩
    exact projection_synthesis hb c

@[simp] theorem projection_mul {b : ℝ} (hb : 0 < b) (M : Mat2) :
    projection hb * corner hb M = corner hb M := by
  rw [projection, ← corner_mul, one_mul]

@[simp] theorem mul_projection {b : ℝ} (hb : 0 < b) (M : Mat2) :
    corner hb M * projection hb = corner hb M := by
  rw [projection, ← corner_mul, mul_one]

@[simp] theorem projection_sq {b : ℝ} (hb : 0 < b) :
    projection hb * projection hb = projection hb := projection_mul hb 1

@[simp] theorem projection_adjoint {b : ℝ} (hb : 0 < b) :
    (projection hb).adjoint = projection hb := by
  simp [projection, corner_adjoint]

theorem projection_isStarProjection {b : ℝ} (hb : 0 < b) :
    IsStarProjection (projection hb) := by
  exact ⟨projection_sq hb, projection_adjoint hb⟩

def loweringMatrix : Mat2 := !![0, 1; 0, 0]
def raisingMatrix : Mat2 := !![0, 0; 1, 0]

theorem corner_lowering {b : ℝ} (hb : 0 < b) :
    corner hb loweringMatrix = compressedLowering hb := by
  ext F
  simp [corner_apply, loweringMatrix, compressedLowering, InnerProductSpace.rankOne_apply]

theorem corner_raising {b : ℝ} (hb : 0 < b) :
    corner hb raisingMatrix = compressedRaising hb := by
  rw [compressedRaising, ← corner_lowering, corner_adjoint]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [loweringMatrix, raisingMatrix]

/-- A Schwartz representative of the projection of an arbitrary `L²` vector. -/
def projectedCore {b : ℝ} (hb : 0 < b) (F : ComplexL2) : Core :=
  inner ℂ (groundState hb) F • hermite hb 0 +
    inner ℂ (firstState hb) F • hermite hb 1

theorem embedding_hermite {b : ℝ} (hb : 0 < b) (n : ℕ) :
    embedding (hermite hb n) = state hb n := rfl

theorem embedding_projectedCore {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    embedding (projectedCore hb F) = projection hb F := by
  simp only [projectedCore, map_add, map_smul, embedding_hermite, state_zero, state_one,
    projection_apply]

theorem projection_state_two {b : ℝ} (hb : 0 < b) :
    projection hb (state hb 2) = 0 := by
  rw [projection_apply, ← state_zero hb, ← state_one hb,
    state_inner_eq_zero hb (by decide : (0 : ℕ) ≠ 2),
    state_inner_eq_zero hb (by decide : (1 : ℕ) ≠ 2)]
  simp

/-- Equality with the actual differential compression, for every original vector. -/
theorem annihilation_compression {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    embedding (annihilation b (projectedCore hb F)) = compressedLowering hb F := by
  simp only [projectedCore, map_add, map_smul, annihilation_hermite_zero,
    annihilation_hermite_succ hb 0, smul_zero, zero_add]
  norm_num [embedding_hermite, embedding_groundSchwartz, compressedLowering,
    InnerProductSpace.rankOne_apply]

/-- The component raised to the second excited state is removed by the same projection. -/
theorem creation_compression {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    projection hb (embedding (creation b (projectedCore hb F))) =
      compressedRaising hb F := by
  simp only [projectedCore, map_add, map_smul, creation_hermite, embedding_hermite]
  have hp : projection hb (firstState hb) = firstState hb := by
    simp [projection_apply, inner_ground_first hb, inner_self_eq_norm_sq_to_K,
      firstState_norm hb]
  simp only [Nat.zero_add, state_one]
  norm_num [hp, projection_state_two, compressedRaising, compressedLowering,
    InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_apply]

/-- The source spin operators, defined by the actual compressed differential ladder. -/
def spin1 {b : ℝ} (hb : 0 < b) : End :=
  (1 / 2 : ℂ) • (compressedRaising hb + compressedLowering hb)

def spin2 {b : ℝ} (hb : 0 < b) : End :=
  (2 * Complex.I)⁻¹ • (compressedRaising hb - compressedLowering hb)

def spin3 {b : ℝ} (hb : 0 < b) : End :=
  compressedRaising hb * compressedLowering hb - (1 / 2 : ℂ) • projection hb

def spinMatrix1 : Mat2 := !![0, 1 / 2; 1 / 2, 0]
def spinMatrix2 : Mat2 := !![0, Complex.I / 2; -Complex.I / 2, 0]
def spinMatrix3 : Mat2 := !![-1 / 2, 0; 0, 1 / 2]

theorem spin1_eq_corner {b : ℝ} (hb : 0 < b) : spin1 hb = corner hb spinMatrix1 := by
  rw [spin1, ← corner_raising, ← corner_lowering, ← map_add, ← map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [raisingMatrix, loweringMatrix, spinMatrix1]

theorem spin2_eq_corner {b : ℝ} (hb : 0 < b) : spin2 hb = corner hb spinMatrix2 := by
  rw [spin2, ← corner_raising, ← corner_lowering, ← map_sub, ← map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raisingMatrix, loweringMatrix, spinMatrix2, div_eq_mul_inv]

theorem spin3_eq_corner {b : ℝ} (hb : 0 < b) : spin3 hb = corner hb spinMatrix3 := by
  rw [spin3, ← corner_raising, ← corner_lowering, ← corner_mul, projection,
    ← map_smul, ← map_sub]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raisingMatrix, loweringMatrix, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two]

theorem ladder_commutator {b : ℝ} (hb : 0 < b) :
    compressedRaising hb * compressedLowering hb -
      compressedLowering hb * compressedRaising hb = (2 : ℂ) • spin3 hb := by
  rw [spin3_eq_corner, ← corner_raising, ← corner_lowering, ← corner_mul, ← corner_mul,
    ← map_sub, ← map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raisingMatrix, loweringMatrix, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two]

theorem spin_commutator {b : ℝ} (hb : 0 < b) :
    spin1 hb * spin2 hb - spin2 hb * spin1 hb = Complex.I • spin3 hb := by
  rw [spin1_eq_corner, spin2_eq_corner, spin3_eq_corner, ← corner_mul, ← corner_mul,
    ← map_sub, ← map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinMatrix1, spinMatrix2, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two,
      div_eq_mul_inv] <;> ring

theorem spin3_raising_commutator {b : ℝ} (hb : 0 < b) :
    spin3 hb * compressedRaising hb - compressedRaising hb * spin3 hb =
      compressedRaising hb := by
  rw [spin3_eq_corner, ← corner_raising, ← corner_mul, ← corner_mul, ← map_sub]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raisingMatrix, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two]

theorem spin3_lowering_commutator {b : ℝ} (hb : 0 < b) :
    spin3 hb * compressedLowering hb - compressedLowering hb * spin3 hb =
      -compressedLowering hb := by
  rw [spin3_eq_corner, ← corner_lowering, ← corner_mul, ← corner_mul, ← map_sub,
    ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [loweringMatrix, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two]

theorem spin_commutator_cyclic {b : ℝ} (hb : 0 < b) :
    spin2 hb * spin3 hb - spin3 hb * spin2 hb = Complex.I • spin1 hb ∧
      spin3 hb * spin1 hb - spin1 hb * spin3 hb = Complex.I • spin2 hb := by
  constructor <;>
    rw [spin1_eq_corner, spin2_eq_corner, spin3_eq_corner, ← corner_mul,
      ← corner_mul, ← map_sub, ← map_smul]
  all_goals
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [spinMatrix1, spinMatrix2, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two,
        div_eq_mul_inv] <;> ring_nf <;> norm_num

theorem spin_casimir {b : ℝ} (hb : 0 < b) :
    spin1 hb * spin1 hb + spin2 hb * spin2 hb + spin3 hb * spin3 hb =
      (3 / 4 : ℂ) • projection hb := by
  rw [spin1_eq_corner, spin2_eq_corner, spin3_eq_corner,
    ← corner_mul, ← corner_mul, ← corner_mul, ← map_add, ← map_add, projection, ← map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [spinMatrix1, spinMatrix2, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two,
      div_eq_mul_inv] <;> ring_nf <;> norm_num

theorem hermitian_traceless_span (M : Mat2) (hM : M.conjTranspose = M)
    (ht : Matrix.trace M = 0) :
    M = (2 * (M 0 1).re : ℂ) • spinMatrix1 +
      (2 * (M 0 1).im : ℂ) • spinMatrix2 +
      (-2 * (M 0 0).re : ℂ) • spinMatrix3 := by
  have h00 := congrArg (fun A : Mat2 => A 0 0) hM
  have h10 := congrArg (fun A : Mat2 => A 1 0) hM
  have h11 : M 1 1 = -M 0 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two, eq_neg_iff_add_eq_zero, add_comm] using ht
  have him : (M 0 0).im = 0 := by
    have := congrArg Complex.im h00
    simp [Matrix.conjTranspose_apply] at this
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [spinMatrix1, spinMatrix2, spinMatrix3, h11,
      ← h10, Matrix.conjTranspose_apply, him] <;> ring

theorem skew_traceless_span (M : Mat2) (hM : M.conjTranspose = -M)
    (ht : Matrix.trace M = 0) :
    ∃ x y z : ℝ, M = (Complex.I * x) • spinMatrix1 +
      (Complex.I * y) • spinMatrix2 + (Complex.I * z) • spinMatrix3 := by
  let H : Mat2 := (-Complex.I) • M
  have hH : H.conjTranspose = H := by
    simp [H, Matrix.conjTranspose_smul, hM, smul_neg, neg_smul]
  have htr : Matrix.trace H = 0 := by simp [H, ht]
  have h := hermitian_traceless_span H hH htr
  refine ⟨2 * (H 0 1).re, 2 * (H 0 1).im, -2 * (H 0 0).re, ?_⟩
  have hi : Complex.I • H = M := by simp [H, smul_smul]
  have h' := congrArg (fun A : Mat2 => Complex.I • A) h
  rw [hi] at h'
  simpa only [smul_add, smul_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_neg] using h'

theorem spinMatrix_hermitian :
    spinMatrix1.conjTranspose = spinMatrix1 ∧
      spinMatrix2.conjTranspose = spinMatrix2 ∧
      spinMatrix3.conjTranspose = spinMatrix3 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [spinMatrix1]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [spinMatrix2, spinMatrix3]

theorem spinMatrix_trace :
    Matrix.trace spinMatrix1 = 0 ∧ Matrix.trace spinMatrix2 = 0 ∧
      Matrix.trace spinMatrix3 = 0 := by
  norm_num [Matrix.trace, Fin.sum_univ_two, spinMatrix1, spinMatrix2, spinMatrix3]

theorem spinMatrix_real_independent (x y z : ℝ)
    (h : (x : ℂ) • spinMatrix1 + (y : ℂ) • spinMatrix2 + (z : ℂ) • spinMatrix3 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hr := congrArg (fun M : Mat2 => (M 0 1).re) h
  have hi := congrArg (fun M : Mat2 => (M 0 1).im) h
  have hz := congrArg (fun M : Mat2 => (M 0 0).re) h
  simp [spinMatrix1, spinMatrix2, spinMatrix3] at hr hi hz
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A finite corner is extended by the identity on its orthogonal complement. -/
def control {b : ℝ} (hb : 0 < b) (M : Mat2) : End :=
  1 - projection hb + corner hb M

@[simp] theorem control_one {b : ℝ} (hb : 0 < b) : control hb 1 = 1 := by
  simp [control, projection]

theorem control_mul {b : ℝ} (hb : 0 < b) (M N : Mat2) :
    control hb (M * N) = control hb M * control hb N := by
  simp only [control, corner_mul, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one,
    projection_sq, projection_mul, mul_projection]
  abel

theorem control_adjoint {b : ℝ} (hb : 0 < b) (M : Mat2) :
    (control hb M).adjoint = control hb M.conjTranspose := by
  simp [control, ContinuousLinearMap.adjoint_one, corner_adjoint]

theorem control_mem_unitary {b : ℝ} (hb : 0 < b) (M : Mat2)
    (hM : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) : control hb M ∈ unitary End := by
  rcases hM with ⟨hl, hr⟩
  constructor
  · change (control hb M).adjoint * control hb M = 1
    rw [control_adjoint, ← control_mul]
    exact (congrArg (control hb) hl).trans (control_one hb)
  · change control hb M * (control hb M).adjoint = 1
    rw [control_adjoint, ← control_mul]
    exact (congrArg (control hb) hr).trans (control_one hb)

theorem control_injective {b : ℝ} (hb : 0 < b) : Function.Injective (control hb) := by
  intro M N h
  apply corner_injective hb
  exact add_left_cancel h

theorem control_synthesis {b : ℝ} (hb : 0 < b) (M : Mat2) (c : Coordinates) :
    control hb M (synthesis hb c) =
      synthesis hb (WithLp.toLp 2 (M.mulVec (fun i => c i))) := by
  simp [control, projection_synthesis, corner_synthesis]

theorem control_of_orthogonal {b : ℝ} (hb : 0 < b) (M : Mat2) (F : ComplexL2)
    (hg : inner ℂ (groundState hb) F = 0) (hf : inner ℂ (firstState hb) F = 0) :
    control hb M F = F := by
  simp [control, projection_apply, corner_apply, hg, hf]

end GeneratedFoundations.Operations.SourceSpinCorner
