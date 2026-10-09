module

public import GeneratedFoundations.Operations.SourceMatrixUnits

/-!
# Finite Hermite corners

A finite selection of Hermite states identifies a matrix algebra with a corner
of the Gaussian Hilbert space. Its matrix units belong to the algebra generated
by the normalized ladder. A unitary matrix extends by the identity on the
orthogonal complement of the selected states.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteFamily
open GeneratedFoundations.Operations.SourceSpinCorner (End)
open GeneratedFoundations.Operations.SourceMatrixUnits

namespace GeneratedFoundations.Operations.FiniteHermiteCorner

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def corner {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) :
    Matrix ι ι ℂ →ₗ[ℂ] End where
  toFun M := ∑ i, ∑ j, M i j • matrixUnit hb (modes i) (modes j)
  map_add' M N := by
    apply ContinuousLinearMap.ext
    intro F
    simp only [sum_apply, Matrix.add_apply, smul_apply, add_smul,
      Finset.sum_add_distrib, add_apply]
  map_smul' c M := by
    simp [Finset.smul_sum, smul_smul]

omit [DecidableEq ι] in
theorem corner_def {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) (M : Matrix ι ι ℂ) :
    corner hb modes M = ∑ i, ∑ j, M i j • matrixUnit hb (modes i) (modes j) := rfl

omit [DecidableEq ι] in
theorem corner_apply {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (M : Matrix ι ι ℂ) (F : ComplexL2) :
    corner hb modes M F =
      ∑ i, ∑ j, (M i j * inner ℂ (state hb (modes j)) F) • state hb (modes i) := by
  simp [corner_def, sum_apply, matrixUnit_apply, smul_smul]

theorem corner_state {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M : Matrix ι ι ℂ) (j : ι) :
    corner hb modes M (state hb (modes j)) = ∑ i, M i j • state hb (modes i) := by
  simp [corner_apply, state_inner, hinj.eq_iff]

theorem corner_entry {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M : Matrix ι ι ℂ) (i j : ι) :
    inner ℂ (state hb (modes i)) (corner hb modes M (state hb (modes j))) = M i j := by
  rw [corner_state hb modes hinj]
  simp [inner_sum, inner_smul_right, state_inner, hinj.eq_iff]

theorem corner_injective {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) : Function.Injective (corner hb modes) := by
  intro M N h
  ext i j
  simpa only [corner_entry hb modes hinj] using congrArg
    (fun T : End => inner ℂ (state hb (modes i)) (T (state hb (modes j)))) h

omit [DecidableEq ι] in
theorem corner_state_outside {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (M : Matrix ι ι ℂ) (k : ℕ) (hk : ∀ i, modes i ≠ k) :
    corner hb modes M (state hb k) = 0 := by
  simp [corner_apply, state_inner, hk]

theorem corner_mul_matrixUnit {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M : Matrix ι ι ℂ) (k l : ι) :
    corner hb modes M * matrixUnit hb (modes k) (modes l) =
      ∑ i, M i k • matrixUnit hb (modes i) (modes l) := by
  apply ContinuousLinearMap.ext
  intro F
  change corner hb modes M (matrixUnit hb (modes k) (modes l) F) = _
  simp only [matrixUnit_apply, map_smul, corner_state hb modes hinj, sum_apply,
    smul_apply, Finset.smul_sum, smul_smul, mul_comm]

theorem corner_mul {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M N : Matrix ι ι ℂ) :
    corner hb modes (M * N) = corner hb modes M * corner hb modes N := by
  apply end_ext hb
  intro n
  by_cases hn : ∃ j, modes j = n
  · obtain ⟨j, rfl⟩ := hn
    simp only [mul_apply_eq_comp, corner_state hb modes hinj, map_sum, map_smul,
      Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · have hout : ∀ i, modes i ≠ n := fun i hi => hn ⟨i, hi⟩
    rw [corner_state_outside hb modes (M * N) n hout, mul_apply_eq_comp,
      corner_state_outside hb modes N n hout, map_zero]

omit [DecidableEq ι] in
theorem corner_adjoint {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (M : Matrix ι ι ℂ) :
    (corner hb modes M).adjoint = corner hb modes M.conjTranspose := by
  simp only [corner_def, map_sum, map_smulₛₗ, matrixUnit_adjoint,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

def projection {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) : End := corner hb modes 1

theorem projection_apply {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) (F : ComplexL2) :
    projection hb modes F = ∑ i, inner ℂ (state hb (modes i)) F • state hb (modes i) := by
  simp [projection, corner_apply, Matrix.one_apply]

@[simp] theorem projection_state {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (i : ι) :
    projection hb modes (state hb (modes i)) = state hb (modes i) := by
  simp [projection, corner_state hb modes hinj, Matrix.one_apply]

@[simp] theorem projection_mul {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M : Matrix ι ι ℂ) :
    projection hb modes * corner hb modes M = corner hb modes M := by
  rw [projection, ← corner_mul hb modes hinj, one_mul]

@[simp] theorem mul_projection {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M : Matrix ι ι ℂ) :
    corner hb modes M * projection hb modes = corner hb modes M := by
  rw [projection, ← corner_mul hb modes hinj, mul_one]

@[simp] theorem projection_sq {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) :
    projection hb modes * projection hb modes = projection hb modes :=
  projection_mul hb modes hinj 1

@[simp] theorem projection_adjoint {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) :
    (projection hb modes).adjoint = projection hb modes := by
  simp [projection, corner_adjoint]

def sourceSpace {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) : Submodule ℂ ComplexL2 :=
  Submodule.span ℂ (Set.range (fun i => state hb (modes i)))

theorem projection_mem {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) (F : ComplexL2) :
    projection hb modes F ∈ sourceSpace hb modes := by
  rw [projection_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem projection_eq_self_iff {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (F : ComplexL2) :
    projection hb modes F = F ↔ F ∈ sourceSpace hb modes := by
  constructor
  · intro h
    rw [← h]
    exact projection_mem hb modes F
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨i, rfl⟩
        exact projection_state hb modes hinj i
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [map_smul, hx]

def entries {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) (T : End) : Matrix ι ι ℂ :=
  fun i j => inner ℂ (state hb (modes i)) (T (state hb (modes j)))

@[simp] theorem entries_corner {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M : Matrix ι ι ℂ) :
    entries hb modes (corner hb modes M) = M := by
  ext i j
  exact corner_entry hb modes hinj M i j

/-- Every operator compressed to the selected Hermite space has these matrix entries. -/
theorem corner_entries {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) (T : End) :
    corner hb modes (entries hb modes T) = projection hb modes * T * projection hb modes := by
  apply ContinuousLinearMap.ext
  intro F
  change corner hb modes (entries hb modes T) F =
    projection hb modes (T (projection hb modes F))
  rw [projection_apply hb modes F, map_sum]
  simp only [map_smul, map_sum, projection_apply, Finset.smul_sum, smul_smul,
    corner_apply, entries]
  calc
    _ = ∑ j, ∑ i,
        (inner ℂ (state hb (modes i)) (T (state hb (modes j))) *
          inner ℂ (state hb (modes j)) F) • state hb (modes i) := Finset.sum_comm
    _ = _ := by simp only [mul_comm]

theorem mem_range_corner_iff {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (T : End) :
    T ∈ LinearMap.range (corner hb modes) ↔ projection hb modes * T * projection hb modes = T := by
  constructor
  · rintro ⟨M, rfl⟩
    rw [projection_mul hb modes hinj, mul_projection hb modes hinj]
  · intro h
    exact ⟨entries hb modes T, (corner_entries hb modes T).trans h⟩

def control {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) (M : Matrix ι ι ℂ) : End :=
  1 - projection hb modes + corner hb modes M

@[simp] theorem control_one {b : ℝ} (hb : 0 < b) (modes : ι → ℕ) :
    control hb modes 1 = 1 := by simp [control, projection]

theorem control_mul {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M N : Matrix ι ι ℂ) :
    control hb modes (M * N) = control hb modes M * control hb modes N := by
  simp only [control, corner_mul hb modes hinj, mul_add, add_mul, mul_sub, sub_mul,
    one_mul, mul_one, projection_sq hb modes hinj, projection_mul hb modes hinj,
    mul_projection hb modes hinj]
  abel

theorem control_adjoint {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (M : Matrix ι ι ℂ) :
    (control hb modes M).adjoint = control hb modes M.conjTranspose := by
  simp [control, corner_adjoint, ContinuousLinearMap.adjoint_one]

theorem control_mem_unitary {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M : Matrix ι ι ℂ)
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) : control hb modes M ∈ unitary End := by
  rcases hM with ⟨hl, hr⟩
  constructor
  · change (control hb modes M).adjoint * control hb modes M = 1
    rw [control_adjoint, ← control_mul hb modes hinj]
    exact (congrArg (control hb modes) hl).trans (control_one hb modes)
  · change control hb modes M * (control hb modes M).adjoint = 1
    rw [control_adjoint, ← control_mul hb modes hinj]
    exact (congrArg (control hb modes) hr).trans (control_one hb modes)

theorem control_fixed_complement {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (M : Matrix ι ι ℂ) (F : ComplexL2)
    (hF : projection hb modes F = 0) : control hb modes M F = F := by
  have hcorner : corner hb modes M F = 0 := by
    have h := congrArg (fun T : End => T F) (mul_projection hb modes hinj M)
    simpa [mul_apply_eq_comp, hF] using h.symm
  simp [control, hF, hcorner]

theorem control_conjugation {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (hinj : Function.Injective modes) (U X : Matrix ι ι ℂ) :
    control hb modes U * corner hb modes X * (control hb modes U).adjoint =
      corner hb modes (U * X * U.conjTranspose) := by
  rw [control_adjoint]
  simp only [control, add_mul, sub_mul, mul_add, mul_sub, one_mul, mul_one,
    projection_mul hb modes hinj, mul_projection hb modes hinj, sub_self,
    zero_add, ← corner_mul hb modes hinj]

omit [DecidableEq ι] in
theorem corner_mem_ladder {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (M : Matrix ι ι ℂ) : corner hb modes M ∈ ladderOperationAlgebra hb := by
  rw [corner_def]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  exact (ladderOperationAlgebra hb).smul_mem (matrixUnit_mem_ladder hb _ _) _

theorem control_mem_ladder {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)
    (M : Matrix ι ι ℂ) : control hb modes M ∈ ladderOperationAlgebra hb := by
  exact add_mem (sub_mem (one_mem _) (corner_mem_ladder hb modes 1))
    (corner_mem_ladder hb modes M)

end GeneratedFoundations.Operations.FiniteHermiteCorner
