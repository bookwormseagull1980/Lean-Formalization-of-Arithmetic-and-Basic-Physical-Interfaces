module

public import GeneratedFoundations.Operations.FiniteHermiteCorner
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Exponentials on finite Hermite corners

The corner map preserves products but sends the matrix identity to the
source projection.  Adjoining the complementary scalar block gives a
unital algebra homomorphism and transports the exponential on the whole
Gaussian Hilbert space.  All resulting controls lie in the finite source
algebra and act as the identity on the complementary subspace.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix.Norms.Operator
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteFamily
open GeneratedFoundations.Operations.SourceSpinCorner (End)
open GeneratedFoundations.Operations.SourceMatrixUnits

namespace GeneratedFoundations.Operations.FiniteHermiteCornerExponential

open FiniteHermiteCorner

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {b : ℝ} (hb : 0 < b) (modes : ι → ℕ)

def complement : End := 1 - projection hb modes

@[simp] theorem complement_sq (hinj : Function.Injective modes) :
    complement hb modes * complement hb modes = complement hb modes := by
  simp [complement, sub_mul, mul_sub, projection_sq hb modes hinj]

@[simp] theorem complement_corner (hinj : Function.Injective modes)
    (M : Matrix ι ι ℂ) : complement hb modes * corner hb modes M = 0 := by
  simp [complement, sub_mul, projection_mul hb modes hinj]

@[simp] theorem corner_complement (hinj : Function.Injective modes)
    (M : Matrix ι ι ℂ) : corner hb modes M * complement hb modes = 0 := by
  simp [complement, mul_sub, mul_projection hb modes hinj]

/-- The complementary scalar and the selected finite matrix preserve the
ambient operator identity together. -/
def blockAlgebra (hinj : Function.Injective modes) :
    (ℂ × Matrix ι ι ℂ) →ₐ[ℂ] End where
  toFun p := p.1 • complement hb modes + corner hb modes p.2
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro F
    change (0 : ℂ) • (complement hb modes F) + corner hb modes 0 F = 0
    simp
  map_one' := by simp [complement, projection]
  map_add' p q := by
    apply ContinuousLinearMap.ext
    intro F
    change (p.1 + q.1) • complement hb modes F + corner hb modes (p.2 + q.2) F =
      (p.1 • complement hb modes F + corner hb modes p.2 F) +
        (q.1 • complement hb modes F + corner hb modes q.2 F)
    rw [add_smul, map_add]
    simp only [add_apply]
    abel
  map_mul' p q := by
    apply ContinuousLinearMap.ext
    intro F
    have hQQ : complement hb modes (complement hb modes F) = complement hb modes F :=
      congrArg (fun T : End => T F) (complement_sq hb modes hinj)
    have hQM : complement hb modes (corner hb modes q.2 F) = 0 :=
      congrArg (fun T : End => T F) (complement_corner hb modes hinj q.2)
    have hMQ : corner hb modes p.2 (complement hb modes F) = 0 :=
      congrArg (fun T : End => T F) (corner_complement hb modes hinj p.2)
    have hprod : corner hb modes (p.2 * q.2) F =
        corner hb modes p.2 (corner hb modes q.2 F) :=
      congrArg (fun T : End => T F) (corner_mul hb modes hinj p.2 q.2)
    change (p.1 * q.1) • complement hb modes F + corner hb modes (p.2 * q.2) F =
      p.1 • complement hb modes (q.1 • complement hb modes F + corner hb modes q.2 F) +
        corner hb modes p.2 (q.1 • complement hb modes F + corner hb modes q.2 F)
    simp only [map_add, map_smul, hQQ, hQM, hMQ, hprod, smul_zero,
      add_zero, zero_add, smul_smul]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_one, Prod.snd_one, smul_eq_mul, mul_one, map_smul]
    rw [← show projection hb modes = corner hb modes (1 : Matrix ι ι ℂ) from rfl]
    simp [complement, smul_sub]

set_option backward.isDefEq.respectTransparency false in
theorem exp_blocks (hinj : Function.Injective modes) (z : ℂ) (M : Matrix ι ι ℂ) :
    NormedSpace.exp (z • complement hb modes + corner hb modes M) =
      NormedSpace.exp z • complement hb modes + corner hb modes (NormedSpace.exp M) := by
  have h := NormedSpace.map_exp (blockAlgebra hb modes hinj)
    (blockAlgebra hb modes hinj).toLinearMap.continuous_of_finiteDimensional (z, M)
  simpa [blockAlgebra] using h.symm

/-- The exponential has a complementary identity term even though its
generator vanishes there. -/
theorem exp_corner (hinj : Function.Injective modes) (M : Matrix ι ι ℂ) :
    NormedSpace.exp (corner hb modes M) = control hb modes (NormedSpace.exp M) := by
  have h := exp_blocks hb modes hinj 0 M
  have hzero : (0 : ℂ) • complement hb modes + corner hb modes M = corner hb modes M := by
    apply ContinuousLinearMap.ext
    intro F
    change (0 : ℂ) • complement hb modes F + corner hb modes M F = corner hb modes M F
    simp
  rw [hzero] at h
  simpa [FiniteHermiteCorner.control, complement] using h

theorem exp_smul_corner (hinj : Function.Injective modes) (z : ℂ)
    (M : Matrix ι ι ℂ) :
    NormedSpace.exp (z • corner hb modes M) =
      control hb modes (NormedSpace.exp (z • M)) := by
  rw [← map_smul, exp_corner hb modes hinj]

theorem exp_corner_fixed_complement (hinj : Function.Injective modes)
    (M : Matrix ι ι ℂ) (F : ComplexL2) (hF : projection hb modes F = 0) :
    NormedSpace.exp (corner hb modes M) F = F := by
  rw [exp_corner hb modes hinj]
  exact control_fixed_complement hb modes hinj _ F hF

theorem exp_corner_state (hinj : Function.Injective modes)
    (M : Matrix ι ι ℂ) (j : ι) :
    NormedSpace.exp (corner hb modes M) (state hb (modes j)) =
      ∑ i, NormedSpace.exp M i j • state hb (modes i) := by
  rw [exp_corner hb modes hinj]
  change state hb (modes j) - projection hb modes (state hb (modes j)) +
    corner hb modes (NormedSpace.exp M) (state hb (modes j)) = _
  rw [projection_state hb modes hinj, sub_self, zero_add]
  exact corner_state hb modes hinj (NormedSpace.exp M) j

omit [DecidableEq ι] in
theorem exp_smul_corner_mem_unitary (M : Matrix ι ι ℂ)
    (hM : M.conjTranspose = M) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • corner hb modes M) ∈ unitary End := by
  let : NormedAlgebra ℚ End := .restrictScalars ℚ ℂ End
  have hcorner : star (corner hb modes M) = corner hb modes M := by
    change (corner hb modes M).adjoint = corner hb modes M
    rw [corner_adjoint, hM]
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  apply skewAdjoint.mem_iff.mpr
  simp [star_smul, hcorner]
  exact neg_smul (Complex.I * (t : ℂ)) (corner hb modes M)

omit [DecidableEq ι] in
theorem corner_mem_finiteSource (M : Matrix ι ι ℂ) :
    corner hb modes M ∈ finiteSourceAlgebra hb := by
  rw [corner_def]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  exact (finiteSourceAlgebra hb).smul_mem (matrixUnit_mem hb _ _) _

theorem control_mem_finiteSource (M : Matrix ι ι ℂ) :
    control hb modes M ∈ finiteSourceAlgebra hb :=
  add_mem (sub_mem (one_mem _) (corner_mem_finiteSource hb modes 1))
    (corner_mem_finiteSource hb modes M)

/-- Membership uses the finite matrix formula, without assuming that the
algebra generated by source words is closed under infinite sums. -/
theorem exp_corner_mem_finiteSource (hinj : Function.Injective modes)
    (M : Matrix ι ι ℂ) :
    NormedSpace.exp (corner hb modes M) ∈ finiteSourceAlgebra hb := by
  rw [exp_corner hb modes hinj]
  exact control_mem_finiteSource hb modes _

theorem exp_smul_corner_mem_finiteSource (hinj : Function.Injective modes)
    (z : ℂ) (M : Matrix ι ι ℂ) :
    NormedSpace.exp (z • corner hb modes M) ∈ finiteSourceAlgebra hb := by
  rw [exp_smul_corner hb modes hinj]
  exact control_mem_finiteSource hb modes _

theorem exp_smul_corner_mem_ladder (hinj : Function.Injective modes)
    (z : ℂ) (M : Matrix ι ι ℂ) :
    NormedSpace.exp (z • corner hb modes M) ∈ ladderOperationAlgebra hb :=
  finiteSourceAlgebra_le_ladder hb
    (exp_smul_corner_mem_finiteSource hb modes hinj z M)

end GeneratedFoundations.Operations.FiniteHermiteCornerExponential
