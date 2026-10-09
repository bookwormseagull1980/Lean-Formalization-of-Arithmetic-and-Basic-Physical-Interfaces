module

public import GeneratedFoundations.Operations.SourceSpinCornerGroup
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Controlled source operations and the local Gaussian cycle

Finite matrices act on the actual Gaussian corner and trivially on its
orthogonal complement. The exponential identity is proved using a unital
algebra homomorphism from the product of the complementary scalar algebra
and the matrix algebra. This retains the essential distinction between the
global oscillator cycle `-I` and the controlled cycle `I - 2P`.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix.Norms.Operator
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.GaussianAffineLadder
  (embedding coreEquiv liftCore_coreEquiv)
open GeneratedFoundations.Operations.HermiteFamily
open GeneratedFoundations.Operations.HermiteCompleteness
open GeneratedFoundations.Operations.HermiteOscillator
open GeneratedFoundations.Operations.HermitePhaseFlow
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup

namespace GeneratedFoundations.Operations.SourceSpinCornerFlow

def complement {b : ℝ} (hb : 0 < b) : End := 1 - projection hb

@[simp] theorem complement_sq {b : ℝ} (hb : 0 < b) :
    complement hb * complement hb = complement hb := by
  simp [complement, sub_mul, mul_sub]

@[simp] theorem complement_corner {b : ℝ} (hb : 0 < b) (M : Mat2) :
    complement hb * corner hb M = 0 := by simp [complement, sub_mul]

@[simp] theorem corner_complement {b : ℝ} (hb : 0 < b) (M : Mat2) :
    corner hb M * complement hb = 0 := by simp [complement, mul_sub]

/-- The complementary scalar and finite matrix blocks together preserve the ambient unit. -/
def blockAlgebra {b : ℝ} (hb : 0 < b) : (ℂ × Mat2) →ₐ[ℂ] End where
  toFun p := p.1 • complement hb + corner hb p.2
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro F
    change (0 : ℂ) • (complement hb F) + corner hb 0 F = 0
    simp
  map_one' := by simp [complement, projection]
  map_add' p q := by
    apply ContinuousLinearMap.ext
    intro F
    change (p.1 + q.1) • complement hb F + corner hb (p.2 + q.2) F =
      (p.1 • complement hb F + corner hb p.2 F) +
        (q.1 • complement hb F + corner hb q.2 F)
    rw [add_smul, map_add]
    simp only [add_apply]
    abel
  map_mul' p q := by
    apply ContinuousLinearMap.ext
    intro F
    have hQQ : complement hb (complement hb F) = complement hb F :=
      congrArg (fun T : End => T F) (complement_sq hb)
    have hQM : complement hb (corner hb q.2 F) = 0 :=
      congrArg (fun T : End => T F) (complement_corner hb q.2)
    have hMQ : corner hb p.2 (complement hb F) = 0 :=
      congrArg (fun T : End => T F) (corner_complement hb p.2)
    have hprod : corner hb (p.2 * q.2) F = corner hb p.2 (corner hb q.2 F) :=
      congrArg (fun T : End => T F) (corner_mul hb p.2 q.2)
    change (p.1 * q.1) • complement hb F + corner hb (p.2 * q.2) F =
      p.1 • complement hb (q.1 • complement hb F + corner hb q.2 F) +
        corner hb p.2 (q.1 • complement hb F + corner hb q.2 F)
    simp only [map_add, map_smul, hQQ, hQM, hMQ, hprod, smul_zero,
      add_zero, zero_add, smul_smul]
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_one, Prod.snd_one, smul_eq_mul, mul_one, map_smul]
    rw [← show projection hb = corner hb (1 : Mat2) from rfl]
    simp [complement, smul_sub]

set_option backward.isDefEq.respectTransparency false in
/-- The nonunital corner has the necessary complementary identity term in its exponential. -/
theorem exp_corner {b : ℝ} (hb : 0 < b) (M : Mat2) :
    NormedSpace.exp (corner hb M) = control hb (NormedSpace.exp M) := by
  have h := NormedSpace.map_exp (blockAlgebra hb)
    (blockAlgebra hb).toLinearMap.continuous_of_finiteDimensional ((0 : ℂ), M)
  have hz : blockAlgebra hb ((0 : ℂ), M) = corner hb M := by
    apply ContinuousLinearMap.ext
    intro F
    change (0 : ℂ) • complement hb F + corner hb M F = corner hb M F
    simp
  rw [hz] at h
  simpa [blockAlgebra, complement, SourceSpinCorner.control] using h.symm

def sourceRepresentation {b : ℝ} (hb : 0 < b) : SU2 →* unitary End where
  toFun U := ⟨control hb U.val,
    control_mem_unitary hb U.val (Matrix.mem_specialUnitaryGroup_iff.mp U.property).1⟩
  map_one' := Subtype.ext (control_one hb)
  map_mul' U V := Subtype.ext (control_mul hb U.val V.val)

theorem sourceRepresentation_injective {b : ℝ} (hb : 0 < b) :
    Function.Injective (sourceRepresentation hb) := by
  intro U V h
  apply Subtype.ext
  exact control_injective hb (congrArg Subtype.val h)

theorem exp_spin3_source {b : ℝ} (hb : 0 < b) (t : ℝ) :
    NormedSpace.exp ((Complex.I * t) • spin3 hb) = control hb (zRotation t) := by
  rw [spin3_eq_corner, ← map_smul, exp_corner, exp_spin3]

theorem exp_spin2_source {b : ℝ} (hb : 0 < b) (t : ℝ) :
    NormedSpace.exp ((Complex.I * t) • spin2 hb) = control hb (yRotation t) := by
  rw [spin2_eq_corner, ← map_smul, exp_corner, exp_spin2]

/-- Every controlled special unitary is a finite product of actual source-operator exponentials. -/
theorem source_exponentials_generate_all {b : ℝ} (hb : 0 < b) (U : SU2) :
    ∃ a t c : ℝ,
      (sourceRepresentation hb U : End) =
        NormedSpace.exp ((Complex.I * a) • spin3 hb) *
        NormedSpace.exp ((Complex.I * t) • spin2 hb) *
        NormedSpace.exp ((Complex.I * c) • spin3 hb) := by
  obtain ⟨a, t, c, h⟩ := euler_factorization U.val U.property
  refine ⟨a, t, c, ?_⟩
  change control hb U.val = _
  rw [h, control_mul, control_mul, exp_spin3_source, exp_spin2_source, exp_spin3_source]

def hamiltonianMatrix : Mat2 := !![1 / 2, 0; 0, 3 / 2]

def localHamiltonian {b : ℝ} (hb : 0 < b) : End := corner hb hamiltonianMatrix

theorem localHamiltonian_eq {b : ℝ} (hb : 0 < b) :
    localHamiltonian hb = projection hb + spin3 hb := by
  rw [localHamiltonian, projection, spin3_eq_corner, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hamiltonianMatrix, spinMatrix3]

theorem projected_mem_hamiltonian_domain {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    projection hb F ∈ (hamiltonian b).domain := by
  apply (operator_le_hamiltonian hb).1
  exact ⟨projectedCore hb F, embedding_projectedCore hb F⟩

/-- The finite generator is the compression of the already proved self-adjoint differential closure. -/
theorem hamiltonian_projection {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    hamiltonian b ⟨projection hb F, projected_mem_hamiltonian_domain hb F⟩ =
      localHamiltonian hb F := by
  have h := (operator_le_hamiltonian hb).2
    (x := coreEquiv (projectedCore hb F))
    (y := ⟨projection hb F, projected_mem_hamiltonian_domain hb F⟩)
    (embedding_projectedCore hb F)
  rw [← h]
  change GaussianAffineLadder.liftCore (schwartzOperator b)
    (coreEquiv (projectedCore hb F)) = _
  rw [liftCore_coreEquiv]
  simp only [projectedCore, map_add, map_smul, schwartzOperator_hermite,
    embedding_hermite, state_zero, state_one]
  norm_num [localHamiltonian, corner_apply, hamiltonianMatrix, eigenvalue]
  module

theorem flow_state {b : ℝ} (hb : 0 < b) (t : ℝ) (n : ℕ) :
    flow hb t (state hb n) = phase t n • state hb n := by
  apply eq_of_coefficients_eq hb
  intro m
  rw [flow_inner, inner_smul_right]
  by_cases h : m = n
  · subst n
    rfl
  · simp [state_inner_eq_zero hb h]

def cycleMatrix (t : ℝ) : Mat2 := Matrix.diagonal ![phase t 0, phase t 1]

theorem exp_hamiltonianMatrix (t : ℝ) :
    NormedSpace.exp ((-Complex.I * t) • hamiltonianMatrix) = cycleMatrix t := by
  have h : (-Complex.I * (t : ℂ)) • hamiltonianMatrix =
      Matrix.diagonal ![-Complex.I * t / 2, -Complex.I * t * (3 / 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hamiltonianMatrix]
    ring
  rw [h, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleMatrix, phase, eigenvalue, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  all_goals
    congr 1
    ring

def localFlow {b : ℝ} (hb : 0 < b) (t : ℝ) : End :=
  NormedSpace.exp ((-Complex.I * t) • localHamiltonian hb)

theorem localFlow_control {b : ℝ} (hb : 0 < b) (t : ℝ) :
    localFlow hb t = control hb (cycleMatrix t) := by
  rw [localFlow, localHamiltonian, ← map_smul, exp_corner, exp_hamiltonianMatrix]

/-- Exact equality on the original Hilbert space, including its infinite-dimensional complement. -/
theorem localFlow_formula {b : ℝ} (hb : 0 < b) (t : ℝ) (F : ComplexL2) :
    localFlow hb t F = F - projection hb F + flow hb t (projection hb F) := by
  rw [localFlow_control]
  have h0 : flow hb t (groundState hb) = phase t 0 • groundState hb := by
    simpa only [state_zero] using flow_state hb t 0
  have h1 : flow hb t (firstState hb) = phase t 1 • firstState hb := by
    simpa only [state_one] using flow_state hb t 1
  simp [SourceSpinCorner.control, corner_apply, cycleMatrix, projection_apply, h0, h1, smul_smul,
    mul_comm]

theorem cycleMatrix_mem_unitary (t : ℝ) :
    cycleMatrix t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Complex.conj_mul', phase_norm]

theorem cycleMatrix_phase_spin (t : ℝ) :
    cycleMatrix t = Complex.exp (-Complex.I * t) • zRotation (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleMatrix, zRotation, phase, eigenvalue, ← Complex.exp_add]
  all_goals
    congr 1
    ring

/-- The scalar phase and the spin rotation come from the same closed Gaussian generator. -/
theorem source_phase_spin {b : ℝ} (hb : 0 < b) (t : ℝ) (F : ComplexL2)
    (hF : F ∈ sourceSpace hb) :
    flow hb t F = Complex.exp (-Complex.I * t) • control hb (zRotation (-t)) F := by
  have hp := (projection_eq_self_iff hb F).mpr hF
  have h := localFlow_formula hb t F
  rw [hp, sub_self, zero_add, localFlow_control, cycleMatrix_phase_spin] at h
  rw [← h]
  simp [SourceSpinCorner.control, hp, map_smul]

def localUnitary {b : ℝ} (hb : 0 < b) (t : ℝ) : unitary End :=
  ⟨localFlow hb t, by
    rw [localFlow_control]
    exact control_mem_unitary hb _ (cycleMatrix_mem_unitary t)⟩

theorem localFlow_add {b : ℝ} (hb : 0 < b) (s t : ℝ) :
    localFlow hb (s + t) = localFlow hb s * localFlow hb t := by
  rw [localFlow_control, localFlow_control, localFlow_control, ← control_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleMatrix, Matrix.mul_apply, Fin.sum_univ_two, phase_add]

theorem localFlow_two_pi {b : ℝ} (hb : 0 < b) :
    localFlow hb (2 * Real.pi) = 1 - (2 : ℂ) • projection hb := by
  rw [localFlow_control]
  have h : cycleMatrix (2 * Real.pi) = -(1 : Mat2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycleMatrix, phase_two_pi]
  rw [h]
  simp only [SourceSpinCorner.control, map_neg]
  rw [← show projection hb = corner hb (1 : Mat2) from rfl]
  module

theorem localFlow_two_pi_control {b : ℝ} (hb : 0 < b) :
    localFlow hb (2 * Real.pi) = control hb (-(1 : Mat2)) := by
  rw [localFlow_control]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycleMatrix, phase_two_pi]

theorem localFlow_four_pi {b : ℝ} (hb : 0 < b) :
    localFlow hb (4 * Real.pi) = 1 := by
  rw [show 4 * Real.pi = 2 * Real.pi + 2 * Real.pi by ring,
    localFlow_add, localFlow_two_pi_control, ← control_mul]
  simp [control_one]

theorem localFlow_two_pi_source {b : ℝ} (hb : 0 < b) (F : ComplexL2)
    (hF : F ∈ sourceSpace hb) : localFlow hb (2 * Real.pi) F = -F := by
  rw [localFlow_two_pi]
  simp [(projection_eq_self_iff hb F).mpr hF]
  module

/-- The same-source bypass is fixed by the local cycle, unlike the global oscillator cycle. -/
theorem localFlow_two_pi_bypass {b : ℝ} (hb : 0 < b) :
    localFlow hb (2 * Real.pi) (state hb 2) = state hb 2 := by
  rw [localFlow_two_pi]
  simp [projection_state_two]

theorem local_centre_commutes {b : ℝ} (hb : 0 < b) (M : Mat2) :
    localFlow hb (2 * Real.pi) * control hb M =
      control hb M * localFlow hb (2 * Real.pi) := by
  rw [localFlow_two_pi_control, ← control_mul, ← control_mul]
  congr 1
  simp

theorem cycle_determinant (t : ℝ) :
    Matrix.det (cycleMatrix t) = Complex.exp (-2 * Complex.I * t) := by
  simp [cycleMatrix, phase, eigenvalue, ← Complex.exp_add]
  congr 1
  ring

end GeneratedFoundations.Operations.SourceSpinCornerFlow
