module

public import GeneratedFoundations.Operations.HermiteCompleteness
public import GeneratedFoundations.Operations.EigenbasisClosure

/-! The self-adjoint closure of the actual Gaussian oscillator

The operator starts with the differential number operator on the common
Schwartz core, with the order-neutral half-unit added. Its complete Hermite
basis is the family of generated Lebesgue functions. The real-eigenbasis
closure theorem is then applied to this actual partially defined operator.
This identifies the full domain of its self-adjoint closure and proves
uniqueness among all self-adjoint extensions of the differential operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap ComplexConjugate LinearPMap
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.GaussianAffineLadder
open GeneratedFoundations.Operations.HermiteFamily

namespace GeneratedFoundations.Operations.HermiteOscillator

def eigenvalue (n : ℕ) : ℝ := n + 1 / 2

def schwartzOperator (b : ℝ) : Core →L[ℂ] Core :=
  number b + (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ Core

theorem schwartzOperator_apply (b : ℝ) (f : Core) :
    schwartzOperator b f = number b f + (1 / 2 : ℂ) • f := rfl

/-- This is exactly the half-sum of the two actual differential orderings. -/
theorem schwartzOperator_eq_orderNeutral {b : ℝ} (hb : 0 < b) (f : Core) :
    schwartzOperator b f = (1 / 2 : ℂ) •
      (creation b (annihilation b f) + annihilation b (creation b f)) := by
  rw [schwartzOperator_apply, annihilation_creation hb]
  change number b f + (1 / 2 : ℂ) • f =
    (1 / 2 : ℂ) • (number b f + (number b f + f))
  ext x
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem schwartzOperator_symmetric (b : ℝ) (f g : Core) :
    inner ℂ (embedding (schwartzOperator b f)) (embedding g) =
      inner ℂ (embedding f) (embedding (schwartzOperator b g)) := by
  simp [schwartzOperator_apply, map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, number_symmetric, map_ofNat]

theorem schwartzOperator_hermite {b : ℝ} (hb : 0 < b) (n : ℕ) :
    schwartzOperator b (hermite hb n) = (eigenvalue n : ℂ) • hermite hb n := by
  rw [schwartzOperator_apply, number_hermite, ← add_smul]
  congr 1
  simp [eigenvalue]

/-- The initial operator retains the actual Schwartz image as its domain. -/
def operator (b : ℝ) : ComplexL2 →ₗ.[ℂ] ComplexL2 := liftCore (schwartzOperator b)

theorem operator_domain (b : ℝ) : (operator b).domain = coreDomain := rfl

theorem operator_dense (b : ℝ) : Dense ((operator b).domain : Set ComplexL2) :=
  liftCore_dense (schwartzOperator b)

theorem operator_symmetric (b : ℝ) : (operator b).IsFormalAdjoint (operator b) := by
  intro x y
  obtain ⟨f, rfl⟩ := coreEquiv.surjective x
  obtain ⟨g, rfl⟩ := coreEquiv.surjective y
  simpa only [operator, liftCore_coreEquiv, coreEquiv_coe] using
    schwartzOperator_symmetric b f g

theorem basis_mem_domain {b : ℝ} (hb : 0 < b) (n : ℕ) :
    HermiteCompleteness.basis hb n ∈ (operator b).domain := by
  rw [HermiteCompleteness.basis_apply]
  exact state_mem_core hb n

theorem operator_basis {b : ℝ} (hb : 0 < b) (n : ℕ) :
    operator b ⟨HermiteCompleteness.basis hb n, basis_mem_domain hb n⟩ =
      (eigenvalue n : ℂ) • HermiteCompleteness.basis hb n := by
  have h : (⟨HermiteCompleteness.basis hb n, basis_mem_domain hb n⟩ : (operator b).domain) =
      coreEquiv (hermite hb n) := by
    apply Subtype.ext
    exact HermiteCompleteness.basis_apply hb n
  rw [h]
  change liftCore (schwartzOperator b) (coreEquiv (hermite hb n)) = _
  rw [liftCore_coreEquiv, schwartzOperator_hermite, map_smul,
    HermiteCompleteness.basis_apply]
  rfl

/-- The Hamiltonian is defined as the graph closure of the source operator. -/
def hamiltonian (b : ℝ) : ComplexL2 →ₗ.[ℂ] ComplexL2 := (operator b).closure

theorem hamiltonian_eq_adjoint {b : ℝ} (hb : 0 < b) :
    hamiltonian b = (operator b).adjoint :=
  EigenbasisClosure.closure_eq_adjoint (HermiteCompleteness.basis hb) (operator b)
    eigenvalue (basis_mem_domain hb) (operator_basis hb) (operator_symmetric b)

theorem hamiltonian_selfAdjoint {b : ℝ} (hb : 0 < b) : IsSelfAdjoint (hamiltonian b) :=
  EigenbasisClosure.closure_selfAdjoint (HermiteCompleteness.basis hb) (operator b)
    eigenvalue (basis_mem_domain hb) (operator_basis hb) (operator_symmetric b)

theorem operator_le_hamiltonian {b : ℝ} (hb : 0 < b) : operator b ≤ hamiltonian b := by
  rw [hamiltonian_eq_adjoint hb]
  exact EigenbasisClosure.le_adjoint (HermiteCompleteness.basis hb) (operator b)
    (basis_mem_domain hb) (operator_symmetric b)

theorem state_mem_hamiltonian_domain {b : ℝ} (hb : 0 < b) (n : ℕ) :
    HermiteFamily.state hb n ∈ (hamiltonian b).domain :=
  (operator_le_hamiltonian hb).1 (state_mem_core hb n)

theorem hamiltonian_state {b : ℝ} (hb : 0 < b) (n : ℕ) :
    hamiltonian b ⟨HermiteFamily.state hb n, state_mem_hamiltonian_domain hb n⟩ =
      (n + 1 / 2 : ℂ) • HermiteFamily.state hb n := by
  have h := (operator_le_hamiltonian hb).2
    (x := ⟨HermiteCompleteness.basis hb n, basis_mem_domain hb n⟩)
    (y := ⟨HermiteFamily.state hb n, state_mem_hamiltonian_domain hb n⟩)
    (HermiteCompleteness.basis_apply hb n)
  simpa [eigenvalue, HermiteCompleteness.basis_apply] using h.symm.trans (operator_basis hb n)

/-- Uniqueness quantifies over every self-adjoint extension in the original space. -/
theorem selfAdjoint_extension_unique {b : ℝ} (hb : 0 < b)
    (S : ComplexL2 →ₗ.[ℂ] ComplexL2) (hS : IsSelfAdjoint S) (hext : operator b ≤ S) :
    S = hamiltonian b :=
  EigenbasisClosure.selfAdjoint_extension_unique (HermiteCompleteness.basis hb) (operator b)
    eigenvalue (basis_mem_domain hb) (operator_basis hb) (operator_symmetric b) S hS hext

/-- The self-adjoint closure has exactly the weighted square-summable coefficient domain. -/
theorem hamiltonian_domain_iff {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    F ∈ (hamiltonian b).domain ↔
      Summable (fun n : ℕ => (n + 1 / 2 : ℝ) ^ 2 *
        ‖inner ℂ (HermiteFamily.state hb n) F‖ ^ 2) := by
  rw [hamiltonian_eq_adjoint hb]
  simpa only [eigenvalue, HermiteCompleteness.basis_apply] using
    EigenbasisClosure.adjoint_domain_iff_summable (HermiteCompleteness.basis hb) (operator b)
      eigenvalue (basis_mem_domain hb) (operator_basis hb) (operator_symmetric b) F

/-- Coefficients of the actual closed operator agree with its derived eigenvalues. -/
theorem hamiltonian_coefficients {b : ℝ} (hb : 0 < b) (F : (hamiltonian b).domain) (n : ℕ) :
    inner ℂ (HermiteFamily.state hb n) (hamiltonian b F) =
      (n + 1 / 2 : ℂ) * inner ℂ (HermiteFamily.state hb n) (F : ComplexL2) := by
  have h := hamiltonian_eq_adjoint hb
  have hmem : (F : ComplexL2) ∈ (operator b).adjoint.domain := by
    rw [← h]
    exact F.property
  have hval : hamiltonian b F = (operator b).adjoint ⟨F, hmem⟩ := by
    exact (LinearPMap.ext_iff.mp h).2 (x := (F : ComplexL2))
      (hf := F.property) (hg := hmem)
  rw [hval]
  simpa [eigenvalue, HermiteCompleteness.basis_apply] using
    EigenbasisClosure.adjoint_coefficients (HermiteCompleteness.basis hb) (operator b)
      eigenvalue (basis_mem_domain hb) (operator_basis hb) ⟨F, hmem⟩ n

end GeneratedFoundations.Operations.HermiteOscillator
