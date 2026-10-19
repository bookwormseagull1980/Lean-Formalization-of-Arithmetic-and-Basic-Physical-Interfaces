module

public import GeneratedFoundations.Geometry.SourceSpinorSpectralCore
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Multiplicities of the differentiated source spinor

The trace is computed in the original two-component Haar metric. Together
with the explicit polynomial splitting, it determines both multiplicities
without inserting a spinor spectrum as initial data.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceSpinorSpectralCore

namespace GeneratedFoundations.Geometry.SourceSpinorMultiplicity

attribute [local irreducible] kineticBasis

def componentBasis (m : ℕ) :
    OrthonormalBasis (Σ _ : Fin 2, Fin (m + 1)) ℂ (SpinorBlock m) :=
  Pi.orthonormalBasis (fun _ : Fin 2 => sourceBasis m)

theorem component_diagonal_cancel (m : ℕ) (j : Fin (m + 1)) :
    inner ℂ (PiLp.single 2 0 (sourceBasis m j))
        (kineticBlock m (PiLp.single 2 0 (sourceBasis m j))) +
      inner ℂ (PiLp.single 2 1 (sourceBasis m j))
        (kineticBlock m (PiLp.single 2 1 (sourceBasis m j))) = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, PiLp.single_apply, inner_smul_right]

theorem kinetic_trace (m : ℕ) :
    LinearMap.trace ℂ (SpinorBlock m) (kineticBlock m) = 0 := by
  rw [LinearMap.trace_eq_sum_inner _ (componentBasis m)]
  simp only [componentBasis, Pi.orthonormalBasis_apply, Fintype.sum_sigma, Fin.sum_univ_two]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ => component_diagonal_cancel m j

theorem sum_kineticEigenvalue (m : ℕ) :
    ∑ j, kineticEigenvalue m j = 0 := by
  have h := (kineticBlock_symmetric m).re_trace_eq_sum_eigenvalues
    (spinorBlock_finrank m)
  change RCLike.re (LinearMap.trace ℂ (SpinorBlock m) (kineticBlock m)) =
    ∑ j, kineticEigenvalue m j at h
  rw [← h, kinetic_trace]
  rfl

def plusMultiplicity (m : ℕ) : ℕ :=
  Fintype.card {j : Fin (2 * (m + 1)) // kineticEigenvalue m j = (m : ℝ)}

def minusMultiplicity (m : ℕ) : ℕ :=
  Fintype.card {j : Fin (2 * (m + 1)) // kineticEigenvalue m j = -((m : ℝ) + 2)}

private theorem count_as_sum (m : ℕ) (c : ℝ) :
    (Fintype.card {j : Fin (2 * (m + 1)) // kineticEigenvalue m j = c} : ℝ) =
      ∑ j : Fin (2 * (m + 1)), if kineticEigenvalue m j = c then 1 else 0 := by
  classical
  simp [Fintype.card_subtype, Finset.sum_boole]

theorem branch_count_sum (m : ℕ) :
    plusMultiplicity m + minusMultiplicity m = 2 * (m + 1) := by
  classical
  have hpoint (j : Fin (2 * (m + 1))) :
      (if kineticEigenvalue m j = (m : ℝ) then (1 : ℝ) else 0) +
        (if kineticEigenvalue m j = -((m : ℝ) + 2) then 1 else 0) = 1 := by
    rcases kineticEigenvalue_branches m j with hp | hn
    · have hn : kineticEigenvalue m j ≠ -((m : ℝ) + 2) := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      rw [ite_eq_left hp, ite_eq_right hn]
      norm_num
    · have hp : kineticEigenvalue m j ≠ (m : ℝ) := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      rw [ite_eq_right hp, ite_eq_left hn]
      norm_num
  have hs := congrArg (fun f : Fin (2 * (m + 1)) → ℝ => ∑ j, f j) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hs
  rw [← count_as_sum m (m : ℝ), ← count_as_sum m (-((m : ℝ) + 2))] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  apply Nat.cast_injective (R := ℝ)
  simpa only [plusMultiplicity, minusMultiplicity, Nat.cast_add] using hs

theorem branch_weighted_sum (m : ℕ) :
    (m : ℝ) * plusMultiplicity m -
      ((m : ℝ) + 2) * minusMultiplicity m = 0 := by
  classical
  have hpoint (j : Fin (2 * (m + 1))) : kineticEigenvalue m j =
      (m : ℝ) * (if kineticEigenvalue m j = (m : ℝ) then 1 else 0) -
        ((m : ℝ) + 2) *
          (if kineticEigenvalue m j = -((m : ℝ) + 2) then 1 else 0) := by
    rcases kineticEigenvalue_branches m j with hp | hn
    · have hn : kineticEigenvalue m j ≠ -((m : ℝ) + 2) := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      rw [ite_eq_left hp, ite_eq_right hn, hp]
      ring
    · have hp : kineticEigenvalue m j ≠ (m : ℝ) := by
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      rw [ite_eq_right hp, ite_eq_left hn, hn]
      ring
  have hs := congrArg (fun f : Fin (2 * (m + 1)) → ℝ => ∑ j, f j) (funext hpoint)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [← count_as_sum m (m : ℝ), ← count_as_sum m (-((m : ℝ) + 2)),
    sum_kineticEigenvalue] at hs
  exact hs.symm

/-- The two dimensions are forced by the differentiated operator and its
trace. The lower summand is absent in degree zero. -/
theorem branch_multiplicities (m : ℕ) :
    plusMultiplicity m = m + 2 ∧ minusMultiplicity m = m := by
  have hc : (plusMultiplicity m : ℝ) + minusMultiplicity m =
      2 * ((m : ℝ) + 1) := by exact_mod_cast branch_count_sum m
  have ht := branch_weighted_sum m
  have hmul : (2 * (m : ℝ) + 2) * ((minusMultiplicity m : ℝ) - m) = 0 := by
    linear_combination (m : ℝ) * hc - ht
  have hn : (minusMultiplicity m : ℝ) = m :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (by positivity))
  have hn' : minusMultiplicity m = m := by exact_mod_cast hn
  exact ⟨by have := branch_count_sum m; omega, hn'⟩

theorem eigenspace_dimension (m : ℕ) (c : ℝ) :
    Module.finrank ℂ (Module.End.eigenspace (kineticBlock m) (c : ℂ)) =
      Fintype.card {j : Fin (2 * (m + 1)) // kineticEigenvalue m j = c} := by
  have h := (kineticBlock_symmetric m).card_filter_eigenvalues_eq
    (spinorBlock_finrank m) (c : ℂ)
  change (Finset.univ.filter
    (fun j => (kineticEigenvalue m j : ℂ) = (c : ℂ))).card = _ at h
  simpa only [Complex.ofReal_inj, Fintype.card_subtype] using h.symm

theorem positive_eigenspace_finrank (m : ℕ) :
    Module.finrank ℂ (Module.End.eigenspace (kineticBlock m) (m : ℂ)) = m + 2 := by
  simpa only [Complex.ofReal_natCast] using
    (eigenspace_dimension m (m : ℝ)).trans (branch_multiplicities m).1

theorem negative_eigenspace_finrank (m : ℕ) :
    Module.finrank ℂ
      (Module.End.eigenspace (kineticBlock m) ((-((m : ℝ) + 2) : ℝ) : ℂ)) = m := by
  rw [eigenspace_dimension]
  exact (branch_multiplicities m).2

end GeneratedFoundations.Geometry.SourceSpinorMultiplicity
