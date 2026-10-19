module

public import GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum
public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Full bounded resolvents of the differentiated source spinor

The two differentiated branches escape every bounded spectral interval.
Their coefficient inverse is therefore uniformly bounded away from the
actual eigenvalues. The inverse acts on the original Haar field space and
takes values in the full closed differential domain. Both inverse
identities exclude additional continuous or residual spectral points.
-/

@[expose] public section

noncomputable section

open scoped BigOperators LinearPMap lp
open GeneratedFoundations.Geometry.SourceSpinorSpectralCore
open GeneratedFoundations.Geometry.SourceSpinorHaarBlock
open GeneratedFoundations.Geometry.SourceSpinorHilbertSum
open GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceSpinorResolvent

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

def inverseCoefficient (z : ℂ) (m : ℕ) (j : Fin (2 * (m + 1))) : ℂ :=
  (((kineticEigenvalue m j + 3 / 2 : ℝ) : ℂ) - z)⁻¹

theorem degree_le_abs_eigenvalue (m : ℕ) (j : Fin (2 * (m + 1))) :
    (m : ℝ) - 1 / 2 ≤ |kineticEigenvalue m j + 3 / 2| := by
  rcases kineticEigenvalue_branches m j with hp | hn
  · rw [hp]
    exact (by linarith : (m : ℝ) - 1 / 2 ≤ (m : ℝ) + 3 / 2).trans (le_abs_self _)
  · rw [hn]
    exact (by linarith : (m : ℝ) - 1 / 2 ≤ -(-((m : ℝ) + 2) + 3 / 2)).trans
      (neg_le_abs _)

theorem inverseCoefficient_bounded (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m j, ‖inverseCoefficient z m j‖ ≤ C := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z‖ + 2)
  let C : ℝ := 1 + ∑ m ∈ Finset.range N,
    ∑ j : Fin (2 * (m + 1)), ‖inverseCoefficient z m j‖
  have hsum : 0 ≤ ∑ m ∈ Finset.range N,
      ∑ j : Fin (2 * (m + 1)), ‖inverseCoefficient z m j‖ :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro m j
  by_cases hm : m < N
  · have hj : ‖inverseCoefficient z m j‖ ≤
        ∑ k : Fin (2 * (m + 1)), ‖inverseCoefficient z m k‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have hm' : (∑ k : Fin (2 * (m + 1)), ‖inverseCoefficient z m k‖) ≤
        ∑ n ∈ Finset.range N, ∑ k : Fin (2 * (n + 1)), ‖inverseCoefficient z n k‖ :=
      Finset.single_le_sum
        (f := fun n : ℕ => ∑ k : Fin (2 * (n + 1)), ‖inverseCoefficient z n k‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr hm)
    dsimp [C]
    linarith
  · have hNm : (N : ℝ) ≤ m := by exact_mod_cast (le_of_not_gt hm)
    have hsub : |kineticEigenvalue m j + 3 / 2| - ‖z‖ ≤
        ‖((kineticEigenvalue m j + 3 / 2 : ℝ) : ℂ) - z‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        norm_sub_norm_le ((kineticEigenvalue m j + 3 / 2 : ℝ) : ℂ) z
    have hlarge : 1 ≤ ‖((kineticEigenvalue m j + 3 / 2 : ℝ) : ℂ) - z‖ := by
      have hgrowth := degree_le_abs_eigenvalue m j
      linarith
    have hinv : ‖inverseCoefficient z m j‖ ≤ 1 := by
      rw [inverseCoefficient, norm_inv]
      exact inv_le_one_of_one_le₀ hlarge
    dsimp [C]
    linarith

def inverseBound (z : ℂ) : ℝ := Classical.choose (inverseCoefficient_bounded z)

theorem inverseBound_nonneg (z : ℂ) : 0 ≤ inverseBound z :=
  (Classical.choose_spec (inverseCoefficient_bounded z)).1

theorem inverseCoefficient_le (z : ℂ) (a : SpinIndex) :
    ‖inverseCoefficient z a.1.1 a.2‖ ≤ inverseBound z :=
  (Classical.choose_spec (inverseCoefficient_bounded z)).2 a.1.1 a.2

def inverseSequenceMap (z : ℂ) :
    lp (fun _ : SpinIndex => ℂ) 2 →L[ℂ] lp (fun _ : SpinIndex => ℂ) 2 :=
  lp.mapCLM 2
    (fun a : SpinIndex => inverseCoefficient z a.1.1 a.2 • ContinuousLinearMap.id ℂ ℂ)
    (inverseBound_nonneg z)
    (fun a => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        inverseCoefficient_le z a)

def shifted (z : ℂ) : closedDirac.domain →ₗ[ℂ] SpinorL2 :=
  closedDirac.toFun - z • closedDirac.domain.subtype

def resolvent (z : ℂ) (_hz : ∀ a : SpinIndex, z ≠ (eigenvalue a : ℂ)) :
    SpinorL2 →L[ℂ] SpinorL2 :=
  diracHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((inverseSequenceMap z).comp
      diracHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem resolvent_coefficients (z : ℂ)
    (hz : ∀ a : SpinIndex, z ≠ (eigenvalue a : ℂ)) (F : SpinorL2) (a : SpinIndex) :
    inner ℂ (eigenfield a) (resolvent z hz F) =
      ((eigenvalue a : ℂ) - z)⁻¹ * inner ℂ (eigenfield a) F := by
  have h : diracHilbertBasis.repr (resolvent z hz F) a =
      inverseCoefficient z a.1.1 a.2 * diracHilbertBasis.repr F a := by
    change diracHilbertBasis.repr
      (diracHilbertBasis.repr.symm (inverseSequenceMap z (diracHilbertBasis.repr F))) a = _
    rw [diracHilbertBasis.repr.apply_symm_apply]
    rfl
  simpa only [HilbertBasis.repr_apply_apply, diracHilbertBasis_apply,
    inverseCoefficient, eigenvalue] using h

theorem domain_iff_memℓp (F : SpinorL2) :
    F ∈ closedDirac.domain ↔
      Memℓp (fun a : SpinIndex => (eigenvalue a : ℂ) * inner ℂ (eigenfield a) F) 2 := by
  simpa only [closedDirac, finiteDirac, diracHilbertBasis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_memℓp diracHilbertBasis eigenvalue F

theorem resolvent_mem_domain (z : ℂ)
    (hz : ∀ a : SpinIndex, z ≠ (eigenvalue a : ℂ)) (F : SpinorL2) :
    resolvent z hz F ∈ closedDirac.domain := by
  apply (domain_iff_memℓp _).mpr
  have heq : (fun a : SpinIndex => (eigenvalue a : ℂ) *
      inner ℂ (eigenfield a) (resolvent z hz F)) =
      (fun a => diracHilbertBasis.repr (F + z • resolvent z hz F) a) := by
    funext a
    rw [HilbertBasis.repr_apply_apply, diracHilbertBasis_apply, inner_add_right,
      inner_smul_right, resolvent_coefficients]
    have hden : (eigenvalue a : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
    field_simp [hden]
    ring
  rw [heq]
  exact lp.memℓp (diracHilbertBasis.repr (F + z • resolvent z hz F))

theorem resolvent_right_inverse (z : ℂ)
    (hz : ∀ a : SpinIndex, z ≠ (eigenvalue a : ℂ)) (F : SpinorL2) :
    shifted z ⟨resolvent z hz F, resolvent_mem_domain z hz F⟩ = F := by
  apply EigenbasisClosure.eq_of_coefficients diracHilbertBasis
  intro a
  rw [diracHilbertBasis_apply]
  change inner ℂ (eigenfield a)
    (closedDirac ⟨resolvent z hz F, resolvent_mem_domain z hz F⟩ - z • resolvent z hz F) = _
  rw [inner_sub_right, closedDirac_coefficients, inner_smul_right, resolvent_coefficients]
  have hden : (eigenvalue a : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
  field_simp [hden]

theorem resolvent_left_inverse (z : ℂ)
    (hz : ∀ a : SpinIndex, z ≠ (eigenvalue a : ℂ)) (F : closedDirac.domain) :
    resolvent z hz (shifted z F) = (F : SpinorL2) := by
  apply EigenbasisClosure.eq_of_coefficients diracHilbertBasis
  intro a
  rw [diracHilbertBasis_apply, resolvent_coefficients]
  change ((eigenvalue a : ℂ) - z)⁻¹ *
    inner ℂ (eigenfield a) (closedDirac F - z • (F : SpinorL2)) = _
  rw [inner_sub_right, closedDirac_coefficients, inner_smul_right]
  have hden : (eigenvalue a : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
  field_simp [hden]

structure IsResolvent (z : ℂ) (S : SpinorL2 →L[ℂ] SpinorL2) : Prop where
  mem_domain : ∀ F, S F ∈ closedDirac.domain
  right_inverse : ∀ F, shifted z ⟨S F, mem_domain F⟩ = F
  left_inverse : ∀ F : closedDirac.domain, S (shifted z F) = (F : SpinorL2)

theorem resolvent_spec (z : ℂ) (hz : ∀ a : SpinIndex, z ≠ (eigenvalue a : ℂ)) :
    IsResolvent z (resolvent z hz) where
  mem_domain := resolvent_mem_domain z hz
  right_inverse := resolvent_right_inverse z hz
  left_inverse := resolvent_left_inverse z hz

theorem IsResolvent.not_eigenvalue {z : ℂ} {S : SpinorL2 →L[ℂ] SpinorL2}
    (hS : IsResolvent z S) (a : SpinIndex) : z ≠ (eigenvalue a : ℂ) := by
  intro hz
  subst z
  have hmem : eigenfield a ∈ finiteDirac.domain :=
    finiteDirac_domain.symm ▸ Submodule.subset_span (Set.mem_range_self a)
  have hle : finiteDirac ≤ closedDirac :=
    FiniteEigenbasisCore.le_closure diracHilbertBasis eigenvalue
  let F : closedDirac.domain := ⟨eigenfield a, hle.1 hmem⟩
  have ha : closedDirac F = (eigenvalue a : ℂ) • eigenfield a := by
    exact (hle.2 (x := ⟨eigenfield a, hmem⟩) (y := F) rfl).symm.trans
      (finiteDirac_eigenfield a)
  have hzF : shifted (eigenvalue a : ℂ) F = 0 := by
    change closedDirac F - (eigenvalue a : ℂ) • eigenfield a = 0
    rw [ha, sub_self]
  have h := hS.left_inverse F
  rw [hzF, map_zero] at h
  exact eigenfield_orthonormal.ne_zero a h.symm

def resolventSet : Set ℂ := {z | ∃ S, IsResolvent z S}

def spectrum : Set ℂ := resolventSetᶜ

/-- The bounded two-sided inverse on the full closed domain exists at every
point outside the differentiated eigenvalue set. -/
theorem mem_resolventSet_iff (z : ℂ) :
    z ∈ resolventSet ↔ ∀ a : SpinIndex, z ≠ (eigenvalue a : ℂ) := by
  constructor
  · rintro ⟨S, hS⟩ a
    exact hS.not_eigenvalue a
  · intro hz
    exact ⟨resolvent z hz, resolvent_spec z hz⟩

/-- This statement excludes continuous and residual spectrum, as well as
additional eigenvalues, in the original Haar spinor space. -/
theorem mem_spectrum_iff (z : ℂ) :
    z ∈ spectrum ↔ ∃ a : SpinIndex, z = (eigenvalue a : ℂ) := by
  change (¬ z ∈ resolventSet) ↔ _
  simp only [mem_resolventSet_iff, not_forall, not_not]

theorem positive_branch_present (k : ℕ) :
    ∃ a : SpinIndex, eigenvalue a = (k : ℝ) + 3 / 2 := by
  have hcard : 0 < Fintype.card
      {j : Fin (2 * (k + 1)) // kineticEigenvalue k j = (k : ℝ)} := by
    change 0 < SourceSpinorMultiplicity.plusMultiplicity k
    rw [(SourceSpinorMultiplicity.branch_multiplicities k).1]
    omega
  obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp hcard
  exact ⟨⟨⟨k, 0⟩, j⟩, by simp only [eigenvalue, hj]⟩

theorem negative_branch_present (k : ℕ) :
    ∃ a : SpinIndex, eigenvalue a = -((k : ℝ) + 3 / 2) := by
  have hcard : 0 < Fintype.card
      {j : Fin (2 * ((k + 1) + 1)) //
        kineticEigenvalue (k + 1) j = -(((k + 1 : ℕ) : ℝ) + 2)} := by
    change 0 < SourceSpinorMultiplicity.minusMultiplicity (k + 1)
    rw [(SourceSpinorMultiplicity.branch_multiplicities (k + 1)).2]
    omega
  obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp hcard
  refine ⟨⟨⟨k + 1, 0⟩, j⟩, ?_⟩
  change kineticEigenvalue (k + 1) j + 3 / 2 = _
  rw [hj]
  push_cast
  ring

theorem eigenvalue_is_half_integer (a : SpinIndex) :
    ∃ k : ℕ, eigenvalue a = (k : ℝ) + 3 / 2 ∨
      eigenvalue a = -((k : ℝ) + 3 / 2) := by
  rcases kineticEigenvalue_branches a.1.1 a.2 with hp | hn
  · exact ⟨a.1.1, Or.inl (by simp only [eigenvalue, hp])⟩
  · have hm : 1 ≤ a.1.1 := by
      by_contra h
      have hm0 : a.1.1 = 0 := by omega
      have hs := diracEigenvalue_sq_lower a.1.1 a.2
      rw [hn, hm0] at hs
      norm_num at hs
    refine ⟨a.1.1 - 1, Or.inr ?_⟩
    change kineticEigenvalue a.1.1 a.2 + 3 / 2 = _
    rw [hn, Nat.cast_sub hm, Nat.cast_one]
    ring

/-- The complete spectrum is the two differentiated half-integer towers.
Their presence and exhaustion are both proved on the original field space. -/
theorem spectrum_half_integers (z : ℂ) :
    z ∈ spectrum ↔ ∃ k : ℕ,
      z = (((k : ℝ) + 3 / 2 : ℝ) : ℂ) ∨
        z = -(((k : ℝ) + 3 / 2 : ℝ) : ℂ) := by
  rw [mem_spectrum_iff]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hp | hn⟩ := eigenvalue_is_half_integer a
    · exact ⟨k, Or.inl (congrArg Complex.ofReal hp)⟩
    · refine ⟨k, Or.inr ?_⟩
      simpa only [Complex.ofReal_neg] using congrArg Complex.ofReal hn
  · rintro ⟨k, hp | hn⟩
    · obtain ⟨a, ha⟩ := positive_branch_present k
      exact ⟨a, hp.trans (congrArg Complex.ofReal ha).symm⟩
    · obtain ⟨a, ha⟩ := negative_branch_present k
      refine ⟨a, hn.trans ?_⟩
      simpa only [Complex.ofReal_neg] using (congrArg Complex.ofReal ha).symm

end GeneratedFoundations.Geometry.SourceSpinorResolvent
