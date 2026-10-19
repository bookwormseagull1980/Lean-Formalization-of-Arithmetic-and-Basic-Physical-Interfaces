module

public import GeneratedFoundations.Geometry.SourceTensorTTClosedSpectrum
public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Bounded resolvents of the original TT rough operator

The eigenvalues derived from covariant differentiation escape every bounded
interval. Their coefficient inverses define bounded maps on the original
closed TT field. Both inverse identities hold on the full operator domain,
excluding additional continuous and residual spectrum.
-/

@[expose] public section

noncomputable section

open scoped BigOperators LinearPMap lp
open GeneratedFoundations.Geometry.SourceTensorTTBlock
open GeneratedFoundations.Geometry.SourceTensorTTBranches
open GeneratedFoundations.Geometry.SourceTensorTTField
open GeneratedFoundations.Geometry.SourceTensorTTClosedSpectrum
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceTensorTTResolvent

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

def inverseCoefficient (z : ℂ) (m : ℕ)
    (j : Fin (Module.finrank ℂ (ttSpace m))) : ℂ :=
  (((ttCurlEigenvalue m j ^ 2 - 3 : ℝ) : ℂ) - z)⁻¹

theorem degree_le_eigenvalue (m : ℕ)
    (j : Fin (Module.finrank ℂ (ttSpace m))) :
    (m : ℝ) - 6 ≤ ttCurlEigenvalue m j ^ 2 - 3 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rcases tt_eigenvalue_cases m j with hp | hn
  · rw [hp]
    nlinarith [sq_nonneg (m : ℝ)]
  · rw [hn]
    nlinarith [sq_nonneg ((m : ℝ) - 3 / 2)]

theorem inverseCoefficient_bounded (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m j, ‖inverseCoefficient z m j‖ ≤ C := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z‖ + 8)
  let C : ℝ := 1 + ∑ m ∈ Finset.range N,
    ∑ j : Fin (Module.finrank ℂ (ttSpace m)), ‖inverseCoefficient z m j‖
  have hsum : 0 ≤ ∑ m ∈ Finset.range N,
      ∑ j : Fin (Module.finrank ℂ (ttSpace m)), ‖inverseCoefficient z m j‖ :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro m j
  by_cases hm : m < N
  · have hj : ‖inverseCoefficient z m j‖ ≤
        ∑ k : Fin (Module.finrank ℂ (ttSpace m)), ‖inverseCoefficient z m k‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have hm' : (∑ k : Fin (Module.finrank ℂ (ttSpace m)), ‖inverseCoefficient z m k‖) ≤
        ∑ n ∈ Finset.range N,
          ∑ k : Fin (Module.finrank ℂ (ttSpace n)), ‖inverseCoefficient z n k‖ :=
      Finset.single_le_sum
        (f := fun n : ℕ =>
          ∑ k : Fin (Module.finrank ℂ (ttSpace n)), ‖inverseCoefficient z n k‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr hm)
    dsimp [C]
    linarith
  · have hNm : (N : ℝ) ≤ m := by exact_mod_cast (le_of_not_gt hm)
    have hsub : |ttCurlEigenvalue m j ^ 2 - 3| - ‖z‖ ≤
        ‖((ttCurlEigenvalue m j ^ 2 - 3 : ℝ) : ℂ) - z‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        norm_sub_norm_le ((ttCurlEigenvalue m j ^ 2 - 3 : ℝ) : ℂ) z
    have hlarge : 1 ≤ ‖((ttCurlEigenvalue m j ^ 2 - 3 : ℝ) : ℂ) - z‖ := by
      have hgrowth := degree_le_eigenvalue m j
      have habs := le_abs_self (ttCurlEigenvalue m j ^ 2 - 3)
      linarith
    have hinv : ‖inverseCoefficient z m j‖ ≤ 1 := by
      rw [inverseCoefficient, norm_inv]
      exact inv_le_one_of_one_le₀ hlarge
    dsimp [C]
    linarith

def inverseBound (z : ℂ) : ℝ := Classical.choose (inverseCoefficient_bounded z)

theorem inverseBound_nonneg (z : ℂ) : 0 ≤ inverseBound z :=
  (Classical.choose_spec (inverseCoefficient_bounded z)).1

theorem inverseCoefficient_le (z : ℂ) (a : TTIndex) :
    ‖inverseCoefficient z a.1.1.val a.2‖ ≤ inverseBound z :=
  (Classical.choose_spec (inverseCoefficient_bounded z)).2 a.1.1.val a.2

def inverseSequenceMap (z : ℂ) :
    lp (fun _ : TTIndex => ℂ) 2 →L[ℂ] lp (fun _ : TTIndex => ℂ) 2 :=
  lp.mapCLM 2
    (fun a : TTIndex => inverseCoefficient z a.1.1.val a.2 • ContinuousLinearMap.id ℂ ℂ)
    (inverseBound_nonneg z)
    (fun a => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        inverseCoefficient_le z a)

def shifted (z : ℂ) : closedRough.domain →ₗ[ℂ] ttField :=
  closedRough.toFun - z • closedRough.domain.subtype

def resolvent (z : ℂ) (_hz : ∀ a : TTIndex, z ≠ (roughEigenvalue a : ℂ)) :
    ttField →L[ℂ] ttField :=
  ttHilbertBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((inverseSequenceMap z).comp
      ttHilbertBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem resolvent_coefficients (z : ℂ)
    (hz : ∀ a : TTIndex, z ≠ (roughEigenvalue a : ℂ)) (F : ttField) (a : TTIndex) :
    inner ℂ (eigenfield a) (resolvent z hz F) =
      ((roughEigenvalue a : ℂ) - z)⁻¹ * inner ℂ (eigenfield a) F := by
  have h : ttHilbertBasis.repr (resolvent z hz F) a =
      inverseCoefficient z a.1.1.val a.2 * ttHilbertBasis.repr F a := by
    change ttHilbertBasis.repr
      (ttHilbertBasis.repr.symm (inverseSequenceMap z (ttHilbertBasis.repr F))) a = _
    rw [ttHilbertBasis.repr.apply_symm_apply]
    rfl
  simpa only [HilbertBasis.repr_apply_apply, ttHilbertBasis_apply,
    inverseCoefficient, roughEigenvalue] using h

theorem domain_iff_memℓp (F : ttField) :
    F ∈ closedRough.domain ↔
      Memℓp (fun a : TTIndex => (roughEigenvalue a : ℂ) * inner ℂ (eigenfield a) F) 2 := by
  simpa only [closedRough, finiteRough, ttHilbertBasis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_memℓp ttHilbertBasis roughEigenvalue F

theorem resolvent_mem_domain (z : ℂ)
    (hz : ∀ a : TTIndex, z ≠ (roughEigenvalue a : ℂ)) (F : ttField) :
    resolvent z hz F ∈ closedRough.domain := by
  apply (domain_iff_memℓp _).mpr
  have heq : (fun a : TTIndex => (roughEigenvalue a : ℂ) *
      inner ℂ (eigenfield a) (resolvent z hz F)) =
      (fun a => ttHilbertBasis.repr (F + z • resolvent z hz F) a) := by
    funext a
    rw [HilbertBasis.repr_apply_apply, ttHilbertBasis_apply, inner_add_right,
      inner_smul_right, resolvent_coefficients]
    have hden : (roughEigenvalue a : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
    field_simp [hden]
    ring
  rw [heq]
  exact lp.memℓp (ttHilbertBasis.repr (F + z • resolvent z hz F))

theorem resolvent_right_inverse (z : ℂ)
    (hz : ∀ a : TTIndex, z ≠ (roughEigenvalue a : ℂ)) (F : ttField) :
    shifted z ⟨resolvent z hz F, resolvent_mem_domain z hz F⟩ = F := by
  apply EigenbasisClosure.eq_of_coefficients ttHilbertBasis
  intro a
  rw [ttHilbertBasis_apply]
  change inner ℂ (eigenfield a)
    (closedRough ⟨resolvent z hz F, resolvent_mem_domain z hz F⟩ - z • resolvent z hz F) = _
  rw [inner_sub_right, closedRough_coefficients, inner_smul_right, resolvent_coefficients]
  have hden : (roughEigenvalue a : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
  field_simp [hden]

theorem resolvent_left_inverse (z : ℂ)
    (hz : ∀ a : TTIndex, z ≠ (roughEigenvalue a : ℂ)) (F : closedRough.domain) :
    resolvent z hz (shifted z F) = (F : ttField) := by
  apply EigenbasisClosure.eq_of_coefficients ttHilbertBasis
  intro a
  rw [ttHilbertBasis_apply, resolvent_coefficients]
  change ((roughEigenvalue a : ℂ) - z)⁻¹ *
    inner ℂ (eigenfield a) (closedRough F - z • (F : ttField)) = _
  rw [inner_sub_right, closedRough_coefficients, inner_smul_right]
  have hden : (roughEigenvalue a : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
  field_simp [hden]

structure IsResolvent (z : ℂ) (S : ttField →L[ℂ] ttField) : Prop where
  mem_domain : ∀ F, S F ∈ closedRough.domain
  right_inverse : ∀ F, shifted z ⟨S F, mem_domain F⟩ = F
  left_inverse : ∀ F : closedRough.domain, S (shifted z F) = (F : ttField)

theorem resolvent_spec (z : ℂ) (hz : ∀ a : TTIndex, z ≠ (roughEigenvalue a : ℂ)) :
    IsResolvent z (resolvent z hz) where
  mem_domain := resolvent_mem_domain z hz
  right_inverse := resolvent_right_inverse z hz
  left_inverse := resolvent_left_inverse z hz

theorem IsResolvent.not_eigenvalue {z : ℂ} {S : ttField →L[ℂ] ttField}
    (hS : IsResolvent z S) (a : TTIndex) : z ≠ (roughEigenvalue a : ℂ) := by
  intro hz
  subst z
  have hmem : eigenfield a ∈ finiteRough.domain :=
    finiteRough_domain.symm ▸ Submodule.subset_span (Set.mem_range_self a)
  have hle : finiteRough ≤ closedRough :=
    FiniteEigenbasisCore.le_closure ttHilbertBasis roughEigenvalue
  let F : closedRough.domain := ⟨eigenfield a, hle.1 hmem⟩
  have ha : closedRough F = (roughEigenvalue a : ℂ) • eigenfield a := by
    exact (hle.2 (x := ⟨eigenfield a, hmem⟩) (y := F) rfl).symm.trans
      (finiteRough_eigenfield a)
  have hzF : shifted (roughEigenvalue a : ℂ) F = 0 := by
    change closedRough F - (roughEigenvalue a : ℂ) • eigenfield a = 0
    rw [ha, sub_self]
  have h := hS.left_inverse F
  rw [hzF, map_zero] at h
  exact eigenfield_orthonormal.ne_zero a h.symm

def resolventSet : Set ℂ := {z | ∃ S, IsResolvent z S}

def spectrum : Set ℂ := resolventSetᶜ

/-- The bounded two-sided inverse on the full closed domain exists at every
point outside the differentiated eigenvalue set. -/
theorem mem_resolventSet_iff (z : ℂ) :
    z ∈ resolventSet ↔ ∀ a : TTIndex, z ≠ (roughEigenvalue a : ℂ) := by
  constructor
  · rintro ⟨S, hS⟩ a
    exact hS.not_eigenvalue a
  · intro hz
    exact ⟨resolvent z hz, resolvent_spec z hz⟩

/-- This statement excludes continuous and residual spectrum, as well as
additional eigenvalues, in the original TT Haar space. -/
theorem mem_spectrum_iff (z : ℂ) :
    z ∈ spectrum ↔ ∃ a : TTIndex, z = (roughEigenvalue a : ℂ) := by
  change (¬ z ∈ resolventSet) ↔ _
  simp only [mem_resolventSet_iff, not_forall, not_not]

end GeneratedFoundations.Geometry.SourceTensorTTResolvent
