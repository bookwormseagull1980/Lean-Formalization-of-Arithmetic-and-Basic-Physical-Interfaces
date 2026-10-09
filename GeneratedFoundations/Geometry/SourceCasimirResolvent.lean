module

public import GeneratedFoundations.Geometry.SourceCasimirClosure
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Tactic.FieldSimp

/-!
# The full spectrum of the closed source Casimir

The inverse is a bounded map on the original source Haar Hilbert space,
constructed through its actual complete matrix coefficients.  Its values
lie in the full closed-operator domain, and both inverse identities are
proved there.  The resulting spectrum statement therefore excludes
continuous and residual spectral points as well as additional eigenvalues.
-/

@[expose] public section

noncomputable section

open scoped BigOperators LinearPMap
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceCasimirClosure
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceCasimirResolvent

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

private theorem index_le_energy (m : ℕ) : (m : ℝ) ≤ energy m := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold energy
  nlinarith [sq_nonneg (m : ℝ)]

def inverseCoefficient (z : ℂ) (m : ℕ) : ℂ := ((energy m : ℂ) - z)⁻¹

/-- The growing source energies give a uniform inverse-coefficient bound.
The finitely many low degrees are kept explicitly in the bound. -/
theorem inverseCoefficient_bounded (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ‖inverseCoefficient z m‖ ≤ C := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z‖ + 1)
  let C : ℝ := 1 + ∑ m ∈ Finset.range N, ‖inverseCoefficient z m‖
  have hsum : 0 ≤ ∑ m ∈ Finset.range N, ‖inverseCoefficient z m‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro m
  by_cases hm : m < N
  · have hsingle : ‖inverseCoefficient z m‖ ≤
        ∑ n ∈ Finset.range N, ‖inverseCoefficient z n‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hm)
    dsimp [C]
    linarith
  · have hNm : (N : ℝ) ≤ m := by exact_mod_cast (le_of_not_gt hm)
    have hsub : energy m - ‖z‖ ≤ ‖(energy m : ℂ) - z‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (energy_nonneg m)] using
        norm_sub_norm_le (energy m : ℂ) z
    have hlarge : 1 ≤ ‖(energy m : ℂ) - z‖ := by
      have hgrowth := index_le_energy m
      linarith
    have hinv : ‖inverseCoefficient z m‖ ≤ 1 := by
      rw [inverseCoefficient, norm_inv]
      exact inv_le_one_of_one_le₀ hlarge
    dsimp [C]
    linarith

def inverseBound (z : ℂ) : ℝ := Classical.choose (inverseCoefficient_bounded z)

theorem inverseBound_nonneg (z : ℂ) : 0 ≤ inverseBound z :=
  (Classical.choose_spec (inverseCoefficient_bounded z)).1

theorem inverseCoefficient_le (z : ℂ) (m : ℕ) :
    ‖inverseCoefficient z m‖ ≤ inverseBound z :=
  (Classical.choose_spec (inverseCoefficient_bounded z)).2 m

def inverseSequenceMap (z : ℂ) :
    lp (fun _ : Index => ℂ) 2 →L[ℂ] lp (fun _ : Index => ℂ) 2 :=
  lp.mapCLM 2
    (fun a : Index => inverseCoefficient z a.1 • ContinuousLinearMap.id ℂ ℂ)
    (inverseBound_nonneg z)
    (fun a => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        inverseCoefficient_le z a.1)

/-- The bounded candidate is transported by the original Hilbert basis.
The non-eigenvalue hypothesis is used to prove its inverse identities. -/
def resolvent (z : ℂ) (_hz : ∀ m : ℕ, z ≠ (energy m : ℂ)) :
    SourceL2 →L[ℂ] SourceL2 :=
  basis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((inverseSequenceMap z).comp basis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem resolvent_repr (z : ℂ) (hz : ∀ m : ℕ, z ≠ (energy m : ℂ))
    (f : SourceL2) (a : Index) :
    basis.repr (resolvent z hz f) a = inverseCoefficient z a.1 * basis.repr f a := by
  change basis.repr (basis.repr.symm (inverseSequenceMap z (basis.repr f))) a = _
  rw [basis.repr.apply_symm_apply]
  rfl

theorem resolvent_coefficients (z : ℂ) (hz : ∀ m : ℕ, z ≠ (energy m : ℂ))
    (f : SourceL2) (a : Index) :
    inner ℂ (basisVector a) (resolvent z hz f) =
      inverseCoefficient z a.1 * inner ℂ (basisVector a) f := by
  simpa only [basis.repr_apply_apply, basis_apply] using resolvent_repr z hz f a

theorem operator_domain_iff_memℓp (f : SourceL2) :
    f ∈ operator.domain ↔
      Memℓp (fun a : Index => (energy a.1 : ℂ) * inner ℂ (basisVector a) f) 2 := by
  simpa only [operator, finiteCore, basis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_memℓp basis (fun a => energy a.1) f

theorem resolvent_mem_domain (z : ℂ) (hz : ∀ m : ℕ, z ≠ (energy m : ℂ))
    (f : SourceL2) : resolvent z hz f ∈ operator.domain := by
  apply (operator_domain_iff_memℓp _).mpr
  have heq : (fun a : Index => (energy a.1 : ℂ) *
        inner ℂ (basisVector a) (resolvent z hz f)) =
      (fun a => basis.repr (f + z • resolvent z hz f) a) := by
    funext a
    rw [basis.repr_apply_apply, basis_apply, inner_add_right, inner_smul_right,
      resolvent_coefficients]
    have hden : (energy a.1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a.1).symm
    unfold inverseCoefficient
    field_simp [hden]
    ring
  rw [heq]
  exact lp.memℓp (basis.repr (f + z • resolvent z hz f))

theorem resolvent_right_inverse (z : ℂ) (hz : ∀ m : ℕ, z ≠ (energy m : ℂ))
    (f : SourceL2) : shifted z ⟨resolvent z hz f, resolvent_mem_domain z hz f⟩ = f := by
  apply SourceCompleteCoefficients.eq_of_coefficients_eq
  intro a
  change inner ℂ (basisVector a)
      (operator ⟨resolvent z hz f, resolvent_mem_domain z hz f⟩ - z • resolvent z hz f) = _
  rw [inner_sub_right, operator_coefficients, inner_smul_right, resolvent_coefficients]
  have hden : (energy a.1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a.1).symm
  unfold inverseCoefficient
  field_simp [hden]

theorem resolvent_left_inverse (z : ℂ) (hz : ∀ m : ℕ, z ≠ (energy m : ℂ))
    (u : operator.domain) : resolvent z hz (shifted z u) = (u : SourceL2) := by
  apply SourceCompleteCoefficients.eq_of_coefficients_eq
  intro a
  rw [resolvent_coefficients]
  change inverseCoefficient z a.1 *
      inner ℂ (basisVector a) (operator u - z • (u : SourceL2)) = _
  rw [inner_sub_right, operator_coefficients, inner_smul_right]
  have hden : (energy a.1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a.1).symm
  unfold inverseCoefficient
  field_simp [hden]

/-- A resolvent must be bounded on the original Hilbert space and invert
the actual closed operator on its full domain in both directions. -/
structure IsResolvent (z : ℂ) (S : SourceL2 →L[ℂ] SourceL2) : Prop where
  mem_domain : ∀ f, S f ∈ operator.domain
  right_inverse : ∀ f, shifted z ⟨S f, mem_domain f⟩ = f
  left_inverse : ∀ u : operator.domain, S (shifted z u) = (u : SourceL2)

theorem resolvent_spec (z : ℂ) (hz : ∀ m : ℕ, z ≠ (energy m : ℂ)) :
    IsResolvent z (resolvent z hz) where
  mem_domain := resolvent_mem_domain z hz
  right_inverse := resolvent_right_inverse z hz
  left_inverse := resolvent_left_inverse z hz

theorem IsResolvent.unique {z : ℂ} {S T : SourceL2 →L[ℂ] SourceL2}
    (hS : IsResolvent z S) (hT : IsResolvent z T) : S = T := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    S f = S (shifted z ⟨T f, hT.mem_domain f⟩) := by rw [hT.right_inverse]
    _ = T f := hS.left_inverse ⟨T f, hT.mem_domain f⟩

theorem IsResolvent.not_eigenvalue {z : ℂ} {S : SourceL2 →L[ℂ] SourceL2}
    (hS : IsResolvent z S) (m : ℕ) : z ≠ (energy m : ℂ) := by
  intro hz
  subst z
  let a : Index := ⟨m, 0, 0⟩
  let u : operator.domain := ⟨basisVector a, basis_mem_domain a⟩
  have hu : shifted (energy m : ℂ) u = 0 := by
    change operator ⟨basisVector a, basis_mem_domain a⟩ -
      (energy a.1 : ℂ) • basisVector a = 0
    rw [operator_basis, sub_self]
  have h := hS.left_inverse u
  rw [hu, map_zero] at h
  exact basisVector_orthonormal.ne_zero a h.symm

def resolventSet : Set ℂ := {z | ∃ S : SourceL2 →L[ℂ] SourceL2, IsResolvent z S}

/-- Complement of the full bounded two-sided resolvent set. -/
def spectrum : Set ℂ := resolventSetᶜ

theorem mem_resolventSet_iff (z : ℂ) :
    z ∈ resolventSet ↔ ∀ m : ℕ, z ≠ (energy m : ℂ) := by
  constructor
  · rintro ⟨S, hS⟩ m
    exact hS.not_eigenvalue m
  · intro hz
    exact ⟨resolvent z hz, resolvent_spec z hz⟩

/-- No additional continuous or residual spectral points remain. -/
theorem mem_spectrum_iff (z : ℂ) :
    z ∈ spectrum ↔ ∃ m : ℕ, z = (energy m : ℂ) := by
  change (¬ z ∈ resolventSet) ↔ _
  simp only [mem_resolventSet_iff, not_forall, not_not]

theorem spectrum_eq_range : spectrum = Set.range (fun m : ℕ => (energy m : ℂ)) := by
  ext z
  rw [mem_spectrum_iff]
  exact exists_congr (fun _ => eq_comm)

theorem resolvent_existsUnique (z : ℂ) (hz : ∀ m : ℕ, z ≠ (energy m : ℂ)) :
    ∃! S : SourceL2 →L[ℂ] SourceL2, IsResolvent z S := by
  refine ⟨resolvent z hz, resolvent_spec z hz, ?_⟩
  intro S hS
  exact hS.unique (resolvent_spec z hz)

end GeneratedFoundations.Geometry.SourceCasimirResolvent
