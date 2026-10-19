module

public import GeneratedFoundations.Geometry.SourceSpinorParitySpectrum
public import GeneratedFoundations.Geometry.SourceSpinorResolvent

/-!
# Bounded resolvents on both generated central spinor sectors

The inverse acts in each actual central eigenspace. At an eigenvalue of the
opposite sector the corresponding full-space coefficient inverse is zero;
those coefficients do not occur in this sector. The same proved global
inverse bound therefore constructs both sector resolvents and excludes
unlisted continuous or residual spectrum in each space.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap lp
open GeneratedFoundations.Geometry.SourceSpinorHaarBlock
open GeneratedFoundations.Geometry.SourceSpinorSpectralCore
open GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum
open GeneratedFoundations.Geometry.SourceSpinorParitySpectrum
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceSpinorParityResolvent

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

private theorem sector_inner_smul (odd : Bool) (G F : sector odd) (z : ℂ) :
    inner ℂ G (z • F) = z * inner ℂ G F := by
  change inner ℂ (G : SpinorL2) (z • (F : SpinorL2)) =
    z * inner ℂ (G : SpinorL2) (F : SpinorL2)
  exact inner_smul_right _ _ z

def inverseSequence (odd : Bool) (z : ℂ) :
    lp (fun _ : Index odd => ℂ) 2 →L[ℂ] lp (fun _ : Index odd => ℂ) 2 :=
  lp.mapCLM 2
    (fun a : Index odd => ((eigenvalue a.val : ℂ) - z)⁻¹ •
      ContinuousLinearMap.id ℂ ℂ)
    (SourceSpinorResolvent.inverseBound_nonneg z)
    (fun a => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one,
        SourceSpinorResolvent.inverseCoefficient, eigenvalue] using
        SourceSpinorResolvent.inverseCoefficient_le z a.val)

def shifted (odd : Bool) (z : ℂ) :
    (closedSectorDirac odd).domain →ₗ[ℂ] sector odd :=
  (closedSectorDirac odd).toFun - z • (closedSectorDirac odd).domain.subtype

def resolvent (odd : Bool) (z : ℂ) : sector odd →L[ℂ] sector odd :=
  (sectorHilbertBasis odd).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((inverseSequence odd z).comp
      (sectorHilbertBasis odd).repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem resolvent_coefficients (odd : Bool) (z : ℂ) (F : sector odd) (a : Index odd) :
    inner ℂ (sectorHilbertBasis odd a) (resolvent odd z F) =
      ((eigenvalue a.val : ℂ) - z)⁻¹ * inner ℂ (sectorHilbertBasis odd a) F := by
  have h : (sectorHilbertBasis odd).repr (resolvent odd z F) a =
      ((eigenvalue a.val : ℂ) - z)⁻¹ * (sectorHilbertBasis odd).repr F a := by
    change (sectorHilbertBasis odd).repr
      ((sectorHilbertBasis odd).repr.symm
        (inverseSequence odd z ((sectorHilbertBasis odd).repr F))) a = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  simpa only [HilbertBasis.repr_apply_apply] using h

theorem resolvent_mem_domain (odd : Bool) (z : ℂ)
    (hz : ∀ a : Index odd, z ≠ (eigenvalue a.val : ℂ)) (F : sector odd) :
    resolvent odd z F ∈ (closedSectorDirac odd).domain := by
  apply (FiniteEigenbasisCore.closure_domain_iff_memℓp
    (sectorHilbertBasis odd) (fun a => eigenvalue a.val) _).mpr
  have heq : (fun a : Index odd => (eigenvalue a.val : ℂ) *
      inner ℂ (sectorHilbertBasis odd a) (resolvent odd z F)) =
      (fun a => (sectorHilbertBasis odd).repr (F + z • resolvent odd z F) a) := by
    funext a
    rw [HilbertBasis.repr_apply_apply, inner_add_right, sector_inner_smul,
      resolvent_coefficients]
    have hden : (eigenvalue a.val : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
    field_simp [hden]
    ring
  rw [heq]
  exact lp.memℓp ((sectorHilbertBasis odd).repr (F + z • resolvent odd z F))

private theorem sector_coefficients (odd : Bool)
    (F : (closedSectorDirac odd).domain) (a : Index odd) :
    inner ℂ (sectorHilbertBasis odd a) (closedSectorDirac odd F) =
      (eigenvalue a.val : ℂ) * inner ℂ (sectorHilbertBasis odd a) (F : sector odd) :=
  FiniteEigenbasisCore.closure_coefficients
    (sectorHilbertBasis odd) (fun a => eigenvalue a.val) F a

theorem resolvent_right_inverse (odd : Bool) (z : ℂ)
    (hz : ∀ a : Index odd, z ≠ (eigenvalue a.val : ℂ)) (F : sector odd) :
    shifted odd z ⟨resolvent odd z F, resolvent_mem_domain odd z hz F⟩ = F := by
  apply EigenbasisClosure.eq_of_coefficients (sectorHilbertBasis odd)
  intro a
  change inner ℂ (sectorHilbertBasis odd a)
    (closedSectorDirac odd ⟨resolvent odd z F, resolvent_mem_domain odd z hz F⟩ -
      z • resolvent odd z F) = _
  rw [inner_sub_right, sector_coefficients, sector_inner_smul, resolvent_coefficients]
  have hden : (eigenvalue a.val : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
  field_simp [hden]

theorem resolvent_left_inverse (odd : Bool) (z : ℂ)
    (hz : ∀ a : Index odd, z ≠ (eigenvalue a.val : ℂ))
    (F : (closedSectorDirac odd).domain) :
    resolvent odd z (shifted odd z F) = (F : sector odd) := by
  apply EigenbasisClosure.eq_of_coefficients (sectorHilbertBasis odd)
  intro a
  rw [resolvent_coefficients]
  change ((eigenvalue a.val : ℂ) - z)⁻¹ * inner ℂ (sectorHilbertBasis odd a)
    (closedSectorDirac odd F - z • (F : sector odd)) = _
  rw [inner_sub_right, sector_coefficients, sector_inner_smul]
  have hden : (eigenvalue a.val : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz a).symm
  field_simp [hden]

structure IsResolvent (odd : Bool) (z : ℂ) (S : sector odd →L[ℂ] sector odd) : Prop where
  mem_domain : ∀ F, S F ∈ (closedSectorDirac odd).domain
  right_inverse : ∀ F, shifted odd z ⟨S F, mem_domain F⟩ = F
  left_inverse : ∀ F : (closedSectorDirac odd).domain,
    S (shifted odd z F) = (F : sector odd)

theorem resolvent_spec (odd : Bool) (z : ℂ)
    (hz : ∀ a : Index odd, z ≠ (eigenvalue a.val : ℂ)) :
    IsResolvent odd z (resolvent odd z) where
  mem_domain := resolvent_mem_domain odd z hz
  right_inverse := resolvent_right_inverse odd z hz
  left_inverse := resolvent_left_inverse odd z hz

theorem IsResolvent.not_eigenvalue {odd : Bool} {z : ℂ}
    {S : sector odd →L[ℂ] sector odd} (hS : IsResolvent odd z S) (a : Index odd) :
    z ≠ (eigenvalue a.val : ℂ) := by
  intro hz
  subst z
  let B := sectorHilbertBasis odd
  let v : Index odd → ℝ := fun a => eigenvalue a.val
  have hmem : B a ∈ (finiteSectorDirac odd).domain :=
    FiniteEigenbasisCore.basis_mem_domain B v a
  have hle : finiteSectorDirac odd ≤ closedSectorDirac odd :=
    FiniteEigenbasisCore.le_closure B v
  let F : (closedSectorDirac odd).domain := ⟨B a, hle.1 hmem⟩
  have ha : closedSectorDirac odd F = (eigenvalue a.val : ℂ) • B a :=
    (hle.2 (x := ⟨B a, hmem⟩) (y := F) rfl).symm.trans
      (FiniteEigenbasisCore.basis_action B v a)
  have hzF : shifted odd (eigenvalue a.val : ℂ) F = 0 := by
    change closedSectorDirac odd F - (eigenvalue a.val : ℂ) • B a = 0
    rw [ha, sub_self]
  have h := hS.left_inverse F
  rw [hzF, map_zero] at h
  exact B.orthonormal.ne_zero a h.symm

def spectrum (odd : Bool) : Set ℂ := {z | ¬ ∃ S, IsResolvent odd z S}

/-- Each actual central sector has exactly its differentiated eigenvalues;
the bounded inverse proves exhaustion on the full closed domain. -/
theorem mem_spectrum_iff (odd : Bool) (z : ℂ) :
    z ∈ spectrum odd ↔ ∃ a : Index odd, z = (eigenvalue a.val : ℂ) := by
  classical
  constructor
  · intro hz
    by_contra h
    have he : ∀ a : Index odd, z ≠ (eigenvalue a.val : ℂ) := by
      simpa only [not_exists] using h
    exact hz ⟨resolvent odd z, resolvent_spec odd z he⟩
  · rintro ⟨a, rfl⟩ ⟨S, hS⟩
    exact hS.not_eigenvalue a rfl

theorem positive_label (odd : Bool) (k : ℕ) :
    (∃ a : Index odd, eigenvalue a.val = (k : ℝ) + 3 / 2) ↔
      (-1 : ℂ) ^ k = sign odd := by
  constructor
  · rintro ⟨a, ha⟩
    rcases kineticEigenvalue_branches a.val.1.1 a.val.2 with hp | hn
    · have hm : a.val.1.1 = k := by
        apply Nat.cast_injective (R := ℝ)
        change kineticEigenvalue a.val.1.1 a.val.2 + 3 / 2 = _ at ha
        rw [hp] at ha
        linarith
      simpa only [hm] using a.property
    · change kineticEigenvalue a.val.1.1 a.val.2 + 3 / 2 = _ at ha
      rw [hn] at ha
      have hm := Nat.cast_nonneg (α := ℝ) a.val.1.1
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith
  · intro hk
    have hc : 0 < Fintype.card
        {j : Fin (2 * (k + 1)) // kineticEigenvalue k j = (k : ℝ)} := by
      change 0 < SourceSpinorMultiplicity.plusMultiplicity k
      rw [(SourceSpinorMultiplicity.branch_multiplicities k).1]
      omega
    obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp hc
    exact ⟨⟨⟨⟨k, 0⟩, j⟩, hk⟩, by simp only [eigenvalue, hj]⟩

theorem negative_label (odd : Bool) (k : ℕ) :
    (∃ a : Index odd, eigenvalue a.val = -((k : ℝ) + 3 / 2)) ↔
      (-1 : ℂ) ^ (k + 1) = sign odd := by
  constructor
  · rintro ⟨a, ha⟩
    rcases kineticEigenvalue_branches a.val.1.1 a.val.2 with hp | hn
    · change kineticEigenvalue a.val.1.1 a.val.2 + 3 / 2 = _ at ha
      rw [hp] at ha
      have hm := Nat.cast_nonneg (α := ℝ) a.val.1.1
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith
    · have hm : a.val.1.1 = k + 1 := by
        apply Nat.cast_injective (R := ℝ)
        change kineticEigenvalue a.val.1.1 a.val.2 + 3 / 2 = _ at ha
        rw [hn] at ha
        push_cast
        linarith
      simpa only [hm] using a.property
  · intro hk
    have hc : 0 < Fintype.card
        {j : Fin (2 * ((k + 1) + 1)) //
          kineticEigenvalue (k + 1) j = -(((k + 1 : ℕ) : ℝ) + 2)} := by
      change 0 < SourceSpinorMultiplicity.minusMultiplicity (k + 1)
      rw [(SourceSpinorMultiplicity.branch_multiplicities (k + 1)).2]
      omega
    obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp hc
    refine ⟨⟨⟨⟨k + 1, 0⟩, j⟩, hk⟩, ?_⟩
    change kineticEigenvalue (k + 1) j + 3 / 2 = _
    rw [hj]
    push_cast
    ring

/-- The two spin structures have the opposite branch parities forced by
the original central operation. Both presence and exhaustion are proved. -/
theorem spectrum_labels (odd : Bool) (z : ℂ) :
    z ∈ spectrum odd ↔ ∃ k : ℕ,
      (z = (((k : ℝ) + 3 / 2 : ℝ) : ℂ) ∧ (-1 : ℂ) ^ k = sign odd) ∨
      (z = -(((k : ℝ) + 3 / 2 : ℝ) : ℂ) ∧ (-1 : ℂ) ^ (k + 1) = sign odd) := by
  rw [mem_spectrum_iff]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hp | hn⟩ := SourceSpinorResolvent.eigenvalue_is_half_integer a.val
    · exact ⟨k, Or.inl ⟨congrArg Complex.ofReal hp,
        (positive_label odd k).mp ⟨a, hp⟩⟩⟩
    · refine ⟨k, Or.inr ⟨?_, (negative_label odd k).mp ⟨a, hn⟩⟩⟩
      simpa only [Complex.ofReal_neg] using congrArg Complex.ofReal hn
  · rintro ⟨k, ⟨hz, hk⟩ | ⟨hz, hk⟩⟩
    · obtain ⟨a, ha⟩ := (positive_label odd k).mpr hk
      exact ⟨a, hz.trans (congrArg Complex.ofReal ha).symm⟩
    · obtain ⟨a, ha⟩ := (negative_label odd k).mpr hk
      refine ⟨a, hz.trans ?_⟩
      simpa only [Complex.ofReal_neg] using (congrArg Complex.ofReal ha).symm

end GeneratedFoundations.Geometry.SourceSpinorParityResolvent
