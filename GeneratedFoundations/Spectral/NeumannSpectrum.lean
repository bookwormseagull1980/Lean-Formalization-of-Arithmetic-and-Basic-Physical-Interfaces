module

public import GeneratedFoundations.Spectral.NeumannResolvent
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# The full spectrum of the Neumann differential operator

The resolvent is defined by bounded two-sided inverses on the original
absolutely continuous Sobolev domain. The compact inverse of `I + A` reduces
the construction at an arbitrary non-eigenvalue to the Fredholm alternative
for a bounded compact operator. This proves the full spectrum statement,
including the absence of continuous or residual spectrum.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped LinearPMap

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

/-- The shifted differential operator on its original Neumann domain. -/
def neumannShift (z : ℂ) :
    (complexNeumannOperator hL.out).domain →ₗ[ℂ] ComplexIntervalL2 0 L :=
  (complexNeumannOperator hL.out).toFun -
    z • (complexNeumannOperator hL.out).domain.subtype

theorem neumannShift_apply (z : ℂ) (u : (complexNeumannOperator hL.out).domain) :
    neumannShift L z u = complexNeumannOperator hL.out u -
      z • (u : ComplexIntervalL2 0 L) := rfl

/-- A bounded inverse must take values in the actual differential domain. -/
structure IsNeumannResolvent (z : ℂ)
    (S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L) : Prop where
  mem_domain : ∀ f, S f ∈ (complexNeumannOperator hL.out).domain
  right_inverse : ∀ f, neumannShift L z ⟨S f, mem_domain f⟩ = f
  left_inverse : ∀ u : (complexNeumannOperator hL.out).domain,
    S (neumannShift L z u) = (u : ComplexIntervalL2 0 L)

/-- The usual resolvent set for the closed, unbounded Neumann operator. -/
def neumannResolventSet : Set ℂ :=
  {z | ∃ S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L,
    IsNeumannResolvent L z S}

def neumannSpectrum : Set ℂ := (neumannResolventSet L)ᶜ

theorem IsNeumannResolvent.unique {z : ℂ}
    {S T : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L}
    (hS : IsNeumannResolvent L z S) (hT : IsNeumannResolvent L z T) : S = T := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    S f = S (neumannShift L z ⟨T f, hT.mem_domain f⟩) := by
      rw [hT.right_inverse]
    _ = T f := hS.left_inverse ⟨T f, hT.mem_domain f⟩

theorem neumannShift_eq_zero_iff (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ))
    (u : (complexNeumannOperator hL.out).domain) :
    neumannShift L z u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    apply Subtype.ext
    change (u : ComplexIntervalL2 0 L) = 0
    by_contra hne
    have heig : complexNeumannOperator hL.out u =
        z • (u : ComplexIntervalL2 0 L) :=
      sub_eq_zero.mp hu
    obtain ⟨n, hn⟩ := (complexNeumann_eigenvalue_iff L z).mp ⟨u, hne, heig⟩
    exact hz n hn
  · rintro rfl
    exact map_zero _

theorem neumannShift_injective (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) :
    Function.Injective (neumannShift L z) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply (neumannShift_eq_zero_iff L z hz (u - v)).mp
  rw [map_sub, huv, sub_self]

/-- The bounded Fredholm factor in `(A - z) (I + A)⁻¹`. -/
def neumannFredholmOperator (z : ℂ) :
    ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L :=
  1 - (z + 1) • neumannResolvent L

theorem neumannFredholmOperator_apply (z : ℂ) (f : ComplexIntervalL2 0 L) :
    neumannFredholmOperator L z f = f - (z + 1) • neumannResolvent L f := rfl

theorem neumannShift_resolvent (z : ℂ) (f : ComplexIntervalL2 0 L) :
    neumannShift L z ⟨neumannResolvent L f, neumannResolvent_mem_domain L f⟩ =
      neumannFredholmOperator L z f := by
  rw [neumannShift_apply, complexNeumannOperator_resolvent,
    neumannFredholmOperator_apply, add_smul, one_smul]
  abel

theorem neumannFredholmOperator_eq_zero (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ))
    (f : ComplexIntervalL2 0 L) (hf : neumannFredholmOperator L z f = 0) : f = 0 := by
  have hu : (⟨neumannResolvent L f, neumannResolvent_mem_domain L f⟩ :
      (complexNeumannOperator hL.out).domain) = 0 :=
    (neumannShift_eq_zero_iff L z hz _).mp ((neumannShift_resolvent L z f).trans hf)
  have hv : neumannResolvent L f = 0 := congrArg Subtype.val hu
  have h := neumannResolvent_right_inverse L f
  rw [hu, LinearPMap.map_zero, hv, add_zero] at h
  exact h.symm

theorem neumannFredholmOperator_isUnit (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) :
    IsUnit (neumannFredholmOperator L z) := by
  let K : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L :=
    (z + 1) • neumannResolvent L
  have hK : IsCompactOperator K := (neumannResolvent_isCompact L).smul (z + 1)
  have hnot : ¬ Module.End.HasEigenvalue K.toLinearMap (1 : ℂ) := by
    intro heig
    obtain ⟨f, hf⟩ := heig.exists_hasEigenvector
    have hKf : K f = f := by
      simpa only [ContinuousLinearMap.coe_coe, one_smul] using hf.apply_eq_smul
    have hzero : neumannFredholmOperator L z f = 0 := by
      change f - K f = 0
      rw [hKf, sub_self]
    exact hf.2 (neumannFredholmOperator_eq_zero L z hz f hzero)
  have hr := (hK.hasEigenvalue_or_mem_resolventSet (one_ne_zero : (1 : ℂ) ≠ 0)).resolve_left hnot
  have hu := spectrum.mem_resolventSet_iff.mp hr
  simp only [map_one] at hu
  convert! hu using 1

def neumannFredholmInverse (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) :
    ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L :=
  ↑(neumannFredholmOperator_isUnit L z hz).unit⁻¹

theorem neumannFredholmInverse_right (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) (f : ComplexIntervalL2 0 L) :
    neumannFredholmOperator L z (neumannFredholmInverse L z hz f) = f := by
  have h := congrArg (fun T : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L => T f)
    (neumannFredholmOperator_isUnit L z hz).mul_val_inv
  exact h

/-- The bounded inverse of `A - z` for every parameter outside its eigenvalues. -/
def neumannShiftResolvent (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) :
    ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L :=
  (neumannResolvent L).comp (neumannFredholmInverse L z hz)

theorem neumannShiftResolvent_mem_domain (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) (f : ComplexIntervalL2 0 L) :
    neumannShiftResolvent L z hz f ∈ (complexNeumannOperator hL.out).domain :=
  neumannResolvent_mem_domain L (neumannFredholmInverse L z hz f)

theorem neumannShiftResolvent_right_inverse (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) (f : ComplexIntervalL2 0 L) :
    neumannShift L z
      ⟨neumannShiftResolvent L z hz f, neumannShiftResolvent_mem_domain L z hz f⟩ = f := by
  change neumannShift L z
    ⟨neumannResolvent L (neumannFredholmInverse L z hz f),
      neumannResolvent_mem_domain L (neumannFredholmInverse L z hz f)⟩ = f
  rw [neumannShift_resolvent, neumannFredholmInverse_right]

theorem neumannShiftResolvent_left_inverse (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ))
    (u : (complexNeumannOperator hL.out).domain) :
    neumannShiftResolvent L z hz (neumannShift L z u) = (u : ComplexIntervalL2 0 L) := by
  have hu : (⟨neumannShiftResolvent L z hz (neumannShift L z u),
      neumannShiftResolvent_mem_domain L z hz (neumannShift L z u)⟩ :
      (complexNeumannOperator hL.out).domain) = u :=
    neumannShift_injective L z hz (neumannShiftResolvent_right_inverse L z hz _)
  exact congrArg Subtype.val hu

theorem neumannShiftResolvent_spec (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) :
    IsNeumannResolvent L z (neumannShiftResolvent L z hz) where
  mem_domain := neumannShiftResolvent_mem_domain L z hz
  right_inverse := neumannShiftResolvent_right_inverse L z hz
  left_inverse := neumannShiftResolvent_left_inverse L z hz

theorem neumannShiftResolvent_isCompact (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) :
    IsCompactOperator (neumannShiftResolvent L z hz) :=
  (neumannResolvent_isCompact L).comp_clm (neumannFredholmInverse L z hz)

theorem IsNeumannResolvent.not_eigenvalue {z : ℂ}
    {S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L}
    (hS : IsNeumannResolvent L z S) (n : ℕ) : z ≠ (neumannEigenvalue L n : ℂ) := by
  intro hz
  subst z
  let u : (complexNeumannOperator hL.out).domain :=
    ⟨neumannCosineMode L n, neumannCosineMode_mem_domain L n⟩
  have hu : neumannShift L (neumannEigenvalue L n : ℂ) u = 0 := by
    rw [neumannShift_apply, complexNeumannOperator_cosine, sub_self]
  have h := hS.left_inverse u
  rw [hu, map_zero] at h
  exact (neumannCosineMode_orthonormal L).ne_zero n h.symm

theorem mem_neumannResolventSet_iff (z : ℂ) :
    z ∈ neumannResolventSet L ↔ ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ) := by
  constructor
  · rintro ⟨S, hS⟩ n
    exact IsNeumannResolvent.not_eigenvalue L hS n
  · intro hz
    exact ⟨neumannShiftResolvent L z hz, neumannShiftResolvent_spec L z hz⟩

/-- No spectral points remain besides the eigenvalues of the original operator. -/
theorem mem_neumannSpectrum_iff (z : ℂ) :
    z ∈ neumannSpectrum L ↔ ∃ n : ℕ, z = (neumannEigenvalue L n : ℂ) := by
  change (¬ z ∈ neumannResolventSet L) ↔ _
  simp only [mem_neumannResolventSet_iff, not_forall, not_not]

theorem neumannSpectrum_eq_range :
    neumannSpectrum L = Set.range (fun n : ℕ => (neumannEigenvalue L n : ℂ)) := by
  ext z
  rw [mem_neumannSpectrum_iff]
  exact exists_congr (fun _ => eq_comm)

theorem neumannResolvent_existsUnique (z : ℂ)
    (hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ)) :
    ∃! S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L,
      IsNeumannResolvent L z S := by
  refine ⟨neumannShiftResolvent L z hz, neumannShiftResolvent_spec L z hz, ?_⟩
  intro S hS
  exact IsNeumannResolvent.unique L hS (neumannShiftResolvent_spec L z hz)

theorem IsNeumannResolvent.isCompact {z : ℂ}
    {S : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L}
    (hS : IsNeumannResolvent L z S) : IsCompactOperator S := by
  have hz : ∀ n : ℕ, z ≠ (neumannEigenvalue L n : ℂ) :=
    IsNeumannResolvent.not_eigenvalue L hS
  rw [IsNeumannResolvent.unique L hS (neumannShiftResolvent_spec L z hz)]
  exact neumannShiftResolvent_isCompact L z hz

end GeneratedFoundations.Spectral
