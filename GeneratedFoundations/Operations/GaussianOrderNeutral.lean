module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Order-neutral affine quadratic expressions

The ordering involution has a unique fixed point when the two terms are
distinct.  The affine classification is independent of the operator
domain on which an annihilation-creation pair realizes the two terms.
-/

@[expose] public section

namespace GeneratedFoundations.Operations.GaussianOrderNeutral

def orderSwap (α : ℝ) : ℝ := 1 - α

theorem orderSwap_involutive : Function.Involutive orderSwap := by
  intro α
  simp [orderSwap]

theorem orderSwap_fixed_iff (α : ℝ) : orderSwap α = α ↔ α = 1 / 2 := by
  dsimp [orderSwap]
  constructor <;> intro h <;> linarith

theorem orderSwap_preserves_unitInterval {α : ℝ} (hα : α ∈ Set.Icc 0 1) :
    orderSwap α ∈ Set.Icc 0 1 := by
  rcases hα with ⟨h0, h1⟩
  constructor <;> dsimp [orderSwap] <;> linarith

theorem orderNeutral_weight_existsUnique :
    ∃! α : ℝ, α ∈ Set.Icc 0 1 ∧ orderSwap α = α := by
  refine ⟨1 / 2, ⟨by norm_num, by norm_num [orderSwap]⟩, ?_⟩
  intro α hα
  exact (orderSwap_fixed_iff α).mp hα.2

section AffineExpressions

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def quadraticClosure (x y : E) (α : ℝ) : E :=
  α • x + (1 - α) • y

theorem quadraticClosure_eq_shift (x y : E) (α : ℝ) :
    quadraticClosure x y α = x + (1 - α) • (y - x) := by
  simp only [quadraticClosure, sub_smul, one_smul, smul_sub]
  abel

theorem quadraticClosure_orderSwap (x y : E) (α : ℝ) :
    quadraticClosure x y (orderSwap α) = quadraticClosure y x α := by
  simp only [quadraticClosure, orderSwap, sub_sub_cancel]
  exact add_comm _ _

theorem quadraticClosure_eq_iff (x y : E) (hxy : x ≠ y) (α β : ℝ) :
    quadraticClosure x y α = quadraticClosure x y β ↔ α = β := by
  rw [quadraticClosure_eq_shift, quadraticClosure_eq_shift, add_left_cancel_iff]
  constructor
  · intro h
    have hgap : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
    have hz : ((1 - α) - (1 - β)) • (y - x) = 0 := by
      rw [sub_smul, h, sub_self]
    have hs : (1 - α) - (1 - β) = 0 :=
      (smul_eq_zero.mp hz).resolve_right hgap
    linarith
  · intro h
    subst β
    rfl

theorem quadraticClosure_injective (x y : E) (hxy : x ≠ y) :
    Function.Injective (quadraticClosure x y) := by
  intro α β h
  exact (quadraticClosure_eq_iff x y hxy α β).mp h

theorem quadraticClosure_orderNeutral_iff (x y : E) (hxy : x ≠ y) (α : ℝ) :
    quadraticClosure x y α = quadraticClosure x y (orderSwap α) ↔
      α = 1 / 2 := by
  rw [quadraticClosure_eq_iff x y hxy]
  constructor
  · intro h
    exact (orderSwap_fixed_iff α).mp h.symm
  · intro h
    exact ((orderSwap_fixed_iff α).mpr h).symm

theorem quadraticClosure_midpoint (x y : E) :
    quadraticClosure x y (1 / 2) = (1 / 2 : ℝ) • (x + y) := by
  norm_num [quadraticClosure, smul_add]

theorem quadraticClosure_orderNeutral_value (x y : E) (hxy : x ≠ y)
    (α : ℝ)
    (hα : quadraticClosure x y α = quadraticClosure x y (orderSwap α)) :
    quadraticClosure x y α = (1 / 2 : ℝ) • (x + y) := by
  rw [(quadraticClosure_orderNeutral_iff x y hxy α).mp hα]
  exact quadraticClosure_midpoint x y

theorem quadraticClosure_orderNeutral_existsUnique (x y : E) (hxy : x ≠ y) :
    ∃! α : ℝ, α ∈ Set.Icc 0 1 ∧
      quadraticClosure x y α = quadraticClosure x y (orderSwap α) := by
  refine ⟨1 / 2, ⟨by norm_num, ?_⟩, ?_⟩
  · exact (quadraticClosure_orderNeutral_iff x y hxy (1 / 2)).mpr rfl
  · intro α hα
    exact (quadraticClosure_orderNeutral_iff x y hxy α).mp hα.2

omit [Module ℝ E] in
theorem distinct_of_nonzero_gap (x y gap : E) (hgap : gap ≠ 0)
    (hrel : y = x + gap) : x ≠ y := by
  intro hxy
  apply hgap
  calc
    gap = y - x := by rw [hrel]; abel
    _ = 0 := sub_eq_zero.mpr hxy.symm

theorem quadraticClosure_midpoint_of_gap (x y gap : E) (hrel : y = x + gap) :
    quadraticClosure x y (1 / 2) = x + (1 / 2 : ℝ) • gap := by
  rw [quadraticClosure_eq_shift, hrel]
  have hcancel : x + gap - x = gap := by abel
  rw [hcancel]
  norm_num

end AffineExpressions

end GeneratedFoundations.Operations.GaussianOrderNeutral
