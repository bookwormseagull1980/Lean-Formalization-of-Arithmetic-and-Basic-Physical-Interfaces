module

public import GeneratedFoundations.Geometry.SourceScalarResponse
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Ring.Commute

/-!
# The effective action on the generated reversal-real response

Two independent source frames act on a reversal-real matrix by left and
right multiplication. The kernel is calculated on all response matrices,
before taking any quotient: precisely the simultaneous central sign is
invisible. The quotient is then constructed from this proved kernel, and
its induced action is faithful and unique.

This is a quotient of the response action. It does not identify the complete
state representations of a frame and its central relift. In particular, it
does not assign the physical charged representation's kernel to another
carrier.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Operations.ReversalRealConnector
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceScalarResponse

namespace GeneratedFoundations.Geometry.SourceFrameQuotient

def negative : SU2 :=
  ⟨canonical (-1) 0, canonical_mem_specialUnitary (-1) 0 (by norm_num)⟩

@[simp] theorem negative_matrix : (negative : Mat2) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negative, canonical]

def centralSign : Frame := (negative, negative)

theorem centralSign_sq : centralSign * centralSign = 1 := by
  apply Prod.ext <;> apply Subtype.ext <;>
    change (negative : Mat2) * (negative : Mat2) = 1 <;> simp

theorem centralSign_ne_one : centralSign ≠ 1 := by
  intro h
  have he := congrArg (fun g : Frame => (g.1 : Mat2) 0 0) h
  norm_num [centralSign] at he

theorem centralSign_commute (g : Frame) : centralSign * g = g * centralSign := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [centralSign]

theorem frameMatrix_fixed_iff (g : Frame) (M : Mat2) :
    frameMatrix g M = M ↔ (g.1 : Mat2) * M = M * (g.2 : Mat2) := by
  have hleft : (g.2 : Mat2).conjTranspose * (g.2 : Mat2) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2.property).1.1
  have hright : (g.2 : Mat2) * (g.2 : Mat2).conjTranspose = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2.property).1.2
  constructor
  · intro h
    have he := congrArg (fun A : Mat2 => A * (g.2 : Mat2)) h
    simpa only [frameMatrix, mul_assoc, hleft, mul_one] using he
  · intro h
    rw [frameMatrix, h, mul_assoc, hright, mul_one]

def permutation (g : Frame) : Equiv.Perm Spinor where
  toFun := frameDoublet g
  invFun := frameDoublet g⁻¹
  left_inv := frameDoublet_inverse g
  right_inv v := by
    simpa only [inv_inv] using frameDoublet_inverse g⁻¹ v

def response : Frame →* Equiv.Perm Spinor where
  toFun := permutation
  map_one' := by
    apply Equiv.ext
    intro v
    exact frameDoublet_one v
  map_mul' g h := by
    apply Equiv.ext
    intro v
    exact frameDoublet_mul g h v

@[simp] theorem response_apply (g : Frame) (v : Spinor) :
    response g v = frameDoublet g v := rfl

theorem centralSign_response (v : Spinor) : frameDoublet centralSign v = v := by
  apply connectorOfDoublet_injective
  rw [connectorOfDoublet_frameDoublet]
  simp [frameMatrix, centralSign]

private theorem fixed_reversalReal (g : Frame)
    (hg : ∀ v : Spinor, frameDoublet g v = v)
    (M : Mat2) (hM : ReversalReal M) : frameMatrix g M = M := by
  obtain ⟨v, rfl, _⟩ := (reversalReal_iff_existsUnique_doublet M).mp hM
  rw [← connectorOfDoublet_frameDoublet, hg]

/-- The simultaneous sign is the whole kernel, not merely one invisible
element. The proof tests the identity and both native reversal-real axes. -/
theorem response_kernel_iff (g : Frame) :
    (∀ v : Spinor, frameDoublet g v = v) ↔ g = 1 ∨ g = centralSign := by
  constructor
  · intro hg
    have h1 := (frameMatrix_fixed_iff g 1).mp
      (fixed_reversalReal g hg 1 (by rw [reversalReal_iff_entries]; simp))
    have hsame : (g.1 : Mat2) = (g.2 : Mat2) := by simpa using h1
    have heps := (frameMatrix_fixed_iff g (canonicalMatrix 0 1)).mp
      (fixed_reversalReal g hg _ (canonicalMatrix_reversalReal 0 1))
    have hdiag := (frameMatrix_fixed_iff g (canonicalMatrix Complex.I 0)).mp
      (fixed_reversalReal g hg _ (canonicalMatrix_reversalReal Complex.I 0))
    rw [← hsame] at heps hdiag
    have hb := congrArg (fun A : Mat2 => A 0 1) hdiag
    simp [canonicalMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hb
    have hzero : (g.1 : Mat2) 0 1 = 0 := by
      have hh : (2 * Complex.I) * (g.1 : Mat2) 0 1 = 0 := by
        linear_combination -hb
      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
    have hd := congrArg (fun A : Mat2 => A 0 1) heps
    simp [canonicalMatrix, Matrix.mul_apply, Fin.sum_univ_two] at hd
    have hlower : (g.1 : Mat2) 1 0 = 0 := by
      have he := congrArg (fun A : Mat2 => A 1 0)
        (specialUnitary_entries (g.1 : Mat2) g.1.property)
      simpa [canonical, hzero] using he
    have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp g.1.property).2
    have hsquare : ((g.1 : Mat2) 0 0) ^ 2 = 1 := by
      simpa [Matrix.det_fin_two, hzero, hlower, ← hd, pow_two] using hdet
    have hform : (g.1 : Mat2) = (g.1 : Mat2) 0 0 • (1 : Mat2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hzero, hlower, hd]
    rcases sq_eq_one_iff.mp hsquare with hplus | hminus
    · left
      apply Prod.ext <;> apply Subtype.ext
      · simpa [hplus] using hform
      · simpa [hplus] using hsame.symm.trans hform
    · right
      apply Prod.ext <;> apply Subtype.ext
      · change (g.1 : Mat2) = (negative : Mat2)
        simpa [hminus] using hform
      · change (g.2 : Mat2) = (negative : Mat2)
        simpa [hminus] using hsame.symm.trans hform
  · rintro (rfl | rfl)
    · exact frameDoublet_one
    · exact centralSign_response

theorem mem_response_kernel (g : Frame) :
    g ∈ response.ker ↔ g = 1 ∨ g = centralSign := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact (response_kernel_iff g).mp (fun v => Equiv.congr_fun h v)
  · intro h
    apply Equiv.ext
    intro v
    exact (response_kernel_iff g).mpr h v

theorem centralSign_order : orderOf centralSign = 2 := by
  apply (orderOf_eq_iff (by norm_num : 0 < (2 : ℕ))).mpr
  refine ⟨by simpa [pow_two] using centralSign_sq, ?_⟩
  intro n hn hpos he
  have hn1 : n = 1 := by omega
  subst n
  exact centralSign_ne_one (by simpa using he)

theorem kernel_eq_zpowers : response.ker = Subgroup.zpowers centralSign := by
  apply le_antisymm
  · intro g hg
    rcases (mem_response_kernel g).mp hg with rfl | rfl
    · exact (Subgroup.zpowers centralSign).one_mem
    · exact Subgroup.mem_zpowers centralSign
  · exact Subgroup.zpowers_le.mpr ((mem_response_kernel centralSign).mpr (Or.inr rfl))

theorem kernel_card : Nat.card response.ker = 2 := by
  rw [kernel_eq_zpowers, Nat.card_zpowers, centralSign_order]

abbrev EffectiveFrame := Frame ⧸ response.ker

def quotientMap : Frame →* EffectiveFrame := QuotientGroup.mk' response.ker

def effectiveResponse : EffectiveFrame →* Equiv.Perm Spinor := QuotientGroup.kerLift response

theorem effectiveResponse_faithful : Function.Injective effectiveResponse :=
  QuotientGroup.kerLift_injective response

@[simp] theorem effectiveResponse_quotientMap (g : Frame) :
    effectiveResponse (quotientMap g) = response g := rfl

/-- The effective action is determined by its value on the actual frames. -/
theorem effectiveResponse_unique (R : EffectiveFrame →* Equiv.Perm Spinor)
    (hR : ∀ g, R (quotientMap g) = response g) : R = effectiveResponse := by
  apply MonoidHom.ext
  intro q
  induction q using Quotient.inductionOn' with
  | h g => exact hR g

theorem central_relift_response (g : Frame) (v : Spinor) :
    frameDoublet (centralSign * g) v = frameDoublet g v := by
  rw [frameDoublet_mul, centralSign_response]

end GeneratedFoundations.Geometry.SourceFrameQuotient
