module

public import GeneratedFoundations.Operations.SourceSpinCornerGroup
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The full centre of the generated source spin group

Two explicit determinant-one unitary matrices detect scalar matrices by
commutation. The determinant condition then leaves exactly the two scalar
elements of the actual source group. Thus the result classifies the whole
centre, rather than only verifying that the negative identity is central.

The quotient interface records precisely the two representatives identified
by the centre. It does not identify this quotient with an orthogonal group,
a projective space, or a covering of a geometric rotation group.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup

namespace GeneratedFoundations.Geometry.SourceSpinCentre

/-- A diagonal unitary with distinct eigenvalues. -/
def diagonalProbe : SU2 :=
  ⟨canonical Complex.I 0, canonical_mem_specialUnitary _ _ (by simp)⟩

/-- A unitary interchanging the two generated source directions. -/
def exchangeProbe : SU2 :=
  ⟨canonical 0 (-1), canonical_mem_specialUnitary _ _ (by simp)⟩

/-- Commuting with these two actual group elements forces a matrix to be
scalar. No unitary or determinant hypothesis on the tested matrix is needed. -/
theorem commuting_probes_scalar (M : Mat2)
    (hz : (diagonalProbe : Mat2) * M = M * (diagonalProbe : Mat2))
    (hy : (exchangeProbe : Mat2) * M = M * (exchangeProbe : Mat2)) :
    M = (M 0 0) • (1 : Mat2) := by
  have h01 : M 0 1 = 0 := by
    have hentry := congrArg (fun A : Mat2 => A 0 1) hz
    have hr := congrArg Complex.re hentry
    have hi := congrArg Complex.im hentry
    simp [diagonalProbe, canonical, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] at hr hi
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
  have h10 : M 1 0 = 0 := by
    have hentry := congrArg (fun A : Mat2 => A 1 0) hz
    have hr := congrArg Complex.re hentry
    have hi := congrArg Complex.im hentry
    simp [diagonalProbe, canonical, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] at hr hi
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
  have h11 : M 1 1 = M 0 0 := by
    have hentry := congrArg (fun A : Mat2 => A 0 1) hy
    simpa [exchangeProbe, canonical, Matrix.mul_apply, Fin.sum_univ_two] using hentry
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, h11]

theorem mem_centre_iff_scalar (U : SU2) :
    U ∈ Subgroup.center SU2 ↔ ∃ z : ℂ, (U : Mat2) = z • (1 : Mat2) := by
  constructor
  · intro hU
    refine ⟨(U : Mat2) 0 0, commuting_probes_scalar U.val ?_ ?_⟩
    · exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hU) diagonalProbe)
    · exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hU) exchangeProbe)
  · rintro ⟨z, hz⟩
    apply Subgroup.mem_center_iff.mpr
    intro V
    apply Subtype.ext
    change (V : Mat2) * (U : Mat2) = (U : Mat2) * (V : Mat2)
    rw [hz]
    simp

def negativeIdentity : SU2 :=
  ⟨canonical (-1) 0, canonical_mem_specialUnitary _ _ (by simp)⟩

@[simp]
theorem negativeIdentity_coe : (negativeIdentity : Mat2) = -(1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negativeIdentity, canonical]

theorem negativeIdentity_ne_one : negativeIdentity ≠ (1 : SU2) := by
  intro h
  have hentry := congrArg (fun U : SU2 => (U : Mat2) 0 0) h
  norm_num [negativeIdentity_coe] at hentry

@[simp]
theorem negativeIdentity_sq : negativeIdentity * negativeIdentity = 1 := by
  apply Subtype.ext
  change (negativeIdentity : Mat2) * (negativeIdentity : Mat2) = (1 : Mat2)
  simp

theorem negativeIdentity_mem_centre : negativeIdentity ∈ Subgroup.center SU2 :=
  (mem_centre_iff_scalar negativeIdentity).mpr ⟨-1, by simp⟩

/-- The determinant excludes every scalar except the two signs. -/
theorem mem_centre_iff (U : SU2) :
    U ∈ Subgroup.center SU2 ↔ U = 1 ∨ U = negativeIdentity := by
  constructor
  · intro hU
    obtain ⟨z, hz⟩ := (mem_centre_iff_scalar U).mp hU
    have hdet := (Matrix.mem_specialUnitaryGroup_iff.mp U.property).2
    have hz2 : z ^ 2 = 1 := by
      rw [hz] at hdet
      simpa [Matrix.det_smul] using hdet
    rcases sq_eq_one_iff.mp hz2 with hp | hn
    · left
      apply Subtype.ext
      change (U : Mat2) = (1 : Mat2)
      rw [hz, hp, one_smul]
    · right
      apply Subtype.ext
      rw [hz, hn, negativeIdentity_coe, neg_one_smul]
  · rintro (rfl | rfl)
    · exact (Subgroup.center SU2).one_mem
    · exact negativeIdentity_mem_centre

theorem centre_eq_pair :
    (Subgroup.center SU2 : Set SU2) = {1, negativeIdentity} := by
  ext U
  simp only [SetLike.mem_coe, mem_centre_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- The central subgroup has exactly two elements as a type. -/
theorem centre_card : Nat.card (Subgroup.center SU2) = 2 := by
  let e : Subgroup.center SU2 := ⟨1, (Subgroup.center SU2).one_mem⟩
  let n : Subgroup.center SU2 := ⟨negativeIdentity, negativeIdentity_mem_centre⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨e, n, ?_, ?_⟩
  · intro hen
    exact negativeIdentity_ne_one (congrArg Subtype.val hen).symm
  · apply Set.eq_univ_of_forall
    intro U
    rcases (mem_centre_iff U.val).mp U.property with hU | hU
    · exact Or.inl (Subtype.ext hU)
    · exact Or.inr (Subtype.ext hU)

abbrev CentralQuotient := SU2 ⧸ Subgroup.center SU2

def quotientMap : SU2 →* CentralQuotient := QuotientGroup.mk' (Subgroup.center SU2)

theorem quotientMap_kernel : quotientMap.ker = Subgroup.center SU2 :=
  QuotientGroup.ker_mk' (Subgroup.center SU2)

theorem quotientMap_eq_one_iff (U : SU2) :
    quotientMap U = 1 ↔ U = 1 ∨ U = negativeIdentity := by
  change (U : CentralQuotient) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, mem_centre_iff]

/-- Equality in the quotient identifies exactly a pair of opposite source
operations, with no further geometric identification of the quotient. -/
theorem quotientMap_eq_iff (U V : SU2) :
    quotientMap U = quotientMap V ↔ U = V ∨ U = negativeIdentity * V := by
  change (U : CentralQuotient) = (V : CentralQuotient) ↔ _
  rw [QuotientGroup.eq_iff_div_mem, mem_centre_iff, div_eq_one, div_eq_iff_eq_mul]

theorem quotientMap_matrix_eq_iff (U V : SU2) :
    quotientMap U = quotientMap V ↔ (U : Mat2) = (V : Mat2) ∨
      (U : Mat2) = -(V : Mat2) := by
  rw [quotientMap_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · right
      rw [h]
      change (negativeIdentity : Mat2) * (V : Mat2) = -(V : Mat2)
      simp
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · right
      apply Subtype.ext
      change (U : Mat2) = (negativeIdentity : Mat2) * (V : Mat2)
      simpa using h

end GeneratedFoundations.Geometry.SourceSpinCentre
