module

public import GeneratedFoundations.Physical.SourceChiralCarrier
public import GeneratedFoundations.Physical.SourceChargeLattice
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The primitive charge on the actual chiral source carrier

The relative generator acts on the retained colour and scalar source
factors. The right-spin generator acts on the original Gaussian phase
basis transported to the degree-one Haar carrier. Thus the charge weights
below are eigenvalues of the specified source operators, rather than a
separate assignment to sixteen coordinate labels.

Uniqueness compares the generators in the retained two-generator family,
with the integral, primitive and pointwise-vacuum conditions of the charge
lattice theorem. It does not classify arbitrary endomorphisms of the
matter space or independently chosen right-frame bundles.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct BigOperators
open GeneratedFoundations.Operations.SourceSpinCorner

namespace GeneratedFoundations.Physical.SourceMatterCharge

open SourceJointResponse SourceMinimalRepresentation SourceChiralCarrier
open SourceChargeLattice

def colourSector : ColourLabel → ColourSector
  | .inl _ => .coloured
  | .inr _ => .scalar

def spinSector : ChiralLabel → SpinSector
  | .inl _ => .left
  | .inr s => if s = 0 then .upper else .lower

def sectorOf (i : FullIndex) : Sector := (colourSector i.1, spinSector i.2)

theorem sectorOf_surjective : Function.Surjective sectorOf := by
  rintro ⟨c, s⟩
  cases c <;> cases s
  · exact ⟨(Sum.inl 0, Sum.inl 0), rfl⟩
  · exact ⟨(Sum.inl 0, Sum.inr 0), by simp [sectorOf, colourSector, spinSector]⟩
  · exact ⟨(Sum.inl 0, Sum.inr 1), by simp [sectorOf, colourSector, spinSector]⟩
  · exact ⟨(Sum.inr 0, Sum.inl 0), rfl⟩
  · exact ⟨(Sum.inr 0, Sum.inr 0), by simp [sectorOf, colourSector, spinSector]⟩
  · exact ⟨(Sum.inr 0, Sum.inr 1), by simp [sectorOf, colourSector, spinSector]⟩

/-- Repetition of the colour and left-spin weights changes no common divisor. -/
theorem primitive_on_fullBasis_iff (w : Sector → ℤ) :
    (∀ d : ℤ, (∀ i : FullIndex, d ∣ w (sectorOf i)) → IsUnit d) ↔
      PrimitiveWeights w := by
  constructor
  · intro h d hd
    exact h d (fun i => hd (sectorOf i))
  · intro h d hd
    apply h d
    intro p
    obtain ⟨i, rfl⟩ := sectorOf_surjective p
    exact hd i

def spinSign (s : SpinLabel) : ℤ := if s = 0 then 1 else -1

def twiceSpinMatrix : Mat2 := Matrix.diagonal ![1, -1]

def twiceSpin : Module.End ℂ S := SourceSpinIdentification.spinAction twiceSpinMatrix

theorem twiceSpin_basis (s : SpinLabel) :
    twiceSpin (spinBasis s) = (spinSign s : ℂ) • spinBasis s := by
  change SourceSpinIdentification.spinAction twiceSpinMatrix
    (SourceSpinIdentification.spinBasis s) = _
  rw [SourceSpinIdentification.spinAction_basis]
  fin_cases s <;> simp [twiceSpinMatrix, spinSign, spinBasis]

theorem sourceBasis_relative (a b : ℤ) (c : ColourLabel) (s : SpinLabel) :
    relativeSource a b (sourceBasis (c, s)) =
      (relativeWeight a b (colourSector c) : ℂ) • sourceBasis (c, s) := by
  apply WithLp.ofLp_injective 2
  cases c <;>
    simp [relativeSource_apply, colourSector, relativeWeight, WithLp.ofLp_smul]

theorem sourceBasis_twiceSpin (c : ColourLabel) (s : SpinLabel) :
    spinOnSource twiceSpin (sourceBasis (c, s)) =
      (spinSign s : ℂ) • sourceBasis (c, s) := by
  apply WithLp.ofLp_injective 2
  cases c <;>
    simp [twiceSpin_basis, TensorProduct.tmul_smul, WithLp.ofLp_smul]

theorem diagonalBlocks_left (A B : Module.End ℂ SourceCarrier) (x : SourceCarrier) :
    diagonalBlocks A B (leftInclusion x) = leftInclusion (A x) := by
  apply WithLp.ofLp_injective 2
  simp

theorem diagonalBlocks_right (A B : Module.End ℂ SourceCarrier) (x : SourceCarrier) :
    diagonalBlocks A B (rightInclusion x) = rightInclusion (B x) := by
  apply WithLp.ofLp_injective 2
  simp

/-- The relative generator already classified on the actual minimal carrier. -/
def relativeGenerator : Module.End ℂ FullMatter :=
  diagonalBlocks primitiveRelativeSource primitiveRelativeSource

/-- Twice the right-spin generator is zero on the left-labelled source copy. -/
def twiceRightGenerator : Module.End ℂ FullMatter :=
  diagonalBlocks 0 (spinOnSource twiceSpin)

def rightGenerator : Module.End ℂ FullMatter := (1 / 2 : ℂ) • twiceRightGenerator

def chargeOperator (r β : ℤ) : Module.End ℂ FullMatter :=
  (r : ℂ) • twiceRightGenerator + (β : ℂ) • relativeGenerator

def realChargeOperator (α β : ℝ) : Module.End ℂ FullMatter :=
  (α : ℂ) • rightGenerator + (β : ℂ) • relativeGenerator

def generatedChargeOperator : Module.End ℂ FullMatter := chargeOperator 3 1

def hyperchargeOperator : Module.End ℂ FullMatter :=
  (1 / 6 : ℂ) • generatedChargeOperator

theorem relativeGenerator_basis (i : FullIndex) :
    relativeGenerator (fullBasis i) =
      (baseRelativeWeight (colourSector i.1) : ℂ) • fullBasis i := by
  rcases i with ⟨c, s | s⟩ <;>
    simp [relativeGenerator, primitiveRelativeSource, diagonalBlocks_left,
      diagonalBlocks_right, sourceBasis_relative, baseRelativeWeight]

theorem twiceRightGenerator_basis (i : FullIndex) :
    twiceRightGenerator (fullBasis i) =
      (twiceRightWeight (spinSector i.2) : ℂ) • fullBasis i := by
  rcases i with ⟨c, s | s⟩
  · simp [twiceRightGenerator, diagonalBlocks_left, spinSector, twiceRightWeight]
  · simp only [fullBasis_right, twiceRightGenerator, diagonalBlocks_right,
      sourceBasis_twiceSpin, map_smul]
    fin_cases s <;> simp [spinSign, spinSector, twiceRightWeight]

theorem chargeOperator_basis (r β : ℤ) (i : FullIndex) :
    chargeOperator r β (fullBasis i) =
      (chargeWeight r β (sectorOf i) : ℂ) • fullBasis i := by
  simp only [chargeOperator, LinearMap.add_apply, LinearMap.smul_apply,
    twiceRightGenerator_basis, relativeGenerator_basis, smul_smul, ← add_smul]
  congr 1
  simp [chargeWeight, sectorOf]

theorem generatedChargeOperator_basis (i : FullIndex) :
    generatedChargeOperator (fullBasis i) =
      (generatedCharge (sectorOf i) : ℂ) • fullBasis i :=
  chargeOperator_basis 3 1 i

theorem realChargeOperator_basis (α β : ℝ) (i : FullIndex) :
    realChargeOperator α β (fullBasis i) =
      (realCharge α β (sectorOf i) : ℂ) • fullBasis i := by
  simp only [realChargeOperator, rightGenerator, LinearMap.add_apply,
    LinearMap.smul_apply, twiceRightGenerator_basis, relativeGenerator_basis,
    smul_smul, ← add_smul]
  congr 1
  simp only [realCharge, sectorOf, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_intCast]
  ring

theorem generatedChargeOperator_eq_generators :
    generatedChargeOperator = (6 : ℂ) • rightGenerator + relativeGenerator := by
  norm_num [generatedChargeOperator, chargeOperator, rightGenerator, smul_smul]

theorem realChargeOperator_integral (r β : ℤ) :
    realChargeOperator (2 * (r : ℝ)) (β : ℝ) = chargeOperator r β := by
  simp only [realChargeOperator, rightGenerator, chargeOperator, smul_smul]
  push_cast
  congr 1
  congr 1
  ring

theorem chargeOperator_oriented_unique {r β : ℤ}
    (hp : PrimitiveCharge r β)
    (hv : chargeWeight r β (.scalar, .upper) = 0) (hβ : 0 < β) :
    chargeOperator r β = generatedChargeOperator := by
  obtain ⟨rfl, rfl⟩ := oriented_fixedUpper_unique hp hv hβ
  rfl

theorem realChargeOperator_oriented_unique {α β : ℝ} {w : Sector → ℤ}
    (hw : IntegralRealization α β w) (hp : PrimitiveWeights w)
    (hv : realCharge α β (.scalar, .upper) = 0) (hβ : 0 < β) :
    realChargeOperator α β = generatedChargeOperator := by
  obtain ⟨rfl, rfl, _⟩ := oriented_real_vacuum_unique hw hp hv hβ
  have hi := realChargeOperator_integral 3 1
  norm_num at hi
  exact hi

def neutralIndex : FullIndex := (Sum.inr 0, Sum.inr 0)

def neutralVector : FullMatter := fullBasis neutralIndex

def neutralLine : Submodule ℂ FullMatter := ℂ ∙ neutralVector

theorem neutralVector_ne_zero : neutralVector ≠ 0 :=
  fullBasis.toBasis.ne_zero neutralIndex

theorem neutralVector_source :
    neutralVector = rightInclusion
      (WithLp.toLp 2 (0, lineBasis 0 ⊗ₜ[ℂ] spinBasis 0)) := by
  simp [neutralVector, neutralIndex]

theorem chargeOperator_annihilates_vacuum_iff (r β : ℤ) :
    chargeOperator r β neutralVector = 0 ↔
      chargeWeight r β (.scalar, .upper) = 0 := by
  rw [neutralVector, chargeOperator_basis]
  change (chargeWeight r β (.scalar, .upper) : ℂ) • fullBasis neutralIndex = 0 ↔ _
  rw [smul_eq_zero]
  have hne : fullBasis neutralIndex ≠ 0 := neutralVector_ne_zero
  simp only [hne, or_false, Int.cast_eq_zero]

theorem realChargeOperator_annihilates_vacuum_iff (α β : ℝ) :
    realChargeOperator α β neutralVector = 0 ↔
      realCharge α β (.scalar, .upper) = 0 := by
  rw [neutralVector, realChargeOperator_basis]
  change (realCharge α β (.scalar, .upper) : ℂ) • fullBasis neutralIndex = 0 ↔ _
  rw [smul_eq_zero]
  have hne : fullBasis neutralIndex ≠ 0 := neutralVector_ne_zero
  simp only [hne, or_false, Complex.ofReal_eq_zero]

theorem chargeOperator_unique_of_source_vacuum {r β : ℤ}
    (hp : PrimitiveCharge r β) (hv : chargeOperator r β neutralVector = 0)
    (hβ : 0 < β) : chargeOperator r β = generatedChargeOperator :=
  chargeOperator_oriented_unique hp ((chargeOperator_annihilates_vacuum_iff r β).mp hv) hβ

theorem realChargeOperator_unique_of_source_vacuum {α β : ℝ} {w : Sector → ℤ}
    (hw : IntegralRealization α β w) (hp : PrimitiveWeights w)
    (hv : realChargeOperator α β neutralVector = 0) (hβ : 0 < β) :
    realChargeOperator α β = generatedChargeOperator :=
  realChargeOperator_oriented_unique hw hp
    ((realChargeOperator_annihilates_vacuum_iff α β).mp hv) hβ

theorem generatedCharge_index_zero_iff (i : FullIndex) :
    generatedCharge (sectorOf i) = 0 ↔ i = neutralIndex := by
  rw [generatedCharge_zero_iff]
  rcases i with ⟨c | c, s | s⟩
  · simp [sectorOf, colourSector, spinSector, neutralIndex]
  · fin_cases s <;> simp [sectorOf, colourSector, spinSector, neutralIndex]
  · simp [sectorOf, colourSector, spinSector, neutralIndex]
  · fin_cases c
    fin_cases s <;> simp [sectorOf, colourSector, spinSector, neutralIndex]

@[simp] theorem generatedCharge_neutral : generatedChargeOperator neutralVector = 0 := by
  rw [neutralVector, generatedChargeOperator_basis]
  simp [neutralIndex, sectorOf, colourSector, spinSector, generatedCharge]

theorem hyperchargeOperator_basis (i : FullIndex) :
    hyperchargeOperator (fullBasis i) =
      ((generatedCharge (sectorOf i) : ℂ) / 6) • fullBasis i := by
  rw [hyperchargeOperator, LinearMap.smul_apply, generatedChargeOperator_basis, smul_smul]
  congr 1
  ring

private theorem coefficient_of_eigenbasis (A : Module.End ℂ FullMatter)
    (w : FullIndex → ℂ) (hA : ∀ i, A (fullBasis i) = w i • fullBasis i)
    (x : FullMatter) (i : FullIndex) :
    fullBasis.repr (A x) i = w i * fullBasis.repr x i := by
  nth_rw 1 [← fullBasis.sum_repr x]
  simp [map_sum, map_smul, hA, OrthonormalBasis.repr_self, Pi.single_apply,
    mul_comm]

theorem chargeOperator_coefficient (r β : ℤ) (x : FullMatter) (i : FullIndex) :
    fullBasis.repr (chargeOperator r β x) i =
      (chargeWeight r β (sectorOf i) : ℂ) * fullBasis.repr x i :=
  coefficient_of_eigenbasis _ _ (chargeOperator_basis r β) x i

private theorem kernel_of_one_zero (A : Module.End ℂ FullMatter)
    (w : FullIndex → ℂ) (hA : ∀ i, A (fullBasis i) = w i • fullBasis i)
    (hw : ∀ i, w i = 0 ↔ i = neutralIndex) : LinearMap.ker A = neutralLine := by
  ext x
  constructor
  · intro hx
    have hAx : A x = 0 := hx
    have hc : ∀ i, i ≠ neutralIndex → fullBasis.repr x i = 0 := by
      intro i hi
      have hiw : w i ≠ 0 := fun hz => hi ((hw i).mp hz)
      have h := coefficient_of_eigenbasis A w hA x i
      rw [hAx, map_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hiw
    apply Submodule.mem_span_singleton.mpr
    refine ⟨fullBasis.repr x neutralIndex, ?_⟩
    apply fullBasis.repr.injective
    apply PiLp.ext
    intro i
    by_cases hi : i = neutralIndex
    · subst i
      simp [neutralVector, OrthonormalBasis.repr_self]
    · simp [neutralVector, OrthonormalBasis.repr_self, hi, hc i hi]
  · intro hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change A (c • neutralVector) = 0
    rw [map_smul, neutralVector, hA, (hw neutralIndex).mpr rfl]
    simp

theorem generatedChargeOperator_kernel :
    LinearMap.ker generatedChargeOperator = neutralLine := by
  apply kernel_of_one_zero generatedChargeOperator
    (fun i => (generatedCharge (sectorOf i) : ℂ)) generatedChargeOperator_basis
  intro i
  rw [Int.cast_eq_zero, generatedCharge_index_zero_iff]

theorem neutralLine_finrank : Module.finrank ℂ neutralLine = 1 :=
  finrank_span_singleton neutralVector_ne_zero

theorem chargedQuotient_finrank : Module.finrank ℂ (FullMatter ⧸ neutralLine) = 15 := by
  have h := neutralLine.finrank_quotient_add_finrank
  rw [neutralLine_finrank, fullMatter_finrank] at h
  omega

/-- A scalar response on the coloured source summand, with zero scalar-line
response. Nonnegativity is a parameter condition. Its identification with
a specified normalized colour Casimir requires a separate choice of `κ`. -/
def colourCasimir (κ : ℝ) : Module.End ℂ FullMatter :=
  (κ : ℂ) • diagonalBlocks (relativeSource 1 0) (relativeSource 1 0)

def colourCasimirWeight (κ : ℝ) (c : ColourLabel) : ℝ :=
  match c with
  | .inl _ => κ
  | .inr _ => 0

private theorem relativeBlocks_basis (a b : ℤ) (i : FullIndex) :
    diagonalBlocks (relativeSource a b) (relativeSource a b) (fullBasis i) =
      (relativeWeight a b (colourSector i.1) : ℂ) • fullBasis i := by
  rcases i with ⟨c, s | s⟩
  · exact (congrArg (diagonalBlocks (relativeSource a b) (relativeSource a b))
      (fullBasis_left c s)).trans
      ((diagonalBlocks_left _ _ (sourceBasis (c, s))).trans
        ((congrArg leftInclusion (sourceBasis_relative a b c s)).trans
          ((map_smul leftInclusion (relativeWeight a b (colourSector c) : ℂ)
            (sourceBasis (c, s))).trans
            (congrArg (fun x : FullMatter =>
              (relativeWeight a b (colourSector c) : ℂ) • x) (fullBasis_left c s).symm))))
  · exact (congrArg (diagonalBlocks (relativeSource a b) (relativeSource a b))
      (fullBasis_right c s)).trans
      ((diagonalBlocks_right _ _ (sourceBasis (c, s))).trans
        ((congrArg rightInclusion (sourceBasis_relative a b c s)).trans
          ((map_smul rightInclusion (relativeWeight a b (colourSector c) : ℂ)
            (sourceBasis (c, s))).trans
            (congrArg (fun x : FullMatter =>
              (relativeWeight a b (colourSector c) : ℂ) • x) (fullBasis_right c s).symm))))

theorem colourCasimir_basis (κ : ℝ) (i : FullIndex) :
    colourCasimir κ (fullBasis i) =
      (colourCasimirWeight κ i.1 : ℂ) • fullBasis i := by
  rw [colourCasimir, LinearMap.smul_apply, relativeBlocks_basis, smul_smul]
  have hw : (κ : ℂ) * (relativeWeight 1 0 (colourSector i.1) : ℂ) =
      (colourCasimirWeight κ i.1 : ℂ) := by
    cases i.1 <;> simp [colourSector, relativeWeight, colourCasimirWeight]
  exact congrArg (fun c : ℂ => c • fullBasis i) hw

def responseWeight (κ : ℝ) (i : FullIndex) : ℝ :=
  colourCasimirWeight κ i.1 + ((generatedCharge (sectorOf i) : ℝ) / 6) ^ 2

def chargedResponse (κ : ℝ) : Module.End ℂ FullMatter :=
  colourCasimir κ + hyperchargeOperator * hyperchargeOperator

theorem chargedResponse_basis (κ : ℝ) (i : FullIndex) :
    chargedResponse κ (fullBasis i) =
      (responseWeight κ i : ℂ) • fullBasis i := by
  simp only [chargedResponse, LinearMap.add_apply, Module.End.mul_apply,
    colourCasimir_basis, hyperchargeOperator_basis, map_smul, smul_smul, ← add_smul]
  congr 1
  simp only [responseWeight, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_intCast, pow_two]

theorem colourCasimirWeight_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (c : ColourLabel) :
    0 ≤ colourCasimirWeight κ c := by
  cases c <;> simp [colourCasimirWeight, hκ]

theorem responseWeight_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (i : FullIndex) :
    0 ≤ responseWeight κ i :=
  add_nonneg (colourCasimirWeight_nonneg hκ i.1) (sq_nonneg _)

theorem responseWeight_zero_iff {κ : ℝ} (hκ : 0 ≤ κ) (i : FullIndex) :
    responseWeight κ i = 0 ↔ i = neutralIndex := by
  constructor
  · intro h
    have hc := colourCasimirWeight_nonneg hκ i.1
    have hs := sq_nonneg ((generatedCharge (sectorOf i) : ℝ) / 6)
    have hsq : ((generatedCharge (sectorOf i) : ℝ) / 6) ^ 2 = 0 := by
      dsimp [responseWeight] at h
      linarith
    have hz : (generatedCharge (sectorOf i) : ℝ) = 0 := by
      have hd := (sq_eq_zero_iff).mp hsq
      linarith
    apply (generatedCharge_index_zero_iff i).mp
    exact_mod_cast hz
  · rintro rfl
    simp [responseWeight, neutralIndex, colourCasimirWeight, sectorOf,
      colourSector, spinSector, generatedCharge]

theorem chargedResponse_kernel {κ : ℝ} (hκ : 0 ≤ κ) :
    LinearMap.ker (chargedResponse κ) = neutralLine := by
  apply kernel_of_one_zero (chargedResponse κ)
    (fun i => (responseWeight κ i : ℂ)) (chargedResponse_basis κ)
  intro i
  rw [Complex.ofReal_eq_zero, responseWeight_zero_iff hκ]

theorem chargedResponse_quotient_finrank {κ : ℝ} (hκ : 0 ≤ κ) :
    Module.finrank ℂ (FullMatter ⧸ LinearMap.ker (chargedResponse κ)) = 15 := by
  rw [chargedResponse_kernel hκ]
  exact chargedQuotient_finrank

end GeneratedFoundations.Physical.SourceMatterCharge
