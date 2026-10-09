module

public import GeneratedFoundations.Operations.GibbsExponentialDifferentiation
public import GeneratedFoundations.Operations.PreparedTraceForm

/-!
# The finite Gibbs trace form

At a real diagonal reference, the exponential derivative gives a symmetric
trace pairing. Subtracting the weighted mean removes precisely the scalar
direction. Positive divided differences express the resulting form as a sum
of weighted squared matrix entries. This file treats the form and its rank;
its identification with the logarithmic response Hessian is separate.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace GeneratedFoundations.Operations.GibbsTraceForm

open PreparedTraceForm (Mat Hermitian Traceless realTrace)
open GibbsExponentialDifferentiation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def Z (a : ι → ℝ) : ℝ := ∑ i, Real.exp (a i)

omit [DecidableEq ι] in
theorem Z_pos (a : ι → ℝ) : 0 < Z a :=
  Finset.sum_pos (fun i _ => Real.exp_pos (a i)) Finset.univ_nonempty

omit [DecidableEq ι] in
theorem Z_ne_zero (a : ι → ℝ) : Z a ≠ 0 := ne_of_gt (Z_pos a)

def weightedTrace (a : ι → ℝ) : Mat ι →ₗ[ℝ] ℝ where
  toFun K := realTrace ι (realDiagonal (fun i => Real.exp (a i)) * K)
  map_add' K L := by simp only [mul_add, map_add]
  map_smul' r K := by simp only [mul_smul_comm, map_smul, RingHom.id_apply]

omit [Nonempty ι] in
@[simp] theorem weightedTrace_apply (a : ι → ℝ) (K : Mat ι) :
    weightedTrace a K = realTrace ι (realDiagonal (fun i => Real.exp (a i)) * K) := rfl

omit [Nonempty ι] in
theorem weightedTrace_eq_sum (a : ι → ℝ) (K : Mat ι) :
    weightedTrace a K = ∑ i, Real.exp (a i) * (K i i).re := by
  change Complex.reAddGroupHom (∑ i, (realDiagonal (fun i => Real.exp (a i)) * K) i i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((realDiagonal (fun i => Real.exp (a i)) * K) i i).re = _
  simp only [realDiagonal, Matrix.diagonal_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

omit [Nonempty ι] in
@[simp] theorem weightedTrace_one (a : ι → ℝ) : weightedTrace a (1 : Mat ι) = Z a := by
  simp only [weightedTrace_eq_sum, Matrix.one_apply_eq, Complex.one_re, mul_one, Z]

def mean (a : ι → ℝ) : Mat ι →ₗ[ℝ] ℝ := (Z a)⁻¹ • weightedTrace a

omit [Nonempty ι] in
@[simp] theorem mean_apply (a : ι → ℝ) (K : Mat ι) :
    mean a K = weightedTrace a K / Z a := by
  simp only [mean, LinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

@[simp] theorem mean_one (a : ι → ℝ) : mean a (1 : Mat ι) = 1 := by
  rw [mean_apply, weightedTrace_one, div_self (Z_ne_zero a)]

@[simp] theorem mean_scalar (a : ι → ℝ) (r : ℝ) : mean a (r • (1 : Mat ι)) = r := by
  rw [map_smul, mean_one, smul_eq_mul, mul_one]

def centered (a : ι → ℝ) (K : Mat ι) : Mat ι := K - mean a K • (1 : Mat ι)

omit [Nonempty ι] in
theorem centered_isHermitian (a : ι → ℝ) {K : Mat ι} (hK : K.IsHermitian) :
    (centered a K).IsHermitian :=
  hK.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))

@[simp] theorem centered_scalar (a : ι → ℝ) (r : ℝ) :
    centered a (r • (1 : Mat ι)) = 0 := by
  rw [centered, mean_scalar, sub_self]

theorem centered_eq_zero_iff (a : ι → ℝ) (K : Mat ι) :
    centered a K = 0 ↔ ∃ r : ℝ, K = r • (1 : Mat ι) := by
  constructor
  · intro h
    exact ⟨mean a K, sub_eq_zero.mp h⟩
  · rintro ⟨r, rfl⟩
    exact centered_scalar a r

@[simp] theorem weightedTrace_centered (a : ι → ℝ) (K : Mat ι) :
    weightedTrace a (centered a K) = 0 := by
  simp only [centered, map_sub, map_smul, weightedTrace_one, smul_eq_mul, mean_apply]
  field_simp [Z_ne_zero a]
  ring

def responsePairing (a : ι → ℝ) : LinearMap.BilinForm ℝ (Mat ι) where
  toFun K :=
    { toFun L := realTrace ι (diagonalDerivative a K * L)
      map_add' L M := by simp only [mul_add, map_add]
      map_smul' r L := by simp only [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' K L := by
    ext M
    simp only [map_add, add_mul, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  map_smul' r K := by
    ext L
    simp only [map_smul, smul_mul_assoc, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]

omit [Nonempty ι] in
@[simp] theorem responsePairing_apply (a : ι → ℝ) (K L : Mat ι) :
    responsePairing a K L = realTrace ι (diagonalDerivative a K * L) := rfl

omit [Nonempty ι] in
theorem responsePairing_eq_sum (a : ι → ℝ) (K L : Mat ι) :
    responsePairing a K L = ∑ i, ∑ j,
      expDividedDifference (a i) (a j) * (K i j * L j i).re := by
  change Complex.reAddGroupHom
    (∑ i, ∑ j, (expDividedDifference (a i) (a j) • K i j) * L j i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.real_smul, Complex.mul_re]
  ring

omit [Nonempty ι] in
theorem responsePairing_symm (a : ι → ℝ) (K L : Mat ι) :
    responsePairing a K L = responsePairing a L K := by
  rw [responsePairing_eq_sum, responsePairing_eq_sum]
  calc
    (∑ i, ∑ j, expDividedDifference (a i) (a j) * (K i j * L j i).re) =
        ∑ j, ∑ i, expDividedDifference (a i) (a j) * (K i j * L j i).re :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [expDividedDifference_symm (a i) (a j), mul_comm (K i j) (L j i)]

omit [Nonempty ι] in
theorem realTrace_diagonalDerivative (a : ι → ℝ) (K : Mat ι) :
    realTrace ι (diagonalDerivative a K) = weightedTrace a K := by
  change Complex.reAddGroupHom (∑ i, diagonalDerivative a K i i) =
    Complex.reAddGroupHom (∑ i, (realDiagonal (fun i => Real.exp (a i)) * K) i i)
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [diagonalDerivative_apply, expDividedDifference_self,
    realDiagonal, Matrix.diagonal_mul, Complex.real_smul]

omit [Nonempty ι] in
@[simp] theorem responsePairing_one_right (a : ι → ℝ) (K : Mat ι) :
    responsePairing a K 1 = weightedTrace a K := by
  rw [responsePairing_apply, mul_one, realTrace_diagonalDerivative]

omit [Nonempty ι] in
@[simp] theorem responsePairing_one_left (a : ι → ℝ) (K : Mat ι) :
    responsePairing a 1 K = weightedTrace a K := by
  rw [responsePairing_symm, responsePairing_one_right]

def weightedNormSq (a : ι → ℝ) (K : Mat ι) : ℝ :=
  ∑ i, ∑ j, expDividedDifference (a i) (a j) * Complex.normSq (K i j)

omit [Nonempty ι] in
theorem responsePairing_self_normSq (a : ι → ℝ) {K : Mat ι} (hK : K.IsHermitian) :
    responsePairing a K K = weightedNormSq a K := by
  rw [responsePairing_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hK.apply j i, Complex.star_def, Complex.mul_conj]
  simp

omit [DecidableEq ι] [Nonempty ι] in
theorem weightedNormSq_nonneg (a : ι → ℝ) (K : Mat ι) : 0 ≤ weightedNormSq a K :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (expDividedDifference_pos (a i) (a j)).le (Complex.normSq_nonneg _)

omit [DecidableEq ι] [Nonempty ι] in
theorem weightedNormSq_eq_zero_iff (a : ι → ℝ) (K : Mat ι) :
    weightedNormSq a K = 0 ↔ K = 0 := by
  constructor
  · intro h
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg
        (expDividedDifference_pos (a i) (a j)).le (Complex.normSq_nonneg (K i j)))).mp h
    ext i j
    have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (expDividedDifference_pos (a i) (a j)).le
        (Complex.normSq_nonneg (K i j)))).mp (hs i (Finset.mem_univ i))
    exact Complex.normSq_eq_zero.mp
      ((mul_eq_zero.mp (ht j (Finset.mem_univ j))).resolve_left
        (ne_of_gt (expDividedDifference_pos (a i) (a j))))
  · rintro rfl
    simp [weightedNormSq]

def gibbsForm (a : ι → ℝ) : LinearMap.BilinForm ℝ (Mat ι) where
  toFun K :=
    { toFun L := responsePairing a K L / Z a - mean a K * mean a L
      map_add' L M := by
        simp only [map_add]
        ring
      map_smul' r L := by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' K L := by
    ext M
    simp only [map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' r K := by
    ext L
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring

omit [Nonempty ι] in
@[simp] theorem gibbsForm_apply (a : ι → ℝ) (K L : Mat ι) :
    gibbsForm a K L = realTrace ι (diagonalDerivative a K * L) / Z a -
      mean a K * mean a L := rfl

omit [Nonempty ι] in
theorem gibbsForm_symm (a : ι → ℝ) (K L : Mat ι) :
    gibbsForm a K L = gibbsForm a L K := by
  change responsePairing a K L / Z a - _ = responsePairing a L K / Z a - _
  rw [responsePairing_symm, mul_comm (mean a K) (mean a L)]

theorem gibbsForm_centered (a : ι → ℝ) (K L : Mat ι) :
    gibbsForm a K L = responsePairing a (centered a K) (centered a L) / Z a := by
  change responsePairing a K L / Z a - mean a K * mean a L = _
  simp only [centered, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    responsePairing_one_right, responsePairing_one_left, weightedTrace_one,
    smul_eq_mul, mean_apply]
  field_simp [Z_ne_zero a]
  ring

theorem gibbsForm_self_normSq (a : ι → ℝ) {K : Mat ι} (hK : K.IsHermitian) :
    gibbsForm a K K = weightedNormSq a (centered a K) / Z a := by
  rw [gibbsForm_centered, responsePairing_self_normSq a (centered_isHermitian a hK)]

theorem gibbsForm_nonneg (a : ι → ℝ) {K : Mat ι} (hK : K.IsHermitian) :
    0 ≤ gibbsForm a K K := by
  rw [gibbsForm_self_normSq a hK]
  exact div_nonneg (weightedNormSq_nonneg a _) (Z_pos a).le

theorem gibbsForm_self_eq_zero_iff (a : ι → ℝ) {K : Mat ι} (hK : K.IsHermitian) :
    gibbsForm a K K = 0 ↔ ∃ r : ℝ, K = r • (1 : Mat ι) := by
  rw [gibbsForm_self_normSq a hK, div_eq_zero_iff]
  simp only [Z_ne_zero a, or_false, weightedNormSq_eq_zero_iff, centered_eq_zero_iff]

theorem gibbsForm_scalar_left (a : ι → ℝ) (r : ℝ) (L : Mat ι) :
    gibbsForm a (r • (1 : Mat ι)) L = 0 := by
  rw [gibbsForm_centered, centered_scalar, map_zero, LinearMap.zero_apply, zero_div]

theorem gibbsForm_kernel_iff (a : ι → ℝ) (K : Hermitian ι) :
    (∀ L : Hermitian ι, gibbsForm a K L = 0) ↔
      ∃ r : ℝ, (K : Mat ι) = r • (1 : Mat ι) := by
  constructor
  · intro h
    exact (gibbsForm_self_eq_zero_iff a (PreparedTraceForm.hermitian_isHermitian ι K)).mp (h K)
  · rintro ⟨r, hr⟩ L
    rw [hr]
    exact gibbsForm_scalar_left a r L

theorem gibbsForm_traceless_pos (a : ι → ℝ) (K : Traceless ι) (hK : K ≠ 0) :
    0 < gibbsForm a (K.val : Mat ι) (K.val : Mat ι) := by
  have hh := PreparedTraceForm.hermitian_isHermitian ι K.val
  refine lt_of_le_of_ne (gibbsForm_nonneg a hh) ?_
  intro hz
  obtain ⟨r, hr⟩ := (gibbsForm_self_eq_zero_iff a hh).mp hz.symm
  have ht : realTrace ι (K.val : Mat ι) = 0 := K.property
  rw [hr, map_smul, PreparedTraceForm.realTrace_one] at ht
  have hr0 : r = 0 := (mul_eq_zero.mp ht).resolve_right (PreparedTraceForm.card_ne_zero ι)
  apply hK
  apply Subtype.ext
  apply Subtype.ext
  simpa [hr0] using hr

def hermitianForm (a : ι → ℝ) : LinearMap.BilinForm ℝ (Hermitian ι) :=
  (gibbsForm a).compl₁₂ (PreparedTraceForm.hermitianSubspace ι).subtype
    (PreparedTraceForm.hermitianSubspace ι).subtype

omit [Nonempty ι] in
@[simp] theorem hermitianForm_apply (a : ι → ℝ) (K L : Hermitian ι) :
    hermitianForm a K L = gibbsForm a (K : Mat ι) (L : Mat ι) := rfl

def scalarOne : Hermitian ι := ⟨1, IsSelfAdjoint.one _⟩

theorem scalarOne_ne_zero : (scalarOne : Hermitian ι) ≠ 0 := by
  intro h
  have hval : (1 : Mat ι) = 0 := congrArg Subtype.val h
  exact one_ne_zero hval

theorem hermitianForm_ker_eq_span_one (a : ι → ℝ) :
    LinearMap.ker (hermitianForm a) = Submodule.span ℝ {(scalarOne : Hermitian ι)} := by
  ext K
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  have hk : hermitianForm a K = 0 ↔ ∀ L : Hermitian ι, gibbsForm a K L = 0 := by
    constructor
    · intro h L
      exact congrArg (fun f : Hermitian ι →ₗ[ℝ] ℝ => f L) h
    · intro h
      exact LinearMap.ext h
  rw [hk, gibbsForm_kernel_iff]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr.symm⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, (congrArg Subtype.val hr).symm⟩

theorem finrank_range_hermitianForm (a : ι → ℝ) :
    Module.finrank ℝ (LinearMap.range (hermitianForm a)) = (Fintype.card ι) ^ 2 - 1 := by
  have h := (hermitianForm a).finrank_range_add_finrank_ker
  rw [hermitianForm_ker_eq_span_one, finrank_span_singleton scalarOne_ne_zero,
    PreparedTraceForm.finrank_hermitian] at h
  omega

end GeneratedFoundations.Operations.GibbsTraceForm
