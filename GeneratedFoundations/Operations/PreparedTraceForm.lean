module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic

/-!
# The prepared trace covariance

The trace covariance is a real symmetric bilinear form on complex matrices.
On Hermitian matrices it is nonnegative, its nullspace consists exactly of
real scalar matrices, and its restriction to the traceless subspace is
positive definite. Unitary conjugation preserves the form.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix ComplexConjugate
open Module

namespace GeneratedFoundations.Operations.PreparedTraceForm

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

abbrev Mat := Matrix ι ι ℂ

def hermitianSubspace : Submodule ℝ (Mat ι) := selfAdjoint.submodule ℝ (Mat ι)

abbrev Hermitian := selfAdjoint (Mat ι)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem mem_hermitianSubspace (K : Mat ι) :
    K ∈ hermitianSubspace ι ↔ K.IsHermitian :=
  Matrix.isHermitian_iff_isSelfAdjoint.symm

omit [Fintype ι] [DecidableEq ι] in
theorem hermitian_isHermitian (K : Hermitian ι) : (K : Mat ι).IsHermitian :=
  K.property.isHermitian

def realTrace : Mat ι →ₗ[ℝ] ℝ :=
  Complex.reLm.comp (Matrix.traceLinearMap ι ℝ ℂ)

omit [DecidableEq ι] in
@[simp] theorem realTrace_apply (K : Mat ι) : realTrace ι K = (Matrix.trace K).re := rfl

@[simp] theorem realTrace_one : realTrace ι (1 : Mat ι) = Fintype.card ι := by
  simp [realTrace]

def preparedForm : LinearMap.BilinForm ℝ (Mat ι) where
  toFun K :=
    { toFun := fun L => realTrace ι (K * L) / Fintype.card ι -
        realTrace ι K * realTrace ι L / (Fintype.card ι : ℝ) ^ 2
      map_add' := by
        intro L M
        simp only [mul_add, map_add]
        ring
      map_smul' := by
        intro a L
        simp only [mul_smul_comm, map_smul, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' := by
    intro K L
    ext M
    simp only [add_mul, map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' := by
    intro a K
    ext L
    simp only [smul_mul_assoc, map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring

@[simp] theorem preparedForm_apply (K L : Mat ι) :
    preparedForm ι K L = (Matrix.trace (K * L)).re / (Fintype.card ι : ℝ) -
      (Matrix.trace K).re * (Matrix.trace L).re / (Fintype.card ι : ℝ) ^ 2 := rfl

theorem preparedForm_symm (K L : Mat ι) : preparedForm ι K L = preparedForm ι L K := by
  simp only [preparedForm_apply, Matrix.trace_mul_comm K L, mul_comm]

def meanTrace (K : Mat ι) : ℝ := realTrace ι K / Fintype.card ι

def centered (K : Mat ι) : Mat ι := K - meanTrace ι K • (1 : Mat ι)

theorem centered_isHermitian {K : Mat ι} (hK : K.IsHermitian) :
    (centered ι K).IsHermitian :=
  hK.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))

omit [DecidableEq ι] in
theorem trace_square_normSq {K : Mat ι} (hK : K.IsHermitian) :
    realTrace ι (K * K) = ∑ i : ι, ∑ j : ι, Complex.normSq (K j i) := by
  change (Matrix.trace (K * K)).re = _
  calc
    _ = (Matrix.trace (K.conjTranspose * K)).re := by rw [hK.eq]
    _ = _ := by
      change Complex.reAddGroupHom
        (∑ i : ι, ∑ j : ι, star (K j i) * K j i) = _
      simp only [map_sum]
      simp [Complex.mul_re, Complex.normSq_apply]

omit [DecidableEq ι] in
theorem sum_normSq_nonneg (K : Mat ι) :
    0 ≤ ∑ i : ι, ∑ j : ι, Complex.normSq (K j i) :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

omit [DecidableEq ι] in
theorem sum_normSq_eq_zero_iff (K : Mat ι) :
    (∑ i : ι, ∑ j : ι, Complex.normSq (K j i)) = 0 ↔ K = 0 := by
  constructor
  · intro h
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (K j i))).mp h
    ext i j
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Complex.normSq_nonneg (K k j))).mp (hs j (Finset.mem_univ j))
    exact Complex.normSq_eq_zero.mp (ht i (Finset.mem_univ i))
  · rintro rfl
    simp

variable [Nonempty ι]

omit [DecidableEq ι] in
theorem card_pos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos

omit [DecidableEq ι] in
theorem card_ne_zero : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt (card_pos ι)

@[simp] theorem meanTrace_scalar (a : ℝ) :
    meanTrace ι (a • (1 : Mat ι)) = a := by
  simp [meanTrace, map_smul, smul_eq_mul]

@[simp] theorem centered_scalar (a : ℝ) : centered ι (a • (1 : Mat ι)) = 0 := by
  simp [centered]

@[simp] theorem realTrace_centered (K : Mat ι) : realTrace ι (centered ι K) = 0 := by
  simp only [centered, map_sub, map_smul, realTrace_one, smul_eq_mul, meanTrace]
  field_simp [card_ne_zero ι]
  ring

theorem centered_eq_zero_iff (K : Mat ι) :
    centered ι K = 0 ↔ ∃ a : ℝ, K = a • (1 : Mat ι) := by
  constructor
  · intro h
    exact ⟨meanTrace ι K, sub_eq_zero.mp h⟩
  · rintro ⟨a, rfl⟩
    exact centered_scalar ι a

theorem preparedForm_centered (K L : Mat ι) :
    preparedForm ι K L = realTrace ι (centered ι K * centered ι L) /
      (Fintype.card ι : ℝ) := by
  change realTrace ι (K * L) / (Fintype.card ι : ℝ) -
      realTrace ι K * realTrace ι L / (Fintype.card ι : ℝ) ^ 2 = _
  simp only [centered, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
    one_mul, mul_one, map_sub, map_smul, realTrace_one, smul_eq_mul, meanTrace]
  field_simp [card_ne_zero ι]
  ring

theorem preparedForm_self_normSq {K : Mat ι} (hK : K.IsHermitian) :
    preparedForm ι K K =
      (∑ i : ι, ∑ j : ι, Complex.normSq (centered ι K j i)) / (Fintype.card ι : ℝ) := by
  rw [preparedForm_centered, trace_square_normSq ι (centered_isHermitian ι hK)]

theorem preparedForm_nonneg {K : Mat ι} (hK : K.IsHermitian) :
    0 ≤ preparedForm ι K K := by
  rw [preparedForm_self_normSq ι hK]
  exact div_nonneg (sum_normSq_nonneg ι _) (card_pos ι).le

theorem preparedForm_self_eq_zero_iff {K : Mat ι} (hK : K.IsHermitian) :
    preparedForm ι K K = 0 ↔ ∃ a : ℝ, K = a • (1 : Mat ι) := by
  rw [preparedForm_self_normSq ι hK, div_eq_zero_iff]
  simp only [card_ne_zero ι, or_false, sum_normSq_eq_zero_iff, centered_eq_zero_iff]

theorem preparedForm_scalar_left (a : ℝ) (L : Mat ι) :
    preparedForm ι (a • (1 : Mat ι)) L = 0 := by
  rw [preparedForm_centered, centered_scalar, zero_mul, map_zero, zero_div]

theorem preparedForm_kernel_iff (K : Hermitian ι) :
    (∀ L : Hermitian ι, preparedForm ι K L = 0) ↔
      ∃ a : ℝ, (K : Mat ι) = a • (1 : Mat ι) := by
  constructor
  · intro h
    exact (preparedForm_self_eq_zero_iff ι (hermitian_isHermitian ι K)).mp (h K)
  · rintro ⟨a, ha⟩ L
    rw [ha]
    exact preparedForm_scalar_left ι a L

def hermitianTrace : Hermitian ι →ₗ[ℝ] ℝ :=
  (realTrace ι).comp (hermitianSubspace ι).subtype

omit [DecidableEq ι] [Nonempty ι] in
@[simp] theorem hermitianTrace_apply (K : Hermitian ι) :
    hermitianTrace ι K = (Matrix.trace (K : Mat ι)).re := rfl

def tracelessSubspace : Submodule ℝ (Hermitian ι) := LinearMap.ker (hermitianTrace ι)

abbrev Traceless := tracelessSubspace ι

omit [DecidableEq ι] [Nonempty ι] in
theorem trace_real {K : Mat ι} (hK : K.IsHermitian) :
    ((Matrix.trace K).re : ℂ) = Matrix.trace K := by
  rw [← Complex.conj_eq_iff_re]
  exact (Matrix.trace_conjTranspose K).symm.trans (congrArg Matrix.trace hK.eq)

omit [DecidableEq ι] [Nonempty ι] in
theorem mem_tracelessSubspace (K : Hermitian ι) :
    K ∈ tracelessSubspace ι ↔ Matrix.trace (K : Mat ι) = 0 := by
  change (Matrix.trace (K : Mat ι)).re = 0 ↔ _
  constructor
  · intro h
    rw [← trace_real ι (hermitian_isHermitian ι K), h]
    rfl
  · intro h
    rw [h]
    rfl

theorem preparedForm_traceless_pos (K : Traceless ι) (hK : K ≠ 0) :
    0 < preparedForm ι (K.val : Mat ι) (K.val : Mat ι) := by
  have hh := hermitian_isHermitian ι K.val
  refine lt_of_le_of_ne (preparedForm_nonneg ι hh) ?_
  intro hz
  obtain ⟨a, ha⟩ := (preparedForm_self_eq_zero_iff ι hh).mp hz.symm
  have ht : realTrace ι (K.val : Mat ι) = 0 := K.property
  rw [ha, map_smul, realTrace_one] at ht
  have ha0 : a = 0 := (mul_eq_zero.mp ht).resolve_right (card_ne_zero ι)
  apply hK
  apply Subtype.ext
  apply Subtype.ext
  simpa [ha0] using ha

omit [Nonempty ι] in
theorem realTrace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (K : Mat ι) :
    realTrace ι ((U : Mat ι) * K * (U : Mat ι).conjTranspose) = realTrace ι K := by
  change (Matrix.trace ((U : Mat ι) * K * (U : Mat ι).conjTranspose)).re =
    (Matrix.trace K).re
  rw [Matrix.trace_mul_cycle]
  have hU : (U : Mat ι).conjTranspose * (U : Mat ι) = 1 := U.property.1
  rw [hU, one_mul]

omit [Nonempty ι] in
theorem preparedForm_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (K L : Mat ι) :
    preparedForm ι ((U : Mat ι) * K * (U : Mat ι).conjTranspose)
        ((U : Mat ι) * L * (U : Mat ι).conjTranspose) = preparedForm ι K L := by
  have hU : (U : Mat ι).conjTranspose * (U : Mat ι) = 1 := U.property.1
  have hm : ((U : Mat ι) * K * (U : Mat ι).conjTranspose) *
      ((U : Mat ι) * L * (U : Mat ι).conjTranspose) =
      (U : Mat ι) * (K * L) * (U : Mat ι).conjTranspose := by
    simp only [mul_assoc, ← mul_assoc (U : Mat ι).conjTranspose (U : Mat ι),
      hU, one_mul]
  change realTrace ι _ / (Fintype.card ι : ℝ) -
      realTrace ι _ * realTrace ι _ / (Fintype.card ι : ℝ) ^ 2 = _
  rw [hm, realTrace_unitary_conj, realTrace_unitary_conj, realTrace_unitary_conj]
  rfl

instance hermitian_finiteDimensional : FiniteDimensional ℝ (Hermitian ι) :=
  FiniteDimensional.of_injective (hermitianSubspace ι).subtype Subtype.val_injective

omit [DecidableEq ι] [Nonempty ι] in
/-- The imaginary-part map is onto the Hermitian space and has that same
space as its kernel. Rank-nullity therefore determines its real dimension. -/
theorem finrank_hermitian : finrank ℝ (Hermitian ι) = (Fintype.card ι) ^ 2 := by
  have h := (imaginaryPart (A := Mat ι)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (imaginaryPart_surjective (A := Mat ι)),
    finrank_top, ker_imaginaryPart] at h
  change finrank ℝ (Hermitian ι) + finrank ℝ (Hermitian ι) = finrank ℝ (Mat ι) at h
  have hm : finrank ℝ (Mat ι) = (Fintype.card ι) ^ 2 * 2 := by
    rw [Module.finrank_matrix, Complex.finrank_real_complex]
    ring
  rw [hm] at h
  omega

theorem hermitianTrace_surjective : Function.Surjective (hermitianTrace ι) := by
  intro a
  refine ⟨⟨(a / (Fintype.card ι : ℝ)) • (1 : Mat ι),
    (IsSelfAdjoint.all _).smul (IsSelfAdjoint.one _)⟩, ?_⟩
  change realTrace ι ((a / (Fintype.card ι : ℝ)) • (1 : Mat ι)) = a
  simp only [map_smul, realTrace_one, smul_eq_mul]
  field_simp [card_ne_zero ι]

theorem finrank_traceless : finrank ℝ (Traceless ι) = (Fintype.card ι) ^ 2 - 1 := by
  have h := (hermitianTrace ι).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (hermitianTrace_surjective ι),
    finrank_top, Module.finrank_self, finrank_hermitian] at h
  change 1 + finrank ℝ (Traceless ι) = (Fintype.card ι) ^ 2 at h
  omega

end GeneratedFoundations.Operations.PreparedTraceForm
