module

public import GeneratedFoundations.Operations.GibbsTraceForm

/-!
# Exact block separation in the original Gibbs response

A two-block observation partitions the existing carrier. It changes neither
the reference weights nor the matrix algebra. The within-block and
cross-block parts are orthogonal in the actual Gibbs Hessian; the latter
retains its full logarithmic-mean weighted square. Scalar directions and
empty blocks require no separate invertibility assumption. The retained
block-diagonal response still includes the covariance of the block means.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Operations.GibbsBlockResponse

open PreparedTraceForm GibbsTraceForm GibbsExponentialDifferentiation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def block (b : ι → Bool) (K : Hermitian ι) : Hermitian ι :=
  ⟨fun i j => if b i = b j then (K : Mat ι) i j else 0, by
    apply Matrix.IsHermitian.isSelfAdjoint
    apply Matrix.IsHermitian.ext
    intro i j
    change star (if b j = b i then (K : Mat ι) j i else 0) =
      if b i = b j then (K : Mat ι) i j else 0
    by_cases h : b i = b j
    · simp only [ite_eq_left h, ite_eq_left h.symm]
      exact (hermitian_isHermitian ι K).apply i j
    · simp only [ite_eq_right h, ite_eq_right (Ne.symm h), star_zero]⟩

def off (b : ι → Bool) (K : Hermitian ι) : Hermitian ι := K - block b K

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
@[simp] theorem block_apply (b : ι → Bool) (K : Hermitian ι) (i j : ι) :
    (block b K : Mat ι) i j = if b i = b j then (K : Mat ι) i j else 0 := rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem off_apply (b : ι → Bool) (K : Hermitian ι) (i j : ι) :
    (off b K : Mat ι) i j = if b i = b j then 0 else (K : Mat ι) i j := by
  change (K : Mat ι) i j - (block b K : Mat ι) i j = _
  rw [block_apply]
  by_cases h : b i = b j <;> simp [h]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem reconstruction (b : ι → Bool) (K : Hermitian ι) :
    K = block b K + off b K := by
  simp [off]

omit [Nonempty ι] in
theorem mean_off (a : ι → ℝ) (b : ι → Bool) (K : Hermitian ι) :
    mean a (off b K : Mat ι) = 0 := by
  rw [mean_apply, weightedTrace_eq_sum]
  simp only [off_apply, ite_true, Complex.zero_re, mul_zero, Finset.sum_const_zero,
    zero_div]

omit [Nonempty ι] in
theorem mean_block (a : ι → ℝ) (b : ι → Bool) (K : Hermitian ι) :
    mean a (block b K : Mat ι) = mean a (K : Mat ι) := by
  rw [mean_apply, mean_apply, weightedTrace_eq_sum, weightedTrace_eq_sum]
  simp only [block_apply, ite_true]

omit [Nonempty ι] in
theorem block_off_orthogonal (a : ι → ℝ) (b : ι → Bool) (K : Hermitian ι) :
    hermitianForm a (block b K) (off b K) = 0 := by
  change responsePairing a (block b K : Mat ι) (off b K : Mat ι) / Z a -
    mean a (block b K : Mat ι) * mean a (off b K : Mat ι) = 0
  rw [mean_off, mul_zero, sub_zero, responsePairing_eq_sum]
  have hz : (∑ i, ∑ j, expDividedDifference (a i) (a j) *
      ((block b K : Mat ι) i j * (off b K : Mat ι) j i).re) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : b i = b j
    · simp only [block_apply, off_apply, ite_eq_left h, ite_eq_left h.symm,
        mul_zero, Complex.zero_re]
    · simp only [block_apply, ite_eq_right h, zero_mul, Complex.zero_re, mul_zero]
  rw [hz, zero_div]

/-- The cross-block response remains an explicit part of the same metric. -/
theorem off_response (a : ι → ℝ) (b : ι → Bool) (K : Hermitian ι) :
    hermitianForm a (off b K) (off b K) =
      (∑ i, ∑ j, if b i = b j then 0 else
        expDividedDifference (a i) (a j) * Complex.normSq ((K : Mat ι) i j)) / Z a := by
  rw [hermitianForm_apply, gibbsForm_self_normSq a (hermitian_isHermitian ι (off b K))]
  simp only [GibbsTraceForm.centered, mean_off, zero_smul, sub_zero]
  congr 1
  unfold weightedNormSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : b i = b j <;> simp [off_apply, h]

theorem off_response_nonneg (a : ι → ℝ) (b : ι → Bool) (K : Hermitian ι) :
    0 ≤ hermitianForm a (off b K) (off b K) :=
  gibbsForm_nonneg a (hermitian_isHermitian ι (off b K))

omit [Nonempty ι] in
/-- Exact Pythagoras, before any blockwise bound or capacity replacement. -/
theorem response_decomposition (a : ι → ℝ) (b : ι → Bool) (K : Hermitian ι) :
    hermitianForm a K K = hermitianForm a (block b K) (block b K) +
      hermitianForm a (off b K) (off b K) := by
  have hbo := block_off_orthogonal a b K
  have hob : hermitianForm a (off b K) (block b K) = 0 := by
    rw [hermitianForm_apply, gibbsForm_symm]
    exact hbo
  calc
    hermitianForm a K K =
        hermitianForm a (block b K + off b K) (block b K + off b K) :=
      congrArg (fun J => hermitianForm a J J) (reconstruction b K)
    _ = _ := by
      simp only [map_add, LinearMap.add_apply]
      rw [hbo, hob]
      ring

end GeneratedFoundations.Operations.GibbsBlockResponse
