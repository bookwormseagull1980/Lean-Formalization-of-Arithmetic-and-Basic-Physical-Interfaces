module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The trace of a positive operator

The extended trace is the supremum of the diagonal sums over all finite
orthonormal families. It therefore does not depend on a chosen Hilbert basis.
For a nonnegative diagonal operator with summable weights, Parseval's identity
and Bessel's inequality identify this trace with the sum of its weights.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate ENNReal

namespace GeneratedFoundations.Spectral.PositiveOperatorTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The usual extended trace on positive operators, expressed without a basis. -/
def positiveTrace (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (v : Fin n → H) (_ : Orthonormal ℂ v),
    ∑ i, ENNReal.ofReal (inner ℂ (v i) (T (v i))).re

theorem finite_diagonal_le_trace (T : H →L[ℂ] H) {n : ℕ} (v : Fin n → H)
    (hv : Orthonormal ℂ v) :
    (∑ i, ENNReal.ofReal (inner ℂ (v i) (T (v i))).re) ≤ positiveTrace T :=
  le_iSup_of_le n (le_iSup_of_le v (le_iSup_of_le hv le_rfl))

/-- The positive trace-class criterion; positivity is an operator property. -/
def IsPositiveTraceClass [CompleteSpace H] (T : H →L[ℂ] H) : Prop :=
  IsSelfAdjoint T ∧ (∀ x, 0 ≤ (inner ℂ x (T x)).re) ∧ positiveTrace T < ∞

theorem positiveTrace_le_of_intertwining
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H →ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (S : K →L[ℂ] K)
    (h : ∀ x, S (U x) = U (T x)) : positiveTrace T ≤ positiveTrace S := by
  refine iSup_le fun n => iSup_le fun v => iSup_le fun hv => ?_
  have hsum := finite_diagonal_le_trace S (fun i => U (v i))
    (hv.comp_linearIsometry U)
  simpa only [h, U.inner_map_map] using hsum

/-- Unitary transport preserves the trace without selecting any basis. -/
theorem positiveTrace_eq_of_unitary_intertwining
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (S : K →L[ℂ] K)
    (h : ∀ x, S (U x) = U (T x)) : positiveTrace T = positiveTrace S := by
  apply le_antisymm
  · exact positiveTrace_le_of_intertwining U.toLinearIsometry T S h
  · apply positiveTrace_le_of_intertwining U.symm.toLinearIsometry S T
    intro x
    apply U.injective
    change U (T (U.symm x)) = U (U.symm (S x))
    simpa only [LinearIsometryEquiv.apply_symm_apply] using (h (U.symm x)).symm

variable (b : HilbertBasis ℕ ℂ H) (T : H →L[ℂ] H) (w : ℕ → ℝ)

set_option backward.isDefEq.respectTransparency false in
theorem diagonal_quadratic_hasSum
    (hcoeff : ∀ (x : H) n, inner ℂ (b n) (T x) = (w n : ℂ) * inner ℂ (b n) x)
    (x : H) :
    HasSum (fun n => w n * ‖inner ℂ (b n) x‖ ^ 2) (inner ℂ x (T x)).re := by
  have h := Complex.hasSum_re (b.hasSum_inner_mul_inner x (T x))
  convert h using 1
  funext n
  rw [hcoeff]
  have heq : inner ℂ x (b n) * ((w n : ℂ) * inner ℂ (b n) x) =
      (w n : ℂ) * (‖inner ℂ (b n) x‖ ^ 2 : ℝ) := by
    rw [← inner_conj_symm x (b n), mul_left_comm, RCLike.conj_mul]
    rw [Complex.ofReal_pow]
    rfl
  rw [heq, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem diagonal_quadratic_nonneg
    (hw : ∀ n, 0 ≤ w n)
    (hcoeff : ∀ (x : H) n, inner ℂ (b n) (T x) = (w n : ℂ) * inner ℂ (b n) x)
    (x : H) : 0 ≤ (inner ℂ x (T x)).re := by
  rw [← (diagonal_quadratic_hasSum b T w hcoeff x).tsum_eq]
  exact tsum_nonneg fun n => mul_nonneg (hw n) (sq_nonneg _)

theorem finite_diagonal_le_sum
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hcoeff : ∀ (x : H) n, inner ℂ (b n) (T x) = (w n : ℂ) * inner ℂ (b n) x)
    {m : ℕ} (v : Fin m → H) (hv : Orthonormal ℂ v) :
    (∑ i, (inner ℂ (v i) (T (v i))).re) ≤ ∑' n, w n := by
  have hsum : HasSum (fun n => ∑ i, w n * ‖inner ℂ (b n) (v i)‖ ^ 2)
      (∑ i, (inner ℂ (v i) (T (v i))).re) :=
    hasSum_sum fun i _ => diagonal_quadratic_hasSum b T w hcoeff (v i)
  apply hasSum_le _ hsum hs.hasSum
  intro n
  rw [← Finset.mul_sum]
  apply mul_le_of_le_one_right (hw n)
  have h := hv.sum_inner_products_le (b n) (s := Finset.univ)
  simpa only [norm_inner_symm (b n), b.orthonormal.norm_eq_one, one_pow] using h

theorem positiveTrace_eq_tsum_of_diagonal
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hcoeff : ∀ (x : H) n, inner ℂ (b n) (T x) = (w n : ℂ) * inner ℂ (b n) x) :
    positiveTrace T = ∑' n, ENNReal.ofReal (w n) := by
  classical
  apply le_antisymm
  · refine iSup_le fun m => iSup_le fun v => iSup_le fun hv => ?_
    calc
      (∑ i, ENNReal.ofReal (inner ℂ (v i) (T (v i))).re) =
          ENNReal.ofReal (∑ i, (inner ℂ (v i) (T (v i))).re) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ =>
          diagonal_quadratic_nonneg b T w hw hcoeff (v i)).symm
      _ ≤ ENNReal.ofReal (∑' n, w n) :=
        ENNReal.ofReal_le_ofReal (finite_diagonal_le_sum b T w hw hs hcoeff v hv)
      _ = ∑' n, ENNReal.ofReal (w n) := ENNReal.ofReal_tsum_of_nonneg hw hs
  · rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun m => ?_
    have hv : Orthonormal ℂ (fun i : Fin m => b i.val) :=
      b.orthonormal.comp (fun i : Fin m => i.val) Fin.val_injective
    have h := finite_diagonal_le_trace T (fun i : Fin m => b i.val) hv
    have hd (n : ℕ) : (inner ℂ (b n) (T (b n))).re = w n := by
      rw [hcoeff]
      simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp only [hd] at h
    convert h using 1
    exact (Fin.sum_univ_eq_sum_range (fun n => ENNReal.ofReal (w n)) m).symm

theorem positiveTrace_lt_top_of_diagonal
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hcoeff : ∀ (x : H) n, inner ℂ (b n) (T x) = (w n : ℂ) * inner ℂ (b n) x) :
    positiveTrace T < ∞ := by
  rw [positiveTrace_eq_tsum_of_diagonal b T w hw hs hcoeff]
  exact hs.tsum_ofReal_lt_top

end GeneratedFoundations.Spectral.PositiveOperatorTrace
