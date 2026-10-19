module

public import GeneratedFoundations.Geometry.SourceTensorCovariantDerivative

/-!
# Tensor curl from the generated covariant differential

The cyclic contraction acts on the first tensor index and uses the Koszul
connection on both indices. On symmetric trace-free tensors it equals the
already derived one-form curl on each column, plus the tensor itself. This
identity retains the second-index connection term. The transverse kernel
is preserved, and the second-order identity follows from the original
one-form differential identity. No tensor spectral branch is assumed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSpinorConnection
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceTensorCovariantDerivative

namespace GeneratedFoundations.Geometry.SourceTensorCurl

attribute [local irreducible] coefficientCovariant coefficientConnection

private theorem covariantLinear_apply (m : ℕ) (i : Fin 3)
    (H : TensorCoefficients m) (a b : Fin 3) :
    covariantLinear m i H a b = coefficientCovariant m i H a b := rfl

/-- The full connection table is evaluated from the original Koszul formula. -/
theorem koszul_table (i a b : Fin 3) :
    koszul i a b =
      ![ ![![0, 0, 0], ![0, 0, -1], ![0, 1, 0]],
         ![![0, 0, 1], ![0, 0, 0], ![-1, 0, 0]],
         ![![0, -1, 0], ![1, 0, 0], ![0, 0, 0]] ] i a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [koszul, tracePair, unitAxis, axisVelocity, spinMatrix,
      spinMatrix1, spinMatrix2, spinMatrix3, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num

def coefficientTensorCurl (m : ℕ) (H : TensorCoefficients m) :
    TensorCoefficients m := fun a b =>
  ![coefficientCovariant m 1 H 2 b - coefficientCovariant m 2 H 1 b,
    coefficientCovariant m 2 H 0 b - coefficientCovariant m 0 H 2 b,
    coefficientCovariant m 0 H 1 b - coefficientCovariant m 1 H 0 b] a

set_option maxHeartbeats 1600000 in
/-- The transpose and trace terms come from the second tensor connection. -/
theorem curl_connection (m : ℕ) (H : TensorCoefficients m) (a b : Fin 3) :
    coefficientTensorCurl m H a b =
      coefficientCurl m (fun c => H c b) a + H b a -
        if a = b then (∑ c : Fin 3, H c c) else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [coefficientTensorCurl, coefficientCovariant, coefficientConnection, coefficientCurl,
      koszul_table, Fin.sum_univ_three] <;> module

theorem curl_symmetric_tracefree (m : ℕ) (H : TensorCoefficients m)
    (hs : ∀ a b, H a b = H b a) (ht : (∑ a : Fin 3, H a a) = 0)
    (a b : Fin 3) :
    coefficientTensorCurl m H a b =
      coefficientCurl m (fun c => H c b) a + H a b := by
  rw [curl_connection, hs b a, ht]
  split_ifs <;> simp

theorem curl_column (m : ℕ) (H : TensorCoefficients m)
    (hs : ∀ a b, H a b = H b a) (ht : (∑ a : Fin 3, H a a) = 0)
    (b : Fin 3) :
    (fun a => coefficientTensorCurl m H a b) =
      coefficientCurl m (fun a => H a b) + (fun a => H a b) := by
  funext a
  exact curl_symmetric_tracefree m H hs ht a b

theorem curl_add (m : ℕ) (H K : TensorCoefficients m) :
    coefficientTensorCurl m (H + K) =
      coefficientTensorCurl m H + coefficientTensorCurl m K := by
  funext a b
  fin_cases a <;>
    simp [coefficientTensorCurl, ← covariantLinear_apply, map_add, Pi.add_apply] <;> module

theorem curl_smul (m : ℕ) (c : ℂ) (H : TensorCoefficients m) :
    coefficientTensorCurl m (c • H) = c • coefficientTensorCurl m H := by
  funext a b
  fin_cases a <;>
    simp [coefficientTensorCurl, ← covariantLinear_apply, map_smul, Pi.smul_apply, smul_sub]

/-- Symmetry cancels the connection contribution to the divergence. -/
theorem divergence_columns (m : ℕ) (H : TensorCoefficients m)
    (hs : ∀ a b, H a b = H b a) (b : Fin 3) :
    SourceTensorCovariantDerivative.coefficientDivergence m H b =
      -SourceOneFormDifferential.coefficientDivergence m (fun a => H a b) := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs21 := hs 2 1
  fin_cases b <;>
    simp [SourceTensorCovariantDerivative.coefficientDivergence,
      SourceOneFormDifferential.coefficientDivergence, coefficientCovariant,
      coefficientConnection, koszul_table, Fin.sum_univ_three, hs10, hs20, hs21] <;> module

theorem transverse_columns (m : ℕ) (H : TensorCoefficients m)
    (hH : H ∈ ttCoefficients m) (b : Fin 3) :
    SourceOneFormDifferential.coefficientDivergence m (fun a => H a b) = 0 := by
  have hd := congrFun hH.2.2 b
  rw [divergence_columns m H hH.1 b] at hd
  exact neg_eq_zero.mp hd

theorem curl_trace_zero (m : ℕ) (H : TensorCoefficients m)
    (hs : ∀ a b, H a b = H b a) (ht : (∑ a : Fin 3, H a a) = 0) :
    (∑ a : Fin 3, coefficientTensorCurl m H a a) = 0 := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs21 := hs 2 1
  calc
    _ = (3 : ℂ) • (∑ a : Fin 3, H a a) := by
      simp only [Fin.sum_univ_three, curl_symmetric_tracefree m H hs ht, coefficientCurl,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, hs10, hs20, hs21]
      module
    _ = 0 := by rw [ht, smul_zero]

/-- The antisymmetric part is a differential constraint, not an omitted
polarization. Transversality and zero trace make it vanish. -/
theorem curl_preserves_symmetry (m : ℕ) (H : TensorCoefficients m)
    (hH : H ∈ ttCoefficients m) :
    ∀ a b, coefficientTensorCurl m H a b = coefficientTensorCurl m H b a := by
  have hs := hH.1
  have ht := hH.2.1
  have hd (b : Fin 3) := transverse_columns m H hH b
  have htrace (i : Fin 3) :
      unitHilbertAxis m i (H 0 0) + unitHilbertAxis m i (H 1 1) +
        unitHilbertAxis m i (H 2 2) = 0 := by
    have h := congrArg (unitHilbertAxis m i) ht
    simpa only [Fin.sum_univ_three, map_add, map_zero] using h
  have h01 : coefficientTensorCurl m H 0 1 - coefficientTensorCurl m H 1 0 =
      SourceOneFormDifferential.coefficientDivergence m (fun a => H a 2) -
        (unitHilbertAxis m 2 (H 0 0) + unitHilbertAxis m 2 (H 1 1) +
          unitHilbertAxis m 2 (H 2 2)) := by
    simp only [curl_symmetric_tracefree m H hs ht, coefficientCurl,
      SourceOneFormDifferential.coefficientDivergence, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, hs 2 0, hs 2 1, hs 1 0]
    module
  have h12 : coefficientTensorCurl m H 1 2 - coefficientTensorCurl m H 2 1 =
      SourceOneFormDifferential.coefficientDivergence m (fun a => H a 0) -
        (unitHilbertAxis m 0 (H 0 0) + unitHilbertAxis m 0 (H 1 1) +
          unitHilbertAxis m 0 (H 2 2)) := by
    simp only [curl_symmetric_tracefree m H hs ht, coefficientCurl,
      SourceOneFormDifferential.coefficientDivergence, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hs 2 0,
      hs 2 1, hs 1 0]
    module
  have h20 : coefficientTensorCurl m H 2 0 - coefficientTensorCurl m H 0 2 =
      SourceOneFormDifferential.coefficientDivergence m (fun a => H a 1) -
        (unitHilbertAxis m 1 (H 0 0) + unitHilbertAxis m 1 (H 1 1) +
          unitHilbertAxis m 1 (H 2 2)) := by
    simp only [curl_symmetric_tracefree m H hs ht, coefficientCurl,
      SourceOneFormDifferential.coefficientDivergence, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hs 2 0, hs 2 1, hs 1 0]
    module
  rw [hd, htrace, sub_self] at h01 h12 h20
  intro a b
  fin_cases a <;> fin_cases b <;>
    first | rfl | exact sub_eq_zero.mp h01 | exact (sub_eq_zero.mp h01).symm |
      exact sub_eq_zero.mp h12 | exact (sub_eq_zero.mp h12).symm |
      exact sub_eq_zero.mp h20 | exact (sub_eq_zero.mp h20).symm

theorem curl_preserves_transverse (m : ℕ) (H : TensorCoefficients m)
    (hH : H ∈ ttCoefficients m) :
    SourceTensorCovariantDerivative.coefficientDivergence m
      (coefficientTensorCurl m H) = 0 := by
  funext b
  rw [divergence_columns m _ (curl_preserves_symmetry m H hH) b,
    curl_column m H hH.1 hH.2.1]
  simp only [SourceOneFormDifferential.coefficientDivergence, Pi.add_apply, map_add,
    Finset.sum_add_distrib]
  change -(SourceOneFormDifferential.coefficientDivergence m
      (coefficientCurl m (fun a => H a b)) +
    SourceOneFormDifferential.coefficientDivergence m (fun a => H a b)) = 0
  rw [coefficientDivergence_curl_zero, transverse_columns m H hH b]
  simp

theorem curl_mem (m : ℕ) (H : TensorCoefficients m)
    (hH : H ∈ ttCoefficients m) : coefficientTensorCurl m H ∈ ttCoefficients m :=
  ⟨curl_preserves_symmetry m H hH,
    curl_trace_zero m H hH.1 hH.2.1, curl_preserves_transverse m H hH⟩

/-- The tensor identity is a consequence of the derived one-form identity
and both tensor-index connection terms. -/
theorem curl_square (m : ℕ) (H : TensorCoefficients m)
    (hH : H ∈ ttCoefficients m) :
    coefficientTensorCurl m (coefficientTensorCurl m H) =
      ((m : ℂ) * ((m : ℂ) + 2) - 3) • H +
        (4 : ℂ) • coefficientTensorCurl m H := by
  have hC := curl_mem m H hH
  funext a b
  rw [curl_symmetric_tracefree m _ hC.1 hC.2.1,
    curl_column m H hH.1 hH.2.1 b, coefficientCurl_add,
    coefficientCurl_square, transverse_columns m H hH b]
  simp only [coefficientGradient, map_zero, Pi.add_apply, Pi.smul_apply,
    curl_symmetric_tracefree m H hH.1 hH.2.1]
  module

end GeneratedFoundations.Geometry.SourceTensorCurl
