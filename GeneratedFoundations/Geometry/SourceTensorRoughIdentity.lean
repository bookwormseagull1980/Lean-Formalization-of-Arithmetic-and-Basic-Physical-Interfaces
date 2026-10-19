module

public import GeneratedFoundations.Geometry.SourceTensorCurl

/-!
# The tensor rough operator and its transverse curl identity

The rough operator is the negative sum of the squares of the original
covariant derivatives. Expanding both index connections gives its relation
to tensor curl. On the transverse--traceless differential kernel it is
exactly curl squared minus three. The constant and the differential kernel
are obtained before applying any spectral theorem.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceSpinorConnection
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceTensorCovariantDerivative
open GeneratedFoundations.Geometry.SourceTensorCurl

namespace GeneratedFoundations.Geometry.SourceTensorRoughIdentity

attribute [local irreducible] coefficientCovariant coefficientConnection coefficientRough

private theorem scalar_casimir (m : ℕ) (v : HilbertCarrier m) :
    ((m : ℂ) * ((m : ℂ) + 2)) • v =
      -(unitHilbertAxis m 0 (unitHilbertAxis m 0 v) +
        unitHilbertAxis m 1 (unitHilbertAxis m 1 v) +
        unitHilbertAxis m 2 (unitHilbertAxis m 2 v)) := by
  have h := coefficientDivergence_gradient m v
  simpa only [SourceOneFormDifferential.coefficientDivergence,
    coefficientGradient, Fin.sum_univ_three, neg_neg]
    using (congrArg Neg.neg h).symm

private def derivative (m : ℕ) (i : Fin 3) (H : TensorCoefficients m) :
    TensorCoefficients m := fun a b => unitHilbertAxis m i (H a b)

private theorem connection_derivative (m : ℕ) (i : Fin 3)
    (H : TensorCoefficients m) (a b : Fin 3) :
    coefficientConnection m i (derivative m i H) a b =
      unitHilbertAxis m i (coefficientConnection m i H a b) := by
  simp only [coefficientConnection, derivative, map_sub, map_neg, map_sum, map_smul]

private theorem covariant_square (m : ℕ) (i : Fin 3)
    (H : TensorCoefficients m) (a b : Fin 3) :
    coefficientCovariant m i (coefficientCovariant m i H) a b =
      unitHilbertAxis m i (unitHilbertAxis m i (H a b)) +
      (2 : ℂ) • unitHilbertAxis m i (coefficientConnection m i H a b) +
      coefficientConnection m i (coefficientConnection m i H) a b := by
  have hcov : coefficientCovariant m i H =
      derivative m i H + coefficientConnection m i H := by
    funext a b
    simp only [coefficientCovariant, derivative, Pi.add_apply]
  rw [hcov, coefficientCovariant, coefficientConnection_add]
  simp only [Pi.add_apply]
  rw [connection_derivative]
  simp only [derivative, map_add]
  module

private def algebraConnection {V : Type*} [AddCommGroup V] [Module ℂ V]
    (i : Fin 3) (H : Fin 3 → Fin 3 → V) : Fin 3 → Fin 3 → V := fun a b =>
  -(∑ c : Fin 3, (koszul i a c : ℂ) • H c b) -
    ∑ c : Fin 3, (koszul i b c : ℂ) • H a c

private theorem algebra_connection_square {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H : Fin 3 → Fin 3 → V)
    (hs : ∀ a b, H a b = H b a) (ht : (∑ a : Fin 3, H a a) = 0)
    (a b : Fin 3) :
    (∑ i : Fin 3, algebraConnection i (algebraConnection i H) a b) =
        (-6 : ℂ) • H a b := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs21 := hs 2 1
  have ht22 : H 2 2 = -(H 0 0 + H 1 1) := by
    apply eq_neg_of_add_eq_zero_right
    simpa only [Fin.sum_univ_three] using ht
  fin_cases a <;> fin_cases b <;>
    simp [algebraConnection, Fin.sum_univ_three, koszul_table,
      hs10, hs20, hs21, ht22] <;> module

private theorem connection_square_sum (m : ℕ) (H : TensorCoefficients m)
    (hs : ∀ a b, H a b = H b a) (ht : (∑ a : Fin 3, H a a) = 0)
    (a b : Fin 3) :
    (∑ i : Fin 3,
      coefficientConnection m i (coefficientConnection m i H) a b) =
        (-6 : ℂ) • H a b := by
  simpa only [coefficientConnection, algebraConnection]
    using algebra_connection_square H hs ht a b

set_option maxHeartbeats 800000 in
private theorem connection_derivative_sum (m : ℕ) (H : TensorCoefficients m)
    (hs : ∀ a b, H a b = H b a) (ht : (∑ a : Fin 3, H a a) = 0)
    (a b : Fin 3) :
    (∑ i : Fin 3, unitHilbertAxis m i (coefficientConnection m i H a b)) =
      (6 : ℂ) • H a b - coefficientTensorCurl m H a b -
        coefficientTensorCurl m H b a := by
  have hs10 := hs 1 0
  have hs20 := hs 2 0
  have hs21 := hs 2 1
  fin_cases a <;> fin_cases b <;>
    simp [curl_symmetric_tracefree m H hs ht, coefficientCurl,
      coefficientConnection, Fin.sum_univ_three, koszul_table,
      map_add, map_sub, map_neg, map_smul, hs10, hs20, hs21] <;> module

/-- Expansion of the actual two-index connection on the trace-free kernel. -/
theorem rough_curl_tracefree (m : ℕ) (H : TensorCoefficients m)
    (hs : ∀ a b, H a b = H b a) (ht : (∑ a : Fin 3, H a a) = 0)
    (a b : Fin 3) :
    coefficientRough m H a b =
      ((m : ℂ) * ((m : ℂ) + 2) - 6) • H a b +
        (2 : ℂ) • coefficientTensorCurl m H a b +
          (2 : ℂ) • coefficientTensorCurl m H b a := by
  simp only [coefficientRough, Pi.neg_apply, Finset.sum_apply, covariant_square,
    Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [connection_square_sum m H hs ht a b,
    connection_derivative_sum m H hs ht a b]
  have hc : (∑ i : Fin 3, unitHilbertAxis m i (unitHilbertAxis m i (H a b))) =
      -(((m : ℂ) * ((m : ℂ) + 2)) • H a b) := by
    apply neg_injective
    simpa only [Fin.sum_univ_three, neg_neg, add_assoc] using
      (scalar_casimir m (H a b)).symm
  rw [hc]
  module

/-- On TT tensors, the original rough differential is curl squared minus
three; this also proves that the rough differential preserves TT. -/
theorem rough_eq_curl_square (m : ℕ) (H : TensorCoefficients m)
    (hH : H ∈ ttCoefficients m) :
    coefficientRough m H =
      coefficientTensorCurl m (coefficientTensorCurl m H) - (3 : ℂ) • H := by
  rw [curl_square m H hH]
  funext a b
  rw [rough_curl_tracefree m H hH.1 hH.2.1 a b,
    curl_preserves_symmetry m H hH b a]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  module

theorem rough_mem_tt (m : ℕ) (H : TensorCoefficients m)
    (hH : H ∈ ttCoefficients m) : coefficientRough m H ∈ ttCoefficients m := by
  rw [rough_eq_curl_square m H hH]
  exact (ttCoefficients m).sub_mem
    (curl_mem m _ (curl_mem m H hH)) ((ttCoefficients m).smul_mem _ hH)

/-- Possible tensor curl eigenvalues are forced by the original covariant
differential identity, without a branch assumption. -/
theorem tt_curl_eigenvalue (m : ℕ) (c : ℂ) (H : TensorCoefficients m)
    (hH : H ∈ ttCoefficients m) (hne : H ≠ 0)
    (he : coefficientTensorCurl m H = c • H) :
    c = (m : ℂ) + 3 ∨ c = 1 - (m : ℂ) := by
  have h := curl_square m H hH
  rw [he, curl_smul, he, smul_smul, smul_smul] at h
  have hf : ((c - ((m : ℂ) + 3)) * (c + (m : ℂ) - 1)) • H = 0 := by
    calc
      _ = (c * c) • H - (((m : ℂ) * ((m : ℂ) + 2) - 3) • H +
          (4 * c) • H) := by module
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp ((smul_eq_zero.mp hf).resolve_right hne) with hp | hn
  · exact Or.inl (sub_eq_zero.mp hp)
  · right
    linear_combination hn

end GeneratedFoundations.Geometry.SourceTensorRoughIdentity
