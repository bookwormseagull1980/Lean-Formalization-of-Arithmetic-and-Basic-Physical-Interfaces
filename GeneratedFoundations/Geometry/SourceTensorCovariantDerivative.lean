module

public import GeneratedFoundations.Geometry.SourceSpinorConnection
public import GeneratedFoundations.Geometry.SourceOneFormDifferential

/-!
# Covariant tensor differentiation in the generated trace-metric frame

The connection coefficients are the Koszul coefficients of the actual source
frame. They act on both covariant tensor indices. Matrix-coefficient synthesis
intertwines this differential and its second-order rough operator with finite
operators on the original source coefficient spaces. Symmetry is preserved by
the connection. No tensor eigenvalue or TT spectral decomposition is used in
these constructions.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceSpinorConnection
open GeneratedFoundations.Geometry.SourceOneFormDifferential

namespace GeneratedFoundations.Geometry.SourceTensorCovariantDerivative

abbrev TensorCoefficients (m : ℕ) := Fin 3 → Fin 3 → HilbertCarrier m

abbrev SourceTensor := Fin 3 → Fin 3 → SU2 → ℂ

/-- Metric compatibility follows directly from the Koszul formula. -/
theorem koszul_skew (i a b : Fin 3) : koszul i a b = -koszul i b a := by
  simp only [koszul, tracePair, Matrix.conjTranspose_sub, sub_mul, Matrix.trace_sub,
    Complex.sub_re]
  ring

theorem koszul_diagonal (i a : Fin 3) : koszul i a a = 0 := by
  have h := koszul_skew i a a
  linarith

/-- The unit source directions have zero self-acceleration in the derived
connection. Thus the rough operator needs no extra frame-drift term. -/
theorem koszul_geodesic (i c : Fin 3) : koszul i i c = 0 := by
  fin_cases i <;> fin_cases c <;>
    (norm_num [koszul, tracePair, unitAxis, axisVelocity, spinMatrix,
      spinMatrix1, spinMatrix2, spinMatrix3, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> ring_nf <;>
      norm_num [Complex.neg_re])

def coefficientConnection (m : ℕ) (i : Fin 3) (H : TensorCoefficients m) :
    TensorCoefficients m := fun a b =>
  -(∑ c : Fin 3, (koszul i a c : ℂ) • H c b) -
    ∑ c : Fin 3, (koszul i b c : ℂ) • H a c

def coefficientCovariant (m : ℕ) (i : Fin 3) (H : TensorCoefficients m) :
    TensorCoefficients m := fun a b =>
  unitHilbertAxis m i (H a b) + coefficientConnection m i H a b

def covariant (i : Fin 3) (H : SourceTensor) : SourceTensor := fun a b g =>
  unitAxisDerivative i (H a b) g -
    (∑ c : Fin 3, (koszul i a c : ℂ) * H c b g) -
    ∑ c : Fin 3, (koszul i b c : ℂ) * H a c g

def coefficientTensor (m : ℕ) (v : HilbertCarrier m) (H : TensorCoefficients m) :
    SourceTensor := fun a b => matrixCoefficient m v (H a b)

/-- Both tensor-index connection terms are retained in the actual field
differential. The source derivative supplies its first-order part. -/
theorem covariant_coefficientTensor (m : ℕ) (i : Fin 3)
    (v : HilbertCarrier m) (H : TensorCoefficients m) :
    covariant i (coefficientTensor m v H) =
      coefficientTensor m v (coefficientCovariant m i H) := by
  funext a b g
  have hinner (c : ℂ) (u : HilbertCarrier m) :
      inner ℂ v (c • u) = c * inner ℂ v u := inner_smul_right v u c
  simp only [covariant, coefficientTensor, unitAxisDerivative_matrixCoefficient,
    coefficientCovariant, coefficientConnection, matrixCoefficient_apply, map_add, map_sub,
    map_neg, map_sum, map_smul, inner_add_right, inner_sub_right, inner_neg_right, inner_sum,
    hinner]
  ring

def coefficientRough (m : ℕ) (H : TensorCoefficients m) : TensorCoefficients m :=
  -∑ i : Fin 3, coefficientCovariant m i (coefficientCovariant m i H)

def rough (H : SourceTensor) : SourceTensor :=
  -∑ i : Fin 3, covariant i (covariant i H)

theorem rough_coefficientTensor (m : ℕ) (v : HilbertCarrier m)
    (H : TensorCoefficients m) :
    rough (coefficientTensor m v H) =
      coefficientTensor m v (coefficientRough m H) := by
  simp only [rough, covariant_coefficientTensor]
  funext a b g
  simp only [coefficientTensor, coefficientRough, Pi.neg_apply, Finset.sum_apply,
    matrixCoefficient_apply]
  simp only [map_neg, map_sum, inner_neg_right, inner_sum]

theorem coefficientConnection_add (m : ℕ) (i : Fin 3)
    (H K : TensorCoefficients m) :
    coefficientConnection m i (H + K) =
      coefficientConnection m i H + coefficientConnection m i K := by
  funext a b
  simp only [coefficientConnection, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  module

theorem coefficientConnection_smul (m : ℕ) (i : Fin 3) (c : ℂ)
    (H : TensorCoefficients m) :
    coefficientConnection m i (c • H) = c • coefficientConnection m i H := by
  funext a b
  simp only [coefficientConnection, Pi.smul_apply, smul_smul, smul_sub, smul_neg,
    Finset.smul_sum, mul_comm]

def covariantLinear (m : ℕ) (i : Fin 3) :
    Module.End ℂ (TensorCoefficients m) where
  toFun := coefficientCovariant m i
  map_add' H K := by
    funext a b
    simp only [coefficientCovariant, Pi.add_apply, map_add, coefficientConnection_add]
    module
  map_smul' c H := by
    funext a b
    simp only [coefficientCovariant, Pi.smul_apply, map_smul, coefficientConnection_smul,
      smul_add, RingHom.id_apply]

def roughLinear (m : ℕ) : Module.End ℂ (TensorCoefficients m) :=
  -∑ i : Fin 3, (covariantLinear m i).comp (covariantLinear m i)

theorem roughLinear_apply (m : ℕ) (H : TensorCoefficients m) :
    roughLinear m H = coefficientRough m H := by
  simp only [roughLinear, coefficientRough, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, covariantLinear, LinearMap.coe_mk, AddHom.coe_mk]

theorem covariant_symmetric (m : ℕ) (i : Fin 3) (H : TensorCoefficients m)
    (hH : ∀ a b, H a b = H b a) :
    ∀ a b, coefficientCovariant m i H a b = coefficientCovariant m i H b a := by
  intro a b
  have hleft : (∑ c : Fin 3, (koszul i a c : ℂ) • H c b) =
      ∑ c : Fin 3, (koszul i a c : ℂ) • H b c := by
    exact Finset.sum_congr rfl fun c _ => congrArg _ (hH c b)
  have hright : (∑ c : Fin 3, (koszul i b c : ℂ) • H a c) =
      ∑ c : Fin 3, (koszul i b c : ℂ) • H c a := by
    exact Finset.sum_congr rfl fun c _ => congrArg _ (hH a c)
  rw [coefficientCovariant, coefficientCovariant, hH a b,
    coefficientConnection, coefficientConnection, hleft, hright]
  module

theorem coefficientConnection_trace (m : ℕ) (i : Fin 3)
    (H : TensorCoefficients m) :
    (∑ a : Fin 3, coefficientConnection m i H a a) = 0 := by
  have hswap : (∑ a : Fin 3, ∑ c : Fin 3, (koszul i a c : ℂ) • H c a) =
      -(∑ a : Fin 3, ∑ c : Fin 3, (koszul i a c : ℂ) • H a c) := by
    rw [Finset.sum_comm]
    have he (a c : Fin 3) : (koszul i c a : ℂ) • H a c =
        -((koszul i a c : ℂ) • H a c) := by
      rw [koszul_skew i c a, Complex.ofReal_neg]
      module
    simp_rw [he]
    simp only [Finset.sum_neg_distrib]
  simp only [coefficientConnection, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hswap]
  module

theorem covariant_trace_zero (m : ℕ) (i : Fin 3) (H : TensorCoefficients m)
    (hH : (∑ a : Fin 3, H a a) = 0) :
    (∑ a : Fin 3, coefficientCovariant m i H a a) = 0 := by
  simp only [coefficientCovariant, Finset.sum_add_distrib]
  rw [← map_sum, hH, map_zero, coefficientConnection_trace, add_zero]

attribute [local irreducible] coefficientCovariant coefficientConnection coefficientRough

set_option maxHeartbeats 800000 in
theorem rough_symmetric (m : ℕ) (H : TensorCoefficients m)
    (hH : ∀ a b, H a b = H b a) :
    ∀ a b, coefficientRough m H a b = coefficientRough m H b a := by
  intro a b
  simp only [coefficientRough, Pi.neg_apply, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact covariant_symmetric m i _ (covariant_symmetric m i H hH) a b

theorem rough_trace_zero (m : ℕ) (H : TensorCoefficients m)
    (hH : (∑ a : Fin 3, H a a) = 0) :
    (∑ a : Fin 3, coefficientRough m H a a) = 0 := by
  simp only [coefficientRough, Pi.neg_apply, Finset.sum_apply, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  have hzero (i : Fin 3) :
      (∑ a : Fin 3, coefficientCovariant m i (coefficientCovariant m i H) a a) = 0 :=
    covariant_trace_zero m i _ (covariant_trace_zero m i H hH)
  simp only [hzero, Finset.sum_const_zero, neg_zero]

def coefficientDivergence (m : ℕ) (H : TensorCoefficients m) :
    Fin 3 → HilbertCarrier m := fun b =>
  -∑ a : Fin 3, coefficientCovariant m a H a b

/-- The transverse--traceless constraint space is defined on the original
tensor coefficient carrier, before any spectral classification. -/
def ttCoefficients (m : ℕ) : Submodule ℂ (TensorCoefficients m) where
  carrier := {H | (∀ a b, H a b = H b a) ∧
    (∑ a : Fin 3, H a a) = 0 ∧ coefficientDivergence m H = 0}
  zero_mem' := by
    refine ⟨fun _ _ => rfl, by simp, ?_⟩
    funext b
    simp [coefficientDivergence, coefficientCovariant, coefficientConnection]
  add_mem' := by
    intro H K hH hK
    refine ⟨fun a b => by simp only [Pi.add_apply, hH.1 a b, hK.1 a b], ?_, ?_⟩
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hH.2.1, hK.2.1, add_zero]
    · funext b
      change -(∑ a : Fin 3, covariantLinear m a (H + K) a b) = 0
      simp only [map_add, Pi.add_apply, Finset.sum_add_distrib, neg_add_rev]
      have h1 := congrFun hH.2.2 b
      have h2 := congrFun hK.2.2 b
      change -(∑ a : Fin 3, covariantLinear m a H a b) = 0 at h1
      change -(∑ a : Fin 3, covariantLinear m a K a b) = 0 at h2
      rw [h1, h2, add_zero]
  smul_mem' := by
    intro c H hH
    refine ⟨fun a b => by simp only [Pi.smul_apply, hH.1 a b], ?_, ?_⟩
    · simp only [Pi.smul_apply, ← Finset.smul_sum, hH.2.1, smul_zero]
    · funext b
      change -(∑ a : Fin 3, covariantLinear m a (c • H) a b) = 0
      simp only [map_smul, Pi.smul_apply, ← Finset.smul_sum, ← smul_neg]
      have h := congrFun hH.2.2 b
      change -(∑ a : Fin 3, covariantLinear m a H a b) = 0 at h
      rw [h, smul_zero]

end GeneratedFoundations.Geometry.SourceTensorCovariantDerivative
