module

public import GeneratedFoundations.Geometry.SourceTensorCovariantDerivative
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Tensor connection energy in the original source coefficient metric

The nine tensor components carry the sum of the original Haar-induced
inner products. The covariant derivatives include both index connections
computed by the Koszul formula. Their skewness is proved before applying
the finite spectral theorem to the resulting rough operator.

The complete block here contains all two-tensors. Restriction to the
transverse--traceless differential kernel requires its invariance and is
not supplied by this block diagonalization.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceSpinorConnection
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceTensorCovariantDerivative

namespace GeneratedFoundations.Geometry.SourceTensorSpectralCore

attribute [local irreducible] coefficientCovariant coefficientConnection

abbrev TensorBlock (m : ℕ) :=
  PiLp 2 (fun _ : Fin 3 × Fin 3 => HilbertCarrier m)

instance tensorBlockInner (m : ℕ) : InnerProductSpace ℂ (TensorBlock m) :=
  PiLp.innerProductSpace (fun _ : Fin 3 × Fin 3 => HilbertCarrier m)

def covariantBlock (m : ℕ) (i : Fin 3) : Module.End ℂ (TensorBlock m) where
  toFun H := WithLp.toLp 2 (fun ab =>
    coefficientCovariant m i (fun a b => H (a, b)) ab.1 ab.2)
  map_add' H K := by
    apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
    funext ab
    exact congrFun (congrFun
      ((covariantLinear m i).map_add (fun a b => H (a, b))
        (fun a b => K (a, b))) ab.1) ab.2
  map_smul' c H := by
    apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
    funext ab
    exact congrFun (congrFun
      ((covariantLinear m i).map_smul c (fun a b => H (a, b))) ab.1) ab.2

@[simp] theorem covariantBlock_apply (m : ℕ) (i : Fin 3)
    (H : TensorBlock m) (a b : Fin 3) :
    covariantBlock m i H (a, b) =
      coefficientCovariant m i (fun a b => H (a, b)) a b := rfl

set_option maxHeartbeats 800000 in
/-- Integration by parts uses the same source derivative and the metric
Koszul connection on both tensor indices. -/
theorem covariantBlock_skew (m : ℕ) (i : Fin 3) (H K : TensorBlock m) :
    inner ℂ (covariantBlock m i H) K =
      -inner ℂ H (covariantBlock m i K) := by
  have haxis (x y : HilbertCarrier m) :
      inner ℂ (unitHilbertAxis m i x) y =
        -inner ℂ x (unitHilbertAxis m i y) :=
    eq_neg_of_add_eq_zero_left (unitAxis_skew_pairing m i x y)
  have hleft (c : ℂ) (x y : HilbertCarrier m) :
      inner ℂ (c • x) y = conj c * inner ℂ x y :=
    inner_smul_left x y c
  have hright (c : ℂ) (x y : HilbertCarrier m) :
      inner ℂ x (c • y) = c * inner ℂ x y :=
    inner_smul_right x y c
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, covariantBlock_apply,
    coefficientCovariant, coefficientConnection, inner_add_left,
    inner_sub_left, inner_neg_left, inner_sum, sum_inner, hleft,
    inner_add_right, inner_sub_right, inner_neg_right, hright,
    Complex.conj_ofReal, haxis]
  simp only [Fin.sum_univ_three, koszul_diagonal, Complex.ofReal_zero,
    zero_mul, koszul_skew i 1 0, koszul_skew i 2 0, koszul_skew i 2 1,
    Complex.ofReal_neg, neg_mul]
  ring

def roughBlock (m : ℕ) : Module.End ℂ (TensorBlock m) :=
  -∑ i : Fin 3, (covariantBlock m i).comp (covariantBlock m i)

@[simp] theorem roughBlock_apply (m : ℕ) (H : TensorBlock m) :
    roughBlock m H = -∑ i : Fin 3, covariantBlock m i (covariantBlock m i H) := by
  simp only [roughBlock, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.comp_apply]

theorem roughBlock_component (m : ℕ) (H : TensorBlock m) (a b : Fin 3) :
    roughBlock m H (a, b) =
      coefficientRough m (fun a b => H (a, b)) a b := by
  simp only [roughBlock_apply, coefficientRough, Fin.sum_univ_three,
    Pi.neg_apply, Pi.add_apply]
  rfl

theorem rough_pairing_right (m : ℕ) (H K : TensorBlock m) :
    inner ℂ H (roughBlock m K) =
      ∑ i : Fin 3, inner ℂ (covariantBlock m i H) (covariantBlock m i K) := by
  rw [roughBlock_apply, inner_neg_right, inner_sum]
  have h (i : Fin 3) :
      inner ℂ H (covariantBlock m i (covariantBlock m i K)) =
        -inner ℂ (covariantBlock m i H) (covariantBlock m i K) := by
    have h := covariantBlock_skew m i H (covariantBlock m i K)
    rw [h, neg_neg]
  simp only [h, Finset.sum_neg_distrib, neg_neg]

theorem rough_pairing_left (m : ℕ) (H K : TensorBlock m) :
    inner ℂ (roughBlock m H) K =
      ∑ i : Fin 3, inner ℂ (covariantBlock m i H) (covariantBlock m i K) := by
  rw [roughBlock_apply, inner_neg_left, sum_inner]
  simp only [covariantBlock_skew, Finset.sum_neg_distrib, neg_neg]

theorem roughBlock_symmetric (m : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := TensorBlock m) (roughBlock m) := by
  intro H K
  rw [rough_pairing_left, rough_pairing_right]

/-- The energy is the sum of all three covariant derivative norms. Both
connection-index contributions are included before squaring. -/
theorem roughBlock_energy (m : ℕ) (H : TensorBlock m) :
    (inner ℂ H (roughBlock m H)).re =
      ∑ i : Fin 3, ‖covariantBlock m i H‖ ^ 2 := by
  rw [rough_pairing_right]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (covariantBlock m i H)).symm

theorem roughBlock_nonnegative (m : ℕ) (H : TensorBlock m) :
    0 ≤ (inner ℂ H (roughBlock m H)).re := by
  rw [roughBlock_energy]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem tensorBlock_finrank (m : ℕ) :
    Module.finrank ℂ (TensorBlock m) = 9 * (m + 1) := by
  calc
    _ = Module.finrank ℂ (Fin 3 × Fin 3 → HilbertCarrier m) :=
      (WithLp.linearEquiv 2 ℂ (Fin 3 × Fin 3 → HilbertCarrier m)).finrank_eq
    _ = _ := by simp [Module.finrank_pi_fintype, hilbertCarrier_finrank]

def roughBasis (m : ℕ) :
    OrthonormalBasis (Fin (9 * (m + 1))) ℂ (TensorBlock m) :=
  (roughBlock_symmetric m).eigenvectorBasis (tensorBlock_finrank m)

def roughEigenvalue (m : ℕ) (j : Fin (9 * (m + 1))) : ℝ :=
  (roughBlock_symmetric m).eigenvalues (tensorBlock_finrank m) j

theorem roughBasis_eigenvector (m : ℕ) (j : Fin (9 * (m + 1))) :
    roughBlock m (roughBasis m j) =
      (roughEigenvalue m j : ℂ) • roughBasis m j :=
  (roughBlock_symmetric m).apply_eigenvectorBasis (tensorBlock_finrank m) j

end GeneratedFoundations.Geometry.SourceTensorSpectralCore
