module

public import GeneratedFoundations.Geometry.SourceTensorTracefreeBlock
public import GeneratedFoundations.Geometry.SourceTensorRoughIdentity

/-!
# The actual transverse--traceless tensor block

The carrier is the simultaneous kernel of symmetry defect, trace and the
previously computed tensor divergence. It inherits the original nine-component
Haar metric. Tensor curl and the covariant rough operator restrict to this
kernel by differential identities. Symmetry and the spectral theorem are used
only after these restrictions have been constructed.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceTensorCovariantDerivative
open GeneratedFoundations.Geometry.SourceTensorSpectralCore
open GeneratedFoundations.Geometry.SourceTensorCurl
open GeneratedFoundations.Geometry.SourceTensorRoughIdentity

namespace GeneratedFoundations.Geometry.SourceTensorTTBlock

private theorem square_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (v : V) (c : ℂ) (he : T v = c • v) :
    T (T v) - (3 : ℂ) • v = (c ^ 2 - 3) • v := by
  rw [he, map_smul, he, smul_smul, pow_two, sub_smul]

def coefficients (m : ℕ) : TensorBlock m →ₗ[ℂ] TensorCoefficients m where
  toFun H := fun a b => H (a, b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ttSpace (m : ℕ) : Submodule ℂ (TensorBlock m) :=
  (ttCoefficients m).comap (coefficients m)

instance ttSpaceNormed (m : ℕ) : NormedAddCommGroup (ttSpace m) :=
  Submodule.normedAddCommGroup (𝕜 := ℂ) (E := TensorBlock m) (ttSpace m)

instance ttSpaceInner (m : ℕ) : InnerProductSpace ℂ (ttSpace m) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := TensorBlock m) (ttSpace m)

theorem tt_property (m : ℕ) (H : ttSpace m) :
    coefficients m (H : TensorBlock m) ∈ ttCoefficients m := H.property

def curlBlock (m : ℕ) : Module.End ℂ (TensorBlock m) where
  toFun H := WithLp.toLp 2 (fun ab =>
    coefficientTensorCurl m (coefficients m H) ab.1 ab.2)
  map_add' H K := by
    apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
    funext ab
    exact congrFun (congrFun (curl_add m (coefficients m H) (coefficients m K))
      ab.1) ab.2
  map_smul' c H := by
    apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
    funext ab
    exact congrFun (congrFun (curl_smul m c (coefficients m H)) ab.1) ab.2

@[simp] theorem curlBlock_apply (m : ℕ) (H : TensorBlock m) (a b : Fin 3) :
    curlBlock m H (a, b) = coefficientTensorCurl m (coefficients m H) a b := rfl

theorem curlBlock_mem (m : ℕ) (H : ttSpace m) :
    curlBlock m H ∈ ttSpace m := curl_mem m _ (tt_property m H)

theorem roughBlock_mem (m : ℕ) (H : ttSpace m) :
    roughBlock m H ∈ ttSpace m := by
  change coefficients m (roughBlock m H) ∈ ttCoefficients m
  have he : coefficients m (roughBlock m H) =
      coefficientRough m (coefficients m H) := by
    funext a b
    exact roughBlock_component m H a b
  rw [he]
  exact rough_mem_tt m _ (tt_property m H)

def ttCurl (m : ℕ) : Module.End ℂ (ttSpace m) where
  toFun H := ⟨curlBlock m H, curlBlock_mem m H⟩
  map_add' H K := Subtype.ext ((curlBlock m).map_add H K)
  map_smul' c H := Subtype.ext ((curlBlock m).map_smul c H)

def ttRough (m : ℕ) : Module.End ℂ (ttSpace m) where
  toFun H := ⟨roughBlock m H, roughBlock_mem m H⟩
  map_add' H K := Subtype.ext ((roughBlock m).map_add H K)
  map_smul' c H := Subtype.ext ((roughBlock m).map_smul c H)

theorem ttCurl_symmetric (m : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := ttSpace m) (ttCurl m) := by
  intro H K
  have hskew (i : Fin 3) (x y : HilbertCarrier m) :
      inner ℂ (unitHilbertAxis m i x) y =
        -inner ℂ x (unitHilbertAxis m i y) :=
    eq_neg_of_add_eq_zero_left (unitAxis_skew_pairing m i x y)
  have htwoL (x y : HilbertCarrier m) :
      inner ℂ ((2 : ℂ) • x) y = (2 : ℂ) * inner ℂ x y := by
    simpa only [map_ofNat] using (inner_smul_left x y (2 : ℂ))
  have htwoR (x y : HilbertCarrier m) :
      inner ℂ x ((2 : ℂ) • y) = (2 : ℂ) * inner ℂ x y :=
    inner_smul_right x y (2 : ℂ)
  have hH := tt_property m H
  have hK := tt_property m K
  have hHC (a b : Fin 3) : curlBlock m (H : TensorBlock m) (a, b) =
      coefficientCurl m (fun c => (H : TensorBlock m) (c, b)) a +
        (H : TensorBlock m) (a, b) :=
    curl_symmetric_tracefree m _ hH.1 hH.2.1 a b
  have hKC (a b : Fin 3) : curlBlock m (K : TensorBlock m) (a, b) =
      coefficientCurl m (fun c => (K : TensorBlock m) (c, b)) a +
        (K : TensorBlock m) (a, b) :=
    curl_symmetric_tracefree m _ hK.1 hK.2.1 a b
  change inner ℂ (curlBlock m (H : TensorBlock m)) (K : TensorBlock m) =
    inner ℂ (H : TensorBlock m) (curlBlock m (K : TensorBlock m))
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, hHC, hKC,
    Fin.sum_univ_three, coefficientCurl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    inner_add_left, inner_sub_left, inner_add_right,
    inner_sub_right, htwoL, htwoR, hskew]
  ring

theorem ttRough_symmetric (m : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := ttSpace m) (ttRough m) := by
  intro H K
  exact roughBlock_symmetric m H K

theorem ttRough_energy (m : ℕ) (H : ttSpace m) :
    (inner ℂ H (ttRough m H)).re =
      ∑ i : Fin 3, ‖covariantBlock m i (H : TensorBlock m)‖ ^ 2 :=
  roughBlock_energy m H

theorem ttRough_nonnegative (m : ℕ) (H : ttSpace m) :
    0 ≤ (inner ℂ H (ttRough m H)).re := roughBlock_nonnegative m H

/-- This equality relates the two original differential restrictions on
their actual common domain. -/
theorem ttRough_eq_curl_square (m : ℕ) (H : ttSpace m) :
    ttRough m H = ttCurl m (ttCurl m H) - (3 : ℂ) • H := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
  funext ab
  exact congrFun (congrFun (rough_eq_curl_square m _ (tt_property m H)) ab.1) ab.2

def ttBasis (m : ℕ) : OrthonormalBasis
    (Fin (Module.finrank ℂ (ttSpace m))) ℂ (ttSpace m) :=
  (ttCurl_symmetric m).eigenvectorBasis rfl

/-- A curl eigenfield has its rough eigenvalue fixed by the derived
covariant differential identity. -/
theorem ttRough_of_curl_eigenvector (m : ℕ) (H : ttSpace m) (c : ℂ)
    (he : ttCurl m H = c • H) : ttRough m H = (c ^ 2 - 3) • H :=
  (ttRough_eq_curl_square m H).trans (square_eigenvector (ttCurl m) H c he)

def ttCurlEigenvalue (m : ℕ) (j : Fin (Module.finrank ℂ (ttSpace m))) : ℝ :=
  (ttCurl_symmetric m).eigenvalues rfl j

theorem ttBasis_eigenvector (m : ℕ) (j : Fin (Module.finrank ℂ (ttSpace m))) :
    ttCurl m (ttBasis m j) = (ttCurlEigenvalue m j : ℂ) • ttBasis m j :=
  (ttCurl_symmetric m).apply_eigenvectorBasis rfl j

attribute [local irreducible] ttBasis ttCurlEigenvalue ttCurl ttRough

theorem ttBasis_rough_eigenvector (m : ℕ)
    (j : Fin (Module.finrank ℂ (ttSpace m))) :
    ttRough m (ttBasis m j) =
      ((ttCurlEigenvalue m j ^ 2 - 3 : ℝ) : ℂ) • ttBasis m j := by
  calc
    ttRough m (ttBasis m j) =
        ttCurl m (ttCurl m (ttBasis m j)) - (3 : ℂ) • ttBasis m j :=
      ttRough_eq_curl_square m (ttBasis m j)
    _ = ((ttCurlEigenvalue m j : ℂ) ^ 2 - 3) • ttBasis m j :=
      square_eigenvector (ttCurl m) (ttBasis m j) (ttCurlEigenvalue m j : ℂ)
        (ttBasis_eigenvector m j)
    _ = ((ttCurlEigenvalue m j ^ 2 - 3 : ℝ) : ℂ) • ttBasis m j := by
      exact congrArg (fun c : ℂ => c • ttBasis m j)
        (by push_cast; rfl)

end GeneratedFoundations.Geometry.SourceTensorTTBlock
