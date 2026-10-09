module

public import GeneratedFoundations.Geometry.SourceSymmetricWeights
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Tactic.LinearCombination

/-!
# Clebsch–Gordan splitting for the actual source polynomials

The two factors of the intermediate product are actual degree `m`
homogeneous polynomials. Multiplication by the two variables, polynomial
differentiation, and the determinant-one identity construct the splitting.
In particular, a dimension equality is not used to supply the inverse.

The positive-degree result is indexed by `m = k + 1`, so its target is
`Carrier (k + 2) × Carrier k`. The tensor identification uses the established
degree-one polynomial equivalence. All actions below retain the column
substitution convention of `sourceRepresentation`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct
open Module MvPolynomial
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights

namespace GeneratedFoundations.Geometry.SourceClebschGordan

abbrev PairCarrier (m : ℕ) := Carrier m × Carrier m

/-- Multiplication by a coordinate in the actual homogeneous submodule. -/
def multiplyVariable (m : ℕ) (i : Fin 2) : Carrier m →ₗ[ℂ] Carrier (m + 1) where
  toFun p := ⟨(X i : PolynomialSpace) * (p : PolynomialSpace), by
    change ((X i : PolynomialSpace) * (p : PolynomialSpace)).IsHomogeneous (m + 1)
    simpa only [Nat.add_comm 1 m] using (isHomogeneous_X ℂ i).mul p.property⟩
  map_add' p q := Subtype.ext (mul_add (X i) (p : PolynomialSpace) (q : PolynomialSpace))
  map_smul' c p := by
    apply Subtype.ext
    change X i * (c • (p : PolynomialSpace)) = c • (X i * (p : PolynomialSpace))
    simp only [smul_eq_C_mul]
    ring

/-- The actual formal derivative, with its degree drop proved. -/
def derivative (m : ℕ) (i : Fin 2) : Carrier (m + 1) →ₗ[ℂ] Carrier m where
  toFun p := ⟨pderiv i (p : PolynomialSpace), by simpa using p.property.pderiv (i := i)⟩
  map_add' p q := Subtype.ext ((pderiv i).map_add (p : PolynomialSpace) (q : PolynomialSpace))
  map_smul' c p := Subtype.ext ((pderiv i).map_smul c (p : PolynomialSpace))

@[simp] theorem multiplyVariable_coe (m : ℕ) (i : Fin 2) (p : Carrier m) :
    (multiplyVariable m i p : PolynomialSpace) = X i * (p : PolynomialSpace) := rfl

@[simp] theorem derivative_coe (m : ℕ) (i : Fin 2) (p : Carrier (m + 1)) :
    (derivative m i p : PolynomialSpace) = pderiv i p := rfl

def multiplyPair (m : ℕ) : PairCarrier m →ₗ[ℂ] Carrier (m + 1) :=
  (multiplyVariable m 0).comp (LinearMap.fst ℂ _ _) +
    (multiplyVariable m 1).comp (LinearMap.snd ℂ _ _)

def determinantKernel (k : ℕ) : Carrier k →ₗ[ℂ] PairCarrier (k + 1) :=
  (-multiplyVariable k 1).prod (multiplyVariable k 0)

def curlPair (k : ℕ) : PairCarrier (k + 1) →ₗ[ℂ] Carrier k :=
  (derivative k 0).comp (LinearMap.snd ℂ _ _) -
    (derivative k 1).comp (LinearMap.fst ℂ _ _)

def eulerSection (k : ℕ) : Carrier (k + 2) →ₗ[ℂ] PairCarrier (k + 1) :=
  ((k + 2 : ℂ)⁻¹) • ((derivative (k + 1) 0).prod (derivative (k + 1) 1))

def splitPair (k : ℕ) : PairCarrier (k + 1) →ₗ[ℂ] Carrier (k + 2) × Carrier k :=
  (multiplyPair (k + 1)).prod (((k + 2 : ℂ)⁻¹) • curlPair k)

def joinPair (k : ℕ) : Carrier (k + 2) × Carrier k →ₗ[ℂ] PairCarrier (k + 1) :=
  (eulerSection k).comp (LinearMap.fst ℂ _ _) +
    (determinantKernel k).comp (LinearMap.snd ℂ _ _)

private theorem scalar_degree_ne_zero (k : ℕ) : (k + 2 : ℂ) ≠ 0 := by
  exact_mod_cast (show k + 2 ≠ 0 by omega)

private theorem inverse_degree (k : ℕ) :
    C ((k + 2 : ℂ)⁻¹) * C (k + 2 : ℂ) = (1 : PolynomialSpace) := by
  rw [← map_mul, inv_mul_cancel₀ (scalar_degree_ne_zero k), map_one]

private theorem euler_identity (m : ℕ) (p : Carrier m) :
    X 0 * pderiv 0 (p : PolynomialSpace) + X 1 * pderiv 1 (p : PolynomialSpace) =
      C (m : ℂ) * (p : PolynomialSpace) := by
  have h : X 0 * pderiv 0 (p : PolynomialSpace) + X 1 * pderiv 1 (p : PolynomialSpace) =
      (m : ℂ) • (p : PolynomialSpace) := by
    simpa only [Fin.sum_univ_two, Nat.cast_smul_eq_nsmul] using
      p.property.sum_X_mul_pderiv
  simpa only [smul_eq_C_mul] using h

private theorem pderiv_zero_one (p : PolynomialSpace) :
    pderiv 0 (pderiv 1 p) = pderiv 1 (pderiv 0 p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      fin_cases i <;> simp [hp] <;> ring

theorem multiply_eulerSection (k : ℕ) (f : Carrier (k + 2)) :
    multiplyPair (k + 1) (eulerSection k f) = f := by
  apply Subtype.ext
  change X 0 * ((k + 2 : ℂ)⁻¹ • pderiv 0 (f : PolynomialSpace)) +
    X 1 * ((k + 2 : ℂ)⁻¹ • pderiv 1 (f : PolynomialSpace)) = (f : PolynomialSpace)
  simp only [smul_eq_C_mul]
  calc
    _ = C ((k + 2 : ℂ)⁻¹) *
        (X 0 * pderiv 0 (f : PolynomialSpace) + X 1 * pderiv 1 (f : PolynomialSpace)) := by ring
    _ = C ((k + 2 : ℂ)⁻¹) * (C (k + 2 : ℂ) * (f : PolynomialSpace)) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        congrArg (fun p : PolynomialSpace ↦ C ((k + 2 : ℂ)⁻¹) * p)
          (euler_identity (k + 2) f)
    _ = (f : PolynomialSpace) := by rw [← mul_assoc, inverse_degree, one_mul]

theorem multiply_determinantKernel (k : ℕ) (r : Carrier k) :
    multiplyPair (k + 1) (determinantKernel k r) = 0 := by
  apply Subtype.ext
  change X 0 * (-(X 1 * (r : PolynomialSpace))) + X 1 * (X 0 * (r : PolynomialSpace)) = 0
  ring

theorem curl_eulerSection (k : ℕ) (f : Carrier (k + 2)) :
    curlPair k (eulerSection k f) = 0 := by
  apply Subtype.ext
  change pderiv 0 ((k + 2 : ℂ)⁻¹ • pderiv 1 (f : PolynomialSpace)) -
    pderiv 1 ((k + 2 : ℂ)⁻¹ • pderiv 0 (f : PolynomialSpace)) = 0
  simp only [Derivation.map_smul, pderiv_zero_one, sub_self]

theorem curl_determinantKernel (k : ℕ) (r : Carrier k) :
    curlPair k (determinantKernel k r) = (k + 2 : ℂ) • r := by
  apply Subtype.ext
  change pderiv 0 (X 0 * (r : PolynomialSpace)) -
    pderiv 1 (-(X 1 * (r : PolynomialSpace))) = (k + 2 : ℂ) • (r : PolynomialSpace)
  simp only [map_neg, pderiv_mul, pderiv_X_self, one_mul, sub_neg_eq_add, smul_eq_C_mul]
  calc
    _ = X 0 * pderiv 0 (r : PolynomialSpace) + X 1 * pderiv 1 (r : PolynomialSpace) +
        (r : PolynomialSpace) + (r : PolynomialSpace) := by ring
    _ = C (k : ℂ) * (r : PolynomialSpace) + (r : PolynomialSpace) + (r : PolynomialSpace) := by
      rw [euler_identity]
    _ = C (k + 2 : ℂ) * (r : PolynomialSpace) := by simp only [map_add, map_ofNat]; ring

/-- The inverse is established on the polynomials themselves, using Euler's identity. -/
theorem join_split (k : ℕ) (v : PairCarrier (k + 1)) :
    joinPair k (splitPair k v) = v := by
  have hp := euler_identity (k + 1) v.1
  have hq := euler_identity (k + 1) v.2
  apply Prod.ext
  · apply Subtype.ext
    change (k + 2 : ℂ)⁻¹ • pderiv 0
        (X 0 * (v.1 : PolynomialSpace) + X 1 * (v.2 : PolynomialSpace)) +
      -(X 1 * ((k + 2 : ℂ)⁻¹ •
        (pderiv 0 (v.2 : PolynomialSpace) - pderiv 1 (v.1 : PolynomialSpace)))) =
        (v.1 : PolynomialSpace)
    simp only [map_add, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
      one_mul, zero_mul, zero_add, smul_eq_C_mul]
    calc
      _ = C ((k + 2 : ℂ)⁻¹) * ((v.1 : PolynomialSpace) +
          (X 0 * pderiv 0 (v.1 : PolynomialSpace) + X 1 * pderiv 1 (v.1 : PolynomialSpace))) := by ring
      _ = C ((k + 2 : ℂ)⁻¹) * (C (k + 2 : ℂ) * (v.1 : PolynomialSpace)) := by
        rw [hp]
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, map_ofNat]
        ring
      _ = (v.1 : PolynomialSpace) := by rw [← mul_assoc, inverse_degree, one_mul]
  · apply Subtype.ext
    change (k + 2 : ℂ)⁻¹ • pderiv 1
        (X 0 * (v.1 : PolynomialSpace) + X 1 * (v.2 : PolynomialSpace)) +
      X 0 * ((k + 2 : ℂ)⁻¹ •
        (pderiv 0 (v.2 : PolynomialSpace) - pderiv 1 (v.1 : PolynomialSpace))) =
        (v.2 : PolynomialSpace)
    simp only [map_add, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
      one_mul, zero_mul, zero_add, smul_eq_C_mul]
    calc
      _ = C ((k + 2 : ℂ)⁻¹) * ((v.2 : PolynomialSpace) +
          (X 0 * pderiv 0 (v.2 : PolynomialSpace) + X 1 * pderiv 1 (v.2 : PolynomialSpace))) := by ring
      _ = C ((k + 2 : ℂ)⁻¹) * (C (k + 2 : ℂ) * (v.2 : PolynomialSpace)) := by
        rw [hq]
        simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, map_ofNat]
        ring
      _ = (v.2 : PolynomialSpace) := by rw [← mul_assoc, inverse_degree, one_mul]

theorem split_join (k : ℕ) (v : Carrier (k + 2) × Carrier k) :
    splitPair k (joinPair k v) = v := by
  apply Prod.ext
  · change multiplyPair (k + 1) (eulerSection k v.1 + determinantKernel k v.2) = v.1
    rw [map_add, multiply_eulerSection, multiply_determinantKernel, add_zero]
  · change (k + 2 : ℂ)⁻¹ • curlPair k (eulerSection k v.1 + determinantKernel k v.2) = v.2
    rw [map_add, curl_eulerSection, curl_determinantKernel, zero_add, smul_smul,
      inv_mul_cancel₀ (scalar_degree_ne_zero k), one_smul]

def pairClebschGordan (k : ℕ) : PairCarrier (k + 1) ≃ₗ[ℂ] Carrier (k + 2) × Carrier k where
  toFun := splitPair k
  map_add' := (splitPair k).map_add
  map_smul' := (splitPair k).map_smul
  invFun := joinPair k
  left_inv := join_split k
  right_inv := split_join k

/-- The action on the two actual polynomial coefficients of
`X₀ ⊗ p + X₁ ⊗ q`. The row entries here follow from column substitution. -/
def pairAction (m : ℕ) (U : SU2) : Module.End ℂ (PairCarrier m) :=
  (((U : Mat2) 0 0) • (sourceRepresentation m U).comp (LinearMap.fst ℂ _ _) +
    ((U : Mat2) 0 1) • (sourceRepresentation m U).comp (LinearMap.snd ℂ _ _)).prod
  (((U : Mat2) 1 0) • (sourceRepresentation m U).comp (LinearMap.fst ℂ _ _) +
    ((U : Mat2) 1 1) • (sourceRepresentation m U).comp (LinearMap.snd ℂ _ _))

theorem eulerSection_intertwines (k : ℕ) (U : SU2) (f : Carrier (k + 2)) :
    pairAction (k + 1) U (eulerSection k f) =
      eulerSection k (sourceRepresentation (k + 2) U f) := by
  apply Prod.ext <;> apply Subtype.ext
  · change (U : Mat2) 0 0 • polynomialAction (U : Mat2)
        ((k + 2 : ℂ)⁻¹ • pderiv 0 (f : PolynomialSpace)) +
      (U : Mat2) 0 1 • polynomialAction (U : Mat2)
        ((k + 2 : ℂ)⁻¹ • pderiv 1 (f : PolynomialSpace)) =
      (k + 2 : ℂ)⁻¹ • pderiv 0 (polynomialAction (U : Mat2) f)
    rw [pderiv_polynomialAction]
    simp only [smul_eq_C_mul, map_mul, polynomialAction_C]
    ring
  · change (U : Mat2) 1 0 • polynomialAction (U : Mat2)
        ((k + 2 : ℂ)⁻¹ • pderiv 0 (f : PolynomialSpace)) +
      (U : Mat2) 1 1 • polynomialAction (U : Mat2)
        ((k + 2 : ℂ)⁻¹ • pderiv 1 (f : PolynomialSpace)) =
      (k + 2 : ℂ)⁻¹ • pderiv 1 (polynomialAction (U : Mat2) f)
    rw [pderiv_polynomialAction]
    simp only [smul_eq_C_mul, map_mul, polynomialAction_C]
    ring

theorem determinantKernel_intertwines (k : ℕ) (U : SU2) (r : Carrier k) :
    pairAction (k + 1) U (determinantKernel k r) =
      determinantKernel k (sourceRepresentation k U r) := by
  have hd : (U : Mat2) 0 0 * (U : Mat2) 1 1 -
      (U : Mat2) 0 1 * (U : Mat2) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (Matrix.mem_specialUnitaryGroup_iff.mp U.property).2
  have hdC := congrArg (C : ℂ → PolynomialSpace) hd
  simp only [map_sub, map_mul, map_one] at hdC
  apply Prod.ext <;> apply Subtype.ext
  · change (U : Mat2) 0 0 • polynomialAction (U : Mat2) (-(X 1 * (r : PolynomialSpace))) +
      (U : Mat2) 0 1 • polynomialAction (U : Mat2) (X 0 * (r : PolynomialSpace)) =
      -(X 1 * polynomialAction (U : Mat2) r)
    simp only [map_neg, map_mul, polynomialAction_X, variableImage, Fin.sum_univ_two,
      smul_eq_C_mul]
    linear_combination -(X 1 * polynomialAction (U : Mat2) r) * hdC
  · change (U : Mat2) 1 0 • polynomialAction (U : Mat2) (-(X 1 * (r : PolynomialSpace))) +
      (U : Mat2) 1 1 • polynomialAction (U : Mat2) (X 0 * (r : PolynomialSpace)) =
      X 0 * polynomialAction (U : Mat2) r
    simp only [map_neg, map_mul, polynomialAction_X, variableImage, Fin.sum_univ_two,
      smul_eq_C_mul]
    linear_combination (X 0 * polynomialAction (U : Mat2) r) * hdC

theorem joinPair_intertwines (k : ℕ) (U : SU2) (v : Carrier (k + 2) × Carrier k) :
    pairAction (k + 1) U (joinPair k v) =
      joinPair k (sourceRepresentation (k + 2) U v.1, sourceRepresentation k U v.2) := by
  change pairAction (k + 1) U (eulerSection k v.1 + determinantKernel k v.2) =
    eulerSection k (sourceRepresentation (k + 2) U v.1) +
      determinantKernel k (sourceRepresentation k U v.2)
  rw [map_add, eulerSection_intertwines, determinantKernel_intertwines]

theorem splitPair_intertwines (k : ℕ) (U : SU2) (v : PairCarrier (k + 1)) :
    splitPair k (pairAction (k + 1) U v) =
      (sourceRepresentation (k + 2) U (splitPair k v).1,
        sourceRepresentation k U (splitPair k v).2) := by
  apply (pairClebschGordan k).symm.injective
  change joinPair k (splitPair k (pairAction (k + 1) U v)) =
    joinPair k (sourceRepresentation (k + 2) U (splitPair k v).1,
      sourceRepresentation k U (splitPair k v).2)
  rw [join_split, ← joinPair_intertwines, join_split]

/-- The tensor factor is the actual degree-one polynomial carrier, transported
through its proved equivalence with two coordinate coefficients. -/
def tensorPairEquiv (m : ℕ) : Carrier 1 ⊗[ℂ] Carrier m ≃ₗ[ℂ] PairCarrier m :=
  (TensorProduct.congr degreeOneEquiv.symm (LinearEquiv.refl ℂ (Carrier m))).trans
    ((TensorProduct.comm ℂ (Fin 2 → ℂ) (Carrier m)).trans
      ((TensorProduct.piScalarRight ℂ ℂ (Carrier m) (Fin 2)).trans
        (LinearEquiv.finTwoArrow ℂ (Carrier m))))

theorem tensorPairEquiv_tmul (m : ℕ) (v : Fin 2 → ℂ) (p : Carrier m) :
    tensorPairEquiv m (degreeOnePolynomial v ⊗ₜ[ℂ] p) = (v 0 • p, v 1 • p) := by
  change tensorPairEquiv m (degreeOneEquiv v ⊗ₜ[ℂ] p) = _
  simp [tensorPairEquiv, TensorProduct.piScalarRightHom_tmul, LinearEquiv.finTwoArrow]

theorem tensorPairEquiv_intertwines (m : ℕ) (U : SU2) (t : Carrier 1 ⊗[ℂ] Carrier m) :
    tensorPairEquiv m ((sourceRepresentation 1).tprod (sourceRepresentation m) U t) =
      pairAction m U (tensorPairEquiv m t) := by
  have hmaps :
      (tensorPairEquiv m).toLinearMap.comp
          (((sourceRepresentation 1).tprod (sourceRepresentation m)) U) =
        (pairAction m U).comp (tensorPairEquiv m).toLinearMap := by
    apply TensorProduct.ext'
    intro f p
    obtain ⟨v, rfl⟩ := degreeOneEquiv.surjective f
    change tensorPairEquiv m
        (sourceRepresentation 1 U (degreeOnePolynomial v) ⊗ₜ[ℂ] sourceRepresentation m U p) =
      pairAction m U (tensorPairEquiv m (degreeOnePolynomial v ⊗ₜ[ℂ] p))
    rw [degreeOne_intertwines, tensorPairEquiv_tmul, tensorPairEquiv_tmul]
    apply Prod.ext <;>
      simp [pairAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        map_smul, add_smul, smul_smul, mul_comm]
  exact LinearMap.congr_fun hmaps t

/-- Explicit all-positive-degree Clebsch–Gordan linear equivalence. -/
def clebschGordanLinear (k : ℕ) :
    Carrier 1 ⊗[ℂ] Carrier (k + 1) ≃ₗ[ℂ] Carrier (k + 2) × Carrier k :=
  (tensorPairEquiv (k + 1)).trans (pairClebschGordan k)

/-- Clebsch–Gordan for the actual source representation, not an abstract
representation postulated to have the same dimension. -/
def clebschGordan (k : ℕ) :
    ((sourceRepresentation 1).tprod (sourceRepresentation (k + 1))).Equiv
      ((sourceRepresentation (k + 2)).prod (sourceRepresentation k)) :=
  Representation.Equiv.mk (clebschGordanLinear k) (by
    intro U
    apply LinearMap.ext
    intro t
    change splitPair k
        (tensorPairEquiv (k + 1)
          (((sourceRepresentation 1).tprod (sourceRepresentation (k + 1))) U t)) =
      (sourceRepresentation (k + 2) U (splitPair k (tensorPairEquiv (k + 1) t)).1,
        sourceRepresentation k U (splitPair k (tensorPairEquiv (k + 1) t)).2)
    rw [tensorPairEquiv_intertwines, splitPair_intertwines])

/-- A degree-zero carrier element is proved to be its actual constant
polynomial; no new trivial-representation assumption is introduced. -/
theorem degreeZero_eq_constant (p : Carrier 0) :
    (p : PolynomialSpace) = C ((p : PolynomialSpace).coeff 0) :=
  totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr p.property)

def constantEquiv : Carrier 0 ≃ₗ[ℂ] ℂ where
  toFun p := (p : PolynomialSpace).coeff 0
  map_add' p q := by simp
  map_smul' c p := by simp
  invFun c := ⟨C c, isHomogeneous_C (Fin 2) c⟩
  left_inv p := Subtype.ext (degreeZero_eq_constant p).symm
  right_inv c := by simp

theorem source_degreeZero (U : SU2) (p : Carrier 0) :
    sourceRepresentation 0 U p = p := by
  apply Subtype.ext
  change polynomialAction (U : Mat2) p = (p : PolynomialSpace)
  calc
    _ = polynomialAction (U : Mat2) (C ((p : PolynomialSpace).coeff 0)) :=
      congrArg (polynomialAction (U : Mat2)) (degreeZero_eq_constant p)
    _ = C ((p : PolynomialSpace).coeff 0) := polynomialAction_C _ _
    _ = (p : PolynomialSpace) := (degreeZero_eq_constant p).symm

def clebschGordanZeroLinear : Carrier 1 ⊗[ℂ] Carrier 0 ≃ₗ[ℂ] Carrier 1 :=
  (TensorProduct.congr (LinearEquiv.refl ℂ (Carrier 1)) constantEquiv).trans
    (TensorProduct.rid ℂ (Carrier 1))

theorem clebschGordanZeroLinear_tmul (p : Carrier 1) (c : Carrier 0) :
    clebschGordanZeroLinear (p ⊗ₜ[ℂ] c) = constantEquiv c • p := by
  simp [clebschGordanZeroLinear]

/-- The degree-zero endpoint is an independent, actual tensor-unit
identification, rather than an expression involving a negative degree. -/
def clebschGordanZero :
    ((sourceRepresentation 1).tprod (sourceRepresentation 0)).Equiv
      (sourceRepresentation 1) :=
  Representation.Equiv.mk clebschGordanZeroLinear (by
    intro U
    apply TensorProduct.ext'
    intro p c
    change clebschGordanZeroLinear
        (sourceRepresentation 1 U p ⊗ₜ[ℂ] sourceRepresentation 0 U c) =
      sourceRepresentation 1 U (clebschGordanZeroLinear (p ⊗ₜ[ℂ] c))
    rw [source_degreeZero, clebschGordanZeroLinear_tmul, clebschGordanZeroLinear_tmul, map_smul])

end GeneratedFoundations.Geometry.SourceClebschGordan
