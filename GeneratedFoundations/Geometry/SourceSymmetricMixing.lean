module

public import GeneratedFoundations.Geometry.SourceSymmetricWeights
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Nonzero mixing coefficients in every source degree

A single rational determinant-one unitary operation connects every
homogeneous monomial to the highest monomial. Acting on that highest
monomial, the same source operation has a nonzero coefficient in every
degree-compatible monomial. The coefficients are obtained from actual
polynomial substitution and the multinomial coefficient formula.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate
open Module MvPolynomial
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights

namespace GeneratedFoundations.Geometry.SourceSymmetricMixing

/-- On homogeneous degree `m`, evaluation at `(1,0)` extracts the
coefficient of `X₀^m`. -/
theorem homogeneous_top_evaluation {m : ℕ} (p : Carrier m) :
    MvPolynomial.aeval (![1, 0] : Fin 2 → ℂ) (p : PolynomialSpace) =
      (p : PolynomialSpace).coeff (exponentOfIndex m 0).val := by
  let E : Carrier m →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval (![1, 0] : Fin 2 → ℂ)).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ m).subtype
  let L : Carrier m →ₗ[ℂ] ℂ :=
    (MvPolynomial.lcoeff ℂ (exponentOfIndex m 0).val).comp
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ m).subtype
  have hEL : E = L := by
    apply LinearMap.ext_on_range (mode_span m)
    intro k
    change MvPolynomial.aeval (![1, 0] : Fin 2 → ℂ)
      (mode m k : PolynomialSpace) =
        (mode m k : PolynomialSpace).coeff (exponentOfIndex m 0).val
    rw [mode_coefficient]
    by_cases hk : k = 0
    · subst k
      simp [mode_coe]
    · have hkn : k.val ≠ 0 := fun h => hk (Fin.ext h)
      simp [mode_coe, hk, hkn]
  exact congrArg (fun f : Carrier m →ₗ[ℂ] ℂ => f p) hEL

/-- The highest coefficient of an arbitrary actual matrix substitution. -/
theorem action_to_top_coefficient (m : ℕ) (M : Mat2) (k : Fin (m + 1)) :
    (degreeAction m M (mode m k) : PolynomialSpace).coeff
      (exponentOfIndex m 0).val = M 0 0 ^ (m - k.val) * M 0 1 ^ k.val := by
  rw [← homogeneous_top_evaluation]
  change MvPolynomial.aeval (![1, 0] : Fin 2 → ℂ)
    (polynomialAction M (mode m k : PolynomialSpace)) =
      M 0 0 ^ (m - k.val) * M 0 1 ^ k.val
  simp [mode_coe, variableImage, Fin.sum_univ_two]

theorem exponent_multinomial (m : ℕ) (k : Fin (m + 1)) :
    (exponentOfIndex m k).val.multinomial = m.choose k.val := by
  have hk : k.val ≤ m := by omega
  rw [Finsupp.multinomial_eq_of_support_subset
    (Finset.subset_univ (exponentOfIndex m k).val.support),
    Finset.univ_fin2, Nat.binomial_eq_choose Fin.zero_ne_one]
  simp only [exponent_zero, exponent_one, Nat.sub_add_cancel hk]
  exact Nat.choose_symm hk

/-- The two-variable coefficient formula includes the binomial factor,
including at both endpoints and in degree zero. -/
theorem linear_power_coefficient (m : ℕ) (a b : ℂ) (k : Fin (m + 1)) :
    ((C a * X 0 + C b * X 1 : PolynomialSpace) ^ m).coeff
      (exponentOfIndex m k).val =
        (m.choose k.val : ℂ) * a ^ (m - k.val) * b ^ k.val := by
  have hd : (exponentOfIndex m k).val.sum (fun _ n => n) = m :=
    (exponentOfIndex m k).property
  have hp : (exponentOfIndex m k).val.prod
      (fun i n => (![a, b] : Fin 2 → ℂ) i ^ n) =
        a ^ (m - k.val) * b ^ k.val := by
    rw [(exponentOfIndex m k).val.prod_fintype _ (fun _ => pow_zero _)]
    simp [Fin.prod_univ_two]
  have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype
    (![a, b] : Fin 2 → ℂ) (exponentOfIndex m k).val m
  rw [ite_eq_left hd, exponent_multinomial, hp] at h
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    MvPolynomial.smul_eq_C_mul, mul_assoc] using h

/-- The same rational mixing operation works in every homogeneous degree. -/
def mixingSource : SU2 :=
  ⟨canonical (3 / 5) (4 / 5), canonical_mem_specialUnitary _ _ (by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im])⟩

theorem mixing_to_top_coefficient (m : ℕ) (k : Fin (m + 1)) :
    (sourceRepresentation m mixingSource (mode m k) : PolynomialSpace).coeff
      (exponentOfIndex m 0).val = (3 / 5 : ℂ) ^ (m - k.val) * (4 / 5 : ℂ) ^ k.val := by
  simpa [sourceRepresentation, mixingSource, canonical] using
    action_to_top_coefficient m (mixingSource : Mat2) k

theorem mixing_to_top_ne_zero (m : ℕ) (k : Fin (m + 1)) :
    (sourceRepresentation m mixingSource (mode m k) : PolynomialSpace).coeff
      (exponentOfIndex m 0).val ≠ 0 := by
  rw [mixing_to_top_coefficient]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

theorem mixing_from_top_polynomial (m : ℕ) :
    (sourceRepresentation m mixingSource (mode m 0) : PolynomialSpace) =
      (C (3 / 5 : ℂ) * X 0 + C (-4 / 5 : ℂ) * X 1) ^ m := by
  change polynomialAction (mixingSource : Mat2) (mode m 0 : PolynomialSpace) = _
  simp [mode_coe, variableImage, mixingSource, canonical, Fin.sum_univ_two]
  simp only [map_ofNat, neg_div, map_neg, neg_mul]

theorem mixing_from_top_coefficient (m : ℕ) (k : Fin (m + 1)) :
    (sourceRepresentation m mixingSource (mode m 0) : PolynomialSpace).coeff
      (exponentOfIndex m k).val =
        (m.choose k.val : ℂ) * (3 / 5 : ℂ) ^ (m - k.val) * (-4 / 5 : ℂ) ^ k.val := by
  rw [mixing_from_top_polynomial]
  exact linear_power_coefficient m (3 / 5) (-4 / 5) k

/-- Positivity of the natural binomial coefficient, followed by the
injective natural-number cast, rules out cancellation in every degree. -/
theorem mixing_from_top_ne_zero (m : ℕ) (k : Fin (m + 1)) :
    (sourceRepresentation m mixingSource (mode m 0) : PolynomialSpace).coeff
      (exponentOfIndex m k).val ≠ 0 := by
  rw [mixing_from_top_coefficient]
  have hchoose : (m.choose k.val : ℂ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show k.val ≤ m by omega)
  exact mul_ne_zero
    (mul_ne_zero hchoose (pow_ne_zero _ (by norm_num)))
    (pow_ne_zero _ (by norm_num))

end GeneratedFoundations.Geometry.SourceSymmetricMixing
