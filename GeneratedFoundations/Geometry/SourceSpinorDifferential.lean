module

public import GeneratedFoundations.Geometry.SourceOneFormDifferential
public import GeneratedFoundations.Geometry.SourceClebschGordan
public import GeneratedFoundations.Geometry.SourceSpinorConnection

/-!
# Spin differentiation in the generated orthonormal source frame

Clifford multiplication uses the matrices of the original unit source
velocities. The connection coefficients are computed by the metric Koszul
formula from their commutators. Thus the constant in the contracted spin
connection is an output of the frame, not a prescribed Dirac eigenvalue.

The polynomial part below differentiates the same source representations as
the scalar and one-form constructions. Its explicit polynomial splitting
will be used before passing to the original Haar field space.
-/

@[expose] public section

noncomputable section

open Module MvPolynomial
open scoped BigOperators
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights
open GeneratedFoundations.Geometry.SourcePolynomialCasimir
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceClebschGordan
open GeneratedFoundations.Geometry.SourceSpinorConnection

namespace GeneratedFoundations.Geometry.SourceSpinorDifferential

/-- First-order spin differentiation, before adding the contracted connection. -/
def polynomialKinetic (m : ℕ) : Module.End ℂ (PairCarrier m) :=
  ((weightOperator m).comp (LinearMap.fst ℂ _ _) +
    (2 : ℂ) • (lowering m).comp (LinearMap.snd ℂ _ _)).prod
      ((2 : ℂ) • (raising m).comp (LinearMap.fst ℂ _ _) -
        (weightOperator m).comp (LinearMap.snd ℂ _ _))

/-- The connection term is the previously computed matrix contraction. -/
def polynomialDirac (m : ℕ) : Module.End ℂ (PairCarrier m) :=
  polynomialKinetic m + (3 / 2 : ℂ) • (1 : Module.End ℂ (PairCarrier m))

def cliffordPair (m : ℕ) (i : Fin 3) : Module.End ℂ (PairCarrier m) :=
  ((clifford i 0 0) • (LinearMap.fst ℂ (Carrier m) (Carrier m)) +
    (clifford i 0 1) • (LinearMap.snd ℂ (Carrier m) (Carrier m))).prod
      ((clifford i 1 0) • (LinearMap.fst ℂ (Carrier m) (Carrier m)) +
        (clifford i 1 1) • (LinearMap.snd ℂ (Carrier m) (Carrier m)))

/-- This is the actual Clifford contraction of the differentiated source
axes, expressed in the already generated polynomial coordinates. -/
theorem polynomialKinetic_eq_contraction (m : ℕ) :
    polynomialKinetic m = ∑ i : Fin 3,
      (cliffordPair m i).comp
        ((polynomialAxis m i).prodMap (polynomialAxis m i)) := by
  apply LinearMap.ext
  intro p
  apply Prod.ext <;>
    simp [polynomialKinetic, cliffordPair, clifford, unitAxis, axisVelocity, spinMatrix,
      spinMatrix1, spinMatrix2, spinMatrix3, polynomialAxis, Fin.sum_univ_three, smul_add,
      smul_sub, smul_smul] <;>
    match_scalars <;> ring_nf <;> norm_num

private theorem euler (m : ℕ) (p : Carrier m) :
    X 0 * pderiv 0 (p : PolynomialSpace) + X 1 * pderiv 1 (p : PolynomialSpace) =
      C (m : ℂ) * (p : PolynomialSpace) := by
  have h : X 0 * pderiv 0 (p : PolynomialSpace) + X 1 * pderiv 1 (p : PolynomialSpace) =
      (m : ℂ) • (p : PolynomialSpace) := by
    simpa only [Fin.sum_univ_two, Nat.cast_smul_eq_nsmul] using
      p.property.sum_X_mul_pderiv
  simpa only [smul_eq_C_mul] using h

/-- The upper polynomial summand is an actual eigenspace of the differentiated
operator. Its vectors are constructed by the Euler section. -/
theorem kinetic_eulerSection (k : ℕ) (f : Carrier (k + 2)) :
    polynomialKinetic (k + 1) (eulerSection k f) =
      (k + 1 : ℂ) • eulerSection k f := by
  have h0 := euler (k + 1) (derivative (k + 1) 0 f)
  have h1 := euler (k + 1) (derivative (k + 1) 1 f)
  simp only [derivative_coe, Nat.cast_add, Nat.cast_one, map_add, map_one,
    mixed_partials_commute] at h0 h1
  apply Prod.ext <;> apply Subtype.ext
  · simp only [polynomialKinetic, Function.prod_apply, LinearMap.prod_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, weightOperator, raising,
    lowering, LinearMap.sub_apply, transfer_coe, Submodule.coe_add, Submodule.coe_sub,
    Prod.smul_fst, Prod.smul_snd, eulerSection, LinearMap.smul_apply, derivative_coe,
    Submodule.coe_smul, smul_eq_C_mul, pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
    map_add, map_ofNat, map_one, mixed_partials_commute]
    linear_combination C ((k + 2 : ℂ)⁻¹) * h0
  · simp only [polynomialKinetic, Function.prod_apply, LinearMap.prod_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    weightOperator, raising, lowering, transfer_coe, Submodule.coe_sub, Prod.smul_fst,
    Prod.smul_snd, eulerSection, LinearMap.smul_apply, derivative_coe, Submodule.coe_smul,
    smul_eq_C_mul, pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add, map_add, map_ofNat,
    map_one, mixed_partials_commute]
    linear_combination C ((k + 2 : ℂ)⁻¹) * h1

/-- The lower polynomial summand is the determinant-kernel eigenspace. -/
theorem kinetic_determinantKernel (k : ℕ) (f : Carrier k) :
    polynomialKinetic (k + 1) (determinantKernel k f) =
      (-(k + 3 : ℂ)) • determinantKernel k f := by
  have he := euler k f
  apply Prod.ext <;> apply Subtype.ext
  · simp only [polynomialKinetic, Function.prod_apply, LinearMap.prod_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, weightOperator, raising,
    lowering, LinearMap.sub_apply, transfer_coe, Submodule.coe_add, Submodule.coe_sub,
    LinearMap.smul_apply, determinantKernel, LinearMap.neg_apply, multiplyVariable_coe,
    Prod.smul_fst, Submodule.coe_neg, Submodule.coe_smul, smul_eq_C_mul, map_neg, pderiv_mul,
    pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_mul, one_mul, zero_add,
    map_add, map_ofNat]
    linear_combination X 1 * he
  · simp only [polynomialKinetic, Function.prod_apply, LinearMap.prod_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    weightOperator, raising, lowering, transfer_coe, Submodule.coe_sub, LinearMap.smul_apply,
    determinantKernel, LinearMap.neg_apply, multiplyVariable_coe, Prod.smul_snd,
    Submodule.coe_neg, Submodule.coe_smul, smul_eq_C_mul, map_neg, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_mul, one_mul, zero_add, map_add,
    map_ofNat]
    linear_combination -(X 0) * he

/-- The explicit polynomial splitting diagonalizes the first-order
derivative on its entire carrier, not just on selected highest weights. -/
theorem kinetic_joinPair (k : ℕ) (p : Carrier (k + 2) × Carrier k) :
    polynomialKinetic (k + 1) (joinPair k p) =
      joinPair k ((k + 1 : ℂ) • p.1, (-(k + 3 : ℂ)) • p.2) := by
  change polynomialKinetic (k + 1)
      (eulerSection k p.1 + determinantKernel k p.2) = _
  rw [map_add, kinetic_eulerSection, kinetic_determinantKernel]
  change _ = eulerSection k ((k + 1 : ℂ) • p.1) +
    determinantKernel k ((-(k + 3 : ℂ)) • p.2)
  rw [map_smul, map_smul]

theorem splitPair_kinetic (k : ℕ) (p : PairCarrier (k + 1)) :
    splitPair k (polynomialKinetic (k + 1) p) =
      ((k + 1 : ℂ) • (splitPair k p).1,
        (-(k + 3 : ℂ)) • (splitPair k p).2) := by
  have h := congrArg (splitPair k) (kinetic_joinPair k (splitPair k p))
  simpa only [join_split, split_join] using h

/-- These are all possible first-order eigenvalues in every positive
homogeneous source degree. The inverse of the explicit splitting proves
that no additional polarization can be hidden between the two summands. -/
theorem kinetic_eigenvalue {k : ℕ} {c : ℂ} (p : PairCarrier (k + 1))
    (hp : p ≠ 0) (he : polynomialKinetic (k + 1) p = c • p) :
    c = (k + 1 : ℂ) ∨ c = -(k + 3 : ℂ) := by
  have h := splitPair_kinetic k p
  rw [he, map_smul] at h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  by_cases hq : (splitPair k p).1 = 0
  · have hr : (splitPair k p).2 ≠ 0 := by
      intro hr
      have hs : splitPair k p = 0 := Prod.ext hq hr
      have hj := congrArg (joinPair k) hs
      rw [join_split, map_zero] at hj
      exact hp hj
    right
    have hc : (c + (k + 3 : ℂ)) • (splitPair k p).2 = 0 := by
      simp only [Prod.smul_snd] at h1
      calc
        _ = c • (splitPair k p).2 - (-(k + 3 : ℂ)) • (splitPair k p).2 := by module
        _ = 0 := by rw [h1]; module
    exact eq_neg_of_add_eq_zero_left ((smul_eq_zero.mp hc).resolve_right hr)
  · left
    have hc : (c - (k + 1 : ℂ)) • (splitPair k p).1 = 0 := by
      simp only [Prod.smul_fst] at h0
      calc
        _ = c • (splitPair k p).1 - (k + 1 : ℂ) • (splitPair k p).1 := sub_smul _ _ _
        _ = 0 := by rw [h0]; module
    exact sub_eq_zero.mp ((smul_eq_zero.mp hc).resolve_right hq)

end GeneratedFoundations.Geometry.SourceSpinorDifferential
