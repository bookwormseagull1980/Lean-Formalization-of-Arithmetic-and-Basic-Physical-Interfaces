module

public import GeneratedFoundations.Geometry.SourceSymmetricWeights
public import GeneratedFoundations.Geometry.SourceSymmetricUnitary
public import Mathlib.Tactic.Module

/-!
# The Casimir identity on the actual homogeneous source carriers

The three operators are formed from polynomial degree transfers. Their
quadratic identity follows from commuting polynomial partial derivatives
and Euler's identity on the whole homogeneous carrier. Transport uses the
existing Haar realization of that same carrier.

Identification with analytic derivatives of the source group orbits is a
separate statement. The identities here supply its algebraic normalization;
they do not define a Laplacian by prescribing its eigenvalues.
-/

@[expose] public section

noncomputable section

open Module MvPolynomial
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights
open GeneratedFoundations.Geometry.SourceSymmetricUnitary

namespace GeneratedFoundations.Geometry.SourcePolynomialCasimir

theorem mixed_partials_commute (p : PolynomialSpace) :
    pderiv 0 (pderiv 1 p) = pderiv 1 (pderiv 0 p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      fin_cases i <;> simp [hp] <;> ring

/-- The doubled diagonal weight and both actual degree-transfer products. -/
def polynomialCasimir (m : ℕ) : Module.End ℂ (Carrier m) :=
  weightOperator m * weightOperator m +
    (2 : ℂ) • (raising m * lowering m + lowering m * raising m)

theorem polynomialCasimir_euler (m : ℕ) :
    polynomialCasimir m =
      (transfer m 0 0 + transfer m 1 1) * (transfer m 0 0 + transfer m 1 1) +
        (2 : ℂ) • (transfer m 0 0 + transfer m 1 1) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [polynomialCasimir, weightOperator, raising, lowering,
    Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, transfer_coe]
  simp only [map_add, map_sub, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
    pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1), one_mul, zero_mul,
    zero_add, smul_eq_C_mul, map_ofNat, mixed_partials_commute]
  ring

/-- The scalar follows from Euler's identity, including degree zero. -/
theorem polynomialCasimir_eq_scalar (m : ℕ) :
    polynomialCasimir m =
      ((m : ℂ) * ((m : ℂ) + 2)) • (1 : Module.End ℂ (Carrier m)) := by
  rw [polynomialCasimir_euler, total_degree_operator]
  simp only [smul_mul_smul_comm, mul_one, smul_smul]
  module

theorem polynomialCasimir_apply (m : ℕ) (p : Carrier m) :
    polynomialCasimir m p = ((m : ℂ) * ((m : ℂ) + 2)) • p := by
  rw [polynomialCasimir_eq_scalar]
  rfl

/-- The half-angle first-axis operation in the source column convention. -/
def axisOne (m : ℕ) : Module.End ℂ (Carrier m) :=
  (Complex.I / 2) • (raising m + lowering m)

def axisTwo (m : ℕ) : Module.End ℂ (Carrier m) :=
  (1 / 2 : ℂ) • (lowering m - raising m)

def axisThree (m : ℕ) : Module.End ℂ (Carrier m) :=
  (-Complex.I / 2) • weightOperator m

theorem axis_casimir_polynomial (m : ℕ) :
    (-4 : ℂ) • (axisOne m * axisOne m + axisTwo m * axisTwo m +
      axisThree m * axisThree m) = polynomialCasimir m := by
  have hI : (Complex.I / 2) * (Complex.I / 2) = (-1 / 4 : ℂ) := by
    norm_num [div_mul_div_comm]
  have hnegI : (-Complex.I / 2) * (-Complex.I / 2) = (-1 / 4 : ℂ) := by
    norm_num [div_mul_div_comm]
  have hhalf : (1 / 2 : ℂ) * (1 / 2) = 1 / 4 := by norm_num
  have hsub : (lowering m - raising m) * (lowering m - raising m) =
      lowering m * lowering m - lowering m * raising m -
        (raising m * lowering m - raising m * raising m) := by
    apply LinearMap.ext
    intro p
    simp only [Module.End.mul_apply, LinearMap.sub_apply, map_sub]
    abel
  simp only [axisOne, axisTwo, axisThree, polynomialCasimir,
    smul_mul_smul_comm, hI, hnegI, hhalf, add_mul, mul_add,
    hsub, smul_add, smul_smul]
  module

/-- The round normalization is four times the half-angle spin Casimir. -/
theorem axis_casimir (m : ℕ) :
    (-4 : ℂ) • (axisOne m * axisOne m + axisTwo m * axisTwo m +
      axisThree m * axisThree m) =
      ((m : ℂ) * ((m : ℂ) + 2)) • (1 : Module.End ℂ (Carrier m)) := by
  rw [axis_casimir_polynomial, polynomialCasimir_eq_scalar]

/-- Transport of an actual polynomial operator to its Haar Hilbert carrier. -/
def hilbertOperator (m : ℕ) :
    Module.End ℂ (Carrier m) ≃ₐ[ℂ] Module.End ℂ (HilbertCarrier m) :=
  (carrierEquiv m).conjAlgEquiv ℂ

theorem hilbertOperator_apply (m : ℕ) (T : Module.End ℂ (Carrier m)) (p : Carrier m) :
    hilbertOperator m T (carrierEquiv m p) = carrierEquiv m (T p) := by
  simp [hilbertOperator, LinearEquiv.conjAlgEquiv_apply]

def hilbertAxisOne (m : ℕ) : Module.End ℂ (HilbertCarrier m) :=
  hilbertOperator m (axisOne m)

def hilbertAxisTwo (m : ℕ) : Module.End ℂ (HilbertCarrier m) :=
  hilbertOperator m (axisTwo m)

def hilbertAxisThree (m : ℕ) : Module.End ℂ (HilbertCarrier m) :=
  hilbertOperator m (axisThree m)

def hilbertCasimir (m : ℕ) : Module.End ℂ (HilbertCarrier m) :=
  hilbertOperator m (polynomialCasimir m)

theorem hilbertCasimir_eq_scalar (m : ℕ) :
    hilbertCasimir m =
      ((m : ℂ) * ((m : ℂ) + 2)) • (1 : Module.End ℂ (HilbertCarrier m)) := by
  simp only [hilbertCasimir, polynomialCasimir_eq_scalar, map_smul, map_one]

theorem hilbert_axis_casimir (m : ℕ) :
    (-4 : ℂ) • (hilbertAxisOne m * hilbertAxisOne m +
      hilbertAxisTwo m * hilbertAxisTwo m + hilbertAxisThree m * hilbertAxisThree m) =
      ((m : ℂ) * ((m : ℂ) + 2)) • (1 : Module.End ℂ (HilbertCarrier m)) := by
  have h := congrArg (hilbertOperator m) (axis_casimir m)
  simpa only [map_smul, map_add, map_mul, map_one,
    hilbertAxisOne, hilbertAxisTwo, hilbertAxisThree] using h

theorem round_energy_index (m : ℕ) :
    (m : ℝ) * ((m : ℝ) + 2) = ((m + 1 : ℕ) : ℝ) ^ 2 - 1 := by
  push_cast
  ring

end GeneratedFoundations.Geometry.SourcePolynomialCasimir
