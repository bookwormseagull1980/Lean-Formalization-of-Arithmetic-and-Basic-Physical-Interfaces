module

public import GeneratedFoundations.Geometry.SourceAxisMetric
public import Mathlib.Tactic.NoncommRing

/-!
# Exterior differentiation in the generated source frame

The frame is the trace-orthonormal frame obtained by differentiating the
original source curves. Its commutators are computed on the homogeneous
polynomials and transported to their existing Haar realizations. In the
column convention used by those curves the cyclic commutator is `-2 E_k`.
Consequently the cyclic components of the exterior derivative contain
`+2 A_k`. This term is derived from the frame, not inserted to fit a spectrum.

The differential operators below act on functions on the original source
group. Matrix-coefficient synthesis intertwines them with explicitly computed
finite operators. No one-form eigenvalue, coclosed decomposition, or spectral
exhaustion is assumed here.
-/

@[expose] public section

noncomputable section

open Module MvPolynomial
open scoped BigOperators
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourcePolynomialCasimir
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceAxisMetric

namespace GeneratedFoundations.Geometry.SourceOneFormDifferential

/-- The polynomial operators of the actual unit source velocities. -/
def polynomialAxis (m : ℕ) (i : Fin 3) : Module.End ℂ (Carrier m) :=
  ![Complex.I • (raising m + lowering m),
    lowering m - raising m, -Complex.I • weightOperator m] i

theorem polynomialAxis_commutator_01 (m : ℕ) :
    polynomialAxis m 0 * polynomialAxis m 1 -
      polynomialAxis m 1 * polynomialAxis m 0 =
        (-2 : ℂ) • polynomialAxis m 2 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [polynomialAxis, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    raising, lowering, weightOperator, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_smul, Submodule.coe_sub, Submodule.coe_add,
    Submodule.coe_smul, transfer_coe]
  simp only [map_add, map_sub, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
    one_mul, zero_mul, zero_add, smul_eq_C_mul, mixed_partials_commute]
  simp only [map_neg]
  norm_num
  simp only [smul_eq_C_mul, map_ofNat]
  ring

theorem polynomialAxis_commutator_12 (m : ℕ) :
    polynomialAxis m 1 * polynomialAxis m 2 -
      polynomialAxis m 2 * polynomialAxis m 1 =
        (-2 : ℂ) • polynomialAxis m 0 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [polynomialAxis, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    raising, lowering, weightOperator, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_add,
    Submodule.coe_smul, transfer_coe]
  simp only [map_sub, smul_eq_C_mul]
  simp only [map_neg]
  norm_num
  simp only [smul_eq_C_mul, map_ofNat, mixed_partials_commute]
  ring

theorem polynomialAxis_commutator_20 (m : ℕ) :
    polynomialAxis m 2 * polynomialAxis m 0 -
      polynomialAxis m 0 * polynomialAxis m 2 =
        (-2 : ℂ) • polynomialAxis m 1 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [polynomialAxis, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    raising, lowering, weightOperator, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, map_smul, Submodule.coe_sub, Submodule.coe_add,
    Submodule.coe_smul, transfer_coe]
  simp only [map_add, smul_eq_C_mul]
  simp only [map_neg]
  norm_num
  simp only [smul_eq_C_mul, map_ofNat, mixed_partials_commute]
  ring_nf
  norm_num [← map_pow]
  abel

/-- Transport uses the same Haar carrier as the source matrix coefficients. -/
theorem polynomialAxis_transport (m : ℕ) (i : Fin 3) :
    hilbertOperator m (polynomialAxis m i) = unitHilbertAxis m i := by
  fin_cases i <;>
    simp [polynomialAxis, unitHilbertAxis, halfHilbertAxis,
      SourceCoefficientDifferentiation.hilbertAxis, hilbertAxisOne, hilbertAxisTwo,
      hilbertAxisThree, axisOne, axisTwo, axisThree, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, _root_.map_smul, _root_.map_add]
  all_goals module

private theorem transport_sub (m : ℕ) (X Y : Module.End ℂ (Carrier m)) :
    hilbertOperator m (X - Y) = hilbertOperator m X - hilbertOperator m Y :=
  map_sub (hilbertOperator m) X Y

private theorem transport_mul (m : ℕ) (X Y : Module.End ℂ (Carrier m)) :
    hilbertOperator m (X * Y) = hilbertOperator m X * hilbertOperator m Y :=
  map_mul (hilbertOperator m) X Y

theorem unitAxis_commutator_01 (m : ℕ) :
    unitHilbertAxis m 0 * unitHilbertAxis m 1 -
      unitHilbertAxis m 1 * unitHilbertAxis m 0 =
        (-2 : ℂ) • unitHilbertAxis m 2 := by
  calc
    _ = hilbertOperator m
        (polynomialAxis m 0 * polynomialAxis m 1 -
          polynomialAxis m 1 * polynomialAxis m 0) := by
      rw [transport_sub, transport_mul, transport_mul,
        polynomialAxis_transport, polynomialAxis_transport]
    _ = _ := by rw [polynomialAxis_commutator_01, map_smul, polynomialAxis_transport]

theorem unitAxis_commutator_12 (m : ℕ) :
    unitHilbertAxis m 1 * unitHilbertAxis m 2 -
      unitHilbertAxis m 2 * unitHilbertAxis m 1 =
        (-2 : ℂ) • unitHilbertAxis m 0 := by
  calc
    _ = hilbertOperator m
        (polynomialAxis m 1 * polynomialAxis m 2 -
          polynomialAxis m 2 * polynomialAxis m 1) := by
      rw [transport_sub, transport_mul, transport_mul,
        polynomialAxis_transport, polynomialAxis_transport]
    _ = _ := by rw [polynomialAxis_commutator_12, map_smul, polynomialAxis_transport]

theorem unitAxis_commutator_20 (m : ℕ) :
    unitHilbertAxis m 2 * unitHilbertAxis m 0 -
      unitHilbertAxis m 0 * unitHilbertAxis m 2 =
        (-2 : ℂ) • unitHilbertAxis m 1 := by
  calc
    _ = hilbertOperator m
        (polynomialAxis m 2 * polynomialAxis m 0 -
          polynomialAxis m 0 * polynomialAxis m 2) := by
      rw [transport_sub, transport_mul, transport_mul,
        polynomialAxis_transport, polynomialAxis_transport]
    _ = _ := by rw [polynomialAxis_commutator_20, map_smul, polynomialAxis_transport]

/-- A one-form is recorded by its three coefficients in the generated frame. -/
abbrev SourceOneForm := Fin 3 → SU2 → ℂ

def gradient (f : SU2 → ℂ) : SourceOneForm := fun i => unitAxisDerivative i f

/-- Cyclic components of `dA`, including the noncoordinate-frame term. -/
def curl (A : SourceOneForm) : SourceOneForm := fun i g =>
  (![unitAxisDerivative 1 (A 2) g - unitAxisDerivative 2 (A 1) g,
     unitAxisDerivative 2 (A 0) g - unitAxisDerivative 0 (A 2) g,
     unitAxisDerivative 0 (A 1) g - unitAxisDerivative 1 (A 0) g] i) +
       2 * A i g

/-- Synthesis retains the actual group function in every frame direction. -/
def coefficientForm (m : ℕ) (v : HilbertCarrier m)
    (A : Fin 3 → HilbertCarrier m) : SourceOneForm :=
  fun i => matrixCoefficient m v (A i)

def coefficientGradient (m : ℕ) (a : HilbertCarrier m) :
    Fin 3 → HilbertCarrier m := fun i => unitHilbertAxis m i a

def coefficientCurl (m : ℕ) (A : Fin 3 → HilbertCarrier m) :
    Fin 3 → HilbertCarrier m := fun i =>
  (![unitHilbertAxis m 1 (A 2) - unitHilbertAxis m 2 (A 1),
     unitHilbertAxis m 2 (A 0) - unitHilbertAxis m 0 (A 2),
     unitHilbertAxis m 0 (A 1) - unitHilbertAxis m 1 (A 0)] i) +
       (2 : ℂ) • A i

theorem unitAxisDerivative_matrixCoefficient (m : ℕ) (i : Fin 3)
    (v a : HilbertCarrier m) :
    unitAxisDerivative i (matrixCoefficient m v a) =
      matrixCoefficient m v (unitHilbertAxis m i a) := by
  rw [unitAxisDerivative_eq,
    SourceCoefficientDifferentiation.axisDerivative_matrixCoefficient]
  funext g
  simp [unitHilbertAxis, matrixCoefficient_apply, inner_smul_right]

theorem gradient_matrixCoefficient (m : ℕ) (v a : HilbertCarrier m) :
    gradient (matrixCoefficient m v a) =
      coefficientForm m v (coefficientGradient m a) := by
  funext i
  exact unitAxisDerivative_matrixCoefficient m i v a

theorem curl_coefficientForm (m : ℕ) (v : HilbertCarrier m)
    (A : Fin 3 → HilbertCarrier m) :
    curl (coefficientForm m v A) =
      coefficientForm m v (coefficientCurl m A) := by
  funext i g
  fin_cases i <;>
    simp [curl, coefficientForm, coefficientCurl, unitAxisDerivative_matrixCoefficient,
      matrixCoefficient_apply, inner_sub_right, inner_add_right, inner_smul_right]

/-- The cancellation `d(df)=0` follows from the actual source commutators. -/
theorem coefficientCurl_gradient_zero (m : ℕ) (a : HilbertCarrier m) :
    coefficientCurl m (coefficientGradient m a) = 0 := by
  have h01 := congrArg (fun T : Module.End ℂ (HilbertCarrier m) => T a)
    (unitAxis_commutator_01 m)
  have h12 := congrArg (fun T : Module.End ℂ (HilbertCarrier m) => T a)
    (unitAxis_commutator_12 m)
  have h20 := congrArg (fun T : Module.End ℂ (HilbertCarrier m) => T a)
    (unitAxis_commutator_20 m)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h01 h12 h20
  funext i
  fin_cases i <;> simp [coefficientCurl, coefficientGradient, h01, h12, h20]

theorem curl_gradient_matrixCoefficient (m : ℕ) (v a : HilbertCarrier m) :
    curl (gradient (matrixCoefficient m v a)) = 0 := by
  rw [gradient_matrixCoefficient, curl_coefficientForm,
    coefficientCurl_gradient_zero]
  funext i g
  simp [coefficientForm, matrixCoefficient_apply]

private theorem skew_of_preserved_pairing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (f g : ℝ → E) (a b da db : E)
    (hf : HasDerivAt f da 0) (hg : HasDerivAt g db 0)
    (hf0 : f 0 = a) (hg0 : g 0 = b)
    (hp : ∀ t, inner ℂ (f t) (g t) = inner ℂ a b) :
    inner ℂ da b + inner ℂ a db = 0 := by
  have h := hf.inner ℂ hg
  rw [hf0, hg0] at h
  have hfun : (fun t => inner ℂ (f t) (g t)) = fun _ : ℝ => inner ℂ a b := funext hp
  rw [hfun] at h
  have hc : HasDerivAt (fun _ : ℝ => inner ℂ a b) (0 : ℂ) (0 : ℝ) :=
    hasDerivAt_const (0 : ℝ) (inner ℂ a b)
  exact (add_comm _ _).trans (h.unique hc)

/-- Skew symmetry follows by differentiating the original unitary action,
not by installing a matrix adjoint convention. -/
theorem unitAxis_skew_pairing (m : ℕ) (i : Fin 3)
    (a b : HilbertCarrier m) :
    inner ℂ (unitHilbertAxis m i a) b +
      inner ℂ a (unitHilbertAxis m i b) = 0 := by
  have hone (v : HilbertCarrier m) : unitaryAction m 1 v = v := by
    obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
    simp only [unitaryAction_apply_carrier, map_one, Module.End.one_apply]
  have hz : axisCurve i (2 * (0 : ℝ)) = (1 : SU2) := by
    simpa only [axisCurve, mul_zero] using SourceCoefficientDifferentiation.sourceAxis_zero i
  have hzero (v : HilbertCarrier m) :
      unitaryAction m (axisCurve i (2 * (0 : ℝ))) v = v :=
    (congrArg (fun U : SU2 => unitaryAction m U v) hz).trans (hone v)
  exact skew_of_preserved_pairing
    (fun t => unitaryAction m (axisCurve i (2 * t)) a)
    (fun t => unitaryAction m (axisCurve i (2 * t)) b)
    a b (unitHilbertAxis m i a) (unitHilbertAxis m i b)
    (unit_axis_hilbert_hasDerivAt_zero m i a)
    (unit_axis_hilbert_hasDerivAt_zero m i b)
    (hzero a) (hzero b)
    (fun t => (unitaryAction m (axisCurve i (2 * t))).inner_map_map a b)

def coefficientDivergence (m : ℕ) (A : Fin 3 → HilbertCarrier m) :
    HilbertCarrier m := ∑ i : Fin 3, unitHilbertAxis m i (A i)

theorem coefficientDivergence_gradient (m : ℕ) (a : HilbertCarrier m) :
    coefficientDivergence m (coefficientGradient m a) =
      -(((m : ℂ) * ((m : ℂ) + 2)) • a) := by
  have h := congrArg (fun T : Module.End ℂ (HilbertCarrier m) => T a)
    (unit_axis_negative_square_sum_eq_scalar m)
  simp only [LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h
  simpa only [coefficientDivergence, coefficientGradient, neg_eq_iff_eq_neg] using h

/-- The divergence of the actual exterior derivative vanishes on the
matrix-coefficient core, with the noncoordinate-frame terms retained. -/
theorem coefficientDivergence_curl_zero (m : ℕ)
    (A : Fin 3 → HilbertCarrier m) :
    coefficientDivergence m (coefficientCurl m A) = 0 := by
  have h01 := congrArg (fun T : Module.End ℂ (HilbertCarrier m) => T (A 2))
    (unitAxis_commutator_01 m)
  have h12 := congrArg (fun T : Module.End ℂ (HilbertCarrier m) => T (A 0))
    (unitAxis_commutator_12 m)
  have h20 := congrArg (fun T : Module.End ℂ (HilbertCarrier m) => T (A 1))
    (unitAxis_commutator_20 m)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h01 h12 h20
  calc
    _ = (unitHilbertAxis m 0 (unitHilbertAxis m 1 (A 2)) -
          unitHilbertAxis m 1 (unitHilbertAxis m 0 (A 2))) +
        (unitHilbertAxis m 1 (unitHilbertAxis m 2 (A 0)) -
          unitHilbertAxis m 2 (unitHilbertAxis m 1 (A 0))) +
        (unitHilbertAxis m 2 (unitHilbertAxis m 0 (A 1)) -
          unitHilbertAxis m 0 (unitHilbertAxis m 2 (A 1))) +
        (2 : ℂ) • coefficientDivergence m A := by
      simp [coefficientDivergence, coefficientCurl, Fin.sum_univ_three, map_add, map_sub,
        map_smul]
      module
    _ = 0 := by
      rw [h01, h12, h20]
      simp only [coefficientDivergence, Fin.sum_univ_three]
      module

/-- The one-form second-order identity is computed from source derivatives.
Its lower-order term is fixed by the source frame commutator. -/
theorem coefficientCurl_square (m : ℕ) (A : Fin 3 → HilbertCarrier m) :
    coefficientCurl m (coefficientCurl m A) =
      coefficientGradient m (coefficientDivergence m A) +
      ((m : ℂ) * ((m : ℂ) + 2)) • A + (2 : ℂ) • coefficientCurl m A := by
  have h01 (a : HilbertCarrier m) := congrArg
    (fun T : Module.End ℂ (HilbertCarrier m) => T a) (unitAxis_commutator_01 m)
  have h12 (a : HilbertCarrier m) := congrArg
    (fun T : Module.End ℂ (HilbertCarrier m) => T a) (unitAxis_commutator_12 m)
  have h20 (a : HilbertCarrier m) := congrArg
    (fun T : Module.End ℂ (HilbertCarrier m) => T a) (unitAxis_commutator_20 m)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, sub_eq_iff_eq_add] at h01 h12 h20
  have hc (a : HilbertCarrier m) :
      ((m : ℂ) * ((m : ℂ) + 2)) • a =
        -(unitHilbertAxis m 0 (unitHilbertAxis m 0 a) +
          unitHilbertAxis m 1 (unitHilbertAxis m 1 a) +
          unitHilbertAxis m 2 (unitHilbertAxis m 2 a)) := by
    have h := coefficientDivergence_gradient m a
    simpa only [coefficientDivergence, coefficientGradient, Fin.sum_univ_three,
      neg_neg] using (congrArg Neg.neg h).symm
  funext i
  fin_cases i <;>
    simp [coefficientCurl, coefficientGradient, coefficientDivergence, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.add_apply,
      Pi.smul_apply, hc, map_add, map_sub, map_smul, h01, h12, h20] <;> module

theorem coefficientCurl_add (m : ℕ) (A B : Fin 3 → HilbertCarrier m) :
    coefficientCurl m (A + B) = coefficientCurl m A + coefficientCurl m B := by
  funext i
  fin_cases i <;> simp [coefficientCurl, map_add] <;> module

theorem coefficientCurl_smul (m : ℕ) (c : ℂ) (A : Fin 3 → HilbertCarrier m) :
    coefficientCurl m (c • A) = c • coefficientCurl m A := by
  funext i
  fin_cases i <;> simp [coefficientCurl, map_smul] <;> module

/-- The constant homogeneous carrier has zero actual directional derivative. -/
theorem polynomialAxis_degree_zero (i : Fin 3) :
    polynomialAxis 0 i = 0 := by
  apply linearMap_ext_modes
  intro k
  have hk : k.val = 0 := by omega
  have hp : (mode 0 k : PolynomialSpace) = 1 := by
    rw [mode_coe]
    simp
  apply Subtype.ext
  fin_cases i <;>
    simp [polynomialAxis, raising, lowering, weightOperator, transfer_coe, hp]

theorem unitAxis_degree_zero (i : Fin 3) : unitHilbertAxis 0 i = 0 := by
  rw [← polynomialAxis_transport, polynomialAxis_degree_zero, map_zero]

theorem coefficientCurl_degree_zero (A : Fin 3 → HilbertCarrier 0) :
    coefficientCurl 0 A = (2 : ℂ) • A := by
  funext i
  fin_cases i <;> simp [coefficientCurl, unitAxis_degree_zero]

/-- The two possible non-gauge curl eigenvalues follow from the computed
second-order differential identity, rather than a prescribed branch table. -/
theorem coclosed_curl_eigenvalue (m : ℕ) (c : ℂ)
    (A : Fin 3 → HilbertCarrier m) (hA : A ≠ 0)
    (hdiv : coefficientDivergence m A = 0)
    (hcurl : coefficientCurl m A = c • A) :
    c = (m : ℂ) + 2 ∨ c = -(m : ℂ) := by
  have h := coefficientCurl_square m A
  rw [hcurl, coefficientCurl_smul, hcurl, hdiv] at h
  have hg : coefficientGradient m 0 = 0 := by
    funext i
    simp [coefficientGradient]
  rw [hg, zero_add, smul_smul, smul_smul] at h
  have hfactor : ((c - ((m : ℂ) + 2)) * (c + (m : ℂ))) • A = 0 := by
    calc
      _ = (c * c) • A - ((m : ℂ) * ((m : ℂ) + 2)) • A -
          (2 * c) • A := by module
      _ = 0 := by rw [h]; module
  have hscalar := (smul_eq_zero.mp hfactor).resolve_right hA
  rcases mul_eq_zero.mp hscalar with hplus | hminus
  · exact Or.inl (sub_eq_zero.mp hplus)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hminus)

/-- Projective parity and the actual degree-zero block give the round
one-form lower bound on every coclosed source-degree eigenvector. -/
theorem coclosed_curl_eigenvalue_sq_ge_four {m : ℕ} (hm : Even m) (c : ℝ)
    (A : Fin 3 → HilbertCarrier m) (hA : A ≠ 0)
    (hdiv : coefficientDivergence m A = 0)
    (hcurl : coefficientCurl m A = (c : ℂ) • A) : 4 ≤ c ^ 2 := by
  by_cases hm0 : m = 0
  · subst m
    have htwo : ((2 : ℂ) - (c : ℂ)) • A = 0 := by
      calc
        _ = (2 : ℂ) • A - (c : ℂ) • A := sub_smul (2 : ℂ) (c : ℂ) A
        _ = 0 := by rw [← coefficientCurl_degree_zero, hcurl, sub_self]
    have hc : c = 2 := by
      have h := sub_eq_zero.mp ((smul_eq_zero.mp htwo).resolve_right hA)
      exact_mod_cast h.symm
    norm_num [hc]
  · have hm2 : 2 ≤ m := by
      obtain ⟨k, hk⟩ := hm
      omega
    have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    rcases coclosed_curl_eigenvalue m (c : ℂ) A hA hdiv hcurl with hp | hn
    · have hc : c = (m : ℝ) + 2 := by exact_mod_cast hp
      rw [hc]
      nlinarith
    · have hc : c = -(m : ℝ) := by exact_mod_cast hn
      rw [hc]
      nlinarith

end GeneratedFoundations.Geometry.SourceOneFormDifferential
