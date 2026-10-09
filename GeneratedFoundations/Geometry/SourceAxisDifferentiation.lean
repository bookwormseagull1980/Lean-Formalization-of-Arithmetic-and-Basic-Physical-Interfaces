module

public import GeneratedFoundations.Geometry.SourcePolynomialCasimir
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivatives of the actual source-axis orbits

The diagonal source curve acts on each actual homogeneous monomial by the
previously proved half-angle weight. Differentiating that scalar exponential
and using the monomial span identifies the derivative on every vector in the
Haar Hilbert realization. In particular, the polynomial weight operator is
identified with an analytic derivative, rather than assumed to be one.

Conjugating this source curve by an actual fixed source operation transports
the derivative by the same unitary action. This statement does not assume an
infinitesimal representation or a spectral formula for a Laplacian.
-/

@[expose] public section

noncomputable section

open Module MvPolynomial
open scoped Topology ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourcePolynomialCasimir

namespace GeneratedFoundations.Geometry.SourceAxisDifferentiation

/-- The frequency includes the half-angle of the original source curve. -/
def frequency (m : ℕ) (k : Fin (m + 1)) : ℂ :=
  (-Complex.I / 2) * ((m : ℂ) - 2 * (k.val : ℂ))

def zPhase (m : ℕ) (k : Fin (m + 1)) (t : ℝ) : ℂ :=
  Complex.exp (frequency m k * (t : ℂ))

theorem zPhase_eq_weight (m : ℕ) (k : Fin (m + 1)) (t : ℝ) :
    zPhase m k t =
      Complex.exp (-Complex.I * (t : ℂ) / 2) ^ (m - k.val) *
        Complex.exp (Complex.I * (t : ℂ) / 2) ^ k.val := by
  have hk : k.val ≤ m := by omega
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  unfold zPhase frequency
  congr 1
  rw [Nat.cast_sub hk]
  ring

@[simp] theorem zPhase_zero (m : ℕ) (k : Fin (m + 1)) : zPhase m k 0 = 1 := by
  simp [zPhase]

theorem zPhase_hasDerivAt (m : ℕ) (k : Fin (m + 1)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => zPhase m k s) (frequency m k * zPhase m k t) t := by
  have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := t))
  simpa only [zPhase, mul_one, one_mul, mul_comm] using
    (hr.const_mul (frequency m k)).cexp

theorem source_z_phase_mode (m : ℕ) (k : Fin (m + 1)) (t : ℝ) :
    sourceRepresentation m (zElement t) (mode m k) = zPhase m k t • mode m k := by
  rw [source_z_axis_weight, zPhase_eq_weight]

theorem axisThree_mode (m : ℕ) (k : Fin (m + 1)) :
    axisThree m (mode m k) = frequency m k • mode m k := by
  simp only [axisThree, LinearMap.smul_apply, weightOperator_mode, smul_smul, frequency]

theorem z_axis_mode_hasDerivAt (m : ℕ) (k : Fin (m + 1)) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => unitaryAction m (zElement s) (carrierEquiv m (mode m k)))
      (unitaryAction m (zElement t) (carrierEquiv m (axisThree m (mode m k)))) t := by
  have hfun : (fun s : ℝ => unitaryAction m (zElement s) (carrierEquiv m (mode m k))) =
      fun s => zPhase m k s • carrierEquiv m (mode m k) := by
    funext s
    rw [unitaryAction_apply_carrier, source_z_phase_mode, map_smul]
  rw [hfun]
  simpa only [unitaryAction_apply_carrier, axisThree_mode, map_smul,
    source_z_phase_mode, smul_smul, mul_comm] using
      (zPhase_hasDerivAt m k t).smul_const (carrierEquiv m (mode m k))

/-- Every polynomial vector has the actual derivative, at every source parameter. -/
theorem z_axis_hasDerivAt (m : ℕ) (p : Carrier m) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => unitaryAction m (zElement s) (carrierEquiv m p))
      (unitaryAction m (zElement t) (carrierEquiv m (axisThree m p))) t := by
  have hp : p ∈ Submodule.span ℂ (Set.range (mode m)) := by
    rw [mode_span]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun q _ => HasDerivAt
    (fun s : ℝ => unitaryAction m (zElement s) (carrierEquiv m q))
    (unitaryAction m (zElement t) (carrierEquiv m (axisThree m q))) t)
    ?_ ?_ ?_ ?_ hp
  · rintro q ⟨k, rfl⟩
    exact z_axis_mode_hasDerivAt m k t
  · simpa only [map_zero] using hasDerivAt_const t (0 : HilbertCarrier m)
  · intro q r _ _ hq hr
    simpa only [map_add, Pi.add_apply] using! hq.add hr
  · intro c q _ hq
    simpa only [map_smul, Pi.smul_apply] using! hq.const_smul c

/-- The derivative on the whole inherited Hilbert space is the transported
polynomial operator. No coordinate-space replacement is used. -/
theorem z_axis_hilbert_hasDerivAt (m : ℕ) (v : HilbertCarrier m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryAction m (zElement s) v)
      (unitaryAction m (zElement t) (hilbertAxisThree m v)) t := by
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
  simpa only [hilbertAxisThree, hilbertOperator_apply] using z_axis_hasDerivAt m p t

@[simp] theorem zElement_zero : zElement 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zElement, zRotation]

theorem unitaryAction_one_apply (m : ℕ) (v : HilbertCarrier m) :
    unitaryAction m 1 v = v := by
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
  simp only [unitaryAction_apply_carrier, map_one, Module.End.one_apply]

theorem unitaryAction_mul_apply (m : ℕ) (U V : SU2) (v : HilbertCarrier m) :
    unitaryAction m (U * V) v = unitaryAction m U (unitaryAction m V v) := by
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
  simp only [unitaryAction_apply_carrier, map_mul, Module.End.mul_apply]

/-- The generator formula has exactly the original minus sign and half-angle. -/
theorem z_axis_hasDerivAt_zero (m : ℕ) (p : Carrier m) :
    HasDerivAt (fun s : ℝ => unitaryAction m (zElement s) (carrierEquiv m p))
      (carrierEquiv m ((-Complex.I / 2) • weightOperator m p)) 0 := by
  simpa only [zElement_zero, unitaryAction_one_apply, axisThree, LinearMap.smul_apply]
    using z_axis_hasDerivAt m p 0

theorem z_axis_hilbert_hasDerivAt_zero (m : ℕ) (v : HilbertCarrier m) :
    HasDerivAt (fun s : ℝ => unitaryAction m (zElement s) v)
      (hilbertAxisThree m v) 0 := by
  simpa only [zElement_zero, unitaryAction_one_apply] using z_axis_hilbert_hasDerivAt m v 0

/-- Any fixed actual source conjugation gives a differentiable source curve.
The derivative is obtained by applying a bounded real-linear map to the
proved orbit derivative; it is not postulated as a Lie-algebra action. -/
theorem conjugate_z_axis_hasDerivAt (m : ℕ) (U : SU2) (v : HilbertCarrier m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryAction m (U * zElement s * U⁻¹) v)
      (unitaryAction m U (unitaryAction m (zElement t)
        (hilbertAxisThree m (unitaryAction m U⁻¹ v)))) t := by
  let F : HilbertCarrier m →L[ℝ] HilbertCarrier m :=
    ((unitaryAction m U).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ
  have h := F.hasFDerivAt.comp_hasDerivAt t
    (z_axis_hilbert_hasDerivAt m (unitaryAction m U⁻¹ v) t)
  change HasDerivAt
    (fun s : ℝ => unitaryAction m U (unitaryAction m (zElement s) (unitaryAction m U⁻¹ v)))
    (unitaryAction m U (unitaryAction m (zElement t)
      (hilbertAxisThree m (unitaryAction m U⁻¹ v)))) t at h
  simpa only [unitaryAction_mul_apply] using h

theorem conjugate_z_axis_hasDerivAt_zero (m : ℕ) (U : SU2) (v : HilbertCarrier m) :
    HasDerivAt (fun s : ℝ => unitaryAction m (U * zElement s * U⁻¹) v)
      (unitaryAction m U (hilbertAxisThree m (unitaryAction m U⁻¹ v))) 0 := by
  simpa only [zElement_zero, unitaryAction_one_apply] using
    conjugate_z_axis_hasDerivAt m U v 0

/-- A fixed source operation with rational real and imaginary parts. -/
def yConjugator : SU2 :=
  ⟨canonical ((1 + Complex.I) / 2) ((1 + Complex.I) / 2),
    canonical_mem_specialUnitary _ _ (by
      simp only [← Complex.normSq_eq_norm_sq]
      norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im])⟩

def xConjugator : SU2 :=
  ⟨canonical ((1 + Complex.I) / 2) ((1 - Complex.I) / 2),
    canonical_mem_specialUnitary _ _ (by
      simp only [← Complex.normSq_eq_norm_sq]
      norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im])⟩

private theorem positive_half_phase (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ) / 2) =
      (Real.cos (t / 2) : ℂ) + (Real.sin (t / 2) : ℂ) * Complex.I := by
  rw [show Complex.I * (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I (t / 2)

private theorem negative_half_phase (t : ℝ) :
    Complex.exp (-Complex.I * (t : ℂ) / 2) =
      (Real.cos (t / 2) : ℂ) - (Real.sin (t / 2) : ℂ) * Complex.I := by
  rw [show -Complex.I * (t : ℂ) / 2 = ((-(t / 2) : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul, sub_eq_add_neg]

/-- The conjugate curve is the original trigonometric source operation. -/
theorem yConjugator_z (t : ℝ) :
    yConjugator * zElement t * yConjugator⁻¹ = yElement t := by
  have h : yConjugator * zElement t = yElement t * yConjugator := by
    apply Subtype.ext
    change canonical ((1 + Complex.I) / 2) ((1 + Complex.I) / 2) * zRotation t =
      yRotation t * canonical ((1 + Complex.I) / 2) ((1 + Complex.I) / 2)
    simp only [zRotation, positive_half_phase, negative_half_phase]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonical, yRotation, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat] <;>
      ring_nf <;> norm_num <;> ring
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

/-- The first-axis curve is constructed by an actual source conjugation. -/
def xElement (t : ℝ) : SU2 := xConjugator * zElement t * xConjugator⁻¹

/-- The constructed curve has the first-axis half-angle matrix. -/
theorem xElement_matrix (t : ℝ) :
    (xElement t : Mat2) =
      !![(Real.cos (t / 2) : ℂ), Complex.I * (Real.sin (t / 2) : ℂ);
        Complex.I * (Real.sin (t / 2) : ℂ), (Real.cos (t / 2) : ℂ)] := by
  change (canonical ((1 + Complex.I) / 2) ((1 - Complex.I) / 2) * zRotation t) *
      star (canonical ((1 + Complex.I) / 2) ((1 - Complex.I) / 2)) = _
  simp only [zRotation, positive_half_phase, negative_half_phase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonical, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, map_ofNat] <;>
    ring_nf <;> norm_num <;> ring

private theorem variableImage_smul (M : Mat2) (i : Fin 2) :
    variableImage M i = M 0 i • X 0 + M 1 i • X 1 := by
  simp only [variableImage, Fin.sum_univ_two, smul_eq_C_mul]

private theorem pderiv_action_smul (M : Mat2) (p : PolynomialSpace) (i : Fin 2) :
    pderiv i (polynomialAction M p) =
      M i 0 • polynomialAction M (pderiv 0 p) +
        M i 1 • polynomialAction M (pderiv 1 p) := by
  simpa only [smul_eq_C_mul] using pderiv_polynomialAction M p i

private theorem sourceRepresentation_coe (m : ℕ) (U : SU2) (p : Carrier m) :
    (sourceRepresentation m U p : PolynomialSpace) = polynomialAction (U : Mat2) p := rfl

/-- The formal second-axis operator is obtained from the actual substitution
chain rule and the fixed source matrix, before any analytic identification. -/
theorem yConjugator_intertwines (m : ℕ) (p : Carrier m) :
    sourceRepresentation m yConjugator (axisThree m p) =
      axisTwo m (sourceRepresentation m yConjugator p) := by
  apply Subtype.ext
  simp only [sourceRepresentation_coe, axisThree, axisTwo, weightOperator,
    raising, lowering, LinearMap.smul_apply, LinearMap.sub_apply,
    Submodule.coe_smul, Submodule.coe_sub, transfer_coe]
  simp only [map_smul, map_sub, map_mul, polynomialAction_X,
    variableImage_smul, pderiv_action_smul]
  dsimp only [yConjugator, canonical]
  simp only [map_div₀, map_add, map_one, map_ofNat, Complex.conj_I,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  match_scalars <;> ring_nf <;> norm_num <;> ring_nf <;> norm_num <;> ring

theorem xConjugator_intertwines (m : ℕ) (p : Carrier m) :
    sourceRepresentation m xConjugator (axisThree m p) =
      axisOne m (sourceRepresentation m xConjugator p) := by
  apply Subtype.ext
  simp only [sourceRepresentation_coe, axisThree, axisOne, weightOperator,
    raising, lowering, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_sub,
    Submodule.coe_add, transfer_coe]
  simp only [map_smul, map_sub, map_mul, polynomialAction_X,
    variableImage_smul, pderiv_action_smul]
  dsimp only [xConjugator, canonical]
  simp only [map_div₀, map_add, map_sub, map_one, map_ofNat, Complex.conj_I,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  match_scalars <;> ring_nf <;> norm_num <;> ring_nf

theorem yConjugator_hilbert_generator (m : ℕ) (v : HilbertCarrier m) :
    unitaryAction m yConjugator (hilbertAxisThree m (unitaryAction m yConjugator⁻¹ v)) =
      hilbertAxisTwo m v := by
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
  simp only [unitaryAction_apply_carrier, hilbertAxisThree, hilbertAxisTwo,
    hilbertOperator_apply]
  rw [yConjugator_intertwines, ← Module.End.mul_apply (sourceRepresentation m yConjugator), ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

theorem xConjugator_hilbert_generator (m : ℕ) (v : HilbertCarrier m) :
    unitaryAction m xConjugator (hilbertAxisThree m (unitaryAction m xConjugator⁻¹ v)) =
      hilbertAxisOne m v := by
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
  simp only [unitaryAction_apply_carrier, hilbertAxisThree, hilbertAxisOne,
    hilbertOperator_apply]
  rw [xConjugator_intertwines, ← Module.End.mul_apply (sourceRepresentation m xConjugator), ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

/-- Analytic differentiation of the original second-axis source curve. -/
theorem y_axis_hilbert_hasDerivAt_zero (m : ℕ) (v : HilbertCarrier m) :
    HasDerivAt (fun s : ℝ => unitaryAction m (yElement s) v)
      (hilbertAxisTwo m v) 0 := by
  simpa only [yConjugator_z, yConjugator_hilbert_generator] using
    conjugate_z_axis_hasDerivAt_zero m yConjugator v

/-- Analytic differentiation of the first-axis source conjugate. -/
theorem x_axis_hilbert_hasDerivAt_zero (m : ℕ) (v : HilbertCarrier m) :
    HasDerivAt (fun s : ℝ => unitaryAction m (xElement s) v)
      (hilbertAxisOne m v) 0 := by
  simpa only [xElement, xConjugator_hilbert_generator] using
    conjugate_z_axis_hasDerivAt_zero m xConjugator v

theorem unitaryAction_inv_apply (m : ℕ) (U : SU2) (v : HilbertCarrier m) :
    unitaryAction m U⁻¹ (unitaryAction m U v) = v := by
  rw [← unitaryAction_mul_apply, inv_mul_cancel, unitaryAction_one_apply]

/-- The derivative at an arbitrary parameter is the action at that parameter
applied to the already identified conjugated generator. -/
theorem conjugate_z_axis_hasDerivAt_action (m : ℕ) (U : SU2)
    (v : HilbertCarrier m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryAction m (U * zElement s * U⁻¹) v)
      (unitaryAction m (U * zElement t * U⁻¹)
        (unitaryAction m U (hilbertAxisThree m (unitaryAction m U⁻¹ v)))) t := by
  apply (conjugate_z_axis_hasDerivAt m U v t).congr_deriv
  simp only [unitaryAction_mul_apply, unitaryAction_inv_apply]

theorem y_axis_hilbert_hasDerivAt (m : ℕ) (v : HilbertCarrier m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryAction m (yElement s) v)
      (unitaryAction m (yElement t) (hilbertAxisTwo m v)) t := by
  simpa only [yConjugator_z, yConjugator_hilbert_generator] using
    conjugate_z_axis_hasDerivAt_action m yConjugator v t

theorem x_axis_hilbert_hasDerivAt (m : ℕ) (v : HilbertCarrier m) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitaryAction m (xElement s) v)
      (unitaryAction m (xElement t) (hilbertAxisOne m v)) t := by
  simpa only [xElement, xConjugator_hilbert_generator] using
    conjugate_z_axis_hasDerivAt_action m xConjugator v t

end GeneratedFoundations.Geometry.SourceAxisDifferentiation
