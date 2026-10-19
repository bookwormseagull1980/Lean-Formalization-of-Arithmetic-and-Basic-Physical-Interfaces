module

public import GeneratedFoundations.Geometry.SourceOneFormContinuousCore
public import GeneratedFoundations.Physical.SourceComplexColourCoordinates
public import GeneratedFoundations.Physical.SourceHaarConnectionHessian

/-!
# Nonlinear source-colour curvature on the original Haar field core

Every colour component is a finite sum of the actual continuous source
fields. The vertex is the commutator of the already generated colour
matrices. Its products therefore exist on the original compact carrier.
The action retains this nonlinear vertex before taking a variation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate BigOperators
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum
open GeneratedFoundations.Geometry.SourceOneFormClosedHodge
open GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
open GeneratedFoundations.Geometry.SourceOneFormContinuousCore
open GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
open GeneratedFoundations.Physical.SourceGeneratedYangMillsResponseHessian
open GeneratedFoundations.Physical.SourceGeneratedRadialVariation

namespace GeneratedFoundations.Physical.SourceHaarYangMillsAction

abbrev ColourCore := Fin 8 → Core
abbrev ColourFields := PiLp 2 (fun _ : Fin 8 => OneFormL2)

instance colourFieldsInner : InnerProductSpace ℂ ColourFields :=
  PiLp.innerProductSpace (fun _ : Fin 8 => OneFormL2)

/-- Inclusion into the original eight-colour Haar field space. -/
def field : ColourCore →ₗ[ℂ] ColourFields where
  toFun A := WithLp.toLp 2 (fun a => includeCore (A a))
  map_add' A B := by
    apply (WithLp.equiv 2 (Fin 8 → OneFormL2)).injective
    funext a
    exact map_add includeCore (A a) (B a)
  map_smul' t A := by
    apply (WithLp.equiv 2 (Fin 8 → OneFormL2)).injective
    funext a
    exact map_smul includeCore t (A a)

def differentiated : ColourCore →ₗ[ℂ] ColourFields where
  toFun A := field (fun a => coreCurl (A a))
  map_add' A B := by
    change field (fun a => coreCurl (A a + B a)) = field _ + field _
    simp only [map_add]
    exact map_add field _ _
  map_smul' t A := by
    change field (fun a => coreCurl (t • A a)) = t • field _
    simp only [map_smul]
    exact map_smul field _ _

theorem differentiated_component (A : ColourCore) (a : Fin 8) :
    differentiated A a = closedCurl (coreToCurlDomain (A a)) := by
  exact (coreCurl_is_differential (A a)).symm

def continuousBracket (f g : Fin 8 → C(CentralQuotient, ℂ)) (a : Fin 8) :
    C(CentralQuotient, ℂ) :=
  ⟨fun x => SourceComplexColourCoordinates.bracket (fun b => f b x) (fun b => g b x) a,
    by
      unfold SourceComplexColourCoordinates.bracket
        SourceComplexColourCoordinates.coordinates SourceColourCasimir.expansionCoefficient
        SourceComplexColourCoordinates.lieMatrix SourceComplexColourCoordinates.hermitianMatrix
      fin_cases a <;> fun_prop⟩

theorem continuousBracket_smul (s t : ℂ)
    (f g : Fin 8 → C(CentralQuotient, ℂ)) (a : Fin 8) :
    continuousBracket (s • f) (t • g) a = (s * t) • continuousBracket f g a := by
  ext x
  exact congrFun (SourceComplexColourCoordinates.bracket_smul s t
    (fun b => f b x) (fun b => g b x)) a

/-- The three independent two-form components in the oriented source frame. -/
def vertexRepresentative (A : ColourCore) (a : Fin 8) : ContinuousField :=
  ![continuousBracket (fun b => representative (A b) 1)
      (fun b => representative (A b) 2) a,
    continuousBracket (fun b => representative (A b) 2)
      (fun b => representative (A b) 0) a,
    continuousBracket (fun b => representative (A b) 0)
      (fun b => representative (A b) 1) a]

/-- The nonlinear term is computed on continuous fields and then mapped to
Haar space, so it need not lie in the coclosed subspace. -/
def vertex (A : ColourCore) : ColourFields :=
  WithLp.toLp 2 (fun a => toHaar (vertexRepresentative A a))

theorem vertex_smul (t : ℂ) (A : ColourCore) :
    vertex (t • A) = (t * t) • vertex A := by
  apply (WithLp.equiv 2 (Fin 8 → OneFormL2)).injective
  funext a
  have h : vertexRepresentative (t • A) a = (t * t) • vertexRepresentative A a := by
    funext j
    fin_cases j <;>
      simp only [vertexRepresentative, Pi.smul_apply, map_smul] <;>
      exact continuousBracket_smul t t _ _ a
  change toHaar (vertexRepresentative (t • A) a) =
    (t * t) • toHaar (vertexRepresentative A a)
  rw [h, map_smul]

def linearCurvature (L : ℝ) : ColourCore →ₗ[ℂ] ColourFields :=
  ((1 / L : ℝ) : ℂ) • differentiated

/-- Hodge dual of the full nonlinear source-frame curvature. -/
def curvature (L : ℝ) (A : ColourCore) : ColourFields :=
  linearCurvature L A + vertex A

theorem curvature_ray (L t : ℝ) (A : ColourCore) :
    curvature L ((t : ℂ) • A) =
      (t : ℂ) • linearCurvature L A + ((t ^ 2 : ℝ) : ℂ) • vertex A := by
  rw [curvature, map_smul, vertex_smul]
  simp only [pow_two, Complex.ofReal_mul]

/-- The invariant coefficient norm is fixed by the source colour trace
metric. Its local real-coordinate normalization is proved in
`matrixConnectionNormSq_coordinates`. -/
def action (L z radial : ℝ) (A : ColourCore) : ℝ :=
  sourceRadialPotential z radial + (1 / 2 : ℝ) * ‖curvature L A‖ ^ 2 +
    (1 / 2 : ℝ) * coclosedResponseShift L (z + sourceRadialIncrement z radial) *
      ‖field A‖ ^ 2

def quadratic (L z radial : ℝ) (A : ColourCore) : ℝ :=
  normalizedRadialMassSq z * radial ^ 2 + ‖linearCurvature L A‖ ^ 2 +
    coclosedResponseShift L z * ‖field A‖ ^ 2

def cubic (L z radial : ℝ) (A : ColourCore) : ℝ :=
  (inner ℂ (linearCurvature L A) (vertex A)).re +
    (1 / 2 : ℝ) * coclosedResponseShift L (sourceRadialIncrement z radial) * ‖field A‖ ^ 2

private theorem normSq_ray {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (X Y : E) (t : ℝ) :
    ‖(t : ℂ) • X + ((t ^ 2 : ℝ) : ℂ) • Y‖ ^ 2 =
      t ^ 2 * ‖X‖ ^ 2 + 2 * t ^ 3 * (inner ℂ X Y).re + t ^ 4 * ‖Y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ)]
  change ‖(t : ℂ) • X‖ ^ 2 +
      2 * (inner ℂ ((t : ℂ) • X) (((t ^ 2 : ℝ) : ℂ) • Y)).re +
      ‖((t ^ 2 : ℝ) : ℂ) • Y‖ ^ 2 = _
  simp only [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- Exact nonlinear expansion; the common response update contributes at
cubic order and the commutator norm at quartic order. -/
theorem action_ray (L z radial t : ℝ) (A : ColourCore) :
    action L z (t * radial) ((t : ℂ) • A) =
      sourceRadialPotential z (t * radial) +
      (1 / 2 : ℝ) * t ^ 2 *
        (‖linearCurvature L A‖ ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2) +
      t ^ 3 * cubic L z radial A + (1 / 2 : ℝ) * t ^ 4 * ‖vertex A‖ ^ 2 := by
  rw [action, curvature_ray, normSq_ray, map_smul, norm_smul]
  simp only [mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [sourceRadialIncrement_scale, coclosedResponseShift_affine]
  unfold cubic
  ring

def rayPolynomial (L z radial : ℝ) (A : ColourCore) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * t ^ 2 *
      (‖linearCurvature L A‖ ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2) +
    t ^ 3 * cubic L z radial A + (1 / 2 : ℝ) * t ^ 4 * ‖vertex A‖ ^ 2

theorem rayPolynomial_hasDerivAt (L z radial t : ℝ) (A : ColourCore) :
    HasDerivAt (rayPolynomial L z radial A)
      (t * (‖linearCurvature L A‖ ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2) +
        3 * t ^ 2 * cubic L z radial A + 2 * t ^ 3 * ‖vertex A‖ ^ 2) t := by
  have h2 := ((hasDerivAt_id t).pow 2).mul_const
    ((1 / 2 : ℝ) *
      (‖linearCurvature L A‖ ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2))
  have h3 := ((hasDerivAt_id t).pow 3).mul_const (cubic L z radial A)
  have h4 := ((hasDerivAt_id t).pow 4).mul_const ((1 / 2 : ℝ) * ‖vertex A‖ ^ 2)
  convert! (h2.add h3).add h4 using 1
  · funext u
    simp only [rayPolynomial, Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

theorem rayPolynomial_secondDeriv (L z radial : ℝ) (A : ColourCore) :
    HasDerivAt (fun t : ℝ => deriv (rayPolynomial L z radial A) t)
      (‖linearCurvature L A‖ ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2) 0 := by
  have h1 := (hasDerivAt_id (0 : ℝ)).mul_const
    (‖linearCurvature L A‖ ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2)
  have h2 := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (3 * cubic L z radial A)
  have h3 := ((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (2 * ‖vertex A‖ ^ 2)
  convert! (h1.add h2).add h3 using 1
  · funext t
    rw [(rayPolynomial_hasDerivAt L z radial t A).deriv]
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · simp

/-- Differentiation of the full nonlinear Haar action gives the actual
curl quadratic form and the same Gaussian response shift. -/
theorem action_secondDeriv {z : ℝ} (hz : 0 < z) (L radial : ℝ) (A : ColourCore) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ =>
      action L z (u * radial) ((u : ℂ) • A)) t) (quadratic L z radial A) 0 := by
  have hs := sourceRadialPotential_ray_secondDeriv_zero hz radial
  have hp := rayPolynomial_secondDeriv L z radial A
  have h := hs.add hp
  have hvalue : normalizedRadialMassSq z * radial ^ 2 +
      (‖linearCurvature L A‖ ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2) =
        quadratic L z radial A := by
    unfold quadratic
    ring
  rw [hvalue] at h
  apply h.congr_of_eventuallyEq
  have hS : IsOpen {t : ℝ |
      0 < z + Real.sqrt (SourceRadialMassIntertwiner.scoreVariance z) * (t * radial)} :=
    isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : ℝ) ∈ {t : ℝ |
      0 < z + Real.sqrt (SourceRadialMassIntertwiner.scoreVariance z) * (t * radial)} :=
    by simpa using hz
  filter_upwards [hS.mem_nhds hzero] with t ht
  have heq : (fun u : ℝ => action L z (u * radial) ((u : ℂ) • A)) =
      fun u => sourceRadialPotential z (u * radial) + rayPolynomial L z radial A u := by
    funext u
    rw [action_ray]
    unfold rayPolynomial
    ring
  have hd : DifferentiableAt ℝ
      (fun u : ℝ => sourceRadialPotential z (u * radial)) t := by
    simpa only [Function.comp_def, id_eq] using
      ((sourceRadialPotential_hasDerivAt (z := z) (radial := t * radial) hz ht).comp t
        ((hasDerivAt_id t).mul_const radial)).differentiableAt
  rw [heq]
  exact deriv_add hd (rayPolynomial_hasDerivAt L z radial t A).differentiableAt

theorem action_connection_ray (L z radial t : ℝ) (A : ColourCore) :
    action L z radial ((t : ℂ) • A) = sourceRadialPotential z radial +
      (1 / 2 : ℝ) * t ^ 2 *
        (‖linearCurvature L A‖ ^ 2 +
          coclosedResponseShift L (z + sourceRadialIncrement z radial) * ‖field A‖ ^ 2) +
      t ^ 3 * (inner ℂ (linearCurvature L A) (vertex A)).re +
      (1 / 2 : ℝ) * t ^ 4 * ‖vertex A‖ ^ 2 := by
  rw [action, curvature_ray, normSq_ray, map_smul, norm_smul]
  simp only [mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem action_connection_firstDeriv_zero (L z radial : ℝ) (A : ColourCore) :
    HasDerivAt (fun t : ℝ => action L z radial ((t : ℂ) • A)) 0 0 := by
  have h2 := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
    ((1 / 2 : ℝ) * (‖linearCurvature L A‖ ^ 2 +
      coclosedResponseShift L (z + sourceRadialIncrement z radial) * ‖field A‖ ^ 2))
  have h3 := ((hasDerivAt_id (0 : ℝ)).pow 3).mul_const
    ((inner ℂ (linearCurvature L A) (vertex A)).re)
  have h4 := ((hasDerivAt_id (0 : ℝ)).pow 4).mul_const ((1 / 2 : ℝ) * ‖vertex A‖ ^ 2)
  convert! (((hasDerivAt_const (0 : ℝ) (sourceRadialPotential z radial)).add h2).add h3).add h4
      using 1
  · funext t
    rw [action_connection_ray]
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · simp

/-- The zero mixed block follows from the full nonlinear action, with the
radial dependence of the Gaussian shift still present. -/
theorem action_mixed_secondDeriv_zero (L z radial : ℝ) (A : ColourCore) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      action L z (s * radial) ((t : ℂ) • A)) 0) 0 0 := by
  have heq : (fun s : ℝ => deriv (fun t : ℝ =>
      action L z (s * radial) ((t : ℂ) • A)) 0) = fun _ => 0 := by
    funext s
    exact (action_connection_firstDeriv_zero L z (s * radial) A).deriv
  rw [heq]
  exact hasDerivAt_const 0 0

theorem field_normSq (A : ColourCore) :
    ‖field A‖ ^ 2 = ∑ a, ‖(A a : coclosedField)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem differentiated_normSq (A : ColourCore) :
    ‖differentiated A‖ ^ 2 = ∑ a, ‖(coreCurl (A a) : coclosedField)‖ ^ 2 :=
  field_normSq (fun a => coreCurl (A a))

theorem linearCurvature_normSq (L : ℝ) (A : ColourCore) :
    ‖linearCurvature L A‖ ^ 2 = ‖differentiated A‖ ^ 2 / L ^ 2 := by
  change ‖((1 / L : ℝ) : ℂ) • differentiated A‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
  ring

def responseField (L z : ℝ) (A : ColourCore) : ColourFields :=
  WithLp.toLp 2 (fun a => (SourceHaarConnectionHessian.finiteOperator L z (A a) : OneFormL2))

theorem field_inner_response (L z : ℝ) (A : ColourCore) :
    (inner ℂ (field A) (responseField L z A)).re =
      ∑ a, (inner ℂ (A a : coclosedField)
        (SourceHaarConnectionHessian.finiteOperator L z (A a))).re := by
  rw [PiLp.inner_apply]
  change (∑ a, inner ℂ (A a : coclosedField)
    (SourceHaarConnectionHessian.finiteOperator L z (A a))).re = _
  exact map_sum Complex.reAddGroupHom
    (fun a : Fin 8 => inner ℂ (A a : coclosedField)
      (SourceHaarConnectionHessian.finiteOperator L z (A a))) Finset.univ

/-- The Hessian derived from the nonlinear action is the quadratic form of
the original differential Haar-field operator in all eight colour channels. -/
theorem quadratic_eq_operator (L z radial : ℝ) (A : ColourCore) :
    quadratic L z radial A = normalizedRadialMassSq z * radial ^ 2 +
      (inner ℂ (field A) (responseField L z A)).re := by
  rw [quadratic, linearCurvature_normSq, differentiated_normSq, field_normSq,
    field_inner_response]
  simp_rw [SourceHaarConnectionHessian.finiteOperator_energy]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  ring

theorem differentiated_coercivity (A : ColourCore) :
    4 * ‖field A‖ ^ 2 ≤ ‖differentiated A‖ ^ 2 := by
  rw [field_normSq, differentiated_normSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hm : (coreToCurlDomain (A a) : OneFormL2) ∈ coclosedField := by
    rw [coreToCurlDomain_val]
    exact (A a).val.property
  have h := closedCurl_coclosed_coercivity (coreToCurlDomain (A a)) hm
  rw [coreToCurlDomain_val, coreCurl_is_differential] at h
  exact h

/-- The complete finite-core lower bound has no shell cutoff or omitted
colour multiplicity. Its first term is the actual generated radial response. -/
theorem quadratic_coercivity (L z radial : ℝ) (A : ColourCore) :
    generatedYangMillsGapSq L z * (radial ^ 2 + ‖field A‖ ^ 2) ≤
      quadratic L z radial A := by
  have hr := mul_le_mul_of_nonneg_right (generatedYangMillsGapSq_le_radial L z)
    (sq_nonneg radial)
  have hg : generatedYangMillsGapSq L z ≤ 4 / L ^ 2 + coclosedResponseShift L z := by
    have h := generatedYangMillsGapSq_le_coclosed (L := L) (z := z) (l := 1) (by norm_num)
    norm_num [coclosedMassIndex, SourceRP3FieldSpectrum.vectorEigenvalue,
      SourceRP3FieldSpectrum.vectorCasimir] at h
    exact h
  have hc := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖field A‖)
  have hd := div_le_div_of_nonneg_right (differentiated_coercivity A) (sq_nonneg L)
  rw [quadratic, linearCurvature_normSq]
  calc
    generatedYangMillsGapSq L z * (radial ^ 2 + ‖field A‖ ^ 2) =
        generatedYangMillsGapSq L z * radial ^ 2 +
          generatedYangMillsGapSq L z * ‖field A‖ ^ 2 := by ring
    _ ≤ normalizedRadialMassSq z * radial ^ 2 +
        (4 / L ^ 2 + coclosedResponseShift L z) * ‖field A‖ ^ 2 := add_le_add hr hc
    _ = normalizedRadialMassSq z * radial ^ 2 +
        (4 * ‖field A‖ ^ 2) / L ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2 := by ring
    _ ≤ normalizedRadialMassSq z * radial ^ 2 +
        ‖differentiated A‖ ^ 2 / L ^ 2 + coclosedResponseShift L z * ‖field A‖ ^ 2 :=
      add_le_add (add_le_add le_rfl hd) le_rfl

end GeneratedFoundations.Physical.SourceHaarYangMillsAction
