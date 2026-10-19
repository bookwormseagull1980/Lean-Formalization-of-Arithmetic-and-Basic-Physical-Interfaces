module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsAction
public import GeneratedFoundations.Physical.SourceGeneratedRadialVariation
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

/-!
# The generated connection response and its exact second variation

This file derives the radial/connection Hessian from one common response.
The nonlinear curvature is retained before any quadratic approximation.  A
connection jet is scaled by one real parameter and the full response is
expanded exactly.  The quadratic coefficient is therefore the Hessian; the
radial--connection coupling first occurs in degree three, so the mixed
Hessian vanishes as a theorem rather than as an assigned matrix entry.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsResponseHessian

open SourceFourDimensionalGaugeKinematics
open SourceFourDimensionalYangMills
open SourceGeneratedYangMillsGap

/-- The derivative part of the generated colour curvature. -/
def matrixLinearCurvature (A : MatrixConnectionJet)
    (mu nu : CoordinateIndex) : Mat3 :=
  A.derivative mu nu - A.derivative nu mu

/-- The commutator part of the generated colour curvature. -/
def matrixBracketCurvature (A : MatrixConnectionJet)
    (mu nu : CoordinateIndex) : Mat3 :=
  A.value mu * A.value nu - A.value nu * A.value mu

theorem matrixCurvature_eq_linear_add_bracket (A : MatrixConnectionJet)
    (mu nu : CoordinateIndex) :
    matrixCurvature A mu nu =
      matrixLinearCurvature A mu nu + matrixBracketCurvature A mu nu := rfl

/-- Real scaling of a connection jet, represented on its complex matrices. -/
def scaleMatrixConnectionJet (t : ℝ) (A : MatrixConnectionJet) :
    MatrixConnectionJet where
  value := fun mu => (t : ℂ) • A.value mu
  derivative := fun mu nu => (t : ℂ) • A.derivative mu nu

/-- Zero matrix connection jet. -/
def zeroMatrixConnectionJet : MatrixConnectionJet where
  value := fun _ => 0
  derivative := fun _ _ => 0

@[simp] theorem matrixLinearCurvature_scale (t : ℝ) (A : MatrixConnectionJet)
    (mu nu : CoordinateIndex) :
    matrixLinearCurvature (scaleMatrixConnectionJet t A) mu nu =
      (t : ℂ) • matrixLinearCurvature A mu nu := by
  simp [matrixLinearCurvature, scaleMatrixConnectionJet, smul_sub]

@[simp] theorem matrixBracketCurvature_scale (t : ℝ) (A : MatrixConnectionJet)
    (mu nu : CoordinateIndex) :
    matrixBracketCurvature (scaleMatrixConnectionJet t A) mu nu =
      ((t ^ 2 : ℝ) : ℂ) • matrixBracketCurvature A mu nu := by
  simp only [matrixBracketCurvature, scaleMatrixConnectionJet]
  ext i j
  simp [Matrix.mul_apply]
  ring

/-- The symmetric trace pairing polarizing `colourQuadratic`. -/
def colourPairing (X Y : Mat3) : ℝ :=
  -(Matrix.trace (X * Y)).re

theorem colourPairing_symmetric (X Y : Mat3) :
    colourPairing X Y = colourPairing Y X := by
  simp [colourPairing, Matrix.trace_mul_comm X Y]

theorem colourQuadratic_add (X Y : Mat3) :
    colourQuadratic (X + Y) =
      colourQuadratic X + 2 * colourPairing X Y + colourQuadratic Y := by
  simp only [colourQuadratic, colourPairing, add_mul, mul_add,
    Matrix.trace_add]
  rw [Matrix.trace_mul_comm Y X]
  simp only [Complex.add_re]
  ring

theorem colourQuadratic_real_smul (t : ℝ) (X : Mat3) :
    colourQuadratic ((t : ℂ) • X) = t ^ 2 * colourQuadratic X := by
  simp only [colourQuadratic, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_smul, smul_eq_mul]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem colourPairing_real_smul (s t : ℝ) (X Y : Mat3) :
    colourPairing ((s : ℂ) • X) ((t : ℂ) • Y) =
      s * t * colourPairing X Y := by
  simp only [colourPairing, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem colourQuadratic_complex_ofReal_smul (t : ℝ) (X : Mat3) :
    colourQuadratic (t • X) = t ^ 2 * colourQuadratic X :=
  colourQuadratic_real_smul t X

theorem colourPairing_complex_ofReal_smul (s t : ℝ) (X Y : Mat3) :
    colourPairing (s • X) (t • Y) = s * t * colourPairing X Y :=
  colourPairing_real_smul s t X Y

/-- Quadratic density of the connection values. -/
def matrixConnectionDensity (A : MatrixConnectionJet) : ℝ :=
  ∑ μ, colourQuadratic (A.value μ)

/-- The coefficient metric fixed by the generated colour basis. Its factor
of two is forced by `trace (T_a T_b) = delta_ab / 2`. -/
def matrixConnectionNormSq (A : MatrixConnectionJet) : ℝ :=
  2 * matrixConnectionDensity A

/-- In the generated colour coordinates this is exactly the Euclidean
coefficient norm, with no remaining normalization constant. -/
theorem matrixConnectionNormSq_coordinates (A : ColourConnectionJet) :
    matrixConnectionNormSq (colourMatrixConnectionJet A) =
      ∑ μ, ∑ a, (A.value μ a) ^ 2 := by
  unfold matrixConnectionNormSq matrixConnectionDensity
  change 2 * (∑ μ, colourQuadratic (colourLieMatrix (A.value μ))) = _
  simp_rw [colourQuadratic_coordinates]
  rw [← Finset.mul_sum]
  ring

/-- Quadratic density of the derivative curvature. -/
def matrixLinearCurvatureDensity (A : MatrixConnectionJet) : ℝ :=
  ∑ μ, ∑ ν, colourQuadratic (matrixLinearCurvature A μ ν)

/-- Quartic density of the commutator curvature. -/
def matrixBracketCurvatureDensity (A : MatrixConnectionJet) : ℝ :=
  ∑ μ, ∑ ν, colourQuadratic (matrixBracketCurvature A μ ν)

/-- Cubic derivative--commutator interference retained by the common action. -/
def matrixCurvatureInterference (A : MatrixConnectionJet) : ℝ :=
  ∑ μ, ∑ ν,
    colourPairing (matrixLinearCurvature A μ ν)
      (matrixBracketCurvature A μ ν)

theorem matrixCurvatureDensity_decomposition (A : MatrixConnectionJet) :
    SourceGeneratedYangMillsAction.matrixCurvatureDensity A =
      matrixLinearCurvatureDensity A +
        2 * matrixCurvatureInterference A +
          matrixBracketCurvatureDensity A := by
  simp only [SourceGeneratedYangMillsAction.matrixCurvatureDensity,
    matrixCurvature_eq_linear_add_bracket, colourQuadratic_add,
    matrixLinearCurvatureDensity, matrixCurvatureInterference,
    matrixBracketCurvatureDensity, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]

@[simp] theorem matrixConnectionDensity_scale (t : ℝ) (A : MatrixConnectionJet) :
    matrixConnectionDensity (scaleMatrixConnectionJet t A) =
      t ^ 2 * matrixConnectionDensity A := by
  unfold matrixConnectionDensity
  change (∑ μ, colourQuadratic ((t : ℂ) • A.value μ)) =
    t ^ 2 * ∑ μ, colourQuadratic (A.value μ)
  simp_rw [colourQuadratic_real_smul]
  rw [← Finset.mul_sum]

@[simp] theorem matrixLinearCurvatureDensity_scale
    (t : ℝ) (A : MatrixConnectionJet) :
    matrixLinearCurvatureDensity (scaleMatrixConnectionJet t A) =
      t ^ 2 * matrixLinearCurvatureDensity A := by
  unfold matrixLinearCurvatureDensity
  simp only [matrixLinearCurvature_scale]
  change (∑ μ, ∑ ν,
      colourQuadratic ((t : ℂ) • matrixLinearCurvature A μ ν)) =
    t ^ 2 * ∑ μ, ∑ ν, colourQuadratic (matrixLinearCurvature A μ ν)
  simp_rw [colourQuadratic_real_smul]
  simp_rw [← Finset.mul_sum]

@[simp] theorem matrixBracketCurvatureDensity_scale
    (t : ℝ) (A : MatrixConnectionJet) :
    matrixBracketCurvatureDensity (scaleMatrixConnectionJet t A) =
      t ^ 4 * matrixBracketCurvatureDensity A := by
  unfold matrixBracketCurvatureDensity
  simp only [matrixBracketCurvature_scale]
  change (∑ μ, ∑ ν,
      colourQuadratic (((t ^ 2 : ℝ) : ℂ) • matrixBracketCurvature A μ ν)) =
    t ^ 4 * ∑ μ, ∑ ν, colourQuadratic (matrixBracketCurvature A μ ν)
  simp_rw [colourQuadratic_real_smul]
  simp_rw [← Finset.mul_sum]
  ring

@[simp] theorem matrixCurvatureInterference_scale
    (t : ℝ) (A : MatrixConnectionJet) :
    matrixCurvatureInterference (scaleMatrixConnectionJet t A) =
      t ^ 3 * matrixCurvatureInterference A := by
  unfold matrixCurvatureInterference
  simp only [matrixLinearCurvature_scale, matrixBracketCurvature_scale]
  change (∑ μ, ∑ ν,
      colourPairing ((t : ℂ) • matrixLinearCurvature A μ ν)
        (((t ^ 2 : ℝ) : ℂ) • matrixBracketCurvature A μ ν)) =
    t ^ 3 * ∑ μ, ∑ ν,
      colourPairing (matrixLinearCurvature A μ ν)
        (matrixBracketCurvature A μ ν)
  simp_rw [colourPairing_real_smul]
  simp_rw [← Finset.mul_sum]
  ring

/-- The exact generated Gaussian connection response.  It retains the full
nonlinear curvature and adds the source-generated common response shift. -/
def connectionResponse (L q : ℝ) (A : MatrixConnectionJet) : ℝ :=
  (1 / 2 : ℝ) *
      SourceGeneratedYangMillsAction.matrixCurvatureDensity A +
    (1 / 2 : ℝ) * coclosedResponseShift L q * matrixConnectionNormSq A

/-- The trace-coordinate expression includes the metric conversion already
proved above. Curvature is summed over ordered antisymmetric index pairs;
connection values have no such duplicate index. -/
theorem connectionResponse_trace (L q : ℝ) (A : MatrixConnectionJet) :
    connectionResponse L q A =
      (1 / 2 : ℝ) * SourceGeneratedYangMillsAction.matrixCurvatureDensity A +
        coclosedResponseShift L q * matrixConnectionDensity A := by
  unfold connectionResponse matrixConnectionNormSq
  ring

theorem connectionResponse_zero (L q : ℝ) :
    connectionResponse L q zeroMatrixConnectionJet = 0 := by
  simp [connectionResponse, SourceGeneratedYangMillsAction.matrixCurvatureDensity,
    matrixCurvature, zeroMatrixConnectionJet, matrixConnectionNormSq, matrixConnectionDensity,
    colourQuadratic]

/-- Exact expansion of the full nonlinear response along a connection ray.
The coefficient of `t^2` is the connection Hessian; the cubic and quartic
terms are retained explicitly. -/
theorem connectionResponse_scale (L q t : ℝ) (A : MatrixConnectionJet) :
    connectionResponse L q (scaleMatrixConnectionJet t A) =
      (1 / 2 : ℝ) * t ^ 2 *
        (matrixLinearCurvatureDensity A +
          2 * coclosedResponseShift L q * matrixConnectionDensity A) +
      t ^ 3 * matrixCurvatureInterference A +
      (1 / 2 : ℝ) * t ^ 4 * matrixBracketCurvatureDensity A := by
  rw [connectionResponse_trace, matrixCurvatureDensity_decomposition]
  simp only [matrixLinearCurvatureDensity_scale,
    matrixCurvatureInterference_scale, matrixBracketCurvatureDensity_scale,
    matrixConnectionDensity_scale]
  ring

/-- Local radial potential at a generated condensed amplitude. -/
def radialHessianPotential (z radial : ℝ) : ℝ :=
  (1 / 2 : ℝ) * normalizedRadialMassSq z * radial ^ 2

theorem radialHessianPotential_scale (z radial t : ℝ) :
    radialHessianPotential z (t * radial) =
      (1 / 2 : ℝ) * t ^ 2 * normalizedRadialMassSq z * radial ^ 2 := by
  simp [radialHessianPotential]
  ring

/-- The actual intensity increment of a unit-score radial coordinate.  This
is the same normalization used by the integrated complete restoring force. -/
def sourceRadialIncrement (z radial : ℝ) : ℝ :=
  Real.sqrt (SourceRadialMassIntertwiner.scoreVariance z) * radial

theorem sourceRadialIncrement_scale (z radial t : ℝ) :
    sourceRadialIncrement z (t * radial) = t * sourceRadialIncrement z radial := by
  unfold sourceRadialIncrement
  ring

/-- Quadratic radial germ of one common local response. The connection sees
the same normalized intensity increment as the complete radial potential. -/
def commonResponseAction (L z radial : ℝ) (A : MatrixConnectionJet) : ℝ :=
  radialHessianPotential z radial +
    connectionResponse L (z + sourceRadialIncrement z radial) A

theorem coclosedResponseShift_affine (L z radial t : ℝ) :
    coclosedResponseShift L (z + t * radial) =
      coclosedResponseShift L z + t * coclosedResponseShift L radial := by
  unfold coclosedResponseShift
  ring

/-- The quadratic coefficient of the common radial/connection response. -/
def commonQuadraticSecondVariation (L z radial : ℝ)
    (A : MatrixConnectionJet) : ℝ :=
  normalizedRadialMassSq z * radial ^ 2 +
    matrixLinearCurvatureDensity A +
    2 * coclosedResponseShift L z * matrixConnectionDensity A

/-- Exact common-ray expansion.  The radial--connection term is cubic, hence
it does not enter the Hessian. -/
theorem commonResponseAction_scale (L z radial t : ℝ)
    (A : MatrixConnectionJet) :
    commonResponseAction L z (t * radial) (scaleMatrixConnectionJet t A) =
      (1 / 2 : ℝ) * t ^ 2 *
        commonQuadraticSecondVariation L z radial A +
      t ^ 3 *
        (matrixCurvatureInterference A +
          coclosedResponseShift L (sourceRadialIncrement z radial) *
            matrixConnectionDensity A) +
      (1 / 2 : ℝ) * t ^ 4 * matrixBracketCurvatureDensity A := by
  rw [commonResponseAction, radialHessianPotential_scale,
    connectionResponse_scale, sourceRadialIncrement_scale, coclosedResponseShift_affine]
  unfold commonQuadraticSecondVariation
  ring

/-- The actual first derivative along a joint radial/connection ray.  This
connects the exact polynomial expansion to differentiation, rather than
merely naming its quadratic coefficient a Hessian. -/
theorem commonResponseAction_ray_hasDerivAt (L z radial t : ℝ)
    (A : MatrixConnectionJet) :
    HasDerivAt
      (fun u : ℝ => commonResponseAction L z (u * radial)
        (scaleMatrixConnectionJet u A))
      (t * commonQuadraticSecondVariation L z radial A +
        3 * t ^ 2 * (matrixCurvatureInterference A +
          coclosedResponseShift L (sourceRadialIncrement z radial) *
            matrixConnectionDensity A) +
        2 * t ^ 3 * matrixBracketCurvatureDensity A) t := by
  have h2 := ((hasDerivAt_id t).pow 2).mul_const
    ((1 / 2 : ℝ) * commonQuadraticSecondVariation L z radial A)
  have h3 := ((hasDerivAt_id t).pow 3).mul_const
    (matrixCurvatureInterference A +
      coclosedResponseShift L (sourceRadialIncrement z radial) *
        matrixConnectionDensity A)
  have h4 := ((hasDerivAt_id t).pow 4).mul_const
    ((1 / 2 : ℝ) * matrixBracketCurvatureDensity A)
  convert! (h2.add h3).add h4 using 1
  · funext u
    rw [commonResponseAction_scale]
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

/-- The joint-ray second derivative at the source is precisely the common
quadratic second variation. -/
theorem commonResponseAction_secondDeriv (L z radial : ℝ)
    (A : MatrixConnectionJet) :
    HasDerivAt
      (fun t : ℝ => deriv (fun u : ℝ =>
        commonResponseAction L z (u * radial) (scaleMatrixConnectionJet u A)) t)
      (commonQuadraticSecondVariation L z radial A) 0 := by
  have h1 := (hasDerivAt_id (0 : ℝ)).mul_const
    (commonQuadraticSecondVariation L z radial A)
  have h2 := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
    (3 * (matrixCurvatureInterference A +
      coclosedResponseShift L (sourceRadialIncrement z radial) *
        matrixConnectionDensity A))
  have h3 := ((hasDerivAt_id (0 : ℝ)).pow 3).mul_const
    (2 * matrixBracketCurvatureDensity A)
  convert! (h1.add h2).add h3 using 1
  · funext t
    rw [(commonResponseAction_ray_hasDerivAt L z radial t A).deriv]
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · simp

/-- At zero connection the actual connection derivative vanishes for every
radial displacement.  The source-dependent shift is retained throughout. -/
theorem commonResponseAction_connection_hasDerivAt_zero
    (L z radial : ℝ) (A : MatrixConnectionJet) :
    HasDerivAt
      (fun t : ℝ => commonResponseAction L z radial (scaleMatrixConnectionJet t A))
      0 0 := by
  have h2 := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
    ((1 / 2 : ℝ) * (matrixLinearCurvatureDensity A +
      2 * coclosedResponseShift L (z + sourceRadialIncrement z radial) *
        matrixConnectionDensity A))
  have h3 := ((hasDerivAt_id (0 : ℝ)).pow 3).mul_const
    (matrixCurvatureInterference A)
  have h4 := ((hasDerivAt_id (0 : ℝ)).pow 4).mul_const
    ((1 / 2 : ℝ) * matrixBracketCurvatureDensity A)
  convert! (((hasDerivAt_const (0 : ℝ) (radialHessianPotential z radial)).add
    (h2.add h3)).add h4) using 1
  · funext t
    rw [commonResponseAction, connectionResponse_scale]
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · simp

/-- The mixed derivative of the common action is zero by differentiation.
It is not assigned to zero in a block matrix. -/
theorem commonResponseAction_mixed_secondDeriv_zero (L z radial : ℝ)
    (A : MatrixConnectionJet) :
    HasDerivAt
      (fun s : ℝ => deriv (fun t : ℝ =>
        commonResponseAction L z (s * radial) (scaleMatrixConnectionJet t A)) 0)
      0 0 := by
  have hfun : (fun s : ℝ => deriv (fun t : ℝ =>
      commonResponseAction L z (s * radial) (scaleMatrixConnectionJet t A)) 0) =
      fun _ => 0 := by
    funext s
    exact (commonResponseAction_connection_hasDerivAt_zero L z (s * radial) A).deriv
  rw [hfun]
  exact hasDerivAt_const 0 0

/-- The nonlinear radial restoring potential and the connection response
come from the same complete source.  `commonResponseAction` is its radial
quadratic germ, not its definition. -/
def sourceCommonResponseAction (L z radial : ℝ) (A : MatrixConnectionJet) : ℝ :=
  SourceGeneratedRadialVariation.sourceRadialPotential z radial +
    connectionResponse L (z + sourceRadialIncrement z radial) A

theorem sourceCommonResponseAction_eq_germ_add_remainder
    (L z radial : ℝ) (A : MatrixConnectionJet) :
    sourceCommonResponseAction L z radial A =
      commonResponseAction L z radial A +
        SourceGeneratedRadialVariation.sourceRadialPotential z radial -
          radialHessianPotential z radial := by
  unfold sourceCommonResponseAction commonResponseAction
  ring

theorem radialHessianPotential_ray_hasDerivAt (z radial t : ℝ) :
    HasDerivAt (fun u : ℝ => radialHessianPotential z (u * radial))
      (t * normalizedRadialMassSq z * radial ^ 2) t := by
  have h := ((hasDerivAt_id t).pow 2).mul_const
    ((1 / 2 : ℝ) * normalizedRadialMassSq z * radial ^ 2)
  convert! h using 1
  · funext u
    simp only [radialHessianPotential, Pi.pow_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

/-- The true nonlinear common source and its quadratic germ have the same
second derivative, including the complete restoring tower. -/
theorem sourceCommonResponseAction_secondDeriv {z : ℝ} (hz : 0 < z)
    (L radial : ℝ) (A : MatrixConnectionJet) :
    HasDerivAt
      (fun t : ℝ => deriv (fun u : ℝ =>
        sourceCommonResponseAction L z (u * radial) (scaleMatrixConnectionJet u A)) t)
      (commonQuadraticSecondVariation L z radial A) 0 := by
  have hpot := SourceGeneratedRadialVariation.sourceRadialPotential_ray_secondDeriv_zero
    hz radial
  have hgerm := commonResponseAction_secondDeriv L z radial A
  have hquad : HasDerivAt (fun t : ℝ => deriv
      (fun u : ℝ => radialHessianPotential z (u * radial)) t)
      (normalizedRadialMassSq z * radial ^ 2) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).mul_const
      (normalizedRadialMassSq z * radial ^ 2)
    convert! h using 1
    · funext t
      rw [(radialHessianPotential_ray_hasDerivAt z radial t).deriv]
      simp only [id_eq]
      ring
    · simp
  have hsum := (hgerm.add hpot).sub hquad
  have hsum' : HasDerivAt
      (fun t : ℝ => deriv (fun u : ℝ =>
          commonResponseAction L z (u * radial) (scaleMatrixConnectionJet u A)) t +
        deriv (fun u : ℝ => SourceGeneratedRadialVariation.sourceRadialPotential z
          (u * radial)) t -
        deriv (fun u : ℝ => radialHessianPotential z (u * radial)) t)
      (commonQuadraticSecondVariation L z radial A) 0 := by
    convert! hsum using 1
    ring
  apply hsum'.congr_of_eventuallyEq
  have hS : IsOpen {t : ℝ | 0 < z +
      Real.sqrt (SourceRadialMassIntertwiner.scoreVariance z) * (t * radial)} :=
    isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : ℝ) ∈ {t : ℝ | 0 < z +
      Real.sqrt (SourceRadialMassIntertwiner.scoreVariance z) * (t * radial)} := by
    simpa using hz
  filter_upwards [hS.mem_nhds hzero] with t ht
  have hp := (SourceGeneratedRadialVariation.sourceRadialPotential_hasDerivAt hz ht).comp t
    ((hasDerivAt_id t).mul_const radial)
  simp only [Function.comp_def, id_eq] at hp
  have hq := radialHessianPotential_ray_hasDerivAt z radial t
  have hg := commonResponseAction_ray_hasDerivAt L z radial t A
  have heq : (fun u : ℝ => sourceCommonResponseAction L z (u * radial)
      (scaleMatrixConnectionJet u A)) =
      fun u => commonResponseAction L z (u * radial) (scaleMatrixConnectionJet u A) +
        SourceGeneratedRadialVariation.sourceRadialPotential z (u * radial) -
        radialHessianPotential z (u * radial) := by
    funext u
    exact sourceCommonResponseAction_eq_germ_add_remainder L z (u * radial) _
  have hpointwise : (fun u : ℝ =>
      commonResponseAction L z (u * radial) (scaleMatrixConnectionJet u A) +
        SourceGeneratedRadialVariation.sourceRadialPotential z (u * radial) -
        radialHessianPotential z (u * radial)) =
      ((fun u : ℝ => commonResponseAction L z (u * radial)
          (scaleMatrixConnectionJet u A)) +
        (fun u : ℝ => SourceGeneratedRadialVariation.sourceRadialPotential z
          (u * radial)) -
        (fun u : ℝ => radialHessianPotential z (u * radial))) := by
    funext u
    simp only [Pi.add_apply, Pi.sub_apply]
  rw [heq, hpointwise,
    deriv_sub (hg.differentiableAt.add hp.differentiableAt) hq.differentiableAt,
    deriv_add hg.differentiableAt hp.differentiableAt]

/-- The actual nonlinear potential also has zero radial/connection mixed
derivative; replacing it by its quadratic germ is unnecessary for this fact. -/
theorem sourceCommonResponseAction_mixed_secondDeriv_zero (L z radial : ℝ)
    (A : MatrixConnectionJet) :
    HasDerivAt
      (fun s : ℝ => deriv (fun t : ℝ =>
        sourceCommonResponseAction L z (s * radial) (scaleMatrixConnectionJet t A)) 0)
      0 0 := by
  have hfun : (fun s : ℝ => deriv (fun t : ℝ =>
      sourceCommonResponseAction L z (s * radial) (scaleMatrixConnectionJet t A)) 0) =
      fun _ => 0 := by
    funext s
    have h := ((commonResponseAction_connection_hasDerivAt_zero L z (s * radial) A).add_const
      (SourceGeneratedRadialVariation.sourceRadialPotential z (s * radial))).sub_const
        (radialHessianPotential z (s * radial))
    have heq : (fun t : ℝ => sourceCommonResponseAction L z (s * radial)
        (scaleMatrixConnectionJet t A)) =
        fun t => commonResponseAction L z (s * radial) (scaleMatrixConnectionJet t A) +
          SourceGeneratedRadialVariation.sourceRadialPotential z (s * radial) -
          radialHessianPotential z (s * radial) := by
      funext t
      exact sourceCommonResponseAction_eq_germ_add_remainder L z (s * radial) _
    rw [heq]
    exact h.deriv
  rw [hfun]
  exact hasDerivAt_const 0 0

/-- Polarization of the common quadratic second variation. -/
def commonHessianPairing (L z : ℝ)
    (radial1 radial2 : ℝ) (A1 A2 : MatrixConnectionJet) : ℝ :=
  normalizedRadialMassSq z * radial1 * radial2 +
    (∑ μ, ∑ ν,
      colourPairing (matrixLinearCurvature A1 μ ν)
        (matrixLinearCurvature A2 μ ν)) +
    2 * coclosedResponseShift L z *
      (∑ μ, colourPairing (A1.value μ) (A2.value μ))

/-- The radial and connection directions are orthogonal in the Hessian.  This
is derived from the common action expansion above: their first coupling is
cubic, not quadratic. -/
theorem commonHessianPairing_radial_connection_zero
    (L z radial : ℝ) (A : MatrixConnectionJet) :
    commonHessianPairing L z radial 0 zeroMatrixConnectionJet A = 0 := by
  simp [commonHessianPairing, zeroMatrixConnectionJet,
    matrixLinearCurvature, colourPairing]

/-- The radial Hessian is exactly the existing source-normalized radial mass. -/
theorem commonHessianPairing_radial (L z r1 r2 : ℝ) :
    commonHessianPairing L z r1 r2
      zeroMatrixConnectionJet zeroMatrixConnectionJet =
      normalizedRadialMassSq z * r1 * r2 := by
  simp [commonHessianPairing, zeroMatrixConnectionJet,
    matrixLinearCurvature, colourPairing]

/-- The connection Hessian is the derivative curvature plus the generated
Gaussian response shift. -/
theorem commonHessianPairing_connection (L z : ℝ)
    (A1 A2 : MatrixConnectionJet) :
    commonHessianPairing L z 0 0 A1 A2 =
      (∑ μ, ∑ ν,
        colourPairing (matrixLinearCurvature A1 μ ν)
          (matrixLinearCurvature A2 μ ν)) +
      2 * coclosedResponseShift L z *
        (∑ μ, colourPairing (A1.value μ) (A2.value μ)) := by
  simp [commonHessianPairing]

end GeneratedFoundations.Physical.SourceGeneratedYangMillsResponseHessian
