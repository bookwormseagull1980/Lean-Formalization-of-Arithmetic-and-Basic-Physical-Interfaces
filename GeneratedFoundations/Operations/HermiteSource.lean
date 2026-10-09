module

public import GeneratedFoundations.Correlation.ComplexGaussianStates
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# The first two modes of the Gaussian differential source

The source modes are actual functions in complex Lebesgue `L²`. Their
normalization is inherited from the generated Gaussian state after the explicit
width change `b ↦ √2 b`. Orthogonality follows from Gaussian moments, and the
ladder coefficients follow from differentiation of these functions.

Only the finite source space is treated here. No assertion about completeness
of the full Hermite family or the domain of the unbounded Hilbert adjoint is
made by the finite-dimensional constructions.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open GeneratedFoundations.Correlation.GaussianCorrelation
open GeneratedFoundations.Correlation.ComplexGaussianStates

namespace GeneratedFoundations.Operations.HermiteSource

def sourceWidth (b : ℝ) : ℝ := Real.sqrt 2 * b

theorem sourceWidth_pos {b : ℝ} (hb : 0 < b) : 0 < sourceWidth b := by
  unfold sourceWidth
  positivity

theorem sourceWidth_sq (b : ℝ) : sourceWidth b ^ 2 = 2 * b ^ 2 := by
  rw [sourceWidth, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def groundProfile (b y : ℝ) : ℝ := state (sourceWidth b) 0 y

def firstProfile (b y : ℝ) : ℝ := (Real.sqrt 2 / b) * y * groundProfile b y

def sourceVariance (b : ℝ) : ℝ≥0 := ⟨b ^ 2 / 2, by positivity⟩

@[simp] theorem sourceVariance_coe (b : ℝ) : (sourceVariance b : ℝ) = b ^ 2 / 2 := rfl

theorem sourceVariance_ne_zero {b : ℝ} (hb : 0 < b) : sourceVariance b ≠ 0 := by
  intro h
  have hz := congrArg (fun v : ℝ≥0 => (v : ℝ)) h
  change b ^ 2 / 2 = 0 at hz
  nlinarith

theorem source_normalizationMass {b : ℝ} (hb : 0 < b) :
    normalizationMass (sourceWidth b) = Real.sqrt (Real.pi * b ^ 2) := by
  rw [normalizationMass_eq, sourceWidth_sq]
  congr 1
  field_simp [hb.ne']

theorem groundProfile_eq (b y : ℝ) :
    groundProfile b y = Real.exp (-(y ^ 2 / (2 * b ^ 2))) /
      Real.sqrt (normalizationMass (sourceWidth b)) := by
  simp only [groundProfile, state, rawState, sub_zero, sourceWidth_sq]

theorem groundProfile_sq {b : ℝ} (hb : 0 < b) (y : ℝ) :
    groundProfile b y ^ 2 = gaussianPDFReal 0 (sourceVariance b) y := by
  have hm := normalizationMass_pos (sourceWidth_pos hb)
  have he : Real.exp (-(y ^ 2 / (2 * b ^ 2))) ^ 2 = Real.exp (-y ^ 2 / b ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [groundProfile_eq, div_pow, Real.sq_sqrt hm.le, he, source_normalizationMass hb]
  simp only [gaussianPDFReal, sourceVariance_coe, sub_zero]
  have hc : 2 * Real.pi * (b ^ 2 / 2) = Real.pi * b ^ 2 := by ring
  have hd : 2 * (b ^ 2 / 2) = b ^ 2 := by ring
  rw [hc, hd]
  ring

/-- The square of the source amplitude is a member of the same generated law. -/
theorem groundProfile_squared_measure {μ : ℝ → Measure ℝ}
    (hμ : GeneratedFoundations.Probability.CompositionalGaussianAxioms μ)
    {b : ℝ} (hb : 0 < b) :
    volume.withDensity (fun y => ENNReal.ofReal (groundProfile b y ^ 2)) = μ (b ^ 2 / 2) := by
  rw [hμ.law_eq_withDensity (t := b ^ 2 / 2) (by positivity)]
  congr 1
  funext y
  rw [groundProfile_sq hb]
  rfl

theorem groundProfile_continuous (b : ℝ) : Continuous (groundProfile b) :=
  state_continuous (sourceWidth b) 0

theorem firstProfile_continuous (b : ℝ) : Continuous (firstProfile b) :=
  (continuous_const.mul continuous_id).mul (groundProfile_continuous b)

theorem groundProfile_memLp {b : ℝ} (hb : 0 < b) : MemLp (groundProfile b) 2 volume :=
  state_memLp (sourceWidth_pos hb) 0

theorem integral_ground_sq {b : ℝ} (hb : 0 < b) :
    (∫ y : ℝ, groundProfile b y ^ 2) = 1 :=
  state_sq_integral (sourceWidth_pos hb) 0

theorem integral_mul_ground_sq {b : ℝ} (hb : 0 < b) :
    (∫ y : ℝ, y * groundProfile b y ^ 2) = 0 := by
  have h := integral_id_gaussianReal (μ := 0) (v := sourceVariance b)
  rw [integral_gaussianReal_eq_integral_smul (sourceVariance_ne_zero hb)] at h
  simpa only [groundProfile_sq hb, smul_eq_mul, mul_comm] using h

theorem integral_sq_mul_ground_sq {b : ℝ} (hb : 0 < b) :
    (∫ y : ℝ, y ^ 2 * groundProfile b y ^ 2) = b ^ 2 / 2 := by
  have hm := variance_eq_sub
    (memLp_id_gaussianReal' (μ := 0) (v := sourceVariance b) 2 (by norm_num))
  have h : (∫ y : ℝ, y ^ 2 ∂gaussianReal 0 (sourceVariance b)) = sourceVariance b := by
    simpa using hm.symm
  rw [integral_gaussianReal_eq_integral_smul (sourceVariance_ne_zero hb)] at h
  simpa only [groundProfile_sq hb, smul_eq_mul, mul_comm, sourceVariance_coe] using h

theorem integral_ground_mul_first {b : ℝ} (hb : 0 < b) :
    (∫ y : ℝ, groundProfile b y * firstProfile b y) = 0 := by
  have he (y : ℝ) : groundProfile b y * firstProfile b y =
      (Real.sqrt 2 / b) * (y * groundProfile b y ^ 2) := by
    unfold firstProfile
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_mul_ground_sq hb, mul_zero]

theorem integral_first_sq {b : ℝ} (hb : 0 < b) :
    (∫ y : ℝ, firstProfile b y ^ 2) = 1 := by
  have he (y : ℝ) : firstProfile b y ^ 2 =
      ((Real.sqrt 2 / b) ^ 2) * (y ^ 2 * groundProfile b y ^ 2) := by
    unfold firstProfile
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sq_mul_ground_sq hb, div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [hb.ne']

theorem firstProfile_memLp {b : ℝ} (hb : 0 < b) : MemLp (firstProfile b) 2 volume := by
  apply (memLp_two_iff_integrable_sq (firstProfile_continuous b).aestronglyMeasurable).mpr
  apply Integrable.of_integral_ne_zero
  rw [integral_first_sq hb]
  norm_num

def groundState {b : ℝ} (hb : 0 < b) : ComplexL2 :=
  complexState (sourceWidth_pos hb) 0

def firstState {b : ℝ} (hb : 0 < b) : ComplexL2 :=
  realEmbedding ((firstProfile_memLp hb).toLp (firstProfile b))

theorem groundState_coe {b : ℝ} (hb : 0 < b) :
    groundState hb =ᵐ[volume] fun y => (groundProfile b y : ℂ) :=
  complexState_coe (sourceWidth_pos hb) 0

theorem firstState_coe {b : ℝ} (hb : 0 < b) :
    firstState hb =ᵐ[volume] fun y => (firstProfile b y : ℂ) := by
  filter_upwards [realEmbedding_coe ((firstProfile_memLp hb).toLp (firstProfile b)),
    (firstProfile_memLp hb).coeFn_toLp] with y he hf
  change realEmbedding ((firstProfile_memLp hb).toLp (firstProfile b)) y = _
  rw [he, hf]

theorem groundState_norm {b : ℝ} (hb : 0 < b) : ‖groundState hb‖ = 1 :=
  complexState_norm (sourceWidth_pos hb) 0

theorem inner_ground_first {b : ℝ} (hb : 0 < b) :
    inner ℂ (groundState hb) (firstState hb) = 0 := by
  rw [L2.inner_def]
  calc
    (∫ y : ℝ, inner ℂ (groundState hb y) (firstState hb y)) =
        ∫ y : ℝ, ((groundProfile b y * firstProfile b y : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [groundState_coe hb, firstState_coe hb] with y hg hf
      rw [hg, hf]
      simp [RCLike.inner_apply, mul_comm]
    _ = 0 := by
      rw [integral_complex_ofReal]
      simp [integral_ground_mul_first hb]

theorem inner_first_self {b : ℝ} (hb : 0 < b) :
    inner ℂ (firstState hb) (firstState hb) = 1 := by
  rw [L2.inner_def]
  calc
    (∫ y : ℝ, inner ℂ (firstState hb y) (firstState hb y)) =
        ∫ y : ℝ, ((firstProfile b y ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [firstState_coe hb] with y hf
      rw [hf]
      rw [RCLike.inner_apply]
      simp [pow_two]
    _ = 1 := by
      rw [integral_complex_ofReal]
      simp [integral_first_sq hb]

theorem firstState_norm {b : ℝ} (hb : 0 < b) : ‖firstState hb‖ = 1 := by
  have h := congrArg Complex.re (inner_first_self hb)
  change RCLike.re (inner ℂ (firstState hb) (firstState hb)) = (1 : ℝ) at h
  rw [inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (firstState hb)]

def sourceModes {b : ℝ} (hb : 0 < b) : Fin 2 → ComplexL2 :=
  ![groundState hb, firstState hb]

theorem sourceModes_orthonormal {b : ℝ} (hb : 0 < b) :
    Orthonormal ℂ (sourceModes hb) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · simp [sourceModes, inner_self_eq_norm_sq_to_K, groundState_norm hb]
  · simpa [sourceModes] using inner_ground_first hb
  · simpa [sourceModes, inner_ground_first hb] using
      (inner_conj_symm (𝕜 := ℂ) (firstState hb) (groundState hb)).symm
  · simpa [sourceModes] using inner_first_self hb

theorem groundProfile_hasDerivAt {b : ℝ} (hb : 0 < b) (y : ℝ) :
    HasDerivAt (groundProfile b) (-y / b ^ 2 * groundProfile b y) y := by
  have h := ((((hasDerivAt_id y).pow 2).div_const (2 * b ^ 2)).neg.exp).div_const
    (Real.sqrt (normalizationMass (sourceWidth b)))
  simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one] at h
  convert h using 1
  · funext x
    exact groundProfile_eq b x
  · rw [groundProfile_eq]
    field_simp [hb.ne']

theorem firstProfile_hasDerivAt {b : ℝ} (hb : 0 < b) (y : ℝ) :
    HasDerivAt (firstProfile b)
      ((Real.sqrt 2 / b) * (1 - y ^ 2 / b ^ 2) * groundProfile b y) y := by
  have h := ((hasDerivAt_id y).const_mul (Real.sqrt 2 / b)).mul
    (groundProfile_hasDerivAt hb y)
  convert h using 1
  · funext x
    rfl
  · dsimp only [id_eq]
    ring

def lowering (b : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  ((b : ℂ) * deriv f y + (y / b : ℝ) * f y) / (Real.sqrt 2 : ℝ)

def raising (b : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (-(b : ℂ) * deriv f y + (y / b : ℝ) * f y) / (Real.sqrt 2 : ℝ)

theorem lowering_ground {b : ℝ} (hb : 0 < b) :
    lowering b (fun y => (groundProfile b y : ℂ)) = 0 := by
  funext y
  change lowering b (fun x => (groundProfile b x : ℂ)) y = (0 : ℂ)
  rw [lowering, (groundProfile_hasDerivAt hb y).ofReal_comp.deriv]
  push_cast
  field_simp [hb.ne']
  ring

theorem lowering_first {b : ℝ} (hb : 0 < b) :
    lowering b (fun y => (firstProfile b y : ℂ)) = fun y => (groundProfile b y : ℂ) := by
  funext y
  rw [lowering, (firstProfile_hasDerivAt hb y).ofReal_comp.deriv]
  dsimp [firstProfile]
  push_cast
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hb.ne', hs]
  ring

theorem raising_ground {b : ℝ} (hb : 0 < b) :
    raising b (fun y => (groundProfile b y : ℂ)) = fun y => (firstProfile b y : ℂ) := by
  funext y
  rw [raising, (groundProfile_hasDerivAt hb y).ofReal_comp.deriv]
  dsimp [firstProfile]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  push_cast
  field_simp [hb.ne', hsn]
  linear_combination - y * (groundProfile b y : ℂ) * hs

theorem inner_first_ground {b : ℝ} (hb : 0 < b) :
    inner ℂ (firstState hb) (groundState hb) = 0 := by
  simpa [inner_ground_first hb] using
    (inner_conj_symm (𝕜 := ℂ) (firstState hb) (groundState hb)).symm

abbrev Coordinates := EuclideanSpace ℂ (Fin 2)

def synthesis {b : ℝ} (hb : 0 < b) : Coordinates →ₗ[ℂ] ComplexL2 where
  toFun c := c 0 • groundState hb + c 1 • firstState hb
  map_add' c d := by
    simp only [PiLp.add_apply, add_smul]
    abel
  map_smul' z c := by
    simp [smul_add, smul_smul]

theorem synthesis_inner {b : ℝ} (hb : 0 < b) (c d : Coordinates) :
    inner ℂ (synthesis hb c) (synthesis hb d) = inner ℂ c d := by
  simp [synthesis, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_ground_first hb, inner_first_ground hb,
    inner_self_eq_norm_sq_to_K, groundState_norm hb, firstState_norm hb,
    PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

def synthesisIsometry {b : ℝ} (hb : 0 < b) : Coordinates →ₗᵢ[ℂ] ComplexL2 :=
  (synthesis hb).isometryOfInner (synthesis_inner hb)

/-- The source space is the range of the actual two Gaussian modes in `L²`. -/
def sourceSpace {b : ℝ} (hb : 0 < b) : Submodule ℂ ComplexL2 :=
  LinearMap.range (synthesis hb)

def sourceCoordinates {b : ℝ} (hb : 0 < b) : sourceSpace hb ≃ₗᵢ[ℂ] Coordinates :=
  (synthesisIsometry hb).equivRange.symm

theorem sourceSpace_eq_span {b : ℝ} (hb : 0 < b) :
    sourceSpace hb = Submodule.span ℂ (Set.range (sourceModes hb)) := by
  apply le_antisymm
  · rintro v ⟨c, rfl⟩
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  · rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    fin_cases i
    · exact ⟨WithLp.toLp 2 ![(1 : ℂ), 0], by simp [synthesis, sourceModes]⟩
    · exact ⟨WithLp.toLp 2 ![(0 : ℂ), 1], by simp [synthesis, sourceModes]⟩

theorem sourceSpace_finrank {b : ℝ} (hb : 0 < b) :
    Module.finrank ℂ (sourceSpace hb) = 2 := by
  rw [(sourceCoordinates hb).toLinearEquiv.finrank_eq]
  exact finrank_euclideanSpace_fin

def representative (b : ℝ) (c : Coordinates) (y : ℝ) : ℂ :=
  c 0 * (groundProfile b y : ℂ) + c 1 * (firstProfile b y : ℂ)

theorem synthesis_coe {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    synthesis hb c =ᵐ[volume] representative b c := by
  filter_upwards [Lp.coeFn_add (c 0 • groundState hb) (c 1 • firstState hb),
    Lp.coeFn_smul (c 0) (groundState hb), Lp.coeFn_smul (c 1) (firstState hb),
    groundState_coe hb, firstState_coe hb] with y ha h0 h1 hg hf
  change (c 0 • groundState hb + c 1 • firstState hb) y = _
  rw [ha]
  change (c 0 • groundState hb) y + (c 1 • firstState hb) y = _
  rw [h0, h1]
  simp only [Pi.smul_apply, smul_eq_mul, hg, hf, representative]

theorem representative_memLp {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    MemLp (representative b c) 2 volume :=
  (Lp.memLp (synthesis hb c)).ae_eq (synthesis_coe hb c)

theorem lowering_representative {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    lowering b (representative b c) = fun y => c 1 * (groundProfile b y : ℂ) := by
  funext y
  have hd0 := (groundProfile_hasDerivAt hb y).ofReal_comp
  have hd1 := (firstProfile_hasDerivAt hb y).ofReal_comp
  have hd := (hd0.const_mul (c 0)).add (hd1.const_mul (c 1))
  have h0 := congrFun (lowering_ground hb) y
  have h1 := congrFun (lowering_first hb) y
  simp only [lowering, hd0.deriv, hd1.deriv, Pi.zero_apply] at h0 h1
  change ((b : ℂ) * deriv (representative b c) y +
    (y / b : ℝ) * representative b c y) / (Real.sqrt 2 : ℝ) = _
  rw [show deriv (representative b c) y = _ from hd.deriv]
  dsimp only [representative]
  linear_combination c 0 * h0 + c 1 * h1

theorem raising_const_mul (b : ℝ) (z : ℂ) {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) :
    raising b (fun y => z * f y) = fun y => z * raising b f y := by
  funext y
  have hd := (hf y).hasDerivAt.const_mul z
  rw [raising, hd.deriv]
  dsimp only [raising]
  ring

theorem number_representative {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    raising b (lowering b (representative b c)) =
      fun y => c 1 * (firstProfile b y : ℂ) := by
  rw [lowering_representative hb c, raising_const_mul b (c 1)
    (fun y => (groundProfile_hasDerivAt hb y).ofReal_comp.differentiableAt), raising_ground hb]

/-- The bounded compression supported on the actual two-mode source space. -/
def compressedLowering {b : ℝ} (hb : 0 < b) : ComplexL2 →L[ℂ] ComplexL2 :=
  InnerProductSpace.rankOne ℂ (groundState hb) (firstState hb)

def compressedRaising {b : ℝ} (hb : 0 < b) : ComplexL2 →L[ℂ] ComplexL2 :=
  (compressedLowering hb).adjoint

def compressedNumber {b : ℝ} (hb : 0 < b) : ComplexL2 →L[ℂ] ComplexL2 :=
  (compressedRaising hb).comp (compressedLowering hb)

theorem compressedLowering_synthesis {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedLowering hb (synthesis hb c) = c 1 • groundState hb := by
  simp [compressedLowering, InnerProductSpace.rankOne_apply, synthesis,
    inner_add_right, inner_smul_right, inner_first_ground hb, firstState_norm hb]

theorem compressedRaising_synthesis {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedRaising hb (synthesis hb c) = c 0 • firstState hb := by
  simp [compressedRaising, compressedLowering, InnerProductSpace.adjoint_rankOne,
    InnerProductSpace.rankOne_apply, synthesis, inner_add_right, inner_smul_right,
    inner_ground_first hb, inner_self_eq_norm_sq_to_K, groundState_norm hb]

theorem compressedNumber_synthesis {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedNumber hb (synthesis hb c) = c 1 • firstState hb := by
  rw [compressedNumber, ContinuousLinearMap.comp_apply, compressedLowering_synthesis]
  simp [compressedRaising,
    compressedLowering, InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_apply,
    inner_self_eq_norm_sq_to_K, groundState_norm hb]

/-- The compression agrees with differentiation of every source representative. -/
theorem compressedLowering_differential {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedLowering hb (synthesis hb c) =ᵐ[volume] lowering b (representative b c) := by
  rw [compressedLowering_synthesis, lowering_representative hb c]
  filter_upwards [Lp.coeFn_smul (c 1) (groundState hb), groundState_coe hb] with y hs hg
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hg]

theorem compressedNumber_differential {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedNumber hb (synthesis hb c) =ᵐ[volume]
      raising b (lowering b (representative b c)) := by
  rw [compressedNumber_synthesis, number_representative hb c]
  filter_upwards [Lp.coeFn_smul (c 1) (firstState hb), firstState_coe hb] with y hs hf
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hf]

theorem compressedLowering_coordinates {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedLowering hb (synthesis hb c) =
      synthesis hb (WithLp.toLp 2 ![c 1, 0]) := by
  rw [compressedLowering_synthesis]
  simp [synthesis]

theorem compressedRaising_coordinates {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedRaising hb (synthesis hb c) =
      synthesis hb (WithLp.toLp 2 ![0, c 0]) := by
  rw [compressedRaising_synthesis]
  simp [synthesis]

theorem compressedNumber_coordinates {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedNumber hb (synthesis hb c) =
      synthesis hb (WithLp.toLp 2 ![0, c 1]) := by
  rw [compressedNumber_synthesis]
  simp [synthesis]

theorem compressedLowering_matrix {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedLowering hb (synthesis hb c) = synthesis hb
      (WithLp.toLp 2 ((!![(0 : ℂ), 1; 0, 0]).mulVec (fun i => c i))) := by
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using compressedLowering_coordinates hb c

theorem compressedRaising_matrix {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedRaising hb (synthesis hb c) = synthesis hb
      (WithLp.toLp 2 ((!![(0 : ℂ), 0; 1, 0]).mulVec (fun i => c i))) := by
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using compressedRaising_coordinates hb c

theorem compressedNumber_matrix {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedNumber hb (synthesis hb c) = synthesis hb
      (WithLp.toLp 2 ((!![(0 : ℂ), 0; 0, 1]).mulVec (fun i => c i))) := by
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using compressedNumber_coordinates hb c

theorem groundState_ne_zero {b : ℝ} (hb : 0 < b) : groundState hb ≠ 0 := by
  intro h
  have hn := groundState_norm hb
  rw [h, norm_zero] at hn
  norm_num at hn

theorem compressedLowering_kernel_coordinates {b : ℝ} (hb : 0 < b) (c : Coordinates) :
    compressedLowering hb (synthesis hb c) = 0 ↔ c 1 = 0 := by
  rw [compressedLowering_synthesis, smul_eq_zero]
  simp [groundState_ne_zero hb]

/-- The annihilation line is the line through the actual Gaussian ground state. -/
theorem source_vacuum_line {b : ℝ} (hb : 0 < b) (v : ComplexL2)
    (hv : v ∈ sourceSpace hb) :
    compressedLowering hb v = 0 ↔ ∃ z : ℂ, v = z • groundState hb := by
  constructor
  · intro ha
    obtain ⟨c, rfl⟩ := hv
    have hc := (compressedLowering_kernel_coordinates hb c).mp ha
    exact ⟨c 0, by simp [synthesis, hc]⟩
  · rintro ⟨z, rfl⟩
    simp [compressedLowering, InnerProductSpace.rankOne_apply,
      inner_first_ground hb]

end GeneratedFoundations.Operations.HermiteSource
