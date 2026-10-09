module

public import GeneratedFoundations.Operations.GaussianAffineLadder
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# The Gaussian vacuum and Hilbert adjoint on the Schwartz core

The normalized Gaussian is constructed as a Schwartz function and identified
with the previously generated Lebesgue `L²` vector. The Hilbert adjoint agrees
with formal adjunction on this common invariant core. This gives the original
annihilation and commutator hypotheses their Hilbert-space meaning and proves
that both ordered products are independent of the residual unit phase.

The statements concern the actual Schwartz core. They do not identify the
maximal domains of products or assert essential self-adjointness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Polynomial
open scoped SchwartzMap ComplexConjugate
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.GaussianAffineLadder

namespace GeneratedFoundations.Operations.GaussianLadderCore

/-- A direct global Gaussian bound, obtained from the exponential series. -/
theorem pow_mul_gaussian_bound (n : ℕ) (x : ℝ) :
    ‖x‖ ^ n * Real.exp (-(x ^ 2 / 2)) ≤
      (n.factorial : ℝ) * Real.exp (1 / 2) := by
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hp : ‖x‖ ^ n ≤ Real.exp ‖x‖ * (n.factorial : ℝ) :=
    (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp ‖x‖ (norm_nonneg x) n)
  have hx : ‖x‖ - x ^ 2 / 2 ≤ 1 / 2 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  calc
    ‖x‖ ^ n * Real.exp (-(x ^ 2 / 2)) ≤
        (Real.exp ‖x‖ * (n.factorial : ℝ)) * Real.exp (-(x ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * Real.exp (‖x‖ - x ^ 2 / 2) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ (n.factorial : ℝ) * Real.exp (1 / 2) := by
      gcongr

theorem polynomial_mul_gaussian_bound (p : ℝ[X]) :
    ∃ C : ℝ, ∀ x : ℝ, ‖p.eval x‖ * Real.exp (-(x ^ 2 / 2)) ≤ C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨C, hC⟩ := hp
      obtain ⟨D, hD⟩ := hq
      refine ⟨C + D, fun x => ?_⟩
      rw [Polynomial.eval_add]
      calc
        ‖p.eval x + q.eval x‖ * Real.exp (-(x ^ 2 / 2)) ≤
            (‖p.eval x‖ + ‖q.eval x‖) * Real.exp (-(x ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_pos _).le
        _ ≤ C + D := by rw [add_mul]; exact add_le_add (hC x) (hD x)
  | monomial n a =>
      refine ⟨‖a‖ * ((n.factorial : ℝ) * Real.exp (1 / 2)), fun x => ?_⟩
      simpa only [Polynomial.eval_monomial, norm_mul, norm_pow, mul_assoc] using
        mul_le_mul_of_nonneg_left (pow_mul_gaussian_bound n x) (norm_nonneg a)

/-- Every derivative is controlled using its actual Hermite polynomial factor. -/
def standardGaussian : SchwartzMap ℝ ℝ where
  toFun x := Real.exp (-(x ^ 2 / 2))
  smooth' := by fun_prop
  decay' k n := by
    obtain ⟨C, hC⟩ := polynomial_mul_gaussian_bound
      (X ^ k * (hermite n).map (Int.castRingHom ℝ))
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
    simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_map, Polynomial.aeval_def, norm_mul, norm_pow,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_assoc] using hC x

theorem dilation_growth {b : ℝ} (hb : 0 < b) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖x / b‖) ^ k := by
  refine ⟨1, b, fun x => ?_⟩
  rw [pow_one, norm_div, Real.norm_of_nonneg hb.le]
  have hx : b * (‖x‖ / b) = ‖x‖ := by field_simp [hb.ne']
  nlinarith

def realGroundSchwartz {b : ℝ} (hb : 0 < b) : SchwartzMap ℝ ℝ :=
  (Real.sqrt (GeneratedFoundations.Correlation.GaussianCorrelation.normalizationMass
    (sourceWidth b)))⁻¹ •
      SchwartzMap.compCLM ℝ (g := fun x : ℝ => x / b)
        (by simp only [div_eq_mul_inv]; fun_prop)
        (dilation_growth hb) standardGaussian

theorem realGroundSchwartz_apply {b : ℝ} (hb : 0 < b) (x : ℝ) :
    realGroundSchwartz hb x = groundProfile b x := by
  change (Real.sqrt _)⁻¹ * Real.exp (-((x / b) ^ 2 / 2)) = _
  rw [groundProfile_eq]
  have hx : (x / b) ^ 2 / 2 = x ^ 2 / (2 * b ^ 2) := by
    field_simp
  rw [hx]
  ring

def groundSchwartz {b : ℝ} (hb : 0 < b) : Core :=
  (realGroundSchwartz hb).postcompCLM Complex.ofRealCLM

@[simp] theorem groundSchwartz_apply {b : ℝ} (hb : 0 < b) (x : ℝ) :
    groundSchwartz hb x = (groundProfile b x : ℂ) := by
  simp only [groundSchwartz, SchwartzMap.postcompCLM_apply,
    Complex.ofRealCLM_apply, realGroundSchwartz_apply]

theorem groundSchwartz_coe {b : ℝ} (hb : 0 < b) :
    (groundSchwartz hb : ℝ → ℂ) = fun x => (groundProfile b x : ℂ) :=
  funext (groundSchwartz_apply hb)

/-- The Schwartz construction and the generated source give the same `L²` vector. -/
theorem embedding_groundSchwartz {b : ℝ} (hb : 0 < b) :
    embedding (groundSchwartz hb) = groundState hb := by
  apply Lp.ext
  filter_upwards [(groundSchwartz hb).coeFn_toLp 2 volume, groundState_coe hb] with x hs hg
  change ((groundSchwartz hb).toLp 2 volume) x = groundState hb x
  rw [hs, hg, groundSchwartz_apply]

theorem groundState_mem_core {b : ℝ} (hb : 0 < b) : groundState hb ∈ coreDomain := by
  rw [← embedding_groundSchwartz hb]
  exact (coreEquiv (groundSchwartz hb)).property

/-- Scalar multiplication acts on the whole affine comparison class. -/
def scaleCoefficients (z : ℂ) (c : Coefficients) : Coefficients :=
  ⟨z * c.c₀, z * c.c₁, z * c.c₂⟩

theorem core_scale (b : ℝ) (z : ℂ) (c : Coefficients) :
    core b (scaleCoefficients z c) = z • core b c := by
  ext f x
  simp only [core_apply, differential, scaleCoefficients, smul_apply, smul_eq_mul]
  ring

theorem formal_scale (z : ℂ) (c : Coefficients) :
    formalCoefficients (scaleCoefficients z c) =
      scaleCoefficients (conj z) (formalCoefficients c) := by
  simp only [formalCoefficients, scaleCoefficients, map_mul]
  congr 1
  ring

/-- Both orderings are unchanged by multiplication of the operator by a unit phase. -/
theorem ordered_products_phase_independent (b : ℝ) (c : Coefficients)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (core b (formalCoefficients (scaleCoefficients z c))).comp
        (core b (scaleCoefficients z c)) =
      (core b (formalCoefficients c)).comp (core b c) ∧
    (core b (scaleCoefficients z c)).comp
        (core b (formalCoefficients (scaleCoefficients z c))) =
      (core b c).comp (core b (formalCoefficients c)) := by
  rw [formal_scale, core_scale, core_scale]
  constructor <;> ext f <;>
    simp [ContinuousLinearMap.comp_apply, smul_smul, Complex.conj_mul',
      Complex.mul_conj', hz]

def canonicalCoefficients : Coefficients :=
  ⟨0, (Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹⟩

theorem coefficients_eq_phase_canonical {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (hground : differential b c (fun x => (groundProfile b x : ℂ)) = 0) :
    c = scaleCoefficients (phase c) canonicalCoefficients := by
  have hc := annihilation_forces_coefficients hb c hground
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  cases c with
  | mk c₀ c₁ c₂ =>
      simp only at hc
      simp only [scaleCoefficients, canonicalCoefficients, phase]
      congr 1
      · simp [hc.2]
      · field_simp [hs]
      · rw [hc.1]; field_simp [hs]

theorem ordered_products_eq_canonical {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (hground : differential b c (fun x => (groundProfile b x : ℂ)) = 0)
    (hCCR : ∀ f : Core, core b c (core b (formalCoefficients c) f) -
      core b (formalCoefficients c) (core b c f) = f) :
    (core b (formalCoefficients c)).comp (core b c) =
      (core b (formalCoefficients canonicalCoefficients)).comp (core b canonicalCoefficients) ∧
    (core b c).comp (core b (formalCoefficients c)) =
      (core b canonicalCoefficients).comp (core b (formalCoefficients canonicalCoefficients)) := by
  have h := ordered_products_phase_independent b canonicalCoefficients
    (phase_norm hb c hground hCCR)
  rwa [← coefficients_eq_phase_canonical hb c hground] at h

/-- A core vector is in the domain of the maximal Hilbert adjoint. -/
def adjointCorePoint (b : ℝ) (c : Coefficients) (f : Core) :
    (liftCore (core b c)).adjoint.domain :=
  ⟨embedding f, (core_adjoint_le_hilbert_adjoint b c).1 (coreEquiv f).property⟩

theorem adjoint_on_core (b : ℝ) (c : Coefficients) (f : Core) :
    (liftCore (core b c)).adjoint (adjointCorePoint b c f) =
      embedding (core b (formalCoefficients c) f) := by
  exact ((core_adjoint_le_hilbert_adjoint b c).2
    (x := coreEquiv f) (y := adjointCorePoint b c f) rfl).symm.trans
      (liftCore_coreEquiv _ f)

theorem adjoint_preserves_core (b : ℝ) (c : Coefficients) (f : Core) :
    (liftCore (core b c)).adjoint (adjointCorePoint b c f) ∈ coreDomain := by
  rw [adjoint_on_core]
  exact (coreEquiv (core b (formalCoefficients c) f)).property

/-- Apply the actual Hilbert adjoint first, then the original core operator. -/
def hilbertAdjointThenCore (b : ℝ) (c : Coefficients) (f : Core) : ComplexL2 :=
  liftCore (core b c) ⟨(liftCore (core b c)).adjoint (adjointCorePoint b c f),
    adjoint_preserves_core b c f⟩

/-- Apply the original operator first; its core image lies in the Hilbert adjoint domain. -/
def coreThenHilbertAdjoint (b : ℝ) (c : Coefficients) (f : Core) : ComplexL2 :=
  (liftCore (core b c)).adjoint (adjointCorePoint b c (core b c f))

theorem hilbertAdjointThenCore_eq (b : ℝ) (c : Coefficients) (f : Core) :
    hilbertAdjointThenCore b c f =
      embedding (core b c (core b (formalCoefficients c) f)) := by
  have h : (⟨(liftCore (core b c)).adjoint (adjointCorePoint b c f),
      adjoint_preserves_core b c f⟩ : coreDomain) =
        coreEquiv (core b (formalCoefficients c) f) := by
    apply Subtype.ext
    exact adjoint_on_core b c f
  exact (congrArg (fun u : coreDomain => liftCore (core b c) u) h).trans
    (liftCore_coreEquiv _ _)

theorem coreThenHilbertAdjoint_eq (b : ℝ) (c : Coefficients) (f : Core) :
    coreThenHilbertAdjoint b c f =
      embedding (core b (formalCoefficients c) (core b c f)) :=
  adjoint_on_core b c (core b c f)

def HilbertCCR (b : ℝ) (c : Coefficients) : Prop :=
  ∀ f : Core, hilbertAdjointThenCore b c f - coreThenHilbertAdjoint b c f = embedding f

theorem hilbertCCR_iff_coreCCR (b : ℝ) (c : Coefficients) :
    HilbertCCR b c ↔ ∀ f : Core,
      core b c (core b (formalCoefficients c) f) -
        core b (formalCoefficients c) (core b c f) = f := by
  simp only [HilbertCCR, hilbertAdjointThenCore_eq, coreThenHilbertAdjoint_eq,
    ← map_sub, embedding_injective.eq_iff]

theorem ground_annihilation_iff {b : ℝ} (hb : 0 < b) (c : Coefficients) :
    liftCore (core b c) (coreEquiv (groundSchwartz hb)) = 0 ↔
      differential b c (fun x => (groundProfile b x : ℂ)) = 0 := by
  rw [liftCore_coreEquiv, ← map_zero embedding, embedding_injective.eq_iff]
  constructor
  · intro h
    funext x
    have hx := congrArg (fun f : Core => f x) h
    simpa only [core_apply, groundSchwartz_coe, zero_apply, Pi.zero_apply] using hx
  · intro h
    ext x
    simpa only [core_apply, groundSchwartz_coe, Pi.zero_apply, zero_apply] using congrFun h x

/-- Hilbert-space annihilation and CCR imply the full affine uniqueness conclusion. -/
theorem gaussian_ladder_unique_on_hilbert_core {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (hground : liftCore (core b c) (coreEquiv (groundSchwartz hb)) = 0)
    (hCCR : HilbertCCR b c) :
    ∃! z : ℂ, ‖z‖ = 1 ∧ ∀ f : ℝ → ℂ,
      differential b c f = fun x => z * lowering b f x :=
  gaussian_affine_ladder_unique hb c ((ground_annihilation_iff hb c).mp hground)
    ((hilbertCCR_iff_coreCCR b c).mp hCCR)

/-- The phase cancellation also holds for both actual Hilbert-space products on the core. -/
theorem hilbert_ordered_products_eq_canonical {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (hground : liftCore (core b c) (coreEquiv (groundSchwartz hb)) = 0)
    (hCCR : HilbertCCR b c) (f : Core) :
    coreThenHilbertAdjoint b c f = coreThenHilbertAdjoint b canonicalCoefficients f ∧
    hilbertAdjointThenCore b c f = hilbertAdjointThenCore b canonicalCoefficients f := by
  have h := ordered_products_eq_canonical hb c ((ground_annihilation_iff hb c).mp hground)
    ((hilbertCCR_iff_coreCCR b c).mp hCCR)
  constructor
  · rw [coreThenHilbertAdjoint_eq, coreThenHilbertAdjoint_eq]
    exact congrArg embedding (congrArg (fun T : Core →L[ℂ] Core => T f) h.1)
  · rw [hilbertAdjointThenCore_eq, hilbertAdjointThenCore_eq]
    exact congrArg embedding (congrArg (fun T : Core →L[ℂ] Core => T f) h.2)

end GeneratedFoundations.Operations.GaussianLadderCore
