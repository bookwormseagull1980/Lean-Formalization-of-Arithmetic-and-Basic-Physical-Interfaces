module

public import GeneratedFoundations.Operations.HermiteSource
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Gaussian annihilation in the complex affine first-order class

The three coefficients of the differential expression are arbitrary complex
numbers. The Gaussian annihilation equation determines their affine relations;
the canonical commutator on Schwartz space determines the remaining magnitude.
The formal adjoint is verified by integration by parts on the actual Schwartz
core and is distinguished from the maximal Hilbert adjoint.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap ComplexConjugate
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteSource

namespace GeneratedFoundations.Operations.GaussianAffineLadder

structure Coefficients where
  c₀ : ℂ
  c₁ : ℂ
  c₂ : ℂ

def differential (b : ℝ) (c : Coefficients) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  c.c₁ * b * deriv f x + c.c₂ * (x / b : ℝ) * f x + c.c₀ * f x

def formalCoefficients (c : Coefficients) : Coefficients :=
  ⟨conj c.c₀, -conj c.c₁, conj c.c₂⟩

abbrev Core := SchwartzMap ℝ ℂ

def derivative : Core →L[ℂ] Core := SchwartzMap.derivCLM ℂ ℂ

def position : Core →L[ℂ] Core :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

@[simp] theorem derivative_apply (f : Core) (x : ℝ) :
    derivative f x = deriv f x := rfl

@[simp] theorem position_apply (f : Core) (x : ℝ) :
    position f x = (x : ℂ) * f x := by
  simpa only [position, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
      (by fun_prop : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth) f x

def core (b : ℝ) (c : Coefficients) : Core →L[ℂ] Core :=
  (c.c₁ * b) • derivative + (c.c₂ / b) • position +
    c.c₀ • ContinuousLinearMap.id ℂ Core

theorem core_apply (b : ℝ) (c : Coefficients) (f : Core) (x : ℝ) :
    core b c f x = differential b c f x := by
  simp only [core, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    derivative_apply, position_apply, smul_eq_mul, differential, Complex.ofReal_div]
  ring

theorem core_hasDerivAt (b : ℝ) (c : Coefficients) (f : Core) (x : ℝ) :
    HasDerivAt (core b c f)
      (c.c₁ * b * deriv (derivative f) x +
        (c.c₂ / b) * (f x + x * deriv f x) + c.c₀ * deriv f x) x := by
  have hd := (((derivative f).hasDerivAt x).const_mul (c.c₁ * b)).add
    ((((hasDerivAt_id x).ofReal_comp).mul (f.hasDerivAt x)).const_mul (c.c₂ / b))
  have h := hd.add ((f.hasDerivAt x).const_mul c.c₀)
  convert h using 1
  · funext y
    rw [core_apply]
    simp only [differential, derivative_apply, Complex.ofReal_div,
      Pi.add_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [Complex.ofReal_one, one_mul, id_eq]

theorem groundProfile_pos {b : ℝ} (hb : 0 < b) (x : ℝ) :
    0 < groundProfile b x := by
  rw [groundProfile_eq]
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr
    (GeneratedFoundations.Correlation.GaussianCorrelation.normalizationMass_pos
      (sourceWidth_pos hb)))

theorem differential_ground {b : ℝ} (hb : 0 < b) (c : Coefficients) (x : ℝ) :
    differential b c (fun y => (groundProfile b y : ℂ)) x =
      ((c.c₂ - c.c₁) * (x / b : ℝ) + c.c₀) * (groundProfile b x : ℂ) := by
  rw [differential, (groundProfile_hasDerivAt hb x).ofReal_comp.deriv]
  push_cast
  field_simp [hb.ne']
  ring

/-- No affine coefficient relation is assumed in the annihilation equation. -/
theorem annihilation_forces_coefficients {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (h : differential b c (fun y => (groundProfile b y : ℂ)) = 0) :
    c.c₂ = c.c₁ ∧ c.c₀ = 0 := by
  have hzero := congrFun h 0
  rw [differential_ground hb] at hzero
  simp only [zero_div, Complex.ofReal_zero, mul_zero, zero_add, Pi.zero_apply] at hzero
  have hg0 : (groundProfile b 0 : ℂ) ≠ 0 := by
    exact_mod_cast (groundProfile_pos hb 0).ne'
  have hc0 : c.c₀ = 0 := (mul_eq_zero.mp hzero).resolve_right hg0
  have hone := congrFun h b
  rw [differential_ground hb, hc0] at hone
  simp only [div_self hb.ne', Complex.ofReal_one, mul_one, add_zero, Pi.zero_apply] at hone
  have hgb : (groundProfile b b : ℂ) ≠ 0 := by
    exact_mod_cast (groundProfile_pos hb b).ne'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hone).resolve_right hgb), hc0⟩

/-- The commutator is calculated from the differential expressions on the core. -/
theorem core_commutator {b : ℝ} (hb : 0 < b) (c : Coefficients) (f : Core) :
    core b c (core b (formalCoefficients c) f) -
      core b (formalCoefficients c) (core b c f) =
        (c.c₁ * conj c.c₂ + c.c₂ * conj c.c₁) • f := by
  ext x
  simp only [sub_apply, smul_apply, smul_eq_mul,
    core_apply, differential]
  rw [(core_hasDerivAt b (formalCoefficients c) f x).deriv,
    (core_hasDerivAt b c f x).deriv]
  simp only [formalCoefficients]
  push_cast
  field_simp [hb.ne']
  ring

def embedding : Core →L[ℂ] ComplexL2 := SchwartzMap.toLpCLM ℂ ℂ 2 volume

theorem embedding_injective : Function.Injective embedding :=
  SchwartzMap.injective_toLp 2 volume

theorem embedding_dense : DenseRange embedding := by
  exact SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := volume) (p := 2) (by norm_num)

theorem exists_nonzero_core : ∃ f : Core, f ≠ 0 := by
  obtain ⟨f, hf⟩ := embedding_dense.exists_dist_lt
    (groundState (by norm_num : (0 : ℝ) < 1)) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨f, ?_⟩
  intro h
  subst f
  have hn := groundState_norm (by norm_num : (0 : ℝ) < 1)
  norm_num [hn] at hf

theorem normalized_commutator_forces_scalar {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (hCCR : ∀ f : Core, core b c (core b (formalCoefficients c) f) -
      core b (formalCoefficients c) (core b c f) = f) :
    c.c₁ * conj c.c₂ + c.c₂ * conj c.c₁ = 1 := by
  obtain ⟨f, hf⟩ := exists_nonzero_core
  have h := hCCR f
  rw [core_commutator hb c f] at h
  have hz : (c.c₁ * conj c.c₂ + c.c₂ * conj c.c₁ - 1) • f = 0 := by
    rw [sub_smul, one_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hf)

def phase (c : Coefficients) : ℂ := (Real.sqrt 2 : ℝ) * c.c₁

theorem phase_norm {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (hground : differential b c (fun y => (groundProfile b y : ℂ)) = 0)
    (hCCR : ∀ f : Core, core b c (core b (formalCoefficients c) f) -
      core b (formalCoefficients c) (core b c f) = f) :
    ‖phase c‖ = 1 := by
  have hc := annihilation_forces_coefficients hb c hground
  have hk := normalized_commutator_forces_scalar hb c hCCR
  rw [hc.1] at hk
  have hr := congrArg Complex.re hk
  have hn : 2 * ‖c.c₁‖ ^ 2 = 1 := by
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.one_re] at hr
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  rw [phase, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn0 := norm_nonneg c.c₁
  have hs0 := Real.sqrt_nonneg 2
  have hsq : (Real.sqrt 2 * ‖c.c₁‖) ^ 2 = 1 := by
    rw [mul_pow, hs]
    exact hn
  nlinarith [mul_nonneg hs0 hn0]

theorem differential_eq_phase_lowering {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (hground : differential b c (fun y => (groundProfile b y : ℂ)) = 0)
    (f : ℝ → ℂ) :
    differential b c f = fun x => phase c * lowering b f x := by
  have hc := annihilation_forces_coefficients hb c hground
  funext x
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [differential, hc.1, hc.2, zero_mul, add_zero, phase, lowering]
  field_simp [hs]

theorem embedding_inner (f g : Core) :
    inner ℂ (embedding f) (embedding g) = ∫ x : ℝ, inner ℂ (f x) (g x) :=
  SchwartzMap.inner_toL2_toL2_eq f g volume

theorem derivative_skew_symmetric (f g : Core) :
    inner ℂ (embedding (derivative f)) (embedding g) =
      -inner ℂ (embedding f) (embedding (derivative g)) := by
  have h := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left f g
    ((ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap)
  have hi : (∫ x : ℝ, inner ℂ (f x) (deriv g x)) =
      -(∫ x : ℝ, inner ℂ (deriv f x) (g x)) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, ContinuousLinearMap.mul_apply', RCLike.inner_apply,
      mul_comm] using h
  rw [embedding_inner, embedding_inner]
  simpa only [derivative_apply, neg_neg] using (congrArg Neg.neg hi).symm

theorem position_symmetric (f g : Core) :
    inner ℂ (embedding (position f)) (embedding g) =
      inner ℂ (embedding f) (embedding (position g)) := by
  rw [embedding_inner, embedding_inner]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp [position_apply, RCLike.inner_apply, mul_comm, mul_left_comm]

/-- Integration by parts proves the proposed coefficients really give the adjoint on the core. -/
theorem formal_adjoint_identity (b : ℝ) (c : Coefficients) (f g : Core) :
    inner ℂ (embedding (core b c f)) (embedding g) =
      inner ℂ (embedding f) (embedding (core b (formalCoefficients c) g)) := by
  simp [core, formalCoefficients, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, derivative_skew_symmetric, position_symmetric]

def coreDomain : Submodule ℂ ComplexL2 := LinearMap.range embedding.toLinearMap

def coreEquiv : Core ≃ₗ[ℂ] coreDomain :=
  LinearEquiv.ofInjective embedding.toLinearMap embedding_injective

@[simp] theorem coreEquiv_coe (f : Core) : (coreEquiv f : ComplexL2) = embedding f := rfl

/-- The actual Schwartz operator, represented as a densely defined operator in Lebesgue L². -/
def liftCore (T : Core →L[ℂ] Core) : ComplexL2 →ₗ.[ℂ] ComplexL2 where
  domain := coreDomain
  toFun := embedding.toLinearMap.comp (T.toLinearMap.comp coreEquiv.symm.toLinearMap)

@[simp] theorem liftCore_coreEquiv (T : Core →L[ℂ] Core) (f : Core) :
    liftCore T (coreEquiv f) = embedding (T f) := by
  simp [liftCore]

theorem liftCore_dense (T : Core →L[ℂ] Core) :
    Dense ((liftCore T).domain : Set ComplexL2) := embedding_dense

theorem core_formal_adjoint (b : ℝ) (c : Coefficients) :
    (liftCore (core b c)).IsFormalAdjoint (liftCore (core b (formalCoefficients c))) := by
  intro x y
  obtain ⟨f, rfl⟩ := coreEquiv.surjective x
  obtain ⟨g, rfl⟩ := coreEquiv.surjective y
  simpa only [liftCore_coreEquiv, coreEquiv_coe] using formal_adjoint_identity b c f g

/-- Graph containment in the maximal Hilbert adjoint; no equality of full domains is asserted. -/
theorem core_adjoint_le_hilbert_adjoint (b : ℝ) (c : Coefficients) :
    liftCore (core b (formalCoefficients c)) ≤ (liftCore (core b c)).adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint (liftCore_dense (core b c)) (core_formal_adjoint b c)

/-- Classification within the full complex affine first-order comparison class. -/
theorem gaussian_affine_ladder_unique {b : ℝ} (hb : 0 < b) (c : Coefficients)
    (hground : differential b c (fun y => (groundProfile b y : ℂ)) = 0)
    (hCCR : ∀ f : Core, core b c (core b (formalCoefficients c) f) -
      core b (formalCoefficients c) (core b c f) = f) :
    ∃! z : ℂ, ‖z‖ = 1 ∧ ∀ f : ℝ → ℂ,
      differential b c f = fun x => z * lowering b f x := by
  refine ⟨phase c, ⟨phase_norm hb c hground hCCR,
    differential_eq_phase_lowering hb c hground⟩, ?_⟩
  intro z hz
  have h := congrFun ((hz.2 (fun x => (firstProfile b x : ℂ))).symm.trans
    (differential_eq_phase_lowering hb c hground (fun x => (firstProfile b x : ℂ)))) 0
  simp only [lowering_first hb] at h
  have hg : (groundProfile b 0 : ℂ) ≠ 0 := by
    exact_mod_cast (groundProfile_pos hb 0).ne'
  exact mul_right_cancel₀ hg h

end GeneratedFoundations.Operations.GaussianAffineLadder
