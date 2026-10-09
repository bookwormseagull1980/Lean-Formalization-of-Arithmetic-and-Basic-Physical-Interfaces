module

public import GeneratedFoundations.Spectral.AngularGenerator
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The strong flow of the original periodic derivative

The Fourier multipliers define a strongly continuous group on the original
Haar Hilbert space. Square-summable domination identifies its entire strong
generator domain with the previously constructed periodic Sobolev domain.
Both inclusions are proved; convergence on individual Fourier modes alone
is not used as a domain criterion.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory InnerProductSpace
open scoped Topology lp LinearPMap
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Spectral.AngularFlow

abbrev Sequence := ℓ²(ℤ, ℂ)

def phase (t : ℝ) (n : ℤ) : ℂ := Complex.exp (Complex.I * (((n : ℝ) * t : ℝ) : ℂ))

@[simp] theorem phase_zero (n : ℤ) : phase 0 n = 1 := by simp [phase]

theorem phase_norm (t : ℝ) (n : ℤ) : ‖phase t n‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_add (s t : ℝ) (n : ℤ) : phase (s + t) n = phase s n * phase t n := by
  simp only [phase, mul_add, Complex.ofReal_add, Complex.exp_add]

theorem phase_continuous (n : ℤ) : Continuous (fun t => phase t n) := by
  unfold phase
  fun_prop

theorem phase_hasDerivAt_zero (n : ℤ) :
    HasDerivAt (fun t : ℝ => phase t n) (Complex.I * (n : ℂ)) 0 := by
  have hx := ((((hasDerivAt_id (0 : ℝ)).const_mul (n : ℝ)).ofReal_comp).const_mul
    Complex.I).cexp
  simpa [phase] using hx

theorem phase_sub_one_bound (t : ℝ) (n : ℤ) :
    ‖phase t n - 1‖ ≤ ‖t‖ * ‖(n : ℝ)‖ := by
  simpa only [phase, norm_mul, mul_comm] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (n : ℝ) * t))

theorem phase_slope_tendsto (n : ℤ) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) * (phase t n - 1))
      (𝓝[≠] 0) (𝓝 (Complex.I * (n : ℂ))) := by
  simpa only [zero_add, phase_zero, Complex.real_smul, Complex.ofReal_inv] using
    (phase_hasDerivAt_zero n).tendsto_slope_zero

def sequenceMap (t : ℝ) (v : Sequence) : Sequence :=
  ⟨fun n => phase t n * v n, (lp.memℓp v).mono' (by
    intro n
    simp only [norm_mul, phase_norm, one_mul, le_refl])⟩

@[simp] theorem sequenceMap_apply (t : ℝ) (v : Sequence) (n : ℤ) :
    sequenceMap t v n = phase t n * v n := rfl

def sequenceLinear (t : ℝ) : Sequence →ₗ[ℂ] Sequence where
  toFun := sequenceMap t
  map_add' v w := by
    apply lp.ext
    funext n
    change phase t n * (v n + w n) = phase t n * v n + phase t n * w n
    ring
  map_smul' c v := by
    apply lp.ext
    funext n
    change phase t n * (c * v n) = c * (phase t n * v n)
    ring

theorem sequence_norm (t : ℝ) (v : Sequence) : ‖sequenceLinear t v‖ = ‖v‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num)
    intro n
    change ‖phase t n * v n‖ ≤ ‖v n‖
    simp only [norm_mul, phase_norm, one_mul, le_refl]
  · apply lp.norm_mono (by norm_num)
    intro n
    change ‖v n‖ ≤ ‖phase t n * v n‖
    simp only [norm_mul, phase_norm, one_mul, le_refl]

def sequenceOperator (t : ℝ) : Sequence →L[ℂ] Sequence :=
  (sequenceLinear t).mkContinuous 1 (by
    intro v
    simp only [sequence_norm, one_mul, le_refl])

private theorem sequence_norm_sq (v : Sequence) : ‖v‖ ^ 2 = ∑' n, ‖v n‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v

private theorem sequence_summable (v : Sequence) : Summable (fun n => ‖v n‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)

private theorem sequence_tendsto_zero {α : Type*} {l : Filter α} (v : α → Sequence)
    (bound : ℤ → ℝ) (hsum : Summable bound)
    (hpoint : ∀ n, Tendsto (fun a => v a n) l (𝓝 0))
    (hbound : ∀ᶠ a in l, ∀ n, ‖v a n‖ ^ 2 ≤ bound n) : Tendsto v l (𝓝 0) := by
  have hsq : Tendsto (fun a => ‖v a‖ ^ 2) l (𝓝 0) := by
    simp_rw [sequence_norm_sq]
    have hsumlimit := tendsto_tsum_of_dominated_convergence
      (f := fun a n => ‖v a n‖ ^ 2) (g := fun _ => (0 : ℝ)) hsum
      (fun n => by simpa using (hpoint n).norm.pow 2)
      (hbound.mono (fun a ha n => by simpa only [Real.norm_eq_abs, abs_sq] using ha n))
    simpa only [tsum_zero] using hsumlimit
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

theorem sequence_stronglyContinuous (v : Sequence) :
    Continuous (fun t : ℝ => sequenceOperator t v) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero _ (fun n => 4 * ‖v n‖ ^ 2)
    ((sequence_summable v).mul_left 4)
  · intro n
    have hc := ((phase_continuous n).continuousAt (x := s)).mul_const (v n)
    change Tendsto (fun t : ℝ => phase t n * v n - phase s n * v n) (𝓝 s) (𝓝 0)
    simpa only [sub_self] using hc.tendsto.sub_const (phase s n * v n)
  · apply Eventually.of_forall
    intro t n
    have hpart (r : ℝ) : ‖phase r n * v n‖ = ‖v n‖ := by
      rw [norm_mul, phase_norm, one_mul]
    have hnorm : ‖phase t n * v n - phase s n * v n‖ ≤ 2 * ‖v n‖ :=
      (norm_sub_le _ _).trans (by rw [hpart, hpart]; linarith)
    change ‖phase t n * v n - phase s n * v n‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (phase t n * v n - phase s n * v n), norm_nonneg (v n)]

private theorem sequence_derivative (v w : Sequence)
    (hw : ∀ n, w n = Complex.I * (n : ℂ) * v n) :
    Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (sequenceOperator t v - v)) (𝓝[≠] 0) (𝓝 w) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero _ (fun n => 4 * ‖w n‖ ^ 2)
    ((sequence_summable w).mul_left 4)
  · intro n
    have hp := ((phase_slope_tendsto n).mul_const (v n)).sub_const (w n)
    convert hp using 1
    · funext t
      change (t⁻¹ : ℂ) * (phase t n * v n - v n) - w n = _
      ring
    · rw [hw, sub_self]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    intro n
    have ht0 : t ≠ 0 := ht
    have htNorm : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht0
    have hn : ‖w n‖ = ‖(n : ℝ)‖ * ‖v n‖ := by
      rw [hw, norm_mul, norm_mul, Complex.norm_I, one_mul]
      rw [← Complex.ofReal_intCast, Complex.norm_real]
    have hq : ‖(t⁻¹ : ℂ) * (phase t n * v n - v n)‖ ≤ ‖w n‖ := by
      rw [show phase t n * v n - v n = (phase t n - 1) * v n by ring,
        norm_mul, norm_mul, norm_inv, Complex.norm_real]
      calc
        _ ≤ ‖t‖⁻¹ * ((‖t‖ * ‖(n : ℝ)‖) * ‖v n‖) := by
          gcongr
          exact phase_sub_one_bound t n
        _ = ‖(n : ℝ)‖ * ‖v n‖ := by field_simp [htNorm]
        _ = ‖w n‖ := hn.symm
    have hdiff := norm_sub_le ((t⁻¹ : ℂ) * (phase t n * v n - v n)) (w n)
    change ‖(t⁻¹ : ℂ) * (phase t n * v n - v n) - w n‖ ^ 2 ≤ _
    nlinarith [norm_nonneg ((t⁻¹ : ℂ) * (phase t n * v n - v n) - w n),
      norm_nonneg (w n)]

variable (L : ℝ) [hL : Fact (0 < L)]

def coefficients : HaarCircleL2 L ≃ₗᵢ[ℂ] Sequence := (fourierBasis (T := 2 * L)).repr

theorem coefficients_apply (f : HaarCircleL2 L) (n : ℤ) :
    coefficients L f n = inner ℂ (fourierLp 2 n) f := by
  simpa only [coefficients, coe_fourierBasis] using
    (fourierBasis (T := 2 * L)).repr_apply_apply f n

def flow (t : ℝ) : HaarCircleL2 L →L[ℂ] HaarCircleL2 L :=
  (coefficients L).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sequenceOperator t).comp (coefficients L).toContinuousLinearEquiv.toContinuousLinearMap)

theorem coefficients_flow (t : ℝ) (f : HaarCircleL2 L) :
    coefficients L (flow L t f) = sequenceOperator t (coefficients L f) := by
  simp [flow]

theorem flow_coefficient (t : ℝ) (f : HaarCircleL2 L) (n : ℤ) :
    inner ℂ (fourierLp 2 n) (flow L t f) = phase t n * inner ℂ (fourierLp 2 n) f := by
  simp only [← coefficients_apply, coefficients_flow]
  rfl

theorem flow_fourier (t : ℝ) (n : ℤ) :
    flow L t (fourierLp 2 n) = phase t n • fourierLp 2 n := by
  apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
  intro k
  simp only [coe_fourierBasis, flow_coefficient, inner_smul_right, haarFourier_inner]
  by_cases hk : k = n
  · subst k
    simp only [ite_true]
  · simp only [ite_eq_right hk, mul_zero]

@[simp] theorem flow_zero (f : HaarCircleL2 L) : flow L 0 f = f := by
  apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
  intro n
  simp only [coe_fourierBasis, flow_coefficient, phase_zero, one_mul]

theorem flow_add (s t : ℝ) (f : HaarCircleL2 L) :
    flow L (s + t) f = flow L s (flow L t f) := by
  apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
  intro n
  simp only [coe_fourierBasis, flow_coefficient, phase_add, mul_assoc]

theorem flow_norm (t : ℝ) (f : HaarCircleL2 L) : ‖flow L t f‖ = ‖f‖ := by
  change ‖(coefficients L).symm (sequenceOperator t (coefficients L f))‖ = ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  change ‖sequenceLinear t (coefficients L f)‖ = ‖f‖
  rw [sequence_norm, LinearIsometryEquiv.norm_map]

theorem flow_stronglyContinuous (f : HaarCircleL2 L) :
    Continuous (fun t : ℝ => flow L t f) :=
  (coefficients L).symm.continuous.comp (sequence_stronglyContinuous (coefficients L f))

/-- The strong two-sided difference quotient at the identity parameter. -/
def HasGenerator (f g : HaarCircleL2 L) : Prop :=
  Tendsto (fun t : ℝ => (t⁻¹ : ℂ) • (flow L t f - f)) (𝓝[≠] 0) (𝓝 g)

theorem generator_on_domain (f : (AngularGenerator.operator L).domain) :
    HasGenerator L (f : HaarCircleL2 L) (Complex.I • AngularGenerator.operator L f) := by
  have hs := sequence_derivative (coefficients L (f : HaarCircleL2 L))
    (coefficients L (Complex.I • AngularGenerator.operator L f)) (by
      intro n
      simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, coefficients_apply,
        AngularGenerator.coefficients]
      ring)
  have ht := (coefficients L).symm.continuous.continuousAt.tendsto.comp hs
  simpa only [HasGenerator, Function.comp_def, map_smul, map_sub,
    ← coefficients_flow, LinearIsometryEquiv.symm_apply_apply] using ht

/-- A convergent strong quotient necessarily belongs to the original H1 domain. -/
theorem mem_domain_of_generator (f g : HaarCircleL2 L) (hg : HasGenerator L f g) :
    f ∈ (AngularGenerator.operator L).domain := by
  have hc (n : ℤ) : inner ℂ (fourierLp 2 n) g =
      Complex.I * (n : ℂ) * inner ℂ (fourierLp 2 n) f := by
    have ht := (innerSL ℂ (fourierLp (T := 2 * L) 2 n)).continuous.continuousAt.tendsto.comp hg
    have hp := (phase_slope_tendsto n).mul_const (inner ℂ (fourierLp 2 n) f)
    have ht' : Tendsto (fun t : ℝ => (t⁻¹ : ℂ) *
        ((phase t n - 1) * inner ℂ (fourierLp 2 n) f))
        (𝓝[≠] 0) (𝓝 (inner ℂ (fourierLp 2 n) g)) := by
      convert ht using 1
      · funext t
        change (t⁻¹ : ℂ) * ((phase t n - 1) * inner ℂ (fourierLp (T := 2 * L) 2 n) f) =
          inner ℂ (fourierLp (T := 2 * L) 2 n) ((t⁻¹ : ℂ) • (flow L t f - f))
        simp only [inner_smul_right, inner_sub_right, flow_coefficient]
        ring
      · rfl
    exact tendsto_nhds_unique ht' (by simpa only [mul_assoc] using hp)
  apply AngularGenerator.adjoint_domain_le L
  apply (EigenbasisClosure.adjoint_domain_iff (fourierBasis (T := 2 * L))
    (AngularGenerator.operator L) (fun n : ℤ => (n : ℝ))
    (AngularGenerator.basis_mem_domain L) (AngularGenerator.operator_basis L)
    (AngularGenerator.formalAdjoint L) f).mpr
  refine ⟨-Complex.I • g, fun n => ?_⟩
  simp only [coe_fourierBasis, inner_smul_right, hc, Complex.ofReal_intCast]
  calc
    -Complex.I * (Complex.I * (n : ℂ) * inner ℂ (fourierLp 2 n) f) =
        -(Complex.I * Complex.I) * ((n : ℂ) * inner ℂ (fourierLp 2 n) f) := by ring
    _ = (n : ℂ) * inner ℂ (fourierLp 2 n) f := by
      rw [Complex.I_mul_I]
      simp

theorem generator_iff (f g : HaarCircleL2 L) :
    HasGenerator L f g ↔ ∃ hf : f ∈ (AngularGenerator.operator L).domain,
      g = Complex.I • AngularGenerator.operator L ⟨f, hf⟩ := by
  constructor
  · intro hg
    have hf := mem_domain_of_generator L f g hg
    exact ⟨hf, tendsto_nhds_unique hg (generator_on_domain L ⟨f, hf⟩)⟩
  · rintro ⟨hf, rfl⟩
    exact generator_on_domain L ⟨f, hf⟩

theorem generator_domain_iff (f : HaarCircleL2 L) :
    (∃ g, HasGenerator L f g) ↔ f ∈ (AngularGenerator.operator L).domain := by
  constructor
  · rintro ⟨g, hg⟩
    exact mem_domain_of_generator L f g hg
  · intro hf
    exact ⟨_, generator_on_domain L ⟨f, hf⟩⟩

end GeneratedFoundations.Spectral.AngularFlow
