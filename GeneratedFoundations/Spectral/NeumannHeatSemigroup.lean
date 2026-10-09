module

public import GeneratedFoundations.Spectral.NeumannSpectralDomain
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The heat semigroup of the original Neumann operator

The complete cosine basis defines contractive spectral multipliers on the
original interval Hilbert space. Square-summable domination proves strong
continuity and identifies the full right-generator domain with the original
Sobolev Neumann domain. The parameter is the compositional change parameter.
Positivity preservation of functions is a separate kernel statement.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology lp LinearPMap ComplexConjugate NNReal
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Spectral.NeumannHeatSemigroup

abbrev Sequence := ℓ²(ℕ, ℂ)

variable (L : ℝ)

def decay (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t * neumannEigenvalue L n / 2)

theorem decay_pos (t : ℝ) (n : ℕ) : 0 < decay L t n := Real.exp_pos _

theorem decay_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : decay L t n ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (neumannEigenvalue_nonneg L n))
    (by norm_num)

@[simp] theorem decay_zero (n : ℕ) : decay L 0 n = 1 := by simp [decay]

@[simp] theorem decay_mode_zero (t : ℝ) : decay L t 0 = 1 := by
  simp [decay, neumannEigenvalue_zero]

theorem decay_add (s t : ℝ) (n : ℕ) :
    decay L (s + t) n = decay L s n * decay L t n := by
  rw [decay, show -(s + t) * neumannEigenvalue L n / 2 =
    -s * neumannEigenvalue L n / 2 + -t * neumannEigenvalue L n / 2 by ring,
    Real.exp_add]
  rfl

theorem decay_hasDerivAt (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s : ℝ => decay L s n)
      ((-neumannEigenvalue L n / 2) * decay L t n) t := by
  simpa only [decay, one_mul, neg_mul, mul_neg, mul_comm, Function.id_def, Pi.neg_apply] using
    ((((hasDerivAt_id t).neg).mul_const (neumannEigenvalue L n)).div_const 2).exp

theorem decay_continuous (n : ℕ) : Continuous (fun t : ℝ => decay L t n) :=
  continuous_iff_continuousAt.mpr fun t => (decay_hasDerivAt L t n).continuousAt

theorem decay_sub_one_bound {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ‖(decay L t n : ℂ) - 1‖ ≤ t * neumannEigenvalue L n / 2 := by
  have hupper := decay_le_one L ht n
  have hlower := Real.add_one_le_exp (-t * neumannEigenvalue L n / 2)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hupper)]
  change -t * neumannEigenvalue L n / 2 + 1 ≤ decay L t n at hlower
  linarith

def sequenceMap (t : ℝ≥0) (v : Sequence) : Sequence :=
  ⟨fun n => (decay L t n : ℂ) * v n, (lp.memℓp v).mono' (by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos L t n)]
    exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one L t.property n))⟩

@[simp] theorem sequenceMap_apply (t : ℝ≥0) (v : Sequence) (n : ℕ) :
    sequenceMap L t v n = (decay L t n : ℂ) * v n := rfl

def sequenceLinear (t : ℝ≥0) : Sequence →ₗ[ℂ] Sequence where
  toFun := sequenceMap L t
  map_add' v w := by
    apply lp.ext
    funext n
    change (decay L t n : ℂ) * (v n + w n) = _
    simp only [mul_add, sequenceMap_apply, lp.coeFn_add, Pi.add_apply]
  map_smul' c v := by
    apply lp.ext
    funext n
    change (decay L t n : ℂ) * (c * v n) = c * ((decay L t n : ℂ) * v n)
    ring

theorem sequence_norm_le (t : ℝ≥0) (v : Sequence) : ‖sequenceLinear L t v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  change ‖(decay L t n : ℂ) * v n‖ ≤ ‖v n‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos L t n)]
  exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one L t.property n)

def sequenceOperator (t : ℝ≥0) : Sequence →L[ℂ] Sequence :=
  (sequenceLinear L t).mkContinuous 1 (by
    intro v
    simpa only [one_mul] using sequence_norm_le L t v)

variable [hL : Fact (0 < L)]

def coefficients : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] Sequence := (neumannCosineBasis L).repr

theorem coefficients_apply (f : ComplexIntervalL2 0 L) (n : ℕ) :
    coefficients L f n = inner ℂ (neumannCosineMode L n) f := by
  simpa only [coefficients, coe_neumannCosineBasis] using
    (neumannCosineBasis L).repr_apply_apply f n

def heat (t : ℝ≥0) : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L :=
  (coefficients L).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sequenceOperator L t).comp (coefficients L).toContinuousLinearEquiv.toContinuousLinearMap)

theorem coefficients_heat (t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    coefficients L (heat L t f) = sequenceOperator L t (coefficients L f) := by
  simp [heat]

theorem heat_coefficient (t : ℝ≥0) (f : ComplexIntervalL2 0 L) (n : ℕ) :
    inner ℂ (neumannCosineMode L n) (heat L t f) =
      (decay L t n : ℂ) * inner ℂ (neumannCosineMode L n) f := by
  simp only [← coefficients_apply, coefficients_heat]
  rfl

@[simp] theorem heat_zero (f : ComplexIntervalL2 0 L) : heat L 0 f = f := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
  intro n
  simp only [coe_neumannCosineBasis, heat_coefficient, NNReal.coe_zero, decay_zero,
    Complex.ofReal_one, one_mul]

theorem heat_add (s t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    heat L (s + t) f = heat L s (heat L t f) := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
  intro n
  simp only [coe_neumannCosineBasis, heat_coefficient, NNReal.coe_add, decay_add,
    Complex.ofReal_mul, mul_assoc]

theorem heat_norm_le (t : ℝ≥0) (f : ComplexIntervalL2 0 L) : ‖heat L t f‖ ≤ ‖f‖ := by
  rw [← (coefficients L).norm_map (heat L t f), coefficients_heat,
    ← (coefficients L).norm_map f]
  exact sequence_norm_le L t _

theorem heat_cosine (t : ℝ≥0) (n : ℕ) :
    heat L t (neumannCosineMode L n) = (decay L t n : ℂ) • neumannCosineMode L n := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
  intro m
  simp only [coe_neumannCosineBasis, heat_coefficient, inner_smul_right,
    orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L) m n]
  by_cases h : m = n
  · subst m; simp
  · simp [h]

theorem heat_fixes_constant_mode (t : ℝ≥0) :
    heat L t (neumannCosineMode L 0) = neumannCosineMode L 0 := by
  simp [heat_cosine, decay_mode_zero]

theorem heat_selfAdjoint (t : ℝ≥0) : IsSelfAdjoint (heat L t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (heat L t f) g = inner ℂ f (heat L t g)
  rw [← (coefficients L).inner_map_map (heat L t f) g,
    ← (coefficients L).inner_map_map f (heat L t g), coefficients_heat, coefficients_heat,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ ((decay L t n : ℂ) * coefficients L f n) (coefficients L g n) =
    inner ℂ (coefficients L f n) ((decay L t n : ℂ) * coefficients L g n)
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

private theorem sequence_norm_sq (v : Sequence) : ‖v‖ ^ 2 = ∑' n, ‖v n‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v

private theorem sequence_summable (v : Sequence) : Summable (fun n => ‖v n‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)

private theorem sequence_tendsto_zero {α : Type*} {l : Filter α} (v : α → Sequence)
    (bound : ℕ → ℝ) (hsum : Summable bound)
    (hpoint : ∀ n, Tendsto (fun a => v a n) l (𝓝 0))
    (hbound : ∀ᶠ a in l, ∀ n, ‖v a n‖ ^ 2 ≤ bound n) : Tendsto v l (𝓝 0) := by
  have hsq : Tendsto (fun a => ‖v a‖ ^ 2) l (𝓝 0) := by
    simp_rw [sequence_norm_sq]
    have h := tendsto_tsum_of_dominated_convergence
      (f := fun a n => ‖v a n‖ ^ 2) (g := fun _ => (0 : ℝ)) hsum
      (fun n => by simpa using (hpoint n).norm.pow 2)
      (hbound.mono (fun a ha n => by simpa only [Real.norm_eq_abs, abs_sq] using ha n))
    simpa only [tsum_zero] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

omit hL in
theorem sequence_stronglyContinuous (v : Sequence) :
    Continuous (fun t : ℝ≥0 => sequenceOperator L t v) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero _ (fun n => 4 * ‖v n‖ ^ 2)
    ((sequence_summable v).mul_left 4)
  · intro n
    have hc : Continuous (fun t : ℝ≥0 => (decay L t n : ℂ)) :=
      Complex.continuous_ofReal.comp ((decay_continuous L n).comp continuous_subtype_val)
    have h := (hc.continuousAt (x := s)).mul_const (v n)
    change Tendsto (fun t : ℝ≥0 => (decay L t n : ℂ) * v n - (decay L s n : ℂ) * v n)
      (𝓝 s) (𝓝 0)
    simpa only [sub_self] using h.tendsto.sub_const
      ((decay L s n : ℂ) * v n)
  · apply Eventually.of_forall
    intro t n
    have hpart (r : ℝ≥0) : ‖(decay L r n : ℂ) * v n‖ ≤ ‖v n‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos L r n)]
      exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one L r.property n)
    have h : ‖(decay L t n : ℂ) * v n - (decay L s n : ℂ) * v n‖ ≤ 2 * ‖v n‖ :=
      (norm_sub_le _ _).trans (by nlinarith [hpart t, hpart s])
    change ‖(decay L t n : ℂ) * v n - (decay L s n : ℂ) * v n‖ ^ 2 ≤ _
    nlinarith [norm_nonneg ((decay L t n : ℂ) * v n - (decay L s n : ℂ) * v n),
      norm_nonneg (v n)]

theorem heat_stronglyContinuous (f : ComplexIntervalL2 0 L) :
    Continuous (fun t : ℝ≥0 => heat L t f) :=
  (coefficients L).symm.continuous.comp (sequence_stronglyContinuous L (coefficients L f))

private theorem coe_tendsto_right :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · exact (continuous_subtype_val.continuousAt (x := (0 : ℝ≥0))).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht

omit hL in
private theorem decay_slope_tendsto (n : ℕ) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) * ((decay L t n : ℂ) - 1))
      (𝓝[>] 0) (𝓝 ((-neumannEigenvalue L n / 2 : ℝ) : ℂ)) := by
  have h := ((decay_hasDerivAt L 0 n).ofReal_comp).tendsto_slope_zero_right.comp
    coe_tendsto_right
  simpa only [Function.comp_def, zero_add, decay_zero, mul_one, Complex.ofReal_one,
    Complex.real_smul, Complex.ofReal_inv] using h

omit hL in
private theorem sequence_rightDerivative (v w : Sequence)
    (hw : ∀ n, w n = ((-neumannEigenvalue L n / 2 : ℝ) : ℂ) * v n) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) • (sequenceOperator L t v - v))
      (𝓝[>] 0) (𝓝 w) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero _ (fun n => 4 * ‖w n‖ ^ 2)
    ((sequence_summable w).mul_left 4)
  · intro n
    have h := ((decay_slope_tendsto L n).mul_const (v n)).sub_const (w n)
    convert h using 1
    · funext t
      change ((t : ℝ)⁻¹ : ℂ) * ((decay L t n : ℂ) * v n - v n) - w n = _
      ring
    · rw [hw, sub_self]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    intro n
    have ht' : (0 : ℝ) < t := ht
    have hnonneg := neumannEigenvalue_nonneg L n
    have hn : ‖w n‖ = (neumannEigenvalue L n / 2) * ‖v n‖ := by
      rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnonneg) (by norm_num))]
      congr 1
      ring
    have hq : ‖((t : ℝ)⁻¹ : ℂ) * ((decay L t n : ℂ) * v n - v n)‖ ≤ ‖w n‖ := by
      rw [show (decay L t n : ℂ) * v n - v n = ((decay L t n : ℂ) - 1) * v n by ring,
        norm_mul, norm_mul]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht']
      calc
        _ ≤ (t : ℝ)⁻¹ * (((t : ℝ) * neumannEigenvalue L n / 2) * ‖v n‖) := by
          gcongr
          exact decay_sub_one_bound L ht'.le n
        _ = (neumannEigenvalue L n / 2) * ‖v n‖ := by field_simp [ht'.ne']
        _ = ‖w n‖ := hn.symm
    have hdiff := norm_sub_le
      (((t : ℝ)⁻¹ : ℂ) * ((decay L t n : ℂ) * v n - v n)) (w n)
    change ‖((t : ℝ)⁻¹ : ℂ) * ((decay L t n : ℂ) * v n - v n) - w n‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (((t : ℝ)⁻¹ : ℂ) * ((decay L t n : ℂ) * v n - v n) - w n),
      norm_nonneg (w n)]

/-- A strong right derivative with respect to the nonnegative change parameter. -/
def HasRightGenerator (f g : ComplexIntervalL2 0 L) : Prop :=
  Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) • (heat L t f - f)) (𝓝[>] 0) (𝓝 g)

theorem rightGenerator_on_domain (f : (complexNeumannOperator hL.out).domain) :
    HasRightGenerator L (f : ComplexIntervalL2 0 L)
      ((-1 / 2 : ℂ) • complexNeumannOperator hL.out f) := by
  have h := sequence_rightDerivative L (coefficients L (f : ComplexIntervalL2 0 L))
    (coefficients L ((-1 / 2 : ℂ) • complexNeumannOperator hL.out f)) (by
      intro n
      simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, coefficients_apply,
        complexNeumannOperator_coefficients, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_ofNat]
      ring)
  have hh := (coefficients L).symm.continuous.continuousAt.tendsto.comp h
  simpa only [HasRightGenerator, Function.comp_def, map_smul, map_sub,
    ← coefficients_heat, LinearIsometryEquiv.symm_apply_apply] using hh

/-- Every convergent right difference quotient starts in the actual Neumann domain. -/
theorem mem_domain_of_rightGenerator (f g : ComplexIntervalL2 0 L)
    (hg : HasRightGenerator L f g) : f ∈ (complexNeumannOperator hL.out).domain := by
  have hc (n : ℕ) : inner ℂ (neumannCosineMode L n) g =
      ((-neumannEigenvalue L n / 2 : ℝ) : ℂ) * inner ℂ (neumannCosineMode L n) f := by
    have h : Tendsto (fun t : ℝ≥0 => inner ℂ (neumannCosineMode L n)
        (((t : ℝ)⁻¹ : ℂ) • (heat L t f - f))) (𝓝[>] 0)
        (𝓝 (inner ℂ (neumannCosineMode L n) g)) :=
      (innerSL ℂ (neumannCosineMode L n)).continuous.continuousAt.tendsto.comp hg
    have hp := (decay_slope_tendsto L n).mul_const (inner ℂ (neumannCosineMode L n) f)
    have h' : Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) *
        (((decay L t n : ℂ) - 1) * inner ℂ (neumannCosineMode L n) f))
        (𝓝[>] 0) (𝓝 (inner ℂ (neumannCosineMode L n) g)) := by
      convert h using 1
      funext t
      simp only [inner_smul_right,
        inner_sub_right, heat_coefficient]
      ring
    exact tendsto_nhds_unique h' (by simpa only [mul_assoc] using hp)
  apply complexNeumannAdjoint_domain_le L
  apply (EigenbasisClosure.adjoint_domain_iff (neumannCosineBasis L)
    (complexNeumannOperator hL.out) (neumannEigenvalue L)
    (neumannCosineBasis_mem_domain L) (complexNeumannOperator_cosineBasis L)
    (complexNeumann_formalAdjoint hL.out) f).mpr
  refine ⟨(-2 : ℂ) • g, fun n => ?_⟩
  simp only [coe_neumannCosineBasis, inner_smul_right, hc,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

theorem rightGenerator_iff (f g : ComplexIntervalL2 0 L) :
    HasRightGenerator L f g ↔
      ∃ hf : f ∈ (complexNeumannOperator hL.out).domain,
        g = (-1 / 2 : ℂ) • complexNeumannOperator hL.out ⟨f, hf⟩ := by
  constructor
  · intro hg
    have hf := mem_domain_of_rightGenerator L f g hg
    exact ⟨hf, tendsto_nhds_unique hg (rightGenerator_on_domain L ⟨f, hf⟩)⟩
  · rintro ⟨hf, rfl⟩
    exact rightGenerator_on_domain L ⟨f, hf⟩

theorem rightGenerator_domain_iff (f : ComplexIntervalL2 0 L) :
    (∃ g, HasRightGenerator L f g) ↔ f ∈ (complexNeumannOperator hL.out).domain := by
  constructor
  · rintro ⟨g, hg⟩
    exact mem_domain_of_rightGenerator L f g hg
  · intro hf
    exact ⟨_, rightGenerator_on_domain L ⟨f, hf⟩⟩

theorem heat_mem_domain (t : ℝ≥0) (f : (complexNeumannOperator hL.out).domain) :
    heat L t (f : ComplexIntervalL2 0 L) ∈ (complexNeumannOperator hL.out).domain := by
  apply complexNeumannAdjoint_domain_le L
  apply (EigenbasisClosure.adjoint_domain_iff (neumannCosineBasis L)
    (complexNeumannOperator hL.out) (neumannEigenvalue L)
    (neumannCosineBasis_mem_domain L) (complexNeumannOperator_cosineBasis L)
    (complexNeumann_formalAdjoint hL.out) (heat L t (f : ComplexIntervalL2 0 L))).mpr
  refine ⟨heat L t (complexNeumannOperator hL.out f), fun n => ?_⟩
  simp only [coe_neumannCosineBasis, heat_coefficient, complexNeumannOperator_coefficients]
  ring

theorem operator_heat (t : ℝ≥0) (f : (complexNeumannOperator hL.out).domain) :
    complexNeumannOperator hL.out ⟨heat L t (f : ComplexIntervalL2 0 L), heat_mem_domain L t f⟩ =
      heat L t (complexNeumannOperator hL.out f) := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
  intro n
  simp only [coe_neumannCosineBasis, heat_coefficient, complexNeumannOperator_coefficients]
  ring

end GeneratedFoundations.Spectral.NeumannHeatSemigroup
