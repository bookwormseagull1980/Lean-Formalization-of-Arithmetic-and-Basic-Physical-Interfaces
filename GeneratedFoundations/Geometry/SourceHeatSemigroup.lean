module

public import GeneratedFoundations.Geometry.SourceCasimirClosure
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The heat semigroup of the original source Casimir

The complete matrix coefficients of the original probability-Haar space
define the heat multipliers in every degree and both matrix indices.
Square-summable domination gives strong continuity and the strong right
derivative. Conversely, existence of that derivative forces the weighted
square-summability condition of the already constructed source Casimir.
Thus the right generator is exactly its negative, on its full domain.

The exponent uses the actual round source energy without an additional
factor of one half. No identification with an interval operator is used.
Positivity preservation is a separate statement about the convolution law.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology lp LinearPMap ComplexConjugate NNReal
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceCasimirClosure

namespace GeneratedFoundations.Geometry.SourceHeatSemigroup

abbrev Sequence := ℓ²(Index, ℂ)

def decay (t : ℝ) (m : ℕ) : ℝ := Real.exp (-t * energy m)

theorem decay_pos (t : ℝ) (m : ℕ) : 0 < decay t m := Real.exp_pos _

theorem decay_le_one {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : decay t m ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (energy_nonneg m)

@[simp] theorem decay_zero (m : ℕ) : decay 0 m = 1 := by simp [decay]

@[simp] theorem decay_degree_zero (t : ℝ) : decay t 0 = 1 := by
  simp [decay, energy]

theorem decay_add (s t : ℝ) (m : ℕ) : decay (s + t) m = decay s m * decay t m := by
  change Real.exp (-(s + t) * energy m) = Real.exp (-s * energy m) * Real.exp (-t * energy m)
  rw [show -(s + t) * energy m = -s * energy m + -t * energy m by ring, Real.exp_add]

theorem decay_hasDerivAt (t : ℝ) (m : ℕ) :
    HasDerivAt (fun s : ℝ => decay s m) ((-energy m) * decay t m) t := by
  simpa only [decay, one_mul, neg_mul, mul_neg, mul_comm, Function.id_def, Pi.neg_apply] using
    (((hasDerivAt_id t).neg).mul_const (energy m)).exp

theorem decay_continuous (m : ℕ) : Continuous (fun t : ℝ => decay t m) :=
  continuous_iff_continuousAt.mpr fun t => (decay_hasDerivAt t m).continuousAt

theorem decay_sub_one_bound {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    ‖(decay t m : ℂ) - 1‖ ≤ t * energy m := by
  have hupper := decay_le_one ht m
  have hlower := Real.add_one_le_exp (-t * energy m)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hupper)]
  change -t * energy m + 1 ≤ decay t m at hlower
  linarith

def sequenceMap (t : ℝ≥0) (v : Sequence) : Sequence :=
  ⟨fun a => (decay t a.1 : ℂ) * v a, (lp.memℓp v).mono' (by
    intro a
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos t a.1)]
    exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one t.property a.1))⟩

@[simp] theorem sequenceMap_apply (t : ℝ≥0) (v : Sequence) (a : Index) :
    sequenceMap t v a = (decay t a.1 : ℂ) * v a := rfl

def sequenceLinear (t : ℝ≥0) : Sequence →ₗ[ℂ] Sequence where
  toFun := sequenceMap t
  map_add' v w := by
    apply lp.ext
    funext a
    change (decay t a.1 : ℂ) * (v a + w a) = _
    simp only [mul_add, sequenceMap_apply, lp.coeFn_add, Pi.add_apply]
  map_smul' c v := by
    apply lp.ext
    funext a
    change (decay t a.1 : ℂ) * (c * v a) = c * ((decay t a.1 : ℂ) * v a)
    ring

theorem sequence_norm_le (t : ℝ≥0) (v : Sequence) : ‖sequenceLinear t v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num)
  intro a
  change ‖(decay t a.1 : ℂ) * v a‖ ≤ ‖v a‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos t a.1)]
  exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one t.property a.1)

def sequenceOperator (t : ℝ≥0) : Sequence →L[ℂ] Sequence :=
  (sequenceLinear t).mkContinuous 1 (by
    intro v
    simpa only [one_mul] using sequence_norm_le t v)

/-- Conjugation uses the already proved complete basis in the original source space. -/
def heat (t : ℝ≥0) : SourceL2 →L[ℂ] SourceL2 :=
  coefficients.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sequenceOperator t).comp coefficients.toContinuousLinearEquiv.toContinuousLinearMap)

theorem coefficients_heat (t : ℝ≥0) (f : SourceL2) :
    coefficients (heat t f) = sequenceOperator t (coefficients f) := by
  simp [heat]

theorem heat_coefficient (t : ℝ≥0) (f : SourceL2) (a : Index) :
    inner ℂ (basisVector a) (heat t f) =
      (decay t a.1 : ℂ) * inner ℂ (basisVector a) f := by
  have h := congrArg (fun v : Sequence => v a) (coefficients_heat t f)
  change coefficients (heat t f) a = (decay t a.1 : ℂ) * coefficients f a at h
  simpa only [coefficients_apply] using h

@[simp] theorem heat_zero (f : SourceL2) : heat 0 f = f := by
  apply eq_of_coefficients_eq
  intro a
  simp only [heat_coefficient, NNReal.coe_zero, decay_zero, Complex.ofReal_one, one_mul]

theorem heat_add (s t : ℝ≥0) (f : SourceL2) : heat (s + t) f = heat s (heat t f) := by
  apply eq_of_coefficients_eq
  intro a
  simp only [heat_coefficient, NNReal.coe_add, decay_add, Complex.ofReal_mul, mul_assoc]

theorem heat_norm_le (t : ℝ≥0) (f : SourceL2) : ‖heat t f‖ ≤ ‖f‖ := by
  rw [← coefficients.norm_map (heat t f), coefficients_heat, ← coefficients.norm_map f]
  exact sequence_norm_le t _

theorem heat_opNorm_le (t : ℝ≥0) : ‖heat t‖ ≤ 1 :=
  (heat t).opNorm_le_bound zero_le_one (fun f => by
    simpa only [one_mul] using heat_norm_le t f)

theorem heat_basis (t : ℝ≥0) (a : Index) :
    heat t (basisVector a) = (decay t a.1 : ℂ) • basisVector a := by
  apply eq_of_coefficients_eq
  intro b
  simp only [heat_coefficient, inner_smul_right,
    orthonormal_iff_ite.mp basisVector_orthonormal]
  by_cases h : b = a
  · subst b
    simp
  · simp [h]

theorem heat_fixes_zero_degree_basis (t : ℝ≥0) (i j : Fin 1) :
    heat t (basisVector ⟨0, i, j⟩) = basisVector ⟨0, i, j⟩ := by
  simp [heat_basis]

theorem heat_selfAdjoint (t : ℝ≥0) : IsSelfAdjoint (heat t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (heat t f) g = inner ℂ f (heat t g)
  rw [← coefficients.inner_map_map (heat t f) g,
    ← coefficients.inner_map_map f (heat t g), coefficients_heat, coefficients_heat,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  change inner ℂ ((decay t a.1 : ℂ) * coefficients f a) (coefficients g a) =
    inner ℂ (coefficients f a) ((decay t a.1 : ℂ) * coefficients g a)
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

private theorem sequence_norm_sq (v : Sequence) : ‖v‖ ^ 2 = ∑' a, ‖v a‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v

private theorem sequence_summable (v : Sequence) : Summable (fun a => ‖v a‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)

private theorem sequence_tendsto_zero {α : Type*} {l : Filter α} (v : α → Sequence)
    (bound : Index → ℝ) (hsum : Summable bound)
    (hpoint : ∀ a, Tendsto (fun x => v x a) l (𝓝 0))
    (hbound : ∀ᶠ x in l, ∀ a, ‖v x a‖ ^ 2 ≤ bound a) : Tendsto v l (𝓝 0) := by
  have hsq : Tendsto (fun x => ‖v x‖ ^ 2) l (𝓝 0) := by
    simp_rw [sequence_norm_sq]
    have h := tendsto_tsum_of_dominated_convergence
      (f := fun x a => ‖v x a‖ ^ 2) (g := fun _ => (0 : ℝ)) hsum
      (fun a => by simpa using (hpoint a).norm.pow 2)
      (hbound.mono (fun x hx a => by simpa only [Real.norm_eq_abs, abs_sq] using hx a))
    simpa only [tsum_zero] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

theorem sequence_stronglyContinuous (v : Sequence) :
    Continuous (fun t : ℝ≥0 => sequenceOperator t v) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero _ (fun a => 4 * ‖v a‖ ^ 2)
    ((sequence_summable v).mul_left 4)
  · intro a
    have hc : Continuous (fun t : ℝ≥0 => (decay t a.1 : ℂ)) :=
      Complex.continuous_ofReal.comp ((decay_continuous a.1).comp continuous_subtype_val)
    have h := (hc.continuousAt (x := s)).mul_const (v a)
    change Tendsto (fun t : ℝ≥0 => (decay t a.1 : ℂ) * v a - (decay s a.1 : ℂ) * v a)
      (𝓝 s) (𝓝 0)
    simpa only [sub_self] using h.tendsto.sub_const ((decay s a.1 : ℂ) * v a)
  · apply Eventually.of_forall
    intro t a
    have hpart (r : ℝ≥0) : ‖(decay r a.1 : ℂ) * v a‖ ≤ ‖v a‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos r a.1)]
      exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one r.property a.1)
    have h : ‖(decay t a.1 : ℂ) * v a - (decay s a.1 : ℂ) * v a‖ ≤ 2 * ‖v a‖ :=
      (norm_sub_le _ _).trans (by nlinarith [hpart t, hpart s])
    change ‖(decay t a.1 : ℂ) * v a - (decay s a.1 : ℂ) * v a‖ ^ 2 ≤ _
    nlinarith [norm_nonneg ((decay t a.1 : ℂ) * v a - (decay s a.1 : ℂ) * v a),
      norm_nonneg (v a)]

theorem heat_stronglyContinuous (f : SourceL2) : Continuous (fun t : ℝ≥0 => heat t f) :=
  coefficients.symm.continuous.comp (sequence_stronglyContinuous (coefficients f))

private theorem coe_tendsto_right :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · exact (continuous_subtype_val.continuousAt (x := (0 : ℝ≥0))).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht

private theorem decay_slope_tendsto (m : ℕ) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) * ((decay t m : ℂ) - 1))
      (𝓝[>] 0) (𝓝 ((-energy m : ℝ) : ℂ)) := by
  have h := ((decay_hasDerivAt 0 m).ofReal_comp).tendsto_slope_zero_right.comp
    coe_tendsto_right
  simpa only [Function.comp_def, zero_add, decay_zero, mul_one, Complex.ofReal_one,
    Complex.real_smul, Complex.ofReal_inv] using h

private theorem sequence_rightDerivative (v w : Sequence)
    (hw : ∀ a, w a = ((-energy a.1 : ℝ) : ℂ) * v a) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) • (sequenceOperator t v - v))
      (𝓝[>] 0) (𝓝 w) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero _ (fun a => 4 * ‖w a‖ ^ 2)
    ((sequence_summable w).mul_left 4)
  · intro a
    have h := ((decay_slope_tendsto a.1).mul_const (v a)).sub_const (w a)
    convert h using 1
    · funext t
      change ((t : ℝ)⁻¹ : ℂ) * ((decay t a.1 : ℂ) * v a - v a) - w a = _
      ring
    · rw [hw, sub_self]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    intro a
    have ht' : (0 : ℝ) < t := ht
    have hn : ‖w a‖ = energy a.1 * ‖v a‖ := by
      rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (energy_nonneg a.1)]
    have hq : ‖((t : ℝ)⁻¹ : ℂ) * ((decay t a.1 : ℂ) * v a - v a)‖ ≤ ‖w a‖ := by
      rw [show (decay t a.1 : ℂ) * v a - v a = ((decay t a.1 : ℂ) - 1) * v a by ring,
        norm_mul, norm_mul]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht']
      calc
        _ ≤ (t : ℝ)⁻¹ * (((t : ℝ) * energy a.1) * ‖v a‖) := by
          gcongr
          exact decay_sub_one_bound ht'.le a.1
        _ = energy a.1 * ‖v a‖ := by field_simp [ht'.ne']
        _ = ‖w a‖ := hn.symm
    have hdiff := norm_sub_le
      (((t : ℝ)⁻¹ : ℂ) * ((decay t a.1 : ℂ) * v a - v a)) (w a)
    change ‖((t : ℝ)⁻¹ : ℂ) * ((decay t a.1 : ℂ) * v a - v a) - w a‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (((t : ℝ)⁻¹ : ℂ) * ((decay t a.1 : ℂ) * v a - v a) - w a),
      norm_nonneg (w a)]

/-- The strong right derivative in the nonnegative compositional parameter. -/
def HasRightGenerator (f g : SourceL2) : Prop :=
  Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) • (heat t f - f)) (𝓝[>] 0) (𝓝 g)

theorem rightGenerator_on_domain (f : operator.domain) :
    HasRightGenerator (f : SourceL2) (-(operator f)) := by
  have h := sequence_rightDerivative (coefficients (f : SourceL2))
    (coefficients (-(operator f))) (by
      intro a
      simp only [coefficients_apply, inner_neg_right, operator_coefficients,
        Complex.ofReal_neg, neg_mul])
  have hh := coefficients.symm.continuous.continuousAt.tendsto.comp h
  simpa only [HasRightGenerator, Function.comp_def, map_smul, map_sub,
    ← coefficients_heat, LinearIsometryEquiv.symm_apply_apply] using hh

/-- A strong right derivative supplies exactly the weighted square-summable
coefficient sequence required by the original closed source operator. -/
theorem mem_domain_of_rightGenerator (f g : SourceL2) (hg : HasRightGenerator f g) :
    f ∈ operator.domain := by
  have hc (a : Index) : inner ℂ (basisVector a) g =
      ((-energy a.1 : ℝ) : ℂ) * inner ℂ (basisVector a) f := by
    have h : Tendsto (fun t : ℝ≥0 => inner ℂ (basisVector a)
        (((t : ℝ)⁻¹ : ℂ) • (heat t f - f))) (𝓝[>] 0)
        (𝓝 (inner ℂ (basisVector a) g)) :=
      (innerSL ℂ (basisVector a)).continuous.continuousAt.tendsto.comp hg
    have hp := (decay_slope_tendsto a.1).mul_const (inner ℂ (basisVector a) f)
    have h' : Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) *
        (((decay t a.1 : ℂ) - 1) * inner ℂ (basisVector a) f))
        (𝓝[>] 0) (𝓝 (inner ℂ (basisVector a) g)) := by
      convert h using 1
      funext t
      simp only [inner_smul_right, inner_sub_right, heat_coefficient]
      ring
    exact tendsto_nhds_unique h' (by simpa only [mul_assoc] using hp)
  have hn (a : Index) : ‖coefficients g a‖ ^ 2 =
      energy a.1 ^ 2 * ‖inner ℂ (basisVector a) f‖ ^ 2 := by
    rw [coefficients_apply, hc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg (energy_nonneg a.1), mul_pow]
  apply (operator_domain_iff f).mpr
  simpa only [hn] using sequence_summable (coefficients g)

/-- Both the full domain and the sign of the generator are identified. -/
theorem rightGenerator_iff (f g : SourceL2) :
    HasRightGenerator f g ↔ ∃ hf : f ∈ operator.domain, g = -(operator ⟨f, hf⟩) := by
  constructor
  · intro hg
    have hf := mem_domain_of_rightGenerator f g hg
    exact ⟨hf, tendsto_nhds_unique hg (rightGenerator_on_domain ⟨f, hf⟩)⟩
  · rintro ⟨hf, rfl⟩
    exact rightGenerator_on_domain ⟨f, hf⟩

theorem rightGenerator_domain_iff (f : SourceL2) :
    (∃ g, HasRightGenerator f g) ↔ f ∈ operator.domain := by
  constructor
  · rintro ⟨g, hg⟩
    exact mem_domain_of_rightGenerator f g hg
  · intro hf
    exact ⟨_, rightGenerator_on_domain ⟨f, hf⟩⟩

end GeneratedFoundations.Geometry.SourceHeatSemigroup
