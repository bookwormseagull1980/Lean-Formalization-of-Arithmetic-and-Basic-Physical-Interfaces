module

public import GeneratedFoundations.Arithmetic.HistoryHaarHeatFlow
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Tactic.GCongr

/-!
# Exact generator of the complete arithmetic Haar heat flow

The strong derivative is taken from positive compositional times. Its
existence is equivalent to membership in the full differential Hessian
domain, not merely the finite core. The proof uses square-summable
domination of the actual eigen-coefficients in both directions.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology lp NNReal LinearPMap

namespace GeneratedFoundations.Arithmetic.HistoryHaarHeatGenerator

open HistoryHaarClosedHessian HistoryHaarHeatFlow

private theorem eigenvalue_nonneg (N : ℕ) (a : BasisIndex N) :
    0 ≤ eigenvalue N a := (by norm_num : (0 : ℝ) ≤ 4).trans (eigenvalue_ge_four N a)

theorem operator_coefficients (N : ℕ) (x : (operator N).domain) (a : BasisIndex N) :
    inner ℂ (basis N a) (operator N x) =
      (eigenvalue N a : ℂ) * inner ℂ (basis N a) (x : Fields N) :=
  Operations.FiniteEigenbasisCore.closure_coefficients (basis N) (eigenvalue N) x a

private theorem sequence_summable (N : ℕ) (v : Sequence N) :
    Summable (fun a => ‖v a‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)

private theorem sequence_norm_sq (N : ℕ) (v : Sequence N) :
    ‖v‖ ^ 2 = ∑' a, ‖v a‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v

private theorem sequence_tendsto_zero (N : ℕ) {α : Type*} {l : Filter α}
    (v : α → Sequence N) (bound : BasisIndex N → ℝ) (hsum : Summable bound)
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

theorem decay_hasDerivAt (N : ℕ) (t : ℝ) (a : BasisIndex N) :
    HasDerivAt (fun s : ℝ => decay N s a) ((-eigenvalue N a) * decay N t a) t := by
  simpa only [decay, one_mul, neg_mul, mul_neg, mul_comm, Function.id_def, Pi.neg_apply] using
    (((hasDerivAt_id t).neg).mul_const (eigenvalue N a)).exp

theorem decay_sub_one_bound (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (a : BasisIndex N) :
    ‖(decay N t a : ℂ) - 1‖ ≤ t * eigenvalue N a := by
  have hupper := decay_le_one N ht a
  have hlower := Real.add_one_le_exp (-t * eigenvalue N a)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hupper)]
  change -t * eigenvalue N a + 1 ≤ decay N t a at hlower
  linarith

private theorem coe_tendsto_right :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · exact (continuous_subtype_val.continuousAt (x := (0 : ℝ≥0))).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht

private theorem decay_slope_tendsto (N : ℕ) (a : BasisIndex N) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) * ((decay N t a : ℂ) - 1))
      (𝓝[>] 0) (𝓝 ((-eigenvalue N a : ℝ) : ℂ)) := by
  have h := ((decay_hasDerivAt N 0 a).ofReal_comp).tendsto_slope_zero_right.comp
    coe_tendsto_right
  simpa only [Function.comp_def, zero_add, decay_zero, mul_one, Complex.ofReal_one,
    Complex.real_smul, Complex.ofReal_inv] using h

private theorem sequence_rightDerivative (N : ℕ) (v w : Sequence N)
    (hw : ∀ a, w a = ((-eigenvalue N a : ℝ) : ℂ) * v a) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) • (sequenceOperator N t v - v))
      (𝓝[>] 0) (𝓝 w) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero N _ (fun a => 4 * ‖w a‖ ^ 2)
    ((sequence_summable N w).mul_left 4)
  · intro a
    have h := ((decay_slope_tendsto N a).mul_const (v a)).sub_const (w a)
    convert h using 1
    · funext t
      change ((t : ℝ)⁻¹ : ℂ) * ((decay N t a : ℂ) * v a - v a) - w a = _
      ring
    · rw [hw, sub_self]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    intro a
    have ht' : (0 : ℝ) < t := ht
    have hn : ‖w a‖ = eigenvalue N a * ‖v a‖ := by
      rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (eigenvalue_nonneg N a)]
    have hq : ‖((t : ℝ)⁻¹ : ℂ) * ((decay N t a : ℂ) * v a - v a)‖ ≤ ‖w a‖ := by
      rw [show (decay N t a : ℂ) * v a - v a = ((decay N t a : ℂ) - 1) * v a by ring,
        norm_mul, norm_mul]
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht']
      calc
        _ ≤ (t : ℝ)⁻¹ * (((t : ℝ) * eigenvalue N a) * ‖v a‖) := by
          gcongr
          exact decay_sub_one_bound N ht'.le a
        _ = eigenvalue N a * ‖v a‖ := by field_simp [ht'.ne']
        _ = ‖w a‖ := hn.symm
    have hdiff := norm_sub_le
      (((t : ℝ)⁻¹ : ℂ) * ((decay N t a : ℂ) * v a - v a)) (w a)
    change ‖((t : ℝ)⁻¹ : ℂ) * ((decay N t a : ℂ) * v a - v a) - w a‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (((t : ℝ)⁻¹ : ℂ) * ((decay N t a : ℂ) * v a - v a) - w a),
      norm_nonneg (w a)]

def HasRightGenerator (N : ℕ) (x y : Fields N) : Prop :=
  Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) • (heat N t x - x)) (𝓝[>] 0) (𝓝 y)

theorem rightGenerator_on_domain (N : ℕ) (x : (operator N).domain) :
    HasRightGenerator N (x : Fields N) (-(operator N x)) := by
  have h := sequence_rightDerivative N ((basis N).repr (x : Fields N))
    ((basis N).repr (-(operator N x))) (by
      intro a
      simp only [HilbertBasis.repr_apply_apply, inner_neg_right, operator_coefficients,
        Complex.ofReal_neg, neg_mul])
  have hh := (basis N).repr.symm.continuous.continuousAt.tendsto.comp h
  simpa only [HasRightGenerator, Function.comp_def, map_smul, map_sub,
    ← coefficients_heat, LinearIsometryEquiv.symm_apply_apply] using hh

theorem mem_domain_of_rightGenerator (N : ℕ) (x y : Fields N)
    (hy : HasRightGenerator N x y) : x ∈ (operator N).domain := by
  have hc (a : BasisIndex N) : inner ℂ (basis N a) y =
      ((-eigenvalue N a : ℝ) : ℂ) * inner ℂ (basis N a) x := by
    have h : Tendsto (fun t : ℝ≥0 => inner ℂ (basis N a)
        (((t : ℝ)⁻¹ : ℂ) • (heat N t x - x))) (𝓝[>] 0)
        (𝓝 (inner ℂ (basis N a) y)) :=
      (innerSL ℂ (basis N a)).continuous.continuousAt.tendsto.comp hy
    have hp := (decay_slope_tendsto N a).mul_const (inner ℂ (basis N a) x)
    have h' : Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) *
        (((decay N t a : ℂ) - 1) * inner ℂ (basis N a) x))
        (𝓝[>] 0) (𝓝 (inner ℂ (basis N a) y)) := by
      convert h using 1
      funext t
      simp only [inner_smul_right, inner_sub_right, heat_coefficient]
      ring
    exact tendsto_nhds_unique h' (by simpa only [mul_assoc] using hp)
  have hn (a : BasisIndex N) : ‖(basis N).repr y a‖ ^ 2 =
      eigenvalue N a ^ 2 * ‖inner ℂ (basis N a) x‖ ^ 2 := by
    rw [HilbertBasis.repr_apply_apply, hc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg (eigenvalue_nonneg N a), mul_pow]
  apply (operator_domain N x).mpr
  simpa only [hn] using sequence_summable N ((basis N).repr y)

theorem rightGenerator_iff (N : ℕ) (x y : Fields N) :
    HasRightGenerator N x y ↔
      ∃ hx : x ∈ (operator N).domain, y = -(operator N ⟨x, hx⟩) := by
  constructor
  · intro hy
    have hx := mem_domain_of_rightGenerator N x y hy
    exact ⟨hx, tendsto_nhds_unique hy (rightGenerator_on_domain N ⟨x, hx⟩)⟩
  · rintro ⟨hx, rfl⟩
    exact rightGenerator_on_domain N ⟨x, hx⟩

theorem rightGenerator_domain_iff (N : ℕ) (x : Fields N) :
    (∃ y, HasRightGenerator N x y) ↔ x ∈ (operator N).domain := by
  constructor
  · rintro ⟨y, hy⟩
    exact mem_domain_of_rightGenerator N x y hy
  · intro hx
    exact ⟨_, rightGenerator_on_domain N ⟨x, hx⟩⟩

end GeneratedFoundations.Arithmetic.HistoryHaarHeatGenerator
