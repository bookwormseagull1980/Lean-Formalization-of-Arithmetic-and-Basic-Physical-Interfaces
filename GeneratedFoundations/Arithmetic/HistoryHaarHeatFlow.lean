module

public import GeneratedFoundations.Arithmetic.HistoryHaarClosedHessian
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Complete evolution of the arithmetic matrix-valued Haar Hessian

The heat multipliers act on every coefficient of the complete Hilbert
basis, not on a truncated list of Haar modes. Their exponent uses the
Hessian derived from the actual nonlinear matrix-curvature action.
The lower spectral edge is four for every arithmetic cutoff. This
operator and its energy differ from the history reaction generator.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology lp NNReal

namespace GeneratedFoundations.Arithmetic.HistoryHaarHeatFlow

open HistoryHaarClosedHessian
open Geometry.SourceOneFormCoclosedSpectrum

abbrev Sequence (N : ℕ) := ℓ²(BasisIndex N, ℂ)

def decay (N : ℕ) (t : ℝ) (a : BasisIndex N) : ℝ :=
  Real.exp (-t * eigenvalue N a)

theorem eigenvalue_ge_four (N : ℕ) (a : BasisIndex N) : 4 ≤ eigenvalue N a :=
  coclosed_eigenvalue_sq_ge_four a.2

theorem decay_pos (N : ℕ) (t : ℝ) (a : BasisIndex N) : 0 < decay N t a :=
  Real.exp_pos _

theorem decay_le_gap (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (a : BasisIndex N) :
    decay N t a ≤ Real.exp (-4 * t) := by
  apply Real.exp_le_exp.mpr
  have h := eigenvalue_ge_four N a
  nlinarith

theorem decay_le_one (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (a : BasisIndex N) :
    decay N t a ≤ 1 :=
  (decay_le_gap N ht a).trans (Real.exp_le_one_iff.mpr (by linarith))

@[simp] theorem decay_zero (N : ℕ) (a : BasisIndex N) : decay N 0 a = 1 := by
  simp [decay]

theorem decay_add (N : ℕ) (s t : ℝ) (a : BasisIndex N) :
    decay N (s + t) a = decay N s a * decay N t a := by
  simp only [decay]
  rw [show -(s + t) * eigenvalue N a =
    -s * eigenvalue N a + -t * eigenvalue N a by ring, Real.exp_add]

theorem decay_continuous (N : ℕ) (a : BasisIndex N) : Continuous (fun t => decay N t a) := by
  unfold decay
  fun_prop

def sequenceMap (N : ℕ) (t : ℝ≥0) (v : Sequence N) : Sequence N :=
  ⟨fun a => (decay N t a : ℂ) * v a, (lp.memℓp v).mono' (by
    intro a
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos N t a)]
    exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one N t.property a))⟩

@[simp] theorem sequenceMap_apply (N : ℕ) (t : ℝ≥0) (v : Sequence N) (a : BasisIndex N) :
    sequenceMap N t v a = (decay N t a : ℂ) * v a := rfl

def sequenceLinear (N : ℕ) (t : ℝ≥0) : Sequence N →ₗ[ℂ] Sequence N where
  toFun := sequenceMap N t
  map_add' v w := by
    apply lp.ext
    funext a
    change (decay N t a : ℂ) * (v a + w a) = _
    simp only [mul_add, sequenceMap_apply, lp.coeFn_add, Pi.add_apply]
  map_smul' c v := by
    apply lp.ext
    funext a
    change (decay N t a : ℂ) * (c * v a) = c * ((decay N t a : ℂ) * v a)
    ring

theorem sequence_norm_le (N : ℕ) (t : ℝ≥0) (v : Sequence N) :
    ‖sequenceLinear N t v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num)
  intro a
  change ‖(decay N t a : ℂ) * v a‖ ≤ ‖v a‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos N t a)]
  exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one N t.property a)

def sequenceOperator (N : ℕ) (t : ℝ≥0) : Sequence N →L[ℂ] Sequence N :=
  (sequenceLinear N t).mkContinuous 1 (by
    intro v
    simpa only [one_mul] using sequence_norm_le N t v)

def heat (N : ℕ) (t : ℝ≥0) : Fields N →L[ℂ] Fields N :=
  (basis N).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sequenceOperator N t).comp (basis N).repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem coefficients_heat (N : ℕ) (t : ℝ≥0) (x : Fields N) :
    (basis N).repr (heat N t x) = sequenceOperator N t ((basis N).repr x) := by
  simp [heat]

theorem heat_coefficient (N : ℕ) (t : ℝ≥0) (x : Fields N) (a : BasisIndex N) :
    inner ℂ (basis N a) (heat N t x) =
      (decay N t a : ℂ) * inner ℂ (basis N a) x := by
  have h := congrArg (fun v : Sequence N => v a) (coefficients_heat N t x)
  change (basis N).repr (heat N t x) a =
    (decay N t a : ℂ) * (basis N).repr x a at h
  simpa only [HilbertBasis.repr_apply_apply] using h

@[simp] theorem heat_zero (N : ℕ) (x : Fields N) : heat N 0 x = x := by
  apply Operations.EigenbasisClosure.eq_of_coefficients (basis N)
  intro a
  simp only [heat_coefficient, NNReal.coe_zero, decay_zero, Complex.ofReal_one, one_mul]

theorem heat_add (N : ℕ) (s t : ℝ≥0) (x : Fields N) :
    heat N (s + t) x = heat N s (heat N t x) := by
  apply Operations.EigenbasisClosure.eq_of_coefficients (basis N)
  intro a
  simp only [heat_coefficient, NNReal.coe_add, decay_add, Complex.ofReal_mul, mul_assoc]

theorem heat_basis (N : ℕ) (t : ℝ≥0) (a : BasisIndex N) :
    heat N t (basis N a) = (decay N t a : ℂ) • basis N a := by
  apply Operations.EigenbasisClosure.eq_of_coefficients (basis N)
  intro b
  simp only [heat_coefficient, inner_smul_right,
    orthonormal_iff_ite.mp (basis N).orthonormal]
  by_cases h : b = a
  · subst b; simp
  · simp [h]

/-- The constant is derived from the complete differential spectrum and
does not depend on the number of retained histories. -/
theorem heat_norm_decay (N : ℕ) (t : ℝ≥0) (x : Fields N) :
    ‖heat N t x‖ ≤ Real.exp (-4 * (t : ℝ)) * ‖x‖ := by
  have h : ‖sequenceOperator N t ((basis N).repr x)‖ ≤
      ‖(Real.exp (-4 * (t : ℝ)) : ℂ) • (basis N).repr x‖ := by
    apply lp.norm_mono (by norm_num)
    intro a
    change ‖(decay N t a : ℂ) * (basis N).repr x a‖ ≤
      ‖(Real.exp (-4 * (t : ℝ)) : ℂ) * (basis N).repr x a‖
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (decay_pos N t a), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (decay_le_gap N t.property a) (norm_nonneg _)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), (basis N).repr.norm_map] at h
  rw [← (basis N).repr.norm_map (heat N t x), coefficients_heat]
  exact h

private theorem sequence_norm_sq (N : ℕ) (v : Sequence N) :
    ‖v‖ ^ 2 = ∑' a, ‖v a‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v

private theorem sequence_summable (N : ℕ) (v : Sequence N) :
    Summable (fun a => ‖v a‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)

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

theorem sequence_stronglyContinuous (N : ℕ) (v : Sequence N) :
    Continuous (fun t : ℝ≥0 => sequenceOperator N t v) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero N _ (fun a => 4 * ‖v a‖ ^ 2)
    ((sequence_summable N v).mul_left 4)
  · intro a
    have hc : Continuous (fun t : ℝ≥0 => (decay N t a : ℂ)) :=
      Complex.continuous_ofReal.comp ((decay_continuous N a).comp continuous_subtype_val)
    have h := (hc.continuousAt (x := s)).mul_const (v a)
    change Tendsto (fun t : ℝ≥0 => (decay N t a : ℂ) * v a -
      (decay N s a : ℂ) * v a) (𝓝 s) (𝓝 0)
    simpa only [sub_self] using h.tendsto.sub_const ((decay N s a : ℂ) * v a)
  · apply Eventually.of_forall
    intro t a
    have hpart (r : ℝ≥0) : ‖(decay N r a : ℂ) * v a‖ ≤ ‖v a‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (decay_pos N r a)]
      exact mul_le_of_le_one_left (norm_nonneg _) (decay_le_one N r.property a)
    have h : ‖(decay N t a : ℂ) * v a - (decay N s a : ℂ) * v a‖ ≤ 2 * ‖v a‖ :=
      (norm_sub_le _ _).trans (by linarith [hpart t, hpart s])
    have hh := norm_nonneg ((decay N t a : ℂ) * v a - (decay N s a : ℂ) * v a)
    change ‖(decay N t a : ℂ) * v a - (decay N s a : ℂ) * v a‖ ^ 2 ≤ _
    nlinarith

theorem heat_stronglyContinuous (N : ℕ) (x : Fields N) :
    Continuous (fun t : ℝ≥0 => heat N t x) := by
  exact (basis N).repr.symm.continuous.comp
    (sequence_stronglyContinuous N ((basis N).repr x))

theorem heat_preserves_domain (N : ℕ) (t : ℝ≥0) {x : Fields N}
    (hx : x ∈ (operator N).domain) : heat N t x ∈ (operator N).domain := by
  rw [operator_domain] at hx ⊢
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _ hx
  intro a
  rw [heat_coefficient, norm_mul, mul_pow]
  have h : ‖(decay N t a : ℂ)‖ ^ 2 ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hp := (decay_pos N t a).le
    have hu := decay_le_one N t.property a
    simpa only [one_pow] using pow_le_pow_left₀ hp hu 2
  calc
    _ = ‖(decay N t a : ℂ)‖ ^ 2 *
        (eigenvalue N a ^ 2 * ‖inner ℂ (basis N a) x‖ ^ 2) := by ring
    _ ≤ 1 * (eigenvalue N a ^ 2 * ‖inner ℂ (basis N a) x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := one_mul _

structure Conclusions : Prop where
  identity : ∀ N x, heat N 0 x = x
  composition : ∀ N s t x, heat N (s + t) x = heat N s (heat N t x)
  complete_continuity : ∀ N x, Continuous (fun t : ℝ≥0 => heat N t x)
  actual_coefficients : ∀ N t x a, inner ℂ (basis N a) (heat N t x) =
    (decay N t a : ℂ) * inner ℂ (basis N a) x
  uniform_decay : ∀ N t x, ‖heat N t x‖ ≤ Real.exp (-4 * (t : ℝ)) * ‖x‖
  invariant_domain : ∀ N t x, x ∈ (operator N).domain → heat N t x ∈ (operator N).domain

theorem generated : Conclusions where
  identity := heat_zero
  composition := heat_add
  complete_continuity := heat_stronglyContinuous
  actual_coefficients := heat_coefficient
  uniform_decay := heat_norm_decay
  invariant_domain := fun N t _ hx => heat_preserves_domain N t hx

end GeneratedFoundations.Arithmetic.HistoryHaarHeatFlow
