module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A scaled power limit for contractions

The power comparison is valid in a noncommutative normed algebra.  The
integer step count is the actual natural floor of the inverse-square
scale.  Its rounding error is estimated explicitly.  The resulting limit
uses the punctured neighborhood of zero: the value of the zero-scale
step count is not part of the positive-time limiting assertion.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace GeneratedFoundations.Operations.ContractivePowerLimit

/-- The number of repeated steps at resolution `ε`. -/
def steps (K ε : ℝ) : ℕ := ⌊K / ε ^ 2⌋₊

@[simp] theorem steps_zero_scale (K : ℝ) : steps K 0 = 0 := by
  simp [steps]

@[simp] theorem steps_zero_time (ε : ℝ) : steps 0 ε = 0 := by
  simp [steps]

/-- The actual rounded duration differs from `K` by at most one step. -/
theorem scaled_steps_bounds {K ε : ℝ} (hK : 0 ≤ K) (hε : ε ≠ 0) :
    0 ≤ K - ε ^ 2 * (steps K ε : ℝ) ∧
      K - ε ^ 2 * (steps K ε : ℝ) ≤ ε ^ 2 := by
  unfold steps
  have hsq : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
  have hlow := mul_le_mul_of_nonneg_left
    (Nat.floor_le (div_nonneg hK hsq.le)) hsq.le
  have hupp := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one (K / ε ^ 2)) hsq
  have hcancel : ε ^ 2 * (K / ε ^ 2) = K := by
    field_simp [hε]
  rw [hcancel] at hlow hupp
  constructor
  · exact sub_nonneg.mpr hlow
  · nlinarith

theorem scaled_steps_tendsto {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun ε : ℝ => ε ^ 2 * (steps K ε : ℝ)) (𝓝[≠] 0) (𝓝 K) := by
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[≠] 0) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hs : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    simpa using hε.pow 2
  have hb : ∀ᶠ ε : ℝ in 𝓝[≠] 0,
      0 ≤ K - ε ^ 2 * (steps K ε : ℝ) ∧
        K - ε ^ 2 * (steps K ε : ℝ) ≤ ε ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact scaled_steps_bounds hK (by simpa using hε)
  have hr := squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2) hs
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ => K) (𝓝[≠] 0) (𝓝 K)).sub hr
  simpa only [sub_sub_cancel, sub_zero] using ht

section NormedRing

variable {E : Type*} [NormedRing E] [NormOneClass E]

theorem norm_pow_le_one {x : E} (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖x ^ n‖ ≤ 1 :=
  (norm_pow_le x n).trans (pow_le_one₀ (norm_nonneg x) hx)

/-- No commutation of the two contractions is used. -/
theorem norm_pow_sub_pow_le {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hid : x ^ (n + 1) - y ^ (n + 1) =
          (x ^ n - y ^ n) * x + y ^ n * (x - y) := by
        simp only [pow_succ, sub_mul, mul_sub]
        abel
      have hfirst : ‖x ^ n - y ^ n‖ * ‖x‖ ≤ (n : ℝ) * ‖x - y‖ :=
        (mul_le_of_le_one_right (norm_nonneg _) hx).trans ih
      have hsecond : ‖y ^ n‖ * ‖x - y‖ ≤ ‖x - y‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (norm_pow_le_one hy n) (norm_nonneg (x - y))
      calc
        ‖x ^ (n + 1) - y ^ (n + 1)‖ =
            ‖(x ^ n - y ^ n) * x + y ^ n * (x - y)‖ := congrArg norm hid
        _ ≤ ‖(x ^ n - y ^ n) * x‖ + ‖y ^ n * (x - y)‖ := norm_add_le _ _
        _ ≤ ‖x ^ n - y ^ n‖ * ‖x‖ + ‖y ^ n‖ * ‖x - y‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ (n : ℝ) * ‖x - y‖ + ‖x - y‖ := add_le_add hfirst hsecond
        _ = ((n + 1 : ℕ) : ℝ) * ‖x - y‖ := by push_cast; ring

/-- The floor bound converts the accumulated error into the normalized
one-step error. This inequality also holds at the zero scale. -/
theorem norm_scaled_power_sub_le {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    {K : ℝ} (hK : 0 ≤ K) (ε : ℝ) :
    ‖x ^ steps K ε - y ^ steps K ε‖ ≤ K * (‖x - y‖ / ε ^ 2) := by
  calc
    _ ≤ (steps K ε : ℝ) * ‖x - y‖ := norm_pow_sub_pow_le hx hy _
    _ ≤ (K / ε ^ 2) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hK (sq_nonneg ε)))
        (norm_nonneg (x - y))
    _ = K * (‖x - y‖ / ε ^ 2) := by ring

end NormedRing

section NormedAlgebra

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [NormOneClass E]

def comparison (a ε : ℝ) : E := Real.exp (-a * ε ^ 2) • (1 : E)

theorem norm_comparison_le_one {a : ℝ} (ha : 0 ≤ a) (ε : ℝ) :
    ‖comparison (E := E) a ε‖ ≤ 1 := by
  rw [comparison, norm_smul, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sq_nonneg ε))

omit [NormOneClass E] in
theorem comparison_pow (a ε : ℝ) (n : ℕ) :
    comparison (E := E) a ε ^ n =
      Real.exp (-a * (ε ^ 2 * (n : ℝ))) • (1 : E) := by
  rw [comparison, smul_pow, one_pow, ← Real.exp_nat_mul]
  congr 2
  ring

omit [NormOneClass E] in
theorem comparison_power_tendsto (a : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun ε : ℝ => comparison (E := E) a ε ^ steps K ε)
      (𝓝[≠] 0) (𝓝 (Real.exp (-a * K) • (1 : E))) := by
  have he : Tendsto (fun ε : ℝ => -a * (ε ^ 2 * (steps K ε : ℝ)))
      (𝓝[≠] 0) (𝓝 (-a * K)) :=
    tendsto_const_nhds.mul (scaled_steps_tendsto hK)
  have hexp := (Real.continuous_exp.tendsto (-a * K)).comp he
  simpa only [comparison_pow, Function.comp_def] using
    hexp.smul (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : E))
      (𝓝[≠] 0) (𝓝 (1 : E)))

/-- Quadratic one-step agreement of contractions gives the full scaled
power limit with the actual rounded number of steps. -/
theorem power_tendsto (M : ℝ → E) {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hM : ∀ ε : ℝ, ‖M ε‖ ≤ 1)
    (herr : Tendsto (fun ε : ℝ => ‖M ε - comparison a ε‖ / ε ^ 2)
      (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => M ε ^ steps K ε)
      (𝓝[≠] 0) (𝓝 (Real.exp (-a * K) • (1 : E))) := by
  have hb : Tendsto (fun ε : ℝ => K * (‖M ε - comparison a ε‖ / ε ^ 2))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => K) (𝓝[≠] 0) (𝓝 K)).mul herr
  have hnorm : Tendsto
      (fun ε : ℝ => ‖M ε ^ steps K ε - comparison a ε ^ steps K ε‖)
      (𝓝[≠] 0) (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun ε =>
      norm_scaled_power_sub_le (hM ε) (norm_comparison_le_one ha ε) hK ε) hb
  have hdiff : Tendsto
      (fun ε : ℝ => M ε ^ steps K ε - comparison a ε ^ steps K ε)
      (𝓝[≠] 0) (𝓝 (0 : E)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [sub_add_cancel, zero_add] using
    hdiff.add (comparison_power_tendsto (E := E) a hK)

/-- An operator-valued normalized remainder may be supplied directly. -/
theorem power_tendsto_of_scaled (M : ℝ → E) {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hM : ∀ ε : ℝ, ‖M ε‖ ≤ 1)
    (herr : Tendsto (fun ε : ℝ => (ε ^ 2)⁻¹ • (M ε - comparison a ε))
      (𝓝[≠] 0) (𝓝 (0 : E))) :
    Tendsto (fun ε : ℝ => M ε ^ steps K ε)
      (𝓝[≠] 0) (𝓝 (Real.exp (-a * K) • (1 : E))) := by
  apply power_tendsto M ha hK hM
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow, sq_abs,
    norm_zero, div_eq_mul_inv, mul_comm] using herr.norm

end NormedAlgebra

end GeneratedFoundations.Operations.ContractivePowerLimit
