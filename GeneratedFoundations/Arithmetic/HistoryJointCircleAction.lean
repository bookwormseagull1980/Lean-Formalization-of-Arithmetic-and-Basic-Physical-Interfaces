module

public import GeneratedFoundations.Arithmetic.HistoryJointPhaseFlow

/-!
# The actual integer-character circle action on the full arithmetic source

The circle characters use the previously calculated charge weights. Their
action is assembled through the original eight projection sectors and keeps
all histories and phases. Its lift is exactly the already constructed
continuous charge flow. This identifies the circle and exponential
descriptions without replacing the source by a list of charge labels.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryJointCircleAction

open HistoryJointCharge HistoryJointChargeLattice
open HistoryJointPhaseFlow
open HistoryPhaseProjection (projection residual)

def weights (n : ℕ) (r b : ℤ) (z : Circle) : Spin → ℂ × ℂ :=
  fun s => ((z : ℂ) ^ weight n r b (false, s), (z : ℂ) ^ weight n r b (true, s))

def action (n : ℕ) (r b : ℤ) (z : Circle) : Module.End ℂ (Space n) :=
  sectorAlgebra n (weights n r b z)

theorem action_apply (n : ℕ) (r b : ℤ) (z : Circle) (x : Space n) (s : Spin) :
    action n r b z x s =
      (z : ℂ) ^ weight n r b (false, s) • projection n (x s) +
        (z : ℂ) ^ weight n r b (true, s) • residual n (x s) := by
  change blocks n (fun q => HistoryRelativePhase.block n (weights n r b z q)) x s = _
  rw [blocks_apply]
  rfl

theorem action_one (n : ℕ) (r b : ℤ) : action n r b 1 = 1 := by
  change sectorAlgebra n (weights n r b 1) = 1
  have hw : weights n r b 1 = 1 := by ext s <;> simp [weights]
  rw [hw, map_one]

theorem action_mul (n : ℕ) (r b : ℤ) (z v : Circle) :
    action n r b (z * v) = action n r b z * action n r b v := by
  unfold action
  rw [← map_mul]
  congr 1
  ext s <;> simp [weights, mul_zpow]

def representation (n : ℕ) (r b : ℤ) : Circle →* Module.End ℂ (Space n) where
  toFun := action n r b
  map_one' := action_one n r b
  map_mul' := action_mul n r b

theorem character_exp (q : ℤ) (t : ℝ) :
    (Circle.exp t : ℂ) ^ q = HistoryRelativePhase.scalar (q : ℝ) t := by
  rw [Circle.coe_exp, ← Complex.exp_int_mul]
  unfold HistoryRelativePhase.scalar Operations.FinitePhaseFlow.phase
  congr 1
  push_cast
  ring

theorem action_exp (n : ℕ) (r b : ℤ) (t : ℝ) :
    action n r b (Circle.exp t) = flow n r b t := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [action_apply, flow_apply, character_exp]

theorem action_inner (n : ℕ) (r b : ℤ) (z : Circle) (x y : Space n) :
    inner ℂ (action n r b z x) (action n r b z y) = inner ℂ x y := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  rw [action_exp]
  exact flow_inner n r b t x y

/-- Every vector in every actual projection sector has the computed
character, including the additional neutral sectors at the small roots. -/
theorem action_sector (n : ℕ) (r b : ℤ) (z : Circle) (p : Sector) (x : Fibre n) :
    action n r b z (HistoryChargeSectors.sectorSection n p x) =
      (z : ℂ) ^ weight n r b p • HistoryChargeSectors.sectorSection n p x := by
  rcases p with ⟨c, q⟩
  apply PiLp.ext
  intro s
  by_cases hs : s = q
  · subst s
    cases c <;>
      simp only [action_apply, HistoryChargeSectors.sectorSection_apply,
        HistoryChargeSectors.phaseProjection, Bool.false_eq_true, ↓reduceIte,
        PiLp.smul_apply]
    all_goals
      have hp := congrArg (fun A : Module.End ℂ (Fibre n) => A x)
        (HistoryPhaseProjection.projection_idempotent n)
      have hr := congrArg (fun A : Module.End ℂ (Fibre n) => A x)
        (HistoryPhaseProjection.residual_idempotent n)
      have hpr := congrArg (fun A : Module.End ℂ (Fibre n) => A x)
        (HistoryPhaseProjection.projection_residual n)
      have hrp := congrArg (fun A : Module.End ℂ (Fibre n) => A x)
        (HistoryPhaseProjection.residual_projection n)
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at hp hr hpr hrp
      simp only [hp, hr, hpr, hrp, smul_zero, add_zero, zero_add]
  · simp [action_apply, HistoryChargeSectors.sectorSection_apply, hs]

/-- The character is detected by the whole occupied projection, independently
of any choice of a vector or a basis in that sector. -/
theorem action_sectorProjection (n : ℕ) (r b : ℤ) (z : Circle) (p : Sector) :
    action n r b z * HistoryChargeSectors.sectorProjection n p =
      (z : ℂ) ^ weight n r b p • HistoryChargeSectors.sectorProjection n p := by
  apply LinearMap.ext
  intro x
  exact action_sector n r b z p (HistoryJointCharge.sectionMap n p.2 x)

/-- The primitive character is faithful on the original complete carrier.
The decisive weight-one sector has positive actual rank for every n > 0. -/
theorem generated_eq_one_iff {n : ℕ} (hn : 0 < n) (z : Circle) :
    action n n 1 z = 1 ↔ z = 1 := by
  constructor
  · intro hz
    let p : Sector := (true, .inl 0)
    have hs := action_sectorProjection n n 1 z p
    rw [hz, one_mul] at hs
    have he : (z : ℂ) • HistoryChargeSectors.sectorProjection n p =
        HistoryChargeSectors.sectorProjection n p := by
      simpa only [p, detail_left, zpow_one] using hs.symm
    have hzero : ((z : ℂ) - 1) • HistoryChargeSectors.sectorProjection n p = 0 := by
      rw [sub_smul, one_smul, he, sub_self]
    exact Circle.coe_eq_one.mp (sub_eq_zero.mp
      ((smul_eq_zero.mp hzero).resolve_right
        (HistoryChargeSectors.sectorProjection_ne_zero hn p)))
  · rintro rfl
    exact action_one n n 1

theorem generated_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (representation n n 1) := by
  intro z w h
  apply mul_inv_eq_one.mp
  apply (generated_eq_one_iff hn (z * w⁻¹)).mp
  calc
    action n n 1 (z * w⁻¹) = action n n 1 z * action n n 1 w⁻¹ := action_mul ..
    _ = action n n 1 w * action n n 1 w⁻¹ := congrArg (fun A => A * action n n 1 w⁻¹) h
    _ = action n n 1 (w * w⁻¹) := (action_mul ..).symm
    _ = 1 := by rw [mul_inv_cancel, action_one]

theorem generatedFlow_eq_one_iff {n : ℕ} (hn : 0 < n) (t : ℝ) :
    flow n n 1 t = 1 ↔ ∃ k : ℤ, t = k * (2 * Real.pi) := by
  rw [← action_exp, generated_eq_one_iff hn, Circle.exp_eq_one]

theorem generatedFlow_periodic_iff {n : ℕ} (hn : 0 < n) (t : ℝ) :
    Function.Periodic (flow n n 1) t ↔ ∃ k : ℤ, t = k * (2 * Real.pi) := by
  constructor
  · intro hp
    apply (generatedFlow_eq_one_iff hn t).mp
    simpa only [zero_add, flow_zero] using hp 0
  · intro hp s
    rw [flow_add, (generatedFlow_eq_one_iff hn t).mpr hp, mul_one]

theorem generatedFlow_least_positive_period {n : ℕ} (hn : 0 < n) :
    IsLeast {t : ℝ | 0 < t ∧ Function.Periodic (flow n n 1) t} (2 * Real.pi) := by
  refine ⟨⟨by positivity, (generatedFlow_periodic_iff hn _).mpr ⟨1, by simp⟩⟩, ?_⟩
  rintro t ⟨ht, hp⟩
  obtain ⟨k, rfl⟩ := (generatedFlow_periodic_iff hn t).mp hp
  have hk : (0 : ℝ) < k := (mul_pos_iff_of_pos_right (by positivity : 0 < 2 * Real.pi)).mp ht
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hk'' : (1 : ℝ) ≤ k := by exact_mod_cast hk'
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk''
    (le_of_lt (by positivity : 0 < 2 * Real.pi))

structure Conclusions : Prop where
  all_coefficients : ∀ n r b z x s, action n r b z x s =
    (z : ℂ) ^ weight n r b (false, s) • projection n (x s) +
      (z : ℂ) ^ weight n r b (true, s) • residual n (x s)
  exact_exponential_lift : ∀ n r b t, action n r b (Circle.exp t) = flow n r b t
  every_actual_sector : ∀ n r b z p x,
    action n r b z (HistoryChargeSectors.sectorSection n p x) =
      (z : ℂ) ^ weight n r b p • HistoryChargeSectors.sectorSection n p x
  all_inner_products : ∀ n r b z x y,
    inner ℂ (action n r b z x) (action n r b z y) = inner ℂ x y
  faithful_primitive_character : ∀ n, 0 < n → Function.Injective (representation n n 1)
  actual_flow_kernel : ∀ n, 0 < n → ∀ t,
    flow n n 1 t = 1 ↔ ∃ k : ℤ, t = k * (2 * Real.pi)
  actual_least_period : ∀ n, 0 < n →
    IsLeast {t : ℝ | 0 < t ∧ Function.Periodic (flow n n 1) t} (2 * Real.pi)

theorem generated : Conclusions where
  all_coefficients := action_apply
  exact_exponential_lift := action_exp
  every_actual_sector := action_sector
  all_inner_products := action_inner
  faithful_primitive_character := fun _ => generated_injective
  actual_flow_kernel := fun _ => generatedFlow_eq_one_iff
  actual_least_period := fun _ => generatedFlow_least_positive_period

end GeneratedFoundations.Arithmetic.HistoryJointCircleAction
