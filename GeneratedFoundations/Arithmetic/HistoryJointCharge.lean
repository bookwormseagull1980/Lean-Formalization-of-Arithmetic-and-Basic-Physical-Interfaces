module

public import GeneratedFoundations.Arithmetic.HistoryJointChargeLattice
public import GeneratedFoundations.Arithmetic.HistoryRelativePhaseKernel

/-!
# Joint phase and source charges on the full arithmetic fibre

The carrier keeps the entire generated history--phase Hilbert space at
each of the original four source coordinates. Averaging acts only on the
phase coordinate; right spin acts only on the source coordinate. Their
joint response is therefore constructed before any trace or quotient.

The neutral space is computed from the actual response. In particular it
contains every history, rather than a chosen one-dimensional vacuum. The
phase fibre at root two has an additional neutral detail sector; root one
is entirely neutral. All original coefficients remain available in the
retained projections and the full coherent norm identity.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryJointCharge

open HistoryJointChargeLattice
open HistoryPhaseProjection (projection residual)

abbrev Fibre (n : ℕ) := HistoryModuleRepresentation.Space n
abbrev Space (n : ℕ) := PiLp 2 (fun _ : Spin => Fibre n)

def inclusion (n : ℕ) (s : Spin) : Fibre n →ₗ[ℂ] Space n where
  toFun x := PiLp.single 2 s x
  map_add' x y := by
    classical
    apply PiLp.ext
    intro t
    by_cases h : t = s <;> simp [h]
  map_smul' c x := by
    classical
    apply PiLp.ext
    intro t
    by_cases h : t = s <;> simp [h]

def sectionMap (n : ℕ) (s : Spin) : Space n →ₗ[ℂ] Fibre n where
  toFun x := x s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem section_inclusion (n : ℕ) (s : Spin) :
    (sectionMap n s).comp (inclusion n s) = 1 := by
  apply LinearMap.ext
  intro x
  change (PiLp.single 2 s x : Space n) s = x
  exact PiLp.single_eq_same _ _ _

def blocks (n : ℕ) (B : Spin → Module.End ℂ (Fibre n)) : Module.End ℂ (Space n) :=
  ∑ s, (inclusion n s).comp ((B s).comp (sectionMap n s))

@[simp] theorem blocks_apply (n : ℕ) (B : Spin → Module.End ℂ (Fibre n))
    (x : Space n) (s : Spin) : blocks n B x s = B s (x s) := by
  classical
  change WithLp.ofLp (∑ t, PiLp.single 2 t (B t (x t)) : Space n) s = _
  rw [WithLp.ofLp_sum]
  change (∑ t, (PiLp.single 2 t (B t (x t)) : Space n) s) = _
  rw [Finset.sum_eq_single s]
  · exact PiLp.single_eq_same _ _ _
  · intro t _ hts
    exact PiLp.single_eq_of_ne (β := fun _ : Spin => Fibre n) 2 (Ne.symm hts) (B t (x t))
  · simp

theorem blocks_trace (n : ℕ) (B : Spin → Module.End ℂ (Fibre n)) :
    LinearMap.trace ℂ (Space n) (blocks n B) =
      ∑ s, LinearMap.trace ℂ (Fibre n) (B s) := by
  rw [blocks, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, section_inclusion]
  rfl

def component (n : ℕ) (r b : ℤ) (s : Spin) : Module.End ℂ (Fibre n) :=
  HistoryRelativePhase.block n ((weight n r b (false, s) : ℂ), (weight n r b (true, s) : ℂ))

def response (n : ℕ) (r b : ℤ) : Module.End ℂ (Space n) := blocks n (component n r b)

def generatedResponse (n : ℕ) : Module.End ℂ (Space n) := response n n 1

theorem component_generators (n : ℕ) (r b : ℤ) (s : Spin) :
    component n r b s = (b : ℂ) • HistoryRelativePhase.generator n +
      (r * rightWeight s : ℤ) • (1 : Module.End ℂ (Fibre n)) := by
  unfold component HistoryRelativePhase.generator HistoryRelativePhase.relative
    HistoryRelativePhase.block weight relativeWeight
  push_cast
  simp only [add_smul, mul_smul, one_smul, HistoryPhaseProjection.residual]
  module

theorem component_trace (n : ℕ) (r b : ℤ) (s : Spin) :
    LinearMap.trace ℂ (Fibre n) (component n r b s) =
      (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) *
        ((weight n r b (false, s) : ℂ) + n * weight n r b (true, s)) := by
  change LinearMap.trace ℂ (Fibre n)
    ((weight n r b (false, s) : ℂ) • projection n +
      (weight n r b (true, s) : ℂ) • residual n) = _
  rw [map_add, map_smul, map_smul, HistoryPhaseProjection.projection_trace,
    HistoryPhaseProjection.residual_trace]
  simp only [smul_eq_mul]
  ring

theorem response_trace (n : ℕ) (r b : ℤ) :
    LinearMap.trace ℂ (Space n) (response n r b) = 0 := by
  rw [response, blocks_trace]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, component_trace]
  simp [weight, rightWeight, relativeWeight]
  ring

theorem component_energy (n : ℕ) (r b : ℤ) (s : Spin) (x : Fibre n) :
    ‖component n r b s x‖ ^ 2 =
      (weight n r b (false, s) : ℝ) ^ 2 * ‖projection n x‖ ^ 2 +
      (weight n r b (true, s) : ℝ) ^ 2 * ‖residual n x‖ ^ 2 := by
  rw [component, HistoryRelativePhase.block_apply, norm_add_sq (𝕜 := ℂ)]
  simp only [inner_smul_left, inner_smul_right,
    HistoryPhaseProjection.projection_residual_inner, mul_zero,
    norm_smul, mul_pow]
  norm_cast
  simp [sq_abs]

theorem response_energy (n : ℕ) (r b : ℤ) (x : Space n) :
    ‖response n r b x‖ ^ 2 = ∑ s,
      ((weight n r b (false, s) : ℝ) ^ 2 * ‖projection n (x s)‖ ^ 2 +
        (weight n r b (true, s) : ℝ) ^ 2 * ‖residual n (x s)‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro s _
  rw [response, blocks_apply, component_energy]

theorem component_zero_iff (n : ℕ) (r b : ℤ) (s : Spin) (x : Fibre n) :
    component n r b s x = 0 ↔
      (weight n r b (false, s) : ℂ) • projection n x = 0 ∧
      (weight n r b (true, s) : ℂ) • residual n x = 0 := by
  constructor
  · intro hx
    have hp := congrArg (projection n) hx
    have hr := congrArg (residual n) hx
    have hid := LinearMap.congr_fun (HistoryPhaseProjection.projection_idempotent n) x
    have hrd := LinearMap.congr_fun (HistoryPhaseProjection.residual_idempotent n) x
    have hpr := LinearMap.congr_fun (HistoryPhaseProjection.projection_residual n) x
    have hrp := LinearMap.congr_fun (HistoryPhaseProjection.residual_projection n) x
    change projection n (projection n x) = _ at hid
    change residual n (residual n x) = _ at hrd
    change projection n (residual n x) = 0 at hpr
    change residual n (projection n x) = 0 at hrp
    simpa only [component, HistoryRelativePhase.block_apply, map_add, map_smul,
      map_zero, hid, hrd, hpr, hrp, smul_zero, add_zero, zero_add] using And.intro hp hr
  · rintro ⟨hp, hr⟩
    simp only [component, HistoryRelativePhase.block_apply, hp, hr, add_zero]

def neutral (n : ℕ) : Submodule ℂ (Space n) := LinearMap.ker (generatedResponse n)

theorem neutral_iff (n : ℕ) (x : Space n) : x ∈ neutral n ↔ ∀ s,
    ((generatedWeight n (false, s) : ℂ) • projection n (x s) = 0 ∧
      (generatedWeight n (true, s) : ℂ) • residual n (x s) = 0) := by
  change generatedResponse n x = 0 ↔ _
  constructor
  · intro hx s
    apply (component_zero_iff n n 1 s (x s)).mp
    simpa only [generatedResponse, response, blocks_apply, PiLp.zero_apply]
      using congrArg (fun z : Space n => z s) hx
  · intro hx
    apply PiLp.ext
    intro s
    simpa only [generatedResponse, response, blocks_apply, PiLp.zero_apply]
      using (component_zero_iff n n 1 s (x s)).mpr (hx s)

theorem generated_unique (n : ℕ) (r b : ℤ) (hp : Primitive n r b)
    (hv : weight n r b (false, .inr 0) = 0) (hb : 0 < b) :
    response n r b = generatedResponse n := by
  obtain ⟨rfl, rfl⟩ := oriented_unique n hp hv hb
  rfl

theorem full_dimension (n : ℕ) : Module.finrank ℂ (Space n) =
    4 * (Fintype.card (CompleteHistory.History (n + 1)) * (n + 1)) := by
  rw [(WithLp.linearEquiv 2 ℂ (Spin → Fibre n)).finrank_eq,
    Module.finrank_pi_fintype]
  simp [Spin, Operations.SourceCliffordConnector.ChiralIndex]

structure Conclusions : Prop where
  original_generators : ∀ n r b s, component n r b s =
    (b : ℂ) • HistoryRelativePhase.generator n +
      (r * rightWeight s : ℤ) • (1 : Module.End ℂ (Fibre n))
  actual_trace : ∀ n r b, LinearMap.trace ℂ (Space n) (response n r b) = 0
  full_energy : ∀ n r b (x : Space n), ‖response n r b x‖ ^ 2 = ∑ s,
    ((weight n r b (false, s) : ℝ) ^ 2 * ‖projection n (x s)‖ ^ 2 +
      (weight n r b (true, s) : ℝ) ^ 2 * ‖residual n (x s)‖ ^ 2)
  actual_kernel : ∀ n (x : Space n), x ∈ neutral n ↔ ∀ s,
    ((generatedWeight n (false, s) : ℂ) • projection n (x s) = 0 ∧
      (generatedWeight n (true, s) : ℂ) • residual n (x s) = 0)
  character_unique : ∀ n r b, Primitive n r b →
    weight n r b (false, .inr 0) = 0 → 0 < b → response n r b = generatedResponse n
  actual_dimension : ∀ n, Module.finrank ℂ (Space n) =
    4 * (Fintype.card (CompleteHistory.History (n + 1)) * (n + 1))

theorem generated : Conclusions where
  original_generators := component_generators
  actual_trace := response_trace
  full_energy := response_energy
  actual_kernel := neutral_iff
  character_unique := generated_unique
  actual_dimension := full_dimension

end GeneratedFoundations.Arithmetic.HistoryJointCharge
