module

public import GeneratedFoundations.Arithmetic.HistoryJointCharge

/-!
# The actual neutral projection, charged quotient and charge capacity

The neutral projection is the zero-weight spectral projection of the
already constructed joint response. It is not a selected line. The full
kernel, its retained complement, the quotient rank and the squared-charge
trace are calculated with the actual invariant/detail multiplicities.
The small phase fibre is kept as a separate case.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryJointChargeQuotient

open HistoryJointCharge HistoryJointChargeLattice
open HistoryPhaseProjection (projection residual)

theorem blocks_mul (n : ℕ) (B C : Spin → Module.End ℂ (Fibre n)) :
    blocks n B * blocks n C = blocks n (fun s => B s * C s) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [Module.End.mul_apply, blocks_apply]

theorem phaseBlock_trace (n : ℕ) (z : ℂ × ℂ) :
    LinearMap.trace ℂ (Fibre n) (HistoryRelativePhase.block n z) =
      (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) * (z.1 + n * z.2) := by
  change LinearMap.trace ℂ (Fibre n) (z.1 • projection n + z.2 • residual n) = _
  rw [map_add, map_smul, map_smul, HistoryPhaseProjection.projection_trace,
    HistoryPhaseProjection.residual_trace]
  simp only [smul_eq_mul]
  ring

def mask (z : ℤ) : ℂ := if z = 0 then 1 else 0

theorem mask_sq (z : ℤ) : mask z * mask z = mask z := by
  by_cases h : z = 0 <;> simp [mask, h]

theorem mul_mask (z : ℤ) : (z : ℂ) * mask z = 0 := by
  by_cases h : z = 0 <;> simp [mask, h]

def neutralComponent (n : ℕ) (s : Spin) : Module.End ℂ (Fibre n) :=
  HistoryRelativePhase.block n
    (mask (generatedWeight n (false, s)), mask (generatedWeight n (true, s)))

def neutralProjection (n : ℕ) : Module.End ℂ (Space n) := blocks n (neutralComponent n)

theorem neutralProjection_idempotent (n : ℕ) :
    IsIdempotentElem (neutralProjection n) := by
  change blocks n (neutralComponent n) * blocks n (neutralComponent n) = _
  rw [blocks_mul]
  congr 1
  funext s
  unfold neutralComponent
  rw [← map_mul]
  congr 1
  exact Prod.ext (mask_sq _) (mask_sq _)

theorem response_neutral_zero (n : ℕ) : generatedResponse n * neutralProjection n = 0 := by
  change blocks n (component n n 1) * blocks n (neutralComponent n) = 0
  rw [blocks_mul]
  have hz (s : Spin) : component n n 1 s * neutralComponent n s = 0 := by
    unfold component neutralComponent
    rw [← map_mul]
    have h : ((generatedWeight n (false, s) : ℂ), (generatedWeight n (true, s) : ℂ)) *
        (mask (generatedWeight n (false, s)), mask (generatedWeight n (true, s))) = 0 :=
      Prod.ext (mul_mask _) (mul_mask _)
    change HistoryRelativePhase.block n
      (((generatedWeight n (false, s) : ℂ), (generatedWeight n (true, s) : ℂ)) * _) = 0
    rw [h, map_zero]
  simp only [hz]
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [blocks_apply, LinearMap.zero_apply, PiLp.zero_apply]

theorem neutralProjection_fixed_iff (n : ℕ) (x : Space n) :
    neutralProjection n x = x ↔ x ∈ neutral n := by
  constructor
  · intro hx
    change generatedResponse n x = 0
    rw [← hx]
    exact LinearMap.congr_fun (response_neutral_zero n) x
  · intro hx
    apply PiLp.ext
    intro s
    obtain ⟨hp, hr⟩ := (neutral_iff n x).mp hx s
    have he (z : ℤ) (v : Fibre n) (hv : (z : ℂ) • v = 0) : mask z • v = v := by
      by_cases hz : z = 0
      · simp [mask, hz]
      · have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz
        have hv' : v = 0 := (smul_eq_zero.mp hv).resolve_left hz'
        simp [hv']
    change blocks n (neutralComponent n) x s = _
    rw [blocks_apply]
    change mask (generatedWeight n (false, s)) • projection n (x s) +
      mask (generatedWeight n (true, s)) • residual n (x s) = _
    rw [he _ _ hp, he _ _ hr, HistoryPhaseProjection.full_reconstruction]

theorem neutral_range (n : ℕ) : LinearMap.range (neutralProjection n) = neutral n := by
  ext x
  rw [LinearMap.IsIdempotentElem.mem_range_iff (neutralProjection_idempotent n),
    neutralProjection_fixed_iff]

theorem neutralProjection_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (neutralProjection n) =
      (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) *
        (∑ s : Spin, (mask (generatedWeight n (false, s)) +
          n * mask (generatedWeight n (true, s)))) := by
  rw [neutralProjection, blocks_trace]
  simp only [neutralComponent, phaseBlock_trace]
  rw [Finset.mul_sum]

theorem neutral_trace_large {n : ℕ} (hn : 2 ≤ n) :
    LinearMap.trace ℂ (Space n) (neutralProjection n) =
      (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) := by
  rw [neutralProjection_trace]
  have hm (c : Bool) (s : Spin) : mask (generatedWeight n (c, s)) =
      if (c, s) = (false, .inr 0) then 1 else 0 := by
    simp only [mask, generated_zero_iff hn]
  simp [hm]

theorem neutral_trace_one :
    LinearMap.trace ℂ (Space 1) (neutralProjection 1) =
      (2 * Fintype.card (CompleteHistory.History 2) : ℂ) := by
  rw [neutralProjection_trace]
  norm_num [mask, generatedWeight, weight, relativeWeight, rightWeight,
    Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem neutral_finrank_large {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℂ (neutral n) = Fintype.card (CompleteHistory.History (n + 1)) := by
  have h := (LinearMap.IsIdempotentElem.isProj_range _
    (neutralProjection_idempotent n)).trace
  rw [neutral_range, neutral_trace_large hn] at h
  exact_mod_cast h.symm

theorem charged_quotient_finrank {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℂ (Space n ⧸ neutral n) =
      (4 * n + 3) * Fintype.card (CompleteHistory.History (n + 1)) := by
  have h := (neutral n).finrank_quotient_add_finrank
  rw [neutral_finrank_large hn, full_dimension] at h
  nlinarith

theorem response_sq_trace (n : ℕ) :
    LinearMap.trace ℂ (Space n) (generatedResponse n * generatedResponse n) =
      (2 * (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) * n * (n + 1) * (n + 2)) := by
  change LinearMap.trace ℂ (Space n) (blocks n (component n n 1) *
    blocks n (component n n 1)) = _
  rw [blocks_mul]
  have he (s : Spin) : component n n 1 s * component n n 1 s =
      HistoryRelativePhase.block n
        ((generatedWeight n (false, s) : ℂ) ^ 2, (generatedWeight n (true, s) : ℂ) ^ 2) := by
    unfold component
    rw [← map_mul]
    congr 1
    apply Prod.ext <;> simp [pow_two, generatedWeight]
  simp only [blocks_trace, he, phaseBlock_trace, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp [generatedWeight, weight, relativeWeight, rightWeight]
  ring

structure Conclusions : Prop where
  actual_neutral_projection : ∀ n x, neutralProjection n x = x ↔ x ∈ neutral n
  full_neutral_range : ∀ n, LinearMap.range (neutralProjection n) = neutral n
  neutral_rank : ∀ n, 2 ≤ n →
    Module.finrank ℂ (neutral n) = Fintype.card (CompleteHistory.History (n + 1))
  actual_charged_rank : ∀ n, 2 ≤ n → Module.finrank ℂ (Space n ⧸ neutral n) =
    (4 * n + 3) * Fintype.card (CompleteHistory.History (n + 1))
  complete_charge_capacity : ∀ n,
    LinearMap.trace ℂ (Space n) (generatedResponse n * generatedResponse n) =
      2 * (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) * n * (n + 1) * (n + 2)

theorem generated : Conclusions where
  actual_neutral_projection := neutralProjection_fixed_iff
  full_neutral_range := neutral_range
  neutral_rank := fun _ => neutral_finrank_large
  actual_charged_rank := fun _ => charged_quotient_finrank
  complete_charge_capacity := response_sq_trace

end GeneratedFoundations.Arithmetic.HistoryJointChargeQuotient
