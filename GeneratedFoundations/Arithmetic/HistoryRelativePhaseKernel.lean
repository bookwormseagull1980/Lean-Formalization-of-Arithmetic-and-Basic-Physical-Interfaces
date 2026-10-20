module

public import GeneratedFoundations.Arithmetic.HistoryRelativePhase

/-!
# Effective kernel of the generated relative phase

The invariant and detail projections are those obtained by averaging the
actual finite phase translations. For every nontrivial phase fibre the
detail trace is positive, and the primitive relative phase has precisely
the integral two-pi kernel. The trivial phase fibre is treated separately.
Thus effectiveness is established on the original space, without adding
a charged coordinate or prescribing a period.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryRelativePhaseKernel

open HistoryModuleRepresentation HistoryRelativePhase HistoryPhaseProjection

theorem residual_ne_zero {n : ℕ} (hn : 0 < n) :
    HistoryPhaseProjection.residual n ≠ 0 := by
  intro h
  have ht := residual_trace n
  rw [h, map_zero] at ht
  have hc : (Fintype.card (CompleteHistory.History (n + 1)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (CompleteHistory.History (n + 1)) ≠ 0)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  exact (mul_ne_zero hc hn') ht.symm

theorem flow_residual (n : ℕ) (t : ℝ) :
    flow n t * HistoryPhaseProjection.residual n =
      scalar 1 t • HistoryPhaseProjection.residual n := by
  change (scalar (-(n : ℝ)) t • projection n +
    scalar 1 t • HistoryPhaseProjection.residual n) * _ = _
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, projection_residual,
    residual_idempotent, smul_zero, zero_add]

theorem scalar_int_period (w k : ℤ) : scalar (w : ℝ) (k * (2 * Real.pi)) = 1 := by
  unfold scalar Operations.FinitePhaseFlow.phase
  convert Complex.exp_int_mul_two_pi_mul_I (w * k) using 1
  congr 1
  push_cast
  ring

theorem flow_eq_one_iff {n : ℕ} (hn : 0 < n) (t : ℝ) :
    flow n t = 1 ↔ ∃ k : ℤ, t = k * (2 * Real.pi) := by
  constructor
  · intro hf
    have hs : scalar 1 t • HistoryPhaseProjection.residual n =
        HistoryPhaseProjection.residual n := by rw [← flow_residual, hf, one_mul]
    have hz : (scalar 1 t - 1) • HistoryPhaseProjection.residual n = 0 := by
      rw [sub_smul, one_smul, hs, sub_self]
    have he : scalar 1 t = 1 :=
      sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (residual_ne_zero hn))
    have hex : Complex.exp (Complex.I * (t : ℂ)) = 1 := by
      simpa [scalar, Operations.FinitePhaseFlow.phase] using he
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hex
    exact ⟨k, by simpa using congrArg Complex.im hk⟩
  · rintro ⟨k, rfl⟩
    have h1 := scalar_int_period (-(n : ℤ)) k
    have h2 := scalar_int_period 1 k
    change block n (scalar (-(n : ℝ)) _, scalar 1 _) = 1
    have h1' : scalar (-(n : ℝ)) (k * (2 * Real.pi)) = 1 := by
      simpa using h1
    have h2' : scalar 1 (k * (2 * Real.pi)) = 1 := by simpa using h2
    rw [h1', h2']
    exact (block n).map_one

theorem projection_zero : projection 0 = 1 := by
  let : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  ext f ⟨h, a⟩
  simp [projection_apply, Subsingleton.elim a (default : ZMod 1)]
  rfl

theorem residual_zero : HistoryPhaseProjection.residual 0 = 0 := by
  rw [HistoryPhaseProjection.residual, projection_zero, sub_self]

theorem trivial_phase (t : ℝ) : flow 0 t = 1 := by
  simp [flow, block, projection_zero, residual_zero, scalar,
    Operations.FinitePhaseFlow.phase]

structure Conclusions : Prop where
  actual_detail_nonzero : ∀ n, 0 < n → HistoryPhaseProjection.residual n ≠ 0
  effective_kernel : ∀ n, 0 < n → ∀ t,
    flow n t = 1 ↔ ∃ k : ℤ, t = k * (2 * Real.pi)
  degenerate_fibre : ∀ t, flow 0 t = 1

theorem generated : Conclusions where
  actual_detail_nonzero := fun _ => residual_ne_zero
  effective_kernel := fun _ => flow_eq_one_iff
  degenerate_fibre := trivial_phase

end GeneratedFoundations.Arithmetic.HistoryRelativePhaseKernel
