module

public import GeneratedFoundations.Arithmetic.HistoryPhaseExactSequence
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Group.Int.Units

/-!
# The primitive relative response of the actual phase decomposition

The invariant and zero-average observation spaces are the complementary
spaces constructed from the generated phase average. Their dimensions are
`H` and `H*n`, where `H` is the actual history count at root `n+1`.
Consequently their primitive trace-free relative weights are `(-n,1)`, up
to simultaneous sign. The positive detail orientation fixes that sign.

Weights in comparison statements are integer competitors, not source
parameters. The generated response uses the derived weights. At root one
the detail space is zero; no faithful two-sector interpretation is asserted
there. The response and trace formulas still hold at that degenerate root.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryRelativeCharge

open CompleteHistory HistoryPhaseExactSequence

def PrimitivePair (a b : ℤ) : Prop :=
  ∀ d : ℤ, d ∣ a → d ∣ b → IsUnit d

def relativeResponse (n : ℕ) (a b : ℤ) : Module.End ℝ (Space n) :=
  (a : ℝ) • projection n + (b : ℝ) • residual n

theorem relativeResponse_on_invariant (n : ℕ) (a b : ℤ) (f : Space n)
    (hf : HistoryPhaseBundle.PhaseInvariant f) :
    relativeResponse n a b f = (a : ℝ) • f := by
  have hp : projection n f = f := by
    ext x
    exact HistoryPhaseBundle.phaseAverage_of_invariant f hf x
  have hr : residual n f = 0 := by
    change f - projection n f = 0
    rw [hp, sub_self]
  simp only [relativeResponse, LinearMap.add_apply, LinearMap.smul_apply,
    hp, hr, smul_zero, add_zero]

theorem relativeResponse_on_detail (n : ℕ) (a b : ℤ) (f : zeroMean n) :
    relativeResponse n a b f = (b : ℝ) • (f : Space n) := by
  have hp : projection n (f : Space n) = 0 := by
    ext x
    change HistoryPhaseBundle.phaseAverage (f : Space n) x.1 = 0
    exact congrFun f.property x.1
  have hr : residual n (f : Space n) = f := by
    change (f : Space n) - projection n f = f
    rw [hp, sub_zero]
  simp only [relativeResponse, LinearMap.add_apply, LinearMap.smul_apply,
    hp, hr, smul_zero, zero_add]

theorem relativeResponse_phase_covariant (n : ℕ) (a b : ℤ)
    (q : ZMod (n + 1)) (f : Space n) :
    relativeResponse n a b (fun x => f (HistoryPhaseBundle.translate q x)) =
      fun x => relativeResponse n a b f (HistoryPhaseBundle.translate q x) := by
  ext x
  change (a : ℝ) * HistoryPhaseBundle.phaseAverage
      (fun y => f (HistoryPhaseBundle.translate q y)) x.1 +
    (b : ℝ) * (f (HistoryPhaseBundle.translate q x) -
      HistoryPhaseBundle.phaseAverage (fun y => f (HistoryPhaseBundle.translate q y)) x.1) =
    (a : ℝ) * HistoryPhaseBundle.phaseAverage f x.1 +
      (b : ℝ) * (f (HistoryPhaseBundle.translate q x) - HistoryPhaseBundle.phaseAverage f x.1)
  rw [HistoryPhaseBundle.phaseAverage_translate]

theorem projection_trace (n : ℕ) :
    LinearMap.trace ℝ (Space n) (projection n) =
      (Fintype.card (History (n + 1)) : ℝ) := by
  rw [projection, LinearMap.trace_comp_comm', average_lift, LinearMap.trace_one]
  simp [HistorySpace, Module.finrank_fintype_fun_eq_card]

theorem residual_trace (n : ℕ) :
    LinearMap.trace ℝ (Space n) (residual n) =
      (Fintype.card (History (n + 1)) : ℝ) * n := by
  rw [HistoryPhaseExactSequence.residual, map_sub, LinearMap.trace_one,
    projection_trace, space_finrank]
  push_cast
  ring

theorem relativeResponse_trace (n : ℕ) (a b : ℤ) :
    LinearMap.trace ℝ (Space n) (relativeResponse n a b) =
      (Fintype.card (History (n + 1)) : ℝ) * ((a : ℝ) + n * (b : ℝ)) := by
  simp only [relativeResponse, map_add, map_smul, projection_trace,
    residual_trace, smul_eq_mul]
  ring

theorem relativeResponse_trace_zero_iff (n : ℕ) (a b : ℤ) :
    LinearMap.trace ℝ (Space n) (relativeResponse n a b) = 0 ↔
      a + (n : ℤ) * b = 0 := by
  rw [relativeResponse_trace, mul_eq_zero]
  have hH : (Fintype.card (History (n + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (History (n + 1)) ≠ 0)
  rw [or_iff_right hH]
  exact_mod_cast (Iff.rfl : (a : ℝ) + (n : ℝ) * (b : ℝ) = 0 ↔
    (a : ℝ) + (n : ℝ) * (b : ℝ) = 0)

theorem primitive_traceFree_iff (n : ℕ) (a b : ℤ) :
    PrimitivePair a b ∧ a + (n : ℤ) * b = 0 ↔
      (a = -(n : ℤ) ∧ b = 1) ∨ (a = n ∧ b = -1) := by
  constructor
  · rintro ⟨hp, ht⟩
    have hb : IsUnit b := hp b ⟨-(n : ℤ), by linarith⟩ dvd_rfl
    rcases Int.isUnit_iff.mp hb with hb | hb
    · left
      exact ⟨by rw [hb] at ht; linarith, hb⟩
    · right
      exact ⟨by rw [hb] at ht; linarith, hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨?_, by ring⟩
      intro d _ hd
      exact isUnit_of_dvd_one hd
    · refine ⟨?_, by ring⟩
      intro d _ hd
      exact isUnit_of_dvd_unit hd (Int.isUnit_iff.mpr (Or.inr rfl))

theorem oriented_relative_unique (n : ℕ) {a b : ℤ} (hp : PrimitivePair a b)
    (ht : LinearMap.trace ℝ (Space n) (relativeResponse n a b) = 0) (hb : 0 < b) :
    a = -(n : ℤ) ∧ b = 1 := by
  rcases (primitive_traceFree_iff n a b).mp
      ⟨hp, (relativeResponse_trace_zero_iff n a b).mp ht⟩ with h | h
  · exact h
  · exfalso
    linarith [h.2]

theorem oriented_relative_existsUnique (n : ℕ) :
    ∃! p : ℤ × ℤ, PrimitivePair p.1 p.2 ∧
      LinearMap.trace ℝ (Space n) (relativeResponse n p.1 p.2) = 0 ∧ 0 < p.2 := by
  refine ⟨(-(n : ℤ), 1), ?_, ?_⟩
  · refine ⟨?_, (relativeResponse_trace_zero_iff n _ _).mpr (by ring), by norm_num⟩
    intro d _ hd
    exact isUnit_of_dvd_one hd
  · intro p hp
    exact Prod.ext (oriented_relative_unique n hp.1 hp.2.1 hp.2.2).1
      (oriented_relative_unique n hp.1 hp.2.1 hp.2.2).2

/-- The mixed term vanishes by the proved phase-average orthogonality under
the actual generated probability law, not by dropping matrix coefficients. -/
theorem relativeResponse_energy (n : ℕ) (a b : ℤ) (f : Space n) :
    HistoryPhaseBundle.energy (relativeResponse n a b f) =
      (a : ℝ) ^ 2 * HistoryPhaseBundle.energy (projection n f) +
        (b : ℝ) ^ 2 * HistoryPhaseBundle.energy (residual n f) := by
  calc
    _ = (a : ℝ) ^ 2 * HistoryPhaseBundle.energy (projection n f) +
        (b : ℝ) ^ 2 * HistoryPhaseBundle.energy (residual n f) +
          2 * (a : ℝ) * (b : ℝ) *
            HistoryPhaseBundle.mean (fun x =>
              HistoryPhaseBundle.phaseProjection f x * HistoryPhaseBundle.phaseResidual f x) := by
      simp only [HistoryPhaseBundle.energy, HistoryPhaseBundle.mean_eq_probability_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      change HistoryPhaseBundle.probability x *
          ((a : ℝ) * HistoryPhaseBundle.phaseProjection f x +
            (b : ℝ) * HistoryPhaseBundle.phaseResidual f x) ^ 2 = _
      simp only [projection_apply, residual_apply]
      ring
    _ = _ := by rw [HistoryPhaseBundle.projection_residual_orthogonal, mul_zero, add_zero]

def generatedResponse (n : ℕ) : Module.End ℝ (Space n) :=
  relativeResponse n (-(n : ℤ)) 1

theorem generatedResponse_trace (n : ℕ) :
    LinearMap.trace ℝ (Space n) (generatedResponse n) = 0 := by
  apply (relativeResponse_trace_zero_iff n _ _).mpr
  ring

theorem generatedResponse_unique (n : ℕ) (a b : ℤ)
    (hp : PrimitivePair a b)
    (ht : LinearMap.trace ℝ (Space n) (relativeResponse n a b) = 0) (hb : 0 < b) :
    relativeResponse n a b = generatedResponse n := by
  obtain ⟨rfl, rfl⟩ := oriented_relative_unique n hp ht hb
  rfl

structure Conclusions : Prop where
  exact_trace : ∀ n a b,
    LinearMap.trace ℝ (Space n) (relativeResponse n a b) =
      (Fintype.card (History (n + 1)) : ℝ) * ((a : ℝ) + n * (b : ℝ))
  primitive_classification : ∀ (n : ℕ) (a b : ℤ),
    PrimitivePair a b ∧ a + (n : ℤ) * b = 0 ↔
      (a = -(n : ℤ) ∧ b = 1) ∨ (a = n ∧ b = -1)
  canonical_trace_zero : ∀ n,
    LinearMap.trace ℝ (Space n) (generatedResponse n) = 0
  unique_oriented_response : ∀ n a b, PrimitivePair a b →
    LinearMap.trace ℝ (Space n) (relativeResponse n a b) = 0 → 0 < b →
      relativeResponse n a b = generatedResponse n
  full_weighted_energy : ∀ n a b (f : Space n),
    HistoryPhaseBundle.energy (relativeResponse n a b f) =
      (a : ℝ) ^ 2 * HistoryPhaseBundle.energy (projection n f) +
        (b : ℝ) ^ 2 * HistoryPhaseBundle.energy (residual n f)

theorem generated : Conclusions where
  exact_trace := relativeResponse_trace
  primitive_classification := primitive_traceFree_iff
  canonical_trace_zero := generatedResponse_trace
  unique_oriented_response := generatedResponse_unique
  full_weighted_energy := relativeResponse_energy

end GeneratedFoundations.Arithmetic.HistoryRelativeCharge
