module

public import GeneratedFoundations.Arithmetic.HistoryObservation
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Unit-rate exchange along the actual history reflection

Reflection already acts on the complete source and preserves its weights.
The unit-rate exchange generator `I - reflection` consequently has the
source-even and source-odd spectral projections constructed there.  Its
semigroup is computed from those projections.  The conserved expectation,
positivity and exact energy loss are proved for the actual history law.

The rate is calibrated to one, just as reverse splitting is calibrated in
`CompleteHistoryDynamics`.  Uniqueness among all source-preserving dynamics
is not inferred from stationarity.  This exchange acts inside each fixed
root fibre; the separate three-species reaction incidence remains explicit
in `HistoryReactionOperator`.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.HistoryReflectionFlow

open Arithmetic.CompleteHistory Arithmetic.CompleteHistoryGeometry Arithmetic.HistoryObservation

def generator {k : ℕ} (f : History k → ℝ) (h : History k) : ℝ :=
  f h - f (reflect h)

def flow {k : ℕ} (t : ℝ) (f : History k → ℝ) (h : History k) : ℝ :=
  evenPart f h + Real.exp (-2 * t) * oddPart f h

@[simp] theorem flow_zero {k : ℕ} (f : History k → ℝ) : flow 0 f = f := by
  funext h
  simpa [flow] using congrFun (reconstruct f) h

theorem flow_even {k : ℕ} (t : ℝ) (f : History k → ℝ) :
    evenPart (flow t f) = evenPart f := by
  funext h
  simp only [evenPart, flow, evenPart, oddPart, reflect_involutive]
  ring

theorem flow_odd {k : ℕ} (t : ℝ) (f : History k → ℝ) :
    oddPart (flow t f) = fun h => Real.exp (-2 * t) * oddPart f h := by
  funext h
  simp only [oddPart, flow, evenPart, oddPart, reflect_involutive]
  ring

theorem flow_add {k : ℕ} (s t : ℝ) (f : History k → ℝ) :
    flow s (flow t f) = flow (s + t) f := by
  funext h
  simp only [flow, flow_even, flow_odd]
  rw [show -2 * (s + t) = -2 * s + -2 * t by ring, Real.exp_add]
  ring

theorem flow_convex {k : ℕ} (t : ℝ) (f : History k → ℝ) (h : History k) :
    flow t f h = (1 + Real.exp (-2 * t)) / 2 * f h +
      (1 - Real.exp (-2 * t)) / 2 * f (reflect h) := by
  simp only [flow, evenPart, oddPart]
  ring

theorem flow_nonneg {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (f : History k → ℝ)
    (hf : ∀ h, 0 ≤ f h) (h : History k) : 0 ≤ flow t f h := by
  rw [flow_convex]
  have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact add_nonneg
    (mul_nonneg (by positivity) (hf h))
    (mul_nonneg (div_nonneg (sub_nonneg.mpr he) (by norm_num)) (hf (reflect h)))

theorem flow_mean {k : ℕ} (t : ℝ) (f : History k → ℝ) :
    mean (flow t f) = mean f := by
  change mean (fun h => evenPart f h + Real.exp (-2 * t) * oddPart f h) = mean f
  rw [mean_add, mean_mul, even_mean, odd_mean_zero, mul_zero, add_zero]

theorem energy_scaled {k : ℕ} (c : ℝ) (f : History k → ℝ) :
    energy (fun h => c * f h) = c ^ 2 * energy f := by
  simp only [energy, pairing, mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem flow_energy {k : ℕ} (t : ℝ) (f : History k → ℝ) :
    energy (flow t f) = energy (evenPart f) +
      Real.exp (-4 * t) * energy (oddPart f) := by
  rw [energy_decomposition, flow_even, flow_odd, energy_scaled]
  have he : Real.exp (-2 * t) ^ 2 = Real.exp (-4 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]

theorem flow_energy_le {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (f : History k → ℝ) :
    energy (flow t f) ≤ energy f := by
  rw [flow_energy, energy_decomposition f]
  have he : Real.exp (-4 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hn := energy_nonneg (oddPart f)
  nlinarith

theorem flow_hasDerivAt {k : ℕ} (t : ℝ) (f : History k → ℝ) (h : History k) :
    HasDerivAt (fun s => flow s f h) (-2 * Real.exp (-2 * t) * oddPart f h) t := by
  convert
    (hasDerivAt_const t (evenPart f h)).add
      ((((hasDerivAt_id t).const_mul (-2)).exp).mul_const (oddPart f h)) using 1
  · rfl
  · simp only [id_eq]
    ring

structure Conclusions : Prop where
  semigroup : ∀ {k : ℕ} (s t : ℝ) (f : History k → ℝ), flow s (flow t f) = flow (s + t) f
  initial_value : ∀ {k : ℕ} (f : History k → ℝ), flow 0 f = f
  source_conservation : ∀ {k : ℕ} (t : ℝ) (f : History k → ℝ), mean (flow t f) = mean f
  exact_dissipation : ∀ {k : ℕ} (t : ℝ) (f : History k → ℝ),
    energy (flow t f) = energy (evenPart f) + Real.exp (-4 * t) * energy (oddPart f)
  contraction : ∀ {k : ℕ} (t : ℝ), 0 ≤ t → ∀ (f : History k → ℝ),
    energy (flow t f) ≤ energy f

theorem generated : Conclusions where
  semigroup := flow_add
  initial_value := flow_zero
  source_conservation := flow_mean
  exact_dissipation := flow_energy
  contraction := flow_energy_le

end GeneratedFoundations.Analysis.HistoryReflectionFlow
