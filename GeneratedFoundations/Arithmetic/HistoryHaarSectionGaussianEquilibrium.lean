module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianState
public import GeneratedFoundations.Operations.FinitePrecisionEquilibrium

/-!
# Stationarity of the actual arithmetic Gaussian section source

The equilibrium increment uses precisely the covariance of the original
realified section law. Both source sectors and both real quadratures
remain present. The full probability law is preserved, so every original
observation and its connected variance are preserved. Among Gaussian
states, the covariance fixed-point equation determines the same state
uniquely when the retention is nontrivial.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianEquilibrium

open HistoryHaarSectionGaussianState (RealIndex Space realPrecision realPrecision_pos law)
open Operations
local instance (N : ℕ) : DecidableEq (HistoryHaarSectionJointHessian.Index N) := Classical.decEq _

def equilibriumLaw (N : ℕ) (B u omega time : ℝ) : Measure (Space N B u) :=
  FinitePrecisionEquilibrium.mehlerLaw (realPrecision N B u) omega time

theorem original_source_equilibrium (N : ℕ) (B u : ℝ) {omega time : ℝ}
    (homega : 0 ≤ omega) (htime : 0 ≤ time) :
    equilibriumLaw N B u omega time = law N B u := by
  simpa only [equilibriumLaw, HistoryHaarSectionGaussianState.law] using
    FinitePrecisionEquilibrium.mehler_preserves_law
      (realPrecision N B u) homega htime

theorem all_source_expectations_preserved (N : ℕ) (B u : ℝ) {omega time : ℝ}
    (homega : 0 ≤ omega) (htime : 0 ≤ time) (f : Space N B u → ℝ) :
    (∫ x, f x ∂equilibriumLaw N B u omega time) = ∫ x, f x ∂law N B u := by
  rw [original_source_equilibrium N B u homega htime]

theorem connected_response_preserved (N : ℕ) (B u : ℝ) {omega time : ℝ}
    (homega : 0 ≤ omega) (htime : 0 ≤ time) (f g : Space N B u → ℝ) :
    cov[f, g; equilibriumLaw N B u omega time] = cov[f, g; law N B u] := by
  rw [original_source_equilibrium N B u homega htime]

theorem stationary_covariance_unique (N : ℕ) (B u : ℝ) {r : ℝ} (hr : r ^ 2 ≠ 1)
    (C : Matrix (RealIndex N B u) (RealIndex N B u) ℝ) :
    FinitePrecisionEquilibrium.covarianceUpdate (realPrecision N B u) r C = C ↔
      C = FinitePrecisionGaussian.covarianceMatrix (realPrecision N B u) :=
  FinitePrecisionEquilibrium.covariance_fixed_iff _ hr C

structure Conclusions : Prop where
  same_source_law : ∀ N B u omega time, 0 ≤ omega → 0 ≤ time →
    equilibriumLaw N B u omega time = law N B u
  every_observation : ∀ N B u omega time, 0 ≤ omega → 0 ≤ time →
    ∀ f : Space N B u → ℝ,
      (∫ x, f x ∂equilibriumLaw N B u omega time) = ∫ x, f x ∂law N B u
  unique_stationary_covariance : ∀ N B u r, r ^ 2 ≠ 1 →
    ∀ C : Matrix (RealIndex N B u) (RealIndex N B u) ℝ,
      FinitePrecisionEquilibrium.covarianceUpdate (realPrecision N B u) r C = C ↔
        C = FinitePrecisionGaussian.covarianceMatrix (realPrecision N B u)

theorem generated : Conclusions where
  same_source_law := fun N B u _ _ => original_source_equilibrium N B u
  every_observation := fun N B u _ _ => all_source_expectations_preserved N B u
  unique_stationary_covariance := fun N B u _ => stationary_covariance_unique N B u

end GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianEquilibrium
