module

public import GeneratedFoundations.Operations.FinitePrecisionEquilibrium
public import GeneratedFoundations.Physical.SourceTTNativeEndpoint

/-!
# Closure under the existing source equilibrium composition

The original source update preserves a prescribed Gaussian covariance by
an independent Gaussian increment. Here it is applied to every finite
projection of the actual retained precision family. All joint source
moments, including the quadratic-score variance used in the TT readout,
are preserved. This is stronger than mere existence of a Gaussian state.

The computed closure class is closure under this equilibrium update. It
is not declared to be a physical endpoint-admissibility predicate. Each
radius has its own prescribed source covariance and corresponding
equilibrium kernel. The result does not give different stationary laws
for one fixed kernel, nor extend the active-content branch to all radii.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory

namespace GeneratedFoundations.Physical.SourceTTEquilibriumClosure

open Operations SourceTTNativeEndpoint SourceTTClosureBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourcePrecision (c : ℝ) (mode : ι → Fin 8) (u : ι → ℝ) : ι → ℝ :=
  fun i => branchPrecision c (mode i) (u i)

def sourceLaw (c : ℝ) (mode : ι → Fin 8) (u : ι → ℝ) :
    Measure (FinitePrecisionGaussian.Space ι) :=
  FinitePrecisionGaussian.law (sourcePrecision c mode u)

def equilibriumLaw (c : ℝ) (mode : ι → Fin 8) (u : ι → ℝ)
    (omega : ι → ℝ) (time : ℝ) : Measure (FinitePrecisionGaussian.Space ι) :=
  FinitePrecisionEquilibrium.coordinateMehlerLaw (sourcePrecision c mode u) omega time

theorem original_source_equilibrium {c : ℝ} (hc : 0 < c)
    (mode : ι → Fin 8) (u : ι → ℝ)
    {omega : ι → ℝ} {time : ℝ} (homega : ∀ i, 0 ≤ omega i) (htime : 0 ≤ time) :
    equilibriumLaw c mode u omega time = sourceLaw c mode u :=
  FinitePrecisionEquilibrium.coordinate_mehler_preserves_law
    (fun i => branch_precision_pos hc (mode i) (u i)) omega homega htime

/-- Every original observable has its same expectation after the original
joint equilibrium update; no radial substitution is made. -/
theorem all_source_expectations_preserved {c : ℝ} (hc : 0 < c)
    (mode : ι → Fin 8) (u : ι → ℝ)
    {omega : ι → ℝ} {time : ℝ} (homega : ∀ i, 0 ≤ omega i) (htime : 0 ≤ time)
    (f : FinitePrecisionGaussian.Space ι → ℝ) :
    (∫ x, f x ∂equilibriumLaw c mode u omega time) =
      ∫ x, f x ∂sourceLaw c mode u := by
  rw [original_source_equilibrium hc mode u homega htime]

/-- In particular the same update preserves the connected kinetic-score
response used by the original TT coefficient. -/
theorem tt_score_variance_preserved {c : ℝ} (hc : 0 < c)
    (mode : ι → Fin 8) (u q2 : ι → ℝ)
    {omega : ι → ℝ} {time : ℝ} (homega : ∀ i, 0 ≤ omega i) (htime : 0 ≤ time) :
    Var[FinitePrecisionGaussian.score q2; equilibriumLaw c mode u omega time] =
      Var[FinitePrecisionGaussian.score q2; sourceLaw c mode u] := by
  rw [original_source_equilibrium hc mode u homega htime]

/-- Positive retained precision together with exact stationarity under
the existing independent equilibrium composition, for every finite
projection. This definition contains no response threshold. -/
def FiniteEquilibriumClosed (c : ℝ) : Prop :=
  0 < c ∧ ∀ (n : ℕ) (mode : Fin n → Fin 8) (u : Fin n → ℝ),
    (∀ i, 0 < sourcePrecision c mode u i) ∧
    ∀ (omega : Fin n → ℝ) (time : ℝ), (∀ i, 0 ≤ omega i) → 0 ≤ time →
      equilibriumLaw c mode u omega time = sourceLaw c mode u

theorem finite_equilibrium_closed_iff (c : ℝ) : FiniteEquilibriumClosed c ↔ 0 < c := by
  constructor
  · exact And.left
  · intro hc
    refine ⟨hc, ?_⟩
    intro n mode u
    exact ⟨fun i => branch_precision_pos hc (mode i) (u i),
      fun _ _ homega htime => original_source_equilibrium hc mode u homega htime⟩

theorem finite_equilibrium_closed_radii :
    {c : ℝ | FiniteEquilibriumClosed c} = Set.Ioi (0 : ℝ) := by
  ext c
  exact finite_equilibrium_closed_iff c

/-- A state may be closed under the actual equilibrium composition and
fail the separate split-response realization condition. -/
theorem equilibrium_closed_outside_realization :
    ∃ c : ℝ, FiniteEquilibriumClosed c ∧
      ¬ Realizable SourceTTGaussianCoefficient.coefficient c := by
  obtain ⟨c, hc, _, hnot⟩ := source_precisions_exist_below_candidate_boundary
  exact ⟨c, (finite_equilibrium_closed_iff c).2 hc, hnot⟩

/-- The comparison can be made inside any allowed open branch interval
containing the candidate boundary. It need not use a radius outside that
interval. The interval bounds themselves remain explicit hypotheses. -/
theorem equilibrium_closed_below_boundary_in_interval {lo hi : ℝ}
    (hlo : 0 < lo) (hbelow : lo < SourceTTGaussianCoefficient.radius)
    (habove : SourceTTGaussianCoefficient.radius ≤ hi) :
    ∃ c ∈ Set.Ioo lo hi, FiniteEquilibriumClosed c ∧
      ¬ Realizable SourceTTGaussianCoefficient.coefficient c := by
  let c := (lo + SourceTTGaussianCoefficient.radius) / 2
  have hloc : lo < c := by dsimp [c]; linarith
  have hcr : c < SourceTTGaussianCoefficient.radius := by dsimp [c]; linarith
  have hc : 0 < c := lt_trans hlo hloc
  refine ⟨c, ⟨hloc, lt_of_lt_of_le hcr habove⟩,
    (finite_equilibrium_closed_iff c).2 hc, ?_⟩
  rw [realizable_iff SourceTTGaussianCoefficient.coefficient_pos]
  exact not_le.mpr hcr

theorem equilibrium_closure_not_realization :
    ¬ ∀ c : ℝ, FiniteEquilibriumClosed c ↔
      Realizable SourceTTGaussianCoefficient.coefficient c := by
  intro h
  obtain ⟨c, hclosed, hnot⟩ := equilibrium_closed_outside_realization
  exact hnot ((h c).1 hclosed)

/-! ## The existing homogeneous ladder feedback -/

/-- The compact ladder has vertex `c^4/D` and source response `J/c^4`.
Its unit-feedback condition, combined with source equilibrium, fixes
`J=D`; it gives no additional radius condition. This is an identity for
those actual homogeneous factors, not a replacement endpoint rule. -/
theorem equilibrium_and_feedback_iff (J D c : ℝ) (hD : D ≠ 0) :
    (FiniteEquilibriumClosed c ∧ (c ^ 4 / D) * (J / c ^ 4) = 1) ↔
      (0 < c ∧ J = D) := by
  constructor
  · rintro ⟨hclosed, hfeedback⟩
    have hc := (finite_equilibrium_closed_iff c).1 hclosed
    rw [SourceTTEndpointBalance.feedback_scale_cancellation J D c hD hc.ne'] at hfeedback
    exact ⟨hc, (div_eq_one_iff_eq hD).1 hfeedback⟩
  · rintro ⟨hc, hJD⟩
    refine ⟨(finite_equilibrium_closed_iff c).2 hc, ?_⟩
    rw [SourceTTEndpointBalance.feedback_scale_cancellation J D c hD hc.ne', hJD,
      div_self hD]

/-- At a fixed feedback-critical deformation, every positive member of
the retained radius family is closed under both displayed conditions. -/
theorem feedback_critical_radii (J D : ℝ) (hD : D ≠ 0) (hJD : J = D) :
    {c : ℝ | FiniteEquilibriumClosed c ∧ (c ^ 4 / D) * (J / c ^ 4) = 1} =
      Set.Ioi (0 : ℝ) := by
  ext c
  rw [Set.mem_ofPred_eq, equilibrium_and_feedback_iff J D c hD]
  simp only [hJD, and_true, Set.mem_Ioi]

/-- A common Gaussian equilibrium and a homogeneous unit ladder feedback
can both hold below the single-channel response-realization boundary. -/
theorem equilibrium_feedback_outside_realization (J D : ℝ)
    (hD : D ≠ 0) (hJD : J = D) :
    ∃ c : ℝ, (FiniteEquilibriumClosed c ∧ (c ^ 4 / D) * (J / c ^ 4) = 1) ∧
      ¬ Realizable SourceTTGaussianCoefficient.coefficient c := by
  obtain ⟨c, hclosed, hnot⟩ := equilibrium_closed_outside_realization
  have hc := (finite_equilibrium_closed_iff c).1 hclosed
  exact ⟨c, (equilibrium_and_feedback_iff J D c hD).2 ⟨hc, hJD⟩, hnot⟩

end GeneratedFoundations.Physical.SourceTTEquilibriumClosure
