module

public import GeneratedFoundations.Physical.SourceTTClosureBoundary

/-!
# The fixed-branch source domain and the implemented endpoint update

The actual endpoint routine first finds a scale at a specified positive
response level and then divides the radius by that scale. In the exact
homogeneous response model its update is constant: `c ↦ A / θ`. The
least-boundary property holds precisely when that supplied level is
`4/27`. This computation therefore verifies the implementation of an
endpoint rule, without deriving the rule from source evolution.

Every positive radius gives positive precisions in the original eight
branches, and every finite projection has its unique original Gaussian
state. Such existence alone is strictly weaker than membership in the
single-channel realization class. The comparison vertices and a physical
closure condition must consequently remain part of any source-level
identification of that class.

No physical admissibility predicate or new update rule is installed here.
The endpoint routine and the positive-precision source are compared on a
fixed content and frequency branch. Positivity of this precision family
does not assert that the active physical content stays fixed at all radii.
-/

@[expose] public section
noncomputable section
open MeasureTheory

namespace GeneratedFoundations.Physical.SourceTTNativeEndpoint

open Operations SourceTensorResponseEndpoint SourceTTResponseNormalization
open SourceTTClosureBoundary

/-! ## Exact reduction of the implemented scale-crossing update -/

/-- The fixed-branch readout at relative scale `t`. -/
def scaleResponse (A c t : ℝ) : ℝ := t * A / c

/-- The crossing scale in the existing routine, with its response level
kept as an explicit input. -/
def crossingScale (A θ c : ℝ) : ℝ := θ * c / A

/-- The radius update `c / t*` used after the crossing has been found. -/
def crossingUpdate (A θ c : ℝ) : ℝ := c / crossingScale A θ c

theorem crossing_scale_unique {A θ c t : ℝ}
    (hA : 0 < A) (hc : 0 < c) :
    scaleResponse A c t = θ ↔ t = crossingScale A θ c := by
  unfold scaleResponse crossingScale
  constructor
  · intro h
    apply (eq_div_iff hA.ne').2
    have he := (div_eq_iff hc.ne').1 h
    nlinarith
  · intro h
    rw [h]
    field_simp

theorem crossing_update_eq {A θ c : ℝ}
    (hA : 0 < A) (hθ : 0 < θ) (hc : 0 < c) :
    crossingUpdate A θ c = A / θ := by
  unfold crossingUpdate crossingScale
  field_simp [hA.ne', hθ.ne', hc.ne']

theorem crossing_update_idempotent {A θ c : ℝ}
    (hA : 0 < A) (hθ : 0 < θ) (hc : 0 < c) :
    crossingUpdate A θ (crossingUpdate A θ c) = crossingUpdate A θ c := by
  rw [crossing_update_eq hA hθ hc,
    crossing_update_eq hA hθ (div_pos hA hθ)]

theorem crossing_update_fixed_iff {A θ c : ℝ}
    (hA : 0 < A) (hθ : 0 < θ) (hc : 0 < c) :
    crossingUpdate A θ c = c ↔ A / c = θ := by
  rw [crossing_update_eq hA hθ hc]
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    apply (div_eq_iff hθ.ne').2
    have he := (div_eq_iff hc.ne').1 h
    nlinarith

/-- The implemented update selects the candidate least boundary exactly
for the existing prescribed threshold, rather than for every level. -/
theorem update_least_boundary_iff_level {A θ c : ℝ}
    (hA : 0 < A) (hθ : 0 < θ) (hc : 0 < c) :
    IsLeast {r : ℝ | Realizable A r} (crossingUpdate A θ c) ↔
      θ = (4 / 27 : ℝ) := by
  rw [crossing_update_eq hA hθ hc,
    least_realizable_iff_matching hA (div_pos hA hθ)]
  have he : A / (A / θ) = θ := by field_simp
  rw [he]

theorem implemented_update_selects_candidate_boundary {A c : ℝ}
    (hA : 0 < A) (hc : 0 < c) :
    IsLeast {r : ℝ | Realizable A r}
      (crossingUpdate A (4 / 27) c) :=
  (update_least_boundary_iff_level hA (by norm_num) hc).2 rfl

/-- Changing only the matching level changes the update's selected
radius, while leaving the complete fixed coefficient unchanged. -/
theorem distinct_levels_distinct_updates {A θ η c : ℝ}
    (hA : 0 < A) (hθ : 0 < θ) (hη : 0 < η) (hc : 0 < c)
    (hne : θ ≠ η) :
    crossingUpdate A θ c ≠ crossingUpdate A η c := by
  rw [crossing_update_eq hA hθ hc, crossing_update_eq hA hη hc]
  exact SourceTTEndpointBalance.distinct_matching_levels hA hθ hη hne

/-! ## The original Gaussian source on the same fixed branch -/

/-- The original precision after the homogeneous frequency change of
variables, before any endpoint matching. -/
def branchPrecision (c : ℝ) (i : Fin 8) (u : ℝ) : ℝ :=
  (u ^ 2 + (SourceTTGaussianCoefficient.branch i).1 +
    (SourceTTGaussianCoefficient.branch i).2.1) / c ^ 2

theorem branch_precision_pos {c : ℝ} (hc : 0 < c) (i : Fin 8) (u : ℝ) :
    0 < branchPrecision c i u := by
  obtain ⟨ha, _, hb, _⟩ := SourceTTGaussianCoefficient.branch_bounds i
  apply div_pos _ (sq_pos_of_pos hc)
  nlinarith [sq_nonneg u]

/-- Any finite retained projection, with all its repetitions of spectral
and colour labels, has its original centred Gaussian at every positive
radius. This statement does not assert physical endpoint closure. -/
theorem finite_source_exists_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ} (hc : 0 < c) (mode : ι → Fin 8) (u : ι → ℝ) :
    ∃! ν : Measure (FinitePrecisionGaussian.Space ι),
      ProbabilityTheory.IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      FinitePrecisionGaussian.precisionMatrix (fun i => branchPrecision c (mode i) (u i)) *
        FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  FinitePrecisionGaussian.law_existsUnique fun i => branch_precision_pos hc (mode i) (u i)

/-- Positivity of all the retained precisions is not the same condition
as realizability of the separate single-channel matching profile. -/
theorem source_precisions_exist_below_candidate_boundary :
    ∃ c : ℝ, 0 < c ∧
      (∀ (i : Fin 8) (u : ℝ), 0 < branchPrecision c i u) ∧
      ¬ Realizable SourceTTGaussianCoefficient.coefficient c := by
  let c := SourceTTGaussianCoefficient.radius / 2
  have hc : 0 < c := div_pos SourceTTGaussianCoefficient.radius_pos (by norm_num)
  refine ⟨c, hc, branch_precision_pos hc, ?_⟩
  rw [realizable_iff SourceTTGaussianCoefficient.coefficient_pos]
  change ¬ SourceTTGaussianCoefficient.radius ≤ c
  dsimp [c]
  linarith [SourceTTGaussianCoefficient.radius_pos]

/-- The original mass fractions are invariant under this homogeneous
radius change; it does not move them toward a maximizing split. -/
theorem mass_fraction_homothety (a b u : ℝ) {c : ℝ}
    (hc : 0 < c) (hp : 0 < u ^ 2 + a + b) :
    massFraction ((u ^ 2 + a) / c ^ 2) (b / c ^ 2) =
      massFraction (u ^ 2 + a) b := by
  unfold massFraction
  field_simp [hc.ne', hp.ne']

/-- Even a retained scalar mode has a nonmaximal mass fraction throughout
the same homogeneous path. No change of endpoint units removes this. -/
theorem retained_scalar_fraction_nonmaximal {c : ℝ} (hc : 0 < c) :
    massFraction ((1 : ℝ) / c ^ 2) ((3 / 4 : ℝ) / c ^ 2) = 3 / 7 ∧
      massFraction ((1 : ℝ) / c ^ 2) ((3 / 4 : ℝ) / c ^ 2) ≠ 1 / 3 := by
  have he : massFraction ((1 : ℝ) / c ^ 2) ((3 / 4 : ℝ) / c ^ 2) = 3 / 7 := by
    calc
      _ = massFraction (1 ^ 2 + 0) (3 / 4) := by
        convert! mass_fraction_homothety 0 (3 / 4) 1 hc (by norm_num) using 1
        norm_num
      _ = 3 / 7 := by norm_num [massFraction]
  constructor
  · exact he
  · rw [he]
    norm_num

end GeneratedFoundations.Physical.SourceTTNativeEndpoint
