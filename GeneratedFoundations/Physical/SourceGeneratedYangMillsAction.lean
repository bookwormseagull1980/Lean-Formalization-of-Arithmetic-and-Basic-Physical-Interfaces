module

public import GeneratedFoundations.Physical.SourceFourDimensionalYangMills
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The source-generated Yang--Mills action

The generated four-dimensional colour curvature, its trace normalization, the
unique condensed response and the projective coclosed spectrum are assembled
here.  The local action density retains the nonlinear curvature.  The finite
spectral action is a canonical one-coordinate-per-shell witness for the same
generated eigenvalue law; the complete branches, multiplicities and colours
are retained by `SourceGeneratedYangMillsFullReduction`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsAction

open SourceConformalResponse SourceInternalYangMillsResponse
open SourceFourDimensionalYangMills SourceGeneratedYangMillsGap

/-- The unique positive condensed coordinate selected by the generated
feedback at radius `L`. -/
noncomputable def condensedAmplitude (L : ℝ) (hL : criticalRadius < L) : ℝ :=
  Classical.choose (existsUnique_generatedYangMillsGap hL)

theorem condensedAmplitude_spec (L : ℝ) (hL : criticalRadius < L) :
    0 < condensedAmplitude L hL ∧
    completeResponse (condensedAmplitude L hL) = generatedTarget L ∧
    0 < generatedYangMillsGapSq L (condensedAmplitude L hL) :=
  (Classical.choose_spec (existsUnique_generatedYangMillsGap hL)).1

theorem condensedAmplitude_unique (L : ℝ) (hL : criticalRadius < L)
    {z : ℝ} (hz : 0 < z)
    (hresponse : completeResponse z = generatedTarget L) :
    z = condensedAmplitude L hL := by
  exact (Classical.choose_spec (existsUnique_generatedYangMillsGap hL)).2 z
    ⟨hz, hresponse, generatedYangMillsGapSq_pos
      (criticalRadius_pos.trans hL) hz⟩

/-- Curvature density for the matrix connection presentation used by local
gauge transformations. -/
def matrixCurvatureDensity (A : MatrixConnectionJet) : ℝ :=
  ∑ μ, ∑ ν, colourQuadratic (matrixCurvature A μ ν)

/-- The generated local action density.  The gauge part is the full nonlinear
curvature density; the radial part is the normalized Hessian at the generated
condensed coordinate. -/
def localActionDensity (z radial : ℝ) (A : MatrixConnectionJet) : ℝ :=
  (1 / 2 : ℝ) * matrixCurvatureDensity A +
    (1 / 2 : ℝ) * normalizedRadialMassSq z * radial ^ 2

theorem localActionDensity_gauge_invariant (z radial : ℝ)
    (q : LocalColourGaugeTwoJet) (A : MatrixConnectionJet) :
    localActionDensity z radial (transformMatrixConnectionJet q A) =
      localActionDensity z radial A := by
  unfold localActionDensity matrixCurvatureDensity
  rw [localQuadraticDensity_gauge_invariant]

theorem localActionDensity_generated_nonneg {z : ℝ} (hz : 0 < z)
    (radial : ℝ) (A : ColourConnectionJet) :
    0 ≤ localActionDensity z radial (colourMatrixConnectionJet A) := by
  unfold localActionDensity matrixCurvatureDensity
  rw [show (∑ μ, ∑ ν,
      colourQuadratic (matrixCurvature (colourMatrixConnectionJet A) μ ν)) =
      euclideanCurvatureDensity A by rfl]
  exact add_nonneg
    (mul_nonneg (by norm_num) (euclideanCurvatureDensity_nonneg A))
    (mul_nonneg (mul_nonneg (by norm_num)
      (normalizedRadialMassSq_pos hz).le) (sq_nonneg radial))

/-- A finite radial/coclosed shell witness through cutoff `N`.  Its
`i`-th coclosed coordinate is the positive odd RP3 shell
`coclosedShellDegree i`; the cutoff is universally quantified and does not
enter any coercivity constant.  Branch, polarization and colour multiplicities
are intentionally suppressed here and restored in the complete response core. -/
structure SpectralConfiguration (N : ℕ) where
  radial : ℝ
  coclosed : Fin N → ℝ

namespace SpectralConfiguration

def zero (N : ℕ) : SpectralConfiguration N :=
  ⟨0, fun _ => 0⟩

def normSq {N : ℕ} (x : SpectralConfiguration N) : ℝ :=
  x.radial ^ 2 + ∑ i, x.coclosed i ^ 2

theorem normSq_nonneg {N : ℕ} (x : SpectralConfiguration N) :
    0 ≤ normSq x := by
  unfold normSq
  positivity

theorem normSq_eq_zero_iff {N : ℕ} (x : SpectralConfiguration N) :
    normSq x = 0 ↔ x = zero N := by
  constructor
  · intro h
    unfold normSq at h
    have hr : x.radial = 0 := by
      have hs : x.radial ^ 2 = 0 := by
        have hsum : 0 ≤ ∑ i, x.coclosed i ^ 2 := by positivity
        nlinarith [sq_nonneg x.radial]
      exact sq_eq_zero_iff.mp hs
    have hc : ∀ i, x.coclosed i = 0 := by
      intro i
      have hsum : ∑ j, x.coclosed j ^ 2 = 0 := by
        rw [hr] at h
        simpa using h
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (x.coclosed j))).mp hsum i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hi
    cases x
    simp only [zero] at hr ⊢
    congr
    funext i
    exact hc i
  · rintro rfl
    simp [normSq, zero]

end SpectralConfiguration

/-- Canonical generated quadratic action on the finite shell witness. -/
def spectralAction {N : ℕ} (L z : ℝ)
    (x : SpectralConfiguration N) : ℝ :=
  (1 / 2 : ℝ) * normalizedRadialMassSq z * x.radial ^ 2 +
    (1 / 2 : ℝ) * ∑ i,
      coclosedMassIndex L z (coclosedShellDegree i.1) * x.coclosed i ^ 2

theorem spectralAction_nonneg {N : ℕ} {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) (x : SpectralConfiguration N) :
    0 ≤ spectralAction L z x := by
  unfold spectralAction
  apply add_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num)
      (normalizedRadialMassSq_pos hz).le) (sq_nonneg x.radial)
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (coclosedMassIndex_pos hL hz (coclosedShellDegree i.1)).le
        (sq_nonneg (x.coclosed i)))

/-- Bundled action interface. -/
structure Properties : Prop where
  unique_condensate : ∀ L (hL : criticalRadius < L),
    0 < condensedAmplitude L hL ∧
    completeResponse (condensedAmplitude L hL) = generatedTarget L
  local_gauge_invariance : ∀ z radial q A,
    localActionDensity z radial (transformMatrixConnectionJet q A) =
      localActionDensity z radial A
  generated_local_nonnegative : ∀ {z}, 0 < z → ∀ radial A,
    0 ≤ localActionDensity z radial (colourMatrixConnectionJet A)
  spectral_nonnegative : ∀ {N L z}, 0 < L → 0 < z →
    ∀ x : SpectralConfiguration N, 0 ≤ spectralAction L z x

theorem properties : Properties where
  unique_condensate := fun L hL =>
    ⟨(condensedAmplitude_spec L hL).1, (condensedAmplitude_spec L hL).2.1⟩
  local_gauge_invariance := localActionDensity_gauge_invariant
  generated_local_nonnegative := fun hz radial A =>
    localActionDensity_generated_nonneg hz radial A
  spectral_nonnegative := fun hL hz x => spectralAction_nonneg hL hz x

end GeneratedFoundations.Physical.SourceGeneratedYangMillsAction
