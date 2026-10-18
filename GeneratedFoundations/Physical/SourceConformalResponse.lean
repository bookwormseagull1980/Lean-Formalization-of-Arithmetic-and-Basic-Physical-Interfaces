module

public import GeneratedFoundations.Physical.SourceRP3FieldSpectrum
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The source conformal restoring response

The even scalar shells of the actual generated projective spectrum determine
the two dimensionless sequences

`c_j = (2j+1)^2 - 1/4` and `d_j = (2j+1)^2`.

This file begins the scalar-response layer directly from those shells.  No
field spectrum, coupling, reference radius, kinetic coefficient or mass gap is
an input.  The finite responses below are exact rational functions of the
generated shell data; their positivity, strict monotonicity and positive
curvature are proved before passage to the complete tower.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open GeneratedFoundations.Physical.SourceRP3FieldSpectrum

namespace GeneratedFoundations.Physical.SourceConformalResponse

/-- Odd coordinate of the `j`-th projective scalar shell. -/
def oddCoordinate (j : ℕ) : ℝ := 2 * (j : ℝ) + 1

/-- Dimensionless conformal eigenvalue of the `j`-th even scalar shell. -/
def conformalIndex (j : ℕ) : ℝ := oddCoordinate j ^ 2 - 1 / 4

/-- Multiplicity of the same generated shell. -/
def conformalMultiplicity (j : ℕ) : ℝ := oddCoordinate j ^ 2

theorem oddCoordinate_pos (j : ℕ) : 0 < oddCoordinate j := by
  unfold oddCoordinate
  positivity

theorem conformalMultiplicity_pos (j : ℕ) :
    0 < conformalMultiplicity j := by
  unfold conformalMultiplicity
  exact sq_pos_of_pos (oddCoordinate_pos j)

theorem conformalIndex_pos (j : ℕ) : 0 < conformalIndex j := by
  have hj : 1 ≤ oddCoordinate j := by
    unfold oddCoordinate
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  unfold conformalIndex
  nlinarith

theorem succ_le_oddCoordinate (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) ≤ oddCoordinate j := by
  simp only [oddCoordinate, Nat.cast_add, Nat.cast_one]
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

theorem succ_square_le_multiplicity (j : ℕ) :
    (((j + 1 : ℕ) : ℝ) ^ 2) ≤ conformalMultiplicity j := by
  unfold conformalMultiplicity
  nlinarith [succ_le_oddCoordinate j, oddCoordinate_pos j]

theorem three_quarters_multiplicity_le_index (j : ℕ) :
    (3 / 4 : ℝ) * conformalMultiplicity j ≤ conformalIndex j := by
  have hm : 1 ≤ conformalMultiplicity j := by
    unfold conformalMultiplicity
    have hsucc : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    have hone : (1 : ℝ) ≤ oddCoordinate j := hsucc.trans (succ_le_oddCoordinate j)
    have hs : (1 : ℝ) * 1 ≤ oddCoordinate j * oddCoordinate j :=
      mul_self_le_mul_self (by norm_num) hone
    simpa only [one_mul, pow_two] using hs
  unfold conformalIndex conformalMultiplicity at hm ⊢
  nlinarith

/-- The response shell is not a second spectrum: it is the actual even scalar
Casimir shifted by the conformal curvature term. -/
theorem conformalIndex_eq_scalar_shift (j : ℕ) :
    conformalIndex j = scalarCasimir (2 * j) + 3 / 4 := by
  simp only [conformalIndex, oddCoordinate, scalarCasimir, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

theorem conformalMultiplicity_eq_scalar (j : ℕ) :
    conformalMultiplicity j = scalarMultiplicity (2 * j) := by
  simp only [conformalMultiplicity, oddCoordinate, scalarMultiplicity,
    Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

/-- One shell of the dimensionless restoring response. -/
def responseTerm (j : ℕ) (z : ℝ) : ℝ :=
  conformalMultiplicity j * z /
    (conformalIndex j * (conformalIndex j + z))

/-- One shell of the radial curvature response. -/
def curvatureTerm (j : ℕ) (z : ℝ) : ℝ :=
  conformalMultiplicity j / (conformalIndex j + z) ^ 2

@[simp] theorem responseTerm_zero (j : ℕ) : responseTerm j 0 = 0 := by
  simp [responseTerm]

theorem responseTerm_nonneg (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ responseTerm j z := by
  exact div_nonneg (mul_nonneg (conformalMultiplicity_pos j).le hz)
    (mul_nonneg (conformalIndex_pos j).le
      (add_nonneg (conformalIndex_pos j).le hz))

theorem curvatureTerm_pos (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 < curvatureTerm j z := by
  exact div_pos (conformalMultiplicity_pos j)
    (sq_pos_of_pos (add_pos_of_pos_of_nonneg (conformalIndex_pos j) hz))

/-- Uniform `p`-series majorant for every nonnegative curvature shell. -/
theorem curvatureTerm_le_pseries (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    curvatureTerm j z ≤
      (16 / 9 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 2) := by
  let p : ℝ := ((j + 1 : ℕ) : ℝ)
  let d : ℝ := conformalMultiplicity j
  let c : ℝ := conformalIndex j
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hd : 0 < d := by simpa [d] using conformalMultiplicity_pos j
  have hc : 0 < c := by simpa [c] using conformalIndex_pos j
  have hpd : p ^ 2 ≤ d := by simpa [p, d] using succ_square_le_multiplicity j
  have hcd : (3 / 4 : ℝ) * d ≤ c := by
    simpa [c, d] using three_quarters_multiplicity_le_index j
  have hcz : c ≤ c + z := by linarith
  have hcross : 9 * p ^ 2 * d ≤ 16 * (c + z) ^ 2 := by
    have h1 : 9 * p ^ 2 * d ≤ 9 * d ^ 2 := by nlinarith
    have h2 : 9 * d ^ 2 ≤ 16 * c ^ 2 := by nlinarith
    have h3 : 16 * c ^ 2 ≤ 16 * (c + z) ^ 2 := by nlinarith
    exact h1.trans (h2.trans h3)
  change d / (c + z) ^ 2 ≤ (16 / 9 : ℝ) / p ^ 2
  rw [div_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < c + z))
    (mul_pos (by norm_num : (0 : ℝ) < 9) (sq_pos_of_pos hp))).2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hcross

theorem curvatureTerm_summable {z : ℝ} (hz : 0 ≤ z) :
    Summable (fun j => curvatureTerm j z) := by
  have hp : Summable (fun n : ℕ => (16 / 9 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
      ((summable_nat_add_iff 1).mpr hs).mul_left (16 / 9 : ℝ)
  exact Summable.of_nonneg_of_le
    (fun j => (curvatureTerm_pos j hz).le)
    (fun j => curvatureTerm_le_pseries j hz) hp

theorem responseTerm_le_linear_curvature (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    responseTerm j z ≤ z * curvatureTerm j 0 := by
  have hc : 0 < conformalIndex j := conformalIndex_pos j
  have hcz : 0 < conformalIndex j + z := add_pos_of_pos_of_nonneg hc hz
  unfold responseTerm curvatureTerm
  rw [add_zero]
  rw [show z * (conformalMultiplicity j / conformalIndex j ^ 2) =
      conformalMultiplicity j * z / conformalIndex j ^ 2 by ring]
  apply (div_le_div_iff₀ (mul_pos hc hcz) (sq_pos_of_pos hc)).2
  have hden : conformalIndex j ^ 2 ≤
      conformalIndex j * (conformalIndex j + z) := by
    nlinarith [mul_nonneg hc.le hz]
  exact mul_le_mul_of_nonneg_left hden
    (mul_nonneg (conformalMultiplicity_pos j).le hz)

theorem responseTerm_summable {z : ℝ} (hz : 0 ≤ z) :
    Summable (fun j => responseTerm j z) := by
  exact Summable.of_nonneg_of_le
    (fun j => responseTerm_nonneg j hz)
    (fun j => responseTerm_le_linear_curvature j hz)
    ((curvatureTerm_summable (z := 0) (le_refl 0)).mul_left z)

/-- Complete dimensionless restoring response of the generated even scalar
tower. -/
def completeResponse (z : ℝ) : ℝ := ∑' j, responseTerm j z

/-- Complete positive radial curvature response. -/
def completeCurvature (z : ℝ) : ℝ := ∑' j, curvatureTerm j z

@[simp] theorem completeResponse_zero : completeResponse 0 = 0 := by
  simp [completeResponse]

theorem completeResponse_nonneg {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ completeResponse z := by
  exact tsum_nonneg fun j => responseTerm_nonneg j hz

theorem completeCurvature_pos {z : ℝ} (hz : 0 ≤ z) :
    0 < completeCurvature z := by
  exact (curvatureTerm_summable hz).tsum_pos
    (fun j => (curvatureTerm_pos j hz).le) 0 (curvatureTerm_pos 0 hz)

/-- Exact two-point difference identity; it is the algebraic source of strict
monotonicity and introduces no differentiability assumption. -/
theorem responseTerm_sub (j : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    responseTerm j y - responseTerm j x =
      conformalMultiplicity j * (y - x) /
        ((conformalIndex j + x) * (conformalIndex j + y)) := by
  have hc : conformalIndex j ≠ 0 := (conformalIndex_pos j).ne'
  have hcx : conformalIndex j + x ≠ 0 :=
    (add_pos_of_pos_of_nonneg (conformalIndex_pos j) hx).ne'
  have hcy : conformalIndex j + y ≠ 0 :=
    (add_pos_of_pos_of_nonneg (conformalIndex_pos j) hy).ne'
  unfold responseTerm
  field_simp [hc, hcx, hcy]
  ring

theorem responseTerm_strictMonoOn (j : ℕ) :
    StrictMonoOn (responseTerm j) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hdiff : 0 < conformalMultiplicity j * (y - x) /
      ((conformalIndex j + x) * (conformalIndex j + y)) := by
    exact div_pos (mul_pos (conformalMultiplicity_pos j) (sub_pos.mpr hxy))
      (mul_pos (add_pos_of_pos_of_nonneg (conformalIndex_pos j) hx)
        (add_pos_of_pos_of_nonneg (conformalIndex_pos j) hy))
  rw [← sub_pos, responseTerm_sub j hx hy]
  exact hdiff

theorem completeResponse_strictMonoOn :
    StrictMonoOn completeResponse (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold completeResponse
  exact Summable.tsum_lt_tsum (i := 0)
    (fun j => (responseTerm_strictMonoOn j hx hy hxy).le)
    (responseTerm_strictMonoOn 0 hx hy hxy)
    (responseTerm_summable hx) (responseTerm_summable hy)

theorem completeResponse_root_unique {target x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxt : completeResponse x = target)
    (hyt : completeResponse y = target) : x = y := by
  exact completeResponse_strictMonoOn.injOn hx hy (hxt.trans hyt.symm)

theorem oddCoordinate_mono {j N : ℕ} (h : j ≤ N) :
    oddCoordinate j ≤ oddCoordinate N := by
  unfold oddCoordinate
  exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1

theorem conformalIndex_mono {j N : ℕ} (h : j ≤ N) :
    conformalIndex j ≤ conformalIndex N := by
  have ho := oddCoordinate_mono h
  have hj := oddCoordinate_pos j
  have hN := oddCoordinate_pos N
  unfold conformalIndex
  nlinarith

theorem conformalIndex_lt_multiplicity (j : ℕ) :
    conformalIndex j < conformalMultiplicity j := by
  unfold conformalIndex conformalMultiplicity
  norm_num

/-- At the scale of shell `N`, each retained shell contributes at least one
half. This lower bound is obtained solely from the generated shell ordering. -/
theorem half_le_responseTerm_at_shell {j N : ℕ} (h : j ≤ N) :
    (1 / 2 : ℝ) ≤ responseTerm j (conformalIndex N) := by
  have hcj : 0 < conformalIndex j := conformalIndex_pos j
  have hcN : 0 < conformalIndex N := conformalIndex_pos N
  have hcmono : conformalIndex j ≤ conformalIndex N := conformalIndex_mono h
  have hcd : conformalIndex j < conformalMultiplicity j :=
    conformalIndex_lt_multiplicity j
  unfold responseTerm
  apply (le_div_iff₀ (mul_pos hcj (add_pos hcj hcN))).2
  nlinarith

theorem responseTerm_continuousOn (j : ℕ) :
    ContinuousOn (responseTerm j) (Set.Ici 0) := by
  apply ContinuousOn.div
  · exact continuousOn_const.mul continuousOn_id
  · exact continuousOn_const.mul (continuousOn_const.add continuousOn_id)
  · intro z hz
    exact mul_ne_zero (conformalIndex_pos j).ne'
      (add_pos_of_pos_of_nonneg (conformalIndex_pos j) hz).ne'

theorem completeResponse_continuousOn_Icc {Y : ℝ} (_hY : 0 ≤ Y) :
    ContinuousOn completeResponse (Set.Icc 0 Y) := by
  unfold completeResponse
  apply continuousOn_tsum
  · intro j
    exact (responseTerm_continuousOn j).mono fun _z hz => hz.1
  · exact (curvatureTerm_summable (z := 0) (le_refl 0)).mul_left Y
  · intro j z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (responseTerm_nonneg j hz.1)]
    exact (responseTerm_le_linear_curvature j hz.1).trans
      (mul_le_mul_of_nonneg_right hz.2 (curvatureTerm_pos j (le_refl 0)).le)

/-- The first `N+1` generated shells already force linear growth of the
complete response when evaluated at the `N`-th shell scale. -/
theorem half_shell_count_le_completeResponse (N : ℕ) :
    (((N + 1 : ℕ) : ℝ) / 2) ≤ completeResponse (conformalIndex N) := by
  have hfinite : (((N + 1 : ℕ) : ℝ) / 2) ≤
      ∑ j ∈ Finset.range (N + 1), responseTerm j (conformalIndex N) := by
    calc
      (((N + 1 : ℕ) : ℝ) / 2) =
          ∑ _j ∈ Finset.range (N + 1), (1 / 2 : ℝ) := by simp; ring
      _ ≤ ∑ j ∈ Finset.range (N + 1),
          responseTerm j (conformalIndex N) := by
        apply Finset.sum_le_sum
        intro j hj
        exact half_le_responseTerm_at_shell
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hsum : (∑ j ∈ Finset.range (N + 1),
      responseTerm j (conformalIndex N)) ≤
      completeResponse (conformalIndex N) := by
    unfold completeResponse
    exact (responseTerm_summable (conformalIndex_pos N).le).sum_le_tsum
      (Finset.range (N + 1))
      (fun j _hj => responseTerm_nonneg j (conformalIndex_pos N).le)
  exact hfinite.trans hsum

theorem completeResponse_unboundedAbove (target : ℝ) :
    ∃ z : ℝ, 0 ≤ z ∧ target < completeResponse z := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * target)
  refine ⟨conformalIndex N, (conformalIndex_pos N).le, ?_⟩
  have hlower := half_shell_count_le_completeResponse N
  have hcast : (2 * target : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNs : (N : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self N
  linarith

/-- Every positive dimensionless source drive meets the complete generated
restoring response at exactly one positive amplitude. -/
theorem existsUnique_completeResponse_root {target : ℝ} (htarget : 0 < target) :
    ∃! z : ℝ, 0 < z ∧ completeResponse z = target := by
  obtain ⟨Y, hY0, htargetY⟩ := completeResponse_unboundedAbove target
  have htarget_mem : target ∈
      Set.Icc (completeResponse 0) (completeResponse Y) := by
    constructor
    · simpa using htarget.le
    · exact htargetY.le
  obtain ⟨z, hzIcc, hzroot⟩ :=
    (intermediate_value_Icc hY0 (completeResponse_continuousOn_Icc hY0))
      htarget_mem
  have hzpos : 0 < z := by
    apply lt_of_le_of_ne hzIcc.1
    intro hz
    have hz0 : z = 0 := hz.symm
    subst z
    simp only [completeResponse_zero] at hzroot
    linarith
  refine ⟨z, ⟨hzpos, hzroot⟩, ?_⟩
  intro y hy
  exact completeResponse_root_unique hy.1.le hzpos.le hy.2 hzroot

/-- Dimensionless radial gap carried by a positive response amplitude.  It
uses only the amplitude and complete curvature of the generated tower. -/
def generatedRadialGap (z : ℝ) : ℝ :=
  4 * z * completeCurvature z

theorem generatedRadialGap_pos {z : ℝ} (hz : 0 < z) :
    0 < generatedRadialGap z := by
  unfold generatedRadialGap
  exact mul_pos (mul_pos (by norm_num) hz) (completeCurvature_pos hz.le)

/-- The normalized complete scalar mass index: the actual generated even
scalar Casimir plus the radial gap from the same response tower. -/
def generatedScalarMassIndex (j : ℕ) (z : ℝ) : ℝ :=
  scalarCasimir (2 * j) + generatedRadialGap z

theorem scalarCasimir_even_nonneg (j : ℕ) :
    0 ≤ scalarCasimir (2 * j) := by
  unfold scalarCasimir
  positivity

theorem generatedRadialGap_le_massIndex (j : ℕ) (z : ℝ) :
    generatedRadialGap z ≤ generatedScalarMassIndex j z := by
  unfold generatedScalarMassIndex
  linarith [scalarCasimir_even_nonneg j]

@[simp] theorem generatedScalarMassIndex_zero (z : ℝ) :
    generatedScalarMassIndex 0 z = generatedRadialGap z := by
  norm_num [generatedScalarMassIndex, scalarCasimir]

/-- Every positive drive therefore determines one positive response amplitude
and, at that same amplitude, a positive bottom for the complete generated
scalar tower. -/
theorem existsUnique_root_with_scalarGap {target : ℝ} (htarget : 0 < target) :
    ∃! z : ℝ,
      0 < z ∧ completeResponse z = target ∧
      0 < generatedRadialGap z ∧
      (∀ j, generatedRadialGap z ≤ generatedScalarMassIndex j z) ∧
      generatedScalarMassIndex 0 z = generatedRadialGap z := by
  obtain ⟨z, hz, hzunique⟩ := existsUnique_completeResponse_root htarget
  refine ⟨z, ⟨hz.1, hz.2, generatedRadialGap_pos hz.1,
    fun j => generatedRadialGap_le_massIndex j z,
    generatedScalarMassIndex_zero z⟩, ?_⟩
  intro y hy
  exact hzunique y ⟨hy.1, hy.2.1⟩

/-- The unit of the generated response coordinate. It is a normalization of
the already constructed dimensionless response, not an additional datum. -/
def canonicalDrive : ℝ := 1

theorem canonicalDrive_pos : 0 < canonicalDrive := by
  norm_num [canonicalDrive]

/-- The unique balance at one generated response unit. -/
noncomputable def canonicalAmplitude : ℝ :=
  Classical.choose (existsUnique_completeResponse_root canonicalDrive_pos)

theorem canonicalAmplitude_spec :
    0 < canonicalAmplitude ∧
      completeResponse canonicalAmplitude = canonicalDrive :=
  (Classical.choose_spec
    (existsUnique_completeResponse_root canonicalDrive_pos)).1

theorem canonicalAmplitude_unique {z : ℝ}
    (hz : 0 < z) (hresponse : completeResponse z = canonicalDrive) :
    z = canonicalAmplitude := by
  exact (Classical.choose_spec
    (existsUnique_completeResponse_root canonicalDrive_pos)).2 z
      ⟨hz, hresponse⟩

/-- The source-normalized radial gap, selected without an additional
coupling, radius, kinetic factor or target value. -/
noncomputable def canonicalRadialGap : ℝ :=
  generatedRadialGap canonicalAmplitude

theorem canonicalRadialGap_pos : 0 < canonicalRadialGap := by
  exact generatedRadialGap_pos canonicalAmplitude_spec.1

/-- Complete source-normalized scalar tower at the canonical balance. -/
noncomputable def canonicalScalarMassIndex (j : ℕ) : ℝ :=
  generatedScalarMassIndex j canonicalAmplitude

theorem canonicalRadialGap_le_massIndex (j : ℕ) :
    canonicalRadialGap ≤ canonicalScalarMassIndex j := by
  exact generatedRadialGap_le_massIndex j canonicalAmplitude

@[simp] theorem canonicalScalarMassIndex_zero :
    canonicalScalarMassIndex 0 = canonicalRadialGap := by
  exact generatedScalarMassIndex_zero canonicalAmplitude

/-- Complete-tower properties determined by the generated scalar spectrum. -/
structure CompleteProperties : Prop where
  scalar_origin : ∀ j,
    conformalIndex j = scalarCasimir (2 * j) + 3 / 4 ∧
      conformalMultiplicity j = scalarMultiplicity (2 * j)
  continuous_on_compact_nonnegative : ∀ Y, 0 ≤ Y →
    ContinuousOn completeResponse (Set.Icc 0 Y)
  strict_restoring : StrictMonoOn completeResponse (Set.Ici 0)
  positive_curvature : ∀ z, 0 ≤ z → 0 < completeCurvature z
  unbounded_response : ∀ target, ∃ z, 0 ≤ z ∧ target < completeResponse z
  positive_root : ∀ target, 0 < target →
    ∃! z, 0 < z ∧ completeResponse z = target
  positive_scalar_gap : ∀ target, 0 < target →
    ∃! z,
      0 < z ∧ completeResponse z = target ∧
      0 < generatedRadialGap z ∧
      (∀ j, generatedRadialGap z ≤ generatedScalarMassIndex j z) ∧
      generatedScalarMassIndex 0 z = generatedRadialGap z
  canonical_balance : 0 < canonicalAmplitude ∧
    completeResponse canonicalAmplitude = canonicalDrive
  canonical_gap : 0 < canonicalRadialGap ∧
    (∀ j, canonicalRadialGap ≤ canonicalScalarMassIndex j) ∧
    canonicalScalarMassIndex 0 = canonicalRadialGap

theorem completeProperties : CompleteProperties where
  scalar_origin := fun j =>
    ⟨conformalIndex_eq_scalar_shift j, conformalMultiplicity_eq_scalar j⟩
  continuous_on_compact_nonnegative := fun _Y hY =>
    completeResponse_continuousOn_Icc hY
  strict_restoring := completeResponse_strictMonoOn
  positive_curvature := fun _z hz => completeCurvature_pos hz
  unbounded_response := completeResponse_unboundedAbove
  positive_root := fun _target htarget =>
    existsUnique_completeResponse_root htarget
  positive_scalar_gap := fun _target htarget =>
    existsUnique_root_with_scalarGap htarget
  canonical_balance := canonicalAmplitude_spec
  canonical_gap := ⟨canonicalRadialGap_pos,
    canonicalRadialGap_le_massIndex, canonicalScalarMassIndex_zero⟩

/-- Exact response of the constant shell through shell `N`. -/
def finiteResponse (N : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), responseTerm j z

/-- Exact curvature of the same retained tower. -/
def finiteCurvature (N : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), curvatureTerm j z

@[simp] theorem finiteResponse_zero (N : ℕ) : finiteResponse N 0 = 0 := by
  simp [finiteResponse]

theorem finiteResponse_nonneg (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ finiteResponse N z := by
  exact Finset.sum_nonneg fun j _ => responseTerm_nonneg j hz

theorem finiteCurvature_pos (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 < finiteCurvature N z := by
  apply Finset.sum_pos
  · intro j _
    exact curvatureTerm_pos j hz
  · simp

theorem finiteResponse_strictMonoOn (N : ℕ) :
    StrictMonoOn (finiteResponse N) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply Finset.sum_lt_sum
  · intro j hj
    exact (responseTerm_strictMonoOn j hx hy hxy).le
  · exact ⟨0, by simp, responseTerm_strictMonoOn 0 hx hy hxy⟩

/-- A retained source tower has at most one nonnegative stationary amplitude
for any target response. -/
theorem finiteResponse_root_unique (N : ℕ) {target x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxt : finiteResponse N x = target)
    (hyt : finiteResponse N y = target) : x = y := by
  exact (finiteResponse_strictMonoOn N).injOn hx hy (hxt.trans hyt.symm)

/-- The exact finite-shell properties inherited from the generated scalar
spectrum, prior to any dimensional reparametrization. -/
structure FiniteProperties : Prop where
  scalar_origin : ∀ j,
    conformalIndex j = scalarCasimir (2 * j) + 3 / 4 ∧
      conformalMultiplicity j = scalarMultiplicity (2 * j)
  zero_response : ∀ N, finiteResponse N 0 = 0
  strict_restoring : ∀ N, StrictMonoOn (finiteResponse N) (Set.Ici 0)
  positive_curvature : ∀ N z, 0 ≤ z → 0 < finiteCurvature N z
  root_unique : ∀ N target x y, 0 ≤ x → 0 ≤ y →
    finiteResponse N x = target → finiteResponse N y = target → x = y

theorem finiteProperties : FiniteProperties where
  scalar_origin := fun j =>
    ⟨conformalIndex_eq_scalar_shift j, conformalMultiplicity_eq_scalar j⟩
  zero_response := finiteResponse_zero
  strict_restoring := finiteResponse_strictMonoOn
  positive_curvature := fun N _z hz => finiteCurvature_pos N hz
  root_unique := fun N _ _ _ hx hy hxt hyt =>
    finiteResponse_root_unique N hx hy hxt hyt

end GeneratedFoundations.Physical.SourceConformalResponse
