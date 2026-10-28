module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionAction
public import GeneratedFoundations.Geometry.SourcePolarMetric
public import GeneratedFoundations.Geometry.SourceProjectiveVolume
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Spatial homothety of the original joint Haar action

The angular metric and its dimension come from the source polar metric.
The quotient volume is the measured projective volume. Holding the original
connection one-form, section and fibre response fixed, inverse metrics act on
the covariant derivative once and on curvature twice. The fibre Casimir does
not change under this base-metric variation. These operations give the full spatial action, including
its nonlinear curvature and derivative--connection interference.

This is a three-dimensional spatial metric variation, not a four-dimensional
TT endpoint prescription or a variation of an observation bandwidth. All
positive stationary scales of this family are classified. A unique scale
for a fixed nonzero configuration does not select that configuration or a
window: the zero configuration is jointly stationary at every scale.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Quaternion

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricVariation

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionAction (Sections covariantDerivative sectionField)

/-- The angular dimension is computed before forming the volume factor. -/
theorem source_angular_dimension {q : ℍ} (hq : ‖q‖ = 1) :
    Module.finrank ℝ (Geometry.SourcePolarMetric.angularSpace q) = 3 :=
  Geometry.SourcePolarMetric.angular_finrank hq

theorem angular_metric_homothety {q : ℍ} (hq : ‖q‖ = 1) (c : ℝ)
    (v w : Geometry.SourcePolarMetric.angularSpace q) :
    inner ℝ (Geometry.SourcePolarMetric.polarLinear c q (0, v))
      (Geometry.SourcePolarMetric.polarLinear c q (0, w)) =
      c ^ 2 * inner ℝ (v : ℍ) (w : ℍ) := by
  simpa using Geometry.SourcePolarMetric.polar_inner hq c (0, v) (0, w)

theorem quotient_volume_homothety (c : ℝ) :
    Geometry.SourceProjectiveVolume.roundVolume c =
      c ^ 3 * Geometry.SourceProjectiveVolume.roundVolume 1 := by
  simp only [Geometry.SourceProjectiveVolume.roundVolume_eq, one_pow, mul_one]
  ring

/-- Contragredient transport is determined on every covector, rather than
chosen by a norm-scaling convention. -/
theorem covector_transport_existsUnique {E F : Type*} [AddCommGroup E]
    [Module ℝ E] [AddCommGroup F] [Module ℝ F] (T : E →ₗ[ℝ] F)
    {c : ℝ} (hc : c ≠ 0) :
    ∃! S : E →ₗ[ℝ] F, ∀ v, S (c • v) = T v := by
  refine ⟨c⁻¹ • T, ?_, ?_⟩
  · intro v
    simp only [LinearMap.smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  · intro S hS
    ext v
    have h := hS (c⁻¹ • v)
    simpa only [smul_smul, mul_inv_cancel₀ hc, one_smul, map_smul,
      LinearMap.smul_apply] using h

/-- A two-form has two inverse-frame factors, uniquely, before integration. -/
theorem twoform_transport_existsUnique {E F : Type*} [AddCommGroup E]
    [Module ℝ E] [AddCommGroup F] [Module ℝ F] (T : E →ₗ[ℝ] E →ₗ[ℝ] F)
    {c : ℝ} (hc : c ≠ 0) :
    ∃! S : E →ₗ[ℝ] E →ₗ[ℝ] F, ∀ v w, S (c • v) (c • w) = T v w := by
  refine ⟨(c⁻¹ * c⁻¹) • T, ?_, ?_⟩
  · intro v w
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    have he : c * (c * (c⁻¹ * c⁻¹)) = 1 := by field_simp
    rw [he, one_smul]
  · intro S hS
    ext v w
    have h := hS (c⁻¹ • v) (c⁻¹ • w)
    simpa only [smul_smul, mul_inv_cancel₀ hc, one_smul, map_smul,
      LinearMap.smul_apply] using h

/-- Original nonlinear curvature energy in the unit Haar metric. -/
def curvatureEnergy (N : ℕ) (A : Coefficients N) : ℝ :=
  HistoryHaarMatrixCurvature.action N A

/-- Original covariant section energy, with its complete current retained. -/
def sectionEnergy (N : ℕ) (A : Coefficients N) (ψ : Sections N) : ℝ :=
  ‖covariantDerivative N A ψ‖ ^ 2 / 2 +
    HistoryDefiningResponse.coefficient N * ‖sectionField N ψ‖ ^ 2 / 2

theorem curvatureEnergy_nonneg (N : ℕ) (A : Coefficients N) :
    0 ≤ curvatureEnergy N A := HistoryHaarMatrixCurvature.action_nonneg N A

theorem sectionEnergy_nonneg (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    0 ≤ sectionEnergy N A ψ := by
  unfold sectionEnergy
  exact add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (div_nonneg (mul_nonneg (HistoryDefiningResponse.coefficient_pos N).le
      (sq_nonneg _)) (by norm_num))

theorem original_action_decomposition (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    HistoryHaarSectionAction.action N A ψ = curvatureEnergy N A + sectionEnergy N A ψ := by
  unfold HistoryHaarSectionAction.action curvatureEnergy sectionEnergy
  ring

/-- Keep the original kinetic and fibre-restoring terms separate. -/
def kineticEnergy (N : ℕ) (A : Coefficients N) (ψ : Sections N) : ℝ :=
  ‖covariantDerivative N A ψ‖ ^ 2 / 2

def restoringEnergy (N : ℕ) (ψ : Sections N) : ℝ :=
  HistoryDefiningResponse.coefficient N * ‖sectionField N ψ‖ ^ 2 / 2

theorem kineticEnergy_nonneg (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    0 ≤ kineticEnergy N A ψ := by unfold kineticEnergy; positivity

theorem restoringEnergy_nonneg (N : ℕ) (ψ : Sections N) :
    0 ≤ restoringEnergy N ψ :=
  div_nonneg (mul_nonneg (HistoryDefiningResponse.coefficient_pos N).le
    (sq_nonneg _)) (by norm_num)

/-- Relative angular volume and both inverse-metric contractions act on the
original fields. The independently derived fibre Casimir is held fixed. -/
def geometricAction (N : ℕ) (A : Coefficients N) (ψ : Sections N) (c : ℝ) : ℝ :=
  c ^ 3 * (‖(((c ^ 2)⁻¹ : ℝ) : ℂ) • HistoryHaarMatrixCurvature.curvature N A‖ ^ 2 / 2 +
    ‖((c⁻¹ : ℝ) : ℂ) • covariantDerivative N A ψ‖ ^ 2 / 2 + restoringEnergy N ψ)

theorem geometricAction_exact (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    {c : ℝ} (hc : c ≠ 0) :
    geometricAction N A ψ c = curvatureEnergy N A / c +
      c * kineticEnergy N A ψ + c ^ 3 * restoringEnergy N ψ := by
  simp only [geometricAction, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, curvatureEnergy, HistoryHaarMatrixCurvature.action, kineticEnergy]
  field_simp

@[simp] theorem geometricAction_one (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    geometricAction N A ψ 1 = HistoryHaarSectionAction.action N A ψ := by
  rw [geometricAction_exact N A ψ one_ne_zero]
  simp only [div_one, one_mul, one_pow]
  rfl

theorem geometricAction_nonneg (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    {c : ℝ} (hc : 0 < c) : 0 ≤ geometricAction N A ψ c := by
  rw [geometricAction_exact N A ψ hc.ne']
  exact add_nonneg
    (add_nonneg (div_nonneg (curvatureEnergy_nonneg N A) hc.le)
      (mul_nonneg hc.le (kineticEnergy_nonneg N A ψ)))
    (mul_nonneg (pow_nonneg hc.le _) (restoringEnergy_nonneg N ψ))

/-- No cubic or quartic term in the original functionals is discarded. -/
theorem geometricAction_original_functionals (N : ℕ) (A : Coefficients N)
    (ψ : Sections N) {c : ℝ} (hc : c ≠ 0) :
    geometricAction N A ψ c = c * HistoryHaarSectionAction.action N A ψ +
      (1 / c - c) * HistoryHaarMatrixCurvature.action N A +
      (c ^ 3 - c) * restoringEnergy N ψ := by
  rw [geometricAction_exact N A ψ hc]
  unfold curvatureEnergy kineticEnergy restoringEnergy HistoryHaarSectionAction.action
  ring

def scaleForce (N : ℕ) (A : Coefficients N) (ψ : Sections N) (c : ℝ) : ℝ :=
  kineticEnergy N A ψ + 3 * c ^ 2 * restoringEnergy N ψ - curvatureEnergy N A / c ^ 2

def scaleBalance (N : ℕ) (A : Coefficients N) (ψ : Sections N) (c : ℝ) : ℝ :=
  kineticEnergy N A ψ * c ^ 2 + 3 * restoringEnergy N ψ * c ^ 4

theorem geometricAction_hasDerivAt (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    {c : ℝ} (hc : 0 < c) :
    HasDerivAt (geometricAction N A ψ) (scaleForce N A ψ c) c := by
  have hd := (((hasDerivAt_const c (curvatureEnergy N A)).div
    (hasDerivAt_id c) hc.ne').add
    ((hasDerivAt_id c).mul_const (kineticEnergy N A ψ))).add
    (((hasDerivAt_id c).pow 3).mul_const (restoringEnergy N ψ))
  have hd' : HasDerivAt (fun r : ℝ => curvatureEnergy N A / r +
      r * kineticEnergy N A ψ + r ^ 3 * restoringEnergy N ψ)
      (scaleForce N A ψ c) c := by
    convert! hd using 1
    simp only [scaleForce, id_eq]
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hc] with r hr
  exact geometricAction_exact N A ψ hr.ne'

theorem stationary_iff_balance (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    {c : ℝ} (hc : 0 < c) :
    deriv (geometricAction N A ψ) c = 0 ↔
      scaleBalance N A ψ c = curvatureEnergy N A := by
  rw [(geometricAction_hasDerivAt N A ψ hc).deriv, scaleForce, sub_eq_zero,
    eq_div_iff (pow_ne_zero 2 hc.ne')]
  have he : (kineticEnergy N A ψ + 3 * c ^ 2 * restoringEnergy N ψ) * c ^ 2 =
      scaleBalance N A ψ c := by unfold scaleBalance; ring
  rw [he]

/-- Strict monotonicity compares every positive scale whenever either
original section term is present. -/
theorem scaleBalance_strictMonoOn (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    (hM : 0 < kineticEnergy N A ψ + restoringEnergy N ψ) :
    StrictMonoOn (scaleBalance N A ψ) (Set.Ici 0) := by
  intro c hc r hr hcr
  have h2 : c ^ 2 < r ^ 2 := by change 0 ≤ c at hc; nlinarith
  have h4 : c ^ 4 < r ^ 4 := by nlinarith [sq_nonneg c, sq_nonneg r]
  have hK := kineticEnergy_nonneg N A ψ
  have hV := restoringEnergy_nonneg N ψ
  unfold scaleBalance
  by_cases hKp : 0 < kineticEnergy N A ψ
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h2 hKp)
      (mul_le_mul_of_nonneg_left h4.le (by positivity))
  · have hVp : 0 < restoringEnergy N ψ := by linarith
    exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left h2.le hK)
      (mul_lt_mul_of_pos_left h4 (by positivity))

theorem existsUnique_stationary_scale (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    (hY : 0 < curvatureEnergy N A)
    (hM : 0 < kineticEnergy N A ψ + restoringEnergy N ψ) :
    ∃! c : ℝ, 0 < c ∧ deriv (geometricAction N A ψ) c = 0 := by
  let b := 1 + curvatureEnergy N A / (kineticEnergy N A ψ + restoringEnergy N ψ)
  have hb : 1 < b := by dsimp [b]; linarith [div_pos hY hM]
  have hb2 : b ≤ b ^ 2 := by nlinarith
  have hb4 : b ≤ 3 * b ^ 4 := by nlinarith [sq_nonneg (b ^ 2)]
  have hK := kineticEnergy_nonneg N A ψ
  have hV := restoringEnergy_nonneg N ψ
  have hid : (kineticEnergy N A ψ + restoringEnergy N ψ) * b =
      kineticEnergy N A ψ + restoringEnergy N ψ + curvatureEnergy N A := by
    dsimp [b]
    field_simp
  have htop : curvatureEnergy N A < scaleBalance N A ψ b := by
    unfold scaleBalance
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hb2),
      mul_nonneg hV (sub_nonneg.mpr hb4)]
  have hcont : ContinuousOn (scaleBalance N A ψ) (Set.Icc 0 b) := by
    unfold scaleBalance
    fun_prop
  have hz : scaleBalance N A ψ 0 = 0 := by simp [scaleBalance]
  obtain ⟨c, hc, he⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ b by linarith)
    hcont (show curvatureEnergy N A ∈ Set.Icc (scaleBalance N A ψ 0)
      (scaleBalance N A ψ b) by rw [hz]; exact ⟨hY.le, htop.le⟩)
  have hcp : 0 < c := by
    by_contra hn
    have hcz : c = 0 := le_antisymm (le_of_not_gt hn) hc.1
    rw [hcz, hz] at he
    linarith
  refine ⟨c, ⟨hcp, (stationary_iff_balance N A ψ hcp).mpr he⟩, ?_⟩
  intro r hr
  exact (scaleBalance_strictMonoOn N A ψ hM).injOn hr.1.le hcp.le
    (((stationary_iff_balance N A ψ hr.1).mp hr.2).trans he.symm)

/-- Necessity as well as sufficiency, including all degenerate cases. -/
theorem existsUnique_stationary_scale_iff (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    (∃! c : ℝ, 0 < c ∧ deriv (geometricAction N A ψ) c = 0) ↔
      0 < curvatureEnergy N A ∧ 0 < kineticEnergy N A ψ + restoringEnergy N ψ := by
  constructor
  · rintro ⟨c, hc, hu⟩
    have hK := kineticEnergy_nonneg N A ψ
    have hV := restoringEnergy_nonneg N ψ
    have hM : 0 < kineticEnergy N A ψ + restoringEnergy N ψ := by
      by_contra hn
      have hK0 : kineticEnergy N A ψ = 0 := by linarith
      have hV0 : restoringEnergy N ψ = 0 := by linarith
      have hY0 : curvatureEnergy N A = 0 := by
        have hb := (stationary_iff_balance N A ψ hc.1).mp hc.2
        simpa only [scaleBalance, hK0, hV0, zero_mul, mul_zero, zero_add] using hb.symm
      have hall (r : ℝ) (hr : 0 < r) : deriv (geometricAction N A ψ) r = 0 := by
        rw [stationary_iff_balance N A ψ hr]
        simp only [scaleBalance, hK0, hV0, hY0, zero_mul, mul_zero, zero_add]
      have h1 := hu 1 ⟨by norm_num, hall 1 (by norm_num)⟩
      have h2 := hu 2 ⟨by norm_num, hall 2 (by norm_num)⟩
      linarith
    have hpos := scaleBalance_strictMonoOn N A ψ hM
      (show (0 : ℝ) ∈ Set.Ici 0 by norm_num) hc.1.le hc.1
    simp only [scaleBalance, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 4 ≠ 0), mul_zero, add_zero] at hpos
    have hb := (stationary_iff_balance N A ψ hc.1).mp hc.2
    unfold scaleBalance at hb
    exact ⟨by linarith, hM⟩
  · rintro ⟨hY, hM⟩
    exact existsUnique_stationary_scale N A ψ hY hM

/-- The exact difference to any stationary scale is a positive square.
All original field nonlinearities remain inside Y, K and V. -/
theorem geometricAction_gap (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hstat : deriv (geometricAction N A ψ) r = 0) :
    geometricAction N A ψ c - geometricAction N A ψ r =
      (c - r) ^ 2 / c * (kineticEnergy N A ψ + restoringEnergy N ψ *
        (c ^ 2 + 2 * c * r + 3 * r ^ 2)) := by
  have hb := (stationary_iff_balance N A ψ hr).mp hstat
  rw [geometricAction_exact N A ψ hc.ne', geometricAction_exact N A ψ hr.ne', ← hb]
  unfold scaleBalance
  field_simp
  ring

theorem unique_global_minimum (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    (hM : 0 < kineticEnergy N A ψ + restoringEnergy N ψ)
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r)
    (hstat : deriv (geometricAction N A ψ) r = 0) :
    geometricAction N A ψ r ≤ geometricAction N A ψ c ∧
      (geometricAction N A ψ c = geometricAction N A ψ r ↔ c = r) := by
  have hp : 0 < kineticEnergy N A ψ + restoringEnergy N ψ *
      (c ^ 2 + 2 * c * r + 3 * r ^ 2) := by
    have hK := kineticEnergy_nonneg N A ψ
    have hV := restoringEnergy_nonneg N ψ
    have ht : 0 < c ^ 2 + 2 * c * r + 3 * r ^ 2 := by positivity
    by_cases hKp : 0 < kineticEnergy N A ψ
    · exact add_pos_of_pos_of_nonneg hKp (mul_nonneg hV ht.le)
    · have hVp : 0 < restoringEnergy N ψ := by linarith
      exact add_pos_of_nonneg_of_pos hK (mul_pos hVp ht)
  have he := geometricAction_gap N A ψ hc hr hstat
  have hq : 0 ≤ (c - r) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  constructor
  · nlinarith
  · constructor
    · intro h
      have hzero : (c - r) ^ 2 / c = 0 := by nlinarith
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((div_eq_zero_iff.mp hzero).resolve_right hc.ne'))
    · rintro rfl
      rfl

@[simp] theorem curvatureEnergy_zero (N : ℕ) : curvatureEnergy N 0 = 0 := by
  have hv := HistoryHaarMatrixCurvature.vertex_smul N 0 0
  simp only [zero_smul, zero_mul] at hv
  change ‖HistoryHaarMatrixCurvature.differentiated N 0 +
    HistoryHaarMatrixCurvature.vertex N 0‖ ^ 2 / 2 = 0
  rw [map_zero, hv, add_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]

@[simp] theorem kineticEnergy_zero (N : ℕ) : kineticEnergy N 0 0 = 0 := by
  have h := HistoryHaarSectionAction.connectionDerivative_smul N 0 0 0 0
  simp only [zero_smul, zero_mul] at h
  simp [kineticEnergy, covariantDerivative, h]

@[simp] theorem restoringEnergy_zero (N : ℕ) : restoringEnergy N 0 = 0 := by
  simp [restoringEnergy]

theorem zero_configuration_stationary (N : ℕ) {c : ℝ} (hc : 0 < c) :
    deriv (geometricAction N 0 0) c = 0 := by
  rw [stationary_iff_balance N 0 0 hc]
  simp [scaleBalance]

/-- The spatial action alone does not select a positive scale across all
configurations. This does not identify the zero configuration with the
positive Gaussian source state or with a stationary effective action. -/
theorem no_unique_scale_for_unselected_configurations (N : ℕ) :
    ¬ ∃! c : ℝ, 0 < c ∧ ∃ A ψ, deriv (geometricAction N A ψ) c = 0 := by
  rintro ⟨c, _, hu⟩
  have h1 := hu 1 ⟨by norm_num, 0, 0, zero_configuration_stationary N (by norm_num)⟩
  have h2 := hu 2 ⟨by norm_num, 0, 0, zero_configuration_stationary N (by norm_num)⟩
  linarith

structure Conclusions : Prop where
  actual_geometric_action : ∀ N A ψ c, 0 < c →
    geometricAction N A ψ c = curvatureEnergy N A / c +
      c * kineticEnergy N A ψ + c ^ 3 * restoringEnergy N ψ
  actual_scale_variation : ∀ N A ψ c, 0 < c →
    HasDerivAt (geometricAction N A ψ) (scaleForce N A ψ c) c
  all_positive_scales : ∀ N A ψ, 0 < curvatureEnergy N A →
    0 < kineticEnergy N A ψ + restoringEnergy N ψ →
    ∃! c : ℝ, 0 < c ∧ deriv (geometricAction N A ψ) c = 0
  exact_uniqueness_criterion : ∀ N A ψ,
    ((∃! c : ℝ, 0 < c ∧ deriv (geometricAction N A ψ) c = 0) ↔
      0 < curvatureEnergy N A ∧ 0 < kineticEnergy N A ψ + restoringEnergy N ψ)
  exact_global_comparison : ∀ N A ψ c r, 0 < c → 0 < r →
    deriv (geometricAction N A ψ) r = 0 →
    geometricAction N A ψ c - geometricAction N A ψ r =
      (c - r) ^ 2 / c * (kineticEnergy N A ψ + restoringEnergy N ψ *
        (c ^ 2 + 2 * c * r + 3 * r ^ 2))
  unselected_configuration_test : ∀ N,
    ¬ ∃! c : ℝ, 0 < c ∧ ∃ A ψ, deriv (geometricAction N A ψ) c = 0

theorem generated : Conclusions where
  actual_geometric_action := fun N A ψ _ hc => geometricAction_exact N A ψ hc.ne'
  actual_scale_variation := fun N A ψ _ hc => geometricAction_hasDerivAt N A ψ hc
  all_positive_scales := existsUnique_stationary_scale
  exact_uniqueness_criterion := existsUnique_stationary_scale_iff
  exact_global_comparison := fun N A ψ _ _ hc hr => geometricAction_gap N A ψ hc hr
  unselected_configuration_test := no_unique_scale_for_unselected_configurations

end GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricVariation
