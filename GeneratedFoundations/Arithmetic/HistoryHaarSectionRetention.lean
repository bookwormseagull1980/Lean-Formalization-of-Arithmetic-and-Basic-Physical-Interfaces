module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionBoundary
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Complete Gaussian mass and finite-window retention

The normalizer of a finite observation is compared with the complete
Gaussian source, rather than declared to be its full mass. The original
field and scalar rows give an exact summable formula for this full mass.
Every finite observation retains a strictly positive, strictly incomplete
fraction on a positive bandwidth. Window information below is the negative
logarithm of this calculated fraction. It is not a TT effective-action
coefficient or an assumption selecting a physical position count.

The original differentiated field and scalar spectra also determine a
joint partition of bandwidths. Their positions interlace, so the scalar
count equals the field-shell count or exceeds it by one. The joint cells
are tested by the same complete Gaussian response and by the calculated
retention fraction. No fixed retention target is inserted as an endpoint
condition.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionRetention

open HistoryHaarSectionWindow HistoryHaarSectionContent HistoryHaarSectionShells
open HistoryHaarSectionComparison (weight weight_pos weight_continuous)
open HistoryHaarSectionProbability (branchMass mass branchMass_nonneg)
open HistoryHaarSectionExhaustion
open HistoryHaarSectionJointHessian (Index)
open Geometry.SourceScalarKineticForm (position)

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

theorem branchMass_positionIndex (N j : ℕ) (B : ℝ)
    (a : HistoryHaarSectionAction.PositionLabels N j) :
    branchMass N B (positionIndex N j a) = fieldIntegral B (position j) := rfl

theorem complete_position_mass (N j : ℕ) (B : ℝ) :
    (∑ a : HistoryHaarSectionAction.PositionLabels N j,
      branchMass N B (positionIndex N j a)) =
      (HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2 : ℕ) *
        fieldIntegral B (position j) := by
  simp only [branchMass_positionIndex, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, HistoryHaarSectionAction.position_multiplicity]

def scalarMassRow (N : ℕ) (B : ℝ) (j : ℕ) : ℝ :=
  (HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2 : ℕ) *
    fieldIntegral B (position j)

theorem scalarMassRow_nonneg (N : ℕ) (B : ℝ) (j : ℕ) :
    0 ≤ scalarMassRow N B j :=
  mul_nonneg (Nat.cast_nonneg _) (fieldIntegral_nonneg _ _)

/-- Both terms regroup the same original joint support. -/
theorem mass_eq_finite_rows (N : ℕ) (B : ℝ) :
    mass N B = (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 *
      ∑ m ∈ Finset.range (HistorySpectralWindow.enumerationBound B), fieldRow B m +
      ∑ j ∈ Finset.range (positionCount B), scalarMassRow N B j := by
  classical
  have hf : (∑ i ∈ (support N B).filter (fun i => ¬ i.isRight = true),
      branchMass N B i) = fieldResponse N B := by
    unfold fieldResponse
    apply Finset.sum_congr rfl
    intro i hi
    cases i with
    | inl a => exact (branchIntegral_field N B a).symm
    | inr a => simp at hi
  have hs : (∑ i ∈ (support N B).filter (fun i => i.isRight = true),
      branchMass N B i) = ∑ j ∈ Finset.range (positionCount B), scalarMassRow N B j := by
    rw [scalarSupport_eq_image, Finset.sum_image]
    · change (∑ i : ContentLabels N (positionCount B),
        branchMass N B (contentIndex N (positionCount B) i)) = _
      rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl (fun j _ => complete_position_mass N j.val B)
    · exact fun _ _ _ _ h => contentIndex_injective _ _ h
  have he := Finset.sum_filter_add_sum_filter_not (support N B)
    (fun i => i.isRight = true) (branchMass N B)
  rw [hf, hs, add_comm] at he
  unfold mass
  rw [← he, fieldResponse_eq_rows]
  rfl

private theorem square_ge_nat (m : ℕ) : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hp : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    nlinarith

theorem fieldRow_eq_zero_of_outside {B : ℝ} {m : ℕ}
    (hm : HistorySpectralWindow.enumerationBound B ≤ m) : fieldRow B m = 0 := by
  have hb : B ≤ (m : ℝ) :=
    (Nat.le_ceil B).trans (by
      exact_mod_cast (Nat.le_succ (Nat.ceil B)).trans hm)
  have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h1 : B ≤ ((m : ℝ) + 2) ^ 2 := by nlinarith [square_ge_nat m]
  have h2 : B ≤ (m : ℝ) ^ 2 := hb.trans (square_ge_nat m)
  simp only [fieldRow, fieldIntegral_eq_zero h1, fieldIntegral_eq_zero h2,
    mul_zero, add_zero, ite_self]

theorem scalarMassRow_eq_zero_of_outside (N : ℕ) {B : ℝ} {j : ℕ}
    (hj : positionCount B ≤ j) : scalarMassRow N B j = 0 := by
  have hb : B ≤ position j := le_of_not_gt
    (fun h => Nat.not_lt_of_ge hj ((position_lt_iff j B).mp h))
  simp only [scalarMassRow, fieldIntegral_eq_zero hb, mul_zero]

/-- The finite observation is exactly a zero-extended sum on all rows. -/
theorem mass_eq_tsum_rows (N : ℕ) (B : ℝ) :
    mass N B = (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * ∑' m, fieldRow B m +
      ∑' j, scalarMassRow N B j := by
  rw [mass_eq_finite_rows]
  congr 1
  · congr 1
    exact (tsum_eq_sum (fun m hm => fieldRow_eq_zero_of_outside
      (Nat.le_of_not_gt (fun h => hm (Finset.mem_range.mpr h))))).symm
  · exact (tsum_eq_sum (fun j hj => scalarMassRow_eq_zero_of_outside N
      (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))))).symm

theorem fieldIntegral_tendsto_full (a : ℝ) :
    Tendsto (fun B => fieldIntegral B a) atTop (𝓝 (Real.exp (-a) * frequencyMass)) := by
  have he (B : ℝ) : fieldIntegral B a = Real.exp (-a) *
      ∫ u in (0 : ℝ)..Real.sqrt (B - a), Real.exp (-(u ^ 2)) := by
    unfold fieldIntegral
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    change Real.exp (-(u ^ 2 + a)) = Real.exp (-a) * Real.exp (-(u ^ 2))
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-(u ^ 2))) (Ioi 0) := by
    simpa only [neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn (s := Ioi 0)
  have hg : (∫ u in Ioi (0 : ℝ), Real.exp (-(u ^ 2))) = frequencyMass := by
    simpa [frequencyMass] using integral_gaussian_Ioi 1
  have ht := intervalIntegral_tendsto_integral_Ioi 0 hi
    (Real.tendsto_sqrt_atTop.comp (show Tendsto (fun B : ℝ => B - a) atTop atTop by
      simpa only [sub_eq_add_neg, id_eq] using!
        tendsto_atTop_add_const_right atTop (-a) tendsto_id))
  simpa only [hg, Function.comp_apply] using! ht.const_mul (Real.exp (-a))

theorem fieldRow_tendsto_full (m : ℕ) :
    Tendsto (fun B => fieldRow B m) atTop (𝓝 (fieldHeat m * frequencyMass)) := by
  unfold fieldRow fieldHeat
  split_ifs
  · convert! (((fieldIntegral_tendsto_full (((m : ℝ) + 2) ^ 2)).const_mul ((m + 3 : ℕ) : ℝ)).add
      ((fieldIntegral_tendsto_full ((m : ℝ) ^ 2)).const_mul ((m - 1 : ℕ) : ℝ))).const_mul
        ((m + 1 : ℕ) : ℝ) using 1
    congr 1
    ring
  · simp

theorem scalarMassRow_tendsto_full (N j : ℕ) :
    Tendsto (fun B => scalarMassRow N B j) atTop
      (𝓝 ((HistoryAdjointCasimir.dimension N : ℝ) * scalarHeat j * frequencyMass)) := by
  convert! (fieldIntegral_tendsto_full (position j)).const_mul
    ((HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2 : ℕ) : ℝ) using 1
  congr 1
  unfold scalarHeat
  push_cast
  ring

theorem scalarMassRow_le_full (N j : ℕ) (B : ℝ) :
    scalarMassRow N B j ≤
      (HistoryAdjointCasimir.dimension N : ℝ) * scalarHeat j * frequencyMass := by
  have h := mul_le_mul_of_nonneg_left (fieldIntegral_le_full B (position j))
    (Nat.cast_nonneg (HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2))
  simpa only [scalarMassRow, scalarHeat, Nat.cast_mul, Nat.cast_pow, mul_assoc] using h

/-- The previous full Gaussian budget is precisely the complete mass of
the source; it is not merely an upper bound on finite probabilities. -/
theorem mass_tendsto_fullBudget (N : ℕ) :
    Tendsto (mass N) atTop (𝓝 (fullBudget N)) := by
  have hf := tendsto_tsum_of_dominated_convergence
    (summable_fieldHeat.mul_right frequencyMass) fieldRow_tendsto_full
    (Eventually.of_forall (fun B m => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fieldRow_nonneg B m)]
      exact field_row_le_full B m))
  have hs := tendsto_tsum_of_dominated_convergence
    ((summable_scalarHeat.mul_left (HistoryAdjointCasimir.dimension N : ℝ)).mul_right frequencyMass)
    (scalarMassRow_tendsto_full N)
    (Eventually.of_forall (fun B j => by
      rw [Real.norm_eq_abs, abs_of_nonneg (scalarMassRow_nonneg N B j)]
      exact scalarMassRow_le_full N j B))
  simp_rw [tsum_mul_right, tsum_mul_left] at hf hs
  have ht := (hf.const_mul ((HistoryAdjointCasimir.dimension N : ℝ) ^ 2)).add hs
  simp_rw [← mass_eq_tsum_rows] at ht
  convert ht using 1
  congr 1
  unfold fullBudget
  ring

theorem branchMass_mono (N : ℕ) (i : Index N) : Monotone (fun B => branchMass N B i) := by
  intro B C hBC
  apply intervalIntegral.integral_mono_interval le_rfl (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt (sub_le_sub_right hBC _))
  · exact Eventually.of_forall (fun u => (weight_pos N i u).le)
  · exact (weight_continuous N i).intervalIntegrable _ _

theorem mass_mono (N : ℕ) : Monotone (mass N) := by
  intro B C hBC
  rw [HistoryHaarSectionBoundary.mass_eq_larger_sum N hBC]
  exact Finset.sum_le_sum (fun i _ => branchMass_mono N i hBC)

theorem mass_strictMonoOn (N : ℕ) : StrictMonoOn (mass N) (Ici 0) := by
  intro B hB C _ hBC
  change 0 ≤ B at hB
  let i := positionIndex N 0 (basePositionLabel N 0)
  have hi0 : kinetic N i = 0 := by
    change position 0 = 0
    norm_num [Geometry.SourceScalarKineticForm.position_eq]
  have hi : i ∈ support N C := (mem_support N C i).mpr (by rw [hi0]; linarith [hB])
  have hs : Real.sqrt (B - kinetic N i) < Real.sqrt (C - kinetic N i) :=
    Real.sqrt_lt_sqrt (by simpa only [hi0, sub_zero] using hB)
      (sub_lt_sub_right hBC _)
  have hp : 0 < ∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i),
      weight N i u := intervalIntegral.intervalIntegral_pos_of_pos_on
    ((weight_continuous N i).intervalIntegrable _ _) (fun u _ => weight_pos N i u) hs
  have hd := HistoryHaarSectionBoundary.branchMass_change N i B C
  rw [HistoryHaarSectionBoundary.mass_eq_larger_sum N hBC.le]
  exact Finset.sum_lt_sum (fun j _ => branchMass_mono N j hBC.le)
    ⟨i, hi, by linarith [hd]⟩

theorem mass_zero (N : ℕ) : mass N 0 = 0 := by
  unfold mass
  exact Finset.sum_eq_zero (fun i _ =>
    HistoryHaarSectionBoundary.branchMass_eq_zero N 0 i (kinetic_nonneg N i))

theorem mass_le_fullBudget (N : ℕ) (B : ℝ) : mass N B ≤ fullBudget N := by
  apply ge_of_tendsto (mass_tendsto_fullBudget N)
  filter_upwards [eventually_ge_atTop B] with C hC
  exact mass_mono N hC

theorem fullBudget_pos (N : ℕ) : 0 < fullBudget N :=
  (HistoryHaarSectionProbability.mass_pos_of_pos N (by norm_num : (0 : ℝ) < 1)).trans_le
    (mass_le_fullBudget N 1)

theorem mass_lt_fullBudget (N : ℕ) {B : ℝ} (hB : 0 ≤ B) : mass N B < fullBudget N :=
  (mass_strictMonoOn N hB (by change 0 ≤ B + 1; linarith) (by linarith : B < B + 1)).trans_le
    (mass_le_fullBudget N (B + 1))

/-- The actual retained fraction of the complete Gaussian source. -/
def retention (N : ℕ) (B : ℝ) : ℝ := mass N B / fullBudget N

theorem retention_continuous (N : ℕ) : Continuous (retention N) :=
  (HistoryHaarSectionBoundary.mass_continuous N).div_const _

theorem retention_zero (N : ℕ) : retention N 0 = 0 := by simp [retention, mass_zero]

theorem retention_pos (N : ℕ) {B : ℝ} (hB : 0 < B) : 0 < retention N B :=
  div_pos (HistoryHaarSectionProbability.mass_pos_of_pos N hB) (fullBudget_pos N)

theorem retention_lt_one (N : ℕ) {B : ℝ} (hB : 0 ≤ B) : retention N B < 1 :=
  (div_lt_one (fullBudget_pos N)).mpr (mass_lt_fullBudget N hB)

theorem retention_strictMonoOn (N : ℕ) : StrictMonoOn (retention N) (Ici 0) := by
  intro B hB C hC hBC
  exact (div_lt_div_iff_of_pos_right (fullBudget_pos N)).mpr (mass_strictMonoOn N hB hC hBC)

theorem retention_tendsto_one (N : ℕ) : Tendsto (retention N) atTop (𝓝 1) := by
  simpa only [retention, div_self (fullBudget_pos N).ne'] using!
    (mass_tendsto_fullBudget N).div_const (fullBudget N)

/-- Logarithmic information of retaining this window in the complete
source. This is distinct from the conditional precision KL within it. -/
def retentionInformation (N : ℕ) (B : ℝ) : ℝ := -Real.log (retention N B)

theorem retentionInformation_pos (N : ℕ) {B : ℝ} (hB : 0 < B) :
    0 < retentionInformation N B := by
  exact neg_pos.mpr (Real.log_neg (retention_pos N hB) (retention_lt_one N hB.le))

theorem retentionInformation_strictAntiOn (N : ℕ) :
    StrictAntiOn (retentionInformation N) (Ioi 0) := by
  intro B hB C hC hBC
  exact neg_lt_neg (Real.log_lt_log (retention_pos N hB)
    (retention_strictMonoOn N hB.le hC.le hBC))

/-- Complete normalization cancels in the information transferred between
two actual windows; neither of their Gaussian masses is replaced. -/
theorem retentionInformation_change (N : ℕ) {B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    retentionInformation N B - retentionInformation N C = Real.log (mass N C / mass N B) := by
  have hb := (HistoryHaarSectionProbability.mass_pos_of_pos N hB).ne'
  have hc := (HistoryHaarSectionProbability.mass_pos_of_pos N hC).ne'
  have hz := (fullBudget_pos N).ne'
  simp only [retentionInformation, retention, Real.log_div hb hz, Real.log_div hc hz,
    Real.log_div hc hb]
  ring

theorem existsUnique_retention_threshold (N : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃! B : ℝ, 0 < B ∧ retention N B = r := by
  have he : ∀ᶠ C : ℝ in atTop, r < retention N C :=
    (tendsto_order.mp (retention_tendsto_one N)).1 r hr1
  obtain ⟨C, hC, hC0⟩ := (he.and (eventually_ge_atTop (0 : ℝ))).exists
  have ht : r ∈ Icc (retention N 0) (retention N C) := by
    rw [retention_zero]
    exact ⟨hr.le, hC.le⟩
  obtain ⟨B, hB, hBr⟩ := intermediate_value_Icc hC0 (retention_continuous N).continuousOn ht
  have hB0 : 0 < B := by
    by_contra hn
    have hz : B = 0 := le_antisymm (le_of_not_gt hn) hB.1
    subst B
    rw [retention_zero] at hBr
    linarith
  refine ⟨B, ⟨hB0, hBr⟩, ?_⟩
  intro D hD
  exact (retention_strictMonoOn N).injOn hD.1.le hB0.le (hD.2.trans hBr.symm)

/-- Distinct positive kinetic shells of the original coclosed field. -/
def fieldPosition (j : ℕ) : ℝ := 4 * ((j : ℝ) + 1) ^ 2

theorem field_kinetic_position (N : ℕ) (a : HistoryHaarClosedHessian.BasisIndex N) :
    ∃ j, kinetic N (.inl a) = fieldPosition j := by
  obtain ⟨l, ⟨j, hj⟩, _, he⟩ :=
    Geometry.SourceOneFormCurlBranches.every_nongauge_field_mode_has_odd_degree
      a.2.val a.2.property
  refine ⟨j, ?_⟩
  change Geometry.SourceOneFormCurlSpectrum.eigenvalue a.2.val ^ 2 = _
  rw [he, hj]
  push_cast
  unfold fieldPosition
  ring

theorem every_field_position_realized (N j : ℕ) :
    ∃ a : HistoryHaarClosedHessian.BasisIndex N,
      kinetic N (.inl a) = fieldPosition j := by
  let m := 2 * (j + 1)
  have hm : Even m := ⟨j + 1, by dsimp [m]; omega⟩
  have hm0 : m ≠ 0 := by dsimp [m]; omega
  have hp : 0 < Geometry.SourceOneFormMultiplicity.minusMultiplicity m := by
    rw [(Geometry.SourceOneFormMultiplicity.nonconstant_branch_multiplicities hm hm0).2]
    dsimp [m]
    omega
  obtain ⟨k, hk⟩ := Fintype.card_pos_iff.mp hp
  let a : Geometry.SourceOneFormCoclosedSpectrum.CoclosedIndex :=
    ⟨⟨⟨⟨m, hm⟩, 0⟩, k⟩, by
      change Geometry.SourceOneFormSpectralCore.curlEigenvalue m k ≠ 0
      rw [hk]
      exact neg_ne_zero.mpr (by exact_mod_cast hm0)⟩
  let h := (basePositionLabel N 0).1
  refine ⟨((h, h), a), ?_⟩
  change Geometry.SourceOneFormSpectralCore.curlEigenvalue m k ^ 2 = _
  rw [hk, neg_sq]
  dsimp [m, fieldPosition]
  push_cast
  ring

/-- This counts spectral positions, not polarization or history labels. -/
def fieldPositionCount (B : ℝ) : ℕ := Nat.ceil (Real.sqrt B / 2) - 1

theorem fieldPosition_lt_iff (j : ℕ) (B : ℝ) :
    fieldPosition j < B ↔ j < fieldPositionCount B := by
  have hc : j < Nat.ceil (Real.sqrt B / 2) - 1 ↔
      j + 1 < Nat.ceil (Real.sqrt B / 2) := by omega
  simp only [fieldPositionCount, hc, Nat.lt_ceil, Nat.cast_add, Nat.cast_one]
  have hs : 2 * ((j : ℝ) + 1) < Real.sqrt B ↔
      (2 * ((j : ℝ) + 1)) ^ 2 < B := Real.lt_sqrt (by positivity)
  unfold fieldPosition
  constructor
  · intro h
    have hh := hs.mpr (by nlinarith)
    linarith
  · intro h
    have hh := hs.mp (by linarith)
    nlinarith

/-- A counted field shell is present if and only if an original field
label of that shell belongs to the original joint support. -/
theorem field_content_realized_iff (N j : ℕ) (B : ℝ) :
    j < fieldPositionCount B ↔
      ∃ a : HistoryHaarClosedHessian.BasisIndex N,
        Sum.inl a ∈ support N B ∧ kinetic N (.inl a) = fieldPosition j := by
  constructor
  · intro hj
    obtain ⟨a, ha⟩ := every_field_position_realized N j
    exact ⟨a, (mem_support N B _).mpr (by
      rw [ha]; exact (fieldPosition_lt_iff j B).mpr hj), ha⟩
  · rintro ⟨a, ha, he⟩
    exact (fieldPosition_lt_iff j B).mp (he ▸ (mem_support N B _).mp ha)

theorem scalar_field_interlacing (j : ℕ) :
    position j < fieldPosition j ∧ fieldPosition j < position (j + 1) := by
  simp only [Geometry.SourceScalarKineticForm.position_eq, fieldPosition,
    Nat.cast_add, Nat.cast_one]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor <;> nlinarith

/-- The two contents cannot be chosen independently: their difference
is at most the single scalar birth between two successive field shells. -/
theorem joint_content_bounds (B : ℝ) :
    fieldPositionCount B ≤ positionCount B ∧
      positionCount B ≤ fieldPositionCount B + 1 := by
  constructor
  · by_contra hn
    have hf := (fieldPosition_lt_iff (positionCount B) B).mpr (Nat.lt_of_not_ge hn)
    have hs := (position_lt_iff (positionCount B) B).mp
      ((scalar_field_interlacing (positionCount B)).1.trans hf)
    exact (Nat.lt_irrefl _) hs
  · by_contra hn
    have hs := (position_lt_iff (fieldPositionCount B + 1) B).mpr
      (Nat.lt_of_not_ge hn)
    have hf := (fieldPosition_lt_iff (fieldPositionCount B) B).mp
      ((scalar_field_interlacing (fieldPositionCount B)).2.trans hs)
    exact (Nat.lt_irrefl _) hf

theorem joint_content_alternatives (B : ℝ) :
    positionCount B = fieldPositionCount B ∨
      positionCount B = fieldPositionCount B + 1 := by
  have h := joint_content_bounds B
  omega

theorem field_count_eq_succ_iff (B : ℝ) (j : ℕ) :
    fieldPositionCount B = j + 1 ↔
      fieldPosition j < B ∧ B ≤ fieldPosition (j + 1) := by
  constructor
  · intro h
    constructor
    · exact (fieldPosition_lt_iff j B).mpr (by omega)
    · exact le_of_not_gt (fun hb => by
        have hc := (fieldPosition_lt_iff (j + 1) B).mp hb
        omega)
  · rintro ⟨hl, hu⟩
    have hl' := (fieldPosition_lt_iff j B).mp hl
    have hu' : ¬ j + 1 < fieldPositionCount B := fun h =>
      (not_lt_of_ge hu) ((fieldPosition_lt_iff (j + 1) B).mpr h)
    omega

/-- First half of each joint spectral cell. Both sector counts are
computed on one cutoff, with the strict birth and retained upper edge. -/
theorem joint_equal_cell (B : ℝ) (j : ℕ) :
    (fieldPositionCount B = j + 1 ∧ positionCount B = j + 1) ↔
      fieldPosition j < B ∧ B ≤ position (j + 1) := by
  rw [field_count_eq_succ_iff, positionCount_eq_succ_iff]
  have h0 := scalar_field_interlacing j
  have h1 := scalar_field_interlacing (j + 1)
  constructor
  · exact fun h => ⟨h.1.1, h.2.2⟩
  · exact fun h => ⟨⟨h.1, h.2.trans h1.1.le⟩,
      ⟨h0.1.trans h.1, h.2⟩⟩

/-- Second half, including the initial scalar-only window. -/
theorem joint_scalar_birth_cell (B : ℝ) (j : ℕ) :
    (fieldPositionCount B = j ∧ positionCount B = j + 1) ↔
      position j < B ∧ B ≤ fieldPosition j := by
  constructor
  · rintro ⟨hf, hs⟩
    refine ⟨((positionCount_eq_succ_iff B j).mp hs).1, ?_⟩
    exact le_of_not_gt (fun h => by
      have hc := (fieldPosition_lt_iff j B).mp h
      omega)
  · rintro ⟨hl, hu⟩
    have hs : positionCount B = j + 1 := (positionCount_eq_succ_iff B j).mpr
      ⟨hl, hu.trans (scalar_field_interlacing j).2.le⟩
    have hf : fieldPositionCount B ≤ j := by
      by_contra hn
      exact (not_lt_of_ge hu) ((fieldPosition_lt_iff j B).mpr (Nat.lt_of_not_ge hn))
    have hb := joint_content_bounds B
    exact ⟨by omega, hs⟩

private theorem band_iff_response (N : ℕ) {B a b : ℝ}
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a < B ∧ B ≤ b) ↔
      (responseTrace N a < responseTrace N B ∧ responseTrace N B ≤ responseTrace N b) := by
  have ht := HistoryHaarSectionWindow.responseTrace_strictMonoOn N
  constructor
  · exact fun h => ⟨ht ha hB h.1, ht.monotoneOn hB hb h.2⟩
  · rintro ⟨hl, hu⟩
    constructor
    · exact lt_of_not_ge (fun h => (not_lt_of_ge (ht.monotoneOn hB ha h)) hl)
    · exact le_of_not_gt (fun h => (not_lt_of_ge hu) (ht hb hB h))

/-- Joint shell and content selection can be tested with two values of
the same complete Gaussian response. No sector is removed in either test. -/
theorem joint_equal_cell_response (N j : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (fieldPositionCount B = j + 1 ∧ positionCount B = j + 1) ↔
      responseTrace N (fieldPosition j) < responseTrace N B ∧
        responseTrace N B ≤ responseTrace N (position (j + 1)) := by
  rw [joint_equal_cell]
  exact band_iff_response N hB (by unfold fieldPosition; positivity)
    (Geometry.SourceCasimirClosure.energy_nonneg _)

theorem joint_scalar_birth_cell_response (N j : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (fieldPositionCount B = j ∧ positionCount B = j + 1) ↔
      responseTrace N (position j) < responseTrace N B ∧
        responseTrace N B ≤ responseTrace N (fieldPosition j) := by
  rw [joint_scalar_birth_cell]
  exact band_iff_response N hB (Geometry.SourceCasimirClosure.energy_nonneg _)
    (by unfold fieldPosition; positivity)

private theorem band_iff_retention (N : ℕ) {B a b : ℝ}
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a < B ∧ B ≤ b) ↔
      (retention N a < retention N B ∧ retention N B ≤ retention N b) := by
  have ht := retention_strictMonoOn N
  constructor
  · exact fun h => ⟨ht ha hB h.1, ht.monotoneOn hB hb h.2⟩
  · rintro ⟨hl, hu⟩
    constructor
    · exact lt_of_not_ge (fun h => (not_lt_of_ge (ht.monotoneOn hB ha h)) hl)
    · exact le_of_not_gt (fun h => (not_lt_of_ge hu) (ht hb hB h))

/-- The full-source retention and the original response test exactly the
same joint cell. No target retention or preferred content count is imposed. -/
theorem joint_equal_cell_retention (N j : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (fieldPositionCount B = j + 1 ∧ positionCount B = j + 1) ↔
      retention N (fieldPosition j) < retention N B ∧
        retention N B ≤ retention N (position (j + 1)) := by
  rw [joint_equal_cell]
  exact band_iff_retention N hB (by unfold fieldPosition; positivity)
    (Geometry.SourceCasimirClosure.energy_nonneg _)

theorem joint_scalar_birth_cell_retention (N j : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (fieldPositionCount B = j ∧ positionCount B = j + 1) ↔
      retention N (position j) < retention N B ∧
        retention N B ≤ retention N (fieldPosition j) := by
  rw [joint_scalar_birth_cell]
  exact band_iff_retention N hB (Geometry.SourceCasimirClosure.energy_nonneg _)
    (by unfold fieldPosition; positivity)

theorem initial_scalar_cell (B : ℝ) :
    (fieldPositionCount B = 0 ∧ positionCount B = 1) ↔ 0 < B ∧ B ≤ 4 := by
  have h := joint_scalar_birth_cell B 0
  norm_num [fieldPosition, Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

theorem first_joint_cell (B : ℝ) :
    (fieldPositionCount B = 1 ∧ positionCount B = 1) ↔ 4 < B ∧ B ≤ 8 := by
  have h := joint_equal_cell B 0
  norm_num [fieldPosition, Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

theorem second_joint_cell (B : ℝ) :
    (fieldPositionCount B = 1 ∧ positionCount B = 2) ↔ 8 < B ∧ B ≤ 16 := by
  have h := joint_scalar_birth_cell B 1
  norm_num [fieldPosition, Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

theorem third_joint_cell (B : ℝ) :
    (fieldPositionCount B = 2 ∧ positionCount B = 2) ↔ 16 < B ∧ B ≤ 24 := by
  have h := joint_equal_cell B 1
  norm_num [fieldPosition, Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

theorem fourth_joint_cell (B : ℝ) :
    (fieldPositionCount B = 2 ∧ positionCount B = 3) ↔ 24 < B ∧ B ≤ 36 := by
  have h := joint_scalar_birth_cell B 2
  norm_num [fieldPosition, Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

theorem fifth_joint_cell (B : ℝ) :
    (fieldPositionCount B = 3 ∧ positionCount B = 3) ↔ 36 < B ∧ B ≤ 48 := by
  have h := joint_equal_cell B 2
  norm_num [fieldPosition, Geometry.SourceScalarKineticForm.position_eq] at h
  exact h

structure Conclusions : Prop where
  complete_gaussian_mass : ∀ N, Tendsto (mass N) atTop (𝓝 (fullBudget N))
  positive_full_mass : ∀ N, 0 < fullBudget N
  exact_gaussian_rows : ∀ N B, mass N B =
    (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * ∑' m, fieldRow B m +
      ∑' j, scalarMassRow N B j
  actual_retention_bounds : ∀ N B, 0 < B → 0 < retention N B ∧ retention N B < 1
  exhaustive_retention : ∀ N, Tendsto (retention N) atTop (𝓝 1)
  window_information_transfer : ∀ N B C, 0 < B → 0 < C →
    retentionInformation N B - retentionInformation N C = Real.log (mass N C / mass N B)
  all_field_shells_actual : ∀ N j, ∃ a : HistoryHaarClosedHessian.BasisIndex N,
    kinetic N (.inl a) = fieldPosition j
  joint_content : ∀ B, positionCount B = fieldPositionCount B ∨
    positionCount B = fieldPositionCount B + 1
  common_equal_cell : ∀ N j B, 0 ≤ B →
    ((fieldPositionCount B = j + 1 ∧ positionCount B = j + 1) ↔
      responseTrace N (fieldPosition j) < responseTrace N B ∧
        responseTrace N B ≤ responseTrace N (position (j + 1)))
  common_scalar_birth_cell : ∀ N j B, 0 ≤ B →
    ((fieldPositionCount B = j ∧ positionCount B = j + 1) ↔
      responseTrace N (position j) < responseTrace N B ∧
        responseTrace N B ≤ responseTrace N (fieldPosition j))
  complete_retention_cell : ∀ N j B, 0 ≤ B →
    ((fieldPositionCount B = j + 1 ∧ positionCount B = j + 1) ↔
      retention N (fieldPosition j) < retention N B ∧
        retention N B ≤ retention N (position (j + 1)))

theorem generated : Conclusions where
  complete_gaussian_mass := mass_tendsto_fullBudget
  positive_full_mass := fullBudget_pos
  exact_gaussian_rows := mass_eq_tsum_rows
  actual_retention_bounds := fun N _ hB => ⟨retention_pos N hB, retention_lt_one N hB.le⟩
  exhaustive_retention := retention_tendsto_one
  window_information_transfer := fun N _ _ hB hC => retentionInformation_change N hB hC
  all_field_shells_actual := every_field_position_realized
  joint_content := joint_content_alternatives
  common_equal_cell := fun N j _ hB => joint_equal_cell_response N j hB
  common_scalar_birth_cell := fun N j _ hB => joint_scalar_birth_cell_response N j hB
  complete_retention_cell := fun N j _ hB => joint_equal_cell_retention N j hB

end GeneratedFoundations.Arithmetic.HistoryHaarSectionRetention
