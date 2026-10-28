module

public import GeneratedFoundations.Physical.SourceTTCollectiveVariance

/-!
# Maximum-response reference for the TT endpoint

The reference uses the same per-leg logarithmic mass response as the
retained trace. Its parameter `t` is the reference mass/kinetic ratio
relative to its maximizing value. The actual source coefficient is held
fixed when this reference is varied. This is a calibration comparison,
not a mass deformation or an update of the full physical source.

The peak gives a stationary, globally least reference-matched radius.
Its exact calibration defect is quadratic at the peak. The second part
retains the full frequency trace and identifies its capacity deficit as
an integral, with the original weights and bandwidth unchanged.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Physical.SourceTTReferenceCalibration

open SourceTensorResponseEndpoint SourceTTCollectiveComparison
  SourceTTCollectiveVariance

/-- `t = 1` means the reference mass/kinetic ratio is one half. -/
def referenceLevel (t : ℝ) : ℝ :=
  massWeightedResponse (massFraction 2 t)

theorem referenceLevel_eq {t : ℝ} (ht : 0 < t) :
    referenceLevel t = 4 * t / (t + 2) ^ 3 := by
  unfold referenceLevel massFraction massWeightedResponse
  field_simp [show 2 + t ≠ 0 by linarith, show t + 2 ≠ 0 by linarith]
  ring

theorem referenceLevel_pos {t : ℝ} (ht : 0 < t) : 0 < referenceLevel t := by
  rw [referenceLevel_eq ht]
  positivity

@[simp] theorem referenceLevel_one : referenceLevel 1 = (4 / 27 : ℝ) := by
  norm_num [referenceLevel, massFraction, massWeightedResponse]

def referenceRadius (A t : ℝ) : ℝ := A / referenceLevel t

theorem referenceRadius_eq {t : ℝ} (ht : 0 < t) (A : ℝ) :
    referenceRadius A t = A * (t + 2) ^ 3 / (4 * t) := by
  rw [referenceRadius, referenceLevel_eq ht]
  field_simp

@[simp] theorem referenceRadius_one (A : ℝ) :
    referenceRadius A 1 = endpointRoot A := by
  rw [referenceRadius, referenceLevel_one, endpointRoot]
  ring

/-- Exact sensitivity to a reference-ratio change, holding the actual
spectral coefficient fixed. The leading error is quadratic. -/
theorem relative_reference_defect {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    referenceRadius A t / endpointRoot A - 1 =
      (t - 1) ^ 2 * (t + 8) / (27 * t) := by
  rw [referenceRadius_eq ht, endpointRoot]
  field_simp [hA.ne', ht.ne']
  ring

theorem peak_reference_least {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    endpointRoot A ≤ referenceRadius A t := by
  have hd : 0 ≤ referenceRadius A t / endpointRoot A - 1 := by
    rw [relative_reference_defect hA ht]
    positivity
  have he := (le_div_iff₀ (endpointRoot_pos hA)).1 (by linarith :
    1 ≤ referenceRadius A t / endpointRoot A)
  simpa only [one_mul] using he

theorem peak_reference_equality_iff {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    referenceRadius A t = endpointRoot A ↔ t = 1 := by
  constructor
  · intro he
    have hd := relative_reference_defect hA ht
    rw [he, div_self (endpointRoot_pos hA).ne', sub_self] at hd
    have hz : (t - 1) ^ 2 * (t + 8) = 0 :=
      (div_eq_zero_iff.mp hd.symm).resolve_right (by positivity)
    have hs : (t - 1) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_right (by linarith)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · rintro rfl
    exact referenceRadius_one A

theorem referenceRadius_hasDerivAt {t : ℝ} (ht : 0 < t) (A : ℝ) :
    HasDerivAt (referenceRadius A)
      (A * (t + 2) ^ 2 * (t - 1) / (2 * t ^ 2)) t := by
  have hd := ((((hasDerivAt_id t).add_const 2).pow 3).const_mul A).div
    ((hasDerivAt_id t).const_mul 4) (by positivity : 4 * id t ≠ 0)
  have hf : ∀ᶠ s in nhds t, referenceRadius A s = A * (s + 2) ^ 3 / (4 * s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact referenceRadius_eq hs A
  convert! hd.congr_of_eventuallyEq hf using 1
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat]
  field_simp [ht.ne']
  ring

theorem referenceRadius_stationary (A : ℝ) :
    HasDerivAt (referenceRadius A) 0 1 := by
  simpa only [sub_self, mul_zero, zero_div] using
    referenceRadius_hasDerivAt (by norm_num : (0 : ℝ) < 1) A

/-- A ten percent change of the reference mass/kinetic ratio changes the
matched radius by at most `89/24300`, with the source held fixed. -/
theorem ten_percent_reference_bound {A t : ℝ} (hA : 0 < A)
    (ht0 : 9 / 10 ≤ t) (ht1 : t ≤ 11 / 10) :
    0 ≤ referenceRadius A t / endpointRoot A - 1 ∧
      referenceRadius A t / endpointRoot A - 1 ≤ (89 / 24300 : ℝ) := by
  have ht : 0 < t := by linarith
  rw [relative_reference_defect hA ht]
  have hs : (t - 1) ^ 2 ≤ (1 / 100 : ℝ) := by nlinarith
  have hr : (t + 8) / (27 * t) ≤ (89 / 243 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 27 * t)).2
    linarith
  constructor
  · positivity
  · calc
      (t - 1) ^ 2 * (t + 8) / (27 * t) =
          (t - 1) ^ 2 * ((t + 8) / (27 * t)) := by ring
      _ ≤ (1 / 100 : ℝ) * (89 / 243) :=
        mul_le_mul hs hr (by positivity) (by norm_num)
      _ = _ := by norm_num

def deficitProfile (a b z u : ℝ) : ℝ :=
  (fraction a b z u - 1 / 3) ^ 2 * (4 / 3 - fraction a b z u) * envelope a u

theorem deficitProfile_eq (a b z u : ℝ) :
    deficitProfile a b z u =
      (4 / 27 : ℝ) * envelope a u - capacityProfile a b z u := by
  rw [deficitProfile, ← response_factorization]
  unfold fraction capacityProfile
  ring

/-- The average's deficit from the reference maximum is evaluated on the
original spectrum. Equality of a single reference is never substituted
for the varying fractions in this trace. -/
theorem actual_trace_capacity_deficit (z : ℝ) :
    (4 / 27 : ℝ) * weightCoefficient - capacityCoefficient z =
      (1 / (32 * Real.pi ^ 3)) *
        ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 *
          ∫ u in (0 : ℝ)..upper i,
            deficitProfile (SourceTTGaussianCoefficient.branch i).1
              (SourceTTGaussianCoefficient.branch i).2.1 z u := by
  have hi (i : Branch) :
      (∫ u in (0 : ℝ)..upper i,
        deficitProfile (SourceTTGaussianCoefficient.branch i).1
          (SourceTTGaussianCoefficient.branch i).2.1 z u) =
      (4 / 27 : ℝ) * weightIntegral i - capacityIntegral z i := by
    have ha := (SourceTTGaussianCoefficient.branch_bounds i).1
    have hb := (SourceTTGaussianCoefficient.branch_bounds i).2.2.1
    simp_rw [deficitProfile_eq]
    rw [intervalIntegral.integral_sub
      (f := fun u => (4 / 27 : ℝ) * envelope (SourceTTGaussianCoefficient.branch i).1 u)
      (g := fun u => capacityProfile (SourceTTGaussianCoefficient.branch i).1
        (SourceTTGaussianCoefficient.branch i).2.1 z u)
      ((by unfold envelope; fun_prop : Continuous
        (fun u => (4 / 27 : ℝ) * envelope (SourceTTGaussianCoefficient.branch i).1 u)).intervalIntegrable _ _)
      ((capacityProfile_continuous ha hb z).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
    rfl
  simp_rw [hi]
  unfold weightCoefficient capacityCoefficient
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end GeneratedFoundations.Physical.SourceTTReferenceCalibration
