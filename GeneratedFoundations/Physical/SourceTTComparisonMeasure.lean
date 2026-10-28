module

public import GeneratedFoundations.Physical.SourceTTCapacitySpectrum
public import GeneratedFoundations.Physical.SourceTTComparisonTransport
public import GeneratedFoundations.Operations.PositiveMomentCompletion
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The retained TT comparison trace as a finite positive measure

The measure below retains all eight branches, their original continuous
frequency integrals, their multiplicities and the Gaussian trace unit.
Its moments are exactly the higher same-source responses already defined
in `SourceTTComparisonTransport`. Positive mass near the actual first-branch
peak then supplies the endpoint hypotheses of the positive-moment theorems.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators

namespace GeneratedFoundations.Physical.SourceTTComparisonMeasure

open SourceTTCapacitySpectrum

abbrev Space := Branch × ℝ

/-- The original frequency density, with its multiplicity and trace unit. -/
def density (i : Branch) (u : ℝ) : ℝ := weight i u / (32 * Real.pi ^ 3)

theorem density_pos (i : Branch) (u : ℝ) : 0 < density i u := by
  exact div_pos (weight_pos i u) (by positivity)

theorem density_continuous (i : Branch) : Continuous (density i) := by
  unfold density weight
  fun_prop

def branchMeasure (i : Branch) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 (upper i))).withDensity
    (fun u => ENNReal.ofReal (density i u))

instance branchMeasure_finite (i : Branch) : IsFiniteMeasure (branchMeasure i) := by
  exact isFiniteMeasure_withDensity_ofReal (density_continuous i).integrableOn_Icc.2

def placedMeasure (i : Branch) : Measure Space :=
  Measure.map (fun u => (i, u)) (branchMeasure i)

instance placedMeasure_finite (i : Branch) : IsFiniteMeasure (placedMeasure i) :=
  (branchMeasure i).isFiniteMeasure_map _

/-- A finite measure representing the retained frequency trace, rather
than a new Gaussian probability law. -/
def sourceMeasure : Measure Space := ∑ i : Branch, placedMeasure i

instance sourceMeasure_finite : IsFiniteMeasure sourceMeasure := by
  unfold sourceMeasure
  infer_instance

def response (x : Space) : ℝ := capacity x.1 x.2

theorem response_continuous : Continuous response :=
  continuous_prod_of_discrete_left.mpr capacity_continuous

theorem response_bounds (x : Space) : 0 ≤ response x ∧ response x ≤ (4 / 27 : ℝ) :=
  capacity_bounds x.1 x.2

theorem upper_nonneg (i : Branch) : 0 ≤ upper i := Real.sqrt_nonneg _

theorem branch_moment (i : Branch) (n : ℕ) :
    (∫ u, capacity i u ^ n ∂branchMeasure i) =
      (1 / (32 * Real.pi ^ 3)) * SourceTTCapacitySpectrum.multiplicity i *
        ∫ u in (0 : ℝ)..upper i,
          SourceTTComparisonTransport.momentProfile n 0 (kinetic i) (mass i) 0 u := by
  unfold branchMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((density_continuous i).measurable.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (density_pos i _).le, smul_eq_mul]
  have he : (fun u => density i u * capacity i u ^ n) =
      (fun u => ((1 / (32 * Real.pi ^ 3)) * SourceTTCapacitySpectrum.multiplicity i) *
        SourceTTComparisonTransport.momentProfile n 0 (kinetic i) (mass i) 0 u) := by
    funext u
    simp only [density, weight, SourceTTComparisonTransport.momentProfile,
      pow_zero, one_mul, SourceTTComparisonTransport.capacity,
      SourceTTCollectiveVariance.fraction, capacity, fraction,
      SourceTTCollectiveComparison.envelope, Real.exp_zero, one_mul]
    ring
  rw [he, integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (upper_nonneg i)]

theorem source_moment (n : ℕ) :
    Operations.PositiveMomentRatios.moment sourceMeasure response n =
      SourceTTComparisonTransport.traceMoment n 0 0 := by
  unfold Operations.PositiveMomentRatios.moment sourceMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    Operations.PositiveMomentRatios.integrable_pow_of_bound
      (μ := placedMeasure i) response_continuous.measurable response_bounds n)]
  unfold SourceTTComparisonTransport.traceMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hf : AEStronglyMeasurable (fun x : Space => response x ^ n)
      (Measure.map (fun u : ℝ => (i, u)) (branchMeasure i)) := by
    exact ((continuous_pow n).comp response_continuous).aestronglyMeasurable
  rw [placedMeasure, integral_map (f := fun x : Space => response x ^ n)
    (by fun_prop : Measurable (fun u : ℝ => (i, u))).aemeasurable hf]
  simpa only [response, mul_assoc, SourceTTCapacitySpectrum.multiplicity,
    kinetic, mass, upper, SourceTTCollectiveComparison.upper] using branch_moment i n

theorem peakFrequency_interior : peakFrequency ∈ Set.Ioo (0 : ℝ) (upper 0) := by
  constructor
  · exact Real.sqrt_pos.2 (by norm_num)
  · change Real.sqrt (3 / 2) < Real.sqrt (5 * Real.pi - 0)
    apply Real.sqrt_lt_sqrt (by norm_num)
    linarith [Real.pi_gt_three]

/-- Each source interval near the genuine first-branch peak has positive
original trace mass; no atomic reference measure is substituted. -/
theorem branch_peak_mass (ε : ℝ) (hε : 0 < ε) :
    0 < branchMeasure 0 {u | (4 / 27 : ℝ) - ε ≤ capacity 0 u} := by
  let s : Set ℝ := Set.Ioo 0 (upper 0) ∩ {u | (4 / 27 : ℝ) - ε < capacity 0 u}
  have hsopen : IsOpen s := isOpen_Ioo.inter
    (isOpen_lt continuous_const (capacity_continuous 0))
  have hsnonempty : s.Nonempty := by
    refine ⟨peakFrequency, peakFrequency_interior, ?_⟩
    change (4 / 27 : ℝ) - ε < capacity 0 peakFrequency
    rw [capacity_first_peak]
    linarith
  have hspos : 0 < volume s := hsopen.measure_pos volume hsnonempty
  have hlevel : MeasurableSet {u | (4 / 27 : ℝ) - ε ≤ capacity 0 u} :=
    measurableSet_le measurable_const (capacity_continuous 0).measurable
  have hbase : 0 < (volume.restrict (Set.Icc 0 (upper 0)))
      {u | (4 / 27 : ℝ) - ε ≤ capacity 0 u} := by
    rw [Measure.restrict_apply hlevel]
    apply hspos.trans_le
    apply measure_mono
    intro u hu
    have hu' : u ∈ Set.Ioo 0 (upper 0) ∧
        (4 / 27 : ℝ) - ε < capacity 0 u := hu
    change (4 / 27 : ℝ) - ε ≤ capacity 0 u ∧ 0 ≤ u ∧ u ≤ upper 0
    exact ⟨hu'.2.le, hu'.1.1.le, hu'.1.2.le⟩
  apply lt_of_le_of_ne bot_le
  intro hzero
  have hz := (withDensity_apply_eq_zero
    ((density_continuous 0).measurable.ennreal_ofReal)).1 hzero.symm
  have he : {u : ℝ | ENNReal.ofReal (density 0 u) ≠ 0} = Set.univ := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.2 (density_pos 0 u)).ne'
  rw [he, Set.univ_inter] at hz
  exact hbase.ne' hz

theorem peak_mass (ε : ℝ) (hε : 0 < ε) :
    0 < sourceMeasure.real {x | (4 / 27 : ℝ) - ε ≤ response x} := by
  have hs : MeasurableSet {x | (4 / 27 : ℝ) - ε ≤ response x} :=
    measurableSet_le measurable_const response_continuous.measurable
  have hm : placedMeasure 0 ≤ sourceMeasure := by
    unfold sourceMeasure
    exact Finset.single_le_sum (fun i _ => bot_le) (Finset.mem_univ 0)
  have hp : 0 < placedMeasure 0 {x | (4 / 27 : ℝ) - ε ≤ response x} := by
    rw [placedMeasure, Measure.map_apply (by fun_prop) hs]
    exact branch_peak_mass ε hε
  exact ENNReal.toReal_pos (hp.trans_le (hm _)).ne' (measure_ne_top _ _)

theorem source_ratio_tendsto :
    Tendsto (Operations.PositiveMomentRatios.ratio sourceMeasure response)
      atTop (𝓝 (4 / 27 : ℝ)) :=
  Operations.PositiveMomentRatios.ratio_tendsto response_continuous.measurable
    response_bounds (by norm_num) peak_mass

theorem source_budget_iff (r : ℝ) :
    Operations.PositiveMomentCompletion.IsMomentBudget sourceMeasure response r ↔
      (4 / 27 : ℝ) ≤ r :=
  Operations.PositiveMomentCompletion.moment_budget_iff response_continuous.measurable
    response_bounds (by norm_num) peak_mass

/-- The adjacent ratios use the original trace integrals exactly. -/
theorem trace_ratio_tendsto :
    Tendsto (fun n : ℕ => SourceTTComparisonTransport.traceMoment (n + 1) 0 0 /
      SourceTTComparisonTransport.traceMoment n 0 0)
      atTop (𝓝 (4 / 27 : ℝ)) := by
  have he : Operations.PositiveMomentRatios.ratio sourceMeasure response =
      (fun n : ℕ => SourceTTComparisonTransport.traceMoment (n + 1) 0 0 /
        SourceTTComparisonTransport.traceMoment n 0 0) := by
    funext n
    simp only [Operations.PositiveMomentRatios.ratio, source_moment]
  rw [← he]
  exact source_ratio_tendsto

theorem least_source_budget :
    IsLeast {r : ℝ |
      Operations.PositiveMomentCompletion.IsMomentBudget sourceMeasure response r}
      (4 / 27 : ℝ) :=
  Operations.PositiveMomentCompletion.least_moment_budget response_continuous.measurable
    response_bounds (by norm_num) peak_mass

end GeneratedFoundations.Physical.SourceTTComparisonMeasure
