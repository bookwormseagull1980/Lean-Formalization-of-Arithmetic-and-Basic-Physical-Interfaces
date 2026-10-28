module

public import GeneratedFoundations.Physical.SourceTTGaussianCoefficient
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Exact range of the original eight-branch TT capacity readout

The mass-weighted response is evaluated on the original branch data and
frequency intervals.  Its complete pointwise range is `[0, 4/27]`:
the first branch reaches the upper endpoint at `sqrt (3/2)`, and every
other branch lies strictly below it.  Thus the half-readout has greatest
value `2/27`, with no change to the source weights or bandwidth.

These are range and supremum statements about the actual frequency
readout.  They do not identify a multiplication-operator spectrum or a
physical source-update generator.
-/

@[expose] public section
noncomputable section

namespace GeneratedFoundations.Physical.SourceTTCapacitySpectrum

open SourceTensorResponseEndpoint

abbrev Branch := Fin 8

def kinetic (i : Branch) : ℝ := (SourceTTGaussianCoefficient.branch i).1

def mass (i : Branch) : ℝ := (SourceTTGaussianCoefficient.branch i).2.1

def multiplicity (i : Branch) : ℝ := (SourceTTGaussianCoefficient.branch i).2.2

def upper (i : Branch) : ℝ := Real.sqrt (5 * Real.pi - kinetic i)

def fraction (i : Branch) (u : ℝ) : ℝ := massFraction (u ^ 2 + kinetic i) (mass i)

def capacity (i : Branch) (u : ℝ) : ℝ := massWeightedResponse (fraction i u)

/-- The original finite collection of closed frequency intervals. -/
def Frequency := {p : Branch × ℝ // p.2 ∈ Set.Icc 0 (upper p.1)}

def readout (x : Frequency) : ℝ := capacity x.1.1 x.1.2

def halfReadout (x : Frequency) : ℝ := readout x / 2

/-- The source envelope, including its original positive multiplicity. -/
def weight (i : Branch) (u : ℝ) : ℝ :=
  multiplicity i * Real.exp (-(u ^ 2 + kinetic i) / Real.pi)

theorem kinetic_nonneg (i : Branch) : 0 ≤ kinetic i :=
  (SourceTTGaussianCoefficient.branch_bounds i).1

theorem mass_pos (i : Branch) : 0 < mass i :=
  (SourceTTGaussianCoefficient.branch_bounds i).2.2.1

theorem multiplicity_pos (i : Branch) : 0 < multiplicity i :=
  (SourceTTGaussianCoefficient.branch_bounds i).2.2.2

theorem precision_pos (i : Branch) (u : ℝ) : 0 < u ^ 2 + kinetic i + mass i := by
  have ha := kinetic_nonneg i
  have hb := mass_pos i
  nlinarith [sq_nonneg u]

theorem fraction_bounds (i : Branch) (u : ℝ) :
    0 ≤ fraction i u ∧ fraction i u ≤ 1 := by
  exact massFraction_mem_unitInterval (by nlinarith [kinetic_nonneg i, sq_nonneg u])
    (mass_pos i).le (precision_pos i u)

theorem capacity_bounds (i : Branch) (u : ℝ) :
    0 ≤ capacity i u ∧ capacity i u ≤ (4 / 27 : ℝ) := by
  obtain ⟨h0, h1⟩ := fraction_bounds i u
  exact ⟨mul_nonneg h0 (sq_nonneg _), massWeightedResponse_le h0 h1⟩

theorem capacity_continuous (i : Branch) : Continuous (capacity i) := by
  have hf : Continuous (fraction i) := by
    unfold fraction massFraction
    exact continuous_const.div (by fun_prop) (fun u => (precision_pos i u).ne')
  exact hf.mul ((continuous_const.sub hf).pow 2)

theorem weight_pos (i : Branch) (u : ℝ) : 0 < weight i u :=
  mul_pos (multiplicity_pos i) (Real.exp_pos _)

def peakFrequency : ℝ := Real.sqrt (3 / 2)

theorem peakFrequency_nonneg : 0 ≤ peakFrequency := Real.sqrt_nonneg _

theorem peakFrequency_sq : peakFrequency ^ 2 = (3 / 2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

theorem peakFrequency_mem : peakFrequency ∈ Set.Icc (0 : ℝ) (upper 0) := by
  constructor
  · exact peakFrequency_nonneg
  · change Real.sqrt (3 / 2) ≤ Real.sqrt (5 * Real.pi - 0)
    rw [sub_zero]
    apply Real.sqrt_le_sqrt
    linarith [Real.pi_gt_three]

@[simp] theorem capacity_first_zero : capacity 0 0 = 0 := by
  norm_num [capacity, fraction, kinetic, mass, SourceTTGaussianCoefficient.branch,
    massFraction, massWeightedResponse]

@[simp] theorem capacity_first_peak : capacity 0 peakFrequency = (4 / 27 : ℝ) := by
  unfold capacity fraction
  rw [peakFrequency_sq]
  norm_num [kinetic, mass, SourceTTGaussianCoefficient.branch,
    massFraction, massWeightedResponse]

theorem capacity_first_eq_peak_iff {u : ℝ} (hu : 0 ≤ u) :
    capacity 0 u = (4 / 27 : ℝ) ↔ u = peakFrequency := by
  constructor
  · intro he
    obtain ⟨h0, h1⟩ := fraction_bounds 0 u
    have hf := (massWeightedResponse_eq_critical_iff h0 h1).mp he
    change (3 / 4 : ℝ) / (u ^ 2 + 0 + 3 / 4) = 1 / 3 at hf
    have hd : u ^ 2 + 0 + (3 / 4 : ℝ) ≠ 0 := by nlinarith [sq_nonneg u]
    have hs : u ^ 2 = (3 / 2 : ℝ) := by
      have hm := (div_eq_iff hd).mp hf
      nlinarith
    have ha := (sq_eq_sq_iff_abs_eq_abs u peakFrequency).mp
      (hs.trans peakFrequency_sq.symm)
    simpa only [abs_of_nonneg hu, abs_of_nonneg peakFrequency_nonneg] using ha
  · rintro rfl
    exact capacity_first_peak

/-- The seven nonzero-index branches have kinetic offset larger than twice
their mass offset; no frequency in any of them can maximize the capacity. -/
theorem nonfirst_mass_bound (i : Branch) (hi : i ≠ 0) : 2 * mass i < kinetic i := by
  fin_cases i <;>
    norm_num [kinetic, mass, SourceTTGaussianCoefficient.branch,
      SourceTTGaussianCoefficient.torsion_eq] at *

theorem fraction_lt_third_of_nonfirst (i : Branch) (hi : i ≠ 0) (u : ℝ) :
    fraction i u < (1 / 3 : ℝ) := by
  unfold fraction massFraction
  rw [div_lt_iff₀ (precision_pos i u)]
  nlinarith [nonfirst_mass_bound i hi, sq_nonneg u]

theorem capacity_lt_peak_of_nonfirst (i : Branch) (hi : i ≠ 0) (u : ℝ) :
    capacity i u < (4 / 27 : ℝ) := by
  obtain ⟨h0, h1⟩ := fraction_bounds i u
  have hb := (capacity_bounds i u).2
  have he : capacity i u ≠ (4 / 27 : ℝ) := by
    intro heq
    have hy := (massWeightedResponse_eq_critical_iff h0 h1).mp heq
    linarith [fraction_lt_third_of_nonfirst i hi u]
  exact lt_of_le_of_ne hb he

def peak : Frequency := ⟨(0, peakFrequency), peakFrequency_mem⟩

@[simp] theorem readout_peak : readout peak = (4 / 27 : ℝ) :=
  capacity_first_peak

theorem readout_bounds (x : Frequency) :
    0 ≤ readout x ∧ readout x ≤ (4 / 27 : ℝ) :=
  capacity_bounds x.1.1 x.1.2

theorem readout_eq_peak_iff (x : Frequency) :
    readout x = (4 / 27 : ℝ) ↔ x = peak := by
  constructor
  · intro he
    have hi : x.1.1 = 0 := by
      by_contra hi
      have hs := capacity_lt_peak_of_nonfirst x.1.1 hi x.1.2
      exact (ne_of_lt hs) he
    have hu : x.1.2 = peakFrequency := by
      apply (capacity_first_eq_peak_iff x.2.1).mp
      simpa only [readout, hi] using he
    apply Subtype.ext
    exact Prod.ext hi hu
  · rintro rfl
    exact readout_peak

/-- All intermediate response values already occur on the first branch,
between zero frequency and its unique nonnegative maximizing frequency. -/
theorem exists_frequency_of_mem_range {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (4 / 27)) : ∃ x : Frequency, readout x = r := by
  have hr' : r ∈ Set.Icc (capacity 0 0) (capacity 0 peakFrequency) := by
    simpa only [capacity_first_zero, capacity_first_peak] using hr
  obtain ⟨u, hu, he⟩ := intermediate_value_Icc peakFrequency_nonneg
    (capacity_continuous 0).continuousOn hr'
  exact ⟨⟨(0, u), hu.1, hu.2.trans peakFrequency_mem.2⟩, he⟩

theorem readout_range : Set.range readout = Set.Icc (0 : ℝ) (4 / 27) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    exact readout_bounds x
  · exact exists_frequency_of_mem_range

theorem readout_isGreatest : IsGreatest (Set.range readout) (4 / 27 : ℝ) := by
  exact ⟨⟨peak, readout_peak⟩, by rintro r ⟨x, rfl⟩; exact (readout_bounds x).2⟩

theorem readout_sSup : sSup (Set.range readout) = (4 / 27 : ℝ) :=
  readout_isGreatest.isLUB.csSup_eq ⟨_, readout_isGreatest.1⟩

theorem halfReadout_range : Set.range halfReadout = Set.Icc (0 : ℝ) (2 / 27) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨h0, h1⟩ := readout_bounds x
    constructor <;> unfold halfReadout <;> linarith
  · intro hr
    obtain ⟨x, hx⟩ := exists_frequency_of_mem_range
      (show 2 * r ∈ Set.Icc (0 : ℝ) (4 / 27) by constructor <;> linarith [hr.1, hr.2])
    exact ⟨x, by unfold halfReadout; linarith⟩

theorem halfReadout_isGreatest : IsGreatest (Set.range halfReadout) (2 / 27 : ℝ) := by
  refine ⟨⟨peak, by norm_num [halfReadout, readout_peak]⟩, ?_⟩
  rintro r ⟨x, rfl⟩
  obtain ⟨_, h⟩ := readout_bounds x
  unfold halfReadout
  linarith

theorem halfReadout_sSup : sSup (Set.range halfReadout) = (2 / 27 : ℝ) :=
  halfReadout_isGreatest.isLUB.csSup_eq ⟨_, halfReadout_isGreatest.1⟩

end GeneratedFoundations.Physical.SourceTTCapacitySpectrum
