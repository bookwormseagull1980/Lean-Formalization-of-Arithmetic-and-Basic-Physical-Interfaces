module

public import GeneratedFoundations.Spectral.ReflectionEven
public import GeneratedFoundations.Spectral.NeumannPoisson
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Tactic.LinearCombination

/-!
# Reflection of the actual second-order Sobolev domain

Integral identities determine the weak derivatives of the reflected
representatives. The two Neumann traces remove the middle seam and the
periodic seam, respectively. No spectral expansion is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

theorem hasComplexH1Derivative_of_primitiveAt {a b c : ℝ} (hab : a < b)
    (hc : c ∈ Icc a b) {f g : ℝ → ℂ} (hg : MemLp g 2 (intervalMeasure a b))
    (hrep : ∀ x ∈ Icc a b, f x = f c + ∫ z in c..x, g z) :
    HasComplexH1Derivative a b f g := by
  apply hasComplexH1Derivative_of_primitive hab hg
  intro x hx
  have hgi := complex_intervalIntegrable_of_memLp hab.le hg
  have hca := hgi.mono_set ((uIcc_subset_Icc hc ⟨le_rfl, hab.le⟩).trans Icc_subset_uIcc)
  have hax := hgi.mono_set ((uIcc_subset_Icc ⟨le_rfl, hab.le⟩ hx).trans Icc_subset_uIcc)
  rw [hrep x hx, hrep a ⟨le_rfl, hab.le⟩, add_assoc,
    intervalIntegral.integral_add_adjacent_intervals hca hax]

def evenReflection (f : ℝ → ℂ) (x : ℝ) : ℂ := f |x|

def oddReflection (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x < 0 then -evenReflection f x else evenReflection f x

theorem evenReflection_nonnegative (f : ℝ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    evenReflection f x = f x := by simp [evenReflection, abs_of_nonneg hx]

theorem evenReflection_nonpositive (f : ℝ → ℂ) {x : ℝ} (hx : x ≤ 0) :
    evenReflection f x = f (-x) := by simp [evenReflection, abs_of_nonpos hx]

theorem oddReflection_nonnegative (f : ℝ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    oddReflection f x = f x := by
  simp [oddReflection, not_lt.mpr hx, evenReflection_nonnegative f hx]

theorem oddReflection_negative (f : ℝ → ℂ) {x : ℝ} (hx : x < 0) :
    oddReflection f x = -f (-x) := by
  simp [oddReflection, hx, evenReflection_nonpositive f hx.le]

@[simp] theorem evenReflection_zero (f : ℝ → ℂ) : evenReflection f 0 = f 0 := by
  simp [evenReflection]

@[simp] theorem oddReflection_zero (f : ℝ → ℂ) : oddReflection f 0 = f 0 := by
  simp [oddReflection, evenReflection]

theorem evenReflection_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure 0 L)) :
    MemLp (evenReflection f) 2 (intervalMeasure (-L) L) := by
  have hmp : MeasurePreserving abs (intervalMeasure (-L) L)
      ((2 : ℝ≥0∞) • intervalMeasure 0 L) :=
    ⟨continuous_abs.measurable, map_abs_intervalMeasure hL⟩
  exact (hf.smul_measure (c := (2 : ℝ≥0∞)) (by norm_num)).comp_measurePreserving hmp

theorem oddReflection_memLp {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure 0 L)) :
    MemLp (oddReflection f) 2 (intervalMeasure (-L) L) := by
  have he := evenReflection_memLp hL hf
  have hp := MemLp.piecewise (s := Iio (0 : ℝ)) measurableSet_Iio
    (he.neg.mono_measure Measure.restrict_le_self)
    (he.mono_measure Measure.restrict_le_self)
  convert! hp using 1

theorem integral_oddReflection (f : ℝ → ℂ) (x : ℝ) :
    (∫ y in 0..x, oddReflection f y) = ∫ y in 0..|x|, f y := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    apply intervalIntegral.integral_congr
    intro y hy
    have h : y ∈ Icc 0 x := by simpa only [uIcc_of_le hx] using hy
    exact oddReflection_nonnegative f h.1
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hx']
    calc
      _ = ∫ y in 0..x, -f (-y) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne (0 : ℝ)] with y hy hmem
        have hynonpos : y ≤ 0 := by
          have h : y ∈ Icc x 0 := by
            simpa only [uIcc_of_ge hx'.le] using uIoc_subset_uIcc hmem
          exact h.2
        exact oddReflection_negative f (lt_of_le_of_ne hynonpos hy)
      _ = -(∫ y in -x..0, f y) := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg, neg_zero]
      _ = _ := by rw [intervalIntegral.integral_symm, neg_neg]

theorem integral_evenReflection_nonnegative (f : ℝ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ y in 0..x, evenReflection f y) = ∫ y in 0..x, f y := by
  apply intervalIntegral.integral_congr
  intro y hy
  have h : y ∈ Icc 0 x := by simpa only [uIcc_of_le hx] using hy
  exact evenReflection_nonnegative f h.1

theorem integral_evenReflection_nonpositive (f : ℝ → ℂ) {x : ℝ} (hx : x ≤ 0) :
    (∫ y in 0..x, evenReflection f y) = ∫ y in -x..0, f y := by
  calc
    _ = ∫ y in 0..x, f (-y) := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact evenReflection_nonpositive f (by
        have h : y ∈ Icc x 0 := by simpa only [uIcc_of_ge hx] using hy
        exact h.2)
    _ = _ := by rw [intervalIntegral.integral_comp_neg, neg_zero]

theorem HasComplexH1Derivative.reflect_even {L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℂ} (h : HasComplexH1Derivative 0 L f g) :
    HasComplexH1Derivative (-L) L (evenReflection f) (oddReflection g) := by
  apply hasComplexH1Derivative_of_primitiveAt (by linarith : -L < L)
    (c := 0) ⟨by linarith, hL.le⟩ (oddReflection_memLp hL h.derivative_memLp)
  intro x hx
  have hax : |x| ∈ Icc 0 L := ⟨abs_nonneg x, abs_le.mpr hx⟩
  rw [evenReflection_zero, integral_oddReflection,
    h.integral_eq_sub ⟨le_rfl, hL.le⟩ hax]
  change f |x| = f 0 + (f |x| - f 0)
  ring

theorem HasComplexH1Derivative.reflect_odd {L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℂ} (h : HasComplexH1Derivative 0 L f g) (hzero : f 0 = 0) :
    HasComplexH1Derivative (-L) L (oddReflection f) (evenReflection g) := by
  apply hasComplexH1Derivative_of_primitiveAt (by linarith : -L < L)
    (c := 0) ⟨by linarith, hL.le⟩ (evenReflection_memLp hL h.derivative_memLp)
  intro x hx
  rw [oddReflection_zero, hzero, zero_add]
  by_cases hx0 : 0 ≤ x
  · rw [oddReflection_nonnegative f hx0, integral_evenReflection_nonnegative g hx0,
      h.integral_eq_sub ⟨le_rfl, hL.le⟩ ⟨hx0, hx.2⟩, hzero, sub_zero]
  · have hxn : x < 0 := lt_of_not_ge hx0
    rw [oddReflection_negative f hxn, integral_evenReflection_nonpositive g hxn.le,
      h.integral_eq_sub ⟨by linarith, by linarith [hx.1]⟩ ⟨le_rfl, hL.le⟩,
      hzero, zero_sub]

theorem HasComplexH1Derivative.restrict {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) {f g : ℝ → ℂ} (h : HasComplexH1Derivative a b f g) :
    HasComplexH1Derivative c d f g := by
  have hs : Icc c d ⊆ Icc a b := fun _ hx => ⟨hac.trans hx.1, hx.2.trans hdb⟩
  have hm : intervalMeasure c d ≤ intervalMeasure a b :=
    Measure.restrict_mono hs le_rfl
  refine ⟨h.absolutelyContinuous.mono ?_, h.derivative_memLp.mono_measure hm,
    h.hasDeriv_ae.filter_mono (ae_mono hm)⟩
  simpa only [uIcc_of_le hab, uIcc_of_le hcd] using hs

theorem interval_neg_measurePreserving {L : ℝ} :
    MeasurePreserving (fun x : ℝ => -x) (intervalMeasure (-L) L)
      (intervalMeasure (-L) L) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (s := Icc (-L) L) measurableSet_Icc
  have hs : (fun x : ℝ => -x) ⁻¹' Icc (-L) L = Icc (-L) L := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simpa only [hs, intervalMeasure] using h

theorem HasComplexH1Derivative.comp_neg {L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℂ} (h : HasComplexH1Derivative (-L) L f g) :
    HasComplexH1Derivative (-L) L (fun x => f (-x)) (fun x => -g (-x)) := by
  have hmem : MemLp (fun x => -g (-x)) 2 (intervalMeasure (-L) L) := by
    convert! (h.derivative_memLp.comp_measurePreserving
      interval_neg_measurePreserving).neg using 1
  apply hasComplexH1Derivative_of_primitiveAt (by linarith : -L < L)
    (c := 0) ⟨by linarith, hL.le⟩ hmem
  intro x hx
  have hnx : -x ∈ Icc (-L) L := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg, neg_zero,
    h.integral_eq_sub hnx ⟨by linarith, hL.le⟩]
  ring

/-- Periodic traces are imposed on actual absolutely continuous representatives. -/
structure PeriodicIntervalH2 (L : ℝ) extends ComplexH2Representative (-L) L where
  value_match : value (-L) = value L
  first_match : first (-L) = first L

def PeriodicIntervalH2.IsEven {L : ℝ} (f : PeriodicIntervalH2 L) : Prop :=
  ∀ x ∈ Icc (-L) L, f.value (-x) = f.value x

def reflectNeumann {L : ℝ} (hL : 0 < L) (f : ComplexH2Representative 0 L)
    (hf : IsComplexNeumann f) : PeriodicIntervalH2 L where
  value := evenReflection f.value
  first := oddReflection f.first
  second := evenReflection f.second
  firstDerivative := f.firstDerivative.reflect_even hL
  secondDerivative := f.secondDerivative.reflect_odd hL hf.1
  value_match := by simp [evenReflection, abs_of_pos hL]
  first_match := by
    rw [oddReflection_negative f.first (by linarith : -L < 0), neg_neg,
      oddReflection_nonnegative f.first hL.le, hf.2, neg_zero]

theorem reflectNeumann_isEven {L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative 0 L) (hf : IsComplexNeumann f) :
    (reflectNeumann hL f hf).IsEven := by
  intro x _
  simp [reflectNeumann, evenReflection]

def PeriodicIntervalH2.restrict {L : ℝ} (hL : 0 < L) (f : PeriodicIntervalH2 L) :
    ComplexH2Representative 0 L where
  value := f.value
  first := f.first
  second := f.second
  firstDerivative := f.firstDerivative.restrict (by linarith) hL.le (by linarith) le_rfl
  secondDerivative := f.secondDerivative.restrict (by linarith) hL.le (by linarith) le_rfl

theorem PeriodicIntervalH2.first_odd {L : ℝ} (hL : 0 < L)
    (f : PeriodicIntervalH2 L) (hf : f.IsEven) :
    ∀ x ∈ Icc (-L) L, -f.first (-x) = f.first x := by
  have href := f.firstDerivative.comp_neg hL
  have heq : (fun x => f.value (-x)) =ᵐ[intervalMeasure (-L) L] f.value :=
    ae_restrict_of_forall_mem measurableSet_Icc hf
  have hd := complexH1Derivative_unique (by linarith : -L < L)
    href f.firstDerivative heq
  apply Measure.eqOn_Icc_of_ae_eq volume (by linarith : -L ≠ L) hd _
    f.secondDerivative.continuousOn
  exact ((f.secondDerivative.comp_neg hL).continuousOn).neg

lemma complex_eq_zero_of_neg_eq_self {z : ℂ} (hz : -z = z) : z = 0 := by
  have h : (2 : ℂ) * z = 0 := by linear_combination -hz
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

theorem PeriodicIntervalH2.restrict_neumann {L : ℝ} (hL : 0 < L)
    (f : PeriodicIntervalH2 L) (hf : f.IsEven) :
    IsComplexNeumann (f.restrict hL) := by
  constructor
  · have h := f.first_odd hL hf 0 ⟨by linarith, hL.le⟩
    simp only [neg_zero] at h
    exact complex_eq_zero_of_neg_eq_self h
  · have h := f.first_odd hL hf L ⟨by linarith, le_rfl⟩
    rw [f.first_match] at h
    exact complex_eq_zero_of_neg_eq_self h

/-- Every periodic even `H²` extension, not only the explicitly reflected
one, forces the two Neumann traces on its interval restriction. -/
theorem neumann_iff_periodic_even_extension {L : ℝ} (hL : 0 < L)
    (f : ComplexH2Representative 0 L) :
    IsComplexNeumann f ↔ ∃ F : PeriodicIntervalH2 L,
      F.IsEven ∧ EqOn F.value f.value (Icc 0 L) := by
  constructor
  · intro hf
    refine ⟨reflectNeumann hL f hf, reflectNeumann_isEven hL f hf, ?_⟩
    intro x hx
    exact evenReflection_nonnegative f.value hx.1
  · rintro ⟨F, hF, heq⟩
    have hL2 : (F.restrict hL).toL2 = f.toL2 := by
      apply ((F.restrict hL).toL2_eq_iff f).mpr
      exact ae_restrict_of_forall_mem measurableSet_Icc heq
    have htrace := (ComplexH2Representative.trace_unique hL hL2).2
    have hn := F.restrict_neumann hL hF
    exact ⟨(htrace ⟨le_rfl, hL.le⟩).symm.trans hn.1,
      (htrace ⟨hL.le, le_rfl⟩).symm.trans hn.2⟩

end GeneratedFoundations.Spectral
