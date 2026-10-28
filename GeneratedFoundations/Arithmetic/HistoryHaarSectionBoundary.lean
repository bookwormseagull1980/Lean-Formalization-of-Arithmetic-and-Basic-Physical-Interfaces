module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionExhaustion
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Moving boundaries of the original Gaussian spectral window

The precision comparison varies its kinetic coefficient at a fixed window.
Here the bandwidth itself varies. Every original spectral row is retained;
the cutoff derivative is computed from its actual moving frequency edge.
All active rows share the exact boundary factor `exp (-B)`. The remaining
weights retain the restoring coefficient and the individual birth edge.

Continuity holds at births as well. Derivative statements are made away
from actual kinetic birth values. They do not replace a birth term by zero,
nor impose a stationary bandwidth or a prescribed number of positions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionBoundary

open HistoryHaarSectionWindow HistoryHaarSectionComparison
open HistoryHaarSectionProbability (branchMass mass)
open HistoryHaarSectionJointHessian (Index)

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

private def primitive (f : ℝ → ℝ) (a B : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - a), f u

private theorem primitive_continuous (f : ℝ → ℝ) (hf : Continuous f) (a : ℝ) :
    Continuous (primitive f a) :=
  (intervalIntegral.differentiable_integral_of_continuous hf).continuous.comp
    (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))

private theorem primitive_hasDerivAt_active (f : ℝ → ℝ) (hf : Continuous f)
    (a : ℝ) {B : ℝ} (hB : a < B) :
    HasDerivAt (primitive f a)
      (f (Real.sqrt (B - a)) / (2 * Real.sqrt (B - a))) B := by
  have hs := ((hasDerivAt_id B).sub_const a).sqrt (sub_pos.mpr hB).ne'
  have hi := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 (Real.sqrt (B - a)))
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  convert! hi.comp B hs using 1
  simp only [id_eq, mul_one_div]

private theorem primitive_hasDerivAt_inactive (f : ℝ → ℝ) (a : ℝ)
    {B : ℝ} (hB : B < a) : HasDerivAt (primitive f a) 0 B := by
  apply (hasDerivAt_const B (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hB] with C hC
  simp only [primitive, Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr hC.le),
    intervalIntegral.integral_same]

theorem branchIntegral_continuous (N : ℕ) (i : Index N) :
    Continuous (fun B => branchIntegral N B i) :=
  primitive_continuous (kernel N i) (kernel_continuous N i) (kinetic N i)

theorem branchMass_continuous (N : ℕ) (i : Index N) :
    Continuous (fun B => branchMass N B i) :=
  primitive_continuous (weight N i) (weight_continuous N i) (kinetic N i)

theorem kernel_at_edge (N : ℕ) (i : Index N) {B : ℝ}
    (hB : kinetic N i < B) :
    kernel N i (Real.sqrt (B - kinetic N i)) =
      (B / (B + restoring N i)) ^ 2 * Real.exp (-B) := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hB.le)
  rw [kernel, hs, source_response_decomposition]
  congr 2 <;> ring

theorem weight_at_edge (N : ℕ) (i : Index N) {B : ℝ}
    (hB : kinetic N i < B) :
    weight N i (Real.sqrt (B - kinetic N i)) = Real.exp (-B) := by
  rw [weight, kineticPrecision, Real.sq_sqrt (sub_nonneg.mpr hB.le)]
  congr 1
  ring

/-- Exact boundary density after factoring out the common Gaussian. -/
def responseEdge (N : ℕ) (B : ℝ) (i : Index N) : ℝ :=
  (B / (B + restoring N i)) ^ 2 / (2 * Real.sqrt (B - kinetic N i))

def massEdge (N : ℕ) (B : ℝ) (i : Index N) : ℝ :=
  1 / (2 * Real.sqrt (B - kinetic N i))

def branchSlope (N : ℕ) (B : ℝ) (i : Index N) : ℝ :=
  if kinetic N i < B then Real.exp (-B) * responseEdge N B i else 0

def branchMassSlope (N : ℕ) (B : ℝ) (i : Index N) : ℝ :=
  if kinetic N i < B then Real.exp (-B) * massEdge N B i else 0

theorem branchIntegral_hasDerivAt (N : ℕ) (i : Index N) {B : ℝ}
    (hB : kinetic N i ≠ B) :
    HasDerivAt (fun C => branchIntegral N C i) (branchSlope N B i) B := by
  by_cases h : kinetic N i < B
  · have hd := primitive_hasDerivAt_active (kernel N i) (kernel_continuous N i) _ h
    change HasDerivAt (fun C => branchIntegral N C i) _ B at hd
    convert hd using 1
    rw [branchSlope, ite_eq_left h, kernel_at_edge N i h, responseEdge]
    ring
  · have hl : B < kinetic N i := lt_of_le_of_ne (le_of_not_gt h) hB.symm
    have hd := primitive_hasDerivAt_inactive (kernel N i) (kinetic N i) hl
    change HasDerivAt (fun C => branchIntegral N C i) 0 B at hd
    simpa only [branchSlope, ite_eq_right h] using hd

theorem branchMass_hasDerivAt (N : ℕ) (i : Index N) {B : ℝ}
    (hB : kinetic N i ≠ B) :
    HasDerivAt (fun C => branchMass N C i) (branchMassSlope N B i) B := by
  by_cases h : kinetic N i < B
  · have hd := primitive_hasDerivAt_active (weight N i) (weight_continuous N i) _ h
    change HasDerivAt (fun C => branchMass N C i) _ B at hd
    convert hd using 1
    rw [branchMassSlope, ite_eq_left h, weight_at_edge N i h, massEdge]
    ring
  · have hl : B < kinetic N i := lt_of_le_of_ne (le_of_not_gt h) hB.symm
    have hd := primitive_hasDerivAt_inactive (weight N i) (kinetic N i) hl
    change HasDerivAt (fun C => branchMass N C i) 0 B at hd
    simpa only [branchMassSlope, ite_eq_right h] using hd

theorem branchMass_eq_zero (N : ℕ) (B : ℝ) (i : Index N)
    (hi : B ≤ kinetic N i) : branchMass N B i = 0 := by
  simp only [branchMass, Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr hi),
    intervalIntegral.integral_same]

theorem mass_eq_larger_sum (N : ℕ) {B C : ℝ} (hBC : B ≤ C) :
    mass N B = ∑ i ∈ support N C, branchMass N B i := by
  classical
  apply Finset.sum_subset (support_mono N hBC)
  intro i _ hnot
  exact branchMass_eq_zero N B i
    (le_of_not_gt (fun hi => hnot ((mem_support N B i).mpr hi)))

/-- One finite complete enumeration works on a whole neighborhood of any
bandwidth, including a birth value. Earlier integrals already extend by zero. -/
theorem responseTrace_continuous (N : ℕ) : Continuous (responseTrace N) := by
  apply continuous_iff_continuousAt.mpr
  intro B
  have h := (continuous_finsetSum (support N (B + 1))
    (fun i _ => branchIntegral_continuous N i)).continuousAt (x := B)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds (show B < B + 1 by linarith)] with C hC
  exact responseTrace_eq_larger_sum N hC.le

theorem mass_continuous (N : ℕ) : Continuous (mass N) := by
  apply continuous_iff_continuousAt.mpr
  intro B
  have h := (continuous_finsetSum (support N (B + 1))
    (fun i _ => branchMass_continuous N i)).continuousAt (x := B)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds (show B < B + 1 by linarith)] with C hC
  exact mass_eq_larger_sum N hC.le

def responseBoundary (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ support N B, responseEdge N B i

def massBoundary (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ support N B, massEdge N B i

theorem responseTrace_hasDerivAt (N : ℕ) {B : ℝ}
    (hregular : ∀ i : Index N, kinetic N i ≠ B) :
    HasDerivAt (responseTrace N) (Real.exp (-B) * responseBoundary N B) B := by
  have hd := HasDerivAt.fun_sum (u := support N (B + 1))
    (fun i _ => branchIntegral_hasDerivAt N i (hregular i))
  have he : (∑ i ∈ support N (B + 1), branchSlope N B i) =
      Real.exp (-B) * responseBoundary N B := by
    have he' : (∑ i ∈ support N B, branchSlope N B i) =
        ∑ i ∈ support N (B + 1), branchSlope N B i := by
      apply Finset.sum_subset (support_mono N (show B ≤ B + 1 by linarith))
      intro i _ hi
      simp only [branchSlope, ite_eq_right (fun h => hi ((mem_support N B i).mpr h))]
    rw [← he', responseBoundary, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [branchSlope, ite_eq_left ((mem_support N B i).mp hi)]
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds (show B < B + 1 by linarith)] with C hC
  exact responseTrace_eq_larger_sum N hC.le

theorem mass_hasDerivAt (N : ℕ) {B : ℝ}
    (hregular : ∀ i : Index N, kinetic N i ≠ B) :
    HasDerivAt (mass N) (Real.exp (-B) * massBoundary N B) B := by
  have hd := HasDerivAt.fun_sum (u := support N (B + 1))
    (fun i _ => branchMass_hasDerivAt N i (hregular i))
  have he : (∑ i ∈ support N (B + 1), branchMassSlope N B i) =
      Real.exp (-B) * massBoundary N B := by
    have he' : (∑ i ∈ support N B, branchMassSlope N B i) =
        ∑ i ∈ support N (B + 1), branchMassSlope N B i := by
      apply Finset.sum_subset (support_mono N (show B ≤ B + 1 by linarith))
      intro i _ hi
      simp only [branchMassSlope, ite_eq_right (fun h => hi ((mem_support N B i).mpr h))]
    rw [← he', massBoundary, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [branchMassSlope, ite_eq_left ((mem_support N B i).mp hi)]
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds (show B < B + 1 by linarith)] with C hC
  exact mass_eq_larger_sum N hC.le

def normalizedResponse (N : ℕ) (B : ℝ) : ℝ := responseTrace N B / mass N B

/-- A signed same-window balance: the boundary response is compared with
the complete interior average before any inequality is used. -/
def boundaryBalance (N : ℕ) (B : ℝ) : ℝ :=
  responseBoundary N B - normalizedResponse N B * massBoundary N B

theorem boundaryBalance_eq_sum (N : ℕ) (B : ℝ) :
    boundaryBalance N B = ∑ i ∈ support N B,
      massEdge N B i * ((B / (B + restoring N i)) ^ 2 - normalizedResponse N B) := by
  unfold boundaryBalance responseBoundary massBoundary responseEdge massEdge
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalizedResponse_hasDerivAt (N : ℕ) {B : ℝ} (hB : 0 < B)
    (hregular : ∀ i : Index N, kinetic N i ≠ B) :
    HasDerivAt (normalizedResponse N)
      (Real.exp (-B) / mass N B * boundaryBalance N B) B := by
  have hm := (HistoryHaarSectionProbability.mass_pos_of_pos N hB).ne'
  have hd := (responseTrace_hasDerivAt N hregular).div (mass_hasDerivAt N hregular) hm
  convert hd using 1
  · rfl
  · unfold boundaryBalance normalizedResponse
    field_simp

theorem normalizedResponse_stationary_iff (N : ℕ) {B : ℝ} (hB : 0 < B)
    (hregular : ∀ i : Index N, kinetic N i ≠ B) :
    deriv (normalizedResponse N) B = 0 ↔ boundaryBalance N B = 0 := by
  rw [(normalizedResponse_hasDerivAt N hB hregular).deriv]
  exact mul_eq_zero.trans (or_iff_right
    (div_pos (Real.exp_pos _) (HistoryHaarSectionProbability.mass_pos_of_pos N hB)).ne')

theorem responseTrace_lt_mass (N : ℕ) {B : ℝ} (hB : 0 < B) :
    responseTrace N B < mass N B := by
  let i := positionIndex N 0 (HistoryHaarSectionExhaustion.basePositionLabel N 0)
  have hi0 : kinetic N i = 0 := by
    change Geometry.SourceScalarKineticForm.position 0 = 0
    norm_num [Geometry.SourceScalarKineticForm.position_eq]
  have hi : i ∈ support N B := (mem_support N B i).mpr (by rwa [hi0])
  have hk0 : kernel N i 0 = 0 := by simp [kernel, hi0]
  have hw0 : weight N i 0 = 1 := by simp [weight, kineticPrecision, hi0]
  have hstrict : branchIntegral N B i < branchMass N B i := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (Real.sqrt_pos.mpr (by rwa [hi0, sub_zero]))
      (kernel_continuous N i).continuousOn (weight_continuous N i).continuousOn
      (fun u _ => HistoryHaarSectionProbability.kernel_le_weight N i u)
    refine ⟨0, ⟨le_rfl, Real.sqrt_nonneg _⟩, ?_⟩
    rw [hk0, hw0]
    norm_num
  exact Finset.sum_lt_sum
    (fun j _ => HistoryHaarSectionProbability.branchIntegral_le_mass N B j)
    ⟨i, hi, hstrict⟩

theorem normalizedResponse_lt_one (N : ℕ) {B : ℝ} (hB : 0 < B) :
    normalizedResponse N B < 1 := by
  exact (div_lt_one (HistoryHaarSectionProbability.mass_pos_of_pos N hB)).mpr
    (responseTrace_lt_mass N hB)

def fieldBoundary (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ support N B, if i.isLeft then massEdge N B i else 0

def scalarBoundary (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ support N B, if i.isRight then massEdge N B i else 0

def scalarEdgeFraction (N : ℕ) (B : ℝ) : ℝ :=
  (B / (B + HistoryDefiningResponse.coefficient N)) ^ 2

theorem massBoundary_field_scalar (N : ℕ) (B : ℝ) :
    massBoundary N B = fieldBoundary N B + scalarBoundary N B := by
  unfold massBoundary fieldBoundary scalarBoundary
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases i <;> simp

theorem responseBoundary_field_scalar (N : ℕ) {B : ℝ} (hB : 0 < B) :
    responseBoundary N B = fieldBoundary N B +
      scalarEdgeFraction N B * scalarBoundary N B := by
  unfold responseBoundary fieldBoundary scalarBoundary
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | inl a => simp [responseEdge, massEdge, restoring, hB.ne']
  | inr a => simp [responseEdge, massEdge, restoring, scalarEdgeFraction, div_eq_mul_inv]

/-- Both sectors come from the same original support. In particular this
identity keeps the sign of their contributions to the changing average. -/
theorem boundaryBalance_field_scalar (N : ℕ) {B : ℝ} (hB : 0 < B) :
    boundaryBalance N B =
      fieldBoundary N B * (1 - normalizedResponse N B) +
      scalarBoundary N B * (scalarEdgeFraction N B - normalizedResponse N B) := by
  rw [boundaryBalance, responseBoundary_field_scalar N hB, massBoundary_field_scalar]
  ring

theorem scalarBoundary_nonneg (N : ℕ) (B : ℝ) : 0 ≤ scalarBoundary N B := by
  unfold scalarBoundary
  apply Finset.sum_nonneg
  intro i _
  unfold massEdge
  split_ifs <;> positivity

theorem fieldBoundary_pos (N : ℕ) {B : ℝ} (hB : 4 < B) : 0 < fieldBoundary N B := by
  let i : Index N := .inl (HistoryHaarClosedHessian.minimizingIndex N)
  have hi0 : kinetic N i = 4 := HistoryHaarClosedHessian.eigenvalue_minimizingIndex N
  have hi : i ∈ support N B := (mem_support N B i).mpr (by rwa [hi0])
  unfold fieldBoundary
  refine Finset.sum_pos' ?_ ?_
  · intro j _
    unfold massEdge
    split_ifs <;> positivity
  · refine ⟨i, hi, ?_⟩
    change 0 < massEdge N B i
    unfold massEdge
    exact div_pos (by norm_num) (mul_pos (by norm_num)
      (Real.sqrt_pos.mpr (by rw [hi0]; exact sub_pos.mpr hB)))

/-- Above the first actual connection shell, stationarity requires the
scalar edge response to be strictly below the full interior response.
No stationarity or count is imposed as a source axiom. -/
theorem stationary_requires_scalar_edge_deficit (N : ℕ) {B : ℝ} (hB : 4 < B)
    (hbalance : boundaryBalance N B = 0) :
    scalarEdgeFraction N B < normalizedResponse N B := by
  by_contra hn
  have hB0 : 0 < B := by linarith
  have hf := mul_pos (fieldBoundary_pos N hB)
    (sub_pos.mpr (normalizedResponse_lt_one N hB0))
  have hs := mul_nonneg (scalarBoundary_nonneg N B) (sub_nonneg.mpr (le_of_not_gt hn))
  rw [boundaryBalance_field_scalar N hB0] at hbalance
  linarith

theorem branchIntegral_change (N : ℕ) (i : Index N) (B C : ℝ) :
    branchIntegral N C i - branchIntegral N B i =
      ∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i), kernel N i u := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    ((kernel_continuous N i).intervalIntegrable 0 (Real.sqrt (B - kinetic N i)))
    ((kernel_continuous N i).intervalIntegrable
      (Real.sqrt (B - kinetic N i)) (Real.sqrt (C - kinetic N i)))
  unfold branchIntegral
  linarith

theorem branchMass_change (N : ℕ) (i : Index N) (B C : ℝ) :
    branchMass N C i - branchMass N B i =
      ∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i), weight N i u := by
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    ((weight_continuous N i).intervalIntegrable 0 (Real.sqrt (B - kinetic N i)))
    ((weight_continuous N i).intervalIntegrable
      (Real.sqrt (B - kinetic N i)) (Real.sqrt (C - kinetic N i)))
  unfold branchMass
  linarith

/-- Actual finite-window exchange. The lower edge is zero on a newly born
row, so that births and extensions use the same original integral. -/
def windowExchange (N : ℕ) (B C : ℝ) : ℝ :=
  ∑ i ∈ support N C,
    ∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i),
      weight N i u * (kineticFraction N i u ^ 2 - normalizedResponse N B)

theorem branchExchange_eq (N : ℕ) (i : Index N) (B C : ℝ) :
    (∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i),
      weight N i u * (kineticFraction N i u ^ 2 - normalizedResponse N B)) =
      (branchIntegral N C i - branchIntegral N B i) -
        normalizedResponse N B * (branchMass N C i - branchMass N B i) := by
  have hp (u : ℝ) :
      weight N i u * (kineticFraction N i u ^ 2 - normalizedResponse N B) =
        kernel N i u - normalizedResponse N B * weight N i u := by
    rw [kernel_eq_comparison_curvature, Operations.ScalarPrecisionComparison.curvature_zero]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_sub
    ((kernel_continuous N i).intervalIntegrable _ _)
    (((weight_continuous N i).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, ← branchIntegral_change, ← branchMass_change]

theorem windowExchange_eq (N : ℕ) {B C : ℝ} (hBC : B ≤ C) :
    windowExchange N B C = (responseTrace N C - responseTrace N B) -
      normalizedResponse N B * (mass N C - mass N B) := by
  unfold windowExchange
  simp_rw [branchExchange_eq]
  rw [responseTrace_eq_larger_sum N hBC, mass_eq_larger_sum N hBC]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, responseTrace, mass]

/-- A finite, exact capacity-transfer identity, valid across all births.
It makes no differentiability or stationarity assumption on either edge. -/
theorem normalizedResponse_change (N : ℕ) {B C : ℝ} (hB : 0 < B) (hBC : B ≤ C) :
    normalizedResponse N C - normalizedResponse N B = windowExchange N B C / mass N C := by
  have hmB := (HistoryHaarSectionProbability.mass_pos_of_pos N hB).ne'
  have hmC := (HistoryHaarSectionProbability.mass_pos_of_pos N (hB.trans_le hBC)).ne'
  rw [windowExchange_eq N hBC]
  unfold normalizedResponse
  field_simp
  ring

private theorem squared_fraction_mono {b x y : ℝ} (hb : 0 ≤ b) (hx : 0 < x)
    (hxy : x ≤ y) : (x / (x + b)) ^ 2 ≤ (y / (y + b)) ^ 2 := by
  have hdx : 0 < x + b := by linarith
  have hdy : 0 < y + b := by linarith
  have hr : x / (x + b) ≤ y / (y + b) :=
    (div_le_div_iff₀ hdx hdy).mpr (by nlinarith)
  exact pow_le_pow_left₀ (div_nonneg hx.le hdx.le) hr 2

/-- The exact Gaussian mass of each added interval bounds its response
using the two actual endpoint fractions. A newly born row starts at
`max B (kinetic N i)`, not at the earlier, inaccessible kinetic value `B`.
Neither the Gaussian weight nor the restoring coefficient is replaced. -/
theorem branch_change_bounds (N : ℕ) (i : Index N) {B C : ℝ} (hB : 0 < B)
    (hBC : B ≤ C) (hi : kinetic N i < C) :
    (max B (kinetic N i) / (max B (kinetic N i) + restoring N i)) ^ 2 *
        (branchMass N C i - branchMass N B i) ≤
        branchIntegral N C i - branchIntegral N B i ∧
      branchIntegral N C i - branchIntegral N B i ≤
        (C / (C + restoring N i)) ^ 2 * (branchMass N C i - branchMass N B i) := by
  have hedge : Real.sqrt (B - kinetic N i) ≤ Real.sqrt (C - kinetic N i) :=
    Real.sqrt_le_sqrt (sub_le_sub_right hBC _)
  have hq (u : ℝ)
      (hu : u ∈ Icc (Real.sqrt (B - kinetic N i)) (Real.sqrt (C - kinetic N i))) :
      B ≤ kineticPrecision N i u ∧ kineticPrecision N i u ≤ C := by
    have hslo : Real.sqrt (B - kinetic N i) ^ 2 = max (B - kinetic N i) 0 :=
      Real.sq_sqrt'
    have hmax := le_max_left (B - kinetic N i) 0
    have hshi := Real.sq_sqrt (sub_nonneg.mpr hi.le)
    have hu0 := (Real.sqrt_nonneg (B - kinetic N i)).trans hu.1
    have hlo := sq_le_sq₀ (Real.sqrt_nonneg (B - kinetic N i)) hu0 |>.mpr hu.1
    have hhi := sq_le_sq₀ hu0 (Real.sqrt_nonneg (C - kinetic N i)) |>.mpr hu.2
    unfold kineticPrecision
    constructor <;> nlinarith
  have hk (u : ℝ) : kernel N i u = weight N i u * kineticFraction N i u ^ 2 := by
    rw [kernel_eq_comparison_curvature, Operations.ScalarPrecisionComparison.curvature_zero]
  have hr (u : ℝ)
      (hu : u ∈ Icc (Real.sqrt (B - kinetic N i)) (Real.sqrt (C - kinetic N i))) :
      (max B (kinetic N i) / (max B (kinetic N i) + restoring N i)) ^ 2 ≤
          kineticFraction N i u ^ 2 ∧
        kineticFraction N i u ^ 2 ≤ (C / (C + restoring N i)) ^ 2 := by
    have hp := hq u hu
    have hentry : max B (kinetic N i) ≤ kineticPrecision N i u := by
      apply max_le hp.1
      unfold kineticPrecision
      linarith [sq_nonneg u]
    rw [kineticFraction, precision, source_response_decomposition]
    rw [← add_assoc]
    change (max B (kinetic N i) / (max B (kinetic N i) + restoring N i)) ^ 2 ≤
      (kineticPrecision N i u / (kineticPrecision N i u + restoring N i)) ^ 2 ∧
      (kineticPrecision N i u / (kineticPrecision N i u + restoring N i)) ^ 2 ≤
        (C / (C + restoring N i)) ^ 2
    exact ⟨squared_fraction_mono (restoring_nonneg N i)
        (hB.trans_le (le_max_left _ _)) hentry,
      squared_fraction_mono (restoring_nonneg N i) (hB.trans_le hp.1) hp.2⟩
  rw [branchIntegral_change, branchMass_change]
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hedge
      (((weight_continuous N i).const_mul _).intervalIntegrable _ _)
      ((kernel_continuous N i).intervalIntegrable _ _)
    intro u hu
    rw [hk]
    nlinarith [mul_le_mul_of_nonneg_left (hr u hu).1 (weight_pos N i u).le]
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hedge
      ((kernel_continuous N i).intervalIntegrable _ _)
      (((weight_continuous N i).const_mul _).intervalIntegrable _ _)
    intro u hu
    rw [hk]
    nlinarith [mul_le_mul_of_nonneg_left (hr u hu).2 (weight_pos N i u).le]

/-- A complete finite-shell bound using all original row masses and their
own restoring coefficients. Its constants do not depend on a row count. -/
theorem response_change_bounds (N : ℕ) {B C : ℝ} (hB : 0 < B) (hBC : B ≤ C) :
    (∑ i ∈ support N C,
      (max B (kinetic N i) / (max B (kinetic N i) + restoring N i)) ^ 2 *
      (branchMass N C i - branchMass N B i)) ≤ responseTrace N C - responseTrace N B ∧
    responseTrace N C - responseTrace N B ≤
      ∑ i ∈ support N C, (C / (C + restoring N i)) ^ 2 *
        (branchMass N C i - branchMass N B i) := by
  rw [responseTrace_eq_larger_sum N hBC]
  unfold responseTrace
  rw [← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_le_sum (fun i hi =>
      (branch_change_bounds N i hB hBC ((mem_support N C i).mp hi)).1)
  · exact Finset.sum_le_sum (fun i hi =>
      (branch_change_bounds N i hB hBC ((mem_support N C i).mp hi)).2)

structure Conclusions : Prop where
  continuous_through_births : ∀ N, Continuous (responseTrace N)
  gaussian_mass_continuous : ∀ N, Continuous (mass N)
  complete_response_boundary : ∀ N B, (∀ i : Index N, kinetic N i ≠ B) →
    HasDerivAt (responseTrace N) (Real.exp (-B) * responseBoundary N B) B
  complete_mass_boundary : ∀ N B, (∀ i : Index N, kinetic N i ≠ B) →
    HasDerivAt (mass N) (Real.exp (-B) * massBoundary N B) B
  normalized_joint_balance : ∀ N B, 0 < B → (∀ i : Index N, kinetic N i ≠ B) →
    HasDerivAt (normalizedResponse N)
      (Real.exp (-B) / mass N B * boundaryBalance N B) B
  signed_boundary_sum : ∀ N B,
    boundaryBalance N B = ∑ i ∈ support N B,
      massEdge N B i * ((B / (B + restoring N i)) ^ 2 - normalizedResponse N B)
  strict_capacity_bound : ∀ N B, 0 < B → responseTrace N B < mass N B
  same_source_sector_balance : ∀ N B, 0 < B →
    boundaryBalance N B =
      fieldBoundary N B * (1 - normalizedResponse N B) +
      scalarBoundary N B * (scalarEdgeFraction N B - normalizedResponse N B)
  stationary_content_constraint : ∀ N B, 4 < B → boundaryBalance N B = 0 →
    scalarEdgeFraction N B < normalizedResponse N B
  finite_capacity_exchange : ∀ N B C, 0 < B → B ≤ C →
    normalizedResponse N C - normalizedResponse N B = windowExchange N B C / mass N C
  actual_row_increment_bounds : ∀ N B C, 0 < B → B ≤ C →
    (∑ i ∈ support N C,
      (max B (kinetic N i) / (max B (kinetic N i) + restoring N i)) ^ 2 *
      (branchMass N C i - branchMass N B i)) ≤ responseTrace N C - responseTrace N B ∧
    responseTrace N C - responseTrace N B ≤
      ∑ i ∈ support N C, (C / (C + restoring N i)) ^ 2 *
        (branchMass N C i - branchMass N B i)

theorem generated : Conclusions where
  continuous_through_births := responseTrace_continuous
  gaussian_mass_continuous := mass_continuous
  complete_response_boundary := fun N _ h => responseTrace_hasDerivAt N h
  complete_mass_boundary := fun N _ h => mass_hasDerivAt N h
  normalized_joint_balance := fun N _ hB h => normalizedResponse_hasDerivAt N hB h
  signed_boundary_sum := boundaryBalance_eq_sum
  strict_capacity_bound := fun N _ hB => responseTrace_lt_mass N hB
  same_source_sector_balance := fun N _ hB => boundaryBalance_field_scalar N hB
  stationary_content_constraint := fun N _ hB h => stationary_requires_scalar_edge_deficit N hB h
  finite_capacity_exchange := fun N _ _ hB hBC => normalizedResponse_change N hB hBC
  actual_row_increment_bounds := fun N _ _ hB hBC => response_change_bounds N hB hBC

end GeneratedFoundations.Arithmetic.HistoryHaarSectionBoundary
