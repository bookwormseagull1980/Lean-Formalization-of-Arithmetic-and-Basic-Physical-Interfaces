module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionScale
public import GeneratedFoundations.Geometry.SourceOneFormMultiplicity

/-!
# Complete differential shell tables for the arithmetic window

The finite table is obtained by regrouping the original coclosed basis.
The two curl branches are counted by their differentiated trace and kernel,
not by an assigned field multiplicity. All history matrix entries remain.
The same table reconstructs the Gaussian comparison Hessian and is the
quantity enclosed by a finite interval certificate.

The table supplies the spectral and numerical part of a joint level test.
It does not prescribe a number of positions or an effective vertex.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionShells

open HistoryHaarSectionWindow HistoryHaarSectionContent
open Geometry.SourceOneFormSpectralCore
open Geometry.SourceOneFormCurlSpectrum
open Geometry.SourceOneFormCoclosedSpectrum
open Geometry.SourceOneFormMultiplicity
open Geometry.SourceOneFormHodgeLaplacian

private theorem sum_indicator {ι : Type*} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (x : ℝ) :
    (∑ i, if p i then x else 0) = (Fintype.card {i // p i} : ℝ) * x := by
  classical
  simp [Finset.sum_ite, Fintype.card_subtype]

/-- Every polarization in one original source row is retained. The zero
curl subspace is removed by the already proved coclosed restriction. -/
theorem differential_row_trace {m : ℕ} (hm : Even m) (f : ℝ → ℝ) :
    (∑ j : Fin (3 * (m + 1)),
      if curlEigenvalue m j = 0 then 0 else f (curlEigenvalue m j ^ 2)) =
      (m + 3 : ℕ) * f (((m : ℝ) + 2) ^ 2) +
        (m - 1 : ℕ) * f ((m : ℝ) ^ 2) := by
  classical
  by_cases hm0 : m = 0
  · subst m
    simp [degree_zero_eigenvalue]
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have hpoint (j : Fin (3 * (m + 1))) :
        (if curlEigenvalue m j = 0 then 0 else f (curlEigenvalue m j ^ 2)) =
          (if curlEigenvalue m j = (m : ℝ) + 2 then f (((m : ℝ) + 2) ^ 2) else 0) +
          (if curlEigenvalue m j = -(m : ℝ) then f ((m : ℝ) ^ 2) else 0) := by
      rcases Geometry.SourceOneFormCurlBranches.curlEigenvalue_branches m j with hz | hp | hn
      · have hp' : curlEigenvalue m j ≠ (m : ℝ) + 2 := by linarith
        have hn' : curlEigenvalue m j ≠ -(m : ℝ) := by linarith
        rw [ite_eq_left hz, ite_eq_right hp', ite_eq_right hn']
        exact (zero_add 0).symm
      · have hz' : curlEigenvalue m j ≠ 0 := by linarith
        have hn' : curlEigenvalue m j ≠ -(m : ℝ) := by linarith
        rw [ite_eq_right hz', ite_eq_left hp, ite_eq_right hn', hp, add_zero]
      · have hz' : curlEigenvalue m j ≠ 0 := by linarith
        have hp' : curlEigenvalue m j ≠ (m : ℝ) + 2 := by linarith
        rw [ite_eq_right hz', ite_eq_right hp', ite_eq_left hn, hn, neg_sq, zero_add]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, sum_indicator, sum_indicator]
    change (plusMultiplicity m : ℝ) * _ + (minusMultiplicity m : ℝ) * _ = _
    rw [(nonconstant_branch_multiplicities hm hm0).1,
      (nonconstant_branch_multiplicities hm hm0).2]

def rowEmbedding (m : ℕ) (hm : Even m)
    (p : Fin (m + 1) × Fin (3 * (m + 1))) : CurlIndex :=
  ⟨⟨⟨m, hm⟩, p.1⟩, p.2⟩

theorem rowEmbedding_injective (m : ℕ) (hm : Even m) :
    Function.Injective (rowEmbedding m hm) := by
  intro a b h
  have hh : a.1 = b.1 ∧ a.2 = b.2 := by simpa [rowEmbedding] using h
  exact Prod.ext hh.1 hh.2

private def rowSet (m : ℕ) : Finset CurlIndex := by
  classical
  exact if hm : Even m then Finset.univ.image (rowEmbedding m hm) else ∅

private theorem rowSet_degree {m : ℕ} {a : CurlIndex} (h : a ∈ rowSet m) :
    a.1.1.val = m := by
  classical
  unfold rowSet at h
  split_ifs at h with hm
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
    rfl
  · simp at h

theorem finite_curl_trace (D : ℕ) (f : CurlIndex → ℝ) :
    (∑ a ∈ HistorySpectralWindow.curlCandidates D, f a) =
      ∑ m ∈ Finset.range D, if hm : Even m then
        ∑ p : Fin (m + 1) × Fin (3 * (m + 1)), f (rowEmbedding m hm p)
      else 0 := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(Finset.range D)) rowSet := by
    intro m _ n _ hmn
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact hmn ((rowSet_degree ha).symm.trans (rowSet_degree hb))
  change (∑ a ∈ (Finset.range D).biUnion rowSet, f a) = _
  rw [Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro m _
  unfold rowSet
  split_ifs with hm
  · rw [Finset.sum_image (fun _ _ _ _ h => rowEmbedding_injective m hm h)]
  · simp

/-- The exact finite table of both nonzero curl signs, including the left
matrix-coefficient multiplicity `m+1`. No eigenvector choice remains in it. -/
theorem finite_coclosed_trace (D : ℕ) (f : ℝ → ℝ) :
    (∑ a ∈ HistorySpectralWindow.fieldCandidates D, f (hodgeEigenvalue a)) =
      ∑ m ∈ Finset.range D, if Even m then
        (m + 1 : ℕ) * ((m + 3 : ℕ) * f (((m : ℝ) + 2) ^ 2) +
          (m - 1 : ℕ) * f ((m : ℝ) ^ 2)) else 0 := by
  classical
  change (∑ a ∈ (HistorySpectralWindow.curlCandidates D).subtype
    (fun a => eigenvalue a ≠ 0), f (eigenvalue a.val ^ 2)) = _
  rw [Finset.sum_subtype_eq_sum_filter (fun a : CurlIndex => f (eigenvalue a ^ 2)),
    Finset.sum_filter]
  rw [finite_curl_trace]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs with hm
  · rw [Fintype.sum_prod_type]
    have hrow (p : Fin (m + 1)) :
        (∑ j : Fin (3 * (m + 1)),
          if eigenvalue (rowEmbedding m hm (p, j)) ≠ 0 then
            f (eigenvalue (rowEmbedding m hm (p, j)) ^ 2) else 0) =
          (m + 3 : ℕ) * f (((m : ℝ) + 2) ^ 2) +
            (m - 1 : ℕ) * f ((m : ℝ) ^ 2) := by
      change (∑ j : Fin (3 * (m + 1)),
        if curlEigenvalue m j ≠ 0 then f (curlEigenvalue m j ^ 2) else 0) = _
      have heq (j : Fin (3 * (m + 1))) :
          (if curlEigenvalue m j ≠ 0 then f (curlEigenvalue m j ^ 2) else 0) =
            (if curlEigenvalue m j = 0 then 0 else f (curlEigenvalue m j ^ 2)) := by
        by_cases h : curlEigenvalue m j = 0 <;> simp [h]
      simp_rw [heq]
      exact differential_row_trace hm f
    simp_rw [hrow]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · rfl

def fieldIntegral (B a : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - a), Real.exp (-(u ^ 2 + a))

theorem fieldIntegral_nonneg (B a : ℝ) : 0 ≤ fieldIntegral B a :=
  intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _)
    (fun _ => (Real.exp_pos _).le)

theorem fieldIntegral_eq_zero {B a : ℝ} (h : B ≤ a) : fieldIntegral B a = 0 := by
  simp [fieldIntegral, Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr h)]

theorem branchIntegral_field (N : ℕ) (B : ℝ)
    (a : HistoryHaarClosedHessian.BasisIndex N) :
    branchIntegral N B (.inl a) = fieldIntegral B (hodgeEigenvalue a.2) := by
  apply intervalIntegral.integral_congr
  intro u _
  have hp : 0 < u ^ 2 + hodgeEigenvalue a.2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg u) (HistoryHaarClosedHessian.eigenvalue_pos N a)
  simp only [kernel, kinetic, HistoryHaarSectionJointHessian.eigenvalue,
    HistoryHaarClosedHessian.eigenvalue, Sum.elim_inl, div_self (ne_of_gt hp), one_pow,
    one_mul]

private theorem fieldResponse_candidates (N : ℕ) (B : ℝ) :
    fieldResponse N B =
      ∑ a ∈ (Finset.univ : Finset (HistoryHaarClosedHessian.Label N)) ×ˢ
        HistorySpectralWindow.fieldCandidates (HistorySpectralWindow.enumerationBound B),
        branchIntegral N B (.inl a) := by
  classical
  have hfield : fieldResponse N B =
      ∑ i ∈ support N B, Sum.elim (fun a => branchIntegral N B (.inl a)) (fun _ => 0) i := by
    rw [fieldResponse, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases i <;> simp
  rw [hfield]
  have hext : (∑ i ∈ support N B,
      Sum.elim (fun a => branchIntegral N B (.inl a)) (fun _ => 0) i) =
      ∑ i ∈ candidates N (HistorySpectralWindow.enumerationBound B),
        Sum.elim (fun a => branchIntegral N B (.inl a)) (fun _ => 0) i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hn
    cases i with
    | inl a =>
      apply branchIntegral_eq_zero
      exact le_of_not_gt (fun h => hn ((mem_support N B _).mpr h))
    | inr a => rfl
  rw [hext, candidates, Finset.sum_sumElim]
  simp

/-- All field rows of the actual joint operator, with every original
history matrix entry. The factor is `d_N^2`, not a supplied colour count. -/
theorem fieldResponse_eq_rows (N : ℕ) (B : ℝ) :
    fieldResponse N B = (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 *
      ∑ m ∈ Finset.range (HistorySpectralWindow.enumerationBound B), if Even m then
        (m + 1 : ℕ) *
          ((m + 3 : ℕ) * fieldIntegral B (((m : ℝ) + 2) ^ 2) +
            (m - 1 : ℕ) * fieldIntegral B ((m : ℝ) ^ 2)) else 0 := by
  classical
  rw [fieldResponse_candidates, Finset.sum_product]
  simp_rw [branchIntegral_field]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, finite_coclosed_trace]
  congr 1
  simp [HistoryHaarClosedHessian.Label, HistoryAdjointCasimir.dimension, pow_two]

/-- Explicit complete shell table of the same variational response. -/
def shellTable (N : ℕ) (B : ℝ) : ℝ :=
  (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 *
    (∑ m ∈ Finset.range (HistorySpectralWindow.enumerationBound B), if Even m then
      (m + 1 : ℕ) *
        ((m + 3 : ℕ) * fieldIntegral B (((m : ℝ) + 2) ^ 2) +
          (m - 1 : ℕ) * fieldIntegral B ((m : ℝ) ^ 2)) else 0) +
    ∑ j : Fin (positionCount B),
      (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
        positionIntegral N j.val B

theorem responseTrace_eq_shellTable (N : ℕ) (B : ℝ) :
    responseTrace N B = shellTable N B := by
  rw [responseTrace_content_decomposition, fieldResponse_eq_rows]
  rfl

open HistoryHaarSectionComparison (kineticFraction weight kineticPrecision precision)

theorem kineticFraction_mono_nonneg (N : ℕ)
    (i : HistoryHaarSectionJointHessian.Index N) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    kineticFraction N i u ≤ kineticFraction N i v := by
  have hp := HistoryHaarSectionComparison.precision_pos N i u
  have hp' := HistoryHaarSectionComparison.precision_pos N i v
  have hsq : 0 ≤ v ^ 2 - u ^ 2 := by nlinarith
  have hprod := mul_nonneg hsq (restoring_nonneg N i)
  rw [kineticFraction, kineticFraction, div_le_div_iff₀ hp hp']
  unfold kineticPrecision precision
  rw [source_response_decomposition]
  nlinarith

theorem weight_antitone_nonneg (N : ℕ)
    (i : HistoryHaarSectionJointHessian.Index N) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    weight N i v ≤ weight N i u := by
  apply Real.exp_le_exp.mpr
  unfold kineticPrecision
  nlinarith

/-- The Gaussian and the resolvent ratio move in opposite directions.
Their actual endpoint values give two-sided bounds on every subinterval;
neither factor is replaced by one or discarded. -/
theorem kernel_rectangle_bounds (N : ℕ)
    (i : HistoryHaarSectionJointHessian.Index N) {u v x : ℝ}
    (hu : 0 ≤ u) (hx : x ∈ Set.Icc u v) :
    kineticFraction N i u ^ 2 * weight N i v ≤ kernel N i x ∧
      kernel N i x ≤ kineticFraction N i v ^ 2 * weight N i u := by
  have hx0 : 0 ≤ x := le_trans hu hx.1
  have hlo := kineticFraction_mono_nonneg N i hu hx.1
  have hhi := kineticFraction_mono_nonneg N i hx0 hx.2
  have hr0 := HistoryHaarSectionComparison.kineticFraction_nonneg N i u
  have hrx := HistoryHaarSectionComparison.kineticFraction_nonneg N i x
  have hrv := HistoryHaarSectionComparison.kineticFraction_nonneg N i v
  have hlosq : kineticFraction N i u ^ 2 ≤ kineticFraction N i x ^ 2 := by nlinarith
  have hhisq : kineticFraction N i x ^ 2 ≤ kineticFraction N i v ^ 2 := by nlinarith
  have hwlo := weight_antitone_nonneg N i hx0 hx.2
  have hwhi := weight_antitone_nonneg N i hu hx.1
  change kineticFraction N i u ^ 2 * weight N i v ≤
      kineticFraction N i x ^ 2 * weight N i x ∧
    kineticFraction N i x ^ 2 * weight N i x ≤
      kineticFraction N i v ^ 2 * weight N i u
  exact ⟨mul_le_mul hlosq hwlo (HistoryHaarSectionComparison.weight_pos N i v).le
      (sq_nonneg _),
    mul_le_mul hhisq hwhi (HistoryHaarSectionComparison.weight_pos N i x).le (sq_nonneg _)⟩

def segmentLower (N : ℕ) (i : HistoryHaarSectionJointHessian.Index N) (u v : ℝ) : ℝ :=
  (v - u) * (kineticFraction N i u ^ 2 * weight N i v)

def segmentUpper (N : ℕ) (i : HistoryHaarSectionJointHessian.Index N) (u v : ℝ) : ℝ :=
  (v - u) * (kineticFraction N i v ^ 2 * weight N i u)

theorem segment_integral_bounds (N : ℕ) (i : HistoryHaarSectionJointHessian.Index N)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    segmentLower N i u v ≤ (∫ x in u..v, kernel N i x) ∧
      (∫ x in u..v, kernel N i x) ≤ segmentUpper N i u v := by
  constructor
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      huv intervalIntegrable_const
      ((kernel_continuous N i).intervalIntegrable u v)
      (fun x hx => (kernel_rectangle_bounds N i hu hx).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, segmentLower] using h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) huv
      ((kernel_continuous N i).intervalIntegrable u v) intervalIntegrable_const
      (fun x hx => (kernel_rectangle_bounds N i hu hx).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, segmentUpper] using h

/-- Arbitrarily refined finite partitions enclose the original branch
integral. The sum telescopes exactly, so no spectral or frequency piece is
lost between adjacent cells. All mesh points are comparison coordinates. -/
theorem partition_integral_bounds (N : ℕ) (i : HistoryHaarSectionJointHessian.Index N)
    (a : ℕ → ℝ) (n : ℕ) (ha : ∀ k ≤ n, 0 ≤ a k)
    (hmono : ∀ k < n, a k ≤ a (k + 1)) :
    (∑ k ∈ Finset.range n, segmentLower N i (a k) (a (k + 1))) ≤
        (∫ x in a 0..a n, kernel N i x) ∧
      (∫ x in a 0..a n, kernel N i x) ≤
        ∑ k ∈ Finset.range n, segmentUpper N i (a k) (a (k + 1)) := by
  have htel := intervalIntegral.sum_integral_adjacent_intervals
    (μ := MeasureTheory.volume) (f := kernel N i) (a := a) (n := n)
    (fun k _ => (kernel_continuous N i).intervalIntegrable (a k) (a (k + 1)))
  rw [← htel]
  constructor
  · exact Finset.sum_le_sum (fun k hk =>
      (segment_integral_bounds N i (ha k (Finset.mem_range.mp hk).le)
        (hmono k (Finset.mem_range.mp hk))).1)
  · exact Finset.sum_le_sum (fun k hk =>
      (segment_integral_bounds N i (ha k (Finset.mem_range.mp hk).le)
        (hmono k (Finset.mem_range.mp hk))).2)

/-- A finite mesh of one original frequency interval. These are numerical
comparison coordinates; they do not change the source or its support. -/
structure BranchPartition (N : ℕ) (B : ℝ)
    (i : HistoryHaarSectionJointHessian.Index N) where
  point : ℕ → ℝ
  cells : ℕ
  first : point 0 = 0
  last : point cells = Real.sqrt (B - kinetic N i)
  nonneg : ∀ k ≤ cells, 0 ≤ point k
  ordered : ∀ k < cells, point k ≤ point (k + 1)

def uniformPartition (N : ℕ) (B : ℝ) (i : HistoryHaarSectionJointHessian.Index N)
    (n : ℕ) (hn : 0 < n) : BranchPartition N B i where
  point k := (k : ℝ) / n * Real.sqrt (B - kinetic N i)
  cells := n
  first := by simp
  last := by rw [div_self (by exact_mod_cast hn.ne')]; simp
  nonneg k _ := mul_nonneg (div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg n))
    (Real.sqrt_nonneg _)
  ordered k _ := mul_le_mul_of_nonneg_right
    ((div_le_div_iff_of_pos_right (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
      (by exact_mod_cast Nat.le_succ k)) (Real.sqrt_nonneg _)

def partitionLower {N : ℕ} {B : ℝ} {i : HistoryHaarSectionJointHessian.Index N}
    (p : BranchPartition N B i) : ℝ :=
  ∑ k ∈ Finset.range p.cells, segmentLower N i (p.point k) (p.point (k + 1))

def partitionUpper {N : ℕ} {B : ℝ} {i : HistoryHaarSectionJointHessian.Index N}
    (p : BranchPartition N B i) : ℝ :=
  ∑ k ∈ Finset.range p.cells, segmentUpper N i (p.point k) (p.point (k + 1))

theorem branch_partition_bounds {N : ℕ} {B : ℝ}
    {i : HistoryHaarSectionJointHessian.Index N} (p : BranchPartition N B i) :
    partitionLower p ≤ branchIntegral N B i ∧ branchIntegral N B i ≤ partitionUpper p := by
  have h := partition_integral_bounds N i p.point p.cells p.nonneg p.ordered
  simpa only [p.first, p.last, branchIntegral, partitionLower, partitionUpper] using h

/-- Bounds enclose the actual differential shell table, not an old
homogeneous model or an independently supplied response coefficient. -/
structure ResponseBounds (N : ℕ) (B : ℝ) where
  lo : ℝ
  hi : ℝ
  encloses : lo ≤ shellTable N B ∧ shellTable N B ≤ hi

/-- Construct bounds from proved finite cells; no enclosure of an unknown
coefficient is assumed. The sums range over the complete actual support. -/
def responseBounds_from_partition (N : ℕ) (B : ℝ)
    (p : ∀ i, BranchPartition N B i) : ResponseBounds N B where
  lo := ∑ i ∈ support N B, partitionLower (p i)
  hi := ∑ i ∈ support N B, partitionUpper (p i)
  encloses := by
    rw [← responseTrace_eq_shellTable]
    exact ⟨Finset.sum_le_sum (fun i _ => (branch_partition_bounds (p i)).1),
      Finset.sum_le_sum (fun i _ => (branch_partition_bounds (p i)).2)⟩

theorem consume_response_bounds {N : ℕ} {B : ℝ} (b : ResponseBounds N B) :
    b.lo ≤ responseTrace N B ∧ responseTrace N B ≤ b.hi := by
  rw [responseTrace_eq_shellTable]
  exact b.encloses

theorem consume_scale_bounds {N : ℕ} {B q : ℝ} (hq : 0 < q)
    (b : ResponseBounds N B) :
    b.lo / q ≤ HistoryHaarSectionScale.thresholdScale N B q ∧
      HistoryHaarSectionScale.thresholdScale N B q ≤ b.hi / q := by
  have h := consume_response_bounds b
  exact ⟨(div_le_div_iff_of_pos_right hq).mpr h.1,
    (div_le_div_iff_of_pos_right hq).mpr h.2⟩

/-- The count is certified using bounds on the complete response table.
The square is taken only after retaining the complete common trace. -/
theorem content_count_from_bounds {N m : ℕ} {B q : ℝ} (hq : 0 < q)
    (b : ResponseBounds N B) (hlo : 0 ≤ b.lo)
    (hlower : Geometry.SourceScalarKineticForm.position m < (b.lo / q) ^ 2)
    (hupper : (b.hi / q) ^ 2 ≤ Geometry.SourceScalarKineticForm.position (m + 1)) :
    positionCount (HistoryHaarSectionScale.thresholdScale N B q ^ 2) = m + 1 := by
  have hb := consume_scale_bounds hq b
  have hlop : 0 ≤ b.lo / q := div_nonneg hlo hq.le
  have hr : 0 ≤ HistoryHaarSectionScale.thresholdScale N B q :=
    HistoryHaarSectionScale.thresholdScale_nonneg N hq
  rw [positionCount_eq_succ_iff]
  constructor <;> nlinarith

/-- A finite joint selector, with shell exclusion, content and crossing
all checked against the actual source. The two interval enclosures concern
the explicit full table at the candidate and preceding integer levels. -/
theorem level_from_certified_shell_table (N K R m : ℕ) {q : ℝ} (hq : 0 < q)
    (bR : ResponseBounds N (R : ℝ)) (bK : ResponseBounds N (K : ℝ))
    (i : HistoryHaarSectionJointHessian.Index N)
    (hexcluded : i ∉ support N (R : ℝ)) (hnext : kinetic N i < (K : ℝ) + 2)
    (hlo : 0 ≤ bR.lo)
    (hcontentlo : Geometry.SourceScalarKineticForm.position m < (bR.lo / q) ^ 2)
    (hcontenthi : (bR.hi / q) ^ 2 ≤ Geometry.SourceScalarKineticForm.position (m + 1))
    (hcross : (bK.hi / q) ^ 2 ≤ Geometry.SourceScalarKineticForm.position m) :
    R = K + 1 := by
  apply HistoryHaarSectionScale.level_from_shell_content_and_crossing
    N K R m hq i hexcluded hnext
  · exact content_count_from_bounds hq bR hlo hcontentlo hcontenthi
  · have hk := (consume_scale_bounds hq bK).2
    have hr : 0 ≤ HistoryHaarSectionScale.thresholdScale N (K : ℝ) q :=
      HistoryHaarSectionScale.thresholdScale_nonneg N hq
    nlinarith

structure Conclusions : Prop where
  actual_row_polarizations : ∀ m, Even m → ∀ f : ℝ → ℝ,
    (∑ j : Fin (3 * (m + 1)),
      if curlEigenvalue m j = 0 then 0 else f (curlEigenvalue m j ^ 2)) =
      (m + 3 : ℕ) * f (((m : ℝ) + 2) ^ 2) + (m - 1 : ℕ) * f ((m : ℝ) ^ 2)
  complete_field_table : ∀ N B,
    fieldResponse N B = (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 *
      ∑ m ∈ Finset.range (HistorySpectralWindow.enumerationBound B), if Even m then
        (m + 1 : ℕ) *
          ((m + 3 : ℕ) * fieldIntegral B (((m : ℝ) + 2) ^ 2) +
            (m - 1 : ℕ) * fieldIntegral B ((m : ℝ) ^ 2)) else 0
  actual_complete_response : ∀ N B, responseTrace N B = shellTable N B
  certified_response : ∀ N B (b : ResponseBounds N B),
    b.lo ≤ responseTrace N B ∧ responseTrace N B ≤ b.hi
  constructed_response_bounds : ∀ N B (p : ∀ i, BranchPartition N B i),
    (∑ i ∈ support N B, partitionLower (p i)) ≤ responseTrace N B ∧
      responseTrace N B ≤ ∑ i ∈ support N B, partitionUpper (p i)
  certified_content : ∀ (N m : ℕ) (B q : ℝ), 0 < q → ∀ b : ResponseBounds N B,
    0 ≤ b.lo → Geometry.SourceScalarKineticForm.position m < (b.lo / q) ^ 2 →
    (b.hi / q) ^ 2 ≤ Geometry.SourceScalarKineticForm.position (m + 1) →
    positionCount (HistoryHaarSectionScale.thresholdScale N B q ^ 2) = m + 1

theorem generated : Conclusions where
  actual_row_polarizations := fun _ hm => differential_row_trace hm
  complete_field_table := fieldResponse_eq_rows
  actual_complete_response := responseTrace_eq_shellTable
  certified_response := fun _ _ => consume_response_bounds
  constructed_response_bounds := fun N B p =>
    consume_response_bounds (responseBounds_from_partition N B p)
  certified_content := fun _ _ _ _ hq => content_count_from_bounds hq

end GeneratedFoundations.Arithmetic.HistoryHaarSectionShells
