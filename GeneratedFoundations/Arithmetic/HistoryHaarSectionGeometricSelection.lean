module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricContent
public import GeneratedFoundations.Arithmetic.HistoryHaarSectionShells

/-!
# Native content tests for geometric stationarity

The content equation is evaluated on the original scalar and connection
support. Complete trace formulas retain the scalar multiplicities and both
curl branches, together with every history matrix entry. In particular the
connection multiplicity grows as the square of the generated dimension;
it is not replaced by a supplied colour or position count.

The first two joint spectral cells give exact tests of the original
geometric Gaussian free energy. These tests concern the zero-connection
Gaussian partition at fixed spatial support. The moving frequency window
and the connection-dependent collective response remain separate variations.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Set Filter
open MeasureTheory ProbabilityTheory

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricSelection

open HistoryHaarSectionWindow HistoryHaarSectionContent
open HistoryHaarSectionGeometricContent
open HistoryHaarSectionGeometricState (force freeEnergy)
open HistoryHaarSectionJointHessian (Index)
open Geometry.SourceOneFormHodgeLaplacian (hodgeEigenvalue)

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def scalarTrace (N : ℕ) (B : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ support N B, if i.isRight = true then f (kinetic N i) else 0

def connectionTrace (N : ℕ) (B : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ support N B, if i.isRight = true then 0 else f (kinetic N i)

theorem scalarTrace_eq_rows (N : ℕ) (B : ℝ) (f : ℝ → ℝ) :
    scalarTrace N B f = ∑ j : Fin (positionCount B),
      (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
        f (Geometry.SourceScalarKineticForm.position j.val) := by
  classical
  rw [scalarTrace, ← Finset.sum_filter, scalarSupport_eq_image, Finset.sum_image]
  · change (∑ i : ContentLabels N (positionCount B),
      f (kinetic N (contentIndex N (positionCount B) i))) = _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    simp only [contentIndex, kinetic_positionIndex, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, HistoryHaarSectionAction.position_multiplicity]
  · exact fun _ _ _ _ h => contentIndex_injective _ _ h

theorem connectionTrace_eq_rows (N : ℕ) (B : ℝ) (f : ℝ → ℝ) :
    connectionTrace N B f = (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 *
      ∑ m ∈ Finset.range (HistorySpectralWindow.enumerationBound B), if Even m then
        (m + 1 : ℕ) *
          ((m + 3 : ℕ) * (if ((m : ℝ) + 2) ^ 2 < B then f (((m : ℝ) + 2) ^ 2) else 0) +
            (m - 1 : ℕ) * (if (m : ℝ) ^ 2 < B then f ((m : ℝ) ^ 2) else 0)) else 0 := by
  classical
  have he : connectionTrace N B f =
      ∑ i ∈ candidates N (HistorySpectralWindow.enumerationBound B),
        Sum.elim (fun a => if hodgeEigenvalue a.2 < B then f (hodgeEigenvalue a.2) else 0)
          (fun _ => 0) i := by
    unfold connectionTrace support
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases i <;> simp [kinetic, HistoryHaarClosedHessian.eigenvalue]
  rw [he, candidates, Finset.sum_sumElim]
  simp only [Finset.sum_product, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [HistoryHaarSectionShells.finite_coclosed_trace
    (HistorySpectralWindow.enumerationBound B) (fun a => if a < B then f a else 0)]
  congr 1
  simp [HistoryHaarClosedHessian.Label, HistoryAdjointCasimir.dimension, pow_two]

theorem scalarCount_eq_trace (N : ℕ) (B : ℝ) :
    scalarCount N B = scalarTrace N B (fun _ => 1) := by
  classical
  unfold scalarCount
  rw [Finset.univ_eq_attach, Finset.sum_attach
    (HistoryHaarSectionCovariance.frequencySupport N B 0)
    (fun i => if i.isRight = true then (1 : ℝ) else 0)]
  simp [HistoryHaarSectionCovariance.frequencySupport, scalarTrace]

theorem connectionCount_eq_trace (N : ℕ) (B : ℝ) :
    connectionCount N B = connectionTrace N B (fun _ => 1) := by
  classical
  unfold connectionCount
  rw [Finset.univ_eq_attach, Finset.sum_attach
    (HistoryHaarSectionCovariance.frequencySupport N B 0)
    (fun i => if i.isRight = true then (0 : ℝ) else 1)]
  simp [HistoryHaarSectionCovariance.frequencySupport, connectionTrace]

theorem restoringShare_eq_trace (N : ℕ) (B c : ℝ) :
    restoringShare N B c = scalarTrace N B (fun a =>
      c ^ 2 * HistoryDefiningResponse.coefficient N /
        (a + c ^ 2 * HistoryDefiningResponse.coefficient N)) := by
  classical
  unfold restoringShare
  rw [Finset.univ_eq_attach, Finset.sum_attach
    (HistoryHaarSectionCovariance.frequencySupport N B 0)
    (fun i => if i.isRight = true then
      c ^ 2 * restoring N i / (kinetic N i + c ^ 2 * restoring N i) else 0)]
  simp only [HistoryHaarSectionCovariance.frequencySupport,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, scalarTrace]
  apply Finset.sum_congr rfl
  intro i _
  cases i <;> simp [restoring]

theorem scalarTrace_first_cell (N : ℕ) {B : ℝ} (hlo : 0 < B) (hhi : B ≤ 8)
    (f : ℝ → ℝ) :
    scalarTrace N B f = (HistoryAdjointCasimir.dimension N : ℝ) * f 0 := by
  rw [scalarTrace_eq_rows,
    (positionCount_eq_one_iff B).2 ⟨hlo, hhi⟩]
  simp [Geometry.SourceScalarKineticForm.position_eq]

theorem scalarTrace_second_cell (N : ℕ) {B : ℝ} (hlo : 8 < B) (hhi : B ≤ 24)
    (f : ℝ → ℝ) :
    scalarTrace N B f = (HistoryAdjointCasimir.dimension N : ℝ) * (f 0 + 9 * f 8) := by
  rw [scalarTrace_eq_rows,
    (positionCount_eq_two_iff B).2 ⟨hlo, hhi⟩, Fin.sum_univ_two]
  norm_num [Geometry.SourceScalarKineticForm.position_eq]
  ring

theorem connectionTrace_first_shell (N : ℕ) {B : ℝ} (hlo : 4 < B) (hhi : B ≤ 16)
    (f : ℝ → ℝ) :
    connectionTrace N B f = 6 * (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * f 4 := by
  have he : connectionTrace N B f = connectionTrace N 5 f := by
    classical
    have hset : (support N B).filter (fun i => i.isRight = false) =
        (support N 5).filter (fun i => i.isRight = false) := by
      ext i
      cases i with
      | inl a =>
        simp only [Finset.mem_filter, mem_support, Sum.isRight_inl, and_true]
        exact (HistorySpectralWindow.field_first_shell a.2 hlo hhi).trans
          (HistorySpectralWindow.field_first_shell a.2 (by norm_num) (by norm_num)).symm
      | inr a => simp
    have hf (C : ℝ) : connectionTrace N C f =
        ∑ i ∈ (support N C).filter (fun i => i.isRight = false), f (kinetic N i) := by
      rw [connectionTrace, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      cases i <;> simp
    rw [hf, hf, hset]
  rw [he, connectionTrace_eq_rows]
  norm_num [HistorySpectralWindow.enumerationBound, Finset.sum_range_succ]
  ring

def restoringSlope (N : ℕ) (B c : ℝ) : ℝ :=
  ∑ j : Fin (positionCount B),
    (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
      (2 * c * HistoryDefiningResponse.coefficient N *
        Geometry.SourceScalarKineticForm.position j.val /
        (Geometry.SourceScalarKineticForm.position j.val +
          c ^ 2 * HistoryDefiningResponse.coefficient N) ^ 2)

theorem restoringShare_hasDerivAt (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (restoringShare N B) (restoringSlope N B c) c := by
  have hd (j : Fin (positionCount B)) : HasDerivAt (fun r : ℝ =>
      (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
        (r ^ 2 * HistoryDefiningResponse.coefficient N /
          (Geometry.SourceScalarKineticForm.position j.val +
            r ^ 2 * HistoryDefiningResponse.coefficient N)))
      ((HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
        (2 * c * HistoryDefiningResponse.coefficient N *
          Geometry.SourceScalarKineticForm.position j.val /
          (Geometry.SourceScalarKineticForm.position j.val +
            c ^ 2 * HistoryDefiningResponse.coefficient N) ^ 2)) c := by
    have hp : 0 < Geometry.SourceScalarKineticForm.position j.val +
        c ^ 2 * HistoryDefiningResponse.coefficient N :=
      add_pos_of_nonneg_of_pos (Geometry.SourceCasimirClosure.energy_nonneg _)
        (mul_pos (sq_pos_of_pos hc) (HistoryDefiningResponse.coefficient_pos N))
    have ht := ((hasDerivAt_id c).pow 2).mul_const (HistoryDefiningResponse.coefficient N)
    convert! (ht.div ((hasDerivAt_const c _).add ht) hp.ne').const_mul
      ((HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) : ℝ) using 1
    congr 1
    dsimp
    ring
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)
  convert! hs using 1
  funext r
  rw [restoringShare_eq_trace, scalarTrace_eq_rows]

theorem restoringSlope_nonneg (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    0 ≤ restoringSlope N B c := by
  have hm := HistoryDefiningResponse.coefficient_pos N
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg
    (mul_nonneg (by positivity) (Geometry.SourceCasimirClosure.energy_nonneg _))
    (sq_nonneg _))

theorem restoringSlope_pos (N : ℕ) {B c : ℝ} (hB : 8 < B) (hc : 0 < c) :
    0 < restoringSlope N B c := by
  have hm := HistoryDefiningResponse.coefficient_pos N
  have hj : 1 < positionCount B :=
    (position_lt_iff 1 B).mp (by
      norm_num [Geometry.SourceScalarKineticForm.position_eq]
      exact hB)
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg
      (mul_nonneg (by positivity) (Geometry.SourceCasimirClosure.energy_nonneg _))
      (sq_nonneg _))
  · refine ⟨⟨1, hj⟩, Finset.mem_univ _, ?_⟩
    have hd := HistoryAdjointCasimir.dimension_pos N
    simp only [Geometry.SourceScalarKineticForm.position_eq]
    positivity

theorem logarithmic_force_hasDerivAt (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun r => r * force N B r) (2 * restoringSlope N B c) c := by
  have hd := (hasDerivAt_const c (scalarCount N B - connectionCount N B)).add
    ((restoringShare_hasDerivAt N B hc).const_mul 2)
  apply (hd.congr_deriv (by simp)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hc] with r hr
  exact logarithmic_force_content N B hr

theorem logarithmic_force_strictMonoOn (N : ℕ) {B : ℝ} (hB : 8 < B) :
    StrictMonoOn (fun c => c * force N B c) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro c hc
    exact (logarithmic_force_hasDerivAt N B hc).continuousAt.continuousWithinAt
  · intro c hc
    have hc' : 0 < c := interior_subset hc
    rw [(logarithmic_force_hasDerivAt N B hc').deriv]
    exact mul_pos (by norm_num) (restoringSlope_pos N hB hc')

theorem stationary_geometry_unique (N : ℕ) {B c r : ℝ}
    (hB : 8 < B) (hc : 0 < c) (hr : 0 < r)
    (hfc : force N B c = 0) (hfr : force N B r = 0) : c = r :=
  (logarithmic_force_strictMonoOn N hB).injOn hc hr (by rw [hfc, hfr]; ring)

theorem stationary_curvature_eq (N : ℕ) (B : ℝ) {c : ℝ}
    (hc : 0 < c) (hf : force N B c = 0) :
    HistoryHaarSectionGeometricState.curvature N B c = 2 * restoringSlope N B c / c := by
  have hd := (hasDerivAt_id c).mul
    (HistoryHaarSectionGeometricState.force_hasDerivAt N B hc)
  have he := hd.unique (logarithmic_force_hasDerivAt N B hc)
  simp only [hf, one_mul, zero_add, id_eq] at he
  apply (eq_div_iff hc.ne').2
  nlinarith

theorem stationary_curvature_pos (N : ℕ) {B c : ℝ}
    (hB : 8 < B) (hc : 0 < c) (hf : force N B c = 0) :
    0 < HistoryHaarSectionGeometricState.curvature N B c := by
  have hd := (hasDerivAt_id c).mul
    (HistoryHaarSectionGeometricState.force_hasDerivAt N B hc)
  have he := hd.unique (logarithmic_force_hasDerivAt N B hc)
  simp only [hf, one_mul, zero_add, id_eq] at he
  have hs := restoringSlope_pos N hB hc
  nlinarith

theorem stationary_variance_lt_directMean (N : ℕ) {B c : ℝ}
    (hB : 8 < B) (hc : 0 < c) (hf : force N B c = 0) :
    Var[Operations.FinitePrecisionGaussian.score
        (HistoryHaarSectionGeometricState.firstRealPrecision N B c);
        HistoryHaarSectionGeometricState.law N B c] <
      ∫ x, Operations.FinitePrecisionGaussian.score
        (HistoryHaarSectionGeometricState.secondRealPrecision N B c) x
        ∂HistoryHaarSectionGeometricState.law N B c := by
  have he := HistoryHaarSectionGeometricState.curvature_eq_mean_sub_variance N B hc
  have hp := stationary_curvature_pos N hB hc hf
  linarith

theorem logarithmic_force_first_cell (N : ℕ) {B c : ℝ}
    (hlo : 4 < B) (hhi : B ≤ 8) (hc : 0 < c) :
    c * force N B c = 3 * (HistoryAdjointCasimir.dimension N : ℝ) -
      6 * (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 := by
  have ht : c ^ 2 * HistoryDefiningResponse.coefficient N ≠ 0 :=
    ne_of_gt (mul_pos (sq_pos_of_pos hc) (HistoryDefiningResponse.coefficient_pos N))
  rw [logarithmic_force_content N B hc, scalarCount_eq_trace, connectionCount_eq_trace,
    restoringShare_eq_trace, scalarTrace_first_cell N (by linarith) hhi,
    scalarTrace_first_cell N (by linarith) hhi,
    connectionTrace_first_shell N hlo (by linarith)]
  simp [ht]
  ring

theorem force_first_cell_neg (N : ℕ) {B c : ℝ}
    (hlo : 4 < B) (hhi : B ≤ 8) (hc : 0 < c) : force N B c < 0 := by
  have hd : (4 : ℝ) ≤ HistoryAdjointCasimir.dimension N :=
    by exact_mod_cast HistoryAdjointCasimir.dimension_ge_four N
  have he := logarithmic_force_first_cell N hlo hhi hc
  have hs : c * force N B c < 0 := by
    nlinarith [sq_nonneg ((HistoryAdjointCasimir.dimension N : ℝ) - 4)]
  nlinarith

theorem logarithmic_force_second_cell (N : ℕ) {B c : ℝ}
    (hlo : 8 < B) (hhi : B ≤ 16) (hc : 0 < c) :
    c * force N B c =
      6 * (HistoryAdjointCasimir.dimension N : ℝ) /
        (8 + c ^ 2 * HistoryDefiningResponse.coefficient N) *
      ((2 - (HistoryAdjointCasimir.dimension N : ℝ)) *
        (8 + c ^ 2 * HistoryDefiningResponse.coefficient N) +
        3 * (c ^ 2 * HistoryDefiningResponse.coefficient N)) := by
  have ht : c ^ 2 * HistoryDefiningResponse.coefficient N ≠ 0 :=
    ne_of_gt (mul_pos (sq_pos_of_pos hc) (HistoryDefiningResponse.coefficient_pos N))
  have htp : 0 < c ^ 2 * HistoryDefiningResponse.coefficient N :=
    mul_pos (sq_pos_of_pos hc) (HistoryDefiningResponse.coefficient_pos N)
  have hp : 8 + c ^ 2 * HistoryDefiningResponse.coefficient N ≠ 0 := by positivity
  rw [logarithmic_force_content N B hc, scalarCount_eq_trace, connectionCount_eq_trace,
    restoringShare_eq_trace, scalarTrace_second_cell N hlo (by linarith),
    scalarTrace_second_cell N hlo (by linarith),
    connectionTrace_first_shell N (by linarith) hhi]
  simp only [zero_add, div_self ht, mul_one]
  field_simp [hp]
  ring

/-- Exact compatibility of the original counts and restoring fractions.
The generated dimension is constrained by its actual cardinality, not
treated as a continuously adjustable content parameter. -/
theorem stationary_second_cell_iff (N : ℕ) {B c : ℝ}
    (hlo : 8 < B) (hhi : B ≤ 16) (hc : 0 < c) :
    force N B c = 0 ↔ HistoryAdjointCasimir.dimension N = 4 ∧
      c ^ 2 * HistoryDefiningResponse.coefficient N = 16 := by
  let d : ℝ := HistoryAdjointCasimir.dimension N
  let t : ℝ := c ^ 2 * HistoryDefiningResponse.coefficient N
  have hd : 4 ≤ d := by
    dsimp [d]
    exact_mod_cast HistoryAdjointCasimir.dimension_ge_four N
  have ht : 0 < t := mul_pos (sq_pos_of_pos hc) (HistoryDefiningResponse.coefficient_pos N)
  have hf : 0 < 6 * d / (8 + t) := by positivity
  have he := logarithmic_force_second_cell N hlo hhi hc
  change c * force N B c = 6 * d / (8 + t) * ((2 - d) * (8 + t) + 3 * t) at he
  constructor
  · intro hz
    rw [hz, mul_zero] at he
    have heq : (2 - d) * (8 + t) + 3 * t = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left hf.ne'
    have hlt : d < 5 := by
      by_contra hn
      have hge : 0 ≤ (d - 5) * t := mul_nonneg (by linarith) ht.le
      nlinarith
    have hn : HistoryAdjointCasimir.dimension N < 5 := by
      dsimp [d] at hlt
      exact_mod_cast hlt
    have hn4 : HistoryAdjointCasimir.dimension N = 4 :=
      by have := HistoryAdjointCasimir.dimension_ge_four N; omega
    have hd4 : d = 4 := by dsimp [d]; rw [hn4]; norm_num
    rw [hd4] at heq
    exact ⟨hn4, by dsimp [t] at heq ⊢; nlinarith⟩
  · rintro ⟨hd4, ht16⟩
    have hd4' : d = 4 := by dsimp [d]; rw [hd4]; norm_num
    have ht16' : t = 16 := ht16
    rw [hd4', ht16'] at he
    norm_num at he
    exact he.resolve_left hc.ne'

theorem variational_second_cell_iff (N : ℕ) {B c : ℝ}
    (hlo : 8 < B) (hhi : B ≤ 16) (hc : 0 < c) :
    deriv (freeEnergy N B) c = 0 ↔ HistoryAdjointCasimir.dimension N = 4 ∧
      c ^ 2 * HistoryDefiningResponse.coefficient N = 16 := by
  rw [(HistoryHaarSectionGeometricState.freeEnergy_hasDerivAt N B hc).deriv]
  exact stationary_second_cell_iff N hlo hhi hc

def secondCellRadius (N : ℕ) : ℝ :=
  Real.sqrt (16 / HistoryDefiningResponse.coefficient N)

theorem secondCellRadius_pos (N : ℕ) : 0 < secondCellRadius N :=
  Real.sqrt_pos.mpr (div_pos (by norm_num) (HistoryDefiningResponse.coefficient_pos N))

theorem secondCellRadius_equation (N : ℕ) :
    secondCellRadius N ^ 2 * HistoryDefiningResponse.coefficient N = 16 := by
  have hm := HistoryDefiningResponse.coefficient_pos N
  rw [secondCellRadius, Real.sq_sqrt (div_pos (by norm_num) hm).le]
  exact div_mul_cancel₀ _ hm.ne'

theorem stationary_second_cell_radius (N : ℕ) {B c : ℝ}
    (hlo : 8 < B) (hhi : B ≤ 16) (hc : 0 < c) :
    force N B c = 0 ↔ HistoryAdjointCasimir.dimension N = 4 ∧ c = secondCellRadius N := by
  rw [stationary_second_cell_iff N hlo hhi hc]
  constructor
  · rintro ⟨hd, ht⟩
    refine ⟨hd, ?_⟩
    have he := secondCellRadius_equation N
    have hp := secondCellRadius_pos N
    have hm := HistoryDefiningResponse.coefficient_pos N
    have hs : c ^ 2 = secondCellRadius N ^ 2 := by nlinarith
    nlinarith
  · rintro ⟨hd, rfl⟩
    exact ⟨hd, secondCellRadius_equation N⟩

theorem stationary_second_cell_existsUnique_iff (N : ℕ) {B : ℝ}
    (hlo : 8 < B) (hhi : B ≤ 16) :
    (∃! c : ℝ, 0 < c ∧ force N B c = 0) ↔ HistoryAdjointCasimir.dimension N = 4 := by
  constructor
  · rintro ⟨c, ⟨hc, hf⟩, _⟩
    exact ((stationary_second_cell_iff N hlo hhi hc).1 hf).1
  · intro hd
    refine ⟨secondCellRadius N, ⟨secondCellRadius_pos N, ?_⟩, ?_⟩
    · exact (stationary_second_cell_radius N hlo hhi (secondCellRadius_pos N)).2 ⟨hd, rfl⟩
    · intro c h
      exact ((stationary_second_cell_radius N hlo hhi h.1).1 h.2).2

/-- The curvature at the actual content stationary point is strictly
positive, as calculated from the original Gaussian partition. -/
theorem curvature_second_cell_stationary (N : ℕ) {B c : ℝ}
    (hlo : 8 < B) (hhi : B ≤ 16) (hc : 0 < c) (hz : force N B c = 0) :
    HistoryHaarSectionGeometricState.curvature N B c =
      2 * HistoryDefiningResponse.coefficient N := by
  obtain ⟨hd, ht⟩ := (stationary_second_cell_iff N hlo hhi hc).1 hz
  have hp : 8 + c ^ 2 * HistoryDefiningResponse.coefficient N ≠ 0 := by rw [ht]; norm_num
  have hdq : HasDerivAt (fun r : ℝ => 8 + r ^ 2 * HistoryDefiningResponse.coefficient N)
      (2 * c * HistoryDefiningResponse.coefficient N) c := by
    convert! (hasDerivAt_const c (8 : ℝ)).add
      (((hasDerivAt_id c).pow 2).mul_const (HistoryDefiningResponse.coefficient N)) using 1
    simp
  have hdr := (hasDerivAt_const c (24 : ℝ)).sub
    ((hasDerivAt_const c (576 : ℝ)).div hdq hp)
  have hdr' : HasDerivAt (fun r : ℝ =>
      24 - 576 / (8 + r ^ 2 * HistoryDefiningResponse.coefficient N))
      (2 * c * HistoryDefiningResponse.coefficient N) c := by
    convert! hdr using 1
    rw [ht]
    ring
  have hprod : HasDerivAt (fun r : ℝ => r * force N B r)
      (2 * c * HistoryDefiningResponse.coefficient N) c := by
    apply hdr'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hc] with r hr
    rw [logarithmic_force_second_cell N hlo hhi hr, hd]
    have hrp : 0 < r ^ 2 * HistoryDefiningResponse.coefficient N :=
      mul_pos (sq_pos_of_pos hr) (HistoryDefiningResponse.coefficient_pos N)
    have hrq : 8 + r ^ 2 * HistoryDefiningResponse.coefficient N ≠ 0 := by positivity
    norm_num
    field_simp [hrq]
    ring
  have hactual := (hasDerivAt_id c).mul
    (HistoryHaarSectionGeometricState.force_hasDerivAt N B hc)
  have he := hactual.unique hprod
  simp only [hz, one_mul, zero_add, id_eq] at he
  nlinarith

/-- Every retained root contributes at least one complete history/phase
label. This is a lower bound on the actual generated carrier. -/
theorem generated_dimension_lower (N : ℕ) :
    4 * (N + 1) ≤ HistoryAdjointCasimir.dimension N := by
  have hinj : Function.Injective (fun b : HistoryRootSectors.Roots N =>
      (⟨b, HistoryModuleRepresentation.base b.val⟩ : HistoryCentralSectors.Label N)) := by
    intro a b h
    exact congrArg Sigma.fst h
  have hh := Fintype.card_le_of_injective _ hinj
  simp only [HistoryRootSectors.Roots, Fintype.card_fin] at hh
  rw [HistoryAdjointCasimir.dimension_eq]
  exact Nat.mul_le_mul_left 4 hh

theorem no_stationary_second_cell_after_birth {N : ℕ} (hN : 0 < N) {B c : ℝ}
    (hlo : 8 < B) (hhi : B ≤ 16) (hc : 0 < c) : force N B c ≠ 0 := by
  intro hz
  have hd := ((stationary_second_cell_iff N hlo hhi hc).1 hz).1
  have hb := generated_dimension_lower N
  omega

theorem generated_dimension_zero : HistoryAdjointCasimir.dimension 0 = 4 := by
  have hh : Fintype.card (CompleteHistory.History 1) = 1 := by
    rw [Fintype.card_congr (CompleteHistory.historyDecomposition 1), Fintype.card_sum]
    simp
  have hi : Fintype.card (HistoryModuleRepresentation.Index 0) = 1 := by
    rw [← HistoryModuleRepresentation.space_finrank,
      HistoryModuleRepresentation.actual_dimension]
    norm_num [hh]
  rw [HistoryAdjointCasimir.dimension_eq]
  change 4 * Fintype.card
    (Σ b : Fin 1, HistoryModuleRepresentation.Index b.val) = 4
  rw [Fintype.card_sigma, Fin.sum_univ_one]
  norm_num [hi]

theorem generated_dimension_eq_four_iff (N : ℕ) :
    HistoryAdjointCasimir.dimension N = 4 ↔ N = 0 := by
  constructor
  · intro hd
    have hl := generated_dimension_lower N
    omega
  · rintro rfl
    exact generated_dimension_zero

theorem native_second_cell_stationary_iff (N : ℕ) {B c : ℝ}
    (hlo : 8 < B) (hhi : B ≤ 16) (hc : 0 < c) :
    force N B c = 0 ↔ N = 0 ∧ c = Real.sqrt (128 / 15) := by
  rw [stationary_second_cell_radius N hlo hhi hc, generated_dimension_eq_four_iff]
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    unfold secondCellRadius
    rw [HistoryDefiningResponse.coefficient_eq, generated_dimension_zero]
    norm_num
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    unfold secondCellRadius
    rw [HistoryDefiningResponse.coefficient_eq, generated_dimension_zero]
    norm_num

theorem native_second_cell_curvature {B : ℝ} (hlo : 8 < B) (hhi : B ≤ 16) :
    HistoryHaarSectionGeometricState.curvature 0 B (Real.sqrt (128 / 15)) = 15 / 4 := by
  have hc : 0 < Real.sqrt (128 / 15 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hz := (native_second_cell_stationary_iff 0 hlo hhi hc).2 ⟨rfl, rfl⟩
  rw [curvature_second_cell_stationary 0 hlo hhi hc hz,
    HistoryDefiningResponse.coefficient_eq, generated_dimension_zero]
  norm_num

structure Conclusions : Prop where
  complete_scalar_trace : ∀ N B f, scalarTrace N B f = ∑ j : Fin (positionCount B),
    (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
      f (Geometry.SourceScalarKineticForm.position j.val)
  actual_first_connection_shell : ∀ N B, 4 < B → B ≤ 16 → ∀ f,
    connectionTrace N B f = 6 * (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * f 4
  first_cell_force_sign : ∀ N B c, 4 < B → B ≤ 8 → 0 < c → force N B c < 0
  complete_content_susceptibility : ∀ N B c, 0 < c →
    HasDerivAt (fun r => r * force N B r) (2 * restoringSlope N B c) c
  unique_stationary_geometry : ∀ N B c r, 8 < B → 0 < c → 0 < r →
    force N B c = 0 → force N B r = 0 → c = r
  actual_stationary_restoration : ∀ N B c, 8 < B → 0 < c → force N B c = 0 →
    0 < HistoryHaarSectionGeometricState.curvature N B c
  native_second_cell_equation : ∀ N B c, 8 < B → B ≤ 16 → 0 < c →
    (force N B c = 0 ↔ N = 0 ∧ c = Real.sqrt (128 / 15))
  native_restoring_curvature : ∀ B, 8 < B → B ≤ 16 →
    HistoryHaarSectionGeometricState.curvature 0 B (Real.sqrt (128 / 15)) = 15 / 4
  actual_history_dimension_growth : ∀ N, 4 * (N + 1) ≤ HistoryAdjointCasimir.dimension N

theorem generated : Conclusions where
  complete_scalar_trace := scalarTrace_eq_rows
  actual_first_connection_shell := fun N _ hl hu f => connectionTrace_first_shell N hl hu f
  first_cell_force_sign := fun N _ _ hl hu hc => force_first_cell_neg N hl hu hc
  complete_content_susceptibility := fun N B _ hc => logarithmic_force_hasDerivAt N B hc
  unique_stationary_geometry := fun N _ _ _ hB hc hr hf hg =>
    stationary_geometry_unique N hB hc hr hf hg
  actual_stationary_restoration := fun N _ _ hB hc hf => stationary_curvature_pos N hB hc hf
  native_second_cell_equation := fun N _ _ hl hu hc => native_second_cell_stationary_iff N hl hu hc
  native_restoring_curvature := fun _ hl hu => native_second_cell_curvature hl hu
  actual_history_dimension_growth := generated_dimension_lower

end GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricSelection
