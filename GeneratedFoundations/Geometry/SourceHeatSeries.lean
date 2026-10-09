module

public import GeneratedFoundations.Geometry.SourceCasimirClosure
public import GeneratedFoundations.Geometry.SourceWeakConvergence
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The convergent heat series of the actual source coefficients

The eigenvalue and the full matrix-coefficient multiplicity belong to the
closed source Casimir. At every positive parameter the character series is
absolutely convergent in the uniform norm, by an explicit polynomial times
exponential majorant. Consequently it defines a continuous function on the
original source group.

The conjugated diagonal coefficients fix the Fourier convention: integration
of the kernel times an original matrix entry gives its heat multiplier.
Both this identity and mass one follow from the already proved source Haar
orthogonality. Positivity and identification with the actual operation law
are separate consequences of these moments, not assumptions in this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceClebschGordan
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceWeakConvergence

namespace GeneratedFoundations.Geometry.SourceHeatSeries

open SourceCasimirClosure (energy)

theorem matrixEntry_norm_le_one (m : ℕ) (i j : Fin (m + 1)) :
    ‖matrixEntry m i j‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro U
  change ‖inner ℂ (sourceBasis m i) (unitaryAction m U (sourceBasis m j))‖ ≤ 1
  calc
    _ ≤ ‖sourceBasis m i‖ * ‖unitaryAction m U (sourceBasis m j)‖ :=
      norm_inner_le_norm _ _
    _ = 1 := by simp only [norm_map, OrthonormalBasis.norm_eq_one, one_mul]

/-- The conjugated character uses the original Haar-orthonormal source basis. -/
def conjugateCharacter (m : ℕ) : C(SU2, ℂ) :=
  ∑ i : Fin (m + 1), star (matrixEntry m i i)

theorem conjugateCharacter_norm_le (m : ℕ) :
    ‖conjugateCharacter m‖ ≤ (m : ℝ) + 1 := by
  calc
    _ ≤ ∑ i : Fin (m + 1), ‖star (matrixEntry m i i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_star]
      exact matrixEntry_norm_le_one m i i
    _ = (m : ℝ) + 1 := by simp

def heatWeight (t : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) * Real.exp (-t * energy m)

theorem heatWeight_nonneg (t : ℝ) (m : ℕ) : 0 ≤ heatWeight t m := by
  unfold heatWeight
  positivity

def heatTerm (t : ℝ) (m : ℕ) : C(SU2, ℂ) :=
  (heatWeight t m : ℂ) • conjugateCharacter m

/-- This bound retains the full multiplicity `(m+1)^2`. -/
def majorant (t : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ) + 1) ^ 2 * Real.exp (-t * energy m)

theorem heatTerm_norm_le (t : ℝ) (m : ℕ) : ‖heatTerm t m‖ ≤ majorant t m := by
  rw [heatTerm, norm_smul, Complex.norm_of_nonneg (heatWeight_nonneg t m)]
  calc
    heatWeight t m * ‖conjugateCharacter m‖ ≤ heatWeight t m * ((m : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (conjugateCharacter_norm_le m) (heatWeight_nonneg t m)
    _ = majorant t m := by unfold heatWeight majorant; ring

theorem energy_ge_degree (m : ℕ) : (m : ℝ) ≤ energy m := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold energy
  nlinarith [sq_nonneg (m : ℝ)]

/-- Actual summability is proved, rather than supplied as a heat-kernel
regularity assumption. The comparison series has degree two. -/
theorem majorant_summable {t : ℝ} (ht : 0 < t) : Summable (majorant t) := by
  have hpoly := ((Real.summable_pow_mul_exp_neg_nat_mul 2 ht).add
    ((Real.summable_pow_mul_exp_neg_nat_mul 1 ht).mul_left 2)).add
      (Real.summable_pow_mul_exp_neg_nat_mul 0 ht)
  have hgeom : Summable (fun m : ℕ =>
      ((m : ℝ) + 1) ^ 2 * Real.exp (-t * (m : ℝ))) :=
    hpoly.congr (fun m => by ring)
  apply hgeom.of_nonneg_of_le (fun m => by unfold majorant; positivity)
  intro m
  unfold majorant
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (energy_ge_degree m) (neg_nonpos.mpr ht.le)

theorem heatTerm_norm_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun m => ‖heatTerm t m‖) :=
  (majorant_summable ht).of_nonneg_of_le (fun _ => norm_nonneg _) (heatTerm_norm_le t)

theorem heatTerm_summable {t : ℝ} (ht : 0 < t) : Summable (heatTerm t) :=
  (majorant_summable ht).of_norm_bounded (heatTerm_norm_le t)

/-- All convergence and integral statements below require `0 < t`.
The definition itself uses the ordinary total `tsum` convention. -/
def heatKernel (t : ℝ) : C(SU2, ℂ) := ∑' m : ℕ, heatTerm t m

theorem heatKernel_hasSum {t : ℝ} (ht : 0 < t) : HasSum (heatTerm t) (heatKernel t) :=
  (heatTerm_summable ht).hasSum

theorem heatKernel_apply {t : ℝ} (ht : 0 < t) (U : SU2) :
    heatKernel t U = ∑' m : ℕ,
      (heatWeight t m : ℂ) * ∑ i : Fin (m + 1), conj (matrixEntry m i i U) := by
  have hs := (ContinuousMap.evalCLM ℂ U).hasSum (heatKernel_hasSum ht)
  simpa only [heatTerm, conjugateCharacter, ContinuousMap.evalCLM_apply,
    ContinuousMap.smul_apply, ContinuousMap.sum_apply, ContinuousMap.star_apply,
    Complex.star_def, smul_eq_mul] using hs.tsum_eq.symm

/-- Convergence in `C(SU2,ℂ)` is uniform convergence on the full group. -/
theorem heatKernel_uniform {t : ℝ} (ht : 0 < t) :
    TendstoUniformly
      (fun N : ℕ => fun U : SU2 => ∑ m ∈ Finset.range N, heatTerm t m U)
      (heatKernel t) atTop := by
  have hc := (heatKernel_hasSum ht).tendsto_sum_nat
  have hb := ((ContinuousMap.isometryEquivBoundedOfCompact SU2 ℂ).continuous.tendsto
    (heatKernel t)).comp hc
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hb
  change TendstoUniformly
    (fun N : ℕ => fun U : SU2 => (∑ m ∈ Finset.range N, heatTerm t m) U)
    (heatKernel t) atTop at hu
  simpa only [ContinuousMap.sum_apply] using hu

/-- A bounded linear functional keeps interchange of the uniformly
convergent series and its Haar moments within the same function space. -/
def haarPair (f : C(SU2, ℂ)) : C(SU2, ℂ) →L[ℂ] ℂ :=
  (expectation (⟨sourceHaar, inferInstance⟩ : ProbabilityMeasure SU2)).comp
    ((ContinuousLinearMap.mul ℂ C(SU2, ℂ)).flip f)

@[simp] theorem haarPair_apply (f k : C(SU2, ℂ)) :
    haarPair f k = ∫ U, k U * f U ∂sourceHaar := rfl

theorem haarPair_starEntry_same (m : ℕ) (i j k l : Fin (m + 1)) :
    haarPair (matrixEntry m k l) (star (matrixEntry m i j)) =
      if i = k ∧ j = l then (((m + 1 : ℕ) : ℂ))⁻¹ else 0 := by
  change (∫ U, conj (matrixEntry m i j U) * matrixEntry m k l U ∂sourceHaar) = _
  exact matrixEntry_integral_same m i j k l

theorem haarPair_starEntry_of_ne {m n : ℕ} (hmn : m ≠ n)
    (i j : Fin (m + 1)) (k l : Fin (n + 1)) :
    haarPair (matrixEntry n k l) (star (matrixEntry m i j)) = 0 := by
  change (∫ U, conj (matrixEntry m i j U) * matrixEntry n k l U ∂sourceHaar) = 0
  exact matrixEntry_integral_of_ne hmn i j k l

theorem haarPair_heatTerm_same (t : ℝ) (n : ℕ) (i j : Fin (n + 1)) :
    haarPair (matrixEntry n i j) (heatTerm t n) = heatCoefficient t ⟨n, i, j⟩ := by
  classical
  simp only [heatTerm, conjugateCharacter, map_smul, map_sum,
    haarPair_starEntry_same, smul_eq_mul]
  have hs : (∑ l : Fin (n + 1),
      if l = i ∧ l = j then (((n + 1 : ℕ) : ℂ))⁻¹ else 0) =
      if i = j then (((n + 1 : ℕ) : ℂ))⁻¹ else 0 := by
    by_cases hij : i = j
    · subst j
      simp
    · have hn (l : Fin (n + 1)) : ¬ (l = i ∧ l = j) := by
        rintro ⟨hi, hj⟩
        exact hij (hi.symm.trans hj)
      simp [hij, hn]
  rw [hs]
  by_cases hij : i = j
  · rw [ite_eq_left hij]
    have hd : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    calc
      (heatWeight t n : ℂ) * (((n + 1 : ℕ) : ℂ))⁻¹ =
          (((n + 1 : ℕ) : ℂ) * (Real.exp (-t * energy n) : ℂ)) *
            (((n + 1 : ℕ) : ℂ))⁻¹ := by
        simp only [heatWeight, Complex.ofReal_mul, Complex.ofReal_add,
          Complex.ofReal_natCast, Complex.ofReal_one, Nat.cast_add, Nat.cast_one]
      _ = (Real.exp (-t * energy n) : ℂ) := by field_simp [hd]
      _ = heatCoefficient t ⟨n, i, j⟩ := by simp [heatCoefficient, energy, hij]
  · simp [hij, heatCoefficient]

theorem haarPair_heatTerm (t : ℝ) (m n : ℕ) (i j : Fin (n + 1)) :
    haarPair (matrixEntry n i j) (heatTerm t m) =
      if m = n then heatCoefficient t ⟨n, i, j⟩ else 0 := by
  classical
  by_cases hmn : m = n
  · subst m
    rw [ite_eq_left rfl]
    exact haarPair_heatTerm_same t n i j
  · simp only [heatTerm, conjugateCharacter, map_smul, map_sum,
      haarPair_starEntry_of_ne hmn, Finset.sum_const_zero, smul_zero, ite_eq_right hmn]

/-- These are the moments against every original source matrix entry. -/
theorem heatKernel_matrixEntry_integral (t : ℝ) (ht : 0 < t) (m : ℕ)
    (i j : Fin (m + 1)) :
    (∫ U, heatKernel t U * matrixEntry m i j U ∂sourceHaar) =
      heatCoefficient t ⟨m, i, j⟩ := by
  have hs := (haarPair (matrixEntry m i j)).hasSum (heatKernel_hasSum ht)
  have hs' : HasSum (fun n : ℕ =>
      if n = m then heatCoefficient t ⟨m, i, j⟩ else 0)
      (haarPair (matrixEntry m i j) (heatKernel t)) := by
    simpa only [haarPair_heatTerm] using hs
  exact hs'.unique (hasSum_ite_eq m (heatCoefficient t ⟨m, i, j⟩))

/-- The degree-zero coefficient is actually the constant one function. -/
theorem matrixEntry_zero : matrixEntry 0 0 0 = 1 := by
  ext U
  change inner ℂ (sourceBasis 0 0) (unitaryAction 0 U (sourceBasis 0 0)) = 1
  have hzero (v : HilbertCarrier 0) : unitaryAction 0 U v = v := by
    obtain ⟨q, rfl⟩ := (carrierEquiv 0).surjective v
    rw [unitaryAction_apply_carrier, source_degreeZero]
  rw [hzero, OrthonormalBasis.inner_eq_ite, ite_eq_left rfl]

theorem heatKernel_integral (t : ℝ) (ht : 0 < t) :
    (∫ U, heatKernel t U ∂sourceHaar) = 1 := by
  simpa [matrixEntry_zero, heatCoefficient] using
    heatKernel_matrixEntry_integral t ht 0 0 0

end GeneratedFoundations.Geometry.SourceHeatSeries
