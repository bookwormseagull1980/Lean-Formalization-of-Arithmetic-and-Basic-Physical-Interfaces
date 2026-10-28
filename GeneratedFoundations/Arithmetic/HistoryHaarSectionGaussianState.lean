module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionCovariance
public import GeneratedFoundations.Operations.FinitePrecisionGaussian

/-!
# The realified joint Gaussian state of the complex history field

The original joint Hessian acts on a complex Hilbert space. Each retained
complex coefficient has two real coordinates. Both are kept with the
original kinetic support and precision. Recombination preserves its
quadratic action. Among all centred Gaussian measures on the realified
space, the full precision equation determines one law. Competitors may
have arbitrary cross-sector and cross-quadrature covariances.

Nested windows give exact marginal laws. Gaussian independence is deduced,
not imposed on competitors. The full heat-weighted quadratic score has
variance equal to the original response kernel sum. Keeping only one real
coordinate per complex eigenline would give half this variance.

This constructs the quadratic state at fixed frequency and cutoff. The
original action also has cubic and quartic terms. Its interacting measure
and selection of the cutoff are not defined by this quadratic construction.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianState

open HistoryHaarSectionJointHessian (Index)
open HistoryHaarSectionWindow (kernel)
open HistoryHaarSectionComparison (precision precision_pos kineticPrecision weight)
open HistoryHaarSectionCovariance (WindowIndex frequencySupport)

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def realSupport (N : ℕ) (B u : ℝ) : Finset (Index N × Fin 2) :=
  (frequencySupport N B u).product Finset.univ

abbrev RealIndex (N : ℕ) (B u : ℝ) := ↥(realSupport N B u)
abbrev Space (N : ℕ) (B u : ℝ) := EuclideanSpace ℝ (RealIndex N B u)
abbrev ComplexSpace (N : ℕ) (B u : ℝ) := EuclideanSpace ℂ (WindowIndex N B u)

def slot (N : ℕ) (B u : ℝ) (i : WindowIndex N B u) (q : Fin 2) : RealIndex N B u :=
  ⟨(i.val, q), Finset.mem_product.mpr ⟨i.property, Finset.mem_univ q⟩⟩

def mode (N : ℕ) (B u : ℝ) (i : RealIndex N B u) : WindowIndex N B u :=
  ⟨i.val.1, (Finset.mem_product.mp i.property).1⟩

def slotEquiv (N : ℕ) (B u : ℝ) : RealIndex N B u ≃ WindowIndex N B u × Fin 2 where
  toFun i := (mode N B u i, i.val.2)
  invFun i := slot N B u i.1 i.2
  left_inv i := by ext <;> rfl
  right_inv i := by rfl

theorem sum_realIndex (N : ℕ) (B u : ℝ) (f : RealIndex N B u → ℝ) :
    ∑ i, f i = ∑ i : WindowIndex N B u, ∑ q : Fin 2, f (slot N B u i q) := by
  calc
    ∑ i, f i = ∑ j : WindowIndex N B u × Fin 2, f (slot N B u j.1 j.2) :=
      ((slotEquiv N B u).symm.sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

def complexCoefficients (N : ℕ) (B u : ℝ) (x : Space N B u) : ComplexSpace N B u :=
  WithLp.toLp 2 fun i => (x (slot N B u i 0) : ℂ) + (x (slot N B u i 1) : ℂ) * Complex.I

def realCoefficients (N : ℕ) (B u : ℝ) (z : ComplexSpace N B u) : Space N B u :=
  WithLp.toLp 2 fun i =>
    if i.val.2 = 0 then (z (mode N B u i)).re else (z (mode N B u i)).im

@[simp] theorem realCoefficients_slot_zero (N : ℕ) (B u : ℝ) (z : ComplexSpace N B u)
    (i : WindowIndex N B u) :
    realCoefficients N B u z (slot N B u i 0) = (z i).re := by
  simp [realCoefficients, mode, slot]

@[simp] theorem realCoefficients_slot_one (N : ℕ) (B u : ℝ) (z : ComplexSpace N B u)
    (i : WindowIndex N B u) :
    realCoefficients N B u z (slot N B u i 1) = (z i).im := by
  simp [realCoefficients, mode, slot]

@[simp] theorem complex_realCoefficients (N : ℕ) (B u : ℝ) (z : ComplexSpace N B u) :
    complexCoefficients N B u (realCoefficients N B u z) = z := by
  ext i
  simp only [complexCoefficients, WithLp.ofLp_toLp, realCoefficients_slot_zero,
    realCoefficients_slot_one]
  exact Complex.re_add_im (z i)

@[simp] theorem real_complexCoefficients (N : ℕ) (B u : ℝ) (x : Space N B u) :
    realCoefficients N B u (complexCoefficients N B u x) = x := by
  ext i
  obtain ⟨⟨j, q⟩, rfl⟩ := (slotEquiv N B u).symm.surjective i
  fin_cases q <;> simp [realCoefficients, complexCoefficients, mode, slot, slotEquiv]

theorem complex_coefficient_norm_sq (N : ℕ) (B u : ℝ) (x : Space N B u)
    (i : WindowIndex N B u) :
    ‖complexCoefficients N B u x i‖ ^ 2 =
      x (slot N B u i 0) ^ 2 + x (slot N B u i 1) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [complexCoefficients, Complex.normSq_apply, pow_two]

def realPrecision (N : ℕ) (B u : ℝ) (i : RealIndex N B u) : ℝ :=
  precision N i.val.1 u

theorem realPrecision_pos (N : ℕ) (B u : ℝ) (i : RealIndex N B u) :
    0 < realPrecision N B u i := precision_pos N i.val.1 u

def quadraticAction (N : ℕ) (B u : ℝ) (x : Space N B u) : ℝ :=
  ∑ i, Operations.GaussianPrecisionMoments.score (realPrecision N B u i) (x i)

def complexQuadraticAction (N : ℕ) (B u : ℝ) (z : ComplexSpace N B u) : ℝ :=
  ∑ i, (precision N i.val u / 2) * ‖z i‖ ^ 2

/-- Realification preserves the original complex quadratic form. -/
theorem quadraticAction_eq_complex (N : ℕ) (B u : ℝ) (x : Space N B u) :
    quadraticAction N B u x = complexQuadraticAction N B u (complexCoefficients N B u x) := by
  rw [quadraticAction, sum_realIndex]
  unfold complexQuadraticAction
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two, complex_coefficient_norm_sq]
  simp only [Operations.GaussianPrecisionMoments.score, realPrecision, slot]
  ring

def law (N : ℕ) (B u : ℝ) : Measure (Space N B u) :=
  Operations.FinitePrecisionGaussian.law (realPrecision N B u)

instance (N : ℕ) (B u : ℝ) : IsGaussian (law N B u) := by unfold law; infer_instance
instance (N : ℕ) (B u : ℝ) : IsProbabilityMeasure (law N B u) := inferInstance

@[simp] theorem mean_zero (N : ℕ) (B u : ℝ) : (∫ x, x ∂law N B u) = 0 :=
  Operations.FinitePrecisionGaussian.mean_zero _

theorem covariance_eq (N : ℕ) (B u : ℝ) :
    Operations.FinitePrecisionGaussian.coordinateCovariance (law N B u) =
      Operations.FinitePrecisionGaussian.covarianceMatrix (realPrecision N B u) :=
  Operations.FinitePrecisionGaussian.coordinateCovariance_eq (realPrecision_pos N B u)

/-- The original per-mode inverse precision is one real-quadrature variance;
realification has exactly two such coordinates per complex eigenline. -/
theorem covariance_trace (N : ℕ) (B u : ℝ) :
    Matrix.trace (Operations.FinitePrecisionGaussian.coordinateCovariance (law N B u)) =
      2 * HistoryHaarSectionCovariance.totalVariance N B u := by
  rw [covariance_eq, Operations.FinitePrecisionGaussian.covarianceMatrix,
    Matrix.trace_diagonal, sum_realIndex, HistoryHaarSectionCovariance.totalVariance_eq]
  rw [← Finset.sum_attach (frequencySupport N B u) (fun i => (precision N i u)⁻¹),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [realPrecision, slot]
  ring

theorem law_unique (N : ℕ) (B u : ℝ) (ν : Measure (Space N B u)) [IsGaussian ν]
    (hmean : (∫ x, x ∂ν) = 0)
    (hprecision : Operations.FinitePrecisionGaussian.precisionMatrix (realPrecision N B u) *
      Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1) : ν = law N B u :=
  Operations.FinitePrecisionGaussian.law_unique (realPrecision_pos N B u) ν hmean hprecision

theorem law_existsUnique (N : ℕ) (B u : ℝ) :
    ∃! ν : Measure (Space N B u), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      Operations.FinitePrecisionGaussian.precisionMatrix (realPrecision N B u) *
        Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  Operations.FinitePrecisionGaussian.law_existsUnique (realPrecision_pos N B u)

theorem realSupport_mono (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u : ℝ) :
    realSupport N B u ⊆ realSupport N C u :=
  Finset.product_subset_product
    (HistoryHaarSectionWindow.support_mono N (sub_le_sub_right hBC _)) (fun _ h => h)

theorem covariance_restrict (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u : ℝ) :
    (Operations.FinitePrecisionGaussian.covarianceMatrix (realPrecision N C u)).submatrix
      (fun i : RealIndex N B u => ⟨i.val, realSupport_mono N hBC u i.property⟩)
      (fun i : RealIndex N B u => ⟨i.val, realSupport_mono N hBC u i.property⟩) =
      Operations.FinitePrecisionGaussian.covarianceMatrix (realPrecision N B u) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Operations.FinitePrecisionGaussian.covarianceMatrix, Matrix.submatrix, realPrecision]
  · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simp [Operations.FinitePrecisionGaussian.covarianceMatrix, Matrix.submatrix, hij, hval]

theorem window_marginal (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u : ℝ) :
    MeasurePreserving (EuclideanSpace.restrict₂ (realSupport_mono N hBC u))
      (law N C u) (law N B u) := by
  have hp := Operations.FinitePrecisionGaussian.covariance_posSemidef
    (realPrecision_pos N C u)
  have hm := measurePreserving_restrict₂_multivariateGaussian (μ := 0) hp
    (realSupport_mono N hBC u)
  change MeasurePreserving _ (multivariateGaussian 0 _) (multivariateGaussian 0 _)
  simpa only [map_zero, covariance_restrict N hBC u] using hm

def heatVertex (N : ℕ) (i : Index N) (u : ℝ) : ℝ :=
  Real.exp (-kineticPrecision N i u / 2) * kineticPrecision N i u

def heatScore (N : ℕ) (B u : ℝ) (x : Space N B u) : ℝ :=
  Operations.FinitePrecisionGaussian.score (fun i => heatVertex N i.val.1 u) x

/-- The Gaussian half-field filter on the original kinetic modes. -/
def heatTransform (N : ℕ) (B u : ℝ) (x : Space N B u) : Space N B u :=
  WithLp.toLp 2 fun i => Real.exp (-kineticPrecision N i.val.1 u / 4) * x i

def kineticAction (N : ℕ) (B u : ℝ) (x : Space N B u) : ℝ :=
  Operations.FinitePrecisionGaussian.score (fun i => kineticPrecision N i.val.1 u) x

/-- The response observable is the original kinetic quadratic action after
the Gaussian field filter, rather than a separately assigned covariance. -/
theorem heatScore_eq_transported_kineticAction (N : ℕ) (B u : ℝ) (x : Space N B u) :
    heatScore N B u x = kineticAction N B u (heatTransform N B u x) := by
  unfold heatScore kineticAction Operations.FinitePrecisionGaussian.score
  apply Finset.sum_congr rfl
  intro i _
  have he : Real.exp (-kineticPrecision N i.val.1 u / 4) ^ 2 =
      Real.exp (-kineticPrecision N i.val.1 u / 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [Operations.GaussianPrecisionMoments.score, heatTransform,
    WithLp.ofLp_toLp, mul_pow, he, heatVertex]
  ring

theorem heatScore_mean (N : ℕ) (B u : ℝ) :
    (∫ x, heatScore N B u x ∂law N B u) =
      ∑ i ∈ frequencySupport N B u, heatVertex N i u / precision N i u := by
  rw [show (∫ x, heatScore N B u x ∂law N B u) =
      ∑ i : RealIndex N B u, heatVertex N i.val.1 u / (2 * precision N i.val.1 u) from
    Operations.FinitePrecisionGaussian.score_mean (realPrecision_pos N B u) _, sum_realIndex]
  rw [← Finset.sum_attach (frequencySupport N B u) (fun i => heatVertex N i u / precision N i u)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [slot]
  ring

/-- Both quadratures are included before taking the full score variance. -/
theorem heatScore_variance (N : ℕ) (B u : ℝ) :
    Var[heatScore N B u; law N B u] =
      ∑ i ∈ frequencySupport N B u, kernel N i u := by
  rw [show Var[heatScore N B u; law N B u] =
      ∑ i : RealIndex N B u, (heatVertex N i.val.1 u) ^ 2 /
        (2 * (precision N i.val.1 u) ^ 2) from
    Operations.FinitePrecisionGaussian.score_variance (realPrecision_pos N B u) _, sum_realIndex]
  rw [← Finset.sum_attach (frequencySupport N B u) (fun i => kernel N i u)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [slot]
  have hw : Real.exp (-kineticPrecision N i.val u / 2) ^ 2 = weight N i.val u := by
    rw [pow_two, ← Real.exp_add]
    change Real.exp _ = Real.exp _
    congr 1
    ring
  simp only [heatVertex, mul_pow, hw]
  have hp := (precision_pos N i.val u).ne'
  unfold kernel weight kineticPrecision precision
  dsimp [precision] at hp
  field_simp
  ring

structure Conclusions : Prop where
  unique_realified_gaussian : ∀ N B u,
    ∃! ν : Measure (Space N B u), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      Operations.FinitePrecisionGaussian.precisionMatrix (realPrecision N B u) *
        Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1
  original_complex_action : ∀ N B u (x : Space N B u),
    quadraticAction N B u x = complexQuadraticAction N B u (complexCoefficients N B u x)
  compatible_window_laws : ∀ N B C u (hBC : B ≤ C),
    MeasurePreserving (EuclideanSpace.restrict₂ (realSupport_mono N hBC u))
      (law N C u) (law N B u)
  full_quadratic_fluctuation : ∀ N B u,
    Var[heatScore N B u; law N B u] =
      ∑ i ∈ frequencySupport N B u, kernel N i u
  gaussian_kinetic_origin : ∀ N B u (x : Space N B u),
    heatScore N B u x = kineticAction N B u (heatTransform N B u x)

theorem generated : Conclusions where
  unique_realified_gaussian := law_existsUnique
  original_complex_action := quadraticAction_eq_complex
  compatible_window_laws := fun N _ _ u hBC => window_marginal N hBC u
  full_quadratic_fluctuation := heatScore_variance
  gaussian_kinetic_origin := heatScore_eq_transported_kineticAction

end GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianState
