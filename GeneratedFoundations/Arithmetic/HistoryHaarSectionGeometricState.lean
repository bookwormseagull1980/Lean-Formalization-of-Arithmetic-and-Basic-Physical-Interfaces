module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricVariation
public import GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianState
public import GeneratedFoundations.Operations.FinitePrecisionPath

/-!
# Geometric response of the original finite spatial Gaussian state

The base metric varies while the already generated history fibre stays
fixed. The full nonlinear action is differentiated first. On its vacuum
Hessian, connection precision scales as `1/c`; scalar precision is
`c*a+c^3*C_F`. Both real quadratures of every original complex mode are
retained. The partition is relative to the unit-geometry law, so changing
the normalization does not remove its geometric response.

This is the spatial, fixed-support quadratic state. It neither replaces
the interacting state of the cubic--quartic action nor transports the time
frequency or the moving cutoff. Its exact response is an input to joint
endpoint selection, not a claim that a fixed window selects itself.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricState

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionAction (Sections gradient sectionField)
open HistoryHaarSectionGeometricVariation
open HistoryHaarSectionJointHessian (Index)
open HistoryHaarSectionWindow (kinetic restoring)
open HistoryHaarSectionGaussianState (RealIndex Space mode)

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

/-- The vacuum quadratic coefficient of the same geometric action. -/
def quadratic (N : ℕ) (A : Coefficients N) (ψ : Sections N) (c : ℝ) : ℝ :=
  ‖HistoryHaarMatrixCurvature.differentiated N A‖ ^ 2 / c +
    c * ‖gradient N ψ‖ ^ 2 +
      c ^ 3 * HistoryDefiningResponse.coefficient N * ‖sectionField N ψ‖ ^ 2

def cubic (N : ℕ) (A : Coefficients N) (ψ : Sections N) (c : ℝ) : ℝ :=
  HistoryHaarCoupledAction.cubic N A / c + c * HistoryHaarSectionAction.sectionCurrent N A ψ

def quartic (N : ℕ) (A : Coefficients N) (ψ : Sections N) (c : ℝ) : ℝ :=
  ‖HistoryHaarMatrixCurvature.vertex N A‖ ^ 2 / (2 * c) +
    c * ‖HistoryHaarSectionAction.connectionDerivative N A ψ‖ ^ 2 / 2

/-- No term of the nonlinear action is dropped to obtain the Hessian. -/
theorem action_ray (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    {c : ℝ} (hc : 0 < c) (t : ℝ) :
    geometricAction N ((t : ℂ) • A) ((t : ℂ) • ψ) c =
      t ^ 2 * quadratic N A ψ c / 2 + t ^ 3 * cubic N A ψ c +
        t ^ 4 * quartic N A ψ c := by
  rw [geometricAction_original_functionals N _ _ hc.ne',
    HistoryHaarSectionAction.action_ray, HistoryHaarMatrixCurvature.action_ray]
  simp only [restoringEnergy, map_smul, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  unfold quadratic cubic quartic HistoryHaarSectionAction.quadratic
    HistoryHaarSectionAction.cubic HistoryHaarSectionAction.quartic
    HistoryHaarCoupledAction.cubic
  ring

theorem action_firstDeriv (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    {c : ℝ} (hc : 0 < c) (t : ℝ) :
    HasDerivAt (fun s : ℝ => geometricAction N ((s : ℂ) • A) ((s : ℂ) • ψ) c)
      (t * quadratic N A ψ c + 3 * t ^ 2 * cubic N A ψ c +
        4 * t ^ 3 * quartic N A ψ c) t := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt 0 0
    (quadratic N A ψ c / 2) (cubic N A ψ c) (quartic N A ψ c) t using 1
  · funext s
    rw [action_ray N A ψ hc]
    ring
  · ring

theorem action_secondDeriv (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => geometricAction N ((s : ℂ) • A) ((s : ℂ) • ψ) c) t)
      (quadratic N A ψ c) 0 := by
  have he : (fun t : ℝ => deriv
      (fun s : ℝ => geometricAction N ((s : ℂ) • A) ((s : ℂ) • ψ) c) t) =
      fun t => t * quadratic N A ψ c + 3 * t ^ 2 * cubic N A ψ c +
        4 * t ^ 3 * quartic N A ψ c :=
    funext fun t => (action_firstDeriv N A ψ hc t).deriv
  rw [he]
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt 0
    (quadratic N A ψ c) (3 * cubic N A ψ c) (4 * quartic N A ψ c) 0 0 using 1
  · funext t
    ring
  · simp

/-- The connection block is the original differentiated Hodge form. -/
theorem quadratic_connection (N : ℕ) (A : Coefficients N) (c : ℝ) :
    quadratic N A 0 c =
      (∑ i : HistoryHaarMatrixCurvature.Index N × HistoryHaarMatrixCurvature.Index N,
        (inner ℂ (A i.1 i.2 : Geometry.SourceOneFormClosedHodge.coclosedField)
          (Geometry.SourceOneFormHodgeLaplacian.finiteHodge (A i.1 i.2))).re) / c := by
  simp only [quadratic, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero]
  rw [HistoryHaarMatrixCurvature.hessian_differential]

def precision (N : ℕ) (c : ℝ) : Index N → ℝ :=
  Sum.elim (fun i => HistoryHaarClosedHessian.eigenvalue N i / c)
    (fun i => c * Geometry.SourceCasimirClosure.energy i.2.val.1 +
      c ^ 3 * HistoryDefiningResponse.coefficient N)

theorem quadratic_basisSection (N : ℕ) (i : HistoryHaarMatrixCurvature.Index N)
    (a : Geometry.SourceQuotientHilbert.EvenIndex) (c : ℝ) :
    quadratic N 0 (HistoryHaarSectionAction.basisSection N i a) c =
      precision N c (.inr (i, a)) := by
  have h := HistoryHaarSectionAction.quadratic_basisSection N i a
  simp only [HistoryHaarSectionAction.quadratic, map_zero, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add,
    HistoryHaarSectionAction.basisSection_norm, one_pow, mul_one] at h
  have hg : ‖gradient N (HistoryHaarSectionAction.basisSection N i a)‖ ^ 2 =
      Geometry.SourceCasimirClosure.energy a.val.1 := by linarith
  simp only [quadratic, precision, Sum.elim_inr, map_zero, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_div, zero_add,
    HistoryHaarSectionAction.basisSection_norm, one_pow, mul_one, hg]

theorem precision_pos (N : ℕ) {c : ℝ} (hc : 0 < c) (i : Index N) :
    0 < precision N c i := by
  cases i with
  | inl i => exact div_pos (HistoryHaarClosedHessian.eigenvalue_pos N i) hc
  | inr i =>
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hc.le (Geometry.SourceCasimirClosure.energy_nonneg _))
      (mul_pos (pow_pos hc _) (HistoryDefiningResponse.coefficient_pos N))

@[simp] theorem precision_one (N : ℕ) (i : Index N) :
    precision N 1 i = HistoryHaarSectionJointHessian.eigenvalue N i := by
  cases i <;> simp [precision, HistoryHaarSectionJointHessian.eigenvalue,
    HistoryHaarSectionHessian.eigenvalue]

def firstPrecision (N : ℕ) (c : ℝ) : Index N → ℝ :=
  Sum.elim (fun i => -HistoryHaarClosedHessian.eigenvalue N i / c ^ 2)
    (fun i => Geometry.SourceCasimirClosure.energy i.2.val.1 +
      3 * c ^ 2 * HistoryDefiningResponse.coefficient N)

def secondPrecision (N : ℕ) (c : ℝ) : Index N → ℝ :=
  Sum.elim (fun i => 2 * HistoryHaarClosedHessian.eigenvalue N i / c ^ 3)
    (fun _ => 6 * c * HistoryDefiningResponse.coefficient N)

theorem precision_hasDerivAt (N : ℕ) {c : ℝ} (hc : 0 < c) (i : Index N) :
    HasDerivAt (fun r => precision N r i) (firstPrecision N c i) c := by
  cases i with
  | inl i =>
    have hd := (hasDerivAt_const c (HistoryHaarClosedHessian.eigenvalue N i)).div
      (hasDerivAt_id c) hc.ne'
    have he : firstPrecision N c (.inl i) =
        (0 * c - HistoryHaarClosedHessian.eigenvalue N i * 1) / c ^ 2 := by
      simp [firstPrecision]
    rw [he]
    exact hd
  | inr i =>
    convert ((hasDerivAt_id c).mul_const (Geometry.SourceCasimirClosure.energy i.2.val.1)).add
      (((hasDerivAt_id c).pow 3).mul_const (HistoryDefiningResponse.coefficient N)) using 1
    · rfl
    · simp only [firstPrecision, Sum.elim_inr, id_eq]
      ring

theorem firstPrecision_hasDerivAt (N : ℕ) {c : ℝ} (hc : 0 < c) (i : Index N) :
    HasDerivAt (fun r => firstPrecision N r i) (secondPrecision N c i) c := by
  cases i with
  | inl i =>
    have hd := (hasDerivAt_const c (-HistoryHaarClosedHessian.eigenvalue N i)).div
      ((hasDerivAt_id c).pow 2) (pow_ne_zero 2 hc.ne')
    have he : (0 * c ^ 2 - -HistoryHaarClosedHessian.eigenvalue N i *
        (2 * c ^ (2 - 1) * 1)) / (c ^ 2) ^ 2 = secondPrecision N c (.inl i) := by
      simp only [secondPrecision, Sum.elim_inl]
      field_simp [hc.ne']
      ring
    exact hd.congr_deriv he
  | inr i =>
    have hd := (hasDerivAt_const c (Geometry.SourceCasimirClosure.energy i.2.val.1)).add
      (((hasDerivAt_id c).pow 2).const_mul (3 * HistoryDefiningResponse.coefficient N))
    convert! hd using 1
    · funext r
      simp only [firstPrecision, Sum.elim_inr, Pi.add_apply,
        Pi.pow_apply, id_eq]
      ring
    · simp only [secondPrecision, Sum.elim_inr, id_eq]
      ring

def realPrecision (N : ℕ) (B c : ℝ) (i : RealIndex N B 0) : ℝ :=
  precision N c i.val.1

def firstRealPrecision (N : ℕ) (B c : ℝ) (i : RealIndex N B 0) : ℝ :=
  firstPrecision N c i.val.1

def secondRealPrecision (N : ℕ) (B c : ℝ) (i : RealIndex N B 0) : ℝ :=
  secondPrecision N c i.val.1

def law (N : ℕ) (B c : ℝ) : Measure (Space N B 0) :=
  Operations.FinitePrecisionGaussian.law (realPrecision N B c)

theorem law_existsUnique (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃! ν : Measure (Space N B 0), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      Operations.FinitePrecisionGaussian.precisionMatrix (realPrecision N B c) *
        Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  Operations.FinitePrecisionPath.law_existsUnique (p := realPrecision N B)
    (c := c) (fun i => precision_pos N hc i.val.1)

@[simp] theorem law_one (N : ℕ) (B : ℝ) :
    law N B 1 = HistoryHaarSectionGaussianState.law N B 0 := by
  have hp : realPrecision N B 1 = HistoryHaarSectionGaussianState.realPrecision N B 0 := by
    funext i
    simp [realPrecision, HistoryHaarSectionGaussianState.realPrecision,
      HistoryHaarSectionComparison.precision]
  change Operations.FinitePrecisionGaussian.law (realPrecision N B 1) =
    Operations.FinitePrecisionGaussian.law (HistoryHaarSectionGaussianState.realPrecision N B 0)
  rw [hp]

def partition (N : ℕ) (B c : ℝ) : ℝ :=
  Operations.FinitePrecisionPath.partition (realPrecision N B) 1 c

def freeEnergy (N : ℕ) (B c : ℝ) : ℝ :=
  -Operations.FinitePrecisionPath.logPartition (realPrecision N B) 1 c

def force (N : ℕ) (B c : ℝ) : ℝ :=
  Operations.FinitePrecisionPath.force (realPrecision N B) (firstRealPrecision N B) c

def curvature (N : ℕ) (B c : ℝ) : ℝ :=
  Operations.FinitePrecisionPath.curvature (realPrecision N B)
    (firstRealPrecision N B) (secondRealPrecision N B) c

theorem partition_eq_exp (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    partition N B c = Real.exp (-freeEnergy N B c) := by
  exact (Operations.FinitePrecisionPath.partition_eq_exp
    (p := realPrecision N B) (r := 1) (c := c)
    (fun i => precision_pos N (by norm_num) i.val.1)
    (fun i => precision_pos N hc i.val.1)).trans (by simp [freeEnergy])

theorem freeEnergy_hasDerivAt (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (freeEnergy N B) (force N B c) c := by
  have hd := (Operations.FinitePrecisionPath.logPartition_hasDerivAt
    (p := realPrecision N B) (v := firstRealPrecision N B)
    (r := 1) (c := c) (fun i => precision_pos N hc i.val.1)
    (fun i => precision_hasDerivAt N hc i.val.1)).neg
  convert! hd using 1
  simp only [force, neg_neg]

theorem force_hasDerivAt (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (force N B) (curvature N B c) c :=
  Operations.FinitePrecisionPath.force_hasDerivAt
    (p := realPrecision N B) (v := firstRealPrecision N B)
    (a := secondRealPrecision N B) (c := c)
    (fun i => precision_pos N hc i.val.1)
    (fun i => precision_hasDerivAt N hc i.val.1)
    (fun i => firstPrecision_hasDerivAt N hc i.val.1)

theorem curvature_eq_mean_sub_variance (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    curvature N B c =
      (∫ x, Operations.FinitePrecisionGaussian.score (secondRealPrecision N B c) x
        ∂law N B c) -
      Var[Operations.FinitePrecisionGaussian.score (firstRealPrecision N B c); law N B c] :=
  Operations.FinitePrecisionPath.curvature_eq_mean_sub_variance
    (p := realPrecision N B) (v := firstRealPrecision N B)
    (a := secondRealPrecision N B) (c := c)
    (fun i => precision_pos N hc i.val.1)

/-- Both quadratures have been summed. The equation is evaluated on every
original mode, not on a replacement count or a selected scalar row. -/
theorem logarithmic_force (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    c * force N B c =
      ∑ i : HistoryHaarSectionCovariance.WindowIndex N B 0,
        if i.val.isRight = true then
          1 + 2 * c ^ 2 * restoring N i.val /
            (kinetic N i.val + c ^ 2 * restoring N i.val)
        else -1 := by
  unfold force Operations.FinitePrecisionPath.force
  rw [HistoryHaarSectionGaussianState.sum_realIndex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [realPrecision, firstRealPrecision, HistoryHaarSectionGaussianState.slot]
  cases hi : i.val with
  | inl j =>
    simp only [precision, firstPrecision, Sum.elim_inl,
      Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte]
    field_simp [hc.ne', (HistoryHaarClosedHessian.eigenvalue_pos N j).ne']
    ring
  | inr j =>
    have ha := Geometry.SourceCasimirClosure.energy_nonneg j.2.val.1
    have hv := HistoryDefiningResponse.coefficient_pos N
    have hp : Geometry.SourceCasimirClosure.energy j.2.val.1 +
        c ^ 2 * HistoryDefiningResponse.coefficient N ≠ 0 := by positivity
    simp only [precision, firstPrecision, kinetic, restoring, Sum.elim_inr,
      Sum.isRight_inr, ↓reduceIte]
    field_simp [hc.ne', hp]
    ring

/-- A complete original-mode formula, after combining the two real
coordinates of every complex eigenline. -/
theorem freeEnergy_eq_modes (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    freeEnergy N B c = ∑ i ∈ HistoryHaarSectionWindow.support N B,
      Real.log (precision N c i / HistoryHaarSectionJointHessian.eigenvalue N i) := by
  rw [freeEnergy, Operations.FinitePrecisionPath.negative_logPartition_eq
    (fun i => precision_pos N (by norm_num) i.val.1)
    (fun i => precision_pos N hc i.val.1), HistoryHaarSectionGaussianState.sum_realIndex]
  have hs : HistoryHaarSectionCovariance.frequencySupport N B 0 =
      HistoryHaarSectionWindow.support N B := by
    simp [HistoryHaarSectionCovariance.frequencySupport]
  simp only [Fin.sum_univ_two, realPrecision, HistoryHaarSectionGaussianState.slot,
    precision_one, add_halves]
  rw [Finset.univ_eq_attach, Finset.sum_attach
    (HistoryHaarSectionCovariance.frequencySupport N B 0)
    (fun i => Real.log (precision N c i / HistoryHaarSectionJointHessian.eigenvalue N i)), hs]

/-- A fixed-support spatial determinant cannot distinguish cutoffs with
identical support. Frequency extensions and their endpoint terms must be
retained in any subsequent joint-window selection. -/
theorem freeEnergy_same_support (N : ℕ) {B C : ℝ}
    (hs : HistoryHaarSectionWindow.support N B = HistoryHaarSectionWindow.support N C)
    {c : ℝ} (hc : 0 < c) : freeEnergy N B c = freeEnergy N C c := by
  rw [freeEnergy_eq_modes N B hc, freeEnergy_eq_modes N C hc, hs]

theorem first_cell_equal_freeEnergy (N : ℕ) {B C : ℝ}
    (hBlo : 4 < B) (hBhi : B ≤ 8) (hClo : 4 < C) (hChi : C ≤ 8)
    {c : ℝ} (hc : 0 < c) : freeEnergy N B c = freeEnergy N C c := by
  apply freeEnergy_same_support N ?_ hc
  ext i
  exact (HistoryHaarSectionWindow.mem_support_first_plateau N hBlo hBhi i).trans
    (HistoryHaarSectionWindow.mem_support_first_plateau N hClo hChi i).symm

theorem second_cell_equal_freeEnergy (N : ℕ) {B C : ℝ}
    (hBlo : 8 < B) (hBhi : B ≤ 16) (hClo : 8 < C) (hChi : C ≤ 16)
    {c : ℝ} (hc : 0 < c) : freeEnergy N B c = freeEnergy N C c :=
  freeEnergy_same_support N
    (HistoryHaarSectionWindow.second_plateau_support_constant N hBlo hBhi hClo hChi) hc

structure Conclusions : Prop where
  original_geometric_hessian : ∀ N A ψ c, 0 < c →
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => geometricAction N ((s : ℂ) • A) ((s : ℂ) • ψ) c) t)
      (quadratic N A ψ c) 0
  all_gaussian_competitors : ∀ N B c, 0 < c →
    ∃! ν : Measure (Space N B 0), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      Operations.FinitePrecisionGaussian.precisionMatrix (realPrecision N B c) *
        Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1
  actual_partition : ∀ N B c, 0 < c → partition N B c = Real.exp (-freeEnergy N B c)
  actual_first_variation : ∀ N B c, 0 < c →
    HasDerivAt (freeEnergy N B) (force N B c) c
  actual_second_variation : ∀ N B c, 0 < c →
    HasDerivAt (force N B) (curvature N B c) c
  complete_geometric_response : ∀ N B c, 0 < c →
    curvature N B c =
      (∫ x, Operations.FinitePrecisionGaussian.score (secondRealPrecision N B c) x
        ∂law N B c) -
      Var[Operations.FinitePrecisionGaussian.score (firstRealPrecision N B c); law N B c]
  complete_scale_equation : ∀ N B c, 0 < c →
    c * force N B c =
      ∑ i : HistoryHaarSectionCovariance.WindowIndex N B 0,
        if i.val.isRight = true then
          1 + 2 * c ^ 2 * restoring N i.val /
            (kinetic N i.val + c ^ 2 * restoring N i.val)
        else -1
  same_support_comparison : ∀ N B C,
    HistoryHaarSectionWindow.support N B = HistoryHaarSectionWindow.support N C →
    ∀ c, 0 < c → freeEnergy N B c = freeEnergy N C c

theorem generated : Conclusions where
  original_geometric_hessian := fun N A ψ _ hc => action_secondDeriv N A ψ hc
  all_gaussian_competitors := fun N B _ hc => law_existsUnique N B hc
  actual_partition := fun N B _ hc => partition_eq_exp N B hc
  actual_first_variation := fun N B _ hc => freeEnergy_hasDerivAt N B hc
  actual_second_variation := fun N B _ hc => force_hasDerivAt N B hc
  complete_geometric_response := fun N B _ hc => curvature_eq_mean_sub_variance N B hc
  complete_scale_equation := fun N B _ hc => logarithmic_force N B hc
  same_support_comparison := fun N _ _ hs _ hc => freeEnergy_same_support N hs hc

end GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricState
