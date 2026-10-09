module

public import GeneratedFoundations.Operations.PreparedTraceForm
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The Hessian of the prepared logarithmic trace response

The matrix exponential defines the partition function on the real vector space
of complex matrices. Its convergent power series determines the second
Fréchet derivative at zero. Symmetry and polarization give the mixed terms,
and the logarithm chain rule identifies the Hessian with the prepared trace
form. Restricting the two directions to Hermitian matrices recovers the
prepared response used in the source construction.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology Matrix.Norms.Operator ContDiff

namespace GeneratedFoundations.Operations.PreparedTraceDifferentiation

open PreparedTraceForm

private theorem hasFDerivAt_smul_dual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E → ℝ} {c' : E →L[ℝ] ℝ}
    {f : E → E →L[ℝ] ℝ} {f' : E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => c y • f y) (c x • f' + c'.smulRight (f x)) x := by
  exact hc.smul hf

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Normalized real trace as a continuous real linear functional. -/
def normalizedTrace : Mat ι →L[ℝ] ℝ :=
  (Fintype.card ι : ℝ)⁻¹ • (realTrace ι).toContinuousLinearMap

omit [DecidableEq ι] [Nonempty ι] in
@[simp] theorem normalizedTrace_apply (K : Mat ι) :
    normalizedTrace ι K = (Matrix.trace K).re / (Fintype.card ι : ℝ) := by
  simp [normalizedTrace, div_eq_mul_inv, mul_comm]

@[simp] theorem normalizedTrace_one : normalizedTrace ι (1 : Mat ι) = 1 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  simp [normalizedTrace, hn]

omit [DecidableEq ι] [Nonempty ι] in
theorem normalizedTrace_mul_comm (K L : Mat ι) :
    normalizedTrace ι (K * L) = normalizedTrace ι (L * K) := by
  simp only [normalizedTrace_apply, Matrix.trace_mul_comm K L]

/-- The normalized partition function, defined by the matrix exponential. -/
def partition (K : Mat ι) : ℝ := normalizedTrace ι (NormedSpace.exp K)

/-- The prepared logarithmic response. The real trace is positive near zero. -/
def response (K : Mat ι) : ℝ := Real.log (partition ι K)

@[simp] theorem partition_zero : partition ι 0 = 1 := by
  simp [partition]

@[simp] theorem response_zero : response ι 0 = 0 := by
  simp [response]

omit [Nonempty ι] in
theorem response_apply (K : Mat ι) :
    response ι K = Real.log
      ((Matrix.trace (NormedSpace.exp K)).re / (Fintype.card ι : ℝ)) := by
  simp only [response, partition, normalizedTrace_apply]

def partitionSeries : FormalMultilinearSeries ℝ (Mat ι) ℝ :=
  (normalizedTrace ι).compFormalMultilinearSeries (NormedSpace.expSeries ℝ (Mat ι))

omit [Nonempty ι] in
theorem partition_hasFPowerSeries :
    HasFPowerSeriesOnBall (partition ι) (partitionSeries ι) 0 ⊤ :=
  (normalizedTrace ι).comp_hasFPowerSeriesOnBall NormedSpace.exp_hasFPowerSeriesOnBall

omit [Nonempty ι] in
theorem partition_analyticAt (K : Mat ι) : AnalyticAt ℝ (partition ι) K := by
  obtain ⟨p, r, hp⟩ := NormedSpace.exp_analytic (𝕂 := ℝ) K
  exact ⟨(normalizedTrace ι).compFormalMultilinearSeries p, r,
    (normalizedTrace ι).comp_hasFPowerSeriesOnBall hp⟩

omit [Nonempty ι] in
theorem partition_hasFDerivAt_zero :
    HasFDerivAt (partition ι) (normalizedTrace ι) 0 := by
  have h := (normalizedTrace ι).hasFDerivAt.comp 0
    (_root_.hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat ι))
  simp only [ContinuousLinearMap.one_def] at h
  convert! h using 1

omit [Nonempty ι] in
@[simp] theorem partition_fderiv_zero :
    fderiv ℝ (partition ι) 0 = normalizedTrace ι :=
  (partition_hasFDerivAt_zero ι).fderiv

theorem partition_pos_near_zero : ∀ᶠ K in 𝓝 (0 : Mat ι), 0 < partition ι K := by
  exact (partition_hasFDerivAt_zero ι).continuousAt.eventually
    (isOpen_Ioi.mem_nhds (by simp))

omit [Nonempty ι] in
/-- The derivative of the partition derivative exists as a continuous linear map. -/
theorem partition_fderiv_hasFDerivAt_zero :
    HasFDerivAt (fderiv ℝ (partition ι))
      (fderiv ℝ (fderiv ℝ (partition ι)) 0) 0 :=
  (partition_hasFPowerSeries ι).fderiv.hasFPowerSeriesAt.differentiableAt.hasFDerivAt

omit [Nonempty ι] in
theorem partition_hessian_diagonal (K : Mat ι) :
    fderiv ℝ (fderiv ℝ (partition ι)) 0 K K = normalizedTrace ι (K * K) := by
  have h := congrArg (fun D => D K K)
    (partition_hasFPowerSeries ι).fderiv.hasFPowerSeriesAt.fderiv_eq
  simp only [continuousMultilinearCurryFin1_apply, Fin.snoc_zero] at h
  have hdiag : (partitionSeries ι).derivSeries 1 (fun _ => K) K =
      (2 : ℕ) • partitionSeries ι 2 (fun _ => K) := by
    exact (partitionSeries ι).derivSeries_apply_diag 1 K
  have hsecond : fderiv ℝ (fderiv ℝ (partition ι)) 0 K K =
      (2 : ℕ) • normalizedTrace ι
        (NormedSpace.expSeries ℝ (Mat ι) 2 (fun _ => K)) := by
    convert! h.trans hdiag using 1
  rw [NormedSpace.expSeries_apply_eq] at hsecond
  norm_num [map_smul, smul_eq_mul, nsmul_eq_mul, pow_two] at hsecond
  rw [normalizedTrace_apply]
  linarith

omit [Nonempty ι] in
/-- Polarization determines the mixed second derivatives. -/
theorem partition_hessian_apply (K L : Mat ι) :
    fderiv ℝ (fderiv ℝ (partition ι)) 0 K L = normalizedTrace ι (K * L) := by
  have hs : IsSymmSndFDerivAt ℝ (partition ι) 0 :=
    ((partition_analyticAt ι 0).contDiffAt : ContDiffAt ℝ ω (partition ι) 0).isSymmSndFDerivAt_of_omega
  have hsLK : fderiv ℝ (fderiv ℝ (partition ι)) 0 L K =
      fderiv ℝ (fderiv ℝ (partition ι)) 0 K L := by
    exact hs L K
  have h := partition_hessian_diagonal ι (K + L)
  simp only [map_add, _root_.add_apply, add_mul, mul_add] at h
  rw [partition_hessian_diagonal ι K, partition_hessian_diagonal ι L,
    hsLK, normalizedTrace_mul_comm ι L K] at h
  linarith

/-- The continuous bilinear expression furnished by the logarithm chain rule. -/
def responseHessian : Mat ι →L[ℝ] Mat ι →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (partition ι)) 0 +
    (-normalizedTrace ι).smulRight (normalizedTrace ι)

omit [Nonempty ι] in
theorem responseHessian_apply (K L : Mat ι) :
    responseHessian ι K L = preparedForm ι K L := by
  simp only [responseHessian, _root_.add_apply,
    ContinuousLinearMap.smulRight_apply, _root_.neg_apply,
    _root_.smul_apply, smul_eq_mul, partition_hessian_apply,
    normalizedTrace_apply, preparedForm_apply]
  simp only [div_eq_mul_inv]
  ring

theorem response_hasFDerivAt_zero :
    HasFDerivAt (response ι) (normalizedTrace ι) 0 := by
  have h : HasFDerivAt (fun K : Mat ι => Real.log (partition ι K))
      ((partition ι 0)⁻¹ • normalizedTrace ι) 0 := by
    apply HasFDerivAt.log
    · convert! partition_hasFDerivAt_zero ι using 1
    · simp
  simp only [partition_zero, inv_one, one_smul] at h
  convert! h using 1

@[simp] theorem response_fderiv_zero :
    fderiv ℝ (response ι) 0 = normalizedTrace ι :=
  (response_hasFDerivAt_zero ι).fderiv

private theorem partition_inv_hasFDerivAt_zero :
    HasFDerivAt (fun K : Mat ι => (partition ι K)⁻¹) (-normalizedTrace ι) 0 := by
  have h := (hasDerivAt_inv (show partition ι 0 ≠ 0 by simp)).comp_hasFDerivAt 0
    (partition_hasFDerivAt_zero ι)
  simp only [partition_zero, one_pow, inv_one, Function.comp_def] at h
  convert! h using 1
  exact (neg_one_smul ℝ (normalizedTrace ι)).symm

private theorem partition_inv_smul_fderiv_hasFDerivAt_zero :
    HasFDerivAt
      (fun K : Mat ι => (partition ι K)⁻¹ • fderiv ℝ (partition ι) K)
      (responseHessian ι) 0 := by
  have hproduct : HasFDerivAt
      (fun K : Mat ι => (partition ι K)⁻¹ • fderiv ℝ (partition ι) K)
      ((partition ι 0)⁻¹ • fderiv ℝ (fderiv ℝ (partition ι)) 0 +
        (-normalizedTrace ι).smulRight (fderiv ℝ (partition ι) 0)) 0 := by
    exact hasFDerivAt_smul_dual (E := Mat ι)
      (c := fun K : Mat ι => (partition ι K)⁻¹)
      (c' := by exact -normalizedTrace ι)
      (f := by exact fderiv ℝ (partition ι))
      (f' := by exact fderiv ℝ (fderiv ℝ (partition ι)) 0) (x := 0)
      (by exact partition_inv_hasFDerivAt_zero ι)
      (by exact partition_fderiv_hasFDerivAt_zero ι)
  simp only [partition_zero, inv_one, one_smul, partition_fderiv_zero] at hproduct
  convert! hproduct using 1

/-- The logarithm chain rule identifies the complete second Fréchet derivative. -/
theorem response_fderiv_hasFDerivAt_zero :
    HasFDerivAt (fderiv ℝ (response ι)) (responseHessian ι) 0 := by
  apply (partition_inv_smul_fderiv_hasFDerivAt_zero ι).congr_of_eventuallyEq
  filter_upwards [partition_pos_near_zero ι] with K hK
  exact ((partition_analyticAt ι K).differentiableAt.hasFDerivAt.log
    (ne_of_gt hK)).fderiv

/-- The Hessian is the trace covariance for arbitrary two real matrix directions. -/
theorem response_hessian_apply (K L : Mat ι) :
    fderiv ℝ (fderiv ℝ (response ι)) 0 K L = preparedForm ι K L := by
  rw [(response_fderiv_hasFDerivAt_zero ι).fderiv, responseHessian_apply]

theorem response_hessian_formula (K L : Mat ι) :
    fderiv ℝ (fderiv ℝ (response ι)) 0 K L =
      (Matrix.trace (K * L)).re / (Fintype.card ι : ℝ) -
        (Matrix.trace K).re * (Matrix.trace L).re / (Fintype.card ι : ℝ) ^ 2 := by
  rw [response_hessian_apply, preparedForm_apply]

theorem response_hessian_hermitian (K L : Hermitian ι) :
    fderiv ℝ (fderiv ℝ (response ι)) 0 (K : Mat ι) (L : Mat ι) =
      preparedForm ι (K : Mat ι) (L : Mat ι) :=
  response_hessian_apply ι K L

theorem response_hessian_nonneg {K : Mat ι} (hK : K.IsHermitian) :
    0 ≤ fderiv ℝ (fderiv ℝ (response ι)) 0 K K := by
  rw [response_hessian_apply]
  exact preparedForm_nonneg ι hK

theorem response_hessian_self_eq_zero_iff {K : Mat ι} (hK : K.IsHermitian) :
    fderiv ℝ (fderiv ℝ (response ι)) 0 K K = 0 ↔
      ∃ a : ℝ, K = a • (1 : Mat ι) := by
  rw [response_hessian_apply]
  exact preparedForm_self_eq_zero_iff ι hK

theorem response_hessian_traceless_pos (K : Traceless ι) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (response ι)) 0 (K.val : Mat ι) (K.val : Mat ι) := by
  rw [response_hessian_apply]
  exact preparedForm_traceless_pos ι K hK

end GeneratedFoundations.Operations.PreparedTraceDifferentiation
