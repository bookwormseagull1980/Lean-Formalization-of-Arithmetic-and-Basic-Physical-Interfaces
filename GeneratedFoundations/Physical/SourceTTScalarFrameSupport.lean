module

public import GeneratedFoundations.Geometry.SourceOneFormDifferential
public import GeneratedFoundations.Physical.SourceTTCapacitySpectrum
public import GeneratedFoundations.Physical.SourceTTResponseNormalization
public import GeneratedFoundations.Operations.PrecisionMixedResponse

/-!
# Support of the actual scalar gradient-frame comparison

The frame acts on the differentiated source coefficients before the
quadratic form is taken. Its action is calculated on every scalar row.
The constant row has zero source derivatives for every frame, including
nonlinear frame paths. Adding the unchanged frequency precision does not
alter this statement.

The Gaussian comparison below retains all four real coordinates of the
original constant scalar branch. A spatial frame insertion is absent
from that precision, whereas the independent mass insertion remains.
This determines exactly where a same-vertex reference can be normalized;
it does not replace the original eight-branch comparison trace.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace GeneratedFoundations.Physical.SourceTTScalarFrameSupport

open Geometry.SourceAxisMetric Geometry.SourceAxisTT
open Geometry.SourceSymmetricUnitary
open Geometry.SourceSchurOrthogonality Geometry.SourceOneFormDifferential
open Operations

/-- The same generated source derivatives in a compared spatial frame. -/
def changedAxis (m : ℕ) (R : SpatialTensor) (i : Fin 3) :
    Module.End ℂ (HilbertCarrier m) :=
  ∑ a : Fin 3, (R i a : ℂ) • unitHilbertAxis m a

@[simp] theorem changedAxis_degree_zero (R : SpatialTensor) (i : Fin 3) :
    changedAxis 0 R i = 0 := by
  simp [changedAxis, unitAxis_degree_zero]

/-- Every mixed source pairing is retained before any modal trace. -/
def gradientPairing (m : ℕ) (R : SpatialTensor) (v w : HilbertCarrier m) : ℂ :=
  ∑ i : Fin 3, inner ℂ (changedAxis m R i v) (changedAxis m R i w)

@[simp] theorem gradientPairing_degree_zero (R : SpatialTensor)
    (v w : HilbertCarrier 0) : gradientPairing 0 R v w = 0 := by
  simp [gradientPairing]

/-- Frequency and restoring precision are held fixed in the spatial
gradient comparison, just as in the original first nonconstant shell. -/
def fullPrecisionPairing (m : ℕ) (omega b : ℝ) (R : SpatialTensor)
    (v w : HilbertCarrier m) : ℂ :=
  ((omega ^ 2 + b : ℝ) : ℂ) * inner ℂ v w + gradientPairing m R v w

@[simp] theorem fullPrecisionPairing_degree_zero (omega b : ℝ)
    (R : SpatialTensor) (v w : HilbertCarrier 0) :
    fullPrecisionPairing 0 omega b R v w =
      ((omega ^ 2 + b : ℝ) : ℂ) * inner ℂ v w := by
  simp [fullPrecisionPairing]

/-- No choice of spatial frame path couples the constant row to a
spatial gradient. The frequency may be nonzero. -/
theorem constant_frame_path (omega b : ℝ) (R : ℝ → SpatialTensor)
    (v w : HilbertCarrier 0) :
    (fun t => fullPrecisionPairing 0 omega b (R t) v w) =
      fun _ => ((omega ^ 2 + b : ℝ) : ℂ) * inner ℂ v w := by
  funext t
  exact fullPrecisionPairing_degree_zero omega b (R t) v w

theorem constant_frame_hasDerivAt (omega b t : ℝ) (R : ℝ → SpatialTensor)
    (v w : HilbertCarrier 0) :
    HasDerivAt (fun s => fullPrecisionPairing 0 omega b (R s) v w) 0 t := by
  rw [constant_frame_path]
  exact hasDerivAt_const t _

/-- Four real coordinates are retained; the spatial frame vertex on
each is zero and the original independent mass variation remains. -/
def constantLogPartition (omega b s t : ℝ) : ℝ :=
  ∑ _ : Fin 4,
    PrecisionMixedResponse.logPartition 0 (b / (omega ^ 2 + b)) s t

theorem constantLogPartition_eq (omega b s t : ℝ) :
    constantLogPartition omega b s t =
      -2 * Real.log (1 + t * (b / (omega ^ 2 + b))) := by
  simp [constantLogPartition, PrecisionMixedResponse.logPartition,
    PrecisionMixedResponse.precision]
  ring

/-- This logarithm is the original four-coordinate Gaussian integral,
with its mass insertion and zero spatial frame insertion. -/
theorem constantLogPartition_actual {omega b s t : ℝ}
    (hp : 0 < omega ^ 2 + b)
    (ht : 0 < omega ^ 2 + b + t * b) :
    Real.log (FinitePrecisionTilt.partition
      (fun _ : Fin 4 => omega ^ 2 + b) (fun _ => t * b) 1) =
      constantLogPartition omega b s t := by
  rw [FinitePrecisionTilt.log_partition (fun _ => hp)
    (fun _ => by simpa [FinitePrecisionTilt.variedPrecision] using ht)]
  rw [constantLogPartition_eq]
  simp [FinitePrecisionTilt.logPartition, mul_div_assoc]
  ring

/-- Every positive-order spatial-frame mixed response is zero, not
only the two-insertion covariance. -/
theorem constant_mixed_derivative_zero (omega b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n)
      (fun s => iteratedDeriv n (constantLogPartition omega b s) 0) 0 = 0 := by
  have he : (fun s => iteratedDeriv n (constantLogPartition omega b s) 0) =
      fun _ => iteratedDeriv n (constantLogPartition omega b 0) 0 := by
    funext s
    have hf : constantLogPartition omega b s = constantLogPartition omega b 0 := by
      funext t
      simp only [constantLogPartition_eq]
    rw [hf]
  rw [he]
  have hn' : 2 * n ≠ 0 := by omega
  simp [iteratedDeriv_const, hn']

/-- In the complete original branch law, all coordinates are kept and
the score of this zero vertex is the zero random variable. -/
theorem constant_frame_variance_zero (p : Fin 4 → ℝ) :
    Var[FinitePrecisionGaussian.score (fun _ => (0 : ℝ));
      FinitePrecisionGaussian.law p] = 0 := by
  have he : FinitePrecisionGaussian.score (fun _ : Fin 4 => (0 : ℝ)) =
      (fun _ => (0 : ℝ)) := by
    funext x
    simp [FinitePrecisionGaussian.score, GaussianPrecisionMoments.score]
  rw [he]
  exact variance_zero _

/-- At the actual capacity peak the original kinetic comparison is
positive. It therefore cannot be obtained by rescaling a zero spatial
frame response. -/
theorem peak_kinetic_kernel :
    SourceTensorResponseEndpoint.ttKernel
      (SourceTTCapacitySpectrum.peakFrequency ^ 2) (3 / 4) = (4 / 9 : ℝ) := by
  rw [SourceTTCapacitySpectrum.peakFrequency_sq]
  norm_num [SourceTensorResponseEndpoint.ttKernel]

theorem no_constant_frame_calibration (kappa : ℝ) :
    kappa * Var[FinitePrecisionGaussian.score (fun _ : Fin 4 => (0 : ℝ));
      FinitePrecisionGaussian.law (fun _ =>
        SourceTTCapacitySpectrum.peakFrequency ^ 2 + 3 / 4)] ≠
      SourceTensorResponseEndpoint.ttKernel
        (SourceTTCapacitySpectrum.peakFrequency ^ 2) (3 / 4) := by
  rw [constant_frame_variance_zero, peak_kinetic_kernel]
  norm_num

/-- The remaining seven original branches are uniformly separated from
the capacity maximum, including their complete frequency intervals. -/
theorem nonconstant_fraction_bound (i : Fin 8) (hi : i ≠ 0) (u : ℝ) :
    SourceTTCapacitySpectrum.fraction i u ≤ (3 / 10 : ℝ) := by
  have hm : 7 * SourceTTCapacitySpectrum.mass i ≤
      3 * SourceTTCapacitySpectrum.kinetic i := by
    fin_cases i <;>
      norm_num [SourceTTCapacitySpectrum.kinetic, SourceTTCapacitySpectrum.mass,
        SourceTTGaussianCoefficient.branch, SourceTTGaussianCoefficient.torsion_eq] at *
  unfold SourceTTCapacitySpectrum.fraction SourceTensorResponseEndpoint.massFraction
  rw [div_le_iff₀ (SourceTTCapacitySpectrum.precision_pos i u)]
  nlinarith [sq_nonneg u]

theorem capacity_upper_below_third {y : ℝ} (hy : y ≤ 3 / 10) :
    SourceTensorResponseEndpoint.massWeightedResponse y ≤ (147 / 1000 : ℝ) := by
  have hd : 0 ≤ (3 / 10 : ℝ) - y := sub_nonneg.mpr hy
  have he : (147 / 1000 : ℝ) -
      SourceTensorResponseEndpoint.massWeightedResponse y =
      ((3 / 10 : ℝ) - y) *
        (((3 / 10 : ℝ) - y) ^ 2 + (11 / 10 : ℝ) * ((3 / 10 : ℝ) - y) + 7 / 100) := by
    unfold SourceTensorResponseEndpoint.massWeightedResponse
    ring
  apply sub_nonneg.mp
  rw [he]
  positivity

theorem nonconstant_capacity_margin (i : Fin 8) (hi : i ≠ 0) (u : ℝ) :
    (31 / 27000 : ℝ) ≤
      (4 / 27 : ℝ) - SourceTTCapacitySpectrum.capacity i u := by
  have hb := capacity_upper_below_third (nonconstant_fraction_bound i hi u)
  change SourceTTCapacitySpectrum.capacity i u ≤ (147 / 1000 : ℝ) at hb
  linarith

end GeneratedFoundations.Physical.SourceTTScalarFrameSupport
