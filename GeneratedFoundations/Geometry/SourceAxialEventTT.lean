module

public import GeneratedFoundations.Geometry.SourceLinearTensor
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic

/-!
# Axial tensor comparisons on the generated event carrier

The Euclidean momentum representation of `SourceLinearTensor` admits
transverse trace-free comparisons with temporal components. They are
distinct from the two spatial polarizations used for a massless helicity
readout. An axial vector labels the transverse subspace at zero transfer.

The frame below acts on the original four-coordinate derivative jet. Its
first and direct second precision vertices are calculated from the same
kinetic square. The transfer momentum specifying the tensor constraints
is kept distinct from the frequency carried by the source being compared.
No spacetime metric is added to the source datum.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace GeneratedFoundations.Geometry.SourceAxialEventTT

open SourceLinearTensor

/-- Nonzero axial vector used to label the transverse subspace at zero transfer. -/
def transfer : FourVector := axialMomentum 1

/-- A unit tensor comparison which retains a temporal component. -/
def temporalComparison : FourTensor :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem temporalComparison_axialTT (k : ℝ) :
    IsMomentumTT (axialMomentum k) temporalComparison := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [temporalComparison, Matrix.transpose_apply]
  · norm_num [tensorTrace, temporalComparison, Fin.sum_univ_four]
  · funext i
    fin_cases i <;>
      simp [SourceLinearTensor.contractRight, axialMomentum, temporalComparison,
        Fin.sum_univ_four]

theorem temporalComparison_isTT : IsMomentumTT transfer temporalComparison :=
  temporalComparison_axialTT 1

@[simp] theorem temporalComparison_time : temporalComparison 0 0 = 1 := by
  rfl

theorem temporalComparison_not_spatialLift (h : SourceAxisTT.SpatialTensor) :
    temporalComparison ≠ spatialLift h := by
  intro heq
  have ht := congrFun (congrFun heq (0 : Fin 4)) (0 : Fin 4)
  norm_num [temporalComparison, spatialLift] at ht

def tensorPairing (h k : FourTensor) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace (h.transpose * k)

theorem temporalComparison_unit : tensorPairing temporalComparison temporalComparison = 1 := by
  norm_num [tensorPairing, temporalComparison, Matrix.trace,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]

/-- The affine coframe acts on the existing event derivative coordinates. -/
def coframe (t : ℝ) : FourTensor := (1 : FourTensor) + (t / 2) • temporalComparison

def frequencyJet (omega : ℝ) : FourVector := ![omega, 0, 0, 0]

def changedFrequencyJet (omega t : ℝ) : FourVector :=
  (coframe t).mulVec (frequencyJet omega)

theorem changedFrequencyJet_eq (omega t : ℝ) :
    changedFrequencyJet omega t = ![(1 + t / 2) * omega, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [changedFrequencyJet, coframe, frequencyJet, temporalComparison,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem frequency_kinetic_square (omega t : ℝ) :
    dot4 (changedFrequencyJet omega t) (changedFrequencyJet omega t) =
      omega ^ 2 * (1 + t / 2) ^ 2 := by
  rw [changedFrequencyJet_eq]
  simp [dot4, Fin.sum_univ_four]
  ring

/-- The internal kinetic coefficient and the mass remain in their original
block. Only the displayed event-frequency derivative is compared. -/
def precision (a b omega t : ℝ) : ℝ :=
  a + b + dot4 (changedFrequencyJet omega t) (changedFrequencyJet omega t)

theorem precision_expansion (a b omega t : ℝ) :
    precision a b omega t =
      (omega ^ 2 + a + b) + t * omega ^ 2 + t ^ 2 * omega ^ 2 / 4 := by
  rw [precision, frequency_kinetic_square]
  ring

@[simp] theorem precision_zero (a b omega : ℝ) :
    precision a b omega 0 = omega ^ 2 + a + b := by
  rw [precision_expansion]
  ring

def firstVertex (omega t : ℝ) : ℝ := omega ^ 2 + t * omega ^ 2 / 2

theorem precision_hasDerivAt (a b omega t : ℝ) :
    HasDerivAt (precision a b omega) (firstVertex omega t) t := by
  have hd := ((hasDerivAt_const t (omega ^ 2 + a + b)).add
    ((hasDerivAt_id t).mul_const (omega ^ 2))).add
      ((((hasDerivAt_id t).pow 2).mul_const (omega ^ 2)).div_const 4)
  convert hd using 1
  · funext s
    exact precision_expansion a b omega s
  · simp [firstVertex]
    ring

/-- The direct second vertex is kept from the same coframe square. -/
theorem firstVertex_hasDerivAt (omega t : ℝ) :
    HasDerivAt (firstVertex omega) (omega ^ 2 / 2) t := by
  simpa [firstVertex] using!
    (hasDerivAt_const t (omega ^ 2)).add
      (((hasDerivAt_id t).mul_const (omega ^ 2)).div_const 2)

@[simp] theorem firstVertex_zero (omega : ℝ) : firstVertex omega 0 = omega ^ 2 := by
  simp [firstVertex]

theorem precision_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (omega t : ℝ) :
    0 < precision a b omega t := by
  rw [precision, frequency_kinetic_square]
  nlinarith [sq_nonneg omega, sq_nonneg (1 + t / 2),
    mul_nonneg (sq_nonneg omega) (sq_nonneg (1 + t / 2))]

end GeneratedFoundations.Geometry.SourceAxialEventTT
