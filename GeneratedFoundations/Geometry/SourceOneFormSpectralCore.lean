module

public import GeneratedFoundations.Geometry.SourceOneFormDifferential
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Symmetric curl blocks of the actual source differential

Each block contains three copies of the existing Haar-realized homogeneous
carrier. The operator is obtained by differentiating source matrix
coefficients in the original trace-orthonormal frame. Its symmetry is proved
from derivatives of the original unitary action. The spectral theorem is
therefore applied to an operator already constructed by differentiation;
no eigenvalue is used in the definition of that operator.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential

namespace GeneratedFoundations.Geometry.SourceOneFormSpectralCore

abbrev FrameCarrier (m : ℕ) := PiLp 2 (fun _ : Fin 3 => HilbertCarrier m)

/-- The block uses the sum of the three original Haar inner products. The
named instance also fixes this metric when passing to differential kernels. -/
instance frameCarrierInner (m : ℕ) : InnerProductSpace ℂ (FrameCarrier m) :=
  PiLp.innerProductSpace (fun _ : Fin 3 => HilbertCarrier m)

/-- Curl on one complete source-degree coefficient block. -/
def curlOperator (m : ℕ) : FrameCarrier m →ₗ[ℂ] FrameCarrier m where
  toFun A := WithLp.toLp 2 (coefficientCurl m (fun i => A i))
  map_add' A B := by
    apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier m)).injective
    exact coefficientCurl_add m (fun j => A j) (fun j => B j)
  map_smul' c A := by
    apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier m)).injective
    exact coefficientCurl_smul m c (fun j => A j)

@[simp] theorem curlOperator_apply (m : ℕ) (A : FrameCarrier m) (i : Fin 3) :
    curlOperator m A i = coefficientCurl m (fun j => A j) i := rfl

theorem curlOperator_symmetric (m : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := FrameCarrier m) (curlOperator m) := by
  intro A B
  have hskew (i : Fin 3) (a b : HilbertCarrier m) :
      inner ℂ (unitHilbertAxis m i a) b =
        -inner ℂ a (unitHilbertAxis m i b) :=
    eq_neg_of_add_eq_zero_left (unitAxis_skew_pairing m i a b)
  have htwoL (a b : HilbertCarrier m) :
      inner ℂ ((2 : ℂ) • a) b = (2 : ℂ) * inner ℂ a b := by
    simpa only [map_ofNat] using (inner_smul_left a b (2 : ℂ))
  have htwoR (a b : HilbertCarrier m) :
      inner ℂ a ((2 : ℂ) • b) = (2 : ℂ) * inner ℂ a b :=
    inner_smul_right a b (2 : ℂ)
  have hc0 (X : Fin 3 → HilbertCarrier m) :
      coefficientCurl m X 0 = unitHilbertAxis m 1 (X 2) -
        unitHilbertAxis m 2 (X 1) + (2 : ℂ) • X 0 := rfl
  have hc1 (X : Fin 3 → HilbertCarrier m) :
      coefficientCurl m X 1 = unitHilbertAxis m 2 (X 0) -
        unitHilbertAxis m 0 (X 2) + (2 : ℂ) • X 1 := rfl
  have hc2 (X : Fin 3 → HilbertCarrier m) :
      coefficientCurl m X 2 = unitHilbertAxis m 0 (X 1) -
        unitHilbertAxis m 1 (X 0) + (2 : ℂ) • X 2 := rfl
  simp only [PiLp.inner_apply, Fin.sum_univ_three, curlOperator_apply, hc0, hc1, hc2,
    inner_add_left, inner_sub_left, inner_add_right,
    inner_sub_right, htwoL, htwoR, hskew]
  ring

/-- All frame polarizations in the homogeneous block are retained. -/
theorem frameCarrier_finrank (m : ℕ) :
    Module.finrank ℂ (FrameCarrier m) = 3 * (m + 1) := by
  calc
    _ = Module.finrank ℂ (Fin 3 → HilbertCarrier m) :=
      (WithLp.linearEquiv 2 ℂ (Fin 3 → HilbertCarrier m)).finrank_eq
    _ = _ := by simp [Module.finrank_pi_fintype, SourceSymmetricUnitary.hilbertCarrier_finrank]

/-- A full orthonormal eigenbasis supplied after differential symmetry has
been established. Its eigenvalues are outputs of the finite spectral theorem. -/
def curlBasis (m : ℕ) :
    OrthonormalBasis (Fin (3 * (m + 1))) ℂ (FrameCarrier m) :=
  (curlOperator_symmetric m).eigenvectorBasis (frameCarrier_finrank m)

def curlEigenvalue (m : ℕ) (j : Fin (3 * (m + 1))) : ℝ :=
  (curlOperator_symmetric m).eigenvalues (frameCarrier_finrank m) j

theorem curlBasis_eigenvector (m : ℕ) (j : Fin (3 * (m + 1))) :
    curlOperator m (curlBasis m j) = (curlEigenvalue m j : ℂ) • curlBasis m j :=
  (curlOperator_symmetric m).apply_eigenvectorBasis (frameCarrier_finrank m) j

end GeneratedFoundations.Geometry.SourceOneFormSpectralCore
