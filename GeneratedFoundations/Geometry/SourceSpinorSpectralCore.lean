module

public import GeneratedFoundations.Geometry.SourceSpinorDifferential
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Symmetric differentiated spin blocks in the source Haar metric

The two coefficients belong to the original source representation with its
Haar-induced inner product. Symmetry follows from skewness of the actual
unit-axis derivatives. The finite spectral theorem is applied only after
that calculation.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights
open GeneratedFoundations.Geometry.SourcePolynomialCasimir
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceSpinorDifferential

namespace GeneratedFoundations.Geometry.SourceSpinorSpectralCore

abbrev SpinorBlock (m : ℕ) := PiLp 2 (fun _ : Fin 2 => HilbertCarrier m)

instance spinorBlockInner (m : ℕ) : InnerProductSpace ℂ (SpinorBlock m) :=
  PiLp.innerProductSpace (fun _ : Fin 2 => HilbertCarrier m)

def kineticBlock (m : ℕ) : SpinorBlock m →ₗ[ℂ] SpinorBlock m where
  toFun A := WithLp.toLp 2
    ![Complex.I • unitHilbertAxis m 2 (A 0) -
        Complex.I • unitHilbertAxis m 0 (A 1) + unitHilbertAxis m 1 (A 1),
      -Complex.I • unitHilbertAxis m 0 (A 0) - unitHilbertAxis m 1 (A 0) -
        Complex.I • unitHilbertAxis m 2 (A 1)]
  map_add' A B := by
    apply (WithLp.equiv 2 (Fin 2 → HilbertCarrier m)).injective
    funext i
    fin_cases i <;> simp [map_add] <;> module
  map_smul' c A := by
    apply (WithLp.equiv 2 (Fin 2 → HilbertCarrier m)).injective
    funext i
    fin_cases i <;> simp [map_smul, smul_smul] <;> module

@[simp] theorem kineticBlock_zero (m : ℕ) (A : SpinorBlock m) :
    kineticBlock m A 0 = Complex.I • unitHilbertAxis m 2 (A 0) -
      Complex.I • unitHilbertAxis m 0 (A 1) + unitHilbertAxis m 1 (A 1) := rfl

@[simp] theorem kineticBlock_one (m : ℕ) (A : SpinorBlock m) :
    kineticBlock m A 1 = -Complex.I • unitHilbertAxis m 0 (A 0) -
      unitHilbertAxis m 1 (A 0) - Complex.I • unitHilbertAxis m 2 (A 1) := rfl

theorem kineticBlock_symmetric (m : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := SpinorBlock m) (kineticBlock m) := by
  intro A B
  have hskew (i : Fin 3) (a b : HilbertCarrier m) :
      inner ℂ (unitHilbertAxis m i a) b = -inner ℂ a (unitHilbertAxis m i b) :=
    eq_neg_of_add_eq_zero_left (unitAxis_skew_pairing m i a b)
  have hleft (c : ℂ) (a b : HilbertCarrier m) :
      inner ℂ (c • a) b = conj c * inner ℂ a b :=
    inner_smul_left a b c
  have hright (c : ℂ) (a b : HilbertCarrier m) :
      inner ℂ a (c • b) = c * inner ℂ a b :=
    inner_smul_right a b c
  simp only [PiLp.inner_apply, Fin.sum_univ_two, kineticBlock_zero, kineticBlock_one,
    inner_add_left, inner_sub_left, inner_add_right, inner_sub_right, hleft, hright, hskew,
    map_neg, Complex.conj_I]
  ring

def diracBlock (m : ℕ) : SpinorBlock m →ₗ[ℂ] SpinorBlock m :=
  kineticBlock m + (3 / 2 : ℂ) • (1 : Module.End ℂ (SpinorBlock m))

theorem spinorBlock_finrank (m : ℕ) :
    Module.finrank ℂ (SpinorBlock m) = 2 * (m + 1) := by
  calc
    _ = Module.finrank ℂ (Fin 2 → HilbertCarrier m) :=
      (WithLp.linearEquiv 2 ℂ (Fin 2 → HilbertCarrier m)).finrank_eq
    _ = _ := by simp [Module.finrank_pi_fintype, hilbertCarrier_finrank]

def kineticBasis (m : ℕ) :
    OrthonormalBasis (Fin (2 * (m + 1))) ℂ (SpinorBlock m) :=
  (kineticBlock_symmetric m).eigenvectorBasis (spinorBlock_finrank m)

def kineticEigenvalue (m : ℕ) (j : Fin (2 * (m + 1))) : ℝ :=
  (kineticBlock_symmetric m).eigenvalues (spinorBlock_finrank m) j

theorem kineticBasis_eigenvector (m : ℕ) (j : Fin (2 * (m + 1))) :
    kineticBlock m (kineticBasis m j) =
      (kineticEigenvalue m j : ℂ) • kineticBasis m j :=
  (kineticBlock_symmetric m).apply_eigenvectorBasis (spinorBlock_finrank m) j

/-- Polynomial coefficients are realized in the original Haar-induced metric.
This equivalence transports no proposed eigenvalue data. -/
def pairRealization (m : ℕ) :
    SourceClebschGordan.PairCarrier m ≃ₗ[ℂ] SpinorBlock m :=
  ((carrierEquiv m).prodCongr (carrierEquiv m)).trans
    ((LinearEquiv.finTwoArrow ℂ (HilbertCarrier m)).symm.trans
      (WithLp.linearEquiv 2 ℂ (Fin 2 → HilbertCarrier m)).symm)

@[simp] theorem pairRealization_zero (m : ℕ)
    (p : SourceClebschGordan.PairCarrier m) :
    pairRealization m p 0 = carrierEquiv m p.1 := rfl

@[simp] theorem pairRealization_one (m : ℕ)
    (p : SourceClebschGordan.PairCarrier m) :
    pairRealization m p 1 = carrierEquiv m p.2 := rfl

/-- The derivative in the Haar carrier is the same operator as the explicit
polynomial derivative, before either one is diagonalized. -/
theorem pairRealization_kinetic (m : ℕ)
    (p : SourceClebschGordan.PairCarrier m) :
    kineticBlock m (pairRealization m p) =
      pairRealization m (polynomialKinetic m p) := by
  have ha (i : Fin 3) (f : Carrier m) :
      unitHilbertAxis m i (carrierEquiv m f) =
        carrierEquiv m (polynomialAxis m i f) := by
    rw [← polynomialAxis_transport]
    exact hilbertOperator_apply m (polynomialAxis m i) f
  apply (WithLp.equiv 2 (Fin 2 → HilbertCarrier m)).injective
  funext i
  fin_cases i <;>
    simp [ha, polynomialKinetic, polynomialAxis, map_add, map_sub, map_smul, smul_add, smul_smul] <;>
    match_scalars <;> ring_nf

theorem kineticBlock_degree_zero : kineticBlock 0 = 0 := by
  apply LinearMap.ext
  intro A
  apply (WithLp.equiv 2 (Fin 2 → HilbertCarrier 0)).injective
  funext i
  fin_cases i <;> simp [unitAxis_degree_zero]

/-- Every finite differentiated eigenvector lies in one of the two explicit
polynomial summands. This is an exhaustion statement for the actual block. -/
theorem kineticEigenvalue_branches (m : ℕ) (j : Fin (2 * (m + 1))) :
    kineticEigenvalue m j = (m : ℝ) ∨
      kineticEigenvalue m j = -((m : ℝ) + 2) := by
  cases m with
  | zero =>
      left
      have h := kineticBasis_eigenvector 0 j
      rw [kineticBlock_degree_zero, LinearMap.zero_apply] at h
      have hn : kineticBasis 0 j ≠ 0 := (kineticBasis 0).orthonormal.ne_zero j
      exact_mod_cast (smul_eq_zero.mp h.symm).resolve_right hn
  | succ k =>
      let p := (pairRealization (k + 1)).symm (kineticBasis (k + 1) j)
      have hp : p ≠ 0 := by
        intro hp
        have hz := congrArg (pairRealization (k + 1)) hp
        have hn := (kineticBasis (k + 1)).orthonormal.ne_zero j
        exact hn (by simpa [p] using hz)
      have he : polynomialKinetic (k + 1) p =
          (kineticEigenvalue (k + 1) j : ℂ) • p := by
        apply (pairRealization (k + 1)).injective
        rw [← pairRealization_kinetic, map_smul]
        simpa [p] using kineticBasis_eigenvector (k + 1) j
      rcases kinetic_eigenvalue p hp he with hc | hc
      · left
        exact_mod_cast hc
      · right
        exact_mod_cast hc

theorem diracBlock_basis (m : ℕ) (j : Fin (2 * (m + 1))) :
    diracBlock m (kineticBasis m j) =
      ((kineticEigenvalue m j + 3 / 2 : ℝ) : ℂ) • kineticBasis m j := by
  simp only [diracBlock, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    kineticBasis_eigenvector, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat]
  module

theorem diracEigenvalue_sq_lower (m : ℕ) (j : Fin (2 * (m + 1))) :
    (3 / 2 : ℝ) ^ 2 ≤ (kineticEigenvalue m j + 3 / 2) ^ 2 := by
  rcases kineticEigenvalue_branches m j with hp | hn
  · rw [hp]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  · cases m with
    | zero =>
        have h := kineticBasis_eigenvector 0 j
        rw [kineticBlock_degree_zero, LinearMap.zero_apply] at h
        have hnz : kineticBasis 0 j ≠ 0 := (kineticBasis 0).orthonormal.ne_zero j
        have hz : kineticEigenvalue 0 j = 0 := by
          exact_mod_cast (smul_eq_zero.mp h.symm).resolve_right hnz
        rw [hz]
        norm_num
    | succ k =>
        rw [hn]
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        push_cast
        nlinarith

end GeneratedFoundations.Geometry.SourceSpinorSpectralCore
