module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Determinant phases in a complete finite unitary frame

The phase exponent is the actual dimension. Existence is pointwise; a
continuous choice over a base is not part of the conclusion. The full
root-of-unity ambiguity is retained, including its inverse action on the
determinant-one factor.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.UnitaryDeterminantPhase

abbrev MatrixN (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev SpecialUnitary (n : ℕ) := Matrix.specialUnitaryGroup (Fin n) ℂ

private theorem circle_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ := by
  have hs : star (z : ℂ) = (z : ℂ)⁻¹ := by
    simpa only [Circle.coe_inv, Complex.star_def] using (Circle.coe_inv_eq_conj z).symm
  constructor
  · change star (z : ℂ) * (z : ℂ) = 1
    rw [hs, inv_mul_cancel₀ (Circle.coe_ne_zero z)]
  · change (z : ℂ) * star (z : ℂ) = 1
    rw [hs, mul_inv_cancel₀ (Circle.coe_ne_zero z)]

theorem phase_specialUnitary_det (n : ℕ) (z : Circle) (U : SpecialUnitary n) :
    ((z : ℂ) • (U : MatrixN n)).det = (z : ℂ) ^ n := by
  have hdet : (U : MatrixN n).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.property).2
  rw [Matrix.det_smul, Fintype.card_fin, hdet, mul_one]

theorem exists_phase_specialUnitary (n : ℕ) (hn : 0 < n) (M : MatrixN n)
    (hM : M ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (z : Circle) (U : SpecialUnitary n),
      M = (z : ℂ) • (U : MatrixN n) ∧ (z : ℂ) ^ n = M.det := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq M.det (n := n) hn
  have hdetnorm : ‖M.det‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hM)
  have hnormpow : ‖a‖ ^ n = 1 := by rw [← norm_pow, ha, hdetnorm]
  have hnorm : ‖a‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg a) (Nat.ne_of_gt hn)).mp hnormpow
  let z : Circle := ⟨a, mem_sphere_zero_iff_norm.mpr hnorm⟩
  have hz : (z : ℂ) ^ n = M.det := ha
  have hdet_ne : M.det ≠ 0 := by
    rw [← hz]
    exact pow_ne_zero n (Circle.coe_ne_zero z)
  let A : MatrixN n := ((z⁻¹ : Circle) : ℂ) • M
  have hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.smul_mem_of_mem (circle_mem_unitary z⁻¹) hM
  have hAdet : A.det = 1 := by
    change (((z⁻¹ : Circle) : ℂ) • M).det = 1
    rw [Matrix.det_smul, Fintype.card_fin, Circle.coe_inv, inv_pow, hz,
      inv_mul_cancel₀ hdet_ne]
  refine ⟨z, ⟨A, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hA, hAdet⟩⟩, ?_, hz⟩
  change M = (z : ℂ) • (((z⁻¹ : Circle) : ℂ) • M)
  rw [smul_smul, Circle.coe_inv, mul_inv_cancel₀ (Circle.coe_ne_zero z), one_smul]

theorem decomposition_ambiguity (n : ℕ) (M : MatrixN n) (z w : Circle)
    (U V : SpecialUnitary n)
    (hU : M = (z : ℂ) • (U : MatrixN n))
    (hV : M = (w : ℂ) • (V : MatrixN n)) :
    (w / z) ^ n = 1 ∧
      (V : MatrixN n) = (((w / z)⁻¹ : Circle) : ℂ) • (U : MatrixN n) := by
  have hpow : (w : ℂ) ^ n = (z : ℂ) ^ n := by
    calc
      (w : ℂ) ^ n = M.det := by rw [hV, phase_specialUnitary_det]
      _ = (z : ℂ) ^ n := by rw [hU, phase_specialUnitary_det]
  constructor
  · apply Circle.coe_injective
    simp only [Circle.coe_pow, Circle.coe_div, Circle.coe_one, div_pow, hpow,
      div_self (pow_ne_zero n (Circle.coe_ne_zero z))]
  · have he : (w : ℂ) • (V : MatrixN n) = (z : ℂ) • (U : MatrixN n) := hV.symm.trans hU
    have hh := congrArg (fun A : MatrixN n => (w : ℂ)⁻¹ • A) he
    have hc : (((w / z)⁻¹ : Circle) : ℂ) = (w : ℂ)⁻¹ * (z : ℂ) := by
      rw [Circle.coe_inv, Circle.coe_div, inv_div, div_eq_mul_inv, mul_comm]
    rw [hc]
    simpa only [smul_smul, inv_mul_cancel₀ (Circle.coe_ne_zero w), one_smul] using hh

end GeneratedFoundations.Geometry.UnitaryDeterminantPhase
