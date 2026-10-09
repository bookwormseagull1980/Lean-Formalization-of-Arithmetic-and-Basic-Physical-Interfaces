module

public import GeneratedFoundations.Operations.SourceMatrixUnits
public import GeneratedFoundations.Operations.SourceSpinCornerFlow
public import GeneratedFoundations.Geometry.SourceSpinCentre

/-!
# Coherent preparation and tomography on the actual Gaussian source

The second excited Hermite mode is a reference that bypasses the controlled
two-mode operation. Explicit finite unitaries prepare coherent states from
the source vacuum. These unitaries and the self-adjoint probes belong to
the unital algebra of finite source matrix units. The matrix units are words
in the normalized differential ladder. Expectations on the original Hilbert
space recover every complex process matrix entry.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteFamily
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.HermiteCompleteness
open GeneratedFoundations.Operations.SourceSpinCorner (End Mat2 control)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Operations.SourceMatrixUnits

namespace GeneratedFoundations.Operations.SourceCoherentObservations

def amplitude : ℂ := (Real.sqrt 2 : ℂ)⁻¹

@[simp] theorem amplitude_conj : conj amplitude = amplitude := by simp [amplitude]

theorem amplitude_sq : amplitude * amplitude = (1 / 2 : ℂ) := by
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast (Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  simp only [amplitude, ← mul_inv_rev, h]
  norm_num

def prepared {b : ℝ} (hb : 0 < b) (k : Fin 2) : ComplexL2 :=
  amplitude • (state hb k + state hb 2)

def preparationBase {b : ℝ} (hb : 0 < b) : End :=
  1 + (amplitude - 1) • (matrixUnit hb 0 0 + matrixUnit hb 2 2) +
    amplitude • (matrixUnit hb 2 0 - matrixUnit hb 0 2)

def swapVacuum {b : ℝ} (hb : 0 < b) : End :=
  1 - matrixUnit hb 0 0 - matrixUnit hb 1 1 + matrixUnit hb 0 1 + matrixUnit hb 1 0

def preparation {b : ℝ} (hb : 0 < b) (k : Fin 2) : End :=
  if k = 0 then preparationBase hb else swapVacuum hb * preparationBase hb

theorem preparationBase_adjoint {b : ℝ} (hb : 0 < b) :
    (preparationBase hb).adjoint =
      1 + (amplitude - 1) • (matrixUnit hb 0 0 + matrixUnit hb 2 2) -
        amplitude • (matrixUnit hb 2 0 - matrixUnit hb 0 2) := by
  simp [preparationBase, ContinuousLinearMap.adjoint_one, map_smulₛₗ]
  module

theorem preparationBase_unitary {b : ℝ} (hb : 0 < b) :
    preparationBase hb ∈ unitary End := by
  constructor <;> change _ = (1 : End)
  all_goals
    rw [ContinuousLinearMap.star_eq_adjoint, preparationBase_adjoint]
    apply end_ext hb
    intro n
    have h02 : (0 : ℕ) ≠ 2 := by decide
    by_cases h0 : n = 0 <;> by_cases h2 : n = 2 <;> subst_vars
    all_goals try omega
    all_goals
      simp_all only [preparationBase, mul_apply_eq_comp, add_apply, sub_apply,
        one_apply_eq_self, smul_apply, map_add, map_sub, map_smul, map_neg, matrixUnit_state,
        ite_true, ite_false, eq_comm, add_zero, zero_add, sub_zero, zero_sub,
        smul_zero]
    all_goals
      match_scalars
      all_goals ring_nf <;> norm_num only [pow_two, amplitude_sq, mul_one, one_mul]

theorem swapVacuum_adjoint {b : ℝ} (hb : 0 < b) :
    (swapVacuum hb).adjoint = swapVacuum hb := by
  simp [swapVacuum, ContinuousLinearMap.adjoint_one]
  abel

theorem swapVacuum_unitary {b : ℝ} (hb : 0 < b) : swapVacuum hb ∈ unitary End := by
  constructor <;> change _ = (1 : End)
  all_goals
    rw [ContinuousLinearMap.star_eq_adjoint, swapVacuum_adjoint]
    simp [swapVacuum, mul_add, add_mul, mul_sub, sub_mul, matrixUnit_mul]

theorem preparation_unitary {b : ℝ} (hb : 0 < b) (k : Fin 2) :
    preparation hb k ∈ unitary End := by
  unfold preparation
  split_ifs
  · exact preparationBase_unitary hb
  · exact (unitary End).mul_mem (swapVacuum_unitary hb) (preparationBase_unitary hb)

theorem preparation_mem {b : ℝ} (hb : 0 < b) (k : Fin 2) :
    preparation hb k ∈ finiteSourceAlgebra hb := by
  have hm := matrixUnit_mem hb
  have hbase : preparationBase hb ∈ finiteSourceAlgebra hb := by
    exact (finiteSourceAlgebra hb).add_mem
      ((finiteSourceAlgebra hb).add_mem (finiteSourceAlgebra hb).one_mem
        ((finiteSourceAlgebra hb).smul_mem ((finiteSourceAlgebra hb).add_mem (hm 0 0) (hm 2 2)) _))
      ((finiteSourceAlgebra hb).smul_mem ((finiteSourceAlgebra hb).sub_mem (hm 2 0) (hm 0 2)) _)
  have hswap : swapVacuum hb ∈ finiteSourceAlgebra hb := by
    exact (finiteSourceAlgebra hb).add_mem
      ((finiteSourceAlgebra hb).add_mem
        ((finiteSourceAlgebra hb).sub_mem ((finiteSourceAlgebra hb).sub_mem
          (finiteSourceAlgebra hb).one_mem (hm 0 0)) (hm 1 1)) (hm 0 1)) (hm 1 0)
  unfold preparation
  split_ifs
  · exact hbase
  · exact (finiteSourceAlgebra hb).mul_mem hswap hbase

/-- Both coherent inputs are prepared by explicit generated reversible operators. -/
theorem preparation_vacuum {b : ℝ} (hb : 0 < b) (k : Fin 2) :
    preparation hb k (state hb 0) = prepared hb k := by
  have hbase : preparationBase hb (state hb 0) = amplitude • (state hb 0 + state hb 2) := by
    simp only [preparationBase, add_apply, sub_apply, one_apply_eq_self, smul_apply,
      matrixUnit_state]
    norm_num only [ite_true, ite_false, zero_smul, add_zero, sub_zero]
    module
  fin_cases k
  · exact hbase
  · change swapVacuum hb (preparationBase hb (state hb 0)) =
      amplitude • (state hb 1 + state hb 2)
    rw [hbase, map_smul, map_add]
    simp only [swapVacuum, add_apply, sub_apply, one_apply_eq_self, matrixUnit_state]
    norm_num only [ite_true, ite_false, zero_smul, add_zero, sub_zero]
    module

theorem prepared_norm {b : ℝ} (hb : 0 < b) (k : Fin 2) : ‖prepared hb k‖ = 1 := by
  let U : unitary End := ⟨preparation hb k, preparation_unitary hb k⟩
  rw [← preparation_vacuum]
  change ‖Unitary.linearIsometryEquiv U (state hb 0)‖ = 1
  rw [LinearIsometryEquiv.norm_map]
  exact (state_orthonormal hb).norm_eq_one 0

def xProbe {b : ℝ} (hb : 0 < b) (j : Fin 2) : End :=
  matrixUnit hb j 2 + matrixUnit hb 2 j

def yProbe {b : ℝ} (hb : 0 < b) (j : Fin 2) : End :=
  Complex.I • (matrixUnit hb j 2 - matrixUnit hb 2 j)

theorem xProbe_selfAdjoint {b : ℝ} (hb : 0 < b) (j : Fin 2) :
    IsSelfAdjoint (xProbe hb j) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [xProbe, add_comm]

theorem yProbe_selfAdjoint {b : ℝ} (hb : 0 < b) (j : Fin 2) :
    IsSelfAdjoint (yProbe hb j) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [yProbe, map_smulₛₗ]
  module

theorem xProbe_mem {b : ℝ} (hb : 0 < b) (j : Fin 2) : xProbe hb j ∈ finiteSourceAlgebra hb :=
  (finiteSourceAlgebra hb).add_mem (matrixUnit_mem hb j 2) (matrixUnit_mem hb 2 j)

theorem yProbe_mem {b : ℝ} (hb : 0 < b) (j : Fin 2) : yProbe hb j ∈ finiteSourceAlgebra hb :=
  (finiteSourceAlgebra hb).smul_mem
    ((finiteSourceAlgebra hb).sub_mem (matrixUnit_mem hb j 2) (matrixUnit_mem hb 2 j)) _

theorem probe_square {b : ℝ} (hb : 0 < b) (j : Fin 2) :
    xProbe hb j * xProbe hb j = matrixUnit hb j j + matrixUnit hb 2 2 ∧
      yProbe hb j * yProbe hb j = matrixUnit hb j j + matrixUnit hb 2 2 := by
  have hj : (j : ℕ) ≠ 2 := by omega
  constructor
  · simp [xProbe, mul_add, add_mul, matrixUnit_mul, hj, Ne.symm hj, add_comm]
  · apply ContinuousLinearMap.ext
    intro F
    simp only [yProbe, mul_apply_eq_comp, smul_apply, sub_apply, map_smul,
      map_sub, matrixUnit_apply, state_inner]
    simp only [hj, Ne.symm hj, ite_false, ite_true, mul_one,
      zero_smul, sub_zero, zero_sub, smul_neg, smul_smul, add_apply, matrixUnit_apply]
    have hc (c : ℂ) : -(Complex.I * c * Complex.I) = c := by
      calc
        _ = -(Complex.I * Complex.I) * c := by ring
        _ = c := by rw [Complex.I_mul_I]; ring
    match_scalars <;> simpa only [mul_neg, mul_assoc] using hc _

theorem probe_projection {b : ℝ} (hb : 0 < b) (j : Fin 2) :
    IsStarProjection (matrixUnit hb j j + matrixUnit hb 2 2) := by
  have hj : (j : ℕ) ≠ 2 := by omega
  constructor
  · simp [IsIdempotentElem, mul_add, add_mul, matrixUnit_mul, hj, Ne.symm hj]
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    simp

theorem xProbe_norm {b : ℝ} (hb : 0 < b) (j : Fin 2) : ‖xProbe hb j‖ = 1 := by
  have hp := IsStarProjection.norm_le _ (probe_projection hb j)
  have hs := ContinuousLinearMap.norm_adjoint_comp_self (xProbe hb j)
  rw [(ContinuousLinearMap.isSelfAdjoint_iff'.mp (xProbe_selfAdjoint hb j))] at hs
  change ‖xProbe hb j * xProbe hb j‖ = ‖xProbe hb j‖ * ‖xProbe hb j‖ at hs
  rw [(probe_square hb j).1] at hs
  have hl := (xProbe hb j).le_opNorm (state hb 2)
  have hj : (j : ℕ) ≠ 2 := by omega
  have hx : xProbe hb j (state hb 2) = state hb j := by
    simp only [xProbe, add_apply, matrixUnit_state, ite_true, hj, ite_false, add_zero]
  rw [hx, (state_orthonormal hb).norm_eq_one, (state_orthonormal hb).norm_eq_one,
    mul_one] at hl
  nlinarith [norm_nonneg (xProbe hb j)]

theorem yProbe_norm {b : ℝ} (hb : 0 < b) (j : Fin 2) : ‖yProbe hb j‖ = 1 := by
  have hp := IsStarProjection.norm_le _ (probe_projection hb j)
  have hs := ContinuousLinearMap.norm_adjoint_comp_self (yProbe hb j)
  rw [(ContinuousLinearMap.isSelfAdjoint_iff'.mp (yProbe_selfAdjoint hb j))] at hs
  change ‖yProbe hb j * yProbe hb j‖ = ‖yProbe hb j‖ * ‖yProbe hb j‖ at hs
  rw [(probe_square hb j).2] at hs
  have hl := (yProbe hb j).le_opNorm (state hb 2)
  have hj : (j : ℕ) ≠ 2 := by omega
  have hy : yProbe hb j (state hb 2) = Complex.I • state hb j := by
    simp only [yProbe, smul_apply, sub_apply, matrixUnit_state, ite_true,
      hj, ite_false, sub_zero]
  rw [hy, norm_smul, Complex.norm_I, (state_orthonormal hb).norm_eq_one,
    (state_orthonormal hb).norm_eq_one, mul_one, mul_one] at hl
  nlinarith [norm_nonneg (yProbe hb j)]

theorem control_state {b : ℝ} (hb : 0 < b) (M : Mat2) (k : Fin 2) :
    control hb M (state hb k) = ∑ j : Fin 2, M j k • state hb j := by
  have hmode (i : Fin 2) : sourceModes hb i = state hb i := by
    fin_cases i <;> simp [sourceModes, state_zero, state_one]
  have hp : SourceSpinCorner.projection hb (state hb k) = state hb k := by
    rw [← hmode k]
    change SourceSpinCorner.corner hb 1 (sourceModes hb k) = sourceModes hb k
    rw [SourceSpinCorner.corner_mode]
    fin_cases k <;> simp [Matrix.one_apply]
  change state hb k - SourceSpinCorner.projection hb (state hb k) +
    SourceSpinCorner.corner hb M (state hb k) = _
  rw [hp, sub_self, zero_add, ← hmode k, SourceSpinCorner.corner_mode]
  simp only [hmode]

theorem control_bypass {b : ℝ} (hb : 0 < b) (M : Mat2) :
    control hb M (state hb 2) = state hb 2 := by
  apply SourceSpinCorner.control_of_orthogonal
  · simpa only [← state_zero hb] using state_inner_eq_zero hb (by decide : 0 ≠ 2)
  · simpa only [← state_one hb] using state_inner_eq_zero hb (by decide : 1 ≠ 2)

theorem control_mem {b : ℝ} (hb : 0 < b) (M : Mat2) :
    control hb M ∈ finiteSourceAlgebra hb := by
  have he (i j : Fin 2) : SourceSpinCorner.matrixUnit hb i j = matrixUnit hb i j := by
    fin_cases i <;> fin_cases j <;>
      simp [SourceSpinCorner.matrixUnit, matrixUnit, sourceModes, state_zero, state_one]
  have hc (A : Mat2) : SourceSpinCorner.corner hb A ∈ finiteSourceAlgebra hb := by
    change (∑ i, ∑ j, A i j • SourceSpinCorner.matrixUnit hb i j) ∈ finiteSourceAlgebra hb
    apply (finiteSourceAlgebra hb).sum_mem
    intro i _
    apply (finiteSourceAlgebra hb).sum_mem
    intro j _
    rw [he]
    exact (finiteSourceAlgebra hb).smul_mem (matrixUnit_mem hb i j) _
  exact (finiteSourceAlgebra hb).add_mem
    ((finiteSourceAlgebra hb).sub_mem (finiteSourceAlgebra hb).one_mem (hc 1)) (hc M)

theorem controlled_coefficients {b : ℝ} (hb : 0 < b) (M : Mat2) (j k : Fin 2) :
    inner ℂ (state hb j) (control hb M (prepared hb k)) = amplitude * M j k := by
  rw [prepared, map_smul, map_add, control_state, control_bypass]
  fin_cases j <;> fin_cases k <;>
    simp only [Fin.sum_univ_two, inner_smul_right, inner_add_right, state_inner,
      Fin.coe_ofNat_eq_mod]
  all_goals norm_num

theorem controlled_bypass_coefficient {b : ℝ} (hb : 0 < b) (M : Mat2) (k : Fin 2) :
    inner ℂ (state hb 2) (control hb M (prepared hb k)) = amplitude := by
  rw [prepared, map_smul, map_add, control_state, control_bypass]
  fin_cases k <;>
    simp only [Fin.sum_univ_two, inner_smul_right, inner_add_right, state_inner,
      Fin.coe_ofNat_eq_mod]
  all_goals norm_num

def xResponse {b : ℝ} (hb : 0 < b) (j k : Fin 2) (U : SU2) : ℂ :=
  inner ℂ (control hb U.val (prepared hb k))
    (xProbe hb j (control hb U.val (prepared hb k)))

def yResponse {b : ℝ} (hb : 0 < b) (j k : Fin 2) (U : SU2) : ℂ :=
  inner ℂ (control hb U.val (prepared hb k))
    (yProbe hb j (control hb U.val (prepared hb k)))

theorem xResponse_eq {b : ℝ} (hb : 0 < b) (j k : Fin 2) (U : SU2) :
    xResponse hb j k U = ((U.val j k).re : ℂ) := by
  have hj : inner ℂ (control hb U.val (prepared hb k)) (state hb j) =
      conj (amplitude * U.val j k) :=
    (inner_conj_symm _ _).symm.trans (congrArg conj (controlled_coefficients hb U.val j k))
  have h2 : inner ℂ (control hb U.val (prepared hb k)) (state hb 2) = conj amplitude :=
    (inner_conj_symm _ _).symm.trans
      (congrArg conj (controlled_bypass_coefficient hb U.val k))
  simp only [xResponse, xProbe, add_apply, matrixUnit_apply, inner_add_right,
    inner_smul_right, hj, h2, controlled_coefficients,
    controlled_bypass_coefficient, map_mul, amplitude_conj]
  calc
    _ = (amplitude * amplitude) * (conj (U.val j k) + U.val j k) := by ring
    _ = _ := by rw [amplitude_sq]; apply Complex.ext <;> simp; ring

theorem yResponse_eq {b : ℝ} (hb : 0 < b) (j k : Fin 2) (U : SU2) :
    yResponse hb j k U = ((U.val j k).im : ℂ) := by
  have hj : inner ℂ (control hb U.val (prepared hb k)) (state hb j) =
      conj (amplitude * U.val j k) :=
    (inner_conj_symm _ _).symm.trans (congrArg conj (controlled_coefficients hb U.val j k))
  have h2 : inner ℂ (control hb U.val (prepared hb k)) (state hb 2) = conj amplitude :=
    (inner_conj_symm _ _).symm.trans
      (congrArg conj (controlled_bypass_coefficient hb U.val k))
  simp only [yResponse, yProbe, smul_apply, sub_apply, matrixUnit_apply,
    inner_smul_right, inner_sub_right, hj, h2, controlled_coefficients,
    controlled_bypass_coefficient, map_mul, amplitude_conj]
  calc
    _ = Complex.I * (amplitude * amplitude) * (conj (U.val j k) - U.val j k) := by ring
    _ = _ := by rw [amplitude_sq]; apply Complex.ext <;> simp; ring

/-- The observable quotient of controlled processes is the full group, including its centre. -/
theorem responses_identify {b : ℝ} (hb : 0 < b) (U V : SU2)
    (hx : ∀ j k, xResponse hb j k U = xResponse hb j k V)
    (hy : ∀ j k, yResponse hb j k U = yResponse hb j k V) : U = V := by
  apply Subtype.ext
  ext j k
  apply Complex.ext
  · exact_mod_cast (xResponse_eq hb j k U).symm.trans ((hx j k).trans (xResponse_eq hb j k V))
  · exact_mod_cast (yResponse_eq hb j k U).symm.trans ((hy j k).trans (yResponse_eq hb j k V))

theorem responses_separate {b : ℝ} (hb : 0 < b) {U V : SU2} (h : U ≠ V) :
    ∃ j k, xResponse hb j k U ≠ xResponse hb j k V ∨
      yResponse hb j k U ≠ yResponse hb j k V := by
  by_contra hn
  push Not at hn
  exact h (responses_identify hb U V (fun j k => (hn j k).1) (fun j k => (hn j k).2))

/-- Coherent source observations retain the central sign of every process. -/
theorem central_sign_detectable {b : ℝ} (hb : 0 < b) (U : SU2) :
    ∃ j k,
      xResponse hb j k (Geometry.SourceSpinCentre.negativeIdentity * U) ≠ xResponse hb j k U ∨
      yResponse hb j k (Geometry.SourceSpinCentre.negativeIdentity * U) ≠ yResponse hb j k U := by
  apply responses_separate hb
  intro h
  have hc := congrArg (fun V : SU2 => V * U⁻¹) h
  have he : Geometry.SourceSpinCentre.negativeIdentity = 1 := by simpa [mul_assoc] using hc
  exact Geometry.SourceSpinCentre.negativeIdentity_ne_one he

end GeneratedFoundations.Operations.SourceCoherentObservations
