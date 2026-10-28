module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Resolvent compression and the norm of the reconstructed vector

All blocks are orthonormal coordinates of one finite operator. The same
complementary inverse determines the reduced equation, the full vector and
its positive return metric. The difference and derivative identities retain
the entire product of off-diagonal blocks. The last identities use both
orderings in the trace Gram of one state.

The algebraic results are shared operations; each branch must instantiate
them on its own actual carrier. Inverse equations and resolvent-set
membership specify where elimination is defined. They are not source data.
-/

@[expose] public section
noncomputable section
open scoped Matrix ComplexOrder

namespace GeneratedFoundations.Operations.BlockResolventResponse

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The inverse response after eliminating the actual complementary block. -/
def reducedKernel (A : Matrix κ κ ℂ) (V : Matrix ι κ ℂ)
    (R : Matrix ι ι ℂ) (z : ℂ) : Matrix κ κ ℂ :=
  z • 1 - A - Vᴴ * R * V

/-- A retained vector is lifted with its actual complementary amplitude. -/
def eigenvectorLift (W : Matrix ι κ ℂ) : Matrix (κ ⊕ ι) κ ℂ :=
  fun i j => Sum.elim (fun k => (1 : Matrix κ κ ℂ) k j) (fun k => W k j) i

/-- The normalization contains the complementary amplitude, with unit
coefficient, as part of the norm of the same full eigenvector. -/
def returnMetric (V : Matrix ι κ ℂ) (R : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  1 + (R * V)ᴴ * (R * V)

omit [DecidableEq ι] in
theorem eigenvectorLift_gram (W : Matrix ι κ ℂ) :
    (eigenvectorLift W)ᴴ * eigenvectorLift W = 1 + Wᴴ * W := by
  ext i j
  simp [eigenvectorLift, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

omit [DecidableEq ι] in
theorem returnMetric_posDef (V : Matrix ι κ ℂ) (R : Matrix ι ι ℂ) :
    (returnMetric V R).PosDef := by
  exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)

omit [Fintype κ] [DecidableEq ι] in
theorem returnMetric_eq (V : Matrix ι κ ℂ) (R : Matrix ι ι ℂ)
    (hR : Rᴴ = R) :
    returnMetric V R = 1 + Vᴴ * R * R * V := by
  simp only [returnMetric, Matrix.conjTranspose_mul, hR, Matrix.mul_assoc]

omit [Fintype κ] [DecidableEq κ] in
/-- Reconstruction uses the complementary block of the same operator. -/
theorem complement_reconstruction (C R : Matrix ι ι ℂ) (V : Matrix ι κ ℂ)
    (z : ℂ) (hR : (z • 1 - C) * R = 1) :
    V + C * (R * V) = z • (R * V) := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M * V) hR
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc] at h
  exact (sub_eq_iff_eq_add.mp h).symm

/-- The complete block eigenvalue equation is equivalent to the reduced
equation on the same lifted vector. No eigenvalue is chosen as input. -/
theorem eigenvectorLift_equation_iff (A : Matrix κ κ ℂ)
    (C R : Matrix ι ι ℂ) (V : Matrix ι κ ℂ) (z : ℂ)
    (hR : (z • 1 - C) * R = 1) (u : κ → ℂ) :
    Matrix.fromBlocks A Vᴴ V C *ᵥ (eigenvectorLift (R * V) *ᵥ u) =
        z • (eigenvectorLift (R * V) *ᵥ u) ↔
      reducedKernel A V R z *ᵥ u = 0 := by
  have hcomp := congrArg (fun M : Matrix ι κ ℂ => M *ᵥ u)
    (complement_reconstruction C R V z hR)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at hcomp
  have hlift : eigenvectorLift (R * V) *ᵥ u = Sum.elim u ((R * V) *ᵥ u) := by
    ext i
    cases i <;> simp [eigenvectorLift, Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [hlift, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h
    have htop := congrArg (fun v : κ ⊕ ι → ℂ => v ∘ Sum.inl) h
    change A *ᵥ u + Vᴴ *ᵥ ((R * V) *ᵥ u) = z • u at htop
    simp only [reducedKernel, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at htop ⊢
    rw [← htop]
    abel
  · intro h
    have htop : A *ᵥ u + Vᴴ *ᵥ ((R * V) *ᵥ u) = z • u := by
      simp only [← Matrix.mulVec_mulVec]
      simp only [reducedKernel, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
      rw [← sub_eq_zero.mp h]
      abel
    ext i
    cases i with
    | inl j => exact congrFun htop j
    | inr j =>
      change (V *ᵥ u + C *ᵥ ((R * V) *ᵥ u)) j = (z • ((R * V) *ᵥ u)) j
      simpa only [← Matrix.mulVec_mulVec] using congrFun hcomp j

omit [Fintype κ] [DecidableEq κ] in
/-- The resolvent difference follows from the same complementary block. -/
theorem complement_resolvent_difference (C Rz Rw : Matrix ι ι ℂ) (z w : ℂ)
    (hz : Rz * (z • 1 - C) = 1) (hw : (w • 1 - C) * Rw = 1) :
    Rz - Rw = (w - z) • (Rz * Rw) := by
  calc
    Rz - Rw = Rz * ((w • 1 - C) * Rw) - (Rz * (z • 1 - C)) * Rw := by
      rw [hz, hw, Matrix.mul_one, Matrix.one_mul]
    _ = Rz * ((w • 1 - C) - (z • 1 - C)) * Rw := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = Rz * ((w - z) • 1) * Rw := by
      congr 2
      rw [sub_smul]
      abel
    _ = (w - z) • (Rz * Rw) := by
      simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

omit [Fintype κ] in
/-- The exact energy difference of the inverse response already contains
the normalization term; its diagonal limit is the positive return metric. -/
theorem reducedKernel_difference (A : Matrix κ κ ℂ) (V : Matrix ι κ ℂ)
    (C Rz Rw : Matrix ι ι ℂ) (z w : ℂ)
    (hz : Rz * (z • 1 - C) = 1) (hw : (w • 1 - C) * Rw = 1) :
    reducedKernel A V Rz z - reducedKernel A V Rw w =
      (z - w) • (1 + Vᴴ * Rz * Rw * V) := by
  have h := complement_resolvent_difference C Rz Rw z w hz hw
  have hs : Vᴴ * Rz * V - Vᴴ * Rw * V =
      (w - z) • (Vᴴ * Rz * Rw * V) := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, h]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  calc
    reducedKernel A V Rz z - reducedKernel A V Rw w =
        (z - w) • 1 - (Vᴴ * Rz * V - Vᴴ * Rw * V) := by
      rw [reducedKernel, reducedKernel, sub_smul]
      abel
    _ = (z - w) • (1 + Vᴴ * Rz * Rw * V) := by
      rw [hs, show w - z = -(z - w) by ring, neg_smul, sub_neg_eq_add, smul_add]

open scoped Matrix.Norms.Operator

omit [Fintype κ] [DecidableEq κ] in
/-- The actual complementary resolvent has the derivative used in the
energy normalization. The condition specifies its analytic domain. -/
theorem complement_resolvent_derivative (C : Matrix ι ι ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ C) :
    HasDerivAt (resolvent C) (-(resolvent C z) ^ 2) z := by
  exact spectrum.hasDerivAt_resolvent_const_left hz

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
/-- Both CAR orderings use the same state. This is the trace Gram used
by the two-copy joint transition representation. -/
theorem jointState_gram (S ci cj : Matrix ι ι ℂ) (hS : Sᴴ = S) :
    Matrix.trace ((ciᴴ * S)ᴴ * (cjᴴ * S)) +
      Matrix.trace ((S * ciᴴ)ᴴ * (S * cjᴴ)) =
        Matrix.trace ((S * S) * (ci * cjᴴ + cjᴴ * ci)) := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS]
  rw [Matrix.mul_add, Matrix.trace_add]
  congr 1
  · rw [← Matrix.mul_assoc (S * ci) cjᴴ S,
      Matrix.trace_mul_comm (S * ci * cjᴴ) S]
    simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc ci S (S * cjᴴ),
      Matrix.trace_mul_comm ci (S * (S * cjᴴ))]
    simp only [Matrix.mul_assoc]

omit [Fintype κ] [DecidableEq κ] in
/-- The complete CAR and the unit trace of the same state fix the
equal-time normalization, including coherent stationary states. -/
theorem jointState_car_normalization (S ci cj : Matrix ι ι ℂ) (a : ℂ)
    (hS : Sᴴ = S) (htrace : Matrix.trace (S * S) = 1)
    (hcar : ci * cjᴴ + cjᴴ * ci = a • 1) :
    Matrix.trace ((ciᴴ * S)ᴴ * (cjᴴ * S)) +
      Matrix.trace ((S * ciᴴ)ᴴ * (S * cjᴴ)) = a := by
  rw [jointState_gram S ci cj hS, hcar, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, htrace, smul_eq_mul, mul_one]

/-- At a real energy the inverse of a Hermitian complementary block is
Hermitian. The inverse equation refers to that same block. -/
theorem complement_inverse_hermitian (C R : Matrix ι ι ℂ) (r : ℝ)
    (hC : Cᴴ = C)
    (hright : ((r : ℂ) • 1 - C) * R = 1) : Rᴴ = R := by
  have hadj : Rᴴ * ((r : ℂ) • 1 - C) = 1 := by
    have h := congrArg Matrix.conjTranspose hright
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, starRingEnd_apply,
      Complex.conj_ofReal, hC] using h
  calc
    Rᴴ = Rᴴ * (((r : ℂ) • 1 - C) * R) := by rw [hright, Matrix.mul_one]
    _ = (Rᴴ * ((r : ℂ) • 1 - C)) * R := (Matrix.mul_assoc _ _ _).symm
    _ = R := by rw [hadj, Matrix.one_mul]

omit [Fintype κ] [DecidableEq κ] in
/-- The derivative of the square-block reduced response is fixed by the
same resolvent; the plus sign is the complementary norm contribution. -/
theorem reducedKernel_resolvent_derivative (A C V : Matrix ι ι ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ C) :
    HasDerivAt (fun w : ℂ => reducedKernel A V (resolvent C w) w)
      (1 + Vᴴ * resolvent C z * resolvent C z * V) z := by
  have hR := complement_resolvent_derivative C z hz
  have hV := ((hasDerivAt_const z Vᴴ).mul hR).mul (hasDerivAt_const z V)
  have hZ := (hasDerivAt_id z).smul_const (1 : Matrix ι ι ℂ)
  have hF := HasDerivAt.sub (HasDerivAt.sub hZ (hasDerivAt_const z A)) hV
  change HasDerivAt (fun w : ℂ => w • 1 - A - Vᴴ * resolvent C w * V)
    ((1 • (1 : Matrix ι ι ℂ) - 0) -
      ((0 * resolvent C z + Vᴴ * (-(resolvent C z) ^ 2)) * V +
        (Vᴴ * resolvent C z) * 0)) z at hF
  simpa only [reducedKernel, one_smul, zero_mul, mul_zero, zero_add,
    add_zero, sub_zero, mul_neg, neg_mul, sub_neg_eq_add, pow_two,
    Matrix.mul_assoc] using hF

omit [Fintype κ] [DecidableEq κ] in
theorem complementary_resolvent_right (C : Matrix ι ι ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ C) :
    (z • 1 - C) * resolvent C z = 1 := by
  simpa only [resolvent, Algebra.algebraMap_eq_smul_one] using
    Ring.mul_inverse_cancel (algebraMap ℂ (Matrix ι ι ℂ) z - C) hz

omit [Fintype κ] [DecidableEq κ] in
theorem complementary_resolvent_left (C : Matrix ι ι ℂ) (z : ℂ)
    (hz : z ∈ resolventSet ℂ C) :
    resolvent C z * (z • 1 - C) = 1 := by
  simpa only [resolvent, Algebra.algebraMap_eq_smul_one] using
    Ring.inverse_mul_cancel (algebraMap ℂ (Matrix ι ι ℂ) z - C) hz

omit [Fintype κ] [DecidableEq κ] in
/-- In the real complementary resolvent domain the derivative is exactly
the norm induced by reconstructing the full eigenvector. -/
theorem reducedKernel_real_derivative (A C V : Matrix ι ι ℂ) (hC : Cᴴ = C)
    (r : ℝ) (hr : (r : ℂ) ∈ resolventSet ℂ C) :
    HasDerivAt (fun w : ℂ => reducedKernel A V (resolvent C w) w)
      (returnMetric V (resolvent C (r : ℂ))) (r : ℂ) := by
  have hR := complement_inverse_hermitian C (resolvent C (r : ℂ)) r hC
    (complementary_resolvent_right C (r : ℂ) hr)
  rw [returnMetric_eq V _ hR]
  exact reducedKernel_resolvent_derivative A C V (r : ℂ) hr

end GeneratedFoundations.Operations.BlockResolventResponse
