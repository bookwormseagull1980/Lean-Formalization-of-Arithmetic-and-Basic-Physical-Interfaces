module

public import GeneratedFoundations.Physical.SourceMatterCompression
public import Mathlib.Data.Matrix.Block
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matter energies and their normalization from the same finite operator

The retained and complementary coordinates are orthonormal coordinates of
one matter response. Eliminating the complement gives both the eigenvalue
equation and the norm of its lifted eigenvector. At a real energy outside
the complementary spectrum, this norm is the energy derivative of the
same reduced inverse response. It fixes the residue once the complete
operator is evaluated. No source state, coupling or finite matching
coefficient is added to the generated root.
-/

@[expose] public section
noncomputable section
open scoped Matrix ComplexOrder

namespace GeneratedFoundations.Physical.SourceMatterPoleResponse

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

/-- Finite matter response operations exported by the generated root.
The quantified matrices are configurations on its orthonormal coordinate
spaces; the inverse equations specify a resolvent domain. -/
structure Conclusions : Prop where
  lift_gram : ∀ (n r : ℕ) (W : Matrix (Fin n) (Fin r) ℂ),
    (eigenvectorLift W)ᴴ * eigenvectorLift W = 1 + Wᴴ * W
  normalization_positive : ∀ (n r : ℕ) (V : Matrix (Fin n) (Fin r) ℂ)
      (R : Matrix (Fin n) (Fin n) ℂ), (returnMetric V R).PosDef
  lifted_equation : ∀ (n r : ℕ) (A : Matrix (Fin r) (Fin r) ℂ)
      (C R : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin r) ℂ)
      (z : ℂ), (z • 1 - C) * R = 1 → ∀ u : Fin r → ℂ,
    Matrix.fromBlocks A Vᴴ V C *ᵥ (eigenvectorLift (R * V) *ᵥ u) =
        z • (eigenvectorLift (R * V) *ᵥ u) ↔
      reducedKernel A V R z *ᵥ u = 0
  inverse_difference : ∀ (n : ℕ) (C Rz Rw : Matrix (Fin n) (Fin n) ℂ)
      (z w : ℂ), Rz * (z • 1 - C) = 1 → (w • 1 - C) * Rw = 1 →
    Rz - Rw = (w - z) • (Rz * Rw)
  normalization_identity : ∀ (n r : ℕ) (V : Matrix (Fin n) (Fin r) ℂ)
      (R : Matrix (Fin n) (Fin n) ℂ), Rᴴ = R →
    returnMetric V R = 1 + Vᴴ * R * R * V
  kernel_difference : ∀ (n r : ℕ) (A : Matrix (Fin r) (Fin r) ℂ)
      (V : Matrix (Fin n) (Fin r) ℂ) (C Rz Rw : Matrix (Fin n) (Fin n) ℂ)
      (z w : ℂ), Rz * (z • 1 - C) = 1 → (w • 1 - C) * Rw = 1 →
    reducedKernel A V Rz z - reducedKernel A V Rw w =
      (z - w) • (1 + Vᴴ * Rz * Rw * V)
  complement_derivative : ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℂ) (z : ℂ),
    z ∈ resolventSet ℂ C →
      HasDerivAt (resolvent C) (-(resolvent C z) ^ 2) z
  joint_state_normalization : ∀ (n : ℕ) (S ci cj : Matrix (Fin n) (Fin n) ℂ)
      (a : ℂ), Sᴴ = S → Matrix.trace (S * S) = 1 →
      ci * cjᴴ + cjᴴ * ci = a • 1 →
    Matrix.trace ((ciᴴ * S)ᴴ * (cjᴴ * S)) +
      Matrix.trace ((S * ciᴴ)ᴴ * (S * cjᴴ)) = a

theorem generated : Conclusions where
  lift_gram := fun _ _ => eigenvectorLift_gram
  normalization_positive := fun _ _ => returnMetric_posDef
  lifted_equation := fun _ _ => eigenvectorLift_equation_iff
  inverse_difference := fun _ => complement_resolvent_difference
  normalization_identity := fun _ _ => returnMetric_eq
  kernel_difference := fun _ _ => reducedKernel_difference
  complement_derivative := fun _ => complement_resolvent_derivative
  joint_state_normalization := fun _ => jointState_car_normalization

end GeneratedFoundations.Physical.SourceMatterPoleResponse
