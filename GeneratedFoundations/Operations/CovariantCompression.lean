module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Abel

/-!
# Covariant compression with its orthogonal complement

An orthonormal moving readout retains both its compressed connection and
its complement. The identities concern finite-coordinate configurations;
no connection or readout is assumed as additional root data. Both original
connection/readout interference terms remain in the complete Gram response.
-/

@[expose] public section
noncomputable section
open scoped Matrix
namespace GeneratedFoundations.Operations.CovariantCompression


variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The original connection and the derivative of the readout enter together. -/
def covariantJet (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) : Matrix ι κ ℂ :=
  dR + A * R

def retainedConnection (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  Rᴴ * covariantJet R dR A

def complementConnection (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) : Matrix ι κ ℂ :=
  covariantJet R dR A - R * retainedConnection R dR A

omit [Fintype κ] [DecidableEq κ] in
theorem retainedConnection_split (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) :
    retainedConnection R dR A = Rᴴ * dR + Rᴴ * A * R := by
  simp only [retainedConnection, covariantJet, Matrix.mul_add, Matrix.mul_assoc]

omit [DecidableEq κ] in
/-- Exact reconstruction retains the orthogonal source complement. -/
theorem covariantJet_reconstruction (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) :
    R * retainedConnection R dR A + complementConnection R dR A =
      covariantJet R dR A := by
  unfold complementConnection
  abel

theorem complementConnection_orthogonal (R dR : Matrix ι κ ℂ)
    (A : Matrix ι ι ℂ) (hR : Rᴴ * R = 1) :
    Rᴴ * complementConnection R dR A = 0 := by
  simp only [complementConnection, Matrix.mul_sub, ← Matrix.mul_assoc, hR,
    Matrix.one_mul, retainedConnection, sub_self]

/-- Compression and orthogonality determine both blocks uniquely. -/
theorem covariantJet_decomposition_unique (R dR : Matrix ι κ ℂ)
    (A : Matrix ι ι ℂ) (hR : Rᴴ * R = 1)
    (a : Matrix κ κ ℂ) (b : Matrix ι κ ℂ)
    (hjet : covariantJet R dR A = R * a + b) (hb : Rᴴ * b = 0) :
    a = retainedConnection R dR A ∧ b = complementConnection R dR A := by
  have ha : retainedConnection R dR A = a := by
    rw [retainedConnection, hjet, Matrix.mul_add, ← Matrix.mul_assoc, hR, hb]
    simp
  refine ⟨ha.symm, ?_⟩
  rw [complementConnection, hjet, ha]
  abel

omit [Fintype κ] [DecidableEq κ] in
/-- Metric compatibility follows from the original connection and the
actual derivative of an orthonormal readout. -/
theorem retainedConnection_skew (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ)
    (hA : Aᴴ = -A) (hR : dRᴴ * R + Rᴴ * dR = 0) :
    (retainedConnection R dR A)ᴴ + retainedConnection R dR A = 0 := by
  rw [retainedConnection_split]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc]
  have ht := hR
  abel_nf at ht ⊢
  exact ht

/-- The full quadratic response is the retained response plus the
orthogonal complement response. Omitting the latter changes the operator. -/
theorem covariantJet_gram (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ)
    (hR : Rᴴ * R = 1) :
    (covariantJet R dR A)ᴴ * covariantJet R dR A =
      (retainedConnection R dR A)ᴴ * retainedConnection R dR A +
      (complementConnection R dR A)ᴴ * complementConnection R dR A := by
  have hb := complementConnection_orthogonal R dR A hR
  have hbt : (complementConnection R dR A)ᴴ * R = 0 := by
    simpa using congrArg Matrix.conjTranspose hb
  conv_lhs => rw [← covariantJet_reconstruction R dR A]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Rᴴ R, hR, Matrix.one_mul, hb, Matrix.mul_zero,
    ← Matrix.mul_assoc (complementConnection R dR A)ᴴ R, hbt, Matrix.zero_mul]
  simp

omit [Fintype κ] [DecidableEq κ] in
/-- Before compression the moving and original connection terms retain
both cross terms, even when their separate averages vanish. -/
theorem covariantJet_gram_expansion (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) :
    (covariantJet R dR A)ᴴ * covariantJet R dR A =
      dRᴴ * dR + dRᴴ * A * R + Rᴴ * Aᴴ * dR + Rᴴ * Aᴴ * A * R := by
  simp only [covariantJet, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

section FrameTransport

variable [DecidableEq ι]

def passiveReadoutDerivative (U dU : Matrix ι ι ℂ) (R dR : Matrix ι κ ℂ) :
    Matrix ι κ ℂ := Uᴴ * dR - Uᴴ * dU * Uᴴ * R

def passiveConnection (U dU A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Uᴴ * A * U + Uᴴ * dU

omit [Fintype κ] [DecidableEq κ] in
/-- The derivative term of the frame and that of the readout transform
together. This is the passive convention of SourceFrameConnection. -/
theorem covariantJet_passive (U dU : Matrix ι ι ℂ)
    (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    covariantJet (Uᴴ * R) (passiveReadoutDerivative U dU R dR)
      (passiveConnection U dU A) = Uᴴ * covariantJet R dR A := by
  simp only [covariantJet, passiveReadoutDerivative, passiveConnection,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ R, hU, Matrix.one_mul]
  abel

omit [Fintype κ] [DecidableEq κ] in
theorem retainedConnection_passive (U dU : Matrix ι ι ℂ)
    (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    retainedConnection (Uᴴ * R) (passiveReadoutDerivative U dU R dR)
      (passiveConnection U dU A) = retainedConnection R dR A := by
  unfold retainedConnection
  rw [covariantJet_passive U dU R dR A hU]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U Uᴴ, hU, Matrix.one_mul]

omit [DecidableEq κ] in
theorem complementConnection_passive (U dU : Matrix ι ι ℂ)
    (R dR : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    complementConnection (Uᴴ * R) (passiveReadoutDerivative U dU R dR)
      (passiveConnection U dU A) = Uᴴ * complementConnection R dR A := by
  unfold complementConnection
  rw [covariantJet_passive U dU R dR A hU,
    retainedConnection_passive U dU R dR A hU]
  simp only [Matrix.mul_sub, Matrix.mul_assoc]

end FrameTransport


/-- Projection compression is useful without selecting a basis of its range. -/
theorem projection_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (E : Matrix ι ι ℂ) (J : Matrix ι κ ℂ)
    (hE : Eᴴ = E) (hEE : E * E = E) :
    Jᴴ * J = (E * J)ᴴ * (E * J) + ((1 - E) * J)ᴴ * ((1 - E) * J) := by
  have hh : Jᴴ * E * E * J = Jᴴ * E * J := by
    rw [Matrix.mul_assoc Jᴴ E E, hEE]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    hE, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.one_mul, ← Matrix.mul_assoc]
  rw [hh]
  abel

end GeneratedFoundations.Operations.CovariantCompression
