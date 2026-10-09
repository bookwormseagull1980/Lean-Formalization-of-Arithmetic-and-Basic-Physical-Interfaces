module

public import GeneratedFoundations.Physical.SourceReversalRealConnector
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Colour-natural reversal-real connectors

An arbitrary matrix on a colour carrier tensored with a spinor carrier
commutes with the full colour matrix algebra exactly when it is the
identity on colour tensored with one uniquely determined spinor matrix.
The proof uses the colour matrix units, without imposing a tensor form
on the input matrix. Reversal reality then leaves one complex-doublet
coordinate, or equivalently one source quaternion, over the real field.

These are coordinate classification statements. Applying them to the
pre-exchange source carrier also requires its independent responses to
generate the full colour algebra and a specified carrier identification.
No charge assignment or global gauge-group identification is used here.
-/

@[expose] public section

noncomputable section

open scoped Quaternion Kronecker
open GeneratedFoundations.Physical.ReversalRealConnector
open GeneratedFoundations.Physical.SourceReversalRealConnector
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude (matrixMap matrixMap_injective)

namespace GeneratedFoundations.Physical.ColourNaturalConnector

abbrev Index (d : ℕ) := Fin d × Fin 2
abbrev ColourMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev Connector (d : ℕ) := Matrix (Index d) (Index d) ℂ
abbrev Carrier (d : ℕ) := Index d → ℂ

def colourAction {d : ℕ} (A : ColourMatrix d) : Connector d := A ⊗ₖ (1 : Mat2)

def spinLift (d : ℕ) (h : Mat2) : Connector d := (1 : ColourMatrix d) ⊗ₖ h

def block {d : ℕ} (T : Connector d) (a b : Fin d) : Mat2 :=
  fun i j => T (a, i) (b, j)

/-- Naturality is imposed on an arbitrary connector, before its form is determined. -/
def Natural {d : ℕ} (T : Connector d) : Prop :=
  ∀ A : ColourMatrix d, T * colourAction A = colourAction A * T

def UnitNatural {d : ℕ} (T : Connector d) : Prop :=
  ∀ a b : Fin d,
    T * colourAction (Matrix.single a b 1) = colourAction (Matrix.single a b 1) * T

theorem natural_unitNatural {d : ℕ} {T : Connector d} (hT : Natural T) :
    UnitNatural T := fun a b => hT (Matrix.single a b 1)

theorem mul_colourUnit_apply {d : ℕ} (T : Connector d)
    (p q a b : Fin d) (i j : Fin 2) :
    (T * colourAction (Matrix.single p q 1)) (a, i) (b, j) =
      if b = q then T (a, i) (p, j) else 0 := by
  classical
  by_cases hb : b = q
  · subst b
    simp [colourAction, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.single_apply, Matrix.one_apply, mul_ite]
  · simp [colourAction, Matrix.mul_apply, Matrix.one_apply, mul_ite, hb, Ne.symm hb]

theorem colourUnit_mul_apply {d : ℕ} (T : Connector d)
    (p q a b : Fin d) (i j : Fin 2) :
    (colourAction (Matrix.single p q 1) * T) (a, i) (b, j) =
      if a = p then T (q, i) (b, j) else 0 := by
  classical
  by_cases ha : a = p
  · subst a
    simp [colourAction, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.single_apply, Matrix.one_apply, mul_ite, ite_mul]
  · simp [colourAction, Matrix.mul_apply, Matrix.one_apply, mul_ite, ha, Ne.symm ha]

theorem unitNatural_offDiagonal {d : ℕ} {T : Connector d} (hT : UnitNatural T)
    {a b : Fin d} (hab : a ≠ b) : block T a b = 0 := by
  ext i j
  have h := congrArg (fun M : Connector d => M (a, i) (b, j)) (hT b b)
  simpa [mul_colourUnit_apply, colourUnit_mul_apply, block, hab] using h

theorem unitNatural_diagonal_eq {d : ℕ} {T : Connector d} (hT : UnitNatural T)
    (a b : Fin d) : block T a a = block T b b := by
  ext i j
  have h := congrArg (fun M : Connector d => M (a, i) (b, j)) (hT a b)
  simpa [mul_colourUnit_apply, colourUnit_mul_apply, block] using h

@[simp] theorem block_spinLift_same (d : ℕ) (h : Mat2) (a : Fin d) :
    block (spinLift d h) a a = h := by
  ext i j
  simp [block, spinLift]

theorem block_spinLift_ne {d : ℕ} (h : Mat2) {a b : Fin d} (hab : a ≠ b) :
    block (spinLift d h) a b = 0 := by
  ext i j
  simp [block, spinLift, hab]

theorem spinLift_natural (d : ℕ) (h : Mat2) : Natural (spinLift d h) := by
  intro A
  simp only [spinLift, colourAction, ← Matrix.mul_kronecker_mul, one_mul, mul_one]

theorem spinLift_injective (d : ℕ) [NeZero d] : Function.Injective (spinLift d) := by
  intro h k hhk
  have heq := congrArg (fun T : Connector d => block T 0 0) hhk
  simpa only [block_spinLift_same] using heq

/-- Matrix-unit naturality forces equal diagonal blocks and zero off-diagonal blocks. -/
theorem unitNatural_eq_spinLift {d : ℕ} [NeZero d] {T : Connector d}
    (hT : UnitNatural T) : T = spinLift d (block T 0 0) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    have h := congrArg (fun M : Mat2 => M i j) (unitNatural_diagonal_eq hT a 0)
    simpa only [block, spinLift, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul]
      using h
  · have h := congrArg (fun M : Mat2 => M i j) (unitNatural_offDiagonal hT hab)
    simpa [block, spinLift, Matrix.one_apply, hab] using h

theorem natural_iff_unitNatural {d : ℕ} [NeZero d] (T : Connector d) :
    Natural T ↔ UnitNatural T := by
  constructor
  · exact natural_unitNatural
  · intro hT
    rw [unitNatural_eq_spinLift hT]
    exact spinLift_natural d _

theorem natural_iff_existsUnique_spinor {d : ℕ} [NeZero d] (T : Connector d) :
    Natural T ↔ ∃! h : Mat2, T = spinLift d h := by
  constructor
  · intro hT
    have heq := unitNatural_eq_spinLift (natural_unitNatural hT)
    refine ⟨block T 0 0, heq, ?_⟩
    intro h hh
    apply spinLift_injective d
    exact hh.symm.trans heq
  · rintro ⟨h, rfl, _⟩
    exact spinLift_natural d h

def colourReversal {d : ℕ} (v : Carrier d) : Carrier d :=
  fun p => reversal (fun j => v (p.1, j)) p.2

theorem colourReversal_square {d : ℕ} (v : Carrier d) :
    colourReversal (colourReversal v) = -v := by
  ext ⟨a, i⟩
  exact congrFun (reversal_square (fun j => v (a, j))) i

def ReversalRealOnColours {d : ℕ} (T : Connector d) : Prop :=
  ∀ v : Carrier d, T.mulVec (colourReversal v) = colourReversal (T.mulVec v)

theorem spinLift_mulVec (d : ℕ) (h : Mat2) (v : Carrier d) (a : Fin d) (i : Fin 2) :
    (spinLift d h).mulVec v (a, i) = h.mulVec (fun j => v (a, j)) i := by
  simp [spinLift, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.one_apply, ite_mul]

theorem spinLift_reversalReal_iff (d : ℕ) [NeZero d] (h : Mat2) :
    ReversalRealOnColours (spinLift d h) ↔ ReversalReal h := by
  constructor
  · intro hr v
    have hv := hr (fun p => v p.2)
    ext i
    have hi := congrFun hv (0, i)
    simpa only [colourReversal, spinLift_mulVec] using hi
  · intro hr v
    ext ⟨a, i⟩
    simpa only [colourReversal, spinLift_mulVec] using
      congrFun (hr (fun j => v (a, j))) i

/-- The full antilinear equation reduces to the same two entry relations in every colour. -/
theorem natural_reversalReal_iff_entries {d : ℕ} [NeZero d] {T : Connector d}
    (hT : Natural T) :
    ReversalRealOnColours T ↔
      ∀ a : Fin d,
        T (a, 1) (a, 0) = -star (T (a, 0) (a, 1)) ∧
        T (a, 1) (a, 1) = star (T (a, 0) (a, 0)) := by
  obtain ⟨h, rfl, _⟩ := (natural_iff_existsUnique_spinor T).mp hT
  rw [spinLift_reversalReal_iff]
  simp only [spinLift, Matrix.kronecker_apply,
    Matrix.one_apply_eq, one_mul]
  constructor
  · intro hr a
    exact (reversalReal_iff_entries h).mp hr
  · intro hr
    exact (reversalReal_iff_entries h).mpr (hr 0)

theorem natural_reversalReal_iff_unique_doublet {d : ℕ} [NeZero d] (T : Connector d) :
    Natural T ∧ ReversalRealOnColours T ↔
      ∃! H : Spinor, T = spinLift d (connectorOfDoublet H) := by
  constructor
  · rintro ⟨hn, hr⟩
    obtain ⟨h, hT, _⟩ := (natural_iff_existsUnique_spinor T).mp hn
    have hh : ReversalReal h := (spinLift_reversalReal_iff d h).mp (hT ▸ hr)
    obtain ⟨H, hH, _⟩ := (reversalReal_iff_existsUnique_doublet h).mp hh
    have hTH : T = spinLift d (connectorOfDoublet H) := hT.trans (congrArg (spinLift d) hH)
    refine ⟨H, hTH, ?_⟩
    intro K hK
    apply connectorOfDoublet_injective
    apply spinLift_injective d
    exact hK.symm.trans hTH
  · rintro ⟨H, rfl, _⟩
    exact ⟨spinLift_natural d _,
      (spinLift_reversalReal_iff d _).mpr (connectorOfDoublet_reversalReal H)⟩

theorem natural_reversalReal_iff_unique_quaternion {d : ℕ} [NeZero d] (T : Connector d) :
    Natural T ∧ ReversalRealOnColours T ↔
      ∃! q : ℍ, T = spinLift d (matrixMap q) := by
  constructor
  · rintro ⟨hn, hr⟩
    obtain ⟨h, hT, _⟩ := (natural_iff_existsUnique_spinor T).mp hn
    have hh : ReversalReal h := (spinLift_reversalReal_iff d h).mp (hT ▸ hr)
    obtain ⟨q, hq, _⟩ := (reversalReal_iff_unique_sourceAmplitude h).mp hh
    have hTq : T = spinLift d (matrixMap q) := hT.trans (congrArg (spinLift d) hq.symm)
    refine ⟨q, hTq, ?_⟩
    intro p hp
    apply matrixMap_injective
    apply spinLift_injective d
    exact hp.symm.trans hTq
  · rintro ⟨q, rfl, _⟩
    exact ⟨spinLift_natural d _, (spinLift_reversalReal_iff d _).mpr (matrixMap_reversalReal q)⟩

def doubletConnector (d : ℕ) : Spinor →ₗ[ℝ] Connector d where
  toFun H := spinLift d (connectorOfDoublet H)
  map_add' H K := by
    rw [connectorOfDoublet_add]
    exact Matrix.kronecker_add _ _ _
  map_smul' r H := by
    rw [connectorOfDoublet_real_smul]
    exact Matrix.kronecker_smul r _ _

theorem doubletConnector_injective (d : ℕ) [NeZero d] :
    Function.Injective (doubletConnector d) :=
  (spinLift_injective d).comp connectorOfDoublet_injective

def elementarySpace (d : ℕ) : Submodule ℝ (Connector d) := (doubletConnector d).range

theorem mem_elementarySpace_iff (d : ℕ) [NeZero d] (T : Connector d) :
    T ∈ elementarySpace d ↔ Natural T ∧ ReversalRealOnColours T := by
  constructor
  · rintro ⟨H, hH⟩
    change spinLift d (connectorOfDoublet H) = T at hH
    rw [← hH]
    exact ⟨spinLift_natural d _,
      (spinLift_reversalReal_iff d _).mpr (connectorOfDoublet_reversalReal H)⟩
  · intro hT
    obtain ⟨H, hH, _⟩ := (natural_reversalReal_iff_unique_doublet T).mp hT
    exact ⟨H, hH.symm⟩

def doubletEquivElementary (d : ℕ) [NeZero d] : Spinor ≃ₗ[ℝ] elementarySpace d :=
  LinearEquiv.ofInjective (doubletConnector d) (doubletConnector_injective d)

theorem elementarySpace_finrank (d : ℕ) [NeZero d] :
    Module.finrank ℝ (elementarySpace d) = 4 := by
  rw [← (doubletEquivElementary d).finrank_eq]
  change Module.finrank ℝ (Fin 2 → ℂ) = 4
  simp [Module.finrank_pi_fintype]

end GeneratedFoundations.Physical.ColourNaturalConnector
