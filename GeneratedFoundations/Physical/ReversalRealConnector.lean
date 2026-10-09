module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Classification of the two-dimensional reversal-real matrix equation

The equation `h J = J h`, with `J v = epsilon * conjugate v`, classifies
arbitrary complex two-by-two matrices by a unique complex doublet through
a real-linear equivalence.  The two matrix columns are related by the
pseudoreal structure, whose antilinear map squares to `-1`, and do not
supply independent doublet coordinates.
-/

@[expose] public section

namespace GeneratedFoundations.Physical.ReversalRealConnector

abbrev Spinor := Fin 2 → ℂ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def epsilon : Mat2 := !![0, 1; -1, 0]

def conjugateMatrix (h : Mat2) : Mat2 := fun i j => star (h i j)

def reversal (v : Spinor) : Spinor := ![star (v 1), -star (v 0)]

def ReversalReal (h : Mat2) : Prop :=
  ∀ v : Spinor, h.mulVec (reversal v) = reversal (h.mulVec v)

def canonicalMatrix (a b : ℂ) : Mat2 := !![a, b; -star b, star a]

def connectorOfDoublet (H : Spinor) : Mat2 :=
  !![star (H 1), H 0; -star (H 0), H 1]

def doubletOfMatrix (h : Mat2) : Spinor := fun i => h i 1

theorem reversal_eq_epsilon_mulVec (v : Spinor) :
    reversal v = epsilon.mulVec (fun i => star (v i)) := by
  ext i
  fin_cases i <;> simp [reversal, epsilon, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem reversal_add (v w : Spinor) : reversal (v + w) = reversal v + reversal w := by
  ext i
  fin_cases i <;> simp [reversal]
  all_goals ring

theorem reversal_smul (c : ℂ) (v : Spinor) :
    reversal (c • v) = star c • reversal v := by
  ext i
  fin_cases i <;> simp [reversal, smul_eq_mul]

theorem reversal_square (v : Spinor) : reversal (reversal v) = -v := by
  ext i
  fin_cases i <;> simp [reversal]

theorem reversalReal_iff_entries (h : Mat2) :
    ReversalReal h ↔ h 1 0 = -star (h 0 1) ∧ h 1 1 = star (h 0 0) := by
  constructor
  · intro hr
    have h0 := congrFun (hr ![1, 0]) 0
    have h1 := congrFun (hr ![1, 0]) 1
    simp [reversal, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    constructor
    · have hc := congrArg (fun z : ℂ => star z) h0
      simpa using hc.symm
    · exact h1
  · rintro ⟨hc, hd⟩ v
    ext i
    fin_cases i <;>
      simp [reversal, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc, hd]
    all_goals ring

theorem matrixReality_iff_entries (h : Mat2) :
    h * epsilon = epsilon * conjugateMatrix h ↔
      h 1 0 = -star (h 0 1) ∧ h 1 1 = star (h 0 0) := by
  constructor
  · intro hr
    have hc := congrArg (fun m : Mat2 => m 1 1) hr
    have hd := congrArg (fun m : Mat2 => m 1 0) hr
    constructor
    · simpa [epsilon, conjugateMatrix, Matrix.mul_apply, Fin.sum_univ_two] using hc
    · simpa [epsilon, conjugateMatrix, Matrix.mul_apply, Fin.sum_univ_two] using hd
  · rintro ⟨hc, hd⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [epsilon, conjugateMatrix, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]

theorem reversalReal_iff_matrixReality (h : Mat2) :
    ReversalReal h ↔ h * epsilon = epsilon * conjugateMatrix h := by
  exact (reversalReal_iff_entries h).trans (matrixReality_iff_entries h).symm

theorem canonicalMatrix_reversalReal (a b : ℂ) : ReversalReal (canonicalMatrix a b) := by
  rw [reversalReal_iff_entries]
  simp [canonicalMatrix]

theorem canonicalMatrix_injective :
    Function.Injective (fun p : ℂ × ℂ => canonicalMatrix p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · have h := congrArg (fun m : Mat2 => m 0 0) hpq
    simpa [canonicalMatrix] using h
  · have h := congrArg (fun m : Mat2 => m 0 1) hpq
    simpa [canonicalMatrix] using h

theorem reversalReal_iff_existsUnique_parameters (h : Mat2) :
    ReversalReal h ↔ ∃! p : ℂ × ℂ, h = canonicalMatrix p.1 p.2 := by
  constructor
  · intro hr
    obtain ⟨hc, hd⟩ := (reversalReal_iff_entries h).mp hr
    have hform : h = canonicalMatrix (h 0 0) (h 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [canonicalMatrix, hc, hd]
    refine ⟨(h 0 0, h 0 1), hform, ?_⟩
    intro p hp
    apply canonicalMatrix_injective
    exact hp.symm.trans hform
  · rintro ⟨p, hp, _⟩
    rw [hp]
    exact canonicalMatrix_reversalReal p.1 p.2

theorem connectorOfDoublet_reversalReal (H : Spinor) :
    ReversalReal (connectorOfDoublet H) := by
  rw [reversalReal_iff_entries]
  simp [connectorOfDoublet]

@[simp] theorem connectorOfDoublet_secondColumn (H : Spinor) (i : Fin 2) :
    connectorOfDoublet H i 1 = H i := by
  fin_cases i <;> rfl

theorem connectorOfDoublet_firstColumn (H : Spinor) :
    (fun i => connectorOfDoublet H i 0) = reversal H := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem doubletOfMatrix_connectorOfDoublet (H : Spinor) :
    doubletOfMatrix (connectorOfDoublet H) = H := by
  ext i
  exact connectorOfDoublet_secondColumn H i

theorem connectorOfDoublet_doubletOfMatrix (h : Mat2) (hr : ReversalReal h) :
    connectorOfDoublet (doubletOfMatrix h) = h := by
  obtain ⟨hc, hd⟩ := (reversalReal_iff_entries h).mp hr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [connectorOfDoublet, doubletOfMatrix, hc, hd]

theorem connectorOfDoublet_injective : Function.Injective connectorOfDoublet := by
  intro H K h
  have hc := congrArg doubletOfMatrix h
  simpa using hc

theorem reversalReal_iff_existsUnique_doublet (h : Mat2) :
    ReversalReal h ↔ ∃! H : Spinor, h = connectorOfDoublet H := by
  constructor
  · intro hr
    refine ⟨doubletOfMatrix h, (connectorOfDoublet_doubletOfMatrix h hr).symm, ?_⟩
    intro H hH
    have hc := congrArg doubletOfMatrix hH
    simpa using hc.symm
  · rintro ⟨H, hH, _⟩
    rw [hH]
    exact connectorOfDoublet_reversalReal H

theorem connectorOfDoublet_add (H K : Spinor) :
    connectorOfDoublet (H + K) = connectorOfDoublet H + connectorOfDoublet K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [connectorOfDoublet]
  all_goals ring

theorem connectorOfDoublet_real_smul (r : ℝ) (H : Spinor) :
    connectorOfDoublet (r • H) = r • connectorOfDoublet H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [connectorOfDoublet]

def reversalRealSubmodule : Submodule ℝ Mat2 where
  carrier := {h | ReversalReal h}
  zero_mem' := by
    change ReversalReal 0
    rw [reversalReal_iff_entries]
    simp
  add_mem' := by
    intro h k hh hk
    obtain ⟨hc, hd⟩ := (reversalReal_iff_entries h).mp hh
    obtain ⟨kc, kd⟩ := (reversalReal_iff_entries k).mp hk
    change ReversalReal (h + k)
    rw [reversalReal_iff_entries]
    constructor
    · change h 1 0 + k 1 0 = -star (h 0 1 + k 0 1)
      simp [hc, kc]
      ring
    · change h 1 1 + k 1 1 = star (h 0 0 + k 0 0)
      simp [hd, kd]
  smul_mem' := by
    intro r h hh
    obtain ⟨hc, hd⟩ := (reversalReal_iff_entries h).mp hh
    change ReversalReal (r • h)
    rw [reversalReal_iff_entries]
    constructor
    · change r • h 1 0 = -star (r • h 0 1)
      simp [hc]
    · change r • h 1 1 = star (r • h 0 0)
      simp [hd]

/-- All solutions of the actual antilinear commutation equation, with the
second column as their unique complex-doublet coordinate.  The scalar field
of this equivalence is deliberately `ℝ`. -/
def doubletEquivReversalReal : Spinor ≃ₗ[ℝ] reversalRealSubmodule where
  toFun H := ⟨connectorOfDoublet H, connectorOfDoublet_reversalReal H⟩
  invFun h := doubletOfMatrix h.1
  left_inv H := doubletOfMatrix_connectorOfDoublet H
  right_inv h := by
    apply Subtype.ext
    exact connectorOfDoublet_doubletOfMatrix h.1 h.2
  map_add' H K := by
    apply Subtype.ext
    exact connectorOfDoublet_add H K
  map_smul' r H := by
    apply Subtype.ext
    exact connectorOfDoublet_real_smul r H

theorem reversalReal_finrank : Module.finrank ℝ reversalRealSubmodule = 4 := by
  rw [← doubletEquivReversalReal.finrank_eq]
  change Module.finrank ℝ (Fin 2 → ℂ) = 4
  simp [Module.finrank_pi_fintype]

end GeneratedFoundations.Physical.ReversalRealConnector
