module

public import GeneratedFoundations.Arithmetic.CompleteHistoryGeometry

/-!
# Whole-history energy transport and quotient descent

Internal node transport alone remembers the chosen expression history.  The
unit-leaf source boundary supplies the complementary energy.  Their sum
telescopes exactly to the square of the generated root, so the complete
transport, and only the complete transport in this construction, descends to
the scalar evaluation quotient.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.CompleteHistoryTransport

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.CompleteHistoryGeometry

/-- Energy carried by the unit-leaf boundary of a complete history. -/
def sourceEnergy {k : ℕ} (h : History k) : ℝ := leafCount h

/-- Sum of the local square-energy defects over every internal vertex. -/
def internalEnergy : {k : ℕ} → History k → ℝ
  | _, .one => 0
  | k, .node c hl hr =>
      internalEnergy hl + internalEnergy hr +
        (k : ℝ) ^ 2 - (c.left.1 : ℝ) ^ 2 - (c.right.1 : ℝ) ^ 2

/-- The internal defects telescope to root energy minus leaf energy. -/
theorem internalEnergy_telescope {k : ℕ} (h : History k) :
    internalEnergy h = (k : ℝ) ^ 2 - sourceEnergy h := by
  induction h with
  | one => norm_num [internalEnergy, sourceEnergy, leafCount]
  | node c hl hr ihl ihr =>
      simp only [internalEnergy, sourceEnergy, leafCount]
      rw [ihl, ihr]
      simp only [sourceEnergy]
      push_cast
      ring

/-- The leaf boundary and all internal vertex defects form one exact ledger. -/
theorem completeEnergy_eq_root_square {k : ℕ} (h : History k) :
    sourceEnergy h + internalEnergy h = (k : ℝ) ^ 2 := by
  rw [internalEnergy_telescope]
  ring

/-- Transport carried by the retained unit-leaf boundary. -/
def sourceTransport (tau : ℝ) {k : ℕ} (h : History k) : ℝ :=
  Real.exp (-tau * sourceEnergy h / 2)

/-- Transport carried by the unresolved internal vertex defects. -/
def internalTransport (tau : ℝ) {k : ℕ} (h : History k) : ℝ :=
  Real.exp (-tau * internalEnergy h / 2)

/-- Complete transport before quotienting the history fibre. -/
def completeTransport (tau : ℝ) {k : ℕ} (h : History k) : ℝ :=
  sourceTransport tau h * internalTransport tau h

/-- The unique scalar square-spectrum response at the root. -/
def rootTransport (tau : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-tau * (k : ℝ) ^ 2 / 2)

/-- After both parts of the ledger are retained, transport depends only on the
generated root and therefore descends through evaluation. -/
theorem completeTransport_descends (tau : ℝ) {k : ℕ} (h : History k) :
    completeTransport tau h = rootTransport tau k := by
  rw [completeTransport, sourceTransport, internalTransport, ← Real.exp_add]
  unfold rootTransport
  congr 1
  rw [show -tau * sourceEnergy h / 2 + -tau * internalEnergy h / 2 =
      -tau * (sourceEnergy h + internalEnergy h) / 2 by ring]
  rw [completeEnergy_eq_root_square]

def witnessTwo : History 2 :=
  addHistory History.one History.one

def witnessThree : History 3 :=
  addHistory History.one witnessTwo

def witnessSixAdd : History 6 :=
  addHistory witnessThree witnessThree

def witnessSixMul : History 6 :=
  mulHistory witnessThree witnessTwo (by norm_num) (by norm_num)

@[simp] theorem leafCount_witnessSixAdd : leafCount witnessSixAdd = 6 := by
  norm_num [witnessSixAdd, witnessThree, witnessTwo, addHistory, leafCount]

@[simp] theorem leafCount_witnessSixMul : leafCount witnessSixMul = 5 := by
  norm_num [witnessSixMul, witnessThree, witnessTwo, addHistory, mulHistory, leafCount]

/-- Equal scalar roots can retain different internal energy.  This witnesses
why the source boundary cannot be discarded before quotient descent. -/
theorem internalEnergy_not_root_determined :
    internalEnergy witnessSixAdd ≠ internalEnergy witnessSixMul := by
  rw [internalEnergy_telescope, internalEnergy_telescope]
  simp [sourceEnergy]

structure Conclusions : Prop where
  telescope : ∀ {k : ℕ} (h : History k),
    internalEnergy h = (k : ℝ) ^ 2 - sourceEnergy h
  complete_ledger : ∀ {k : ℕ} (h : History k),
    sourceEnergy h + internalEnergy h = (k : ℝ) ^ 2
  quotient_descent : ∀ (tau : ℝ) {k : ℕ} (h : History k),
    completeTransport tau h = rootTransport tau k
  unresolved_history_witness :
    ∃ h₁ h₂ : History 6, internalEnergy h₁ ≠ internalEnergy h₂

theorem completeHistoryTransportConclusions : Conclusions where
  telescope := internalEnergy_telescope
  complete_ledger := completeEnergy_eq_root_square
  quotient_descent := completeTransport_descends
  unresolved_history_witness :=
    ⟨witnessSixAdd, witnessSixMul, internalEnergy_not_root_determined⟩

end GeneratedFoundations.Arithmetic.CompleteHistoryTransport
