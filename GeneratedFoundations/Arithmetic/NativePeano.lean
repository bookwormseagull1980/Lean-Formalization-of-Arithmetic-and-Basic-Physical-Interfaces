module

public import GeneratedFoundations.Arithmetic.NativeModes

/-!
# Recursion on circle modes

Recursion is unique for the constant mode and modulation successor. The index
map is introduced after the pointwise and compositional operations.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.NativeModes

def index (u : Mode) : ℕ := Classical.choose (powerMode_surjective u)

@[simp] theorem powerMode_index (u : Mode) : powerMode (index u) = u :=
  Classical.choose_spec (powerMode_surjective u)

@[simp] theorem index_powerMode (n : ℕ) : index (powerMode n) = n :=
  powerMode_injective (powerMode_index _)

@[simp] theorem index_zero : index 0 = 0 := by
  simpa using index_powerMode 0

@[simp] theorem index_successor (u : Mode) : index (successor u) = index u + 1 := by
  obtain ⟨n, rfl⟩ := powerMode_surjective u
  simp

def fold {X : Type*} (xzero : X) (step : X → X) (u : Mode) : X :=
  Nat.rec xzero (fun _ x => step x) (index u)

@[simp] theorem fold_zero {X : Type*} (xzero : X) (step : X → X) :
    fold xzero step 0 = xzero := by simp [fold]

@[simp] theorem fold_successor {X : Type*} (xzero : X) (step : X → X) (u : Mode) :
    fold xzero step (successor u) = step (fold xzero step u) := by simp [fold]

theorem recursion_existsUnique {X : Type*} (xzero : X) (step : X → X) :
    ∃! f : Mode → X, f 0 = xzero ∧ ∀ u, f (successor u) = step (f u) := by
  refine ⟨fold xzero step, ⟨fold_zero _ _, fold_successor _ _⟩, ?_⟩
  intro f hf
  funext u
  apply successor_induction (P := fun u => f u = fold xzero step u) ?_ ?_ u
  · simpa using hf.1
  · intro v hv
    rw [hf.2, fold_successor, hv]

/-- Comparison with the standard natural-number semiring. -/
def powerModeEquiv : ℕ ≃+* Mode where
  toEquiv := Equiv.ofBijective powerMode ⟨powerMode_injective, powerMode_surjective⟩
  map_mul' := powerMode_mul
  map_add' := powerMode_add

@[simp] theorem powerModeEquiv_apply (n : ℕ) : powerModeEquiv n = powerMode n := rfl

theorem semiring_model_exists : Nonempty (ℕ ≃+* Mode) := ⟨powerModeEquiv⟩

theorem successor_preserving_map_unique (f : Mode → Mode)
    (hzero : f 0 = 0) (hstep : ∀ u, f (successor u) = successor (f u)) : f = id := by
  funext u
  apply successor_induction (P := fun u => f u = u) hzero ?_ u
  intro v hv
  rw [hstep, hv]

end GeneratedFoundations.Arithmetic.NativeModes
