module

public import GeneratedFoundations.Analysis.HistoryReactionOperator

/-!
# Covariance of the complete history reaction action

Reflection acts on the actual histories and interchanges both ordered child
legs of every reaction.  The reaction conductance is invariant because it is
the intensity of the reflected parent.  Reindexing the complete reaction
sum, including additive and multiplicative channels, therefore preserves the
whole action and all mixed variations.  No cross block is removed.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.HistoryReactionCovariance

open Arithmetic.CompleteHistory Arithmetic.CompleteHistoryGeometry
open HistoryReactionForm

def speciesReflection (N : ℕ) : Species N ≃ Species N where
  toFun x := ⟨x.1, reflect x.2⟩
  invFun x := ⟨x.1, reflect x.2⟩
  left_inv x := by simp [Arithmetic.HistoryObservation.reflect_involutive]
  right_inv x := by simp [Arithmetic.HistoryObservation.reflect_involutive]

def reflectReaction {N : ℕ} (e : Reaction N) : Reaction N :=
  ⟨e.1, Channel.swap e.2.1, reflect e.2.2.2, reflect e.2.2.1⟩

@[simp] theorem reflectReaction_twice {N : ℕ} (e : Reaction N) :
    reflectReaction (reflectReaction e) = e := by
  rcases e with ⟨k, c, hl, hr⟩
  rcases c with ⟨⟨op, l, r⟩, hc⟩
  change (⟨k, ⟨(op, l, r), hc⟩, reflect (reflect hl),
    reflect (reflect hr)⟩ : Reaction N) = _
  simp only [Arithmetic.HistoryObservation.reflect_involutive]

def reactionReflection (N : ℕ) : Reaction N ≃ Reaction N where
  toFun := reflectReaction
  invFun := reflectReaction
  left_inv := reflectReaction_twice
  right_inv := reflectReaction_twice

@[simp] theorem parent_reflect {N : ℕ} (e : Reaction N) :
    parent (reflectReaction e) = speciesReflection N (parent e) := rfl

@[simp] theorem left_reflect {N : ℕ} (e : Reaction N) :
    left (reflectReaction e) = speciesReflection N (right e) := rfl

@[simp] theorem right_reflect {N : ℕ} (e : Reaction N) :
    right (reflectReaction e) = speciesReflection N (left e) := rfl

@[simp] theorem conductance_reflect (alpha L : ℝ) {N : ℕ} (e : Reaction N) :
    conductance alpha L (reflectReaction e) = conductance alpha L e := by
  exact Arithmetic.HistoryObservation.intensity_reflect alpha L (parent e).2

def pullback {N : ℕ} (f : Species N → ℝ) : Species N → ℝ :=
  fun x => f (speciesReflection N x)

theorem differential_reflect {N : ℕ} (f : Species N → ℝ) (e : Reaction N) :
    differential (pullback f) e = differential f (reflectReaction e) := by
  simp only [pullback, differential, parent_reflect, left_reflect, right_reflect]
  ring

theorem form_covariant (alpha L : ℝ) {N : ℕ} (f g : Species N → ℝ) :
    form alpha L (pullback f) (pullback g) = form alpha L f g := by
  unfold form
  apply Fintype.sum_equiv (reactionReflection N)
  intro e
  simp only [reactionReflection, Equiv.coe_fn_mk, conductance_reflect,
    differential_reflect]

theorem action_covariant (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    action alpha L (pullback f) = action alpha L f := by
  exact congrArg (fun x : ℝ => x / 2) (form_covariant alpha L f f)

theorem mixed_hessian_covariant (alpha L : ℝ) {N : ℕ} (f u v : Species N → ℝ) :
    action alpha L (fun x => pullback f x + pullback u x + pullback v x) -
      action alpha L (fun x => pullback f x + pullback u x) -
      action alpha L (fun x => pullback f x + pullback v x) +
      action alpha L (pullback f) = form alpha L u v := by
  rw [action_mixed_variation, form_covariant]

structure Conclusions : Prop where
  true_channel_symmetry : ∀ {N : ℕ} (e : Reaction N), reflectReaction (reflectReaction e) = e
  complete_action : ∀ (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ),
    action alpha L (pullback f) = action alpha L f
  full_mixed_response : ∀ (alpha L : ℝ) {N : ℕ} (u v : Species N → ℝ),
    form alpha L (pullback u) (pullback v) = form alpha L u v

theorem generated : Conclusions where
  true_channel_symmetry := reflectReaction_twice
  complete_action := action_covariant
  full_mixed_response := form_covariant

end GeneratedFoundations.Analysis.HistoryReactionCovariance
