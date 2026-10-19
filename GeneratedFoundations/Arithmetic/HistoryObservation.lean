module

public import GeneratedFoundations.Arithmetic.CompleteHistoryGeometry
public import GeneratedFoundations.Analysis.HistoryTiltedBalance

/-!
# Reflection and observations of the actual complete history source

The reference law is the previously constructed equal-channel history law.
Reflection reverses every ordered vertex; it is not an independently chosen
exchange on an auxiliary two-state carrier.  The weighted pairing, its even
and odd projections, and their exact energy decomposition are therefore
observations of that same source.  The fixed positive root is an observation
index, not a new parameter in the minimal-change datum.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryObservation

open CompleteHistory CompleteHistoryGeometry

theorem history_nonempty (k : ℕ) (hk : 0 < k) : Nonempty (History k) := by
  by_contra hn
  let : IsEmpty (History k) := not_nonempty_iff.mp hn
  have h := flatWeight_sum_one k hk
  simp at h

instance (n : ℕ) : Nonempty (History (n + 1)) :=
  history_nonempty (n + 1) (by omega)

@[simp] theorem reflect_involutive {k : ℕ} (h : History k) :
    reflect (reflect h) = h := by
  induction h with
  | one => rfl
  | node c hl hr ihl ihr =>
      rcases c with ⟨⟨op, l, r⟩, hc⟩
      change History.node ⟨(op, l, r), hc⟩ (reflect (reflect hl)) (reflect (reflect hr)) = _
      rw [ihl, ihr]

def reflection (k : ℕ) : History k ≃ History k where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_involutive
  right_inv := reflect_involutive

@[simp] theorem weight_reflect {k : ℕ} (h : History k) :
    flatWeight (reflect h) = flatWeight h := by
  induction h with
  | one => rfl
  | node c hl hr ihl ihr => simp [reflect, flatWeight, ihl, ihr, mul_comm]

theorem weight_pos {k : ℕ} (h : History k) : 0 < flatWeight h :=
  Analysis.HistoryTiltedBalance.flatWeight_pos h

@[simp] theorem intensity_reflect (alpha L : ℝ) {k : ℕ} (h : History k) :
    flatGaussianIntensity alpha L (reflect h) = flatGaussianIntensity alpha L h := by
  simp [flatGaussianIntensity]

def mean {k : ℕ} (f : History k → ℝ) : ℝ :=
  ∑ h, flatWeight h * f h

def pairing {k : ℕ} (f g : History k → ℝ) : ℝ :=
  mean (fun h => f h * g h)

def energy {k : ℕ} (f : History k → ℝ) : ℝ := pairing f f

theorem mean_add {k : ℕ} (f g : History k → ℝ) :
    mean (fun h => f h + g h) = mean f + mean g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

theorem mean_mul {k : ℕ} (c : ℝ) (f : History k → ℝ) :
    mean (fun h => c * f h) = c * mean f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem mean_const (k : ℕ) (hk : 0 < k) (c : ℝ) :
    mean (fun _ : History k => c) = c := by
  simp only [mean, ← Finset.sum_mul, flatWeight_sum_one k hk, one_mul]

theorem mean_reflect {k : ℕ} (f : History k → ℝ) :
    mean (fun h => f (reflect h)) = mean f := by
  classical
  apply (Fintype.sum_equiv (reflection k)
    (fun h => flatWeight h * f (reflect h))
    (fun h => flatWeight h * f h) ?_)
  intro h
  simp [reflection]

theorem mean_reflection_odd {k : ℕ} (f : History k → ℝ)
    (hf : ∀ h, f (reflect h) = -f h) : mean f = 0 := by
  have h := mean_reflect f
  have hn : mean (fun h => f (reflect h)) = -mean f := by
    simp [mean, hf, ← Finset.sum_neg_distrib]
  rw [hn] at h
  linarith

theorem orientation_mean_zero (k : ℕ) :
    mean (fun h : History k => (orientationScore h : ℝ)) = 0 := by
  apply mean_reflection_odd
  intro h
  simp

def evenPart {k : ℕ} (f : History k → ℝ) (h : History k) : ℝ :=
  (f h + f (reflect h)) / 2

def oddPart {k : ℕ} (f : History k → ℝ) (h : History k) : ℝ :=
  (f h - f (reflect h)) / 2

@[simp] theorem evenPart_reflect {k : ℕ} (f : History k → ℝ) (h : History k) :
    evenPart f (reflect h) = evenPart f h := by
  simp [evenPart, add_comm]

@[simp] theorem oddPart_reflect {k : ℕ} (f : History k → ℝ) (h : History k) :
    oddPart f (reflect h) = -oddPart f h := by
  simp only [oddPart, reflect_involutive]
  ring

theorem reconstruct {k : ℕ} (f : History k → ℝ) :
    (fun h => evenPart f h + oddPart f h) = f := by
  funext h
  simp only [evenPart, oddPart]
  ring

theorem evenPart_idempotent {k : ℕ} (f : History k → ℝ) :
    evenPart (evenPart f) = evenPart f := by
  funext h
  simp only [evenPart, reflect_involutive]
  ring

theorem oddPart_idempotent {k : ℕ} (f : History k → ℝ) :
    oddPart (oddPart f) = oddPart f := by
  funext h
  rw [oddPart, oddPart_reflect]
  ring

theorem pairing_even_odd {k : ℕ} (f g : History k → ℝ) :
    pairing (evenPart f) (oddPart g) = 0 := by
  apply mean_reflection_odd
  intro h
  simp

theorem energy_nonneg {k : ℕ} (f : History k → ℝ) : 0 ≤ energy f := by
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (weight_pos h).le (mul_self_nonneg (f h))

theorem energy_eq_zero_iff {k : ℕ} (f : History k → ℝ) :
    energy f = 0 ↔ f = 0 := by
  constructor
  · intro he
    funext h
    have hs : flatWeight h * (f h * f h) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun h _ => mul_nonneg (weight_pos h).le (mul_self_nonneg (f h)))).mp he h
        (Finset.mem_univ h)
    have := (mul_eq_zero.mp hs).resolve_left (ne_of_gt (weight_pos h))
    simpa using (mul_self_eq_zero.mp this)
  · rintro rfl
    simp [energy, pairing, mean]

theorem energy_decomposition {k : ℕ} (f : History k → ℝ) :
    energy f = energy (evenPart f) + energy (oddPart f) := by
  have ho := pairing_even_odd f f
  have he : energy f = energy (evenPart f) + energy (oddPart f) +
      2 * pairing (evenPart f) (oddPart f) := by
    simp only [energy, pairing, mean, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    simp only [evenPart, oddPart]
    ring
  rw [ho, mul_zero, add_zero] at he
  exact he

theorem odd_mean_zero {k : ℕ} (f : History k → ℝ) : mean (oddPart f) = 0 :=
  mean_reflection_odd _ (oddPart_reflect f)

theorem even_mean {k : ℕ} (f : History k → ℝ) : mean (evenPart f) = mean f := by
  have h := congrArg mean (reconstruct f)
  rw [mean_add, odd_mean_zero, add_zero] at h
  exact h

theorem gaussian_mean (alpha L : ℝ) {k : ℕ} (f : History k → ℝ) :
    (∑ h, flatGaussianIntensity alpha L h * f h) =
      gaussianRootMass alpha L k * mean f := by
  simp only [flatGaussianIntensity, mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem conditional_mean (alpha L : ℝ) {k : ℕ} (f : History k → ℝ) :
    (∑ h, flatGaussianIntensity alpha L h * f h) / gaussianRootMass alpha L k =
      mean f := by
  rw [gaussian_mean]
  exact mul_div_cancel_left₀ _ (ne_of_gt (gaussianRootMass_pos alpha L k))

structure Conclusions : Prop where
  source_reflection : ∀ (alpha L : ℝ) {k : ℕ} (h : History k),
    flatGaussianIntensity alpha L (reflect h) = flatGaussianIntensity alpha L h
  orientation_balance : ∀ k,
    mean (fun h : History k => (orientationScore h : ℝ)) = 0
  complete_energy : ∀ {k : ℕ} (f : History k → ℝ),
    energy f = energy (evenPart f) + energy (oddPart f)
  faithful_energy : ∀ {k : ℕ} (f : History k → ℝ), energy f = 0 ↔ f = 0

theorem generated : Conclusions where
  source_reflection := intensity_reflect
  orientation_balance := orientation_mean_zero
  complete_energy := energy_decomposition
  faithful_energy := energy_eq_zero_iff

end GeneratedFoundations.Arithmetic.HistoryObservation
