module

public import GeneratedFoundations.Arithmetic.HistoryObservation

/-!
# The generated history--phase bundle and its actual frame changes

The base consists of the positive generated roots.  Above root `n+1` the
fibre is the existing complete history fibre times its canonical finite
phase kernel.  Phase translation and history reflection are defined on these
fibres themselves.  They commute, preserve the root, and give exact frame
cocycles.  No arbitrary bundle or transition rule is an input.

The phase average is an idempotent projection onto precisely the phase-blind
observations.  Its uniqueness follows from translation invariance and the
preserved average, not from a selected coordinate representative.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryPhaseBundle

open CompleteHistory CompleteHistoryGeometry CompleteNaturalObject

abbrev Fiber (n : ℕ) := CompleteFiber (n + 1)

abbrev Total := Σ n : ℕ, Fiber n

def root (x : Total) : ℕ := x.1 + 1

def translate {n : ℕ} (q : ZMod (n + 1)) : Fiber n ≃ Fiber n where
  toFun x := (x.1, x.2 + q)
  invFun x := (x.1, x.2 - q)
  left_inv x := by simp
  right_inv x := by simp

def reflection (n : ℕ) : Fiber n ≃ Fiber n :=
  Equiv.prodCongr (HistoryObservation.reflection (n + 1)) (Equiv.refl _)

@[simp] theorem translate_zero {n : ℕ} (x : Fiber n) : translate 0 x = x := by
  simp [translate]

theorem translate_comp {n : ℕ} (p q : ZMod (n + 1)) (x : Fiber n) :
    translate p (translate q x) = translate (q + p) x := by
  simp [translate, add_assoc]

theorem reflection_translate {n : ℕ} (q : ZMod (n + 1)) (x : Fiber n) :
    reflection n (translate q x) = translate q (reflection n x) := rfl

def transition {n : ℕ} (p q : ZMod (n + 1)) : Fiber n ≃ Fiber n := translate (q - p)

theorem transition_cocycle {n : ℕ} (p q r : ZMod (n + 1)) (x : Fiber n) :
    transition q r (transition p q x) = transition p r x := by
  simp [transition, translate]
  abel

theorem translate_faithful {n : ℕ} (p q : ZMod (n + 1))
    (hpq : translate p = translate q) : p = q := by
  let h : History (n + 1) := Classical.choice (HistoryObservation.history_nonempty _ (by omega))
  have he := congrArg (fun e : Fiber n ≃ Fiber n => (e (h, 0)).2) hpq
  simpa [translate] using he

def phaseAverage {n : ℕ} (f : Fiber n → ℝ) (h : History (n + 1)) : ℝ :=
  (∑ a : ZMod (n + 1), f (h, a)) / (n + 1 : ℝ)

def phaseProjection {n : ℕ} (f : Fiber n → ℝ) (x : Fiber n) : ℝ := phaseAverage f x.1

def PhaseInvariant {n : ℕ} (f : Fiber n → ℝ) : Prop :=
  ∀ (q : ZMod (n + 1)) (x : Fiber n), f (translate q x) = f x

theorem phaseAverage_translate {n : ℕ} (f : Fiber n → ℝ) (q : ZMod (n + 1)) :
    phaseAverage (fun x => f (translate q x)) = phaseAverage f := by
  funext h
  unfold phaseAverage
  apply congrArg (fun x : ℝ => x / (n + 1 : ℝ))
  exact Fintype.sum_equiv (Equiv.addRight q)
    (fun a => f (translate q (h, a))) (fun a => f (h, a)) (fun _ => rfl)

theorem projected_invariant {n : ℕ} (f : Fiber n → ℝ) :
    PhaseInvariant (phaseProjection f) := by
  intro q x
  rfl

theorem phaseInvariant_iff {n : ℕ} (f : Fiber n → ℝ) :
    PhaseInvariant f ↔ ∀ x, f x = f (x.1, 0) := by
  constructor
  · intro hf x
    simpa [translate] using hf x.2 (x.1, 0)
  · intro hf q x
    rw [hf (translate q x), hf x]
    rfl

theorem phaseAverage_of_invariant {n : ℕ} (f : Fiber n → ℝ) (hf : PhaseInvariant f)
    (x : Fiber n) : phaseAverage f x.1 = f x := by
  have hc : ∀ a : ZMod (n + 1), f (x.1, a) = f x := by
    intro a
    rw [(phaseInvariant_iff f).mp hf (x.1, a), (phaseInvariant_iff f).mp hf x]
  simp only [phaseAverage, hc, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  exact mul_div_cancel_left₀ _ hn

theorem phaseProjection_idempotent {n : ℕ} (f : Fiber n → ℝ) :
    phaseProjection (phaseProjection f) = phaseProjection f := by
  funext x
  exact phaseAverage_of_invariant _ (projected_invariant f) x

theorem phaseProjection_unique {n : ℕ} (f g : Fiber n → ℝ)
    (hg : PhaseInvariant g) (havg : phaseAverage g = phaseAverage f) :
    g = phaseProjection f := by
  funext x
  calc
    g x = phaseAverage g x.1 := (phaseAverage_of_invariant g hg x).symm
    _ = phaseAverage f x.1 := congrFun havg x.1
    _ = phaseProjection f x := rfl

/-- The history projection is the effective quotient of the actual phase
translations: every invariant observation factors uniquely through it. -/
theorem invariant_factorization {n : ℕ} (f : Fiber n → ℝ) (hf : PhaseInvariant f) :
    ∃! g : History (n + 1) → ℝ, ∀ x, f x = g x.1 := by
  refine ⟨fun h => f (h, 0), (phaseInvariant_iff f).mp hf, ?_⟩
  intro g hg
  funext h
  exact (hg (h, 0)).symm

def phaseResidual {n : ℕ} (f : Fiber n → ℝ) : Fiber n → ℝ :=
  fun x => f x - phaseProjection f x

theorem phaseAverage_sub {n : ℕ} (f g : Fiber n → ℝ) :
    phaseAverage (fun x => f x - g x) = fun h => phaseAverage f h - phaseAverage g h := by
  funext h
  simp only [phaseAverage, Finset.sum_sub_distrib, sub_div]

theorem phaseAverage_residual {n : ℕ} (f : Fiber n → ℝ) :
    phaseAverage (phaseResidual f) = 0 := by
  funext h
  change phaseAverage (fun x => f x - phaseProjection f x) h = 0
  rw [phaseAverage_sub]
  have hp := phaseAverage_of_invariant _ (projected_invariant f) (h, 0)
  change phaseAverage f h - phaseAverage (phaseProjection f) h = 0
  rw [hp]
  exact sub_self _

theorem retained_residual_decomposition {n : ℕ} (f : Fiber n → ℝ) :
    f = fun x => phaseProjection f x + phaseResidual f x := by
  funext x
  simp [phaseResidual]

theorem residual_zero_iff {n : ℕ} (f : Fiber n → ℝ) :
    phaseResidual f = 0 ↔ PhaseInvariant f := by
  constructor
  · intro hf
    have heq : f = phaseProjection f := by
      funext x
      have hx := congrFun hf x
      exact sub_eq_zero.mp hx
    rw [heq]
    exact projected_invariant f
  · intro hf
    funext x
    exact sub_eq_zero.mpr (phaseAverage_of_invariant f hf x).symm

def mean {n : ℕ} (f : Fiber n → ℝ) : ℝ :=
  HistoryObservation.mean (phaseAverage f)

theorem mean_translate {n : ℕ} (f : Fiber n → ℝ) (q : ZMod (n + 1)) :
    mean (fun x => f (translate q x)) = mean f := by
  rw [mean, mean, phaseAverage_translate]

theorem mean_projected {n : ℕ} (f : Fiber n → ℝ) :
    mean (phaseProjection f) = mean f := by
  unfold mean
  congr 1
  funext h
  exact phaseAverage_of_invariant _ (projected_invariant f) (h, 0)

/-- The phase density is fixed by translation invariance and the already
generated history marginal.  It is not a second choice of probability law. -/
def probability {n : ℕ} (x : Fiber n) : ℝ := flatWeight x.1 / (n + 1 : ℝ)

theorem probability_pos {n : ℕ} (x : Fiber n) : 0 < probability x :=
  div_pos (HistoryObservation.weight_pos x.1) (by positivity)

theorem probability_marginal {n : ℕ} (h : History (n + 1)) :
    (∑ a : ZMod (n + 1), probability (h, a)) = flatWeight h := by
  simp only [probability, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  exact mul_div_cancel₀ _ (by positivity)

theorem probability_total (n : ℕ) : (∑ x : Fiber n, probability x) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [probability_marginal]
  exact flatWeight_sum_one (n + 1) (by omega)

theorem probability_unique {n : ℕ} (p : Fiber n → ℝ) (hp : PhaseInvariant p)
    (hmarginal : ∀ h : History (n + 1),
      (∑ a : ZMod (n + 1), p (h, a)) = flatWeight h) : p = probability := by
  funext x
  have ha := phaseAverage_of_invariant p hp x
  change (∑ a : ZMod (n + 1), p (x.1, a)) / (n + 1 : ℝ) = p x at ha
  rw [hmarginal] at ha
  exact ha.symm

theorem mean_eq_probability_sum {n : ℕ} (f : Fiber n → ℝ) :
    mean f = ∑ x, probability x * f x := by
  rw [Fintype.sum_prod_type]
  simp only [mean, HistoryObservation.mean, phaseAverage, probability,
    Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro a _
  ring

def energy {n : ℕ} (f : Fiber n → ℝ) : ℝ := mean (fun x => f x ^ 2)

theorem projection_residual_orthogonal {n : ℕ} (f : Fiber n → ℝ) :
    mean (fun x => phaseProjection f x * phaseResidual f x) = 0 := by
  unfold mean HistoryObservation.mean phaseAverage
  apply Finset.sum_eq_zero
  intro h _
  have hz := congrFun (phaseAverage_residual f) h
  change (∑ a : ZMod (n + 1), phaseResidual f (h, a)) / (n + 1 : ℝ) = 0 at hz
  have hs : (∑ a : ZMod (n + 1), phaseResidual f (h, a)) = 0 :=
    (div_eq_zero_iff.mp hz).resolve_right (by positivity)
  simp only [phaseProjection, ← Finset.mul_sum, hs, mul_zero, zero_div]

theorem energy_decomposition {n : ℕ} (f : Fiber n → ℝ) :
    energy f = energy (phaseProjection f) + energy (phaseResidual f) := by
  have ho := projection_residual_orthogonal f
  rw [mean_eq_probability_sum] at ho
  simp only [energy, mean_eq_probability_sum, ← Finset.sum_add_distrib]
  calc
    _ = (∑ x : Fiber n, (probability x * (phaseProjection f x ^ 2 +
        phaseResidual f x ^ 2))) +
        2 * ∑ x : Fiber n, probability x * (phaseProjection f x * phaseResidual f x) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      dsimp [phaseResidual]
      ring
    _ = _ := by rw [ho]; simp [mul_add]

structure Conclusions : Prop where
  faithful_frames : ∀ {n : ℕ} (p q : ZMod (n + 1)), translate p = translate q → p = q
  cocycle : ∀ {n : ℕ} (p q r : ZMod (n + 1)) (x : Fiber n),
    transition q r (transition p q x) = transition p r x
  commuting_actions : ∀ {n : ℕ} (q : ZMod (n + 1)) (x : Fiber n),
    reflection n (translate q x) = translate q (reflection n x)
  projection : ∀ {n : ℕ} (f : Fiber n → ℝ),
    phaseProjection (phaseProjection f) = phaseProjection f
  observation_preserved : ∀ {n : ℕ} (f : Fiber n → ℝ), mean (phaseProjection f) = mean f
  effective_quotient : ∀ {n : ℕ} (f : Fiber n → ℝ), PhaseInvariant f →
    ∃! g : History (n + 1) → ℝ, ∀ x, f x = g x.1
  retained_decomposition : ∀ {n : ℕ} (f : Fiber n → ℝ),
    f = fun x => phaseProjection f x + phaseResidual f x
  residual_kernel : ∀ {n : ℕ} (f : Fiber n → ℝ), phaseAverage (phaseResidual f) = 0
  probability_normalized : ∀ n : ℕ, (∑ x : Fiber n, probability x) = 1
  probability_selected : ∀ {n : ℕ} (p : Fiber n → ℝ), PhaseInvariant p →
    (∀ h : History (n + 1), (∑ a : ZMod (n + 1), p (h, a)) = flatWeight h) →
      p = probability
  full_energy : ∀ {n : ℕ} (f : Fiber n → ℝ),
    energy f = energy (phaseProjection f) + energy (phaseResidual f)

theorem generated : Conclusions where
  faithful_frames := translate_faithful
  cocycle := transition_cocycle
  commuting_actions := reflection_translate
  projection := phaseProjection_idempotent
  observation_preserved := mean_projected
  effective_quotient := invariant_factorization
  retained_decomposition := retained_residual_decomposition
  residual_kernel := phaseAverage_residual
  probability_normalized := probability_total
  probability_selected := probability_unique
  full_energy := energy_decomposition

end GeneratedFoundations.Arithmetic.HistoryPhaseBundle
