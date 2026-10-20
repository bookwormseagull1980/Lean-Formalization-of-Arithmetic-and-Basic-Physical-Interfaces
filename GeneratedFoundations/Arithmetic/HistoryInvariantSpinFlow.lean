module

public import GeneratedFoundations.Arithmetic.HistoryJointPhaseCoordinates
public import GeneratedFoundations.Operations.SourceNumberFlow

/-!
# The Gaussian number flow on every invariant history

The invariant phase fibre contains the entire history space at each of
the two right source coordinates. Its inclusion is formed from the
original phase average, and the normalized joint charge flow restricts
to the Gaussian two-state number flow on all these coefficients.
The nonzero-root condition is needed for the already specified charge
normalization. Root zero remains covered by the full phase flow.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryInvariantSpinFlow

open HistoryJointCharge HistoryJointChargeLattice
open HistoryPhaseProjection (projection residual lift HistorySpace)
open HistoryRelativePhase (scalar)
open HistoryJointPhaseCoordinates (normalizedFlow)

abbrev SpinHistories (n : ℕ) := Fin 2 → HistorySpace n

@[simp] theorem lift_at (n : ℕ) (f : HistorySpace n)
    (a : CompleteHistory.History (n + 1)) (q : ZMod (n + 1)) :
    lift n f (a, q) = f a := rfl

def sectionMap (n : ℕ) (s : Spin) : HistorySpace n →ₗ[ℂ] Space n :=
  (inclusion n s).comp (lift n)

theorem sectionMap_injective (n : ℕ) (s : Spin) :
    Function.Injective (sectionMap n s) := by
  intro f g h
  funext a
  simpa [sectionMap, inclusion] using
    congrArg (fun x : Space n => x s (a, 0)) h

theorem flow_section (n : ℕ) (r b : ℤ) (t : ℝ) (s : Spin) (f : HistorySpace n) :
    HistoryJointPhaseFlow.flow n r b t (sectionMap n s f) =
      scalar (weight n r b (false, s)) t • sectionMap n s f := by
  have hp : projection n (lift n f) = lift n f := by
    change (lift n) (((HistoryPhaseProjection.average n).comp (lift n)) f) = _
    rw [HistoryPhaseProjection.average_lift]
    rfl
  have hr : residual n (lift n f) = 0 := by
    simp [HistoryPhaseProjection.residual, hp]
  apply PiLp.ext
  intro q
  by_cases hq : q = s
  · subst q
    simp [HistoryJointPhaseFlow.flow_apply, sectionMap, inclusion, hp, hr]
  · simp [HistoryJointPhaseFlow.flow_apply, sectionMap, inclusion, hq]

def spinInclusion (n : ℕ) : SpinHistories n →ₗ[ℂ] Space n :=
  ∑ i : Fin 2, (sectionMap n (.inr i)).comp (LinearMap.proj i)

theorem spinInclusion_apply (n : ℕ) (x : SpinHistories n) :
    spinInclusion n x = sectionMap n (.inr 0) (x 0) +
      sectionMap n (.inr 1) (x 1) := by
  simp [spinInclusion, Fin.sum_univ_two]

theorem spinInclusion_injective (n : ℕ) : Function.Injective (spinInclusion n) := by
  intro x y h
  funext i a
  have hi := congrArg (fun z : Space n => z (.inr i) (a, 0)) h
  fin_cases i <;> simpa [spinInclusion_apply, sectionMap, inclusion] using hi

def numberAction (n : ℕ) (t : ℝ) (x : SpinHistories n) : SpinHistories n :=
  fun i => ∑ j, Operations.SourceNumberFlow.numberFlowMatrix t i j • x j

theorem normalized_upper (n : ℕ) (t : ℝ) (f : HistorySpace n) :
    normalizedFlow n t (sectionMap n (.inr 0) f) = sectionMap n (.inr 0) f := by
  rw [normalizedFlow, flow_section]
  simp [scalar, weight, relativeWeight, rightWeight, Operations.FinitePhaseFlow.phase]

theorem normalized_lower {n : ℕ} (hn : 0 < n) (t : ℝ) (f : HistorySpace n) :
    normalizedFlow n t (sectionMap n (.inr 1) f) =
      Complex.exp (-Complex.I * (t : ℂ)) • sectionMap n (.inr 1) f := by
  rw [normalizedFlow, flow_section]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : scalar (weight n n 1 (false, .inr 1)) (t / (2 * n)) =
      Complex.exp (-Complex.I * (t : ℂ)) := by
    unfold scalar Operations.FinitePhaseFlow.phase
    congr 1
    simp only [weight, rightWeight, relativeWeight]
    push_cast
    field_simp [hn']
    ring
  rw [hs]

/-- The comparison retains both source coordinates at every history. -/
theorem normalizedFlow_numberAction {n : ℕ} (hn : 0 < n) (t : ℝ)
    (x : SpinHistories n) :
    normalizedFlow n t (spinInclusion n x) =
      spinInclusion n (numberAction n t x) := by
  rw [spinInclusion_apply, map_add, normalized_upper, normalized_lower hn,
    spinInclusion_apply]
  simp [numberAction, Operations.SourceNumberFlow.numberFlowMatrix,
    Fin.sum_univ_two, map_smul]

structure Conclusions : Prop where
  all_histories_retained : ∀ n, Function.Injective (spinInclusion n)
  original_number_flow : ∀ n, 0 < n → ∀ t x,
    normalizedFlow n t (spinInclusion n x) = spinInclusion n (numberAction n t x)
  invariant_upper : ∀ n t f,
    normalizedFlow n t (sectionMap n (.inr 0) f) = sectionMap n (.inr 0) f

theorem generated : Conclusions where
  all_histories_retained := spinInclusion_injective
  original_number_flow := fun _ hn => normalizedFlow_numberAction hn
  invariant_upper := normalized_upper

end GeneratedFoundations.Arithmetic.HistoryInvariantSpinFlow
