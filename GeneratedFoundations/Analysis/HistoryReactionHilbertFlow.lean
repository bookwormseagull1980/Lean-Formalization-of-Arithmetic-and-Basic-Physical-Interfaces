module

public import GeneratedFoundations.Analysis.HistoryReactionHilbert
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Evolution on all generated history coefficients

The generator is the norm-convergent complete reaction operator. Its domain
is the whole history Hilbert space. The evolution, coefficient-energy law and
cutoff limit therefore concern one fixed complete space; they are not just a
family of unrelated finite matrix exponentials.
-/

@[expose] public section

noncomputable section

open scoped Topology InnerProduct
open Filter

namespace GeneratedFoundations.Analysis.HistoryReactionHilbertFlow

open HistoryReactionHilbert

local instance : NormedAlgebra ℚ (Space →L[ℝ] Space) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

def evolution (alpha L t : ℝ) : Space →L[ℝ] Space :=
  NormedSpace.exp (t • (-operator alpha L))

def flow (alpha L t : ℝ) (f : Space) : Space := evolution alpha L t f

@[simp] theorem evolution_zero (alpha L : ℝ) : evolution alpha L 0 = 1 := by
  simp [evolution]

@[simp] theorem flow_zero (alpha L : ℝ) (f : Space) : flow alpha L 0 f = f := by
  simp [flow]

theorem evolution_add (alpha L s t : ℝ) :
    evolution alpha L (s + t) = evolution alpha L s * evolution alpha L t := by
  have hc : Commute (s • (-operator alpha L)) (t • (-operator alpha L)) :=
    by
      show (s • (-operator alpha L)) * (t • (-operator alpha L)) =
        (t • (-operator alpha L)) * (s • (-operator alpha L))
      ext f
      simp only [mul_apply_eq_comp, smul_apply, map_smul, smul_smul]
      rw [mul_comm s t]
  exact (congrArg NormedSpace.exp (add_smul s t (-operator alpha L))).trans
    (NormedSpace.exp_add_of_commute hc)

theorem flow_add (alpha L s t : ℝ) (f : Space) :
    flow alpha L (s + t) f = flow alpha L s (flow alpha L t f) := by
  unfold flow
  rw [evolution_add]
  rfl

theorem flow_hasDerivAt (alpha L t : ℝ) (f : Space) :
    HasDerivAt (fun u => flow alpha L u f)
      (-operator alpha L (flow alpha L t f)) t := by
  have h := (hasDerivAt_exp_smul_const' (-operator alpha L) t).clm_apply
    (hasDerivAt_const t f)
  simpa only [flow, evolution, mul_apply_eq_comp, neg_apply,
    ContinuousLinearMap.map_zero, add_zero] using h

def energy (f : Space) : ℝ := ‖f‖ ^ 2 / 2

theorem energy_hasDerivAt {alpha L : ℝ} (_ha : 0 < alpha) (_hL : 0 < L)
    (t : ℝ) (f : Space) :
    HasDerivAt (fun u => energy (flow alpha L u f))
      (-form alpha L (flow alpha L t f) (flow alpha L t f)) t := by
  have h := ((flow_hasDerivAt alpha L t f).norm_sq).div_const 2
  convert h using 1
  · rfl
  · simp only [form, inner_neg_right]
    ring

theorem energy_antitone {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) (f : Space) :
    Antitone (fun t => energy (flow alpha L t f)) := by
  apply antitone_of_deriv_nonpos
  · exact fun t => (energy_hasDerivAt ha hL t f).differentiableAt
  · intro t
    rw [(energy_hasDerivAt ha hL t f).deriv]
    exact neg_nonpos.mpr (form_nonneg ha hL _)

/-- The contraction factor one is independent of the number of histories.
It is not a claim of a strictly positive, cutoff-independent reaction gap. -/
theorem norm_flow_le {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    {t : ℝ} (ht : 0 ≤ t) (f : Space) : ‖flow alpha L t f‖ ≤ ‖f‖ := by
  have he := energy_antitone ha hL f ht
  change energy (flow alpha L t f) ≤ energy (flow alpha L 0 f) at he
  rw [flow_zero] at he
  dsimp [energy] at he
  nlinarith [norm_nonneg (flow alpha L t f), norm_nonneg f]

/-- The complete action has the same exact dissipation law as its finite
reaction restrictions. The full operator occurs twice before taking a norm;
none of its mixed incidence terms is replaced by a diagonal bound. -/
theorem action_hasDerivAt {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    (t : ℝ) (f : Space) :
    HasDerivAt (fun u => action alpha L (flow alpha L u f))
      (-‖operator alpha L (flow alpha L t f)‖ ^ 2) t := by
  have hf := flow_hasDerivAt alpha L t f
  have hK := (hasDerivAt_const t (operator alpha L)).clm_apply hf
  have h := (hf.inner ℝ hK).div_const 2
  have hs : inner ℝ (flow alpha L t f)
      (operator alpha L (operator alpha L (flow alpha L t f))) =
        ‖operator alpha L (flow alpha L t f)‖ ^ 2 := by
    exact ((operator_symmetric ha hL) (flow alpha L t f)
      (operator alpha L (flow alpha L t f))).symm.trans (real_inner_self_eq_norm_sq _)
  convert h using 1
  · rfl
  · simp only [zero_apply, zero_add, map_neg,
      inner_neg_left, inner_neg_right, hs, real_inner_self_eq_norm_sq]
    ring

theorem action_antitone {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) (f : Space) :
    Antitone (fun t => action alpha L (flow alpha L t f)) := by
  apply antitone_of_deriv_nonpos
  · exact fun t => (action_hasDerivAt ha hL t f).differentiableAt
  · intro t
    rw [(action_hasDerivAt ha hL t f).deriv]
    exact neg_nonpos.mpr (sq_nonneg _)

theorem action_flow_le_initial {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    {t : ℝ} (ht : 0 ≤ t) (f : Space) :
    action alpha L (flow alpha L t f) ≤ action alpha L f := by
  simpa only [flow_zero] using action_antitone ha hL f ht

theorem cutoff_evolution_tendsto {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    (t : ℝ) :
    Tendsto (fun N => NormedSpace.exp (t • (-cutoffOperator alpha L N))) atTop
      (𝓝 (evolution alpha L t)) := by
  exact NormedSpace.exp_continuous.continuousAt.tendsto.comp
    ((cutoffOperator_tendsto ha hL).neg.const_smul t)

theorem cutoff_flow_tendsto {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    (t : ℝ) (f : Space) :
    Tendsto (fun N => NormedSpace.exp (t • (-cutoffOperator alpha L N)) f) atTop
      (𝓝 (flow alpha L t f)) :=
  (continuous_eval_const f).tendsto _ |>.comp (cutoff_evolution_tendsto ha hL t)

structure Conclusions : Prop where
  semigroup : ∀ alpha L s t f,
    flow alpha L (s + t) f = flow alpha L s (flow alpha L t f)
  equation : ∀ alpha L t f,
    HasDerivAt (fun u => flow alpha L u f) (-operator alpha L (flow alpha L t f)) t
  full_dissipation : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L → ∀ t f,
    HasDerivAt (fun u => energy (flow alpha L u f))
      (-form alpha L (flow alpha L t f) (flow alpha L t f)) t
  action_dissipation : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L → ∀ t f,
    HasDerivAt (fun u => action alpha L (flow alpha L u f))
      (-‖operator alpha L (flow alpha L t f)‖ ^ 2) t
  action_nonincrease : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L → ∀ {t : ℝ}, 0 ≤ t →
    ∀ f, action alpha L (flow alpha L t f) ≤ action alpha L f
  contraction : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L → ∀ {t : ℝ}, 0 ≤ t →
    ∀ f, ‖flow alpha L t f‖ ≤ ‖f‖
  cutoff_limit : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L → ∀ t f,
    Tendsto (fun N => NormedSpace.exp (t • (-cutoffOperator alpha L N)) f) atTop
      (𝓝 (flow alpha L t f))

theorem generated : Conclusions where
  semigroup := flow_add
  equation := flow_hasDerivAt
  full_dissipation := energy_hasDerivAt
  action_dissipation := action_hasDerivAt
  action_nonincrease := action_flow_le_initial
  contraction := norm_flow_le
  cutoff_limit := cutoff_flow_tendsto

end GeneratedFoundations.Analysis.HistoryReactionHilbertFlow
