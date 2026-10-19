module

public import GeneratedFoundations.Analysis.HistoryReactionFlow
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# The complete Gaussian history-reaction operator

The coefficient Hilbert space contains every generated ordered history. Each
actual assembly contributes its three-leg incidence vector, with both child
multiplicities retained. Its rank-one operator is weighted by the same parent
Gaussian intensity as the finite action. The full operator is their sum, not
a diagonal substitute and not the separate reflection-exchange evolution.

The persistent conditional history law sums to one on each root fibre. Thus
the norm of the entire root layer is at most nine times its Gaussian root
mass, independently of how many histories occur in that fibre. At every
positive Gaussian observation scale the layers are absolutely summable in
operator norm. This gives a bounded operator on the complete Hilbert space
and a genuine norm limit of the finite root-layer operators.

The positive Gaussian width and strength below are observation coordinates
of the already generated source. No extra rate, spectral gap or operator is
supplied to the construction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProduct Topology
open Filter

namespace GeneratedFoundations.Analysis.HistoryReactionHilbert

open Arithmetic.CompleteHistory

abbrev AllSpecies := Σ k : ℕ, History k

abbrev Assembly (k : ℕ) := Σ c : Channel k,
  History c.left.val × History c.right.val

abbrev Space := lp (fun _ : AllSpecies => ℝ) 2

def parent {k : ℕ} (e : Assembly k) : AllSpecies :=
  ⟨k, .node e.1 e.2.1 e.2.2⟩

def left {k : ℕ} (e : Assembly k) : AllSpecies := ⟨e.1.left.val, e.2.1⟩

def right {k : ℕ} (e : Assembly k) : AllSpecies := ⟨e.1.right.val, e.2.2⟩

def basisVector (s : AllSpecies) : Space := by
  classical
  exact lp.single 2 s 1

def incidenceVector {k : ℕ} (e : Assembly k) : Space :=
  basisVector (parent e) - basisVector (left e) - basisVector (right e)

def conductance (alpha L : ℝ) {k : ℕ} (e : Assembly k) : ℝ :=
  flatGaussianIntensity alpha L (parent e).2

def differential (f : Space) {k : ℕ} (e : Assembly k) : ℝ :=
  f (parent e) - f (left e) - f (right e)

def layer (alpha L : ℝ) (k : ℕ) : Space →L[ℝ] Space :=
  ∑ e : Assembly k, conductance alpha L e •
    InnerProductSpace.rankOne ℝ (incidenceVector e) (incidenceVector e)

theorem history_value_pos {k : ℕ} (h : History k) : 0 < k := by
  cases h with
  | one => omega
  | node c _ _ => exact Nat.zero_lt_of_lt c.left_lt

@[simp] theorem norm_basisVector (s : AllSpecies) : ‖basisVector s‖ = 1 := by
  classical
  simp [basisVector, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

@[simp] theorem inner_basisVector (s : AllSpecies) (f : Space) :
    inner ℝ (basisVector s) f = f s := by
  classical
  simp [basisVector, lp.inner_single_left]

theorem inner_incidenceVector {k : ℕ} (e : Assembly k) (f : Space) :
    inner ℝ (incidenceVector e) f = differential f e := by
  simp [incidenceVector, inner_sub_left, differential]

theorem norm_incidenceVector_le {k : ℕ} (e : Assembly k) :
    ‖incidenceVector e‖ ≤ 3 := by
  calc
    _ ≤ ‖basisVector (parent e) - basisVector (left e)‖ +
        ‖basisVector (right e)‖ := norm_sub_le _ _
    _ ≤ (‖basisVector (parent e)‖ + ‖basisVector (left e)‖) +
        ‖basisVector (right e)‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ = 3 := by simp only [norm_basisVector]; norm_num

theorem conductance_pos (alpha L : ℝ) {k : ℕ} (e : Assembly k) :
    0 < conductance alpha L e :=
  HistoryTiltedBalance.flatGaussianIntensity_pos _ _ _

/-- This bound uses normalization of the actual complete history law, not
the number of histories or a separately chosen capacity. -/
theorem conductance_sum_le (alpha L : ℝ) (k : ℕ) :
    (∑ e : Assembly k, conductance alpha L e) ≤ gaussianRootMass alpha L k := by
  classical
  have hsplit : (∑ h : History k, flatGaussianIntensity alpha L h) =
      (∑ _ : PLift (k = 1), gaussianRootMass alpha L k) +
        ∑ e : Assembly k, conductance alpha L e := by
    rw [Fintype.sum_equiv (historyDecomposition k)
      (fun h => flatGaussianIntensity alpha L h)
      (fun x => flatGaussianIntensity alpha L ((historyDecomposition k).symm x))
      (fun x => congrArg (flatGaussianIntensity alpha L)
        ((historyDecomposition k).left_inv x).symm)]
    rw [Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro h _
      simp [flatGaussianIntensity]
  have hle : (∑ e : Assembly k, conductance alpha L e) ≤
      ∑ h : History k, flatGaussianIntensity alpha L h := by
    rw [hsplit]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ =>
      (gaussianRootMass_pos alpha L k).le)
  by_cases hk : 0 < k
  · simpa only [flatGaussian_pushforward alpha L k hk] using hle
  · have hz : k = 0 := by omega
    subst k
    let : IsEmpty (History 0) := ⟨fun h => by have := history_value_pos h; omega⟩
    have hzero : (∑ h : History 0, flatGaussianIntensity alpha L h) = 0 := by simp
    exact hle.trans (by rw [hzero]; exact (gaussianRootMass_pos alpha L 0).le)

theorem norm_layer_le (alpha L : ℝ) (k : ℕ) :
    ‖layer alpha L k‖ ≤ 9 * gaussianRootMass alpha L k := by
  classical
  calc
    _ ≤ ∑ e : Assembly k, ‖conductance alpha L e •
        InnerProductSpace.rankOne ℝ (incidenceVector e) (incidenceVector e)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ e : Assembly k, 9 * conductance alpha L e := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_smul, Real.norm_of_nonneg (conductance_pos alpha L e).le,
        InnerProductSpace.norm_rankOne]
      have hn := norm_incidenceVector_le e
      have hn0 := norm_nonneg (incidenceVector e)
      have hsq : ‖incidenceVector e‖ * ‖incidenceVector e‖ ≤ 9 := by nlinarith
      nlinarith [conductance_pos alpha L e]
    _ = 9 * ∑ e : Assembly k, conductance alpha L e := by rw [Finset.mul_sum]
    _ ≤ 9 * gaussianRootMass alpha L k :=
      mul_le_mul_of_nonneg_left (conductance_sum_le alpha L k) (by norm_num)

theorem summable_rootMass {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) :
    Summable (gaussianRootMass alpha L) := by
  have hc : -alpha / L ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hL)
  have hs := Real.summable_exp_nat_mul_of_ge hc
    (f := fun n => (n : ℝ) ^ 2) (fun n => by
      have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        exact_mod_cast (show n ≤ n ^ 2 by simpa only [pow_two] using Nat.le_mul_self n)
      exact hn)
  have he : gaussianRootMass alpha L =
      fun n : ℕ => Real.exp ((-alpha / L ^ 2) * (n : ℝ) ^ 2) := by
    funext n
    dsimp [gaussianRootMass]
    congr 1
    ring
  rw [he]
  exact hs

theorem summable_norm_layer {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) :
    Summable (fun k => ‖layer alpha L k‖) :=
  ((summable_rootMass ha hL).mul_left 9).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_layer_le alpha L)

theorem summable_layer {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) :
    Summable (layer alpha L) := (summable_norm_layer ha hL).of_norm

/-- The complete operator uses all actual reactions and their full incidence
vectors. Positivity and convergence are proved below for positive Gaussian
observation coordinates. -/
def operator (alpha L : ℝ) : Space →L[ℝ] Space := ∑' k, layer alpha L k

def cutoffOperator (alpha L : ℝ) (N : ℕ) : Space →L[ℝ] Space :=
  ∑ k ∈ Finset.range (N + 1), layer alpha L k

def restrict (N : ℕ) (f : Space) : HistoryReactionForm.Species N → ℝ :=
  fun s => f ⟨s.1.val, s.2⟩

theorem cutoffOperator_tendsto {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) :
    Tendsto (cutoffOperator alpha L) atTop (𝓝 (operator alpha L)) :=
  (summable_layer ha hL).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem norm_operator_le {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) :
    ‖operator alpha L‖ ≤ 9 * ∑' k, gaussianRootMass alpha L k := by
  calc
    _ ≤ ∑' k, ‖layer alpha L k‖ := norm_tsum_le_tsum_norm (summable_norm_layer ha hL)
    _ ≤ ∑' k, 9 * gaussianRootMass alpha L k :=
      (summable_norm_layer ha hL).tsum_le_tsum (norm_layer_le alpha L)
        ((summable_rootMass ha hL).mul_left 9)
    _ = _ := tsum_mul_left

/-- All mixed incidence terms remain in the layer pairing. -/
theorem inner_layer (alpha L : ℝ) (k : ℕ) (f g : Space) :
    inner ℝ f (layer alpha L k g) =
      ∑ e : Assembly k, conductance alpha L e * differential f e * differential g e := by
  classical
  simp only [layer, sum_apply, smul_apply,
    inner_sum, inner_smul_right, InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro e _
  rw [real_inner_comm (incidenceVector e) f, inner_incidenceVector,
    inner_incidenceVector]
  ring

/-- Each finite quadratic response is exactly the corresponding restriction
of the full-space cutoff. This identifies the old finite action with the
actual approximating operator, including every cross term. -/
theorem cutoff_pairing_eq_finite (alpha L : ℝ) (N : ℕ) (f g : Space) :
    inner ℝ f (cutoffOperator alpha L N g) =
      HistoryReactionForm.form alpha L (restrict N f) (restrict N g) := by
  classical
  simp only [cutoffOperator, sum_apply, inner_sum, inner_layer]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [HistoryReactionForm.form, Fintype.sum_sigma]
  rfl

def form (alpha L : ℝ) (f g : Space) : ℝ := inner ℝ f (operator alpha L g)

theorem form_eq_tsum {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) (f g : Space) :
    form alpha L f g = ∑' k, ∑ e : Assembly k,
      conductance alpha L e * differential f e * differential g e := by
  unfold form operator
  rw [tsum_apply (summable_layer ha hL) g]
  change (innerSL ℝ f) (∑' k, layer alpha L k g) = _
  rw [(innerSL ℝ f).map_tsum (summable_apply (summable_layer ha hL) g)]
  exact tsum_congr fun k => inner_layer alpha L k f g

theorem form_symm {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) (f g : Space) :
    form alpha L f g = form alpha L g f := by
  rw [form_eq_tsum ha hL, form_eq_tsum ha hL]
  apply tsum_congr
  intro k
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem form_nonneg {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) (f : Space) :
    0 ≤ form alpha L f f := by
  rw [form_eq_tsum ha hL]
  apply tsum_nonneg
  intro k
  apply Finset.sum_nonneg
  intro e _
  nlinarith [conductance_pos alpha L e, sq_nonneg (differential f e)]

theorem operator_symmetric {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) :
    (operator alpha L).IsSymmetric := by
  intro f g
  change inner ℝ (operator alpha L f) g = inner ℝ f (operator alpha L g)
  rw [real_inner_comm g (operator alpha L f)]
  exact form_symm ha hL g f

theorem operator_selfAdjoint {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) :
    IsSelfAdjoint (operator alpha L) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (operator_symmetric ha hL)

def action (alpha L : ℝ) (f : Space) : ℝ := form alpha L f f / 2

theorem action_nonneg {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) (f : Space) :
    0 ≤ action alpha L f := div_nonneg (form_nonneg ha hL f) (by norm_num)

/-- A continuous full-space pairing is the limit of precisely the root-layer
cutoffs used to construct the operator. -/
theorem cutoff_pairing_tendsto {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    (f g : Space) :
    Tendsto (fun N => inner ℝ f (cutoffOperator alpha L N g)) atTop
      (𝓝 (form alpha L f g)) :=
  (innerSL ℝ f).continuous.tendsto _ |>.comp
    ((continuous_eval_const g).tendsto _ |>.comp (cutoffOperator_tendsto ha hL))

theorem finite_form_tendsto {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    (f g : Space) :
    Tendsto (fun N => HistoryReactionForm.form alpha L (restrict N f) (restrict N g))
      atTop (𝓝 (form alpha L f g)) := by
  simpa only [cutoff_pairing_eq_finite] using cutoff_pairing_tendsto ha hL f g

structure Conclusions : Prop where
  absolute_convergence : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L →
    Summable (fun k => ‖layer alpha L k‖)
  actual_cutoff_limit : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L →
    Tendsto (cutoffOperator alpha L) atTop (𝓝 (operator alpha L))
  full_selfAdjoint : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L →
    IsSelfAdjoint (operator alpha L)
  full_positive : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L →
    ∀ f : Space, 0 ≤ form alpha L f f
  full_reaction_form : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L → ∀ f g : Space,
    form alpha L f g = ∑' k, ∑ e : Assembly k,
      conductance alpha L e * differential f e * differential g e
  finite_full_comparison : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L → ∀ f g : Space,
    Tendsto (fun N => HistoryReactionForm.form alpha L (restrict N f) (restrict N g))
      atTop (𝓝 (form alpha L f g))

theorem generated : Conclusions where
  absolute_convergence := summable_norm_layer
  actual_cutoff_limit := cutoffOperator_tendsto
  full_selfAdjoint := operator_selfAdjoint
  full_positive := form_nonneg
  full_reaction_form := form_eq_tsum
  finite_full_comparison := finite_form_tendsto

end GeneratedFoundations.Analysis.HistoryReactionHilbert
