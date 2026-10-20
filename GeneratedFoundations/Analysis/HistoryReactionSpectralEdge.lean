module

public import GeneratedFoundations.Analysis.HistoryReactionHilbertFlow
public import GeneratedFoundations.Arithmetic.HistoryObservation
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The spectral edge of the complete Gaussian reaction operator

The complete reaction form retains every assembly and cross term. At a fixed
positive Gaussian observation scale, its finite root-layer operators converge
in operator norm. Each cutoff acts only on histories up to its root bound.
Consequently actual high-root unit states have arbitrarily small response.

This computes a difference between the two concrete branch outputs: a positive
gap in one source-field operator does not prescribe a positive gap for this
Gaussian-weighted arithmetic reaction operator. The conclusion concerns this
operator and this full coefficient norm, including the anchored subspace.
-/

@[expose] public section

noncomputable section

open scoped BigOperators InnerProduct Topology
open Filter

namespace GeneratedFoundations.Analysis.HistoryReactionSpectralEdge

open Arithmetic.CompleteHistory HistoryReactionHilbert

private theorem positive_response_norm_sq_le (S : Space →L[ℝ] Space)
    (hs : S.IsSymmetric) (hp : ∀ f, 0 ≤ inner ℝ f (S f)) (f : Space) :
    ‖S f‖ ^ 2 ≤ ‖S‖ * inner ℝ f (S f) := by
  by_cases hz : ‖S‖ = 0
  · have hS : S = 0 := norm_eq_zero.mp hz
    simp [hS]
  have hn : 0 < ‖S‖ := lt_of_le_of_ne (norm_nonneg S) (Ne.symm hz)
  have hpos := hp (S f - ‖S‖ • f)
  have he : inner ℝ f (S (S f)) = ‖S f‖ ^ 2 := by
    exact (hs f (S f)).symm.trans (real_inner_self_eq_norm_sq _)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, he,
    real_inner_self_eq_norm_sq] at hpos
  have hb : inner ℝ (S f) (S (S f)) ≤ ‖S‖ * ‖S f‖ ^ 2 := by
    calc
      _ ≤ ‖S f‖ * ‖S (S f)‖ := real_inner_le_norm _ _
      _ ≤ ‖S f‖ * (‖S‖ * ‖S f‖) :=
        mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  apply (mul_le_mul_iff_left₀ hn).mp
  nlinarith

theorem layer_quadratic_nonneg (alpha L : ℝ) (k : ℕ) (f : Space) :
    0 ≤ inner ℝ f (layer alpha L k f) := by
  rw [inner_layer]
  apply Finset.sum_nonneg
  intro e _
  nlinarith [conductance_pos alpha L e, sq_nonneg (differential f e)]

/-- The discarded root layers form a positive tail of the same complete
operator. This is stronger than an arbitrary norm approximation. -/
theorem tail_quadratic_nonneg {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    (N : ℕ) (f : Space) :
    0 ≤ inner ℝ f ((operator alpha L - cutoffOperator alpha L N) f) := by
  have hs := (innerSL ℝ f).summable (summable_apply (summable_layer ha hL) f)
  have hb := hs.sum_le_tsum (Finset.range (N + 1))
    (fun k _ => layer_quadratic_nonneg alpha L k f)
  have hfull : form alpha L f f = ∑' k, inner ℝ f (layer alpha L k f) := by
    rw [form_eq_tsum ha hL]
    exact tsum_congr fun k => (inner_layer alpha L k f f).symm
  have hfinite : inner ℝ f (cutoffOperator alpha L N f) =
      ∑ k ∈ Finset.range (N + 1), inner ℝ f (layer alpha L k f) := by
    simp only [cutoffOperator, sum_apply, inner_sum]
  simp only [sub_apply, inner_sub_right]
  change 0 ≤ form alpha L f f - inner ℝ f (cutoffOperator alpha L N f)
  rw [hfull, hfinite]
  exact sub_nonneg.mpr hb

theorem tail_symmetric {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L) (N : ℕ) :
    (operator alpha L - cutoffOperator alpha L N).IsSymmetric := by
  have hc : (cutoffOperator alpha L N).IsSymmetric := by
    intro f g
    calc
      inner ℝ (cutoffOperator alpha L N f) g =
          inner ℝ g (cutoffOperator alpha L N f) := real_inner_comm _ _
      _ = HistoryReactionForm.form alpha L (restrict N g) (restrict N f) :=
        cutoff_pairing_eq_finite alpha L N g f
      _ = HistoryReactionForm.form alpha L (restrict N f) (restrict N g) :=
        HistoryReactionForm.form_symm alpha L _ _
      _ = inner ℝ f (cutoffOperator alpha L N g) :=
        (cutoff_pairing_eq_finite alpha L N f g).symm
  exact (operator_symmetric ha hL).sub hc

theorem parent_response_positive {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    {k : ℕ} (e : Assembly k) : 0 < form alpha L (basisVector (parent e))
      (basisVector (parent e)) := by
  classical
  have hl : left e ≠ parent e := by
    intro h
    exact (ne_of_lt e.1.left_lt) (congrArg Sigma.fst h)
  have hr : right e ≠ parent e := by
    intro h
    exact (ne_of_lt e.1.right_lt) (congrArg Sigma.fst h)
  have hd : differential (basisVector (parent e)) e = 1 := by
    simp [differential, basisVector, lp.single_apply, hl, hr]
  have he : 0 < inner ℝ (basisVector (parent e))
      (layer alpha L k (basisVector (parent e))) := by
    rw [inner_layer]
    have hb := Finset.single_le_sum (s := (Finset.univ : Finset (Assembly k)))
      (f := fun a => conductance alpha L a *
        differential (basisVector (parent e)) a * differential (basisVector (parent e)) a)
      (fun a _ => by
        have hc := conductance_pos alpha L a
        have hq := sq_nonneg (differential (basisVector (parent e)) a)
        nlinarith) (Finset.mem_univ e)
    rw [hd] at hb
    exact lt_of_lt_of_le (by simpa using conductance_pos alpha L e) hb
  have hs := (innerSL ℝ (basisVector (parent e))).summable
    (summable_apply (summable_layer ha hL) (basisVector (parent e)))
  have hb := hs.sum_le_tsum {k}
    (fun j _ => layer_quadratic_nonneg alpha L j (basisVector (parent e)))
  have hfull : (∑' j, inner ℝ (basisVector (parent e))
      (layer alpha L j (basisVector (parent e)))) =
        form alpha L (basisVector (parent e)) (basisVector (parent e)) := by
    rw [form_eq_tsum ha hL]
    exact tsum_congr fun j => inner_layer alpha L j _ _
  rw [Finset.sum_singleton, hfull] at hb
  exact he.trans_le hb

theorem basisVector_zero_below {s u : AllSpecies} {N : ℕ}
    (hs : N < s.1) (hu : u.1 ≤ N) : basisVector s u = 0 := by
  classical
  have hne : u ≠ s := by
    intro h
    have he := congrArg Sigma.fst h
    omega
  simp [basisVector, lp.single_apply, hne]

theorem layer_annihilates_high_root (alpha L : ℝ) {s : AllSpecies} {k : ℕ}
    (hk : k < s.1) : layer alpha L k (basisVector s) = 0 := by
  classical
  simp only [layer, sum_apply, smul_apply, InnerProductSpace.rankOne_apply]
  apply Finset.sum_eq_zero
  intro e _
  have hp : basisVector s (parent e) = 0 := basisVector_zero_below hk (by rfl)
  have hl : basisVector s (left e) = 0 := basisVector_zero_below hk e.1.left_lt.le
  have hr : basisVector s (right e) = 0 := basisVector_zero_below hk e.1.right_lt.le
  rw [inner_incidenceVector]
  simp [differential, hp, hl, hr]

theorem cutoff_annihilates_high_root (alpha L : ℝ) (N : ℕ) (s : AllSpecies)
    (hs : N < s.1) : cutoffOperator alpha L N (basisVector s) = 0 := by
  classical
  simp only [cutoffOperator, sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact layer_annihilates_high_root alpha L
    (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hs)

theorem high_root_response_le (alpha L : ℝ) (N : ℕ) (s : AllSpecies)
    (hs : N < s.1) :
    ‖operator alpha L (basisVector s)‖ ≤
      ‖operator alpha L - cutoffOperator alpha L N‖ := by
  have he : (operator alpha L - cutoffOperator alpha L N) (basisVector s) =
      operator alpha L (basisVector s) := by
    simp [cutoff_annihilates_high_root alpha L N s hs]
  calc
    _ = ‖(operator alpha L - cutoffOperator alpha L N) (basisVector s)‖ :=
      congrArg norm he.symm
    _ ≤ ‖operator alpha L - cutoffOperator alpha L N‖ * ‖basisVector s‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [norm_basisVector, mul_one]

/-- The small-response states are actual generated histories, not arbitrary
    auxiliary vectors or a change of the reaction form. -/
theorem exists_anchored_unit_small_response {alpha L : ℝ}
    (ha : 0 < alpha) (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Space, ‖f‖ = 1 ∧ f ⟨1, .one⟩ = 0 ∧
      ‖operator alpha L f‖ < ε ∧ form alpha L f f < ε := by
  classical
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (cutoffOperator_tendsto ha hL)) ε hε
  let s : AllSpecies :=
    ⟨N + 2, Classical.choice (Arithmetic.HistoryObservation.history_nonempty (N + 2) (by omega))⟩
  have hs : N < s.1 := by dsimp [s]; omega
  have hn : ‖operator alpha L - cutoffOperator alpha L N‖ < ε := by
    simpa only [dist_eq_norm, norm_sub_rev] using hN N le_rfl
  have hb : ‖operator alpha L (basisVector s)‖ < ε :=
    lt_of_le_of_lt (high_root_response_le alpha L N s hs) hn
  refine ⟨basisVector s, norm_basisVector s, ?_, hb, ?_⟩
  · exact basisVector_zero_below (s := s) (N := N + 1) (by dsimp [s]; omega) (by simp)
  · calc
      form alpha L (basisVector s) (basisVector s) ≤
          ‖basisVector s‖ * ‖operator alpha L (basisVector s)‖ := real_inner_le_norm _ _
      _ < ε := by simpa only [norm_basisVector, one_mul] using hb

/-- Even after fixing the unit leaf, this particular complete response has
    no positive lower bound uniform over all root levels. -/
theorem no_uniform_anchored_coercivity {alpha L c : ℝ}
    (ha : 0 < alpha) (hL : 0 < L) (hc : 0 < c) :
    ¬ ∀ f : Space, f ⟨1, .one⟩ = 0 →
      c * ‖f‖ ^ 2 ≤ form alpha L f f := by
  intro h
  obtain ⟨f, hf, hz, _, he⟩ := exists_anchored_unit_small_response ha hL hc
  have hb := h f hz
  rw [hf, one_pow, mul_one] at hb
  exact (not_lt_of_ge hb) he

/-- At high roots the actual positive tail controls dissipation relative to
the full action itself, not only relative to the coefficient norm. -/
theorem high_root_dissipation_le {alpha L : ℝ} (ha : 0 < alpha) (hL : 0 < L)
    (N : ℕ) (s : AllSpecies) (hs : N < s.1) :
    ‖operator alpha L (basisVector s)‖ ^ 2 ≤
      ‖operator alpha L - cutoffOperator alpha L N‖ *
        form alpha L (basisVector s) (basisVector s) := by
  have he : (operator alpha L - cutoffOperator alpha L N) (basisVector s) =
      operator alpha L (basisVector s) := by
    simp [cutoff_annihilates_high_root alpha L N s hs]
  simpa only [he, form] using positive_response_norm_sq_le
    (operator alpha L - cutoffOperator alpha L N) (tail_symmetric ha hL N)
    (tail_quadratic_nonneg ha hL N) (basisVector s)

/-- The witness has strictly positive complete action. Thus it is not a
conserved zero mode causing a small dissipation-to-action ratio. -/
theorem exists_positive_action_small_dissipation {alpha L : ℝ}
    (ha : 0 < alpha) (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Space, ‖f‖ = 1 ∧ f ⟨1, .one⟩ = 0 ∧
      0 < form alpha L f f ∧ ‖operator alpha L f‖ ^ 2 < ε * form alpha L f f := by
  classical
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (cutoffOperator_tendsto ha hL)) ε hε
  let c := additiveChannel (N + 2) (by omega)
  let e : Assembly (N + 2) := ⟨c,
    Classical.choice (Arithmetic.HistoryObservation.history_nonempty _ c.left_pos),
    Classical.choice (Arithmetic.HistoryObservation.history_nonempty _ c.right_pos)⟩
  have hp := parent_response_positive ha hL e
  have hn : ‖operator alpha L - cutoffOperator alpha L N‖ < ε := by
    simpa only [dist_eq_norm, norm_sub_rev] using hN N le_rfl
  refine ⟨basisVector (parent e), norm_basisVector _, ?_, hp, ?_⟩
  · exact basisVector_zero_below (s := parent e) (N := N + 1)
      (by change N + 1 < N + 2; omega) (by simp)
  · exact (high_root_dissipation_le ha hL N (parent e) (by change N < N + 2; omega)).trans_lt
      (mul_lt_mul_of_pos_right hn hp)

theorem no_uniform_action_coercivity {alpha L c : ℝ}
    (ha : 0 < alpha) (hL : 0 < L) (hc : 0 < c) :
    ¬ ∀ f : Space, f ⟨1, .one⟩ = 0 →
      c * form alpha L f f ≤ ‖operator alpha L f‖ ^ 2 := by
  intro h
  obtain ⟨f, _, hz, _, hf⟩ := exists_positive_action_small_dissipation ha hL hc
  exact (not_lt_of_ge (h f hz)) hf

private theorem deriv_le_of_forward_le {f g : ℝ → ℝ} {f' g' : ℝ}
    (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0) (hzero : f 0 = g 0)
    (hle : ∀ t, 0 ≤ t → f t ≤ g t) : f' ≤ g' := by
  have hd := (hf.sub hg).tendsto_slope_zero_right
  have hb : f' - g' ≤ 0 := le_of_tendsto hd (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    change t⁻¹ * ((f (0 + t) - g (0 + t)) - (f 0 - g 0)) ≤ 0
    rw [zero_add, hzero, sub_self, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le)
      (sub_nonpos.mpr (hle t ht0.le)))
  exact sub_nonpos.mp hb

/-- Forward monotonicity of the full action holds, but a positive exponential
rate with prefactor one cannot hold uniformly over its actual root levels.
The witnesses have positive action and zero unit-leaf coefficient. -/
theorem no_uniform_exponential_action {alpha L c : ℝ}
    (ha : 0 < alpha) (hL : 0 < L) (hc : 0 < c) :
    ¬ ∀ f : Space, f ⟨1, .one⟩ = 0 → ∀ t : ℝ, 0 ≤ t →
      action alpha L (HistoryReactionHilbertFlow.flow alpha L t f) ≤
        Real.exp (-2 * c * t) * action alpha L f := by
  intro h
  obtain ⟨f, _, hz, _, hf⟩ := exists_positive_action_small_dissipation ha hL hc
  have hleft : HasDerivAt
      (fun t => action alpha L (HistoryReactionHilbertFlow.flow alpha L t f))
      (-‖operator alpha L f‖ ^ 2) 0 := by
    simpa only [HistoryReactionHilbertFlow.flow_zero] using
      HistoryReactionHilbertFlow.action_hasDerivAt ha hL 0 f
  have hright : HasDerivAt (fun t : ℝ => Real.exp (-2 * c * t) * action alpha L f)
      ((-2 * c) * action alpha L f) 0 := by
    simpa only [id_eq, mul_zero, Real.exp_zero, mul_one, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).const_mul (-2 * c)).exp.mul_const (action alpha L f))
  have hb := deriv_le_of_forward_le hleft hright
    (by simp only [HistoryReactionHilbertFlow.flow_zero, mul_zero, Real.exp_zero, one_mul])
    (h f hz)
  dsimp only [action] at hb
  exact (not_lt_of_ge (by nlinarith : c * form alpha L f f ≤
    ‖operator alpha L f‖ ^ 2)) hf

structure Conclusions : Prop where
  actual_cutoff_support : ∀ alpha L N s, N < s.1 →
    cutoffOperator alpha L N (basisVector s) = 0
  actual_zero_edge : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L →
    ∀ {ε : ℝ}, 0 < ε → ∃ f : Space, ‖f‖ = 1 ∧ f ⟨1, .one⟩ = 0 ∧
      ‖operator alpha L f‖ < ε ∧ form alpha L f f < ε
  anchored_no_positive_gap : ∀ {alpha L c : ℝ}, 0 < alpha → 0 < L → 0 < c →
    ¬ ∀ f : Space, f ⟨1, .one⟩ = 0 → c * ‖f‖ ^ 2 ≤ form alpha L f f
  positive_action_small_dissipation : ∀ {alpha L : ℝ}, 0 < alpha → 0 < L →
    ∀ {ε : ℝ}, 0 < ε → ∃ f : Space, ‖f‖ = 1 ∧ f ⟨1, .one⟩ = 0 ∧
      0 < form alpha L f f ∧ ‖operator alpha L f‖ ^ 2 < ε * form alpha L f f
  action_no_positive_gap : ∀ {alpha L c : ℝ}, 0 < alpha → 0 < L → 0 < c →
    ¬ ∀ f : Space, f ⟨1, .one⟩ = 0 →
      c * form alpha L f f ≤ ‖operator alpha L f‖ ^ 2
  no_uniform_action_rate : ∀ {alpha L c : ℝ}, 0 < alpha → 0 < L → 0 < c →
    ¬ ∀ f : Space, f ⟨1, .one⟩ = 0 → ∀ t : ℝ, 0 ≤ t →
      action alpha L (HistoryReactionHilbertFlow.flow alpha L t f) ≤
        Real.exp (-2 * c * t) * action alpha L f

theorem generated : Conclusions where
  actual_cutoff_support := cutoff_annihilates_high_root
  actual_zero_edge := exists_anchored_unit_small_response
  anchored_no_positive_gap := no_uniform_anchored_coercivity
  positive_action_small_dissipation := exists_positive_action_small_dissipation
  action_no_positive_gap := no_uniform_action_coercivity
  no_uniform_action_rate := no_uniform_exponential_action

end GeneratedFoundations.Analysis.HistoryReactionSpectralEdge
