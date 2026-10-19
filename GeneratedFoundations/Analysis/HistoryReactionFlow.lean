module

public import GeneratedFoundations.Analysis.HistoryReactionKernel
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The finite evolution of the actual history reaction operator

The generator is the full incidence--conductance--adjoint operator already
obtained by varying the common reaction action.  Its exponential acts on all
species below the observation cutoff.  In particular it is not the separate
two-branch reflection flow and is not a replacement diagonal model.

Finite dimensionality supplies continuity on the whole coefficient space.
The evolution equation and its quadratic dissipation follow for this exact
operator.  The cutoff remains visible in the type; no limit over cutoffs or
cutoff-independent positive gap is asserted by these finite statements.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryReactionFlow

open HistoryReactionForm HistoryReactionOperator

local instance (N : ℕ) : NormedAlgebra ℚ
    ((Species N → ℝ) →L[ℝ] (Species N → ℝ)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

def linearOperator (alpha L : ℝ) (N : ℕ) :
    (Species N → ℝ) →ₗ[ℝ] (Species N → ℝ) where
  toFun := operator alpha L
  map_add' f g := by
    funext s
    change operator alpha L (fun x => f x + g x) s =
      operator alpha L f s + operator alpha L g s
    simp only [operator, differential_add, mul_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' t f := by
    funext s
    change (∑ e, conductance alpha L e * differential (t • f) e * incidence e s) =
      t * ∑ e, conductance alpha L e * differential f e * incidence e s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [differential, Pi.smul_apply, smul_eq_mul]
    ring

def generator (alpha L : ℝ) (N : ℕ) :
    (Species N → ℝ) →L[ℝ] (Species N → ℝ) :=
  (linearOperator alpha L N).toContinuousLinearMap

@[simp] theorem generator_apply (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    generator alpha L N f = operator alpha L f := rfl

def flow (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ) : Species N → ℝ :=
  NormedSpace.exp (t • (-generator alpha L N)) f

@[simp] theorem flow_zero (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    flow alpha L 0 f = f := by
  simp [flow]

theorem flow_add (alpha L s t : ℝ) {N : ℕ} (f : Species N → ℝ) :
    flow alpha L (s + t) f = flow alpha L s (flow alpha L t f) := by
  have hc : Commute (s • (-generator alpha L N)) (t • (-generator alpha L N)) :=
    ((Commute.refl (-generator alpha L N)).smul_left s).smul_right t
  unfold flow
  rw [add_smul, NormedSpace.exp_add_of_commute hc]
  rfl

theorem flow_hasDerivAt (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ) :
    HasDerivAt (fun u => flow alpha L u f)
      (-operator alpha L (flow alpha L t f)) t := by
  have h := (hasDerivAt_exp_smul_const' (-generator alpha L N) t).clm_apply
    (hasDerivAt_const t f)
  simpa only [flow, mul_apply_eq_comp, neg_apply,
    generator_apply, ContinuousLinearMap.map_zero, add_zero] using h

theorem coordinate_hasDerivAt (alpha L t : ℝ) {N : ℕ}
    (f : Species N → ℝ) (s : Species N) :
    HasDerivAt (fun u => flow alpha L u f s)
      (-operator alpha L (flow alpha L t f) s) t :=
  (hasDerivAt_pi.mp (flow_hasDerivAt alpha L t f)) s

def energy {N : ℕ} (f : Species N → ℝ) : ℝ := (∑ s, f s ^ 2) / 2

theorem energy_nonneg {N : ℕ} (f : Species N → ℝ) : 0 ≤ energy f := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by norm_num)

theorem energy_hasDerivAt (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ) :
    HasDerivAt (fun u => energy (flow alpha L u f))
      (-form alpha L (flow alpha L t f) (flow alpha L t f)) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun s _ => (coordinate_hasDerivAt alpha L t f s).pow 2)).div_const 2
  convert h using 1
  · rfl
  · rw [← adjoint_identity]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Finset.sum_div,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring

theorem energy_antitone (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    Antitone (fun t => energy (flow alpha L t f)) := by
  apply antitone_of_deriv_nonpos
  · exact fun t => (energy_hasDerivAt alpha L t f).differentiableAt
  · intro t
    rw [(energy_hasDerivAt alpha L t f).deriv]
    exact neg_nonpos.mpr (form_nonneg alpha L _)

theorem energy_le_initial (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ)
    {t : ℝ} (ht : 0 ≤ t) : energy (flow alpha L t f) ≤ energy f := by
  simpa only [flow_zero] using energy_antitone alpha L f ht

def conservedCharge {N : ℕ} (f : Species N → ℝ) : ℝ :=
  ∑ s, leafCharge s * f s

theorem charge_hasDerivAt (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ) :
    HasDerivAt (fun u => conservedCharge (flow alpha L u f)) 0 t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun s _ => (coordinate_hasDerivAt alpha L t f s).const_mul (leafCharge s))
  convert h using 1
  · rfl
  · exact (leafCharge_conservation alpha L (flow alpha L t f)).symm

theorem charge_preserved (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ) :
    conservedCharge (flow alpha L t f) = conservedCharge f := by
  have hc := is_const_of_deriv_eq_zero
    (fun t => (charge_hasDerivAt alpha L t f).differentiableAt)
    (fun t => (charge_hasDerivAt alpha L t f).deriv) t 0
  simpa only [flow_zero] using hc

theorem differential_hasDerivAt (alpha L t : ℝ) {N : ℕ}
    (f : Species N → ℝ) (e : Reaction N) :
    HasDerivAt (fun u => differential (flow alpha L u f) e)
      (-differential (operator alpha L (flow alpha L t f)) e) t := by
  have h := ((coordinate_hasDerivAt alpha L t f (parent e)).sub
    (coordinate_hasDerivAt alpha L t f (left e))).sub
    (coordinate_hasDerivAt alpha L t f (right e))
  convert h using 1
  · rfl
  · simp only [differential]
    ring

theorem action_hasDerivAt (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ) :
    HasDerivAt (fun u => action alpha L (flow alpha L u f))
      (-(∑ s, operator alpha L (flow alpha L t f) s ^ 2)) t := by
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun e _ =>
    ((differential_hasDerivAt alpha L t f e).pow 2).const_mul
      (conductance alpha L e))).div_const 2
  have hsum : (∑ e : Reaction N, conductance alpha L e *
      (2 * differential (flow alpha L t f) e *
        -differential (operator alpha L (flow alpha L t f)) e)) / 2 =
      -form alpha L (flow alpha L t f) (operator alpha L (flow alpha L t f)) := by
    simp only [form, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hform : form alpha L (flow alpha L t f)
      (operator alpha L (flow alpha L t f)) =
      ∑ s, operator alpha L (flow alpha L t f) s ^ 2 := by
    rw [form_symm, ← adjoint_identity]
    simp only [pow_two]
  convert h using 1
  · funext u
    simp only [action, form, Pi.pow_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  · simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, hsum, hform]

theorem action_antitone (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ) :
    Antitone (fun t => action alpha L (flow alpha L t f)) := by
  apply antitone_of_deriv_nonpos
  · exact fun t => (action_hasDerivAt alpha L t f).differentiableAt
  · intro t
    rw [(action_hasDerivAt alpha L t f).deriv]
    exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

structure Conclusions : Prop where
  actual_semigroup : ∀ (alpha L s t : ℝ) {N : ℕ} (f : Species N → ℝ),
    flow alpha L (s + t) f = flow alpha L s (flow alpha L t f)
  actual_equation : ∀ (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ),
    HasDerivAt (fun u => flow alpha L u f)
      (-operator alpha L (flow alpha L t f)) t
  exact_dissipation : ∀ (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ),
    HasDerivAt (fun u => energy (flow alpha L u f))
      (-form alpha L (flow alpha L t f) (flow alpha L t f)) t
  contraction : ∀ (alpha L : ℝ) {N : ℕ} (f : Species N → ℝ)
    {t : ℝ}, 0 ≤ t → energy (flow alpha L t f) ≤ energy f
  charge_conservation : ∀ (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ),
    conservedCharge (flow alpha L t f) = conservedCharge f
  action_dissipation : ∀ (alpha L t : ℝ) {N : ℕ} (f : Species N → ℝ),
    HasDerivAt (fun u => action alpha L (flow alpha L u f))
      (-(∑ s, operator alpha L (flow alpha L t f) s ^ 2)) t

theorem generated : Conclusions where
  actual_semigroup := flow_add
  actual_equation := flow_hasDerivAt
  exact_dissipation := energy_hasDerivAt
  contraction := energy_le_initial
  charge_conservation := charge_preserved
  action_dissipation := action_hasDerivAt

end GeneratedFoundations.Analysis.HistoryReactionFlow
