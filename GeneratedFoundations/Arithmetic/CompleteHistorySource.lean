module

public import GeneratedFoundations.Arithmetic.ReducedExpressionFoundation
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Complete ordered arithmetic histories

This module retains every ordered binary addition and multiplication history
above a positive generated natural value.  Addition has positive children;
multiplication has non-unit children.  Thus the six unit and zero reductions
of the reduced-expression syntax have already been performed, while no
associativity, commutativity or distributivity relation is imposed on a
history.

The persistent source law divides equally among the admissible channels at
each vertex.  Multiplication by the Gaussian mass of the root gives the unique
flat-history source used across scales, and its pushforward is exactly the
Gaussian square-spectrum mass.  A second, recursively renormalized Gaussian
directory is retained below only as a fixed-scale local reconstruction; it is
not a second persistent source law.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.CompleteHistory

/-- The two native binary operations retained by a complete history. -/
inductive Operation where
  | add
  | mul
  deriving DecidableEq

instance : Fintype Operation where
  elems := {.add, .mul}
  complete x := by cases x <;> simp

/-- A top channel for the positive value `k`.  Children are strictly smaller
than `k`; multiplication channels exclude unit factors. -/
def Channel (k : ℕ) :=
  {x : Operation × Fin k × Fin k //
    0 < x.2.1.1 ∧ 0 < x.2.2.1 ∧
      match x.1 with
      | .add => x.2.1.1 + x.2.2.1 = k
      | .mul => 2 ≤ x.2.1.1 ∧ 2 ≤ x.2.2.1 ∧ x.2.1.1 * x.2.2.1 = k}

noncomputable instance (k : ℕ) : Fintype (Channel k) := by
  classical
  exact Subtype.fintype _

namespace Channel

def operation {k : ℕ} (c : Channel k) : Operation := c.1.1
def left {k : ℕ} (c : Channel k) : Fin k := c.1.2.1
def right {k : ℕ} (c : Channel k) : Fin k := c.1.2.2

theorem left_pos {k : ℕ} (c : Channel k) : 0 < c.left.1 := c.2.1
theorem right_pos {k : ℕ} (c : Channel k) : 0 < c.right.1 := c.2.2.1

theorem left_lt {k : ℕ} (c : Channel k) : c.left.1 < k := c.left.2
theorem right_lt {k : ℕ} (c : Channel k) : c.right.1 < k := c.right.2

theorem equation {k : ℕ} (c : Channel k) :
    match c.operation with
    | .add => c.left.1 + c.right.1 = k
    | .mul => 2 ≤ c.left.1 ∧ 2 ≤ c.right.1 ∧ c.left.1 * c.right.1 = k :=
  c.2.2.2

end Channel

/-- Complete ordered histories over one unit leaf.  The index records the
generated natural value at the root. -/
inductive History : ℕ → Type where
  | one : History 1
  | node {k : ℕ} (c : Channel k)
      (left : History c.left.1) (right : History c.right.1) : History k

/-- A history is either the unit leaf or a channel together with its two
ordered child histories. -/
def historyDecomposition (k : ℕ) :
    History k ≃ PLift (k = 1) ⊕ (Σ c : Channel k, History c.left.1 × History c.right.1) where
  toFun
    | .one => .inl ⟨rfl⟩
    | .node c hl hr => .inr ⟨c, hl, hr⟩
  invFun
    | .inl h => h.down.symm ▸ .one
    | .inr ⟨c, hl, hr⟩ => .node c hl hr
  left_inv h := by cases h <;> rfl
  right_inv x := by
    cases x with
    | inl h => rcases h with ⟨h⟩; cases h; rfl
    | inr x => rcases x with ⟨c, hl, hr⟩; rfl

@[instance_reducible] noncomputable def historyFintypeAux : (k : ℕ) → Fintype (History k) :=
  fun k => Nat.strongRecOn k fun k ih => by
    letI : Fintype (PLift (k = 1)) := Fintype.ofFinite (PLift (k = 1))
    letI (c : Channel k) : Fintype (History c.left.1) := ih c.left.1 c.left_lt
    letI (c : Channel k) : Fintype (History c.right.1) := ih c.right.1 c.right_lt
    exact Fintype.ofEquiv _ (historyDecomposition k).symm

noncomputable instance historyFintype (k : ℕ) : Fintype (History k) :=
  historyFintypeAux k

/-- Every positive value has an additive top channel `(1,k-1)`. -/
def additiveChannel (k : ℕ) (hk : 2 ≤ k) : Channel k :=
  ⟨(.add, ⟨1, hk⟩, ⟨k - 1, by omega⟩), by
    simp only
    constructor
    · omega
    constructor
    · omega
    · omega⟩

theorem channel_nonempty (k : ℕ) (hk : 2 ≤ k) : Nonempty (Channel k) :=
  ⟨additiveChannel k hk⟩

instance channelOneIsEmpty : IsEmpty (Channel 1) :=
  ⟨fun c => by have := c.left_pos; have := c.left_lt; omega⟩

/-- Equal-channel conditional weight on a complete history. -/
def flatWeight : {k : ℕ} → History k → ℝ
  | _, .one => 1
  | _, .node (k := k) _c hl hr =>
      flatWeight hl * flatWeight hr /
        (Fintype.card (Channel k) : ℝ)

@[simp] theorem flatWeight_decomposition_inl {k : ℕ} (h : PLift (k = 1)) :
    flatWeight ((historyDecomposition k).symm (.inl h)) = 1 := by
  rcases h with ⟨h⟩
  subst k
  rfl

@[simp] theorem flatWeight_decomposition_inr {k : ℕ} (c : Channel k)
    (hl : History c.left.1) (hr : History c.right.1) :
    flatWeight ((historyDecomposition k).symm (.inr ⟨c, hl, hr⟩)) =
      flatWeight hl * flatWeight hr / (Fintype.card (Channel k) : ℝ) := rfl

/-- The equal-channel law is normalized on every positive history fiber. -/
theorem flatWeight_sum_one : ∀ (k : ℕ), 0 < k →
    ∑ h : History k, flatWeight h = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      by_cases hk1 : k = 1
      · subst k
        rw [Fintype.sum_equiv (historyDecomposition 1)
          (fun h => flatWeight h)
          (fun x => flatWeight ((historyDecomposition 1).symm x))
          (fun x => congrArg flatWeight ((historyDecomposition 1).left_inv x).symm)]
        simp [flatWeight_decomposition_inl]
      · have hk2 : 2 ≤ k := by omega
        rw [Fintype.sum_equiv (historyDecomposition k)
          (fun h => flatWeight h)
          (fun x => flatWeight ((historyDecomposition k).symm x))
          (fun x => congrArg flatWeight ((historyDecomposition k).left_inv x).symm)]
        rw [Fintype.sum_sum_type, Fintype.sum_sigma]
        simp only [Fintype.sum_prod_type]
        simp only [flatWeight_decomposition_inl, flatWeight_decomposition_inr]
        have hleft (c : Channel k) :
            ∑ h : History c.left.1, flatWeight h = 1 :=
          ih c.left.1 c.left_lt c.left_pos
        have hright (c : Channel k) :
            ∑ h : History c.right.1, flatWeight h = 1 :=
          ih c.right.1 c.right_lt c.right_pos
        have hleafzero : (∑ _h : PLift (k = 1), (1 : ℝ)) = 0 := by
          apply Fintype.sum_eq_zero
          intro h
          exact (hk1 h.down).elim
        have hchannel (c : Channel k) :
            (∑ hl : History c.left.1, ∑ hr : History c.right.1,
              flatWeight hl * flatWeight hr / (Fintype.card (Channel k) : ℝ)) =
                1 / (Fintype.card (Channel k) : ℝ) := by
          simp_rw [← Finset.sum_div]
          rw [← Fintype.sum_mul_sum, hleft c, hright c, one_mul]
        rw [hleafzero, zero_add]
        simp only [hchannel]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : (Fintype.card (Channel k) : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_pos_iff.mpr (channel_nonempty k hk2)).ne'
        field_simp [hcard]

/-- Gaussian mass attached to the generated square index. -/
def gaussianRootMass (alpha L : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-alpha * (k : ℝ) ^ 2 / L ^ 2)

/-- Complete flat-history intensity over a Gaussian root mass. -/
def flatGaussianIntensity (alpha L : ℝ) {k : ℕ} (h : History k) : ℝ :=
  gaussianRootMass alpha L k * flatWeight h

/-- Pushing the complete flat-history intensity to its root gives exactly the
Gaussian square-spectrum mass. -/
theorem flatGaussian_pushforward (alpha L : ℝ) (k : ℕ) (hk : 0 < k) :
    ∑ h : History k, flatGaussianIntensity alpha L h = gaussianRootMass alpha L k := by
  simp only [flatGaussianIntensity, ← Finset.mul_sum, flatWeight_sum_one k hk, mul_one]

/-- Gaussian child-pair partition function over all admissible top channels. -/
def localPartition (alpha L : ℝ) (k : ℕ) : ℝ :=
  ∑ c : Channel k,
    gaussianRootMass alpha L c.left.1 * gaussianRootMass alpha L c.right.1

theorem gaussianRootMass_pos (alpha L : ℝ) (k : ℕ) :
    0 < gaussianRootMass alpha L k := by
  exact Real.exp_pos _

theorem localPartition_pos (alpha L : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    0 < localPartition alpha L k := by
  apply Finset.sum_pos
  · intro c _
    exact mul_pos (gaussianRootMass_pos alpha L c.left.1)
      (gaussianRootMass_pos alpha L c.right.1)
  · exact ⟨additiveChannel k hk, Finset.mem_univ _⟩

/-- The local coupling forced by conservation of the parent Gaussian mass. -/
def localCoupling (alpha L : ℝ) (k : ℕ) : ℝ :=
  gaussianRootMass alpha L k / localPartition alpha L k

/-- Conservation uniquely determines the displayed local coupling. -/
theorem localCoupling_unique (alpha L : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (q : ℝ) (hq : q * localPartition alpha L k = gaussianRootMass alpha L k) :
    q = localCoupling alpha L k := by
  exact (eq_div_iff (ne_of_gt (localPartition_pos alpha L k hk))).2 hq

/-- Fixed-scale recursively renormalized Gaussian directory mass on complete
histories.  This is a local reconstruction identity, not the persistent
cross-scale source law. -/
def directoryMass (alpha L : ℝ) : {k : ℕ} → History k → ℝ
  | _, .one => gaussianRootMass alpha L 1
  | _, .node (k := k) _c hl hr =>
      localCoupling alpha L k * directoryMass alpha L hl * directoryMass alpha L hr

@[simp] theorem directoryMass_decomposition_inl (alpha L : ℝ) {k : ℕ}
    (h : PLift (k = 1)) :
    directoryMass alpha L ((historyDecomposition k).symm (.inl h)) =
      gaussianRootMass alpha L k := by
  rcases h with ⟨h⟩
  subst k
  rfl

@[simp] theorem directoryMass_decomposition_inr (alpha L : ℝ) {k : ℕ}
    (c : Channel k) (hl : History c.left.1) (hr : History c.right.1) :
    directoryMass alpha L ((historyDecomposition k).symm (.inr ⟨c, hl, hr⟩)) =
      localCoupling alpha L k * directoryMass alpha L hl * directoryMass alpha L hr := rfl

/-- At a fixed scale, the recursively renormalized directory compresses every
complete history fiber exactly to the Gaussian root mass. -/
theorem directoryMass_sum_gaussian (alpha L : ℝ) : ∀ (k : ℕ), 0 < k →
    ∑ h : History k, directoryMass alpha L h = gaussianRootMass alpha L k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      by_cases hk1 : k = 1
      · subst k
        rw [Fintype.sum_equiv (historyDecomposition 1)
          (fun h => directoryMass alpha L h)
          (fun x => directoryMass alpha L ((historyDecomposition 1).symm x))
          (fun x => congrArg (directoryMass alpha L)
            ((historyDecomposition 1).left_inv x).symm)]
        simp [directoryMass_decomposition_inl]
      · have hk2 : 2 ≤ k := by omega
        rw [Fintype.sum_equiv (historyDecomposition k)
          (fun h => directoryMass alpha L h)
          (fun x => directoryMass alpha L ((historyDecomposition k).symm x))
          (fun x => congrArg (directoryMass alpha L)
            ((historyDecomposition k).left_inv x).symm)]
        rw [Fintype.sum_sum_type, Fintype.sum_sigma]
        simp only [Fintype.sum_prod_type, directoryMass_decomposition_inl,
          directoryMass_decomposition_inr]
        have hleft (c : Channel k) :
            ∑ h : History c.left.1, directoryMass alpha L h =
              gaussianRootMass alpha L c.left.1 :=
          ih c.left.1 c.left_lt c.left_pos
        have hright (c : Channel k) :
            ∑ h : History c.right.1, directoryMass alpha L h =
              gaussianRootMass alpha L c.right.1 :=
          ih c.right.1 c.right_lt c.right_pos
        have hleafzero :
            (∑ _h : PLift (k = 1),
              gaussianRootMass alpha L k) = 0 := by
          apply Fintype.sum_eq_zero
          intro h
          exact (hk1 h.down).elim
        have hchannel (c : Channel k) :
            (∑ hl : History c.left.1, ∑ hr : History c.right.1,
              localCoupling alpha L k * directoryMass alpha L hl *
                directoryMass alpha L hr) =
              localCoupling alpha L k * gaussianRootMass alpha L c.left.1 *
                gaussianRootMass alpha L c.right.1 := by
          calc
            _ = (∑ hl : History c.left.1,
                  localCoupling alpha L k * directoryMass alpha L hl) *
                (∑ hr : History c.right.1, directoryMass alpha L hr) :=
              (Fintype.sum_mul_sum
                (fun hl : History c.left.1 =>
                  localCoupling alpha L k * directoryMass alpha L hl)
                (fun hr : History c.right.1 => directoryMass alpha L hr)).symm
            _ = (localCoupling alpha L k *
                  ∑ hl : History c.left.1, directoryMass alpha L hl) *
                (∑ hr : History c.right.1, directoryMass alpha L hr) := by
              have hfactor :
                  (∑ hl : History c.left.1,
                    localCoupling alpha L k * directoryMass alpha L hl) =
                    localCoupling alpha L k *
                      ∑ hl : History c.left.1, directoryMass alpha L hl := by
                simpa only using
                  (Finset.mul_sum Finset.univ
                    (fun hl : History c.left.1 => directoryMass alpha L hl)
                    (localCoupling alpha L k)).symm
              rw [hfactor]
            _ = _ := by rw [hleft c, hright c]
        rw [hleafzero, zero_add]
        simp only [hchannel]
        have hfactor :
            (∑ c : Channel k,
              localCoupling alpha L k * gaussianRootMass alpha L c.left.1 *
                gaussianRootMass alpha L c.right.1) =
              localCoupling alpha L k * localPartition alpha L k := by
          rw [localPartition]
          calc
            _ = ∑ c : Channel k, localCoupling alpha L k *
                (gaussianRootMass alpha L c.left.1 *
                  gaussianRootMass alpha L c.right.1) := by
              apply Fintype.sum_congr
              intro c
              ring
            _ = _ := by
              simpa only using
                (Finset.mul_sum Finset.univ
                  (fun c : Channel k => gaussianRootMass alpha L c.left.1 *
                    gaussianRootMass alpha L c.right.1)
                  (localCoupling alpha L k)).symm
        rw [hfactor]
        change localCoupling alpha L k * localPartition alpha L k =
          gaussianRootMass alpha L k
        exact (div_mul_cancel₀ _ (ne_of_gt (localPartition_pos alpha L k hk2)))

/-- Forget the history index while retaining its ordered reduced expression. -/
def toExpression : {k : ℕ} → History k → ReducedExpression.Expr
  | _, .one => 1
  | _, .node c hl hr =>
      match c.operation with
      | .add => toExpression hl + toExpression hr
      | .mul => toExpression hl * toExpression hr

/-- The retained expression evaluates to the history root. -/
@[simp] theorem evalNat_toExpression {k : ℕ} (h : History k) :
    ReducedExpression.evalNat (toExpression h) = k := by
  induction h with
  | one => simp [toExpression]
  | @node k c hl hr ihl ihr =>
      cases hop : c.operation with
      | add =>
          have heq : c.left.1 + c.right.1 = k := by
            simpa [hop] using c.equation
          simp [toExpression, hop, ihl, ihr, heq]
      | mul =>
          have heq : c.left.1 * c.right.1 = k := by
            have hall := c.equation
            rw [hop] at hall
            exact hall.2.2
          simp [toExpression, hop, ihl, ihr, heq]

/-- Each complete history is therefore a member of the pre-existing finite
evaluation fiber of the same generated value. -/
def toEvaluationFiber {k : ℕ} (h : History k) : ReducedExpression.Fiber k :=
  ⟨toExpression h, evalNat_toExpression h⟩

/-- The persistent complete-history source, its expression realization and
its normalized root pushforward are one theorem package.  Arithmetic signs
and finite harmonic observations are later research extensions; they are not
part of the construction of the complete positive source.  The fixed-scale
directory reconstruction above is deliberately not part of this root
conclusion. -/
structure Conclusions : Prop where
  flat_normalization : ∀ (k : ℕ), 0 < k →
    ∑ h : History k, flatWeight h = 1
  flat_gaussian_pushforward : ∀ (alpha L : ℝ) (k : ℕ), 0 < k →
    ∑ h : History k, flatGaussianIntensity alpha L h = gaussianRootMass alpha L k
  expression_realization : ∀ {k : ℕ} (h : History k),
    ReducedExpression.evalNat (toExpression h) = k

theorem completeHistoryConclusions : Conclusions where
  flat_normalization := flatWeight_sum_one
  flat_gaussian_pushforward := flatGaussian_pushforward
  expression_realization := evalNat_toExpression

end GeneratedFoundations.Arithmetic.CompleteHistory
