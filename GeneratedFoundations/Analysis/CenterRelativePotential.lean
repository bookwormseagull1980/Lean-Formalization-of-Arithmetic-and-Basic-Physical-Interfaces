module

public import GeneratedFoundations.Analysis.CenterEndpointPotential
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The full binary relative potential of the central sectors

`CenterEndpointPotential` records the quadratic proxy for the central
two-sector imbalance.  The present file keeps the full binary relative
potential.  Its definition uses the continuous convention
`0 * log 0 = 0`, which is already the convention of `Real.log` in Mathlib.

The potential is written as capacity times a normalized binary density.  This
form has two advantages.  It is meaningful when one sector is empty, and the
loss under ordinary joining is exactly a weighted Jensen gap for the convex
function `t * log t`.  Reversing the central label of the second source gives
the corresponding opposite-centre Jensen--Shannon gap.

All statements in this file are finite exact identities or convexity
inequalities.  No scale limit or all-scale summability assertion is made.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.CenterRelativePotential

open GeneratedFoundations.Analysis.CenterEndpointPotential
open CenterEndpointPotential.CentrePair

/-- The continuous entropy atom.  Since `Real.log 0 = 0`, this implements the
standard convention `0 log 0 = 0`. -/
def entropyAtom (t : ℝ) : ℝ := t * Real.log t

@[simp] theorem entropyAtom_zero : entropyAtom 0 = 0 := by
  simp [entropyAtom]

/-- The normalized binary relative-potential density.  Subtracting the value
at the balanced point makes the density vanish at `p = 1/2` without inserting
an additional normalization constant. -/
def binaryDensity (p : ℝ) : ℝ :=
  entropyAtom p + entropyAtom (1 - p) - 2 * entropyAtom (1 / 2)

@[simp] theorem binaryDensity_half : binaryDensity (1 / 2) = 0 := by
  unfold binaryDensity
  have hhalf : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hhalf]
  ring

theorem binaryDensity_reflection (p : ℝ) :
    binaryDensity (1 - p) = binaryDensity p := by
  unfold binaryDensity entropyAtom
  simp only [sub_sub_cancel]
  ring

/-- Convexity of the normalized binary density, written in the form used by
the finite source ledgers. -/
theorem binaryDensity_convex_combination
    {p q lambda : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hl0 : 0 ≤ lambda) (hl1 : lambda ≤ 1) :
    binaryDensity (lambda * p + (1 - lambda) * q) ≤
      lambda * binaryDensity p + (1 - lambda) * binaryDensity q := by
  have hweight : lambda + (1 - lambda) = (1 : ℝ) := by ring
  have hp_mem : p ∈ Set.Ici (0 : ℝ) := hp0
  have hq_mem : q ∈ Set.Ici (0 : ℝ) := hq0
  have hcp_mem : 1 - p ∈ Set.Ici (0 : ℝ) := sub_nonneg.mpr hp1
  have hcq_mem : 1 - q ∈ Set.Ici (0 : ℝ) := sub_nonneg.mpr hq1
  have hpositive := Real.convexOn_mul_log.2 hp_mem hq_mem hl0
    (sub_nonneg.mpr hl1) hweight
  have hnegative := Real.convexOn_mul_log.2 hcp_mem hcq_mem hl0
    (sub_nonneg.mpr hl1) hweight
  simp only [smul_eq_mul] at hpositive hnegative
  unfold binaryDensity entropyAtom
  have hcomplement :
      1 - (lambda * p + (1 - lambda) * q) =
        lambda * (1 - p) + (1 - lambda) * (1 - q) := by ring
  rw [hcomplement]
  linarith

theorem binaryDensity_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binaryDensity p := by
  have h := binaryDensity_convex_combination
    (p := p) (q := 1 - p) (lambda := (1 / 2 : ℝ))
    hp0 hp1 (sub_nonneg.mpr hp1) (by linarith) (by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) * p + (1 - (1 / 2 : ℝ)) * (1 - p) = 1 / 2 := by
    ring
  rw [hmid, binaryDensity_half, binaryDensity_reflection] at h
  linarith

/-- Binary Pinsker inequality, including the two pure-sector endpoints.
Subtracting the quadratic term leaves a convex reflection-symmetric function
whose second derivative is `(2*p-1)^2 / (p*(1-p))`. -/
theorem half_central_square_le_binaryDensity {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 / 2 : ℝ) * (2 * p - 1) ^ 2 ≤ binaryDensity p := by
  let f : ℝ → ℝ := fun x => binaryDensity x - (1 / 2 : ℝ) * (2 * x - 1) ^ 2
  let f' : ℝ → ℝ := fun x => Real.log x - Real.log (1 - x) - (4 * x - 2)
  let f'' : ℝ → ℝ := fun x => 1 / x + 1 / (1 - x) - 4
  have hf : ContinuousOn f (Set.Icc 0 1) := by
    dsimp [f, binaryDensity, entropyAtom]
    fun_prop
  have hd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x := by
    intro x hx
    have hq : 1 - x ≠ 0 := by linarith [hx.2]
    have ha := Real.hasDerivAt_mul_log hx.1.ne'
    have hb := (Real.hasDerivAt_mul_log hq).comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
    have hc := ((((hasDerivAt_id x).const_mul 2).sub_const 1).pow 2).const_mul
      (1 / 2 : ℝ)
    convert ((ha.add hb).sub_const (2 * entropyAtom (1 / 2))).sub hc using 1 <;>
      (try ext y) <;> dsimp [f, f', binaryDensity, entropyAtom] <;> ring
  have hdd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt f' (f'' x) x := by
    intro x hx
    have hq : 1 - x ≠ 0 := by linarith [hx.2]
    have ha := Real.hasDerivAt_log hx.1.ne'
    have hb := (Real.hasDerivAt_log hq).comp x
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
    have hc := ((hasDerivAt_id x).const_mul 4).sub_const 2
    convert (ha.sub hb).sub hc using 1 <;>
      (try ext y) <;> dsimp [f', f''] <;> ring
  have hdd0 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ f'' x := by
    intro x hx
    have hq : 0 < 1 - x := sub_pos.mpr hx.2
    have heq : f'' x = (2 * x - 1) ^ 2 / (x * (1 - x)) := by
      dsimp [f'']
      field_simp [hx.1.ne', hq.ne']
      ring
    rw [heq]
    exact div_nonneg (sq_nonneg _) (mul_pos hx.1 hq).le
  have hconv : ConvexOn ℝ (Set.Icc 0 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hf
      (f' := f') (f'' := f'')
    · intro x hx
      exact (hd x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      exact (hdd x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      exact hdd0 x (by simpa only [interior_Icc] using hx)
  have h := hconv.2 (show p ∈ Set.Icc (0 : ℝ) 1 from ⟨hp0, hp1⟩)
    (show 1 - p ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) * p + (1 / 2 : ℝ) * (1 - p) = 1 / 2 := by ring
  have hreflect : f (1 - p) = f p := by
    dsimp [f]
    rw [binaryDensity_reflection]
    ring
  have hhalf : f (1 / 2) = 0 := by
    dsimp only [f]
    rw [binaryDensity_half]
    norm_num
  simp only [smul_eq_mul] at h
  rw [hmid, hhalf, hreflect] at h
  dsimp [f] at h
  linarith

/-- Fraction of the capacity in the positive central sector.  The value at
zero capacity is harmless because the full potential is defined separately
there. -/
def positiveFraction (x : CentrePair) : ℝ :=
  x.positive / capacity x

/-- Full non-normalized binary relative potential. -/
def relativePotential (x : CentrePair) : ℝ :=
  if capacity x = 0 then 0
  else capacity x * binaryDensity (positiveFraction x)

@[simp] theorem relativePotential_zero :
    relativePotential (CentrePair.mk 0 0) = 0 := by
  simp [relativePotential, capacity]

theorem positiveFraction_nonneg (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hcap : 0 ≤ capacity x) :
    0 ≤ positiveFraction x := by
  exact div_nonneg hpos hcap

theorem positiveFraction_le_one (x : CentrePair)
    (hneg : 0 ≤ x.negative) (hcap : 0 < capacity x) :
    positiveFraction x ≤ 1 := by
  unfold positiveFraction
  apply (div_le_one hcap).2
  unfold capacity
  linarith

theorem relativePotential_nonneg (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative) :
    0 ≤ relativePotential x := by
  by_cases hzero : capacity x = 0
  · simp [relativePotential, hzero]
  · have hcap0 : 0 ≤ capacity x := capacity_nonneg x hpos hneg
    have hcap : 0 < capacity x := lt_of_le_of_ne hcap0 (Ne.symm hzero)
    rw [relativePotential, if_neg hzero]
    exact mul_nonneg hcap0 <|
      binaryDensity_nonneg
        (positiveFraction_nonneg x hpos hcap0)
        (positiveFraction_le_one x hneg hcap)

/-- The full relative potential dominates one half of the quadratic central
potential.  This is the binary Pinsker comparison in the unnormalized sector
variables, including the zero-capacity case. -/
theorem half_quadraticPotential_le_relativePotential (x : CentrePair)
    (hpos : 0 ≤ x.positive) (hneg : 0 ≤ x.negative) :
    (1 / 2 : ℝ) * quadraticPotential x ≤ relativePotential x := by
  have hcap0 : 0 ≤ capacity x := capacity_nonneg x hpos hneg
  by_cases hzero : capacity x = 0
  · have hsigned : signed x = 0 := by
      simp only [signed, capacity] at hzero ⊢
      linarith
    simp [relativePotential, quadraticPotential, hzero, hsigned]
  · have hcap : 0 < capacity x := lt_of_le_of_ne hcap0 (Ne.symm hzero)
    have hp0 : 0 ≤ positiveFraction x :=
      positiveFraction_nonneg x hpos hcap0
    have hp1 : positiveFraction x ≤ 1 :=
      positiveFraction_le_one x hneg hcap
    have hbinary := half_central_square_le_binaryDensity hp0 hp1
    have hscaled := mul_le_mul_of_nonneg_left hbinary hcap0
    rw [relativePotential, if_neg hzero]
    calc
      (1 / 2 : ℝ) * quadraticPotential x =
          capacity x * ((1 / 2 : ℝ) *
            (2 * positiveFraction x - 1) ^ 2) := by
              have hden : x.positive + x.negative ≠ 0 := hzero
              unfold quadraticPotential positiveFraction signed capacity
              field_simp [hden]
              ring
      _ ≤ capacity x * binaryDensity (positiveFraction x) := hscaled

theorem positiveFraction_swap (x : CentrePair) (hcap : capacity x ≠ 0) :
    positiveFraction (swap x) = 1 - positiveFraction x := by
  simp only [positiveFraction, capacity_swap]
  change x.negative / capacity x = 1 - x.positive / capacity x
  field_simp [hcap]
  unfold capacity
  ring

@[simp] theorem relativePotential_swap (x : CentrePair) :
    relativePotential (swap x) = relativePotential x := by
  by_cases hcap : capacity x = 0
  · simp [relativePotential, hcap]
  · rw [relativePotential, relativePotential, if_neg hcap,
      if_neg (by simpa using hcap), capacity_swap,
      positiveFraction_swap x hcap, binaryDensity_reflection]

/-- Jensen--Shannon loss when two sources carrying the same central labels are
joined.  It is defined as the exact potential loss, not by a quadratic
approximation. -/
def joinJSDissipation (x y : CentrePair) : ℝ :=
  relativePotential x + relativePotential y - relativePotential (add x y)

/-- Jensen--Shannon loss when the second source first reverses its central
label. -/
def oppositeJSDissipation (x y : CentrePair) : ℝ :=
  relativePotential x + relativePotential y -
    relativePotential (oppositeMix x y)

/-- Exact ordinary Jensen--Shannon chain rule. -/
theorem relativePotential_join_chain (x y : CentrePair) :
    relativePotential (add x y) =
      relativePotential x + relativePotential y - joinJSDissipation x y := by
  unfold joinJSDissipation
  ring

/-- Exact opposite-centre Jensen--Shannon chain rule. -/
theorem relativePotential_opposite_chain (x y : CentrePair) :
    relativePotential (oppositeMix x y) =
      relativePotential x + relativePotential y - oppositeJSDissipation x y := by
  unfold oppositeJSDissipation
  ring

theorem oppositeJSDissipation_eq_join_swap (x y : CentrePair) :
    oppositeJSDissipation x y = joinJSDissipation x (swap y) := by
  simp [oppositeJSDissipation, joinJSDissipation, oppositeMix]

private theorem relativePotential_add_le_of_pos_capacity
    (x y : CentrePair)
    (hxpos : 0 ≤ x.positive) (hxneg : 0 ≤ x.negative)
    (hypos : 0 ≤ y.positive) (hyneg : 0 ≤ y.negative)
    (hcx : 0 < capacity x) (hcy : 0 < capacity y) :
    relativePotential (add x y) ≤
      relativePotential x + relativePotential y := by
  have hcxy : 0 < capacity x + capacity y := add_pos hcx hcy
  let lambda : ℝ := capacity x / (capacity x + capacity y)
  let p : ℝ := positiveFraction x
  let q : ℝ := positiveFraction y
  have hl0 : 0 ≤ lambda := div_nonneg hcx.le hcxy.le
  have hl1 : lambda ≤ 1 := by
    dsimp [lambda]
    rw [div_le_one hcxy]
    linarith
  have hp0 : 0 ≤ p := positiveFraction_nonneg x hxpos hcx.le
  have hp1 : p ≤ 1 := positiveFraction_le_one x hxneg hcx
  have hq0 : 0 ≤ q := positiveFraction_nonneg y hypos hcy.le
  have hq1 : q ≤ 1 := positiveFraction_le_one y hyneg hcy
  have hconv := binaryDensity_convex_combination hp0 hp1 hq0 hq1 hl0 hl1
  have hfrac :
      positiveFraction (add x y) = lambda * p + (1 - lambda) * q := by
    rw [positiveFraction, capacity_add]
    dsimp [positiveFraction, lambda, p, q]
    change (x.positive + y.positive) / (capacity x + capacity y) = _
    field_simp [ne_of_gt hcx, ne_of_gt hcy, ne_of_gt hcxy]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hconv hcxy.le
  rw [← hfrac] at hscaled
  have hx0 : capacity x ≠ 0 := ne_of_gt hcx
  have hy0 : capacity y ≠ 0 := ne_of_gt hcy
  have hxy0 : capacity (add x y) ≠ 0 := by
    simpa using ne_of_gt hcxy
  simp only [relativePotential, capacity_add, hx0, hy0, ne_of_gt hcxy, ↓reduceIte]
  dsimp [lambda] at hscaled
  have hleft :
      (capacity x + capacity y) *
          (capacity x / (capacity x + capacity y) * binaryDensity p +
            (1 - capacity x / (capacity x + capacity y)) * binaryDensity q) =
        capacity x * binaryDensity p + capacity y * binaryDensity q := by
    field_simp [ne_of_gt hcxy]
    ring
  rw [hleft] at hscaled
  exact hscaled

/-- Nonnegativity of the ordinary Jensen--Shannon loss, including empty
sectors and the zero-capacity source. -/
theorem joinJSDissipation_nonneg (x y : CentrePair)
    (hxpos : 0 ≤ x.positive) (hxneg : 0 ≤ x.negative)
    (hypos : 0 ≤ y.positive) (hyneg : 0 ≤ y.negative) :
    0 ≤ joinJSDissipation x y := by
  have hcx0 : 0 ≤ capacity x := capacity_nonneg x hxpos hxneg
  have hcy0 : 0 ≤ capacity y := capacity_nonneg y hypos hyneg
  by_cases hcx : capacity x = 0
  · have hxp : x.positive = 0 := by
      simp only [capacity] at hcx
      linarith
    have hxn : x.negative = 0 := by
      simp only [capacity] at hcx
      linarith
    cases x with
    | mk xp xn =>
        simp only at hxp hxn
        subst xp
        subst xn
        simp [joinJSDissipation, relativePotential, add, capacity, positiveFraction] <;>
          exact le_rfl
  · by_cases hcy : capacity y = 0
    · have hyp : y.positive = 0 := by
        simp only [capacity] at hcy
        linarith
      have hyn : y.negative = 0 := by
        simp only [capacity] at hcy
        linarith
      cases y with
      | mk yp yn =>
          simp only at hyp hyn
          subst yp
          subst yn
          simp [joinJSDissipation, relativePotential, add, capacity, positiveFraction] <;>
            exact le_rfl
    · unfold joinJSDissipation
      linarith [relativePotential_add_le_of_pos_capacity x y
        hxpos hxneg hypos hyneg
        (lt_of_le_of_ne hcx0 (Ne.symm hcx))
        (lt_of_le_of_ne hcy0 (Ne.symm hcy))]

/-- Nonnegativity of the opposite-centre Jensen--Shannon loss. -/
theorem oppositeJSDissipation_nonneg (x y : CentrePair)
    (hxpos : 0 ≤ x.positive) (hxneg : 0 ≤ x.negative)
    (hypos : 0 ≤ y.positive) (hyneg : 0 ≤ y.negative) :
    0 ≤ oppositeJSDissipation x y := by
  rw [oppositeJSDissipation_eq_join_swap]
  exact joinJSDissipation_nonneg x (swap y)
    hxpos hxneg hyneg hypos

/-- One exact finite generation stage for the full relative potential: first
mix an oppositely labelled source, then join the legal boundary/birth source.
The two Jensen--Shannon losses remain separate. -/
theorem oppositeMix_then_birth_relative_ledger
    (x y birth : CentrePair) :
    relativePotential (add (oppositeMix x y) birth) =
      relativePotential x + relativePotential y + relativePotential birth -
        oppositeJSDissipation x y -
        joinJSDissipation (oppositeMix x y) birth := by
  rw [relativePotential_join_chain, relativePotential_opposite_chain]
  ring

end GeneratedFoundations.Analysis.CenterRelativePotential
