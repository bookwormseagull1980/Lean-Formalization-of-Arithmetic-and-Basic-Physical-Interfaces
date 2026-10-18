module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Joint prime-occupation and scale space

The complete squarefree occupation source is the set of all finite sets of
prime directions.  It is not a finite prime cube: finite cubes are merely
restrictions of this type.  A prime toggle must be accompanied by the unique
scale change that leaves the dimensionless label-to-scale ratio unchanged.

This module records the algebraic core of that global action.  No Mobius sign
is supplied as source data.  The center character is a derived observation of
the positive occupation, and the Gaussian response is evaluated only after
the joint occupation--scale state has been formed.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.JointOccupationScale

open MeasureTheory

/-- A prime direction, carrying its primality proof. -/
abbrev PrimeIndex := {p : ℕ // Nat.Prime p}

/-- The complete squarefree occupation space.  Every point has finite support,
but there is no global prime cutoff. -/
abbrev Occupation := Finset PrimeIndex

/-- Positive observation scales. -/
abbrev PositiveScale := {L : ℝ // 0 < L}

/-- The positive natural label carried by a finite prime occupation. -/
def label (nu : Occupation) : ℕ := nu.prod fun p => p.1

/-- The center observation of a positive occupation. -/
def centerCharacter (nu : Occupation) : ℤ := nu.prod fun _ => (-1 : ℤ)

/-- Toggle one prime direction. -/
def toggle (p : PrimeIndex) (nu : Occupation) : Occupation :=
  if p ∈ nu then nu.erase p else insert p nu

@[simp] theorem mem_toggle_self (p : PrimeIndex) (nu : Occupation) :
    p ∈ toggle p nu ↔ p ∉ nu := by
  by_cases hp : p ∈ nu <;> simp [toggle, hp]

@[simp] theorem toggle_involution (p : PrimeIndex) (nu : Occupation) :
    toggle p (toggle p nu) = nu := by
  by_cases hp : p ∈ nu
  · simp [toggle, hp]
  · simp [toggle, hp]

/-- Toggling a prime reverses the derived center character. -/
theorem centerCharacter_toggle (p : PrimeIndex) (nu : Occupation) :
    centerCharacter (toggle p nu) = -centerCharacter nu := by
  by_cases hp : p ∈ nu
  · have hprod := Finset.prod_erase_mul nu
      (fun _ : PrimeIndex => (-1 : ℤ)) hp
    simp only [centerCharacter, toggle, hp, ↓reduceIte]
    rw [← hprod]
    ring
  · simp only [centerCharacter, toggle, hp, ↓reduceIte,
      Finset.prod_insert hp]
    ring

/-- The matching scale transport: remove an occupied prime and divide the
scale by it, or insert an unoccupied prime and multiply the scale by it. -/
def transportScale (p : PrimeIndex) (nu : Occupation)
    (L : PositiveScale) : PositiveScale :=
  if p ∈ nu then
    ⟨L.1 / (p.1 : ℝ), div_pos L.2 (Nat.cast_pos.mpr p.2.pos)⟩
  else
    ⟨(p.1 : ℝ) * L.1, mul_pos (Nat.cast_pos.mpr p.2.pos) L.2⟩

/-- The global joint prime flip on occupation and positive scale. -/
def jointFlip (p : PrimeIndex) :
    Occupation × PositiveScale → Occupation × PositiveScale :=
  fun x => (toggle p x.1, transportScale p x.1 x.2)

/-- The dimensionless coordinate seen by every scale-covariant response. -/
def ratio (x : Occupation × PositiveScale) : ℝ :=
  (label x.1 : ℝ) / x.2.1

/-- The generated Gaussian-difference response on the joint source. -/
def gaussianResponse (x : Occupation × PositiveScale) : ℝ :=
  Real.exp (-(ratio x) ^ 2) - Real.exp (-Real.pi * (ratio x) ^ 2)

/-- The matching scale transport is itself reversed by the returned
occupation. -/
theorem transportScale_involution (p : PrimeIndex) (nu : Occupation)
    (L : PositiveScale) :
    transportScale p (toggle p nu) (transportScale p nu L) = L := by
  apply Subtype.ext
  by_cases hp : p ∈ nu
  · simp [transportScale, toggle, hp]
    field_simp [Nat.ne_of_gt p.2.pos]
  · simp [transportScale, toggle, hp]
    field_simp [Nat.ne_of_gt p.2.pos]

/-- The occupation--scale transformation is a global involution on all finite
prime occupations, not merely on a chosen finite cylinder. -/
@[simp] theorem jointFlip_involution (p : PrimeIndex)
    (x : Occupation × PositiveScale) :
    jointFlip p (jointFlip p x) = x := by
  rcases x with ⟨nu, L⟩
  apply Prod.ext
  · exact toggle_involution p nu
  · exact transportScale_involution p nu L

/-- The positive label and the scale acquire the same prime factor. -/
theorem ratio_jointFlip (p : PrimeIndex)
    (x : Occupation × PositiveScale) :
    ratio (jointFlip p x) = ratio x := by
  rcases x with ⟨nu, L⟩
  by_cases hp : p ∈ nu
  · have hprod := Finset.prod_erase_mul nu
      (fun q : PrimeIndex => q.1) hp
    simp only [ratio, jointFlip, label, toggle, transportScale, hp, ↓reduceIte]
    rw [← hprod]
    push_cast
    field_simp [Nat.ne_of_gt p.2.pos]
  · simp only [ratio, jointFlip, label, toggle, transportScale, hp, ↓reduceIte]
    rw [Finset.prod_insert hp]
    push_cast
    field_simp [Nat.ne_of_gt p.2.pos]

/-- Every response depending only on the dimensionless ratio is invariant
under the joint prime flip. -/
theorem response_jointFlip (p : PrimeIndex)
    (F : ℝ → ℝ) (x : Occupation × PositiveScale) :
    F (ratio (jointFlip p x)) = F (ratio x) := by
  rw [ratio_jointFlip]

/-- In particular, the native Gaussian-difference response is invariant. -/
@[simp] theorem gaussianResponse_jointFlip (p : PrimeIndex)
    (x : Occupation × PositiveScale) :
    gaussianResponse (jointFlip p x) = gaussianResponse x := by
  unfold gaussianResponse
  rw [ratio_jointFlip]

/-- The center observation reverses while the positive Gaussian magnitude is
unchanged.  This is the finite-state algebra behind the global center pairing. -/
theorem center_gaussian_jointFlip (p : PrimeIndex)
    (x : Occupation × PositiveScale) :
    (centerCharacter (jointFlip p x).1 : ℝ) * gaussianResponse (jointFlip p x) =
      -((centerCharacter x.1 : ℝ) * gaussianResponse x) := by
  rw [gaussianResponse_jointFlip]
  change (centerCharacter (toggle p x.1) : ℝ) * gaussianResponse x =
    -((centerCharacter x.1 : ℝ) * gaussianResponse x)
  rw [centerCharacter_toggle]
  push_cast
  ring

/-! ## Logarithmic scale and the global measure-preserving action -/

/-- Occupations carry the discrete sigma algebra.  This is the measurable
structure belonging to counting measure; it does not select a finite prime
cylinder. -/
noncomputable instance occupationMeasurableSpace : MeasurableSpace Occupation := ⊤

/-- The prime toggle as a measurable involutive equivalence of the complete
occupation space. -/
def toggleEquiv (p : PrimeIndex) : Occupation ≃ᵐ Occupation where
  toFun := toggle p
  invFun := toggle p
  left_inv := toggle_involution p
  right_inv := toggle_involution p
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

/-- Counting measure is unchanged by a prime toggle. -/
theorem toggle_measurePreserving (p : PrimeIndex) :
    MeasurePreserving (toggle p) Measure.count Measure.count := by
  change MeasurePreserving (toggleEquiv p) Measure.count Measure.count
  refine ⟨(toggleEquiv p).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (toggleEquiv p).measurable hs,
    Measure.count_apply (hs.preimage (toggleEquiv p).measurable),
    Measure.count_apply hs]
  exact congrArg ENat.toENNReal
    (Set.encard_preimage_of_bijective (toggleEquiv p).bijective s)

/-- Translation in logarithmic scale corresponding to insertion or removal of
one prime. -/
def logShift (p : PrimeIndex) (nu : Occupation) : ℝ :=
  if p ∈ nu then -Real.log (p.1 : ℝ) else Real.log (p.1 : ℝ)

/-- The joint action in logarithmic scale.  Lebesgue measure in this coordinate
is exactly logarithmic scale measure `dL/L`. -/
def logJointFlip (p : PrimeIndex) : Occupation × ℝ → Occupation × ℝ :=
  fun x => (toggle p x.1, x.2 + logShift p x.1)

@[simp] theorem logJointFlip_involution (p : PrimeIndex)
    (x : Occupation × ℝ) :
    logJointFlip p (logJointFlip p x) = x := by
  rcases x with ⟨nu, u⟩
  apply Prod.ext
  · exact toggle_involution p nu
  · by_cases hp : p ∈ nu <;> simp [logJointFlip, logShift, toggle, hp]

theorem logJointFlip_measurable (p : PrimeIndex) : Measurable (logJointFlip p) := by
  apply Measurable.prodMk
  · exact (toggleEquiv p).measurable.comp measurable_fst
  · exact measurable_snd.add
      ((measurable_of_countable (logShift p)).comp measurable_fst)

/-- The logarithmic joint action as a measurable involution. -/
def logJointFlipEquiv (p : PrimeIndex) :
    (Occupation × ℝ) ≃ᵐ (Occupation × ℝ) where
  toFun := logJointFlip p
  invFun := logJointFlip p
  left_inv := logJointFlip_involution p
  right_inv := logJointFlip_involution p
  measurable_toFun := logJointFlip_measurable p
  measurable_invFun := logJointFlip_measurable p

/-- Counting measure on all finite occupations times Lebesgue measure in log
scale. -/
def jointMeasure : Measure (Occupation × ℝ) := Measure.count.prod volume

/-- The joint center action preserves the complete occupation--scale measure.
This is the measure-theoretic form of the exact endpoint-free source closure. -/
theorem logJointFlip_measurePreserving (p : PrimeIndex) :
    MeasurePreserving (logJointFlip p) jointMeasure jointMeasure := by
  have h := (toggle_measurePreserving p).skew_product
    (measurable_snd.add
      ((measurable_of_countable (logShift p)).comp measurable_fst))
    (ae_of_all Measure.count fun nu =>
      (measurePreserving_add_right volume (logShift p nu)).map_eq)
  change MeasurePreserving
    (fun x : Occupation × ℝ => (toggle p x.1, x.2 + logShift p x.1))
    (Measure.count.prod volume) (Measure.count.prod volume)
  exact h

/-- Exponentiation identifies logarithmic scale with the earlier positive
scale state. -/
def expState (x : Occupation × ℝ) : Occupation × PositiveScale :=
  (x.1, ⟨Real.exp x.2, Real.exp_pos x.2⟩)

/-- The logarithmic measure-preserving action and the positive-scale action
are the same transformation in the two scale coordinates. -/
theorem expState_logJointFlip (p : PrimeIndex) (x : Occupation × ℝ) :
    expState (logJointFlip p x) = jointFlip p (expState x) := by
  rcases x with ⟨nu, u⟩
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    by_cases hp : p ∈ nu
    · simp only [expState, logJointFlip, logShift, hp, ↓reduceIte,
        jointFlip, transportScale]
      rw [show u + -Real.log (p.1 : ℝ) = u - Real.log (p.1 : ℝ) by ring]
      rw [Real.exp_sub, Real.exp_log (Nat.cast_pos.mpr p.2.pos)]
    · simp only [expState, logJointFlip, logShift, hp, ↓reduceIte,
        jointFlip, transportScale]
      rw [Real.exp_add, Real.exp_log (Nat.cast_pos.mpr p.2.pos)]
      ring

/-- Any scale-covariant response, and in particular the native Gaussian
response, is invariant in logarithmic coordinates. -/
@[simp] theorem gaussianResponse_expState_logJointFlip (p : PrimeIndex)
    (x : Occupation × ℝ) :
    gaussianResponse (expState (logJointFlip p x)) =
      gaussianResponse (expState x) := by
  rw [expState_logJointFlip, gaussianResponse_jointFlip]

/-- An integrable center-odd observable has exactly zero total response on the
complete occupation--scale source.  This theorem is global; finite cylinders
are computational restrictions, not part of its statement. -/
theorem integral_centerOdd_eq_zero (p : PrimeIndex)
    (F : Occupation × ℝ → ℝ) (_hF : Integrable F jointMeasure)
    (hodd : ∀ x, F (logJointFlip p x) = -F x) :
    ∫ x, F x ∂jointMeasure = 0 := by
  have hmp : MeasurePreserving (logJointFlipEquiv p) jointMeasure jointMeasure := by
    change MeasurePreserving (logJointFlip p) jointMeasure jointMeasure
    exact logJointFlip_measurePreserving p
  have hchange := hmp.integral_comp' F
  have hchange' : (∫ x, F (logJointFlip p x) ∂jointMeasure) =
      ∫ x, F x ∂jointMeasure := by
    change (∫ x, F (logJointFlip p x) ∂jointMeasure) =
      ∫ x, F x ∂jointMeasure at hchange
    exact hchange
  have hneg : (∫ x, F (logJointFlip p x) ∂jointMeasure) =
      -(∫ x, F x ∂jointMeasure) := by
    calc
      (∫ x, F (logJointFlip p x) ∂jointMeasure) =
          ∫ x, -F x ∂jointMeasure := by
            apply integral_congr_ae
            exact ae_of_all _ hodd
      _ = -(∫ x, F x ∂jointMeasure) := integral_neg F
  have hself : (∫ x, F x ∂jointMeasure) =
      -(∫ x, F x ∂jointMeasure) := hchange'.symm.trans hneg
  linarith

/-! ## Complete joint-source conclusion -/

/-- The complete occupation--scale source, its generated center observation,
and its native Gaussian response form one globally closed system.  This
structure packages the proved statements so that downstream mathematical and
physical realizations inherit the same object rather than choosing separate
finite models. -/
structure Conclusions : Prop where
  occupation_scale_involution :
    ∀ (p : PrimeIndex) (x : Occupation × PositiveScale),
      jointFlip p (jointFlip p x) = x
  center_reversal :
    ∀ (p : PrimeIndex) (nu : Occupation),
      centerCharacter (toggle p nu) = -centerCharacter nu
  ratio_invariance :
    ∀ (p : PrimeIndex) (x : Occupation × PositiveScale),
      ratio (jointFlip p x) = ratio x
  gaussian_invariance :
    ∀ (p : PrimeIndex) (x : Occupation × PositiveScale),
      gaussianResponse (jointFlip p x) = gaussianResponse x
  complete_measure_invariance :
    ∀ p : PrimeIndex,
      MeasurePreserving (logJointFlip p) jointMeasure jointMeasure
  global_center_closure :
    ∀ (p : PrimeIndex) (F : Occupation × ℝ → ℝ),
      Integrable F jointMeasure →
      (∀ x, F (logJointFlip p x) = -F x) →
      ∫ x, F x ∂jointMeasure = 0

/-- The global joint source satisfies the complete occupation--scale closure
without a finite prime cutoff or an externally supplied driving term. -/
theorem jointOccupationScaleConclusions : Conclusions where
  occupation_scale_involution := jointFlip_involution
  center_reversal := centerCharacter_toggle
  ratio_invariance := ratio_jointFlip
  gaussian_invariance := gaussianResponse_jointFlip
  complete_measure_invariance := logJointFlip_measurePreserving
  global_center_closure := integral_centerOdd_eq_zero

end GeneratedFoundations.Arithmetic.JointOccupationScale
