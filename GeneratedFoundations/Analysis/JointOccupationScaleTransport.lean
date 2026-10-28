module

public import GeneratedFoundations.Analysis.NaturalSourceScaleBudget
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Actual Gaussian density under joint occupation--scale transport

The joint prime flip preserves counting measure times logarithmic scale
measure.  The observation weight is a separate, already generated function
on this same space.  Its exact change supplies a positive half-density
factor; no transition rate or additional source is introduced.

The quadratic identity below uses a nonnegative integral, so it remains an
identity even when a budget is infinite.  It must not be interpreted as a
finiteness theorem or as invariance of the actual constant source vector.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.JointOccupationScaleTransport

open MeasureTheory
open GeneratedFoundations.Arithmetic.JointOccupationScale
open CanonicalMobiusReadout NaturalSourceScaleBudget PrimeCylinderScaleBudget
open scoped ENNReal

/-- The original generated Gaussian response in logarithmic scale. -/
def gaussianProfile (x : Occupation × ℝ) : ℝ :=
  gaussianResponse (expState x)

theorem label_pos (nu : Occupation) : 0 < label nu := by
  exact Finset.prod_pos (fun p _ => p.2.pos)

theorem gaussianProfile_eq_window (nu : Occupation) (u : ℝ) :
    gaussianProfile (nu, u) = gaussianWindowMass (Real.exp u) (label nu) := by
  exact gaussianResponse_eq_window nu ⟨Real.exp u, Real.exp_pos u⟩

theorem gaussianProfile_translation (nu : Occupation) (u : ℝ) :
    gaussianProfile (nu, u) = potentialProfile ∅ (u - Real.log (label nu : ℝ)) := by
  rw [gaussianProfile_eq_window, gaussian_label_translation (label_pos nu)]

theorem gaussianProfile_pos (x : Occupation × ℝ) : 0 < gaussianProfile x := by
  have hr : 0 < ratio (expState x) :=
    div_pos (Nat.cast_pos.mpr (label_pos x.1)) (Real.exp_pos x.2)
  have hpi : 1 < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
  change 0 < Real.exp (-(ratio (expState x)) ^ 2) -
    Real.exp (-Real.pi * (ratio (expState x)) ^ 2)
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  nlinarith [sq_pos_of_pos hr]

@[simp] theorem gaussianProfile_flip (p : PrimeIndex) (x : Occupation × ℝ) :
    gaussianProfile (logJointFlip p x) = gaussianProfile x :=
  gaussianResponse_expState_logJointFlip p x

@[simp] theorem logShift_toggle (p : PrimeIndex) (nu : Occupation) :
    logShift p (toggle p nu) = -logShift p nu := by
  by_cases hp : p ∈ nu <;> simp [logShift, toggle, hp]

/-- The actual scale weight multiplies the original Gaussian magnitude.
`sigma` is the observation exponent, not an input to the generated source. -/
def weightedDensity (sigma : ℝ) (x : Occupation × ℝ) : ℝ :=
  Real.exp (-2 * sigma * x.2) * gaussianProfile x

theorem weightedDensity_pos (sigma : ℝ) (x : Occupation × ℝ) :
    0 < weightedDensity sigma x :=
  mul_pos (Real.exp_pos _) (gaussianProfile_pos x)

theorem weightedDensity_flip (sigma : ℝ) (p : PrimeIndex)
    (x : Occupation × ℝ) :
    weightedDensity sigma (logJointFlip p x) =
      Real.exp (-2 * sigma * logShift p x.1) * weightedDensity sigma x := by
  simp only [weightedDensity, gaussianProfile_flip]
  change Real.exp (-2 * sigma * (x.2 + logShift p x.1)) * gaussianProfile x = _
  rw [show -2 * sigma * (x.2 + logShift p x.1) =
    -2 * sigma * logShift p x.1 + -2 * sigma * x.2 by ring, Real.exp_add]
  ring

/-- The positive half-density fixed by the actual density ratio. -/
def halfDensityFactor (sigma : ℝ) (p : PrimeIndex)
    (x : Occupation × ℝ) : ℝ := Real.exp (-sigma * logShift p x.1)

theorem halfDensityFactor_pos (sigma : ℝ) (p : PrimeIndex)
    (x : Occupation × ℝ) : 0 < halfDensityFactor sigma p x := Real.exp_pos _

theorem halfDensityFactor_sq (sigma : ℝ) (p : PrimeIndex)
    (x : Occupation × ℝ) :
    (halfDensityFactor sigma p x) ^ 2 =
      Real.exp (-2 * sigma * logShift p x.1) := by
  rw [halfDensityFactor, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem halfDensityFactor_flip_mul (sigma : ℝ) (p : PrimeIndex)
    (x : Occupation × ℝ) :
    halfDensityFactor sigma p x *
      halfDensityFactor sigma p (logJointFlip p x) = 1 := by
  simp only [halfDensityFactor, logJointFlip, logShift_toggle]
  calc
    _ = Real.exp 0 := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = 1 := Real.exp_zero

/-- Positivity and the actual density ratio uniquely fix the compensator. -/
theorem halfDensityFactor_unique (sigma : ℝ) (p : PrimeIndex)
    (x : Occupation × ℝ) {r : ℝ} (hr : 0 ≤ r)
    (h : weightedDensity sigma x * r ^ 2 =
      weightedDensity sigma (logJointFlip p x)) :
    r = halfDensityFactor sigma p x := by
  have hd := weightedDensity_pos sigma x
  have hf := halfDensityFactor_pos sigma p x
  rw [weightedDensity_flip, ← halfDensityFactor_sq] at h
  have hs : r ^ 2 = (halfDensityFactor sigma p x) ^ 2 := by
    nlinarith
  nlinarith

/-- Transport of real amplitudes on the same complete generated source. -/
def halfDensityTransport (sigma : ℝ) (p : PrimeIndex)
    (F : Occupation × ℝ → ℝ) (x : Occupation × ℝ) : ℝ :=
  halfDensityFactor sigma p x * F (logJointFlip p x)

theorem halfDensityTransport_involution (sigma : ℝ) (p : PrimeIndex)
    (F : Occupation × ℝ → ℝ) :
    halfDensityTransport sigma p (halfDensityTransport sigma p F) = F := by
  funext x
  simp only [halfDensityTransport, logJointFlip_involution]
  rw [← mul_assoc, halfDensityFactor_flip_mul, one_mul]

/-- Multiplication by the actual Gaussian response commutes with transport. -/
theorem halfDensityTransport_gaussian (sigma : ℝ) (p : PrimeIndex)
    (F : Occupation × ℝ → ℝ) (x : Occupation × ℝ) :
    halfDensityTransport sigma p (fun y => gaussianProfile y * F y) x =
      gaussianProfile x * halfDensityTransport sigma p F x := by
  simp only [halfDensityTransport, gaussianProfile_flip]
  ring

/-- The same transport reverses the generated center observation. -/
theorem halfDensityTransport_center (sigma : ℝ) (p : PrimeIndex)
    (F : Occupation × ℝ → ℝ) (x : Occupation × ℝ) :
    halfDensityTransport sigma p (fun y => (centerCharacter y.1 : ℝ) * F y) x =
      -(centerCharacter x.1 : ℝ) * halfDensityTransport sigma p F x := by
  simp only [halfDensityTransport, logJointFlip, centerCharacter_toggle, Int.cast_neg]
  ring

/-- The full quadratic density, including the transported amplitude. -/
theorem quadratic_density_transport (sigma : ℝ) (p : PrimeIndex)
    (F : Occupation × ℝ → ℝ) (x : Occupation × ℝ) :
    weightedDensity sigma x * (halfDensityTransport sigma p F x) ^ 2 =
      weightedDensity sigma (logJointFlip p x) * (F (logJointFlip p x)) ^ 2 := by
  rw [halfDensityTransport, mul_pow, halfDensityFactor_sq, weightedDensity_flip]
  ring

/-- Nonnegative quadratic budget on the original complete source.  Its
definition does not replace an infinite integral by a finite default value. -/
def quadraticBudget (sigma : ℝ) (F : Occupation × ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (weightedDensity sigma x * (F x) ^ 2) ∂jointMeasure

/-- Exact isometry of the actual weighted quadratic form, allowing infinity.
This is a transport identity, not invariance of the source vector `1`. -/
theorem quadraticBudget_transport (sigma : ℝ) (p : PrimeIndex)
    (F : Occupation × ℝ → ℝ) :
    quadraticBudget sigma (halfDensityTransport sigma p F) =
      quadraticBudget sigma F := by
  unfold quadraticBudget
  simp_rw [quadratic_density_transport]
  have hmp : MeasurePreserving (logJointFlipEquiv p) jointMeasure jointMeasure :=
    logJointFlip_measurePreserving p
  exact hmp.lintegral_comp_emb (logJointFlipEquiv p).measurableEmbedding
    (fun x => ENNReal.ofReal (weightedDensity sigma x * (F x) ^ 2))

theorem halfDensityFactor_lt_one_of_absent {sigma : ℝ} (hsigma : 0 < sigma)
    (p : PrimeIndex) (x : Occupation × ℝ) (hp : p ∉ x.1) :
    halfDensityFactor sigma p x < 1 := by
  have hp' : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  apply Real.exp_lt_one_iff.mpr
  simp only [logShift, hp, ↓reduceIte]
  nlinarith [mul_pos hsigma (Real.log_pos hp')]

/-- The actual scale-weighted density is not preserved by prime insertion. -/
theorem weightedDensity_flip_lt_of_absent {sigma : ℝ} (hsigma : 0 < sigma)
    (p : PrimeIndex) (x : Occupation × ℝ) (hp : p ∉ x.1) :
    weightedDensity sigma (logJointFlip p x) < weightedDensity sigma x := by
  rw [weightedDensity_flip]
  have hfac : Real.exp (-2 * sigma * logShift p x.1) < 1 := by
    have hp' : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
    apply Real.exp_lt_one_iff.mpr
    simp only [logShift, hp, ↓reduceIte]
    nlinarith [mul_pos hsigma (Real.log_pos hp')]
  simpa using mul_lt_mul_of_pos_right hfac (weightedDensity_pos sigma x)

/-- Even the empty-occupation source amplitude changes.  Unitary transport
and an invariant source state are different assertions. -/
theorem constant_source_not_fixed {sigma : ℝ} (hsigma : 0 < sigma)
    (p : PrimeIndex) :
    halfDensityTransport sigma p (fun _ => 1) ≠ (fun _ => 1) := by
  intro h
  have heq := congrFun h (∅, 0)
  have hlt := halfDensityFactor_lt_one_of_absent hsigma p (∅, 0) (by simp)
  simp only [halfDensityTransport, mul_one] at heq
  exact (ne_of_lt hlt) heq

/-! ## Integrability of the actual unweighted complete source -/

/-- Every occupation has the same unweighted scale integral, by the exact
translation of the original Gaussian.  This identity alone asserts no
integrability. -/
theorem gaussianProfile_slice_integral (nu : Occupation) :
    (∫ u : ℝ, gaussianProfile (nu, u)) =
      ∫ u : ℝ, potentialProfile ∅ u := by
  simp_rw [gaussianProfile_translation]
  exact integral_sub_right_eq_self (potentialProfile ∅) (Real.log (label nu : ℝ))

/-- The Gaussian response on all finite occupations and all log scales is
not integrable against the invariant base measure.  Thus the integrable-odd
closure theorem cannot supply a finite Gaussian expectation on this base
measure.  This does not affect the separately weighted scale budgets. -/
theorem gaussianProfile_not_integrable :
    ¬ Integrable gaussianProfile jointMeasure := by
  classical
  intro h
  have hprod : Integrable gaussianProfile (Measure.count.prod volume) := h
  have hs : ∀ nu : Occupation,
      Integrable (fun u : ℝ => gaussianProfile (nu, u)) :=
    Measure.ae_count_iff.mp hprod.prod_right_ae
  have hb : Integrable (potentialProfile ∅) := by
    simpa only [gaussianProfile_translation, label, Finset.prod_empty,
      Nat.cast_one, Real.log_one, sub_zero] using hs ∅
  have hbpos : ∀ u : ℝ, 0 < potentialProfile ∅ u := by
    intro u
    simpa only [gaussianProfile_translation, label, Finset.prod_empty,
      Nat.cast_one, Real.log_one, sub_zero] using gaussianProfile_pos (∅, u)
  have hsupport : Function.support (potentialProfile ∅) = Set.univ := by
    ext u
    simp only [Function.mem_support, ne_eq, (hbpos u).ne', not_false_eq_true,
      Set.mem_univ]
  have hpositive : 0 < ∫ u : ℝ, potentialProfile ∅ u := by
    apply (integral_pos_iff_support_of_nonneg (fun u => (hbpos u).le) hb).mpr
    rw [hsupport]
    simp
  have hi : Integrable (fun _ : Occupation =>
      ∫ u : ℝ, potentialProfile ∅ u) Measure.count := by
    have hi' := hprod.integral_prod_left
    simpa only [gaussianProfile_slice_integral] using hi'
  let : Infinite PrimeIndex := Nat.Primes.infinite
  let : Infinite Occupation := Infinite.of_injective
    (fun p : PrimeIndex => ({p} : Occupation)) Finset.singleton_injective
  let : IsFiniteMeasure (Measure.count : Measure Occupation) :=
    (integrable_const_iff_isFiniteMeasure hpositive.ne').mp hi
  exact (measure_ne_top (Measure.count : Measure Occupation) Set.univ)
    (Measure.count_apply_infinite Set.infinite_univ)

/-- The center character has unit magnitude on every positive occupation. -/
theorem abs_centerCharacter (nu : Occupation) :
    |(centerCharacter nu : ℝ)| = 1 := by
  have h : |centerCharacter nu| = 1 := by
    simp [centerCharacter]
  exact_mod_cast h

/-- The original center-odd Gaussian observation on the invariant base space. -/
def centerGaussianProfile (x : Occupation × ℝ) : ℝ :=
  (centerCharacter x.1 : ℝ) * gaussianProfile x

theorem norm_centerGaussianProfile (x : Occupation × ℝ) :
    ‖centerGaussianProfile x‖ = gaussianProfile x := by
  rw [Real.norm_eq_abs, centerGaussianProfile, abs_mul, abs_centerCharacter,
    one_mul, abs_of_pos (gaussianProfile_pos x)]

/-- In particular the actual odd Gaussian observation does not satisfy the
integrability premise of the global odd-observation closure theorem. -/
theorem centerGaussianProfile_not_integrable :
    ¬ Integrable centerGaussianProfile jointMeasure := by
  intro h
  apply gaussianProfile_not_integrable
  simpa only [norm_centerGaussianProfile] using h.norm

end GeneratedFoundations.Analysis.JointOccupationScaleTransport
