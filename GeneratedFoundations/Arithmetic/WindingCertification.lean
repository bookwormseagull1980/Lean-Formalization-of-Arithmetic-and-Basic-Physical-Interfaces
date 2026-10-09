module

public import GeneratedFoundations.Arithmetic.NativePeano
public import GeneratedFoundations.Spectral.NeumannScaleTransport
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Winding-integral certification of the native circle maps

The winding integral is evaluated on one positively oriented traversal of
the actual unit circle. The derivative is taken on the composed curve,
not assigned from a degree label. Classification of continuous circle
endomorphisms proves smoothness and evaluates this integral at an integer.
On native modes it agrees with the arithmetic coordinate constructed after
the pointwise and compositional operations.

This calculation concerns the endomorphisms themselves. It does not classify
homotopy classes of arbitrary continuous maps.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.WindingCertification

open CircleEndomorphisms NativeModes
open GeneratedFoundations.Spectral

def curve (u : Circle →ₜ* Circle) (t : ℝ) : ℂ := (u (Circle.exp t) : ℂ)

theorem curve_ne_zero (u : Circle →ₜ* Circle) (t : ℝ) : curve u t ≠ 0 :=
  (u (Circle.exp t)).coe_ne_zero

def logarithmicDerivative (u : Circle →ₜ* Circle) (t : ℝ) : ℂ :=
  (curve u t)⁻¹ * deriv (curve u) t

/-- The parametrized integral of `u⁻¹ du` over one positive circle traversal. -/
def degreeIntegral (u : Circle →ₜ* Circle) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * Complex.I)⁻¹ *
    ∫ t in (0 : ℝ)..(2 * Real.pi), logarithmicDerivative u t

theorem curve_power (n : ℤ) :
    curve (powerEndomorphism n) =
      fun t : ℝ => Complex.exp ((n : ℂ) * ((t : ℂ) * Complex.I)) := by
  funext t
  simp only [curve, powerEndomorphism_apply, Circle.coe_zpow, Circle.coe_exp,
    Complex.exp_int_mul]

theorem curve_power_hasDerivAt (n : ℤ) (t : ℝ) :
    HasDerivAt (curve (powerEndomorphism n))
      (curve (powerEndomorphism n) t * ((n : ℂ) * Complex.I)) t := by
  rw [curve_power]
  simpa only [id_eq, Complex.ofReal_one, one_mul] using
    ((((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).const_mul (n : ℂ)).cexp

theorem logarithmicDerivative_power (n : ℤ) (t : ℝ) :
    logarithmicDerivative (powerEndomorphism n) t = (n : ℂ) * Complex.I := by
  unfold logarithmicDerivative
  rw [(curve_power_hasDerivAt n t).deriv, ← mul_assoc,
    inv_mul_cancel₀ (curve_ne_zero _ _), one_mul]

theorem logarithmicDerivative_integrable (u : Circle →ₜ* Circle) :
    IntervalIntegrable (logarithmicDerivative u) MeasureTheory.volume 0 (2 * Real.pi) := by
  obtain ⟨n, rfl, _⟩ := circleEndomorphism_classification u
  have heq : logarithmicDerivative (powerEndomorphism n) =
      fun _ : ℝ => (n : ℂ) * Complex.I := funext (logarithmicDerivative_power n)
  rw [heq]
  exact intervalIntegrable_const

theorem degreeIntegral_power (n : ℤ) : degreeIntegral (powerEndomorphism n) = n := by
  have hperiod : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (two_ne_zero : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have hperiod_complex : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hperiod
  have hnormal : (((2 * Real.pi : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero hperiod_complex Complex.I_ne_zero
  unfold degreeIntegral
  simp_rw [logarithmicDerivative_power]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  have horder : ((2 * Real.pi : ℝ) : ℂ) * ((n : ℂ) * Complex.I) =
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * (n : ℂ) := by ring
  rw [horder, ← mul_assoc, inv_mul_cancel₀ hnormal, one_mul]

theorem degreeIntegral_integer_unique (u : Circle →ₜ* Circle) :
    ∃! n : ℤ, degreeIntegral u = (n : ℂ) := by
  obtain ⟨n, rfl, _⟩ := circleEndomorphism_classification u
  refine ⟨n, degreeIntegral_power n, ?_⟩
  intro m hm
  rw [degreeIntegral_power] at hm
  exact_mod_cast hm.symm

theorem degreeIntegral_native (u : Mode) : degreeIntegral u.val = (index u : ℂ) := by
  obtain ⟨n, rfl⟩ := powerMode_surjective u
  rw [index_powerMode]
  simpa only [powerMode, Int.cast_natCast] using
    degreeIntegral_power (n : ℤ)

/-- The already constructed arithmetic coordinate is certified by the integral. -/
def degreeEquiv : Mode ≃+* ℕ := powerModeEquiv.symm

theorem degreeEquiv_eq_index (u : Mode) : degreeEquiv u = index u := by
  apply powerMode_injective
  change powerModeEquiv (powerModeEquiv.symm u) = powerMode (index u)
  rw [powerModeEquiv.apply_symm_apply, powerMode_index]

theorem degreeEquiv_integral (u : Mode) : (degreeEquiv u : ℂ) = degreeIntegral u.val := by
  rw [degreeEquiv_eq_index, degreeIntegral_native]

theorem degreeIntegral_add (u v : Mode) :
    degreeIntegral (u + v).val = degreeIntegral u.val + degreeIntegral v.val := by
  rw [← degreeEquiv_integral, ← degreeEquiv_integral, ← degreeEquiv_integral,
    map_add, Nat.cast_add]

theorem degreeIntegral_mul (u v : Mode) :
    degreeIntegral (u * v).val = degreeIntegral u.val * degreeIntegral v.val := by
  rw [← degreeEquiv_integral, ← degreeEquiv_integral, ← degreeEquiv_integral,
    map_mul, Nat.cast_mul]

theorem degreeIntegral_injective : Function.Injective (fun u : Mode => degreeIntegral u.val) := by
  intro u v h
  apply degreeEquiv.injective
  have he : (degreeEquiv u : ℂ) = (degreeEquiv v : ℂ) := by
    simpa only [degreeEquiv_integral] using h
  exact_mod_cast he

theorem degree_from_energy (L : ℝ) [Fact (0 < L)] (u : Mode) :
    (degreeEquiv u : ℝ) =
      Real.sqrt (neumannEigenvalue L (index u) / NeumannScaleTransport.energyUnit L) := by
  rw [degreeEquiv_eq_index, NeumannScaleTransport.normalized_eigenvalue,
    Real.sqrt_sq (Nat.cast_nonneg _)]

end GeneratedFoundations.Arithmetic.WindingCertification
