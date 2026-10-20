module

public import GeneratedFoundations.Arithmetic.HistoryJointChargeLattice
public import Mathlib.Data.Int.GCD

/-!
# Integral competitors of the actual joint history charge

The two coefficients below are initially real. Integrality on the retained
source sectors forces them to be integers: the detail left weight gives the
relative coefficient, and subtracting it from the detail upper weight gives
the right coefficient. Thus the integer lattice used in the primitive
classification is a consequence of the realization, not an extra input.

The right generator here has weights `0,0,1,-1`; it is twice the conventional
spin generator. The canonical coefficients are consequently `(n,1)`, with
`n` the actual phase-fibre parameter. Positive detail orientation and fixation
of the invariant upper sector determine this pair uniquely. The comparison
retains the lower-vacuum and opposite-orientation alternatives as well.
As in the lattice module, occupancy of the detail sector requires `n > 0`.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryJointChargeClassification

open HistoryJointChargeLattice

def PrimitiveWeights (w : Sector → ℤ) : Prop :=
  ∀ d : ℤ, (∀ p, d ∣ w p) → IsUnit d

def realWeight (n : ℕ) (α β : ℝ) (p : Sector) : ℝ :=
  α * (rightWeight p.2 : ℝ) + β * (relativeWeight n p.1 : ℝ)

def IntegralRealization (n : ℕ) (α β : ℝ) (w : Sector → ℤ) : Prop :=
  ∀ p, (w p : ℝ) = realWeight n α β p

theorem primitivePair_iff_gcd_eq_one (r b : ℤ) :
    HistoryRelativeCharge.PrimitivePair r b ↔ Int.gcd r b = 1 := by
  constructor
  · intro h
    have hu := h (Int.gcd r b) (Int.gcd_dvd_left r b) (Int.gcd_dvd_right r b)
    simpa using Int.isUnit_iff_natAbs_eq.mp hu
  · intro h d hdr hdb
    apply isUnit_iff_dvd_one.mpr
    have hd := Int.dvd_coe_gcd hdr hdb
    simpa [h] using hd

theorem primitive_iff_gcd_eq_one (n : ℕ) (r b : ℤ) :
    Primitive n r b ↔ Int.gcd r b = 1 :=
  (primitive_iff n r b).trans (primitivePair_iff_gcd_eq_one r b)

theorem integral_parameters {n : ℕ} {α β : ℝ} {w : Sector → ℤ}
    (hw : IntegralRealization n α β w) :
    ∃ r b : ℤ, α = (r : ℝ) ∧ β = (b : ℝ) := by
  have hl := hw (true, .inl 0)
  have hu := hw (true, .inr 0)
  simp [realWeight, rightWeight, relativeWeight] at hl hu
  refine ⟨w (true, .inr 0) - w (true, .inl 0), w (true, .inl 0), ?_, hl.symm⟩
  push_cast
  linarith

theorem integralRealization_eq {n : ℕ} {r b : ℤ} {w : Sector → ℤ}
    (hw : IntegralRealization n (r : ℝ) (b : ℝ) w) : w = weight n r b := by
  funext p
  apply Int.cast_injective (α := ℝ)
  have h := hw p
  dsimp [realWeight, weight] at h ⊢
  push_cast
  exact h

theorem primitive_of_unit (n : ℕ) (r : ℤ) {b : ℤ} (hb : IsUnit b) :
    Primitive n r b := by
  intro d hd
  exact isUnit_of_dvd_unit (by simpa using hd (true, .inl 0)) hb

@[simp] theorem invariant_lower (n : ℕ) (r b : ℤ) :
    weight n r b (false, .inr 1) = -r - n * b := by
  simp [weight, rightWeight, relativeWeight]
  ring

theorem fixed_lower_primitive_iff (n : ℕ) (r b : ℤ)
    (hv : weight n r b (false, .inr 1) = 0) : Primitive n r b ↔ IsUnit b := by
  have hr : r = -(n : ℤ) * b := by rw [invariant_lower] at hv; linarith
  constructor
  · intro hp
    apply (primitive_iff n r b).mp hp b
    · exact ⟨-(n : ℤ), by rw [hr]; ring⟩
    · exact dvd_rfl
  · exact primitive_of_unit n r

theorem primitive_vacuum_classification (n : ℕ) (r b : ℤ) :
    Primitive n r b ∧
        (weight n r b (false, .inr 0) = 0 ∨
          weight n r b (false, .inr 1) = 0) ↔
      (b = 1 ∨ b = -1) ∧ (r = n * b ∨ r = -(n : ℤ) * b) := by
  constructor
  · rintro ⟨hp, hv | hv⟩
    · refine ⟨Int.isUnit_iff.mp ((fixed_upper_primitive_iff n r b hv).mp hp),
        Or.inl ?_⟩
      rw [invariant_upper] at hv
      linarith
    · refine ⟨Int.isUnit_iff.mp ((fixed_lower_primitive_iff n r b hv).mp hp),
        Or.inr ?_⟩
      rw [invariant_lower] at hv
      linarith
  · rintro ⟨hb, hr | hr⟩
    · refine ⟨primitive_of_unit n r (Int.isUnit_iff.mpr hb), Or.inl ?_⟩
      rw [invariant_upper, hr]
      ring
    · refine ⟨primitive_of_unit n r (Int.isUnit_iff.mpr hb), Or.inr ?_⟩
      rw [invariant_lower, hr]
      ring

theorem oriented_real_vacuum_unique {n : ℕ} {α β : ℝ} {w : Sector → ℤ}
    (hw : IntegralRealization n α β w) (hp : PrimitiveWeights w)
    (hv : realWeight n α β (false, .inr 0) = 0) (hβ : 0 < β) :
    α = n ∧ β = 1 ∧ w = generatedWeight n := by
  obtain ⟨r, b, hα, hb⟩ := integral_parameters hw
  have hw' : IntegralRealization n (r : ℝ) (b : ℝ) w := by
    simpa only [hα, hb] using hw
  have he := integralRealization_eq hw'
  have hp' : Primitive n r b := by simpa only [Primitive, PrimitiveWeights, he] using hp
  have hv' : weight n r b (false, .inr 0) = 0 := by
    have h := hw (false, .inr 0)
    rw [hv, he] at h
    exact_mod_cast h
  have hb' : 0 < b := by exact_mod_cast (show 0 < (b : ℝ) by rwa [hb] at hβ)
  obtain ⟨hr, hb1⟩ := oriented_unique n hp' hv' hb'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hr, Int.cast_natCast] using hα
  · simpa only [hb1, Int.cast_one] using hb
  · simpa only [hr, hb1, generatedWeight] using he

structure Conclusions : Prop where
  primitive_lattice : ∀ n r b, Primitive n r b ↔ Int.gcd r b = 1
  integral_coefficients : ∀ n α β w, IntegralRealization n α β w →
    ∃ r b : ℤ, α = (r : ℝ) ∧ β = (b : ℝ)
  canonical_realization : ∀ n α β w, IntegralRealization n α β w →
    PrimitiveWeights w → realWeight n α β (false, .inr 0) = 0 →
    0 < β → α = n ∧ β = 1 ∧ w = generatedWeight n

theorem generated : Conclusions :=
  ⟨primitive_iff_gcd_eq_one, fun _ _ _ _ => integral_parameters,
    fun _ _ _ _ => oriented_real_vacuum_unique⟩

end GeneratedFoundations.Arithmetic.HistoryJointChargeClassification
