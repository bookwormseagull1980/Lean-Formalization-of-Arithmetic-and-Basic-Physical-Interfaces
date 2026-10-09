module

public import GeneratedFoundations.Spectral.CircleOperator
public import GeneratedFoundations.Spectral.CircleNormalization

/-!
# The first weak derivative on the periodic Sobolev domain

The domain is specified by absolutely continuous representatives with an
`L²` weak derivative and matching endpoint values. Both the domain and its
derivative precede any Fourier description. Integration by parts gives the
skew identity. A zero-mean source has a periodic primitive, providing the
regularity recovery needed for the original angular operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval ComplexConjugate LinearPMap

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

def circleHaarLift {f : ℝ → ℂ} (hf : MemLp f 2 (intervalMeasure (-L) L)) :
    HaarCircleL2 L := ((circleLift_memLp L hf).haarAddCircle).toLp (circleLift L f)

theorem circleHaarLift_coe {f : ℝ → ℂ} (hf : MemLp f 2 (intervalMeasure (-L) L)) :
    circleHaarLift L hf =ᵐ[AddCircle.haarAddCircle] circleLift L f := MemLp.coeFn_toLp _

theorem circleHaarLift_eq_iff {f g : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure (-L) L))
    (hg : MemLp g 2 (intervalMeasure (-L) L)) :
    circleHaarLift L hf = circleHaarLift L hg ↔ f =ᵐ[intervalMeasure (-L) L] g := by
  unfold circleHaarLift
  rw [MemLp.toLp_eq_toLp_iff]
  exact (circle_ae_half_iff_haar L
    (p := fun z => circleLift L f z = circleLift L g z)).symm.trans
      (circleLift_ae_iff L (f := f) (g := g))

theorem circleHaarLift_inner {f g : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure (-L) L))
    (hg : MemLp g 2 (intervalMeasure (-L) L)) :
    inner ℂ (circleHaarLift L hf) (circleHaarLift L hg) =
      (2 * L)⁻¹ • ∫ x in -L..L, conj (f x) * g x := by
  rw [L2.inner_def]
  calc
    _ = ∫ z, circleLift L (fun x => conj (f x) * g x) z ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [circleHaarLift_coe L hf, circleHaarLift_coe L hg] with z hfz hgz
      rw [hfz, hgz, RCLike.inner_apply']
      rfl
    _ = _ := by
      rw [AddCircle.integral_haarAddCircle]
      change (2 * L)⁻¹ • (∫ z, AddCircle.liftIoc (2 * L) (-L)
        (fun x => conj (f x) * g x) z) = _
      rw [AddCircle.integral_liftIoc_eq_intervalIntegral,
        show -L + 2 * L = L by ring]

theorem circleHaarLift_integral {f : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure (-L) L)) :
    (∫ z, circleHaarLift L hf z ∂AddCircle.haarAddCircle) =
      (2 * L)⁻¹ • ∫ x in -L..L, f x := by
  rw [integral_congr_ae (circleHaarLift_coe L hf), AddCircle.integral_haarAddCircle]
  change (2 * L)⁻¹ • (∫ z, AddCircle.liftIoc (2 * L) (-L) f z) = _
  rw [AddCircle.integral_liftIoc_eq_intervalIntegral, show -L + 2 * L = L by ring]

theorem haarCircle_pullback_memLp (f : HaarCircleL2 L) :
    MemLp (fun x : ℝ => f (x : AddCircle (2 * L))) 2 (intervalMeasure (-L) L) :=
  (Lp.memLp f).of_haarAddCircle.comp_measurePreserving (circle_quotient_measurePreserving L)

theorem circleLift_pullback (f : AddCircle (2 * L) → ℂ) (z : AddCircle (2 * L)) :
    circleLift L (fun x : ℝ => f (x : AddCircle (2 * L))) z = f z := by
  change f ((AddCircle.equivIoc (2 * L) (-L) z : ℝ) : AddCircle (2 * L)) = f z
  rw [AddCircle.coe_equivIoc]

theorem circleHaarLift_pullback (f : HaarCircleL2 L) :
    circleHaarLift L (haarCircle_pullback_memLp L f) = f := by
  apply Lp.ext
  exact (circleHaarLift_coe L _).mono fun z hz => hz.trans (circleLift_pullback L f z)

theorem haarCircle_pullback_integral (f : HaarCircleL2 L) :
    (∫ x in -L..L, f (x : AddCircle (2 * L))) =
      (2 * L) • ∫ z, f z ∂AddCircle.haarAddCircle := by
  have h := AddCircle.intervalIntegral_preimage (2 * L) (-L) f
  rw [show -L + 2 * L = L by ring, AddCircle.volume_eq_smul_haarAddCircle,
    integral_smul_measure, ENNReal.toReal_ofReal (by linarith [hL.out])] at h
  exact h

/-- Periodic `H¹` data are not defined by Fourier coefficients. -/
structure PeriodicIntervalH1 where
  value : ℝ → ℂ
  first : ℝ → ℂ
  firstDerivative : HasComplexH1Derivative (-L) L value first
  value_match : value (-L) = value L

namespace PeriodicIntervalH1

def constant (c : ℂ) : PeriodicIntervalH1 L where
  value := fun _ => c
  first := fun _ => 0
  firstDerivative := HasComplexH1Derivative.const (-L) L c
  value_match := rfl

def add (f g : PeriodicIntervalH1 L) : PeriodicIntervalH1 L where
  value := fun x => f.value x + g.value x
  first := fun x => f.first x + g.first x
  firstDerivative := f.firstDerivative.add g.firstDerivative
  value_match := by rw [f.value_match, g.value_match]

def smul (c : ℂ) (f : PeriodicIntervalH1 L) : PeriodicIntervalH1 L where
  value := fun x => c * f.value x
  first := fun x => c * f.first x
  firstDerivative := f.firstDerivative.const_mul c
  value_match := by rw [f.value_match]

def toHaarL2 (f : PeriodicIntervalH1 L) : HaarCircleL2 L :=
  circleHaarLift L f.firstDerivative.value_memLp

def firstHaarL2 (f : PeriodicIntervalH1 L) : HaarCircleL2 L :=
  circleHaarLift L f.firstDerivative.derivative_memLp

theorem toHaarL2_eq_iff (f g : PeriodicIntervalH1 L) :
    f.toHaarL2 L = g.toHaarL2 L ↔ f.value =ᵐ[intervalMeasure (-L) L] g.value :=
  circleHaarLift_eq_iff L _ _

theorem firstHaarL2_unique {f g : PeriodicIntervalH1 L}
    (h : f.toHaarL2 L = g.toHaarL2 L) : f.firstHaarL2 L = g.firstHaarL2 L := by
  apply (circleHaarLift_eq_iff L _ _).mpr
  exact complexH1Derivative_unique (by linarith [hL.out]) f.firstDerivative g.firstDerivative
    ((toHaarL2_eq_iff L f g).mp h)

@[simp] theorem toHaarL2_constant_zero : (constant L 0).toHaarL2 L = 0 := rfl
@[simp] theorem firstHaarL2_constant (c : ℂ) : (constant L c).firstHaarL2 L = 0 := rfl

@[simp] theorem toHaarL2_add (f g : PeriodicIntervalH1 L) :
    (f.add L g).toHaarL2 L = f.toHaarL2 L + g.toHaarL2 L := rfl

@[simp] theorem toHaarL2_smul (c : ℂ) (f : PeriodicIntervalH1 L) :
    (f.smul L c).toHaarL2 L = c • f.toHaarL2 L := rfl

@[simp] theorem firstHaarL2_add (f g : PeriodicIntervalH1 L) :
    (f.add L g).firstHaarL2 L = f.firstHaarL2 L + g.firstHaarL2 L := rfl

@[simp] theorem firstHaarL2_smul (c : ℂ) (f : PeriodicIntervalH1 L) :
    (f.smul L c).firstHaarL2 L = c • f.firstHaarL2 L := rfl

theorem firstHaarL2_integral_zero (f : PeriodicIntervalH1 L) :
    (∫ z, f.firstHaarL2 L z ∂AddCircle.haarAddCircle) = 0 := by
  rw [firstHaarL2, circleHaarLift_integral,
    f.firstDerivative.integral_eq_sub
      ⟨le_rfl, by linarith [hL.out]⟩ ⟨by linarith [hL.out], le_rfl⟩,
    ← f.value_match, sub_self, smul_zero]

theorem derivative_skew_inner (f g : PeriodicIntervalH1 L) :
    inner ℂ (f.firstHaarL2 L) (g.toHaarL2 L) =
      -inner ℂ (f.toHaarL2 L) (g.firstHaarL2 L) := by
  change inner ℂ (circleHaarLift L f.firstDerivative.derivative_memLp)
      (circleHaarLift L g.firstDerivative.value_memLp) =
    -inner ℂ (circleHaarLift L f.firstDerivative.value_memLp)
      (circleHaarLift L g.firstDerivative.derivative_memLp)
  rw [circleHaarLift_inner, circleHaarLift_inner]
  have h := complexH1_integrationByParts (by linarith [hL.out] : -L ≤ L)
    f.firstDerivative.conjugate g.firstDerivative
  simp only [f.value_match, g.value_match, sub_self, zero_sub] at h
  rw [h, smul_neg, neg_neg]

/-- A periodic primitive is obtained from a source with zero Haar mean. -/
def primitive (g : HaarCircleL2 L)
    (hg : (∫ z, g z ∂AddCircle.haarAddCircle) = 0) : PeriodicIntervalH1 L where
  value := intervalPrimitive (-L) (fun x => g (x : AddCircle (2 * L)))
  first := fun x => g (x : AddCircle (2 * L))
  firstDerivative := intervalPrimitive_hasH1 (by linarith [hL.out])
    (haarCircle_pullback_memLp L g)
  value_match := by
    simp only [intervalPrimitive, intervalIntegral.integral_same,
      haarCircle_pullback_integral, hg, smul_zero]

theorem primitive_derivative (g : HaarCircleL2 L)
    (hg : (∫ z, g z ∂AddCircle.haarAddCircle) = 0) :
    (primitive L g hg).firstHaarL2 L = g := circleHaarLift_pullback L g

end PeriodicIntervalH1

def periodicH1Domain : Submodule ℂ (HaarCircleL2 L) where
  carrier := {u | ∃ f : PeriodicIntervalH1 L, f.toHaarL2 L = u}
  zero_mem' := ⟨PeriodicIntervalH1.constant L 0, rfl⟩
  add_mem' := by
    rintro u v ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.add L g, PeriodicIntervalH1.toHaarL2_add L f g⟩
  smul_mem' := by
    rintro c u ⟨f, rfl⟩
    exact ⟨f.smul L c, PeriodicIntervalH1.toHaarL2_smul L c f⟩

def periodicH1Representative (u : periodicH1Domain L) : PeriodicIntervalH1 L :=
  Classical.choose u.property

theorem periodicH1Representative_spec (u : periodicH1Domain L) :
    (periodicH1Representative L u).toHaarL2 L = (u : HaarCircleL2 L) :=
  Classical.choose_spec u.property

/-- The original periodic first weak derivative. -/
def periodicFirstDerivative : HaarCircleL2 L →ₗ.[ℂ] HaarCircleL2 L where
  domain := periodicH1Domain L
  toFun :=
    { toFun := fun u => (periodicH1Representative L u).firstHaarL2 L
      map_add' := by
        intro u v
        have heq : (periodicH1Representative L (u + v)).toHaarL2 L =
            ((periodicH1Representative L u).add L (periodicH1Representative L v)).toHaarL2 L := by
          rw [PeriodicIntervalH1.toHaarL2_add, periodicH1Representative_spec,
            periodicH1Representative_spec, periodicH1Representative_spec]
          rfl
        rw [PeriodicIntervalH1.firstHaarL2_unique L heq, PeriodicIntervalH1.firstHaarL2_add]
      map_smul' := by
        intro c u
        have heq : (periodicH1Representative L (c • u)).toHaarL2 L =
            ((periodicH1Representative L u).smul L c).toHaarL2 L := by
          rw [PeriodicIntervalH1.toHaarL2_smul, periodicH1Representative_spec,
            periodicH1Representative_spec]
          rfl
        rw [PeriodicIntervalH1.firstHaarL2_unique L heq, PeriodicIntervalH1.firstHaarL2_smul]
        rfl }

theorem periodicFirstDerivative_on_representative (f : PeriodicIntervalH1 L) :
    (periodicFirstDerivative L).toFun ⟨f.toHaarL2 L, f, rfl⟩ = f.firstHaarL2 L :=
  PeriodicIntervalH1.firstHaarL2_unique L (periodicH1Representative_spec L _)

theorem periodicFirstDerivative_skew (u v : (periodicFirstDerivative L).domain) :
    inner ℂ (periodicFirstDerivative L u) (v : HaarCircleL2 L) =
      -inner ℂ (u : HaarCircleL2 L) (periodicFirstDerivative L v) := by
  change inner ℂ ((periodicH1Representative L u).firstHaarL2 L) (v : HaarCircleL2 L) =
    -inner ℂ (u : HaarCircleL2 L) ((periodicH1Representative L v).firstHaarL2 L)
  rw [← periodicH1Representative_spec L u, ← periodicH1Representative_spec L v]
  exact PeriodicIntervalH1.derivative_skew_inner L _ _

theorem periodicFirstDerivative_range (g : HaarCircleL2 L) :
    (∃ u : (periodicFirstDerivative L).domain, periodicFirstDerivative L u = g) ↔
      (∫ z, g z ∂AddCircle.haarAddCircle) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (periodicH1Representative L u).firstHaarL2_integral_zero L
  · intro hg
    refine ⟨⟨(PeriodicIntervalH1.primitive L g hg).toHaarL2 L, _, rfl⟩, ?_⟩
    exact (periodicFirstDerivative_on_representative L _).trans
      (PeriodicIntervalH1.primitive_derivative L g hg)

end GeneratedFoundations.Spectral
