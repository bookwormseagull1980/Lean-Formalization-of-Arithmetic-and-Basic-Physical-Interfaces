module

public import GeneratedFoundations.Spectral.ReflectionSobolev

/-!
# Periodic Sobolev representatives on the quotient circle

Matching traces give a periodic extension whose weak derivative is the
periodic extension of the interval derivative. The proof uses a primitive
with zero integral over one period, so it applies to absolutely continuous
representatives without imposing classical second differentiability.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

def circleLift (f : ℝ → ℂ) : AddCircle (2 * L) → ℂ :=
  AddCircle.liftIoc (2 * L) (-L) f

def periodicLift (f : ℝ → ℂ) (x : ℝ) : ℂ := circleLift L f x

theorem periodicLift_periodic (f : ℝ → ℂ) :
    Function.Periodic (periodicLift L f) (2 * L) := by
  intro x
  simp only [periodicLift, AddCircle.coe_add_period]

theorem periodicLift_coe_ae (f : ℝ → ℂ) :
    periodicLift L f =ᵐ[intervalMeasure (-L) L] f := by
  rw [intervalMeasure, ← restrict_Ioc_eq_restrict_Icc]
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro x hx
  exact AddCircle.liftIoc_coe_apply (by
    simpa only [show -L + 2 * L = L by ring] using hx)

theorem periodicLift_coe {f : ℝ → ℂ} (hf : f (-L) = f L)
    {x : ℝ} (hx : x ∈ Icc (-L) L) : periodicLift L f x = f x := by
  rcases hx.1.eq_or_lt with h | h
  · subst x
    have hc : ((L : ℝ) : AddCircle (2 * L)) = (-L : ℝ) := by
      convert! AddCircle.coe_add_period (2 * L) (-L) using 1
      congr 1
      ring
    change circleLift L f (-L : ℝ) = f (-L)
    rw [← hc]
    exact (AddCircle.liftIoc_coe_apply
      (show L ∈ Ioc (-L) (-L + 2 * L) from ⟨by linarith [hL.out], by linarith⟩)).trans hf.symm
  · exact AddCircle.liftIoc_coe_apply ⟨h, by linarith [hx.2]⟩

theorem circleLift_continuous {f : ℝ → ℂ} (hf : f (-L) = f L)
    (hc : ContinuousOn f (Icc (-L) L)) : Continuous (circleLift L f) := by
  apply AddCircle.liftIoc_continuous
  · simpa only [show -L + 2 * L = L by ring] using hf
  · simpa only [show -L + 2 * L = L by ring] using hc

theorem circleLift_memLp {f : ℝ → ℂ} (hf : MemLp f 2 (intervalMeasure (-L) L)) :
    MemLp (circleLift L f) 2 (volume : Measure (AddCircle (2 * L))) := by
  apply MemLp.memLp_liftIoc
  simpa only [show -L + 2 * L = L by ring, restrict_Ioc_eq_restrict_Icc,
    intervalMeasure] using hf

theorem periodicLift_memLp_base {f : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure (-L) L)) :
    MemLp (periodicLift L f) 2 (intervalMeasure (-L) L) := by
  exact (circleLift_memLp L hf).comp_measurePreserving (circle_quotient_measurePreserving L)

theorem periodicLift_intervalIntegrable {f : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure (-L) L)) (a b : ℝ) :
    IntervalIntegrable (periodicLift L f) volume a b := by
  apply (periodicLift_periodic L f).intervalIntegrable
    (ne_of_gt (Fact.out : 0 < 2 * L)) (t := -L) _ a b
  simpa only [show -L + 2 * L = L by ring] using
    complex_intervalIntegrable_of_memLp (by linarith [hL.out])
      (periodicLift_memLp_base L hf)

theorem periodicLift_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure (-L) L)) {a b : ℝ} (hab : a ≤ b) :
    MemLp (periodicLift L f) 2 (intervalMeasure a b) := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    (periodicLift_intervalIntegrable L hf a b)
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  have hbase := periodicLift_memLp_base L hf
  have hsquare := (memLp_two_iff_integrable_sq_norm hbase.aestronglyMeasurable).mp hbase
  have hp : Function.Periodic (fun x => ‖periodicLift L f x‖ ^ 2) (2 * L) := by
    intro x
    dsimp only
    rw [periodicLift_periodic L f x]
  have hiBase : IntervalIntegrable (fun x => ‖periodicLift L f x‖ ^ 2)
      volume (-L) (-L + 2 * L) := by
    rw [show -L + 2 * L = L by ring]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by linarith [hL.out] : -L ≤ L)).mpr hsquare
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    (hp.intervalIntegrable (ne_of_gt (Fact.out : 0 < 2 * L)) hiBase a b)

theorem periodicLift_integral {f : ℝ → ℂ} {x y : ℝ}
    (hx : x ∈ Icc (-L) L) (hy : y ∈ Icc (-L) L) :
    (∫ z in x..y, periodicLift L f z) = ∫ z in x..y, f z := by
  apply intervalIntegral.integral_congr_ae_restrict
  apply (periodicLift_coe_ae L f).filter_mono
  apply ae_mono
  apply Measure.restrict_mono _ le_rfl
  exact uIoc_subset_uIcc.trans (uIcc_subset_Icc hx hy)

theorem periodicLift_primitive {f g : ℝ → ℂ}
    (h : HasComplexH1Derivative (-L) L f g) (hf : f (-L) = f L) (x : ℝ) :
    periodicLift L f x = f (-L) + ∫ z in -L..x, periodicLift L g z := by
  let Q : ℝ → ℂ := fun y => f (-L) + ∫ z in -L..y, periodicLift L g z
  have hint := periodicLift_intervalIntegrable L h.derivative_memLp
  have hzero : (∫ z in -L..(-L + 2 * L), periodicLift L g z) = 0 := by
    rw [show -L + 2 * L = L by ring, periodicLift_integral L
      ⟨le_rfl, by linarith [hL.out]⟩ ⟨by linarith [hL.out], le_rfl⟩,
      h.integral_eq_sub ⟨le_rfl, by linarith [hL.out]⟩
        ⟨by linarith [hL.out], le_rfl⟩, ← hf, sub_self]
  have hQ : Function.Periodic Q (2 * L) := by
    intro y
    dsimp only [Q]
    rw [(periodicLift_periodic L g).intervalIntegral_add_eq_add (-L) y hint,
      hzero, add_zero]
  have hQbase : ∀ y ∈ Icc (-L) L, Q y = f y := by
    intro y hy
    dsimp only [Q]
    rw [periodicLift_integral L ⟨le_rfl, by linarith [hL.out]⟩ hy,
      h.integral_eq_sub ⟨le_rfl, by linarith [hL.out]⟩ hy]
    ring
  let r : ℝ := AddCircle.equivIoc (2 * L) (-L) (x : AddCircle (2 * L))
  have hr : r ∈ Icc (-L) L := by
    have h := (AddCircle.equivIoc (2 * L) (-L) (x : AddCircle (2 * L))).property
    exact ⟨h.1.le, by linarith [h.2]⟩
  have hcoe : (r : AddCircle (2 * L)) = (x : AddCircle (2 * L)) :=
    AddCircle.coe_equivIoc
  have hQr : Q r = Q x := congrArg hQ.lift hcoe
  change circleLift L f (x : AddCircle (2 * L)) = Q x
  rw [← hcoe]
  exact (periodicLift_coe L hf hr).trans ((hQbase r hr).symm.trans hQr)

theorem HasComplexH1Derivative.periodicLift {f g : ℝ → ℂ}
    (h : HasComplexH1Derivative (-L) L f g) (hf : f (-L) = f L)
    {a b : ℝ} (hab : a < b) :
    HasComplexH1Derivative a b
      (GeneratedFoundations.Spectral.periodicLift L f)
      (GeneratedFoundations.Spectral.periodicLift L g) := by
  apply hasComplexH1Derivative_of_primitive hab
    (periodicLift_memLp L h.derivative_memLp hab.le)
  intro x _
  rw [periodicLift_primitive L h hf x, periodicLift_primitive L h hf a,
    add_assoc, intervalIntegral.integral_add_adjacent_intervals
      (periodicLift_intervalIntegrable L h.derivative_memLp (-L) a)
      (periodicLift_intervalIntegrable L h.derivative_memLp a x)]

/-- The periodic extension has genuine `H²` data on every bounded real interval. -/
def PeriodicIntervalH2.globalRepresentative (f : PeriodicIntervalH2 L)
    {a b : ℝ} (hab : a < b) : ComplexH2Representative a b where
  value := periodicLift L f.value
  first := periodicLift L f.first
  second := periodicLift L f.second
  firstDerivative := f.firstDerivative.periodicLift L f.value_match hab
  secondDerivative := f.secondDerivative.periodicLift L f.first_match hab

def PeriodicIntervalH2.toCircleL2 (f : PeriodicIntervalH2 L) : ReflectionCircleL2 L :=
  ((circleLift_memLp L f.firstDerivative.value_memLp).smul_measure
    (c := (2 : ℝ≥0∞)⁻¹) (by norm_num)).toLp (circleLift L f.value)

theorem PeriodicIntervalH2.toCircleL2_coe (f : PeriodicIntervalH2 L) :
    f.toCircleL2 L =ᵐ[reflectionCircleMeasure L] circleLift L f.value :=
  MemLp.coeFn_toLp _

/-- The circle domain is defined by arbitrary periodic Sobolev representatives. -/
def periodicCircleH2Domain : Set (ReflectionCircleL2 L) :=
  {u | ∃ f : PeriodicIntervalH2 L, f.toCircleL2 L = u}

theorem PeriodicIntervalH2.isEven_of_toCircleL2_mem_even
    (f : PeriodicIntervalH2 L) (hf : f.toCircleL2 L ∈ evenCircleL2 L) : f.IsEven := by
  have hc := circleLift_continuous L f.value_match f.firstDerivative.continuousOn
  have hcoe := f.toCircleL2_coe L
  have hneg := (Measure.measurePreserving_neg (reflectionCircleMeasure L)).quasiMeasurePreserving.ae
    hcoe
  have he := (mem_evenCircleL2 L (f.toCircleL2 L)).mp hf
  have heAE : (fun z => circleLift L f.value (-z)) =ᵐ[reflectionCircleMeasure L]
      circleLift L f.value := by
    filter_upwards [hcoe, hneg, he] with z hz hn he
    exact hn.symm.trans (he.trans hz)
  have heVol : (fun z => circleLift L f.value (-z)) =ᵐ[volume] circleLift L f.value :=
    (Measure.ae_ennreal_smul_measure_iff (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0)).mp heAE
  have hePoint := Measure.eq_of_ae_eq heVol (hc.comp continuous_neg) hc
  intro x hx
  have hnx : -x ∈ Icc (-L) L := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  calc
    f.value (-x) = periodicLift L f.value (-x) := (periodicLift_coe L f.value_match hnx).symm
    _ = periodicLift L f.value x := by
      simpa only [periodicLift, AddCircle.coe_neg] using congrFun hePoint (x : AddCircle (2 * L))
    _ = f.value x := periodicLift_coe L f.value_match hx

theorem PeriodicIntervalH2.circleLift_of_even (f : PeriodicIntervalH2 L) (hf : f.IsEven)
    (z : AddCircle (2 * L)) : circleLift L f.value z = f.value ‖z‖ := by
  let r : ℝ := AddCircle.equivIoc (2 * L) (-L) z
  have hr : r ∈ Icc (-L) L := by
    have h := (AddCircle.equivIoc (2 * L) (-L) z).property
    exact ⟨h.1.le, by linarith [h.2]⟩
  have hcoe : (r : AddCircle (2 * L)) = z := AddCircle.coe_equivIoc
  have hnorm : ‖z‖ = |r| := by
    rw [← hcoe]
    exact circle_norm_coe L r hr
  change f.value r = f.value ‖z‖
  rw [hnorm]
  by_cases h : 0 ≤ r
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    exact (hf r hr).symm

theorem PeriodicIntervalH2.toCircleL2_eq_reflection_restrict
    (f : PeriodicIntervalH2 L) (hf : f.IsEven) :
    f.toCircleL2 L = reflectingIsometry L (f.restrict hL.out).toL2 := by
  apply Lp.ext
  have hrestrict := (circle_fold_measurePreserving L).quasiMeasurePreserving.ae
    (f.restrict hL.out).firstDerivative.value_memLp.coeFn_toLp
  filter_upwards [f.toCircleL2_coe L, reflectingIsometry_coe L (f.restrict hL.out).toL2,
    hrestrict] with z hz hr hs
  change (f.restrict hL.out).toL2 ‖z‖ = f.value ‖z‖ at hs
  rw [hz, hr, hs]
  exact f.circleLift_of_even L hf z

theorem reflectNeumann_toCircleL2 (f : ComplexH2Representative 0 L) (hf : IsComplexNeumann f) :
    (reflectNeumann hL.out f hf).toCircleL2 L = reflectingIsometry L f.toL2 := by
  rw [(reflectNeumann hL.out f hf).toCircleL2_eq_reflection_restrict L
    (reflectNeumann_isEven hL.out f hf)]
  congr 1
  apply (ComplexH2Representative.toL2_eq_iff _ _).mpr
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro x hx
  exact evenReflection_nonnegative f.value hx.1

/-- Reflection has precisely the periodic `H²` domain on the even circle sector. -/
theorem reflectingIsometry_mem_periodicH2_iff (u : ComplexIntervalL2 0 L) :
    reflectingIsometry L u ∈ periodicCircleH2Domain L ↔ u ∈ complexNeumannDomain 0 L := by
  constructor
  · rintro ⟨f, hf⟩
    have he : f.toCircleL2 L ∈ evenCircleL2 L := by
      rw [hf]
      exact reflectingIsometry_mem_even L u
    have hfe := f.isEven_of_toCircleL2_mem_even L he
    refine ⟨f.restrict hL.out, f.restrict_neumann hL.out hfe, ?_⟩
    apply (reflectingIsometry L).injective
    exact (f.toCircleL2_eq_reflection_restrict L hfe).symm.trans hf
  · rintro ⟨f, hf, rfl⟩
    exact ⟨reflectNeumann hL.out f hf, reflectNeumann_toCircleL2 L f hf⟩

end GeneratedFoundations.Spectral
