module

public import GeneratedFoundations.Spectral.CircleSobolev

/-!
# The periodic second derivative and its Neumann restriction

The circle operator is defined on arbitrary periodic Sobolev representatives.
Uniqueness of weak derivatives makes the operator independent of its chosen
representative. Reflection then identifies its even part with the interval
Neumann operator, both in domain and in graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

theorem circleLift_ae_iff {f g : ℝ → ℂ} :
    circleLift L f =ᵐ[reflectionCircleMeasure L] circleLift L g ↔
      f =ᵐ[intervalMeasure (-L) L] g := by
  constructor
  · intro h
    have hv : circleLift L f =ᵐ[volume] circleLift L g :=
      (Measure.ae_ennreal_smul_measure_iff (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0)).mp h
    have hp : periodicLift L f =ᵐ[intervalMeasure (-L) L] periodicLift L g :=
      (circle_quotient_measurePreserving L).quasiMeasurePreserving.ae hv
    exact (periodicLift_coe_ae L f).symm.trans (hp.trans (periodicLift_coe_ae L g))
  · intro h
    have hi : f =ᵐ[volume.restrict (Ioc (-L) (-L + 2 * L))] g := by
      simpa only [show -L + 2 * L = L by ring, restrict_Ioc_eq_restrict_Icc,
        intervalMeasure] using h
    have hp := (measurePreserving_subtype_coe measurableSet_Ioc).comp
      (AddCircle.measurePreserving_equivIoc (2 * L) (a := -L))
    have he := hp.quasiMeasurePreserving.ae hi
    exact Measure.ae_smul_measure he (2 : ℝ≥0∞)⁻¹

def circleLiftL2 {f : ℝ → ℂ} (hf : MemLp f 2 (intervalMeasure (-L) L)) :
    ReflectionCircleL2 L :=
  ((circleLift_memLp L hf).smul_measure (c := (2 : ℝ≥0∞)⁻¹)
    (by norm_num)).toLp (circleLift L f)

theorem circleLiftL2_coe {f : ℝ → ℂ} (hf : MemLp f 2 (intervalMeasure (-L) L)) :
    circleLiftL2 L hf =ᵐ[reflectionCircleMeasure L] circleLift L f :=
  MemLp.coeFn_toLp _

theorem circleLiftL2_eq_iff {f g : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure (-L) L))
    (hg : MemLp g 2 (intervalMeasure (-L) L)) :
    circleLiftL2 L hf = circleLiftL2 L hg ↔ f =ᵐ[intervalMeasure (-L) L] g := by
  constructor
  · intro heq
    apply (circleLift_ae_iff L).mp
    have hval : circleLiftL2 L hf =ᵐ[reflectionCircleMeasure L] circleLiftL2 L hg :=
      Filter.Eventually.of_forall (fun z => congrArg (fun u : ReflectionCircleL2 L => u z) heq)
    exact (circleLiftL2_coe L hf).symm.trans (hval.trans (circleLiftL2_coe L hg))
  · intro heq
    apply Lp.ext
    exact (circleLiftL2_coe L hf).trans
      (((circleLift_ae_iff L).mpr heq).trans (circleLiftL2_coe L hg).symm)

namespace PeriodicIntervalH2

def constant (c : ℂ) : PeriodicIntervalH2 L where
  toComplexH2Representative := ComplexH2Representative.constant (-L) L c
  value_match := rfl
  first_match := rfl

def add (f g : PeriodicIntervalH2 L) : PeriodicIntervalH2 L where
  toComplexH2Representative := f.toComplexH2Representative.add g.toComplexH2Representative
  value_match := by
    change f.value (-L) + g.value (-L) = f.value L + g.value L
    rw [f.value_match, g.value_match]
  first_match := by
    change f.first (-L) + g.first (-L) = f.first L + g.first L
    rw [f.first_match, g.first_match]

def smul (c : ℂ) (f : PeriodicIntervalH2 L) : PeriodicIntervalH2 L where
  toComplexH2Representative := f.toComplexH2Representative.smul c
  value_match := by
    change c * f.value (-L) = c * f.value L
    rw [f.value_match]
  first_match := by
    change c * f.first (-L) = c * f.first L
    rw [f.first_match]

def secondCircleL2 (f : PeriodicIntervalH2 L) : ReflectionCircleL2 L :=
  circleLiftL2 L f.secondDerivative.derivative_memLp

theorem toCircleL2_eq_iff (f g : PeriodicIntervalH2 L) :
    f.toCircleL2 L = g.toCircleL2 L ↔
      f.toComplexH2Representative.toL2 = g.toComplexH2Representative.toL2 := by
  change circleLiftL2 L f.firstDerivative.value_memLp =
    circleLiftL2 L g.firstDerivative.value_memLp ↔ _
  rw [circleLiftL2_eq_iff, ComplexH2Representative.toL2_eq_iff]

theorem secondCircleL2_unique {f g : PeriodicIntervalH2 L}
    (h : f.toCircleL2 L = g.toCircleL2 L) : f.secondCircleL2 L = g.secondCircleL2 L := by
  apply (circleLiftL2_eq_iff L _ _).mpr
  have hsecond := ComplexH2Representative.secondL2_unique
    (by linarith [hL.out] : -L < L) ((toCircleL2_eq_iff L f g).mp h)
  exact (MemLp.toLp_eq_toLp_iff _ _).mp hsecond

@[simp] theorem toCircleL2_constant_zero : (constant L 0).toCircleL2 L = 0 := rfl

@[simp] theorem toCircleL2_add (f g : PeriodicIntervalH2 L) :
    (f.add L g).toCircleL2 L = f.toCircleL2 L + g.toCircleL2 L := rfl

@[simp] theorem toCircleL2_smul (c : ℂ) (f : PeriodicIntervalH2 L) :
    (f.smul L c).toCircleL2 L = c • f.toCircleL2 L := rfl

@[simp] theorem secondCircleL2_add (f g : PeriodicIntervalH2 L) :
    (f.add L g).secondCircleL2 L = f.secondCircleL2 L + g.secondCircleL2 L := rfl

@[simp] theorem secondCircleL2_smul (c : ℂ) (f : PeriodicIntervalH2 L) :
    (f.smul L c).secondCircleL2 L = c • f.secondCircleL2 L := rfl

end PeriodicIntervalH2

/-- The full periodic domain, without an evenness restriction. -/
def periodicCircleDomain : Submodule ℂ (ReflectionCircleL2 L) where
  carrier := periodicCircleH2Domain L
  zero_mem' := ⟨PeriodicIntervalH2.constant L 0, rfl⟩
  add_mem' := by
    rintro u v ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f.add L g, PeriodicIntervalH2.toCircleL2_add L f g⟩
  smul_mem' := by
    rintro c u ⟨f, rfl⟩
    exact ⟨f.smul L c, PeriodicIntervalH2.toCircleL2_smul L c f⟩

def periodicCircleRepresentative (u : periodicCircleDomain L) : PeriodicIntervalH2 L :=
  Classical.choose u.property

theorem periodicCircleRepresentative_spec (u : periodicCircleDomain L) :
    (periodicCircleRepresentative L u).toCircleL2 L = (u : ReflectionCircleL2 L) :=
  Classical.choose_spec u.property

/-- The actual negative second weak derivative on the full periodic domain. -/
def periodicCircleOperator : ReflectionCircleL2 L →ₗ.[ℂ] ReflectionCircleL2 L where
  domain := periodicCircleDomain L
  toFun :=
    { toFun := fun u => -(periodicCircleRepresentative L u).secondCircleL2 L
      map_add' := by
        intro u v
        have heq : (periodicCircleRepresentative L (u + v)).toCircleL2 L =
            ((periodicCircleRepresentative L u).add L
              (periodicCircleRepresentative L v)).toCircleL2 L := by
          rw [PeriodicIntervalH2.toCircleL2_add, periodicCircleRepresentative_spec,
            periodicCircleRepresentative_spec, periodicCircleRepresentative_spec]
          rfl
        rw [PeriodicIntervalH2.secondCircleL2_unique L heq,
          PeriodicIntervalH2.secondCircleL2_add, neg_add]
      map_smul' := by
        intro c u
        have heq : (periodicCircleRepresentative L (c • u)).toCircleL2 L =
            ((periodicCircleRepresentative L u).smul L c).toCircleL2 L := by
          rw [PeriodicIntervalH2.toCircleL2_smul, periodicCircleRepresentative_spec,
            periodicCircleRepresentative_spec]
          rfl
        rw [PeriodicIntervalH2.secondCircleL2_unique L heq,
          PeriodicIntervalH2.secondCircleL2_smul, smul_neg]
        rfl }

theorem periodicCircleOperator_on_representative (f : PeriodicIntervalH2 L) :
    (periodicCircleOperator L).toFun ⟨f.toCircleL2 L, f, rfl⟩ = -f.secondCircleL2 L := by
  change -(periodicCircleRepresentative L ⟨f.toCircleL2 L, f, rfl⟩).secondCircleL2 L = _
  congr 1
  exact PeriodicIntervalH2.secondCircleL2_unique L (periodicCircleRepresentative_spec L _)

theorem circleLift_evenReflection (f : ℝ → ℂ) (z : AddCircle (2 * L)) :
    circleLift L (evenReflection f) z = f ‖z‖ := by
  let r : ℝ := AddCircle.equivIoc (2 * L) (-L) z
  have hr : r ∈ Icc (-L) L := by
    have h := (AddCircle.equivIoc (2 * L) (-L) z).property
    exact ⟨h.1.le, by linarith [h.2]⟩
  have hc : (r : AddCircle (2 * L)) = z := AddCircle.coe_equivIoc
  change f |r| = f ‖z‖
  rw [← hc, circle_norm_coe L r hr]

theorem reflectNeumann_secondCircleL2 (f : ComplexH2Representative 0 L)
    (hf : IsComplexNeumann f) :
    (reflectNeumann hL.out f hf).secondCircleL2 L = reflectingIsometry L f.secondL2 := by
  apply Lp.ext
  have hs := (circle_fold_measurePreserving L).quasiMeasurePreserving.ae
    f.secondDerivative.derivative_memLp.coeFn_toLp
  filter_upwards [circleLiftL2_coe L (reflectNeumann hL.out f hf).secondDerivative.derivative_memLp,
    reflectingIsometry_coe L f.secondL2, hs] with z hz hr hs
  change f.secondL2 ‖z‖ = f.second ‖z‖ at hs
  rw [hr, hs]
  exact hz.trans (circleLift_evenReflection L f.second z)

def reflectingDomainMap (u : complexNeumannDomain 0 L) : periodicCircleDomain L :=
  ⟨reflectingIsometry L (u : ComplexIntervalL2 0 L),
    (reflectingIsometry_mem_periodicH2_iff L _).mpr u.property⟩

/-- The derivative action, not only its domain, is preserved by reflection. -/
theorem periodicCircleOperator_reflection (u : complexNeumannDomain 0 L) :
    periodicCircleOperator L (reflectingDomainMap L u) =
      reflectingIsometry L (complexNeumannOperator hL.out u) := by
  let f := complexNeumannRepresentative u
  have hf : IsComplexNeumann f := (complexNeumannRepresentative_spec u).1
  let F := reflectNeumann hL.out f hf
  have heq : F.toCircleL2 L = reflectingIsometry L (u : ComplexIntervalL2 0 L) := by
    rw [reflectNeumann_toCircleL2, (complexNeumannRepresentative_spec u).2]
  have hpoint : reflectingDomainMap L u =
      (⟨F.toCircleL2 L, F, rfl⟩ : periodicCircleDomain L) := Subtype.ext heq.symm
  calc
    _ = (periodicCircleOperator L).toFun ⟨F.toCircleL2 L, F, rfl⟩ :=
      congrArg (periodicCircleOperator L).toFun hpoint
    _ = -F.secondCircleL2 L := periodicCircleOperator_on_representative L F
    _ = _ := by
      change -(reflectNeumann hL.out f hf).secondCircleL2 L = reflectingIsometry L (-f.secondL2)
      rw [reflectNeumann_secondCircleL2, map_neg]

/-- Equality of the two operator graphs in the even circle sector. -/
theorem reflectingIsometry_mem_graph_iff (u v : ComplexIntervalL2 0 L) :
    (reflectingIsometry L u, reflectingIsometry L v) ∈ (periodicCircleOperator L).graph ↔
      (u, v) ∈ (complexNeumannOperator hL.out).graph := by
  constructor
  · intro h
    have hex : ∃ w : periodicCircleDomain L,
        (w : ReflectionCircleL2 L) = reflectingIsometry L u ∧
          (periodicCircleOperator L).toFun w = reflectingIsometry L v :=
      (LinearPMap.mem_graph_iff _).mp h
    obtain ⟨w, hw, ha⟩ := hex
    have hwDomain : (w : ReflectionCircleL2 L) ∈ periodicCircleH2Domain L := w.property
    rw [hw] at hwDomain
    have hu : u ∈ complexNeumannDomain 0 L :=
      (reflectingIsometry_mem_periodicH2_iff L u).mp hwDomain
    let z : complexNeumannDomain 0 L := ⟨u, hu⟩
    have hwz : w = reflectingDomainMap L z := Subtype.ext hw
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨z, rfl, ?_⟩
    apply (reflectingIsometry L).injective
    exact (periodicCircleOperator_reflection L z).symm.trans
      ((congrArg (periodicCircleOperator L).toFun hwz).symm.trans ha)
  · intro h
    have hex : ∃ z : complexNeumannDomain 0 L,
        (z : ComplexIntervalL2 0 L) = u ∧ (complexNeumannOperator hL.out).toFun z = v :=
      (LinearPMap.mem_graph_iff _).mp h
    obtain ⟨z, hz, ha⟩ := hex
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨reflectingDomainMap L z, ?_, ?_⟩
    · change reflectingIsometry L (z : ComplexIntervalL2 0 L) = reflectingIsometry L u
      rw [hz]
    · exact (periodicCircleOperator_reflection L z).trans (congrArg (reflectingIsometry L) ha)

theorem periodicCircleOperator_reflection_mem_even (u : complexNeumannDomain 0 L) :
    periodicCircleOperator L (reflectingDomainMap L u) ∈ evenCircleL2 L := by
  rw [periodicCircleOperator_reflection]
  exact reflectingIsometry_mem_even L _

end GeneratedFoundations.Spectral
