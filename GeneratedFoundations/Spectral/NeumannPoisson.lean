module

public import GeneratedFoundations.Spectral.ComplexNeumannDomain
public import Mathlib.Tactic.FieldSimp

/-!
# The Neumann problem for arbitrary square-integrable sources

A source of zero integral has a second-order Sobolev solution obtained by
two indefinite integrals. Fixing the integral of the solution removes the
constant kernel. No eigenfunction expansion is used in this construction.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval ComplexConjugate

namespace GeneratedFoundations.Spectral

theorem hasComplexH1Derivative_of_primitive {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (hg : MemLp g 2 (intervalMeasure a b))
    (hrep : ∀ x ∈ Icc a b, f x = f a + ∫ z in a..x, g z) :
    HasComplexH1Derivative a b f g := by
  apply hasComplexH1Derivative_of_parts
  · apply hasH1Derivative_of_primitive hab hg.re
    intro x hx
    have hgi := (complex_intervalIntegrable_of_memLp hab.le hg).mono_set
      ((uIcc_subset_Icc ⟨le_rfl, hab.le⟩ hx).trans Icc_subset_uIcc)
    have h := congrArg Complex.re (hrep x hx)
    change (f x).re = (f a).re + Complex.reCLM (∫ z in a..x, g z) at h
    rw [← Complex.reCLM.intervalIntegral_comp_comm hgi] at h
    exact h
  · apply hasH1Derivative_of_primitive hab hg.im
    intro x hx
    have hgi := (complex_intervalIntegrable_of_memLp hab.le hg).mono_set
      ((uIcc_subset_Icc ⟨le_rfl, hab.le⟩ hx).trans Icc_subset_uIcc)
    have h := congrArg Complex.im (hrep x hx)
    change (f x).im = (f a).im + Complex.imCLM (∫ z in a..x, g z) at h
    rw [← Complex.imCLM.intervalIntegral_comp_comm hgi] at h
    exact h

noncomputable def intervalPrimitive (a : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ z in a..x, g z

theorem intervalPrimitive_hasH1 {a b : ℝ} (hab : a < b) {g : ℝ → ℂ}
    (hg : MemLp g 2 (intervalMeasure a b)) :
    HasComplexH1Derivative a b (intervalPrimitive a g) g := by
  apply hasComplexH1Derivative_of_primitive hab hg
  intro x _
  simp [intervalPrimitive]

/-- The solution with zero value and zero first derivative at the left endpoint. -/
noncomputable def poissonRepresentative {a b : ℝ} (hab : a < b) (g : ℝ → ℂ)
    (hg : MemLp g 2 (intervalMeasure a b)) : ComplexH2Representative a b where
  value := intervalPrimitive a (intervalPrimitive a (fun x => -g x))
  first := intervalPrimitive a (fun x => -g x)
  second := fun x => -g x
  firstDerivative := intervalPrimitive_hasH1 hab (intervalPrimitive_hasH1 hab hg.neg).value_memLp
  secondDerivative := intervalPrimitive_hasH1 hab hg.neg

theorem poissonRepresentative_neumann {a b : ℝ} (hab : a < b) (g : ℝ → ℂ)
    (hg : MemLp g 2 (intervalMeasure a b)) (hzero : (∫ x in a..b, g x) = 0) :
    IsComplexNeumann (poissonRepresentative hab g hg) := by
  simp [IsComplexNeumann, poissonRepresentative, intervalPrimitive, intervalIntegral.integral_neg,
    hzero]

@[simp] theorem poissonRepresentative_secondL2 {a b : ℝ} (hab : a < b) (g : ℝ → ℂ)
    (hg : MemLp g 2 (intervalMeasure a b)) :
    (poissonRepresentative hab g hg).secondL2 = -(hg.toLp g) := rfl

noncomputable def intervalIntegralL2 {a b : ℝ} (u : ComplexIntervalL2 a b) : ℂ :=
  ∫ x, u x ∂intervalMeasure a b

theorem intervalIntegralL2_toLp {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure a b)) :
    intervalIntegralL2 (hf.toLp f) = ∫ x in a..b, f x := by
  unfold intervalIntegralL2
  rw [integral_congr_ae hf.coeFn_toLp]
  change (∫ x in Icc a b, f x) = _
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

theorem intervalIntegralL2_eq {a b : ℝ} (hab : a ≤ b) (u : ComplexIntervalL2 a b) :
    intervalIntegralL2 u = ∫ x in a..b, u x := by
  simpa only [Lp.toLp_coeFn] using intervalIntegralL2_toLp hab (Lp.memLp u)

/-- Equal sources and equal integrals determine the same Neumann solution. -/
theorem complexNeumann_unique_of_integral {a b : ℝ} (hab : a < b)
    (f g : ComplexH2Representative a b) (hf : IsComplexNeumann f) (hg : IsComplexNeumann g)
    (hsecond : f.secondL2 = g.secondL2)
    (hmass : (∫ x in a..b, f.value x) = ∫ x in a..b, g.value x) : f.toL2 = g.toL2 := by
  let d := f.add (g.smul (-1))
  have hd : IsComplexNeumann d := by
    simp [d, IsComplexNeumann, ComplexH2Representative.add, ComplexH2Representative.smul,
      hf.1, hf.2, hg.1, hg.2]
  have hz : d.secondL2 = 0 := by
    simp [d, hsecond]
  obtain ⟨c, hc⟩ := (complexNeumann_kernel_constants hab d hd).mp hz
  have hfi := complex_intervalIntegrable_of_memLp hab.le f.firstDerivative.value_memLp
  have hgi := complex_intervalIntegrable_of_memLp hab.le g.firstDerivative.value_memLp
  have hdint : (∫ x in a..b, d.value x) = 0 := by
    change (∫ x in a..b, f.value x + (-1 : ℂ) * g.value x) = 0
    rw [intervalIntegral.integral_add hfi (hgi.const_mul _),
      intervalIntegral.integral_const_mul, hmass]
    ring
  have hconst : (∫ x in a..b, d.value x) = (b - a) • c := by
    calc
      _ = ∫ _x in a..b, c := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hc x (by simpa only [uIcc_of_le hab.le] using hx)
      _ = _ := intervalIntegral.integral_const c
  have hc0 : c = 0 := by
    have hcz : (b - a) • c = 0 := hconst.symm.trans hdint
    exact (smul_eq_zero.mp hcz).resolve_left (sub_ne_zero.mpr hab.ne')
  apply (f.toL2_eq_iff g).mpr
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro x hx
  have h := hc x hx
  change f.value x + (-1 : ℂ) * g.value x = c at h
  rw [hc0] at h
  apply sub_eq_zero.mp
  simpa only [neg_one_mul, sub_eq_add_neg] using h

theorem neumannPoisson_exists {a b : ℝ} (hab : a < b) (g : ComplexIntervalL2 a b)
    (hg : intervalIntegralL2 g = 0) :
    ∃ u : (complexNeumannOperator hab).domain,
      complexNeumannOperator hab u = g ∧ intervalIntegralL2 (u : ComplexIntervalL2 a b) = 0 := by
  let f := poissonRepresentative hab g (Lp.memLp g)
  have hf : IsComplexNeumann f :=
    poissonRepresentative_neumann hab g (Lp.memLp g) ((intervalIntegralL2_eq hab.le g).symm.trans hg)
  let c : ℂ := -(∫ x in a..b, f.value x) / (b - a : ℝ)
  let v := f.add (ComplexH2Representative.constant a b c)
  have hv : IsComplexNeumann v := by
    simp [v, IsComplexNeumann, ComplexH2Representative.add, ComplexH2Representative.constant,
      hf.1, hf.2]
  refine ⟨⟨v.toL2, v, hv, rfl⟩, ?_, ?_⟩
  · change (complexNeumannOperator hab).toFun ⟨v.toL2, v, hv, rfl⟩ = g
    rw [complexNeumannOperator_on_representative hab v hv]
    simp [v, f, Lp.toLp_coeFn]
  · change intervalIntegralL2 v.toL2 = 0
    change intervalIntegralL2 (v.firstDerivative.value_memLp.toLp v.value) = 0
    rw [intervalIntegralL2_toLp hab.le v.firstDerivative.value_memLp]
    change (∫ x in a..b, f.value x + c) = 0
    rw [intervalIntegral.integral_add
      (complex_intervalIntegrable_of_memLp hab.le f.firstDerivative.value_memLp)
      (intervalIntegrable_const), intervalIntegral.integral_const]
    have hL : (b - a : ℂ) ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hab.ne')
    simp only [c, Complex.real_smul, Complex.ofReal_sub]
    field_simp [hL]
    ring

theorem neumannPoisson_unique_of_mean {a b : ℝ} (hab : a < b)
    {u v : (complexNeumannOperator hab).domain}
    (hsource : complexNeumannOperator hab u = complexNeumannOperator hab v)
    (hmean : intervalIntegralL2 (u : ComplexIntervalL2 a b) =
      intervalIntegralL2 (v : ComplexIntervalL2 a b)) : u = v := by
  apply Subtype.ext
  let f := complexNeumannRepresentative u
  let g := complexNeumannRepresentative v
  have hsecond : f.secondL2 = g.secondL2 := by
    apply neg_injective
    exact hsource
  have hmass : (∫ x in a..b, f.value x) = ∫ x in a..b, g.value x := by
    rw [← intervalIntegralL2_toLp hab.le f.firstDerivative.value_memLp,
      ← intervalIntegralL2_toLp hab.le g.firstDerivative.value_memLp]
    change intervalIntegralL2 f.toL2 = intervalIntegralL2 g.toL2
    rw [(complexNeumannRepresentative_spec u).2, (complexNeumannRepresentative_spec v).2]
    exact hmean
  have heq := complexNeumann_unique_of_integral hab f g
    (complexNeumannRepresentative_spec u).1 (complexNeumannRepresentative_spec v).1 hsecond hmass
  exact (complexNeumannRepresentative_spec u).2.symm.trans
    (heq.trans (complexNeumannRepresentative_spec v).2)

theorem neumannPoisson_existsUnique {a b : ℝ} (hab : a < b) (g : ComplexIntervalL2 a b)
    (hg : intervalIntegralL2 g = 0) :
    ∃! u : (complexNeumannOperator hab).domain,
      complexNeumannOperator hab u = g ∧ intervalIntegralL2 (u : ComplexIntervalL2 a b) = 0 := by
  obtain ⟨u, hu, hzero⟩ := neumannPoisson_exists hab g hg
  refine ⟨u, ⟨hu, hzero⟩, fun v hv => ?_⟩
  exact neumannPoisson_unique_of_mean hab (hv.1.trans hu.symm) (hv.2.trans hzero.symm)

theorem complexNeumannOperator_integral_eq_zero {a b : ℝ} (hab : a < b)
    (u : (complexNeumannOperator hab).domain) :
    intervalIntegralL2 (complexNeumannOperator hab u) = 0 := by
  let f := complexNeumannRepresentative u
  change intervalIntegralL2 (-f.secondL2) = 0
  change intervalIntegralL2
    (f.secondDerivative.derivative_memLp.neg.toLp (fun x => -f.second x)) = 0
  rw [intervalIntegralL2_toLp hab.le, intervalIntegral.integral_neg,
    f.secondDerivative.integral_eq_sub ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩,
    (complexNeumannRepresentative_spec u).1.1, (complexNeumannRepresentative_spec u).1.2]
  simp

theorem neumann_range_eq_meanZero {a b : ℝ} (hab : a < b) (g : ComplexIntervalL2 a b) :
    (∃ u : (complexNeumannOperator hab).domain, complexNeumannOperator hab u = g) ↔
      intervalIntegralL2 g = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact complexNeumannOperator_integral_eq_zero hab u
  · intro hg
    obtain ⟨u, hu, _⟩ := neumannPoisson_exists hab g hg
    exact ⟨u, hu⟩

end GeneratedFoundations.Spectral
