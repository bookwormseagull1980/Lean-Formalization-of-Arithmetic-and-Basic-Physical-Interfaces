module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Sobolev representatives on a bounded interval

The first-order domain is expressed by absolutely continuous representatives
whose almost-everywhere derivative belongs to `L²`. Its integral representation
is proved from the fundamental theorem of calculus. Endpoint values are taken
only on continuous representatives, and equality in `L²` determines those
values uniquely on every nondegenerate interval.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

noncomputable def intervalMeasure (a b : ℝ) : Measure ℝ :=
  volume.restrict (Icc a b)

instance intervalMeasure_finite (a b : ℝ) : IsFiniteMeasure (intervalMeasure a b) := by
  constructor
  simp [intervalMeasure]

noncomputable abbrev IntervalL2 (a b : ℝ) := Lp ℝ 2 (intervalMeasure a b)

lemma absolutelyContinuous_memLp {a b : ℝ} {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    MemLp f 2 (intervalMeasure a b) := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  apply MemLp.of_bound ((hf.continuousOn.mono Icc_subset_uIcc).aestronglyMeasurable
    measurableSet_Icc) C
  exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => hC x (Icc_subset_uIcc hx)

/-- An absolutely continuous representative with a square-integrable derivative. -/
structure HasH1Derivative (a b : ℝ) (f g : ℝ → ℝ) : Prop where
  absolutelyContinuous : AbsolutelyContinuousOnInterval f a b
  derivative_memLp : MemLp g 2 (intervalMeasure a b)
  hasDeriv_ae : ∀ᵐ x ∂intervalMeasure a b, HasDerivAt f (g x) x

namespace HasH1Derivative

variable {a b : ℝ} {f g : ℝ → ℝ} (h : HasH1Derivative a b f g)

include h

lemma continuousOn : ContinuousOn f (Icc a b) :=
  h.absolutelyContinuous.continuousOn.mono Icc_subset_uIcc

lemma value_memLp : MemLp f 2 (intervalMeasure a b) :=
  absolutelyContinuous_memLp h.absolutelyContinuous

lemma derivative_intervalIntegrable (hab : a ≤ b) : IntervalIntegrable g volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact h.derivative_memLp.integrable (by norm_num)

lemma deriv_eq_ae : deriv f =ᵐ[intervalMeasure a b] g :=
  h.hasDeriv_ae.mono fun _ hx => hx.deriv

/-- The derivative data recover differences of the continuous representative. -/
theorem integral_eq_sub {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (∫ z in x..y, g z) = f y - f x := by
  have hsub : uIcc x y ⊆ uIcc a b := (uIcc_subset_Icc hx hy).trans Icc_subset_uIcc
  have hd : ∀ᵐ z ∂volume, z ∈ Icc a b → deriv f z = g z :=
    (ae_restrict_iff' measurableSet_Icc).mp h.deriv_eq_ae
  calc
    (∫ z in x..y, g z) = ∫ z in x..y, deriv f z := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with z hz hzi
      exact (hz ((uIcc_subset_Icc hx hy) (uIoc_subset_uIcc hzi))).symm
    _ = f y - f x := (h.absolutelyContinuous.mono hsub).integral_deriv_eq_sub

theorem primitive_eq (hab : a ≤ b) {x : ℝ} (hx : x ∈ Icc a b) :
    f x = f a + ∫ z in a..x, g z := by
  rw [h.integral_eq_sub ⟨le_rfl, hab⟩ hx]
  ring

/-- A zero weak derivative forces the continuous representative to be constant. -/
theorem constant_of_derivative_eq_zero (hab : a ≤ b)
    (hg : g =ᵐ[intervalMeasure a b] 0) :
    ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rw [h.primitive_eq hab hx]
  have hz : (∫ z in a..x, g z) = 0 := by
    calc
      (∫ z in a..x, g z) = ∫ _z in a..x, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hg] with z hz hzi
        exact hz ((uIcc_subset_Icc ⟨le_rfl, hab⟩ hx) (uIoc_subset_uIcc hzi))
      _ = 0 := by simp
  rw [hz, add_zero]

end HasH1Derivative

theorem HasH1Derivative.const (a b c : ℝ) :
    HasH1Derivative a b (fun _ => c) (fun _ => 0) := by
  refine ⟨(contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval,
    MemLp.zero, ?_⟩
  exact ae_of_all _ fun x => hasDerivAt_const x c

theorem HasH1Derivative.add {a b : ℝ} {f₁ f₂ g₁ g₂ : ℝ → ℝ}
    (h₁ : HasH1Derivative a b f₁ g₁) (h₂ : HasH1Derivative a b f₂ g₂) :
    HasH1Derivative a b (fun x => f₁ x + f₂ x) (fun x => g₁ x + g₂ x) := by
  refine ⟨h₁.absolutelyContinuous.fun_add h₂.absolutelyContinuous,
    h₁.derivative_memLp.add h₂.derivative_memLp, ?_⟩
  filter_upwards [h₁.hasDeriv_ae, h₂.hasDeriv_ae] with x hx₁ hx₂
  exact hx₁.add hx₂

theorem HasH1Derivative.const_mul {a b : ℝ} {f g : ℝ → ℝ}
    (h : HasH1Derivative a b f g) (c : ℝ) :
    HasH1Derivative a b (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨h.absolutelyContinuous.const_mul c, h.derivative_memLp.const_mul c, ?_⟩
  filter_upwards [h.hasDeriv_ae] with x hx
  exact hx.const_mul c

/-- Continuous representatives equal almost everywhere have the same endpoint
values, including at the two measure-zero boundary points. -/
theorem continuous_representative_unique {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (heq : f =ᵐ[intervalMeasure a b] g) : EqOn f g (Icc a b) :=
  Measure.eqOn_Icc_of_ae_eq volume hab.ne heq hf hg

/-- The first derivative is determined almost everywhere by its `H¹` representative. -/
theorem h1Derivative_unique {a b : ℝ} (hab : a < b)
    {f₁ f₂ g₁ g₂ : ℝ → ℝ} (h₁ : HasH1Derivative a b f₁ g₁)
    (h₂ : HasH1Derivative a b f₂ g₂) (heq : f₁ =ᵐ[intervalMeasure a b] f₂) :
    g₁ =ᵐ[intervalMeasure a b] g₂ := by
  have hpoint := continuous_representative_unique hab h₁.continuousOn h₂.continuousOn heq
  filter_upwards [h₁.hasDeriv_ae, h₂.hasDeriv_ae, ae_restrict_mem measurableSet_Icc]
    with x hx₁ hx₂ hxi
  exact (uniqueDiffOn_Icc hab x hxi).eq_deriv (Icc a b)
    (hx₁.hasDerivWithinAt.congr_of_mem (fun y hy => (hpoint hy).symm) hxi)
    hx₂.hasDerivWithinAt

/-- The integral representation of a Sobolev function implies absolute
continuity and identifies its almost-everywhere derivative. -/
theorem hasH1Derivative_of_primitive {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hg : MemLp g 2 (intervalMeasure a b))
    (hrep : ∀ x ∈ Icc a b, f x = f a + ∫ z in a..x, g z) :
    HasH1Derivative a b f g := by
  have hgi : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr
      (hg.integrable (by norm_num))
  have hpac : AbsolutelyContinuousOnInterval (fun x => f a + ∫ z in a..x, g z) a b :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => f a)).contDiffOn.absolutelyContinuousOnInterval).fun_add
      (hgi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp))
  refine ⟨hpac.congr ?_, hg, ?_⟩
  · intro x hx
    exact (hrep x (by simpa [uIcc_of_le hab.le] using hx)).symm
  · have hder := hgi.ae_hasDerivAt_integral
    have ha : ∀ᵐ x ∂volume, x ≠ a := volume.ae_ne a
    have hb : ∀ᵐ x ∂volume, x ≠ b := volume.ae_ne b
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hder, ha, hb] with x hx hxa hxb hxi
    have hxo : x ∈ Ioo a b := ⟨lt_of_le_of_ne hxi.1 hxa.symm, lt_of_le_of_ne hxi.2 hxb⟩
    have hxder := (hx (by simpa [uIcc_of_le hab.le] using hxi) a (by simp)).const_add (f a)
    apply hxder.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hxo.1 hxo.2] with y hy
    exact hrep y (Ioo_subset_Icc_self hy)

theorem hasH1Derivative_iff_primitive {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hg : MemLp g 2 (intervalMeasure a b)) :
    HasH1Derivative a b f g ↔
      ∀ x ∈ Icc a b, f x = f a + ∫ z in a..x, g z :=
  ⟨fun h _ hx => h.primitive_eq hab.le hx, hasH1Derivative_of_primitive hab hg⟩

/-- Second-order Sobolev data: both the function and its first derivative have
absolutely continuous representatives, and the second derivative lies in `L²`. -/
structure H2Representative (a b : ℝ) where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ
  firstDerivative : HasH1Derivative a b value first
  secondDerivative : HasH1Derivative a b first second

namespace H2Representative

variable {a b : ℝ}

def constant (a b c : ℝ) : H2Representative a b where
  value := fun _ => c
  first := fun _ => 0
  second := fun _ => 0
  firstDerivative := HasH1Derivative.const a b c
  secondDerivative := HasH1Derivative.const a b 0

def add (f g : H2Representative a b) : H2Representative a b where
  value := fun x => f.value x + g.value x
  first := fun x => f.first x + g.first x
  second := fun x => f.second x + g.second x
  firstDerivative := f.firstDerivative.add g.firstDerivative
  secondDerivative := f.secondDerivative.add g.secondDerivative

def smul (c : ℝ) (f : H2Representative a b) : H2Representative a b where
  value := fun x => c * f.value x
  first := fun x => c * f.first x
  second := fun x => c * f.second x
  firstDerivative := f.firstDerivative.const_mul c
  secondDerivative := f.secondDerivative.const_mul c

noncomputable def toL2 (f : H2Representative a b) : IntervalL2 a b :=
  f.firstDerivative.value_memLp.toLp f.value

noncomputable def secondL2 (f : H2Representative a b) : IntervalL2 a b :=
  f.secondDerivative.derivative_memLp.toLp f.second

@[simp] theorem toL2_zero (a b : ℝ) : (constant a b 0).toL2 = 0 := rfl

@[simp] theorem toL2_add (f g : H2Representative a b) :
    (f.add g).toL2 = f.toL2 + g.toL2 := rfl

@[simp] theorem toL2_smul (c : ℝ) (f : H2Representative a b) :
    (f.smul c).toL2 = c • f.toL2 := rfl

@[simp] theorem secondL2_add (f g : H2Representative a b) :
    (f.add g).secondL2 = f.secondL2 + g.secondL2 := rfl

@[simp] theorem secondL2_smul (c : ℝ) (f : H2Representative a b) :
    (f.smul c).secondL2 = c • f.secondL2 := rfl

theorem toL2_eq_iff (f g : H2Representative a b) :
    f.toL2 = g.toL2 ↔ f.value =ᵐ[intervalMeasure a b] g.value :=
  MemLp.toLp_eq_toLp_iff _ _

theorem trace_unique (hab : a < b) {f g : H2Representative a b}
    (heq : f.toL2 = g.toL2) :
    EqOn f.value g.value (Icc a b) ∧ EqOn f.first g.first (Icc a b) := by
  have hv := (f.toL2_eq_iff g).mp heq
  exact ⟨continuous_representative_unique hab f.firstDerivative.continuousOn
    g.firstDerivative.continuousOn hv,
    continuous_representative_unique hab f.secondDerivative.continuousOn
      g.secondDerivative.continuousOn
      (h1Derivative_unique hab f.firstDerivative g.firstDerivative hv)⟩

theorem secondL2_unique (hab : a < b) {f g : H2Representative a b}
    (heq : f.toL2 = g.toL2) : f.secondL2 = g.secondL2 := by
  apply MemLp.toLp_congr
  exact h1Derivative_unique hab f.secondDerivative g.secondDerivative
    (h1Derivative_unique hab f.firstDerivative g.firstDerivative ((f.toL2_eq_iff g).mp heq))

end H2Representative

end GeneratedFoundations.Spectral
