module

public import GeneratedFoundations.Spectral.IntervalSobolev
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Complex Sobolev representatives on a bounded interval

Complex Sobolev data are defined directly by absolute continuity and a
square-integrable almost-everywhere derivative. The real-component description
is proved equivalent, so complexification does not restrict the domain.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

noncomputable abbrev ComplexIntervalL2 (a b : ℝ) := Lp ℂ 2 (intervalMeasure a b)

structure HasComplexH1Derivative (a b : ℝ) (f g : ℝ → ℂ) : Prop where
  absolutelyContinuous : AbsolutelyContinuousOnInterval f a b
  derivative_memLp : MemLp g 2 (intervalMeasure a b)
  hasDeriv_ae : ∀ᵐ x ∂intervalMeasure a b, HasDerivAt f (g x) x

namespace HasComplexH1Derivative

variable {a b : ℝ} {f g : ℝ → ℂ} (h : HasComplexH1Derivative a b f g)

include h

theorem re : HasH1Derivative a b (fun x => (f x).re) (fun x => (g x).re) := by
  refine ⟨Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval h.absolutelyContinuous,
    h.derivative_memLp.re, ?_⟩
  filter_upwards [h.hasDeriv_ae] with x hx
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hx

theorem im : HasH1Derivative a b (fun x => (f x).im) (fun x => (g x).im) := by
  refine ⟨Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval h.absolutelyContinuous,
    h.derivative_memLp.im, ?_⟩
  filter_upwards [h.hasDeriv_ae] with x hx
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx

theorem value_memLp : MemLp f 2 (intervalMeasure a b) :=
  memLp_re_im_iff.mp ⟨h.re.value_memLp, h.im.value_memLp⟩

theorem derivative_intervalIntegrable (hab : a ≤ b) : IntervalIntegrable g volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (h.derivative_memLp.integrable (by norm_num))

theorem continuousOn : ContinuousOn f (Icc a b) :=
  h.absolutelyContinuous.continuousOn.mono Icc_subset_uIcc

theorem integral_eq_sub {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (∫ z in x..y, g z) = f y - f x := by
  have hgi := (h.derivative_intervalIntegrable (hx.1.trans hx.2)).mono_set
    ((uIcc_subset_Icc hx hy).trans Icc_subset_uIcc)
  apply Complex.ext
  · change Complex.reCLM (∫ z in x..y, g z) = (f y).re - (f x).re
    rw [← Complex.reCLM.intervalIntegral_comp_comm hgi]
    exact h.re.integral_eq_sub hx hy
  · change Complex.imCLM (∫ z in x..y, g z) = (f y).im - (f x).im
    rw [← Complex.imCLM.intervalIntegral_comp_comm hgi]
    exact h.im.integral_eq_sub hx hy

end HasComplexH1Derivative

theorem hasComplexH1Derivative_of_parts {a b : ℝ} {f g : ℝ → ℂ}
    (hr : HasH1Derivative a b (fun x => (f x).re) (fun x => (g x).re))
    (hi : HasH1Derivative a b (fun x => (f x).im) (fun x => (g x).im)) :
    HasComplexH1Derivative a b f g := by
  have hreal : AbsolutelyContinuousOnInterval (fun x => ((f x).re : ℂ)) a b :=
    Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hr.absolutelyContinuous
  have himag : AbsolutelyContinuousOnInterval (fun x => ((f x).im : ℂ)) a b :=
    Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hi.absolutelyContinuous
  refine ⟨?_, memLp_re_im_iff.mp ⟨hr.derivative_memLp, hi.derivative_memLp⟩, ?_⟩
  · convert! hreal.fun_add (himag.const_smul Complex.I) using 1
    funext x
    simp only [smul_eq_mul, mul_comm Complex.I, Complex.re_add_im]
  · filter_upwards [hr.hasDeriv_ae, hi.hasDeriv_ae] with x hxr hxi
    convert! hxr.ofReal_comp.add (hxi.ofReal_comp.const_mul Complex.I) using 1
    · funext y
      simp only [Pi.add_apply, mul_comm Complex.I, Complex.re_add_im]
    · simp only [mul_comm Complex.I, Complex.re_add_im]

theorem hasComplexH1Derivative_iff_parts {a b : ℝ} {f g : ℝ → ℂ} :
    HasComplexH1Derivative a b f g ↔
      HasH1Derivative a b (fun x => (f x).re) (fun x => (g x).re) ∧
      HasH1Derivative a b (fun x => (f x).im) (fun x => (g x).im) :=
  ⟨fun h => ⟨h.re, h.im⟩, fun h => hasComplexH1Derivative_of_parts h.1 h.2⟩

theorem complexH1Derivative_unique {a b : ℝ} (hab : a < b)
    {f₁ f₂ g₁ g₂ : ℝ → ℂ} (h₁ : HasComplexH1Derivative a b f₁ g₁)
    (h₂ : HasComplexH1Derivative a b f₂ g₂)
    (heq : f₁ =ᵐ[intervalMeasure a b] f₂) : g₁ =ᵐ[intervalMeasure a b] g₂ := by
  have hre := h1Derivative_unique hab h₁.re h₂.re
    (heq.fun_comp Complex.re)
  have him := h1Derivative_unique hab h₁.im h₂.im
    (heq.fun_comp Complex.im)
  filter_upwards [hre, him] with x hxr hxi
  exact Complex.ext hxr hxi

structure ComplexH2Representative (a b : ℝ) where
  value : ℝ → ℂ
  first : ℝ → ℂ
  second : ℝ → ℂ
  firstDerivative : HasComplexH1Derivative a b value first
  secondDerivative : HasComplexH1Derivative a b first second

namespace ComplexH2Representative

variable {a b : ℝ}

def re (f : ComplexH2Representative a b) : H2Representative a b where
  value := fun x => (f.value x).re
  first := fun x => (f.first x).re
  second := fun x => (f.second x).re
  firstDerivative := f.firstDerivative.re
  secondDerivative := f.secondDerivative.re

def im (f : ComplexH2Representative a b) : H2Representative a b where
  value := fun x => (f.value x).im
  first := fun x => (f.first x).im
  second := fun x => (f.second x).im
  firstDerivative := f.firstDerivative.im
  secondDerivative := f.secondDerivative.im

noncomputable def toL2 (f : ComplexH2Representative a b) : ComplexIntervalL2 a b :=
  f.firstDerivative.value_memLp.toLp f.value

noncomputable def secondL2 (f : ComplexH2Representative a b) : ComplexIntervalL2 a b :=
  f.secondDerivative.derivative_memLp.toLp f.second

theorem toL2_eq_iff (f g : ComplexH2Representative a b) :
    f.toL2 = g.toL2 ↔ f.value =ᵐ[intervalMeasure a b] g.value :=
  MemLp.toLp_eq_toLp_iff _ _

theorem trace_unique (hab : a < b) {f g : ComplexH2Representative a b}
    (heq : f.toL2 = g.toL2) :
    EqOn f.value g.value (Icc a b) ∧ EqOn f.first g.first (Icc a b) := by
  have hv := (f.toL2_eq_iff g).mp heq
  exact ⟨Measure.eqOn_Icc_of_ae_eq volume hab.ne hv f.firstDerivative.continuousOn
    g.firstDerivative.continuousOn,
    Measure.eqOn_Icc_of_ae_eq volume hab.ne
      (complexH1Derivative_unique hab f.firstDerivative g.firstDerivative hv)
      f.secondDerivative.continuousOn g.secondDerivative.continuousOn⟩

theorem secondL2_unique (hab : a < b) {f g : ComplexH2Representative a b}
    (heq : f.toL2 = g.toL2) : f.secondL2 = g.secondL2 := by
  apply MemLp.toLp_congr
  exact complexH1Derivative_unique hab f.secondDerivative g.secondDerivative
    (complexH1Derivative_unique hab f.firstDerivative g.firstDerivative
      ((f.toL2_eq_iff g).mp heq))

end ComplexH2Representative

end GeneratedFoundations.Spectral
