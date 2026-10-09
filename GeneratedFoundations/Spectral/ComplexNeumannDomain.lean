module

public import GeneratedFoundations.Spectral.ComplexIntervalSobolev
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The complex Neumann differential operator

The domain consists of complex second-order Sobolev representatives with
vanishing first-derivative traces. Green's identity is proved in the actual
interval `L²` inner product, before any spectral representation is introduced.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval ComplexConjugate

namespace GeneratedFoundations.Spectral

namespace HasComplexH1Derivative

variable {a b : ℝ} {f g : ℝ → ℂ}

theorem value_memLp_top (h : HasComplexH1Derivative a b f g) :
    MemLp f ∞ (intervalMeasure a b) := by
  obtain ⟨C, hC⟩ := h.absolutelyContinuous.exists_bound
  apply memLp_top_of_bound h.value_memLp.aestronglyMeasurable C
  exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => hC x (Icc_subset_uIcc hx)

theorem const (a b : ℝ) (c : ℂ) :
    HasComplexH1Derivative a b (fun _ => c) (fun _ => 0) := by
  refine ⟨(contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval,
    MemLp.zero, ?_⟩
  exact ae_of_all _ fun x => hasDerivAt_const x c

theorem add {f₁ f₂ g₁ g₂ : ℝ → ℂ}
    (h₁ : HasComplexH1Derivative a b f₁ g₁) (h₂ : HasComplexH1Derivative a b f₂ g₂) :
    HasComplexH1Derivative a b (fun x => f₁ x + f₂ x) (fun x => g₁ x + g₂ x) := by
  refine ⟨h₁.absolutelyContinuous.fun_add h₂.absolutelyContinuous,
    h₁.derivative_memLp.add h₂.derivative_memLp, ?_⟩
  filter_upwards [h₁.hasDeriv_ae, h₂.hasDeriv_ae] with x hx₁ hx₂
  exact hx₁.add hx₂

theorem const_mul (h : HasComplexH1Derivative a b f g) (c : ℂ) :
    HasComplexH1Derivative a b (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨?_, h.derivative_memLp.const_mul c, ?_⟩
  · simpa only [smul_eq_mul] using h.absolutelyContinuous.const_smul c
  · filter_upwards [h.hasDeriv_ae] with x hx
    exact hx.const_mul c

theorem conjugate (h : HasComplexH1Derivative a b f g) :
    HasComplexH1Derivative a b (fun x => conj (f x)) (fun x => conj (g x)) := by
  refine ⟨Complex.conjCLE.lipschitzWith.comp_absolutelyContinuousOnInterval h.absolutelyContinuous,
    ?_, ?_⟩
  · exact h.derivative_memLp.star
  · filter_upwards [h.hasDeriv_ae] with x hx
    exact Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hx

theorem mul {f₁ f₂ g₁ g₂ : ℝ → ℂ}
    (h₁ : HasComplexH1Derivative a b f₁ g₁) (h₂ : HasComplexH1Derivative a b f₂ g₂) :
    HasComplexH1Derivative a b (fun x => f₁ x * f₂ x)
      (fun x => g₁ x * f₂ x + f₁ x * g₂ x) := by
  refine ⟨?_, (h₁.derivative_memLp.fun_mul h₂.value_memLp_top).add
    (h₁.value_memLp_top.fun_mul h₂.derivative_memLp), ?_⟩
  · simpa only [smul_eq_mul] using h₁.absolutelyContinuous.fun_smul h₂.absolutelyContinuous
  · filter_upwards [h₁.hasDeriv_ae, h₂.hasDeriv_ae] with x hx₁ hx₂
    exact hx₁.mul hx₂

end HasComplexH1Derivative

lemma complex_intervalIntegrable_of_memLp {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure a b)) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hf.integrable (by norm_num))

theorem complexH1_integrationByParts {a b : ℝ} (hab : a ≤ b)
    {f g f' g' : ℝ → ℂ} (hf : HasComplexH1Derivative a b f f')
    (hg : HasComplexH1Derivative a b g g') :
    (∫ x in a..b, f x * g' x) =
      f b * g b - f a * g a - ∫ x in a..b, f' x * g x := by
  have h₁ := complex_intervalIntegrable_of_memLp hab
    (hf.derivative_memLp.fun_mul hg.value_memLp_top)
  have h₂ := complex_intervalIntegrable_of_memLp hab
    (hf.value_memLp_top.fun_mul hg.derivative_memLp)
  have h := (hf.mul hg).integral_eq_sub ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  rw [intervalIntegral.integral_add h₁ h₂] at h
  calc
    (∫ x in a..b, f x * g' x) =
        ((∫ x in a..b, f' x * g x) + ∫ x in a..b, f x * g' x) -
          ∫ x in a..b, f' x * g x := by ring
    _ = _ := by rw [h]

namespace ComplexH2Representative

variable {a b : ℝ}

def constant (a b : ℝ) (c : ℂ) : ComplexH2Representative a b where
  value := fun _ => c
  first := fun _ => 0
  second := fun _ => 0
  firstDerivative := HasComplexH1Derivative.const a b c
  secondDerivative := HasComplexH1Derivative.const a b 0

def add (f g : ComplexH2Representative a b) : ComplexH2Representative a b where
  value := fun x => f.value x + g.value x
  first := fun x => f.first x + g.first x
  second := fun x => f.second x + g.second x
  firstDerivative := f.firstDerivative.add g.firstDerivative
  secondDerivative := f.secondDerivative.add g.secondDerivative

def smul (c : ℂ) (f : ComplexH2Representative a b) : ComplexH2Representative a b where
  value := fun x => c * f.value x
  first := fun x => c * f.first x
  second := fun x => c * f.second x
  firstDerivative := f.firstDerivative.const_mul c
  secondDerivative := f.secondDerivative.const_mul c

noncomputable def firstL2 (f : ComplexH2Representative a b) : ComplexIntervalL2 a b :=
  f.firstDerivative.derivative_memLp.toLp f.first

@[simp] theorem toL2_constant_zero (a b : ℝ) : (constant a b 0).toL2 = 0 := rfl

@[simp] theorem secondL2_constant (a b : ℝ) (c : ℂ) : (constant a b c).secondL2 = 0 := rfl

@[simp] theorem toL2_add (f g : ComplexH2Representative a b) :
    (f.add g).toL2 = f.toL2 + g.toL2 := rfl

@[simp] theorem toL2_smul (c : ℂ) (f : ComplexH2Representative a b) :
    (f.smul c).toL2 = c • f.toL2 := rfl

@[simp] theorem secondL2_add (f g : ComplexH2Representative a b) :
    (f.add g).secondL2 = f.secondL2 + g.secondL2 := rfl

@[simp] theorem secondL2_smul (c : ℂ) (f : ComplexH2Representative a b) :
    (f.smul c).secondL2 = c • f.secondL2 := rfl

end ComplexH2Representative

def IsComplexNeumann {a b : ℝ} (f : ComplexH2Representative a b) : Prop :=
  f.first a = 0 ∧ f.first b = 0

theorem complexNeumann_greenIdentity {a b : ℝ} (hab : a ≤ b)
    (f g : ComplexH2Representative a b) (hf : IsComplexNeumann f) :
    (∫ x in a..b, conj (-f.second x) * g.value x) =
      ∫ x in a..b, conj (f.first x) * g.first x := by
  have h := complexH1_integrationByParts hab f.secondDerivative.conjugate g.firstDerivative
  simp only [hf.1, hf.2, map_zero, zero_mul, sub_zero, zero_sub] at h
  rw [h, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _
  simp

theorem complex_inner_toLp {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (intervalMeasure a b)) (hg : MemLp g 2 (intervalMeasure a b)) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ x in a..b, conj (f x) * g x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le hab]
  change (∫ x in Icc a b, inner ℂ ((hf.toLp f) x) ((hg.toLp g) x)) = _
  rw [← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hxf hxg
  rw [hxf, hxg, RCLike.inner_apply']

theorem complexNeumann_greenInner {a b : ℝ} (hab : a ≤ b)
    (f g : ComplexH2Representative a b) (hf : IsComplexNeumann f) :
    inner ℂ (-f.secondL2) g.toL2 = inner ℂ f.firstL2 g.firstL2 := by
  change inner ℂ (f.secondDerivative.derivative_memLp.neg.toLp (fun x => -f.second x))
    (g.firstDerivative.value_memLp.toLp g.value) =
    inner ℂ (f.firstDerivative.derivative_memLp.toLp f.first)
      (g.firstDerivative.derivative_memLp.toLp g.first)
  rw [complex_inner_toLp hab, complex_inner_toLp hab]
  exact complexNeumann_greenIdentity hab f g hf

theorem complexNeumann_nonnegative {a b : ℝ} (hab : a ≤ b)
    (f : ComplexH2Representative a b) (hf : IsComplexNeumann f) :
    0 ≤ (inner ℂ (-f.secondL2) f.toL2).re := by
  rw [complexNeumann_greenInner hab f f hf]
  exact inner_self_nonneg (𝕜 := ℂ) (x := f.firstL2)

theorem complexNeumann_symmetric {a b : ℝ} (hab : a ≤ b)
    (f g : ComplexH2Representative a b) (hf : IsComplexNeumann f) (hg : IsComplexNeumann g) :
    inner ℂ (-f.secondL2) g.toL2 = inner ℂ f.toL2 (-g.secondL2) := by
  rw [complexNeumann_greenInner hab f g hf, ← inner_conj_symm f.toL2 (-g.secondL2),
    complexNeumann_greenInner hab g f hg, inner_conj_symm]

theorem complexNeumann_kernel_constants {a b : ℝ} (hab : a < b)
    (f : ComplexH2Representative a b) (hf : IsComplexNeumann f) :
    f.secondL2 = 0 ↔ ∃ c : ℂ, ∀ x ∈ Icc a b, f.value x = c := by
  constructor
  · intro hz
    have hs : f.second =ᵐ[intervalMeasure a b] 0 := by
      have h := f.secondDerivative.derivative_memLp.coeFn_toLp
      change f.secondL2 =ᵐ[intervalMeasure a b] f.second at h
      rw [hz] at h
      exact h.symm.trans (Lp.coeFn_zero ℂ 2 (intervalMeasure a b))
    have hfirst : ∀ x ∈ Icc a b, f.first x = 0 := by
      intro x hx
      apply Complex.ext
      · have h := f.secondDerivative.re.constant_of_derivative_eq_zero hab.le
          (hs.fun_comp Complex.re) x hx
        simpa only [hf.1, Complex.zero_re] using h
      · have h := f.secondDerivative.im.constant_of_derivative_eq_zero hab.le
          (hs.fun_comp Complex.im) x hx
        simpa only [hf.1, Complex.zero_im] using h
    have hfae : f.first =ᵐ[intervalMeasure a b] 0 :=
      ae_restrict_of_forall_mem measurableSet_Icc hfirst
    refine ⟨f.value a, fun x hx => ?_⟩
    exact Complex.ext
      (f.firstDerivative.re.constant_of_derivative_eq_zero hab.le
        (hfae.fun_comp Complex.re) x hx)
      (f.firstDerivative.im.constant_of_derivative_eq_zero hab.le
        (hfae.fun_comp Complex.im) x hx)
  · rintro ⟨c, hc⟩
    have heq : f.toL2 = (ComplexH2Representative.constant a b c).toL2 := by
      apply (f.toL2_eq_iff _).mpr
      exact ae_restrict_of_forall_mem measurableSet_Icc hc
    exact (ComplexH2Representative.secondL2_unique hab heq).trans
      (ComplexH2Representative.secondL2_constant a b c)

noncomputable def complexNeumannDomain (a b : ℝ) : Submodule ℂ (ComplexIntervalL2 a b) where
  carrier := {u | ∃ f : ComplexH2Representative a b, IsComplexNeumann f ∧ f.toL2 = u}
  zero_mem' := ⟨ComplexH2Representative.constant a b 0, ⟨rfl, rfl⟩, rfl⟩
  add_mem' := by
    rintro u v ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f.add g,
      by simp [IsComplexNeumann, ComplexH2Representative.add, hf.1, hf.2, hg.1, hg.2],
      ComplexH2Representative.toL2_add f g⟩
  smul_mem' := by
    rintro c u ⟨f, hf, rfl⟩
    exact ⟨f.smul c,
      by simp [IsComplexNeumann, ComplexH2Representative.smul, hf.1, hf.2],
      ComplexH2Representative.toL2_smul c f⟩

noncomputable def complexNeumannRepresentative {a b : ℝ} (u : complexNeumannDomain a b) :
    ComplexH2Representative a b := Classical.choose u.property

theorem complexNeumannRepresentative_spec {a b : ℝ} (u : complexNeumannDomain a b) :
    IsComplexNeumann (complexNeumannRepresentative u) ∧
      (complexNeumannRepresentative u).toL2 = (u : ComplexIntervalL2 a b) :=
  Classical.choose_spec u.property

noncomputable def complexNeumannOperator {a b : ℝ} (hab : a < b) :
    ComplexIntervalL2 a b →ₗ.[ℂ] ComplexIntervalL2 a b where
  domain := complexNeumannDomain a b
  toFun :=
    { toFun := fun u => -(complexNeumannRepresentative u).secondL2
      map_add' := by
        intro u v
        have heq : (complexNeumannRepresentative (u + v)).toL2 =
            ((complexNeumannRepresentative u).add (complexNeumannRepresentative v)).toL2 := by
          rw [ComplexH2Representative.toL2_add, (complexNeumannRepresentative_spec (u + v)).2,
            (complexNeumannRepresentative_spec u).2, (complexNeumannRepresentative_spec v).2]
          rfl
        rw [ComplexH2Representative.secondL2_unique hab heq,
          ComplexH2Representative.secondL2_add, neg_add]
      map_smul' := by
        intro c u
        have heq : (complexNeumannRepresentative (c • u)).toL2 =
            ((complexNeumannRepresentative u).smul c).toL2 := by
          rw [ComplexH2Representative.toL2_smul, (complexNeumannRepresentative_spec (c • u)).2,
            (complexNeumannRepresentative_spec u).2]
          rfl
        rw [ComplexH2Representative.secondL2_unique hab heq,
          ComplexH2Representative.secondL2_smul, smul_neg]
        rfl }

theorem complexNeumannOperator_on_representative {a b : ℝ} (hab : a < b)
    (f : ComplexH2Representative a b) (hf : IsComplexNeumann f) :
    (complexNeumannOperator hab).toFun ⟨f.toL2, f, hf, rfl⟩ = -f.secondL2 := by
  change -(complexNeumannRepresentative ⟨f.toL2, f, hf, rfl⟩).secondL2 = -f.secondL2
  congr 1
  exact ComplexH2Representative.secondL2_unique hab (complexNeumannRepresentative_spec _).2

theorem complexNeumann_formalAdjoint {a b : ℝ} (hab : a < b) :
    (complexNeumannOperator hab).IsFormalAdjoint (complexNeumannOperator hab) := by
  intro u v
  change inner ℂ (-(complexNeumannRepresentative u).secondL2) (v : ComplexIntervalL2 a b) =
    inner ℂ (u : ComplexIntervalL2 a b) (-(complexNeumannRepresentative v).secondL2)
  rw [← (complexNeumannRepresentative_spec u).2, ← (complexNeumannRepresentative_spec v).2]
  exact complexNeumann_symmetric hab.le _ _
    (complexNeumannRepresentative_spec u).1 (complexNeumannRepresentative_spec v).1

end GeneratedFoundations.Spectral
