module

public import GeneratedFoundations.Geometry.SourceHeatSeries
public import GeneratedFoundations.Geometry.SourceOperationDiffusion
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The actual operation law has the source heat density

The uniformly convergent source series and the operation-limit probability
law have the same moments against every original matrix entry. The proved
density of those entries identifies their continuous test functionals.
Testing the imaginary part and the negative part then proves that the series
is real and nonnegative at every point. Full support of the original Haar
measure upgrades the intermediate almost-everywhere conclusions.

Consequently the same series is the genuine Haar density of the operation
law. Neither positivity nor absolute continuity is assumed. The assertions
require a strictly positive compositional parameter; they make no assertion
of a continuous density for the identity law at parameter zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceDirectionalGenerator
open GeneratedFoundations.Geometry.SourceDirectionalMoments
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceWeakConvergence
open GeneratedFoundations.Geometry.SourceOperationDiffusion
open GeneratedFoundations.Geometry.SourceHeatSeries

namespace GeneratedFoundations.Geometry.SourceHeatKernelDensity

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance : TopologicalSpace.PseudoMetrizableSpace SU2 :=
  Topology.IsInducing.subtypeVal.pseudoMetrizableSpace

private theorem continuous_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ν : Measure SU2} [IsFiniteMeasure ν]
    {f : SU2 → E} (hf : Continuous f) : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Multiplication by the actual continuous series followed by Haar integration. -/
def kernelFunctional (k : C(SU2, ℂ)) : C(SU2, ℂ) →L[ℂ] ℂ :=
  (expectation (⟨sourceHaar, inferInstance⟩ : ProbabilityMeasure SU2)).comp
    (ContinuousLinearMap.mul ℂ C(SU2, ℂ) k)

@[simp] theorem kernelFunctional_apply (k f : C(SU2, ℂ)) :
    kernelFunctional k f = ∫ U, k U * f U ∂sourceHaar := rfl

private def complexify (f : C(SU2, ℝ)) : C(SU2, ℂ) :=
  ⟨fun U => (f U : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

private theorem kernel_real_test {k : C(SU2, ℂ)} {ρ : ProbabilityMeasure SU2}
    (h : kernelFunctional k = expectation ρ) (f : C(SU2, ℝ)) :
    (∫ U, (k U).re * f U ∂sourceHaar) = ∫ U, f U ∂(ρ : Measure SU2) := by
  have he := congrArg (fun L : C(SU2, ℂ) →L[ℂ] ℂ => L (complexify f)) h
  change (∫ U, k U * (f U : ℂ) ∂sourceHaar) =
    ∫ U, (f U : ℂ) ∂(ρ : Measure SU2) at he
  have hi : Integrable (fun U => k U * (f U : ℂ)) sourceHaar :=
    continuous_integrable (k.continuous.mul (Complex.continuous_ofReal.comp f.continuous))
  have hr := congrArg Complex.re he
  have hre : (∫ U, k U * (f U : ℂ) ∂sourceHaar).re =
      ∫ U, (k U * (f U : ℂ)).re ∂sourceHaar := (integral_re hi).symm
  rw [hre, integral_complex_ofReal] at hr
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using hr

private theorem kernel_imag_test {k : C(SU2, ℂ)} {ρ : ProbabilityMeasure SU2}
    (h : kernelFunctional k = expectation ρ) (f : C(SU2, ℝ)) :
    (∫ U, (k U).im * f U ∂sourceHaar) = 0 := by
  have he := congrArg (fun L : C(SU2, ℂ) →L[ℂ] ℂ => L (complexify f)) h
  change (∫ U, k U * (f U : ℂ) ∂sourceHaar) =
    ∫ U, (f U : ℂ) ∂(ρ : Measure SU2) at he
  have hi : Integrable (fun U => k U * (f U : ℂ)) sourceHaar :=
    continuous_integrable (k.continuous.mul (Complex.continuous_ofReal.comp f.continuous))
  have him := congrArg Complex.im he
  have himag : (∫ U, k U * (f U : ℂ) ∂sourceHaar).im =
      ∫ U, (k U * (f U : ℂ)).im ∂sourceHaar := (integral_im hi).symm
  rw [himag, integral_complex_ofReal] at him
  simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    using him

private theorem eq_zero_of_square_integral (f : C(SU2, ℝ))
    (h : (∫ U, f U ^ 2 ∂sourceHaar) = 0) : ∀ U, f U = 0 := by
  have hi : Integrable (fun U => f U ^ 2) sourceHaar :=
    continuous_integrable (f.continuous.pow 2)
  have hae : (fun U => f U ^ 2) =ᵐ[sourceHaar] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun U => sq_nonneg (f U)) hi).mp h
  have he := sourceHaar.eq_of_ae_eq hae (f.continuous.pow 2) continuous_const
  intro U
  exact sq_eq_zero_iff.mp (congrFun he U)

/-- A continuous complex density representing a probability functional is real. -/
theorem kernel_im_zero {k : C(SU2, ℂ)} {ρ : ProbabilityMeasure SU2}
    (h : kernelFunctional k = expectation ρ) (U : SU2) : (k U).im = 0 := by
  let f : C(SU2, ℝ) := ⟨fun V => (k V).im, Complex.continuous_im.comp k.continuous⟩
  have hz : (∫ V, f V ^ 2 ∂sourceHaar) = 0 := by
    simpa only [f, ContinuousMap.coe_mk, pow_two] using kernel_imag_test h f
  exact eq_zero_of_square_integral f hz U

/-- Nonnegativity follows from testing the actual negative part, not from
the signs of individual character terms. -/
theorem kernel_re_nonneg {k : C(SU2, ℂ)} {ρ : ProbabilityMeasure SU2}
    (h : kernelFunctional k = expectation ρ) (U : SU2) : 0 ≤ (k U).re := by
  let f : C(SU2, ℝ) :=
    ⟨fun V => max (-(k V).re) 0,
      ((Complex.continuous_re.comp k.continuous).neg).max continuous_const⟩
  have hf (V : SU2) : 0 ≤ f V := le_max_right _ _
  have hp (V : SU2) : (k V).re * f V = -(f V ^ 2) := by
    by_cases hk : 0 ≤ (k V).re
    · simp only [f, ContinuousMap.coe_mk, max_eq_right (neg_nonpos.mpr hk),
        mul_zero, zero_pow (by decide : 2 ≠ 0), neg_zero]
    · have hn : 0 ≤ -(k V).re := (neg_pos.mpr (lt_of_not_ge hk)).le
      simp only [f, ContinuousMap.coe_mk, max_eq_left hn]
      ring
  have hr := kernel_real_test h f
  simp_rw [hp] at hr
  rw [integral_neg] at hr
  have hs : 0 ≤ ∫ V, f V ^ 2 ∂sourceHaar := integral_nonneg (fun V => sq_nonneg (f V))
  have hn : 0 ≤ ∫ V, f V ∂(ρ : Measure SU2) := integral_nonneg hf
  have hz : (∫ V, f V ^ 2 ∂sourceHaar) = 0 := by linarith
  have he := eq_zero_of_square_integral f hz U
  have hle : -(k U).re ≤ f U := le_max_left _ _
  rw [he] at hle
  linarith

/-- Pointwise reality, rather than merely equality of Haar equivalence classes. -/
theorem kernel_eq_ofReal {k : C(SU2, ℂ)} {ρ : ProbabilityMeasure SU2}
    (h : kernelFunctional k = expectation ρ) (U : SU2) :
    k U = ((k U).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using kernel_im_zero h U

/-- Equality of continuous test functionals determines the actual density measure. -/
theorem measure_eq_withDensity {k : C(SU2, ℂ)} {ρ : ProbabilityMeasure SU2}
    (h : kernelFunctional k = expectation ρ) :
    (ρ : Measure SU2) = sourceHaar.withDensity (fun U => ENNReal.ofReal (k U).re) := by
  have hcont : Continuous (fun U => (k U).re) := Complex.continuous_re.comp k.continuous
  let : IsFiniteMeasure (sourceHaar.withDensity (fun U => ENNReal.ofReal (k U).re)) :=
    isFiniteMeasure_withDensity_ofReal (continuous_integrable hcont).hasFiniteIntegral
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(SU2, ℝ) := ⟨f, f.continuous⟩
  have hd := integral_withDensity_eq_integral_toReal_smul
    (μ := sourceHaar) (ENNReal.measurable_ofReal.comp hcont.measurable)
    (Eventually.of_forall (fun U => ENNReal.ofReal_lt_top)) (fun U => f U)
  change (∫ U, f U ∂sourceHaar.withDensity (fun U => ENNReal.ofReal (k U).re)) =
    ∫ U, (ENNReal.ofReal (k U).re).toReal • f U ∂sourceHaar at hd
  have hd' : (∫ U, f U ∂sourceHaar.withDensity (fun U => ENNReal.ofReal (k U).re)) =
      ∫ U, (k U).re * f U ∂sourceHaar := by
    simpa only [ENNReal.toReal_ofReal (kernel_re_nonneg h _),
      smul_eq_mul] using hd
  exact (kernel_real_test h fc).symm.trans hd'.symm

variable {μ : Measure Direction} [IsProbabilityMeasure μ] {c : ℝ}
  (h : CenteredIsotropic μ c)

include h

/-- The uniformly convergent series and the actual operation limit define
the same functional on every continuous observation. -/
theorem heatKernel_functional (t : ℝ) (ht : 0 < t) :
    kernelFunctional (heatKernel t) = expectation (heatLaw h t ht.le) := by
  apply linearMap_ext_of_entries
  rintro ⟨m, i, j⟩
  change (∫ U, heatKernel t U * matrixEntry m i j U ∂sourceHaar) = _
  exact (heatKernel_matrixEntry_integral t ht m i j).trans
    (heatLaw_entries h t ht.le ⟨m, i, j⟩).symm

theorem heatKernel_im_zero (t : ℝ) (ht : 0 < t) (U : SU2) :
    (heatKernel t U).im = 0 := kernel_im_zero (heatKernel_functional h t ht) U

theorem heatKernel_re_nonneg (t : ℝ) (ht : 0 < t) (U : SU2) :
    0 ≤ (heatKernel t U).re := kernel_re_nonneg (heatKernel_functional h t ht) U

theorem heatKernel_eq_ofReal (t : ℝ) (ht : 0 < t) (U : SU2) :
    heatKernel t U = ((heatKernel t U).re : ℂ) :=
  kernel_eq_ofReal (heatKernel_functional h t ht) U

/-- The positive-parameter law constructed from the original independent
operations is exactly the Haar measure weighted by the proved heat series. -/
theorem heatLaw_eq_withDensity (t : ℝ) (ht : 0 < t) :
    (heatLaw h t ht.le : Measure SU2) =
      sourceHaar.withDensity (fun U => ENNReal.ofReal (heatKernel t U).re) :=
  measure_eq_withDensity (heatKernel_functional h t ht)

theorem heatKernel_real_integral (t : ℝ) (ht : 0 < t) :
    (∫ U, (heatKernel t U).re ∂sourceHaar) = 1 := by
  simpa only [ContinuousMap.one_apply, mul_one, integral_const, probReal_univ, one_smul]
    using kernel_real_test (heatKernel_functional h t ht) (1 : C(SU2, ℝ))

end GeneratedFoundations.Geometry.SourceHeatKernelDensity
