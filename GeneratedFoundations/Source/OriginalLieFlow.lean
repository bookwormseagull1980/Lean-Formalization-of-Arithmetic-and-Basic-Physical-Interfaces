module

public import GeneratedFoundations.Source.TraceLieGeometry
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Global flows in the original Lie-group structure

A local integral curve of a left-invariant vector field is translated to
every initial point with the same existence interval. The uniform-time
extension theorem then produces a global integral curve in the original
atlas. Uniqueness proves its one-parameter subgroup and scaling laws.

The real variable parameterizes the group curve. The exponential below is
its value at parameter one. Its character formula follows from the scalar
differential equation along the curve. No inverse character is used in the
construction. Joint smoothness of the exponential as a function of the Lie
vector and comparison with a separately defined library exponential are not
asserted here.
-/

@[expose] public section

noncomputable section

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace GeneratedFoundations.Source.OriginalLieFlow

variable (d : MinimalCarrier.OrthogonalChangeDatum)

theorem invariantField_contMDiff
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    ContMDiff (𝓡 d.groupDimension)
      ((𝓡 d.groupDimension).tangent) 1
      (fun g => (⟨g, mulInvariantVectorField (I := 𝓡 d.groupDimension) X g⟩ :
        TangentBundle (𝓡 d.groupDimension) d.Changes)) := by
  let : LieGroup (𝓡 d.groupDimension) (minSmoothness ℝ 3) d.Changes :=
    LieGroup.of_le (n := ∞) (by simp)
  exact (contMDiff_mulInvariantVectorField X).of_le
    (le_trans (by norm_num : (1 : ℕ∞ω) ≤ 2) le_minSmoothness)

set_option backward.isDefEq.respectTransparency false in
theorem derivative_left_translate
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) (g k : d.Changes) :
    mfderiv (𝓡 d.groupDimension) (𝓡 d.groupDimension) (fun y => g * y) k
      (mulInvariantVectorField (I := 𝓡 d.groupDimension) X k) =
      mulInvariantVectorField (I := 𝓡 d.groupDimension) X (g * k) := by
  have hleft (a b : d.Changes) :
      MDifferentiableAt (𝓡 d.groupDimension) (𝓡 d.groupDimension) (fun y => a * y) b :=
    (contMDiff_mul_left (I := 𝓡 d.groupDimension) (n := ∞)).mdifferentiable (by simp) b
  have hcomp : (fun y : d.Changes => g * y) ∘ (fun y => k * y) =
      (fun y => (g * k) * y) := by
    funext y
    exact (mul_assoc g k y).symm
  have hc := mfderiv_comp_apply_of_eq (I := 𝓡 d.groupDimension)
    (I' := 𝓡 d.groupDimension) (I'' := 𝓡 d.groupDimension) (1 : d.Changes)
    (hleft g k) (hleft k 1) (mul_one k) X
  rw [hcomp] at hc
  exact hc.symm

set_option backward.isDefEq.respectTransparency false in
theorem left_translate_hasMFDerivAt
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) (g : d.Changes)
    {γ : ℝ → d.Changes} {t : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 d.groupDimension) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField (I := 𝓡 d.groupDimension) X (γ t)))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 d.groupDimension) (fun s => g * γ s) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField (I := 𝓡 d.groupDimension) X (g * γ t))) := by
  have hg : MDifferentiableAt (𝓡 d.groupDimension) (𝓡 d.groupDimension)
      (fun y => g * y) (γ t) :=
    (contMDiff_mul_left (I := 𝓡 d.groupDimension) (n := ∞)).mdifferentiable (by simp) _
  apply (hg.hasMFDerivAt.comp t hγ).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change mfderiv (𝓡 d.groupDimension) (𝓡 d.groupDimension) (fun y => g * y) (γ t)
    (r • mulInvariantVectorField (I := 𝓡 d.groupDimension) X (γ t)) =
    r • mulInvariantVectorField (I := 𝓡 d.groupDimension) X (g * γ t)
  rw [map_smul, derivative_left_translate]

theorem left_translate_integralCurve
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) (g : d.Changes)
    {γ : ℝ → d.Changes}
    (hγ : IsMIntegralCurve (I := 𝓡 d.groupDimension) γ (mulInvariantVectorField X)) :
    IsMIntegralCurve (I := 𝓡 d.groupDimension) (fun t => g * γ t)
      (mulInvariantVectorField X) :=
  fun t => left_translate_hasMFDerivAt d X g (hγ t)

/-- Uniform local existence follows from left translation of a single
original-atlas integral curve at the identity. -/
theorem exists_global_integralCurve
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    ∃ γ : ℝ → d.Changes, γ 0 = 1 ∧
      IsMIntegralCurve (I := 𝓡 d.groupDimension) γ (mulInvariantVectorField X) := by
  obtain ⟨γ, hzero, hlocal⟩ := CharacterDifferential.exists_local_integralCurve X
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hlocal
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn (invariantField_contMDiff d X) hε
  intro g
  refine ⟨fun t => g * γ t, by simp [hzero], ?_⟩
  intro t ht
  have hmem : t ∈ Metric.ball (0 : ℝ) ε := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, Set.mem_Ioo] using ht
  exact (left_translate_hasMFDerivAt d X g (hball t hmem)).hasMFDerivWithinAt

/-- The chosen curve is characterized uniquely by its original differential
equation and identity initial value. -/
def flow (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) : ℝ → d.Changes :=
  Classical.choose (exists_global_integralCurve d X)

@[simp]
theorem flow_zero (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) : flow d X 0 = 1 :=
  (Classical.choose_spec (exists_global_integralCurve d X)).1

theorem flow_isIntegralCurve (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    IsMIntegralCurve (I := 𝓡 d.groupDimension) (flow d X) (mulInvariantVectorField X) :=
  (Classical.choose_spec (exists_global_integralCurve d X)).2

theorem flow_continuous (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    Continuous (flow d X) := (flow_isIntegralCurve d X).continuous

set_option backward.isDefEq.respectTransparency false in
theorem flow_initial_derivative (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 d.groupDimension) (flow d X) 0 (1 : ℝ) = X := by
  have hd := congrArg
    (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin d.groupDimension) => L 1)
    (flow_isIntegralCurve d X 0).mfderiv
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 d.groupDimension) (flow d X) 0 (1 : ℝ) =
    (1 : ℝ) • mulInvariantVectorField (I := 𝓡 d.groupDimension) X (flow d X 0) at hd
  rw [one_smul, flow_zero] at hd
  have hid : (fun y : d.Changes => (1 : d.Changes) * y) = id := by
    funext y
    exact one_mul y
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 d.groupDimension) (flow d X) 0 (1 : ℝ) =
    mfderiv (𝓡 d.groupDimension) (𝓡 d.groupDimension) (fun y => (1 : d.Changes) * y) 1 X at hd
  rw [hid, mfderiv_id] at hd
  exact hd

theorem flow_unique (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes)
    {γ : ℝ → d.Changes} (hzero : γ 0 = 1)
    (hγ : IsMIntegralCurve (I := 𝓡 d.groupDimension) γ (mulInvariantVectorField X)) :
    γ = flow d X :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (invariantField_contMDiff d X)
    hγ (flow_isIntegralCurve d X) (hzero.trans (flow_zero d X).symm)

theorem flow_add (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) (s t : ℝ) :
    flow d X (s + t) = flow d X s * flow d X t := by
  have hcurve := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (invariantField_contMDiff d X) ((flow_isIntegralCurve d X).comp_add s)
    (left_translate_integralCurve d X (flow d X s) (flow_isIntegralCurve d X))
    (t₀ := 0) (by simp)
  simpa only [Function.comp_apply, add_comm t s] using congrFun hcurve t

theorem flow_smul (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) (a t : ℝ) :
    flow d (a • X) t = flow d X (t * a) := by
  have hscaled : IsMIntegralCurve (I := 𝓡 d.groupDimension) (flow d X ∘ (· * a))
      (mulInvariantVectorField (a • X)) := by
    simpa only [mulInvariantVectorField_smul] using (flow_isIntegralCurve d X).comp_mul a
  have heq := flow_unique d (a • X) (γ := flow d X ∘ (· * a)) (by simp) hscaled
  exact (congrFun heq t).symm

/-- Evaluation at parameter one of the unique original left-invariant flow. -/
def lieExponential (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) : d.Changes :=
  flow d X 1

theorem lieExponential_smul (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) (t : ℝ) :
    lieExponential d (t • X) = flow d X t := by
  simp only [lieExponential, flow_smul, one_mul]

theorem lieExponential_curve_isIntegralCurve
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    IsMIntegralCurve (I := 𝓡 d.groupDimension) (fun t => lieExponential d (t • X))
      (mulInvariantVectorField X) := by
  simpa only [lieExponential_smul] using flow_isIntegralCurve d X

/-- The original global flow determines the character exponential by its
differential equation, with no assumed inverse-character smoothness. -/
theorem character_flow (χ : d.Changes →* Circle) (hχ : Continuous χ)
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) (t : ℝ) :
    (χ (flow d X t) : ℂ) = Complex.exp ((t : ℂ) * CharacterDifferential.differential χ X) := by
  let a : ℂ := CharacterDifferential.differential χ X
  have hconstant (s : ℝ) :
      HasDerivAt (fun r : ℝ => (χ (flow d X r) : ℂ) * Complex.exp (-(r : ℂ) * a)) 0 s := by
    have hchar := CharacterDifferential.curve_character_hasDerivAt χ hχ X
      (flow_isIntegralCurve d X s)
    have hreal : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
        (Complex.ofRealCLM.hasDerivAt (x := s))
    have hexp := (hreal.neg.mul_const a).cexp
    convert hchar.mul hexp using 1
    dsimp [a]
    ring
  have hc := is_const_of_deriv_eq_zero
    (fun s => (hconstant s).differentiableAt) (fun s => (hconstant s).deriv) t 0
  have hproduct : (χ (flow d X t) : ℂ) * Complex.exp (-(t : ℂ) * a) = 1 := by
    simpa only [flow_zero, map_one, Circle.coe_one, Complex.ofReal_zero, neg_zero,
      zero_mul, Complex.exp_zero, one_mul] using hc
  change (χ (flow d X t) : ℂ) = Complex.exp ((t : ℂ) * a)
  calc
    (χ (flow d X t) : ℂ) =
        ((χ (flow d X t) : ℂ) * Complex.exp (-(t : ℂ) * a)) *
          Complex.exp ((t : ℂ) * a) := by
      rw [mul_assoc, ← Complex.exp_add]
      simp only [neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp ((t : ℂ) * a) := by rw [hproduct, one_mul]

theorem character_lieExponential (χ : d.Changes →* Circle) (hχ : Continuous χ)
    (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) :
    (χ (lieExponential d X) : ℂ) = Complex.exp (CharacterDifferential.differential χ X) := by
  simpa only [lieExponential, Complex.ofReal_one, one_mul] using character_flow d χ hχ X 1

theorem positiveUnit_differential (h : MinimalCarrier.IsMinimal d)
    (χ : d.Changes ≃* Circle) (hχ : Continuous χ) :
    CharacterDifferential.differential χ.toMonoidHom
      (TraceLieGeometry.positiveUnit d h χ hχ).tangent = Complex.I := by
  apply Complex.ext
  · simpa only [Complex.I_re] using CharacterDifferential.differential_re_eq_zero
      χ.toMonoidHom hχ (TraceLieGeometry.positiveUnit d h χ hχ).tangent
  · change RepresentationDifferential.phaseDifferential d χ
      (TraceLieGeometry.positiveUnit d h χ hχ).tangent = 1
    exact TraceLieGeometry.phase_positiveUnit d h χ hχ

theorem action_lieExponential_positiveUnit (h : MinimalCarrier.IsMinimal d)
    (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
    (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v) (t : ℝ) (v : d.Carrier) :
    e (d.action (lieExponential d (t • (TraceLieGeometry.positiveUnit d h χ hχ).tangent)) v) =
      Complex.exp ((t : ℂ) * Complex.I) * e v := by
  rw [lieExponential_smul, haction]
  congr 1
  change (χ.toMonoidHom (flow d (TraceLieGeometry.positiveUnit d h χ hχ).tangent t) : ℂ) = _
  simpa only [positiveUnit_differential] using
    character_flow d χ.toMonoidHom hχ (TraceLieGeometry.positiveUnit d h χ hχ).tangent t

/-- The original minimal datum supplies a trace-unit generator and the
phase representation of its actual global one-parameter subgroup. -/
theorem minimalCarrier_original_phase_flow (h : MinimalCarrier.IsMinimal d) :
    ∃ (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes),
      RepresentationDifferential.traceMetric d X X = 1 ∧
      RepresentationDifferential.endomorphism d X = PlaneGenerator.generator e ∧
      IsMIntegralCurve (I := 𝓡 d.groupDimension) (flow d X) (mulInvariantVectorField X) ∧
      (∀ t, lieExponential d (t • X) = flow d X t) ∧
      ∀ (t : ℝ) (v : d.Carrier), e (d.action (lieExponential d (t • X)) v) =
        Complex.exp ((t : ℂ) * Complex.I) * e v := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  refine ⟨e, (TraceLieGeometry.positiveUnit d h χ hχ).tangent, ?_,
    TraceLieGeometry.positiveUnit_image d h e χ hχ haction,
    flow_isIntegralCurve d _, lieExponential_smul d _, ?_⟩
  · rw [← TraceLieGeometry.norm_sq_eq_trace d h,
      TraceLieGeometry.positiveUnit_norm d h e χ hχ haction]
    norm_num
  · exact action_lieExponential_positiveUnit d h e χ hχ haction

end GeneratedFoundations.Source.OriginalLieFlow
