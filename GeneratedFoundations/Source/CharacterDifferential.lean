module

public import GeneratedFoundations.Source.SmoothCharacter
public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Tactic.Linarith

/-!
# The differential of a faithful circle character

All derivatives and integral curves use the original Lie-group structure.
Automatic smoothness comes from Haar averaging, while injectivity of the
differential follows from local integral curves of left-invariant fields.
Neither a one-dimensional Lie algebra nor a smooth inverse character is
assumed. The real coordinate obtained from the imaginary differential is not
identified here with the norm supplied by an arbitrary source chart.
-/

@[expose] public section

noncomputable section

open Set Filter Function
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace GeneratedFoundations.Source.CharacterDifferential

/-- A nontrivial connected Lie group in the original comparison class cannot
have a zero-dimensional model: its original charts would make it discrete. -/
theorem groupDimension_pos (d : MinimalCarrier.OrthogonalChangeDatum) :
    0 < d.groupDimension := by
  apply Nat.pos_of_ne_zero
  intro hz
  let : Subsingleton (EuclideanSpace ℝ (Fin d.groupDimension)) := by
    rw [hz]
    infer_instance
  let : DiscreteTopology d.Changes :=
    ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin d.groupDimension)) d.Changes
  let : Subsingleton d.Changes := PreconnectedSpace.trivial_of_discrete
  exact false_of_nontrivial_of_subsingleton d.Changes

section Character

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [SecondCountableTopology G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]

/-- The actual differential at the identity, for the given source atlas. -/
def differential (χ : G →* Circle) :
    GroupLieAlgebra 𝓘(ℝ, E) G →L[ℝ] ℂ :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (fun g => (χ g : ℂ)) (1 : G)

theorem character_mdifferentiable (χ : G →* Circle) (hχ : Continuous χ) :
    MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (fun g => (χ g : ℂ)) := by
  borelize G
  exact (SmoothCharacter.contMDiff_coe_character (E := E) χ hχ).mdifferentiable
    (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Differentiating the character identity transports the differential at
the identity along the original left-invariant vector field. -/
theorem mfderiv_mulInvariant (χ : G →* Circle) (hχ : Continuous χ)
    (X : GroupLieAlgebra 𝓘(ℝ, E) G) (g : G) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (fun h => (χ h : ℂ)) g
      (mulInvariantVectorField (I := 𝓘(ℝ, E)) X g) =
      (χ g : ℂ) * differential (E := E) χ X := by
  let L : ℂ →L[ℝ] ℂ :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (χ g : ℂ)).restrictScalars ℝ
  have hc := character_mdifferentiable (E := E) χ hχ
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h => g * h) (1 : G) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiable (by simp) _
  have hcomp : (fun h => (χ h : ℂ)) ∘ (fun h => g * h) =
      L ∘ (fun h => (χ h : ℂ)) := by
    funext h
    simp [L, mul_comm]
  have hleft :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ)
        ((fun h => (χ h : ℂ)) ∘ (fun h => g * h)) (1 : G) X : ℂ) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (fun h => (χ h : ℂ)) g
        (mulInvariantVectorField (I := 𝓘(ℝ, E)) X g) :=
    mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, ℂ)) (1 : G) (hc g) hg (mul_one g) X
  have hright :
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (L ∘ fun h => (χ h : ℂ)) (1 : G) X : ℂ) =
      L (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (fun h => (χ h : ℂ)) (1 : G) X) := by
    rw [mfderiv_comp_apply (1 : G) L.mdifferentiableAt (hc _), L.mfderiv_eq]
    rfl
  rw [hcomp] at hleft
  have ht := hleft.symm.trans hright
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (fun h => (χ h : ℂ)) g
      (mulInvariantVectorField (I := 𝓘(ℝ, E)) X g) =
    differential (E := E) χ X * (χ g : ℂ) at ht
  exact ht.trans (mul_comm (differential (E := E) χ X) (χ g : ℂ))

omit [CompactSpace G] [T2Space G] [SecondCountableTopology G] in
/-- Local integral curves exist in the given atlas. No global exponential
map or inverse-character smoothness is needed. -/
theorem exists_local_integralCurve (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    ∃ γ : ℝ → G, γ 0 = 1 ∧
      IsMIntegralCurveAt (I := 𝓘(ℝ, E)) γ
        (mulInvariantVectorField (I := 𝓘(ℝ, E)) X) 0 := by
  let : LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G :=
    LieGroup.of_le (n := ∞) (by simp)
  apply exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (0 : ℝ)
  exact (contMDiffAt_mulInvariantVectorField X).of_le
    (le_trans (by norm_num : (1 : ℕ∞ω) ≤ 2) le_minSmoothness)

set_option backward.isDefEq.respectTransparency false in
theorem curve_character_hasDerivAt (χ : G →* Circle) (hχ : Continuous χ)
    (X : GroupLieAlgebra 𝓘(ℝ, E) G) {γ : ℝ → G} {t : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField (I := 𝓘(ℝ, E)) X (γ t)))) :
    HasDerivAt (fun s => (χ (γ s) : ℂ))
      ((χ (γ t) : ℂ) * differential (E := E) χ X) t := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  have hc := (character_mdifferentiable (E := E) χ hχ (γ t)).hasMFDerivAt
  apply (hc.comp t hγ).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℂ) (fun g => (χ g : ℂ)) (γ t)
    (r • mulInvariantVectorField (I := 𝓘(ℝ, E)) X (γ t)) =
    r • ((χ (γ t) : ℂ) * differential (E := E) χ X)
  rw [map_smul, mfderiv_mulInvariant χ hχ]

set_option backward.isDefEq.respectTransparency false in
/-- A tangent vector in the kernel gives a locally constant character along
its integral curve. Faithfulness makes the curve itself locally constant. -/
theorem differential_eq_zero_iff (χ : G →* Circle) (hχ : Continuous χ)
    (hfaithful : Function.Injective χ) (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    differential (E := E) χ X = 0 ↔ X = 0 := by
  constructor
  · intro hX
    obtain ⟨γ, hγ0, hγ⟩ := exists_local_integralCurve X
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hγ
    have hderiv (t : ℝ) (ht : t ∈ Metric.ball 0 ε) :
        HasDerivAt (fun s => (χ (γ s) : ℂ)) 0 t := by
      simpa [hX] using curve_character_hasDerivAt χ hχ X (hball t ht)
    have hconstant : γ =ᶠ[𝓝 0] fun _ => (1 : G) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
      apply hfaithful
      apply Subtype.val_injective
      have hc := Metric.isOpen_ball.is_const_of_deriv_eq_zero
        (convex_ball (0 : ℝ) ε).isPreconnected
        (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
        (fun t ht => (hderiv t ht).deriv) ht (Metric.mem_ball_self hε)
      simpa [hγ0] using hc
    have hzero : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0 = 0 := by
      simpa using hconstant.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    have hv := congrArg (fun L : ℝ →L[ℝ] E => L 1)
      (hγ.hasMFDerivAt.mfderiv.symm.trans hzero)
    change (1 : ℝ) • mulInvariantVectorField (I := 𝓘(ℝ, E)) X (γ 0) = 0 at hv
    rw [one_smul] at hv
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y => γ 0 * y) (1 : G)) X = 0 at hv
    have hid : (fun y : G => γ 0 * y) = id := by
      funext y
      simp [hγ0]
    rw [hid, mfderiv_id] at hv
    exact hv
  · rintro rfl
    exact map_zero _

theorem differential_injective (χ : G →* Circle) (hχ : Continuous χ)
    (hfaithful : Function.Injective χ) :
    Function.Injective (differential (E := E) χ) := by
  intro X Y hXY
  have hz : differential (E := E) χ (X - Y) = 0 := by simp [map_sub, hXY]
  exact sub_eq_zero.mp ((differential_eq_zero_iff χ hχ hfaithful (X - Y)).mp hz)

/-- The circle-valued constraint forces the differential into the imaginary
line; this follows from differentiating the constant squared norm. -/
theorem differential_re_eq_zero (χ : G →* Circle) (hχ : Continuous χ)
    (X : GroupLieAlgebra 𝓘(ℝ, E) G) :
    (differential (E := E) χ X).re = 0 := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_local_integralCurve X
  have hd : HasDerivAt (fun s => (χ (γ s) : ℂ)) (differential (E := E) χ X) 0 := by
    simpa [hγ0] using curve_character_hasDerivAt χ hχ X hγ.hasMFDerivAt
  have hn := hd.norm_sq
  have hnorm : (fun s => ‖(χ (γ s) : ℂ)‖ ^ 2) = fun _ => (1 : ℝ) := by
    funext s
    simp
  rw [hnorm] at hn
  have hz := hn.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  have hre : 2 * (differential (E := E) χ X).re = 0 := by
    simpa [hγ0, real_inner_eq_re_inner] using hz
  linarith

theorem imaginary_differential_injective (χ : G →* Circle) (hχ : Continuous χ)
    (hfaithful : Function.Injective χ) :
    Function.Injective (Complex.imCLM.comp (differential (E := E) χ)) := by
  intro X Y hXY
  apply differential_injective χ hχ hfaithful
  apply Complex.ext
  · rw [differential_re_eq_zero χ hχ, differential_re_eq_zero χ hχ]
  · exact hXY

end Character

/-- The original minimal datum supplies the character and its faithfulness;
automatic smoothness and differential injectivity are conclusions. -/
theorem minimalCarrier_differential_injective
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d) :
    ∃ (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle),
      ContMDiff (𝓡 d.groupDimension) 𝓘(ℝ, ℂ) ∞ (fun g => (χ g : ℂ)) ∧
      Function.Injective
        (differential (E := EuclideanSpace ℝ (Fin d.groupDimension)) χ.toMonoidHom) ∧
      ∀ g v, e (d.action g v) = (χ g : ℂ) * e v := by
  obtain ⟨_, e, χ, hχ, _, hintertwine⟩ := MinimalCarrier.minimalCarrier_classification d h
  borelize d.Changes
  exact ⟨e, χ, SmoothCharacter.contMDiff_coe_character χ.toMonoidHom hχ,
    differential_injective (E := EuclideanSpace ℝ (Fin d.groupDimension))
      χ.toMonoidHom hχ χ.injective, hintertwine⟩

/-- One-dimensionality of the original Lie model is derived after, rather
than assumed before, injectivity of its imaginary differential. -/
theorem minimalCarrier_groupDimension_eq_one
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d) :
    d.groupDimension = 1 := by
  obtain ⟨_, _, χ, hχ, _, _⟩ := MinimalCarrier.minimalCarrier_classification d h
  let L : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes →L[ℝ] ℝ :=
    Complex.imCLM.comp (differential χ.toMonoidHom)
  have hinj : Function.Injective L :=
    imaginary_differential_injective χ.toMonoidHom hχ χ.injective
  have hle := LinearMap.finrank_le_finrank_of_injective (f := L.toLinearMap) hinj
  have hdim : Module.finrank ℝ (GroupLieAlgebra (𝓡 d.groupDimension) d.Changes) =
      d.groupDimension :=
    (tangentSpaceCastModel (𝓡 d.groupDimension) (1 : d.Changes)).toLinearEquiv.finrank_eq.trans
      finrank_euclideanSpace_fin
  have hup : d.groupDimension ≤ 1 := by
    simpa only [hdim, Module.finrank_self] using hle
  exact Nat.le_antisymm hup (groupDimension_pos d)

end GeneratedFoundations.Source.CharacterDifferential
