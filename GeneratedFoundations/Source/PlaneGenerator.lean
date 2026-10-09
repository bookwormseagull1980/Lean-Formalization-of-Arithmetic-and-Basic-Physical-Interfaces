module

public import GeneratedFoundations.Source.MinimalCarrier
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Normalized skew generators on a real plane

Every skew endomorphism of a real inner-product plane is a real multiple of
a quarter-turn. The representation trace form gives two unit generators.
Each generator determines one complex scalar action, and changing its sign
conjugates that action.

The coordinate isometry is available from the minimal-carrier theorem.
Identifying these operators with the differential of the original Lie-group
representation requires the smoothness and differential comparison.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Source.PlaneGenerator

open scoped ComplexConjugate

def IsSkew {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : Module.End ℝ V) : Prop :=
  ∀ v w, inner ℝ (T v) w = -inner ℝ v (T w)

def complexQuarterTurn : Module.End ℝ ℂ where
  toFun z := Complex.I * z
  map_add' z w := mul_add _ _ _
  map_smul' r z := by simp [Complex.real_smul]; ring

@[simp] theorem complexQuarterTurn_apply (z : ℂ) :
    complexQuarterTurn z = Complex.I * z := rfl

theorem complex_skew_classification (T : Module.End ℝ ℂ) (hT : IsSkew T) :
    ∃! c : ℝ, T = c • complexQuarterTurn := by
  have hreal : (T 1).re = 0 := by
    have h := hT 1 1
    simp [Complex.inner] at h
    linarith
  have himag : (T Complex.I).im = 0 := by
    have h := hT Complex.I Complex.I
    simp [Complex.inner, Complex.mul_re] at h
    linarith
  have hcross : (T Complex.I).re = -(T 1).im := by
    have h := hT Complex.I 1
    simpa [Complex.inner, Complex.mul_re] using h
  refine ⟨(T 1).im, ?_, ?_⟩
  · apply Complex.basisOneI.ext
    intro i
    fin_cases i
    · apply Complex.ext <;> simp [hreal, Complex.real_smul]
    · apply Complex.ext <;> simp [himag, hcross, Complex.real_smul]
  · intro c hc
    have h := congrArg (fun A : Module.End ℝ ℂ => (A 1).im) hc
    simpa [Complex.real_smul] using h.symm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def generator (e : V ≃ₗᵢ[ℝ] ℂ) : Module.End ℝ V :=
  e.symm.toLinearEquiv.toLinearMap.comp
    (complexQuarterTurn.comp e.toLinearEquiv.toLinearMap)

@[simp] theorem generator_coordinate (e : V ≃ₗᵢ[ℝ] ℂ) (v : V) :
    e (generator e v) = Complex.I * e v := by
  simp [generator]

theorem generator_square (e : V ≃ₗᵢ[ℝ] ℂ) :
    generator e * generator e = -1 := by
  ext v
  change generator e (generator e v) = -v
  apply e.injective
  simp [← mul_assoc]

theorem generator_skew (e : V ≃ₗᵢ[ℝ] ℂ) : IsSkew (generator e) := by
  intro v w
  rw [inner_map_complex e, inner_map_complex e]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem generator_isometry (e : V ≃ₗᵢ[ℝ] ℂ) (v : V) :
    ‖generator e v‖ = ‖v‖ := by
  rw [← e.norm_map (generator e v), generator_coordinate, norm_mul,
    Complex.norm_I, one_mul, e.norm_map]

theorem generator_injective (e : V ≃ₗᵢ[ℝ] ℂ) :
    Function.Injective (generator e) := by
  intro v w h
  apply e.injective
  have h' := congrArg e h
  simpa only [generator_coordinate, mul_right_inj' Complex.I_ne_zero] using h'

theorem generator_ne_neg (e : V ≃ₗᵢ[ℝ] ℂ) : generator e ≠ -generator e := by
  intro h
  have hv := congrArg (fun T : Module.End ℝ V => e (T (e.symm 1))) h
  have hi := congrArg Complex.im hv
  norm_num at hi

theorem generator_commutes_connectedAction
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    (e : V ≃ₗᵢ[ℝ] ℂ) (ρ : G →* (V ≃ₗᵢ[ℝ] V))
    (hcontinuous : ∀ v : V, Continuous (fun g : G => ρ g v)) (g : G) (v : V) :
    generator e (ρ g v) = ρ g (generator e v) := by
  let σ := ConnectedPlaneAction.conjugateAction e ρ
  have hc (w : ℂ) : Continuous (fun g : G => σ g w) :=
    e.continuous.comp (hcontinuous (e.symm w))
  obtain ⟨z, hz⟩ := ConnectedPlaneAction.action_is_rotation σ hc g
  have hcoord (w : V) : e (ρ g w) = (z : ℂ) * e w := by
    have hw := LinearIsometryEquiv.congr_fun hz (e w)
    simpa [σ, ConnectedPlaneAction.conjugateAction] using hw
  apply e.injective
  simp only [generator_coordinate, hcoord]
  ring

theorem skew_classification (e : V ≃ₗᵢ[ℝ] ℂ)
    (T : Module.End ℝ V) (hT : IsSkew T) :
    ∃! c : ℝ, T = c • generator e := by
  let A : Module.End ℝ ℂ := e.toLinearEquiv.conj T
  have hA : IsSkew A := by
    intro z w
    have h := hT (e.symm z) (e.symm w)
    rw [← e.inner_map_map, ← e.inner_map_map] at h
    simpa [A, LinearEquiv.conj_apply] using h
  obtain ⟨c, hc, hunique⟩ := complex_skew_classification A hA
  refine ⟨c, ?_, ?_⟩
  · ext v
    apply e.injective
    have hv := congrArg (fun L : Module.End ℝ ℂ => L (e v)) hc
    simpa [A, LinearEquiv.conj_apply] using hv
  · intro d hd
    apply hunique d
    ext z
    simp [A, LinearEquiv.conj_apply, hd]

section TraceForm

variable [FiniteDimensional ℝ V]

def tracePair (S T : Module.End ℝ V) : ℝ :=
  -(LinearMap.trace ℝ V (S * T)) / 2

omit [FiniteDimensional ℝ V] in
theorem coordinate_finrank (e : V ≃ₗᵢ[ℝ] ℂ) : Module.finrank ℝ V = 2 :=
  e.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex

theorem tracePair_smul_generator (e : V ≃ₗᵢ[ℝ] ℂ) (c d : ℝ) :
    tracePair (c • generator e) (d • generator e) = c * d := by
  unfold tracePair
  rw [smul_mul_smul_comm, generator_square, map_smul, map_neg,
    LinearMap.trace_one, coordinate_finrank e]
  simp only [smul_eq_mul, Nat.cast_ofNat]
  ring

theorem generator_trace_unit (e : V ≃ₗᵢ[ℝ] ℂ) :
    tracePair (generator e) (generator e) = 1 := by
  simpa using tracePair_smul_generator e 1 1

theorem skew_trace_positive (e : V ≃ₗᵢ[ℝ] ℂ) (T : Module.End ℝ V)
    (hT : IsSkew T) (hne : T ≠ 0) : 0 < tracePair T T := by
  obtain ⟨c, rfl, _⟩ := skew_classification e T hT
  have hc : c ≠ 0 := by intro h; simp [h] at hne
  rw [tracePair_smul_generator]
  exact mul_self_pos.mpr hc

theorem normalized_skew_iff (e : V ≃ₗᵢ[ℝ] ℂ) (T : Module.End ℝ V)
    (hT : IsSkew T) :
    tracePair T T = 1 ↔ T = generator e ∨ T = -generator e := by
  obtain ⟨c, hc, _⟩ := skew_classification e T hT
  constructor
  · intro hnorm
    rw [hc, tracePair_smul_generator] at hnorm
    have hs : c = 1 ∨ c = -1 := by
      have hsq : c ^ 2 = (1 : ℝ) ^ 2 := by nlinarith
      exact (sq_eq_sq_iff_eq_or_eq_neg).mp hsq
    rcases hs with h | h
    · left; simpa [h] using hc
    · right; simpa [h] using hc
  · rintro (rfl | rfl)
    · exact generator_trace_unit e
    · simpa using tracePair_smul_generator e (-1) (-1)

theorem minimalCarrier_has_two_unit_generators
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d) :
    ∃ J : Module.End ℝ d.Carrier,
      IsSkew J ∧ J * J = -1 ∧ tracePair J J = 1 ∧ J ≠ -J ∧
        ∀ T : Module.End ℝ d.Carrier, IsSkew T →
          (tracePair T T = 1 ↔ T = J ∨ T = -J) := by
  let e := ConnectedPlaneAction.planeCoordinate
    ((MinimalCarrier.minimal_iff_dimension_two d).mp h)
  exact ⟨generator e, generator_skew e, generator_square e,
    generator_trace_unit e, generator_ne_neg e, normalized_skew_iff e⟩

end TraceForm

section ScalarAction

variable (J : Module.End ℝ V) (hJ : J * J = -1)

def complexScalarAction : ℂ →ₐ[ℝ] Module.End ℝ V := Complex.liftAux J hJ

theorem complexScalarAction_apply (z : ℂ) (v : V) :
    complexScalarAction J hJ z v = z.re • v + z.im • J v := by
  simp [complexScalarAction, Complex.liftAux_apply]

include hJ in
theorem complexScalarAction_existsUnique :
    ∃! F : ℂ →ₐ[ℝ] Module.End ℝ V, F Complex.I = J := by
  refine ⟨complexScalarAction J hJ, Complex.liftAux_apply_I J hJ, ?_⟩
  intro F hF
  apply Complex.algHom_ext
  rw [hF, complexScalarAction, Complex.liftAux_apply_I]

theorem complexScalarAction_neg (z : ℂ) :
    complexScalarAction (-J) (by simpa using hJ) z =
      complexScalarAction J hJ (conj z) := by
  ext v
  simp [complexScalarAction_apply]

end ScalarAction

end GeneratedFoundations.Source.PlaneGenerator
