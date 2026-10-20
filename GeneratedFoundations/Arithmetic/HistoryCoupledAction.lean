module

public import GeneratedFoundations.Arithmetic.HistoryCurvatureVariation
public import GeneratedFoundations.Arithmetic.HistoryDefiningDynamics
public import GeneratedFoundations.Geometry.HilbertPolynomialVariation

/-!
# Coupled connection and state response on generated histories

The fibre is the complete generated history--phase/source space. The
connection acts on the state by its actual endomorphisms. Curvature energy,
covariant state energy and the already computed defining Casimir response
belong to one functional. The Casimir coefficient is not a new mass input.

Configurations and variations are internal variables on the fixed carrier.
All first and mixed derivatives refer to this same functional, including
the connection--state product in the covariant derivative. Local two-jet
covariance and positivity precede any restriction to a background.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryCoupledAction

open HistoryCliffordAction (Space)
open HistoryGaugeJets
open Geometry.HilbertPolynomialVariation

def matterLine (N : ℕ) (ψ ξ : MatterJet N) (t : ℝ) : MatterJet N where
  value := ψ.value + t • ξ.value
  derivative μ := ψ.derivative μ + t • ξ.derivative μ

def linearized (N : ℕ) (A V : ConnectionJet N) (ψ ξ : MatterJet N)
    (μ : CoordinateIndex N) : Space N :=
  ξ.derivative μ + A.value μ ξ.value + V.value μ ψ.value

def quadraticTerm (N : ℕ) (V : ConnectionJet N) (ξ : MatterJet N)
    (μ : CoordinateIndex N) : Space N := V.value μ ξ.value

theorem covariant_line (N : ℕ) (A V : ConnectionJet N) (ψ ξ : MatterJet N)
    (t : ℝ) (μ : CoordinateIndex N) :
    covariantComponent N (HistoryCurvatureVariation.line N A V (t : ℂ)).value
        (matterLine N ψ ξ t) μ =
      covariantComponent N A.value ψ μ + t • linearized N A V ψ ξ μ +
        t ^ 2 • quadraticTerm N V ξ μ := by
  simp only [covariantComponent, matterLine, HistoryCurvatureVariation.line,
    linearized, quadraticTerm, LinearMap.add_apply, LinearMap.smul_apply,
    map_add, LinearMap.map_smul_of_tower, smul_add]
  simp only [Complex.coe_smul]
  module

def kinetic (N : ℕ) (A : ConnectionJet N) (ψ : MatterJet N) : ℝ :=
  ∑ μ, energy (covariantComponent N A.value ψ μ)

def action (N : ℕ) (A : ConnectionJet N) (ψ : MatterJet N) : ℝ :=
  HistoryCurvatureVariation.action N A + kinetic N A ψ +
    HistoryDefiningDynamics.action N ψ.value

theorem kinetic_nonneg (N : ℕ) (A : ConnectionJet N) (ψ : MatterJet N) :
    0 ≤ kinetic N A ψ :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by norm_num)

theorem action_nonneg (N : ℕ) (A : ConnectionJet N) (ψ : MatterJet N) :
    0 ≤ action N A ψ := by
  exact add_nonneg
    (add_nonneg (div_nonneg (curvatureDensity_nonneg N A) (by norm_num))
      (kinetic_nonneg N A ψ))
    (le_trans (by positivity) (HistoryDefiningDynamics.action_coercive N ψ.value))

theorem state_coercive (N : ℕ) (A : ConnectionJet N) (ψ : MatterJet N) :
    (15 / 16 : ℝ) * ‖ψ.value‖ ^ 2 ≤ action N A ψ := by
  have hcurv : 0 ≤ HistoryCurvatureVariation.action N A :=
    div_nonneg (curvatureDensity_nonneg N A) (by norm_num)
  have hkin := kinetic_nonneg N A ψ
  have hstate := HistoryDefiningDynamics.action_coercive N ψ.value
  unfold action
  linarith

theorem kinetic_gauge (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N)
    (ψ : MatterJet N) :
    kinetic N (transformConnectionJet N q A)
      (transformMatterJet N q.value q.first ψ) = kinetic N A ψ := by
  have hv : (transformConnectionJet N q A).value =
      transformConnection N q.value q.first A.value := rfl
  simp only [kinetic, hv, covariantComponent_transform, energy,
    HistoryEffectiveFrames.stateResponse_norm]

theorem action_gauge (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N)
    (ψ : MatterJet N) :
    action N (transformConnectionJet N q A)
      (transformMatterJet N q.value q.first ψ) = action N A ψ := by
  unfold action
  rw [kinetic_gauge]
  simp only [HistoryCurvatureVariation.action, curvatureDensity_transform,
    HistoryDefiningDynamics.action, transformMatterJet,
    HistoryEffectiveFrames.stateResponse_norm]

def firstVariation (N : ℕ) (A V : ConnectionJet N) (ψ ξ : MatterJet N) : ℝ :=
  HistoryCurvatureVariation.firstVariation N A V +
    (∑ μ, inner ℝ (covariantComponent N A.value ψ μ) (linearized N A V ψ ξ μ)) +
    HistoryDefiningDynamics.firstVariation N ψ.value ξ.value

def lineDerivative (N : ℕ) (A V : ConnectionJet N) (ψ ξ : MatterJet N) (t : ℝ) : ℝ :=
  HistoryCurvatureVariation.lineDerivative N A V t +
    (∑ μ, (inner ℝ (covariantComponent N A.value ψ μ) (linearized N A V ψ ξ μ) +
      2 * t * (energy (linearized N A V ψ ξ μ) +
        inner ℝ (covariantComponent N A.value ψ μ) (quadraticTerm N V ξ μ)) +
      3 * t ^ 2 * inner ℝ (linearized N A V ψ ξ μ) (quadraticTerm N V ξ μ) +
      4 * t ^ 3 * energy (quadraticTerm N V ξ μ))) +
    (HistoryDefiningDynamics.firstVariation N ψ.value ξ.value +
      2 * t * HistoryDefiningDynamics.action N ξ.value)

theorem action_hasDerivAt (N : ℕ) (A V : ConnectionJet N) (ψ ξ : MatterJet N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => action N (HistoryCurvatureVariation.line N A V (s : ℂ))
      (matterLine N ψ ξ s)) (lineDerivative N A V ψ ξ t) t := by
  have hk := HasDerivAt.sum (u := Finset.univ) (fun μ _ =>
    energy_quadratic_path_hasDerivAt (covariantComponent N A.value ψ μ)
      (linearized N A V ψ ξ μ) (quadraticTerm N V ξ μ) t)
  have hs := ((HistoryCurvatureVariation.action_line_hasDerivAt N A V t).add hk).add
    (HistoryDefiningDynamics.action_hasDerivAt N ψ.value ξ.value t)
  convert hs using 1
  · funext s
    simp only [action, kinetic, covariant_line, Pi.add_apply, Finset.sum_apply]
    rfl
  · rfl

theorem action_first_deriv (N : ℕ) (A V : ConnectionJet N) (ψ ξ : MatterJet N) :
    deriv (fun s : ℝ => action N (HistoryCurvatureVariation.line N A V (s : ℂ))
      (matterLine N ψ ξ s)) 0 = firstVariation N A V ψ ξ := by
  rw [(action_hasDerivAt N A V ψ ξ 0).deriv]
  simp [lineDerivative, firstVariation]

def mixedTerm (N : ℕ) (V W : ConnectionJet N) (ξ η : MatterJet N)
    (μ : CoordinateIndex N) : Space N := V.value μ η.value + W.value μ ξ.value

theorem linearized_line (N : ℕ) (A V W : ConnectionJet N) (ψ ξ η : MatterJet N)
    (t : ℝ) (μ : CoordinateIndex N) :
    linearized N (HistoryCurvatureVariation.line N A W (t : ℂ)) V
        (matterLine N ψ η t) ξ μ =
      linearized N A V ψ ξ μ + t • mixedTerm N V W ξ η μ := by
  simp only [linearized, matterLine, HistoryCurvatureVariation.line, mixedTerm,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, LinearMap.map_smul_of_tower]
  simp only [Complex.coe_smul]
  module

def hessian (N : ℕ) (A V W : ConnectionJet N) (ψ ξ η : MatterJet N) : ℝ :=
  HistoryCurvatureVariation.hessian N A V W +
    (∑ μ, (inner ℝ (linearized N A W ψ η μ) (linearized N A V ψ ξ μ) +
      inner ℝ (covariantComponent N A.value ψ μ) (mixedTerm N V W ξ η μ))) +
    HistoryDefiningDynamics.hessian N ξ.value η.value

theorem hessian_symm (N : ℕ) (A V W : ConnectionJet N) (ψ ξ η : MatterJet N) :
    hessian N A V W ψ ξ η = hessian N A W V ψ η ξ := by
  simp only [hessian, HistoryCurvatureVariation.hessian_symm N A V W,
    HistoryDefiningDynamics.hessian_symm N ξ.value η.value]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro μ _
  rw [real_inner_comm (linearized N A W ψ η μ)]
  simp only [mixedTerm, add_comm]

theorem firstVariation_hasDerivAt (N : ℕ) (A V W : ConnectionJet N)
    (ψ ξ η : MatterJet N) :
    HasDerivAt (fun t : ℝ => firstVariation N
      (HistoryCurvatureVariation.line N A W (t : ℂ)) V (matterLine N ψ η t) ξ)
      (hessian N A V W ψ ξ η) 0 := by
  have hk := HasDerivAt.sum (u := Finset.univ) (fun μ _ =>
    inner_quadratic_linear_hasDerivAt_zero (covariantComponent N A.value ψ μ)
      (linearized N A W ψ η μ) (quadraticTerm N W η μ)
      (linearized N A V ψ ξ μ) (mixedTerm N V W ξ η μ))
  have hs := ((HistoryCurvatureVariation.firstVariation_line_hasDerivAt_zero N A V W).add hk).add
    (HistoryDefiningDynamics.firstVariation_hasDerivAt N ψ.value ξ.value η.value 0)
  convert hs using 1
  · funext t
    simp only [firstVariation, covariant_line, linearized_line,
      Pi.add_apply, Finset.sum_apply]
    rfl
  · rfl

theorem action_mixed_deriv (N : ℕ) (A V W : ConnectionJet N) (ψ ξ η : MatterJet N) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => action N
      (HistoryCurvatureVariation.line N (HistoryCurvatureVariation.line N A W (t : ℂ))
        V (s : ℂ)) (matterLine N (matterLine N ψ η t) ξ s)) 0) 0 =
      hessian N A V W ψ ξ η := by
  have he : (fun t : ℝ => deriv (fun s : ℝ => action N
      (HistoryCurvatureVariation.line N (HistoryCurvatureVariation.line N A W (t : ℂ))
        V (s : ℂ)) (matterLine N (matterLine N ψ η t) ξ s)) 0) =
      (fun t : ℝ => firstVariation N (HistoryCurvatureVariation.line N A W (t : ℂ))
        V (matterLine N ψ η t) ξ) := by
    funext t
    exact action_first_deriv N _ V _ ξ
  rw [he]
  exact (firstVariation_hasDerivAt N A V W ψ ξ η).deriv

structure Conclusions : Prop where
  coupled_response : ∀ N A V ψ ξ (t : ℝ) μ,
    covariantComponent N (HistoryCurvatureVariation.line N A V (t : ℂ)).value
      (matterLine N ψ ξ t) μ = covariantComponent N A.value ψ μ +
        t • linearized N A V ψ ξ μ + t ^ 2 • quadraticTerm N V ξ μ
  full_positivity : ∀ N A ψ, 0 ≤ action N A ψ
  actual_state_bound : ∀ N A ψ, (15 / 16 : ℝ) * ‖ψ.value‖ ^ 2 ≤ action N A ψ
  local_invariance : ∀ N q A ψ, action N (transformConnectionJet N q A)
    (transformMatterJet N q.value q.first ψ) = action N A ψ
  actual_first_derivative : ∀ N A V ψ ξ,
    deriv (fun s : ℝ => action N (HistoryCurvatureVariation.line N A V (s : ℂ))
      (matterLine N ψ ξ s)) 0 = firstVariation N A V ψ ξ
  actual_mixed_derivative : ∀ N A V W ψ ξ η,
    deriv (fun t : ℝ => deriv (fun s : ℝ => action N
      (HistoryCurvatureVariation.line N (HistoryCurvatureVariation.line N A W (t : ℂ))
        V (s : ℂ)) (matterLine N (matterLine N ψ η t) ξ s)) 0) 0 =
      hessian N A V W ψ ξ η
  mixed_symmetry : ∀ N A V W ψ ξ η,
    hessian N A V W ψ ξ η = hessian N A W V ψ η ξ

theorem generated : Conclusions where
  coupled_response := covariant_line
  full_positivity := action_nonneg
  actual_state_bound := state_coercive
  local_invariance := action_gauge
  actual_first_derivative := action_first_deriv
  actual_mixed_derivative := action_mixed_deriv
  mixed_symmetry := hessian_symm

end GeneratedFoundations.Arithmetic.HistoryCoupledAction
