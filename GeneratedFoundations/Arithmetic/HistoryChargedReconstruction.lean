module

public import GeneratedFoundations.Arithmetic.HistoryJointChargeQuotient

/-!
# Retained charged representatives of the actual joint response

The charged space is the range of the complement of the computed neutral
projection. It is canonically equivalent to the quotient by the full
neutral kernel. The equivalence retains the actual vector, not merely its
dimension or its charge label. Orthogonality proves an exact norm ledger.
The degenerate and smallest nontrivial fibres are included explicitly.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryChargedReconstruction

open HistoryJointCharge HistoryJointChargeLattice HistoryJointChargeQuotient
open HistoryPhaseProjection (projection residual)

theorem residual_adjoint (n : ℕ) : (residual n).adjoint = residual n := by
  simp [HistoryPhaseProjection.residual, HistoryPhaseProjection.projection_adjoint]

theorem neutralComponent_symmetric (n : ℕ) (s : Spin) (x y : Fibre n) :
    inner ℂ (neutralComponent n s x) y = inner ℂ x (neutralComponent n s y) := by
  have hp : inner ℂ (projection n x) y = inner ℂ x (projection n y) := by
    simpa only [HistoryPhaseProjection.projection_adjoint] using
      LinearMap.adjoint_inner_left (projection n) y x
  have hr : inner ℂ (residual n x) y = inner ℂ x (residual n y) := by
    simpa only [residual_adjoint] using LinearMap.adjoint_inner_left (residual n) y x
  change inner ℂ (mask _ • projection n x + mask _ • residual n x) y =
    inner ℂ x (mask _ • projection n y + mask _ • residual n y)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hp, hr]
  have hm (z : ℤ) : (starRingEnd ℂ) (mask z) = mask z := by
    by_cases hz : z = 0 <;> simp [mask, hz]
  rw [hm, hm]

theorem neutralProjection_symmetric (n : ℕ) (x y : Space n) :
    inner ℂ (neutralProjection n x) y = inner ℂ x (neutralProjection n y) := by
  change (∑ s : Spin, inner ℂ (neutralProjection n x s) (y s)) =
    ∑ s : Spin, inner ℂ (x s) (neutralProjection n y s)
  apply Finset.sum_congr rfl
  intro s _
  simpa only [neutralProjection, blocks_apply] using neutralComponent_symmetric n s (x s) (y s)

theorem neutralProjection_adjoint (n : ℕ) :
    (neutralProjection n).adjoint = neutralProjection n := by
  symm
  exact (LinearMap.eq_adjoint_iff _ _).mpr (neutralProjection_symmetric n)

def chargedProjection (n : ℕ) : Module.End ℂ (Space n) := 1 - neutralProjection n

abbrev Charged (n : ℕ) := LinearMap.range (chargedProjection n)
abbrev Quotient (n : ℕ) := Space n ⧸ neutral n

theorem reconstruction (n : ℕ) (x : Space n) :
    neutralProjection n x + chargedProjection n x = x := by
  simp [chargedProjection]

theorem charged_idempotent (n : ℕ) : IsIdempotentElem (chargedProjection n) := by
  have hp : neutralProjection n * neutralProjection n = neutralProjection n :=
    neutralProjection_idempotent n
  change (1 - neutralProjection n) * (1 - neutralProjection n) = 1 - neutralProjection n
  noncomm_ring [hp]

theorem neutral_charged_zero (n : ℕ) : neutralProjection n * chargedProjection n = 0 := by
  rw [chargedProjection, mul_sub, mul_one]
  exact sub_eq_zero.mpr (neutralProjection_idempotent n).symm

theorem charged_neutral_zero (n : ℕ) : chargedProjection n * neutralProjection n = 0 := by
  rw [chargedProjection, sub_mul, one_mul]
  exact sub_eq_zero.mpr (neutralProjection_idempotent n).symm

theorem ker_charged (n : ℕ) : LinearMap.ker (chargedProjection n) = neutral n := by
  ext x
  change x - neutralProjection n x = 0 ↔ x ∈ neutral n
  rw [sub_eq_zero, eq_comm]
  exact neutralProjection_fixed_iff n x

def quotientRetained (n : ℕ) : Quotient n ≃ₗ[ℂ] Charged n :=
  (Submodule.quotEquivOfEq _ _ (ker_charged n).symm).trans
    ((chargedProjection n).quotKerEquivRange)

theorem quotientRetained_apply (n : ℕ) (x : Space n) :
    (quotientRetained n ((neutral n).mkQ x) : Space n) = chargedProjection n x := by
  exact (chargedProjection n).quotKerEquivRange_apply_mk x

theorem retained_reconstruction (n : ℕ) (x : Space n) :
    neutralProjection n x + (quotientRetained n ((neutral n).mkQ x) : Space n) = x := by
  rw [quotientRetained_apply, reconstruction]

theorem neutral_charged_inner (n : ℕ) (x y : Space n) :
    inner ℂ (neutralProjection n x) (chargedProjection n y) = 0 := by
  rw [neutralProjection_symmetric]
  have hz := LinearMap.congr_fun (neutral_charged_zero n) y
  change neutralProjection n (chargedProjection n y) = 0 at hz
  rw [hz, inner_zero_right]

theorem retained_energy (n : ℕ) (x : Space n) :
    ‖x‖ ^ 2 = ‖neutralProjection n x‖ ^ 2 +
      ‖(quotientRetained n ((neutral n).mkQ x) : Space n)‖ ^ 2 := by
  rw [quotientRetained_apply]
  have h := norm_add_sq (𝕜 := ℂ) (neutralProjection n x) (chargedProjection n x)
  rw [reconstruction, neutral_charged_inner] at h
  simpa using h

theorem response_retained (n : ℕ) (x : Space n) :
    generatedResponse n (quotientRetained n ((neutral n).mkQ x) : Space n) =
      generatedResponse n x := by
  rw [quotientRetained_apply]
  change generatedResponse n (x - neutralProjection n x) = _
  rw [map_sub]
  have hz := LinearMap.congr_fun (response_neutral_zero n) x
  change generatedResponse n (neutralProjection n x) = 0 at hz
  rw [hz, sub_zero]

def descend {W : Type*} [AddCommGroup W] [Module ℂ W] (n : ℕ)
    (f : Space n →ₗ[ℂ] W) (hf : neutral n ≤ LinearMap.ker f) :
    Quotient n →ₗ[ℂ] W := (neutral n).liftQ f hf

theorem descend_existsUnique {W : Type*} [AddCommGroup W] [Module ℂ W] (n : ℕ)
    (f : Space n →ₗ[ℂ] W) (hf : neutral n ≤ LinearMap.ker f) :
    ∃! g : Quotient n →ₗ[ℂ] W, g.comp ((neutral n).mkQ) = f := by
  refine ⟨descend n f hf, Submodule.liftQ_mkQ _ _ _, ?_⟩
  intro g hg
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (neutral n).mkQ_surjective q
  exact (LinearMap.congr_fun hg x).trans
    (LinearMap.congr_fun (Submodule.liftQ_mkQ (neutral n) f hf).symm x)

theorem neutral_finrank_one : Module.finrank ℂ (neutral 1) =
    2 * Fintype.card (CompleteHistory.History 2) := by
  have h := (LinearMap.IsIdempotentElem.isProj_range _
    (neutralProjection_idempotent 1)).trace
  rw [neutral_range, neutral_trace_one] at h
  exact_mod_cast h.symm

theorem charged_finrank_one : Module.finrank ℂ (Quotient 1) =
    6 * Fintype.card (CompleteHistory.History 2) := by
  have h := (neutral 1).finrank_quotient_add_finrank
  rw [neutral_finrank_one, full_dimension] at h
  nlinarith

structure Conclusions : Prop where
  actual_orthogonal_projection : ∀ n, (neutralProjection n).adjoint = neutralProjection n
  retained_bijective : ∀ n, Function.Bijective (quotientRetained n)
  full_reconstruction : ∀ n x, neutralProjection n x +
    (quotientRetained n ((neutral n).mkQ x) : Space n) = x
  exact_energy : ∀ n x, ‖x‖ ^ 2 = ‖neutralProjection n x‖ ^ 2 +
    ‖(quotientRetained n ((neutral n).mkQ x) : Space n)‖ ^ 2
  complete_response : ∀ n x,
    generatedResponse n (quotientRetained n ((neutral n).mkQ x) : Space n) = generatedResponse n x
  small_neutral_rank : Module.finrank ℂ (neutral 1) =
    2 * Fintype.card (CompleteHistory.History 2)

theorem generated : Conclusions where
  actual_orthogonal_projection := neutralProjection_adjoint
  retained_bijective := fun n => (quotientRetained n).bijective
  full_reconstruction := retained_reconstruction
  exact_energy := retained_energy
  complete_response := response_retained
  small_neutral_rank := neutral_finrank_one

end GeneratedFoundations.Arithmetic.HistoryChargedReconstruction
