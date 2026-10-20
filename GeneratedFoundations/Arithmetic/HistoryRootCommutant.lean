module

public import GeneratedFoundations.Arithmetic.HistoryRootSectors
public import GeneratedFoundations.Operations.MatrixBlockCommutant

/-!
# Residual freedom of the complete root-preserving history action

Every root block contains its full generated history and phase space.
The commutant is derived from the complete action on these blocks. The
conclusion is stated through the already proved unitary coordinates, so
it retains all original coefficients without choosing one history vector.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryRootCommutant

open HistoryRootSectors

theorem complete_commutant (N : ℕ) (T : Module.End ℂ (NativeSpace N))
    (hT : ∀ A x, T (nativeRepresentation N A x) = nativeRepresentation N A (T x)) :
    ∃ c : Roots N → ℂ, ∀ x b i,
      carrierCoordinates N (T x) b i = c b * carrierCoordinates N x b i := by
  let U := carrierCoordinates N
  let S : Module.End ℂ (Space N) := U.toLinearEquiv.conjAlgEquiv ℂ T
  have hS : ∀ A x, S (representation N A x) = representation N A (S x) := by
    intro A x
    have hx : U.symm (representation N A x) =
        nativeRepresentation N ((algebraCoordinates N).symm A) (U.symm x) := by
      apply U.injective
      rw [U.apply_symm_apply]
      have hn := native_intertwining N ((algebraCoordinates N).symm A) (U.symm x)
      change U (nativeRepresentation N ((algebraCoordinates N).symm A) (U.symm x)) =
        representation N ((algebraCoordinates N) ((algebraCoordinates N).symm A))
          (U (U.symm x)) at hn
      rw [U.apply_symm_apply, AlgEquiv.apply_symm_apply] at hn
      exact hn.symm
    change U (T (U.symm (representation N A x))) = representation N A (U (T (U.symm x)))
    rw [hx, hT]
    exact (native_intertwining N ((algebraCoordinates N).symm A) (T (U.symm x))).trans
      (congrArg (fun A => representation N A (U (T (U.symm x))))
        ((algebraCoordinates N).apply_symm_apply A))
  obtain ⟨c, hc⟩ := Operations.MatrixBlockCommutant.hilbert_commutant_scalar
    (size N) (base N) S hS
  refine ⟨c, ?_⟩
  intro x b i
  have h := hc (U x) b i
  change U (T (U.symm (U x))) b i = c b * U x b i at h
  simpa only [U.symm_apply_apply] using h

/-- Once the complete action is fixed, each remaining block scalar is
fixed uniquely by its action on that nonzero block. -/
theorem block_scalars_unique (N : ℕ) (c d : Roots N → ℂ)
    (h : ∀ x : Space N, ∀ b i, c b * x b i = d b * x b i) : c = d := by
  funext b
  let x : Space N := PiLp.single 2 b (PiLp.single 2 (base N b) 1)
  simpa only [x, PiLp.single_eq_same, mul_one] using h x b (base N b)

/-- For a symmetry of the original Hilbert carrier the residual scalars
are phases, one for each actual nonempty root block. -/
theorem unitary_commutant (N : ℕ) (U : NativeSpace N ≃ₗᵢ[ℂ] NativeSpace N)
    (hU : ∀ A x, U (nativeRepresentation N A x) = nativeRepresentation N A (U x)) :
    ∃ c : Roots N → ℂ, (∀ b, ‖c b‖ = 1) ∧ ∀ x b i,
      carrierCoordinates N (U x) b i = c b * carrierCoordinates N x b i := by
  obtain ⟨c, hc⟩ := complete_commutant N U.toLinearEquiv.toLinearMap hU
  change ∀ x b i, carrierCoordinates N (U x) b i =
    c b * carrierCoordinates N x b i at hc
  refine ⟨c, ?_, hc⟩
  intro b
  let e : Space N := PiLp.single 2 b (PiLp.single 2 (base N b) 1)
  have he : ‖e‖ = 1 := by simp [e]
  have hu : carrierCoordinates N (U ((carrierCoordinates N).symm e)) = c b • e := by
    apply PiLp.ext
    intro d
    apply PiLp.ext
    intro i
    rw [hc, (carrierCoordinates N).apply_symm_apply]
    by_cases hd : d = b
    · subst d
      simp [e, PiLp.smul_apply]
    · simp [e, hd, PiLp.smul_apply]
  calc
    ‖c b‖ = ‖c b‖ * ‖e‖ := by rw [he, mul_one]
    _ = ‖c b • e‖ := (norm_smul _ _).symm
    _ = ‖carrierCoordinates N (U ((carrierCoordinates N).symm e))‖ :=
      congrArg norm hu.symm
    _ = ‖U ((carrierCoordinates N).symm e)‖ := (carrierCoordinates N).norm_map _
    _ = ‖(carrierCoordinates N).symm e‖ := U.norm_map _
    _ = ‖e‖ := (carrierCoordinates N).symm.norm_map _
    _ = 1 := he

section LeastRealizations

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [FiniteDimensional ℂ H']

/-- Two least faithful adjoint-compatible realizations of the generated
root algebra are unitarily equivalent. No phase is fixed by the algebra:
the preceding commutant theorem gives precisely the remaining freedom. -/
theorem least_realizations_unitarilyEquivalent (N : ℕ)
    (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H) (hρ : NativeLeast N ρ)
    (σ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H') (hσ : NativeLeast N σ) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ A x, U (ρ A x) = σ A (U x) := by
  obtain ⟨U, hU⟩ := native_least_unitarilyEquivalent N ρ hρ
  obtain ⟨V, hV⟩ := native_least_unitarilyEquivalent N σ hσ
  refine ⟨U.trans V.symm, ?_⟩
  intro A x
  apply V.injective
  simp only [LinearIsometryEquiv.trans_apply, V.apply_symm_apply]
  rw [hV, hU, V.apply_symm_apply]

end LeastRealizations

structure Conclusions : Prop where
  actual_commutant : ∀ N (T : Module.End ℂ (NativeSpace N)),
    (∀ A x, T (nativeRepresentation N A x) = nativeRepresentation N A (T x)) →
      ∃ c : Roots N → ℂ, ∀ x b i,
        carrierCoordinates N (T x) b i = c b * carrierCoordinates N x b i
  unique_scalars : ∀ N (c d : Roots N → ℂ),
    (∀ x : Space N, ∀ b i, c b * x b i = d b * x b i) → c = d
  unitary_phases : ∀ N (U : NativeSpace N ≃ₗᵢ[ℂ] NativeSpace N),
    (∀ A x, U (nativeRepresentation N A x) = nativeRepresentation N A (U x)) →
      ∃ c : Roots N → ℂ, (∀ b, ‖c b‖ = 1) ∧ ∀ x b i,
        carrierCoordinates N (U x) b i = c b * carrierCoordinates N x b i
  least_equivalence : ∀ (N : ℕ) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H']
    (ρ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H), NativeLeast N ρ →
    ∀ (σ : NativeAlgebra N →ₐ[ℂ] Module.End ℂ H'), NativeLeast N σ →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ A x, U (ρ A x) = σ A (U x)

theorem generated : Conclusions where
  actual_commutant := complete_commutant
  unique_scalars := block_scalars_unique
  unitary_phases := unitary_commutant
  least_equivalence := fun N _ _ _ _ _ _ _ _ ρ hρ σ hσ =>
    least_realizations_unitarilyEquivalent N ρ hρ σ hσ

end GeneratedFoundations.Arithmetic.HistoryRootCommutant
