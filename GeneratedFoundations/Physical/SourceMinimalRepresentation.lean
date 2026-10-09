module

public import GeneratedFoundations.Physical.SourceJointResponse
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Least faithful Hilbert realizations of the source response algebra

The least condition compares faithful adjoint-compatible realizations on
arbitrary finite-dimensional complex Hilbert spaces.  Its existence is
proved both in the orthonormal matrix coordinates and on the orthogonal
sum of the two source tensor carriers.  Dimension eight and uniqueness up
to unitary intertwining follow from this condition.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceMinimalRepresentation

open SourceJointResponse

abbrev CoordinateHilbert :=
  MinimalFaithfulModule.StandardHilbert MinimalFaithfulModule.jointBlockSizes

section CoordinateTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- Transport a matrix-block representation through the orthonormal
coordinates of the actual source tensor spaces. -/
def sourceOfMatrix (ρ : MinimalFaithfulModule.JointRepresentation (H := H)) :
    JointEnd →ₐ[ℂ] Module.End ℂ H :=
  ρ.comp matrixCoordinates.toAlgEquiv.toAlgHom

omit [FiniteDimensional ℂ H] in
theorem matrixRepresentation_sourceOfMatrix
    (ρ : MinimalFaithfulModule.JointRepresentation (H := H)) :
    matrixRepresentation (sourceOfMatrix ρ) = ρ := by
  ext A x
  simp [matrixRepresentation, sourceOfMatrix]

omit [FiniteDimensional ℂ H] in
theorem sourceOfMatrix_matrixRepresentation
    (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H) :
    sourceOfMatrix (matrixRepresentation ρ) = ρ := by
  ext A x
  simp [matrixRepresentation, sourceOfMatrix]

omit [FiniteDimensional ℂ H] in
theorem sourceOfMatrix_adjointCompatible
    (ρ : MinimalFaithfulModule.JointRepresentation (H := H))
    (hρ : MinimalFaithfulModule.JointStarCompatible ρ) :
    AdjointCompatible (sourceOfMatrix ρ) := by
  intro A x y
  change inner ℂ (ρ (matrixCoordinates A) x) y =
    inner ℂ x (ρ (matrixCoordinates (star A)) y)
  rw [map_star]
  exact hρ (matrixCoordinates A) x y

omit [FiniteDimensional ℂ H] in
theorem sourceOfMatrix_injective
    (ρ : MinimalFaithfulModule.JointRepresentation (H := H))
    (hρ : Function.Injective ρ) : Function.Injective (sourceOfMatrix ρ) :=
  hρ.comp matrixCoordinates.injective

end CoordinateTransport

def standardRepresentation : JointEnd →ₐ[ℂ] Module.End ℂ CoordinateHilbert :=
  sourceOfMatrix MinimalFaithfulModule.standardJointRepresentation

theorem standardRepresentation_injective : Function.Injective standardRepresentation :=
  sourceOfMatrix_injective _ MinimalFaithfulModule.standardJointRepresentation_injective

theorem standardRepresentation_adjointCompatible :
    AdjointCompatible standardRepresentation :=
  sourceOfMatrix_adjointCompatible _
    MinimalFaithfulModule.standardJointRepresentation_starCompatible

theorem coordinateHilbert_finrank : Module.finrank ℂ CoordinateHilbert = 8 :=
  MinimalFaithfulModule.standardJointRepresentation_finrank

/-- The actual colour-spin and scalar-spin carriers with their sum inner product. -/
abbrev SourceCarrier := WithLp 2 (Coloured × Scalar)

def sourceCarrierCoordinates : (Coloured × Scalar) ≃ₗ[ℂ] SourceCarrier :=
  (WithLp.linearEquiv 2 ℂ (Coloured × Scalar)).symm

def sourceCarrierRepresentation : JointEnd →ₐ[ℂ] Module.End ℂ SourceCarrier :=
  (sourceCarrierCoordinates.conjAlgEquiv ℂ).toAlgHom.comp carrierRepresentation

theorem sourceCarrierRepresentation_apply (A : JointEnd) (x : SourceCarrier) :
    WithLp.ofLp (sourceCarrierRepresentation A x) =
      (A.1 (WithLp.ofLp x).1, A.2 (WithLp.ofLp x).2) := rfl

theorem sourceCarrierRepresentation_injective :
    Function.Injective sourceCarrierRepresentation :=
  (sourceCarrierCoordinates.conjAlgEquiv ℂ).injective.comp carrierRepresentation_injective

theorem sourceCarrierRepresentation_adjointCompatible :
    AdjointCompatible sourceCarrierRepresentation := by
  intro A x y
  change inner ℂ (A.1 (WithLp.ofLp x).1) (WithLp.ofLp y).1 +
      inner ℂ (A.2 (WithLp.ofLp x).2) (WithLp.ofLp y).2 =
    inner ℂ (WithLp.ofLp x).1 (star A.1 (WithLp.ofLp y).1) +
      inner ℂ (WithLp.ofLp x).2 (star A.2 (WithLp.ofLp y).2)
  simp only [LinearMap.star_eq_adjoint, LinearMap.adjoint_inner_right]

theorem sourceCarrier_finrank : Module.finrank ℂ SourceCarrier = 8 := by
  rw [← sourceCarrierCoordinates.finrank_eq]
  exact carrier_finrank_eight

section LeastRealization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- Least dimension among faithful adjoint-compatible Hilbert realizations
of the actual source response algebra. -/
def IsLeastFaithfulRepresentation (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H) : Prop :=
  Function.Injective ρ ∧ AdjointCompatible ρ ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [FiniteDimensional ℂ E] (σ : JointEnd →ₐ[ℂ] Module.End ℂ E),
      Function.Injective σ → AdjointCompatible σ →
        Module.finrank ℂ H ≤ Module.finrank ℂ E

theorem standardRepresentation_isLeast :
    IsLeastFaithfulRepresentation standardRepresentation := by
  refine ⟨standardRepresentation_injective, standardRepresentation_adjointCompatible, ?_⟩
  intro E _ _ _ σ hσ _
  rw [coordinateHilbert_finrank]
  exact faithful_finrank_ge_eight σ hσ

theorem sourceCarrierRepresentation_isLeast :
    IsLeastFaithfulRepresentation sourceCarrierRepresentation := by
  refine ⟨sourceCarrierRepresentation_injective,
    sourceCarrierRepresentation_adjointCompatible, ?_⟩
  intro E _ _ _ σ hσ _
  rw [sourceCarrier_finrank]
  exact faithful_finrank_ge_eight σ hσ

theorem least_finrank_eight (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeastFaithfulRepresentation ρ) : Module.finrank ℂ H = 8 := by
  have hle := hρ.2.2 SourceCarrier sourceCarrierRepresentation
    sourceCarrierRepresentation_injective sourceCarrierRepresentation_adjointCompatible
  rw [sourceCarrier_finrank] at hle
  exact Nat.le_antisymm hle (faithful_finrank_ge_eight ρ hρ.1)

theorem isLeast_iff (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H) :
    IsLeastFaithfulRepresentation ρ ↔
      Function.Injective ρ ∧ AdjointCompatible ρ ∧ Module.finrank ℂ H = 8 := by
  constructor
  · intro hρ
    exact ⟨hρ.1, hρ.2.1, least_finrank_eight ρ hρ⟩
  · rintro ⟨hρinj, hρstar, hdim⟩
    refine ⟨hρinj, hρstar, ?_⟩
    intro E _ _ _ σ hσ _
    rw [hdim]
    exact faithful_finrank_ge_eight σ hσ

omit [FiniteDimensional ℂ H] in
theorem isLeast_iff_matrixRepresentation (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H) :
    IsLeastFaithfulRepresentation ρ ↔
      MinimalFaithfulModule.IsLeastFaithfulJointRepresentation (matrixRepresentation ρ) := by
  constructor
  · intro hρ
    refine ⟨hρ.1.comp matrixCoordinates.symm.injective,
      matrixRepresentation_starCompatible ρ hρ.2.1, ?_⟩
    intro E _ _ _ σ hσinj hσstar
    exact hρ.2.2 E (sourceOfMatrix σ) (sourceOfMatrix_injective σ hσinj)
      (sourceOfMatrix_adjointCompatible σ hσstar)
  · intro hρ
    have hρinj : Function.Injective ρ := by
      intro A B hAB
      apply matrixCoordinates.injective
      apply hρ.1
      change ρ (matrixCoordinates.symm (matrixCoordinates A)) =
        ρ (matrixCoordinates.symm (matrixCoordinates B))
      exact (congrArg ρ (matrixCoordinates.symm_apply_apply A)).trans
        (hAB.trans (congrArg ρ (matrixCoordinates.symm_apply_apply B)).symm)
    have hρstar : AdjointCompatible ρ := by
      have h := sourceOfMatrix_adjointCompatible (matrixRepresentation ρ) hρ.2.1
      rwa [sourceOfMatrix_matrixRepresentation] at h
    refine ⟨hρinj, hρstar, ?_⟩
    intro E _ _ _ σ hσinj hσstar
    exact hρ.2.2 E (matrixRepresentation σ)
      (hσinj.comp matrixCoordinates.symm.injective)
      (matrixRepresentation_starCompatible σ hσstar)

theorem least_unitarilyEquivalentToSource (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeastFaithfulRepresentation ρ) :
    ∃ U : H ≃ₗᵢ[ℂ] SourceCarrier,
      ∀ A x, U (ρ A x) = sourceCarrierRepresentation A (U x) :=
  minimal_realizations_unitarilyEquivalent ρ hρ.2.1 hρ.1
    sourceCarrierRepresentation sourceCarrierRepresentation_adjointCompatible
    sourceCarrierRepresentation_injective (least_finrank_eight ρ hρ) sourceCarrier_finrank

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [FiniteDimensional ℂ H']

/-- The comparison also holds for a Hilbert realization in any universe. -/
theorem least_le (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeastFaithfulRepresentation ρ)
    (σ : JointEnd →ₐ[ℂ] Module.End ℂ H') (hσ : Function.Injective σ) :
    Module.finrank ℂ H ≤ Module.finrank ℂ H' := by
  rw [least_finrank_eight ρ hρ]
  exact faithful_finrank_ge_eight σ hσ

/-- The realization is unique up to a unitary intertwiner; the intertwiner
itself need not be unique. -/
theorem least_unique (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H)
    (hρ : IsLeastFaithfulRepresentation ρ)
    (σ : JointEnd →ₐ[ℂ] Module.End ℂ H')
    (hσ : IsLeastFaithfulRepresentation σ) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ A x, U (ρ A x) = σ A (U x) :=
  minimal_realizations_unitarilyEquivalent ρ hρ.2.1 hρ.1 σ hσ.2.1 hσ.1
    (least_finrank_eight ρ hρ) (least_finrank_eight σ hσ)

end LeastRealization

theorem sourceCarrier_unitarilyEquivalentToCoordinates :
    ∃ U : SourceCarrier ≃ₗᵢ[ℂ] CoordinateHilbert,
      ∀ A x, U (sourceCarrierRepresentation A x) = standardRepresentation A (U x) :=
  least_unique sourceCarrierRepresentation sourceCarrierRepresentation_isLeast
    standardRepresentation standardRepresentation_isLeast

end GeneratedFoundations.Physical.SourceMinimalRepresentation
