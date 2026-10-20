module

public import GeneratedFoundations.Arithmetic.HistoryChiralCoordinates
public import GeneratedFoundations.Operations.MatrixModuleClassification

/-!
# Simultaneous least realizations of the two complete arithmetic sectors

Each sector retains every generated history and phase coefficient, together
with its original two source coordinates. Arbitrary least faithful
adjoint-compatible realizations are compared to these actual sectors.
Their product unitary intertwines both independent actions, projections
and grading at once. Once that unitary is fixed, compatible transport of
every complete operator is unique; uniqueness of the unitary is not asserted.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryPairedRealization

open HistoryCliffordAction
open Operations.MatrixModuleClassification

abbrev SectorIndex (N : ℕ) := HistoryLabel N × Fin 2
abbrev SectorAlgebra (N : ℕ) := Matrix (SectorIndex N) (SectorIndex N) ℂ

def representation (N : ℕ) : SectorAlgebra N →ₐ[ℂ] Module.End ℂ (SectorSpace N) :=
  (HistoryChiralCoordinates.sectorMatrixCoordinates N).symm.toAlgEquiv.toAlgHom

theorem representation_adjoint (N : ℕ) (A : SectorAlgebra N) :
    (representation N A).adjoint = representation N A.conjTranspose := by
  change star ((HistoryChiralCoordinates.sectorMatrixCoordinates N).symm A) =
    (HistoryChiralCoordinates.sectorMatrixCoordinates N).symm (star A)
  exact (map_star (HistoryChiralCoordinates.sectorMatrixCoordinates N).symm A).symm

theorem representation_starCompatible (N : ℕ) : StarCompatible (representation N) := by
  intro A x y
  rw [← representation_adjoint]
  exact (LinearMap.adjoint_inner_right (representation N A) x y).symm

theorem representation_faithful (N : ℕ) : Function.Injective (representation N) :=
  (HistoryChiralCoordinates.sectorMatrixCoordinates N).symm.injective

variable {H HL HR : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup HL] [InnerProductSpace ℂ HL] [FiniteDimensional ℂ HL]
  [NormedAddCommGroup HR] [InnerProductSpace ℂ HR] [FiniteDimensional ℂ HR]

def IsLeast (N : ℕ) (ρ : SectorAlgebra N →ₐ[ℂ] Module.End ℂ H) : Prop :=
  Function.Injective ρ ∧ StarCompatible ρ ∧
    Module.finrank ℂ H = Fintype.card (SectorIndex N)

/-- Every faithful realization must retain the whole history multiplicity,
independently of whether it is least or adjoint compatible. -/
theorem faithful_dimension_lowerBound (N : ℕ)
    (ρ : SectorAlgebra N →ₐ[ℂ] Module.End ℂ H) (hρ : Function.Injective ρ) :
    2 * Fintype.card (HistoryLabel N) ≤ Module.finrank ℂ H := by
  have h := faithful_finrank_lowerBound ρ hρ (historyPoint N, 0)
  simpa [SectorIndex, Fintype.card_prod, Nat.mul_comm] using h

theorem native_isLeast (N : ℕ) : IsLeast N (representation N) :=
  ⟨representation_faithful N, representation_starCompatible N, finrank_euclideanSpace⟩

theorem least_unitarilyEquivalent (N : ℕ)
    (ρ : SectorAlgebra N →ₐ[ℂ] Module.End ℂ H) (hρ : IsLeast N ρ) :
    ∃ U : H ≃ₗᵢ[ℂ] SectorSpace N, ∀ A x, U (ρ A x) = representation N A (U x) :=
  minimalFaithfulRepresentation_unique ρ hρ.2.1 (representation N)
    (representation_starCompatible N) (historyPoint N, 0) hρ.2.2 finrank_euclideanSpace

abbrev Carrier (HL HR : Type*) := WithLp 2 (HL × HR)

theorem pair_finrank : Module.finrank ℂ (Carrier HL HR) =
    Module.finrank ℂ HL + Module.finrank ℂ HR := by
  rw [(WithLp.linearEquiv 2 ℂ (HL × HR)).finrank_eq, Module.finrank_prod]

/-- This dimension statement needs only the two component dimensions;
faithfulness and adjoint compatibility enter the classification, not the
dimension calculation. -/
theorem equal_size_pair_finrank (N : ℕ)
    (hL : Module.finrank ℂ HL = Fintype.card (SectorIndex N))
    (hR : Module.finrank ℂ HR = Fintype.card (SectorIndex N)) :
    Module.finrank ℂ (Carrier HL HR) = 4 * Fintype.card (HistoryLabel N) := by
  rw [pair_finrank, hL, hR]
  simp [SectorIndex, Fintype.card_prod]
  omega

theorem faithful_pair_dimension_lowerBound (N : ℕ)
    (ρL : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HL)
    (ρR : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HR)
    (hL : Function.Injective ρL) (hR : Function.Injective ρR) :
    4 * Fintype.card (HistoryLabel N) ≤ Module.finrank ℂ (Carrier HL HR) := by
  rw [(WithLp.linearEquiv 2 ℂ (HL × HR)).finrank_eq, Module.finrank_prod]
  have h₁ := faithful_dimension_lowerBound N ρL hL
  have h₂ := faithful_dimension_lowerBound N ρR hR
  omega

section Coordinates

omit [FiniteDimensional ℂ HL] [FiniteDimensional ℂ HR]

def pairCoordinates : (HL × HR) ≃ₗ[ℂ] Carrier HL HR :=
  (WithLp.linearEquiv 2 ℂ (HL × HR)).symm

def leftInclusion : HL →ₗ[ℂ] Carrier HL HR :=
  pairCoordinates.toLinearMap.comp (LinearMap.inl ℂ HL HR)

def rightInclusion : HR →ₗ[ℂ] Carrier HL HR :=
  pairCoordinates.toLinearMap.comp (LinearMap.inr ℂ HL HR)

def leftProjection : Carrier HL HR →ₗ[ℂ] HL :=
  (LinearMap.fst ℂ HL HR).comp pairCoordinates.symm.toLinearMap

def rightProjection : Carrier HL HR →ₗ[ℂ] HR :=
  (LinearMap.snd ℂ HL HR).comp pairCoordinates.symm.toLinearMap

@[simp] theorem leftInclusion_apply (x : HL) :
    WithLp.ofLp (leftInclusion (HR := HR) x) = (x, 0) := rfl

@[simp] theorem rightInclusion_apply (y : HR) :
    WithLp.ofLp (rightInclusion (HL := HL) y) = (0, y) := rfl

@[simp] theorem leftProjection_apply (x : Carrier HL HR) :
    leftProjection x = (WithLp.ofLp x).1 := rfl

@[simp] theorem rightProjection_apply (x : Carrier HL HR) :
    rightProjection x = (WithLp.ofLp x).2 := rfl

def blocks (A : Module.End ℂ HL) (B : Module.End ℂ HR) :
    Module.End ℂ (Carrier HL HR) :=
  pairCoordinates.conjAlgEquiv ℂ (LinearMap.prodMap A B)

@[simp] theorem blocks_apply (A : Module.End ℂ HL) (B : Module.End ℂ HR)
    (x : Carrier HL HR) : WithLp.ofLp (blocks A B x) =
      (A (WithLp.ofLp x).1, B (WithLp.ofLp x).2) := rfl

def pairUnitary (N : ℕ) (UL : HL ≃ₗᵢ[ℂ] SectorSpace N)
    (UR : HR ≃ₗᵢ[ℂ] SectorSpace N) : Carrier HL HR ≃ₗᵢ[ℂ] Space N :=
  (LinearIsometryEquiv.withLpProdCongr 2 UL UR).trans (sectorCoordinates N).symm

@[simp] theorem pairUnitary_coordinates (N : ℕ)
    (UL : HL ≃ₗᵢ[ℂ] SectorSpace N) (UR : HR ≃ₗᵢ[ℂ] SectorSpace N)
    (x : Carrier HL HR) :
    WithLp.ofLp (sectorCoordinates N (pairUnitary N UL UR x)) =
      (UL (WithLp.ofLp x).1, UR (WithLp.ofLp x).2) := by
  simp [pairUnitary]

theorem pairUnitary_intertwines (N : ℕ)
    (ρL : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HL)
    (ρR : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HR)
    (UL : HL ≃ₗᵢ[ℂ] SectorSpace N) (UR : HR ≃ₗᵢ[ℂ] SectorSpace N)
    (hUL : ∀ A x, UL (ρL A x) = representation N A (UL x))
    (hUR : ∀ A x, UR (ρR A x) = representation N A (UR x))
    (A B : SectorAlgebra N) (x : Carrier HL HR) :
    pairUnitary N UL UR (blocks (ρL A) (ρR B) x) =
      HistoryChiralBlocks.diagonalBlocks N (representation N A) (representation N B)
        (pairUnitary N UL UR x) := by
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  simp only [pairUnitary_coordinates, blocks_apply, HistoryChiralBlocks.diagonalBlocks_apply]
  exact Prod.ext (hUL A _) (hUR B _)

theorem pairUnitary_projections (N : ℕ)
    (UL : HL ≃ₗᵢ[ℂ] SectorSpace N) (UR : HR ≃ₗᵢ[ℂ] SectorSpace N)
    (x : Carrier HL HR) :
    pairUnitary N UL UR (blocks 1 0 x) = action N (positiveProjection N) (pairUnitary N UL UR x) ∧
    pairUnitary N UL UR (blocks 0 1 x) = action N (negativeProjection N) (pairUnitary N UL UR x) := by
  constructor <;> apply (sectorCoordinates N).injective <;>
    apply WithLp.ofLp_injective 2 <;>
    simp [pairUnitary_coordinates, blocks_apply, sectorCoordinates_positiveProjection,
      sectorCoordinates_negativeProjection]

theorem pairUnitary_leftInclusion (N : ℕ)
    (UL : HL ≃ₗᵢ[ℂ] SectorSpace N) (UR : HR ≃ₗᵢ[ℂ] SectorSpace N) (x : HL) :
    pairUnitary N UL UR (leftInclusion x) = HistoryComplexConnector.positiveInclusion N (UL x) := by
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  simp only [pairUnitary_coordinates, leftInclusion_apply, map_zero]
  rfl

theorem pairUnitary_rightInclusion (N : ℕ)
    (UL : HL ≃ₗᵢ[ℂ] SectorSpace N) (UR : HR ≃ₗᵢ[ℂ] SectorSpace N) (y : HR) :
    pairUnitary N UL UR (rightInclusion y) = HistoryComplexConnector.negativeInclusion N (UR y) := by
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  simp only [pairUnitary_coordinates, rightInclusion_apply, map_zero]
  rfl

theorem pairUnitary_leftProjection (N : ℕ)
    (UL : HL ≃ₗᵢ[ℂ] SectorSpace N) (UR : HR ≃ₗᵢ[ℂ] SectorSpace N) (x : Carrier HL HR) :
    (WithLp.ofLp (sectorCoordinates N (pairUnitary N UL UR x))).1 = UL (leftProjection x) :=
  congrArg Prod.fst (pairUnitary_coordinates N UL UR x)

theorem pairUnitary_rightProjection (N : ℕ)
    (UL : HL ≃ₗᵢ[ℂ] SectorSpace N) (UR : HR ≃ₗᵢ[ℂ] SectorSpace N) (x : Carrier HL HR) :
    (WithLp.ofLp (sectorCoordinates N (pairUnitary N UL UR x))).2 = UR (rightProjection x) :=
  congrArg Prod.snd (pairUnitary_coordinates N UL UR x)

theorem pairUnitary_grading (N : ℕ)
    (UL : HL ≃ₗᵢ[ℂ] SectorSpace N) (UR : HR ≃ₗᵢ[ℂ] SectorSpace N)
    (x : Carrier HL HR) :
    pairUnitary N UL UR (blocks 1 (-1) x) =
      action N (sourceGrading N) (pairUnitary N UL UR x) := by
  rw [HistoryChiralBlocks.grading_eq]
  apply (sectorCoordinates N).injective
  apply WithLp.ofLp_injective 2
  simp [pairUnitary_coordinates, blocks_apply, HistoryChiralBlocks.diagonalBlocks_apply]

def responseTransport (N : ℕ) (U : Carrier HL HR ≃ₗᵢ[ℂ] Space N) :
    Module.End ℂ (Space N) ≃ₐ[ℂ] Module.End ℂ (Carrier HL HR) :=
  U.toLinearEquiv.symm.conjAlgEquiv ℂ

theorem responseTransport_intertwines (N : ℕ) (U : Carrier HL HR ≃ₗᵢ[ℂ] Space N)
    (T : Module.End ℂ (Space N)) (x : Carrier HL HR) :
    U (responseTransport N U T x) = T (U x) := by
  simp [responseTransport, LinearEquiv.conjAlgEquiv_apply]

theorem responseTransport_existsUnique (N : ℕ) (U : Carrier HL HR ≃ₗᵢ[ℂ] Space N)
    (T : Module.End ℂ (Space N)) :
    ∃! A : Module.End ℂ (Carrier HL HR), ∀ x, U (A x) = T (U x) := by
  refine ⟨responseTransport N U T, responseTransport_intertwines N U T, ?_⟩
  intro A hA
  apply LinearMap.ext
  intro x
  apply U.injective
  exact (hA x).trans (responseTransport_intertwines N U T x).symm

end Coordinates

theorem least_pair_classification (N : ℕ)
    (ρL : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HL)
    (ρR : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HR)
    (hL : IsLeast N ρL) (hR : IsLeast N ρR) :
    ∃ U : Carrier HL HR ≃ₗᵢ[ℂ] Space N,
      (∀ A B x, U (blocks (ρL A) (ρR B) x) =
        HistoryChiralBlocks.diagonalBlocks N (representation N A) (representation N B) (U x)) ∧
      (∀ x, U (blocks 1 0 x) = action N (positiveProjection N) (U x)) ∧
      (∀ x, U (blocks 0 1 x) = action N (negativeProjection N) (U x)) ∧
      (∀ x, U (blocks 1 (-1) x) = action N (sourceGrading N) (U x)) := by
  obtain ⟨UL, hUL⟩ := least_unitarilyEquivalent N ρL hL
  obtain ⟨UR, hUR⟩ := least_unitarilyEquivalent N ρR hR
  refine ⟨pairUnitary N UL UR, pairUnitary_intertwines N ρL ρR UL UR hUL hUR,
    fun x => (pairUnitary_projections N UL UR x).1,
    fun x => (pairUnitary_projections N UL UR x).2, pairUnitary_grading N UL UR⟩

theorem least_pair_finrank (N : ℕ)
    (ρL : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HL)
    (ρR : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HR)
    (hL : IsLeast N ρL) (hR : IsLeast N ρR) :
    Module.finrank ℂ (Carrier HL HR) = 4 * Fintype.card (HistoryLabel N) := by
  rw [(WithLp.linearEquiv 2 ℂ (HL × HR)).finrank_eq, Module.finrank_prod,
    hL.2.2, hR.2.2]
  simp [SectorIndex, Fintype.card_prod]
  omega

/-- The dimension and all labelled comparisons use the same realizing
unitary. The dimension is the actual arithmetic label count. -/
theorem least_pair_sourceInterface (N : ℕ)
    (ρL : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HL)
    (ρR : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HR)
    (hL : IsLeast N ρL) (hR : IsLeast N ρR) :
    Module.finrank ℂ (Carrier HL HR) = 4 * Fintype.card (HistoryLabel N) ∧
      ∃ U : Carrier HL HR ≃ₗᵢ[ℂ] Space N,
        (∀ A B x, U (blocks (ρL A) (ρR B) x) =
          HistoryChiralBlocks.diagonalBlocks N (representation N A) (representation N B) (U x)) ∧
        (∀ x, U (blocks 1 0 x) = action N (positiveProjection N) (U x)) ∧
        (∀ x, U (blocks 0 1 x) = action N (negativeProjection N) (U x)) ∧
        (∀ x, U (blocks 1 (-1) x) = action N (sourceGrading N) (U x)) :=
  ⟨least_pair_finrank N ρL ρR hL hR, least_pair_classification N ρL ρR hL hR⟩

/-- The single comparison unitary also determines the compatible transport
of every further operator, including the off-diagonal responses. -/
theorem least_pair_compatible_response (N : ℕ)
    (ρL : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HL)
    (ρR : SectorAlgebra N →ₐ[ℂ] Module.End ℂ HR)
    (hL : IsLeast N ρL) (hR : IsLeast N ρR) :
    ∃ U : Carrier HL HR ≃ₗᵢ[ℂ] Space N,
      (∀ A B x, U (blocks (ρL A) (ρR B) x) =
        HistoryChiralBlocks.diagonalBlocks N (representation N A) (representation N B) (U x)) ∧
      (∀ x, U (blocks 1 0 x) = action N (positiveProjection N) (U x)) ∧
      (∀ x, U (blocks 0 1 x) = action N (negativeProjection N) (U x)) ∧
      (∀ x, U (blocks 1 (-1) x) = action N (sourceGrading N) (U x)) ∧
      (∀ T : Module.End ℂ (Space N),
        ∃! A : Module.End ℂ (Carrier HL HR), ∀ x, U (A x) = T (U x)) := by
  obtain ⟨U, hU, hL', hR', hG⟩ := least_pair_classification N ρL ρR hL hR
  exact ⟨U, hU, hL', hR', hG, responseTransport_existsUnique N U⟩

end GeneratedFoundations.Arithmetic.HistoryPairedRealization
