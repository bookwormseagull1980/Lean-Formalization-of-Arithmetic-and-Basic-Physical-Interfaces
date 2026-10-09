module

public import GeneratedFoundations.Physical.SourceChiralCarrier

/-!
# Least faithful realizations of the two source chiral sectors

The source sectors and their primitive central projections are constructed
in `SourceCliffordChirality`. This module compares arbitrary least faithful
adjoint-compatible Hilbert representations of the generated joint response
algebra on the two corresponding labelled sectors.
Their orthogonal sum is transported to the actual source matter carrier
by the product of the two unitary intertwiners.

One and the same unitary intertwines independent left and right algebra
actions, preserves both labelled subspaces and the grading, and identifies
the sixteen-dimensional sum with `SourceChiralCarrier.FullMatter`.
The separate Clifford construction supplies the two sectors; their existence
is not inferred from the minimality of a single representation. Once the
unitary is fixed, conjugation gives the unique compatible transport of every
source operator. The unitary itself need not be unique. No bundle or local
frame existence statement is made here.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceMinimalChiralPair

open SourceJointResponse SourceMinimalRepresentation
open SourceChiralCarrier (FullMatter)

variable {HL HR : Type*}
  [NormedAddCommGroup HL] [InnerProductSpace ℂ HL]
  [NormedAddCommGroup HR] [InnerProductSpace ℂ HR]

abbrev Carrier (HL HR : Type*) := WithLp 2 (HL × HR)

def pairCoordinates : (HL × HR) ≃ₗ[ℂ] Carrier HL HR :=
  (WithLp.linearEquiv 2 ℂ (HL × HR)).symm

def leftInclusion : HL →ₗ[ℂ] Carrier HL HR :=
  pairCoordinates.toLinearMap.comp (LinearMap.inl ℂ HL HR)

def rightInclusion : HR →ₗ[ℂ] Carrier HL HR :=
  pairCoordinates.toLinearMap.comp (LinearMap.inr ℂ HL HR)

/-- The operators on the two supplied carriers remain independent. -/
def diagonalBlocks (A : Module.End ℂ HL) (B : Module.End ℂ HR) :
    Module.End ℂ (Carrier HL HR) :=
  pairCoordinates.conjAlgEquiv ℂ (LinearMap.prodMap A B)

@[simp] theorem diagonalBlocks_apply (A : Module.End ℂ HL) (B : Module.End ℂ HR)
    (x : Carrier HL HR) :
    WithLp.ofLp (diagonalBlocks A B x) =
      (A (WithLp.ofLp x).1, B (WithLp.ofLp x).2) := rfl

def leftProjection : Module.End ℂ (Carrier HL HR) := diagonalBlocks 1 0

def rightProjection : Module.End ℂ (Carrier HL HR) := diagonalBlocks 0 1

def grading : Module.End ℂ (Carrier HL HR) := diagonalBlocks 1 (-1)

/-- This is the actual Hilbert direct-sum unitary, not a dimension argument. -/
def pairUnitary (UL : HL ≃ₗᵢ[ℂ] SourceCarrier) (UR : HR ≃ₗᵢ[ℂ] SourceCarrier) :
    Carrier HL HR ≃ₗᵢ[ℂ] FullMatter :=
  LinearIsometryEquiv.withLpProdCongr 2 UL UR

@[simp] theorem pairUnitary_apply
    (UL : HL ≃ₗᵢ[ℂ] SourceCarrier) (UR : HR ≃ₗᵢ[ℂ] SourceCarrier)
    (x : Carrier HL HR) :
    WithLp.ofLp (pairUnitary UL UR x) =
      (UL (WithLp.ofLp x).1, UR (WithLp.ofLp x).2) := rfl

theorem pairUnitary_leftInclusion
    (UL : HL ≃ₗᵢ[ℂ] SourceCarrier) (UR : HR ≃ₗᵢ[ℂ] SourceCarrier) (x : HL) :
    pairUnitary UL UR (leftInclusion x) = SourceChiralCarrier.leftInclusion (UL x) := by
  apply WithLp.ofLp_injective 2
  change (UL x, UR 0) = (UL x, 0)
  rw [map_zero]

theorem pairUnitary_rightInclusion
    (UL : HL ≃ₗᵢ[ℂ] SourceCarrier) (UR : HR ≃ₗᵢ[ℂ] SourceCarrier) (x : HR) :
    pairUnitary UL UR (rightInclusion x) = SourceChiralCarrier.rightInclusion (UR x) := by
  apply WithLp.ofLp_injective 2
  change (UL 0, UR x) = (0, UR x)
  rw [map_zero]

theorem pairUnitary_leftProjection
    (UL : HL ≃ₗᵢ[ℂ] SourceCarrier) (UR : HR ≃ₗᵢ[ℂ] SourceCarrier)
    (x : Carrier HL HR) :
    pairUnitary UL UR (leftProjection x) =
      SourceChiralCarrier.leftProjection (pairUnitary UL UR x) := by
  apply WithLp.ofLp_injective 2
  change (UL (WithLp.ofLp x).1, UR 0) = (UL (WithLp.ofLp x).1, 0)
  rw [map_zero]

theorem pairUnitary_rightProjection
    (UL : HL ≃ₗᵢ[ℂ] SourceCarrier) (UR : HR ≃ₗᵢ[ℂ] SourceCarrier)
    (x : Carrier HL HR) :
    pairUnitary UL UR (rightProjection x) =
      SourceChiralCarrier.rightProjection (pairUnitary UL UR x) := by
  apply WithLp.ofLp_injective 2
  change (UL 0, UR (WithLp.ofLp x).2) = (0, UR (WithLp.ofLp x).2)
  rw [map_zero]

theorem pairUnitary_grading
    (UL : HL ≃ₗᵢ[ℂ] SourceCarrier) (UR : HR ≃ₗᵢ[ℂ] SourceCarrier)
    (x : Carrier HL HR) :
    pairUnitary UL UR (grading x) = SourceChiralCarrier.grading (pairUnitary UL UR x) := by
  apply WithLp.ofLp_injective 2
  change (UL (WithLp.ofLp x).1, UR (-(WithLp.ofLp x).2)) =
    (UL (WithLp.ofLp x).1, -(UR (WithLp.ofLp x).2))
  rw [map_neg]

/-- The same product unitary intertwines independent source operators in
the two labelled representations. -/
theorem pairUnitary_intertwines
    (ρL : JointEnd →ₐ[ℂ] Module.End ℂ HL)
    (ρR : JointEnd →ₐ[ℂ] Module.End ℂ HR)
    (UL : HL ≃ₗᵢ[ℂ] SourceCarrier) (UR : HR ≃ₗᵢ[ℂ] SourceCarrier)
    (hUL : ∀ A x, UL (ρL A x) = sourceCarrierRepresentation A (UL x))
    (hUR : ∀ A x, UR (ρR A x) = sourceCarrierRepresentation A (UR x))
    (A B : JointEnd) (x : Carrier HL HR) :
    pairUnitary UL UR (diagonalBlocks (ρL A) (ρR B) x) =
      SourceChiralCarrier.diagonalBlocks (sourceCarrierRepresentation A)
        (sourceCarrierRepresentation B) (pairUnitary UL UR x) := by
  apply WithLp.ofLp_injective 2
  change (UL (ρL A (WithLp.ofLp x).1), UR (ρR B (WithLp.ofLp x).2)) =
    (sourceCarrierRepresentation A (UL (WithLp.ofLp x).1),
      sourceCarrierRepresentation B (UR (WithLp.ofLp x).2))
  exact Prod.ext (hUL A (WithLp.ofLp x).1) (hUR B (WithLp.ofLp x).2)

/-- Once a realizing unitary is fixed, every source operator has a unique
compatible action on that realization. The unitary itself need not be unique. -/
def responseTransport (U : Carrier HL HR ≃ₗᵢ[ℂ] FullMatter) :
    Module.End ℂ FullMatter ≃ₐ[ℂ] Module.End ℂ (Carrier HL HR) :=
  U.toLinearEquiv.symm.conjAlgEquiv ℂ

theorem responseTransport_intertwines (U : Carrier HL HR ≃ₗᵢ[ℂ] FullMatter)
    (T : Module.End ℂ FullMatter) (x : Carrier HL HR) :
    U (responseTransport U T x) = T (U x) := by
  simp [responseTransport, LinearEquiv.conjAlgEquiv_apply]

theorem responseTransport_existsUnique (U : Carrier HL HR ≃ₗᵢ[ℂ] FullMatter)
    (T : Module.End ℂ FullMatter) :
    ∃! A : Module.End ℂ (Carrier HL HR), ∀ x, U (A x) = T (U x) := by
  refine ⟨responseTransport U T, responseTransport_intertwines U T, ?_⟩
  intro A hA
  apply LinearMap.ext
  intro x
  apply U.injective
  exact (hA x).trans (responseTransport_intertwines U T x).symm

variable [FiniteDimensional ℂ HL] [FiniteDimensional ℂ HR]

theorem least_pair_finrank
    (ρL : JointEnd →ₐ[ℂ] Module.End ℂ HL)
    (ρR : JointEnd →ₐ[ℂ] Module.End ℂ HR)
    (hL : IsLeastFaithfulRepresentation ρL) (hR : IsLeastFaithfulRepresentation ρR) :
    Module.finrank ℂ (Carrier HL HR) = 16 := by
  exact (pairCoordinates (HL := HL) (HR := HR)).finrank_eq.symm.trans
    ((Module.finrank_prod (R := ℂ) (M := HL) (M' := HR)).trans
      (congrArg₂ Nat.add (least_finrank_eight ρL hL) (least_finrank_eight ρR hR)))

/-- Interface for two specified least faithful chiral realizations. Every
conclusion uses the single unitary displayed by the existential quantifier. -/
theorem least_pair_sourceInterface
    (ρL : JointEnd →ₐ[ℂ] Module.End ℂ HL)
    (ρR : JointEnd →ₐ[ℂ] Module.End ℂ HR)
    (hL : IsLeastFaithfulRepresentation ρL) (hR : IsLeastFaithfulRepresentation ρR) :
    Module.finrank ℂ (Carrier HL HR) = 16 ∧
      ∃ U : Carrier HL HR ≃ₗᵢ[ℂ] FullMatter,
        (∀ A B x, U (diagonalBlocks (ρL A) (ρR B) x) =
          SourceChiralCarrier.diagonalBlocks (sourceCarrierRepresentation A)
            (sourceCarrierRepresentation B) (U x)) ∧
        (∀ x, U (leftProjection x) = SourceChiralCarrier.leftProjection (U x)) ∧
        (∀ x, U (rightProjection x) = SourceChiralCarrier.rightProjection (U x)) ∧
        (∀ x, U (grading x) = SourceChiralCarrier.grading (U x)) := by
  have hleft : ∃ U : HL ≃ₗᵢ[ℂ] SourceCarrier,
      ∀ (A : JointEnd) (x : HL), U (ρL A x) = sourceCarrierRepresentation A (U x) :=
    least_unitarilyEquivalentToSource (H := HL) ρL hL
  have hright : ∃ U : HR ≃ₗᵢ[ℂ] SourceCarrier,
      ∀ (A : JointEnd) (x : HR), U (ρR A x) = sourceCarrierRepresentation A (U x) :=
    least_unitarilyEquivalentToSource (H := HR) ρR hR
  obtain ⟨UL, hUL⟩ := hleft
  obtain ⟨UR, hUR⟩ := hright
  refine ⟨least_pair_finrank ρL ρR hL hR, pairUnitary UL UR, ?_, ?_, ?_, ?_⟩
  · intro A B x
    exact pairUnitary_intertwines ρL ρR UL UR hUL hUR A B x
  · intro x
    exact pairUnitary_leftProjection UL UR x
  · intro x
    exact pairUnitary_rightProjection UL UR x
  · intro x
    exact pairUnitary_grading UL UR x

/-- The same realizing unitary handles the independent retained responses,
both generated-sector labels, and every further operator on the full carrier.
This is uniqueness of compatible transport, not a claim that arbitrary
extensions of the generated algebra must be least faithful. -/
theorem least_pair_compatible_response
    (ρL : JointEnd →ₐ[ℂ] Module.End ℂ HL)
    (ρR : JointEnd →ₐ[ℂ] Module.End ℂ HR)
    (hL : IsLeastFaithfulRepresentation ρL) (hR : IsLeastFaithfulRepresentation ρR) :
    ∃ U : Carrier HL HR ≃ₗᵢ[ℂ] FullMatter,
      (∀ A B x, U (diagonalBlocks (ρL A) (ρR B) x) =
        SourceChiralCarrier.diagonalBlocks (sourceCarrierRepresentation A)
          (sourceCarrierRepresentation B) (U x)) ∧
      (∀ x, U (leftProjection x) = SourceChiralCarrier.leftProjection (U x)) ∧
      (∀ x, U (rightProjection x) = SourceChiralCarrier.rightProjection (U x)) ∧
      (∀ x, U (grading x) = SourceChiralCarrier.grading (U x)) ∧
      (∀ T : Module.End ℂ FullMatter,
        ∃! A : Module.End ℂ (Carrier HL HR), ∀ x, U (A x) = T (U x)) := by
  have hleft : ∃ U : HL ≃ₗᵢ[ℂ] SourceCarrier,
      ∀ (A : JointEnd) (x : HL), U (ρL A x) = sourceCarrierRepresentation A (U x) :=
    least_unitarilyEquivalentToSource (H := HL) ρL hL
  have hright : ∃ U : HR ≃ₗᵢ[ℂ] SourceCarrier,
      ∀ (A : JointEnd) (x : HR), U (ρR A x) = sourceCarrierRepresentation A (U x) :=
    least_unitarilyEquivalentToSource (H := HR) ρR hR
  obtain ⟨UL, hUL⟩ := hleft
  obtain ⟨UR, hUR⟩ := hright
  refine ⟨pairUnitary UL UR, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B x
    exact pairUnitary_intertwines ρL ρR UL UR hUL hUR A B x
  · intro x
    exact pairUnitary_leftProjection UL UR x
  · intro x
    exact pairUnitary_rightProjection UL UR x
  · intro x
    exact pairUnitary_grading UL UR x
  · exact responseTransport_existsUnique (pairUnitary UL UR)

end GeneratedFoundations.Physical.SourceMinimalChiralPair
