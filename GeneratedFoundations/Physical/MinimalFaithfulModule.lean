module

public import GeneratedFoundations.Operations.MatrixBlockRepresentations
public import GeneratedFoundations.Physical.MatrixModuleClassification

/-! Compatibility names for the common matrix-block classification, followed
    by its physical two-block instance. The general proof is upstream. -/

@[expose] public section

namespace GeneratedFoundations.Physical.MinimalFaithfulModule

open scoped BigOperators

export GeneratedFoundations.Operations.MatrixBlockRepresentations (
  BlockAlgebra
  Representation
  algebraUnit
  matrixUnit
  algebraUnit_mul_same
  algebraUnit_mul_ne
  algebraUnit_mul_other
  matrixUnit_comp_same
  matrixUnit_comp_ne
  matrixUnit_comp_other
  sum_algebraUnits
  sum_matrixUnits
  multiplicitySpace
  diagonal_fixes_multiplicity
  coordinate
  toCoordinates
  reconstruct
  reconstruct_toCoordinates
  toCoordinates_reconstruct
  multiplicityEquiv
  algebraUnit_mul_eq_row
  coordinate_intertwines
  standardRepresentation
  standardRepresentation_injective
  standardRepresentation_finrank
  finrank_eq_sum_multiplicities
  faithful_multiplicity_pos
  faithful_finrank_lowerBound
  minimal_finrank_iff_multiplicities_one
  blockAdjoint
  StarCompatible
  StandardHilbert
  standardHilbertCoordinates
  standardHilbertRepresentation
  standardHilbertRepresentation_apply
  standardHilbertRepresentation_injective
  standardHilbertRepresentation_finrank
  standardHilbertRepresentation_starCompatible
  blockAdjoint_algebraUnit
  matrixUnit_inner
  CoordinatesL2
  coordinatesL2Equiv
  coordinatesL2_inner
  multiplicityUnitary
  multiplicityUnitary_intertwines
  transportUnitary
  transportUnitary_coordinates
  transportUnitary_intertwines
  minimalFaithfulJointRep_unique
)

section JointResponse

def jointBlockSizes : Bool → ℕ
  | true => 6
  | false => 2

abbrev JointAlgebra :=
  Matrix (Fin 6) (Fin 6) ℂ × Matrix (Fin 2) (Fin 2) ℂ

/-- The two-block family notation and the direct-product notation for the
six-dimensional and two-dimensional matrix blocks. -/
def jointAlgebraEquiv : BlockAlgebra (K := ℂ) jointBlockSizes ≃ₐ[ℂ] JointAlgebra where
  toFun a := (a true, a false)
  invFun a := fun b => match b with
    | true => a.1
    | false => a.2
  left_inv a := by
    funext b
    cases b <;> rfl
  right_inv a := rfl
  map_mul' a b := rfl
  map_add' a b := rfl
  commutes' r := rfl

def jointBase (b : Bool) : Fin (jointBlockSizes b) :=
  ⟨0, by cases b <;> decide⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

abbrev JointRepresentation := JointAlgebra →ₐ[ℂ] Module.End ℂ H

noncomputable def jointBlockRepresentation (ρ : JointRepresentation (H := H)) :
    Representation (K := ℂ) (V := H) jointBlockSizes :=
  ρ.comp jointAlgebraEquiv.toAlgHom

def JointStarCompatible (ρ : JointRepresentation (H := H)) : Prop :=
  ∀ a x y, inner ℂ (ρ a x) y =
    inner ℂ x (ρ (a.1.conjTranspose, a.2.conjTranspose) y)

theorem jointAlgebraEquiv_symm_adjoint (a : JointAlgebra) :
    blockAdjoint jointBlockSizes (jointAlgebraEquiv.symm a) =
      jointAlgebraEquiv.symm (a.1.conjTranspose, a.2.conjTranspose) := by
  funext b
  cases b <;> rfl

noncomputable def standardJointRepresentation :
    JointRepresentation (H := StandardHilbert jointBlockSizes) :=
  (standardHilbertRepresentation jointBlockSizes).comp jointAlgebraEquiv.symm.toAlgHom

theorem standardJointRepresentation_injective :
    Function.Injective standardJointRepresentation :=
  (standardHilbertRepresentation_injective jointBlockSizes).comp jointAlgebraEquiv.symm.injective

theorem standardJointRepresentation_starCompatible :
    JointStarCompatible standardJointRepresentation := by
  intro a x y
  change inner ℂ (standardHilbertRepresentation jointBlockSizes (jointAlgebraEquiv.symm a) x) y =
    inner ℂ x (standardHilbertRepresentation jointBlockSizes
      (jointAlgebraEquiv.symm (a.1.conjTranspose, a.2.conjTranspose)) y)
  rw [← jointAlgebraEquiv_symm_adjoint]
  exact standardHilbertRepresentation_starCompatible jointBlockSizes (jointAlgebraEquiv.symm a) x y

theorem standardJointRepresentation_finrank :
    Module.finrank ℂ (StandardHilbert jointBlockSizes) = 8 := by
  simpa [jointBlockSizes] using standardHilbertRepresentation_finrank jointBlockSizes

omit [FiniteDimensional ℂ H] in
theorem jointBlockRepresentation_starCompatible
    (ρ : JointRepresentation (H := H)) (hρ : JointStarCompatible ρ) :
    StarCompatible jointBlockSizes (jointBlockRepresentation ρ) := by
  intro a x y
  exact hρ (jointAlgebraEquiv a) x y

theorem faithfulJointRep_finrank_ge_eight
    (ρ : JointRepresentation (H := H)) (hρ : Function.Injective ρ) :
    8 ≤ Module.finrank ℂ H := by
  have h := faithful_finrank_lowerBound jointBlockSizes (jointBlockRepresentation ρ)
    (hρ.comp jointAlgebraEquiv.injective) jointBase
  simpa [jointBlockSizes] using h

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [FiniteDimensional ℂ H']

/-- Every two faithful adjoint-preserving eight-dimensional realizations
of the joint response algebra are unitarily equivalent. -/
theorem minimalEightDimensionalJointRep_unique
    (ρ : JointRepresentation (H := H)) (hρ : JointStarCompatible ρ)
    (hρinj : Function.Injective ρ)
    (σ : JointRepresentation (H := H')) (hσ : JointStarCompatible σ)
    (hσinj : Function.Injective σ)
    (hdimρ : Module.finrank ℂ H = 8) (hdimσ : Module.finrank ℂ H' = 8) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ a x, U (ρ a x) = σ a (U x) := by
  have hminρ : Module.finrank ℂ H = ∑ b, jointBlockSizes b := by
    simpa [jointBlockSizes] using hdimρ
  have hminσ : Module.finrank ℂ H' = ∑ b, jointBlockSizes b := by
    simpa [jointBlockSizes] using hdimσ
  obtain ⟨U, hU⟩ := minimalFaithfulJointRep_unique jointBlockSizes
    (jointBlockRepresentation ρ) (jointBlockRepresentation_starCompatible ρ hρ)
    (hρinj.comp jointAlgebraEquiv.injective)
    (jointBlockRepresentation σ) (jointBlockRepresentation_starCompatible σ hσ)
    (hσinj.comp jointAlgebraEquiv.injective) jointBase hminρ hminσ
  refine ⟨U, ?_⟩
  intro a x
  simpa [jointBlockRepresentation] using hU (jointAlgebraEquiv.symm a) x

/-- Least dimension among faithful adjoint-preserving representations on
finite-dimensional complex Hilbert spaces. -/
def IsLeastFaithfulJointRepresentation (ρ : JointRepresentation (H := H)) : Prop :=
  Function.Injective ρ ∧ JointStarCompatible ρ ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      (σ : JointRepresentation (H := E)),
      Function.Injective σ → JointStarCompatible σ →
        Module.finrank ℂ H ≤ Module.finrank ℂ E

theorem standardJointRepresentation_isLeast :
    IsLeastFaithfulJointRepresentation standardJointRepresentation := by
  refine ⟨standardJointRepresentation_injective, standardJointRepresentation_starCompatible, ?_⟩
  intro E _ _ _ σ hσ _
  rw [standardJointRepresentation_finrank]
  exact faithfulJointRep_finrank_ge_eight σ hσ

theorem leastFaithfulJointRep_finrank_eight
    (ρ : JointRepresentation (H := H)) (hρ : IsLeastFaithfulJointRepresentation ρ) :
    Module.finrank ℂ H = 8 := by
  have hle := hρ.2.2 (StandardHilbert jointBlockSizes) standardJointRepresentation
    standardJointRepresentation_injective standardJointRepresentation_starCompatible
  rw [standardJointRepresentation_finrank] at hle
  exact Nat.le_antisymm hle (faithfulJointRep_finrank_ge_eight ρ hρ.1)

theorem leastFaithfulJointRep_unitarilyEquivalentToStandard
    (ρ : JointRepresentation (H := H)) (hρ : IsLeastFaithfulJointRepresentation ρ) :
    ∃ U : H ≃ₗᵢ[ℂ] StandardHilbert jointBlockSizes,
      ∀ a x, U (ρ a x) = standardJointRepresentation a (U x) :=
  minimalEightDimensionalJointRep_unique ρ hρ.2.1 hρ.1
    standardJointRepresentation standardJointRepresentation_starCompatible
    standardJointRepresentation_injective (leastFaithfulJointRep_finrank_eight ρ hρ)
    standardJointRepresentation_finrank

theorem leastFaithfulJointRep_unique
    (ρ : JointRepresentation (H := H)) (hρ : IsLeastFaithfulJointRepresentation ρ)
    (σ : JointRepresentation (H := H')) (hσ : IsLeastFaithfulJointRepresentation σ) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ a x, U (ρ a x) = σ a (U x) :=
  minimalEightDimensionalJointRep_unique ρ hρ.2.1 hρ.1 σ hσ.2.1 hσ.1
    (leastFaithfulJointRep_finrank_eight ρ hρ) (leastFaithfulJointRep_finrank_eight σ hσ)

theorem pairedFaithfulJointRep_finrank_ge_sixteen
    (ρ : JointRepresentation (H := H)) (hρ : Function.Injective ρ)
    (σ : JointRepresentation (H := H')) (hσ : Function.Injective σ) :
    16 ≤ Module.finrank ℂ (H × H') := by
  rw [Module.finrank_prod]
  have hleft := faithfulJointRep_finrank_ge_eight ρ hρ
  have hright := faithfulJointRep_finrank_ge_eight σ hσ
  omega

/-- The full left-right carrier retains both eight-dimensional modules.
No quotient by a neutral charge line is taken in this dimension count. -/
theorem pairedMinimalJointRep_finrank_sixteen
    (hdimρ : Module.finrank ℂ H = 8) (hdimσ : Module.finrank ℂ H' = 8) :
    Module.finrank ℂ (H × H') = 16 := by
  rw [Module.finrank_prod, hdimρ, hdimσ]

theorem pairedLeastFaithfulJointRep_finrank_sixteen
    (ρ : JointRepresentation (H := H)) (hρ : IsLeastFaithfulJointRepresentation ρ)
    (σ : JointRepresentation (H := H')) (hσ : IsLeastFaithfulJointRepresentation σ) :
    Module.finrank ℂ (H × H') = 16 :=
  pairedMinimalJointRep_finrank_sixteen
    (leastFaithfulJointRep_finrank_eight ρ hρ) (leastFaithfulJointRep_finrank_eight σ hσ)

end JointResponse

end GeneratedFoundations.Physical.MinimalFaithfulModule
