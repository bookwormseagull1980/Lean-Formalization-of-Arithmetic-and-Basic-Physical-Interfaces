module

public import GeneratedFoundations.Physical.SourceQuadraticResponse
public import GeneratedFoundations.Physical.MinimalFaithfulModule
public import GeneratedFoundations.Geometry.SourceJointResponse
public import GeneratedFoundations.Geometry.SourceQuadraticSplit
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Algebra.Prod

/-! Physical compatibility for the common source algebra and its actual
Haar carriers. The remaining classification uses the physical two-block
realization; the common response construction is imported upstream. -/

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricUnitary

namespace GeneratedFoundations.Physical.SourceJointResponse

export GeneratedFoundations.Geometry.SourceJointResponse (
  Coloured
  JointEnd
  L
  S
  Scalar
  SplitColour
  W
  alternatingSourceUnitary
  alternatingSourceUnitary_intertwines
  colourResponse
  colourResponse_mem
  colour_spin_commute
  colour_spin_product
  colouredBasis
  colouredInner
  colouredNormed
  coloured_end_mem
  coloured_finrank
  coloured_tensor_mem
  containing_quadratic_source_eq_top
  containing_spin_source_eq_top
  quadratic_sourceAlgebra_eq_top
  responseAlgebra
  responseAlgebra_eq_top
  scalarBasis
  scalarInner
  scalarNormed
  scalar_end_mem
  scalar_finrank
  scalar_tensor_mem
  sourceOperator
  sourceOperator_apply
  sourceOperator_eq_unitary
  spinResponse
  spinResponse_mem
  spinSource_mem
  spin_sourceAlgebra_eq_top
  symmetricSourceUnitary
  symmetricSourceUnitary_intertwines
)

/-- These are orthonormal coordinates of the actual tensor Hilbert spaces,
not the non-normalized polynomial monomial coordinates. -/
def matrixCoordinates : JointEnd ≃⋆ₐ[ℂ] MinimalFaithfulModule.JointAlgebra :=
  StarAlgEquiv.ofAlgEquiv
    (AlgEquiv.prodCongr
      (LinearMap.toMatrixOrthonormal colouredBasis).toAlgEquiv
      (LinearMap.toMatrixOrthonormal scalarBasis).toAlgEquiv) (by
        intro A
        apply Prod.ext
        · exact map_star (LinearMap.toMatrixOrthonormal colouredBasis) A.1
        · exact map_star (LinearMap.toMatrixOrthonormal scalarBasis) A.2)

theorem matrixCoordinates_symm_star (A : MinimalFaithfulModule.JointAlgebra) :
    matrixCoordinates.symm (star A) = star (matrixCoordinates.symm A) :=
  map_star matrixCoordinates.symm A

/-- The generated algebra has precisely the two claimed matrix blocks. -/
def generatedMatrixEquiv : responseAlgebra ≃ₐ[ℂ] MinimalFaithfulModule.JointAlgebra :=
  ((Subalgebra.equivOfEq responseAlgebra ⊤ responseAlgebra_eq_top).trans
    Subalgebra.topEquiv).trans matrixCoordinates.toAlgEquiv

/-- The two blocks act faithfully on the actual algebraic direct sum of
their source tensor carriers. -/
def carrierRepresentation : JointEnd →ₐ[ℂ] Module.End ℂ (Coloured × Scalar) :=
  LinearMap.prodMapAlgHom ℂ Coloured Scalar

theorem carrierRepresentation_injective : Function.Injective carrierRepresentation := by
  intro A B h
  apply Prod.ext
  · apply LinearMap.ext
    intro x
    exact congrArg (fun T : Module.End ℂ (Coloured × Scalar) => (T (x, 0)).1) h
  · apply LinearMap.ext
    intro x
    exact congrArg (fun T : Module.End ℂ (Coloured × Scalar) => (T (0, x)).2) h

/-- An endomorphism commuting with the complete joint response algebra is
scalar on each of its two simple carrier blocks.  Thus the least carrier is
unique more precisely than merely up to an unspecified intertwiner: the only
residual linear freedom is one scalar on the coloured block and one on the
scalar block. -/
theorem commutant_carrierRepresentation_is_blockScalar
    (T : Module.End ℂ (Coloured × Scalar))
    (hT : ∀ A x, T (carrierRepresentation A x) =
      carrierRepresentation A (T x)) :
    ∃ lambda mu : ℂ, ∀ x : Coloured × Scalar,
      T x = (lambda • x.1, mu • x.2) := by
  let Tc : Module.End ℂ Coloured :=
    { toFun := fun x => (T (x, 0)).1
      map_add' := by
        intro x y
        simpa using congrArg Prod.fst (T.map_add (x, 0) (y, 0))
      map_smul' := by
        intro c x
        simpa using congrArg Prod.fst (T.map_smul c (x, 0)) }
  let Ts : Module.End ℂ Scalar :=
    { toFun := fun x => (T (0, x)).2
      map_add' := by
        intro x y
        simpa using congrArg Prod.snd (T.map_add (0, x) (0, y))
      map_smul' := by
        intro c x
        simpa using congrArg Prod.snd (T.map_smul c (0, x)) }
  have hcoloured (x : Coloured) : T (x, 0) = (Tc x, 0) := by
    have h := hT (1, 0) (x, 0)
    simpa [carrierRepresentation, Tc] using h
  have hscalar (x : Scalar) : T (0, x) = (0, Ts x) := by
    have h := hT (0, 1) (0, x)
    simpa [carrierRepresentation, Ts] using h
  have hTc : Tc ∈ Set.center (Module.End ℂ Coloured) := by
    rw [Semigroup.mem_center_iff]
    intro A
    apply LinearMap.ext
    intro x
    have h := congrArg Prod.fst (hT (A, 0) (x, 0))
    simpa [carrierRepresentation, Tc] using h.symm
  have hTs : Ts ∈ Set.center (Module.End ℂ Scalar) := by
    rw [Semigroup.mem_center_iff]
    intro A
    apply LinearMap.ext
    intro x
    have h := congrArg Prod.snd (hT (0, A) (0, x))
    simpa [carrierRepresentation, Ts] using h.symm
  obtain ⟨lambda, _, hlambda⟩ := Module.End.mem_center_iff.mp hTc
  obtain ⟨mu, _, hmu⟩ := Module.End.mem_center_iff.mp hTs
  refine ⟨lambda, mu, ?_⟩
  intro x
  calc
    T x = T (x.1, 0) + T (0, x.2) := by
      rw [← T.map_add]
      congr
      ext <;> simp
    _ = (Tc x.1, Ts x.2) := by rw [hcoloured, hscalar]; simp
    _ = (lambda • x.1, mu • x.2) := by
      rw [hlambda, hmu]
      rfl

/-- For a unitary symmetry of the carrier, the two residual block scalars
are phases. -/
theorem unitary_commutant_carrierRepresentation_is_blockPhase
    (U : (Coloured × Scalar) ≃ₗᵢ[ℂ] (Coloured × Scalar))
    (hU : ∀ A x, U (carrierRepresentation A x) =
      carrierRepresentation A (U x)) :
    ∃ lambda mu : ℂ, ‖lambda‖ = 1 ∧ ‖mu‖ = 1 ∧
      ∀ x : Coloured × Scalar, U x = (lambda • x.1, mu • x.2) := by
  obtain ⟨lambda, mu, hblock⟩ :=
    commutant_carrierRepresentation_is_blockScalar
      U.toLinearEquiv.toLinearMap hU
  obtain ⟨x, hx⟩ : ∃ x : Coloured, x ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by
    rw [coloured_finrank]
    norm_num)
  obtain ⟨y, hy⟩ : ∃ y : Scalar, y ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by
    rw [scalar_finrank]
    norm_num)
  have hlambda : ‖lambda‖ = 1 := by
    have hnorm : ‖lambda‖ * ‖x‖ = 1 * ‖x‖ := calc
      ‖lambda‖ * ‖x‖ = ‖(lambda • x, (0 : Scalar))‖ := by
        rw [Prod.norm_def]
        simp only [norm_zero]
        rw [max_eq_left (norm_nonneg _)]
        exact (norm_smul lambda x).symm
      _ = ‖U.toLinearEquiv (x, 0)‖ :=
        (congrArg (fun z : Coloured × Scalar => ‖z‖) (hblock (x, 0))).symm
      _ = ‖(x, 0)‖ := U.norm_map (x, 0)
      _ = 1 * ‖x‖ := by simp [Prod.norm_def]
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hx) hnorm
  have hmu : ‖mu‖ = 1 := by
    have hnorm : ‖mu‖ * ‖y‖ = 1 * ‖y‖ := calc
      ‖mu‖ * ‖y‖ = ‖((0 : Coloured), mu • y)‖ := by
        rw [Prod.norm_def]
        simp only [norm_zero]
        rw [max_eq_right (norm_nonneg _)]
        exact (norm_smul mu y).symm
      _ = ‖U.toLinearEquiv (0, y)‖ :=
        (congrArg (fun z : Coloured × Scalar => ‖z‖) (hblock (0, y))).symm
      _ = ‖(0, y)‖ := U.norm_map (0, y)
      _ = 1 * ‖y‖ := by simp [Prod.norm_def]
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hy) hnorm
  exact ⟨lambda, mu, hlambda, hmu, hblock⟩

theorem carrier_finrank_eight : Module.finrank ℂ (Coloured × Scalar) = 8 := by
  rw [Module.finrank_prod, coloured_finrank, scalar_finrank]

section ArbitraryHilbertRealization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The actual source-block adjoint, before passage to matrix coordinates. -/
def AdjointCompatible (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H) : Prop :=
  ∀ A x y, inner ℂ (ρ A x) y = inner ℂ x (ρ (star A) y)

def matrixRepresentation (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H) :
    MinimalFaithfulModule.JointRepresentation (H := H) :=
  ρ.comp matrixCoordinates.symm.toAlgEquiv.toAlgHom

omit [FiniteDimensional ℂ H] in
theorem matrixRepresentation_starCompatible
    (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H) (hρ : AdjointCompatible ρ) :
    MinimalFaithfulModule.JointStarCompatible (matrixRepresentation ρ) := by
  intro A x y
  change inner ℂ (ρ (matrixCoordinates.symm A) x) y =
    inner ℂ x (ρ (matrixCoordinates.symm (star A)) y)
  calc
    inner ℂ (ρ (matrixCoordinates.symm A) x) y =
        inner ℂ x (ρ (star (matrixCoordinates.symm A)) y) :=
      hρ (matrixCoordinates.symm A) x y
    _ = inner ℂ x (ρ (matrixCoordinates.symm (star A)) y) :=
      congrArg (fun B : JointEnd => inner ℂ x (ρ B y))
        (matrixCoordinates_symm_star A).symm

theorem faithful_finrank_ge_eight (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H)
    (hρ : Function.Injective ρ) : 8 ≤ Module.finrank ℂ H :=
  MinimalFaithfulModule.faithfulJointRep_finrank_ge_eight
    (matrixRepresentation ρ) (hρ.comp matrixCoordinates.symm.injective)

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [FiniteDimensional ℂ H']

/-- The previously proved minimal-module classification now applies to the
actual source response algebra, with its actual Hilbert adjoint. -/
theorem minimal_realizations_unitarilyEquivalent
    (ρ : JointEnd →ₐ[ℂ] Module.End ℂ H) (hρ : AdjointCompatible ρ)
    (hρinj : Function.Injective ρ)
    (σ : JointEnd →ₐ[ℂ] Module.End ℂ H') (hσ : AdjointCompatible σ)
    (hσinj : Function.Injective σ)
    (hdimρ : Module.finrank ℂ H = 8) (hdimσ : Module.finrank ℂ H' = 8) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ A x, U (ρ A x) = σ A (U x) := by
  obtain ⟨U, hU⟩ := MinimalFaithfulModule.minimalEightDimensionalJointRep_unique
    (matrixRepresentation ρ) (matrixRepresentation_starCompatible ρ hρ)
    (hρinj.comp matrixCoordinates.symm.injective)
    (matrixRepresentation σ) (matrixRepresentation_starCompatible σ hσ)
    (hσinj.comp matrixCoordinates.symm.injective) hdimρ hdimσ
  refine ⟨U, ?_⟩
  intro A x
  simpa [matrixRepresentation] using hU (matrixCoordinates A) x

end ArbitraryHilbertRealization

end GeneratedFoundations.Physical.SourceJointResponse
