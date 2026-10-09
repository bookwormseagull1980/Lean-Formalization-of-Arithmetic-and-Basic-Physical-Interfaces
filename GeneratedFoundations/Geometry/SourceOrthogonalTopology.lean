module

public import GeneratedFoundations.Geometry.SourceOrthogonalCover
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The topological double covering of the full orthogonal response

The determinant-one isometries of the quaternion amplitude space carry
the topology of their actual matrices in the basis `1, i, j, k`. This
topology is specified independently of the source homomorphism. The
source action is continuous in these coordinates and is already known
to be onto. Compactness then identifies the target topology with the
quotient topology. The exact diagonal two-element kernel is discrete,
so this same homomorphism is a two-sheeted topological covering.

The quotient identification is a topological group isomorphism. These
statements do not assume that the source product is simply connected.
-/

@[expose] public section

noncomputable section

open Topology
open scoped Quaternion
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceSpecialOrthogonal
open GeneratedFoundations.Geometry.SourceLeftRightAction
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceOrthogonalCover

namespace GeneratedFoundations.Geometry.SourceOrthogonalTopology

/-- Matrix coordinates on all determinant-one real isometries. -/
def operatorMatrix (e : specialOrthogonal) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix quaternionBasis quaternionBasis e.val.toLinearMap

theorem operatorMatrix_injective : Function.Injective operatorMatrix := by
  intro e f h
  have he : e.val.toLinearMap = f.val.toLinearMap :=
    (LinearMap.toMatrix quaternionBasis quaternionBasis).injective h
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  exact congrArg (fun A : Module.End ℝ ℍ => A x) he

/-- The usual finite-dimensional matrix topology, without using the source quotient. -/
instance : TopologicalSpace specialOrthogonal :=
  TopologicalSpace.induced operatorMatrix inferInstance

theorem operatorMatrix_isEmbedding : Topology.IsEmbedding operatorMatrix :=
  operatorMatrix_injective.isEmbedding_induced

instance : T2Space specialOrthogonal := operatorMatrix_isEmbedding.t2Space

theorem operatorMatrix_continuous : Continuous operatorMatrix :=
  operatorMatrix_isEmbedding.continuous

theorem sourceRepresentation_continuous_apply (x : ℍ) :
    Continuous (fun p : SourcePair => sourceRepresentation p x) := by
  have ha : Continuous (fun p : SourcePair => (unitaryEquiv.symm p.1 : ℍ)) :=
    continuous_subtype_val.comp (unitaryEquiv.symm.continuous.comp continuous_fst)
  have hb : Continuous (fun p : SourcePair => (unitaryEquiv.symm p.2 : ℍ)) :=
    continuous_subtype_val.comp (unitaryEquiv.symm.continuous.comp continuous_snd)
  exact (ha.mul continuous_const).mul hb.star

/-- Continuity is checked in the target's matrix coordinates. -/
theorem sourceCover_continuous : Continuous sourceCover := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun p : SourcePair => operatorMatrix (sourceCover p) i j)
  simp only [operatorMatrix, LinearMap.toMatrix_apply]
  change Continuous (fun p : SourcePair =>
    quaternionBasis.coord i (sourceRepresentation p (quaternionBasis j)))
  exact (quaternionBasis.coord i).continuous_of_finiteDimensional.comp
    (sourceRepresentation_continuous_apply (quaternionBasis j))

theorem sourceCover_isQuotientMap : IsQuotientMap sourceCover :=
  .of_surjective_continuous sourceCover_surjective sourceCover_continuous

theorem sourceCover_kernel_isDiscrete : IsDiscrete (sourceCover.ker : Set SourcePair) := by
  rw [sourceCover_kernel]
  exact ((Set.finite_singleton (negativeIdentity, negativeIdentity)).insert
    ((1, 1) : SourcePair)).isDiscrete

/-- The sheets are indexed by the kernel of the original source action. -/
theorem sourceCover_isQuotientCoveringMap :
    IsQuotientCoveringMap sourceCover sourceCover.ker :=
  sourceCover_isQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    sourceCover_kernel_isDiscrete

theorem sourceCover_isCoveringMap : IsCoveringMap sourceCover :=
  sourceCover_isQuotientCoveringMap.isCoveringMap

theorem sourceCover_isLocalHomeomorph : IsLocalHomeomorph sourceCover :=
  sourceCover_isCoveringMap.isLocalHomeomorph

/-- Multiplication and inversion descend continuously to the independent matrix topology. -/
instance : IsTopologicalGroup specialOrthogonal where
  continuous_mul := by
    have hq := sourceCover_isQuotientCoveringMap.isOpenQuotientMap
    apply (hq.prodMap hq).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, Prod.map, Pi.mul_apply, map_mul] using
      sourceCover_continuous.comp (continuous_fst.mul continuous_snd :
        Continuous (fun p : SourcePair × SourcePair => p.1 * p.2))
  continuous_inv := by
    apply sourceCover_isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, map_inv] using
      sourceCover_continuous.comp (continuous_inv : Continuous (Inv.inv : SourcePair → SourcePair))

theorem sourceCover_kernel_card : Nat.card sourceCover.ker = 2 := by
  let e : sourceCover.ker := ⟨1, sourceCover.ker.one_mem⟩
  let n : sourceCover.ker := ⟨(negativeIdentity, negativeIdentity),
    (sourceCover_kernel_iff _).mpr (Or.inr rfl)⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨e, n, ?_, ?_⟩
  · intro h
    exact negativeIdentity_ne_one
      (congrArg (fun p : sourceCover.ker => p.val.1) h).symm
  · apply Set.eq_univ_of_forall
    intro p
    rcases (sourceCover_kernel_iff p.val).mp p.property with hp | hp
    · exact Or.inl (Subtype.ext hp)
    · exact Or.inr (Subtype.ext hp)

theorem sourceCover_fibre_card (e : specialOrthogonal) :
    Nat.card (sourceCover ⁻¹' {e}) = 2 := by
  obtain ⟨p, hp⟩ := sourceCover_surjective e
  exact (Nat.card_congr
    (sourceCover_isQuotientCoveringMap.fiberEquivGroup ⟨p, hp⟩)).trans
    sourceCover_kernel_card

theorem sourceCover_evenlyCovered (e : specialOrthogonal) :
    IsEvenlyCovered sourceCover e sourceCover.ker := by
  let : DiscreteTopology sourceCover.ker :=
    SetLike.isDiscrete_iff_discreteTopology.mp sourceCover_kernel_isDiscrete
  let : DiscreteTopology (sourceCover ⁻¹' {e}) := (sourceCover_isCoveringMap e).1
  obtain ⟨p, hp⟩ := sourceCover_surjective e
  exact (sourceCover_isCoveringMap e).of_fiber_homeomorph
    (sourceCover_isQuotientCoveringMap.fiberEquivGroup ⟨p, hp⟩).toHomeomorphOfDiscrete

theorem sourceCover_local_trivialization (e : specialOrthogonal) :
    ∃ t : Bundle.Trivialization sourceCover.ker sourceCover, e ∈ t.baseSet := by
  let h := sourceCover_evenlyCovered e
  exact ⟨h.toTrivialization', h.2.choose_spec.1⟩

@[simp] theorem sourceQuotientEquiv_mk (p : SourcePair) :
    sourceQuotientEquiv (QuotientGroup.mk p) = sourceCover p := rfl

theorem sourceQuotientEquiv_continuous : Continuous sourceQuotientEquiv := by
  apply (QuotientGroup.isQuotientMap_mk sourceCover.ker).continuous_iff.mpr
  simpa only [Function.comp_def, sourceQuotientEquiv_mk] using sourceCover_continuous

def sourceQuotientHomeomorph : SourcePair ⧸ sourceCover.ker ≃ₜ specialOrthogonal :=
  sourceQuotientEquiv.toEquiv.toHomeomorphOfContinuousClosed
    sourceQuotientEquiv_continuous sourceQuotientEquiv_continuous.isClosedMap

/-- The quotient group and the full determinant-one response group have the same topology. -/
def sourceQuotientContinuousEquiv :
    SourcePair ⧸ sourceCover.ker ≃ₜ* specialOrthogonal where
  toMulEquiv := sourceQuotientEquiv
  continuous_toFun := sourceQuotientHomeomorph.continuous
  continuous_invFun := sourceQuotientHomeomorph.symm.continuous

@[simp] theorem sourceQuotientContinuousEquiv_mk (p : SourcePair) :
    sourceQuotientContinuousEquiv (QuotientGroup.mk p) = sourceCover p := rfl

/-- Compatibility with the source homomorphism fixes the quotient identification. -/
theorem sourceQuotientContinuousEquiv_unique
    (e : SourcePair ⧸ sourceCover.ker ≃ₜ* specialOrthogonal)
    (he : ∀ p : SourcePair, e (QuotientGroup.mk p) = sourceCover p) :
    e = sourceQuotientContinuousEquiv := by
  apply ContinuousMulEquiv.ext
  intro q
  induction q using Quotient.inductionOn' with
  | h p => exact he p

/-- An oriented change of ambient frame lifts to conjugation in the same source product. -/
theorem frame_change_lifts (e : specialOrthogonal) :
    ∃ p : SourcePair, sourceCover p = e ∧
      ∀ q : SourcePair, sourceCover (p * q * p⁻¹) = e * sourceCover q * e⁻¹ := by
  obtain ⟨p, hp⟩ := sourceCover_surjective e
  refine ⟨p, hp, ?_⟩
  intro q
  simp only [map_mul, map_inv, hp]

end GeneratedFoundations.Geometry.SourceOrthogonalTopology
