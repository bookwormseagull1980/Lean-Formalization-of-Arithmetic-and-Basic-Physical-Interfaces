module

public import GeneratedFoundations.Physical.SourceMatterCharge
public import GeneratedFoundations.Physical.SourceScalarConnector
public import GeneratedFoundations.Physical.SourceGaugeTransport
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Operator descent to the charged source quotient

The quotient is the actual sixteen-dimensional source carrier modulo its
neutral right line. A descended operator is defined by a commuting diagram
with the quotient map; invariance of the neutral line is then proved
equivalent to its existence and uniqueness.

The reduced gauge action fixes the neutral vector pointwise and therefore
induces a representation on this quotient. A nonzero elementary scalar
connector sends that same vector to a nonzero left-labelled source vector.
Its self-adjoint odd extension consequently does not induce an operator on
the charged quotient. These statements distinguish quotient descent from
the construction of a different operator by orthogonal compression.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct ComplexConjugate

namespace GeneratedFoundations.Physical.SourceChargedQuotient

open SourceJointResponse SourceMinimalRepresentation SourceChiralCarrier
open SourceMatterCharge SourceScalarConnector ReversalRealConnector

abbrev ChargedMatter := FullMatter ⧸ neutralLine

def quotientMap : FullMatter →ₗ[ℂ] ChargedMatter := neutralLine.mkQ

theorem quotientMap_surjective : Function.Surjective quotientMap :=
  neutralLine.mkQ_surjective

theorem quotientMap_eq_zero_iff (x : FullMatter) :
    quotientMap x = 0 ↔ x ∈ neutralLine := by
  change x ∈ LinearMap.ker neutralLine.mkQ ↔ x ∈ neutralLine
  rw [Submodule.ker_mkQ]

def PreservesNeutral (A : Module.End ℂ FullMatter) : Prop :=
  neutralLine ≤ neutralLine.comap A

def Descends (A : Module.End ℂ FullMatter) : Prop :=
  ∃ B : Module.End ℂ ChargedMatter, quotientMap.comp A = B.comp quotientMap

theorem preservesNeutral_iff (A : Module.End ℂ FullMatter) :
    PreservesNeutral A ↔ A neutralVector ∈ neutralLine := by
  constructor
  · intro h
    exact h (Submodule.mem_span_singleton_self neutralVector)
  · intro h x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change A (c • neutralVector) ∈ neutralLine
    rw [map_smul]
    exact neutralLine.smul_mem c h

/-- The endomorphism is constructed by the quotient universal property. -/
def induced (A : Module.End ℂ FullMatter) (hA : PreservesNeutral A) :
    Module.End ℂ ChargedMatter := neutralLine.mapQ neutralLine A hA

@[simp] theorem induced_apply (A : Module.End ℂ FullMatter) (hA : PreservesNeutral A)
    (x : FullMatter) : induced A hA (quotientMap x) = quotientMap (A x) := rfl

theorem induced_intertwines (A : Module.End ℂ FullMatter) (hA : PreservesNeutral A) :
    quotientMap.comp A = (induced A hA).comp quotientMap := by
  apply LinearMap.ext
  intro x
  rfl

private theorem preserves_of_quotient_intertwines {E : Type*}
    [AddCommGroup E] [Module ℂ E] (K : Submodule ℂ E)
    (A : Module.End ℂ E) (B : Module.End ℂ (E ⧸ K))
    (h : K.mkQ.comp A = B.comp K.mkQ) : K ≤ K.comap A := by
  intro x hx
  change A x ∈ K
  have hx0 : K.mkQ x = 0 := by
    change x ∈ LinearMap.ker K.mkQ
    rwa [Submodule.ker_mkQ]
  have he : K.mkQ (A x) = B (K.mkQ x) := LinearMap.congr_fun h x
  have he0 : K.mkQ (A x) = 0 := he.trans ((congrArg B hx0).trans B.map_zero)
  change A x ∈ LinearMap.ker K.mkQ at he0
  rwa [Submodule.ker_mkQ] at he0

theorem preservesNeutral_of_intertwines (A : Module.End ℂ FullMatter)
    (B : Module.End ℂ ChargedMatter)
    (h : quotientMap.comp A = B.comp quotientMap) : PreservesNeutral A :=
  preserves_of_quotient_intertwines neutralLine A B h

theorem descends_iff (A : Module.End ℂ FullMatter) :
    Descends A ↔ PreservesNeutral A := by
  constructor
  · rintro ⟨B, hB⟩
    exact preservesNeutral_of_intertwines A B hB
  · intro hA
    exact ⟨induced A hA, induced_intertwines A hA⟩

theorem descends_iff_map_le (A : Module.End ℂ FullMatter) :
    Descends A ↔ neutralLine.map A ≤ neutralLine := by
  rw [descends_iff]
  change (neutralLine ≤ neutralLine.comap A) ↔ neutralLine.map A ≤ neutralLine
  exact Submodule.map_le_iff_le_comap.symm

theorem induced_unique (A : Module.End ℂ FullMatter) (hA : PreservesNeutral A)
    (B : Module.End ℂ ChargedMatter)
    (hB : quotientMap.comp A = B.comp quotientMap) : B = induced A hA := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := quotientMap_surjective q
  exact (LinearMap.congr_fun hB x).symm

theorem existsUnique_induced_iff (A : Module.End ℂ FullMatter) :
    (∃! B : Module.End ℂ ChargedMatter,
      quotientMap.comp A = B.comp quotientMap) ↔ PreservesNeutral A := by
  constructor
  · rintro ⟨B, hB, _⟩
    exact preservesNeutral_of_intertwines A B hB
  · intro hA
    exact ⟨induced A hA, induced_intertwines A hA, induced_unique A hA⟩

private def coordinateNeutral : GlobalGaugeKernel.Matter :=
  ((0, 0), ((0, 0), (fun _ => 1, 0)))

private theorem coordinates_neutral :
    SourceGaugeTransport.coordinates neutralVector = coordinateNeutral := by
  rw [neutralVector, SourceGaugeTransport.coordinates_basis]
  ext i <;>
    simp [SourceGaugeTransport.pack, coordinateNeutral, neutralIndex, Pi.single_apply]
  exact Subsingleton.elim _ _

private theorem coordinate_gauge_fixes (g : GlobalGaugeKernel.GaugeGroup) :
    GlobalGaugeKernel.representation g coordinateNeutral = coordinateNeutral := by
  change
    (((GlobalGaugeKernel.blocks g).1.1.mulVec 0,
        (GlobalGaugeKernel.blocks g).1.2.mulVec 0),
      (((GlobalGaugeKernel.blocks g).2.1.1.mulVec 0,
          (GlobalGaugeKernel.blocks g).2.1.2.mulVec 0),
        ((GlobalGaugeKernel.blocks g).2.2.1.mulVec (fun _ => 1),
          (GlobalGaugeKernel.blocks g).2.2.2.mulVec 0))) = coordinateNeutral
  simp [GlobalGaugeKernel.blocks, coordinateNeutral]

theorem gauge_fixes_neutral (g : GlobalGaugeKernel.GaugeGroup) :
    SourceGaugeTransport.representation g neutralVector = neutralVector := by
  apply SourceGaugeTransport.coordinates.injective
  rw [SourceGaugeTransport.coordinates_intertwines, coordinates_neutral,
    coordinate_gauge_fixes]

theorem gauge_preservesNeutral (g : GlobalGaugeKernel.GaugeGroup) :
    PreservesNeutral (SourceGaugeTransport.representation g) := by
  rw [preservesNeutral_iff, gauge_fixes_neutral]
  exact Submodule.mem_span_singleton_self neutralVector

theorem quotient_representation_one {E G : Type*}
    [AddCommGroup E] [Module ℂ E] [Monoid G] (K : Submodule ℂ E)
    (ρ : G →* Module.End ℂ E) (hp : ∀ g, K ≤ K.comap (ρ g)) :
    K.mapQ K (ρ 1) (hp 1) = 1 := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := K.mkQ_surjective q
  change K.mkQ (ρ 1 x) = K.mkQ x
  exact congrArg K.mkQ (LinearMap.congr_fun (map_one ρ) x)

theorem quotient_representation_mul {E G : Type*}
    [AddCommGroup E] [Module ℂ E] [Monoid G] (K : Submodule ℂ E)
    (ρ : G →* Module.End ℂ E) (hp : ∀ g, K ≤ K.comap (ρ g)) (g h : G) :
    K.mapQ K (ρ (g * h)) (hp (g * h)) =
      K.mapQ K (ρ g) (hp g) * K.mapQ K (ρ h) (hp h) := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := K.mkQ_surjective q
  change K.mkQ (ρ (g * h) x) = K.mkQ (ρ g (ρ h x))
  exact congrArg K.mkQ (LinearMap.congr_fun (map_mul ρ g h) x)

def quotientRepresentation : GlobalGaugeKernel.GaugeGroup →* Module.End ℂ ChargedMatter where
  toFun g := induced (SourceGaugeTransport.representation g) (gauge_preservesNeutral g)
  map_one' := quotient_representation_one neutralLine
    SourceGaugeTransport.representation gauge_preservesNeutral
  map_mul' := quotient_representation_mul neutralLine
    SourceGaugeTransport.representation gauge_preservesNeutral

@[simp] theorem quotientRepresentation_apply (g : GlobalGaugeKernel.GaugeGroup)
    (x : FullMatter) :
    quotientRepresentation g (quotientMap x) =
      quotientMap (SourceGaugeTransport.representation g x) := rfl

theorem quotientRepresentation_intertwines (g : GlobalGaugeKernel.GaugeGroup) :
    quotientMap.comp (SourceGaugeTransport.representation g) =
      (quotientRepresentation g).comp quotientMap :=
  induced_intertwines (SourceGaugeTransport.representation g) (gauge_preservesNeutral g)

theorem gauge_descends (g : GlobalGaugeKernel.GaugeGroup) :
    Descends (SourceGaugeTransport.representation g) :=
  (descends_iff _).mpr (gauge_preservesNeutral g)

/-- The source first column is the pseudoreal partner of the same doublet. -/
theorem doubletLift_vacuum (H : Spinor) :
    doubletLift H (spinBasis 0) =
      star (H 1) • spinBasis 0 + (-star (H 0)) • spinBasis 1 := by
  change SourceSpinIdentification.spinAction (connectorOfDoublet H)
    (SourceSpinIdentification.spinBasis 0) = _
  rw [SourceSpinIdentification.spinAction_basis]
  simp [connectorOfDoublet, spinBasis]

theorem scalarConnector_neutral (H : Spinor) :
    scalarConnector H neutralVector =
      star (H 1) • fullBasis (Sum.inr 0, Sum.inl 0) +
        (-star (H 0)) • fullBasis (Sum.inr 0, Sum.inl 1) := by
  rw [scalarConnector, neutralVector_source, connector_right]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    simp [doubletLift_vacuum, TensorProduct.tmul_add, TensorProduct.tmul_smul,
      WithLp.ofLp_smul, WithLp.ofLp_add]
  · simp

private theorem basis_pair_coefficients_zero {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E) {i j : ι} (hij : i ≠ j) {c d : ℂ}
    (h : c • b i + d • b j = 0) : c = 0 ∧ d = 0 := by
  classical
  have hi := congrArg (fun x : E => b.repr x i) h
  have hj := congrArg (fun x : E => b.repr x j) h
  simp [OrthonormalBasis.repr_self, hij, Ne.symm hij] at hi hj
  exact ⟨hi, hj⟩

theorem scalarConnector_neutral_eq_zero_iff (H : Spinor) :
    scalarConnector H neutralVector = 0 ↔ H = 0 := by
  constructor
  · intro h
    obtain ⟨h1, h0⟩ := basis_pair_coefficients_zero fullBasis
      (i := (Sum.inr 0, Sum.inl 0)) (j := (Sum.inr 0, Sum.inl 1))
      (by decide) ((scalarConnector_neutral H).symm.trans h)
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · rintro rfl
    simp [scalarConnector_neutral]

theorem scalarConnector_neutral_ne_zero {H : Spinor} (hH : H ≠ 0) :
    scalarConnector H neutralVector ≠ 0 :=
  fun h => hH ((scalarConnector_neutral_eq_zero_iff H).mp h)

private theorem leftProjection_neutral : leftProjection neutralVector = 0 := by
  rw [neutralVector_source]
  simp [leftProjection, SourceMatterCharge.diagonalBlocks_right]

theorem scalarConnector_neutral_left (H : Spinor) :
    leftProjection (scalarConnector H neutralVector) = scalarConnector H neutralVector := by
  simp [scalarConnector_neutral, leftProjection, SourceMatterCharge.diagonalBlocks_left]

theorem scalarConnector_neutral_not_mem {H : Spinor} (hH : H ≠ 0) :
    scalarConnector H neutralVector ∉ neutralLine := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have hz : leftProjection (c • neutralVector) = 0 :=
    (leftProjection.map_smul c neutralVector).trans
      ((congrArg (fun x : FullMatter => c • x) leftProjection_neutral).trans (smul_zero c))
  exact scalarConnector_neutral_ne_zero hH
    ((scalarConnector_neutral_left H).symm.trans ((congrArg leftProjection hc).symm.trans hz))

theorem scalarConnector_not_preservesNeutral {H : Spinor} (hH : H ≠ 0) :
    ¬ PreservesNeutral (scalarConnector H) := by
  rw [preservesNeutral_iff]
  exact scalarConnector_neutral_not_mem hH

theorem scalarConnector_not_descends {H : Spinor} (hH : H ≠ 0) :
    ¬ Descends (scalarConnector H) := by
  rw [descends_iff]
  exact scalarConnector_not_preservesNeutral hH

theorem scalarConnector_descends_iff (H : Spinor) :
    Descends (scalarConnector H) ↔ H = 0 := by
  constructor
  · intro h
    by_contra hH
    exact scalarConnector_not_descends hH h
  · rintro rfl
    rw [descends_iff, preservesNeutral_iff]
    simp [scalarConnector_neutral]

private theorem preserves_iff_commute_projection {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (A : Module.End ℂ E) (hA : A.IsSymmetric) :
    (K ≤ K.comap A) ↔ Commute A K.starProjection.toLinearMap := by
  constructor
  · intro hp
    apply LinearMap.ext
    intro x
    change A (K.starProjection x) = K.starProjection (A x)
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := K)
    · exact hp (K.starProjection_apply_mem x)
    · intro w hw
      rw [← map_sub, hA]
      exact Submodule.starProjection_inner_eq_zero (K := K) x (A w) (hp hw)
  · intro hc x hx
    have he : A (K.starProjection x) = K.starProjection (A x) :=
      LinearMap.congr_fun hc.eq x
    have hx' : K.starProjection x = x :=
      (Submodule.starProjection_eq_self_iff (K := K)).mpr hx
    exact (Submodule.starProjection_eq_self_iff (K := K)).mp
      (he.symm.trans (congrArg A hx'))

local instance : FiniteDimensional ℂ neutralLine :=
  FiniteDimensional.span_singleton ℂ neutralVector

local instance : CompleteSpace neutralLine := FiniteDimensional.complete ℂ neutralLine

local instance : neutralLine.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace neutralLine

/-- This is the actual Hilbert orthogonal projection, not a chosen matrix cutoff. -/
def neutralProjection : Module.End ℂ FullMatter := neutralLine.starProjection.toLinearMap

theorem preservesNeutral_iff_commute_of_selfAdjoint (A : Module.End ℂ FullMatter)
    (hA : IsSelfAdjoint A) : PreservesNeutral A ↔ Commute A neutralProjection :=
  preserves_iff_commute_projection neutralLine A
    ((LinearMap.isSymmetric_iff_isSelfAdjoint A).mpr hA)

theorem selfAdjoint_descends_iff_commute (A : Module.End ℂ FullMatter)
    (hA : IsSelfAdjoint A) : Descends A ↔ Commute A neutralProjection :=
  (descends_iff A).trans (preservesNeutral_iff_commute_of_selfAdjoint A hA)

theorem scalarConnector_not_commute {H : Spinor} (hH : H ≠ 0) :
    ¬ Commute (scalarConnector H) neutralProjection := by
  rw [← selfAdjoint_descends_iff_commute _ (scalarConnector_isSelfAdjoint H)]
  exact scalarConnector_not_descends hH

theorem scalarConnector_selfAdjoint_odd_not_descends {H : Spinor} (hH : H ≠ 0) :
    IsSelfAdjoint (scalarConnector H) ∧
      grading * scalarConnector H + scalarConnector H * grading = 0 ∧
      ¬ Descends (scalarConnector H) :=
  ⟨scalarConnector_isSelfAdjoint H, scalarConnector_odd H, scalarConnector_not_descends hH⟩

end GeneratedFoundations.Physical.SourceChargedQuotient
