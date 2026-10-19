module

public import GeneratedFoundations.Physical.SourceGlobalGaugeGroup
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The unitary reduced gauge action on the actual source Hilbert space

The six coordinate blocks retain the orthonormal colour, spin and chiral
labels of the actual matter carrier. Their Hermitian pairings add to its
original Hilbert inner product. The raw product coordinate space is used
only for this explicit pairing calculation, without identifying its
default product norm with the source Hilbert norm.

Each of the six matrix blocks preserves its pairing. Consequently the
internally constructed reduced gauge representation is unitary, and its
quotient by the computed central subgroup acts faithfully and unitarily
on the same carrier. No local bundle or compatibility witness is an argument
of this construction. General localized comparison theorems occur separately;
the concrete generated bundle is assembled in `CanonicalMatterBundle`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker

namespace GeneratedFoundations.Physical.SourceGaugeUnitary

open SourceChiralCarrier SourceGaugeTransport

abbrev GaugeGroup := GlobalGaugeKernel.GaugeGroup
abbrev EffectiveGroup := SourceGlobalGaugeGroup.EffectiveGroup

/-- The Hermitian pairing of a single finite coordinate block. -/
def vectorInner {ι : Type*} [Fintype ι] (x y : ι → ℂ) : ℂ := star x ⬝ᵥ y

/-- The sum of all six block pairings, including the neutral right line. -/
def sixBlockInner (x y : GlobalGaugeKernel.Matter) : ℂ :=
  (vectorInner x.1.1 y.1.1 + vectorInner x.1.2 y.1.2) +
    ((vectorInner x.2.1.1 y.2.1.1 + vectorInner x.2.1.2 y.2.1.2) +
      (vectorInner x.2.2.1 y.2.2.1 + vectorInner x.2.2.2 y.2.2.2))

/-- Packing is an explicit permutation of the sixteen pairing summands. -/
theorem sixBlockInner_pack (x y : FullIndex → ℂ) :
    sixBlockInner (pack x) (pack y) = vectorInner x y := by
  simp [sixBlockInner, vectorInner, pack, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

/-- The source inner product, rather than a norm on the raw six-block product. -/
theorem coordinates_inner (x y : FullMatter) :
    sixBlockInner (coordinates x) (coordinates y) = inner ℂ x y := by
  change sixBlockInner (pack (fullBasis.toBasis.equivFun x))
    (pack (fullBasis.toBasis.equivFun y)) = _
  rw [sixBlockInner_pack]
  simp only [OrthonormalBasis.coe_toBasis_repr]
  change star (WithLp.ofLp (fullBasis.repr x)) ⬝ᵥ
    WithLp.ofLp (fullBasis.repr y) = _
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  exact fullBasis.repr.inner_map_map x y

theorem vectorInner_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) (x y : ι → ℂ) :
    vectorInner (A.mulVec x) (A.mulVec y) = vectorInner x y := by
  have ha : A.conjTranspose * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  simp only [vectorInner, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ha, Matrix.vecMul_one]

private theorem circle_smul_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Circle) {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    (z : ℂ) • A ∈ Matrix.unitaryGroup ι ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  have hz : star (z : ℂ) = (z : ℂ)⁻¹ := by
    simpa only [Circle.coe_inv, Complex.star_def] using (Circle.coe_inv_eq_conj z).symm
  rw [star_smul, smul_mul_smul_comm, Matrix.mem_unitaryGroup_iff'.mp hA,
    hz, inv_mul_cancel₀ (Circle.coe_ne_zero z), one_smul]

private theorem kronecker_unitary {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (hB : B ∈ Matrix.unitaryGroup κ ℂ) :
    A ⊗ₖ B ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (A ⊗ₖ B).conjTranspose * (A ⊗ₖ B) = 1
  have ha : A.conjTranspose * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  have hb : B.conjTranspose * B = 1 := Matrix.mem_unitaryGroup_iff'.mp hB
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ha, hb, Matrix.one_kronecker_one]

private theorem circle_pow_smul_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Circle) (n : ℕ) {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    (z : ℂ) ^ n • A ∈ Matrix.unitaryGroup ι ℂ := by
  simpa only [Circle.coe_pow] using circle_smul_unitary (z ^ n) hA

private theorem circle_inv_pow_smul_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Circle) (n : ℕ) {A : Matrix ι ι ℂ} (hA : A ∈ Matrix.unitaryGroup ι ℂ) :
    ((z : ℂ) ^ n)⁻¹ • A ∈ Matrix.unitaryGroup ι ℂ := by
  simpa only [Circle.coe_inv, Circle.coe_pow] using circle_smul_unitary ((z ^ n)⁻¹) hA

/-- All six blocks of the existing representation are unitary matrices. -/
theorem blocks_unitary (g : GaugeGroup) :
    (GlobalGaugeKernel.blocks g).1.1 ∈ Matrix.unitaryGroup (Fin 3 × Fin 2) ℂ ∧
    (GlobalGaugeKernel.blocks g).1.2 ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    (GlobalGaugeKernel.blocks g).2.1.1 ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    (GlobalGaugeKernel.blocks g).2.1.2 ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    (GlobalGaugeKernel.blocks g).2.2.1 ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧
    (GlobalGaugeKernel.blocks g).2.2.2 ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  have h3 : (g.1 : GlobalGaugeKernel.Mat3) ∈ Matrix.unitaryGroup (Fin 3) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.1.property).1
  have h2 : (g.2.1 : Operations.SourceSpinCorner.Mat2) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    (Matrix.mem_specialUnitaryGroup_iff.mp g.2.1.property).1
  refine ⟨circle_smul_unitary g.2.2 (kronecker_unitary h3 h2), ?_, ?_, ?_, ?_, ?_⟩
  · exact circle_inv_pow_smul_unitary g.2.2 3 h2
  · exact circle_pow_smul_unitary g.2.2 4 h3
  · exact circle_inv_pow_smul_unitary g.2.2 2 h3
  · exact (Matrix.unitaryGroup (Fin 1) ℂ).one_mem
  · exact circle_inv_pow_smul_unitary g.2.2 6 (Matrix.unitaryGroup (Fin 1) ℂ).one_mem

theorem coordinate_action_blocks (g : GaugeGroup) (x : GlobalGaugeKernel.Matter) :
    GlobalGaugeKernel.representation g x =
      (((GlobalGaugeKernel.blocks g).1.1.mulVec x.1.1,
          (GlobalGaugeKernel.blocks g).1.2.mulVec x.1.2),
        (((GlobalGaugeKernel.blocks g).2.1.1.mulVec x.2.1.1,
            (GlobalGaugeKernel.blocks g).2.1.2.mulVec x.2.1.2),
          ((GlobalGaugeKernel.blocks g).2.2.1.mulVec x.2.2.1,
            (GlobalGaugeKernel.blocks g).2.2.2.mulVec x.2.2.2))) := rfl

theorem coordinate_action_inner (g : GaugeGroup) (x y : GlobalGaugeKernel.Matter) :
    sixBlockInner (GlobalGaugeKernel.representation g x)
      (GlobalGaugeKernel.representation g y) = sixBlockInner x y := by
  obtain ⟨hq, hl, hu, hd, hn, he⟩ := blocks_unitary g
  simp only [coordinate_action_blocks, sixBlockInner, vectorInner_mulVec hq,
    vectorInner_mulVec hl, vectorInner_mulVec hu, vectorInner_mulVec hd,
    vectorInner_mulVec hn, vectorInner_mulVec he]

/-- Preservation of the original Hilbert inner product on the actual source matter. -/
theorem representation_inner (g : GaugeGroup) (x y : FullMatter) :
    inner ℂ (representation g x) (representation g y) = inner ℂ x y := by
  calc
    inner ℂ (representation g x) (representation g y) =
        sixBlockInner (coordinates (representation g x))
          (coordinates (representation g y)) := (coordinates_inner _ _).symm
    _ = sixBlockInner (GlobalGaugeKernel.representation g (coordinates x))
        (GlobalGaugeKernel.representation g (coordinates y)) :=
      congrArg₂ sixBlockInner (coordinates_intertwines g x) (coordinates_intertwines g y)
    _ = sixBlockInner (coordinates x) (coordinates y) := coordinate_action_inner g _ _
    _ = inner ℂ x y := coordinates_inner x y

theorem representation_norm (g : GaugeGroup) (x : FullMatter) :
    ‖representation g x‖ = ‖x‖ :=
  (LinearMap.norm_map_iff_inner_map_map (representation g)).mpr (representation_inner g) x

def representationLinearEquiv {G E : Type*} [Group G]
    [AddCommGroup E] [Module ℂ E] (ρ : G →* Module.End ℂ E) (g : G) : E ≃ₗ[ℂ] E :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    ((ρ.map_mul g g⁻¹).symm.trans ((congrArg ρ (mul_inv_cancel g)).trans ρ.map_one))
    ((ρ.map_mul g⁻¹ g).symm.trans ((congrArg ρ (inv_mul_cancel g)).trans ρ.map_one))

/-- The inverse is the already specified action of the inverse group element. -/
def linearAction (g : GaugeGroup) : FullMatter ≃ₗ[ℂ] FullMatter :=
  representationLinearEquiv representation g

def unitaryAction (g : GaugeGroup) : FullMatter ≃ₗᵢ[ℂ] FullMatter :=
  (linearAction g).isometryOfInner (representation_inner g)

@[simp] theorem unitaryAction_apply (g : GaugeGroup) (x : FullMatter) :
    unitaryAction g x = representation g x := rfl

@[simp] theorem unitaryAction_symm_apply (g : GaugeGroup) (x : FullMatter) :
    (unitaryAction g).symm x = representation g⁻¹ x := rfl

def unitaryRepresentation : GaugeGroup →* (FullMatter ≃ₗᵢ[ℂ] FullMatter) where
  toFun := unitaryAction
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change representation 1 x = x
    simp only [map_one, Module.End.one_apply]
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    change representation (g * h) x = representation g (representation h x)
    simp only [map_mul, Module.End.mul_apply]

theorem representation_adjoint (g : GaugeGroup) :
    (representation g).adjoint = representation g⁻¹ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  exact (unitaryAction g).symm.inner_map_eq_flip x y

theorem representation_mem_unitary_of_adjoint {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : G →* Module.End ℂ E) (hρ : ∀ g, (ρ g).adjoint = ρ g⁻¹) (g : G) :
    ρ g ∈ unitary (Module.End ℂ E) := by
  rw [Unitary.mem_iff, LinearMap.star_eq_adjoint, hρ]
  constructor <;> rw [← map_mul]
  · rw [inv_mul_cancel, map_one]
  · rw [mul_inv_cancel, map_one]

theorem representation_mem_unitary (g : GaugeGroup) :
    representation g ∈ unitary (Module.End ℂ FullMatter) :=
  representation_mem_unitary_of_adjoint representation representation_adjoint g

/-- The same action viewed as unitary endomorphisms for the actual Hilbert adjoint. -/
def unitaryOperators : GaugeGroup →* unitary (Module.End ℂ FullMatter) where
  toFun g := ⟨representation g, representation_mem_unitary g⟩
  map_one' := Subtype.ext representation.map_one
  map_mul' g h := Subtype.ext (representation.map_mul g h)

/-- The quotient action preserves the same inner product, by representative induction. -/
theorem effectiveRepresentation_inner (q : EffectiveGroup) (x y : FullMatter) :
    inner ℂ (SourceGlobalGaugeGroup.effectiveRepresentation q x)
      (SourceGlobalGaugeGroup.effectiveRepresentation q y) = inner ℂ x y := by
  refine Quotient.inductionOn' q ?_
  intro g
  exact representation_inner g x y

def effectiveLinearAction (q : EffectiveGroup) : FullMatter ≃ₗ[ℂ] FullMatter :=
  representationLinearEquiv SourceGlobalGaugeGroup.effectiveRepresentation q

def effectiveUnitaryAction (q : EffectiveGroup) : FullMatter ≃ₗᵢ[ℂ] FullMatter :=
  (effectiveLinearAction q).isometryOfInner (effectiveRepresentation_inner q)

@[simp] theorem effectiveUnitaryAction_apply (q : EffectiveGroup) (x : FullMatter) :
    effectiveUnitaryAction q x = SourceGlobalGaugeGroup.effectiveRepresentation q x := rfl

def effectiveUnitaryRepresentation : EffectiveGroup →* (FullMatter ≃ₗᵢ[ℂ] FullMatter) where
  toFun := effectiveUnitaryAction
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change SourceGlobalGaugeGroup.effectiveRepresentation 1 x = x
    simp only [map_one, Module.End.one_apply]
  map_mul' q r := by
    apply LinearIsometryEquiv.ext
    intro x
    change SourceGlobalGaugeGroup.effectiveRepresentation (q * r) x =
      SourceGlobalGaugeGroup.effectiveRepresentation q
        (SourceGlobalGaugeGroup.effectiveRepresentation r x)
    simp only [map_mul, Module.End.mul_apply]

@[simp] theorem effectiveUnitaryRepresentation_mk (g : GaugeGroup) :
    effectiveUnitaryRepresentation
      (QuotientGroup.mk' SourceGlobalGaugeGroup.centralSix g) = unitaryRepresentation g := by
  apply LinearIsometryEquiv.ext
  intro x
  exact congrArg (fun A : Module.End ℂ FullMatter => A x)
    (SourceGlobalGaugeGroup.effectiveRepresentation_mk g)

theorem effectiveUnitaryRepresentation_injective :
    Function.Injective effectiveUnitaryRepresentation := by
  intro q r h
  apply SourceGlobalGaugeGroup.effectiveRepresentation_injective
  apply LinearMap.ext
  intro x
  exact congrArg (fun U : FullMatter ≃ₗᵢ[ℂ] FullMatter => U x) h

theorem effectiveRepresentation_mem_unitary (q : EffectiveGroup) :
    SourceGlobalGaugeGroup.effectiveRepresentation q ∈ unitary (Module.End ℂ FullMatter) := by
  refine Quotient.inductionOn' q ?_
  intro g
  exact representation_mem_unitary g

end GeneratedFoundations.Physical.SourceGaugeUnitary
