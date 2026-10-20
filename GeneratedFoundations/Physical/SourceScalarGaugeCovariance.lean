module

public import GeneratedFoundations.Physical.SourceScalarConnector
public import GeneratedFoundations.Physical.SourceGaugeCocycle
public import GeneratedFoundations.Physical.SourceExchangeConnectorTransport
public import GeneratedFoundations.Operations.OrthonormalCoordinates
public import GeneratedFoundations.Operations.UnitaryRepresentation

/-!
# Gauge covariance and local gluing of the actual scalar connector

The complete source matter action is evaluated in its specified orthonormal
colour, spin and chiral coordinates. Its colour factor is shared by both
chiralities. The spin factor has the left frame and the vacuum-stabilized
right frame on its diagonal. This gives the conjugation law for the actual
self-adjoint connector, including its lower adjoint block.

The unique doublet consequently transforms with phase character three.
Its two columns remain related by the source pseudoreal reversal. On
overlaps the same law is invariant under the diagonal sixth-root changes
of lift, and is compatible with the already constructed matter cocycle.
All overlap statements are local; no global frame or global product-group
lift is assumed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker ComplexConjugate

namespace GeneratedFoundations.Physical.SourceScalarGaugeCovariance

open SourceChiralCarrier SourceScalarConnector ReversalRealConnector
open SourceGaugeTransport (coordinates pack unpack representation)
open SourceGaugeCocycle (LiftData CocycleOn CentralDefects unitaryTransition)

abbrev GaugeGroup := GlobalGaugeKernel.GaugeGroup

/-- These are the original labelled orthonormal coordinates, before the
six-block rearrangement or the Hermite-mode permutation. -/
def matrixCoordinates : Module.End ℂ FullMatter ≃⋆ₐ[ℂ] Matrix FullIndex FullIndex ℂ :=
  LinearMap.toMatrixOrthonormal fullBasis

export Operations.OrthonormalCoordinates (basis_equivFun_inner)

private theorem unpack_coordinates (x : FullMatter) (i : FullIndex) :
    unpack (coordinates x) i = inner ℂ (fullBasis i) x := by
  change unpack (pack (fullBasis.toBasis.equivFun x)) i = _
  rw [SourceGaugeTransport.unpack_pack]
  exact basis_equivFun_inner fullBasis x i

/-- The common colour response retains the separate three- and one-dimensional sectors. -/
def colourMatrix (g : GaugeGroup) : Matrix ColourLabel ColourLabel ℂ :=
  Matrix.fromBlocks ((g.2.2 : ℂ) • (g.1 : GlobalGaugeKernel.Mat3)) 0 0
    (((g.2.2 : ℂ) ^ 3)⁻¹ • (1 : GlobalGaugeKernel.Mat1))

def spinFrameMatrix (g : GaugeGroup) : Matrix ChiralLabel ChiralLabel ℂ :=
  Matrix.fromBlocks (g.2.1 : Mat2) 0 0
    (SourcePhaseLift.stabilizerFrame g.2.2 : Mat2)

def chiralMatrix (M : Mat2) : Matrix ChiralLabel ChiralLabel ℂ :=
  Matrix.fromBlocks 0 M M.conjTranspose 0

theorem coordinate_representation_ll (g : GaugeGroup) (c : Fin 3)
    (i : Fin 2) (d : ColourLabel) (j : ChiralLabel) :
    unpack (GlobalGaugeKernel.representation g (pack (Pi.single (d, j) 1)))
        (Sum.inl c, Sum.inl i) =
      (colourMatrix g ⊗ₖ spinFrameMatrix g) (Sum.inl c, Sum.inl i) (d, j) := by
  rw [SourceGaugeUnitary.coordinate_action_blocks]
  rcases d with d | d <;> rcases j with j | j <;>
    fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp [unpack, pack, GlobalGaugeKernel.blocks, colourMatrix, spinFrameMatrix,
      SourcePhaseLift.stabilizerFrame_matrix, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.eq_zero, Pi.single_apply, smul_eq_mul] <;>
    field_simp [Circle.coe_ne_zero g.2.2]

theorem coordinate_representation_lr (g : GaugeGroup) (c : Fin 3)
    (i : Fin 2) (d : ColourLabel) (j : ChiralLabel) :
    unpack (GlobalGaugeKernel.representation g (pack (Pi.single (d, j) 1)))
        (Sum.inl c, Sum.inr i) =
      (colourMatrix g ⊗ₖ spinFrameMatrix g) (Sum.inl c, Sum.inr i) (d, j) := by
  rw [SourceGaugeUnitary.coordinate_action_blocks]
  rcases d with d | d <;> rcases j with j | j <;>
    fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp [unpack, pack, GlobalGaugeKernel.blocks, colourMatrix, spinFrameMatrix,
      SourcePhaseLift.stabilizerFrame_matrix, Matrix.mulVec, dotProduct,
      Fin.eq_zero, Pi.single_apply, smul_eq_mul] <;>
    field_simp [Circle.coe_ne_zero g.2.2]

theorem coordinate_representation_rl (g : GaugeGroup) (c : Fin 1)
    (i : Fin 2) (d : ColourLabel) (j : ChiralLabel) :
    unpack (GlobalGaugeKernel.representation g (pack (Pi.single (d, j) 1)))
        (Sum.inr c, Sum.inl i) =
      (colourMatrix g ⊗ₖ spinFrameMatrix g) (Sum.inr c, Sum.inl i) (d, j) := by
  rw [SourceGaugeUnitary.coordinate_action_blocks]
  rcases d with d | d <;> rcases j with j | j <;>
    fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp [unpack, pack, GlobalGaugeKernel.blocks, colourMatrix, spinFrameMatrix,
      SourcePhaseLift.stabilizerFrame_matrix, Matrix.mulVec, dotProduct,
      Fin.eq_zero, Pi.single_apply, smul_eq_mul]

theorem coordinate_representation_rr (g : GaugeGroup) (c : Fin 1)
    (i : Fin 2) (d : ColourLabel) (j : ChiralLabel) :
    unpack (GlobalGaugeKernel.representation g (pack (Pi.single (d, j) 1)))
        (Sum.inr c, Sum.inr i) =
      (colourMatrix g ⊗ₖ spinFrameMatrix g) (Sum.inr c, Sum.inr i) (d, j) := by
  rw [SourceGaugeUnitary.coordinate_action_blocks]
  rcases d with d | d <;> rcases j with j | j <;>
    fin_cases d <;> fin_cases i <;> fin_cases j <;>
    simp [unpack, pack, GlobalGaugeKernel.blocks, colourMatrix, spinFrameMatrix,
      SourcePhaseLift.stabilizerFrame_matrix, Matrix.mulVec, dotProduct,
      Fin.eq_zero, Pi.single_apply, smul_eq_mul]
  field_simp [Circle.coe_ne_zero g.2.2]

theorem coordinate_representation_entry (g : GaugeGroup) (c d : ColourLabel)
    (i j : ChiralLabel) :
    unpack (GlobalGaugeKernel.representation g (pack (Pi.single (d, j) 1))) (c, i) =
      (colourMatrix g ⊗ₖ spinFrameMatrix g) (c, i) (d, j) := by
  rcases c with c | c <;> rcases i with i | i
  · exact coordinate_representation_ll g c i d j
  · exact coordinate_representation_lr g c i d j
  · exact coordinate_representation_rl g c i d j
  · exact coordinate_representation_rr g c i d j

theorem representation_matrix_entry (g : GaugeGroup) (u v : FullIndex) :
    matrixCoordinates (representation g) u v =
      unpack (GlobalGaugeKernel.representation g (pack (Pi.single v 1))) u := by
  calc
    _ = inner ℂ (fullBasis u) (representation g (fullBasis v)) :=
      LinearMap.toMatrixOrthonormal_apply_apply fullBasis (representation g) u v
    _ = unpack (coordinates (representation g (fullBasis v))) u :=
      (unpack_coordinates (representation g (fullBasis v)) u).symm
    _ = _ := congrArg (fun x : GlobalGaugeKernel.Matter => unpack x u)
      ((SourceGaugeTransport.coordinates_intertwines g (fullBasis v)).trans
        (congrArg (GlobalGaugeKernel.representation g) (SourceGaugeTransport.coordinates_basis v)))

/-- Every entry of the existing six-block representation has this tensor form. -/
theorem representation_matrix (g : GaugeGroup) :
    matrixCoordinates (representation g) = colourMatrix g ⊗ₖ spinFrameMatrix g := by
  apply Matrix.ext
  intro ⟨c, i⟩ ⟨d, j⟩
  exact (representation_matrix_entry g (c, i) (d, j)).trans
    (coordinate_representation_entry g c d i j)

theorem connector_matrix (h : Module.End ℂ SourceJointResponse.S) :
    matrixCoordinates (connector h) =
      (1 : Matrix ColourLabel ColourLabel ℂ) ⊗ₖ chiralMatrix (spinMatrixCoordinates h) := by
  ext ⟨c, i⟩ ⟨d, j⟩
  simpa only [matrixCoordinates, LinearMap.toMatrixOrthonormal_apply_apply,
    Matrix.kronecker_apply, Matrix.one_apply, chiralMatrix] using
      fullBasis_connector_entry h c d i j

theorem spinMatrixCoordinates_eq_sourceMatrix (h : Module.End ℂ SourceJointResponse.S) :
    spinMatrixCoordinates h = sourceMatrix h := by
  calc
    spinMatrixCoordinates h =
        spinMatrixCoordinates (SourceSpinIdentification.spinAction (sourceMatrix h)) :=
      congrArg spinMatrixCoordinates (spinAction_sourceMatrix h).symm
    _ = sourceMatrix h := spinMatrixCoordinates_spinAction _

private theorem spinFrameMatrix_intertwines (g : GaugeGroup) (M : Mat2) :
    spinFrameMatrix g * chiralMatrix M =
      chiralMatrix (gaugeMatrix g.2.1 g.2.2 M) * spinFrameMatrix g := by
  let L : Mat2 := g.2.1
  let R : Mat2 := Geometry.SourcePhaseLift.stabilizerFrame g.2.2
  have hL : L.conjTranspose * L = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.mem_specialUnitaryGroup_iff.mp g.2.1.property).1
  have hR : R.conjTranspose * R = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.mem_specialUnitaryGroup_iff.mp
        (Geometry.SourcePhaseLift.stabilizerFrame g.2.2).property).1
  have hupper : L * M = gaugeMatrix g.2.1 g.2.2 M * R := by
    change L * M = (L * M * R.conjTranspose) * R
    rw [mul_assoc, hR, mul_one]
  have hlower : R * M.conjTranspose =
      (gaugeMatrix g.2.1 g.2.2 M).conjTranspose * L := by
    change R * M.conjTranspose = (L * M * R.conjTranspose).conjTranspose * L
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      mul_assoc, hL, mul_one]
  change Matrix.fromBlocks L 0 0 R * Matrix.fromBlocks 0 M M.conjTranspose 0 =
    Matrix.fromBlocks 0 (gaugeMatrix g.2.1 g.2.2 M)
      (gaugeMatrix g.2.1 g.2.2 M).conjTranspose 0 * Matrix.fromBlocks L 0 0 R
  simp only [Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add]
  rw [← hupper, ← hlower]

export Operations.UnitaryRepresentation (algebraEquiv_mul_eq_of_images)

/-- Colour cancels because the same factor acts on both sides of the
connector. No special property of a coordinate sup norm is used. -/
theorem connector_intertwines (g : GaugeGroup) (h : Module.End ℂ SourceJointResponse.S) :
    representation g * connector h =
      connector (gaugeSpin g.2.1 g.2.2 h) * representation g := by
  apply algebraEquiv_mul_eq_of_images matrixCoordinates.toAlgEquiv
  change matrixCoordinates (representation g) * matrixCoordinates (connector h) =
    matrixCoordinates (connector (gaugeSpin g.2.1 g.2.2 h)) * matrixCoordinates (representation g)
  have hm : (colourMatrix g ⊗ₖ spinFrameMatrix g) *
      ((1 : Matrix ColourLabel ColourLabel ℂ) ⊗ₖ chiralMatrix (spinMatrixCoordinates h)) =
      ((1 : Matrix ColourLabel ColourLabel ℂ) ⊗ₖ
        chiralMatrix (spinMatrixCoordinates (gaugeSpin g.2.1 g.2.2 h))) *
          (colourMatrix g ⊗ₖ spinFrameMatrix g) := by
    simp only [spinMatrixCoordinates_eq_sourceMatrix, sourceMatrix_gaugeSpin]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      mul_one, one_mul, spinFrameMatrix_intertwines]
  exact (congrArg₂ (fun A B : Matrix FullIndex FullIndex ℂ => A * B)
    (representation_matrix g) (connector_matrix h)).trans
      (hm.trans (congrArg₂ (fun A B : Matrix FullIndex FullIndex ℂ => A * B)
        (connector_matrix (gaugeSpin g.2.1 g.2.2 h)) (representation_matrix g)).symm)

/-- Integer phase weight three in the primitive normalization of the full matter action. -/
def scalarAction (g : GaugeGroup) (H : Spinor) : Spinor :=
  (g.2.2 : ℂ) ^ 3 • (g.2.1 : Mat2).mulVec H

@[simp] theorem scalarAction_one (H : Spinor) : scalarAction 1 H = H := by
  simp [scalarAction]

theorem scalarAction_mul (g k : GaugeGroup) (H : Spinor) :
    scalarAction (g * k) H = scalarAction g (scalarAction k H) := by
  simp [scalarAction, mul_pow, Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul]

/-- The source lift fixes the corresponding hypercharge to one half. -/
theorem scalarAction_phase (t : ℝ) (H : Spinor) :
    scalarAction (1, 1, SourcePhaseLift.phase t) H =
      Complex.exp (((t : ℂ) * Complex.I) / 2) • H := by
  have he : (SourcePhaseLift.phase t : ℂ) ^ 3 =
      Complex.exp (((t : ℂ) * Complex.I) / 2) := by
    rw [SourcePhaseLift.phase, Circle.coe_exp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  change (SourcePhaseLift.phase t : ℂ) ^ 3 • (1 : Mat2).mulVec H = _
  rw [Matrix.one_mulVec]
  exact congrArg (fun a : ℂ => a • H) he

theorem scalarConnector_intertwines (g : GaugeGroup) (H : Spinor) :
    representation g * scalarConnector H =
      scalarConnector (scalarAction g H) * representation g := by
  simpa only [scalarConnector, scalarAction, gaugeSpin_doubletLift] using
    connector_intertwines g (doubletLift H)

/- Conjugation on the actual sixteen-dimensional Hilbert space. -/
export Operations.UnitaryRepresentation (conjugate_of_intertwines)

theorem scalarConnector_covariant (g : GaugeGroup) (H : Spinor) :
    representation g * scalarConnector H * representation g⁻¹ =
      scalarConnector (scalarAction g H) :=
  conjugate_of_intertwines representation g (scalarConnector H)
    (scalarConnector (scalarAction g H)) (scalarConnector_intertwines g H)

theorem scalarConnector_injective : Function.Injective scalarConnector := by
  intro H K h
  apply doubletLift_injective
  apply spinMatrixCoordinates.injective
  change spinMatrixCoordinates (doubletLift H) = spinMatrixCoordinates (doubletLift K)
  ext i j
  have he := congrArg (fun A : Module.End ℂ FullMatter =>
    matrixCoordinates A (Sum.inr 0, Sum.inl i) (Sum.inr 0, Sum.inr j)) h
  simpa only [scalarConnector, connector_matrix, Matrix.kronecker_apply,
    Matrix.one_apply_eq, one_mul, chiralMatrix, Matrix.fromBlocks_apply₁₂] using he

/-- The transformed first column is still the reversal of the second. -/
theorem transformed_columns (g : GaugeGroup) (H : Spinor) :
    (fun i => sourceMatrix (gaugeSpin g.2.1 g.2.2 (doubletLift H)) i 0) =
        reversal (scalarAction g H) ∧
      (fun i => sourceMatrix (gaugeSpin g.2.1 g.2.2 (doubletLift H)) i 1) =
        scalarAction g H := by
  simp only [gaugeSpin_doubletLift, sourceMatrix_doubletLift]
  exact ⟨connectorOfDoublet_firstColumn _, funext (connectorOfDoublet_secondColumn _)⟩

/-- The common sixth-root ambiguity of a matter frame is invisible to its
elementary connector as well. -/
theorem scalarAction_eq_of_unitary_eq {g k : GaugeGroup}
    (h : SourceGaugeUnitary.unitaryRepresentation g =
      SourceGaugeUnitary.unitaryRepresentation k) (H : Spinor) :
    scalarAction g H = scalarAction k H := by
  have hrep : representation g = representation k := by
    have hu : SourceGaugeUnitary.unitaryAction g = SourceGaugeUnitary.unitaryAction k := h
    apply LinearMap.ext
    intro x
    exact (SourceGaugeUnitary.unitaryAction_apply g x).symm.trans
      ((congrArg (fun U : FullMatter ≃ₗᵢ[ℂ] FullMatter => U x) hu).trans
        (SourceGaugeUnitary.unitaryAction_apply k x))
  have hinv : representation g⁻¹ = representation k⁻¹ := by
    exact (SourceGaugeUnitary.representation_adjoint g).symm.trans
      ((congrArg LinearMap.adjoint hrep).trans (SourceGaugeUnitary.representation_adjoint k))
  apply scalarConnector_injective
  calc
    scalarConnector (scalarAction g H) =
        representation g * scalarConnector H * representation g⁻¹ :=
      (scalarConnector_covariant g H).symm
    _ = representation k * scalarConnector H * representation k⁻¹ :=
      congrArg₂ (fun A B : Module.End ℂ FullMatter => A * scalarConnector H * B) hrep hinv
    _ = scalarConnector (scalarAction k H) := scalarConnector_covariant k H

theorem scalarAction_central_relift (z : GlobalGaugeKernel.sixthRoots)
    (g : GaugeGroup) (H : Spinor) :
    scalarAction (GlobalGaugeKernel.centralEmbedding z * g) H = scalarAction g H := by
  apply scalarAction_eq_of_unitary_eq
  exact (map_mul SourceGaugeUnitary.unitaryRepresentation
    (GlobalGaugeKernel.centralEmbedding z) g).trans
      ((congrArg (fun U : FullMatter ≃ₗᵢ[ℂ] FullMatter =>
        U * SourceGaugeUnitary.unitaryRepresentation g) (SourceGaugeCocycle.unitary_central z)).trans
          (one_mul _))

section Local

variable {ι X : Type*}

/-- Components use the same passive convention as matter sections:
chart-j components are transported to chart-i components. -/
def CompatibleDoublets (U : ι → Set X) (g : LiftData ι X) (H : ι → X → Spinor) : Prop :=
  ∀ i j x, x ∈ U i → x ∈ U j → H i x = scalarAction (g i j x) (H j x)

def CompatibleConnectors (U : ι → Set X) (g : LiftData ι X)
    (C : ι → X → Module.End ℂ FullMatter) : Prop :=
  ∀ i j x, x ∈ U i → x ∈ U j →
    C i x = representation (g i j x) * C j x * representation (g i j x)⁻¹

/-- Local operator gluing is equivalent to the unique doublet gluing law. -/
theorem compatibleConnectors_iff_doublets (U : ι → Set X) (g : LiftData ι X)
    (H : ι → X → Spinor) :
    CompatibleConnectors U g (fun i x => scalarConnector (H i x)) ↔
      CompatibleDoublets U g H := by
  unfold CompatibleConnectors CompatibleDoublets
  simp only [scalarConnector_covariant, scalarConnector_injective.eq_iff]

/-- Arbitrary local elementary blocks determine the doublets; their
overlap law follows from the operator gluing law. Uniqueness is asserted
on the actual patches, without constraining unused values outside them. -/
theorem local_elementary_doublets (U : ι → Set X) (g : LiftData ι X)
    (A : ι → X → Module.End ℂ SourceMinimalRepresentation.SourceCarrier)
    (hA : ∀ i x, x ∈ U i → SourceExchangeConnectorTransport.SplitElementary (A i x))
    (hglue : CompatibleConnectors U g
      (fun i x => SourceExchangeConnectorTransport.chiralConnector (A i x))) :
    ∃ H : ι → X → Spinor,
      (∀ i x, x ∈ U i →
        SourceExchangeConnectorTransport.chiralConnector (A i x) = scalarConnector (H i x)) ∧
      CompatibleDoublets U g H ∧
      ∀ K : ι → X → Spinor,
        (∀ i x, x ∈ U i →
          SourceExchangeConnectorTransport.chiralConnector (A i x) = scalarConnector (K i x)) →
        ∀ i x, x ∈ U i → K i x = H i x := by
  classical
  have hex (i : ι) (x : X) (hx : x ∈ U i) :
      ∃ H : Spinor, A i x = spinOnSource (doubletLift H) :=
    ((SourceExchangeConnectorTransport.splitElementary_iff_unique_doublet (A i x)).mp
      (hA i x hx)).exists
  let H : ι → X → Spinor := fun i x =>
    if hx : x ∈ U i then Classical.choose (hex i x hx) else 0
  have hH (i : ι) (x : X) (hx : x ∈ U i) : A i x = spinOnSource (doubletLift (H i x)) := by
    simp only [H, dite_eq_left hx]
    exact Classical.choose_spec (hex i x hx)
  have hC (i : ι) (x : X) (hx : x ∈ U i) :
      SourceExchangeConnectorTransport.chiralConnector (A i x) = scalarConnector (H i x) := by
    rw [hH i x hx]
    simp only [SourceExchangeConnectorTransport.chiralConnector, scalarConnector,
      connector, spinOnSource_adjoint]
  refine ⟨H, hC, ?_, ?_⟩
  · intro i j x hi hj
    apply scalarConnector_injective
    calc
      scalarConnector (H i x) =
          SourceExchangeConnectorTransport.chiralConnector (A i x) := (hC i x hi).symm
      _ = representation (g i j x) *
          SourceExchangeConnectorTransport.chiralConnector (A j x) *
            representation (g i j x)⁻¹ := hglue i j x hi hj
      _ = scalarConnector (scalarAction (g i j x) (H j x)) :=
        (congrArg (fun C : Module.End ℂ FullMatter =>
          representation (g i j x) * C * representation (g i j x)⁻¹) (hC j x hj)).trans
            (scalarConnector_covariant (g i j x) (H j x))
  · intro K hK i x hx
    exact scalarConnector_injective ((hK i x hx).symm.trans (hC i x hx))

/-- A product-group lift can have a nontrivial central triple defect. -/
theorem scalarAction_two_routes {U : ι → Set X} {g : LiftData ι X}
    (hg : CentralDefects U g) (i j k : ι) (x : X)
    (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) (H : Spinor) :
    scalarAction (g i j x) (scalarAction (g j k x) H) = scalarAction (g i k x) H := by
  rw [← scalarAction_mul]
  apply scalarAction_eq_of_unitary_eq
  rw [map_mul]
  exact (SourceGaugeCocycle.centralDefects_iff_unitaryCocycle U g).mp hg
    i j k x hi hj hk

theorem centralRelift_doublets_iff (U : ι → Set X)
    (z : ι → ι → X → GlobalGaugeKernel.sixthRoots) (g : LiftData ι X)
    (H : ι → X → Spinor) :
    CompatibleDoublets U (SourceGaugeCocycle.centralRelift z g) H ↔
      CompatibleDoublets U g H := by
  simp only [CompatibleDoublets, SourceGaugeCocycle.centralRelift,
    scalarAction_central_relift]

/-- Applying a compatible connector preserves the actual matter gluing law. -/
theorem scalarConnector_unitary_intertwines (g : GaugeGroup) (H : Spinor) (s : FullMatter) :
    scalarConnector (scalarAction g H) (SourceGaugeUnitary.unitaryRepresentation g s) =
      SourceGaugeUnitary.unitaryRepresentation g (scalarConnector H s) :=
  (LinearMap.congr_fun (scalarConnector_intertwines g H) s).symm

theorem compatibleDoublets_apply_sections {U : ι → Set X} {g : LiftData ι X}
    {H : ι → X → Spinor} {s : ι → X → FullMatter}
    (hH : CompatibleDoublets U g H)
    (hs : SourceGaugeCocycle.CompatibleSections U (unitaryTransition g) s) :
    SourceGaugeCocycle.CompatibleSections U (unitaryTransition g)
      (fun i x => scalarConnector (H i x) (s i x)) := by
  intro i j x hi hj
  change scalarConnector (H i x) (s i x) =
    unitaryTransition g i j x (scalarConnector (H j x) (s j x))
  exact (congrArg (fun K : Spinor => scalarConnector K (s i x)) (hH i j x hi hj)).trans
    ((congrArg (scalarConnector (scalarAction (g i j x) (H j x))) (hs i j x hi hj)).trans
      (scalarConnector_unitary_intertwines (g i j x) (H j x) (s j x)))

end Local

end GeneratedFoundations.Physical.SourceScalarGaugeCovariance
