module

public import GeneratedFoundations.Physical.SourceMinimalRepresentation
public import GeneratedFoundations.Physical.SourceCliffordConnector
public import GeneratedFoundations.Physical.SourceSpinIdentification
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The two labelled source matter carriers

The two chiral labels are attached to copies of the actual orthogonal sum
`(W ⊗ S) ⊕ (L ⊗ S)`.  The spin response is the same `I ⊗ h` in both
retained colour sectors.  Its off-diagonal extension has adjoint blocks,
is self-adjoint and is odd for the left/right grading.

All coordinates below are orthonormal coordinates of the source Hilbert
spaces.  Tensor factors and the retained three-plus-one split remain
visible in their indices.  A specified permutation relates these indices
to the sixteen Hermite states of the four-colour Clifford corner.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct BigOperators ComplexConjugate Kronecker Quaternion
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteFamily
open GeneratedFoundations.Operations.FiniteHermiteCorner

namespace GeneratedFoundations.Physical.SourceChiralCarrier

open SourceJointResponse SourceMinimalRepresentation

/-- Two independently labelled copies of the actual minimal source carrier. -/
abbrev FullMatter := WithLp 2 (SourceCarrier × SourceCarrier)

def fullMatterCoordinates : (SourceCarrier × SourceCarrier) ≃ₗ[ℂ] FullMatter :=
  (WithLp.linearEquiv 2 ℂ (SourceCarrier × SourceCarrier)).symm

theorem fullMatter_finrank : Module.finrank ℂ FullMatter = 16 := by
  rw [← fullMatterCoordinates.finrank_eq, Module.finrank_prod]
  simp [sourceCarrier_finrank]

def leftInclusion : SourceCarrier →ₗ[ℂ] FullMatter :=
  fullMatterCoordinates.toLinearMap.comp (LinearMap.inl ℂ SourceCarrier SourceCarrier)

def rightInclusion : SourceCarrier →ₗ[ℂ] FullMatter :=
  fullMatterCoordinates.toLinearMap.comp (LinearMap.inr ℂ SourceCarrier SourceCarrier)

@[simp] theorem leftInclusion_apply (x : SourceCarrier) :
    WithLp.ofLp (leftInclusion x) = (x, 0) := rfl

@[simp] theorem rightInclusion_apply (x : SourceCarrier) :
    WithLp.ofLp (rightInclusion x) = (0, x) := rfl

theorem left_right_inner (x y : SourceCarrier) :
    inner ℂ (leftInclusion x) (rightInclusion y) = 0 := by
  simp [WithLp.prod_inner_apply]

theorem leftInclusion_inner (x y : SourceCarrier) :
    inner ℂ (leftInclusion x) (leftInclusion y) = inner ℂ x y := by
  simp [WithLp.prod_inner_apply]

theorem rightInclusion_inner (x y : SourceCarrier) :
    inner ℂ (rightInclusion x) (rightInclusion y) = inner ℂ x y := by
  simp [WithLp.prod_inner_apply]

def diagonalBlocks (A B : Module.End ℂ SourceCarrier) : Module.End ℂ FullMatter :=
  fullMatterCoordinates.conjAlgEquiv ℂ (LinearMap.prodMap A B)

@[simp] theorem diagonalBlocks_apply (A B : Module.End ℂ SourceCarrier) (x : FullMatter) :
    WithLp.ofLp (diagonalBlocks A B x) =
      (A (WithLp.ofLp x).1, B (WithLp.ofLp x).2) := rfl

theorem diagonalBlocks_mul (A B C D : Module.End ℂ SourceCarrier) :
    diagonalBlocks A B * diagonalBlocks C D = diagonalBlocks (A * C) (B * D) := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

@[simp] theorem diagonalBlocks_one : diagonalBlocks 1 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

theorem diagonalBlocks_adjoint (A B : Module.End ℂ SourceCarrier) :
    (diagonalBlocks A B).adjoint = diagonalBlocks A.adjoint B.adjoint := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (A.adjoint (WithLp.ofLp x).1) (WithLp.ofLp y).1 +
      inner ℂ (B.adjoint (WithLp.ofLp x).2) (WithLp.ofLp y).2 =
    inner ℂ (WithLp.ofLp x).1 (A (WithLp.ofLp y).1) +
      inner ℂ (WithLp.ofLp x).2 (B (WithLp.ofLp y).2)
  simp only [LinearMap.adjoint_inner_left]

def leftProjection : Module.End ℂ FullMatter := diagonalBlocks 1 0
def rightProjection : Module.End ℂ FullMatter := diagonalBlocks 0 1

@[simp] theorem leftProjection_apply (x : FullMatter) :
    WithLp.ofLp (leftProjection x) = ((WithLp.ofLp x).1, 0) := rfl

@[simp] theorem rightProjection_apply (x : FullMatter) :
    WithLp.ofLp (rightProjection x) = (0, (WithLp.ofLp x).2) := rfl

theorem leftProjection_square : leftProjection * leftProjection = leftProjection := by
  simp [leftProjection, diagonalBlocks_mul]

theorem rightProjection_square : rightProjection * rightProjection = rightProjection := by
  simp [rightProjection, diagonalBlocks_mul]

theorem leftProjection_mul_rightProjection : leftProjection * rightProjection = 0 := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

theorem rightProjection_mul_leftProjection : rightProjection * leftProjection = 0 := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

theorem projections_sum : leftProjection + rightProjection = 1 := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  change ((WithLp.ofLp x).1 + 0, 0 + (WithLp.ofLp x).2) = WithLp.ofLp x
  simp only [add_zero, zero_add]

theorem leftProjection_adjoint : leftProjection.adjoint = leftProjection := by
  simp [leftProjection, diagonalBlocks_adjoint]

theorem rightProjection_adjoint : rightProjection.adjoint = rightProjection := by
  simp [rightProjection, diagonalBlocks_adjoint]

def exchange : Module.End ℂ FullMatter :=
  (fullMatterCoordinates.symm.trans
    ((LinearEquiv.prodComm ℂ SourceCarrier SourceCarrier).trans fullMatterCoordinates)).toLinearMap

@[simp] theorem exchange_apply (x : FullMatter) :
    WithLp.ofLp (exchange x) = ((WithLp.ofLp x).2, (WithLp.ofLp x).1) := rfl

theorem exchange_square : exchange * exchange = 1 := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

theorem exchange_adjoint : exchange.adjoint = exchange := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (WithLp.ofLp x).2 (WithLp.ofLp y).1 +
      inner ℂ (WithLp.ofLp x).1 (WithLp.ofLp y).2 =
    inner ℂ (WithLp.ofLp x).1 (WithLp.ofLp y).2 +
      inner ℂ (WithLp.ofLp x).2 (WithLp.ofLp y).1
  exact add_comm _ _

theorem exchange_diagonalBlocks (A B : Module.End ℂ SourceCarrier) :
    exchange * diagonalBlocks A B = diagonalBlocks B A * exchange := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

def grading : Module.End ℂ FullMatter := diagonalBlocks 1 (-1)

@[simp] theorem grading_apply (x : FullMatter) :
    WithLp.ofLp (grading x) = ((WithLp.ofLp x).1, -(WithLp.ofLp x).2) := rfl

theorem grading_eq_projections : grading = leftProjection - rightProjection := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  change ((WithLp.ofLp x).1, -(WithLp.ofLp x).2) =
    ((WithLp.ofLp x).1 - 0, 0 - (WithLp.ofLp x).2)
  simp

theorem grading_square : grading * grading = 1 := by
  simp [grading, diagonalBlocks_mul]

theorem grading_adjoint : grading.adjoint = grading := by
  simp [grading, diagonalBlocks_adjoint]

/-- The existing common spin response on the actual colour-spin and scalar-spin factors. -/
def spinOnSource : Module.End ℂ S →ₐ[ℂ] Module.End ℂ SourceCarrier :=
  sourceCarrierRepresentation.comp spinResponse

@[simp] theorem spinOnSource_apply (h : Module.End ℂ S) (x : SourceCarrier) :
    WithLp.ofLp (spinOnSource h x) =
      (TensorProduct.map 1 h (WithLp.ofLp x).1,
        TensorProduct.map 1 h (WithLp.ofLp x).2) := rfl

theorem sourceCarrierRepresentation_adjoint (A : JointEnd) :
    (sourceCarrierRepresentation A).adjoint = sourceCarrierRepresentation (star A) := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simpa only [star_star] using sourceCarrierRepresentation_adjointCompatible (star A) x y

theorem spinResponse_adjoint (h : Module.End ℂ S) :
    star (spinResponse h) = spinResponse h.adjoint := by
  apply Prod.ext
  · change (TensorProduct.map (1 : Module.End ℂ W) h).adjoint =
      TensorProduct.map 1 h.adjoint
    simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  · change (TensorProduct.map (1 : Module.End ℂ L) h).adjoint =
      TensorProduct.map 1 h.adjoint
    simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]

theorem spinOnSource_adjoint (h : Module.End ℂ S) :
    (spinOnSource h).adjoint = spinOnSource h.adjoint :=
  (sourceCarrierRepresentation_adjoint (spinResponse h)).trans
    (congrArg sourceCarrierRepresentation (spinResponse_adjoint h))

def commonSpin (h : Module.End ℂ S) : Module.End ℂ FullMatter :=
  diagonalBlocks (spinOnSource h) (spinOnSource h)

/-- The upper block is `I ⊗ h`; the lower block is its actual Hilbert adjoint. -/
def connector (h : Module.End ℂ S) : Module.End ℂ FullMatter :=
  diagonalBlocks (spinOnSource h) (spinOnSource h.adjoint) * exchange

@[simp] theorem connector_apply (h : Module.End ℂ S) (x : FullMatter) :
    WithLp.ofLp (connector h x) =
      (spinOnSource h (WithLp.ofLp x).2,
        spinOnSource h.adjoint (WithLp.ofLp x).1) := rfl

theorem connector_adjoint (h : Module.End ℂ S) : (connector h).adjoint = connector h := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change inner ℂ (spinOnSource h (WithLp.ofLp x).2) (WithLp.ofLp y).1 +
      inner ℂ (spinOnSource h.adjoint (WithLp.ofLp x).1) (WithLp.ofLp y).2 =
    inner ℂ (WithLp.ofLp x).1 (spinOnSource h (WithLp.ofLp y).2) +
      inner ℂ (WithLp.ofLp x).2 (spinOnSource h.adjoint (WithLp.ofLp y).1)
  simp only [← spinOnSource_adjoint, LinearMap.adjoint_inner_left,
    LinearMap.adjoint_inner_right]
  exact add_comm _ _

theorem connector_isSelfAdjoint (h : Module.End ℂ S) : IsSelfAdjoint (connector h) :=
  LinearMap.isSelfAdjoint_iff'.mpr (connector_adjoint h)

theorem connector_odd (h : Module.End ℂ S) :
    grading * connector h + connector h * grading = 0 := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  change (spinOnSource h (WithLp.ofLp x).2 + spinOnSource h (-(WithLp.ofLp x).2),
    -(spinOnSource h.adjoint (WithLp.ofLp x).1) +
      spinOnSource h.adjoint (WithLp.ofLp x).1) = (0, 0)
  simp

theorem connector_square (h : Module.End ℂ S) :
    connector h * connector h =
      diagonalBlocks (spinOnSource (h * h.adjoint)) (spinOnSource (h.adjoint * h)) := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  exact Prod.ext
    (LinearMap.congr_fun (map_mul spinOnSource h h.adjoint) (WithLp.ofLp x).1).symm
    (LinearMap.congr_fun (map_mul spinOnSource h.adjoint h) (WithLp.ofLp x).2).symm

theorem connector_square_of_unitary (h : Module.End ℂ S)
    (hl : h * h.adjoint = 1) (hr : h.adjoint * h = 1) :
    connector h * connector h = 1 := by
  calc
    connector h * connector h =
        diagonalBlocks (spinOnSource (h * h.adjoint)) (spinOnSource (h.adjoint * h)) :=
      connector_square h
    _ = diagonalBlocks (spinOnSource 1) (spinOnSource 1) :=
      congrArg₂ diagonalBlocks (congrArg spinOnSource hl) (congrArg spinOnSource hr)
    _ = diagonalBlocks 1 1 :=
      congrArg₂ diagonalBlocks (map_one spinOnSource) (map_one spinOnSource)
    _ = 1 := diagonalBlocks_one

theorem exchange_eq_connector_one : exchange = connector 1 := by
  simp [connector]

theorem connector_left (h : Module.End ℂ S) (x : SourceCarrier) :
    connector h (leftInclusion x) = rightInclusion (spinOnSource h.adjoint x) := by
  apply WithLp.ofLp_injective 2
  simp

theorem connector_right (h : Module.End ℂ S) (x : SourceCarrier) :
    connector h (rightInclusion x) = leftInclusion (spinOnSource h x) := by
  apply WithLp.ofLp_injective 2
  simp

theorem right_left_inner (x y : SourceCarrier) :
    inner ℂ (rightInclusion x) (leftInclusion y) = 0 := by
  simp [WithLp.prod_inner_apply]

theorem grading_left (x : SourceCarrier) : grading (leftInclusion x) = leftInclusion x := by
  apply WithLp.ofLp_injective 2
  simp

theorem grading_right (x : SourceCarrier) : grading (rightInclusion x) = -rightInclusion x := by
  apply WithLp.ofLp_injective 2
  simp [WithLp.ofLp_neg]

/-- The colour and retained-line coordinates are chosen separately. -/
def colourBasis : OrthonormalBasis (Fin 3) ℂ W :=
  (stdOrthonormalBasis ℂ W).reindex (finCongr (hilbertCarrier_finrank 2))

def lineBasis : OrthonormalBasis (Fin 1) ℂ L :=
  (stdOrthonormalBasis ℂ L).reindex (finCongr (hilbertCarrier_finrank 0))

/-- This is the source-normalized degree-one basis, including its vacuum phase convention. -/
def spinBasis : OrthonormalBasis (Fin 2) ℂ S := SourceSpinIdentification.spinBasis

abbrev ColourLabel := Fin 3 ⊕ Fin 1
abbrev SpinLabel := Fin 2
abbrev ChiralLabel := SpinLabel ⊕ SpinLabel
abbrev SourceIndex := ColourLabel × SpinLabel
abbrev FullIndex := ColourLabel × ChiralLabel

/-- First form the two tensor bases, then put the colour label before spin. -/
def sourceBasis : OrthonormalBasis SourceIndex ℂ SourceCarrier :=
  ((colourBasis.tensorProduct spinBasis).prod (lineBasis.tensorProduct spinBasis)).reindex
    (Equiv.sumProdDistrib (Fin 3) (Fin 1) SpinLabel).symm

@[simp] theorem sourceBasis_coloured (c : Fin 3) (s : SpinLabel) :
    sourceBasis (Sum.inl c, s) = WithLp.toLp 2 (colourBasis c ⊗ₜ[ℂ] spinBasis s, 0) := by
  simp [sourceBasis, OrthonormalBasis.reindex_apply, OrthonormalBasis.tensorProduct_apply]

@[simp] theorem sourceBasis_scalar (c : Fin 1) (s : SpinLabel) :
    sourceBasis (Sum.inr c, s) = WithLp.toLp 2 (0, lineBasis c ⊗ₜ[ℂ] spinBasis s) := by
  simp [sourceBasis, OrthonormalBasis.reindex_apply, OrthonormalBasis.tensorProduct_apply]

/-- The outer chiral label is moved next to spin without changing any tensor factor. -/
def fullBasis : OrthonormalBasis FullIndex ℂ FullMatter :=
  (sourceBasis.prod sourceBasis).reindex
    (Equiv.prodSumDistrib ColourLabel SpinLabel SpinLabel).symm

@[simp] theorem fullBasis_left (c : ColourLabel) (s : SpinLabel) :
    fullBasis (c, Sum.inl s) = leftInclusion (sourceBasis (c, s)) := by
  simp [fullBasis, OrthonormalBasis.reindex_apply, leftInclusion, fullMatterCoordinates]

@[simp] theorem fullBasis_right (c : ColourLabel) (s : SpinLabel) :
    fullBasis (c, Sum.inr s) = rightInclusion (sourceBasis (c, s)) := by
  simp [fullBasis, OrthonormalBasis.reindex_apply, rightInclusion, fullMatterCoordinates]

def sourceCoordinates : SourceCarrier ≃ₗᵢ[ℂ] EuclideanSpace ℂ SourceIndex := sourceBasis.repr
def fullCoordinates : FullMatter ≃ₗᵢ[ℂ] EuclideanSpace ℂ FullIndex := fullBasis.repr

def spinMatrixCoordinates : Module.End ℂ S ≃⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.toMatrixOrthonormal spinBasis

theorem spinMatrixCoordinates_apply (h : Module.End ℂ S) (i j : Fin 2) :
    spinMatrixCoordinates h i j = inner ℂ (spinBasis i) (h (spinBasis j)) :=
  LinearMap.toMatrixOrthonormal_apply_apply spinBasis h i j

theorem spinMatrixCoordinates_adjoint (h : Module.End ℂ S) :
    spinMatrixCoordinates h.adjoint = (spinMatrixCoordinates h).conjTranspose := by
  change spinMatrixCoordinates (star h) = star (spinMatrixCoordinates h)
  exact map_star spinMatrixCoordinates h

/-- These matrix coordinates use the same phase frame as the actual Gaussian control. -/
theorem spinMatrixCoordinates_spinAction (M : Matrix (Fin 2) (Fin 2) ℂ) :
    spinMatrixCoordinates (SourceSpinIdentification.spinAction M) = M :=
  SourceSpinIdentification.spinAction_matrix M

theorem spinMatrixCoordinates_sourceOperator
    (U : Operations.SourceSpinCornerGroup.SU2) :
    spinMatrixCoordinates (sourceOperator 1 U) =
      (U : Operations.SourceSpinCorner.Mat2) := by
  rw [← SourceSpinIdentification.spinAction_sourceOperator]
  exact spinMatrixCoordinates_spinAction _

theorem sourceBasis_spin_entry (h : Module.End ℂ S)
    (c d : ColourLabel) (i j : SpinLabel) :
    inner ℂ (sourceBasis (c, i)) (spinOnSource h (sourceBasis (d, j))) =
      (if c = d then 1 else 0) * spinMatrixCoordinates h i j := by
  cases c <;> cases d <;>
    simp [WithLp.prod_inner_apply, spinMatrixCoordinates_apply,
      OrthonormalBasis.inner_eq_ite, TensorProduct.inner_tmul]

/-- The common `I ⊗ h` is visible entry by entry on both original tensor sectors. -/
theorem fullBasis_connector_entry (h : Module.End ℂ S)
    (c d : ColourLabel) (i j : ChiralLabel) :
    inner ℂ (fullBasis (c, i)) (connector h (fullBasis (d, j))) =
      (if c = d then 1 else 0) *
        (Matrix.fromBlocks 0 (spinMatrixCoordinates h)
          (spinMatrixCoordinates h).conjTranspose 0) i j := by
  cases i <;> cases j <;>
    simp only [fullBasis_left, fullBasis_right, connector_left, connector_right,
      left_right_inner, right_left_inner, leftInclusion_inner, rightInclusion_inner,
      sourceBasis_spin_entry, spinMatrixCoordinates_adjoint,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, mul_zero]

theorem fullBasis_grading_entry (c d : ColourLabel) (i j : ChiralLabel) :
    inner ℂ (fullBasis (c, i)) (grading (fullBasis (d, j))) =
      (if c = d then 1 else 0) * SourceCliffordConnector.grading i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [fullBasis_left, fullBasis_right, grading_left, grading_right,
      inner_neg_right, left_right_inner, right_left_inner, leftInclusion_inner,
      rightInclusion_inner, OrthonormalBasis.inner_eq_ite,
      SourceCliffordConnector.grading, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply,
      Matrix.neg_apply, mul_zero, neg_zero] <;>
    by_cases hcd : c = d <;> by_cases hij : i = j <;> simp [hcd, hij]

/-- The explicit three-plus-one and left/right permutation used by the Hermite corner. -/
def colourChiralEquiv : FullIndex ≃ SourceCliffordConnector.ColourIndex 4 :=
  Equiv.prodCongr finSumFinEquiv (Equiv.refl ChiralLabel)

def hermiteBasis : OrthonormalBasis (SourceCliffordConnector.ColourIndex 4) ℂ FullMatter :=
  fullBasis.reindex colourChiralEquiv

theorem hermiteBasis_reindexed (i : FullIndex) :
    hermiteBasis (colourChiralEquiv i) = fullBasis i := by
  simp [hermiteBasis, OrthonormalBasis.reindex_apply]

theorem hermiteBasis_pair (c : Fin 4) (i : ChiralLabel) :
    hermiteBasis (c, i) = fullBasis (finSumFinEquiv.symm c, i) :=
  OrthonormalBasis.reindex_apply fullBasis colourChiralEquiv (c, i)

def fullMatrixCoordinates : Module.End ℂ FullMatter ≃⋆ₐ[ℂ]
    SourceCliffordConnector.ColourMatrix 4 := LinearMap.toMatrixOrthonormal hermiteBasis

def connectorMatrix (h : Module.End ℂ S) : SourceCliffordConnector.ColourMatrix 4 :=
  (1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ
    Matrix.fromBlocks 0 (spinMatrixCoordinates h) (spinMatrixCoordinates h).conjTranspose 0

theorem fullMatrixCoordinates_connector (h : Module.End ℂ S) :
    fullMatrixCoordinates (connector h) = connectorMatrix h := by
  ext ⟨c, i⟩ ⟨d, j⟩
  rw [show fullMatrixCoordinates (connector h) (c, i) (d, j) =
    inner ℂ (hermiteBasis (c, i)) (connector h (hermiteBasis (d, j))) from
      LinearMap.toMatrixOrthonormal_apply_apply hermiteBasis (connector h) (c, i) (d, j)]
  rw [hermiteBasis_pair, hermiteBasis_pair, fullBasis_connector_entry]
  simp only [finSumFinEquiv.symm.injective.eq_iff, connectorMatrix,
    Matrix.kronecker_apply, Matrix.one_apply]

theorem fullMatrixCoordinates_grading :
    fullMatrixCoordinates grading = SourceCliffordConnector.colourGrading 4 := by
  ext ⟨c, i⟩ ⟨d, j⟩
  rw [show fullMatrixCoordinates grading (c, i) (d, j) =
    inner ℂ (hermiteBasis (c, i)) (grading (hermiteBasis (d, j))) from
      LinearMap.toMatrixOrthonormal_apply_apply hermiteBasis grading (c, i) (d, j)]
  rw [hermiteBasis_pair, hermiteBasis_pair, fullBasis_grading_entry]
  simp only [finSumFinEquiv.symm.injective.eq_iff, SourceCliffordConnector.colourGrading,
    Matrix.kronecker_apply, Matrix.one_apply]

/-- The quaternion matrix acts on the actual source spin Hilbert space through its fixed basis. -/
def quaternionSpin (q : ℍ) : Module.End ℂ S :=
  spinMatrixCoordinates.symm (Geometry.SourceQuaternionAmplitude.matrixMap q)

theorem quaternionSpin_eq_sourceAction (q : ℍ) :
    quaternionSpin q = SourceSpinIdentification.spinAction
      (Geometry.SourceQuaternionAmplitude.matrixMap q) := by
  apply spinMatrixCoordinates.injective
  exact (spinMatrixCoordinates.apply_symm_apply
    (Geometry.SourceQuaternionAmplitude.matrixMap q)).trans
      (spinMatrixCoordinates_spinAction (Geometry.SourceQuaternionAmplitude.matrixMap q)).symm

theorem fullMatrixCoordinates_quaternion (q : ℍ) :
    fullMatrixCoordinates (connector (quaternionSpin q)) =
      SourceCliffordConnector.colourClifford 4 q := by
  rw [fullMatrixCoordinates_connector]
  simp [connectorMatrix, quaternionSpin, SourceCliffordConnector.colourClifford,
    SourceCliffordConnector.clifford]

theorem quaternionConnector_square (q : ℍ) :
    connector (quaternionSpin q) * connector (quaternionSpin q) =
      ((Quaternion.normSq q : ℝ) : ℂ) • (1 : Module.End ℂ FullMatter) := by
  apply fullMatrixCoordinates.injective
  change fullMatrixCoordinates (connector (quaternionSpin q) * connector (quaternionSpin q)) =
    fullMatrixCoordinates (((Quaternion.normSq q : ℝ) : ℂ) • (1 : Module.End ℂ FullMatter))
  have hs : fullMatrixCoordinates (((Quaternion.normSq q : ℝ) : ℂ) •
      (1 : Module.End ℂ FullMatter)) =
        ((Quaternion.normSq q : ℝ) : ℂ) • (1 : SourceCliffordConnector.ColourMatrix 4) :=
    (map_smul fullMatrixCoordinates.toAlgEquiv.toLinearMap
      ((Quaternion.normSq q : ℝ) : ℂ) (1 : Module.End ℂ FullMatter)).trans
        (congrArg (fun M : SourceCliffordConnector.ColourMatrix 4 =>
          ((Quaternion.normSq q : ℝ) : ℂ) • M) (map_one fullMatrixCoordinates))
  calc
    fullMatrixCoordinates (connector (quaternionSpin q) * connector (quaternionSpin q)) =
        fullMatrixCoordinates (connector (quaternionSpin q)) *
          fullMatrixCoordinates (connector (quaternionSpin q)) := map_mul fullMatrixCoordinates _ _
    _ = SourceCliffordConnector.colourClifford 4 q *
        SourceCliffordConnector.colourClifford 4 q :=
      congrArg₂ (· * ·) (fullMatrixCoordinates_quaternion q) (fullMatrixCoordinates_quaternion q)
    _ = ((Quaternion.normSq q : ℝ) : ℂ) • (1 : SourceCliffordConnector.ColourMatrix 4) :=
      (SourceCliffordConnector.colourClifford_square 4 q).trans
        (RCLike.real_smul_eq_coe_smul (K := ℂ) (Quaternion.normSq q)
          (1 : SourceCliffordConnector.ColourMatrix 4))
    _ = _ := hs.symm

/-- This map sends each specified tensor/chiral coordinate to its actual generated Hermite state. -/
def hermiteLinear {b : ℝ} (hb : 0 < b) : FullMatter →ₗ[ℂ] ComplexL2 :=
  hermiteBasis.toBasis.constr ℂ
    (fun i => state hb (SourceCliffordConnector.sourceMode i))

theorem orthonormal_constr_basis {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : OrthonormalBasis ι ℂ E)
    (v : ι → F) (i : ι) : e.toBasis.constr ℂ v (e i) = v i :=
  e.toBasis.constr_basis ℂ v i

@[simp] theorem hermiteLinear_basis {b : ℝ} (hb : 0 < b)
    (i : SourceCliffordConnector.ColourIndex 4) :
    hermiteLinear hb (hermiteBasis i) = state hb (SourceCliffordConnector.sourceMode i) := by
  exact orthonormal_constr_basis hermiteBasis
    (fun j => state hb (SourceCliffordConnector.sourceMode j)) i

theorem hermiteLinear_orthonormal {b : ℝ} (hb : 0 < b) :
    Orthonormal ℂ (hermiteLinear hb ∘ hermiteBasis) := by
  have h := (state_orthonormal hb).comp (SourceCliffordConnector.sourceMode (d := 4))
    (SourceCliffordConnector.sourceMode_injective 4)
  simpa only [Function.comp_def, hermiteLinear_basis] using h

def orthonormalLinearIsometry {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : OrthonormalBasis ι ℂ E) (f : E →ₗ[ℂ] F)
    (hf : Orthonormal ℂ (f ∘ e)) : E →ₗᵢ[ℂ] F :=
  f.isometryOfOrthonormal (v := e.toBasis) e.orthonormal hf

def hermiteIsometry {b : ℝ} (hb : 0 < b) : FullMatter →ₗᵢ[ℂ] ComplexL2 :=
  orthonormalLinearIsometry hermiteBasis (hermiteLinear hb) (hermiteLinear_orthonormal hb)

@[simp] theorem hermiteIsometry_basis {b : ℝ} (hb : 0 < b)
    (i : SourceCliffordConnector.ColourIndex 4) :
    hermiteIsometry hb (hermiteBasis i) = state hb (SourceCliffordConnector.sourceMode i) :=
  hermiteLinear_basis hb i

theorem hermiteIsometry_fullBasis {b : ℝ} (hb : 0 < b) (i : FullIndex) :
    hermiteIsometry hb (fullBasis i) =
      state hb (SourceCliffordConnector.sourceMode (colourChiralEquiv i)) := by
  rw [← hermiteBasis_reindexed i, hermiteIsometry_basis]

theorem hermiteIsometry_coloured_left {b : ℝ} (hb : 0 < b) (c : Fin 3) (s : Fin 2) :
    hermiteIsometry hb (leftInclusion
      (WithLp.toLp 2 (colourBasis c ⊗ₜ[ℂ] spinBasis s, 0))) =
      state hb (4 * c.val + s.val) := by
  have hmode : SourceCliffordConnector.sourceMode
      (colourChiralEquiv (Sum.inl c, Sum.inl s)) = 4 * c.val + s.val := rfl
  simpa only [fullBasis_left, sourceBasis_coloured, hmode] using
    hermiteIsometry_fullBasis hb (Sum.inl c, Sum.inl s)

theorem hermiteIsometry_coloured_right {b : ℝ} (hb : 0 < b) (c : Fin 3) (s : Fin 2) :
    hermiteIsometry hb (rightInclusion
      (WithLp.toLp 2 (colourBasis c ⊗ₜ[ℂ] spinBasis s, 0))) =
      state hb (4 * c.val + (2 + s.val)) := by
  have hmode : SourceCliffordConnector.sourceMode
      (colourChiralEquiv (Sum.inl c, Sum.inr s)) = 4 * c.val + (2 + s.val) := rfl
  simpa only [fullBasis_right, sourceBasis_coloured, hmode] using
    hermiteIsometry_fullBasis hb (Sum.inl c, Sum.inr s)

theorem hermiteIsometry_scalar_left {b : ℝ} (hb : 0 < b) (s : Fin 2) :
    hermiteIsometry hb (leftInclusion
      (WithLp.toLp 2 (0, lineBasis 0 ⊗ₜ[ℂ] spinBasis s))) = state hb (12 + s.val) := by
  have hmode : SourceCliffordConnector.sourceMode
      (colourChiralEquiv (Sum.inr 0, Sum.inl s)) = 12 + s.val := rfl
  simpa only [fullBasis_left, sourceBasis_scalar, hmode] using
    hermiteIsometry_fullBasis hb (Sum.inr 0, Sum.inl s)

theorem hermiteIsometry_scalar_right {b : ℝ} (hb : 0 < b) (s : Fin 2) :
    hermiteIsometry hb (rightInclusion
      (WithLp.toLp 2 (0, lineBasis 0 ⊗ₜ[ℂ] spinBasis s))) = state hb (12 + (2 + s.val)) := by
  have hmode : SourceCliffordConnector.sourceMode
      (colourChiralEquiv (Sum.inr 0, Sum.inr s)) = 12 + (2 + s.val) := rfl
  simpa only [fullBasis_right, sourceBasis_scalar, hmode] using
    hermiteIsometry_fullBasis hb (Sum.inr 0, Sum.inr s)

theorem hermiteIsometry_range {b : ℝ} (hb : 0 < b) :
    LinearMap.range (hermiteIsometry hb).toLinearMap =
      sourceSpace hb (SourceCliffordConnector.sourceMode (d := 4)) := by
  change LinearMap.range (hermiteBasis.toBasis.constr ℂ _) = _
  exact hermiteBasis.toBasis.constr_range ℂ

theorem orthonormalBasis_linearMap_ext {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : OrthonormalBasis ι ℂ E)
    (f g : E →ₗ[ℂ] F) (h : ∀ i, f (e i) = g (e i)) : f = g :=
  e.toBasis.ext h

theorem orthonormalBasis_map_expansion {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : OrthonormalBasis ι ℂ E)
    (f : E →ₗ[ℂ] F) (x : E) : f x = ∑ i, e.repr x i • f (e i) := by
  conv_lhs => rw [← e.sum_repr x]
  simp only [map_sum, map_smul]

theorem hermiteIsometry_intertwines_basis {b : ℝ} (hb : 0 < b)
    (A : Module.End ℂ FullMatter) (j : SourceCliffordConnector.ColourIndex 4) :
    hermiteIsometry hb (A (hermiteBasis j)) =
      corner hb (SourceCliffordConnector.sourceMode (d := 4)) (fullMatrixCoordinates A)
        (hermiteIsometry hb (hermiteBasis j)) := by
  calc
    hermiteIsometry hb (A (hermiteBasis j)) =
        ∑ i, hermiteBasis.repr (A (hermiteBasis j)) i • hermiteIsometry hb (hermiteBasis i) :=
      orthonormalBasis_map_expansion hermiteBasis (hermiteIsometry hb).toLinearMap _
    _ = _ := by
      simp only [hermiteIsometry_basis]
      rw [corner_state hb _ (SourceCliffordConnector.sourceMode_injective 4)]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : ℂ => z • state hb (SourceCliffordConnector.sourceMode i))
        ((hermiteBasis.repr_apply_apply _ i).trans
          (LinearMap.toMatrixOrthonormal_apply_apply hermiteBasis A i j).symm)

theorem hermiteIsometry_intertwines {b : ℝ} (hb : 0 < b)
    (A : Module.End ℂ FullMatter) (x : FullMatter) :
    hermiteIsometry hb (A x) =
      corner hb (SourceCliffordConnector.sourceMode (d := 4)) (fullMatrixCoordinates A)
        (hermiteIsometry hb x) := by
  have hmap : (hermiteIsometry hb).toLinearMap.comp A =
      (corner hb (SourceCliffordConnector.sourceMode (d := 4))
        (fullMatrixCoordinates A)).toLinearMap.comp (hermiteIsometry hb).toLinearMap :=
    orthonormalBasis_linearMap_ext hermiteBasis _ _ (hermiteIsometry_intertwines_basis hb A)
  exact LinearMap.congr_fun hmap x

/-- Equality of the actual operators after the specified orthonormal coordinate permutation. -/
theorem hermiteIsometry_connector {b : ℝ} (hb : 0 < b) (q : ℍ) (x : FullMatter) :
    hermiteIsometry hb (connector (quaternionSpin q) x) =
      SourceCliffordConnector.sourceConnector hb 4 q (hermiteIsometry hb x) := by
  rw [hermiteIsometry_intertwines, fullMatrixCoordinates_quaternion]
  rfl

theorem hermiteIsometry_grading {b : ℝ} (hb : 0 < b) (x : FullMatter) :
    hermiteIsometry hb (grading x) =
      SourceCliffordConnector.sourceGrading hb 4 (hermiteIsometry hb x) := by
  rw [hermiteIsometry_intertwines, fullMatrixCoordinates_grading]
  rfl

end GeneratedFoundations.Physical.SourceChiralCarrier
