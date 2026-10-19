module

public import GeneratedFoundations.Physical.SourceChargedResponse
public import GeneratedFoundations.Physical.GlobalGaugeKernel
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The normalized defining colour Casimir on the source carrier

The eight Hermitian Gell-Mann generators are given explicitly, with
`trace (T a * T b) = delta a b / 2`. Their quadratic sum is computed
before it is transported to the actual three-dimensional source space.
The retained colour line has zero generator action. The source tensor
and chiral lifts therefore identify the existing scalar colour response
with this quadratic sum at `kappa = 4 / 3`.

The normalization is fixed by the source trace metric: the generators are
orthonormal for `2 * trace (T_a T_b)`, and the quadratic sum is proved invariant
under every orthogonal change of such a normalized basis. Thus `4/3` is a
calculated source coefficient, not an independent coupling. The source colour
space, retained line and matter carrier are the
constructions imported from the exchange-retained response and least-module
classification. This file identifies their normalized defining colour
response; the source construction and frame classification are proved in
their respective modules.

Independence under orthogonal changes of normalized generators, and under
changes of orthonormal coordinates on the source colour space, is proved
below. Compatibility with the actual defining SU(3) action is algebraic.
No differentiation theorem for a smooth SU(3) representation is used or
claimed in this file.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate TensorProduct Matrix

namespace GeneratedFoundations.Physical.SourceColourCasimir

open SourceJointResponse SourceMinimalRepresentation SourceChiralCarrier
open SourceChargeLattice SourceMatterCharge SourceChargedResponse

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

def rootThree : ℂ := (Real.sqrt 3 : ℝ)

@[simp] private theorem rootThree_star : star rootThree = rootThree := by
  simp [rootThree]

@[simp] private theorem rootThree_sq : rootThree ^ 2 = 3 := by
  dsimp [rootThree]
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))

/-- The standard Hermitian generators, normalized by the defining trace. -/
def generator : Fin 8 → Mat3 :=
  ![!![0, 1 / 2, 0; 1 / 2, 0, 0; 0, 0, 0],
    !![0, -Complex.I / 2, 0; Complex.I / 2, 0, 0; 0, 0, 0],
    !![1 / 2, 0, 0; 0, -1 / 2, 0; 0, 0, 0],
    !![0, 0, 1 / 2; 0, 0, 0; 1 / 2, 0, 0],
    !![0, 0, -Complex.I / 2; 0, 0, 0; Complex.I / 2, 0, 0],
    !![0, 0, 0; 0, 0, 1 / 2; 0, 1 / 2, 0],
    !![0, 0, 0; 0, 0, -Complex.I / 2; 0, Complex.I / 2, 0],
    !![rootThree / 6, 0, 0; 0, rootThree / 6, 0; 0, 0, -rootThree / 3]]

theorem generator_hermitian (a : Fin 8) : (generator a).IsHermitian := by
  change (generator a)ᴴ = generator a
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [generator, Matrix.conjTranspose_apply]

theorem generator_trace (a : Fin 8) : Matrix.trace (generator a) = 0 := by
  fin_cases a <;>
    norm_num [generator, Matrix.trace, Fin.sum_univ_succ]
  all_goals ring

theorem generator_trace_pair (a b : Fin 8) :
    Matrix.trace (generator a * generator b) = if a = b then 1 / 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [generator, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [rootThree_sq, Complex.I_sq] <;> norm_num

/-- Coefficients obtained from matrix entries, not from an assumed spanning property. -/
def expansionCoefficient (A : Mat3) : Fin 8 → ℂ :=
  ![A 0 1 + A 1 0, Complex.I * (A 0 1 - A 1 0), A 0 0 - A 1 1,
    A 0 2 + A 2 0, Complex.I * (A 0 2 - A 2 0),
    A 1 2 + A 2 1, Complex.I * (A 1 2 - A 2 1),
    rootThree * (A 0 0 + A 1 1)]

theorem generator_expansion (A : Mat3) (htrace : Matrix.trace A = 0) :
    (∑ a, expansionCoefficient A a • generator a) = A := by
  have ht : A 0 0 + A 1 1 + A 2 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ, add_assoc] using htrace
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [expansionCoefficient, generator, Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [rootThree_sq, Complex.I_sq] <;>
    ring_nf
  all_goals linear_combination -ht

theorem expansionCoefficient_real {A : Mat3} (hA : A.IsHermitian) (a : Fin 8) :
    ((expansionCoefficient A a).re : ℂ) = expansionCoefficient A a := by
  apply Complex.conj_eq_iff_re.mp
  have hstar (i j : Fin 3) : star (A i j) = A j i := hA.apply j i
  change star (expansionCoefficient A a) = expansionCoefficient A a
  fin_cases a <;> simp [expansionCoefficient, hstar] <;> ring

/-- Every traceless Hermitian matrix is a real linear combination of the generators. -/
theorem hermitian_generator_expansion (A : Mat3)
    (hA : A.IsHermitian) (htrace : Matrix.trace A = 0) :
    (∑ a, ((expansionCoefficient A a).re : ℂ) • generator a) = A := by
  simp_rw [expansionCoefficient_real hA]
  exact generator_expansion A htrace

theorem trace_combination (c : Fin 8 → ℂ) (b : Fin 8) :
    Matrix.trace ((∑ a, c a • generator a) * generator b) = c b / 2 := by
  simp [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul,
    generator_trace_pair, smul_eq_mul, mul_ite, div_eq_mul_inv]

theorem generator_linearIndependent : LinearIndependent ℂ generator := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc b
  have ht := congrArg (fun A : Mat3 => Matrix.trace (A * generator b)) hc
  rw [trace_combination] at ht
  simpa using ht

theorem generator_real_linearIndependent : LinearIndependent ℝ generator :=
  generator_linearIndependent.restrict_scalars' ℝ

/-- Multiplication by `i` gives the skew-Hermitian, traceless Lie-algebra convention. -/
def lieGenerator (a : Fin 8) : Mat3 := Complex.I • generator a

theorem lieGenerator_skewHermitian (a : Fin 8) :
    (lieGenerator a)ᴴ = -lieGenerator a := by
  simp [lieGenerator, Matrix.conjTranspose_smul, (generator_hermitian a).eq,
    neg_smul]

theorem lieGenerator_trace (a : Fin 8) : Matrix.trace (lieGenerator a) = 0 := by
  simp [lieGenerator, Matrix.trace_smul, generator_trace]

/-- This is the sum of actual generator products, not a prescribed scalar operator. -/
def matrixCasimir : Mat3 := ∑ a, generator a * generator a

theorem matrixCasimir_eq : matrixCasimir = (4 / 3 : ℂ) • (1 : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixCasimir, generator, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [rootThree_sq, Complex.I_sq] <;> norm_num

theorem lieGenerator_casimir :
    -(∑ a, lieGenerator a * lieGenerator a) = matrixCasimir := by
  have hs (a : Fin 8) : lieGenerator a * lieGenerator a =
      -(generator a * generator a) := by
    simp [lieGenerator, smul_smul, Complex.I_mul_I]
  simp_rw [hs]
  simp [matrixCasimir]

/-- A real orthogonal change among the eight trace-normalized generators. -/
def OrthogonalChange (O : Matrix (Fin 8) (Fin 8) ℝ) : Prop :=
  ∀ b c, ∑ a, O a b * O a c = if b = c then 1 else 0

def rotatedGenerator (O : Matrix (Fin 8) (Fin 8) ℝ) (a : Fin 8) : Mat3 :=
  ∑ b, (O a b : ℂ) • generator b

theorem rotatedGenerator_casimir (O : Matrix (Fin 8) (Fin 8) ℝ)
    (hO : OrthogonalChange O) :
    (∑ a, rotatedGenerator O a * rotatedGenerator O a) = matrixCasimir := by
  have ho (b c : Fin 8) :
      (∑ a, (O a b : ℂ) * (O a c : ℂ)) = if b = c then 1 else 0 := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, apply_ite,
      Complex.ofReal_one, Complex.ofReal_zero] using
      congrArg (fun x : ℝ => (x : ℂ)) (hO b c)
  calc
    (∑ a, rotatedGenerator O a * rotatedGenerator O a) =
        ∑ a, ∑ b, ∑ c, ((O a b : ℂ) * (O a c : ℂ)) •
          (generator b * generator c) := by
      simp only [rotatedGenerator]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [mul_comm (O a c : ℂ) (O a b : ℂ)]
    _ = ∑ b, ∑ c, ∑ a, ((O a b : ℂ) * (O a c : ℂ)) •
          (generator b * generator c) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, (∑ a, (O a b : ℂ) * (O a c : ℂ)) •
          (generator b * generator c) := by
      simp only [Finset.sum_smul]
    _ = matrixCasimir := by
      simp_rw [ho]
      simp [matrixCasimir]

def colourCoordinates (b : OrthonormalBasis (Fin 3) ℂ W) :
    Module.End ℂ W ≃⋆ₐ[ℂ] Mat3 := LinearMap.toMatrixOrthonormal b

def colourGeneratorIn (b : OrthonormalBasis (Fin 3) ℂ W) (a : Fin 8) :
    Module.End ℂ W := (colourCoordinates b).symm (generator a)

theorem colourGeneratorIn_isSelfAdjoint (b : OrthonormalBasis (Fin 3) ℂ W) (a : Fin 8) :
    IsSelfAdjoint (colourGeneratorIn b a) := by
  change star ((colourCoordinates b).symm (generator a)) =
    (colourCoordinates b).symm (generator a)
  exact (map_star (colourCoordinates b).symm (generator a)).symm.trans
    (congrArg (colourCoordinates b).symm (generator_hermitian a).star_eq)

def colourCasimirIn (b : OrthonormalBasis (Fin 3) ℂ W) : Module.End ℂ W :=
  ∑ a, colourGeneratorIn b a * colourGeneratorIn b a

private theorem algebraEquiv_quadratic_sum {A B : Type*} [Semiring A] [Semiring B]
    [Algebra ℂ A] [Algebra ℂ B] (e : A ≃ₐ[ℂ] B) (g : Fin 8 → A) (c : ℂ)
    (h : (∑ a, g a * g a) = c • (1 : A)) :
    (∑ a, e (g a) * e (g a)) = c • (1 : B) := by
  have he := congrArg e h
  simpa only [map_sum, map_mul, map_smul, map_one] using he

theorem colourCasimirIn_eq (b : OrthonormalBasis (Fin 3) ℂ W) :
    colourCasimirIn b = (4 / 3 : ℂ) • (1 : Module.End ℂ W) := by
  exact algebraEquiv_quadratic_sum (colourCoordinates b).symm.toAlgEquiv
    generator (4 / 3) matrixCasimir_eq

theorem colourCasimirIn_basis_independent (b c : OrthonormalBasis (Fin 3) ℂ W) :
    colourCasimirIn b = colourCasimirIn c := by
  rw [colourCasimirIn_eq, colourCasimirIn_eq]

def colourGenerator : Fin 8 → Module.End ℂ W := colourGeneratorIn colourBasis

def sourceColourCasimir : Module.End ℂ W := ∑ a, colourGenerator a * colourGenerator a

theorem sourceColourCasimir_eq :
    sourceColourCasimir = (4 / 3 : ℂ) • (1 : Module.End ℂ W) :=
  colourCasimirIn_eq colourBasis

theorem sourceColourCasimir_commutes (A : Module.End ℂ W) :
    Commute sourceColourCasimir A := by
  change sourceColourCasimir * A = A * sourceColourCasimir
  rw [sourceColourCasimir_eq]
  simp

/-- The defining localized colour action in the same actual source coordinates. -/
def definingColourAction (g : GlobalGaugeKernel.SU3) : Module.End ℂ W :=
  (colourCoordinates colourBasis).symm (g : Mat3)

@[simp] theorem definingColourAction_one : definingColourAction 1 = 1 := by
  simp [definingColourAction]

theorem definingColourAction_mul (g h : GlobalGaugeKernel.SU3) :
    definingColourAction (g * h) = definingColourAction g * definingColourAction h := by
  simp [definingColourAction, map_mul]

theorem sourceColourCasimir_su3 (g : GlobalGaugeKernel.SU3) :
    Commute sourceColourCasimir (definingColourAction g) :=
  sourceColourCasimir_commutes _

/-- Tensor with the unchanged source spin and extend by zero on the retained line.
This lift is multiplicative and linear; it is not unital on the whole carrier. -/
def sourceColourLift : Module.End ℂ W →ₗ[ℂ] Module.End ℂ SourceCarrier :=
  sourceCarrierRepresentation.toLinearMap.comp
    (colourResponse.toLinearMap.comp (LinearMap.inl ℂ (Module.End ℂ W) (Module.End ℂ L)))

theorem sourceColourLift_mul (A B : Module.End ℂ W) :
    sourceColourLift (A * B) = sourceColourLift A * sourceColourLift B := by
  change sourceCarrierRepresentation (colourResponse (A * B, 0)) =
    sourceCarrierRepresentation (colourResponse (A, 0)) *
      sourceCarrierRepresentation (colourResponse (B, 0))
  have hp : (A * B, (0 : Module.End ℂ L)) = (A, 0) * (B, 0) :=
    Prod.ext rfl (zero_mul 0).symm
  let f : SplitColour →ₐ[ℂ] Module.End ℂ SourceCarrier :=
    sourceCarrierRepresentation.comp colourResponse
  exact (congrArg f hp).trans (map_mul f (A, 0) (B, 0))

theorem sourceColourLift_one : sourceColourLift 1 = relativeSource 1 0 := by
  simp [sourceColourLift, relativeSource, relativeColour]

theorem sourceColourLift_adjoint (A : Module.End ℂ W) :
    (sourceColourLift A).adjoint = sourceColourLift A.adjoint := by
  have hc : star (colourResponse (A, 0)) = colourResponse (A.adjoint, 0) := by
    apply Prod.ext
    · change (TensorProduct.map A (1 : Module.End ℂ S)).adjoint =
        TensorProduct.map A.adjoint 1
      simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one]
    · change (TensorProduct.map (0 : Module.End ℂ L) (1 : Module.End ℂ S)).adjoint =
        TensorProduct.map 0 1
      simp only [TensorProduct.adjoint_map, LinearMap.adjoint_one, map_zero]
  exact (sourceCarrierRepresentation_adjoint (colourResponse (A, 0))).trans
    (congrArg sourceCarrierRepresentation hc)

def chiralDuplication : Module.End ℂ SourceCarrier →ₗ[ℂ] Module.End ℂ FullMatter :=
  (fullMatterCoordinates.conjAlgEquiv ℂ).toLinearMap.comp
    ((LinearMap.prodMapAlgHom ℂ SourceCarrier SourceCarrier).toLinearMap.comp
      ((LinearMap.id : Module.End ℂ SourceCarrier →ₗ[ℂ] Module.End ℂ SourceCarrier).prod
        LinearMap.id))

@[simp] theorem chiralDuplication_apply (A : Module.End ℂ SourceCarrier) :
    chiralDuplication A = diagonalBlocks A A := rfl

theorem chiralDuplication_mul (A B : Module.End ℂ SourceCarrier) :
    chiralDuplication (A * B) = chiralDuplication A * chiralDuplication B := by
  simp only [chiralDuplication_apply, diagonalBlocks_mul]

def fullColourLift : Module.End ℂ W →ₗ[ℂ] Module.End ℂ FullMatter :=
  chiralDuplication.comp sourceColourLift

theorem fullColourLift_mul (A B : Module.End ℂ W) :
    fullColourLift (A * B) = fullColourLift A * fullColourLift B := by
  exact (congrArg chiralDuplication (sourceColourLift_mul A B)).trans
    (chiralDuplication_mul (sourceColourLift A) (sourceColourLift B))

theorem fullColourLift_one :
    fullColourLift 1 = diagonalBlocks (relativeSource 1 0) (relativeSource 1 0) := by
  exact congrArg chiralDuplication sourceColourLift_one

theorem fullColourLift_adjoint (A : Module.End ℂ W) :
    (fullColourLift A).adjoint = fullColourLift A.adjoint := by
  exact (diagonalBlocks_adjoint (sourceColourLift A) (sourceColourLift A)).trans
    (congrArg₂ diagonalBlocks (sourceColourLift_adjoint A) (sourceColourLift_adjoint A))

def rightGenerator (a : Fin 8) : Module.End ℂ SourceCarrier :=
  sourceColourLift (colourGenerator a)

def fullGenerator (a : Fin 8) : Module.End ℂ FullMatter :=
  fullColourLift (colourGenerator a)

theorem rightGenerator_isSelfAdjoint (a : Fin 8) : IsSelfAdjoint (rightGenerator a) := by
  have ha : (colourGenerator a).adjoint = colourGenerator a := by
    exact (colourGeneratorIn_isSelfAdjoint colourBasis a).star_eq
  change (sourceColourLift (colourGenerator a)).adjoint = sourceColourLift (colourGenerator a)
  exact (sourceColourLift_adjoint (colourGenerator a)).trans (congrArg sourceColourLift ha)

theorem fullGenerator_isSelfAdjoint (a : Fin 8) : IsSelfAdjoint (fullGenerator a) := by
  have ha : (colourGenerator a).adjoint = colourGenerator a := by
    exact (colourGeneratorIn_isSelfAdjoint colourBasis a).star_eq
  change (fullColourLift (colourGenerator a)).adjoint = fullColourLift (colourGenerator a)
  exact (fullColourLift_adjoint (colourGenerator a)).trans (congrArg fullColourLift ha)

def rightCasimir : Module.End ℂ SourceCarrier := ∑ a, rightGenerator a * rightGenerator a

def fullCasimir : Module.End ℂ FullMatter := ∑ a, fullGenerator a * fullGenerator a

private theorem selfAdjoint_square_positive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (A : Module.End ℂ E) (hA : IsSelfAdjoint A) : (A * A).IsPositive := by
  have ha : A.adjoint = A := by simpa only [LinearMap.star_eq_adjoint] using hA.star_eq
  change (A.comp A).IsPositive
  simpa only [ha] using LinearMap.isPositive_adjoint_comp_self A

theorem rightCasimir_isPositive : rightCasimir.IsPositive := by
  apply LinearMap.isPositive_sum
  intro a ha
  exact selfAdjoint_square_positive _ (rightGenerator_isSelfAdjoint a)

theorem fullCasimir_isPositive : fullCasimir.IsPositive := by
  apply LinearMap.isPositive_sum
  intro a ha
  exact selfAdjoint_square_positive _ (fullGenerator_isSelfAdjoint a)

theorem rightCasimir_lift : rightCasimir = sourceColourLift sourceColourCasimir := by
  simp only [rightCasimir, rightGenerator, sourceColourCasimir, map_sum, sourceColourLift_mul]

theorem fullCasimir_lift : fullCasimir = fullColourLift sourceColourCasimir := by
  simp only [fullCasimir, fullGenerator, sourceColourCasimir, map_sum, fullColourLift_mul]

theorem rightCasimir_eq : rightCasimir = rightColourResponse (4 / 3) := by
  have h := rightCasimir_lift.trans
    ((congrArg sourceColourLift sourceColourCasimir_eq).trans
      ((map_smul sourceColourLift (4 / 3 : ℂ) (1 : Module.End ℂ W)).trans
        (congrArg (fun A : Module.End ℂ SourceCarrier => (4 / 3 : ℂ) • A)
          sourceColourLift_one)))
  simpa only [rightColourResponse, Complex.ofReal_div, Complex.ofReal_ofNat] using h

theorem fullCasimir_eq : fullCasimir = SourceMatterCharge.colourCasimir (4 / 3) := by
  have h := fullCasimir_lift.trans
    ((congrArg fullColourLift sourceColourCasimir_eq).trans
      ((map_smul fullColourLift (4 / 3 : ℂ) (1 : Module.End ℂ W)).trans
        (congrArg (fun A : Module.End ℂ FullMatter => (4 / 3 : ℂ) • A)
          fullColourLift_one)))
  simpa only [SourceMatterCharge.colourCasimir, Complex.ofReal_div,
    Complex.ofReal_ofNat] using h

/-- The scale changes quadratically if all Hermitian generators are rescaled. -/
theorem scaled_fullCasimir (r : ℝ) :
    (∑ a, ((r : ℂ) • fullGenerator a) * ((r : ℂ) • fullGenerator a)) =
      SourceMatterCharge.colourCasimir ((4 / 3) * r ^ 2) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← Finset.smul_sum]
  change ((r : ℂ) * (r : ℂ)) • fullCasimir = _
  rw [fullCasimir_eq]
  simp only [SourceMatterCharge.colourCasimir, smul_smul, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
  congr 1
  ring

/-- The right response uses the computed Casimir and the already generated charge. -/
def rightQuadraticResponse : Module.End ℂ SourceCarrier :=
  rightCasimir + rightHypercharge * rightHypercharge

def fullQuadraticResponse : Module.End ℂ FullMatter :=
  fullCasimir + hyperchargeOperator * hyperchargeOperator

theorem rightQuadraticResponse_eq : rightQuadraticResponse = rightResponse (4 / 3) := by
  simp only [rightQuadraticResponse, rightResponse, rightCasimir_eq]

theorem fullQuadraticResponse_eq : fullQuadraticResponse = chargedResponse (4 / 3) := by
  simp only [fullQuadraticResponse, chargedResponse, fullCasimir_eq]

theorem rightQuadraticResponse_isSelfAdjoint : IsSelfAdjoint rightQuadraticResponse := by
  rw [rightQuadraticResponse_eq]
  exact rightResponse_isSelfAdjoint _

theorem rightQuadraticResponse_isPositive : rightQuadraticResponse.IsPositive := by
  rw [rightQuadraticResponse_eq]
  exact rightResponse_isPositive (by norm_num)

theorem fullQuadraticResponse_isSelfAdjoint : IsSelfAdjoint fullQuadraticResponse := by
  rw [fullQuadraticResponse_eq]
  exact chargedResponse_isSelfAdjoint _

theorem fullQuadraticResponse_isPositive : fullQuadraticResponse.IsPositive := by
  rw [fullQuadraticResponse_eq]
  exact chargedResponse_isPositive (by norm_num)

theorem rightQuadraticResponse_kernel : LinearMap.ker rightQuadraticResponse = rightNeutralLine := by
  rw [rightQuadraticResponse_eq]
  exact rightResponse_kernel (by norm_num)

theorem fullQuadraticResponse_kernel : LinearMap.ker fullQuadraticResponse = neutralLine := by
  rw [fullQuadraticResponse_eq]
  exact chargedResponse_kernel (by norm_num)

theorem rightQuadraticResponse_quotient_finrank :
    Module.finrank ℂ (SourceCarrier ⧸ LinearMap.ker rightQuadraticResponse) = 7 := by
  rw [rightQuadraticResponse_kernel]
  exact rightChargedQuotient_finrank

theorem fullQuadraticResponse_quotient_finrank :
    Module.finrank ℂ (FullMatter ⧸ LinearMap.ker fullQuadraticResponse) = 15 := by
  rw [fullQuadraticResponse_kernel]
  exact chargedQuotient_finrank

end GeneratedFoundations.Physical.SourceColourCasimir
