module

public import GeneratedFoundations.Physical.SourceQuadraticResponse
public import GeneratedFoundations.Physical.MinimalFaithfulModule
public import GeneratedFoundations.Geometry.SourceSymmetricUnitary
public import GeneratedFoundations.Geometry.SourceQuadraticSplit
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.Algebra.Algebra.Prod

/-!
# The joint algebra on the actual source carriers

The degree-two, degree-zero and degree-one source Hilbert spaces are used
for `W`, `L` and `S`.  The split-colour algebra acts on the left tensor
factors; an independently variable defining source acts on the right.
Finite sums and products of these commuting responses generate exactly
the two full endomorphism blocks.

The retained `W + L` split and independent response factors are the joint
response construction.  No assertion is made that the diagonal action of
one source group generates this larger algebra.  Matrix coordinates are
taken in orthonormal bases of the actual Haar-orbit Hilbert spaces, so the
resulting matrix-algebra equivalence also preserves the adjoint.
The actual symmetric and alternating tensor subspaces are connected to
these degree-two and degree-zero carriers by unitary source intertwiners.
-/

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricUnitary

namespace GeneratedFoundations.Physical.SourceJointResponse

abbrev W := HilbertCarrier 2
abbrev L := HilbertCarrier 0
abbrev S := HilbertCarrier 1
abbrev Coloured := W ⊗[ℂ] S
abbrev Scalar := L ⊗[ℂ] S

instance colouredNormed : NormedAddCommGroup Coloured :=
  TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := W) (F := S)

instance scalarNormed : NormedAddCommGroup Scalar :=
  TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := L) (F := S)

instance colouredInner : InnerProductSpace ℂ Coloured :=
  TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := W) (F := S)

instance scalarInner : InnerProductSpace ℂ Scalar :=
  TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := L) (F := S)

abbrev SplitColour := Module.End ℂ W × Module.End ℂ L
abbrev JointEnd := Module.End ℂ Coloured × Module.End ℂ Scalar

/-- The colour block is the unitary image of the actual symmetric source square. -/
def symmetricSourceUnitary :
    Geometry.SourceQuadraticSplit.symmetricSpace ≃ₗᵢ[ℂ] W :=
  Geometry.SourceQuadraticSplit.symmetricUnitary

/-- The retained line is the unitary image of the actual alternating source square. -/
def alternatingSourceUnitary :
    Geometry.SourceQuadraticSplit.alternatingSpace ≃ₗᵢ[ℂ] L :=
  Geometry.SourceQuadraticSplit.alternatingUnitary

/-- The actual polynomial source operator in its existing Haar realization. -/
def sourceOperator (m : ℕ) (U : SU2) : Module.End ℂ (HilbertCarrier m) :=
  (carrierEquiv m).conjAlgEquiv ℂ (sourceRepresentation m U)

theorem sourceOperator_apply (m : ℕ) (U : SU2) (p : Carrier m) :
    sourceOperator m U (carrierEquiv m p) =
      carrierEquiv m (sourceRepresentation m U p) := by
  simp [sourceOperator, LinearEquiv.conjAlgEquiv_apply]

theorem sourceOperator_eq_unitary (m : ℕ) (U : SU2) :
    sourceOperator m U = (unitaryAction m U).toLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective x
  exact (sourceOperator_apply m U p).trans (unitaryAction_apply_carrier m U p).symm

theorem symmetricSourceUnitary_intertwines (U : SU2)
    (x : Geometry.SourceQuadraticSplit.symmetricSpace) :
    symmetricSourceUnitary
        ⟨Geometry.SourceQuadraticSplit.tensorAction U x,
          Geometry.SourceQuadraticSplit.symmetricSpace_invariant U x.property⟩ =
      sourceOperator 2 U (symmetricSourceUnitary x) := by
  rw [sourceOperator_eq_unitary]
  exact Geometry.SourceQuadraticSplit.symmetricUnitary_intertwines U x

theorem alternatingSourceUnitary_intertwines (U : SU2)
    (x : Geometry.SourceQuadraticSplit.alternatingSpace) :
    alternatingSourceUnitary
        ⟨Geometry.SourceQuadraticSplit.tensorAction U x,
          Geometry.SourceQuadraticSplit.alternatingSpace_invariant U x.property⟩ =
      sourceOperator 0 U (alternatingSourceUnitary x) := by
  rw [sourceOperator_eq_unitary]
  exact Geometry.SourceQuadraticSplit.alternatingUnitary_intertwines U x

/-- The full quadratic response remains full on the actual Hilbert carrier. -/
theorem containing_quadratic_source_eq_top (A : Subalgebra ℂ (Module.End ℂ W))
    (hA : ∀ U : SU2, sourceOperator 2 U ∈ A) : A = ⊤ := by
  let e := (carrierEquiv 2).conjAlgEquiv ℂ
  have he : A.comap e.toAlgHom = ⊤ :=
    SourceQuadraticResponse.containing_source_eq_top (A.comap e.toAlgHom) hA
  apply top_unique
  intro T _
  obtain ⟨T', rfl⟩ := e.surjective T
  have hT : T' ∈ A.comap e.toAlgHom := by rw [he]; trivial
  exact hT

theorem quadratic_sourceAlgebra_eq_top :
    Algebra.adjoin ℂ (Set.range (sourceOperator 2)) = ⊤ :=
  containing_quadratic_source_eq_top _ fun U =>
    Algebra.subset_adjoin (Set.mem_range_self U)

private def phaseSource : SU2 :=
  ⟨canonical Complex.I 0, canonical_mem_specialUnitary _ _ (by norm_num)⟩

private def exchangeSource : SU2 :=
  ⟨canonical 0 1, canonical_mem_specialUnitary _ _ (by norm_num)⟩

private def spinMatrixAlgebra : Subalgebra ℂ Mat2 :=
  Algebra.adjoin ℂ (Set.range (fun U : SU2 => (U : Mat2)))

private theorem spinMatrixUnit_mem (i j : Fin 2) :
    Matrix.single i j (1 : ℂ) ∈ spinMatrixAlgebra := by
  have hd : (phaseSource : Mat2) ∈ spinMatrixAlgebra :=
    Algebra.subset_adjoin (Set.mem_range_self phaseSource)
  have hx : (exchangeSource : Mat2) ∈ spinMatrixAlgebra :=
    Algebra.subset_adjoin (Set.mem_range_self exchangeSource)
  have hzero : Matrix.single 0 0 (1 : ℂ) ∈ spinMatrixAlgebra := by
    have h := spinMatrixAlgebra.smul_mem
      (spinMatrixAlgebra.sub_mem spinMatrixAlgebra.one_mem
        (spinMatrixAlgebra.smul_mem hd Complex.I)) (1 / 2 : ℂ)
    have he : (1 / 2 : ℂ) • (1 - Complex.I • (phaseSource : Mat2)) =
        Matrix.single 0 0 1 := by
      ext r s
      fin_cases r <;> fin_cases s <;>
        norm_num [phaseSource, canonical, Matrix.single]
    rwa [he] at h
  have hone : Matrix.single 1 1 (1 : ℂ) ∈ spinMatrixAlgebra := by
    have h := spinMatrixAlgebra.sub_mem spinMatrixAlgebra.one_mem hzero
    have he : (1 : Mat2) - Matrix.single 0 0 1 = Matrix.single 1 1 1 := by
      ext r s
      fin_cases r <;> fin_cases s <;> norm_num [Matrix.single]
    rwa [he] at h
  have h01 : Matrix.single 0 1 (1 : ℂ) ∈ spinMatrixAlgebra := by
    have h := spinMatrixAlgebra.mul_mem (spinMatrixAlgebra.mul_mem hzero hx) hone
    simpa [Matrix.single_mul_mul_single, exchangeSource, canonical] using h
  have h10 : Matrix.single 1 0 (1 : ℂ) ∈ spinMatrixAlgebra := by
    have h := spinMatrixAlgebra.neg_mem
      (spinMatrixAlgebra.mul_mem (spinMatrixAlgebra.mul_mem hone hx) hzero)
    simpa [Matrix.single_mul_mul_single, exchangeSource, canonical,
      Matrix.single_neg] using h
  fin_cases i <;> fin_cases j
  · exact hzero
  · exact h01
  · exact h10
  · exact hone

private theorem spinMatrixAlgebra_eq_top : spinMatrixAlgebra = ⊤ := by
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply spinMatrixAlgebra.sum_mem
  intro i _
  apply spinMatrixAlgebra.sum_mem
  intro j _
  have h := spinMatrixAlgebra.smul_mem (spinMatrixUnit_mem i j) (M i j)
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using h

private def spinCoordinates : Module.End ℂ (Carrier 1) ≃ₐ[ℂ] Mat2 :=
  (degreeOneEquiv.symm.conjAlgEquiv ℂ).trans LinearMap.toMatrixAlgEquiv'

private theorem spinCoordinates_source (U : SU2) :
    spinCoordinates (sourceRepresentation 1 U) = (U : Mat2) := by
  apply Matrix.toLinAlgEquiv'.injective
  change Matrix.toLinAlgEquiv'
      (LinearMap.toMatrixAlgEquiv' ((degreeOneEquiv.symm.conjAlgEquiv ℂ)
        (sourceRepresentation 1 U))) = Matrix.toLinAlgEquiv' (U : Mat2)
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  apply LinearMap.ext
  intro v
  change degreeOneEquiv.symm (sourceRepresentation 1 U (degreeOnePolynomial v)) =
    (U : Mat2).mulVec v
  rw [degreeOne_intertwines]
  exact degreeOneEquiv.symm_apply_apply _

private theorem containing_polynomial_spin_eq_top
    (A : Subalgebra ℂ (Module.End ℂ (Carrier 1)))
    (hA : ∀ U : SU2, sourceRepresentation 1 U ∈ A) : A = ⊤ := by
  have hle : spinMatrixAlgebra ≤ A.map spinCoordinates.toAlgHom := by
    apply Algebra.adjoin_le
    rintro _ ⟨U, rfl⟩
    exact Subalgebra.mem_map.mpr ⟨sourceRepresentation 1 U, hA U,
      spinCoordinates_source U⟩
  rw [spinMatrixAlgebra_eq_top] at hle
  apply top_unique
  intro T _
  obtain ⟨T', hT', he⟩ := Subalgebra.mem_map.mp (hle (show spinCoordinates T ∈ ⊤ from trivial))
  exact spinCoordinates.injective he ▸ hT'

/-- The defining source alone generates every complex-linear spin response. -/
theorem containing_spin_source_eq_top (A : Subalgebra ℂ (Module.End ℂ S))
    (hA : ∀ U : SU2, sourceOperator 1 U ∈ A) : A = ⊤ := by
  let e := (carrierEquiv 1).conjAlgEquiv ℂ
  have he : A.comap e.toAlgHom = ⊤ :=
    containing_polynomial_spin_eq_top (A.comap e.toAlgHom) hA
  apply top_unique
  intro T _
  obtain ⟨T', rfl⟩ := e.surjective T
  have hT : T' ∈ A.comap e.toAlgHom := by rw [he]; trivial
  exact hT

theorem spin_sourceAlgebra_eq_top :
    Algebra.adjoin ℂ (Set.range (sourceOperator 1)) = ⊤ :=
  containing_spin_source_eq_top _ fun U =>
    Algebra.subset_adjoin (Set.mem_range_self U)

/-- Split-colour responses act on the original left tensor factors. -/
def colourResponse : SplitColour →ₐ[ℂ] JointEnd where
  toFun a := (TensorProduct.map a.1 1, TensorProduct.map a.2 1)
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp [TensorProduct.map_add_left]
  map_mul' a b := by
    apply Prod.ext <;>
      simp only [Prod.fst_mul, Prod.snd_mul, ← TensorProduct.map_mul, mul_one]
  commutes' c := by
    apply Prod.ext <;>
      simp [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_left]

/-- One spin response acts on both retained sectors. -/
def spinResponse : Module.End ℂ S →ₐ[ℂ] JointEnd where
  toFun T := (TensorProduct.map 1 T, TensorProduct.map 1 T)
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp [TensorProduct.map_add_right]
  map_mul' A B := by
    apply Prod.ext <;>
      simp only [Prod.fst_mul, Prod.snd_mul, ← TensorProduct.map_mul, one_mul]
  commutes' c := by
    apply Prod.ext <;>
      simp [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_right]

theorem colour_spin_product (a : SplitColour) (T : Module.End ℂ S) :
    colourResponse a * spinResponse T =
      (TensorProduct.map a.1 T, TensorProduct.map a.2 T) := by
  change (TensorProduct.map a.1 1 * TensorProduct.map 1 T,
    TensorProduct.map a.2 1 * TensorProduct.map 1 T) = _
  simp only [← TensorProduct.map_mul, mul_one, one_mul]

theorem colour_spin_commute (a : SplitColour) (T : Module.End ℂ S) :
    Commute (colourResponse a) (spinResponse T) := by
  change colourResponse a * spinResponse T = spinResponse T * colourResponse a
  rw [colour_spin_product]
  change _ = (TensorProduct.map 1 T * TensorProduct.map a.1 1,
    TensorProduct.map 1 T * TensorProduct.map a.2 1)
  simp only [← TensorProduct.map_mul, mul_one, one_mul]

/-- Algebraic closure of the retained colour responses and the independent
actual spin source. There is no topological closure in this definition. -/
def responseAlgebra : Subalgebra ℂ JointEnd :=
  Algebra.adjoin ℂ (Set.range colourResponse ∪
    Set.range (fun U : SU2 => spinResponse (sourceOperator 1 U)))

theorem colourResponse_mem (a : SplitColour) : colourResponse a ∈ responseAlgebra :=
  Algebra.subset_adjoin (Or.inl (Set.mem_range_self a))

theorem spinSource_mem (U : SU2) : spinResponse (sourceOperator 1 U) ∈ responseAlgebra :=
  Algebra.subset_adjoin (Or.inr (Set.mem_range_self U))

theorem spinResponse_mem (T : Module.End ℂ S) : spinResponse T ∈ responseAlgebra := by
  have he : responseAlgebra.comap spinResponse = ⊤ :=
    containing_spin_source_eq_top (responseAlgebra.comap spinResponse) spinSource_mem
  change T ∈ responseAlgebra.comap spinResponse
  rw [he]
  trivial

theorem coloured_tensor_mem (A : Module.End ℂ W) (T : Module.End ℂ S) :
    (TensorProduct.map A T, 0) ∈ responseAlgebra := by
  have h := responseAlgebra.mul_mem (colourResponse_mem (A, 0)) (spinResponse_mem T)
  simpa only [colour_spin_product, TensorProduct.map_zero_left] using h

theorem scalar_tensor_mem (A : Module.End ℂ L) (T : Module.End ℂ S) :
    (0, TensorProduct.map A T) ∈ responseAlgebra := by
  have h := responseAlgebra.mul_mem (colourResponse_mem (0, A)) (spinResponse_mem T)
  simpa only [colour_spin_product, TensorProduct.map_zero_left] using h

theorem coloured_end_mem (A : Module.End ℂ Coloured) : (A, 0) ∈ responseAlgebra := by
  obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ W S W S).surjective A
  induction t using TensorProduct.inductionOn with
  | tmul A T =>
      simpa only [homTensorHomEquiv_apply,
        TensorProduct.homTensorHomMap_apply] using coloured_tensor_mem A T
  | add t u ht hu =>
      simpa only [map_add, Prod.mk_add_mk, add_zero] using responseAlgebra.add_mem ht hu

theorem scalar_end_mem (A : Module.End ℂ Scalar) : (0, A) ∈ responseAlgebra := by
  obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ L S L S).surjective A
  induction t using TensorProduct.inductionOn with
  | tmul A T =>
      simpa only [homTensorHomEquiv_apply,
        TensorProduct.homTensorHomMap_apply] using scalar_tensor_mem A T
  | add t u ht hu =>
      simpa only [map_add, Prod.mk_add_mk, add_zero] using responseAlgebra.add_mem ht hu

/-- Both complete endomorphism blocks are derived from the commuting
response factors; their fullness is not part of the carrier definition. -/
theorem responseAlgebra_eq_top : responseAlgebra = ⊤ := by
  apply top_unique
  rintro ⟨A, B⟩ _
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using
    responseAlgebra.add_mem (coloured_end_mem A) (scalar_end_mem B)

theorem coloured_finrank : Module.finrank ℂ Coloured = 6 := by
  simp [Coloured, W, S, Module.finrank_tensorProduct, hilbertCarrier_finrank]

theorem scalar_finrank : Module.finrank ℂ Scalar = 2 := by
  simp [Scalar, L, S, Module.finrank_tensorProduct, hilbertCarrier_finrank]

def colouredBasis : OrthonormalBasis (Fin 6) ℂ Coloured :=
  (stdOrthonormalBasis ℂ Coloured).reindex (finCongr coloured_finrank)

def scalarBasis : OrthonormalBasis (Fin 2) ℂ Scalar :=
  (stdOrthonormalBasis ℂ Scalar).reindex (finCongr scalar_finrank)

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
