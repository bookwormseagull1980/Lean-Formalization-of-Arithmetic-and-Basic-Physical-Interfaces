module

public import GeneratedFoundations.Geometry.SourceJointResponse
public import GeneratedFoundations.Operations.ColourNaturalConnector
public import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# Independent responses before exchange resolution

The colour carrier is the actual tensor square of the degree-one source
Hilbert space. Independent source responses on its two factors generate
its entire complex endomorphism algebra by finite algebraic operations.
This uses neither exchange resolution nor the diagonal action of one
source group on both factors.

An arbitrary endomorphism of the colour carrier tensored with a further
source spinor is natural for those independent responses exactly when it
is the colour identity tensored with one unique spinor endomorphism.
Orthonormal coordinates and the tensor-product matrix identity transport
the matrix-unit classification to these actual source carriers. Tensor
factorization is a conclusion, not a restriction on the input map.

Reversal reality is a further condition on the unique reduced spinor map.
No antiunitary structure or charge assignment is selected in this file.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Kronecker
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Operations
open GeneratedFoundations.Geometry.SourceJointResponse (S sourceOperator)
open GeneratedFoundations.Operations.ReversalRealConnector (Mat2)

namespace GeneratedFoundations.Geometry.SourcePreExchangeResponse

abbrev C := Geometry.SourceQuadraticSplit.TensorSquare
abbrev FullCarrier := C ⊗[ℂ] S

instance fullCarrierNormed : NormedAddCommGroup FullCarrier :=
  TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := C) (F := S)

instance fullCarrierInner : InnerProductSpace ℂ FullCarrier :=
  TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := C) (F := S)

/-- The first source factor varies independently of the second one. -/
def leftResponse : Module.End ℂ S →ₐ[ℂ] Module.End ℂ C where
  toFun A := TensorProduct.map A 1
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp [TensorProduct.map_add_left]
  map_mul' A B := by simp only [← TensorProduct.map_mul, mul_one]
  commutes' c := by
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_left]

/-- The second source factor is not tied to the first source parameter. -/
def rightResponse : Module.End ℂ S →ₐ[ℂ] Module.End ℂ C where
  toFun A := TensorProduct.map 1 A
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp [TensorProduct.map_add_right]
  map_mul' A B := by simp only [← TensorProduct.map_mul, one_mul]
  commutes' c := by
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_right]

theorem leftResponse_tmul (A : Module.End ℂ S) (x y : S) :
    leftResponse A (x ⊗ₜ[ℂ] y) = A x ⊗ₜ[ℂ] y := by
  simp [leftResponse, TensorProduct.map_tmul]

theorem rightResponse_tmul (A : Module.End ℂ S) (x y : S) :
    rightResponse A (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] A y := by
  simp [rightResponse, TensorProduct.map_tmul]

theorem left_right_product (A B : Module.End ℂ S) :
    leftResponse A * rightResponse B = TensorProduct.map A B := by
  change TensorProduct.map A 1 * TensorProduct.map 1 B = _
  simp only [← TensorProduct.map_mul, mul_one, one_mul]

theorem left_right_commute (A B : Module.End ℂ S) :
    Commute (leftResponse A) (rightResponse B) := by
  change leftResponse A * rightResponse B = rightResponse B * leftResponse A
  rw [left_right_product]
  change _ = TensorProduct.map 1 B * TensorProduct.map A 1
  simp only [← TensorProduct.map_mul, mul_one, one_mul]

/-- Algebraic generation from two independently variable actual sources. -/
def responseAlgebra : Subalgebra ℂ (Module.End ℂ C) :=
  Algebra.adjoin ℂ
    (Set.range (fun U : SU2 => leftResponse (sourceOperator 1 U)) ∪
      Set.range (fun V : SU2 => rightResponse (sourceOperator 1 V)))

theorem leftSource_mem (U : SU2) : leftResponse (sourceOperator 1 U) ∈ responseAlgebra :=
  Algebra.subset_adjoin (Or.inl (Set.mem_range_self U))

theorem rightSource_mem (V : SU2) : rightResponse (sourceOperator 1 V) ∈ responseAlgebra :=
  Algebra.subset_adjoin (Or.inr (Set.mem_range_self V))

/-- No full-response or irreducibility premise is imposed on the tensor square.
Fullness follows from the separately proved defining-source generation on
each factor and the finite tensor-Hom equivalence. -/
theorem containing_independent_sources_eq_top
    (A : Subalgebra ℂ (Module.End ℂ C))
    (hL : ∀ U : SU2, leftResponse (sourceOperator 1 U) ∈ A)
    (hR : ∀ V : SU2, rightResponse (sourceOperator 1 V) ∈ A) : A = ⊤ := by
  have hl : ∀ T : Module.End ℂ S, leftResponse T ∈ A := by
    have he : A.comap leftResponse = ⊤ :=
      SourceJointResponse.containing_spin_source_eq_top (A.comap leftResponse) hL
    intro T
    change T ∈ A.comap leftResponse
    rw [he]
    trivial
  have hr : ∀ T : Module.End ℂ S, rightResponse T ∈ A := by
    have he : A.comap rightResponse = ⊤ :=
      SourceJointResponse.containing_spin_source_eq_top (A.comap rightResponse) hR
    intro T
    change T ∈ A.comap rightResponse
    rw [he]
    trivial
  have ht : ∀ T U : Module.End ℂ S, TensorProduct.map T U ∈ A := by
    intro T U
    rw [← left_right_product]
    exact A.mul_mem (hl T) (hr U)
  apply top_unique
  intro T hT
  clear hT
  obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ S S S S).surjective T
  induction t using TensorProduct.inductionOn with
  | tmul T U =>
      simpa only [homTensorHomEquiv_apply,
        TensorProduct.homTensorHomMap_apply] using ht T U
  | add t u ht hu => simpa only [map_add] using A.add_mem ht hu

theorem responseAlgebra_eq_top : responseAlgebra = ⊤ :=
  containing_independent_sources_eq_top responseAlgebra leftSource_mem rightSource_mem

theorem end_mem_responseAlgebra (A : Module.End ℂ C) : A ∈ responseAlgebra := by
  rw [responseAlgebra_eq_top]
  trivial

/-- The source tensor square is used unchanged as the colour factor. -/
def colourAction : Module.End ℂ C →ₐ[ℂ] Module.End ℂ FullCarrier where
  toFun A := TensorProduct.map A 1
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp [TensorProduct.map_add_left]
  map_mul' A B := by simp only [← TensorProduct.map_mul, mul_one]
  commutes' c := by
    simp [Algebra.algebraMap_eq_smul_one, TensorProduct.map_smul_left]

def spinLift (h : Module.End ℂ S) : Module.End ℂ FullCarrier := TensorProduct.map 1 h

/-- The input connector is an arbitrary complex-linear map on the full carrier. -/
def SourceNatural (T : Module.End ℂ FullCarrier) : Prop :=
  (∀ U : SU2, T * colourAction (leftResponse (sourceOperator 1 U)) =
    colourAction (leftResponse (sourceOperator 1 U)) * T) ∧
  (∀ V : SU2, T * colourAction (rightResponse (sourceOperator 1 V)) =
    colourAction (rightResponse (sourceOperator 1 V)) * T)

def Natural (T : Module.End ℂ FullCarrier) : Prop :=
  ∀ A : Module.End ℂ C, T * colourAction A = colourAction A * T

private def naturalColourAlgebra (T : Module.End ℂ FullCarrier) :
    Subalgebra ℂ (Module.End ℂ C) :=
  (Subalgebra.centralizer ℂ ({T} : Set (Module.End ℂ FullCarrier))).comap colourAction

private theorem mem_naturalColourAlgebra (T : Module.End ℂ FullCarrier)
    (A : Module.End ℂ C) :
    A ∈ naturalColourAlgebra T ↔ T * colourAction A = colourAction A * T := by
  simp only [naturalColourAlgebra, Subalgebra.mem_comap,
    Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

/-- Naturality for the actual independent sources already implies naturality
for every colour endomorphism, by their proved algebraic generation. -/
theorem sourceNatural_iff_natural (T : Module.End ℂ FullCarrier) :
    SourceNatural T ↔ Natural T := by
  constructor
  · rintro ⟨hL, hR⟩
    have he : naturalColourAlgebra T = ⊤ :=
      containing_independent_sources_eq_top (naturalColourAlgebra T)
        (fun U => (mem_naturalColourAlgebra T _).mpr (hL U))
        (fun V => (mem_naturalColourAlgebra T _).mpr (hR V))
    intro A
    apply (mem_naturalColourAlgebra T A).mp
    rw [he]
    trivial
  · intro hT
    exact ⟨fun U => hT _, fun V => hT _⟩

theorem colour_finrank : Module.finrank ℂ C = 4 := by
  simp [C, Geometry.SourceQuadraticSplit.TensorSquare,
    Geometry.SourceQuadraticSplit.Spin, Module.finrank_tensorProduct, hilbertCarrier_finrank]

theorem spin_finrank : Module.finrank ℂ S = 2 := hilbertCarrier_finrank 1

def colourBasis : OrthonormalBasis (Fin 4) ℂ C :=
  (stdOrthonormalBasis ℂ C).reindex (finCongr colour_finrank)

def spinBasis : OrthonormalBasis (Fin 2) ℂ S :=
  (stdOrthonormalBasis ℂ S).reindex (finCongr spin_finrank)

def fullBasis : OrthonormalBasis (Fin 4 × Fin 2) ℂ FullCarrier :=
  colourBasis.tensorProduct spinBasis

theorem fullBasis_toBasis :
    fullBasis.toBasis = colourBasis.toBasis.tensorProduct spinBasis.toBasis :=
  OrthonormalBasis.toBasis_tensorProduct colourBasis spinBasis

def colourCoordinates : Module.End ℂ C ≃ₐ[ℂ] ColourNaturalConnector.ColourMatrix 4 :=
  LinearMap.toMatrixAlgEquiv colourBasis.toBasis

def spinCoordinates : Module.End ℂ S ≃ₐ[ℂ] Mat2 :=
  LinearMap.toMatrixAlgEquiv spinBasis.toBasis

def connectorCoordinates :
    Module.End ℂ FullCarrier ≃ₐ[ℂ] ColourNaturalConnector.Connector 4 :=
  LinearMap.toMatrixAlgEquiv fullBasis.toBasis

theorem tensorCoordinates {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (e : Module.Basis (Fin 4) ℂ E) (f : Module.Basis (Fin 2) ℂ F)
    (b : Module.Basis (Fin 4 × Fin 2) ℂ (E ⊗[ℂ] F))
    (hb : b = e.tensorProduct f) (A : Module.End ℂ E) (h : Module.End ℂ F) :
    LinearMap.toMatrix b b (TensorProduct.map A h) =
      LinearMap.toMatrix e e A ⊗ₖ LinearMap.toMatrix f f h := by
  rw [hb]
  exact TensorProduct.toMatrix_map e f e f A h

/-- The coordinate map intertwines genuine tensor endomorphisms with their
Kronecker matrices; it does not merely compare carrier dimensions. -/
theorem connectorCoordinates_tensor (A : Module.End ℂ C) (h : Module.End ℂ S) :
    connectorCoordinates (TensorProduct.map A h) =
      colourCoordinates A ⊗ₖ spinCoordinates h := by
  change LinearMap.toMatrix fullBasis.toBasis fullBasis.toBasis
    (TensorProduct.map A h) =
      LinearMap.toMatrix colourBasis.toBasis colourBasis.toBasis A ⊗ₖ
        LinearMap.toMatrix spinBasis.toBasis spinBasis.toBasis h
  exact tensorCoordinates colourBasis.toBasis spinBasis.toBasis fullBasis.toBasis
    fullBasis_toBasis A h

theorem connectorCoordinates_colourAction (A : Module.End ℂ C) :
    connectorCoordinates (colourAction A) =
      ColourNaturalConnector.colourAction (colourCoordinates A) := by
  change connectorCoordinates (TensorProduct.map A 1) = _
  rw [connectorCoordinates_tensor, map_one]
  rfl

theorem connectorCoordinates_spinLift (h : Module.End ℂ S) :
    connectorCoordinates (spinLift h) =
      ColourNaturalConnector.spinLift 4 (spinCoordinates h) := by
  change connectorCoordinates (TensorProduct.map 1 h) = _
  rw [connectorCoordinates_tensor, map_one]
  rfl

theorem natural_iff_matrixNatural (T : Module.End ℂ FullCarrier) :
    Natural T ↔ ColourNaturalConnector.Natural (connectorCoordinates T) := by
  constructor
  · intro hT M
    obtain ⟨A, rfl⟩ := colourCoordinates.surjective M
    have h := congrArg connectorCoordinates (hT A)
    simpa only [map_mul, connectorCoordinates_colourAction] using h
  · intro hT A
    apply connectorCoordinates.injective
    simpa only [map_mul, connectorCoordinates_colourAction] using hT (colourCoordinates A)

theorem spinLift_injective : Function.Injective spinLift := by
  intro h k he
  apply spinCoordinates.injective
  apply ColourNaturalConnector.spinLift_injective 4
  have hm := congrArg connectorCoordinates he
  simpa only [connectorCoordinates_spinLift] using hm

theorem spinLift_natural (h : Module.End ℂ S) : Natural (spinLift h) := by
  apply (natural_iff_matrixNatural _).mpr
  rw [connectorCoordinates_spinLift]
  exact ColourNaturalConnector.spinLift_natural 4 _

/-- Every arbitrary natural connector on the actual pre-exchange carrier
has one unique spinor endomorphism, shared by all colour directions. -/
theorem natural_iff_existsUnique_spinor (T : Module.End ℂ FullCarrier) :
    Natural T ↔ ∃! h : Module.End ℂ S, T = spinLift h := by
  constructor
  · intro hT
    obtain ⟨M, hM, _⟩ :=
      (ColourNaturalConnector.natural_iff_existsUnique_spinor (connectorCoordinates T)).mp
        ((natural_iff_matrixNatural T).mp hT)
    have he : T = spinLift (spinCoordinates.symm M) := by
      apply connectorCoordinates.injective
      rw [connectorCoordinates_spinLift, spinCoordinates.apply_symm_apply]
      exact hM
    refine ⟨spinCoordinates.symm M, he, ?_⟩
    intro h hh
    exact spinLift_injective (hh.symm.trans he)
  · rintro ⟨h, rfl, _⟩
    exact spinLift_natural h

/-- The hypotheses mention only the two actual independent source actions;
the full algebra and the tensor factorization are both conclusions. -/
theorem sourceNatural_iff_existsUnique_spinor (T : Module.End ℂ FullCarrier) :
    SourceNatural T ↔ ∃! h : Module.End ℂ S, T = spinLift h := by
  rw [sourceNatural_iff_natural, natural_iff_existsUnique_spinor]

theorem natural_connector_tmul {T : Module.End ℂ FullCarrier}
    (hT : SourceNatural T) :
    ∃! h : Module.End ℂ S, ∀ c : C, ∀ s : S, T (c ⊗ₜ[ℂ] s) = c ⊗ₜ[ℂ] h s := by
  obtain ⟨h, hh, hu⟩ := (sourceNatural_iff_existsUnique_spinor T).mp hT
  refine ⟨h, ?_, ?_⟩
  · intro c s
    rw [hh]
    simp [spinLift, TensorProduct.map_tmul]
  · intro k hk
    apply hu
    apply TensorProduct.ext'
    intro c s
    simpa only [spinLift, TensorProduct.map_tmul, Module.End.one_apply] using hk c s

end GeneratedFoundations.Geometry.SourcePreExchangeResponse
