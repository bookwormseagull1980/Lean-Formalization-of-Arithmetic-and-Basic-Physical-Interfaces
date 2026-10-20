module

public import GeneratedFoundations.Operations.SourceCliffordSectors
public import GeneratedFoundations.Operations.SourceComplexAmplitude

/-!
# Complex even algebra and sectors of the generated source

Complex extension is proved from the explicit source-real decomposition of
all two-by-two matrices. No physical representation or matter dimension
enters this construction. The repetition index is an arbitrary finite
multiplicity used by each branch on its own actual carrier.
-/

@[expose] public section

noncomputable section

open scoped Quaternion Kronecker

namespace GeneratedFoundations.Operations.SourceCliffordComplex

open SourceCliffordConnector SourceCliffordSectors
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open ReversalRealConnector (Mat2)

/-- Complex scalar extension inside the same actual matrix representation. -/
def complexEvenSourceAlgebra : Subalgebra ℂ ChiralMatrix :=
  Algebra.adjoin ℂ (evenSourceAlgebra : Set ChiralMatrix)

theorem complexEvenSourceAlgebra_eq_adjoin_pairs :
    complexEvenSourceAlgebra =
      Algebra.adjoin ℂ {A | ∃ p q : ℍ, A = clifford p * clifford q} := by
  apply le_antisymm
  · have h : evenSourceAlgebra ≤
        (Algebra.adjoin ℂ {A | ∃ p q : ℍ, A = clifford p * clifford q}).restrictScalars ℝ := by
      apply Algebra.adjoin_le
      intro A hA
      change A ∈ Algebra.adjoin ℂ {A | ∃ p q : ℍ, A = clifford p * clifford q}
      exact Algebra.subset_adjoin (R := ℂ) hA
    exact Algebra.adjoin_le h
  · apply Algebra.adjoin_le
    rintro A ⟨p, q, rfl⟩
    exact Algebra.subset_adjoin (clifford_mul_mem p q)

def complexPairMap : (Mat2 × Mat2) →ₐ[ℂ] ChiralMatrix where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_zero' := by simp
  map_one' := Matrix.fromBlocks_one
  map_add' p q := by simp [Matrix.fromBlocks_add]
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]
  commutes' r := by
    change Matrix.fromBlocks (algebraMap ℂ Mat2 r) 0 0 (algebraMap ℂ Mat2 r) =
      algebraMap ℂ ChiralMatrix r
    simp only [Algebra.algebraMap_eq_smul_one]
    simpa only [Matrix.fromBlocks_smul, smul_zero] using
      congrArg (fun M : ChiralMatrix => r • M)
        (Matrix.fromBlocks_one : Matrix.fromBlocks (1 : Mat2) 0 0 1 = (1 : ChiralMatrix))

theorem complexPairMap_injective : Function.Injective complexPairMap := by
  intro p q h
  apply Prod.ext
  · ext i j
    exact congrArg (fun M : ChiralMatrix => M (Sum.inl i) (Sum.inl j)) h
  · ext i j
    exact congrArg (fun M : ChiralMatrix => M (Sum.inr i) (Sum.inr j)) h

private def diagonalMap : Mat2 →ₐ[ℂ] ChiralMatrix :=
  complexPairMap.comp ((AlgHom.id ℂ Mat2).prod (AlgHom.id ℂ Mat2))

theorem complexPairMap_adjoint (p : Mat2 × Mat2) :
    (complexPairMap p).conjTranspose =
      complexPairMap (p.1.conjTranspose, p.2.conjTranspose) := by
  simp [complexPairMap, Matrix.fromBlocks_conjTranspose]

private theorem diagonalMap_mem_complexEven (M : Mat2) :
    diagonalMap M ∈ complexEvenSourceAlgebra := by
  have hq (q : ℍ) : diagonalMap (matrixMap q) = pairMap (q, q) := rfl
  rw [SourceComplexAmplitude.matrix_decomposition M, map_add, map_smul, hq, hq]
  exact complexEvenSourceAlgebra.add_mem
    (Algebra.subset_adjoin (pairMap_mem_even _))
    (complexEvenSourceAlgebra.smul_mem
      (Algebra.subset_adjoin (pairMap_mem_even _)) Complex.I)

theorem complexPairMap_mem (p : Mat2 × Mat2) : complexPairMap p ∈ complexEvenSourceAlgebra := by
  have h : complexPairMap p = positiveProjection * diagonalMap p.1 +
      negativeProjection * diagonalMap p.2 := by
    simp [complexPairMap, positiveProjection, negativeProjection, diagonalMap, pairMap,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  rw [h]
  exact complexEvenSourceAlgebra.add_mem
    (complexEvenSourceAlgebra.mul_mem (Algebra.subset_adjoin positiveProjection_mem_even)
      (diagonalMap_mem_complexEven p.1))
    (complexEvenSourceAlgebra.mul_mem (Algebra.subset_adjoin negativeProjection_mem_even)
      (diagonalMap_mem_complexEven p.2))

theorem complexEvenSourceAlgebra_eq_range : complexEvenSourceAlgebra = complexPairMap.range := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro A hA
    rw [evenSourceAlgebra_eq_range] at hA
    obtain ⟨p, rfl⟩ := hA
    exact ⟨(matrixMap p.1, matrixMap p.2), rfl⟩
  · rintro A ⟨p, rfl⟩
    exact complexPairMap_mem p

/-- The complex even algebra has exactly the two existing two-by-two factors. -/
def complexEvenEquiv : (Mat2 × Mat2) ≃ₐ[ℂ] complexEvenSourceAlgebra :=
  AlgEquiv.ofBijective (complexPairMap.codRestrict complexEvenSourceAlgebra complexPairMap_mem)
    ⟨fun p q h => complexPairMap_injective (congrArg Subtype.val h), by
      rintro ⟨A, hA⟩
      rw [complexEvenSourceAlgebra_eq_range] at hA
      obtain ⟨p, rfl⟩ := hA
      exact ⟨p, rfl⟩⟩

abbrev SpinorCarrier := ChiralIndex → ℂ

theorem positiveProjection_mulVec (v : SpinorCarrier) :
    positiveProjection.mulVec v = Sum.elim (fun i => v (Sum.inl i)) (fun _ => 0) := by
  ext i
  rcases i with i | i <;>
    simp [positiveProjection, pairMap, Matrix.fromBlocks_mulVec]

theorem negativeProjection_mulVec (v : SpinorCarrier) :
    negativeProjection.mulVec v = Sum.elim (fun _ => 0) (fun i => v (Sum.inr i)) := by
  ext i
  rcases i with i | i <;>
    simp [negativeProjection, pairMap, Matrix.fromBlocks_mulVec]

def positiveSpace : Submodule ℂ SpinorCarrier := LinearMap.range positiveProjection.mulVecLin
def negativeSpace : Submodule ℂ SpinorCarrier := LinearMap.range negativeProjection.mulVecLin

def positiveCoordinates : (Fin 2 → ℂ) ≃ₗ[ℂ] positiveSpace where
  toFun v := ⟨Sum.elim v (fun _ => 0), ⟨Sum.elim v (fun _ => 0), by
    change positiveProjection.mulVec _ = _
    rw [positiveProjection_mulVec]
    rfl⟩⟩
  invFun v i := v.val (Sum.inl i)
  left_inv v := rfl
  right_inv v := by
    rcases v with ⟨v, ⟨w, rfl⟩⟩
    apply Subtype.ext
    change Sum.elim (fun i => positiveProjection.mulVec w (Sum.inl i)) (fun _ => 0) =
      positiveProjection.mulVec w
    simp only [positiveProjection_mulVec, Sum.elim_inl]
  map_add' v w := by
    apply Subtype.ext
    ext i
    rcases i with i | i <;> simp
  map_smul' r v := by
    apply Subtype.ext
    ext i
    rcases i with i | i <;> simp

def negativeCoordinates : (Fin 2 → ℂ) ≃ₗ[ℂ] negativeSpace where
  toFun v := ⟨Sum.elim (fun _ => 0) v, ⟨Sum.elim (fun _ => 0) v, by
    change negativeProjection.mulVec _ = _
    rw [negativeProjection_mulVec]
    rfl⟩⟩
  invFun v i := v.val (Sum.inr i)
  left_inv v := rfl
  right_inv v := by
    rcases v with ⟨v, ⟨w, rfl⟩⟩
    apply Subtype.ext
    change Sum.elim (fun _ => 0) (fun i => negativeProjection.mulVec w (Sum.inr i)) =
      negativeProjection.mulVec w
    simp only [negativeProjection_mulVec, Sum.elim_inr]
  map_add' v w := by
    apply Subtype.ext
    ext i
    rcases i with i | i <;> simp
  map_smul' r v := by
    apply Subtype.ext
    ext i
    rcases i with i | i <;> simp

theorem positiveSpace_finrank : Module.finrank ℂ positiveSpace = 2 := by
  rw [← positiveCoordinates.finrank_eq, Module.finrank_fintype_fun_eq_card]
  rfl

theorem negativeSpace_finrank : Module.finrank ℂ negativeSpace = 2 := by
  rw [← negativeCoordinates.finrank_eq, Module.finrank_fintype_fun_eq_card]
  rfl

theorem positiveProjection_formula_complex :
    positiveProjection = (1 / 2 : ℂ) • (1 + grading) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [positiveProjection, pairMap, grading, Matrix.one_apply]
  all_goals split_ifs <;> norm_num

theorem negativeProjection_formula_complex :
    negativeProjection = (1 / 2 : ℂ) • (1 - grading) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [negativeProjection, pairMap, grading, Matrix.one_apply]
  all_goals split_ifs <;> norm_num

/-- Repetition leaves the two actual source projections unchanged. -/
def colourPositive (d : ℕ) : ColourMatrix d :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ positiveProjection

def colourNegative (d : ℕ) : ColourMatrix d :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ negativeProjection

theorem colourPositive_formula (d : ℕ) :
    colourPositive d = (1 / 2 : ℂ) • (1 + colourGrading d) := by
  rw [colourPositive, positiveProjection_formula_complex, Matrix.kronecker_smul,
    Matrix.kronecker_add, Matrix.one_kronecker_one]
  rfl

theorem colourNegative_formula (d : ℕ) :
    colourNegative d = (1 / 2 : ℂ) • (1 - colourGrading d) := by
  have hsub : (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (1 - grading) =
      (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (1 : ChiralMatrix) -
        (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ grading := by
    ext ⟨i, a⟩ ⟨j, b⟩
    exact mul_sub _ _ _
  rw [colourNegative, negativeProjection_formula_complex, Matrix.kronecker_smul,
    hsub, Matrix.one_kronecker_one]
  rfl

/-- An arbitrary complex response and its adjoint form one odd self-adjoint
    connector. Its input is a response observable, not a new source datum. -/
def connector (M : Mat2) : ChiralMatrix :=
  Matrix.fromBlocks 0 M M.conjTranspose 0

theorem connector_adjoint (M : Mat2) : (connector M).conjTranspose = connector M := by
  simp [connector, Matrix.fromBlocks_conjTranspose]

theorem connector_injective : Function.Injective connector := by
  intro M N h
  ext i j
  exact congrArg (fun A : ChiralMatrix => A (Sum.inl i) (Sum.inr j)) h

theorem connector_square (M : Mat2) :
    connector M * connector M = Matrix.fromBlocks (M * M.conjTranspose) 0 0
      (M.conjTranspose * M) := by
  simp [connector, Matrix.fromBlocks_multiply]

theorem connector_square_of_unitary (M : Mat2)
    (hl : M * M.conjTranspose = 1) (hr : M.conjTranspose * M = 1) :
    connector M * connector M = 1 := by
  rw [connector_square, hl, hr, Matrix.fromBlocks_one]

theorem connector_odd (M : Mat2) :
    grading * connector M + connector M * grading = 0 := by
  simp [grading, connector, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]

theorem connector_matrixMap (q : ℍ) : connector (matrixMap q) = clifford q := by
  simp [connector, clifford]

theorem connector_positive (M : Mat2) :
    positiveProjection * connector M = connector M * negativeProjection := by
  simp [positiveProjection, negativeProjection, pairMap, connector, Matrix.fromBlocks_multiply]

theorem connector_negative (M : Mat2) :
    negativeProjection * connector M = connector M * positiveProjection := by
  simp [positiveProjection, negativeProjection, pairMap, connector, Matrix.fromBlocks_multiply]

theorem connector_even_product (M N : Mat2) :
    connector M * connector N ∈ complexEvenSourceAlgebra := by
  rw [complexEvenSourceAlgebra_eq_range]
  exact ⟨(M * N.conjTranspose, M.conjTranspose * N), by
    simp [complexPairMap, connector, Matrix.fromBlocks_multiply]⟩

/-- Independent changes on the two source sectors act on the connector
    by left/right congruence, before any unitary conditions are imposed. -/
theorem connector_covariance (p : Mat2 × Mat2) (M : Mat2) :
    complexPairMap p * connector M * (complexPairMap p).conjTranspose =
      connector (p.1 * M * p.2.conjTranspose) := by
  simp [complexPairMap, connector, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul, mul_assoc]

end GeneratedFoundations.Operations.SourceCliffordComplex
