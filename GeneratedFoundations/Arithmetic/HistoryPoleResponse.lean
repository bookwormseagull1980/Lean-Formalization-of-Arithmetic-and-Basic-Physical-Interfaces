module

public import GeneratedFoundations.Arithmetic.HistoryCliffordAction
public import GeneratedFoundations.Analysis.HistoryPrefixGibbsResponse
public import GeneratedFoundations.Operations.BlockResolventResponse

/-!
# Pole response on the complete arithmetic history--phase carrier

The source chirality already decomposes every actual history--phase fibre
into two orthogonal sectors. Reindexing the existing full matrix algebra
along this decomposition keeps every cross-history entry. The retained,
coupling and complementary blocks below are restrictions of that one
operator, rather than separately supplied coefficients.

Elimination is performed only in the resolvent domain of the complementary
block. Its energy-dependent inverse fixes both the lifted eigenvector and
its positive normalization. The two trace orderings of a normalized state
are retained together. The constructed Gaussian state uses the actual
prefix probabilities and the four source coordinates; it does not make
the positive roots equiprobable.

Source chirality and prime-occupation parity remain different gradings.
No assertion that a general configured operator preserves either grading
is used. All results are internal operations of the generated carrier.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix ComplexOrder Kronecker Quaternion Matrix.Norms.Operator

namespace GeneratedFoundations.Arithmetic.HistoryPoleResponse

open HistoryCliffordAction (HistoryLabel Index Algebra sourceMatrix)
open Operations

abbrev SectorIndex (N : ℕ) := HistoryLabel N × Fin 2
abbrev SectorMatrix (N : ℕ) := Matrix (SectorIndex N) (SectorIndex N) ℂ

def sectorIndexEquiv (N : ℕ) : Index N ≃ SectorIndex N ⊕ SectorIndex N :=
  Equiv.prodSumDistrib (HistoryLabel N) (Fin 2) (Fin 2)

/-- An algebra equivalence, so every full operator and every product is
retained before any complementary coordinate is eliminated. -/
def coordinates (N : ℕ) : Algebra N ≃ₐ[ℂ]
    Matrix (SectorIndex N ⊕ SectorIndex N) (SectorIndex N ⊕ SectorIndex N) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (sectorIndexEquiv N)

def retained (N : ℕ) (H : Algebra N) : SectorMatrix N :=
  fun i j => H (i.1, Sum.inl i.2) (j.1, Sum.inl j.2)

def coupling (N : ℕ) (H : Algebra N) : SectorMatrix N :=
  fun i j => H (i.1, Sum.inr i.2) (j.1, Sum.inl j.2)

def complementary (N : ℕ) (H : Algebra N) : SectorMatrix N :=
  fun i j => H (i.1, Sum.inr i.2) (j.1, Sum.inr j.2)

theorem retained_hermitian (N : ℕ) (H : Algebra N) (hH : Hᴴ = H) :
    (retained N H)ᴴ = retained N H := by
  ext i j
  exact congrArg (fun X : Algebra N => X (i.1, Sum.inl i.2) (j.1, Sum.inl j.2)) hH

theorem complementary_hermitian (N : ℕ) (H : Algebra N) (hH : Hᴴ = H) :
    (complementary N H)ᴴ = complementary N H := by
  ext i j
  exact congrArg (fun X : Algebra N => X (i.1, Sum.inr i.2) (j.1, Sum.inr j.2)) hH

theorem full_reconstruction (N : ℕ) (H : Algebra N) (hH : Hᴴ = H) :
    coordinates N H = Matrix.fromBlocks
      (retained N H) (coupling N H)ᴴ (coupling N H) (complementary N H) := by
  ext i j
  cases i with
  | inl a =>
    cases j with
    | inl b => rfl
    | inr b =>
      exact (congrArg (fun X : Algebra N =>
        X (a.1, Sum.inl a.2) (b.1, Sum.inr b.2)) hH).symm
  | inr a => cases j <;> rfl

/-- The full block coordinates and the existing unitary sector coordinates
act on the same vector coefficients. -/
theorem coordinates_mulVec (N : ℕ) (H : Algebra N) (x : Index N → ℂ) :
    coordinates N H *ᵥ (x ∘ (sectorIndexEquiv N).symm) =
      (H *ᵥ x) ∘ (sectorIndexEquiv N).symm := by
  simpa only [coordinates, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Function.comp_def, Equiv.symm_apply_apply] using
    Matrix.submatrix_mulVec_equiv H (x ∘ (sectorIndexEquiv N).symm)
      (sectorIndexEquiv N).symm (sectorIndexEquiv N).symm

def inverseResponse (N : ℕ) (H : Algebra N) (R : SectorMatrix N) (z : ℂ) :
    SectorMatrix N :=
  BlockResolventResponse.reducedKernel (retained N H) (coupling N H) R z

def normalization (N : ℕ) (H : Algebra N) (R : SectorMatrix N) : SectorMatrix N :=
  BlockResolventResponse.returnMetric (coupling N H) R

def lift (N : ℕ) (H : Algebra N) (R : SectorMatrix N) :=
  BlockResolventResponse.eigenvectorLift (R * coupling N H)

theorem lift_gram (N : ℕ) (H : Algebra N) (R : SectorMatrix N) :
    (lift N H R)ᴴ * lift N H R = normalization N H R :=
  BlockResolventResponse.eigenvectorLift_gram _

theorem normalization_posDef (N : ℕ) (H : Algebra N) (R : SectorMatrix N) :
    (normalization N H R).PosDef :=
  BlockResolventResponse.returnMetric_posDef _ _

theorem normalization_eq (N : ℕ) (H : Algebra N) (R : SectorMatrix N)
    (hR : Rᴴ = R) :
    normalization N H R = 1 + (coupling N H)ᴴ * R * R * coupling N H :=
  BlockResolventResponse.returnMetric_eq _ _ hR

theorem lifted_equation_iff (N : ℕ) (H : Algebra N) (hH : Hᴴ = H)
    (R : SectorMatrix N) (z : ℂ)
    (hR : (z • 1 - complementary N H) * R = 1) (u : SectorIndex N → ℂ) :
    coordinates N H *ᵥ (lift N H R *ᵥ u) = z • (lift N H R *ᵥ u) ↔
      inverseResponse N H R z *ᵥ u = 0 := by
  rw [full_reconstruction N H hH]
  exact BlockResolventResponse.eigenvectorLift_equation_iff _ _ _ _ _ hR u

/-- The native vector is the same lifted vector in the original complete
history--phase coordinates. -/
def nativeLift (N : ℕ) (H : Algebra N) (R : SectorMatrix N)
    (u : SectorIndex N → ℂ) : Index N → ℂ :=
  (lift N H R *ᵥ u) ∘ sectorIndexEquiv N

theorem native_lifted_equation_iff (N : ℕ) (H : Algebra N) (hH : Hᴴ = H)
    (R : SectorMatrix N) (z : ℂ)
    (hR : (z • 1 - complementary N H) * R = 1) (u : SectorIndex N → ℂ) :
    H *ᵥ nativeLift N H R u = z • nativeLift N H R u ↔
      inverseResponse N H R z *ᵥ u = 0 := by
  have h := coordinates_mulVec N H (nativeLift N H R u)
  have hc : (nativeLift N H R u) ∘ (sectorIndexEquiv N).symm = lift N H R *ᵥ u := by
    ext i
    simp [nativeLift, Function.comp_def]
  rw [hc] at h
  rw [← lifted_equation_iff N H hH R z hR u, h]
  constructor
  · intro he
    funext i
    simpa [Function.comp_def, nativeLift] using congrFun he ((sectorIndexEquiv N).symm i)
  · intro he
    funext i
    have hi := congrFun he (sectorIndexEquiv N i)
    simpa [Function.comp_def, nativeLift] using hi

theorem inverse_difference (N : ℕ) (H : Algebra N) (Rz Rw : SectorMatrix N)
    (z w : ℂ) (hz : Rz * (z • 1 - complementary N H) = 1)
    (hw : (w • 1 - complementary N H) * Rw = 1) :
    inverseResponse N H Rz z - inverseResponse N H Rw w =
      (z - w) • (1 + (coupling N H)ᴴ * Rz * Rw * coupling N H) :=
  BlockResolventResponse.reducedKernel_difference _ _ _ _ _ _ _ hz hw

theorem complement_inverse_difference (N : ℕ) (H : Algebra N)
    (Rz Rw : SectorMatrix N) (z w : ℂ)
    (hz : Rz * (z • 1 - complementary N H) = 1)
    (hw : (w • 1 - complementary N H) * Rw = 1) :
    Rz - Rw = (w - z) • (Rz * Rw) :=
  BlockResolventResponse.complement_resolvent_difference _ _ _ _ _ hz hw

theorem complement_derivative (N : ℕ) (H : Algebra N) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (complementary N H)) :
    HasDerivAt (resolvent (complementary N H))
      (-(resolvent (complementary N H) z) ^ 2) z :=
  BlockResolventResponse.complement_resolvent_derivative _ _ hz

theorem inverse_derivative (N : ℕ) (H : Algebra N) (z : ℂ)
    (hz : z ∈ resolventSet ℂ (complementary N H)) :
    HasDerivAt (fun w : ℂ => inverseResponse N H
      (resolvent (complementary N H) w) w)
      (1 + (coupling N H)ᴴ * resolvent (complementary N H) z *
        resolvent (complementary N H) z * coupling N H) z :=
  BlockResolventResponse.reducedKernel_resolvent_derivative _ _ _ _ hz

/-- The derivative coefficient at a real energy is the positive
normalization of the same reconstructed full vector. -/
theorem inverse_real_derivative (N : ℕ) (H : Algebra N) (hH : Hᴴ = H)
    (r : ℝ) (hr : (r : ℂ) ∈ resolventSet ℂ (complementary N H)) :
    HasDerivAt (fun w : ℂ => inverseResponse N H
      (resolvent (complementary N H) w) w)
      (normalization N H (resolvent (complementary N H) (r : ℂ))) (r : ℂ) :=
  BlockResolventResponse.reducedKernel_real_derivative _ _ _
    (complementary_hermitian N H hH) r hr

/-- The original Gaussian marginal is spread only over the four already
generated source coordinates. Every root keeps its actual probability. -/
def stateWeight (N : ℕ) (alpha L : ℝ) (i : Index N) : ℝ :=
  Analysis.HistoryPrefixGibbsResponse.probability N alpha L i.1 / 4

theorem stateWeight_pos (N : ℕ) (alpha L : ℝ) (i : Index N) :
    0 < stateWeight N alpha L i :=
  div_pos (Analysis.HistoryPrefixGibbsResponse.probability_pos _ _ _ _) (by norm_num)

theorem stateWeight_total (N : ℕ) (alpha L : ℝ) :
    (∑ i : Index N, stateWeight N alpha L i) = 1 := by
  simp only [stateWeight, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    SourceCliffordConnector.ChiralIndex, Fintype.card_sum, Fintype.card_fin]
  convert Analysis.HistoryPrefixGibbsResponse.probability_total N alpha L using 1
  apply Finset.sum_congr rfl
  intro i _
  norm_num
  ring

theorem stateWeight_history_marginal (N : ℕ) (alpha L : ℝ) (h : HistoryLabel N) :
    (∑ s : SourceCliffordConnector.ChiralIndex, stateWeight N alpha L (h, s)) =
      Analysis.HistoryPrefixGibbsResponse.probability N alpha L h := by
  simp only [stateWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    SourceCliffordConnector.ChiralIndex, Fintype.card_sum, Fintype.card_fin]
  norm_num
  ring

def stateSqrt (N : ℕ) (alpha L : ℝ) : Algebra N :=
  Matrix.diagonal fun i => (Real.sqrt (stateWeight N alpha L i) : ℂ)

theorem stateSqrt_hermitian (N : ℕ) (alpha L : ℝ) :
    (stateSqrt N alpha L)ᴴ = stateSqrt N alpha L := by
  simp [stateSqrt, Matrix.diagonal_conjTranspose]

theorem stateSqrt_square (N : ℕ) (alpha L : ℝ) :
    stateSqrt N alpha L * stateSqrt N alpha L =
      Matrix.diagonal (fun i => (stateWeight N alpha L i : ℂ)) := by
  rw [stateSqrt, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (stateWeight_pos N alpha L i).le]

theorem stateSqrt_trace (N : ℕ) (alpha L : ℝ) :
    Matrix.trace (stateSqrt N alpha L * stateSqrt N alpha L) = 1 := by
  rw [stateSqrt_square, Matrix.trace_diagonal, ← Complex.ofReal_sum,
    stateWeight_total, Complex.ofReal_one]

/-- Both source orderings are tested in the same complete state. This
statement permits off-diagonal states as well as the constructed Gaussian. -/
theorem joint_state_gram (N : ℕ) (S ci cj : Algebra N) (hS : Sᴴ = S) :
    Matrix.trace ((ciᴴ * S)ᴴ * (cjᴴ * S)) +
      Matrix.trace ((S * ciᴴ)ᴴ * (S * cjᴴ)) =
        Matrix.trace ((S * S) * (ci * cjᴴ + cjᴴ * ci)) :=
  BlockResolventResponse.jointState_gram S ci cj hS

theorem joint_state_normalization (N : ℕ) (S ci cj : Algebra N) (a : ℂ)
    (hS : Sᴴ = S) (htrace : Matrix.trace (S * S) = 1)
    (hcar : ci * cjᴴ + cjᴴ * ci = a • 1) :
    Matrix.trace ((ciᴴ * S)ᴴ * (cjᴴ * S)) +
      Matrix.trace ((S * ciᴴ)ᴴ * (S * cjᴴ)) = a :=
  BlockResolventResponse.jointState_car_normalization S ci cj a hS htrace hcar

theorem source_anticommutator (N : ℕ) (p q : ℍ) :
    sourceMatrix N p * sourceMatrix N q + sourceMatrix N q * sourceMatrix N p =
      (2 * inner ℝ p q) • (1 : Algebra N) := by
  simp only [sourceMatrix, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    ← Matrix.kronecker_add, SourceCliffordConnector.clifford_anticommutator,
    Matrix.kronecker_smul, Matrix.one_kronecker_one]
  ext i j
  simp [Matrix.one_apply]

/-- Exact normalization with actual Gaussian root weights, on every
generated history and phase, including both source orderings. -/
theorem gaussian_source_normalization (N : ℕ) (alpha L : ℝ) (p q : ℍ) :
    Matrix.trace (((sourceMatrix N p)ᴴ * stateSqrt N alpha L)ᴴ *
      ((sourceMatrix N q)ᴴ * stateSqrt N alpha L)) +
      Matrix.trace ((stateSqrt N alpha L * (sourceMatrix N p)ᴴ)ᴴ *
        (stateSqrt N alpha L * (sourceMatrix N q)ᴴ)) = (2 * inner ℝ p q : ℝ) := by
  rw [joint_state_gram N _ _ _ (stateSqrt_hermitian N alpha L)]
  simp only [HistoryCliffordAction.sourceMatrix_adjoint]
  rw [source_anticommutator, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, stateSqrt_trace]
  simp

structure Conclusions : Prop where
  full_operator_reconstruction : ∀ N H, Hᴴ = H →
    coordinates N H = Matrix.fromBlocks
      (retained N H) (coupling N H)ᴴ (coupling N H) (complementary N H)
  positive_normalization : ∀ N H R, (normalization N H R).PosDef
  exact_lift_gram : ∀ N H R, (lift N H R)ᴴ * lift N H R = normalization N H R
  native_eigenvector_equation : ∀ N H, Hᴴ = H → ∀ R z,
    (z • 1 - complementary N H) * R = 1 → ∀ u,
      H *ᵥ nativeLift N H R u = z • nativeLift N H R u ↔
        inverseResponse N H R z *ᵥ u = 0
  kernel_difference : ∀ N H Rz Rw z w,
    Rz * (z • 1 - complementary N H) = 1 →
    (w • 1 - complementary N H) * Rw = 1 →
      inverseResponse N H Rz z - inverseResponse N H Rw w =
        (z - w) • (1 + (coupling N H)ᴴ * Rz * Rw * coupling N H)
  real_normalization_derivative : ∀ N H, Hᴴ = H → ∀ r : ℝ,
    (r : ℂ) ∈ resolventSet ℂ (complementary N H) →
      HasDerivAt (fun w : ℂ => inverseResponse N H
        (resolvent (complementary N H) w) w)
        (normalization N H (resolvent (complementary N H) (r : ℂ))) (r : ℂ)
  complete_normalization : ∀ N (S ci cj : Algebra N) a,
    Sᴴ = S → Matrix.trace (S * S) = 1 → ci * cjᴴ + cjᴴ * ci = a • 1 →
      Matrix.trace ((ciᴴ * S)ᴴ * (cjᴴ * S)) +
        Matrix.trace ((S * ciᴴ)ᴴ * (S * cjᴴ)) = a
  actual_state_trace : ∀ N alpha L,
    Matrix.trace (stateSqrt N alpha L * stateSqrt N alpha L) = 1
  complete_source_gram : ∀ N alpha L p q,
    Matrix.trace (((sourceMatrix N p)ᴴ * stateSqrt N alpha L)ᴴ *
      ((sourceMatrix N q)ᴴ * stateSqrt N alpha L)) +
      Matrix.trace ((stateSqrt N alpha L * (sourceMatrix N p)ᴴ)ᴴ *
        (stateSqrt N alpha L * (sourceMatrix N q)ᴴ)) = (2 * inner ℝ p q : ℝ)

theorem generated : Conclusions where
  full_operator_reconstruction := full_reconstruction
  positive_normalization := normalization_posDef
  exact_lift_gram := lift_gram
  native_eigenvector_equation := native_lifted_equation_iff
  kernel_difference := inverse_difference
  real_normalization_derivative := inverse_real_derivative
  complete_normalization := joint_state_normalization
  actual_state_trace := stateSqrt_trace
  complete_source_gram := gaussian_source_normalization

end GeneratedFoundations.Arithmetic.HistoryPoleResponse
