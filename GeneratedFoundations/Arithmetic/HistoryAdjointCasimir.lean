module

public import GeneratedFoundations.Arithmetic.HistoryGaugeJets
public import GeneratedFoundations.Geometry.HilbertTraceVariation
public import GeneratedFoundations.Operations.MatrixAdjointCasimir

/-!
# Adjoint response of the complete arithmetic operation algebra

Every retained history, phase and source sector contributes to the index.
The full matrix-unit completeness sum is transported through the faithful
operation representation. Its scalar kernel and traceless response are
computed at that generated dimension. This operation-algebra response is a
different operator from the Gaussian-weighted reaction operator on complete
histories; their lower-edge statements are therefore kept distinct.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryAdjointCasimir

open HistoryCliffordAction (Index HistoryLabel Algebra Space action historyPoint)

def dimension (N : ℕ) : ℕ := Fintype.card (Index N)

theorem dimension_eq (N : ℕ) : dimension N = 4 * Fintype.card (HistoryLabel N) := by
  simp [dimension, HistoryCliffordAction.Index,
    Operations.SourceCliffordConnector.ChiralIndex, Nat.mul_comm]

theorem dimension_pos (N : ℕ) : 0 < dimension N :=
  Fintype.card_pos_iff.mpr ⟨(historyPoint N, Sum.inl 0)⟩

theorem dimension_ge_four (N : ℕ) : 4 ≤ dimension N := by
  have hc : 1 ≤ Fintype.card (HistoryLabel N) :=
    Fintype.card_pos_iff.mpr ⟨historyPoint N⟩
  rw [dimension_eq]
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left 4 hc

def responseIndex (N : ℕ) : ℝ := dimension N

theorem responseIndex_eq (N : ℕ) :
    responseIndex N = 4 * (Fintype.card (HistoryLabel N) : ℝ) := by
  change (dimension N : ℝ) = _
  exact_mod_cast dimension_eq N

/-- Remove precisely the scalar part of each actual matrix unit. The family
is redundant, but its complete reconstruction formula is exact. -/
def tracelessUnit (N : ℕ) (i j : Index N) : Algebra N :=
  Matrix.single i j 1 -
    ((if i = j then 1 else 0) / (dimension N : ℂ)) • (1 : Algebra N)

theorem trace_tracelessUnit (N : ℕ) (i j : Index N) :
    Matrix.trace (tracelessUnit N i j) = 0 := by
  have hd : (dimension N : ℂ) ≠ 0 := by exact_mod_cast (dimension_pos N).ne'
  by_cases hij : i = j
  · subst j
    rw [tracelessUnit, ite_eq_left (Eq.refl i), Matrix.trace_sub, Matrix.trace_single_eq_same,
      Matrix.trace_smul, Matrix.trace_one]
    change 1 - (1 / (dimension N : ℂ)) * (dimension N : ℂ) = 0
    simp [hd]
  · simp [tracelessUnit, hij]

theorem tracelessUnit_reconstruct (N : ℕ) (X : Algebra N) :
    (∑ i, ∑ j, X i j • tracelessUnit N i j) =
      X - (Matrix.trace X / (dimension N : ℂ)) • (1 : Algebra N) := by
  have hfirst : (∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ)) = X := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using (Matrix.matrix_eq_sum_single X).symm
  have hsecond : (∑ i, ∑ j, X i j •
      (((if i = j then 1 else 0) / (dimension N : ℂ)) • (1 : Algebra N))) =
      (Matrix.trace X / (dimension N : ℂ)) • (1 : Algebra N) := by
    simp [smul_smul, ← Finset.sum_smul, Matrix.trace, div_eq_mul_inv,
      Finset.sum_mul]
  simp only [tracelessUnit, smul_sub, Finset.sum_sub_distrib]
  rw [hfirst, hsecond]

theorem tracelessUnit_spans (N : ℕ) (X : Algebra N) (hX : Matrix.trace X = 0) :
    (∑ i, ∑ j, X i j • tracelessUnit N i j) = X := by
  simp [tracelessUnit_reconstruct, hX]

def casimir (N : ℕ) (X : Algebra N) : Algebra N :=
  Operations.MatrixAdjointCasimir.casimir X

theorem casimir_eq (N : ℕ) (X : Algebra N) :
    casimir N X = (dimension N : ℂ) • X - Matrix.trace X • (1 : Algebra N) :=
  Operations.MatrixAdjointCasimir.casimir_eq X

theorem casimir_traceless (N : ℕ) (X : Algebra N) (hX : Matrix.trace X = 0) :
    casimir N X = (dimension N : ℂ) • X :=
  Operations.MatrixAdjointCasimir.casimir_traceless X hX

theorem casimir_tracelessUnit (N : ℕ) (i j : Index N) :
    casimir N (tracelessUnit N i j) = (dimension N : ℂ) • tracelessUnit N i j :=
  casimir_traceless N _ (trace_tracelessUnit N i j)

theorem casimir_tracelessUnit_real (N : ℕ) (i j : Index N) :
    casimir N (tracelessUnit N i j) = (responseIndex N : ℂ) • tracelessUnit N i j := by
  simpa [responseIndex] using casimir_tracelessUnit N i j

theorem casimir_kernel (N : ℕ) (X : Algebra N) :
    casimir N X = 0 ↔ ∃ c : ℂ, X = c • (1 : Algebra N) := by
  let _ : Nonempty (Index N) := ⟨(historyPoint N, Sum.inl 0)⟩
  exact Operations.MatrixAdjointCasimir.casimir_kernel X

theorem trace_action (N : ℕ) (X : Algebra N) :
    LinearMap.trace ℂ (Space N) (action N X) = Matrix.trace X := by
  rw [HistoryCliffordAction.action, AlgEquiv.trans_apply, LinearMap.trace_map]
  exact Matrix.trace_toLin'_eq X

def operator (N : ℕ) (X : Module.End ℂ (Space N)) : Module.End ℂ (Space N) :=
  action N (casimir N ((action N).symm X))

theorem operator_eq (N : ℕ) (X : Module.End ℂ (Space N)) :
    operator N X = (dimension N : ℂ) • X -
      LinearMap.trace ℂ (Space N) X • (1 : Module.End ℂ (Space N)) := by
  rw [operator, casimir_eq, map_sub, map_smul, map_smul, map_one,
    AlgEquiv.apply_symm_apply]
  congr 1
  rw [← trace_action N ((action N).symm X), AlgEquiv.apply_symm_apply]

theorem operator_traceless (N : ℕ) (X : Module.End ℂ (Space N))
    (hX : LinearMap.trace ℂ (Space N) X = 0) :
    operator N X = (dimension N : ℂ) • X := by
  simp [operator_eq, hX]

theorem operator_kernel (N : ℕ) (X : Module.End ℂ (Space N)) :
    operator N X = 0 ↔ ∃ c : ℂ, X = c • (1 : Module.End ℂ (Space N)) := by
  constructor
  · intro hX
    have hM : casimir N ((action N).symm X) = 0 := by
      apply (action N).injective
      simpa only [operator, map_zero] using hX
    obtain ⟨c, hc⟩ := (casimir_kernel N _).mp hM
    refine ⟨c, ?_⟩
    simpa only [AlgEquiv.apply_symm_apply, map_smul, map_one] using congrArg (action N) hc
  · rintro ⟨c, rfl⟩
    rw [operator]
    simp only [map_smul, map_one]
    rw [casimir, Operations.MatrixAdjointCasimir.casimir_scalar, map_zero]

theorem traceless_pair (N : ℕ) (X : Module.End ℂ (Space N))
    (hX : LinearMap.trace ℂ (Space N) X = 0) :
    Geometry.HilbertTraceVariation.pair X (operator N X) =
      (dimension N : ℝ) * Geometry.HilbertTraceQuadratic.energy X := by
  rw [operator_traceless N X hX]
  simpa only [Geometry.HilbertTraceVariation.energy_eq_pair,
    Complex.ofReal_natCast, Complex.real_smul] using
    Geometry.HilbertTraceVariation.pair_smul_right (dimension N : ℝ) X X

theorem traceless_pair_pos (N : ℕ) (X : Module.End ℂ (Space N))
    (hX : LinearMap.trace ℂ (Space N) X = 0) (hne : X ≠ 0) :
    0 < Geometry.HilbertTraceVariation.pair X (operator N X) := by
  rw [traceless_pair N X hX]
  apply mul_pos (Nat.cast_pos.mpr (dimension_pos N))
  exact lt_of_le_of_ne (Geometry.HilbertTraceQuadratic.energy_nonneg X)
    (Ne.symm fun h => hne ((Geometry.HilbertTraceQuadratic.energy_eq_zero_iff X).mp h))

theorem casimir_conjugate (N : ℕ) (u : (Algebra N)ˣ) (X : Algebra N) :
    casimir N ((↑u : Algebra N) * X * (↑(u⁻¹) : Algebra N)) =
      (↑u : Algebra N) * casimir N X * (↑(u⁻¹) : Algebra N) :=
  Operations.MatrixAdjointCasimir.casimir_conjugate u X

def scalarPart (N : ℕ) (X : Module.End ℂ (Space N)) : Module.End ℂ (Space N) :=
  (LinearMap.trace ℂ (Space N) X / (dimension N : ℂ)) • 1

def tracelessPart (N : ℕ) (X : Module.End ℂ (Space N)) : Module.End ℂ (Space N) :=
  X - scalarPart N X

theorem trace_identity (N : ℕ) :
    LinearMap.trace ℂ (Space N) (1 : Module.End ℂ (Space N)) = (dimension N : ℂ) := by
  rw [LinearMap.trace_one, finrank_euclideanSpace]
  rfl

theorem trace_tracelessPart (N : ℕ) (X : Module.End ℂ (Space N)) :
    LinearMap.trace ℂ (Space N) (tracelessPart N X) = 0 := by
  have hd : (dimension N : ℂ) ≠ 0 := by exact_mod_cast (dimension_pos N).ne'
  rw [tracelessPart, map_sub, scalarPart, map_smul, trace_identity]
  simp [hd]

theorem complete_decomposition (N : ℕ) (X : Module.End ℂ (Space N)) :
    X = scalarPart N X + tracelessPart N X := by
  simp [tracelessPart]

theorem scalarPart_traceless (N : ℕ) (X : Module.End ℂ (Space N))
    (hX : LinearMap.trace ℂ (Space N) X = 0) : scalarPart N X = 0 := by
  simp [scalarPart, hX]

theorem tracelessPart_idempotent (N : ℕ) (X : Module.End ℂ (Space N)) :
    tracelessPart N (tracelessPart N X) = tracelessPart N X := by
  rw [tracelessPart, scalarPart_traceless N _ (trace_tracelessPart N X), sub_zero]

theorem operator_eq_tracelessPart (N : ℕ) (X : Module.End ℂ (Space N)) :
    operator N X = (dimension N : ℂ) • tracelessPart N X := by
  have hd : (dimension N : ℂ) ≠ 0 := by exact_mod_cast (dimension_pos N).ne'
  rw [operator_eq, tracelessPart, scalarPart, smul_sub, smul_smul]
  field_simp

theorem scalar_traceless_orthogonal (N : ℕ) (c : ℂ) (X : Module.End ℂ (Space N))
    (hX : LinearMap.trace ℂ (Space N) X = 0) :
    Geometry.HilbertTraceVariation.pair (c • (1 : Module.End ℂ (Space N))) X = 0 := by
  have ha : (c • (1 : Module.End ℂ (Space N))).adjoint =
      star c • (1 : Module.End ℂ (Space N)) := by
    simp [← LinearMap.star_eq_adjoint]
  rw [Geometry.HilbertTraceVariation.pair, ha, smul_mul_assoc, one_mul, map_smul, hX,
    smul_zero, Complex.zero_re]

theorem complete_pair (N : ℕ) (X : Module.End ℂ (Space N)) :
    Geometry.HilbertTraceVariation.pair X (operator N X) =
      (dimension N : ℝ) * Geometry.HilbertTraceQuadratic.energy (tracelessPart N X) := by
  rw [operator_eq_tracelessPart]
  have he := Geometry.HilbertTraceVariation.pair_smul_right
    (dimension N : ℝ) X (tracelessPart N X)
  simp only [Complex.ofReal_natCast] at he
  rw [he]
  have hx := complete_decomposition N X
  have ho : Geometry.HilbertTraceVariation.pair (scalarPart N X) (tracelessPart N X) = 0 :=
    scalar_traceless_orthogonal N _ _ (trace_tracelessPart N X)
  conv_lhs => arg 2; arg 1; rw [hx]
  rw [Geometry.HilbertTraceVariation.pair_add_left, ho, zero_add]
  rfl

theorem complete_pair_nonneg (N : ℕ) (X : Module.End ℂ (Space N)) :
    0 ≤ Geometry.HilbertTraceVariation.pair X (operator N X) := by
  rw [complete_pair]
  exact mul_nonneg (Nat.cast_nonneg _) (Geometry.HilbertTraceQuadratic.energy_nonneg _)

theorem complete_coercivity (N : ℕ) (X : Module.End ℂ (Space N)) :
    4 * Geometry.HilbertTraceQuadratic.energy (tracelessPart N X) ≤
      Geometry.HilbertTraceVariation.pair X (operator N X) := by
  rw [complete_pair]
  apply mul_le_mul_of_nonneg_right _ (Geometry.HilbertTraceQuadratic.energy_nonneg _)
  exact_mod_cast dimension_ge_four N

structure Conclusions : Prop where
  actual_dimension : ∀ N, dimension N = 4 * Fintype.card (HistoryLabel N)
  positive_dimension : ∀ N, 0 < dimension N
  actual_index : ∀ N, responseIndex N = 4 * (Fintype.card (HistoryLabel N) : ℝ)
  complete_traceless_generators : ∀ N (X : Algebra N), Matrix.trace X = 0 →
    (∑ i, ∑ j, X i j • tracelessUnit N i j) = X
  generator_response : ∀ N i j,
    casimir N (tracelessUnit N i j) = (responseIndex N : ℂ) • tracelessUnit N i j
  complete_response : ∀ N X,
    casimir N X = (dimension N : ℂ) • X - Matrix.trace X • (1 : Algebra N)
  exact_kernel : ∀ N X,
    operator N X = 0 ↔ ∃ c : ℂ, X = c • (1 : Module.End ℂ (Space N))
  traceless_response : ∀ N (X : Module.End ℂ (Space N)),
    LinearMap.trace ℂ (Space N) X = 0 →
      operator N X = (dimension N : ℂ) • X
  positive_traceless_response : ∀ N (X : Module.End ℂ (Space N)),
    LinearMap.trace ℂ (Space N) X = 0 → X ≠ 0 →
      0 < Geometry.HilbertTraceVariation.pair X (operator N X)
  complete_positive_response : ∀ N (X : Module.End ℂ (Space N)),
    Geometry.HilbertTraceVariation.pair X (operator N X) =
      (dimension N : ℝ) * Geometry.HilbertTraceQuadratic.energy (tracelessPart N X)
  complete_nonnegative_response : ∀ N (X : Module.End ℂ (Space N)),
    0 ≤ Geometry.HilbertTraceVariation.pair X (operator N X)
  cutoff_independent_coercivity : ∀ N (X : Module.End ℂ (Space N)),
    4 * Geometry.HilbertTraceQuadratic.energy (tracelessPart N X) ≤
      Geometry.HilbertTraceVariation.pair X (operator N X)

theorem generated : Conclusions where
  actual_dimension := dimension_eq
  positive_dimension := dimension_pos
  actual_index := responseIndex_eq
  complete_traceless_generators := tracelessUnit_spans
  generator_response := casimir_tracelessUnit_real
  complete_response := casimir_eq
  exact_kernel := operator_kernel
  traceless_response := operator_traceless
  positive_traceless_response := traceless_pair_pos
  complete_positive_response := complete_pair
  complete_nonnegative_response := complete_pair_nonneg
  cutoff_independent_coercivity := complete_coercivity

end GeneratedFoundations.Arithmetic.HistoryAdjointCasimir
