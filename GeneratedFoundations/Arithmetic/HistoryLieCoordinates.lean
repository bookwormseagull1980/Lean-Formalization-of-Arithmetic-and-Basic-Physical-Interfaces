module

public import GeneratedFoundations.Arithmetic.HistoryHermitianBasis
public import GeneratedFoundations.Arithmetic.HistoryLieAlgebra

/-!
# Independent real coordinates of complete arithmetic connection jets

The Hermitian basis was constructed on every matrix coefficient of the
history--phase/source carrier. Multiplication by `I` transports that real
basis to all skew-Hermitian traceless operations. The resulting coordinates
are independent and unique, and their Euclidean norm is the actual negative
trace quadratic form. Connection and derivative coefficients use this same
basis; no commutator or curvature coefficient is discarded.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryLieCoordinates

open HistoryCliffordAction (Algebra Space action)
open HistoryHermitianBasis (GeneratorIndex generator lieGenerator)

abbrev Coordinates (N : ℕ) := GeneratorIndex N → ℝ

def hermitianMatrix (N : ℕ) (c : Coordinates N) : Algebra N :=
  ∑ a, c a • generator N a

def matrix (N : ℕ) (c : Coordinates N) : Algebra N :=
  Complex.I • hermitianMatrix N c

theorem hermitianMatrix_mem (N : ℕ) (c : Coordinates N) :
    (hermitianMatrix N c).IsHermitian ∧ Matrix.trace (hermitianMatrix N c) = 0 := by
  constructor
  · change (∑ a, c a • generator N a).conjTranspose = _
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
    apply Finset.sum_congr rfl
    intro a _
    rw [(HistoryHermitianBasis.generator_hermitian N a).eq]
    simp
  · simp [hermitianMatrix, Matrix.trace_sum, HistoryHermitianBasis.generator_trace]

theorem matrix_mem (N : ℕ) (c : Coordinates N) : HistoryLieAlgebra.IsLie N (matrix N c) := by
  have hh := hermitianMatrix_mem N c
  constructor
  · simp [matrix, Matrix.conjTranspose_smul, hh.1.eq, Complex.conj_I]
  · simp [matrix, Matrix.trace_smul, hh.2]

theorem hermitianMatrix_injective (N : ℕ) : Function.Injective (hermitianMatrix N) := by
  intro c d h
  exact (HistoryHermitianBasis.generator_real_linearIndependent N).fintypeLinearCombination_injective h

theorem matrix_injective (N : ℕ) : Function.Injective (matrix N) := by
  intro c d h
  apply hermitianMatrix_injective N
  have hh := congrArg (fun X : Algebra N => (-Complex.I) • X) h
  simpa only [matrix, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] using hh

def hermitianPart (N : ℕ) (X : Algebra N) (hX : HistoryLieAlgebra.IsLie N X) :
    HistoryHermitianBasis.GeneratorSpace N :=
  HistoryHermitianBasis.ofMatrix N ((-Complex.I) • X)
    (by
      change ((-Complex.I) • X).conjTranspose = _
      rw [Matrix.conjTranspose_smul, hX.1]
      simp [Complex.conj_I])
    (by simp [Matrix.trace_smul, hX.2])

def coefficients (N : ℕ) (X : Algebra N) (hX : HistoryLieAlgebra.IsLie N X) :
    Coordinates N := HistoryHermitianBasis.coefficients N (hermitianPart N X hX)

theorem matrix_coefficients (N : ℕ) (X : Algebra N)
    (hX : HistoryLieAlgebra.IsLie N X) : matrix N (coefficients N X hX) = X := by
  have hh := HistoryHermitianBasis.real_expansion N (hermitianPart N X hX)
  change hermitianMatrix N (coefficients N X hX) = (-Complex.I) • X at hh
  rw [matrix, hh, smul_smul]
  simp [mul_neg, Complex.I_mul_I]

theorem matrix_image (N : ℕ) (X : Algebra N) :
    (∃ c : Coordinates N, matrix N c = X) ↔ HistoryLieAlgebra.IsLie N X := by
  constructor
  · rintro ⟨c, rfl⟩
    exact matrix_mem N c
  · intro hX
    exact ⟨coefficients N X hX, matrix_coefficients N X hX⟩

theorem coefficients_unique (N : ℕ) (X : Algebra N)
    (hX : HistoryLieAlgebra.IsLie N X) (c : Coordinates N) (hc : matrix N c = X) :
    c = coefficients N X hX :=
  matrix_injective N (hc.trans (matrix_coefficients N X hX).symm)

def quadratic (N : ℕ) (X : Algebra N) : ℝ := -(Matrix.trace (X * X)).re

theorem quadratic_coordinates (N : ℕ) (c : Coordinates N) :
    quadratic N (matrix N c) = ∑ a, c a ^ 2 := by
  have hh := hermitianMatrix_mem N c
  let H := HistoryHermitianBasis.ofMatrix N (hermitianMatrix N c) hh.1 hh.2
  have hc : HistoryHermitianBasis.coefficients N H = c := by
    symm
    exact HistoryHermitianBasis.real_expansion_unique N H c rfl
  have hp := HistoryHermitianBasis.coefficients_parseval N H
  rw [hc] at hp
  change (∑ a, c a ^ 2) =
    (Matrix.trace ((hermitianMatrix N c).conjTranspose * hermitianMatrix N c)).re at hp
  rw [hh.1.eq] at hp
  simp only [quadratic, matrix, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Complex.I_mul_I, neg_smul, one_smul, Matrix.trace_neg, Complex.neg_re,
    neg_neg]
  exact hp.symm

theorem quadratic_nonneg (N : ℕ) (c : Coordinates N) : 0 ≤ quadratic N (matrix N c) := by
  rw [quadratic_coordinates]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem quadratic_eq_zero (N : ℕ) (c : Coordinates N) :
    quadratic N (matrix N c) = 0 ↔ c = 0 := by
  rw [quadratic_coordinates]
  constructor
  · intro h
    funext a
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (c a))).mp h a
      (Finset.mem_univ a)
    exact sq_eq_zero_iff.mp ha
  · rintro rfl
    simp

structure ConnectionJet (N : ℕ) where
  value : HistoryGaugeJets.CoordinateIndex N → Coordinates N
  derivative : HistoryGaugeJets.CoordinateIndex N → HistoryGaugeJets.CoordinateIndex N →
    Coordinates N

def operatorJet (N : ℕ) (A : ConnectionJet N) : HistoryGaugeJets.ConnectionJet N where
  value μ := action N (matrix N (A.value μ))
  derivative μ ν := action N (matrix N (A.derivative μ ν))

def curvature (N : ℕ) (A : ConnectionJet N) (μ ν : HistoryGaugeJets.CoordinateIndex N) :
    Algebra N := matrix N (A.derivative μ ν) - matrix N (A.derivative ν μ) +
      (matrix N (A.value μ) * matrix N (A.value ν) -
        matrix N (A.value ν) * matrix N (A.value μ))

theorem curvature_mem (N : ℕ) (A : ConnectionJet N)
    (μ ν : HistoryGaugeJets.CoordinateIndex N) : HistoryLieAlgebra.IsLie N (curvature N A μ ν) :=
  HistoryLieAlgebra.add_mem N
    (HistoryLieAlgebra.sub_mem N (matrix_mem N _) (matrix_mem N _))
    (HistoryLieAlgebra.commutator_mem N (matrix_mem N _) (matrix_mem N _))

theorem curvature_operatorJet (N : ℕ) (A : ConnectionJet N)
    (μ ν : HistoryGaugeJets.CoordinateIndex N) :
    HistoryGaugeJets.curvature (operatorJet N A) μ ν = action N (curvature N A μ ν) := by
  simp only [HistoryGaugeJets.curvature, Geometry.ConnectionJetAlgebra.curvature,
    operatorJet, curvature, map_add, map_sub, map_mul]

structure Conclusions : Prop where
  all_real_directions : ∀ N X,
    (∃ c : Coordinates N, matrix N c = X) ↔ HistoryLieAlgebra.IsLie N X
  independent_coordinates : ∀ N, Function.Injective (matrix N)
  unique_coefficients : ∀ N X (hX : HistoryLieAlgebra.IsLie N X) c,
    matrix N c = X → c = coefficients N X hX
  exact_trace_metric : ∀ N c, quadratic N (matrix N c) = ∑ a, c a ^ 2
  positive_metric : ∀ N c, 0 ≤ quadratic N (matrix N c)
  metric_kernel : ∀ N c, quadratic N (matrix N c) = 0 ↔ c = 0
  retained_curvature : ∀ N A μ ν,
    HistoryGaugeJets.curvature (operatorJet N A) μ ν = action N (curvature N A μ ν)
  closed_curvature : ∀ N A μ ν, HistoryLieAlgebra.IsLie N (curvature N A μ ν)

theorem generated : Conclusions where
  all_real_directions := matrix_image
  independent_coordinates := matrix_injective
  unique_coefficients := coefficients_unique
  exact_trace_metric := quadratic_coordinates
  positive_metric := quadratic_nonneg
  metric_kernel := quadratic_eq_zero
  retained_curvature := curvature_operatorJet
  closed_curvature := curvature_mem

end GeneratedFoundations.Arithmetic.HistoryLieCoordinates
