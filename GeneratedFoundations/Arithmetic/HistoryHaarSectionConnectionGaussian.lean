module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionVariation
public import GeneratedFoundations.Operations.FiniteMatrixGaussianResponse

/-!
# The Gaussian state of the original connection-dependent section form

The complex source basis is realified with both quadratures. Products of
the connection with source sections remain in the original Haar space.
The resulting full real precision is a Gram matrix plus the original
restoring term. Its positive inverse determines one centred Gaussian,
without requiring a comparison measure to have diagonal covariance.

Connection insertions are the actual derivatives of this same action.
They are not replaced by independent labelwise heat vertices.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate ComplexOrder Matrix

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionGaussian

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionAction
open HistoryHaarSectionConnectionVariation

local instance (N : ℕ) : InnerProductSpace ℝ (StateFields N) :=
  InnerProductSpace.complexToReal
local instance (N : ℕ) : InnerProductSpace ℝ (DerivativeFields N) :=
  InnerProductSpace.complexToReal

abbrev RealIndex (N : ℕ) (B u : ℝ) := WindowIndex N B u × Fin 2
abbrev Space (N : ℕ) (B u : ℝ) := EuclideanSpace ℝ (RealIndex N B u)

local instance (N : ℕ) (B u : ℝ) : DecidableEq (RealIndex N B u) := Classical.decEq _

def phase (q : Fin 2) : ℂ := if q = 0 then 1 else Complex.I

def realSection (N : ℕ) (B u : ℝ) (i : RealIndex N B u) : Sections N :=
  phase i.2 • windowSection N B u i.1

def sourceSection (N : ℕ) (B u : ℝ) (x : Space N B u) : Sections N :=
  ∑ i, (x i : ℂ) • realSection N B u i

theorem realSection_field_gram (N : ℕ) (B u : ℝ) :
    Matrix.gram ℝ (fun i : RealIndex N B u => sectionField N (realSection N B u i)) = 1 := by
  classical
  ext ⟨i, q⟩ ⟨j, r⟩
  have hg := congrArg (fun M : Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ => M i j)
    (windowSection_gram N B u)
  simp only [Matrix.gram_apply] at hg
  change (inner ℂ (sectionField N (realSection N B u (i, q)))
    (sectionField N (realSection N B u (j, r)))).re = _
  fin_cases q <;> fin_cases r <;>
    simp [realSection, phase, map_smul, inner_smul_left, inner_smul_right, hg,
      Matrix.one_apply, Prod.mk.injEq] <;> split_ifs <;> simp_all

def realPrecision (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    Matrix (RealIndex N B u) (RealIndex N B u) ℝ :=
  Matrix.gram ℝ (fun i => covariantDerivative N A (realSection N B u i)) +
    (HistoryDefiningResponse.coefficient N + u ^ 2) • 1

theorem realPrecision_posDef (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    (realPrecision N B u A).PosDef := by
  classical
  exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_gram ℝ _)
    (Matrix.PosDef.one.smul (add_pos_of_pos_of_nonneg
      (HistoryDefiningResponse.coefficient_pos N) (sq_nonneg u)))

theorem realPrecision_uniform_lower (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    (realPrecision N B u A - ((15 / 8 : ℝ) + u ^ 2) • 1).PosSemidef := by
  classical
  rw [realPrecision, add_sub_assoc, ← sub_smul]
  have he : HistoryDefiningResponse.coefficient N + u ^ 2 - ((15 / 8 : ℝ) + u ^ 2) =
      HistoryDefiningResponse.coefficient N - 15 / 8 := by ring
  rw [he]
  exact (Matrix.posSemidef_gram ℝ _).add
    (Matrix.PosSemidef.one.smul (sub_nonneg.mpr (HistoryDefiningResponse.coefficient_lower N)))

theorem section_field (N : ℕ) (B u : ℝ) (x : Space N B u) :
    sectionField N (sourceSection N B u x) =
      ∑ i, x i • sectionField N (realSection N B u i) := by
  simp only [sourceSection, map_sum, map_smul, Complex.coe_smul]
  rfl

theorem section_covariant (N : ℕ) (B u : ℝ) (A : Coefficients N) (x : Space N B u) :
    covariantDerivative N A (sourceSection N B u x) =
      ∑ i, x i • covariantDerivative N A (realSection N B u i) := by
  change covariantLinear N A _ = _
  simp only [sourceSection, map_sum, map_smul, covariantLinear_apply, Complex.coe_smul]
  rfl

/-- The real precision is exactly the original action, not a diagonal
comparison with the same positive lower bound. -/
theorem score_eq_original_action (N : ℕ) (B u : ℝ) (A : Coefficients N)
    (x : Space N B u) :
    Operations.FiniteMatrixGaussian.score (realPrecision N B u A) x =
      sectionAction N A (sourceSection N B u x) + u ^ 2 * ‖sectionField N (sourceSection N B u x)‖ ^ 2 / 2 := by
  classical
  rw [Operations.FiniteMatrixGaussian.score_eq_dotProduct, realPrecision,
    Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]
  have hD := Matrix.star_dotProduct_gram_mulVec
    (fun i : RealIndex N B u => covariantDerivative N A (realSection N B u i))
    (fun i => x i) (fun i => x i)
  have hF := Matrix.star_dotProduct_gram_mulVec
    (fun i : RealIndex N B u => sectionField N (realSection N B u i))
    (fun i => x i) (fun i => x i)
  simp only [star_trivial, realSection_field_gram, Matrix.one_mulVec,
    real_inner_self_eq_norm_sq] at hD hF
  have hD' : (x ⬝ᵥ (Matrix.gram ℝ fun i =>
      covariantDerivative N A (realSection N B u i)) *ᵥ x) =
      ‖covariantDerivative N A (sourceSection N B u x)‖ ^ 2 := by
    rw [section_covariant]
    exact hD
  have hF' : (x ⬝ᵥ x) = ‖sectionField N (sourceSection N B u x)‖ ^ 2 := by
    rw [section_field]
    exact hF
  rw [hD', hF', sectionAction_eq]
  ring

def law (N : ℕ) (B u : ℝ) (A : Coefficients N) : Measure (Space N B u) :=
  Operations.FiniteMatrixGaussian.law (realPrecision N B u A)

instance (N : ℕ) (B u : ℝ) (A : Coefficients N) : IsGaussian (law N B u A) := by
  unfold law; infer_instance
instance (N : ℕ) (B u : ℝ) (A : Coefficients N) : IsProbabilityMeasure (law N B u A) :=
  inferInstance

theorem law_existsUnique (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    ∃! ν : Measure (Space N B u), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      realPrecision N B u A * Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  Operations.FiniteMatrixGaussian.law_existsUnique (realPrecision_posDef N B u A)

theorem covariance_eq (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    Operations.FinitePrecisionGaussian.coordinateCovariance (law N B u A) =
      (realPrecision N B u A)⁻¹ :=
  Operations.FiniteMatrixGaussian.coordinateCovariance_eq (realPrecision_posDef N B u A)

end GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionGaussian
