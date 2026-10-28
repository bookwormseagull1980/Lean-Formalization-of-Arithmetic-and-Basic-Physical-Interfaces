module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionCollectiveWindow

/-!
# Frequency, connection and geometric variation of one section source

The reference frequency fixes the actual finite coefficient space. Within
that space the frequency in the action varies, together with the original
connection and logarithmic spatial scale. The frequency term is the same
quadratic term as in `realPrecision`, with the cubic Haar-volume factor
already derived for scalar restoring terms. At unit scale and the reference
frequency the original connection-dependent precision is recovered exactly.

The first and mixed direct insertions are differentiated before taking
expectations. In particular the mixed frequency--geometry terms and the
direct second frequency insertion are retained. Observation uses the full
Gaussian marginal and keeps its conditional return. These identities do
not identify a frequency coordinate with a selected observation endpoint.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionFrequencyCollective

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionAction
open HistoryHaarSectionConnectionGaussian (RealIndex Space realSection sourceSection)
open HistoryHaarSectionConnectionResponse (currentMatrix secondMatrix)
open HistoryHaarSectionCollectiveResponse (scalePath)
open HistoryHaarSectionConnectionMarginal (embed embed_injective)
open Operations.FiniteMatrixGaussian (score)

local instance (N : ℕ) (B u : ℝ) : DecidableEq (RealIndex N B u) := Classical.decEq _
local instance (N : ℕ) : InnerProductSpace ℝ (DerivativeFields N) :=
  InnerProductSpace.complexToReal
local instance (N : ℕ) : InnerProductSpace ℝ (StateFields N) :=
  InnerProductSpace.complexToReal

def kineticMatrix (N : ℕ) (B u₀ : ℝ) (A : Coefficients N) :
    Matrix (RealIndex N B u₀) (RealIndex N B u₀) ℝ :=
  Matrix.gram ℝ (fun i => covariantDerivative N A (realSection N B u₀ i))

def precision (N : ℕ) (B u₀ : ℝ) (A : Coefficients N) (c u : ℝ) :
    Matrix (RealIndex N B u₀) (RealIndex N B u₀) ℝ :=
  c • kineticMatrix N B u₀ A +
    (c ^ 3 * (HistoryDefiningResponse.coefficient N + u ^ 2)) • 1

theorem precision_posDef (N : ℕ) (B u₀ : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) (u : ℝ) : (precision N B u₀ A c u).PosDef := by
  exact Matrix.PosDef.posSemidef_add ((Matrix.posSemidef_gram ℝ _).smul hc.le)
    (Matrix.PosDef.one.smul (mul_pos (pow_pos hc _)
      (add_pos_of_pos_of_nonneg (HistoryDefiningResponse.coefficient_pos N) (sq_nonneg u))))

theorem precision_at_source (N : ℕ) (B u₀ : ℝ) (A : Coefficients N) :
    precision N B u₀ A 1 u₀ =
      HistoryHaarSectionConnectionGaussian.realPrecision N B u₀ A := by
  simp only [precision, one_pow, one_mul, one_smul,
    HistoryHaarSectionConnectionGaussian.realPrecision, kineticMatrix]

/-- The original section action, with its frequency term and actual
geometric Haar-volume variation. No response normalization is inserted. -/
theorem score_eq_original (N : ℕ) (B u₀ : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) (u : ℝ) (x : Space N B u₀) :
    HistoryHaarSectionGeometricVariation.geometricAction N A (sourceSection N B u₀ x) c +
        c ^ 3 * u ^ 2 * ‖sectionField N (sourceSection N B u₀ x)‖ ^ 2 / 2 =
      HistoryHaarMatrixCurvature.action N A / c + score (precision N B u₀ A c u) x := by
  have hD := Matrix.star_dotProduct_gram_mulVec
    (fun i : RealIndex N B u₀ => covariantDerivative N A (realSection N B u₀ i))
    (fun i => x i) (fun i => x i)
  have hF := Matrix.star_dotProduct_gram_mulVec
    (fun i : RealIndex N B u₀ => sectionField N (realSection N B u₀ i))
    (fun i => x i) (fun i => x i)
  simp only [star_trivial, HistoryHaarSectionConnectionGaussian.realSection_field_gram,
    Matrix.one_mulVec, real_inner_self_eq_norm_sq] at hD hF
  have hD' : x ⬝ᵥ kineticMatrix N B u₀ A *ᵥ x =
      ‖covariantDerivative N A (sourceSection N B u₀ x)‖ ^ 2 := by
    rw [HistoryHaarSectionConnectionGaussian.section_covariant]
    exact hD
  have hF' : x ⬝ᵥ x = ‖sectionField N (sourceSection N B u₀ x)‖ ^ 2 := by
    rw [HistoryHaarSectionConnectionGaussian.section_field]
    exact hF
  rw [Operations.FiniteMatrixGaussian.score_eq_dotProduct, precision,
    Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hD', hF',
    HistoryHaarSectionGeometricVariation.geometricAction_exact N A _ hc.ne']
  unfold HistoryHaarSectionGeometricVariation.curvatureEnergy
    HistoryHaarSectionGeometricVariation.kineticEnergy
    HistoryHaarSectionGeometricVariation.restoringEnergy
  ring

def firstMatrix (N : ℕ) (B u₀ : ℝ) (A X : Coefficients N) (c u v r : ℝ) :
    Matrix (RealIndex N B u₀) (RealIndex N B u₀) ℝ :=
  c • currentMatrix N B u₀ A X + (v * c) • kineticMatrix N B u₀ A +
    (c ^ 3 * (3 * v * (HistoryDefiningResponse.coefficient N + u ^ 2) + 2 * u * r)) • 1

def directMatrix (N : ℕ) (B u₀ : ℝ) (A X Y : Coefficients N)
    (c u v w r q : ℝ) : Matrix (RealIndex N B u₀) (RealIndex N B u₀) ℝ :=
  c • secondMatrix N B u₀ X Y +
    (w * c) • currentMatrix N B u₀ A X + (v * c) • currentMatrix N B u₀ A Y +
    (v * w * c) • kineticMatrix N B u₀ A +
    (c ^ 3 * (9 * v * w * (HistoryDefiningResponse.coefficient N + u ^ 2) +
      6 * v * u * q + 6 * w * u * r + 2 * r * q)) • 1

private theorem scalePath_hasDerivAt (c v : ℝ) :
    HasDerivAt (scalePath c v) (v * c) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).const_mul v).exp).const_mul c
  simpa [scalePath, mul_comm, mul_left_comm, mul_assoc] using! h

private theorem frequencyPath_hasDerivAt (u q : ℝ) :
    HasDerivAt (fun t : ℝ => u + q * t) q 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_add u

private theorem kineticMatrix_hasDerivAt (N : ℕ) (B u₀ : ℝ) (A Y : Coefficients N) :
    HasDerivAt (fun t : ℝ => kineticMatrix N B u₀ (A + (t : ℂ) • Y))
      (currentMatrix N B u₀ A Y) 0 := by
  have h := (HistoryHaarSectionConnectionResponse.realPrecision_hasDerivAt N B u₀ A Y).sub_const
    ((HistoryDefiningResponse.coefficient N + u₀ ^ 2) •
      (1 : Matrix (RealIndex N B u₀) _ ℝ))
  simpa only [HistoryHaarSectionConnectionGaussian.realPrecision, add_sub_cancel_right,
    kineticMatrix] using h

theorem precision_collective_hasDerivAt (N : ℕ) (B u₀ : ℝ)
    (A Y : Coefficients N) (c u w q : ℝ) :
    HasDerivAt (fun t : ℝ => precision N B u₀
      (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
      (firstMatrix N B u₀ A Y c u w q) 0 := by
  have hc := scalePath_hasDerivAt c w
  have hu := frequencyPath_hasDerivAt u q
  have hk := kineticMatrix_hasDerivAt N B u₀ A Y
  have hm := ((hu.pow 2).const_add (HistoryDefiningResponse.coefficient N))
  have h := (hc.smul hk).add (((hc.pow 3).mul hm).smul_const
    (1 : Matrix (RealIndex N B u₀) _ ℝ))
  change HasDerivAt (fun t : ℝ => precision N B u₀
    (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t)) _ 0 at h
  apply h.congr_deriv
  simp only [Pi.pow_apply, scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero, firstMatrix]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem firstMatrix_collective_hasDerivAt (N : ℕ) (B u₀ : ℝ)
    (A X Y : Coefficients N) (c u v w r q : ℝ) :
    HasDerivAt (fun t : ℝ => firstMatrix N B u₀
      (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r)
      (directMatrix N B u₀ A X Y c u v w r q) 0 := by
  have hc := scalePath_hasDerivAt c w
  have hu := frequencyPath_hasDerivAt u q
  have hv := HistoryHaarSectionConnectionResponse.currentMatrix_hasDerivAt N B u₀ A X Y 0
  have hk := kineticMatrix_hasDerivAt N B u₀ A Y
  have hm := (((hu.pow 2).const_add (HistoryDefiningResponse.coefficient N)).const_mul
    (3 * v)).add ((hu.const_mul 2).mul_const r)
  have h := ((hc.smul hv).add ((hc.const_mul v).smul hk)).add
    (((hc.pow 3).mul hm).smul_const (1 : Matrix (RealIndex N B u₀) _ ℝ))
  change HasDerivAt (fun t : ℝ => firstMatrix N B u₀
    (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r) _ 0 at h
  apply h.congr_deriv
  simp only [Pi.pow_apply, Pi.add_apply, scalePath, mul_zero, Real.exp_zero, mul_one,
    Complex.ofReal_zero, zero_smul, add_zero, directMatrix]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem firstMatrix_symmetric (N : ℕ) (B u₀ : ℝ)
    (A X : Coefficients N) (c u v r : ℝ) : (firstMatrix N B u₀ A X c u v r).IsSymm := by
  exact (((HistoryHaarSectionConnectionResponse.currentMatrix_symmetric N B u₀ A X).smul c).add
    ((Matrix.posSemidef_gram ℝ _).isHermitian.isSymm.smul (v * c))).add
      (Matrix.isSymm_one.smul _)

def law (N : ℕ) (B u₀ : ℝ) (A : Coefficients N) (c u : ℝ) : Measure (Space N B u₀) :=
  Operations.FiniteMatrixGaussian.law (precision N B u₀ A c u)

theorem collective_mean_hasDerivAt (N : ℕ) (B u₀ : ℝ)
    (A X Y : Coefficients N) {c : ℝ} (hc : 0 < c) (u v w r q : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, score
      (firstMatrix N B u₀ (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r) x
      ∂law N B u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
      ((∫ x, score (directMatrix N B u₀ A X Y c u v w r q) x ∂law N B u₀ A c u) -
        cov[score (firstMatrix N B u₀ A X c u v r),
          score (firstMatrix N B u₀ A Y c u w q); law N B u₀ A c u]) 0 := by
  have h := Operations.FiniteMatrixGaussian.varying_mean_hasDerivAt
    (fun t => precision N B u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
    (fun t => firstMatrix N B u₀ (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r)
    0 (firstMatrix N B u₀ A Y c u w q) (directMatrix N B u₀ A X Y c u v w r q)
    (fun t => precision_posDef N B u₀ _ (mul_pos hc (Real.exp_pos _)) _)
    (precision_collective_hasDerivAt N B u₀ A Y c u w q)
    (firstMatrix_collective_hasDerivAt N B u₀ A X Y c u v w r q)
    (firstMatrix_symmetric N B u₀ A Y c u w q)
  simpa only [scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero, law] using! h

def effectiveFirst (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) (c u v r : ℝ) :
    Matrix (RealIndex N B u₀) (RealIndex N B u₀) ℝ :=
  Operations.FiniteMatrixGaussian.retainedInsertion
    (precision N C u₀ A c u) (firstMatrix N C u₀ A X c u v r) (embed N hBC u₀)

def effectiveDirect (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u₀ : ℝ)
    (A X Y : Coefficients N) (c u v w r q : ℝ) :
    Matrix (RealIndex N B u₀) (RealIndex N B u₀) ℝ :=
  Operations.FiniteMatrixGaussian.retainedDirect
    (precision N C u₀ A c u) (firstMatrix N C u₀ A X c u v r)
    (firstMatrix N C u₀ A Y c u w q) (directMatrix N C u₀ A X Y c u v w r q)
    (embed N hBC u₀)

def observedLaw (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u₀ : ℝ)
    (A : Coefficients N) (c u : ℝ) : Measure (Space N B u₀) :=
  Operations.FiniteMatrixGaussian.law
    (Operations.FiniteMatrixGaussian.retainedPrecision (precision N C u₀ A c u) (embed N hBC u₀))

theorem observedLaw_eq_map (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u₀ : ℝ)
    (A : Coefficients N) {c : ℝ} (hc : 0 < c) (u : ℝ) :
    observedLaw N hBC u₀ A c u = (law N C u₀ A c u).map
      (Operations.FiniteMatrixGaussian.select (embed N hBC u₀)) :=
  (Operations.FiniteMatrixGaussian.selected_law
    (precision_posDef N C u₀ A hc u) (embed_injective N hBC u₀)).symm

theorem observed_collective_mean_hasDerivAt (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (u₀ : ℝ) (A X Y : Coefficients N) {c : ℝ} (hc : 0 < c) (u v w r q : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, score
      (effectiveFirst N hBC u₀ (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r) x
      ∂observedLaw N hBC u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
      ((∫ x, score (effectiveDirect N hBC u₀ A X Y c u v w r q) x
        ∂observedLaw N hBC u₀ A c u) -
        cov[score (effectiveFirst N hBC u₀ A X c u v r),
          score (effectiveFirst N hBC u₀ A Y c u w q); observedLaw N hBC u₀ A c u]) 0 := by
  have h := Operations.FiniteMatrixGaussian.retained_mean_hasDerivAt
    (fun t => precision N C u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
    (fun t => firstMatrix N C u₀ (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r)
    0 (firstMatrix N C u₀ A Y c u w q) (directMatrix N C u₀ A X Y c u v w r q)
    (e := embed N hBC u₀) (embed_injective N hBC u₀)
    (fun t => precision_posDef N C u₀ _ (mul_pos hc (Real.exp_pos _)) _)
    (precision_collective_hasDerivAt N C u₀ A Y c u w q)
    (firstMatrix_collective_hasDerivAt N C u₀ A X Y c u v w r q)
    (firstMatrix_symmetric N C u₀ A Y c u w q)
  simpa only [scalePath, mul_zero, Real.exp_zero, mul_one, Complex.ofReal_zero,
    zero_smul, add_zero, effectiveFirst, effectiveDirect, observedLaw] using! h

theorem full_current_balance (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u₀ : ℝ)
    (A X : Coefficients N) {c : ℝ} (hc : 0 < c) (u v r : ℝ) :
    (∫ x, score (firstMatrix N C u₀ A X c u v r) x ∂law N C u₀ A c u) =
      (∫ x, score (effectiveFirst N hBC u₀ A X c u v r) x
        ∂observedLaw N hBC u₀ A c u) +
        Matrix.trace (Operations.FiniteMatrixGaussian.conditionalCovariance
          (precision N C u₀ A c u) (embed N hBC u₀) *
            firstMatrix N C u₀ A X c u v r) / 2 := by
  exact Operations.FiniteMatrixGaussian.full_mean_eq_retained_add_conditional
    (precision_posDef N C u₀ A hc u) (embed_injective N hBC u₀) _

private theorem currentMatrix_zero (N : ℕ) (B u₀ : ℝ) (A : Coefficients N) :
    currentMatrix N B u₀ A 0 = 0 := by
  have hd := HistoryHaarSectionConnectionResponse.realPrecision_hasDerivAt N B u₀ A 0
  have hz : HasDerivAt (fun t : ℝ =>
      HistoryHaarSectionConnectionGaussian.realPrecision N B u₀ (A + (t : ℂ) • 0)) 0 0 := by
    simpa only [smul_zero, add_zero] using hasDerivAt_const (0 : ℝ)
      (HistoryHaarSectionConnectionGaussian.realPrecision N B u₀ A)
  exact hd.unique hz

/-- The native geometric content retains the frequency contribution to
the scalar restoring covariance, rather than using its zero-frequency value. -/
theorem geometric_current_mean (N : ℕ) (B u₀ : ℝ) (A : Coefficients N)
    {c : ℝ} (hc : 0 < c) (u : ℝ) :
    (∫ x, score (firstMatrix N B u₀ A 0 c u 1 0) x ∂law N B u₀ A c u) =
      (Fintype.card (RealIndex N B u₀) : ℝ) / 2 +
        c ^ 3 * (HistoryDefiningResponse.coefficient N + u ^ 2) *
          Matrix.trace ((precision N B u₀ A c u)⁻¹) := by
  have he : firstMatrix N B u₀ A 0 c u 1 0 = precision N B u₀ A c u +
      (2 * c ^ 3 * (HistoryDefiningResponse.coefficient N + u ^ 2)) • 1 := by
    rw [firstMatrix, currentMatrix_zero]
    ext i j
    simp only [precision, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    ring
  rw [he, law, Operations.FiniteMatrixGaussian.score_mean_trace (precision_posDef N B u₀ A hc u)]
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Operations.FiniteMatrixGaussian.inverse_mul_precision (precision_posDef N B u₀ A hc u),
    Matrix.trace_add, Matrix.trace_one, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

structure Conclusions : Prop where
  source_precision : ∀ N B u₀ A,
    precision N B u₀ A 1 u₀ = HistoryHaarSectionConnectionGaussian.realPrecision N B u₀ A
  original_frequency_action : ∀ N B u₀ A c, 0 < c → ∀ u x,
    HistoryHaarSectionGeometricVariation.geometricAction N A (sourceSection N B u₀ x) c +
        c ^ 3 * u ^ 2 * ‖sectionField N (sourceSection N B u₀ x)‖ ^ 2 / 2 =
      HistoryHaarMatrixCurvature.action N A / c + score (precision N B u₀ A c u) x
  complete_response : ∀ N B u₀ A X Y c, 0 < c → ∀ u v w r q,
    HasDerivAt (fun t : ℝ => ∫ x, score
      (firstMatrix N B u₀ (A + (t : ℂ) • Y) X (scalePath c w t) (u + q * t) v r) x
      ∂law N B u₀ (A + (t : ℂ) • Y) (scalePath c w t) (u + q * t))
      ((∫ x, score (directMatrix N B u₀ A X Y c u v w r q) x ∂law N B u₀ A c u) -
        cov[score (firstMatrix N B u₀ A X c u v r),
          score (firstMatrix N B u₀ A Y c u w q); law N B u₀ A c u]) 0

theorem generated : Conclusions where
  source_precision := precision_at_source
  original_frequency_action := fun N B u₀ A _ hc u x => score_eq_original N B u₀ A hc u x
  complete_response := fun N B u₀ A X Y _ hc u v w r q =>
    collective_mean_hasDerivAt N B u₀ A X Y hc u v w r q

end GeneratedFoundations.Arithmetic.HistoryHaarSectionFrequencyCollective
