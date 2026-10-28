module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionResponse
public import GeneratedFoundations.Operations.FiniteMatrixGaussianMarginal

/-!
# Unique observation states through actual connection windows

The source section and its precision are the original ones. A smaller
frequency support defines an injective observation map. The observed law
is the actual marginal of the same complete finite Gaussian source;
its precision is the inverse of the retained full covariance. This keeps
the eliminated connection correlations. Repeated observations compose
without replacing this precision by the bare smaller-window form.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionMarginal

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionConnectionVariation (scalarSupport WindowIndex mem_scalarSupport)
open HistoryHaarSectionConnectionGaussian (RealIndex Space realPrecision realSection law)

local instance (N : ℕ) (B u : ℝ) : DecidableEq (RealIndex N B u) := Classical.decEq _
local instance (N : ℕ) : InnerProductSpace ℝ (HistoryHaarSectionAction.DerivativeFields N) :=
  InnerProductSpace.complexToReal

theorem scalarSupport_mono (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u : ℝ) :
    scalarSupport N B u ⊆ scalarSupport N C u := by
  intro i hi
  exact (mem_scalarSupport N C u i).mpr
    (HistoryHaarSectionWindow.support_mono N (sub_le_sub_right hBC _)
      ((mem_scalarSupport N B u i).mp hi))

def embed (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u : ℝ)
    (i : RealIndex N B u) : RealIndex N C u :=
  (⟨i.1.val, scalarSupport_mono N hBC u i.1.property⟩, i.2)

theorem embed_injective (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u : ℝ) :
    Function.Injective (embed N hBC u) := by
  intro i j h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun x => x.1.val) h
  · exact congrArg (fun x : RealIndex N C u => x.2) h

theorem embed_comp (N : ℕ) {B C D : ℝ} (hBC : B ≤ C) (hCD : C ≤ D) (u : ℝ) :
    embed N hCD u ∘ embed N hBC u = embed N (hBC.trans hCD) u := by
  funext i
  rfl

/-- The original smaller precision is the principal block of the source
action. It is not, in general, its integrated marginal precision. -/
theorem original_precision_restrict (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (u : ℝ) (A : Coefficients N) :
    (realPrecision N C u A).submatrix (embed N hBC u) (embed N hBC u) =
      realPrecision N B u A := by
  ext i j
  have he : embed N hBC u i = embed N hBC u j ↔ i = j :=
    (embed_injective N hBC u).eq_iff
  change inner ℝ
      (HistoryHaarSectionAction.covariantDerivative N A
        (realSection N C u (embed N hBC u i)))
      (HistoryHaarSectionAction.covariantDerivative N A
        (realSection N C u (embed N hBC u j))) +
      (HistoryDefiningResponse.coefficient N + u ^ 2) *
        (if embed N hBC u i = embed N hBC u j then 1 else 0) =
    inner ℝ
      (HistoryHaarSectionAction.covariantDerivative N A (realSection N B u i))
      (HistoryHaarSectionAction.covariantDerivative N A (realSection N B u j)) +
      (HistoryDefiningResponse.coefficient N + u ^ 2) * (if i = j then 1 else 0)
  simp only [he]
  rfl

def observation (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (u : ℝ) :
    Space N C u →L[ℝ] Space N B u :=
  Operations.FiniteMatrixGaussian.select (embed N hBC u)

def effectivePrecision (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (u : ℝ) (A : Coefficients N) : Matrix (RealIndex N B u) (RealIndex N B u) ℝ :=
  Operations.FiniteMatrixGaussian.retainedPrecision (realPrecision N C u A) (embed N hBC u)

def observedLaw (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (u : ℝ) (A : Coefficients N) : Measure (Space N B u) :=
  (law N C u A).map (observation N hBC u)

theorem effectivePrecision_posDef (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (u : ℝ) (A : Coefficients N) : (effectivePrecision N hBC u A).PosDef :=
  Operations.FiniteMatrixGaussian.retainedPrecision_posDef
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N C u A)
    (embed_injective N hBC u)

theorem observedLaw_eq (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (u : ℝ) (A : Coefficients N) :
    observedLaw N hBC u A = Operations.FiniteMatrixGaussian.law (effectivePrecision N hBC u A) :=
  Operations.FiniteMatrixGaussian.selected_law
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N C u A)
    (embed_injective N hBC u)

theorem observed_covariance (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (u : ℝ) (A : Coefficients N) :
    Operations.FinitePrecisionGaussian.coordinateCovariance (observedLaw N hBC u A) =
      ((realPrecision N C u A)⁻¹).submatrix (embed N hBC u) (embed N hBC u) :=
  Operations.FiniteMatrixGaussian.selected_covariance
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N C u A) (embed N hBC u)

theorem observedLaw_existsUnique (N : ℕ) {B C : ℝ} (hBC : B ≤ C)
    (u : ℝ) (A : Coefficients N) :
    ∃! ν : Measure (Space N B u), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      effectivePrecision N hBC u A *
        Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  Operations.FiniteMatrixGaussian.retained_law_existsUnique
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N C u A)
    (embed_injective N hBC u)

theorem observation_comp (N : ℕ) {B C D : ℝ} (hBC : B ≤ C) (hCD : C ≤ D) (u : ℝ) :
    (observation N hBC u).comp (observation N hCD u) =
      observation N (hBC.trans hCD) u := by
  rw [observation, observation, Operations.FiniteMatrixGaussian.select_comp, embed_comp]
  rfl

theorem observedLaw_tower (N : ℕ) {B C D : ℝ} (hBC : B ≤ C) (hCD : C ≤ D)
    (u : ℝ) (A : Coefficients N) :
    (observedLaw N hCD u A).map (observation N hBC u) =
      observedLaw N (hBC.trans hCD) u A := by
  unfold observedLaw observation
  change ((Operations.FiniteMatrixGaussian.law (realPrecision N D u A)).map
    (Operations.FiniteMatrixGaussian.select (embed N hCD u))).map
      (Operations.FiniteMatrixGaussian.select (embed N hBC u)) = _
  rw [Operations.FiniteMatrixGaussian.selected_law_comp, embed_comp]
  rfl

theorem effectivePrecision_tower (N : ℕ) {B C D : ℝ} (hBC : B ≤ C) (hCD : C ≤ D)
    (u : ℝ) (A : Coefficients N) :
    Operations.FiniteMatrixGaussian.retainedPrecision
      (effectivePrecision N hCD u A) (embed N hBC u) =
        effectivePrecision N (hBC.trans hCD) u A := by
  unfold effectivePrecision
  rw [Operations.FiniteMatrixGaussian.retainedPrecision_comp
    (HistoryHaarSectionConnectionGaussian.realPrecision_posDef N D u A)
    (embed_injective N hCD u), embed_comp]

structure Conclusions : Prop where
  original_principal_block : ∀ N B C (hBC : B ≤ C) u A,
    (realPrecision N C u A).submatrix (embed N hBC u) (embed N hBC u) =
      realPrecision N B u A
  positive_effective_precision : ∀ N B C (hBC : B ≤ C) u A,
    (effectivePrecision N hBC u A).PosDef
  actual_observed_state : ∀ N B C (hBC : B ≤ C) u A,
    observedLaw N hBC u A = Operations.FiniteMatrixGaussian.law (effectivePrecision N hBC u A)
  unique_observed_gaussian : ∀ N B C (hBC : B ≤ C) u A,
    ∃! ν : Measure (Space N B u), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      effectivePrecision N hBC u A *
        Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1
  observation_composition : ∀ N B C D (hBC : B ≤ C) (hCD : C ≤ D) u A,
    (observedLaw N hCD u A).map (observation N hBC u) =
      observedLaw N (hBC.trans hCD) u A

theorem generated : Conclusions where
  original_principal_block := fun N _ _ hBC => original_precision_restrict N hBC
  positive_effective_precision := fun N _ _ hBC => effectivePrecision_posDef N hBC
  actual_observed_state := fun N _ _ hBC => observedLaw_eq N hBC
  unique_observed_gaussian := fun N _ _ hBC => observedLaw_existsUnique N hBC
  observation_composition := fun N _ _ _ hBC hCD => observedLaw_tower N hBC hCD

end GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionMarginal
