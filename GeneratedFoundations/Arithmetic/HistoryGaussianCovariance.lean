module

public import GeneratedFoundations.Arithmetic.HistoryResponseCertificates

/-!
# Isotropic covariance on the complete arithmetic connection carrier

The coordinate directions and independent traceless generators are those of
the actual arithmetic prefix. Haar volume is normalized to one. Equal
component variance is therefore fixed by the total intensity and the
calculated component count. Contracting the remaining coordinate directions
uses the full double-commutator Casimir, not a colour-dimension label.

An intensity is a configuration coordinate. For the closed centre source
it is the already calculated unit susceptibility. A one-coordinate carrier
has no transverse direction, so its transverse shift is zero; positivity
is asserted only when an actual transverse direction exists.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryGaussianCovariance

open HistoryCliffordAction (Algebra)
open HistoryGaugeJets (CoordinateIndex)

def componentCount (N : ℕ) : ℕ := HistoryResponseCertificates.coefficientCount N

theorem componentCount_eq (N : ℕ) :
    componentCount N = Fintype.card (CoordinateIndex N) *
      (HistoryAdjointCasimir.dimension N ^ 2 - 1) :=
  HistoryResponseCertificates.coefficientCount_eq N

theorem componentCount_pos (N : ℕ) : 0 < componentCount N :=
  HistoryResponseCertificates.coefficientCount_pos N

def componentVariance (N : ℕ) (q : ℝ) : ℝ := q / componentCount N

theorem componentVariance_total (N : ℕ) (q : ℝ) :
    (componentCount N : ℝ) * componentVariance N q = q := by
  have hc : (componentCount N : ℝ) ≠ 0 := by
    exact_mod_cast (componentCount_pos N).ne'
  unfold componentVariance
  field_simp

theorem componentVariance_unique (N : ℕ) (q v : ℝ)
    (hv : (componentCount N : ℝ) * v = q) : v = componentVariance N q := by
  have hc : (componentCount N : ℝ) ≠ 0 := by
    exact_mod_cast (componentCount_pos N).ne'
  exact (eq_div_iff hc).mpr (by simpa [mul_comm] using hv)

theorem componentVariance_pos (N : ℕ) {q : ℝ} (hq : 0 < q) :
    0 < componentVariance N q :=
  div_pos hq (Nat.cast_pos.mpr (componentCount_pos N))

def transverseCount (N : ℕ) (i : CoordinateIndex N) : ℕ :=
  (Finset.univ.erase i).card

theorem transverseCount_eq (N : ℕ) (i : CoordinateIndex N) :
    transverseCount N i = Fintype.card (CoordinateIndex N) - 1 := by
  simp [transverseCount]

def transverseShift (N : ℕ) (q : ℝ) (i : CoordinateIndex N) : ℝ :=
  transverseCount N i * componentVariance N q * HistoryAdjointCasimir.dimension N

def transverseAction (N : ℕ) (q : ℝ) (i : CoordinateIndex N)
    (X : Algebra N) : Algebra N :=
  ∑ _j ∈ Finset.univ.erase i,
    (componentVariance N q : ℂ) • HistoryAdjointCasimir.casimir N X

/-- The common coefficient is read off only after the actual Casimir
contraction and the complete transverse sum have been evaluated. -/
theorem transverseAction_eq (N : ℕ) (q : ℝ) (i : CoordinateIndex N)
    (X : Algebra N) (hX : Matrix.trace X = 0) :
    transverseAction N q i X = (transverseShift N q i : ℂ) • X := by
  unfold transverseAction
  rw [HistoryAdjointCasimir.casimir_traceless N X hX]
  simp only [smul_smul, ← Finset.sum_smul, Finset.sum_const, nsmul_eq_mul]
  congr 1
  simp only [transverseShift, transverseCount, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  ring

theorem transverseShift_nonneg (N : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (i : CoordinateIndex N) : 0 ≤ transverseShift N q i := by
  unfold transverseShift componentVariance
  positivity

theorem transverseShift_pos (N : ℕ) {q : ℝ} (hq : 0 < q)
    (i : CoordinateIndex N) (hi : 0 < transverseCount N i) :
    0 < transverseShift N q i :=
  mul_pos (mul_pos (Nat.cast_pos.mpr hi) (componentVariance_pos N hq))
    (Nat.cast_pos.mpr (HistoryAdjointCasimir.dimension_pos N))

theorem transverseShift_scale (N : ℕ) (q t : ℝ) (i : CoordinateIndex N) :
    transverseShift N (t * q) i = t * transverseShift N q i := by
  unfold transverseShift componentVariance
  ring

theorem transverseShift_affine (N : ℕ) (q v t : ℝ) (i : CoordinateIndex N) :
    transverseShift N (q + t * v) i =
      transverseShift N q i + t * transverseShift N v i := by
  unfold transverseShift componentVariance
  ring

def generatedIntensity (N : ℕ) : ℝ := HistoryCentreNormalization.variance N 0

theorem generatedIntensity_eq (N : ℕ) : generatedIntensity N = 1 :=
  HistoryJointCentreResponse.closed_susceptibility N

theorem generatedIntensity_pos (N : ℕ) : 0 < generatedIntensity N := by
  rw [generatedIntensity_eq]
  exact zero_lt_one

theorem closed_variance (N : ℕ) :
    componentVariance N (generatedIntensity N) = (componentCount N : ℝ)⁻¹ := by
  simp [componentVariance, generatedIntensity_eq]

structure Conclusions : Prop where
  actual_components : ∀ N, componentCount N = Fintype.card (CoordinateIndex N) *
    (HistoryAdjointCasimir.dimension N ^ 2 - 1)
  exact_total : ∀ N q, (componentCount N : ℝ) * componentVariance N q = q
  unique_isotropic_variance : ∀ N q v,
    (componentCount N : ℝ) * v = q → v = componentVariance N q
  actual_contraction : ∀ N q i (X : Algebra N), Matrix.trace X = 0 →
    transverseAction N q i X = (transverseShift N q i : ℂ) • X
  closed_intensity : ∀ N, generatedIntensity N = 1

theorem generated : Conclusions where
  actual_components := componentCount_eq
  exact_total := componentVariance_total
  unique_isotropic_variance := componentVariance_unique
  actual_contraction := transverseAction_eq
  closed_intensity := generatedIntensity_eq

end GeneratedFoundations.Arithmetic.HistoryGaussianCovariance
