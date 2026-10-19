module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsAction
public import Mathlib.Tactic.Linarith

/-!
# Euler equation of the generated Yang--Mills spectral action

The radial and coclosed equations are obtained from the same quadratic action
defined in `SourceGeneratedYangMillsAction`.  Positivity of the generated mass
operator makes the condensed zero-fluctuation configuration the unique
solution at every finite spectral cutoff.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsEquation

open SourceGeneratedYangMillsGap SourceGeneratedYangMillsAction

namespace SpectralConfiguration

def add {N : ℕ} (x y : SpectralConfiguration N) : SpectralConfiguration N :=
  ⟨x.radial + y.radial, fun i => x.coclosed i + y.coclosed i⟩

def smul {N : ℕ} (a : ℝ) (x : SpectralConfiguration N) :
    SpectralConfiguration N :=
  ⟨a * x.radial, fun i => a * x.coclosed i⟩

end SpectralConfiguration

/-- Gradient of the generated spectral action. -/
def equation {N : ℕ} (L z : ℝ)
    (x : SpectralConfiguration N) : SpectralConfiguration N :=
  ⟨normalizedRadialMassSq z * x.radial,
    fun i => coclosedMassIndex L z (coclosedShellDegree i.1) * x.coclosed i⟩

/-- Bilinear first variation of the same action. -/
def firstVariation {N : ℕ} (L z : ℝ)
    (x y : SpectralConfiguration N) : ℝ :=
  normalizedRadialMassSq z * x.radial * y.radial +
    ∑ i, coclosedMassIndex L z (coclosedShellDegree i.1) *
      x.coclosed i * y.coclosed i

/-- Exact polarization identity.  This identifies `equation` as the Euler
operator of `spectralAction` without importing an independent field law. -/
theorem spectralAction_add {N : ℕ} (L z : ℝ)
    (x y : SpectralConfiguration N) :
    spectralAction L z (SpectralConfiguration.add x y) =
      spectralAction L z x + spectralAction L z y +
        firstVariation L z x y := by
  have hcross :
      (∑ i, coclosedMassIndex L z (coclosedShellDegree i.1) *
        (2 * x.coclosed i * y.coclosed i)) =
        2 * ∑ i, coclosedMassIndex L z (coclosedShellDegree i.1) *
          x.coclosed i * y.coclosed i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  unfold spectralAction SpectralConfiguration.add firstVariation
  simp_rw [add_sq]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hcross]
  ring_nf

theorem firstVariation_self_eq_two_action {N : ℕ} (L z : ℝ)
    (x : SpectralConfiguration N) :
    firstVariation L z x x = 2 * spectralAction L z x := by
  unfold firstVariation spectralAction
  simp_rw [pow_two]
  ring_nf

theorem equation_eq_zero_iff {N : ℕ} {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) (x : SpectralConfiguration N) :
    equation L z x = SpectralConfiguration.zero N ↔
      x = SpectralConfiguration.zero N := by
  constructor
  · intro h
    have hr : x.radial = 0 := by
      have heq := congrArg SpectralConfiguration.radial h
      simp only [equation, SpectralConfiguration.zero] at heq
      exact (mul_eq_zero.mp heq).resolve_left
        (normalizedRadialMassSq_pos hz).ne'
    have hc : ∀ i, x.coclosed i = 0 := by
      intro i
      have heq := congrArg (fun y => y.coclosed i) h
      simp only [equation, SpectralConfiguration.zero] at heq
      exact (mul_eq_zero.mp heq).resolve_left
        (coclosedMassIndex_pos hL hz (coclosedShellDegree i.1)).ne'
    cases x
    simp only [SpectralConfiguration.zero] at hr ⊢
    congr
    funext i
    exact hc i
  · rintro rfl
    simp [equation, SpectralConfiguration.zero]

theorem firstVariation_self_pos {N : ℕ} {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) {x : SpectralConfiguration N}
    (hx : x ≠ SpectralConfiguration.zero N) :
    0 < firstVariation L z x x := by
  have haction : 0 < spectralAction L z x := by
    unfold spectralAction
    by_cases hr : x.radial = 0
    · have hc : ∃ i, x.coclosed i ≠ 0 := by
        by_contra hnone
        simp only [not_exists, not_not] at hnone
        apply hx
        cases x
        simp only [SpectralConfiguration.zero] at hr ⊢
        congr
        funext i
        exact hnone i
      rcases hc with ⟨i, hi⟩
      have hsum : 0 < ∑ j,
          coclosedMassIndex L z (coclosedShellDegree j.1) * x.coclosed j ^ 2 := by
        apply Finset.sum_pos'
        · intro j _
          exact mul_nonneg (coclosedMassIndex_pos hL hz (coclosedShellDegree j.1)).le
            (sq_nonneg (x.coclosed j))
        · exact ⟨i, Finset.mem_univ i,
            mul_pos (coclosedMassIndex_pos hL hz (coclosedShellDegree i.1))
              (sq_pos_of_ne_zero hi)⟩
      rw [hr, zero_pow (by norm_num)]
      norm_num
      linarith
    · have hrad : 0 < (1 / 2 : ℝ) * normalizedRadialMassSq z *
          x.radial ^ 2 := by
        exact mul_pos (mul_pos (by norm_num)
          (normalizedRadialMassSq_pos hz)) (sq_pos_of_ne_zero hr)
      have hsum : 0 ≤ (1 / 2 : ℝ) * ∑ i,
          coclosedMassIndex L z (coclosedShellDegree i.1) * x.coclosed i ^ 2 := by
        exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
          mul_nonneg (coclosedMassIndex_pos hL hz (coclosedShellDegree i.1)).le
            (sq_nonneg (x.coclosed i)))
      exact add_pos_of_pos_of_nonneg hrad hsum
  rw [firstVariation_self_eq_two_action]
  positivity

/-- Bundled generated equation interface. -/
structure Properties : Prop where
  polarization : ∀ {N} L z (x y : SpectralConfiguration N),
    spectralAction L z (SpectralConfiguration.add x y) =
      spectralAction L z x + spectralAction L z y +
        firstVariation L z x y
  unique_solution : ∀ {N L z}, 0 < L → 0 < z →
    ∀ x : SpectralConfiguration N,
      equation L z x = SpectralConfiguration.zero N ↔
        x = SpectralConfiguration.zero N
  positive_variation : ∀ {N L z}, 0 < L → 0 < z →
    ∀ {x : SpectralConfiguration N}, x ≠ SpectralConfiguration.zero N →
      0 < firstVariation L z x x

theorem properties : Properties where
  polarization := spectralAction_add
  unique_solution := equation_eq_zero_iff
  positive_variation := firstVariation_self_pos

end GeneratedFoundations.Physical.SourceGeneratedYangMillsEquation
