module

public import GeneratedFoundations.Operations.HermiteFamily

/-! Polynomial Gaussian vectors in the generated Hermite span

The sum of the actual lowering and raising operators recovers multiplication
by the source coordinate. Consequently the algebraic Hermite span is invariant
under this multiplication and contains every monomial times the same Gaussian.
No completeness assumption is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap ComplexConjugate
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteSource
open GeneratedFoundations.Operations.GaussianAffineLadder
open GeneratedFoundations.Operations.GaussianLadderCore
open GeneratedFoundations.Operations.HermiteFamily

namespace GeneratedFoundations.Operations.HermiteSpan

def sourceSpan {b : ℝ} (hb : 0 < b) : Submodule ℂ Core :=
  Submodule.span ℂ (Set.range (hermite hb))

theorem hermite_mem_span {b : ℝ} (hb : 0 < b) (n : ℕ) :
    hermite hb n ∈ sourceSpan hb := Submodule.subset_span ⟨n, rfl⟩

theorem position_eq_ladder {b : ℝ} (hb : 0 < b) (f : Core) :
    position f = ((b : ℂ) / (Real.sqrt 2 : ℂ)) •
      (annihilation b f + creation b f) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  ext x
  simp only [position_apply, smul_apply, add_apply, smul_eq_mul,
    annihilation_apply, creation_apply, lowering, raising, Complex.ofReal_div]
  calc
    _ = (2 / (Real.sqrt 2 : ℂ) ^ 2) * ((x : ℂ) * f x) := by rw [hs]; norm_num
    _ = _ := by field_simp [hb', hn]; ring

theorem annihilation_hermite_mem {b : ℝ} (hb : 0 < b) (n : ℕ) :
    annihilation b (hermite hb n) ∈ sourceSpan hb := by
  cases n with
  | zero => rw [annihilation_hermite_zero]; exact (sourceSpan hb).zero_mem
  | succ n =>
      rw [annihilation_hermite_succ]
      exact (sourceSpan hb).smul_mem _ (hermite_mem_span hb n)

theorem creation_hermite_mem {b : ℝ} (hb : 0 < b) (n : ℕ) :
    creation b (hermite hb n) ∈ sourceSpan hb := by
  rw [creation_hermite]
  exact (sourceSpan hb).smul_mem _ (hermite_mem_span hb (n + 1))

/-- Coordinate multiplication preserves the genuine algebraic source span. -/
theorem position_mem_span {b : ℝ} (hb : 0 < b) {f : Core}
    (hf : f ∈ sourceSpan hb) : position f ∈ sourceSpan hb := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨n, rfl⟩ := hf
      rw [position_eq_ladder hb]
      exact (sourceSpan hb).smul_mem _
        ((sourceSpan hb).add_mem (annihilation_hermite_mem hb n) (creation_hermite_mem hb n))
  | zero => simp only [map_zero]; exact (sourceSpan hb).zero_mem
  | add f g _ _ hf hg => rw [map_add]; exact (sourceSpan hb).add_mem hf hg
  | smul c f _ hf => rw [map_smul]; exact (sourceSpan hb).smul_mem c hf

def monomialGaussian {b : ℝ} (hb : 0 < b) : ℕ → Core
  | 0 => groundSchwartz hb
  | n + 1 => position (monomialGaussian hb n)

theorem monomialGaussian_apply {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    monomialGaussian hb n x = (x : ℂ) ^ n * (groundProfile b x : ℂ) := by
  induction n with
  | zero => simp [monomialGaussian]
  | succ n ih =>
      rw [monomialGaussian, position_apply, ih, pow_succ]
      ring

theorem monomialGaussian_mem_span {b : ℝ} (hb : 0 < b) (n : ℕ) :
    monomialGaussian hb n ∈ sourceSpan hb := by
  induction n with
  | zero =>
      change groundSchwartz hb ∈ sourceSpan hb
      rw [← hermite_zero hb]
      exact hermite_mem_span hb 0
  | succ n ih => exact position_mem_span hb ih

/-- Orthogonality to the normalized family extends to its algebraic source span. -/
theorem inner_eq_zero_of_mem_span {b : ℝ} (hb : 0 < b) (F : ComplexL2)
    (hF : ∀ n, inner ℂ (HermiteFamily.state hb n) F = 0) {f : Core}
    (hf : f ∈ sourceSpan hb) : inner ℂ (embedding f) F = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨n, rfl⟩ := hf; exact hF n
  | zero => simp
  | add f g _ _ hf hg => simp only [map_add, inner_add_left, hf, hg, add_zero]
  | smul c f _ hf => simp only [map_smul, inner_smul_left, hf, mul_zero]

end GeneratedFoundations.Operations.HermiteSpan
