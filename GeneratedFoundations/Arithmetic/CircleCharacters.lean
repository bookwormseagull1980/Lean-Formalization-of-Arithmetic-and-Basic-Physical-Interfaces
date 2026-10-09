module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring

/-!
# Continuous characters of the circle

A continuous multiplicative character on the additive circle is a unique
Fourier monomial. The proof uses translation invariance and Fourier
completeness.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace GeneratedFoundations.Arithmetic.CircleCharacters

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma fourier_map_add (n : ℤ) (x y : AddCircle (1 : ℝ)) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp [fourier_apply, smul_add, AddCircle.toCircle_add]

lemma fourier_index_injective :
    Function.Injective (fourier (T := (1 : ℝ))) := by
  intro m n h
  by_contra hmn
  have hc := congrArg (fun f : C(AddCircle (1 : ℝ), ℂ) => fourierCoeff f m) h
  simp [fourierCoeff_fourier, hmn] at hc

lemma exists_nonzero_coefficient (f : C(AddCircle (1 : ℝ), ℂ))
    (hzero : f 0 = 1) : ∃ n : ℤ, fourierCoeff f n ≠ 0 := by
  by_contra! h
  have hcoeff : fourierCoeff f = 0 := funext h
  have hs : Summable (fourierCoeff f) := by rw [hcoeff]; exact summable_zero
  have hsum := hasSum_fourier_series_of_summable hs
  simp only [h, zero_smul] at hsum
  have hf : f = 0 := hsum.unique hasSum_zero
  have hv := congrArg (fun g : C(AddCircle (1 : ℝ), ℂ) => g 0) hf
  simp [hzero] at hv

lemma character_eq_fourier_of_coefficient_ne_zero
    (f : C(AddCircle (1 : ℝ), ℂ))
    (hadd : ∀ x y, f (x + y) = f x * f y)
    (n : ℤ) (hn : fourierCoeff f n ≠ 0) : f = fourier n := by
  ext z
  have hshift := integral_add_left_eq_self
    (μ := AddCircle.haarAddCircle)
    (fun x : AddCircle (1 : ℝ) => fourier (-n) x * f x) z
  have hfun :
      (fun x : AddCircle (1 : ℝ) => fourier (-n) (z + x) * f (z + x)) =
      (fun x => (fourier (-n) z * f z) * (fourier (-n) x * f x)) := by
    funext x
    rw [fourier_map_add, hadd]
    ring
  rw [hfun, integral_const_mul] at hshift
  change (fourier (-n) z * f z) * fourierCoeff f n = fourierCoeff f n at hshift
  have hproduct : fourier (-n) z * f z = 1 :=
    mul_right_cancel₀ hn (hshift.trans (one_mul _).symm)
  calc
    f z = (fourier n z * fourier (-n) z) * f z := by
      rw [← fourier_add, add_neg_cancel, fourier_zero]
      simp
    _ = fourier n z * (fourier (-n) z * f z) := by ring
    _ = fourier n z := by rw [hproduct, mul_one]

theorem character_existsUnique_fourier
    (f : C(AddCircle (1 : ℝ), ℂ)) (hzero : f 0 = 1)
    (hadd : ∀ x y, f (x + y) = f x * f y) :
    ∃! n : ℤ, f = fourier n := by
  obtain ⟨n, hn⟩ := exists_nonzero_coefficient f hzero
  have hf := character_eq_fourier_of_coefficient_ne_zero f hadd n hn
  refine ⟨n, hf, ?_⟩
  intro m hm
  exact fourier_index_injective (hm.symm.trans hf)

end GeneratedFoundations.Arithmetic.CircleCharacters
