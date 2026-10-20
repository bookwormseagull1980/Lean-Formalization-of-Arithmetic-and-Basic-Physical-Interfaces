module

public import GeneratedFoundations.Geometry.SourceQuaternionAmplitude

/-!
# Complex extension of the generated quaternion amplitude

The source real form determines both components of an arbitrary complex
two-by-two response. The decomposition below is computed from all four
matrix entries. It therefore retains every complex response direction rather
than imposing the reversal-real condition on a general perturbation.
-/

@[expose] public section

noncomputable section

open scoped Quaternion

namespace GeneratedFoundations.Operations.SourceComplexAmplitude

open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Operations.SourceSpinCorner (Mat2)
open GeneratedFoundations.Operations.SourceSpinCornerGroup (canonical)

/-- The first component in the complexification of the actual source real form. -/
def realPart (M : Mat2) : ℍ :=
  ⟨((M 0 0).re + (M 1 1).re) / 2,
    ((M 0 0).im - (M 1 1).im) / 2,
    ((M 0 1).re - (M 1 0).re) / 2,
    ((M 0 1).im + (M 1 0).im) / 2⟩

def imagPart (M : Mat2) : ℍ :=
  ⟨((M 0 0).im + (M 1 1).im) / 2,
    ((M 1 1).re - (M 0 0).re) / 2,
    ((M 0 1).im - (M 1 0).im) / 2,
    -((M 0 1).re + (M 1 0).re) / 2⟩

theorem matrix_decomposition (M : Mat2) :
    M = matrixMap (realPart M) + Complex.I • matrixMap (imagPart M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [matrixMap_eq, canonical, realPart, imagPart, smul_eq_mul, map_ofNat] <;> ring

@[simp] theorem realPart_decomposition (p q : ℍ) :
    realPart (matrixMap p + Complex.I • matrixMap q) = p := by
  ext <;> simp [realPart, matrixMap_eq, canonical, smul_eq_mul] <;> ring

@[simp] theorem imagPart_decomposition (p q : ℍ) :
    imagPart (matrixMap p + Complex.I • matrixMap q) = q := by
  ext <;> simp [imagPart, matrixMap_eq, canonical, smul_eq_mul] <;> ring

theorem decomposition_unique (M : Mat2) (p q : ℍ)
    (h : M = matrixMap p + Complex.I • matrixMap q) :
    p = realPart M ∧ q = imagPart M := by
  constructor
  · simpa only [realPart_decomposition] using (congrArg realPart h).symm
  · simpa only [imagPart_decomposition] using (congrArg imagPart h).symm

/-- The actual real amplitude generates the full complex matrix algebra. -/
theorem complex_adjoin_eq_top :
    Algebra.adjoin ℂ (Set.range matrixMap) = ⊤ := by
  apply top_unique
  intro M _
  rw [matrix_decomposition M]
  exact (Algebra.adjoin ℂ (Set.range matrixMap)).add_mem
    (Algebra.subset_adjoin ⟨realPart M, rfl⟩)
    ((Algebra.adjoin ℂ (Set.range matrixMap)).smul_mem
      (Algebra.subset_adjoin ⟨imagPart M, rfl⟩) Complex.I)

end GeneratedFoundations.Operations.SourceComplexAmplitude
