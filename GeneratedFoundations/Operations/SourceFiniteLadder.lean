module

public import GeneratedFoundations.Operations.FiniteHermiteCorner
public import GeneratedFoundations.Operations.FiniteLadderAlgebra

/-!
# Finite compression of the Gaussian differential ladder

Projection onto the first `n+1` Hermite states has a Schwartz representative.
Applying the differential annihilation, creation and number operators to that
representative gives the finite weighted ladder matrices. The creation
operator also requires projection of its output.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.GaussianAffineLadder (Core embedding)
open GeneratedFoundations.Operations.HermiteFamily
open GeneratedFoundations.Operations.SourceSpinCorner (End embedding_hermite)

namespace GeneratedFoundations.Operations.SourceFiniteLadder

open FiniteLadderAlgebra (Index Mat)

variable {b : ℝ} (hb : 0 < b) (n : ℕ)

def modes : Index n → ℕ := Fin.val

theorem modes_injective : Function.Injective (modes n) := Fin.val_injective

def corner : Mat n →ₗ[ℂ] End := FiniteHermiteCorner.corner hb (modes n)

def projection : End := FiniteHermiteCorner.projection hb (modes n)

def projectedCore (F : ComplexL2) : Core :=
  ∑ j : Index n, inner ℂ (state hb j.val) F • hermite hb j.val

theorem embedding_projectedCore (F : ComplexL2) :
    embedding (projectedCore hb n F) = projection hb n F := by
  simp only [projectedCore, map_sum, map_smul, embedding_hermite, projection,
    FiniteHermiteCorner.projection_apply, modes]

def compressedAnnihilation : End := corner hb n (FiniteLadderAlgebra.lowering n)

def compressedCreation : End :=
  corner hb n (FiniteLadderAlgebra.lowering n).conjTranspose

def compressedNumber : End := corner hb n (FiniteLadderAlgebra.number n)

theorem annihilation_column (j : Index n) :
    embedding (annihilation b (hermite hb j.val)) =
      compressedAnnihilation hb n (state hb j.val) := by
  by_cases hj : j.val = 0
  · calc
      embedding (annihilation b (hermite hb j.val)) = 0 := by
        rw [hj, annihilation_hermite_zero, map_zero]
      _ = compressedAnnihilation hb n (state hb j.val) := by
        change 0 = FiniteHermiteCorner.corner hb (modes n)
          (FiniteLadderAlgebra.lowering n) (state hb (modes n j))
        rw [FiniteHermiteCorner.corner_state hb (modes n) (modes_injective n)]
        simp [FiniteLadderAlgebra.lowering, hj]
  · let i₀ : Index n := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hi₀ : i₀.val + 1 = j.val := by dsimp [i₀]; omega
    have hdelta (i : Index n) : i.val + 1 = j.val ↔ i = i₀ := by
      constructor
      · intro h
        apply Fin.ext
        dsimp [i₀]
        omega
      · rintro rfl
        exact hi₀
    calc
      embedding (annihilation b (hermite hb j.val)) =
          (Real.sqrt (j.val : ℝ) : ℂ) • state hb i₀.val := by
        rw [← hi₀, annihilation_hermite_succ, map_smul, embedding_hermite]
        simp only [Nat.cast_add, Nat.cast_one]
      _ = compressedAnnihilation hb n (state hb j.val) := by
        change _ = FiniteHermiteCorner.corner hb (modes n)
          (FiniteLadderAlgebra.lowering n) (state hb (modes n j))
        rw [FiniteHermiteCorner.corner_state hb (modes n) (modes_injective n)]
        simp [FiniteLadderAlgebra.lowering, hdelta, modes]

theorem creation_column (j : Index n) :
    projection hb n (embedding (creation b (hermite hb j.val))) =
      compressedCreation hb n (state hb j.val) := by
  rw [creation_hermite, map_smul, embedding_hermite]
  change FiniteHermiteCorner.projection hb (modes n)
      ((Real.sqrt (j.val + 1 : ℝ) : ℂ) • state hb (j.val + 1)) =
    FiniteHermiteCorner.corner hb (modes n)
      (FiniteLadderAlgebra.lowering n).conjTranspose (state hb (modes n j))
  rw [FiniteHermiteCorner.projection_apply,
    FiniteHermiteCorner.corner_state hb (modes n) (modes_injective n)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [modes, inner_smul_right, SourceMatrixUnits.state_inner,
    Matrix.conjTranspose_apply, FiniteLadderAlgebra.lowering]
  by_cases h : j.val + 1 = i.val
  · simp [← h, Nat.cast_add, Nat.cast_one]
  · simp [h, Ne.symm h]

theorem number_column (j : Index n) :
    embedding (number b (hermite hb j.val)) =
      compressedNumber hb n (state hb j.val) := by
  rw [number_hermite, map_smul, embedding_hermite]
  change _ = FiniteHermiteCorner.corner hb (modes n)
    (FiniteLadderAlgebra.number n) (state hb (modes n j))
  rw [FiniteHermiteCorner.corner_state hb (modes n) (modes_injective n),
    FiniteLadderAlgebra.number_eq_diagonal]
  simp [Matrix.diagonal_apply, modes]

private theorem differential_compression (D : Core →L[ℂ] Core) (M : Mat n)
    (hD : ∀ j : Index n, embedding (D (hermite hb j.val)) =
      corner hb n M (state hb j.val)) (F : ComplexL2) :
    embedding (D (projectedCore hb n F)) = corner hb n M F := by
  calc
    embedding (D (projectedCore hb n F)) =
        ∑ j : Index n, inner ℂ (state hb j.val) F •
          corner hb n M (state hb j.val) := by
      simp only [projectedCore, map_sum, map_smul, hD]
    _ = corner hb n M (projection hb n F) := by
      simp only [projection, FiniteHermiteCorner.projection_apply,
        map_sum, map_smul, modes]
    _ = corner hb n M F := by
      exact congrArg (fun T : End => T F)
        (FiniteHermiteCorner.mul_projection hb (modes n) (modes_injective n) M)

private theorem differential_output_compression (D : Core →L[ℂ] Core) (M : Mat n)
    (hD : ∀ j : Index n, projection hb n (embedding (D (hermite hb j.val))) =
      corner hb n M (state hb j.val)) (F : ComplexL2) :
    projection hb n (embedding (D (projectedCore hb n F))) = corner hb n M F := by
  calc
    projection hb n (embedding (D (projectedCore hb n F))) =
        ∑ j : Index n, inner ℂ (state hb j.val) F •
          corner hb n M (state hb j.val) := by
      simp only [projectedCore, map_sum, map_smul, hD]
    _ = corner hb n M (projection hb n F) := by
      simp only [projection, FiniteHermiteCorner.projection_apply,
        map_sum, map_smul, modes]
    _ = corner hb n M F := by
      exact congrArg (fun T : End => T F)
        (FiniteHermiteCorner.mul_projection hb (modes n) (modes_injective n) M)

theorem embedding_annihilation_projectedCore (F : ComplexL2) :
    embedding (annihilation b (projectedCore hb n F)) = compressedAnnihilation hb n F :=
  differential_compression hb n (annihilation b) (FiniteLadderAlgebra.lowering n)
    (annihilation_column hb n) F

theorem projection_embedding_annihilation_projectedCore (F : ComplexL2) :
    projection hb n (embedding (annihilation b (projectedCore hb n F))) =
      compressedAnnihilation hb n F := by
  rw [embedding_annihilation_projectedCore]
  exact congrArg (fun T : End => T F)
    (FiniteHermiteCorner.projection_mul hb (modes n) (modes_injective n)
      (FiniteLadderAlgebra.lowering n))

theorem projection_embedding_creation_projectedCore (F : ComplexL2) :
    projection hb n (embedding (creation b (projectedCore hb n F))) =
      compressedCreation hb n F :=
  differential_output_compression hb n (creation b)
    (FiniteLadderAlgebra.lowering n).conjTranspose (creation_column hb n) F

theorem embedding_number_projectedCore (F : ComplexL2) :
    embedding (number b (projectedCore hb n F)) = compressedNumber hb n F :=
  differential_compression hb n (number b) (FiniteLadderAlgebra.number n)
    (number_column hb n) F

theorem projection_embedding_number_projectedCore (F : ComplexL2) :
    projection hb n (embedding (number b (projectedCore hb n F))) =
      compressedNumber hb n F := by
  rw [embedding_number_projectedCore]
  exact congrArg (fun T : End => T F)
    (FiniteHermiteCorner.projection_mul hb (modes n) (modes_injective n)
      (FiniteLadderAlgebra.number n))

theorem compressedCreation_adjoint :
    (compressedAnnihilation hb n).adjoint = compressedCreation hb n :=
  FiniteHermiteCorner.corner_adjoint hb (modes n) (FiniteLadderAlgebra.lowering n)

theorem compressedNumber_factorization :
    compressedNumber hb n = compressedCreation hb n * compressedAnnihilation hb n :=
  FiniteHermiteCorner.corner_mul hb (modes n) (modes_injective n)
    (FiniteLadderAlgebra.lowering n).conjTranspose (FiniteLadderAlgebra.lowering n)

end GeneratedFoundations.Operations.SourceFiniteLadder
