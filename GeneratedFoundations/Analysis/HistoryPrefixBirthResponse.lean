module

public import GeneratedFoundations.Analysis.HistoryPrefixMobiusResponse
public import GeneratedFoundations.Operations.GibbsBlockResponse

/-!
# Birth response in the actual natural root prefix

The prefix extension adjoins root N+2, together with its entire existing
history--phase fibre, to roots 1,...,N+1. The reference law is the original
Gaussian law. The new-root fraction is computed from its actual mass and
the full partition, with no independently supplied transition probability.

Arbitrary Hermitian observations retain their cross-birth entries through
the exact block-response decomposition. For root observations the same
Hessian yields the complete birth covariance and its exact Schur reduction.
Natural-prefix extension and maximum-prime-factor generation are different
operations; this module treats the former without identifying their states.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryPrefixBirthResponse

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open HistoryPrefixGibbsResponse

def rootObservation (N : ℕ) (f : ℕ → ℝ) (i : Index N) : ℝ := f (i.1.val + 1)

def rootMean (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) : ℝ :=
  mean N alpha L (rootObservation N f)

def birth (N : ℕ) (i : Index (N + 1)) : ℝ := if i.1.val = N + 1 then 1 else 0

def birthBlock (N : ℕ) (i : Index (N + 1)) : Bool := decide (i.1.val = N + 1)

def birthFraction (N : ℕ) (alpha L : ℝ) : ℝ :=
  gaussianRootMass alpha L (N + 2) / GibbsTraceForm.Z (logIntensity (N + 1) alpha L)

theorem partition_succ (N : ℕ) (alpha L : ℝ) :
    GibbsTraceForm.Z (logIntensity (N + 1) alpha L) =
      GibbsTraceForm.Z (logIntensity N alpha L) + gaussianRootMass alpha L (N + 2) := by
  rw [partition_eq_prefix, partition_eq_prefix, Fin.sum_univ_castSucc]
  rfl

theorem birthFraction_pos (N : ℕ) (alpha L : ℝ) : 0 < birthFraction N alpha L :=
  div_pos (gaussianRootMass_pos _ _ _) (GibbsTraceForm.Z_pos _)

theorem birthFraction_lt_one (N : ℕ) (alpha L : ℝ) : birthFraction N alpha L < 1 := by
  unfold birthFraction
  apply (div_lt_one (GibbsTraceForm.Z_pos _)).mpr
  rw [partition_succ]
  linarith [GibbsTraceForm.Z_pos (logIntensity N alpha L)]

theorem weighted_rootMean (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    GibbsTraceForm.Z (logIntensity N alpha L) * rootMean N alpha L f =
      ∑ b : Fin (N + 1), gaussianRootMass alpha L (b.val + 1) * f (b.val + 1) := by
  unfold rootMean rootObservation
  rw [mean_root_observation N alpha L (fun b => f (b.val + 1)),
    mul_div_cancel₀ _ (GibbsTraceForm.Z_ne_zero _)]

/-- The whole old capacity and actual new mass precede normalization. -/
theorem weighted_rootMean_succ (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    GibbsTraceForm.Z (logIntensity (N + 1) alpha L) * rootMean (N + 1) alpha L f =
      GibbsTraceForm.Z (logIntensity N alpha L) * rootMean N alpha L f +
        gaussianRootMass alpha L (N + 2) * f (N + 2) := by
  rw [weighted_rootMean, weighted_rootMean, Fin.sum_univ_castSucc]
  rfl

theorem rootMean_succ (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    rootMean (N + 1) alpha L f =
      (1 - birthFraction N alpha L) * rootMean N alpha L f +
        birthFraction N alpha L * f (N + 2) := by
  apply (mul_left_cancel₀ (GibbsTraceForm.Z_ne_zero (logIntensity (N + 1) alpha L)))
  rw [weighted_rootMean_succ]
  unfold birthFraction
  rw [partition_succ]
  have hz : GibbsTraceForm.Z (logIntensity N alpha L) +
      gaussianRootMass alpha L (N + 2) ≠ 0 :=
    ne_of_gt (add_pos (GibbsTraceForm.Z_pos _) (gaussianRootMass_pos _ _ _))
  field_simp [hz]
  ring

theorem mean_birth (N : ℕ) (alpha L : ℝ) :
    mean (N + 1) alpha L (birth N) = birthFraction N alpha L := by
  change mean (N + 1) alpha L (fun i => if i.1.val = N + 1 then 1 else 0) = _
  rw [mean_root_observation (N + 1) alpha L
    (fun b : Fin (N + 2) => if b.val = N + 1 then 1 else 0)]
  rw [Finset.sum_eq_single (Fin.last (N + 1))]
  · simp [birthFraction]
  · intro b _ hb
    have hv : b.val ≠ N + 1 := fun h => hb (Fin.ext h)
    simp [hv]
  · simp

theorem mean_root_mul_birth (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    mean (N + 1) alpha L (fun i => rootObservation (N + 1) f i * birth N i) =
      f (N + 2) * birthFraction N alpha L := by
  rw [← mean_birth]
  unfold mean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.1.val = N + 1 <;> simp [rootObservation, birth, h, mul_comm]

theorem birth_hessian (N : ℕ) (alpha L : ℝ) :
    fderiv ℝ (fderiv ℝ (response (N + 1) alpha L)) 0
      (diagonalObservation (birth N)) (diagonalObservation (birth N)) =
        birthFraction N alpha L * (1 - birthFraction N alpha L) := by
  rw [hessian_covariance]
  have he : (fun i => birth N i * birth N i) = birth N := by
    funext i
    by_cases h : i.1.val = N + 1 <;> simp [birth, h]
  rw [he, mean_birth]
  ring

/-- The mixed term is computed from the same source and its exact update. -/
theorem root_birth_hessian (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    fderiv ℝ (fderiv ℝ (response (N + 1) alpha L)) 0
      (diagonalObservation (rootObservation (N + 1) f)) (diagonalObservation (birth N)) =
        birthFraction N alpha L * (1 - birthFraction N alpha L) *
          (f (N + 2) - rootMean N alpha L f) := by
  rw [hessian_covariance, mean_root_mul_birth, mean_birth]
  change f (N + 2) * birthFraction N alpha L -
    rootMean (N + 1) alpha L f * birthFraction N alpha L = _
  rw [rootMean_succ]
  ring

theorem root_hessian (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N f)) =
        rootMean N alpha L (fun n => f n * f n) - (rootMean N alpha L f) ^ 2 := by
  rw [hessian_covariance, pow_two]
  rfl

theorem root_joint_hessian (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N g)) =
        rootMean N alpha L (fun n => f n * g n) - rootMean N alpha L f * rootMean N alpha L g := by
  rw [hessian_covariance]
  rfl

/-- Joint birth covariance, retaining the mixed term for every pair of root
observations in the same actual state. -/
theorem root_joint_hessian_succ (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ) :
    fderiv ℝ (fderiv ℝ (response (N + 1) alpha L)) 0
      (diagonalObservation (rootObservation (N + 1) f))
      (diagonalObservation (rootObservation (N + 1) g)) =
      (1 - birthFraction N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N g)) +
        birthFraction N alpha L * (1 - birthFraction N alpha L) *
          (f (N + 2) - rootMean N alpha L f) * (g (N + 2) - rootMean N alpha L g) := by
  rw [root_joint_hessian, root_joint_hessian,
    rootMean_succ N alpha L (fun n => f n * g n), rootMean_succ N alpha L f,
    rootMean_succ N alpha L g]
  ring

/-- Total variance includes the full between-birth square. -/
theorem root_hessian_succ (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    fderiv ℝ (fderiv ℝ (response (N + 1) alpha L)) 0
      (diagonalObservation (rootObservation (N + 1) f))
      (diagonalObservation (rootObservation (N + 1) f)) =
      (1 - birthFraction N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N f)) +
        birthFraction N alpha L * (1 - birthFraction N alpha L) *
          (f (N + 2) - rootMean N alpha L f) ^ 2 := by
  rw [root_hessian, root_hessian, rootMean_succ N alpha L (fun n => f n * f n),
    rootMean_succ N alpha L f]
  ring

open HistoryPrefixResponseReduction (form residual)

/-- Removing the actual birth observation retains exactly the old conditional
root response. Positivity of its denominator follows from actual capacities. -/
theorem birth_schur_response (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    form (N + 1) alpha L
      (residual alpha L (diagonalObservation (rootObservation (N + 1) f))
        (diagonalObservation (birth N)))
      (residual alpha L (diagonalObservation (rootObservation (N + 1) f))
        (diagonalObservation (birth N))) =
      (1 - birthFraction N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N f)) := by
  have h := HistoryPrefixResponseReduction.schur_identity alpha L
    (diagonalObservation (rootObservation (N + 1) f)) (diagonalObservation (birth N))
  have hMM : form (N + 1) alpha L
      (diagonalObservation (rootObservation (N + 1) f))
      (diagonalObservation (rootObservation (N + 1) f)) =
      (1 - birthFraction N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N f)) +
        birthFraction N alpha L * (1 - birthFraction N alpha L) *
          (f (N + 2) - rootMean N alpha L f) ^ 2 := by
    rw [HistoryPrefixResponseReduction.form_hessian, root_hessian_succ]
  have hMS : form (N + 1) alpha L
      (diagonalObservation (rootObservation (N + 1) f)) (diagonalObservation (birth N)) =
      birthFraction N alpha L * (1 - birthFraction N alpha L) *
        (f (N + 2) - rootMean N alpha L f) := by
    rw [HistoryPrefixResponseReduction.form_hessian, root_birth_hessian]
  have hSS : form (N + 1) alpha L (diagonalObservation (birth N))
      (diagonalObservation (birth N)) = birthFraction N alpha L * (1 - birthFraction N alpha L) := by
    rw [HistoryPrefixResponseReduction.form_hessian, birth_hessian]
  rw [hMM, hMS, hSS] at h
  have hγ := (birthFraction_pos N alpha L).ne'
  have hα := (sub_pos.mpr (birthFraction_lt_one N alpha L)).ne'
  have he : (birthFraction N alpha L * (1 - birthFraction N alpha L) *
      (f (N + 2) - rootMean N alpha L f)) ^ 2 /
      (birthFraction N alpha L * (1 - birthFraction N alpha L)) =
      birthFraction N alpha L * (1 - birthFraction N alpha L) *
        (f (N + 2) - rootMean N alpha L f) ^ 2 := by
    field_simp [hγ, hα]
  rw [he] at h
  linarith

theorem restored_old_capacity (N : ℕ) (alpha L : ℝ) :
    GibbsTraceForm.Z (logIntensity (N + 1) alpha L) * (1 - birthFraction N alpha L) =
      GibbsTraceForm.Z (logIntensity N alpha L) := by
  unfold birthFraction
  rw [mul_sub, mul_one, mul_div_cancel₀ _ (GibbsTraceForm.Z_ne_zero _), partition_succ]
  ring

/-- The conditional normalization factor is exactly compensated by restoring
the original capacity. It is not an additional contraction of the source. -/
theorem restored_birth_schur_response (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    GibbsTraceForm.Z (logIntensity (N + 1) alpha L) *
      form (N + 1) alpha L
        (residual alpha L (diagonalObservation (rootObservation (N + 1) f))
          (diagonalObservation (birth N)))
        (residual alpha L (diagonalObservation (rootObservation (N + 1) f))
          (diagonalObservation (birth N))) =
      GibbsTraceForm.Z (logIntensity N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N f)) := by
  rw [birth_schur_response, ← mul_assoc, restored_old_capacity]

/-- The actual new mass produces the exact between-birth fluctuation. -/
theorem restored_root_hessian_succ (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ) :
    GibbsTraceForm.Z (logIntensity (N + 1) alpha L) *
      fderiv ℝ (fderiv ℝ (response (N + 1) alpha L)) 0
        (diagonalObservation (rootObservation (N + 1) f))
        (diagonalObservation (rootObservation (N + 1) f)) =
      GibbsTraceForm.Z (logIntensity N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N f)) +
        gaussianRootMass alpha L (N + 2) * (1 - birthFraction N alpha L) *
          (f (N + 2) - rootMean N alpha L f) ^ 2 := by
  rw [root_hessian_succ, mul_add, ← mul_assoc
    (GibbsTraceForm.Z (logIntensity (N + 1) alpha L)) (1 - birthFraction N alpha L),
    restored_old_capacity]
  congr 1
  calc
    _ = (GibbsTraceForm.Z (logIntensity (N + 1) alpha L) * birthFraction N alpha L) *
        (1 - birthFraction N alpha L) * (f (N + 2) - rootMean N alpha L f) ^ 2 := by ring
    _ = _ := by
      rw [birthFraction, mul_div_cancel₀ _ (GibbsTraceForm.Z_ne_zero _)]

/-- All matrix entries across the actual birth are retained with their
original logarithmic-mean weights. -/
theorem full_birth_response (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index (N + 1))) :
    form (N + 1) alpha L K K =
      form (N + 1) alpha L (GibbsBlockResponse.block (birthBlock N) K)
        (GibbsBlockResponse.block (birthBlock N) K) +
      (∑ i, ∑ j, if birthBlock N i = birthBlock N j then 0 else
        GibbsExponentialDifferentiation.expDividedDifference
          (logIntensity (N + 1) alpha L i) (logIntensity (N + 1) alpha L j) *
            Complex.normSq ((K : Mat (Index (N + 1))) i j)) /
        GibbsTraceForm.Z (logIntensity (N + 1) alpha L) := by
  exact (GibbsBlockResponse.response_decomposition
    (logIntensity (N + 1) alpha L) (birthBlock N) K).trans
      (congrArg (fun r => form (N + 1) alpha L
        (GibbsBlockResponse.block (birthBlock N) K) (GibbsBlockResponse.block (birthBlock N) K) + r)
          (GibbsBlockResponse.off_response (logIntensity (N + 1) alpha L) (birthBlock N) K))

structure Conclusions : Prop where
  actual_partition_update : ∀ (N : ℕ) (alpha L : ℝ),
    GibbsTraceForm.Z (logIntensity (N + 1) alpha L) =
      GibbsTraceForm.Z (logIntensity N alpha L) + gaussianRootMass alpha L (N + 2)
  actual_birth_fraction : ∀ (N : ℕ) (alpha L : ℝ),
    0 < birthFraction N alpha L ∧ birthFraction N alpha L < 1
  actual_mixed_response : ∀ (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ),
    fderiv ℝ (fderiv ℝ (response (N + 1) alpha L)) 0
      (diagonalObservation (rootObservation (N + 1) f)) (diagonalObservation (birth N)) =
        birthFraction N alpha L * (1 - birthFraction N alpha L) *
          (f (N + 2) - rootMean N alpha L f)
  actual_joint_response : ∀ (N : ℕ) (alpha L : ℝ) (f g : ℕ → ℝ),
    fderiv ℝ (fderiv ℝ (response (N + 1) alpha L)) 0
      (diagonalObservation (rootObservation (N + 1) f))
      (diagonalObservation (rootObservation (N + 1) g)) =
      (1 - birthFraction N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N g)) +
        birthFraction N alpha L * (1 - birthFraction N alpha L) *
          (f (N + 2) - rootMean N alpha L f) * (g (N + 2) - rootMean N alpha L g)
  actual_reduced_response : ∀ (N : ℕ) (alpha L : ℝ) (f : ℕ → ℝ),
    form (N + 1) alpha L
      (residual alpha L (diagonalObservation (rootObservation (N + 1) f))
        (diagonalObservation (birth N)))
      (residual alpha L (diagonalObservation (rootObservation (N + 1) f))
        (diagonalObservation (birth N))) =
      (1 - birthFraction N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (diagonalObservation (rootObservation N f)) (diagonalObservation (rootObservation N f))
  complete_matrix_birth : ∀ (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index (N + 1))),
    form (N + 1) alpha L K K =
      form (N + 1) alpha L (GibbsBlockResponse.block (birthBlock N) K)
        (GibbsBlockResponse.block (birthBlock N) K) +
      form (N + 1) alpha L (GibbsBlockResponse.off (birthBlock N) K)
        (GibbsBlockResponse.off (birthBlock N) K)

theorem generated : Conclusions where
  actual_partition_update := partition_succ
  actual_birth_fraction := fun N alpha L => ⟨birthFraction_pos N alpha L, birthFraction_lt_one N alpha L⟩
  actual_mixed_response := root_birth_hessian
  actual_joint_response := root_joint_hessian_succ
  actual_reduced_response := birth_schur_response
  complete_matrix_birth := fun N alpha L K =>
    GibbsBlockResponse.response_decomposition (logIntensity (N + 1) alpha L) (birthBlock N) K

end GeneratedFoundations.Analysis.HistoryPrefixBirthResponse
