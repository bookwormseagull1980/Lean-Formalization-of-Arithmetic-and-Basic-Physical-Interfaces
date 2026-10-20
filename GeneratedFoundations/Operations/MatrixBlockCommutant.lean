module

public import GeneratedFoundations.Operations.MatrixBlockRepresentations

/-!
# Commutants of complete finite matrix-block actions

The algebra contains every matrix unit in every block. Commuting with
these actual operations forces an endomorphism to be scalar on each
whole block; no invariant-block hypothesis is supplied separately.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Operations.MatrixBlockCommutant

open MatrixBlockRepresentations

variable {K B : Type*} [Field K] [DecidableEq B] (n : B → ℕ)

def unitVector (b : B) (i : Fin (n b)) : ∀ c, Fin (n c) → K :=
  Pi.single b (Pi.single i 1)

theorem unit_action (b : B) (i j : Fin (n b)) (x : ∀ c, Fin (n c) → K) :
    standardRepresentation (K := K) n (algebraUnit n b i j) x = x b j • unitVector n b i := by
  funext c k
  by_cases h : b = c
  · subst c
    simp [standardRepresentation, LinearMap.piMap, algebraUnit, unitVector,
      Pi.single_apply, Matrix.single_mulVec, smul_eq_mul, mul_comm, Function.update_apply]
  · simp [standardRepresentation, LinearMap.piMap, algebraUnit, unitVector, h]

theorem commutant_scalar
    (base : ∀ b, Fin (n b)) (T : Module.End K (∀ b, Fin (n b) → K))
    (hT : ∀ a x, T (standardRepresentation (K := K) n a x) =
      standardRepresentation (K := K) n a (T x)) :
    ∃ c : B → K, ∀ x b i, T x b i = c b * x b i := by
  refine ⟨fun b => T (unitVector n b (base b)) b (base b), ?_⟩
  intro x b i
  have h := congrArg (fun y : ∀ b, Fin (n b) → K => y b (base b))
    (hT (algebraUnit n b (base b) i) x)
  rw [unit_action, unit_action, map_smul] at h
  simpa [unitVector, mul_comm] using h.symm

omit [DecidableEq B] in
theorem scalar_commutes (c : B → K)
    (T : Module.End K (∀ b, Fin (n b) → K))
    (hT : ∀ x b i, T x b i = c b * x b i) :
    ∀ a x, T (standardRepresentation (K := K) n a x) =
      standardRepresentation (K := K) n a (T x) := by
  intro a x
  funext b i
  rw [hT]
  change c b * (∑ j, a b i j * x b j) = ∑ j, a b i j * T x b j
  simp only [hT, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hilbert_commutant_scalar [Fintype B]
    (n : B → ℕ) (base : ∀ b, Fin (n b))
    (T : Module.End ℂ (StandardHilbert n))
    (hT : ∀ a x, T (standardHilbertRepresentation n a x) =
      standardHilbertRepresentation n a (T x)) :
    ∃ c : B → ℂ, ∀ x b i, T x b i = c b * x b i := by
  let U := standardHilbertCoordinates n
  let S : Module.End ℂ (∀ b, Fin (n b) → ℂ) := U.symm.conjAlgEquiv ℂ T
  have hS : ∀ a x, S (standardRepresentation (K := ℂ) n a x) =
      standardRepresentation (K := ℂ) n a (S x) := by
    intro a x
    apply U.injective
    simpa [S, U, standardHilbertRepresentation, AlgHom.comp_apply,
      LinearEquiv.conjAlgEquiv_apply] using hT a (U x)
  obtain ⟨c, hc⟩ := commutant_scalar n base S hS
  refine ⟨c, ?_⟩
  intro x b i
  have h := hc (U.symm x) b i
  change (U.symm (T (U (U.symm x)))) b i = c b * (U.symm x) b i at h
  rw [U.apply_symm_apply] at h
  exact h

end GeneratedFoundations.Operations.MatrixBlockCommutant
