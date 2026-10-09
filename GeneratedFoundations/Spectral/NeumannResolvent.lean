module

public import GeneratedFoundations.Spectral.NeumannSpectralDomain
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# A compact resolvent of the Neumann differential operator

The inverse of `I + A` is constructed on the original interval Hilbert space
as an operator-norm convergent sum of rank-one maps. Its coefficients place
its range in the actual Sobolev domain. Both inverse identities are proved
for the original differential operator. Compactness follows from the finite
rank partial sums and the closedness of the compact operators.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter InnerProductSpace
open scoped Topology ComplexConjugate LinearPMap
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

def neumannResolventWeight (n : ℕ) : ℝ := (1 + neumannEigenvalue L n)⁻¹

omit hL in
theorem neumannResolventWeight_pos (n : ℕ) : 0 < neumannResolventWeight L n :=
  inv_pos.mpr (add_pos_of_pos_of_nonneg zero_lt_one (neumannEigenvalue_nonneg L n))

theorem neumannResolventWeight_summable : Summable (neumannResolventWeight L) := by
  have hseries : Summable (fun n : ℕ => (L / Real.pi) ^ 2 * ((n : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_norm_bounded ((summable_nat_add_iff 1).mpr hseries)
  intro n
  rw [Real.norm_eq_abs, abs_of_pos (neumannResolventWeight_pos L (n + 1))]
  calc
    neumannResolventWeight L (n + 1) ≤ (neumannEigenvalue L (n + 1))⁻¹ :=
      inv_anti₀ (neumannEigenvalue_pos L (Nat.succ_pos n)) (by linarith)
    _ = (L / Real.pi) ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      dsimp only [neumannEigenvalue]
      field_simp [hn, hL.out.ne', Real.pi_ne_zero]

def neumannResolventTerm (n : ℕ) : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L :=
  (neumannResolventWeight L n : ℂ) •
    rankOne ℂ (neumannCosineMode L n) (neumannCosineMode L n)

theorem neumannResolventTerm_norm (n : ℕ) :
    ‖neumannResolventTerm L n‖ = neumannResolventWeight L n := by
  rw [neumannResolventTerm, norm_smul, norm_rankOne,
    (neumannCosineMode_orthonormal L).norm_eq_one n]
  simp only [mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (neumannResolventWeight_pos L n)]

theorem neumannResolventTerm_summable : Summable (neumannResolventTerm L) := by
  apply Summable.of_norm
  simpa only [neumannResolventTerm_norm] using neumannResolventWeight_summable L

/-- The bounded inverse of `I + A` on the original interval Hilbert space. -/
def neumannResolvent : ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L :=
  ∑' n : ℕ, neumannResolventTerm L n

theorem neumannResolvent_hasSum : HasSum (neumannResolventTerm L) (neumannResolvent L) :=
  (neumannResolventTerm_summable L).hasSum

def neumannResolventTruncation (N : ℕ) :
    ComplexIntervalL2 0 L →L[ℂ] ComplexIntervalL2 0 L :=
  ∑ n ∈ Finset.range N, neumannResolventTerm L n

theorem neumannResolventTruncation_tendsto :
    Tendsto (neumannResolventTruncation L) atTop (𝓝 (neumannResolvent L)) :=
  (neumannResolvent_hasSum L).tendsto_sum_nat

theorem neumannResolventTruncation_norm_tendsto_zero :
    Tendsto (fun N => ‖neumannResolventTruncation L N - neumannResolvent L‖)
      atTop (𝓝 0) := by
  simpa only [sub_self, norm_zero] using
    ((neumannResolventTruncation_tendsto L).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => neumannResolvent L) atTop
        (𝓝 (neumannResolvent L)))).norm

theorem neumannResolventTerm_isCompact (n : ℕ) :
    IsCompactOperator (neumannResolventTerm L n) := by
  have h : IsCompactOperator
      (rankOne ℂ (neumannCosineMode L n) (neumannCosineMode L n)) := by
    rw [rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ (neumannCosineMode L n))).comp_clm
        (innerSL ℂ (neumannCosineMode L n))
  exact h.smul (neumannResolventWeight L n : ℂ)

theorem neumannResolventTruncation_isCompact (N : ℕ) :
    IsCompactOperator (neumannResolventTruncation L N) := by
  let K := compactOperator (RingHom.id ℂ) (ComplexIntervalL2 0 L) (ComplexIntervalL2 0 L)
  exact K.sum_mem fun n _ => neumannResolventTerm_isCompact L n

theorem neumannResolvent_isCompact : IsCompactOperator (neumannResolvent L) :=
  isCompactOperator_of_tendsto (neumannResolventTruncation_tendsto L)
    (Eventually.of_forall (neumannResolventTruncation_isCompact L))

theorem neumannResolvent_coefficients (f : ComplexIntervalL2 0 L) (n : ℕ) :
    inner ℂ (neumannCosineMode L n) (neumannResolvent L f) =
      (neumannResolventWeight L n : ℂ) * inner ℂ (neumannCosineMode L n) f := by
  have hs := (innerSL ℂ (neumannCosineMode L n)).hasSum
    (hasSum_apply (neumannResolvent_hasSum L) f)
  have hterm : ∀ m : ℕ,
      inner ℂ (neumannCosineMode L n) (neumannResolventTerm L m f) =
        if m = n then (neumannResolventWeight L n : ℂ) *
          inner ℂ (neumannCosineMode L n) f else 0 := by
    intro m
    simp only [neumannResolventTerm, smul_apply, rankOne_apply,
      inner_smul_right, orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L) n m]
    by_cases hm : m = n
    · subst m
      simp
    · simp [hm, Ne.symm hm]
  have hsingle : HasSum (fun m : ℕ => if m = n then
      (neumannResolventWeight L n : ℂ) * inner ℂ (neumannCosineMode L n) f else 0)
      ((neumannResolventWeight L n : ℂ) * inner ℂ (neumannCosineMode L n) f) :=
    hasSum_ite_eq n _
  exact (hs.congr_fun (fun m => (hterm m).symm)).unique hsingle

omit hL in
private theorem neumannResolventWeight_identity (n : ℕ) (c : ℂ) :
    c - (neumannResolventWeight L n : ℂ) * c =
      (neumannEigenvalue L n : ℂ) * ((neumannResolventWeight L n : ℂ) * c) := by
  have hr : (1 : ℝ) + neumannEigenvalue L n ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (neumannEigenvalue_nonneg L n))
  have hc : (1 : ℂ) + (neumannEigenvalue L n : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [neumannResolventWeight, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one]
  field_simp [hc]
  ring

/-- The range lies in the original absolutely continuous Neumann domain. -/
theorem neumannResolvent_mem_domain (f : ComplexIntervalL2 0 L) :
    neumannResolvent L f ∈ (complexNeumannOperator hL.out).domain := by
  apply complexNeumannAdjoint_domain_le L
  apply (EigenbasisClosure.adjoint_domain_iff (neumannCosineBasis L)
    (complexNeumannOperator hL.out) (neumannEigenvalue L)
    (neumannCosineBasis_mem_domain L) (complexNeumannOperator_cosineBasis L)
    (complexNeumann_formalAdjoint hL.out) (neumannResolvent L f)).mpr
  refine ⟨f - neumannResolvent L f, fun n => ?_⟩
  simp only [coe_neumannCosineBasis, inner_sub_right, neumannResolvent_coefficients]
  exact neumannResolventWeight_identity L n _

theorem complexNeumannOperator_resolvent (f : ComplexIntervalL2 0 L) :
    complexNeumannOperator hL.out
      ⟨neumannResolvent L f, neumannResolvent_mem_domain L f⟩ = f - neumannResolvent L f := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
  intro n
  simp only [coe_neumannCosineBasis, complexNeumannOperator_coefficients,
    inner_sub_right, neumannResolvent_coefficients]
  exact (neumannResolventWeight_identity L n _).symm

theorem neumannResolvent_right_inverse (f : ComplexIntervalL2 0 L) :
    neumannResolvent L f + complexNeumannOperator hL.out
      ⟨neumannResolvent L f, neumannResolvent_mem_domain L f⟩ = f := by
  rw [complexNeumannOperator_resolvent]
  abel

theorem neumannResolvent_left_inverse (f : (complexNeumannOperator hL.out).domain) :
    neumannResolvent L ((f : ComplexIntervalL2 0 L) + complexNeumannOperator hL.out f) =
      (f : ComplexIntervalL2 0 L) := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
  intro n
  simp only [coe_neumannCosineBasis, neumannResolvent_coefficients, inner_add_right,
    complexNeumannOperator_coefficients]
  have h := neumannResolventWeight_identity L n
    (inner ℂ (neumannCosineMode L n) (f : ComplexIntervalL2 0 L))
  calc
    _ = (neumannResolventWeight L n : ℂ) *
        inner ℂ (neumannCosineMode L n) (f : ComplexIntervalL2 0 L) +
      (neumannEigenvalue L n : ℂ) * ((neumannResolventWeight L n : ℂ) *
        inner ℂ (neumannCosineMode L n) (f : ComplexIntervalL2 0 L)) := by ring
    _ = _ := by rw [← h]; ring

end GeneratedFoundations.Spectral
