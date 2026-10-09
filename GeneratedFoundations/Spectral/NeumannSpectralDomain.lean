module

public import GeneratedFoundations.Spectral.NeumannCosineEigenfunctions
public import GeneratedFoundations.Spectral.NeumannPoisson
public import GeneratedFoundations.Operations.EigenbasisClosure

/-!
# The full domain of the interval Neumann operator

The complete cosine basis is a family of eigenvectors of the actual Sobolev
operator. Its adjoint is tested against these eigenvectors. The independently
constructed Poisson solution then recovers every adjoint-domain vector in the
original Neumann domain, including its constant component. Thus the original
operator, rather than only a diagonal extension, is self-adjoint.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate LinearPMap
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

theorem neumannCosineMode_zero_inner (f : ComplexIntervalL2 0 L) :
    inner ℂ (neumannCosineMode L 0) f =
      (Real.sqrt L : ℂ)⁻¹ * intervalIntegralL2 f := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (Real.sqrt L : ℂ)⁻¹ * f x ∂intervalMeasure 0 L := by
      apply integral_congr_ae
      filter_upwards [neumannCosineMode_zero_coe L] with x hx
      simp only [hx, RCLike.inner_apply', map_inv₀, Complex.conj_ofReal]
    _ = _ := integral_const_mul _ _

theorem neumannCosineMode_zero_inner_eq_zero_iff (f : ComplexIntervalL2 0 L) :
    inner ℂ (neumannCosineMode L 0) f = 0 ↔ intervalIntegralL2 f = 0 := by
  have hs : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hL.out).ne'
  rw [neumannCosineMode_zero_inner, mul_eq_zero]
  simp only [inv_ne_zero hs, false_or]

theorem complexNeumann_domain_dense :
    Dense ((complexNeumannOperator hL.out).domain : Set (ComplexIntervalL2 0 L)) :=
  EigenbasisClosure.domain_dense (neumannCosineBasis L) (complexNeumannOperator hL.out)
    (neumannCosineBasis_mem_domain L)

theorem complexNeumannOperator_coefficients
    (f : (complexNeumannOperator hL.out).domain) (n : ℕ) :
    inner ℂ (neumannCosineMode L n) (complexNeumannOperator hL.out f) =
      (neumannEigenvalue L n : ℂ) * inner ℂ (neumannCosineMode L n)
        (f : ComplexIntervalL2 0 L) := by
  simpa only [coe_neumannCosineBasis] using
    EigenbasisClosure.operator_coefficients (neumannCosineBasis L)
      (complexNeumannOperator hL.out) (neumannEigenvalue L)
      (neumannCosineBasis_mem_domain L) (complexNeumannOperator_cosineBasis L)
      (complexNeumann_formalAdjoint hL.out) f n

theorem complexNeumannAdjoint_coefficients
    (f : (complexNeumannOperator hL.out).adjoint.domain) (n : ℕ) :
    inner ℂ (neumannCosineMode L n) ((complexNeumannOperator hL.out).adjoint f) =
      (neumannEigenvalue L n : ℂ) * inner ℂ (neumannCosineMode L n)
        (f : ComplexIntervalL2 0 L) := by
  simpa only [coe_neumannCosineBasis] using
    EigenbasisClosure.adjoint_coefficients (neumannCosineBasis L)
      (complexNeumannOperator hL.out) (neumannEigenvalue L)
      (neumannCosineBasis_mem_domain L) (complexNeumannOperator_cosineBasis L) f n

/-- Every actual adjoint-domain vector has a Neumann Sobolev representative. -/
theorem complexNeumannAdjoint_domain_le :
    (complexNeumannOperator hL.out).adjoint.domain ≤ (complexNeumannOperator hL.out).domain := by
  intro f hf
  let y : (complexNeumannOperator hL.out).adjoint.domain := ⟨f, hf⟩
  let g := (complexNeumannOperator hL.out).adjoint y
  have hg : intervalIntegralL2 g = 0 := by
    apply (neumannCosineMode_zero_inner_eq_zero_iff L g).mp
    simpa only [neumannEigenvalue_zero, Complex.ofReal_zero, zero_mul] using
      complexNeumannAdjoint_coefficients L y 0
  obtain ⟨v, hv, _⟩ := neumannPoisson_exists hL.out g hg
  let c := inner ℂ (neumannCosineMode L 0) f -
    inner ℂ (neumannCosineMode L 0) (v : ComplexIntervalL2 0 L)
  let w : (complexNeumannOperator hL.out).domain :=
    v + c • ⟨neumannCosineMode L 0, neumannCosineMode_mem_domain L 0⟩
  have hw : (w : ComplexIntervalL2 0 L) = f := by
    apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
    intro n
    simp only [coe_neumannCosineBasis]
    change inner ℂ (neumannCosineMode L n)
      ((v : ComplexIntervalL2 0 L) + c • neumannCosineMode L 0) = _
    rw [inner_add_right, inner_smul_right]
    cases n with
    | zero =>
        rw [orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L) 0 0]
        simp only [ite_true, mul_one]
        dsimp only [c]
        ring
    | succ n =>
        have hn0 : inner ℂ (neumannCosineMode L (n + 1)) (neumannCosineMode L 0) = 0 := by
          simpa using orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L) (n + 1) 0
        rw [hn0, mul_zero, add_zero]
        have hpos : 0 < neumannEigenvalue L (n + 1) :=
          neumannEigenvalue_pos L (Nat.succ_pos n)
        have hn : (neumannEigenvalue L (n + 1) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
        have hvn := complexNeumannOperator_coefficients L v (n + 1)
        rw [hv] at hvn
        exact mul_left_cancel₀ hn (hvn.symm.trans (complexNeumannAdjoint_coefficients L y (n + 1)))
  rw [← hw]
  exact w.property

theorem complexNeumann_adjoint_eq :
    (complexNeumannOperator hL.out).adjoint = complexNeumannOperator hL.out := by
  apply le_antisymm
  · refine ⟨complexNeumannAdjoint_domain_le L, ?_⟩
    intro x y hxy
    apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
    intro n
    simp only [coe_neumannCosineBasis]
    rw [complexNeumannAdjoint_coefficients, complexNeumannOperator_coefficients, hxy]
  · exact EigenbasisClosure.le_adjoint (neumannCosineBasis L)
      (complexNeumannOperator hL.out) (neumannCosineBasis_mem_domain L)
      (complexNeumann_formalAdjoint hL.out)

theorem complexNeumann_selfAdjoint : IsSelfAdjoint (complexNeumannOperator hL.out) :=
  LinearPMap.isSelfAdjoint_def.mpr (complexNeumann_adjoint_eq L)

theorem complexNeumann_closed : (complexNeumannOperator hL.out).IsClosed :=
  (complexNeumann_selfAdjoint L).isClosed

theorem complexNeumann_operator_nonnegative
    (f : (complexNeumannOperator hL.out).domain) :
    0 ≤ (inner ℂ (complexNeumannOperator hL.out f) (f : ComplexIntervalL2 0 L)).re := by
  change 0 ≤ (inner ℂ (-(complexNeumannRepresentative f).secondL2)
    (f : ComplexIntervalL2 0 L)).re
  rw [← (complexNeumannRepresentative_spec f).2]
  exact complexNeumann_nonnegative hL.out.le (complexNeumannRepresentative f)
    (complexNeumannRepresentative_spec f).1

/-- The coefficient criterion characterizes the original differential domain. -/
theorem complexNeumann_domain_iff (f : ComplexIntervalL2 0 L) :
    f ∈ (complexNeumannOperator hL.out).domain ↔
      Summable (fun n : ℕ => (neumannEigenvalue L n) ^ 2 *
        ‖inner ℂ (neumannCosineMode L n) f‖ ^ 2) := by
  have h := EigenbasisClosure.adjoint_domain_iff_summable (neumannCosineBasis L)
    (complexNeumannOperator hL.out) (neumannEigenvalue L)
    (neumannCosineBasis_mem_domain L) (complexNeumannOperator_cosineBasis L)
    (complexNeumann_formalAdjoint hL.out) f
  simpa only [complexNeumann_adjoint_eq, coe_neumannCosineBasis] using h

theorem complexNeumann_closure_eq :
    (complexNeumannOperator hL.out).closure = complexNeumannOperator hL.out := by
  rw [EigenbasisClosure.closure_eq_adjoint (neumannCosineBasis L)
    (complexNeumannOperator hL.out) (neumannEigenvalue L)
    (neumannCosineBasis_mem_domain L) (complexNeumannOperator_cosineBasis L)
    (complexNeumann_formalAdjoint hL.out), complexNeumann_adjoint_eq]

theorem complexNeumann_selfAdjoint_extension_unique
    (S : ComplexIntervalL2 0 L →ₗ.[ℂ] ComplexIntervalL2 0 L)
    (hS : IsSelfAdjoint S) (hTS : complexNeumannOperator hL.out ≤ S) :
    S = complexNeumannOperator hL.out := by
  have h := EigenbasisClosure.selfAdjoint_extension_unique (neumannCosineBasis L)
    (complexNeumannOperator hL.out) (neumannEigenvalue L)
    (neumannCosineBasis_mem_domain L) (complexNeumannOperator_cosineBasis L)
    (complexNeumann_formalAdjoint hL.out) S hS hTS
  exact h.trans (complexNeumann_closure_eq L)

/-- The eigenvalues are exhausted by the modes of the actual differential operator. -/
theorem complexNeumann_eigenvalue_iff (z : ℂ) :
    (∃ f : (complexNeumannOperator hL.out).domain,
      (f : ComplexIntervalL2 0 L) ≠ 0 ∧
        complexNeumannOperator hL.out f = z • (f : ComplexIntervalL2 0 L)) ↔
      ∃ n : ℕ, z = (neumannEigenvalue L n : ℂ) := by
  constructor
  · rintro ⟨f, hf, heig⟩
    have hcoeff : ∃ n : ℕ, inner ℂ (neumannCosineMode L n) (f : ComplexIntervalL2 0 L) ≠ 0 := by
      by_contra h
      push Not at h
      apply hf
      apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
      intro n
      simpa only [coe_neumannCosineBasis, inner_zero_right] using h n
    obtain ⟨n, hn⟩ := hcoeff
    refine ⟨n, ?_⟩
    have hc := complexNeumannOperator_coefficients L f n
    rw [heig, inner_smul_right] at hc
    exact mul_right_cancel₀ hn hc
  · rintro ⟨n, rfl⟩
    exact ⟨⟨neumannCosineMode L n, neumannCosineMode_mem_domain L n⟩,
      (neumannCosineMode_orthonormal L).ne_zero n, complexNeumannOperator_cosine L n⟩

theorem neumannEigenvalue_strictMono : StrictMono (neumannEigenvalue L) := by
  intro m n hmn
  unfold neumannEigenvalue
  apply (sq_lt_sq₀
    (div_nonneg (mul_nonneg (Nat.cast_nonneg m) Real.pi_pos.le) hL.out.le)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le) hL.out.le)).mpr
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by exact_mod_cast hmn) Real.pi_pos) hL.out

/-- Each eigenspace in the original Sobolev domain is exactly one complex line. -/
theorem complexNeumann_eigenvector_iff (n : ℕ)
    (f : (complexNeumannOperator hL.out).domain) :
    complexNeumannOperator hL.out f =
      (neumannEigenvalue L n : ℂ) • (f : ComplexIntervalL2 0 L) ↔
    ∃ c : ℂ, (f : ComplexIntervalL2 0 L) = c • neumannCosineMode L n := by
  constructor
  · intro heig
    refine ⟨inner ℂ (neumannCosineMode L n) (f : ComplexIntervalL2 0 L), ?_⟩
    apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
    intro i
    simp only [coe_neumannCosineBasis]
    rw [inner_smul_right, orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L)]
    by_cases hin : i = n
    · subst i
      simp only [ite_true, mul_one]
    · have hi : inner ℂ (neumannCosineMode L i) (f : ComplexIntervalL2 0 L) = 0 := by
        by_contra hzero
        have hc := complexNeumannOperator_coefficients L f i
        rw [heig, inner_smul_right] at hc
        have he : neumannEigenvalue L n = neumannEigenvalue L i :=
          Complex.ofReal_injective (mul_right_cancel₀ hzero hc)
        exact hin ((neumannEigenvalue_strictMono L).injective he).symm
      simp only [hin, ite_false, mul_zero, hi]
  · rintro ⟨c, hc⟩
    apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis L)
    intro i
    simp only [coe_neumannCosineBasis]
    rw [complexNeumannOperator_coefficients, inner_smul_right, hc, inner_smul_right,
      orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L)]
    by_cases hin : i = n
    · subst i
      rfl
    · simp only [hin, ite_false, mul_zero]

end GeneratedFoundations.Spectral
