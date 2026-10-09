module

public import GeneratedFoundations.Spectral.PeriodicH1
public import GeneratedFoundations.Spectral.NeumannCosineBasis
public import GeneratedFoundations.Operations.EigenbasisClosure

/-!
# The original periodic angular generator

The operator is the normalized first weak derivative on the actual periodic
`H¹` domain in probability Haar `L²`. Its eigenfunctions are derived from
their ordinary derivatives. A periodic primitive then recovers every vector
in the adjoint domain, establishing self-adjointness of the original
operator and the weighted Fourier criterion for precisely that domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Interval ComplexConjugate LinearPMap
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Spectral.AngularGenerator

variable (L : ℝ) [hL : Fact (0 < L)]

def factor : ℂ := -Complex.I * (L / Real.pi : ℝ)

theorem factor_ne_zero : factor L ≠ 0 := by
  apply mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
  exact_mod_cast div_ne_zero hL.out.ne' Real.pi_ne_zero

omit hL in
theorem factor_conj : conj (factor L) = -factor L := by
  simp only [factor, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The angular normalization multiplies the actual weak derivative. -/
def operator : HaarCircleL2 L →ₗ.[ℂ] HaarCircleL2 L where
  domain := periodicH1Domain L
  toFun := factor L • (periodicFirstDerivative L).toFun

theorem operator_apply (u : (operator L).domain) :
    operator L u = factor L • periodicFirstDerivative L u := rfl

theorem operator_on_representative (f : PeriodicIntervalH1 L) :
    (operator L).toFun ⟨f.toHaarL2 L, f, rfl⟩ = factor L • f.firstHaarL2 L := by
  change factor L • (periodicFirstDerivative L).toFun ⟨f.toHaarL2 L, f, rfl⟩ = _
  rw [periodicFirstDerivative_on_representative]

theorem formalAdjoint : (operator L).IsFormalAdjoint (operator L) := by
  intro u v
  rw [operator_apply, operator_apply, inner_smul_left, inner_smul_right,
    factor_conj]
  rw [periodicFirstDerivative_skew L u v]
  ring

theorem complexH1_of_contDiff {a b : ℝ} {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hd : ∀ x, HasDerivAt f (g x) x) : HasComplexH1Derivative a b f g := by
  refine ⟨hf.contDiffOn.absolutelyContinuousOnInterval, ?_, ae_of_all _ hd⟩
  obtain ⟨C, hC⟩ := hg.contDiffOn.absolutelyContinuousOnInterval.exists_bound
  apply MemLp.of_bound (hg.continuous.continuousOn.aestronglyMeasurable measurableSet_Icc) C
  exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => hC x (Icc_subset_uIcc hx)

def fourierSlope (n : ℤ) : ℂ := 2 * Real.pi * Complex.I * n / (2 * L : ℝ)

omit hL in
theorem fourier_contDiff (n : ℤ) :
    ContDiff ℝ 1 (fun x : ℝ => fourier (T := 2 * L) n (x : AddCircle (2 * L))) := by
  simp_rw [fourier_coe_apply]
  exact Complex.contDiff_exp.comp
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const (2 * L : ℝ))

def fourierRepresentative (n : ℤ) : PeriodicIntervalH1 L where
  value := fun x => fourier n (x : AddCircle (2 * L))
  first := fun x => fourierSlope L n * fourier n (x : AddCircle (2 * L))
  firstDerivative := complexH1_of_contDiff (fourier_contDiff L n)
    (contDiff_const.mul (fourier_contDiff L n)) (hasDerivAt_fourier (2 * L) n)
  value_match := by
    apply congrArg (fourier n)
    have h := AddCircle.coe_add_period (2 * L) (-L)
    simpa only [show -L + 2 * L = L by ring] using h.symm

theorem fourierRepresentative_value (n : ℤ) :
    (fourierRepresentative L n).toHaarL2 L = fourierLp 2 n := by
  apply Lp.ext
  filter_upwards [circleHaarLift_coe L (fourierRepresentative L n).firstDerivative.value_memLp,
    coeFn_fourierLp (T := 2 * L) 2 n] with z hz hn
  change circleHaarLift L (fourierRepresentative L n).firstDerivative.value_memLp z =
    fourierLp 2 n z
  rw [hz, hn]
  exact circleLift_pullback L (fourier n) z

theorem fourierRepresentative_first (n : ℤ) :
    (fourierRepresentative L n).firstHaarL2 L = fourierSlope L n • fourierLp 2 n := by
  rw [← fourierRepresentative_value L n]
  rfl

theorem factor_mul_slope (n : ℤ) : factor L * fourierSlope L n = (n : ℂ) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
  have hpc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [factor, fourierSlope, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp [hLc, hpc]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem fourier_mem_domain (n : ℤ) : fourierLp (T := 2 * L) 2 n ∈ (operator L).domain :=
  ⟨fourierRepresentative L n, fourierRepresentative_value L n⟩

theorem operator_fourier (n : ℤ) :
    operator L ⟨fourierLp 2 n, fourier_mem_domain L n⟩ = (n : ℂ) • fourierLp 2 n := by
  have heq : (⟨fourierLp 2 n, fourier_mem_domain L n⟩ : (operator L).domain) =
      ⟨(fourierRepresentative L n).toHaarL2 L, fourierRepresentative L n, rfl⟩ :=
    Subtype.ext (fourierRepresentative_value L n).symm
  rw [heq]
  change (operator L).toFun
    ⟨(fourierRepresentative L n).toHaarL2 L, fourierRepresentative L n, rfl⟩ = _
  rw [operator_on_representative, fourierRepresentative_first,
    smul_smul, factor_mul_slope]

theorem basis_mem_domain (n : ℤ) : fourierBasis (T := 2 * L) n ∈ (operator L).domain := by
  simpa only [coe_fourierBasis] using fourier_mem_domain L n

theorem operator_basis (n : ℤ) :
    operator L ⟨fourierBasis n, basis_mem_domain L n⟩ =
      ((n : ℝ) : ℂ) • fourierBasis n := by
  simpa only [coe_fourierBasis, Complex.ofReal_intCast] using operator_fourier L n

theorem domain_dense : Dense ((operator L).domain : Set (HaarCircleL2 L)) :=
  EigenbasisClosure.domain_dense fourierBasis (operator L) (basis_mem_domain L)

theorem coefficients (u : (operator L).domain) (n : ℤ) :
    inner ℂ (fourierLp (T := 2 * L) 2 n) (operator L u) =
      (n : ℂ) * inner ℂ (fourierLp 2 n) (u : HaarCircleL2 L) := by
  simpa only [coe_fourierBasis, Complex.ofReal_intCast] using
    EigenbasisClosure.operator_coefficients fourierBasis (operator L) (fun n : ℤ => (n : ℝ))
      (basis_mem_domain L) (operator_basis L) (formalAdjoint L) u n

theorem adjoint_coefficients (u : (operator L).adjoint.domain) (n : ℤ) :
    inner ℂ (fourierLp (T := 2 * L) 2 n) ((operator L).adjoint u) =
      (n : ℂ) * inner ℂ (fourierLp 2 n) (u : HaarCircleL2 L) := by
  simpa only [coe_fourierBasis, Complex.ofReal_intCast] using
    EigenbasisClosure.adjoint_coefficients fourierBasis (operator L) (fun n : ℤ => (n : ℝ))
      (basis_mem_domain L) (operator_basis L) u n

theorem zero_inner_integral (f : HaarCircleL2 L) :
    inner ℂ (fourierLp (T := 2 * L) 2 0) f = ∫ z, f z ∂AddCircle.haarAddCircle := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp (T := 2 * L) 2 0] with z hz
  simp only [hz, fourier_zero, RCLike.inner_apply', map_one, one_mul]

theorem range_iff_mean_zero (g : HaarCircleL2 L) :
    (∃ u : (operator L).domain, operator L u = g) ↔
      (∫ z, g z ∂AddCircle.haarAddCircle) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [← zero_inner_integral, coefficients, Int.cast_zero, zero_mul]
  · intro hg
    have hg' : (∫ z, ((factor L)⁻¹ • g) z ∂AddCircle.haarAddCircle) = 0 := by
      rw [integral_congr_ae (Lp.coeFn_smul (factor L)⁻¹ g)]
      simp only [Pi.smul_apply, integral_smul, hg, smul_zero]
    obtain ⟨u, hu⟩ := (periodicFirstDerivative_range L ((factor L)⁻¹ • g)).mpr hg'
    refine ⟨u, ?_⟩
    change factor L • periodicFirstDerivative L u = g
    rw [hu, smul_smul, mul_inv_cancel₀ (factor_ne_zero L), one_smul]

/-- The primitive construction recovers the original Sobolev regularity of
every adjoint-domain vector; no spectral-domain equality is assumed. -/
theorem adjoint_domain_le : (operator L).adjoint.domain ≤ (operator L).domain := by
  intro f hf
  let y : (operator L).adjoint.domain := ⟨f, hf⟩
  let g := (operator L).adjoint y
  have hg : (∫ z, g z ∂AddCircle.haarAddCircle) = 0 := by
    rw [← zero_inner_integral]
    simpa only [Int.cast_zero, zero_mul] using adjoint_coefficients L y 0
  obtain ⟨v, hv⟩ := (range_iff_mean_zero L g).mpr hg
  let c := inner ℂ (fourierLp (T := 2 * L) 2 0) f -
    inner ℂ (fourierLp 2 0) (v : HaarCircleL2 L)
  let w : (operator L).domain := v + c • ⟨fourierLp 2 0, fourier_mem_domain L 0⟩
  have hw : (w : HaarCircleL2 L) = f := by
    apply EigenbasisClosure.eq_of_coefficients fourierBasis
    intro n
    simp only [coe_fourierBasis]
    change inner ℂ (fourierLp (T := 2 * L) 2 n)
      ((v : HaarCircleL2 L) + c • fourierLp 2 0) = _
    rw [inner_add_right, inner_smul_right, haarFourier_inner]
    by_cases hn : n = 0
    · subst n
      simp only [ite_true, mul_one]
      dsimp only [c]
      ring
    · simp only [hn, ite_false, mul_zero, add_zero]
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hvn := coefficients L v n
      rw [hv] at hvn
      exact mul_left_cancel₀ hn' (hvn.symm.trans (adjoint_coefficients L y n))
  rw [← hw]
  exact w.property

theorem adjoint_eq : (operator L).adjoint = operator L := by
  apply le_antisymm
  · refine ⟨adjoint_domain_le L, ?_⟩
    intro x y hxy
    apply EigenbasisClosure.eq_of_coefficients fourierBasis
    intro n
    simp only [coe_fourierBasis]
    rw [adjoint_coefficients, coefficients, hxy]
  · exact EigenbasisClosure.le_adjoint fourierBasis (operator L)
      (basis_mem_domain L) (formalAdjoint L)

theorem selfAdjoint : IsSelfAdjoint (operator L) :=
  LinearPMap.isSelfAdjoint_def.mpr (adjoint_eq L)

theorem closed : (operator L).IsClosed := (selfAdjoint L).isClosed

theorem domain_iff_weighted_fourier (f : HaarCircleL2 L) :
    f ∈ (operator L).domain ↔
      Summable (fun n : ℤ => (n : ℝ) ^ 2 * ‖inner ℂ (fourierLp 2 n) f‖ ^ 2) := by
  have h := EigenbasisClosure.adjoint_domain_iff_summable fourierBasis (operator L)
    (fun n : ℤ => (n : ℝ)) (basis_mem_domain L) (operator_basis L) (formalAdjoint L) f
  simpa only [adjoint_eq, coe_fourierBasis] using h

theorem eigenvalue_iff (z : ℂ) :
    (∃ f : (operator L).domain, (f : HaarCircleL2 L) ≠ 0 ∧
      operator L f = z • (f : HaarCircleL2 L)) ↔ ∃ n : ℤ, z = (n : ℂ) := by
  constructor
  · rintro ⟨f, hf, heig⟩
    have hn : ∃ n : ℤ, inner ℂ (fourierLp (T := 2 * L) 2 n) (f : HaarCircleL2 L) ≠ 0 := by
      by_contra h
      push Not at h
      apply hf
      apply EigenbasisClosure.eq_of_coefficients fourierBasis
      intro n
      simpa only [coe_fourierBasis, inner_zero_right] using h n
    obtain ⟨n, hn⟩ := hn
    refine ⟨n, ?_⟩
    have hc := coefficients L f n
    rw [heig, inner_smul_right] at hc
    exact mul_right_cancel₀ hn hc
  · rintro ⟨n, rfl⟩
    exact ⟨⟨fourierLp 2 n, fourier_mem_domain L n⟩,
      orthonormal_fourier.ne_zero n, operator_fourier L n⟩

theorem eigenvector_iff (n : ℤ) (f : (operator L).domain) :
    operator L f = (n : ℂ) • (f : HaarCircleL2 L) ↔
      ∃ c : ℂ, (f : HaarCircleL2 L) = c • fourierLp 2 n := by
  constructor
  · intro heig
    refine ⟨inner ℂ (fourierLp (T := 2 * L) 2 n) (f : HaarCircleL2 L), ?_⟩
    apply EigenbasisClosure.eq_of_coefficients fourierBasis
    intro i
    simp only [coe_fourierBasis]
    rw [inner_smul_right, haarFourier_inner]
    by_cases hin : i = n
    · subst i
      simp only [ite_true, mul_one]
    · have hz : inner ℂ (fourierLp (T := 2 * L) 2 i) (f : HaarCircleL2 L) = 0 := by
        by_contra hzero
        have hc := coefficients L f i
        rw [heig, inner_smul_right] at hc
        have hi : (n : ℂ) = (i : ℂ) := mul_right_cancel₀ hzero hc
        exact hin (by exact_mod_cast hi.symm)
      simp only [hin, ite_false, mul_zero, hz]
  · rintro ⟨c, hc⟩
    apply EigenbasisClosure.eq_of_coefficients fourierBasis
    intro i
    simp only [coe_fourierBasis]
    rw [coefficients, inner_smul_right, hc, inner_smul_right, haarFourier_inner]
    by_cases hin : i = n
    · subst i
      rfl
    · simp only [hin, ite_false, mul_zero]

theorem kernel_iff_constant (f : (operator L).domain) :
    operator L f = 0 ↔ ∃ c : ℂ, (f : HaarCircleL2 L) = c • fourierLp 2 0 := by
  simpa only [Int.cast_zero, zero_smul] using eigenvector_iff L 0 f

/-- Completeness refers to the full complex circle, not its even part. -/
theorem eigenfunctions_complete (f : HaarCircleL2 L) :
    HasSum (fun n : ℤ => inner ℂ (fourierLp 2 n) f • fourierLp 2 n) f := by
  simpa only [HilbertBasis.repr_apply_apply, coe_fourierBasis] using
    HilbertBasis.hasSum_repr (fourierBasis (T := 2 * L)) f

end GeneratedFoundations.Spectral.AngularGenerator
