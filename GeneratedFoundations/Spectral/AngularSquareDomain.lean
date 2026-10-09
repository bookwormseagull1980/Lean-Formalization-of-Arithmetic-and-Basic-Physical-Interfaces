module

public import GeneratedFoundations.Spectral.OrientedLift
public import GeneratedFoundations.Spectral.NeumannScaleTransport
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The square of the original angular derivative

The square acts on exactly those vectors in the original periodic `H¹`
domain whose first image is again in that domain. Its Fourier criterion is
derived from this definition. The oriented lift identifies this full domain
on the nonnegative channel with the original Neumann domain and intertwines
the two unbounded operators after division by the first positive energy.
-/

@[expose] public section

noncomputable section

open InnerProductSpace Set
open scoped LinearPMap
open GeneratedFoundations.Operations
open GeneratedFoundations.Spectral.AngularSpectralChannels

namespace GeneratedFoundations.Spectral.AngularSquareDomain

variable (L : ℝ) [hL : Fact (0 < L)]

/-- The second application must exist in the original differential domain. -/
def squareDomain : Submodule ℂ (HaarCircleL2 L) where
  carrier := {f | ∃ hf : f ∈ (AngularGenerator.operator L).domain,
    AngularGenerator.operator L ⟨f, hf⟩ ∈ (AngularGenerator.operator L).domain}
  zero_mem' := by
    refine ⟨(AngularGenerator.operator L).domain.zero_mem, ?_⟩
    change (AngularGenerator.operator L).toFun 0 ∈ _
    rw [map_zero]
    exact (AngularGenerator.operator L).domain.zero_mem
  add_mem' := by
    rintro f g ⟨hf, hDf⟩ ⟨hg, hDg⟩
    refine ⟨(AngularGenerator.operator L).domain.add_mem hf hg, ?_⟩
    have hmap := (AngularGenerator.operator L).toFun.map_add
      (⟨f, hf⟩ : (AngularGenerator.operator L).domain)
      (⟨g, hg⟩ : (AngularGenerator.operator L).domain)
    exact Eq.mpr (congrArg (fun z : HaarCircleL2 L =>
      z ∈ (AngularGenerator.operator L).domain) hmap)
        ((AngularGenerator.operator L).domain.add_mem hDf hDg)
  smul_mem' := by
    rintro c f ⟨hf, hDf⟩
    refine ⟨(AngularGenerator.operator L).domain.smul_mem c hf, ?_⟩
    have hmap := (AngularGenerator.operator L).toFun.map_smul c
      (⟨f, hf⟩ : (AngularGenerator.operator L).domain)
    exact Eq.mpr (congrArg (fun z : HaarCircleL2 L =>
      z ∈ (AngularGenerator.operator L).domain) hmap)
        ((AngularGenerator.operator L).domain.smul_mem c hDf)

theorem mem_squareDomain_iff (f : HaarCircleL2 L) :
    f ∈ squareDomain L ↔
      ∃ hf : f ∈ (AngularGenerator.operator L).domain,
        AngularGenerator.operator L ⟨f, hf⟩ ∈ (AngularGenerator.operator L).domain := Iff.rfl

def firstInput : squareDomain L →ₗ[ℂ] (AngularGenerator.operator L).domain :=
  Submodule.inclusion (fun _ hf => hf.choose)

@[simp] theorem firstInput_coe (f : squareDomain L) :
    (firstInput L f : HaarCircleL2 L) = (f : HaarCircleL2 L) := rfl

def secondInput : squareDomain L →ₗ[ℂ] (AngularGenerator.operator L).domain :=
  ((AngularGenerator.operator L).toFun.comp (firstInput L)).codRestrict
    (AngularGenerator.operator L).domain (fun f => f.property.choose_spec)

@[simp] theorem secondInput_coe (f : squareDomain L) :
    (secondInput L f : HaarCircleL2 L) = AngularGenerator.operator L (firstInput L f) := rfl

/-- Two successive applications of the original weak derivative. -/
def square : HaarCircleL2 L →ₗ.[ℂ] HaarCircleL2 L where
  domain := squareDomain L
  toFun := (AngularGenerator.operator L).toFun.comp (secondInput L)

theorem square_apply (f : (square L).domain) :
    square L f = AngularGenerator.operator L (secondInput L f) := rfl

theorem square_coefficients (f : (square L).domain) (n : ℤ) :
    inner ℂ (fourierLp (T := 2 * L) 2 n) (square L f) =
      (n : ℂ) ^ 2 * inner ℂ (fourierLp 2 n) (f : HaarCircleL2 L) := by
  rw [square_apply, AngularGenerator.coefficients, secondInput_coe L f,
    AngularGenerator.coefficients, firstInput_coe L f]
  ring

theorem int_square_le_fourth (n : ℤ) : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
  by_cases hn : n = 0
  · simp [hn]
  have hs : 1 ≤ (n : ℝ) ^ 2 := by
    rcases (show n ≤ -1 ∨ 1 ≤ n by omega) with h | h
    · have hr : (n : ℝ) ≤ -1 := by exact_mod_cast h
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
    · have hr : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  calc
    (n : ℝ) ^ 2 = 1 * (n : ℝ) ^ 2 := (one_mul _).symm
    _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = (n : ℝ) ^ 4 := by ring

theorem image_mem_domain_iff (f : (AngularGenerator.operator L).domain) :
    AngularGenerator.operator L f ∈ (AngularGenerator.operator L).domain ↔
      Summable (fun n : ℤ => (n : ℝ) ^ 4 *
        ‖inner ℂ (fourierLp (T := 2 * L) 2 n) (f : HaarCircleL2 L)‖ ^ 2) := by
  rw [AngularGenerator.domain_iff_weighted_fourier]
  have hfun :
      (fun n : ℤ => (n : ℝ) ^ 2 *
        ‖inner ℂ (fourierLp (T := 2 * L) 2 n) (AngularGenerator.operator L f)‖ ^ 2) =
      (fun n : ℤ => (n : ℝ) ^ 4 *
        ‖inner ℂ (fourierLp (T := 2 * L) 2 n) (f : HaarCircleL2 L)‖ ^ 2) := by
    funext n
    rw [AngularGenerator.coefficients, norm_mul, mul_pow, Complex.norm_intCast, sq_abs]
    ring
  rw [hfun]

/-- The fourth-power criterion is a consequence of the two actual domain conditions. -/
theorem square_domain_iff (f : HaarCircleL2 L) :
    f ∈ (square L).domain ↔
      Summable (fun n : ℤ => (n : ℝ) ^ 4 * ‖inner ℂ (fourierLp 2 n) f‖ ^ 2) := by
  change f ∈ squareDomain L ↔ _
  rw [mem_squareDomain_iff]
  constructor
  · rintro ⟨hf, hDf⟩
    exact (image_mem_domain_iff L ⟨f, hf⟩).mp hDf
  · intro h
    have hf : f ∈ (AngularGenerator.operator L).domain := by
      apply (AngularGenerator.domain_iff_weighted_fourier L f).mpr
      exact Summable.of_nonneg_of_le
        (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (fun n => mul_le_mul_of_nonneg_right (int_square_le_fourth n) (sq_nonneg _)) h
    exact ⟨hf, (image_mem_domain_iff L ⟨f, hf⟩).mpr h⟩

theorem square_formalAdjoint : (square L).IsFormalAdjoint (square L) := by
  intro f g
  calc
    inner ℂ (square L f) (g : HaarCircleL2 L) =
        inner ℂ (AngularGenerator.operator L (firstInput L f))
          (AngularGenerator.operator L (firstInput L g)) :=
      AngularGenerator.formalAdjoint L (secondInput L f) (firstInput L g)
    _ = inner ℂ (f : HaarCircleL2 L) (square L g) :=
      AngularGenerator.formalAdjoint L (firstInput L f) (secondInput L g)

theorem square_fourier_mem_domain (n : ℤ) :
    fourierLp (T := 2 * L) 2 n ∈ (square L).domain := by
  refine ⟨AngularGenerator.fourier_mem_domain L n, ?_⟩
  rw [AngularGenerator.operator_fourier]
  exact (AngularGenerator.operator L).domain.smul_mem (n : ℂ)
    (AngularGenerator.fourier_mem_domain L n)

theorem square_fourier (n : ℤ) :
    square L ⟨fourierLp 2 n, square_fourier_mem_domain L n⟩ =
      (((n : ℝ) ^ 2 : ℝ) : ℂ) • fourierLp 2 n := by
  apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
  intro k
  simp only [coe_fourierBasis, square_coefficients, inner_smul_right, haarFourier_inner]
  by_cases hkn : k = n
  · subst k
    simp only [ite_true, mul_one, Complex.ofReal_pow, Complex.ofReal_intCast]
  · simp only [hkn, ite_false, mul_zero]

theorem square_basis_mem_domain (n : ℤ) :
    fourierBasis (T := 2 * L) n ∈ (square L).domain := by
  simpa only [coe_fourierBasis] using square_fourier_mem_domain L n

theorem square_basis (n : ℤ) :
    square L ⟨fourierBasis n, square_basis_mem_domain L n⟩ =
      (((n : ℝ) ^ 2 : ℝ) : ℂ) • fourierBasis n := by
  simpa only [coe_fourierBasis] using square_fourier L n

theorem square_adjoint_domain_iff (f : HaarCircleL2 L) :
    f ∈ (square L).adjoint.domain ↔ f ∈ (square L).domain := by
  rw [EigenbasisClosure.adjoint_domain_iff_summable
    (fourierBasis (T := 2 * L)) (square L) (fun n : ℤ => (n : ℝ) ^ 2)
    (square_basis_mem_domain L) (square_basis L) (square_formalAdjoint L), square_domain_iff]
  simp only [coe_fourierBasis, ← pow_mul]

theorem square_selfAdjoint : IsSelfAdjoint (square L) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply le_antisymm
  · refine ⟨fun f hf => (square_adjoint_domain_iff L f).mp hf, ?_⟩
    intro f g hfg
    apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
    intro n
    rw [EigenbasisClosure.adjoint_coefficients (fourierBasis (T := 2 * L))
      (square L) (fun n : ℤ => (n : ℝ) ^ 2)
      (square_basis_mem_domain L) (square_basis L)]
    simp only [coe_fourierBasis, square_coefficients, hfg,
      Complex.ofReal_pow, Complex.ofReal_intCast]
  · exact EigenbasisClosure.le_adjoint (fourierBasis (T := 2 * L)) (square L)
      (square_basis_mem_domain L) (square_formalAdjoint L)

theorem reflection_mem_square_domain (f : (square L).domain) :
    haarCircleReflection L (f : HaarCircleL2 L) ∈ (square L).domain := by
  rw [square_domain_iff]
  have h := ((square_domain_iff L _).mp f.property).comp_injective
    (neg_injective : Function.Injective (fun n : ℤ => -n))
  have neg_fourth (x : ℝ) : (-x) ^ 4 = x ^ 4 := by ring
  simpa only [Function.comp_def, reflection_coefficients, Int.cast_neg, neg_fourth] using h

def reflectionDomain (f : (square L).domain) : (square L).domain :=
  ⟨haarCircleReflection L f, reflection_mem_square_domain L f⟩

theorem reflection_mem_square_domain_iff (f : HaarCircleL2 L) :
    haarCircleReflection L f ∈ (square L).domain ↔ f ∈ (square L).domain := by
  constructor
  · intro hf
    have h := reflection_mem_square_domain L ⟨haarCircleReflection L f, hf⟩
    simpa only [reflection_involution] using h
  · intro hf
    exact reflection_mem_square_domain L ⟨f, hf⟩

/-- Reversal preserves the square on its complete domain, although it reverses the first derivative. -/
theorem reflection_square (f : (square L).domain) :
    square L (reflectionDomain L f) = haarCircleReflection L (square L f) := by
  apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
  intro n
  simp only [coe_fourierBasis, square_coefficients, reflectionDomain,
    reflection_coefficients, Int.cast_neg, neg_sq]

theorem lift_nonnegative_coefficient (f : ComplexIntervalL2 0 L) (n : ℕ) :
    inner ℂ (fourierLp (T := 2 * L) 2 (n : ℤ)) (OrientedLift.lift L f) =
      inner ℂ (neumannCosineMode L n) f :=
  OrientedLift.unitary_coefficient L f n

theorem lift_negative_coefficient (f : ComplexIntervalL2 0 L) (n : ℤ) (hn : n < 0) :
    inner ℂ (fourierLp (T := 2 * L) 2 n) (OrientedLift.lift L f) = 0 :=
  (positiveChannel_mem_iff L _).mp (OrientedLift.unitary L f).property n hn

theorem lift_fourth_summable_iff (f : ComplexIntervalL2 0 L) :
    Summable (fun n : ℤ => (n : ℝ) ^ 4 *
      ‖inner ℂ (fourierLp 2 n) (OrientedLift.lift L f)‖ ^ 2) ↔
    Summable (fun n : ℕ => (n : ℝ) ^ 4 *
      ‖inner ℂ (neumannCosineMode L n) f‖ ^ 2) := by
  have hneg : Summable (fun n : ℕ => ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 4 *
      ‖inner ℂ (fourierLp (T := 2 * L) 2 (-((n : ℤ) + 1)))
        (OrientedLift.lift L f)‖ ^ 2) := by
    convert (summable_zero : Summable (fun _ : ℕ => (0 : ℝ))) using 1
    funext n
    rw [lift_negative_coefficient L f _ (by omega), norm_zero, zero_pow (by decide), mul_zero]
  constructor
  · intro h
    simpa only [Function.comp_def, lift_nonnegative_coefficient, Int.cast_natCast] using
      h.comp_injective (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℤ)))
  · intro h
    apply Summable.of_nat_of_neg_add_one
    · simpa only [lift_nonnegative_coefficient, Int.cast_natCast] using h
    · exact hneg

/-- Domain equality holds for every Hilbert vector, not only for eigenvectors. -/
theorem lift_mem_square_domain_iff (f : ComplexIntervalL2 0 L) :
    OrientedLift.lift L f ∈ (square L).domain ↔
      f ∈ (complexNeumannOperator hL.out).domain := by
  rw [square_domain_iff, lift_fourth_summable_iff,
    NeumannScaleTransport.normalized_domain_iff]

def positiveSquareDomain : Submodule ℂ (positiveChannel L) :=
  (square L).domain.comap (positiveChannel L).subtype

theorem unitary_mem_positiveSquareDomain_iff (f : ComplexIntervalL2 0 L) :
    OrientedLift.unitary L f ∈ positiveSquareDomain L ↔
      f ∈ (complexNeumannOperator hL.out).domain :=
  lift_mem_square_domain_iff L f

def domainEquiv :
    (complexNeumannOperator hL.out).domain ≃ₗ[ℂ] positiveSquareDomain L where
  toFun f := ⟨OrientedLift.unitary L f,
    (unitary_mem_positiveSquareDomain_iff L f).mpr f.property⟩
  invFun f := ⟨(OrientedLift.unitary L).symm (f : positiveChannel L),
    (unitary_mem_positiveSquareDomain_iff L _).mp (by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using f.property)⟩
  left_inv f := by
    apply Subtype.ext
    exact (OrientedLift.unitary L).symm_apply_apply f
  right_inv f := by
    apply Subtype.ext
    exact (OrientedLift.unitary L).apply_symm_apply f
  map_add' f g := by
    apply Subtype.ext
    exact map_add (OrientedLift.unitary L) (f : ComplexIntervalL2 0 L) (g : ComplexIntervalL2 0 L)
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (OrientedLift.unitary L) c (f : ComplexIntervalL2 0 L)

def liftedDomainVector (f : (complexNeumannOperator hL.out).domain) :
    (square L).domain :=
  ⟨OrientedLift.lift L f, (lift_mem_square_domain_iff L f).mpr f.property⟩

/-- The normalization is the first positive energy of the same interval operator. -/
theorem operator_intertwining (f : (complexNeumannOperator hL.out).domain) :
    square L (liftedDomainVector L f) =
      OrientedLift.lift L ((NeumannScaleTransport.energyUnit L : ℂ)⁻¹ •
        complexNeumannOperator hL.out f) := by
  apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
  intro n
  simp only [coe_fourierBasis, square_coefficients]
  change (n : ℂ) ^ 2 * inner ℂ (fourierLp (T := 2 * L) 2 n)
    (OrientedLift.lift L (f : ComplexIntervalL2 0 L)) = _
  cases n with
  | ofNat n =>
      change ((n : ℤ) : ℂ) ^ 2 * inner ℂ (fourierLp (T := 2 * L) 2 (n : ℤ))
        (OrientedLift.lift L (f : ComplexIntervalL2 0 L)) =
          inner ℂ (fourierLp (T := 2 * L) 2 (n : ℤ))
            (OrientedLift.lift L ((NeumannScaleTransport.energyUnit L : ℂ)⁻¹ •
              complexNeumannOperator hL.out f))
      rw [lift_nonnegative_coefficient, lift_nonnegative_coefficient,
        NeumannScaleTransport.normalized_operator_coefficient]
      simp only [Int.cast_natCast, Complex.ofReal_natCast]
  | negSucc n =>
      rw [lift_negative_coefficient L _ _ (by omega),
        lift_negative_coefficient L _ _ (by omega), mul_zero]

end GeneratedFoundations.Spectral.AngularSquareDomain
