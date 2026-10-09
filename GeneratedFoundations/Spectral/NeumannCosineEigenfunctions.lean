module

public import GeneratedFoundations.Spectral.ComplexNeumannDomain
public import GeneratedFoundations.Spectral.NeumannCosineBasis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Cosine eigenfunctions of the Neumann differential operator

The cosine modes are placed in the existing Sobolev domain by explicit
absolutely continuous representatives and their endpoint derivative traces.
Their eigenvalue equation is then proved for the actual negative second
derivative. Smoothness is used only for these particular representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

private theorem complexH1_of_contDiff_real {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hder : ∀ x, HasDerivAt f (g x) x) :
    HasComplexH1Derivative a b (fun x => (f x : ℂ)) (fun x => (g x : ℂ)) := by
  refine ⟨Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
    hf.contDiffOn.absolutelyContinuousOnInterval,
    (absolutelyContinuous_memLp hg.contDiffOn.absolutelyContinuousOnInterval).ofReal, ?_⟩
  exact ae_of_all _ fun x => (hder x).ofReal_comp

/-- The explicit cosine and its two weak derivatives on a bounded interval. -/
def cosineH2Representative (a b k : ℝ) : ComplexH2Representative a b where
  value := fun x => (Real.cos (k * x) : ℂ)
  first := fun x => ((-k * Real.sin (k * x) : ℝ) : ℂ)
  second := fun x => ((-(k ^ 2) * Real.cos (k * x) : ℝ) : ℂ)
  firstDerivative := by
    apply complexH1_of_contDiff_real
    · exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
    · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))
    · intro x
      convert (Real.hasDerivAt_cos (k * x)).comp x ((hasDerivAt_id x).const_mul k) using 1 <;>
        first | rfl | ring
  secondDerivative := by
    apply complexH1_of_contDiff_real
    · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id))
    · exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
    · intro x
      convert ((Real.hasDerivAt_sin (k * x)).comp x
        ((hasDerivAt_id x).const_mul k)).const_mul (-k) using 1 <;> first | rfl | ring

variable (L : ℝ) [hL : Fact (0 < L)]

def neumannEigenvalue (n : ℕ) : ℝ := ((n : ℝ) * Real.pi / L) ^ 2

omit hL in
@[simp] theorem neumannEigenvalue_zero : neumannEigenvalue L 0 = 0 := by
  simp [neumannEigenvalue]

omit hL in
theorem neumannEigenvalue_nonneg (n : ℕ) : 0 ≤ neumannEigenvalue L n :=
  sq_nonneg _

theorem neumannEigenvalue_pos {n : ℕ} (hn : 0 < n) : 0 < neumannEigenvalue L n := by
  apply sq_pos_of_pos
  exact div_pos (mul_pos (by exact_mod_cast hn) Real.pi_pos) hL.out

/-- Representatives of the normalized interval modes, including the constant mode. -/
def neumannCosineRepresentative : ℕ → ComplexH2Representative 0 L
  | 0 => ComplexH2Representative.constant 0 L (Real.sqrt L : ℂ)⁻¹
  | n + 1 => (cosineH2Representative 0 L ((n + 1 : ℕ) * Real.pi / L)).smul
      ((Real.sqrt L : ℂ)⁻¹ * (Real.sqrt 2 : ℂ))

theorem neumannCosineRepresentative_neumann (n : ℕ) :
    IsComplexNeumann (neumannCosineRepresentative L n) := by
  cases n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n =>
      have hfreq : ((n + 1 : ℕ) : ℝ) * Real.pi / L * L = (n + 1 : ℕ) * Real.pi :=
        div_mul_cancel₀ _ hL.out.ne'
      constructor
      · simp [neumannCosineRepresentative, ComplexH2Representative.smul,
          cosineH2Representative]
      · change ((Real.sqrt L : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)) *
          ((-((n + 1 : ℕ) * Real.pi / L) *
            Real.sin (((n + 1 : ℕ) * Real.pi / L) * L) : ℝ) : ℂ) = 0
        rw [hfreq, Real.sin_nat_mul_pi]
        simp

theorem neumannCosineRepresentative_toL2 (n : ℕ) :
    (neumannCosineRepresentative L n).toL2 = neumannCosineMode L n := by
  apply Lp.ext
  have hrep : ((neumannCosineRepresentative L n).toL2 : ℝ → ℂ) =ᵐ[intervalMeasure 0 L]
      (neumannCosineRepresentative L n).value :=
    (neumannCosineRepresentative L n).firstDerivative.value_memLp.coeFn_toLp
  cases n with
  | zero =>
      filter_upwards [hrep, neumannCosineMode_zero_coe L] with x hx hm
      exact hx.trans hm.symm
  | succ n =>
      filter_upwards [hrep, neumannCosineMode_succ_coe L n] with x hx hm
      rw [hx, hm]
      change _ * (Real.cos (_ / L * x) : ℂ) = _ * (Real.cos (_ * x / L) : ℂ)
      have harg : ((n + 1 : ℕ) : ℝ) * Real.pi / L * x =
          (n + 1 : ℕ) * Real.pi * x / L := by ring
      rw [harg]

theorem neumannCosineRepresentative_secondL2 (n : ℕ) :
    (neumannCosineRepresentative L n).secondL2 =
      -(neumannEigenvalue L n : ℂ) • neumannCosineMode L n := by
  rw [← neumannCosineRepresentative_toL2 L n]
  apply Lp.ext
  have hs : ((neumannCosineRepresentative L n).secondL2 : ℝ → ℂ) =ᵐ[intervalMeasure 0 L]
      (neumannCosineRepresentative L n).second :=
    (neumannCosineRepresentative L n).secondDerivative.derivative_memLp.coeFn_toLp
  have hv : ((neumannCosineRepresentative L n).toL2 : ℝ → ℂ) =ᵐ[intervalMeasure 0 L]
      (neumannCosineRepresentative L n).value :=
    (neumannCosineRepresentative L n).firstDerivative.value_memLp.coeFn_toLp
  filter_upwards [hs, hv,
    Lp.coeFn_smul (-(neumannEigenvalue L n : ℂ))
      (neumannCosineRepresentative L n).toL2] with x hsecond hvalue hsmul
  rw [hsecond, hsmul]
  change (neumannCosineRepresentative L n).second x =
    -(neumannEigenvalue L n : ℂ) * (neumannCosineRepresentative L n).toL2 x
  rw [hvalue]
  cases n with
  | zero => simp [neumannCosineRepresentative, neumannEigenvalue,
      ComplexH2Representative.constant]
  | succ n =>
      simp only [neumannCosineRepresentative, ComplexH2Representative.smul,
        cosineH2Representative, neumannEigenvalue, Complex.ofReal_mul,
        Complex.ofReal_neg, Complex.ofReal_pow]
      ring

theorem neumannCosineMode_mem_domain (n : ℕ) :
    neumannCosineMode L n ∈ (complexNeumannOperator hL.out).domain :=
  ⟨neumannCosineRepresentative L n, neumannCosineRepresentative_neumann L n,
    neumannCosineRepresentative_toL2 L n⟩

theorem complexNeumannOperator_cosine (n : ℕ) :
    complexNeumannOperator hL.out
      ⟨neumannCosineMode L n, neumannCosineMode_mem_domain L n⟩ =
        (neumannEigenvalue L n : ℂ) • neumannCosineMode L n := by
  have hinput : (⟨neumannCosineMode L n, neumannCosineMode_mem_domain L n⟩ :
      (complexNeumannOperator hL.out).domain) =
      ⟨(neumannCosineRepresentative L n).toL2,
        neumannCosineRepresentative L n, neumannCosineRepresentative_neumann L n, rfl⟩ :=
    Subtype.ext (neumannCosineRepresentative_toL2 L n).symm
  rw [hinput]
  calc
    _ = -(neumannCosineRepresentative L n).secondL2 :=
      complexNeumannOperator_on_representative hL.out _
        (neumannCosineRepresentative_neumann L n)
    _ = _ := by rw [neumannCosineRepresentative_secondL2]; simp

theorem neumannCosineBasis_mem_domain (n : ℕ) :
    neumannCosineBasis L n ∈ (complexNeumannOperator hL.out).domain := by
  rw [coe_neumannCosineBasis]
  exact neumannCosineMode_mem_domain L n

theorem complexNeumannOperator_cosineBasis (n : ℕ) :
    complexNeumannOperator hL.out
      ⟨neumannCosineBasis L n, neumannCosineBasis_mem_domain L n⟩ =
        (neumannEigenvalue L n : ℂ) • neumannCosineBasis L n := by
  simpa only [coe_neumannCosineBasis] using complexNeumannOperator_cosine L n

end GeneratedFoundations.Spectral
