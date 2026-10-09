module

public import GeneratedFoundations.Operations.HermiteOscillator
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The strongly continuous phase flow of the Gaussian oscillator

The complete family of generated Hermite functions supplies the coefficient
representation of the original Lebesgue Hilbert space. Unit-modulus spectral
multipliers therefore define operators on that space. Square-summable
domination proves strong continuity and identifies all differentiable vectors
with the domain of the previously constructed self-adjoint graph closure.
The parameter is a phase parameter; no additional time variable is postulated.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology lp LinearPMap
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteOscillator
open GeneratedFoundations.Operations.HermiteCompleteness

namespace GeneratedFoundations.Operations.HermitePhaseFlow

abbrev Sequence := ℓ²(ℕ, ℂ)

def phase (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp ((-Complex.I * (eigenvalue n : ℂ)) * (t : ℂ))

theorem phase_eq (t : ℝ) (n : ℕ) :
    phase t n = Complex.exp (Complex.I * ((-t * eigenvalue n : ℝ) : ℂ)) := by
  unfold phase
  congr 1
  push_cast
  ring

@[simp] theorem phase_norm (t : ℝ) (n : ℕ) : ‖phase t n‖ = 1 := by
  rw [phase_eq]
  exact Complex.norm_exp_I_mul_ofReal _

@[simp] theorem phase_zero (n : ℕ) : phase 0 n = 1 := by simp [phase]

theorem phase_add (s t : ℝ) (n : ℕ) : phase (s + t) n = phase s n * phase t n := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem phase_neg_mul (t : ℝ) (n : ℕ) : phase (-t) n * phase t n = 1 := by
  rw [← phase_add, neg_add_cancel, phase_zero]

theorem phase_mul_neg (t : ℝ) (n : ℕ) : phase t n * phase (-t) n = 1 := by
  rw [← phase_add, add_neg_cancel, phase_zero]

theorem phase_hasDerivAt (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s : ℝ => phase s n)
      ((-Complex.I * (eigenvalue n : ℂ)) * phase t n) t := by
  have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := t))
  simpa only [phase, mul_one, one_mul, mul_comm] using
    (hr.const_mul (-Complex.I * (eigenvalue n : ℂ))).cexp

theorem phase_continuous (n : ℕ) : Continuous (fun t : ℝ => phase t n) :=
  continuous_iff_continuousAt.mpr fun t => (phase_hasDerivAt t n).continuousAt

theorem phase_sub_one_le (t : ℝ) (n : ℕ) :
    ‖phase t n - 1‖ ≤ |t| * eigenvalue n := by
  have hn : 0 ≤ eigenvalue n := by unfold eigenvalue; positivity
  rw [phase_eq]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (by
    simp [Real.norm_eq_abs, abs_of_nonneg hn])

theorem phase_two_pi (n : ℕ) : phase (2 * Real.pi) n = -1 := by
  have h : (-Complex.I * (eigenvalue n : ℂ)) * ((2 * Real.pi : ℝ) : ℂ) =
      -((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) + -(Real.pi * Complex.I) := by
    simp only [eigenvalue, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_mul]
    ring
  rw [phase, h, Complex.exp_add, Complex.exp_neg,
    Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_neg_pi_mul_I]
  norm_num

def sequenceMap (t : ℝ) (v : Sequence) : Sequence :=
  ⟨fun n => phase t n * v n,
    (lp.memℓp v).mono' (by intro n; simp only [norm_mul, phase_norm, one_mul, le_refl])⟩

@[simp] theorem sequenceMap_apply (t : ℝ) (v : Sequence) (n : ℕ) :
    sequenceMap t v n = phase t n * v n := rfl

def sequenceIsometry (t : ℝ) : Sequence ≃ₗᵢ[ℂ] Sequence where
  toFun := sequenceMap t
  invFun := sequenceMap (-t)
  left_inv v := by
    apply lp.ext
    funext n
    simp only [sequenceMap_apply, ← mul_assoc, phase_neg_mul, one_mul]
  right_inv v := by
    apply lp.ext
    funext n
    simp only [sequenceMap_apply, ← mul_assoc, phase_mul_neg, one_mul]
  map_add' v w := by
    apply lp.ext
    funext n
    change phase t n * (v n + w n) = phase t n * v n + phase t n * w n
    ring
  map_smul' c v := by
    apply lp.ext
    funext n
    simp [sequenceMap, mul_left_comm]
  norm_map' v := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num) (by intro n; simp)
    · exact lp.norm_mono (by norm_num) (by intro n; simp)

@[simp] theorem sequenceIsometry_apply (t : ℝ) (v : Sequence) (n : ℕ) :
    sequenceIsometry t v n = phase t n * v n := rfl

/-- The spectral multiplier is transported through the proved genuine Hermite basis. -/
def flow {b : ℝ} (hb : 0 < b) (t : ℝ) : ComplexL2 ≃ₗᵢ[ℂ] ComplexL2 :=
  ((coefficients hb).trans (sequenceIsometry t)).trans (coefficients hb).symm

theorem coefficients_flow {b : ℝ} (hb : 0 < b) (t : ℝ) (F : ComplexL2) :
    coefficients hb (flow hb t F) = sequenceIsometry t (coefficients hb F) := by
  simp [flow]

theorem flow_coefficient {b : ℝ} (hb : 0 < b) (t : ℝ) (F : ComplexL2) (n : ℕ) :
    coefficients hb (flow hb t F) n = phase t n * coefficients hb F n := by
  rw [coefficients_flow]
  rfl

theorem flow_inner {b : ℝ} (hb : 0 < b) (t : ℝ) (F : ComplexL2) (n : ℕ) :
    inner ℂ (HermiteFamily.state hb n) (flow hb t F) =
      phase t n * inner ℂ (HermiteFamily.state hb n) F := by
  simpa only [coefficients_apply] using flow_coefficient hb t F n

@[simp] theorem flow_zero {b : ℝ} (hb : 0 < b) (F : ComplexL2) : flow hb 0 F = F := by
  apply (coefficients hb).injective
  apply lp.ext
  funext n
  simp only [flow_coefficient, phase_zero, one_mul]

theorem flow_add {b : ℝ} (hb : 0 < b) (s t : ℝ) (F : ComplexL2) :
    flow hb (s + t) F = flow hb s (flow hb t F) := by
  apply (coefficients hb).injective
  apply lp.ext
  funext n
  simp only [flow_coefficient, phase_add, mul_assoc]

theorem flow_norm {b : ℝ} (hb : 0 < b) (t : ℝ) (F : ComplexL2) :
    ‖flow hb t F‖ = ‖F‖ := (flow hb t).norm_map F

/-- The central sign is an identity on the entire original Hilbert space. -/
theorem flow_two_pi {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    flow hb (2 * Real.pi) F = -F := by
  apply (coefficients hb).injective
  apply lp.ext
  funext n
  simp only [flow_coefficient, phase_two_pi, neg_one_mul, map_neg, lp.coeFn_neg,
    Pi.neg_apply]

theorem flow_four_pi {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    flow hb (4 * Real.pi) F = F := by
  rw [show 4 * Real.pi = 2 * Real.pi + 2 * Real.pi by ring, flow_add,
    flow_two_pi, flow_two_pi, neg_neg]

private theorem sequence_norm_sq (v : Sequence) : ‖v‖ ^ 2 = ∑' n, ‖v n‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) v

private theorem sequence_summable (v : Sequence) : Summable (fun n => ‖v n‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)

private theorem sequence_tendsto_zero {α : Type*} {l : Filter α} (v : α → Sequence)
    (bound : ℕ → ℝ) (hsum : Summable bound)
    (hpoint : ∀ n, Tendsto (fun a => v a n) l (𝓝 0))
    (hbound : ∀ᶠ a in l, ∀ n, ‖v a n‖ ^ 2 ≤ bound n) : Tendsto v l (𝓝 0) := by
  have hsq : Tendsto (fun a => ‖v a‖ ^ 2) l (𝓝 0) := by
    simp_rw [sequence_norm_sq]
    have h := tendsto_tsum_of_dominated_convergence
      (f := fun a n => ‖v a n‖ ^ 2) (g := fun _ => (0 : ℝ)) hsum
      (fun n => by simpa using (hpoint n).norm.pow 2)
      (hbound.mono (fun a ha n => by simpa only [Real.norm_eq_abs, abs_sq] using ha n))
    simpa only [tsum_zero] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

theorem sequence_stronglyContinuous (v : Sequence) :
    Continuous (fun t : ℝ => sequenceIsometry t v) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero _ (fun n => 4 * ‖v n‖ ^ 2)
    ((sequence_summable v).mul_left 4)
  · intro n
    simpa using (((phase_continuous n).continuousAt (x := s)).mul_const (v n)).tendsto.sub_const
      (phase s n * v n)
  · apply Eventually.of_forall
    intro t n
    have h : ‖phase t n * v n - phase s n * v n‖ ≤ 2 * ‖v n‖ := by
      calc
        _ ≤ ‖phase t n * v n‖ + ‖phase s n * v n‖ := norm_sub_le _ _
        _ = 2 * ‖v n‖ := by simp [two_mul]
    change ‖phase t n * v n - phase s n * v n‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (phase t n * v n - phase s n * v n), norm_nonneg (v n)]

/-- Continuity holds for every Hilbert vector, with no operator-domain restriction. -/
theorem stronglyContinuous {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    Continuous (fun t : ℝ => flow hb t F) := by
  exact (coefficients hb).symm.continuous.comp (sequence_stronglyContinuous (coefficients hb F))

theorem flow_mem_domain_iff {b : ℝ} (hb : 0 < b) (t : ℝ) (F : ComplexL2) :
    flow hb t F ∈ (hamiltonian b).domain ↔ F ∈ (hamiltonian b).domain := by
  rw [hamiltonian_domain_iff hb, hamiltonian_domain_iff hb]
  simp only [flow_inner, norm_mul, phase_norm, one_mul]

theorem hamiltonian_flow {b : ℝ} (hb : 0 < b) (t : ℝ)
    (F : (hamiltonian b).domain) :
    hamiltonian b ⟨flow hb t F, (flow_mem_domain_iff hb t F).mpr F.property⟩ =
      flow hb t (hamiltonian b F) := by
  apply eq_of_coefficients_eq hb
  intro n
  rw [hamiltonian_coefficients, flow_inner, flow_inner, hamiltonian_coefficients]
  ring

private theorem sequence_hasDerivAt_zero (v w : Sequence)
    (hw : ∀ n, w n = (-Complex.I * (eigenvalue n : ℂ)) * v n) :
    HasDerivAt (fun t : ℝ => sequenceIsometry t v) w 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_sub_nhds_zero_iff.mp
  apply sequence_tendsto_zero _ (fun n => 4 * ‖w n‖ ^ 2)
    ((sequence_summable w).mul_left 4)
  · intro n
    have h := ((phase_hasDerivAt 0 n).mul_const (v n)).tendsto_slope_zero
    simpa only [phase_zero, one_mul, mul_one, zero_add, sequenceIsometry_apply,
      lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, hw n, sub_self] using
      h.sub_const ((-Complex.I * (eigenvalue n : ℂ)) * v n)
  · apply Eventually.of_forall
    intro t n
    have hn : 0 ≤ eigenvalue n := by unfold eigenvalue; positivity
    have hwn : ‖w n‖ = eigenvalue n * ‖v n‖ := by
      rw [hw n]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
    have hs : ‖t⁻¹ • (phase t n * v n - v n)‖ ≤ ‖w n‖ := by
      by_cases ht : t = 0
      · simp [ht]
      · rw [norm_smul, norm_inv, Real.norm_eq_abs, ← sub_one_mul, norm_mul, hwn]
        calc
          _ ≤ |t|⁻¹ * ((|t| * eigenvalue n) * ‖v n‖) := by
            gcongr
            exact phase_sub_one_le t n
          _ = eigenvalue n * ‖v n‖ := by field_simp [ht]
    have he : ‖t⁻¹ • (phase t n * v n - v n) - w n‖ ≤ 2 * ‖w n‖ :=
      (norm_sub_le _ _).trans (by linarith)
    change ‖t⁻¹ • (phase (0 + t) n * v n - phase 0 n * v n) - w n‖ ^ 2 ≤ _
    simp only [zero_add, phase_zero, one_mul]
    nlinarith [norm_nonneg (t⁻¹ • (phase t n * v n - v n) - w n), norm_nonneg (w n)]

/-- Every vector in the full closed domain has the derivative prescribed by that operator. -/
theorem hasDerivAt_zero {b : ℝ} (hb : 0 < b) (F : (hamiltonian b).domain) :
    HasDerivAt (fun t : ℝ => flow hb t (F : ComplexL2))
      ((-Complex.I) • hamiltonian b F) 0 := by
  have h := sequence_hasDerivAt_zero (coefficients hb (F : ComplexL2))
    (coefficients hb ((-Complex.I) • hamiltonian b F)) (by
      intro n
      simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, coefficients_apply,
        hamiltonian_coefficients, eigenvalue, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
      ring)
  let L : Sequence →L[ℝ] ComplexL2 :=
    (coefficients hb).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have h' := L.hasFDerivAt.comp_hasDerivAt 0 h
  change HasDerivAt (fun t => (coefficients hb).symm
    (sequenceIsometry t (coefficients hb (F : ComplexL2))))
    ((coefficients hb).symm (coefficients hb ((-Complex.I) • hamiltonian b F))) 0 at h'
  simpa [flow] using h'

/-- Necessity uses all continuous coordinate functionals, not a finite spectral test. -/
theorem mem_domain_of_hasDerivAt {b : ℝ} (hb : 0 < b) (F G : ComplexL2)
    (h : HasDerivAt (fun t : ℝ => flow hb t F) G 0) : F ∈ (hamiltonian b).domain := by
  have hc (n : ℕ) : coefficients hb G n =
      (-Complex.I * (eigenvalue n : ℂ)) * coefficients hb F n := by
    let L : ComplexL2 →L[ℝ] ℂ :=
      ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp
        (coefficients hb).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
    have hL := L.hasFDerivAt.comp_hasDerivAt 0 h
    have hphase := (phase_hasDerivAt 0 n).mul_const (coefficients hb F n)
    have hL' : HasDerivAt (fun t : ℝ => phase t n * coefficients hb F n)
        (coefficients hb G n) 0 := by
      change HasDerivAt (fun t => coefficients hb (flow hb t F) n)
        (coefficients hb G n) 0 at hL
      simpa only [flow_coefficient] using hL
    exact hL'.unique (by simpa only [phase_zero, mul_one] using hphase)
  rw [hamiltonian_domain_iff hb]
  convert sequence_summable (coefficients hb G) using 1
  funext n
  rw [hc n]
  have hn : 0 ≤ eigenvalue n := by unfold eigenvalue; positivity
  have hnorm : ‖(-Complex.I * (eigenvalue n : ℂ)) * coefficients hb F n‖ =
      eigenvalue n * ‖coefficients hb F n‖ := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  have hpow := congrArg (fun x : ℝ => x ^ 2) hnorm.symm
  rw [mul_pow] at hpow
  simpa only [eigenvalue, coefficients_apply] using hpow

/-- The infinitesimal generator has exactly the already established closed domain. -/
theorem differentiableAt_zero_iff {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    DifferentiableAt ℝ (fun t : ℝ => flow hb t F) 0 ↔ F ∈ (hamiltonian b).domain := by
  constructor
  · intro h
    exact mem_domain_of_hasDerivAt hb F _ h.hasDerivAt
  · intro h
    exact (hasDerivAt_zero hb ⟨F, h⟩).differentiableAt

theorem hasDerivAt_phase {b : ℝ} (hb : 0 < b) (F : (hamiltonian b).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow hb s (F : ComplexL2))
      ((-Complex.I) • flow hb t (hamiltonian b F)) t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have h := (hasDerivAt_zero hb F).tendsto_slope_zero
  have hc := (flow hb t).continuous.continuousAt.tendsto.comp h
  have hs (r : ℝ) (V : ComplexL2) : flow hb t (r • V) = r • flow hb t V :=
    LinearMapClass.map_smul_of_tower (flow hb t) r V
  simpa only [Function.comp_def, zero_add, flow_zero, map_smul, hs,
    map_sub, ← flow_add] using hc

end GeneratedFoundations.Operations.HermitePhaseFlow
