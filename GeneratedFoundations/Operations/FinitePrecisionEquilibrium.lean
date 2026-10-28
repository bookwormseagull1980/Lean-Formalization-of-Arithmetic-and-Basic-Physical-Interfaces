module

public import GeneratedFoundations.Operations.FinitePrecisionGaussian

/-!
# The state fixed by the original Gaussian equilibrium update

The independent increment in the existing equilibrium composition has
covariance `(1-r^2) C`, where `C` is the original source covariance.
This module computes its action on the entire finite Gaussian law.
It also solves the covariance fixed-point equation with that increment
held fixed. Each fixed update has its prescribed covariance as its unique
stationary covariance; invariance of this family of updates does not
select a value of an external radius parameter in that covariance.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators NNReal

namespace GeneratedFoundations.Operations.FinitePrecisionEquilibrium

open FinitePrecisionGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scaleMap (r : ℝ) : Space ι →L[ℝ] Space ι :=
  r • ContinuousLinearMap.id ℝ (Space ι)

def scaledLaw (p : ι → ℝ) (r : ℝ) : Measure (Space ι) :=
  (law p).map (scaleMap r)

instance (p : ι → ℝ) (r : ℝ) : IsGaussian (scaledLaw p r) := by
  unfold scaledLaw
  infer_instance

/-- Distribution of the sum of independently retained and refreshed source
coefficients. Both terms come from the same original Gaussian law. -/
def compositionLaw (p : ι → ℝ) (r s : ℝ) : Measure (Space ι) :=
  scaledLaw p r ∗ scaledLaw p s

instance (p : ι → ℝ) (r s : ℝ) : IsGaussian (compositionLaw p r s) := by
  unfold compositionLaw
  infer_instance

private theorem centred_dual (p : ι → ℝ) (L : StrongDual ℝ (Space ι)) :
    (∫ x, L x ∂law p) = 0 := by
  rw [L.integral_comp_id_comm IsGaussian.integrable_id, mean_zero, map_zero]

private theorem scaled_charFun (p : ι → ℝ) (r : ℝ)
    (L : StrongDual ℝ (Space ι)) :
    charFunDual (scaledLaw p r) L =
      Complex.exp (-((r ^ 2 * Var[L; law p] : ℝ) : ℂ) / 2) := by
  have he : L.comp (scaleMap r) = r • L := by
    ext x
    simp [scaleMap]
  have hm : (∫ x, ((r • L) x : ℂ) ∂law p) = 0 := by
    rw [integral_complex_ofReal]
    change ((∫ x, r * L x ∂law p : ℝ) : ℂ) = 0
    rw [integral_const_mul, centred_dual]
    simp
  have hv : Var[⇑(r • L); law p] = r ^ 2 * Var[L; law p] := by
    change Var[fun x => r * L x; law p] = _
    exact variance_const_mul r L (law p)
  rw [scaledLaw, charFunDual_map, he, IsGaussian.charFunDual_eq]
  rw [hm, hv]
  simp only [zero_mul, zero_sub]
  congr 1
  ring

/-- Exact equality of joint measures, rather than agreement of just their
first two moments or of a selected radial observable. -/
theorem composition_preserves_law (p : ι → ℝ) {r s : ℝ}
    (hrs : r ^ 2 + s ^ 2 = 1) : compositionLaw p r s = law p := by
  apply Measure.ext_of_charFunDual
  ext L
  unfold compositionLaw
  rw [charFunDual_conv, scaled_charFun, scaled_charFun,
    ← Complex.exp_add, IsGaussian.charFunDual_eq, integral_complex_ofReal, centred_dual]
  simp only [Complex.ofReal_zero, zero_mul, zero_sub]
  congr 1
  have he : r ^ 2 * Var[L; law p] + s ^ 2 * Var[L; law p] = Var[L; law p] := by
    rw [← add_mul, hrs, one_mul]
  have hec := congrArg (fun x : ℝ => (x : ℂ)) he
  push_cast at hec ⊢
  linear_combination -hec / 2

/-- The source's prescribed Mehler composition at equilibrium. -/
def mehlerLaw (p : ι → ℝ) (omega time : ℝ) : Measure (Space ι) :=
  compositionLaw p (Real.exp (-omega * time))
    (Real.sqrt (1 - Real.exp (-omega * time) ^ 2))

theorem mehler_preserves_law (p : ι → ℝ) {omega time : ℝ}
    (homega : 0 ≤ omega) (htime : 0 ≤ time) : mehlerLaw p omega time = law p := by
  apply composition_preserves_law
  have hr0 := Real.exp_pos (-omega * time)
  have hr1 : Real.exp (-omega * time) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hs : 0 ≤ 1 - Real.exp (-omega * time) ^ 2 := by nlinarith
  rw [Real.sq_sqrt hs]
  ring

/-! ## Different restoring rates on the original spectral coordinates -/

/-- The product representation is deduced from the original joint source
law and its computed independent coordinates. -/
theorem law_eq_product {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    (Measure.pi (fun i => GaussianPrecisionKL.law (p i))).map (toLp 2) = law p := by
  have hi := (coordinates_independent hp).map_fun_eq_pi_map (fun i => by fun_prop)
  have he : (law p).map (fun x : Space ι => fun i => x i) =
      Measure.pi (fun i => GaussianPrecisionKL.law (p i)) := by
    rw [hi]
    congr 1
    funext i
    exact (coordinate_marginal hp i).map_eq
  rw [← he, Measure.map_map (by fun_prop) (by fun_prop)]
  have hid : (toLp 2) ∘ (fun x : Space ι => fun i => x i) = id := by
    funext x
    rfl
  rw [hid, Measure.map_id]

def scalarCompositionLaw (p r s : ℝ) : Measure ℝ :=
  (GaussianPrecisionKL.law p).map (r * ·) ∗
    (GaussianPrecisionKL.law p).map (s * ·)

theorem scalar_composition_preserves_law (p : ℝ) {r s : ℝ}
    (hrs : r ^ 2 + s ^ 2 = 1) : scalarCompositionLaw p r s = GaussianPrecisionKL.law p := by
  have hv : NNReal.mk (r ^ 2) (sq_nonneg r) * GaussianPrecisionKL.variance p +
      NNReal.mk (s ^ 2) (sq_nonneg s) * GaussianPrecisionKL.variance p =
      GaussianPrecisionKL.variance p := by
    apply NNReal.coe_injective
    change r ^ 2 * (GaussianPrecisionKL.variance p : ℝ) +
      s ^ 2 * (GaussianPrecisionKL.variance p : ℝ) = _
    rw [← add_mul, hrs, one_mul]
  unfold scalarCompositionLaw GaussianPrecisionKL.law
  rw [gaussianReal_map_const_mul, gaussianReal_map_const_mul,
    gaussianReal_conv_gaussianReal, hv]
  simp

/-- Coordinate form of the joint update in the original independent
spectral coefficients. The rates may be different on every coordinate. -/
def coordinateCompositionLaw (p r s : ι → ℝ) : Measure (Space ι) :=
  (Measure.pi (fun i => scalarCompositionLaw (p i) (r i) (s i))).map (toLp 2)

theorem coordinate_composition_preserves_law {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (r s : ι → ℝ) (hrs : ∀ i, r i ^ 2 + s i ^ 2 = 1) :
    coordinateCompositionLaw p r s = law p := by
  unfold coordinateCompositionLaw
  have he : (fun i => scalarCompositionLaw (p i) (r i) (s i)) =
      (fun i => GaussianPrecisionKL.law (p i)) := by
    funext i
    exact scalar_composition_preserves_law (p i) (hrs i)
  rw [he]
  exact law_eq_product hp

def coordinateMehlerLaw (p omega : ι → ℝ) (time : ℝ) : Measure (Space ι) :=
  coordinateCompositionLaw p (fun i => Real.exp (-omega i * time))
    (fun i => Real.sqrt (1 - Real.exp (-omega i * time) ^ 2))

theorem coordinate_mehler_preserves_law {p : ι → ℝ} (hp : ∀ i, 0 < p i)
    (omega : ι → ℝ) {time : ℝ} (homega : ∀ i, 0 ≤ omega i) (htime : 0 ≤ time) :
    coordinateMehlerLaw p omega time = law p := by
  apply coordinate_composition_preserves_law hp
  intro i
  have hr0 := Real.exp_pos (-omega i * time)
  have hr1 : Real.exp (-omega i * time) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [homega i])
  have hs : 0 ≤ 1 - Real.exp (-omega i * time) ^ 2 := by nlinarith
  rw [Real.sq_sqrt hs]
  ring

/-- Covariance update with the original innovation covariance held fixed. -/
def covarianceUpdate (p : ι → ℝ) (r : ℝ) (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  r ^ 2 • C + (1 - r ^ 2) • covarianceMatrix p

omit [Fintype ι] in
theorem covariance_fixed_iff (p : ι → ℝ) {r : ℝ} (hr : r ^ 2 ≠ 1)
    (C : Matrix ι ι ℝ) : covarianceUpdate p r C = C ↔ C = covarianceMatrix p := by
  constructor
  · intro h
    ext i j
    have he := congrFun (congrFun h i) j
    change r ^ 2 * C i j + (1 - r ^ 2) * covarianceMatrix p i j = C i j at he
    have hz : (r ^ 2 - 1) * (C i j - covarianceMatrix p i j) = 0 := by
      nlinarith [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hr))
  · rintro rfl
    ext i j
    simp only [covarianceUpdate, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

end GeneratedFoundations.Operations.FinitePrecisionEquilibrium
