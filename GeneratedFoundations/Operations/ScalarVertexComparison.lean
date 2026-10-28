module

public import GeneratedFoundations.Operations.FiniteMatrixGaussianVariation
public import GeneratedFoundations.Operations.PrecisionMixedResponse
public import Mathlib.Tactic

/-!
# Comparison of an unchanged vertex in a scalar precision block

The source coefficient space and its actual quadratic insertion are kept
fixed. A scalar mass shift changes the full Gaussian precision from `A I`
to `(A+b) I`. The relative Fisher form is independent of the particular
vertex, including its mixed matrix entries. A nonzero comparison requires
a nonzero observable vertex; a zero vertex supplies no normalized channel.

This block calculation does not identify a tensor insertion on any given
physical branch. In particular it does not turn a vanishing internal
gradient insertion into a nonzero event insertion, and it does not apply
unchanged to a vertex mixing blocks with unequal kinetic precisions.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Operations.ScalarVertexComparison

open FiniteMatrixGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def precision (p : ℝ) : Matrix ι ι ℝ := Matrix.diagonal (fun _ => p)

omit [Fintype ι] in
theorem precision_posDef {p : ℝ} (hp : 0 < p) : (precision (ι := ι) p).PosDef :=
  Matrix.posDef_diagonal_iff.mpr (fun _ => hp)

theorem precision_inverse (p : ℝ) :
    (precision (ι := ι) p)⁻¹ = Matrix.diagonal (fun _ => p⁻¹) := by
  by_cases hp : p = 0
  · simp [precision, hp]
  · apply Matrix.inv_eq_left_inv
    ext i j
    by_cases hij : i = j
    · subst j
      simp [precision, Matrix.mul_apply, Matrix.diagonal, hp]
    · simp [precision, Matrix.mul_apply, Matrix.diagonal, hij]

/-- The reference coefficient retains both Wick contractions, including
the off-diagonal entries of the actual insertions. -/
def contraction (V W : Matrix ι ι ℝ) : ℝ := Matrix.trace (V * W) / 2

theorem covariance_eq {p : ℝ} (hp : 0 < p) (V W : Matrix ι ι ℝ) (hW : W.IsSymm) :
    cov[score V, score W; law (precision p)] = p⁻¹ ^ 2 * contraction V W := by
  rw [score_covariance_trace (precision_posDef hp) V W hW, precision_inverse]
  have he : Matrix.diagonal (fun _ : ι => p⁻¹) = p⁻¹ • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [he]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_smul, smul_eq_mul, contraction]
  ring

/-- The same bilinear comparison holds for arbitrary full vertices. -/
theorem relative_fisher_form {A b : ℝ} (hA : 0 < A) (hp : 0 < A + b)
    (V W : Matrix ι ι ℝ) (hW : W.IsSymm) :
    cov[score V, score W; law (precision (A + b))] =
      (A ^ 2 / (A + b) ^ 2) * cov[score V, score W; law (precision A)] := by
  rw [covariance_eq hp V W hW, covariance_eq hA V W hW]
  field_simp

omit [DecidableEq ι] in
theorem contraction_self {V : Matrix ι ι ℝ} (hV : V.IsSymm) :
    contraction V V = (∑ i, ∑ j, V i j ^ 2) / 2 := by
  have hs (i j : ι) : V j i = V i j := congrFun (congrFun hV i) j
  simp [contraction, Matrix.trace, Matrix.mul_apply, hs, pow_two]

omit [DecidableEq ι] in
theorem contraction_self_pos {V : Matrix ι ι ℝ} (hV : V.IsSymm) (hne : V ≠ 0) :
    0 < contraction V V := by
  rw [contraction_self hV]
  apply div_pos _ (by norm_num)
  have hex : ∃ i j, V i j ≠ 0 := by
    by_contra! h
    exact hne (by ext i j; exact h i j)
  obtain ⟨i, j, hij⟩ := hex
  apply Finset.sum_pos' (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact ⟨i, Finset.mem_univ _, Finset.sum_pos'
    (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero hij⟩⟩

theorem reference_positive {A : ℝ} (hA : 0 < A)
    {V : Matrix ι ι ℝ} (hV : V.IsSymm) (hne : V ≠ 0) :
    0 < cov[score V, score V; law (precision A)] := by
  rw [covariance_eq hA V V hV]
  exact mul_pos (sq_pos_of_pos (inv_pos.mpr hA)) (contraction_self_pos hV hne)

/-- Normalization is made against the unchanged vertex in its kinetic
reference. Its nonzero condition is a substantive part of this theorem. -/
theorem relative_fisher_ratio {A b : ℝ} (hA : 0 < A) (hp : 0 < A + b)
    {V : Matrix ι ι ℝ} (hV : V.IsSymm) (hne : V ≠ 0) :
    cov[score V, score V; law (precision (A + b))] /
      cov[score V, score V; law (precision A)] = A ^ 2 / (A + b) ^ 2 := by
  rw [relative_fisher_form hA hp V V hV]
  exact mul_div_cancel_right₀ _ (reference_positive hA hV hne).ne'

/-- Agreement on one nonzero quadratic observable already determines the
relative scalar. The full bilinear identity then fixes all observables. -/
theorem relative_scalar_unique {A b r : ℝ} (hA : 0 < A) (hp : 0 < A + b)
    {V : Matrix ι ι ℝ} (hV : V.IsSymm) (hne : V ≠ 0) :
    cov[score V, score V; law (precision (A + b))] =
        r * cov[score V, score V; law (precision A)] ↔
      r = A ^ 2 / (A + b) ^ 2 := by
  rw [relative_fisher_form hA hp V V hV]
  constructor
  · intro h
    exact (mul_right_cancel₀ (reference_positive hA hV hne).ne' h).symm
  · intro h
    rw [h]

theorem relative_operator_pairing {A b : ℝ} (hA : 0 < A) (hp : 0 < A + b)
    (V W : Matrix ι ι ℝ) (hW : W.IsSymm) :
    cov[score V, score ((A ^ 2 / (A + b) ^ 2) • W); law (precision A)] =
      cov[score V, score W; law (precision (A + b))] := by
  rw [covariance_eq hA V _ (hW.smul _), relative_fisher_form hA hp V W hW,
    covariance_eq hA V W hW]
  unfold contraction
  rw [Matrix.mul_smul, Matrix.trace_smul]
  change A⁻¹ ^ 2 * ((A ^ 2 / (A + b) ^ 2) * Matrix.trace (V * W) / 2) = _
  ring

/-- The relative operator is uniquely fixed on the full symmetric
quadratic-response space by the original Gaussian inner products. -/
theorem relative_operator_unique {A b : ℝ} (hA : 0 < A) (hp : 0 < A + b)
    (T : Matrix ι ι ℝ → Matrix ι ι ℝ)
    (hT : ∀ W, W.IsSymm → (T W).IsSymm)
    (hpair : ∀ V W, V.IsSymm → W.IsSymm →
      cov[score V, score (T W); law (precision A)] =
        cov[score V, score W; law (precision (A + b))])
    (W : Matrix ι ι ℝ) (hW : W.IsSymm) :
    T W = (A ^ 2 / (A + b) ^ 2) • W := by
  let K := A ^ 2 / (A + b) ^ 2
  let D := T W - K • W
  have hD : D.IsSymm := (hT W hW).sub (hW.smul K)
  have he := hpair D W hD hW
  rw [relative_fisher_form hA hp D W hW,
    covariance_eq hA D (T W) (hT W hW), covariance_eq hA D W hW] at he
  have hc : contraction D (T W) = K * contraction D W := by
    have hn : A⁻¹ ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    dsimp [K]
    nlinarith [he]
  have hz : contraction D D = 0 := by
    change Matrix.trace (D * (T W - K • W)) / 2 = 0
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul]
    change (Matrix.trace (D * T W) - K * Matrix.trace (D * W)) / 2 = 0
    unfold contraction at hc
    linarith
  have hd : D = 0 := by
    by_contra hne
    exact (contraction_self_pos hD hne).ne' hz
  exact sub_eq_zero.mp hd

/-- The intensity is an existing quadratic observable of every nonempty
coefficient block, including a constant internal scalar mode. -/
theorem intensity_reference_positive [Nonempty ι] {A : ℝ} (hA : 0 < A) :
    0 < cov[score (1 : Matrix ι ι ℝ), score 1; law (precision A)] := by
  exact reference_positive hA Matrix.isSymm_one one_ne_zero

theorem intensity_fisher_eq {p : ℝ} (hp : 0 < p) :
    cov[score (1 : Matrix ι ι ℝ), score 1; law (precision p)] =
      (Fintype.card ι : ℝ) / (2 * p ^ 2) := by
  rw [covariance_eq hp 1 1 Matrix.isSymm_one]
  simp only [contraction, Matrix.one_mul, Matrix.trace_one]
  field_simp

theorem zero_vertex_response (p : ℝ) :
    cov[score (0 : Matrix ι ι ℝ), score 0; law (precision p)] = 0 := by
  have he : score (0 : Matrix ι ι ℝ) = fun _ => (0 : ℝ) := by
    funext x
    simp [score]
  rw [he]
  simp

/-! The following finite eigenvalue calculation retains every eigenvalue
of an unchanged symmetric vertex. A diagonalization must be made in the
same scalar-precision block; these formulas do not discard mixed blocks. -/

omit [DecidableEq ι] in
def logPartition (v : ι → ℝ) (p b s t : ℝ) : ℝ :=
  ∑ i, PrecisionMixedResponse.logPartition (v i / p) (b / p) s t

omit [DecidableEq ι] in
def response (v : ι → ℝ) (p b : ℝ) (k l : ℕ) (s t : ℝ) : ℝ :=
  ∑ i, PrecisionMixedResponse.response (v i / p) (b / p) k l s t

omit [DecidableEq ι] in
def Nonsingular (v : ι → ℝ) (p b s t : ℝ) : Prop :=
  ∀ i, PrecisionMixedResponse.precision (v i / p) (b / p) s t ≠ 0

omit [DecidableEq ι] in
theorem response_zero (v : ι → ℝ) (p b : ℝ) :
    response v p b 0 0 = logPartition v p b := by
  funext s t
  simp only [response, PrecisionMixedResponse.response_zero, logPartition]

omit [DecidableEq ι] in
theorem response_hasDerivAt_left (v : ι → ℝ) (p b : ℝ)
    (k l : ℕ) (s t : ℝ) (hp : Nonsingular v p b s t) :
    HasDerivAt (fun z => response v p b k l z t)
      (response v p b (k + 1) l s t) s := by
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    PrecisionMixedResponse.response_hasDerivAt_left _ _ k l s t (hp i)) using 1
  funext z
  simp only [response, Finset.sum_apply]

omit [DecidableEq ι] in
theorem response_hasDerivAt_right (v : ι → ℝ) (p b : ℝ)
    (k l : ℕ) (s t : ℝ) (hp : Nonsingular v p b s t) :
    HasDerivAt (response v p b k l s)
      (response v p b k (l + 1) s t) t := by
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    PrecisionMixedResponse.response_hasDerivAt_right _ _ k l s t (hp i)) using 1
  funext z
  simp only [response, Finset.sum_apply]

omit [DecidableEq ι] in
theorem nonsingular_eventually_right {v : ι → ℝ} {p b s t : ℝ}
    (hp : Nonsingular v p b s t) :
    ∀ᶠ z in nhds t, Nonsingular v p b s z := by
  apply Filter.eventually_all.mpr
  intro i
  have hc : Continuous (PrecisionMixedResponse.precision (v i / p) (b / p) s) := by
    unfold PrecisionMixedResponse.precision
    fun_prop
  exact hc.continuousAt.eventually (eventually_ne_nhds (hp i))

omit [DecidableEq ι] in
theorem nonsingular_eventually_left {v : ι → ℝ} {p b s t : ℝ}
    (hp : Nonsingular v p b s t) :
    ∀ᶠ z in nhds s, Nonsingular v p b z t := by
  apply Filter.eventually_all.mpr
  intro i
  have hc : Continuous (fun z =>
      PrecisionMixedResponse.precision (v i / p) (b / p) z t) := by
    unfold PrecisionMixedResponse.precision
    fun_prop
  exact hc.continuousAt.eventually (eventually_ne_nhds (hp i))

omit [DecidableEq ι] in
theorem iteratedDeriv_right (v : ι → ℝ) (p b s : ℝ) (l : ℕ) (t : ℝ)
    (hp : Nonsingular v p b s t) :
    iteratedDeriv l (logPartition v p b s) t = response v p b 0 l s t := by
  induction l generalizing t with
  | zero => simp only [iteratedDeriv_zero, response_zero]
  | succ l ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv l (logPartition v p b s) =ᶠ[nhds t]
        response v p b 0 l s := by
      filter_upwards [nonsingular_eventually_right hp] with z hz
      exact ih z hz
    exact he.deriv_eq.trans (response_hasDerivAt_right v p b 0 l s t hp).deriv

omit [DecidableEq ι] in
theorem iteratedDeriv_mixed (v : ι → ℝ) (p b : ℝ) (k l : ℕ) (s t : ℝ)
    (hp : Nonsingular v p b s t) :
    iteratedDeriv k (fun z => iteratedDeriv l (logPartition v p b z) t) s =
      response v p b k l s t := by
  induction k generalizing s with
  | zero => simpa only [iteratedDeriv_zero] using iteratedDeriv_right v p b s l t hp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he :
        (fun z => iteratedDeriv k (fun w => iteratedDeriv l (logPartition v p b w) t) z)
          =ᶠ[nhds s] (fun z => response v p b k l z t) := by
      filter_upwards [nonsingular_eventually_left hp] with z hz
      exact ih z hz
    exact he.deriv_eq.trans (response_hasDerivAt_left v p b k l s t hp).deriv

def gaussianCoefficient (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * ((k - 1).factorial : ℝ) / 2

theorem gaussianCoefficient_ne_zero (k : ℕ) : gaussianCoefficient k ≠ 0 := by
  unfold gaussianCoefficient
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast (Nat.factorial_ne_zero (k - 1)))) (by norm_num)

omit [DecidableEq ι] in
def evenMoment (v : ι → ℝ) (n : ℕ) : ℝ := ∑ i, v i ^ (2 * n)

omit [DecidableEq ι] in
theorem evenMoment_pos {v : ι → ℝ} (hv : v ≠ 0) {n : ℕ} (_hn : 1 ≤ n) :
    0 < evenMoment v n := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (by funext i; exact h i)
  obtain ⟨i, hi⟩ := hex
  unfold evenMoment
  apply Finset.sum_pos'
  · intro j _
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hi) _

omit [DecidableEq ι] in
theorem mixed_derivative_at_origin (v : ι → ℝ) (p b : ℝ)
    (k l : ℕ) (hn : k + l ≠ 0) :
    iteratedDeriv k (fun s => iteratedDeriv l (logPartition v p b s) 0) 0 =
      gaussianCoefficient (k + l) *
        ∑ i, (v i / p) ^ k * (b / p) ^ l := by
  rw [iteratedDeriv_mixed v p b k l 0 0 (by
    intro i; norm_num [PrecisionMixedResponse.precision])]
  simp only [response, PrecisionMixedResponse.response_of_ne _ _ _ _ hn,
    PrecisionMixedResponse.positiveResponse, PrecisionMixedResponse.precision,
    zero_mul, add_zero, one_zpow, mul_one,
    PrecisionMixedResponse.numerator, gaussianCoefficient, Finset.mul_sum]
  simp only [mul_assoc]

omit [DecidableEq ι] in
theorem mixed_even_derivative (v : ι → ℝ) (p b : ℝ)
    (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n) (fun s => iteratedDeriv n (logPartition v p b s) 0) 0 =
      gaussianCoefficient (3 * n) * evenMoment v n * (b ^ n / p ^ (3 * n)) := by
  rw [mixed_derivative_at_origin v p b (2 * n) n (by omega),
    show 2 * n + n = 3 * n by omega]
  unfold evenMoment
  rw [mul_assoc, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_pow, div_pow, show 3 * n = 2 * n + n by omega, pow_add]
  ring

omit [DecidableEq ι] in
theorem pure_kinetic_even_derivative (v : ι → ℝ) (A : ℝ)
    (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv (2 * n) (fun s => logPartition v A 0 s 0) 0 =
      gaussianCoefficient (2 * n) * evenMoment v n / A ^ (2 * n) := by
  have h := mixed_derivative_at_origin v A 0 (2 * n) 0 (by omega)
  simp only [iteratedDeriv_zero, Nat.add_zero, pow_zero, mul_one] at h
  rw [h]
  simp only [div_pow, evenMoment, ← Finset.sum_div]
  ring

omit [DecidableEq ι] in
/-- Every even vertex moment cancels against the unchanged kinetic
reference, before any trace over branches or frequencies is taken. -/
theorem same_vertex_reference_ratio {v : ι → ℝ} (hv : v ≠ 0)
    {A b : ℝ} (_hA : 0 < A) (hp : 0 < A + b) (n : ℕ) (hn : 1 ≤ n) :
    ((iteratedDeriv (2 * n)
        (fun s => iteratedDeriv n (logPartition v (A + b) b s) 0) 0) /
      gaussianCoefficient (3 * n)) /
      ((iteratedDeriv (2 * n) (fun s => logPartition v A 0 s 0) 0) /
        gaussianCoefficient (2 * n)) = (b * A ^ 2 / (A + b) ^ 3) ^ n := by
  rw [mixed_even_derivative v _ _ n hn, pure_kinetic_even_derivative v _ n hn]
  have hc3 := gaussianCoefficient_ne_zero (3 * n)
  have hc2 := gaussianCoefficient_ne_zero (2 * n)
  have hm := (evenMoment_pos hv hn).ne'
  rw [div_pow, mul_pow, pow_mul]
  field_simp [_hA.ne', hp.ne']
  rw [pow_mul]

omit [DecidableEq ι] in
theorem logPartition_eq_actual (v : ι → ℝ) (p b s t : ℝ) :
    FinitePrecisionTilt.logPartition (fun _ : ι => p)
        (fun i => s * v i + t * b) 1 = logPartition v p b s t := by
  simp only [FinitePrecisionTilt.logPartition, logPartition,
    PrecisionMixedResponse.logPartition, PrecisionMixedResponse.precision,
    one_mul, add_div, mul_div_assoc, add_assoc]
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

theorem actual_log_partition {v : ι → ℝ} {p b s t : ℝ} (hp : 0 < p)
    (hv : ∀ i, 0 < p + s * v i + t * b) :
    Real.log (FinitePrecisionTilt.partition (fun _ : ι => p)
      (fun i => s * v i + t * b) 1) = logPartition v p b s t := by
  rw [FinitePrecisionTilt.log_partition (fun _ => hp) (by
    intro i
    simpa only [FinitePrecisionTilt.variedPrecision, one_mul, add_assoc] using hv i)]
  exact logPartition_eq_actual v p b s t

def actualPartition (v : ι → ℝ) (p b s t : ℝ) : ℝ :=
  FinitePrecisionTilt.partition (fun _ : ι => p)
    (fun i => s * v i + t * b) 1

theorem actual_right_derivative_eq {v : ι → ℝ} {p b s : ℝ} (hp : 0 < p)
    (hv : ∀ i, 0 < p + s * v i) (l : ℕ) :
    iteratedDeriv l (fun t => Real.log (actualPartition v p b s t)) 0 =
      iteratedDeriv l (logPartition v p b s) 0 := by
  have hepos : ∀ᶠ t in nhds (0 : ℝ), ∀ i, 0 < p + s * v i + t * b :=
    Filter.eventually_all.mpr fun i =>
      (isOpen_lt continuous_const (by fun_prop :
        Continuous (fun t : ℝ => p + s * v i + t * b))).mem_nhds
          (by simpa using hv i)
  have he : (fun t => Real.log (actualPartition v p b s t)) =ᶠ[nhds 0]
      logPartition v p b s := by
    filter_upwards [hepos] with t ht
    exact actual_log_partition hp ht
  exact he.iteratedDeriv_eq l

theorem actual_mixed_derivative_eq {v : ι → ℝ} {p b : ℝ} (hp : 0 < p)
    (k l : ℕ) :
    iteratedDeriv k
        (fun s => iteratedDeriv l (fun t => Real.log (actualPartition v p b s t)) 0) 0 =
      iteratedDeriv k (fun s => iteratedDeriv l (logPartition v p b s) 0) 0 := by
  have hepos : ∀ᶠ s in nhds (0 : ℝ), ∀ i, 0 < p + s * v i :=
    Filter.eventually_all.mpr fun i =>
      (isOpen_lt continuous_const (by fun_prop :
        Continuous (fun s : ℝ => p + s * v i))).mem_nhds (by simpa using hp)
  have he :
      (fun s => iteratedDeriv l (fun t => Real.log (actualPartition v p b s t)) 0)
        =ᶠ[nhds 0] (fun s => iteratedDeriv l (logPartition v p b s) 0) := by
    filter_upwards [hepos] with s hs
    exact actual_right_derivative_eq hp hs l
  exact he.iteratedDeriv_eq k

/-- The full finite Gaussian partition is used on both sides. No vertex
rescaling or replacement source is introduced in this normalization. -/
theorem actual_same_vertex_reference_ratio {v : ι → ℝ} (hv : v ≠ 0)
    {A b : ℝ} (hA : 0 < A) (hp : 0 < A + b) (n : ℕ) (hn : 1 ≤ n) :
    ((iteratedDeriv (2 * n)
        (fun s => iteratedDeriv n
          (fun t => Real.log (actualPartition v (A + b) b s t)) 0) 0) /
      gaussianCoefficient (3 * n)) /
      ((iteratedDeriv (2 * n) (fun s => Real.log (actualPartition v A 0 s 0)) 0) /
        gaussianCoefficient (2 * n)) = (b * A ^ 2 / (A + b) ^ 3) ^ n := by
  rw [actual_mixed_derivative_eq hp]
  have href := actual_mixed_derivative_eq (v := v) (b := 0) hA (2 * n) 0
  simp only [iteratedDeriv_zero] at href
  rw [href]
  exact same_vertex_reference_ratio hv hA hp n hn

end GeneratedFoundations.Operations.ScalarVertexComparison
