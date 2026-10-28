module

public import GeneratedFoundations.Physical.SourceTTCollectiveComparison

/-!
# Second mass response of the retained tensor source

The branch data, Gaussian weight and frequency interval are unchanged.
The only variation is the common logarithmic mass insertion already used
in `SourceTTCollectiveComparison`. Its effective mass fraction is an
average in the response-weighted source trace. Differentiating that actual
average produces a variance term; replacing the trace by one mass split
would discard this term.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Physical.SourceTTCollectiveVariance

open SourceTensorResponseEndpoint SourceTTCollectiveComparison

def fraction (a b z u : ℝ) : ℝ :=
  massFraction (u ^ 2 + a) (Real.exp z * b)

private theorem precision_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    0 < u ^ 2 + a + Real.exp z * b := by
  have hm := mul_pos (Real.exp_pos z) hb
  nlinarith [sq_nonneg u]

theorem fraction_continuous {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z : ℝ) :
    Continuous (fraction a b z) := by
  exact continuous_const.div (by fun_prop)
    (fun u => (precision_pos ha hb z u).ne')

theorem fraction_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    0 ≤ fraction a b z u ∧ fraction a b z u ≤ 1 :=
  massFraction_mem_unitInterval (by nlinarith [sq_nonneg u])
    (mul_pos (Real.exp_pos z) hb).le (precision_pos ha hb z u)

theorem fraction_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    HasDerivAt (fun t => fraction a b t u)
      (fraction a b z u * (1 - fraction a b z u)) z := by
  have he := (Real.hasDerivAt_exp z).mul_const b
  convert! he.div (he.const_add (u ^ 2 + a)) (precision_pos ha hb z u).ne' using 1
  unfold fraction massFraction
  field_simp

def secondProfile (a b z u : ℝ) : ℝ :=
  fraction a b z u * capacityProfile a b z u

theorem secondProfile_continuous {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z : ℝ) :
    Continuous (secondProfile a b z) :=
  (fraction_continuous ha hb z).mul (capacityProfile_continuous ha hb z)

theorem secondProfile_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    0 ≤ secondProfile a b z u ∧
      secondProfile a b z u ≤ capacityProfile a b z u := by
  have hy := fraction_bounds ha hb z u
  have hc := capacityProfile_bounds ha hb z u
  exact ⟨mul_nonneg hy.1 hc.1,
    (mul_le_mul_of_nonneg_right hy.2 hc.1).trans_eq (one_mul _)⟩

theorem capacityProfile_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z u : ℝ) :
    HasDerivAt (fun t => capacityProfile a b t u)
      (capacityProfile a b z u - 3 * secondProfile a b z u) z := by
  have hf := fraction_hasDerivAt ha hb z u
  have hd := (hf.mul (((hasDerivAt_const z (1 : ℝ)).sub hf).pow 2)).mul_const
    (envelope a u)
  convert! hd using 1
  unfold secondProfile capacityProfile massWeightedResponse fraction
  simp only [Pi.pow_apply, Pi.sub_apply, Nat.cast_ofNat]
  ring

theorem frequency_capacity_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z v : ℝ) :
    HasDerivAt (fun t => ∫ u in (0 : ℝ)..v, capacityProfile a b t u)
      ((∫ u in (0 : ℝ)..v, capacityProfile a b z u) -
        3 * ∫ u in (0 : ℝ)..v, secondProfile a b z u) z := by
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t u => capacityProfile a b t u)
    (F' := fun t u => capacityProfile a b t u - 3 * secondProfile a b t u)
    (bound := fun u => (8 / 27 : ℝ) * envelope a u)
    (s := Set.univ) (Filter.univ_mem : Set.univ ∈ nhds z)
    (Filter.Eventually.of_forall fun t =>
      (capacityProfile_continuous ha hb t).aestronglyMeasurable)
    (show IntervalIntegrable (capacityProfile a b z) volume 0 v from
      (capacityProfile_continuous ha hb z).intervalIntegrable _ _)
    (((capacityProfile_continuous ha hb z).sub
      (continuous_const.mul (secondProfile_continuous ha hb z))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u _ t _ => by
      have hc := capacityProfile_bounds ha hb t u
      have hs := secondProfile_bounds ha hb t u
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith)
    ((by unfold envelope; fun_prop :
      Continuous (fun u => (8 / 27 : ℝ) * envelope a u)).intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun u _ t _ => capacityProfile_hasDerivAt ha hb t u)).2
  convert! hd using 1
  rw [intervalIntegral.integral_sub
    (f := fun u => capacityProfile a b z u)
    (g := fun u => 3 * secondProfile a b z u)
    ((capacityProfile_continuous ha hb z).intervalIntegrable _ _)
    ((continuous_const.mul (secondProfile_continuous ha hb z)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]

def secondIntegral (z : ℝ) (i : Branch) : ℝ :=
  ∫ u in (0 : ℝ)..upper i,
    secondProfile (SourceTTGaussianCoefficient.branch i).1
      (SourceTTGaussianCoefficient.branch i).2.1 z u

def secondCoefficient (z : ℝ) : ℝ :=
  (1 / (32 * Real.pi ^ 3)) *
    ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 * secondIntegral z i

theorem capacityCoefficient_hasDerivAt (z : ℝ) :
    HasDerivAt capacityCoefficient (capacityCoefficient z - 3 * secondCoefficient z) z := by
  have hi (i : Branch) :=
    (frequency_capacity_hasDerivAt (SourceTTGaussianCoefficient.branch_bounds i).1
      (SourceTTGaussianCoefficient.branch_bounds i).2.2.1 z (upper i)).const_mul
        (SourceTTGaussianCoefficient.branch i).2.2
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hi i).const_mul
    (1 / (32 * Real.pi ^ 3))
  convert! hd using 1
  simp only [capacityCoefficient, secondCoefficient, capacityIntegral, secondIntegral]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [mul_sub]
  congr 1
  simp_rw [show ∀ i : Branch,
      (SourceTTGaussianCoefficient.branch i).2.2 *
        (3 * ∫ u in (0 : ℝ)..upper i,
          secondProfile (SourceTTGaussianCoefficient.branch i).1
            (SourceTTGaussianCoefficient.branch i).2.1 z u) =
      3 * ((SourceTTGaussianCoefficient.branch i).2.2 *
        ∫ u in (0 : ℝ)..upper i,
          secondProfile (SourceTTGaussianCoefficient.branch i).1
            (SourceTTGaussianCoefficient.branch i).2.1 z u) from fun _ => by ring,
    ← Finset.mul_sum]
  ring

def centeredProfile (a b z m u : ℝ) : ℝ :=
  kineticProfile a b z u * (fraction a b z u - m) ^ 2

theorem centeredProfile_continuous {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (z m : ℝ) :
    Continuous (centeredProfile a b z m) :=
  (kineticProfile_continuous ha hb z).mul
    (((fraction_continuous ha hb z).sub continuous_const).pow 2)

theorem centeredProfile_nonneg (a b z m u : ℝ) :
    0 ≤ centeredProfile a b z m u :=
  mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (Real.exp_pos _).le) (sq_nonneg _)

theorem centeredProfile_expansion {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z m u : ℝ) :
    centeredProfile a b z m u = secondProfile a b z u -
      2 * m * capacityProfile a b z u + m ^ 2 * kineticProfile a b z u := by
  unfold centeredProfile secondProfile kineticProfile capacityProfile
  rw [ttKernel_eq_massFraction _ _ (precision_pos ha hb z u).ne']
  unfold fraction massWeightedResponse
  ring

def centeredIntegral (z m : ℝ) (i : Branch) : ℝ :=
  ∫ u in (0 : ℝ)..upper i,
    centeredProfile (SourceTTGaussianCoefficient.branch i).1
      (SourceTTGaussianCoefficient.branch i).2.1 z m u

def centeredCoefficient (z m : ℝ) : ℝ :=
  (1 / (32 * Real.pi ^ 3)) *
    ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 * centeredIntegral z m i

theorem centeredCoefficient_nonneg (z m : ℝ) : 0 ≤ centeredCoefficient z m := by
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (SourceTTGaussianCoefficient.branch_bounds i).2.2.2.le
  exact intervalIntegral.integral_nonneg (Real.sqrt_nonneg _) fun u _ =>
    centeredProfile_nonneg _ _ _ _ _

/-- Every retained frequency interval contains distinct mass fractions.
Its positive source response therefore has nonzero centered variance for
every constant proposed as a common split. -/
theorem centeredIntegral_pos (z m : ℝ) (i : Branch) :
    0 < centeredIntegral z m i := by
  have ha := (SourceTTGaussianCoefficient.branch_bounds i).1
  have hb := (SourceTTGaussianCoefficient.branch_bounds i).2.2.1
  have hv : 0 < upper i :=
    Real.sqrt_pos.2 (sub_pos.2 (SourceTTGaussianCoefficient.branch_bounds i).2.1)
  have hm := mul_pos (Real.exp_pos z) hb
  have hy : fraction (SourceTTGaussianCoefficient.branch i).1
      (SourceTTGaussianCoefficient.branch i).2.1 z (2 * upper i / 3) <
      fraction (SourceTTGaussianCoefficient.branch i).1
        (SourceTTGaussianCoefficient.branch i).2.1 z (upper i / 3) := by
    unfold fraction massFraction
    apply (div_lt_div_iff₀ (precision_pos ha hb z _) (precision_pos ha hb z _)).2
    nlinarith [mul_pos hm (sq_pos_of_pos hv)]
  have hp (u : ℝ) (hu : 0 < u)
      (hne : fraction (SourceTTGaussianCoefficient.branch i).1
        (SourceTTGaussianCoefficient.branch i).2.1 z u ≠ m) :
      0 < centeredProfile (SourceTTGaussianCoefficient.branch i).1
        (SourceTTGaussianCoefficient.branch i).2.1 z m u := by
    have hq : 0 < u ^ 2 + (SourceTTGaussianCoefficient.branch i).1 :=
      lt_of_lt_of_le (sq_pos_of_pos hu) (le_add_of_nonneg_right ha)
    exact mul_pos (mul_pos (div_pos (sq_pos_of_pos hq)
      (sq_pos_of_pos (precision_pos ha hb z u))) (Real.exp_pos _))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  apply intervalIntegral.integral_pos hv
    (centeredProfile_continuous ha hb z m).continuousOn
    (fun u _ => centeredProfile_nonneg _ _ _ _ _)
  by_cases h : fraction (SourceTTGaussianCoefficient.branch i).1
      (SourceTTGaussianCoefficient.branch i).2.1 z (upper i / 3) = m
  · refine ⟨2 * upper i / 3, ⟨by linarith, by linarith⟩,
      hp _ (by linarith) ?_⟩
    exact (hy.trans_eq h).ne
  · exact ⟨upper i / 3, ⟨by linarith, by linarith⟩, hp _ (by linarith) h⟩

theorem centeredCoefficient_pos (z m : ℝ) : 0 < centeredCoefficient z m := by
  apply mul_pos (by positivity : (0 : ℝ) < 1 / (32 * Real.pi ^ 3))
  exact Finset.sum_pos (fun i _ =>
    mul_pos (SourceTTGaussianCoefficient.branch_bounds i).2.2.2
      (centeredIntegral_pos z m i)) Finset.univ_nonempty

theorem centeredCoefficient_eq (z m : ℝ) :
    centeredCoefficient z m = secondCoefficient z -
      2 * m * capacityCoefficient z + m ^ 2 * massCoefficient z := by
  have hi (i : Branch) : centeredIntegral z m i = secondIntegral z i -
      2 * m * capacityIntegral z i + m ^ 2 * kineticIntegral z i := by
    have ha := (SourceTTGaussianCoefficient.branch_bounds i).1
    have hb := (SourceTTGaussianCoefficient.branch_bounds i).2.2.1
    unfold centeredIntegral
    simp_rw [centeredProfile_expansion ha hb]
    rw [intervalIntegral.integral_add
      (f := fun u => secondProfile (SourceTTGaussianCoefficient.branch i).1
        (SourceTTGaussianCoefficient.branch i).2.1 z u - 2 * m *
        capacityProfile (SourceTTGaussianCoefficient.branch i).1
          (SourceTTGaussianCoefficient.branch i).2.1 z u)
      (g := fun u => m ^ 2 * kineticProfile (SourceTTGaussianCoefficient.branch i).1
        (SourceTTGaussianCoefficient.branch i).2.1 z u)
      (((secondProfile_continuous ha hb z).sub
        (continuous_const.mul (capacityProfile_continuous ha hb z))).intervalIntegrable _ _)
      ((continuous_const.mul (kineticProfile_continuous ha hb z)).intervalIntegrable _ _),
      intervalIntegral.integral_sub
        (f := fun u => secondProfile (SourceTTGaussianCoefficient.branch i).1
          (SourceTTGaussianCoefficient.branch i).2.1 z u)
        (g := fun u => 2 * m * capacityProfile (SourceTTGaussianCoefficient.branch i).1
          (SourceTTGaussianCoefficient.branch i).2.1 z u)
        ((secondProfile_continuous ha hb z).intervalIntegrable _ _)
        ((continuous_const.mul (capacityProfile_continuous ha hb z)).intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const_mul, secondIntegral,
      capacityIntegral, kineticIntegral]
  unfold centeredCoefficient secondCoefficient capacityCoefficient massCoefficient
  simp_rw [hi]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Variance in the original response-weighted trace. -/
def responseVariance (z : ℝ) : ℝ :=
  centeredCoefficient z (effectiveMassFraction z) / massCoefficient z

theorem responseVariance_nonneg (z : ℝ) : 0 ≤ responseVariance z :=
  div_nonneg (centeredCoefficient_nonneg _ _) (massCoefficient_pos z).le

theorem responseVariance_pos (z : ℝ) : 0 < responseVariance z :=
  div_pos (centeredCoefficient_pos _ _) (massCoefficient_pos z)

theorem responseVariance_eq (z : ℝ) :
    responseVariance z = secondCoefficient z / massCoefficient z -
      (effectiveMassFraction z) ^ 2 := by
  rw [responseVariance, centeredCoefficient_eq]
  unfold effectiveMassFraction
  field_simp [(massCoefficient_pos z).ne']
  ring

/-- Differentiating the actual common-mass source average retains its
between-mode variance. The parameter is the comparison variable, not time. -/
theorem effectiveMassFraction_hasDerivAt (z : ℝ) :
    HasDerivAt effectiveMassFraction
      (effectiveMassFraction z * (1 - effectiveMassFraction z) -
        3 * responseVariance z) z := by
  have hd := (capacityCoefficient_hasDerivAt z).div
    (massCoefficient_hasDerivAt z) (massCoefficient_pos z).ne'
  convert! hd using 1
  rw [responseVariance_eq]
  unfold effectiveMassFraction
  field_simp [(massCoefficient_pos z).ne']
  ring

theorem effectiveMassFraction_deriv_le (z : ℝ) :
    deriv effectiveMassFraction z ≤
      effectiveMassFraction z * (1 - effectiveMassFraction z) := by
  rw [(effectiveMassFraction_hasDerivAt z).deriv]
  linarith [responseVariance_nonneg z]

theorem one_split_derivative_iff (z : ℝ) :
    deriv effectiveMassFraction z =
      effectiveMassFraction z * (1 - effectiveMassFraction z) ↔
      responseVariance z = 0 := by
  rw [(effectiveMassFraction_hasDerivAt z).deriv]
  constructor <;> intro h <;> linarith

theorem effectiveMassFraction_deriv_lt (z : ℝ) :
    deriv effectiveMassFraction z <
      effectiveMassFraction z * (1 - effectiveMassFraction z) := by
  rw [(effectiveMassFraction_hasDerivAt z).deriv]
  linarith [responseVariance_pos z]

/-- A stationary collective capacity fixes a response-weighted moment,
not every individual mass fraction. -/
theorem stationary_capacity_iff (z : ℝ) :
    deriv capacityCoefficient z = 0 ↔
      secondCoefficient z / capacityCoefficient z = 1 / 3 := by
  rw [(capacityCoefficient_hasDerivAt z).deriv]
  apply Iff.intro
  · intro h
    apply (div_eq_iff (capacityCoefficient_pos z).ne').2
    linarith
  · intro h
    have he := (div_eq_iff (capacityCoefficient_pos z).ne').1 h
    linarith

theorem capacityCoefficient_strict_bound (z : ℝ) :
    capacityCoefficient z < (4 / 27 : ℝ) * weightCoefficient := by
  have hstrict : capacityIntegral z (0 : Branch) <
      (4 / 27 : ℝ) * weightIntegral (0 : Branch) := by
    have ha := (SourceTTGaussianCoefficient.branch_bounds (0 : Branch)).1
    have hb := (SourceTTGaussianCoefficient.branch_bounds (0 : Branch)).2.2.1
    rw [capacityIntegral, weightIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (Real.sqrt_pos.2 (sub_pos.2
        (SourceTTGaussianCoefficient.branch_bounds (0 : Branch)).2.1))
      (capacityProfile_continuous ha hb z).continuousOn
      (show ContinuousOn (fun u => (4 / 27 : ℝ) *
        envelope (SourceTTGaussianCoefficient.branch (0 : Branch)).1 u) _ from
        (by unfold envelope; fun_prop : Continuous
          (fun u => (4 / 27 : ℝ) *
            envelope (SourceTTGaussianCoefficient.branch (0 : Branch)).1 u)).continuousOn)
      (fun u _ => (capacityProfile_bounds ha hb z u).2)
    refine ⟨0, ⟨le_rfl, Real.sqrt_nonneg _⟩, ?_⟩
    have hn : Real.exp z * (3 / 4 : ℝ) ≠ 0 :=
      mul_ne_zero (Real.exp_ne_zero z) (by norm_num)
    norm_num [capacityProfile, SourceTTGaussianCoefficient.branch,
      massFraction, massWeightedResponse, envelope, hn]
  have hle (i : Branch) : capacityIntegral z i ≤
      (4 / 27 : ℝ) * weightIntegral i := by
    have ha := (SourceTTGaussianCoefficient.branch_bounds i).1
    have hb := (SourceTTGaussianCoefficient.branch_bounds i).2.2.1
    rw [capacityIntegral, weightIntegral, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
      ((capacityProfile_continuous ha hb z).intervalIntegrable _ _)
      ((by unfold envelope; fun_prop : Continuous
        (fun u => (4 / 27 : ℝ) * envelope (SourceTTGaussianCoefficient.branch i).1 u)).intervalIntegrable _ _)
      (fun u _ => (capacityProfile_bounds ha hb z u).2)
  unfold capacityCoefficient weightCoefficient
  calc
    _ < (1 / (32 * Real.pi ^ 3)) *
        ∑ i : Branch, (SourceTTGaussianCoefficient.branch i).2.2 *
          ((4 / 27 : ℝ) * weightIntegral i) := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      apply Finset.sum_lt_sum
      · exact fun i _ => mul_le_mul_of_nonneg_left (hle i)
          (SourceTTGaussianCoefficient.branch_bounds i).2.2.2.le
      · exact ⟨0, Finset.mem_univ _, mul_lt_mul_of_pos_left hstrict
          (SourceTTGaussianCoefficient.branch_bounds (0 : Branch)).2.2.2⟩
    _ = _ := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem normalized_capacity_strict_bound (z : ℝ) :
    capacityCoefficient z / weightCoefficient < (4 / 27 : ℝ) :=
  (div_lt_iff₀ weightCoefficient_pos).2 (capacityCoefficient_strict_bound z)

end GeneratedFoundations.Physical.SourceTTCollectiveVariance
