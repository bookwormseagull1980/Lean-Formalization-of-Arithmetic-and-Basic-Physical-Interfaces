module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionContent

/-!
# Coordinate scaling of the complete history-section response

The source and its window are the ones constructed in the preceding modules.
Here `c > 0` is a change of frequency/length coordinate, not an additional
source datum. Both kinetic and restoring squared eigenvalues scale by `c⁻²`.
The Gaussian and the frequency cutoff are transported at the same time.

The factor `1/c` is then the Jacobian of the actual one-dimensional frequency
integral. It is proved for every branch and for the complete comparison and
response, rather than inserted into a separate algebraic response definition.
This covariance does not prescribe a content count or an endpoint equation.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionScale

open HistoryHaarSectionJointHessian (Index eigenvalue)
open HistoryHaarSectionWindow
open HistoryHaarSectionComparison
open Operations.ScalarPrecisionComparison

def scaledKinetic (N : ℕ) (c : ℝ) (i : Index N) : ℝ := kinetic N i / c ^ 2

def scaledRestoring (N : ℕ) (c : ℝ) (i : Index N) : ℝ := restoring N i / c ^ 2

def scaledEigenvalue (N : ℕ) (c : ℝ) (i : Index N) : ℝ := eigenvalue N i / c ^ 2

theorem scaled_source_response (N : ℕ) (c : ℝ) (i : Index N) :
    scaledEigenvalue N c i = scaledKinetic N c i + scaledRestoring N c i := by
  simp only [scaledEigenvalue, scaledKinetic, scaledRestoring, source_response_decomposition,
    add_div]

theorem scaledEigenvalue_pos (N : ℕ) {c : ℝ} (hc : 0 < c) (i : Index N) :
    0 < scaledEigenvalue N c i :=
  div_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15 / 8)
    (HistoryHaarSectionJointHessian.eigenvalue_lower N i)) (sq_pos_of_pos hc)

def scaledKineticPrecision (N : ℕ) (c : ℝ) (i : Index N) (ω : ℝ) : ℝ :=
  ω ^ 2 + scaledKinetic N c i

def scaledPrecision (N : ℕ) (c : ℝ) (i : Index N) (ω : ℝ) : ℝ :=
  ω ^ 2 + scaledEigenvalue N c i

theorem scaled_precision_pos (N : ℕ) {c : ℝ} (hc : 0 < c) (i : Index N) (ω : ℝ) :
    0 < scaledPrecision N c i ω :=
  add_pos_of_nonneg_of_pos (sq_nonneg ω) (scaledEigenvalue_pos N hc i)

theorem kinetic_precision_transport (N : ℕ) {c : ℝ} (hc : c ≠ 0)
    (i : Index N) (ω : ℝ) :
    c ^ 2 * scaledKineticPrecision N c i ω = kineticPrecision N i (c * ω) := by
  unfold scaledKineticPrecision scaledKinetic kineticPrecision
  field_simp [hc]

theorem precision_transport (N : ℕ) {c : ℝ} (hc : c ≠ 0)
    (i : Index N) (ω : ℝ) :
    c ^ 2 * scaledPrecision N c i ω = precision N i (c * ω) := by
  unfold scaledPrecision scaledEigenvalue precision
  field_simp [hc]

theorem kinetic_fraction_transport (N : ℕ) {c : ℝ} (hc : c ≠ 0)
    (i : Index N) (ω : ℝ) :
    scaledKineticPrecision N c i ω / scaledPrecision N c i ω =
      kineticFraction N i (c * ω) := by
  rw [kineticFraction, ← kinetic_precision_transport N hc, ← precision_transport N hc]
  exact (mul_div_mul_left _ _ (pow_ne_zero 2 hc)).symm

def scaledWeight (N : ℕ) (c : ℝ) (i : Index N) (ω : ℝ) : ℝ :=
  Real.exp (-(c ^ 2 * scaledKineticPrecision N c i ω))

theorem weight_transport (N : ℕ) {c : ℝ} (hc : c ≠ 0)
    (i : Index N) (ω : ℝ) :
    scaledWeight N c i ω = weight N i (c * ω) := by
  rw [scaledWeight, kinetic_precision_transport N hc, weight]

def scaledKernel (N : ℕ) (c : ℝ) (i : Index N) (ω : ℝ) : ℝ :=
  (scaledKineticPrecision N c i ω / scaledPrecision N c i ω) ^ 2 *
    scaledWeight N c i ω

theorem kernel_transport (N : ℕ) {c : ℝ} (hc : c ≠ 0)
    (i : Index N) (ω : ℝ) : scaledKernel N c i ω = kernel N i (c * ω) := by
  rw [scaledKernel, kinetic_fraction_transport N hc, weight_transport N hc]
  rfl

def frequencyEdge (N : ℕ) (B c : ℝ) (i : Index N) : ℝ :=
  Real.sqrt (B / c ^ 2 - scaledKinetic N c i)

theorem frequencyEdge_transport (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) (i : Index N) :
    frequencyEdge N B c i = Real.sqrt (B - kinetic N i) / c := by
  rw [frequencyEdge, scaledKinetic, ← sub_div, Real.sqrt_div' _ (sq_nonneg c),
    Real.sqrt_sq_eq_abs, abs_of_pos hc]

theorem source_support_transport (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) (i : Index N) :
    scaledKinetic N c i < B / c ^ 2 ↔ i ∈ support N B := by
  rw [scaledKinetic, div_lt_div_iff_of_pos_right (sq_pos_of_pos hc), mem_support]

theorem frequency_window_transport (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c)
    (i : Index N) (ω : ℝ) :
    scaledKineticPrecision N c i ω < B / c ^ 2 ↔
      kineticPrecision N i (c * ω) < B := by
  rw [← kinetic_precision_transport N hc.ne']
  exact lt_div_iff₀' (sq_pos_of_pos hc)

def scaledBranchIntegral (N : ℕ) (B c : ℝ) (i : Index N) : ℝ :=
  ∫ ω in (0 : ℝ)..frequencyEdge N B c i, scaledKernel N c i ω

theorem branchIntegral_transport (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) (i : Index N) :
    scaledBranchIntegral N B c i = branchIntegral N B i / c := by
  simp only [scaledBranchIntegral, frequencyEdge_transport N B hc,
    kernel_transport N hc.ne']
  rw [intervalIntegral.integral_comp_mul_left _ hc.ne']
  have hu : c * (Real.sqrt (B - kinetic N i) / c) = Real.sqrt (B - kinetic N i) := by
    field_simp [hc.ne']
  rw [mul_zero, hu, smul_eq_mul]
  exact (div_eq_inv_mul _ _).symm

def scaledResponse (N : ℕ) (B c : ℝ) : ℝ :=
  ∑ i ∈ support N B, scaledBranchIntegral N B c i

theorem response_transport (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    scaledResponse N B c = responseTrace N B / c := by
  classical
  simp only [scaledResponse, branchIntegral_transport N B hc, Finset.sum_div,
    responseTrace]

theorem response_scale_composition (N : ℕ) (B : ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    scaledResponse N B (c * d) = scaledResponse N B c / d := by
  rw [response_transport N B (mul_pos hc hd), response_transport N B hc]
  exact (div_div _ _ _).symm

theorem response_hasDerivAt_scale (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (scaledResponse N B) (-responseTrace N B / c ^ 2) c := by
  have hd := (hasDerivAt_const c (responseTrace N B)).div (hasDerivAt_id c) hc.ne'
  have hd' : HasDerivAt (fun d : ℝ => responseTrace N B / d)
      (-responseTrace N B / c ^ 2) c := by
    convert! hd using 1
    simp
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hc] with d hd
  exact response_transport N B hd

theorem response_strictAntiOn_scale (N : ℕ) (B : ℝ) (hB : (support N B).Nonempty) :
    StrictAntiOn (scaledResponse N B) (Ioi 0) := by
  intro c hc d hd hcd
  rw [response_transport N B hc, response_transport N B hd]
  exact div_lt_div_of_pos_left (responseTrace_pos N B hB) hc hcd

/-- The same scaling applies before differentiating the comparison. -/
def scaledBranchComparison (N : ℕ) (B c : ℝ) (i : Index N) (z : ℝ) : ℝ :=
  ∫ ω in (0 : ℝ)..frequencyEdge N B c i,
    scaledWeight N c i ω *
      cost (scaledKineticPrecision N c i ω / scaledPrecision N c i ω) z

theorem branchComparison_transport (N : ℕ) (B z : ℝ) {c : ℝ} (hc : 0 < c)
    (i : Index N) :
    scaledBranchComparison N B c i z = branchComparison N B i z / c := by
  simp only [scaledBranchComparison, frequencyEdge_transport N B hc,
    weight_transport N hc.ne', kinetic_fraction_transport N hc.ne']
  change (∫ ω in (0 : ℝ)..Real.sqrt (B - kinetic N i) / c,
    (fun u => weight N i u * cost (kineticFraction N i u) z) (c * ω)) = _
  have hchange := intervalIntegral.integral_comp_mul_left
    (fun u => weight N i u * cost (kineticFraction N i u) z) hc.ne'
    (a := (0 : ℝ)) (b := Real.sqrt (B - kinetic N i) / c)
  rw [hchange]
  have hu : c * (Real.sqrt (B - kinetic N i) / c) = Real.sqrt (B - kinetic N i) := by
    field_simp [hc.ne']
  rw [mul_zero, hu, smul_eq_mul]
  exact (div_eq_inv_mul _ _).symm

def scaledComparison (N : ℕ) (B c z : ℝ) : ℝ :=
  ∑ i ∈ support N B, scaledBranchComparison N B c i z

theorem comparison_transport (N : ℕ) (B z : ℝ) {c : ℝ} (hc : 0 < c) :
    scaledComparison N B c z = comparison N B z / c := by
  classical
  simp only [scaledComparison, branchComparison_transport N B z hc, Finset.sum_div,
    comparison]

theorem scaled_comparison_secondDeriv_zero (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun z => deriv (scaledComparison N B c) z)
      (scaledResponse N B c) 0 := by
  have he : scaledComparison N B c = fun z => comparison N B z / c :=
    funext (fun z => comparison_transport N B z hc)
  rw [he, response_transport N B hc]
  apply ((comparison_secondDeriv_zero N B).div_const c).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  rw [(comparison_hasDerivAt N B hz).deriv]
  exact ((comparison_hasDerivAt N B hz).div_const c).deriv

/-- Exact integration of the complete row decomposition survives the
coordinate change; the connection term is not normalized away. -/
theorem scaled_content_response (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    scaledResponse N B c = (HistoryHaarSectionContent.fieldResponse N B +
      ∑ j : Fin (HistoryHaarSectionContent.positionCount B),
        (HistoryAdjointCasimir.dimension N * (2 * j.val + 1) ^ 2 : ℕ) *
          positionIntegral N j.val B) / c := by
  rw [response_transport N B hc, HistoryHaarSectionContent.responseTrace_content_decomposition]

/-- Content testing is coordinate-independent, including the strict lower
edge and retained upper edge. Coordinate scaling cannot select a content
count that was absent from the original spectral window. -/
theorem scaled_response_content_test (N m : ℕ) {B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) :
    HistoryHaarSectionContent.positionCount B = m + 1 ↔
      scaledResponse N (Geometry.SourceScalarKineticForm.position m) c <
          scaledResponse N B c ∧
        scaledResponse N B c ≤
          scaledResponse N (Geometry.SourceScalarKineticForm.position (m + 1)) c := by
  simp only [response_transport N _ hc, div_lt_div_iff_of_pos_right hc,
    div_le_div_iff_of_pos_right hc]
  exact HistoryHaarSectionContent.response_characterizes_content_count N m hB

/-- The scale at a specified comparison level of the actual response.
This is a certificate coordinate, not an additional source normalization
or a statement that the source selects that comparison level. -/
def thresholdScale (N : ℕ) (B q : ℝ) : ℝ := responseTrace N B / q

theorem thresholdScale_nonneg (N : ℕ) {B q : ℝ} (hq : 0 < q) :
    0 ≤ thresholdScale N B q := by
  unfold thresholdScale responseTrace
  exact div_nonneg (Finset.sum_nonneg (fun i _ => branchIntegral_nonneg N B i)) hq.le

theorem thresholdScale_mono (N : ℕ) {q : ℝ} (hq : 0 < q) :
    Monotone (fun B => thresholdScale N B q) := by
  intro B C hBC
  exact (div_le_div_iff_of_pos_right hq).mpr (responseTrace_mono N hBC)

/-- Integer selection uses three distinct facts about the same source:
an actually excluded spectral label bounds the level above; a position
count bounds its response scale below; the certified lower crossing
connects that scale to the preceding integer. Neither the position count
nor the comparison level is asserted to be selected by this theorem.

In particular a response equation alone supplies none of these two bounds.
All spectral labels, positions and multiplicities remain those of the
complete joint Hessian. -/
theorem level_from_shell_content_and_crossing (N K R m : ℕ) {q : ℝ}
    (hq : 0 < q) (i : Index N)
    (hexcluded : i ∉ support N (R : ℝ))
    (hnext : kinetic N i < (K : ℝ) + 2)
    (hcontent : HistoryHaarSectionContent.positionCount
      (thresholdScale N (R : ℝ) q ^ 2) = m + 1)
    (hcross : thresholdScale N (K : ℝ) q ^ 2 ≤
      Geometry.SourceScalarKineticForm.position m) :
    R = K + 1 := by
  have hbound : (R : ℝ) ≤ kinetic N i := by
    by_contra h
    exact hexcluded ((mem_support N (R : ℝ) i).mpr (lt_of_not_ge h))
  have hRupper : R < K + 2 := by
    exact_mod_cast lt_of_le_of_lt hbound hnext
  have hpos : Geometry.SourceScalarKineticForm.position m <
      thresholdScale N (R : ℝ) q ^ 2 :=
    ((HistoryHaarSectionContent.positionCount_eq_succ_iff _ m).mp hcontent).1
  have hRlower : K < R := by
    by_contra h
    have hRK : (R : ℝ) ≤ K := by exact_mod_cast Nat.le_of_not_gt h
    have hmono := thresholdScale_mono N hq hRK
    have hnonneg := thresholdScale_nonneg N (B := (R : ℝ)) hq
    nlinarith
  omega

/-- The comparison level in this source-unit certificate is the already
generated total intensity. No normalization parameter is accepted.
The position and crossing premises still concern this explicit response;
an effective endpoint law is not inferred from the choice of comparison
units. -/
theorem source_unit_level_from_shell_content_and_crossing (N K R m : ℕ)
    (i : Index N) (hexcluded : i ∉ support N (R : ℝ))
    (hnext : kinetic N i < (K : ℝ) + 2)
    (hcontent : HistoryHaarSectionContent.positionCount
      (thresholdScale N (R : ℝ) (HistoryGaussianCovariance.generatedIntensity N) ^ 2) = m + 1)
    (hcross : thresholdScale N (K : ℝ) (HistoryGaussianCovariance.generatedIntensity N) ^ 2 ≤
      Geometry.SourceScalarKineticForm.position m) :
    R = K + 1 :=
  level_from_shell_content_and_crossing N K R m
    (HistoryGaussianCovariance.generatedIntensity_pos N) i hexcluded hnext hcontent hcross

structure Conclusions : Prop where
  kinetic_and_restoring : ∀ N c i,
    scaledEigenvalue N c i = scaledKinetic N c i + scaledRestoring N c i
  same_source_support : ∀ N B c, 0 < c → ∀ i,
    (scaledKinetic N c i < B / c ^ 2 ↔ i ∈ support N B)
  same_frequency_window : ∀ N B c, 0 < c → ∀ i ω,
    (scaledKineticPrecision N c i ω < B / c ^ 2 ↔ kineticPrecision N i (c * ω) < B)
  actual_branch_jacobian : ∀ N B c, 0 < c → ∀ i,
    scaledBranchIntegral N B c i = branchIntegral N B i / c
  complete_response_jacobian : ∀ N B c, 0 < c →
    scaledResponse N B c = responseTrace N B / c
  complete_comparison_jacobian : ∀ N B c, 0 < c → ∀ z,
    scaledComparison N B c z = comparison N B z / c
  actual_scaled_variation : ∀ N B c, 0 < c →
    HasDerivAt (fun z => deriv (scaledComparison N B c) z) (scaledResponse N B c) 0
  exact_scale_composition : ∀ N B c d, 0 < c → 0 < d →
    scaledResponse N B (c * d) = scaledResponse N B c / d
  same_content_test : ∀ N m B c, 0 ≤ B → 0 < c →
    (HistoryHaarSectionContent.positionCount B = m + 1 ↔
      scaledResponse N (Geometry.SourceScalarKineticForm.position m) c <
          scaledResponse N B c ∧
        scaledResponse N B c ≤
          scaledResponse N (Geometry.SourceScalarKineticForm.position (m + 1)) c)
  source_unit_joint_level_certificate : ∀ (N K R m : ℕ) (i : Index N),
    i ∉ support N (R : ℝ) → kinetic N i < (K : ℝ) + 2 →
    HistoryHaarSectionContent.positionCount
      (thresholdScale N (R : ℝ) (HistoryGaussianCovariance.generatedIntensity N) ^ 2) = m + 1 →
    thresholdScale N (K : ℝ) (HistoryGaussianCovariance.generatedIntensity N) ^ 2 ≤
      Geometry.SourceScalarKineticForm.position m →
    R = K + 1

theorem generated : Conclusions where
  kinetic_and_restoring := scaled_source_response
  same_source_support := fun N B _ hc => source_support_transport N B hc
  same_frequency_window := fun N B _ hc => frequency_window_transport N B hc
  actual_branch_jacobian := fun N B _ hc => branchIntegral_transport N B hc
  complete_response_jacobian := fun N B _ hc => response_transport N B hc
  complete_comparison_jacobian := fun N B _ hc z => comparison_transport N B z hc
  actual_scaled_variation := fun N B _ hc => scaled_comparison_secondDeriv_zero N B hc
  exact_scale_composition := fun N B _ _ hc hd => response_scale_composition N B hc hd
  same_content_test := fun N m _ _ hB hc => scaled_response_content_test N m hB hc
  source_unit_joint_level_certificate := source_unit_level_from_shell_content_and_crossing

end GeneratedFoundations.Arithmetic.HistoryHaarSectionScale
