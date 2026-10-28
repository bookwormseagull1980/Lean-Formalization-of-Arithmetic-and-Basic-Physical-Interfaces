module

public import GeneratedFoundations.Physical.SourceTTEndpointBalance
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The least radius in the Gaussian TT response-realization class

Splitting a unit precision into a kinetic part `1-y` and a mass part `y`
leaves the actual Gaussian law unchanged. Its mass-weighted kinetic-score
response has range `[0, 4/27]`. This range is proved from the Gaussian
response formula; no matching level is supplied to the realization class.

The class below consists of radii whose spectral readout `A/c` can be
realized by such a split. Its least radius and its unique boundary split
are then determined. Applying this result to the full physical source
requires a separate identification of that source's admissible states
with this realization class, and a proof that its native update selects
the least boundary. The conditional transport theorem states both
requirements explicitly. Neither is added to the generated source root.

Weighted saturation and the quantitative defect bound test whether an
actual multimode reduction can attain the single-channel boundary. All
positive-weight mode fractions must equal one third for exact saturation.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceTTClosureBoundary

open Operations SourceTensorResponseEndpoint SourceTTResponseNormalization

/-- The original one-coordinate Gaussian at total precision one. -/
def splitLaw (y : ℝ) : Measure (FinitePrecisionGaussian.Space (Fin 1)) :=
  FinitePrecisionGaussian.law (fun _ => (1 - y) + y)

theorem splitLaw_eq_unit (y : ℝ) :
    splitLaw y = FinitePrecisionGaussian.law (fun _ : Fin 1 => (1 : ℝ)) := by
  unfold splitLaw
  congr 1
  funext i
  ring

/-- The mass fraction times twice the actual kinetic-score variance. -/
def splitResponse (y : ℝ) : ℝ := y * gaussianModeResponse (1 - y) y

theorem splitResponse_eq (y : ℝ) :
    splitResponse y = massWeightedResponse y := by
  rw [splitResponse, gaussianModeResponse_eq (1 - y) y (by linarith)]
  simp only [ttKernel, massWeightedResponse]
  congr 1
  have hp : (1 - y) + y = 1 := by ring
  rw [hp]
  norm_num

/-- Every value in the response interval is realized already on the lower
branch `0 <= y <= 1/3` of the original Gaussian comparison. -/
theorem exists_split_of_mem_range {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ (4 / 27 : ℝ)) :
    ∃ y ∈ Set.Icc (0 : ℝ) (1 / 3), splitResponse y = t := by
  have hc : Continuous (massWeightedResponse : ℝ → ℝ) := by
    unfold massWeightedResponse
    fun_prop
  have ht : t ∈ Set.Icc (massWeightedResponse 0) (massWeightedResponse (1 / 3)) := by
    constructor
    · simpa only [massWeightedResponse, zero_mul] using ht0
    · simpa only [massWeightedResponse_oneThird] using ht1
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 3)
    hc.continuousOn ht
  exact ⟨y, hy, by simpa only [splitResponse_eq] using he⟩

theorem split_response_range :
    splitResponse '' Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) (4 / 27) := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [splitResponse_eq]
    exact ⟨mul_nonneg hy.1 (sq_nonneg _), massWeightedResponse_le hy.1 hy.2⟩
  · intro ht
    obtain ⟨y, hy, he⟩ := exists_split_of_mem_range ht.1 ht.2
    exact ⟨y, ⟨hy.1, by linarith [hy.2]⟩, he⟩

/-- A response-realization class, rather than an assertion about which
states the physical source update reaches. Its definition has no threshold. -/
def Realizable (A c : ℝ) : Prop :=
  0 < c ∧ ∃ y ∈ Set.Icc (0 : ℝ) 1, A / c = splitResponse y

/-- The single-channel realization class has an exact closed lower edge. -/
theorem realizable_iff {A : ℝ} (hA : 0 < A) (c : ℝ) :
    Realizable A c ↔ endpointRoot A ≤ c := by
  constructor
  · rintro ⟨hc, y, hy, he⟩
    have hb : A / c ≤ (4 / 27 : ℝ) := by
      rw [he, splitResponse_eq]
      exact massWeightedResponse_le hy.1 hy.2
    have hm := (div_le_iff₀ hc).1 hb
    unfold endpointRoot
    linarith
  · intro he
    have hc : 0 < c := lt_of_lt_of_le (endpointRoot_pos hA) he
    have ht0 : 0 ≤ A / c := (div_pos hA hc).le
    have ht1 : A / c ≤ (4 / 27 : ℝ) := by
      apply (div_le_iff₀ hc).2
      unfold endpointRoot at he
      linarith
    obtain ⟨y, hy, hyresp⟩ := exists_split_of_mem_range ht0 ht1
    exact ⟨hc, y, ⟨hy.1, by linarith [hy.2]⟩, hyresp.symm⟩

theorem realizable_set {A : ℝ} (hA : 0 < A) :
    {c : ℝ | Realizable A c} = Set.Ici (endpointRoot A) := by
  ext c
  exact realizable_iff hA c

theorem least_realizable_radius {A : ℝ} (hA : 0 < A) :
    IsLeast {c : ℝ | Realizable A c} (endpointRoot A) := by
  rw [realizable_set hA]
  exact isLeast_Ici

theorem least_radius_unique {A c : ℝ} (hA : 0 < A)
    (hfirst : IsLeast {r : ℝ | Realizable A r} c) :
    c = endpointRoot A :=
  hfirst.unique (least_realizable_radius hA)

/-- Matching to the existing level is equivalent to being the least
member of the explicitly specified realization class. -/
theorem least_realizable_iff_matching {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    IsLeast {r : ℝ | Realizable A r} c ↔ A / c = (4 / 27 : ℝ) := by
  constructor
  · intro hfirst
    rw [least_radius_unique hA hfirst]
    exact sub_eq_zero.mp (endpointResidual_root hA)
  · intro hm
    have he := (endpointResidual_eq_zero_iff hA hc).1 (sub_eq_zero.mpr hm)
    rw [he]
    exact least_realizable_radius hA

/-- The separation from the least radius is exactly quadratic in the
departure of the realized mass fraction from one third. -/
theorem realization_radius_defect {A c y : ℝ} (hc : 0 < c)
    (hmatch : A / c = splitResponse y) :
    c - endpointRoot A =
      (27 * c / 4) * (y - 1 / 3) ^ 2 * (4 / 3 - y) := by
  rw [splitResponse_eq] at hmatch
  have he := (div_eq_iff hc.ne').1 hmatch
  rw [mul_assoc (27 * c / 4), ← response_factorization]
  unfold endpointRoot
  rw [he]
  ring

/-- At the least realizable radius the split is forced, not selected from
the two branches of the cubic by an additional convention. -/
theorem boundary_split_unique {A y : ℝ} (hA : 0 < A)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hmatch : A / endpointRoot A = splitResponse y) : y = 1 / 3 := by
  have hr : A / endpointRoot A = (4 / 27 : ℝ) :=
    sub_eq_zero.mp (endpointResidual_root hA)
  apply (massWeightedResponse_eq_critical_iff hy.1 hy.2).1
  rw [hr, splitResponse_eq] at hmatch
  exact hmatch.symm

/-- Identification with an actual source's admissible states and its least
boundary are the hypotheses needed to transport the result to that source. -/
theorem endpoint_of_source_realization {A c : ℝ} {Admissible : ℝ → Prop}
    (hA : 0 < A)
    (hreal : ∀ r : ℝ, Admissible r ↔ Realizable A r)
    (hfirst : IsLeast {r : ℝ | Admissible r} c) :
    c = endpointRoot A ∧ A / c = (4 / 27 : ℝ) := by
  have hs : {r : ℝ | Admissible r} = {r : ℝ | Realizable A r} := by
    ext r
    exact hreal r
  rw [hs] at hfirst
  have he := least_radius_unique hA hfirst
  refine ⟨he, ?_⟩
  rw [he]
  exact sub_eq_zero.mp (endpointResidual_root hA)

/-- A simultaneous positive change of source units preserves the entire
realization class, not only its least boundary. -/
theorem common_calibration_realizable {A c κ : ℝ} (hκ : 0 < κ) :
    (0 < c ∧ ∃ y ∈ Set.Icc (0 : ℝ) 1,
      κ * (A / c) = κ * splitResponse y) ↔ Realizable A c := by
  simp only [Realizable, mul_right_inj' hκ.ne']

theorem fixed_coefficient_boundary :
    IsLeast {c : ℝ | Realizable SourceTTGaussianCoefficient.coefficient c}
      SourceTTGaussianCoefficient.radius :=
  least_realizable_radius SourceTTGaussianCoefficient.coefficient_pos

/-! ## Equality and concentration in the actual weighted mode sum -/

variable {ι : Type*} [Fintype ι]

theorem weighted_saturation_iff (w y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, w i * massWeightedResponse (y i)) = (4 / 27 : ℝ) * ∑ i, w i ↔
      ∀ i, w i = 0 ∨ y i = 1 / 3 := by
  have hn (i : ι) : 0 ≤ w i * ((4 / 27 : ℝ) - massWeightedResponse (y i)) :=
    mul_nonneg (hw i) (sub_nonneg.mpr (massWeightedResponse_le (hy i).1 (hy i).2))
  have hsum : (∑ i, w i * ((4 / 27 : ℝ) - massWeightedResponse (y i))) =
      (4 / 27 : ℝ) * ∑ i, w i - ∑ i, w i * massWeightedResponse (y i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  constructor
  · intro he
    have hz : ∑ i, w i * ((4 / 27 : ℝ) - massWeightedResponse (y i)) = 0 := by
      rw [hsum, he, sub_self]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).1 hz
    intro i
    rcases mul_eq_zero.mp (hzero i (Finset.mem_univ i)) with hi | hi
    · exact Or.inl hi
    · right
      exact (massWeightedResponse_eq_critical_iff (hy i).1 (hy i).2).1
        (sub_eq_zero.mp hi).symm
  · intro he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rcases he i with hi | hi
    · simp [hi]
    · rw [hi, massWeightedResponse_oneThird, mul_comm]

/-- Distance of the mass fractions from the unique maximizing fraction is
controlled by the complete weighted response deficit. -/
theorem weighted_concentration (w y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, w i * (y i - 1 / 3) ^ 2) ≤
      3 * ((4 / 27 : ℝ) * ∑ i, w i - ∑ i, w i * massWeightedResponse (y i)) := by
  rw [SourceTTEndpointBalance.weighted_response_defect, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h0 : 0 ≤ w i * (y i - 1 / 3) ^ 2 := mul_nonneg (hw i) (sq_nonneg _)
  have h1 : (1 / 3 : ℝ) ≤ 4 / 3 - y i := by linarith [(hy i).2]
  have hm := mul_le_mul_of_nonneg_left h1 h0
  nlinarith

theorem weighted_response_strict_of_nonmaximal_mode (w y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, y i ∈ Set.Icc (0 : ℝ) 1)
    (i : ι) (hwi : 0 < w i) (hyi : y i ≠ 1 / 3) :
    (∑ j, w j * massWeightedResponse (y j)) < (4 / 27 : ℝ) * ∑ j, w j := by
  have hle := weighted_response_bound w y hw hy
  apply lt_of_le_of_ne hle
  intro he
  rcases (weighted_saturation_iff w y hw hy).1 he i with hi | hi
  · exact hwi.ne' hi
  · exact hyi hi

end GeneratedFoundations.Physical.SourceTTClosureBoundary
