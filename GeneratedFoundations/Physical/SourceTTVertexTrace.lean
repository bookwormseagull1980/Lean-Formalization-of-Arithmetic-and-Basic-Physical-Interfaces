module

public import GeneratedFoundations.Operations.ScalarVertexComparison
public import GeneratedFoundations.Physical.SourceTTMomentClosure

/-!
# Same-vertex comparisons in the full retained source trace

The actual Gaussian partition is evaluated for each branch and frequency,
then normalized by the unchanged vertex in its pure kinetic reference.
Only after this normalization is the original eight-branch measure used.
Its weights, frequency intervals and Gaussian envelope remain unchanged.

A vertex family is required to be nonzero on every positive-kinetic
block. This is an explicit comparison hypothesis, not an assertion about
spatial TT vertices. The constant spatial-gradient vertex is treated
separately in `SourceTTScalarFrameSupport` and does not satisfy it.
At zero kinetic precision the reference is replaced by the zero-capacity
extension; a degenerate Gaussian is not called a kinetic reference.
-/

@[expose] public section
noncomputable section
open MeasureTheory

namespace GeneratedFoundations.Physical.SourceTTVertexTrace

open Operations.ScalarVertexComparison
open SourceTTComparisonMeasure SourceTTMomentClosure

def kineticPrecision (x : Space) : ℝ := x.2 ^ 2 + SourceTTCapacitySpectrum.kinetic x.1

def massPrecision (x : Space) : ℝ := SourceTTCapacitySpectrum.mass x.1

theorem kineticPrecision_nonneg (x : Space) : 0 ≤ kineticPrecision x := by
  unfold kineticPrecision
  nlinarith [SourceTTCapacitySpectrum.kinetic_nonneg x.1, sq_nonneg x.2]

theorem massPrecision_pos (x : Space) : 0 < massPrecision x :=
  SourceTTCapacitySpectrum.mass_pos x.1

theorem precision_pos (x : Space) : 0 < kineticPrecision x + massPrecision x :=
  SourceTTCapacitySpectrum.precision_pos x.1 x.2

theorem capacity_formula (x : Space) :
    response x = massPrecision x * kineticPrecision x ^ 2 /
      (kineticPrecision x + massPrecision x) ^ 3 := by
  change massPrecision x / (kineticPrecision x + massPrecision x) *
    (1 - massPrecision x / (kineticPrecision x + massPrecision x)) ^ 2 = _
  field_simp [(precision_pos x).ne']
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each partial derivative belongs to the actual finite Gaussian
integral. The reference uses exactly the same eigenvalue list. -/
def normalizedVertexResponse (v : Space → ι → ℝ) (n : ℕ) (x : Space) : ℝ :=
  if n = 0 then 1 else
    if 0 < kineticPrecision x then
      ((iteratedDeriv (2 * n)
        (fun s => iteratedDeriv n (fun t => Real.log
          (actualPartition (v x) (kineticPrecision x + massPrecision x)
            (massPrecision x) s t)) 0) 0) / gaussianCoefficient (3 * n)) /
        ((iteratedDeriv (2 * n) (fun s => Real.log
          (actualPartition (v x) (kineticPrecision x) 0 s 0)) 0) /
            gaussianCoefficient (2 * n))
    else 0

/-- This condition records the precise domain of the same-vertex
normalization. No positivity of a zero reference is assumed. -/
def Visible (v : Space → ι → ℝ) : Prop :=
  ∀ x, 0 < kineticPrecision x → v x ≠ 0

theorem normalizedVertexResponse_eq_at {v : Space → ι → ℝ}
    (n : ℕ) (x : Space) (hv : 0 < kineticPrecision x → v x ≠ 0) :
    normalizedVertexResponse v n x = response x ^ n := by
  by_cases hn : n = 0
  · simp [normalizedVertexResponse, hn]
  · have hn' : 1 ≤ n := by omega
    by_cases hA : 0 < kineticPrecision x
    · rw [normalizedVertexResponse, ite_eq_right hn, ite_eq_left hA,
        actual_same_vertex_reference_ratio (hv hA) hA (precision_pos x) n hn',
        capacity_formula]
    · have hzero : kineticPrecision x = 0 :=
        le_antisymm (le_of_not_gt hA) (kineticPrecision_nonneg x)
      rw [normalizedVertexResponse, ite_eq_right hn, ite_eq_right hA, capacity_formula, hzero]
      simp [hn]

theorem normalizedVertexResponse_eq {v : Space → ι → ℝ} (hv : Visible v)
    (n : ℕ) (x : Space) :
    normalizedVertexResponse v n x = response x ^ n :=
  normalizedVertexResponse_eq_at n x (hv x)

/-- Vanishing vertices on null sets do not alter the original trace.
An entire omitted branch is not covered by this weaker condition. -/
def VisibleAE (v : Space → ι → ℝ) : Prop :=
  ∀ᵐ x ∂sourceMeasure, 0 < kineticPrecision x → v x ≠ 0

theorem normalizedVertexResponse_eq_ae {v : Space → ι → ℝ} (hv : VisibleAE v)
    (n : ℕ) :
    normalizedVertexResponse v n =ᵐ[sourceMeasure] fun x => response x ^ n := by
  filter_upwards [hv] with x hx
  exact normalizedVertexResponse_eq_at n x hx

/-- The zero-kinetic value is consistent with the continuous capacity
readout; no pure-kinetic Gaussian law is used at that point. -/
theorem normalizedVertexResponse_continuous {v : Space → ι → ℝ} (hv : Visible v)
    (n : ℕ) : Continuous (normalizedVertexResponse v n) := by
  have he : normalizedVertexResponse v n = fun x => response x ^ n :=
    funext (normalizedVertexResponse_eq hv n)
  rw [he]
  exact (continuous_pow n).comp response_continuous

/-- The integral of the actual response ratios, with the original
trace weights. This is not a ratio of two integrated responses. -/
def vertexTrace (v : Space → ι → ℝ) (n : ℕ) : ℝ :=
  ∫ x, normalizedVertexResponse v n x ∂sourceMeasure

theorem vertexTrace_eq_sourceMoment {v : Space → ι → ℝ} (hv : Visible v) (n : ℕ) :
    vertexTrace v n = sourceMoment n := by
  rw [vertexTrace, sourceMoment_eq_integral]
  exact integral_congr_ae (ae_of_all _ (normalizedVertexResponse_eq hv n))

theorem vertexTrace_eq_sourceMoment_ae {v : Space → ι → ℝ} (hv : VisibleAE v) (n : ℕ) :
    vertexTrace v n = sourceMoment n := by
  rw [vertexTrace, sourceMoment_eq_integral]
  exact integral_congr_ae (normalizedVertexResponse_eq_ae hv n)

/-- Positivity and complete response coverage are tested in the same
source algebra, after the actual same-vertex comparison. -/
def CompleteVertexReference (v : Space → ι → ℝ) (theta : ℝ) : Prop :=
  SourceTTCompleteComparisonClosure.PositiveReference theta ∧
    ∀ n, vertexTrace v (n + 1) ≤ theta * vertexTrace v n

theorem completeVertexReference_iff {v : Space → ι → ℝ} (hv : Visible v)
    (theta : ℝ) :
    CompleteVertexReference v theta ↔ CompleteMomentReference theta := by
  simp only [CompleteVertexReference, CompleteMomentReference,
    vertexTrace_eq_sourceMoment hv]

theorem completeVertexReference_iff_ae {v : Space → ι → ℝ} (hv : VisibleAE v)
    (theta : ℝ) :
    CompleteVertexReference v theta ↔ CompleteMomentReference theta := by
  simp only [CompleteVertexReference, CompleteMomentReference,
    vertexTrace_eq_sourceMoment_ae hv]

theorem complete_vertex_reference_sharp {v : Space → ι → ℝ} (hv : Visible v)
    (theta : ℝ) :
    CompleteVertexReference v theta ↔ theta = (4 / 27 : ℝ) := by
  rw [completeVertexReference_iff hv, completeMomentReference_iff]

theorem complete_vertex_endpoint_iff {v : Space → ι → ℝ} (hv : Visible v)
    {A c : ℝ} (hA : 0 < A) :
    (0 < c ∧ CompleteVertexReference v (A / c)) ↔
      c = SourceTensorResponseEndpoint.endpointRoot A := by
  rw [completeVertexReference_iff hv, source_comparison_closure_iff hA]

/-- The intensity insertion is already a quadratic observable of the
original coefficient; its comparison supplies an explicit visible family.
It is not identified here with a spatial-gradient tensor insertion. -/
def intensityVertex : Space → Fin 1 → ℝ := fun _ _ => 1

theorem intensityVertex_visible : Visible intensityVertex := by
  intro x _ h
  have he := congrFun h (0 : Fin 1)
  norm_num [intensityVertex] at he

theorem intensity_trace_eq_sourceMoment (n : ℕ) :
    vertexTrace intensityVertex n = sourceMoment n :=
  vertexTrace_eq_sourceMoment intensityVertex_visible n

/-- The same response criterion characterizes an operation at every
positive radius. The criterion is stated explicitly; no physical time
parameter or additional source update is introduced. -/
theorem operation_unique_from_vertex_responses {v : Space → ι → ℝ} (hv : Visible v)
    {A : ℝ} (hA : 0 < A) {F : ℝ → ℝ}
    (hF : ∀ c, 0 < c → 0 < F c ∧ CompleteVertexReference v (A / F c)) :
    ∀ c, 0 < c → F c = SourceTTNativeEndpoint.crossingUpdate A (4 / 27) c := by
  apply operation_unique_from_complete_responses hA
  intro c hc
  exact ⟨(hF c hc).1, (completeVertexReference_iff hv _).1 (hF c hc).2⟩

end GeneratedFoundations.Physical.SourceTTVertexTrace
