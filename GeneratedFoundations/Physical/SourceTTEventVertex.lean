module

public import GeneratedFoundations.Geometry.SourceAxialEventTT
public import GeneratedFoundations.Operations.GaussianPrecisionRelativeCurvature
public import GeneratedFoundations.Physical.SourceTTVertexTrace

/-!
# Event-kinetic tensor comparison in the retained source trace

The existing Euclidean event derivative is varied by an actual coframe.
The tensor direction is transverse and trace-free in the off-shell
four-dimensional comparison space. Its temporal entry changes the
frequency kinetic term, including on the constant internal scalar branch.

The precision blocks and the eight-branch trace are unchanged. This is a
comparison of their positive real Gaussian precisions; no fermionic
determinant or interacting stress-tensor correlation is substituted for it.
At zero transfer the coframe is constant; the displayed nonzero axial
transfer specifies the transverse tensor direction, not a finite-transfer
correlation with a shifted second momentum.

The reference uses the same vertex in the same block. Its zero-frequency
zeros are null for the original measure. Thus the complete reference
criterion can be expressed by actual event-vertex comparisons. The final
uniqueness statements retain that criterion explicitly.
The coframe is compared against the fixed reference coframe; frequency
labels, the spectral envelope and the integration domain remain fixed.
Higher comparisons use independent linear insertions of the derived
first vertex and the mass. They generate its connected moments; higher
derivatives of the nonlinear coframe path retain their own direct terms.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GeneratedFoundations.Physical.SourceTTEventVertex

open SourceTTComparisonMeasure SourceTTMomentClosure SourceTTVertexTrace

def eventVertex (x : Space) : Fin 1 → ℝ := fun _ => x.2 ^ 2

/-- Each original frequency measure remains absolutely continuous;
the zero of the event derivative is a null point, not an omitted branch. -/
theorem branch_frequency_ne_zero_ae (i : SourceTTCapacitySpectrum.Branch) :
    ∀ᵐ u ∂branchMeasure i, u ≠ (0 : ℝ) := by
  have : NullSingletonClass (branchMeasure i) := by
    unfold branchMeasure
    infer_instance
  exact (branchMeasure i).ae_ne 0

theorem frequency_ne_zero_ae : ∀ᵐ x ∂sourceMeasure, x.2 ≠ (0 : ℝ) := by
  unfold sourceMeasure
  rw [ae_finsetSum_measure_iff]
  intro i _
  unfold placedMeasure
  rw [MeasureTheory.ae_map_iff
    (by fun_prop : Measurable (fun u : ℝ => (i, u))).aemeasurable
    (by measurability)]
  exact branch_frequency_ne_zero_ae i

theorem eventVertex_visible_ae : VisibleAE eventVertex := by
  filter_upwards [frequency_ne_zero_ae] with x hx
  intro _ hz
  have he := congrFun hz (0 : Fin 1)
  exact (pow_ne_zero 2 hx) (by simpa [eventVertex] using he)

/-- The vertex is the derivative of the actual event-coframe precision. -/
theorem eventVertex_from_precision (x : Space) :
    HasDerivAt
      (Geometry.SourceAxialEventTT.precision
        (SourceTTCapacitySpectrum.kinetic x.1) (massPrecision x) x.2)
      (eventVertex x 0) 0 := by
  simpa [eventVertex] using Geometry.SourceAxialEventTT.precision_hasDerivAt
    (SourceTTCapacitySpectrum.kinetic x.1) (massPrecision x) x.2 0

/-- The second vertex belongs to the same coframe square. -/
theorem event_direct_vertex (omega : ℝ) :
    HasDerivAt (Geometry.SourceAxialEventTT.firstVertex omega)
      (omega ^ 2 / 2) 0 :=
  Geometry.SourceAxialEventTT.firstVertex_hasDerivAt omega 0

theorem event_precision_path (a b omega s : ℝ) :
    Geometry.SourceAxialEventTT.precision a b omega s =
      Operations.GaussianPrecisionRelativeCurvature.pathPrecision
        (omega ^ 2 + a + b) (omega ^ 2) (omega ^ 2 / 2) s := by
  rw [Geometry.SourceAxialEventTT.precision_expansion]
  unfold Operations.GaussianPrecisionRelativeCurvature.pathPrecision
  ring

/-- Relative entropy of the actual two source laws along the coframe path. -/
def eventKL (a b omega s : ℝ) : ℝ :=
  (InformationTheory.klDiv
    (Operations.GaussianPrecisionKL.law (omega ^ 2 + a + b))
    (Operations.GaussianPrecisionKL.law
      (Geometry.SourceAxialEventTT.precision a b omega s))).toReal

def eventCurvature (p omega : ℝ) : ℝ := omega ^ 4 / (2 * p ^ 2)

/-- Both direct second vertices are retained in the actual relative
likelihood before their cancellation. -/
theorem actual_eventKL_secondDeriv {a b omega : ℝ}
    (hp : 0 < omega ^ 2 + a + b) :
    HasDerivAt (fun s => deriv (eventKL a b omega) s)
      (eventCurvature (omega ^ 2 + a + b) omega) 0 := by
  have he : eventKL a b omega = fun s =>
      (InformationTheory.klDiv
        (Operations.GaussianPrecisionKL.law (omega ^ 2 + a + b))
        (Operations.GaussianPrecisionKL.law
          (Operations.GaussianPrecisionRelativeCurvature.pathPrecision
            (omega ^ 2 + a + b) (omega ^ 2) (omega ^ 2 / 2) s))).toReal := by
    funext s
    rw [eventKL, event_precision_path]
  rw [he]
  rw [eventCurvature, show omega ^ 4 = (omega ^ 2) ^ 2 by ring]
  exact Operations.GaussianPrecisionRelativeCurvature.actualKL_secondDeriv_zero
    hp (omega ^ 2) (omega ^ 2 / 2)

theorem eventCurvature_pos {p omega : ℝ} (hp : 0 < p) (ho : omega ≠ 0) :
    0 < eventCurvature p omega := by
  have hfour : 0 < omega ^ 4 := by
    simpa only [← pow_mul, Nat.reduceMul] using pow_pos (sq_pos_of_ne_zero ho) 2
  exact div_pos hfour (by positivity)

/-- The comparison unit is itself the curvature of the original real
Gaussian law under a unit-frequency event coframe. -/
theorem canonical_eventKL_secondDeriv :
    HasDerivAt (fun s => deriv (eventKL 0 0 1) s) (1 / 2 : ℝ) 0 := by
  simpa [eventCurvature] using
    (actual_eventKL_secondDeriv (a := 0) (b := 0) (omega := 1) (by norm_num))

theorem pure_frequency_reference_unit {omega : ℝ} (ho : omega ≠ 0) :
    eventCurvature (omega ^ 2) omega = (1 / 2 : ℝ) := by
  unfold eventCurvature
  field_simp [pow_ne_zero 2 ho]

/-- Same coframe, same frequency, same internal shell, pure kinetic
reference. This is a blockwise ratio before taking the retained trace. -/
theorem event_reference_ratio (x : Space) (hx : x.2 ≠ 0) :
    eventCurvature (kineticPrecision x + massPrecision x) x.2 /
      eventCurvature (kineticPrecision x) x.2 =
        kineticPrecision x ^ 2 / (kineticPrecision x + massPrecision x) ^ 2 := by
  have hA : 0 < kineticPrecision x := by
    unfold kineticPrecision
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx)
      (SourceTTCapacitySpectrum.kinetic_nonneg x.1)
  unfold eventCurvature
  field_simp [hA.ne', (precision_pos x).ne', pow_ne_zero 4 hx]

/-- The capacity maximum is visible to this actual event vertex. -/
theorem event_vertex_at_peak :
    eventVertex (0, SourceTTCapacitySpectrum.peakFrequency) 0 = (3 / 2 : ℝ) :=
  SourceTTCapacitySpectrum.peakFrequency_sq

/-- The real Gaussian quadratic-response unit is one half. The mass leg
and the two kinetic legs are compared before the original trace is taken. -/
def eventHalfReadout (x : Space) : ℝ :=
  (1 / 2 : ℝ) * (massPrecision x / (kineticPrecision x + massPrecision x)) *
    (eventCurvature (kineticPrecision x + massPrecision x) x.2 /
      eventCurvature (kineticPrecision x) x.2)

theorem event_half_readout (x : Space) (hx : x.2 ≠ 0) :
    eventHalfReadout x = response x / 2 := by
  rw [eventHalfReadout, event_reference_ratio x hx, capacity_formula]
  field_simp [(precision_pos x).ne']

theorem event_half_readout_at_peak :
    eventHalfReadout (0, SourceTTCapacitySpectrum.peakFrequency) = (2 / 27 : ℝ) := by
  rw [event_half_readout _ (Real.sqrt_pos.2 (by norm_num)).ne']
  change SourceTTCapacitySpectrum.capacity 0 SourceTTCapacitySpectrum.peakFrequency / 2 = _
  rw [SourceTTCapacitySpectrum.capacity_first_peak]
  norm_num

theorem event_half_readout_ae :
    eventHalfReadout =ᵐ[sourceMeasure] fun x => response x / 2 := by
  filter_upwards [frequency_ne_zero_ae] with x hx
  exact event_half_readout x hx

theorem event_trace_eq_sourceMoment (n : ℕ) :
    vertexTrace eventVertex n = sourceMoment n :=
  vertexTrace_eq_sourceMoment_ae eventVertex_visible_ae n

theorem event_trace_ratio_tendsto :
    Tendsto (fun n : ℕ => vertexTrace eventVertex (n + 1) /
      vertexTrace eventVertex n) atTop (𝓝 (4 / 27 : ℝ)) := by
  simp only [event_trace_eq_sourceMoment, sourceMoment]
  exact trace_ratio_tendsto

theorem event_complete_reference_iff (theta : ℝ) :
    CompleteVertexReference eventVertex theta ↔ theta = (4 / 27 : ℝ) := by
  rw [completeVertexReference_iff_ae eventVertex_visible_ae,
    completeMomentReference_iff]

theorem event_endpoint_iff {A c : ℝ} (hA : 0 < A) :
    (0 < c ∧ CompleteVertexReference eventVertex (A / c)) ↔
      c = SourceTensorResponseEndpoint.endpointRoot A := by
  rw [completeVertexReference_iff_ae eventVertex_visible_ae,
    source_comparison_closure_iff hA]

theorem implemented_operation_event_complete {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    0 < SourceTTNativeEndpoint.crossingUpdate A (4 / 27) c ∧
      CompleteVertexReference eventVertex
        (A / SourceTTNativeEndpoint.crossingUpdate A (4 / 27) c) := by
  have h := implemented_operation_complete hA hc
  exact ⟨h.1, (completeVertexReference_iff_ae eventVertex_visible_ae _).2 h.2⟩

/-- The existing operation is characterized within the complete positive
reference class, without identifying comparison order with evolution. -/
theorem operation_unique_from_event_responses {A : ℝ} (hA : 0 < A)
    {F : ℝ → ℝ}
    (hF : ∀ c, 0 < c → 0 < F c ∧
      CompleteVertexReference eventVertex (A / F c)) :
    ∀ c, 0 < c → F c = SourceTTNativeEndpoint.crossingUpdate A (4 / 27) c := by
  apply operation_unique_from_complete_responses hA
  intro c hc
  exact ⟨(hF c hc).1,
    (completeVertexReference_iff_ae eventVertex_visible_ae _).1 (hF c hc).2⟩

end GeneratedFoundations.Physical.SourceTTEventVertex
