module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Smooth integration with a compact parameter

The integration variable may range over a compact manifold. Only the kernel
is differentiated; a continuous coefficient in the integration variable need
not be smooth. This distinction permits smoothing a continuous character of
an already specified Lie group without assuming its smoothness in advance.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology Manifold ContDiff

namespace GeneratedFoundations.Source.CompactParameterIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  {μ : Measure K} [IsFiniteMeasure μ]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [T2Space K]
  [SecondCountableTopology K] [CompleteSpace F] in
theorem continuousOn_integral {U : Set E} {f : E → K → F}
    (hf : ContinuousOn (uncurry f) (U ×ˢ univ)) :
    ContinuousOn (fun x => ∫ k, f x k ∂μ) U := by
  exact continuousOn_integral_of_compact_support isCompact_univ hf
    (fun _ k _ hk => (hk (mem_univ k)).elim)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompactSpace K] [T2Space K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
  [NormedSpace ℝ F] [CompleteSpace F] in
theorem continuous_section {U : Set E} {f : E → K → F}
    (hf : ContinuousOn (uncurry f) (U ×ˢ univ)) {x : E} (hx : x ∈ U) :
    Continuous (f x) := by
  exact hf.comp_continuous (continuous_const.prodMk continuous_id)
    (fun k => ⟨hx, mem_univ k⟩)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [T2Space K]
  [SecondCountableTopology K] [NormedSpace ℝ F] [CompleteSpace F] in
theorem integrable_section {U : Set E} {f : E → K → F}
    (hf : ContinuousOn (uncurry f) (U ×ˢ univ)) {x : E} (hx : x ∈ U) :
    Integrable (f x) μ :=
  (continuous_section hf hx).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [T2Space K] [CompleteSpace F] in
/-- Joint continuity of the parameter derivative supplies the domination
required to differentiate an integral, by compactness of a small closed ball
times the integration space. No derivative of the measure is used. -/
theorem hasFDerivAt_integral {U : Set E} (hU : IsOpen U)
    {f : E → K → F} {f' : E → K → E →L[ℝ] F}
    (hf : ContinuousOn (uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (uncurry f') (U ×ˢ univ))
    (hderiv : ∀ x ∈ U, ∀ k, HasFDerivAt (fun y => f y k) (f' x k) x)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ k, f y k ∂μ) (∫ k, f' x k ∂μ) x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hhalf : 0 < ε / 2 := half_pos hε
  have hclosed : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hcompact : IsCompact (Metric.closedBall x (ε / 2) ×ˢ (univ : Set K)) :=
    (isCompact_closedBall x (ε / 2)).prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hf'.mono (Set.prod_mono hclosed Subset.rfl))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds x hhalf)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (continuous_section hf hy).aestronglyMeasurable
  · exact integrable_section hf hx
  · exact (continuous_section hf' hx).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun k y hy =>
      hC (y, k) ⟨Metric.ball_subset_closedBall hy, mem_univ k⟩
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun k y hy => hderiv y
      (hclosed (Metric.ball_subset_closedBall hy)) k

section ManifoldKernel

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {N : Type*} [TopologicalSpace N] {I : ModelWithCorners ℝ H N}
  [ChartedSpace N K] [IsManifold I ∞ K]

omit [FiniteDimensional ℝ E] [CompactSpace K] [T2Space K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- Differentiating only the vector-space variable preserves joint smoothness
in that variable and in the compact manifold parameter. -/
theorem contMDiffOn_partial_fderiv {U : Set E} (hU : IsOpen U)
    {κ : E → K → ℝ} {n : ℕ}
    (hκ : ContMDiffOn ((𝓘(ℝ, E)).prod I) 𝓘(ℝ, ℝ) (n + 1)
      (uncurry κ) (U ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ, E)).prod I) 𝓘(ℝ, E →L[ℝ] ℝ) n
      (fun p : E × K => fderiv ℝ (fun y => κ y p.2) p.1) (U ×ˢ univ) := by
  intro p hp
  have hat : ContMDiffAt ((𝓘(ℝ, E)).prod I) 𝓘(ℝ, ℝ) (n + 1)
      (uncurry κ) p := hκ.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hp)
  have haux : ContMDiffAt (((𝓘(ℝ, E)).prod I).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ)
      (n + 1) (fun q : (E × K) × E => κ q.2 q.1.2) (p, p.1) := by
    exact hat.comp (p, p.1)
      ((contMDiffAt_snd (I := (𝓘(ℝ, E)).prod I) (J := 𝓘(ℝ, E))).prodMk
        ((contMDiffAt_snd (I := 𝓘(ℝ, E)) (J := I)).comp (p, p.1)
          (contMDiffAt_fst (I := (𝓘(ℝ, E)).prod I) (J := 𝓘(ℝ, E)))))
  have hd := haux.mfderiv (m := (n : ℕ∞ω))
    (fun q : E × K => fun y : E => κ y q.2)
    (fun q : E × K => q.1)
    (contMDiffAt_fst (I := 𝓘(ℝ, E)) (J := I)) (by simp)
  simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv] using
    hd.contMDiffWithinAt

omit [T2Space K] [CompleteSpace F] in
/-- Smooth real kernels can be integrated against a continuous vector-valued
coefficient. Finite-dimensionality is required only in the differentiated
variable, to control parameter derivatives on compact neighborhoods. -/
theorem contDiffOn_integral_smul {U : Set E} (hU : IsOpen U)
    {κ : E → K → ℝ} {w : K → F} (hw : Continuous w) (n : ℕ)
    (hκ : ContMDiffOn ((𝓘(ℝ, E)).prod I) 𝓘(ℝ, ℝ) n
      (uncurry κ) (U ×ˢ univ)) :
    ContDiffOn ℝ n (fun x => ∫ k, κ x k • w k ∂μ) U := by
  induction n generalizing κ with
  | zero =>
    simp only [Nat.cast_zero, contDiffOn_zero]
    exact continuousOn_integral (hκ.continuousOn.smul
      (hw.comp continuous_snd).continuousOn)
  | succ n ih =>
    let κ' : E → K → E →L[ℝ] ℝ := fun x k => fderiv ℝ (fun y => κ y k) x
    have hκ' := contMDiffOn_partial_fderiv hU hκ
    have hcκ : ContinuousOn (uncurry κ) (U ×ˢ univ) := hκ.continuousOn
    have hcκ' : ContinuousOn (uncurry κ') (U ×ˢ univ) := hκ'.continuousOn
    let f' : E → K → E →L[ℝ] F := fun x k => (κ' x k).smulRight (w k)
    have hcf' : ContinuousOn (uncurry f') (U ×ˢ univ) := by
      exact (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp_continuousOn
        (hcκ'.prodMk (hw.comp continuous_snd).continuousOn)
    have hderiv (x : E) (hx : x ∈ U) :
        HasFDerivAt (fun y => ∫ k, κ y k • w k ∂μ) (∫ k, f' x k ∂μ) x := by
      apply hasFDerivAt_integral hU
        (hcκ.smul (hw.comp continuous_snd).continuousOn) hcf' _ hx
      intro y hy k
      have hk : ContDiffAt ℝ (n + 1) (fun z => κ z k) y := by
        apply ContMDiffAt.contDiffAt
        exact (hκ.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, mem_univ k⟩)).comp y
          (contMDiffAt_id.prodMk contMDiffAt_const)
      exact (hk.differentiableAt (by simp)).hasFDerivAt.smul_const (w k)
    rw [show (↑(n + 1) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    intro v
    have hkv : ContMDiffOn ((𝓘(ℝ, E)).prod I) 𝓘(ℝ, ℝ) n
        (fun p : E × K => κ' p.1 p.2 v) (U ×ˢ univ) :=
      hκ'.clm_apply contMDiffOn_const
    apply (ih (κ := fun x k => κ' x k v) hkv).congr
    intro x hx
    rw [fderivWithin_of_mem_nhds (hU.mem_nhds hx), (hderiv x hx).fderiv,
      ContinuousLinearMap.integral_apply (integrable_section hcf' hx)]
    rfl

omit [T2Space K] [CompleteSpace F] in
theorem contDiffOn_integral_smul_infty {U : Set E} (hU : IsOpen U)
    {κ : E → K → ℝ} {w : K → F} (hw : Continuous w)
    (hκ : ContMDiffOn ((𝓘(ℝ, E)).prod I) 𝓘(ℝ, ℝ) ∞
      (uncurry κ) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x => ∫ k, κ x k • w k ∂μ) U := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_integral_smul hU hw n (hκ.of_le (by simp))

end ManifoldKernel

end GeneratedFoundations.Source.CompactParameterIntegral
