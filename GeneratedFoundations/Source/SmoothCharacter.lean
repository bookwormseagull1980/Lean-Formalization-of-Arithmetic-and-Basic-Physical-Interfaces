module

public import GeneratedFoundations.Source.CompactParameterIntegral
public import GeneratedFoundations.Source.MinimalCarrier
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Automatic smoothness of continuous circle characters

All smoothness assertions refer to the given Lie-group atlas. A smooth bump
in that atlas is averaged against the continuous character. Haar invariance
identifies the resulting smooth function with a nonzero constant times the
character. Thus the argument does not replace the original Lie structure by
the one transported from its circle image.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology Manifold ContDiff

namespace GeneratedFoundations.Source.SmoothCharacter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [SecondCountableTopology G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G]
  [MeasurableSpace G] [BorelSpace G]

def average (μ : Measure G) (ψ : G → ℝ) (w : G → ℂ) (g : G) : ℂ :=
  ∫ h, ψ (g⁻¹ * h) • w h ∂μ

/-- Smoothness of the average differentiates the bump, never the continuous
coefficient. The original source charts supply the vector-space parameter. -/
theorem contMDiff_average {μ : Measure G} [IsFiniteMeasure μ]
    {ψ : G → ℝ} (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ψ)
    {w : G → ℂ} (hw : Continuous w) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (average μ ψ w) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ, E) ∞
  have hc : Continuous (average μ ψ w) := by
    apply continuousOn_univ.mp
    exact continuousOn_integral_of_compact_support isCompact_univ
      ((hψ.continuous.comp (continuous_fst.inv.mul continuous_snd)).smul
        (hw.comp continuous_snd)).continuousOn
      (fun _ h _ hh => (hh (mem_univ h)).elim)
  rw [contMDiff_iff]
  refine ⟨hc, ?_⟩
  intro g z
  have hlocal : ContDiffOn ℝ ∞
      (fun x => ∫ h, ψ (((extChartAt 𝓘(ℝ, E) g).symm x)⁻¹ * h) • w h ∂μ)
      (extChartAt 𝓘(ℝ, E) g).target := by
    apply CompactParameterIntegral.contDiffOn_integral_smul_infty
      (I := 𝓘(ℝ, E)) (isOpen_extChartAt_target g) hw
    apply hψ.comp_contMDiffOn
    have hchart : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun p : E × G => (extChartAt 𝓘(ℝ, E) g).symm p.1)
        ((extChartAt 𝓘(ℝ, E) g).target ×ˢ univ) :=
      (contMDiffOn_extChartAt_symm g).comp contMDiffOn_fst
        (fun p hp => hp.1)
    exact hchart.inv.mul contMDiffOn_snd
  simpa [average, Function.comp_def, mfld_simps, chartAt_self_eq] using hlocal

omit [CompactSpace G] [T2Space G] [SecondCountableTopology G] in
theorem average_character [IsTopologicalGroup G] {μ : Measure G} [μ.IsMulLeftInvariant]
    (ψ : G → ℝ) (χ : G →* Circle) (g : G) :
    average μ ψ (fun h => (χ h : ℂ)) g =
      (χ g : ℂ) * (∫ h, ψ h • (χ h : ℂ) ∂μ) := by
  unfold average
  rw [← integral_mul_left_eq_self (μ := μ)
    (fun h => ψ (g⁻¹ * h) • (χ h : ℂ)) g]
  simp only [inv_mul_cancel_left, map_mul, Circle.coe_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun h => by
    simp only [Complex.real_smul]
    ring

/-- A sufficiently localized nonnegative bump has nonzero character mean.
The choice uses continuity at the identity and positivity of Haar measure on
nonempty open sets; it does not assume differentiability of the character. -/
theorem exists_bump_nonzero_mean {μ : Measure G} [IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] (χ : G →* Circle) (hχ : Continuous χ) :
    ∃ ψ : SmoothBumpFunction 𝓘(ℝ, E) (1 : G),
      (∫ h, ψ h • (χ h : ℂ) ∂μ) ≠ 0 := by
  have hχc : Continuous (fun h : G => (χ h : ℂ)) := continuous_subtype_val.comp hχ
  have hu : {h : G | (1 : ℝ) / 2 < (χ h : ℂ).re} ∈ 𝓝 (1 : G) := by
    apply (isOpen_lt continuous_const (Complex.continuous_re.comp hχc)).mem_nhds
    norm_num
  obtain ⟨ψ, _, hsupport⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (1 : G)).mem_iff.mp hu
  have hpcont : Continuous (fun h : G => ψ h * (χ h : ℂ).re) :=
    ψ.continuous.mul (Complex.continuous_re.comp hχc)
  have hpnonneg : 0 ≤ fun h : G => ψ h * (χ h : ℂ).re := by
    intro h
    by_cases hz : ψ h = 0
    · simp [hz]
    · have hmem : h ∈ tsupport ψ := subset_closure hz
      exact mul_nonneg (ψ.nonneg (x := h)) (le_of_lt (lt_trans (by norm_num) (hsupport hmem)))
  have hpos : 0 < ∫ h, ψ h * (χ h : ℂ).re ∂μ := by
    apply integral_pos_of_integrable_nonneg_nonzero hpcont
      (hpcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hpnonneg
      (x := (1 : G))
    simp
  have hi : Integrable (fun h : G => ψ h • (χ h : ℂ)) μ :=
    (ψ.continuous.smul hχc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨ψ, ?_⟩
  intro hz
  have hre : (∫ h, ψ h * (χ h : ℂ).re ∂μ) =
      (∫ h, ψ h • (χ h : ℂ) ∂μ).re := by
    simpa [Complex.real_smul] using integral_re hi
  rw [hz] at hre
  simp only [Complex.zero_re] at hre
  rw [hre] at hpos
  exact lt_irrefl 0 hpos

/-- A continuous circle character of a finite-dimensional compact Lie group
is smooth for the original Lie-group structure. -/
theorem contMDiff_coe_character (χ : G →* Circle) (hχ : Continuous χ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun g => (χ g : ℂ)) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ, E) ∞
  let μ : Measure G := Measure.haar
  obtain ⟨ψ, hψ⟩ := exists_bump_nonzero_mean (E := E) (μ := μ) χ hχ
  let A : ℂ := ∫ h, ψ h • (χ h : ℂ) ∂μ
  have hA : A ≠ 0 := hψ
  have hs := contMDiff_average (μ := μ) ψ.contMDiff
    (continuous_subtype_val.comp hχ)
  have hid : (fun g => average μ ψ (fun h => (χ h : ℂ)) g * A⁻¹) =
      (fun g => (χ g : ℂ)) := by
    funext g
    rw [average_character]
    change (χ g : ℂ) * A * A⁻¹ = _
    rw [mul_assoc, mul_inv_cancel₀ hA, mul_one]
  rw [← hid]
  have hscale : ContDiff ℝ ∞ (fun z : ℂ => z * A⁻¹) :=
    contDiff_id.mul contDiff_const
  exact hscale.comp_contMDiff hs

/-- The character in the minimal-carrier classification retains the atlas
of the original datum. Its continuity, not smoothness, is the input. -/
theorem minimalCarrier_character_smooth
    (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d) :
    ∃ (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle),
      ContMDiff (𝓡 d.groupDimension) 𝓘(ℝ, ℂ) ∞ (fun g => (χ g : ℂ)) ∧
        ∀ g v, e (d.action g v) = (χ g : ℂ) * e v := by
  obtain ⟨_, e, χ, hχ, _, hintertwine⟩ :=
    MinimalCarrier.minimalCarrier_classification d h
  borelize d.Changes
  exact ⟨e, χ, contMDiff_coe_character χ.toMonoidHom hχ, hintertwine⟩

end GeneratedFoundations.Source.SmoothCharacter
