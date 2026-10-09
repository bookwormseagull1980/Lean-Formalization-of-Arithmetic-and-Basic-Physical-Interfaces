module

public import GeneratedFoundations.Correlation.GaussianCorrelation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
The real Gaussian states in complex `L²`. Mathlib's Hermitian inner product
is linear in the second slot. `sourceInner` uses the first-slot convention;
the two conventions give the same real Gaussian overlap.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Correlation.GaussianCorrelation

namespace GeneratedFoundations.Correlation.ComplexGaussianStates

abbrev RealL2 := Lp ℝ 2 (volume : Measure ℝ)

abbrev ComplexL2 := Lp ℂ 2 (volume : Measure ℝ)

def realEmbedding : RealL2 →L[ℝ] ComplexL2 := Complex.ofRealCLM.compLpL 2 volume

theorem realEmbedding_coe (f : RealL2) :
    realEmbedding f =ᵐ[volume] fun y => (f y : ℂ) := by
  simpa only [realEmbedding, Complex.ofRealCLM_apply] using Complex.ofRealCLM.coeFn_compLpL f

theorem realEmbedding_inner (f g : RealL2) :
    inner ℂ (realEmbedding f) (realEmbedding g) = (inner ℝ f g : ℂ) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ y : ℝ, inner ℂ (realEmbedding f y) (realEmbedding g y)) =
        ∫ y : ℝ, (inner ℝ (f y) (g y) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [realEmbedding_coe f, realEmbedding_coe g] with y hf hg
      rw [hf, hg]
      simp [RCLike.inner_apply]
    _ = (∫ y : ℝ, inner ℝ (f y) (g y) : ℝ) := integral_complex_ofReal

theorem realEmbedding_norm (f : RealL2) : ‖realEmbedding f‖ = ‖f‖ := by
  have h := congrArg Complex.re (realEmbedding_inner f f)
  change RCLike.re (inner ℂ (realEmbedding f) (realEmbedding f)) = inner ℝ f f at h
  rw [inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (realEmbedding f), norm_nonneg f]

def realEmbeddingIsometry : RealL2 →ₗᵢ[ℝ] ComplexL2 :=
  { realEmbedding.toLinearMap with norm_map' := realEmbedding_norm }

def complexState {b : ℝ} (hb : 0 < b) (x : ℝ) : ComplexL2 :=
  realEmbedding (hilbertState hb x)

theorem complexState_coe {b : ℝ} (hb : 0 < b) (x : ℝ) :
    complexState hb x =ᵐ[volume] fun y => (state b x y : ℂ) := by
  filter_upwards [realEmbedding_coe (hilbertState hb x), (state_memLp hb x).coeFn_toLp]
    with y hmap hstate
  change realEmbedding (hilbertState hb x) y = (state b x y : ℂ)
  rw [hmap]
  exact congrArg Complex.ofReal hstate

theorem complexState_inner {b : ℝ} (hb : 0 < b) (x z : ℝ) :
    inner ℂ (complexState hb x) (complexState hb z) = (profile b (x - z) : ℂ) := by
  rw [complexState, complexState, realEmbedding_inner, hilbertState_inner]

theorem complexState_norm {b : ℝ} (hb : 0 < b) (x : ℝ) : ‖complexState hb x‖ = 1 := by
  rw [complexState, realEmbedding_norm, hilbertState_norm]

def sourceInner (f g : ComplexL2) : ℂ := inner ℂ g f

theorem sourceInner_eq_conj (f g : ComplexL2) :
    sourceInner f g = star (inner ℂ f g) := (inner_conj_symm g f).symm

theorem sourceInner_smul_left (c : ℂ) (f g : ComplexL2) :
    sourceInner (c • f) g = c * sourceInner f g := by
  simp only [sourceInner, inner_smul_right]

theorem sourceInner_smul_right (c : ℂ) (f g : ComplexL2) :
    sourceInner f (c • g) = star c * sourceInner f g := by
  simp only [sourceInner, inner_smul_left, starRingEnd_apply]

theorem sourceInner_complexState {b : ℝ} (hb : 0 < b) (x z : ℝ) :
    sourceInner (complexState hb x) (complexState hb z) = (profile b (x - z) : ℂ) := by
  rw [sourceInner_eq_conj, complexState_inner]
  simp

end GeneratedFoundations.Correlation.ComplexGaussianStates
