module

public import GeneratedFoundations.Spectral.AngularGenerator

/-!
# Spectral channels of the original angular derivative

Each channel is the closed span of eigenspaces of the actual periodic
angular operator with eigenvalues in a prescribed real set. The Fourier
support description is then proved from the classification of that operator.
Its orthogonal projection is therefore specified by the original differential
data; the nonnegative labels are a derived description, not its definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ComplexConjugate LinearPMap Classical
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Spectral.AngularSpectralChannels

variable (L : ℝ) [hL : Fact (0 < L)]

def spectralVectors (S : Set ℝ) : Set (HaarCircleL2 L) :=
  {f | ∃ μ ∈ S, ∃ u : (AngularGenerator.operator L).domain,
    (u : HaarCircleL2 L) = f ∧ AngularGenerator.operator L u = (μ : ℂ) • f}

def spectralSubspace (S : Set ℝ) : Submodule ℂ (HaarCircleL2 L) :=
  (Submodule.span ℂ (spectralVectors L S)).topologicalClosure

theorem spectralSubspace_eq_fourier_span (S : Set ℝ) :
    spectralSubspace L S = (Submodule.span ℂ
      {f : HaarCircleL2 L | ∃ n : ℤ, (n : ℝ) ∈ S ∧ fourierLp 2 n = f}).topologicalClosure := by
  apply congrArg Submodule.topologicalClosure
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨μ, hμ, u, rfl, hu⟩
    by_cases hf : (u : HaarCircleL2 L) = 0
    · rw [hf]
      exact Submodule.zero_mem _
    obtain ⟨n, hn⟩ := (AngularGenerator.eigenvalue_iff L (μ : ℂ)).mp ⟨u, hf, hu⟩
    have hμn : μ = (n : ℝ) := Complex.ofReal_injective (by
      simpa only [Complex.ofReal_intCast] using hn)
    rw [hn] at hu
    obtain ⟨c, hc⟩ := (AngularGenerator.eigenvector_iff L n u).mp hu
    rw [hc]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨n, hμn ▸ hμ, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro f ⟨n, hn, rfl⟩
    apply Submodule.subset_span
    refine ⟨(n : ℝ), hn, ⟨fourierLp 2 n, AngularGenerator.fourier_mem_domain L n⟩, rfl, ?_⟩
    simpa only [Complex.ofReal_intCast] using AngularGenerator.operator_fourier L n

theorem fourier_mem_spectralSubspace (S : Set ℝ) {n : ℤ} (hn : (n : ℝ) ∈ S) :
    fourierLp (T := 2 * L) 2 n ∈ spectralSubspace L S := by
  rw [spectralSubspace_eq_fourier_span]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, hn, rfl⟩)

/-- This support criterion is deduced from the actual eigenspaces. -/
theorem mem_spectralSubspace_iff (S : Set ℝ) (f : HaarCircleL2 L) :
    f ∈ spectralSubspace L S ↔
      ∀ n : ℤ, (n : ℝ) ∉ S → inner ℂ (fourierLp 2 n) f = 0 := by
  constructor
  · intro hf n hn
    have hle : spectralSubspace L S ≤ (innerSL ℂ (fourierLp (T := 2 * L) 2 n)).ker := by
      rw [spectralSubspace_eq_fourier_span]
      apply Submodule.topologicalClosure_minimal _ _ (ContinuousLinearMap.isClosed_ker _)
      apply Submodule.span_le.mpr
      rintro g ⟨i, hi, rfl⟩
      change inner ℂ (fourierLp (T := 2 * L) 2 n) (fourierLp 2 i) = 0
      rw [haarFourier_inner, ite_eq_right]
      intro hni
      exact hn (hni.symm ▸ hi)
    exact hle hf
  · intro hf
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (AngularGenerator.eigenfunctions_complete L f)
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro n _
    by_cases hn : (n : ℝ) ∈ S
    · exact Submodule.smul_mem _ _ (fourier_mem_spectralSubspace L S hn)
    · rw [hf n hn, zero_smul]
      exact Submodule.zero_mem _

instance spectralSubspace_complete (S : Set ℝ) : CompleteSpace (spectralSubspace L S) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (spectralVectors L S)).topologicalClosure)

def spectralProjection (S : Set ℝ) : HaarCircleL2 L →L[ℂ] HaarCircleL2 L :=
  (spectralSubspace L S).starProjection

theorem spectralProjection_orthogonal (S : Set ℝ) : IsStarProjection (spectralProjection L S) :=
  isStarProjection_starProjection

theorem spectralProjection_range (S : Set ℝ) :
    (spectralProjection L S).range = spectralSubspace L S := Submodule.range_starProjection _

theorem spectralProjection_fourier (S : Set ℝ) (n : ℤ) :
    spectralProjection L S (fourierLp 2 n) =
      if (n : ℝ) ∈ S then fourierLp 2 n else 0 := by
  classical
  by_cases hn : (n : ℝ) ∈ S
  · rw [ite_eq_left hn]
    exact (spectralSubspace L S).starProjection_eq_self_iff.mpr
      (fourier_mem_spectralSubspace L S hn)
  · rw [ite_eq_right hn]
    have horth : fourierLp (T := 2 * L) 2 n ∈ (spectralSubspace L S)ᗮ := by
      apply (spectralSubspace L S).mem_orthogonal _ |>.mpr
      intro f hf
      exact inner_eq_zero_symm.mpr ((mem_spectralSubspace_iff L S f).mp hf n hn)
    exact congrArg (fun u : spectralSubspace L S => (u : HaarCircleL2 L))
      ((spectralSubspace L S).orthogonalProjectionOnto_apply_of_mem_orthogonal horth)

theorem spectralProjection_coefficients (S : Set ℝ) (f : HaarCircleL2 L) (n : ℤ) :
    inner ℂ (fourierLp 2 n) (spectralProjection L S f) =
      if (n : ℝ) ∈ S then inner ℂ (fourierLp 2 n) f else 0 := by
  classical
  change inner ℂ (fourierLp 2 n) ((spectralSubspace L S).starProjection f) = _
  rw [← (spectralSubspace L S).inner_starProjection_left_eq_right]
  change inner ℂ (spectralProjection L S (fourierLp 2 n)) f = _
  rw [spectralProjection_fourier]
  split_ifs <;> simp only [inner_zero_left]

theorem spectralSubspace_inter (S T : Set ℝ) :
    spectralSubspace L (S ∩ T) = spectralSubspace L S ⊓ spectralSubspace L T := by
  ext f
  rw [Submodule.mem_inf, mem_spectralSubspace_iff, mem_spectralSubspace_iff,
    mem_spectralSubspace_iff]
  constructor
  · intro h
    exact ⟨fun n hn => h n (fun hST => hn hST.1),
      fun n hn => h n (fun hST => hn hST.2)⟩
  · rintro ⟨hS, hT⟩ n hn
    by_cases hnS : (n : ℝ) ∈ S
    · exact hT n (fun hnT => hn ⟨hnS, hnT⟩)
    · exact hS n hnS

def positiveChannel : Submodule ℂ (HaarCircleL2 L) := spectralSubspace L (Ici 0)
def negativeChannel : Submodule ℂ (HaarCircleL2 L) := spectralSubspace L (Iic 0)
def strictPositiveChannel : Submodule ℂ (HaarCircleL2 L) := spectralSubspace L (Ioi 0)
def strictNegativeChannel : Submodule ℂ (HaarCircleL2 L) := spectralSubspace L (Iio 0)

instance positiveChannel_complete : CompleteSpace (positiveChannel L) :=
  inferInstanceAs (CompleteSpace (spectralSubspace L (Ici 0)))

instance negativeChannel_complete : CompleteSpace (negativeChannel L) :=
  inferInstanceAs (CompleteSpace (spectralSubspace L (Iic 0)))

theorem positiveChannel_mem_iff (f : HaarCircleL2 L) :
    f ∈ positiveChannel L ↔ ∀ n : ℤ, n < 0 → inner ℂ (fourierLp 2 n) f = 0 := by
  simp only [positiveChannel, mem_spectralSubspace_iff, mem_Ici, not_le,
    Int.cast_lt_zero]

theorem negativeChannel_mem_iff (f : HaarCircleL2 L) :
    f ∈ negativeChannel L ↔ ∀ n : ℤ, 0 < n → inner ℂ (fourierLp 2 n) f = 0 := by
  simp only [negativeChannel, mem_spectralSubspace_iff, mem_Iic, not_le,
    Int.cast_pos]

theorem zeroChannel_eq_constants :
    spectralSubspace L {0} = Submodule.span ℂ {fourierLp (T := 2 * L) 2 0} := by
  rw [spectralSubspace_eq_fourier_span]
  have hset : {f : HaarCircleL2 L | ∃ n : ℤ, (n : ℝ) ∈ ({0} : Set ℝ) ∧ fourierLp 2 n = f} =
      {fourierLp (T := 2 * L) 2 0} := by
    ext f
    simp only [Set.mem_ofPred_eq, mem_singleton_iff, Int.cast_eq_zero]
    constructor
    · rintro ⟨n, rfl, rfl⟩
      rfl
    · rintro rfl
      exact ⟨0, rfl, rfl⟩
  rw [hset]
  exact (Submodule.span ℂ {fourierLp (T := 2 * L) 2 0}).closed_of_finiteDimensional
    |>.submodule_topologicalClosure_eq

theorem positive_negative_intersection :
    positiveChannel L ⊓ negativeChannel L =
      Submodule.span ℂ {fourierLp (T := 2 * L) 2 0} := by
  rw [positiveChannel, negativeChannel, ← spectralSubspace_inter]
  have hset : (Ici (0 : ℝ)) ∩ Iic 0 = {0} := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Iic, mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => by simp [h]⟩
  rw [hset, zeroChannel_eq_constants]

theorem reflection_coefficients (f : HaarCircleL2 L) (n : ℤ) :
    inner ℂ (fourierLp 2 n) (haarCircleReflection L f) =
      inner ℂ (fourierLp 2 (-n)) f := by
  have h := (haarCircleReflection L).inner_map_map (fourierLp 2 (-n)) f
  simpa only [haarCircleReflection_fourier, neg_neg] using h

theorem reflection_involution (f : HaarCircleL2 L) :
    haarCircleReflection L (haarCircleReflection L f) = f := by
  apply EigenbasisClosure.eq_of_coefficients fourierBasis
  intro n
  simp only [coe_fourierBasis, reflection_coefficients, neg_neg]

theorem reflection_mem_domain (f : (AngularGenerator.operator L).domain) :
    haarCircleReflection L (f : HaarCircleL2 L) ∈ (AngularGenerator.operator L).domain := by
  rw [AngularGenerator.domain_iff_weighted_fourier]
  have h := ((AngularGenerator.domain_iff_weighted_fourier L _).mp f.property).comp_injective
    (neg_injective : Function.Injective (fun n : ℤ => -n))
  simpa only [Function.comp_def, reflection_coefficients, Int.cast_neg, neg_sq] using h

def reflectionDomain (f : (AngularGenerator.operator L).domain) :
    (AngularGenerator.operator L).domain := ⟨haarCircleReflection L f, reflection_mem_domain L f⟩

/-- Reflection reverses the same original differential operator and preserves
its full Sobolev domain. -/
theorem reflection_operator (f : (AngularGenerator.operator L).domain) :
    AngularGenerator.operator L (reflectionDomain L f) =
      -haarCircleReflection L (AngularGenerator.operator L f) := by
  apply EigenbasisClosure.eq_of_coefficients fourierBasis
  intro n
  simp only [coe_fourierBasis, AngularGenerator.coefficients, inner_neg_right,
    reflection_coefficients, Int.cast_neg, neg_mul, neg_neg, reflectionDomain]

theorem reflection_positive_iff (f : HaarCircleL2 L) :
    haarCircleReflection L f ∈ positiveChannel L ↔ f ∈ negativeChannel L := by
  rw [positiveChannel_mem_iff, negativeChannel_mem_iff]
  constructor
  · intro h n hn
    have hh := h (-n) (neg_neg_of_pos hn)
    simpa only [reflection_coefficients, neg_neg] using hh
  · intro h n hn
    rw [reflection_coefficients]
    exact h (-n) (neg_pos.mpr hn)

theorem reflection_positive_projection (f : HaarCircleL2 L) :
    haarCircleReflection L
      (spectralProjection L (Ici 0) (haarCircleReflection L f)) =
      spectralProjection L (Iic 0) f := by
  apply EigenbasisClosure.eq_of_coefficients fourierBasis
  intro n
  simp only [coe_fourierBasis, reflection_coefficients, spectralProjection_coefficients,
    reflection_coefficients, neg_neg, mem_Ici, mem_Iic, Int.cast_neg, neg_nonneg]

theorem strict_channel_decomposition (f : HaarCircleL2 L)
    (hf : (∫ z, f z ∂AddCircle.haarAddCircle) = 0) :
    spectralProjection L (Ioi 0) f + spectralProjection L (Iio 0) f = f := by
  apply EigenbasisClosure.eq_of_coefficients fourierBasis
  intro n
  simp only [coe_fourierBasis, inner_add_right, spectralProjection_coefficients,
    mem_Ioi, mem_Iio]
  rcases lt_trichotomy (0 : ℝ) (n : ℝ) with hn | hn | hn
  · rw [ite_eq_left hn, ite_eq_right (not_lt.mpr hn.le), add_zero]
  · have hn0 : n = 0 := by exact_mod_cast hn.symm
    subst n
    simp only [Int.cast_zero, lt_self_iff_false, ite_false, add_zero,
      AngularGenerator.zero_inner_integral, hf]
  · rw [ite_eq_right (not_lt.mpr hn.le), ite_eq_left hn, zero_add]

theorem disjoint_spectralSubspaces_orthogonal (S T : Set ℝ) (hST : Disjoint S T)
    {f g : HaarCircleL2 L} (hf : f ∈ spectralSubspace L S)
    (hg : g ∈ spectralSubspace L T) : inner ℂ f g = 0 := by
  rw [← (fourierBasis (T := 2 * L)).tsum_inner_mul_inner f g]
  calc
    _ = ∑' _ : ℤ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      simp only [coe_fourierBasis]
      by_cases hn : (n : ℝ) ∈ S
      · have hnT : (n : ℝ) ∉ T := fun hnT => Set.disjoint_left.mp hST hn hnT
        rw [(mem_spectralSubspace_iff L T g).mp hg n hnT, mul_zero]
      · rw [← inner_conj_symm f (fourierLp 2 n),
          (mem_spectralSubspace_iff L S f).mp hf n hn, map_zero, zero_mul]
    _ = 0 := tsum_zero

theorem strict_channels_orthogonal {f g : HaarCircleL2 L}
    (hf : f ∈ strictPositiveChannel L) (hg : g ∈ strictNegativeChannel L) :
    inner ℂ f g = 0 := by
  apply disjoint_spectralSubspaces_orthogonal L (Ioi 0) (Iio 0) _ hf hg
  exact Set.disjoint_left.mpr fun x hx hy => (lt_asymm hx hy)

end GeneratedFoundations.Spectral.AngularSpectralChannels
