module

public import GeneratedFoundations.Spectral.CircleNormalization
public import Mathlib.Tactic.FieldSimp

/-!
# The complete cosine basis on the interval

The probability Haar Fourier basis is paired by reflection. Its even part is
transported to the actual interval `L²` space. Completeness follows from the
vanishing of all bilateral Fourier coefficients, independently of any claim
about a differential operator or its domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

theorem haarCircleReflection_fourier (n : ℤ) :
    haarCircleReflection L (fourierLp 2 n) = fourierLp 2 (-n) := by
  apply Lp.ext
  let μH : Measure (AddCircle (2 * L)) := AddCircle.haarAddCircle
  have hn : (fun z : AddCircle (2 * L) => fourierLp 2 n (-z)) =ᵐ[μH]
      fun z => fourier n (-z) :=
    (Measure.measurePreserving_neg μH).quasiMeasurePreserving.ae
      (p := fun z : AddCircle (2 * L) => fourierLp 2 n z = fourier n z)
      (coeFn_fourierLp 2 n)
  filter_upwards [haarCircleReflection_coe L (fourierLp 2 n), hn,
    coeFn_fourierLp 2 (-n)] with z hr hnz hm
  rw [hr, hnz, hm]
  simp only [fourier_apply, smul_neg, neg_smul]

theorem haarFourier_inner (i j : ℤ) :
    inner ℂ (fourierLp (T := 2 * L) 2 i) (fourierLp 2 j) =
      if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp orthonormal_fourier i j

def haarCosineMode : ℕ → HaarCircleL2 L
  | 0 => fourierLp 2 0
  | n + 1 => (Real.sqrt 2 : ℂ)⁻¹ •
      (fourierLp 2 (n + 1 : ℕ) + fourierLp 2 (-(n + 1 : ℕ) : ℤ))

theorem haarCosineMode_mem_even (n : ℕ) : haarCosineMode L n ∈ haarEvenCircleL2 L := by
  change haarCircleReflection L (haarCosineMode L n) - haarCosineMode L n = 0
  rw [sub_eq_zero]
  cases n with
  | zero => simp only [haarCosineMode, haarCircleReflection_fourier, neg_zero]
  | succ n =>
      simp only [haarCosineMode, map_smul, map_add, haarCircleReflection_fourier, neg_neg]
      rw [add_comm]

lemma sqrt_two_inv_normalization :
    conj ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ * 2 = 1 := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hc : conj ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by simp
  rw [hc, ← mul_inv, hs]
  norm_num

theorem haarCosineMode_orthonormal : Orthonormal ℂ (haarCosineMode L) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  cases i with
  | zero =>
      cases j with
      | zero =>
          simpa only [haarCosineMode, ite_true] using haarFourier_inner L 0 0
      | succ j =>
          have hj : (0 : ℤ) < (j + 1 : ℕ) := by omega
          have hzero : (0 : ℤ) ≠ (j + 1 : ℕ) := ne_of_lt hj
          have hneg : (0 : ℤ) ≠ -(j + 1 : ℕ) := by omega
          have hnat : (0 : ℕ) ≠ j + 1 := by omega
          simp only [haarCosineMode, inner_smul_right, inner_add_right, haarFourier_inner,
            hzero, hneg, hnat, ite_false, add_zero, mul_zero]
  | succ i =>
      have hi : (0 : ℤ) < (i + 1 : ℕ) := by omega
      cases j with
      | zero =>
          have hzero : ((i + 1 : ℕ) : ℤ) ≠ 0 := ne_of_gt hi
          have hneg : (-(i + 1 : ℕ) : ℤ) ≠ 0 := by omega
          have hnat : i + 1 ≠ (0 : ℕ) := by omega
          simp only [haarCosineMode, inner_smul_left, inner_add_left, haarFourier_inner,
            hzero, hneg, hnat, ite_false, add_zero, mul_zero]
      | succ j =>
          have hj : (0 : ℤ) < (j + 1 : ℕ) := by omega
          have hcross : ((i + 1 : ℕ) : ℤ) ≠ -(j + 1 : ℕ) := by omega
          have hcross' : (-(i + 1 : ℕ) : ℤ) ≠ (j + 1 : ℕ) := by omega
          by_cases hij : i = j
          · subst j
            simp only [haarCosineMode, inner_smul_left, inner_smul_right,
              inner_add_left, inner_add_right, haarFourier_inner, hcross, hcross',
              ite_true, ite_false, mul_one, add_zero, zero_add]
            calc
              _ = conj ((Real.sqrt 2 : ℂ)⁻¹) * (Real.sqrt 2 : ℂ)⁻¹ * 2 := by ring
              _ = 1 := sqrt_two_inv_normalization
          · have hij' : ((i + 1 : ℕ) : ℤ) ≠ (j + 1 : ℕ) := by omega
            have hneg : (-(i + 1 : ℕ) : ℤ) ≠ -(j + 1 : ℕ) := by omega
            have hnat : i + 1 ≠ j + 1 := by omega
            simp only [haarCosineMode, inner_smul_left, inner_smul_right,
              inner_add_left, inner_add_right, haarFourier_inner,
              hij', hneg, hcross, hcross', hnat, ite_false, mul_zero, add_zero]

theorem haarEven_fourier_inner_neg (f : HaarCircleL2 L)
    (hf : f ∈ haarEvenCircleL2 L) (n : ℤ) :
    inner ℂ (fourierLp 2 (-n)) f = inner ℂ (fourierLp 2 n) f := by
  have heven : haarCircleReflection L f = f := by
    change haarCircleReflection L f - f = 0 at hf
    exact sub_eq_zero.mp hf
  calc
    _ = inner ℂ (haarCircleReflection L (fourierLp 2 n)) (haarCircleReflection L f) := by
      rw [haarCircleReflection_fourier, heven]
    _ = _ := (haarCircleReflection L).inner_map_map _ _

theorem haarEven_eq_zero_of_cosine_inner (f : HaarCircleL2 L)
    (hf : f ∈ haarEvenCircleL2 L) (hzero : ∀ n, inner ℂ (haarCosineMode L n) f = 0) :
    f = 0 := by
  have hpos (n : ℕ) : inner ℂ (fourierLp 2 (n + 1 : ℕ)) f = 0 := by
    have h := hzero (n + 1)
    simp only [haarCosineMode, inner_smul_left, inner_add_left,
      haarEven_fourier_inner_neg L f hf] at h
    have hc : conj ((Real.sqrt 2 : ℂ)⁻¹) ≠ 0 := by
      have hconj : conj ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by simp
      rw [hconj]
      apply inv_ne_zero
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have hsum := (mul_eq_zero.mp h).resolve_left hc
    have htwo : (2 : ℂ) * inner ℂ (fourierLp 2 (n + 1 : ℕ)) f = 0 := by
      simpa only [two_mul] using hsum
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hall (n : ℤ) : inner ℂ (fourierLp 2 n) f = 0 := by
    cases n with
    | ofNat n =>
        cases n with
        | zero => exact hzero 0
        | succ n => exact hpos n
    | negSucc n =>
        have hneg := haarEven_fourier_inner_neg L f hf (n + 1 : ℕ)
        simpa only [Int.natCast_add, Int.natCast_one, Int.negSucc_eq] using hneg.trans (hpos n)
  apply (fourierBasis (T := 2 * L)).repr.injective
  apply lp.ext
  funext n
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  rw [show fourierBasis (T := 2 * L) n = fourierLp 2 n from congrFun coe_fourierBasis n]
  simpa only [inner_zero_right] using hall n

def neumannCosineMode (n : ℕ) : ComplexIntervalL2 0 L :=
  (reflectingHaar_unitary L).symm ⟨haarCosineMode L n, haarCosineMode_mem_even L n⟩

theorem reflectingHaar_neumannCosineMode (n : ℕ) :
    reflectingHaarIsometry L (neumannCosineMode L n) = haarCosineMode L n := by
  exact congrArg Subtype.val ((reflectingHaar_unitary L).apply_symm_apply
    ⟨haarCosineMode L n, haarCosineMode_mem_even L n⟩)

theorem neumannCosineMode_orthonormal : Orthonormal ℂ (neumannCosineMode L) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [← (reflectingHaarIsometry L).inner_map_map, reflectingHaar_neumannCosineMode,
    reflectingHaar_neumannCosineMode]
  exact orthonormal_iff_ite.mp (haarCosineMode_orthonormal L) i j

theorem neumannCosineMode_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range (neumannCosineMode L)))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have heven : reflectingHaarIsometry L f ∈ haarEvenCircleL2 L := by
    rw [← reflectingHaarIsometry_range_eq_even]
    exact ⟨f, rfl⟩
  have hz : reflectingHaarIsometry L f = 0 := by
    apply haarEven_eq_zero_of_cosine_inner L _ heven
    intro n
    rw [← reflectingHaar_neumannCosineMode, (reflectingHaarIsometry L).inner_map_map]
    exact (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span ⟨n, rfl⟩)
  apply (reflectingHaarIsometry L).injective
  simpa only [map_zero] using hz

/-- A complete basis of the actual interval space, obtained from the full circle Fourier basis. -/
def neumannCosineBasis : HilbertBasis ℕ ℂ (ComplexIntervalL2 0 L) :=
  HilbertBasis.mkOfOrthogonalEqBot (neumannCosineMode_orthonormal L)
    (neumannCosineMode_orthogonal_eq_bot L)

theorem coe_neumannCosineBasis : ⇑(neumannCosineBasis L) = neumannCosineMode L :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

theorem neumannCosineBasis_hasSum (f : ComplexIntervalL2 0 L) :
    HasSum (fun n => inner ℂ (neumannCosineMode L n) f • neumannCosineMode L n) f := by
  simpa only [HilbertBasis.repr_apply_apply, coe_neumannCosineBasis] using
    (neumannCosineBasis L).hasSum_repr f

def haarCosineValue : ℕ → AddCircle (2 * L) → ℂ
  | 0, _ => 1
  | n + 1, z => (Real.sqrt 2 : ℂ)⁻¹ *
      (fourier (n + 1 : ℕ) z + fourier (-(n + 1 : ℕ) : ℤ) z)

theorem haarCosineMode_coe (n : ℕ) :
    haarCosineMode L n =ᵐ[AddCircle.haarAddCircle] haarCosineValue L n := by
  cases n with
  | zero =>
      filter_upwards [coeFn_fourierLp (T := 2 * L) 2 0] with z hz
      change (fourierLp (T := 2 * L) 2 0 : HaarCircleL2 L) z = 1
      exact hz.trans fourier_zero
  | succ n =>
      filter_upwards [Lp.coeFn_smul (Real.sqrt 2 : ℂ)⁻¹
        (fourierLp (T := 2 * L) 2 (n + 1 : ℕ) + fourierLp 2 (-(n + 1 : ℕ) : ℤ)),
        Lp.coeFn_add (fourierLp (T := 2 * L) 2 (n + 1 : ℕ))
          (fourierLp 2 (-(n + 1 : ℕ) : ℤ)),
        coeFn_fourierLp (T := 2 * L) 2 (n + 1 : ℕ),
        coeFn_fourierLp (T := 2 * L) 2 (-(n + 1 : ℕ) : ℤ)] with z hs ha hp hm
      change (((Real.sqrt 2 : ℂ)⁻¹ •
        (fourierLp 2 (n + 1 : ℕ) + fourierLp 2 (-(n + 1 : ℕ) : ℤ))) : HaarCircleL2 L) z = _
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hs ha
      rw [hs, ha, hp, hm]
      rfl

theorem haarCircle_ae_interval {p : AddCircle (2 * L) → Prop}
    (hp : ∀ᵐ z ∂AddCircle.haarAddCircle, p z) :
    ∀ᵐ (x : ℝ) ∂intervalMeasure 0 L, p (x : AddCircle (2 * L)) := by
  have hh := (circle_ae_half_iff_haar L).mpr hp
  have hv : ∀ᵐ z ∂(volume : Measure (AddCircle (2 * L))), p z :=
    (Measure.ae_ennreal_smul_measure_iff (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0)).mp hh
  have hi : ∀ᵐ (x : ℝ) ∂intervalMeasure (-L) L, p (x : AddCircle (2 * L)) :=
    (circle_quotient_measurePreserving L).quasiMeasurePreserving.ae hv
  apply ae_restrict_of_ae_restrict_of_subset (s := Icc 0 L) (t := Icc (-L) L) _ hi
  intro x hx
  exact ⟨(neg_nonpos.mpr hL.out.le).trans hx.1, hx.2⟩

theorem neumannCosineMode_coe (n : ℕ) :
    neumannCosineMode L n =ᵐ[intervalMeasure 0 L]
      fun x => (Real.sqrt L : ℂ)⁻¹ * haarCosineValue L n (x : AddCircle (2 * L)) := by
  have hr := reflectingHaarIsometry_coe L (neumannCosineMode L n)
  rw [reflectingHaar_neumannCosineMode] at hr
  have hri := haarCircle_ae_interval L hr
  have hci := haarCircle_ae_interval L (haarCosineMode_coe L n)
  have hs : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hL.out).ne'
  filter_upwards [hri, hci, ae_restrict_mem measurableSet_Icc] with x hrx hcx hx
  have hnorm : ‖(x : AddCircle (2 * L))‖ = x := by
    rw [circle_norm_coe L x ⟨(neg_nonpos.mpr hL.out.le).trans hx.1, hx.2⟩,
      abs_of_nonneg hx.1]
  rw [hnorm, hcx] at hrx
  rw [hrx, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

theorem neumannCosineMode_zero_coe :
    neumannCosineMode L 0 =ᵐ[intervalMeasure 0 L] fun _ => (Real.sqrt L : ℂ)⁻¹ := by
  simpa only [haarCosineValue, mul_one] using neumannCosineMode_coe L 0

theorem haarCosineValue_succ_coe (n : ℕ) (x : ℝ) :
    haarCosineValue L (n + 1) (x : AddCircle (2 * L)) =
      (Real.sqrt 2 : ℂ) * (Real.cos ((n + 1 : ℕ) * Real.pi * x / L) : ℂ) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
  let a : ℝ := (n + 1 : ℕ) * Real.pi * x / L
  have hp : fourier (n + 1 : ℕ) (x : AddCircle (2 * L)) =
      Complex.exp ((a : ℂ) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp only [a]
    push_cast
    field_simp [hLc]
  have hm : fourier (-(n + 1 : ℕ) : ℤ) (x : AddCircle (2 * L)) =
      Complex.exp (-(a : ℂ) * Complex.I) := by
    rw [fourier_coe_apply]
    congr 1
    dsimp only [a]
    push_cast
    field_simp [hLc]
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hinv : (Real.sqrt 2 : ℂ)⁻¹ * 2 = (Real.sqrt 2 : ℂ) := by
    rw [← hs, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  change (Real.sqrt 2 : ℂ)⁻¹ * (_ + _) = (Real.sqrt 2 : ℂ) * (Real.cos a : ℂ)
  rw [hp, hm, ← Complex.two_cos, ← Complex.ofReal_cos, ← mul_assoc, hinv]

theorem neumannCosineMode_succ_coe (n : ℕ) :
    neumannCosineMode L (n + 1) =ᵐ[intervalMeasure 0 L]
      fun x => (Real.sqrt L : ℂ)⁻¹ * (Real.sqrt 2 : ℂ) *
        (Real.cos ((n + 1 : ℕ) * Real.pi * x / L) : ℂ) := by
  filter_upwards [neumannCosineMode_coe L (n + 1)] with x hx
  rw [hx, haarCosineValue_succ_coe]
  exact (mul_assoc _ _ _).symm

end GeneratedFoundations.Spectral
