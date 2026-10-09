module

public import GeneratedFoundations.Spectral.NeumannScaleTransport
public import GeneratedFoundations.Spectral.PhysicalWindowOperator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Spatial realization of the Neumann scale transport

Positive spatial dilation transports the actual restricted Lebesgue
measures. Multiplication by the square root of the measure ratio gives a
linear isometry of the original interval L2 spaces. Its inverse is the
opposite dilation, and its action on the normalized cosine modes identifies
it with the previously defined spectral unitary.

Composition with the existing interval translations gives the corresponding
affine formula on actual physical windows. No new operator domain or
spectral criterion is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace GeneratedFoundations.Spectral.NeumannSpatialScale

variable (L M : ℝ) [hL : Fact (0 < L)] [hM : Fact (0 < M)]

def coordinate (y : ℝ) : ℝ := (L / M) * y

def amplitude : ℂ := (Real.sqrt (L / M) : ℂ)

theorem ratio_pos : 0 < L / M := div_pos hL.out hM.out

theorem coordinate_preimage : coordinate L M ⁻¹' Icc 0 L = Icc 0 M := by
  ext y
  have hLM : (L / M) * M = L := div_mul_cancel₀ L hM.out.ne'
  change (0 ≤ (L / M) * y ∧ (L / M) * y ≤ L) ↔ (0 ≤ y ∧ y ≤ M)
  calc
    _ ↔ (L / M) * 0 ≤ (L / M) * y ∧ (L / M) * y ≤ (L / M) * M := by
      rw [mul_zero, hLM]
    _ ↔ _ := by simp only [mul_le_mul_iff_right₀ (ratio_pos L M)]

/-- The Jacobian scales the integration measure in the pullback coordinate. -/
theorem coordinate_measurePreserving :
    MeasurePreserving (coordinate L M)
      (ENNReal.ofReal (L / M) • intervalMeasure 0 M) (intervalMeasure 0 L) := by
  have hvol : MeasurePreserving (coordinate L M)
      (ENNReal.ofReal (L / M) • (volume : Measure ℝ)) volume := by
    refine ⟨measurable_const_mul _, ?_⟩
    change Measure.map (fun x : ℝ => (L / M) * x)
      (ENNReal.ofReal (L / M) • volume) = volume
    rw [Measure.map_smul _ (measurable_const_mul (L / M)).aemeasurable]
    simpa only [abs_of_pos (ratio_pos L M)] using
      Real.smul_map_volume_mul_left (ratio_pos L M).ne'
  simpa only [intervalMeasure, coordinate_preimage, Measure.restrict_smul] using
    hvol.restrict_preimage (s := Icc 0 L) measurableSet_Icc

theorem coordinate_ae {p : ℝ → Prop}
    (hp : ∀ᵐ x ∂intervalMeasure 0 L, p x) :
    ∀ᵐ y ∂intervalMeasure 0 M, p (coordinate L M y) :=
  (Measure.ae_ennreal_smul_measure_iff
    (ne_of_gt (ENNReal.ofReal_pos.mpr (ratio_pos L M)))).mp
      ((coordinate_measurePreserving L M).quasiMeasurePreserving.ae hp)

theorem coordinate_inverse (x : ℝ) : coordinate L M (coordinate M L x) = x := by
  dsimp only [coordinate]
  field_simp [hL.out.ne', hM.out.ne']

theorem amplitude_inverse : amplitude M L * amplitude L M = 1 := by
  have hratio : (M / L) * (L / M) = 1 := by
    field_simp [hL.out.ne', hM.out.ne']
  simp only [amplitude, ← Complex.ofReal_mul,
    ← Real.sqrt_mul (ratio_pos M L).le, hratio, Real.sqrt_one, Complex.ofReal_one]

theorem amplitude_square : conj (amplitude L M) * amplitude L M = (L / M : ℝ) := by
  simp only [amplitude, Complex.conj_ofReal, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (Real.mul_self_sqrt (ratio_pos L M).le)

theorem amplitude_normalization :
    amplitude L M * (Real.sqrt L : ℂ)⁻¹ = (Real.sqrt M : ℂ)⁻¹ := by
  have hLs : (Real.sqrt L : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hL.out).ne'
  have hMs : (Real.sqrt M : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM.out).ne'
  simp only [amplitude, Real.sqrt_div hL.out.le M, Complex.ofReal_div]
  field_simp [hLs, hMs]

theorem pullback_memLp (f : ComplexIntervalL2 0 L) :
    MemLp (fun y => f (coordinate L M y)) 2 (intervalMeasure 0 M) := by
  have hf := (Lp.memLp f).comp_measurePreserving (coordinate_measurePreserving L M)
  have hc : ENNReal.ofReal (L / M) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (ratio_pos L M))
  have hi := hf.smul_measure (ENNReal.inv_ne_top.mpr hc)
  simpa only [Function.comp_def, smul_smul,
    ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul] using hi

/-- The spatial map is constructed from the actual representative pullback. -/
def spatialMap (f : ComplexIntervalL2 0 L) : ComplexIntervalL2 0 M :=
  ((pullback_memLp L M f).const_mul (amplitude L M)).toLp _

theorem spatialMap_coe (f : ComplexIntervalL2 0 L) :
    spatialMap L M f =ᵐ[intervalMeasure 0 M]
      fun y => amplitude L M * f (coordinate L M y) :=
  MemLp.coeFn_toLp _

theorem spatialMap_inverse (f : ComplexIntervalL2 0 L) :
    spatialMap M L (spatialMap L M f) = f := by
  apply Lp.ext
  have hp := coordinate_ae M L (spatialMap_coe L M f)
  filter_upwards [spatialMap_coe M L (spatialMap L M f), hp] with x hx hpx
  rw [hx, hpx, ← mul_assoc, amplitude_inverse, one_mul, coordinate_inverse]

def spatialLinearEquiv : ComplexIntervalL2 0 L ≃ₗ[ℂ] ComplexIntervalL2 0 M where
  toFun := spatialMap L M
  invFun := spatialMap M L
  left_inv := spatialMap_inverse L M
  right_inv := spatialMap_inverse M L
  map_add' f g := by
    apply Lp.ext
    have hadd := coordinate_ae L M (Lp.coeFn_add f g)
    filter_upwards [spatialMap_coe L M (f + g), spatialMap_coe L M f,
      spatialMap_coe L M g, hadd,
      Lp.coeFn_add (spatialMap L M f) (spatialMap L M g)] with y hsum hf hg hfg hout
    change spatialMap L M (f + g) y = (spatialMap L M f + spatialMap L M g) y
    simp only [Pi.add_apply] at hfg hout
    rw [hsum, hout, hf, hg, hfg]
    exact mul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    have hsmul := coordinate_ae L M (Lp.coeFn_smul c f)
    filter_upwards [spatialMap_coe L M (c • f), spatialMap_coe L M f,
      hsmul, Lp.coeFn_smul c (spatialMap L M f)] with y hcf hf hcf' hout
    change spatialMap L M (c • f) y = (c • spatialMap L M f) y
    simp only [Pi.smul_apply, smul_eq_mul] at hcf' hout
    rw [hcf, hout, hf, hcf']
    ring

theorem integral_coordinate (F : ℝ → ℂ) :
    (L / M : ℂ) * (∫ y, F (coordinate L M y) ∂intervalMeasure 0 M) =
      ∫ x, F x ∂intervalMeasure 0 L := by
  have h := (coordinate_measurePreserving L M).integral_comp
    (Homeomorph.mulLeft₀ (L / M) (ratio_pos L M).ne').toMeasurableEquiv.measurableEmbedding F
  have h' : ((L / M : ℝ) : ℂ) *
      (∫ y, F (coordinate L M y) ∂intervalMeasure 0 M) =
        ∫ x, F x ∂intervalMeasure 0 L := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal (ratio_pos L M).le] at h
    exact (Complex.real_smul (x := L / M)
      (z := ∫ y, F (coordinate L M y) ∂intervalMeasure 0 M)).symm.trans h
  exact (congrArg
    (fun c : ℂ => c * (∫ y, F (coordinate L M y) ∂intervalMeasure 0 M))
    (Complex.ofReal_div L M)).symm.trans h'

theorem spatialMap_inner (f g : ComplexIntervalL2 0 L) :
    inner ℂ (spatialMap L M f) (spatialMap L M g) = inner ℂ f g := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ y, inner ℂ (spatialMap L M f y) (spatialMap L M g y) ∂intervalMeasure 0 M) =
        ∫ y, (L / M : ℂ) * (conj (f (coordinate L M y)) * g (coordinate L M y))
          ∂intervalMeasure 0 M := by
      apply integral_congr_ae
      filter_upwards [spatialMap_coe L M f, spatialMap_coe L M g] with y hf hg
      rw [hf, hg, RCLike.inner_apply', map_mul]
      calc
        (conj (amplitude L M) * conj (f (coordinate L M y))) *
            (amplitude L M * g (coordinate L M y)) =
            (conj (amplitude L M) * amplitude L M) *
              (conj (f (coordinate L M y)) * g (coordinate L M y)) := by ring
        _ = _ := by rw [amplitude_square, Complex.ofReal_div]
    _ = (L / M : ℂ) * ∫ y, conj (f (coordinate L M y)) * g (coordinate L M y)
        ∂intervalMeasure 0 M := integral_const_mul _ _
    _ = ∫ x, inner ℂ (f x) (g x) ∂intervalMeasure 0 L := by
      simpa only [RCLike.inner_apply'] using
        integral_coordinate L M (fun x => conj (f x) * g x)

/-- The dilation is unitary before any appeal to spectral coordinates. -/
def spatialUnitary : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] ComplexIntervalL2 0 M :=
  (spatialLinearEquiv L M).isometryOfInner (spatialMap_inner L M)

theorem spatialUnitary_cosine (n : ℕ) :
    spatialUnitary L M (neumannCosineMode L n) = neumannCosineMode M n := by
  apply Lp.ext
  change spatialMap L M (neumannCosineMode L n) =ᵐ[intervalMeasure 0 M] neumannCosineMode M n
  cases n with
  | zero =>
      have hl := coordinate_ae L M (neumannCosineMode_zero_coe L)
      filter_upwards [spatialMap_coe L M (neumannCosineMode L 0), hl,
        neumannCosineMode_zero_coe M] with y hs hly hmy
      rw [hs, hly, hmy, amplitude_normalization]
  | succ n =>
      have hl := coordinate_ae L M (neumannCosineMode_succ_coe L n)
      filter_upwards [spatialMap_coe L M (neumannCosineMode L (n + 1)), hl,
        neumannCosineMode_succ_coe M n] with y hs hly hmy
      have hphase : (n + 1 : ℕ) * Real.pi * coordinate L M y / L =
          (n + 1 : ℕ) * Real.pi * y / M := by
        dsimp only [coordinate]
        field_simp [hL.out.ne', hM.out.ne']
      rw [hs, hly, hmy, hphase]
      simp only [← mul_assoc, amplitude_normalization]

theorem spatialUnitary_eq : spatialUnitary L M = NeumannScaleTransport.unitary L M :=
  NeumannScaleTransport.unitary_unique L M (spatialUnitary L M) (spatialUnitary_cosine L M)

theorem unitary_coe_coordinate (f : ComplexIntervalL2 0 L) :
    NeumannScaleTransport.unitary L M f =ᵐ[intervalMeasure 0 M]
      fun y => amplitude L M * f (coordinate L M y) := by
  rw [← spatialUnitary_eq]
  exact spatialMap_coe L M f

/-- The spectral scale transport has the usual spatial dilation formula. -/
theorem unitary_coe (f : ComplexIntervalL2 0 L) :
    NeumannScaleTransport.unitary L M f =ᵐ[intervalMeasure 0 M]
      fun y => (Real.sqrt (L / M) : ℂ) * f (L * y / M) := by
  simpa only [amplitude, coordinate, div_mul_eq_mul_div₀] using unitary_coe_coordinate L M f

/-- Translation, the existing scale transport, and inverse translation. -/
def windowAffineUnitary (a c : ℝ) :
    ComplexIntervalL2 a (a + L) ≃ₗᵢ[ℂ] ComplexIntervalL2 c (c + M) :=
  (shiftCanonicalL2Equiv (a := a) (L := L)).trans
    ((NeumannScaleTransport.unitary L M).trans
      (shiftCanonicalL2Equiv (a := c) (L := M)).symm)

theorem windowAffineUnitary_coe (a c : ℝ) (f : ComplexIntervalL2 a (a + L)) :
    windowAffineUnitary L M a c f =ᵐ[intervalMeasure c (c + M)]
      fun y => (Real.sqrt (L / M) : ℂ) * f (a + L * (y - c) / M) := by
  let f₀ : ComplexIntervalL2 0 L := shiftCanonicalL2Equiv (a := a) (L := L) f
  have hsource : f₀ =ᵐ[intervalMeasure 0 L] fun x => f (shiftRight a x) :=
    Lp.coeFn_compMeasurePreserving f (shiftRight_measurePreserving (a := a) (L := L))
  have hsource' := coordinate_ae L M hsource
  have hscaled := unitary_coe_coordinate L M f₀
  have hsourceLeft :=
    (shiftLeft_measurePreserving (a := c) (L := M)).quasiMeasurePreserving.ae hsource'
  have hscaledLeft :=
    (shiftLeft_measurePreserving (a := c) (L := M)).quasiMeasurePreserving.ae hscaled
  have hout : windowAffineUnitary L M a c f =ᵐ[intervalMeasure c (c + M)]
      fun y => NeumannScaleTransport.unitary L M f₀ (shiftLeft c y) :=
    Lp.coeFn_compMeasurePreserving (NeumannScaleTransport.unitary L M f₀)
      (shiftLeft_measurePreserving (a := c) (L := M))
  filter_upwards [hout, hscaledLeft, hsourceLeft] with y hy hs hf
  have hcoord : shiftRight a (coordinate L M (shiftLeft c y)) =
      a + L * (y - c) / M := by
    dsimp only [shiftRight, coordinate, shiftLeft]
    ring
  rw [hy, hs, hf, hcoord, amplitude]

/-- The same affine transport on the endpoints of two generated windows. -/
theorem generatedWindow_affine {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    ∃ U : ComplexIntervalL2 (windowLeft b) (windowRight b) ≃ₗᵢ[ℂ]
        ComplexIntervalL2 (windowLeft d) (windowRight d),
      ∀ f, U f =ᵐ[intervalMeasure (windowLeft d) (windowRight d)]
        fun y => (Real.sqrt (windowLengthGenerated b / windowLengthGenerated d) : ℂ) *
          f (windowLeft b + windowLengthGenerated b * (y - windowLeft d) /
            windowLengthGenerated d) := by
  let : Fact (0 < windowLengthGenerated b) := ⟨windowLengthGenerated_pos hb⟩
  let : Fact (0 < windowLengthGenerated d) := ⟨windowLengthGenerated_pos hd⟩
  have h : ∃ U :
      ComplexIntervalL2 (windowLeft b) (windowLeft b + windowLengthGenerated b) ≃ₗᵢ[ℂ]
        ComplexIntervalL2 (windowLeft d) (windowLeft d + windowLengthGenerated d),
      ∀ f, U f =ᵐ[intervalMeasure (windowLeft d) (windowLeft d + windowLengthGenerated d)]
        fun y => (Real.sqrt (windowLengthGenerated b / windowLengthGenerated d) : ℂ) *
          f (windowLeft b + windowLengthGenerated b * (y - windowLeft d) /
            windowLengthGenerated d) :=
    ⟨windowAffineUnitary (windowLengthGenerated b) (windowLengthGenerated d)
      (windowLeft b) (windowLeft d),
      windowAffineUnitary_coe (windowLengthGenerated b) (windowLengthGenerated d)
        (windowLeft b) (windowLeft d)⟩
  have heqb := windowLeft_add_length hb
  have heqd := windowLeft_add_length hd
  generalize windowLeft b + windowLengthGenerated b = cb at h heqb
  subst cb
  generalize windowLeft d + windowLengthGenerated d = cd at h heqd
  subst cd
  exact h

end GeneratedFoundations.Spectral.NeumannSpatialScale
