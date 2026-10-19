module

public import GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock

/-!
# Hodge splitting on the actual source coefficient blocks

The scalar potential and the coclosed projection are computed from the
source Casimir and the previously differentiated gradient and divergence.
Their orthogonality follows from the original Haar pairing. Thus the gauge
and coclosed sectors are obtained as subspaces of the same field block;
neither is introduced as an independent spectral model.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock

namespace GeneratedFoundations.Geometry.SourceOneFormHodgeBlock

def gradientOperator (m : ℕ) : HilbertCarrier m →ₗ[ℂ] FrameCarrier m where
  toFun a := WithLp.toLp 2 (coefficientGradient m a)
  map_add' a b := by
    apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier m)).injective
    funext i
    exact map_add (unitHilbertAxis m i) a b
  map_smul' c a := by
    apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier m)).injective
    funext i
    exact map_smul (unitHilbertAxis m i) c a

theorem divergence_gradient (m : ℕ) (a : HilbertCarrier m) :
    divergenceOperator m (gradientOperator m a) =
      -(((m : ℂ) * ((m : ℂ) + 2)) • a) :=
  coefficientDivergence_gradient m a

theorem curl_gradient (m : ℕ) (a : HilbertCarrier m) :
    curlOperator m (gradientOperator m a) = 0 := by
  apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier m)).injective
  exact coefficientCurl_gradient_zero m a

/-- Integration by parts is inherited from derivatives of the source
unitary action in the probability-Haar metric. -/
theorem gradient_divergence_pairing (m : ℕ) (a : HilbertCarrier m)
    (A : FrameCarrier m) :
    inner ℂ (gradientOperator m a) A = -inner ℂ a (divergenceOperator m A) := by
  change (∑ i : Fin 3, inner ℂ (unitHilbertAxis m i a) (A i)) =
    -inner ℂ a (∑ i : Fin 3, unitHilbertAxis m i (A i))
  calc
    _ = ∑ i : Fin 3, -inner ℂ a (unitHilbertAxis m i (A i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact eq_neg_of_add_eq_zero_left (unitAxis_skew_pairing m i a (A i))
    _ = _ := by simp [inner_sum]

/-- The differential definition of coclosedness agrees with orthogonality
to the full gradient range in the original field block. -/
theorem coclosed_eq_gradient_orthogonal (m : ℕ) :
    coclosedSpace m = (LinearMap.range (gradientOperator m))ᗮ := by
  ext A
  rw [(LinearMap.range (gradientOperator m)).mem_orthogonal]
  constructor
  · intro hA u hu
    obtain ⟨a, rfl⟩ := hu
    rw [gradient_divergence_pairing]
    have hdiv : divergenceOperator m A = 0 := hA
    rw [hdiv, inner_zero_right, neg_zero]
  · intro hA
    have h := hA (gradientOperator m (divergenceOperator m A))
      ⟨divergenceOperator m A, rfl⟩
    rw [gradient_divergence_pairing] at h
    exact inner_self_eq_zero.mp (neg_eq_zero.mp h)

private theorem casimir_ne_zero {m : ℕ} (hm : m ≠ 0) :
    (m : ℂ) * ((m : ℂ) + 2) ≠ 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hreal : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 2) := by positivity
  exact_mod_cast ne_of_gt hreal

theorem divergence_surjective {m : ℕ} (hm : m ≠ 0) :
    Function.Surjective (divergenceOperator m) := by
  intro a
  refine ⟨gradientOperator m (-(((m : ℂ) * ((m : ℂ) + 2))⁻¹ • a)), ?_⟩
  rw [divergence_gradient]
  simp only [smul_neg, smul_smul, neg_neg, mul_inv_cancel₀ (casimir_ne_zero hm), one_smul]

/-- The inverse scalar Casimir occurs only on the nonconstant gradient
range. At degree zero the gradient itself vanishes. -/
def scalarPotential (m : ℕ) (A : FrameCarrier m) : HilbertCarrier m :=
  -(((m : ℂ) * ((m : ℂ) + 2))⁻¹ • divergenceOperator m A)

def coclosedProjection (m : ℕ) : FrameCarrier m →ₗ[ℂ] FrameCarrier m :=
  LinearMap.id + (((m : ℂ) * ((m : ℂ) + 2))⁻¹) •
    ((gradientOperator m).comp (divergenceOperator m))

theorem gradient_potential_add_projection (m : ℕ) (A : FrameCarrier m) :
    gradientOperator m (scalarPotential m A) + coclosedProjection m A = A := by
  simp only [scalarPotential, coclosedProjection, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_neg, map_smul]
  module

theorem projection_coclosed (m : ℕ) (A : FrameCarrier m) :
    coclosedProjection m A ∈ coclosedSpace m := by
  change divergenceOperator m (coclosedProjection m A) = 0
  by_cases hm : m = 0
  · subst m
    simp [divergenceOperator, coefficientDivergence, unitAxis_degree_zero]
  · simp only [coclosedProjection, LinearMap.add_apply, LinearMap.id_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, map_add, map_smul,
      divergence_gradient, smul_neg, smul_smul,
      inv_mul_cancel₀ (casimir_ne_zero hm), one_smul, add_neg_cancel]

theorem projection_fixed (m : ℕ) (A : coclosedSpace m) :
    coclosedProjection m (A : FrameCarrier m) = A := by
  have hA : divergenceOperator m (A : FrameCarrier m) = 0 := A.property
  simp [coclosedProjection, hA]

theorem projection_idempotent (m : ℕ) (A : FrameCarrier m) :
    coclosedProjection m (coclosedProjection m A) = coclosedProjection m A :=
  projection_fixed m ⟨coclosedProjection m A, projection_coclosed m A⟩

theorem curl_projection (m : ℕ) (A : FrameCarrier m) :
    curlOperator m (coclosedProjection m A) = curlOperator m A := by
  have h := congrArg (curlOperator m) (gradient_potential_add_projection m A)
  rw [map_add, curl_gradient, zero_add] at h
  exact h

theorem hodge_parts_orthogonal (m : ℕ) (A : FrameCarrier m) :
    inner ℂ (gradientOperator m (scalarPotential m A)) (coclosedProjection m A) = 0 := by
  rw [gradient_divergence_pairing]
  have h : divergenceOperator m (coclosedProjection m A) = 0 := projection_coclosed m A
  rw [h, inner_zero_right, neg_zero]

/-- The complete block norm splits between the actual potential and
coclosed parts, without discarding an uncomputed mixed term. -/
theorem hodge_norm_sq (m : ℕ) (A : FrameCarrier m) :
    ‖A‖ ^ 2 = ‖gradientOperator m (scalarPotential m A)‖ ^ 2 +
      ‖coclosedProjection m A‖ ^ 2 := by
  calc
    ‖A‖ ^ 2 = ‖gradientOperator m (scalarPotential m A) + coclosedProjection m A‖ ^ 2 :=
      congrArg (fun x : FrameCarrier m => ‖x‖ ^ 2)
        (gradient_potential_add_projection m A).symm
    _ = _ := by
      simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (gradientOperator m (scalarPotential m A)) (coclosedProjection m A)
        (hodge_parts_orthogonal m A)

/-- The actual Hodge projection is contractive in the source Haar norm. -/
theorem projection_norm_sq_le (m : ℕ) (A : FrameCarrier m) :
    ‖coclosedProjection m A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  calc
    _ ≤ ‖gradientOperator m (scalarPotential m A)‖ ^ 2 +
        ‖coclosedProjection m A‖ ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg ‖gradientOperator m (scalarPotential m A)‖)
    _ = _ := (hodge_norm_sq m A).symm

/-- Curl controls precisely the nongauge component of the original field. -/
theorem curl_controls_projection {m : ℕ} (hm : Even m) (A : FrameCarrier m) :
    4 * ‖coclosedProjection m A‖ ^ 2 ≤ ‖curlOperator m A‖ ^ 2 := by
  have h := coclosedCurl_norm_sq_ge_four hm
    (⟨coclosedProjection m A, projection_coclosed m A⟩ : coclosedSpace m)
  change 4 * ‖coclosedProjection m A‖ ^ 2 ≤
    ‖curlOperator m (coclosedProjection m A)‖ ^ 2 at h
  simpa only [curl_projection] using h

/-- On the projective source, the entire null space consists of actual
gradients. No additional harmonic one-form sector is discarded. -/
theorem curl_kernel_eq_gradient_range {m : ℕ} (hm : Even m) :
    LinearMap.ker (curlOperator m) = LinearMap.range (gradientOperator m) := by
  ext A
  constructor
  · intro hA
    have hcurl : curlOperator m A = 0 := hA
    have hp : coclosedProjection m A = 0 := by
      have h := curl_controls_projection hm A
      rw [hcurl, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
      have hn : ‖coclosedProjection m A‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖coclosedProjection m A‖]
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    refine ⟨scalarPotential m A, ?_⟩
    simpa only [hp, add_zero] using gradient_potential_add_projection m A
  · rintro ⟨a, rfl⟩
    exact curl_gradient m a

end GeneratedFoundations.Geometry.SourceOneFormHodgeBlock
