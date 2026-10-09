module

public import GeneratedFoundations.Operations.HermiteMoments
public import GeneratedFoundations.Operations.ZeroMoments
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Completeness of the actual Gaussian-generated Hermite family

An orthogonal vector has a Gaussian-weighted representative with vanishing
moments and absolute exponential control. Fourier uniqueness annihilates that
representative; positivity of the original Gaussian then annihilates the
original `L²` vector. Only after this density proof is the coefficient-space
isometry constructed. The basis vectors remain the generated Lebesgue
functions, not independently postulated sequence vectors.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped lp
open GeneratedFoundations.Correlation.ComplexGaussianStates
open GeneratedFoundations.Operations.HermiteMoments

namespace GeneratedFoundations.Operations.HermiteCompleteness

theorem eq_zero_of_orthogonal {b : ℝ} (hb : 0 < b) (F : ComplexL2)
    (hF : ∀ n, inner ℂ (HermiteFamily.state hb n) F = 0) : F = 0 := by
  apply eq_zero_of_weightedSource_ae_zero hb F
  exact ZeroMoments.ae_eq_zero_of_all_moments_eq_zero
    (weightedSource_integrable hb F)
    (fun r _ => weightedSource_exponential_integrable hb F r)
    (weightedSource_moments_eq_zero hb F hF)

theorem orthogonal_span_eq_bot {b : ℝ} (hb : 0 < b) :
    (Submodule.span ℂ (Set.range (HermiteFamily.state hb)))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro F hF
  change F = 0
  apply eq_zero_of_orthogonal hb F
  intro n
  exact (Submodule.mem_orthogonal _ _).mp hF _ (Submodule.subset_span ⟨n, rfl⟩)

/-- Density is proved in the original Lebesgue `L²` space. -/
theorem dense_span {b : ℝ} (hb : 0 < b) :
    (Submodule.span ℂ (Set.range (HermiteFamily.state hb))).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.mpr (orthogonal_span_eq_bot hb)

def basis {b : ℝ} (hb : 0 < b) : HilbertBasis ℕ ℂ ComplexL2 :=
  HilbertBasis.mkOfOrthogonalEqBot (HermiteFamily.state_orthonormal hb)
    (orthogonal_span_eq_bot hb)

@[simp] theorem basis_apply {b : ℝ} (hb : 0 < b) (n : ℕ) :
    basis hb n = HermiteFamily.state hb n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (HermiteFamily.state_orthonormal hb) (orthogonal_span_eq_bot hb)) n

/-- The sequence representation is an output of the genuine completeness proof. -/
def coefficients {b : ℝ} (hb : 0 < b) : ComplexL2 ≃ₗᵢ[ℂ] ℓ²(ℕ, ℂ) := (basis hb).repr

theorem coefficients_apply {b : ℝ} (hb : 0 < b) (F : ComplexL2) (n : ℕ) :
    coefficients hb F n = inner ℂ (HermiteFamily.state hb n) F := by
  exact (basis hb).repr_apply_apply F n |>.trans (by rw [basis_apply])

theorem coefficients_norm {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    ‖coefficients hb F‖ = ‖F‖ := (coefficients hb).norm_map F

/-- Every original vector is the norm-convergent sum of its source coefficients. -/
theorem hasSum_expansion {b : ℝ} (hb : 0 < b) (F : ComplexL2) :
    HasSum (fun n => inner ℂ (HermiteFamily.state hb n) F • HermiteFamily.state hb n) F := by
  simpa only [HilbertBasis.repr_apply_apply, basis_apply] using (basis hb).hasSum_repr F

theorem eq_of_coefficients_eq {b : ℝ} (hb : 0 < b) {F G : ComplexL2}
    (h : ∀ n, inner ℂ (HermiteFamily.state hb n) F = inner ℂ (HermiteFamily.state hb n) G) :
    F = G := by
  apply (coefficients hb).injective
  apply lp.ext
  funext n
  simpa only [coefficients_apply] using h n

end GeneratedFoundations.Operations.HermiteCompleteness
