module

public import GeneratedFoundations.Operations.SourceFiniteCornerAlgebra
public import GeneratedFoundations.Operations.GibbsConnectedResponse

/-!
# Capacity of the generated finite source corner

The differential ladder algebra, its real response spaces and the two Gibbs
response ranks refer to the same finite Hermite compression. The connected
source response has precisely the real scalar multiples of the corner
projection as its kernel.
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Operator

namespace GeneratedFoundations.Operations.SourceResponseCapacity

open SourceFiniteCornerAlgebra (Carrier sourceAnnihilator)
open PreparedTraceForm (Hermitian Traceless)

variable {b : ℝ} (hb : 0 < b) (n : ℕ) (t : ℝ)

/-- The complete finite capacity statement on the original Gaussian corner. -/
theorem finiteCorner_responseCapacity :
    StarAlgebra.adjoin ℂ ({sourceAnnihilator hb n} :
      Set (Carrier hb n →ₗ[ℂ] Carrier hb n)) = ⊤ ∧
    Module.finrank ℂ (Carrier hb n →ₗ[ℂ] Carrier hb n) = (n + 1) ^ 2 ∧
    Module.finrank ℝ (Hermitian (FiniteLadderAlgebra.Index n)) = (n + 1) ^ 2 ∧
    Module.finrank ℝ (Traceless (FiniteLadderAlgebra.Index n)) = (n + 1) ^ 2 - 1 ∧
    Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (GibbsFiniteResponse.sourceResponse n t hb) 0).toLinearMap) =
        (n + 1) ^ 2 ∧
    (∀ K : Hermitian (FiniteLadderAlgebra.Index n),
      0 ≤ fderiv ℝ (fderiv ℝ (GibbsConnectedResponse.sourceResponse hb n t)) 0 K K) ∧
    (∀ K : Hermitian (FiniteLadderAlgebra.Index n),
      (∀ L : Hermitian (FiniteLadderAlgebra.Index n),
        fderiv ℝ (fderiv ℝ (GibbsConnectedResponse.sourceResponse hb n t)) 0 K L = 0) ↔
      ∃ r : ℝ, SourceFiniteLadder.corner hb n (K : FiniteLadderAlgebra.Mat n) =
        r • SourceFiniteLadder.projection hb n) ∧
    Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (fderiv ℝ (GibbsConnectedResponse.sourceResponse hb n t)) 0).toLinearMap) =
        (n + 1) ^ 2 - 1 := by
  refine ⟨SourceFiniteCornerAlgebra.adjoin_sourceAnnihilator_eq_top hb n,
    SourceFiniteCornerAlgebra.finrank_endomorphisms hb n, ?_, ?_,
    GibbsFiniteResponse.sourceResponse_fderiv_range_finrank n t hb,
    GibbsConnectedResponse.sourceResponse_hessian_nonneg hb n t,
    GibbsConnectedResponse.sourceResponse_hessian_kernel_iff hb n t,
    GibbsConnectedResponse.sourceResponse_hessian_range_finrank hb n t⟩
  · simpa only [FiniteLadderAlgebra.Index, Fintype.card_fin] using
      PreparedTraceForm.finrank_hermitian (FiniteLadderAlgebra.Index n)
  · simpa only [FiniteLadderAlgebra.Index, Fintype.card_fin] using
      PreparedTraceForm.finrank_traceless (FiniteLadderAlgebra.Index n)

end GeneratedFoundations.Operations.SourceResponseCapacity
