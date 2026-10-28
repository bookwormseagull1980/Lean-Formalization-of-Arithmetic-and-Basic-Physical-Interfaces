module

public import GeneratedFoundations.Analysis.HistoryPrefixGibbsResponse
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Gaussian resolution of the complete prefix matrix response

The root square spectrum already fixes the retained half-density at every
history--phase label. Sandwiching by this diagonal matrix transports the
actual unnormalized reference intensity from alpha to alpha+t. Products and
the full matrix exponential do not commute with this resolution. Their
defects are retained below, without a Taylor expansion or a new source law.

The product-square defect is positive semidefinite. The exponential-response
compensation has its exact cocycle and unique residual law; no sign is
asserted for that general compensation. Resolution is a change of Gaussian
observation, not physical time or maximum-prime generation.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal ComplexOrder Matrix.Norms.Operator

namespace GeneratedFoundations.Analysis.HistoryPrefixResolution

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open GibbsExponentialDifferentiation (realDiagonal)
open HistoryPrefixGibbsResponse

def retained (N : ℕ) (L : ℝ) (t : ℝ≥0) (i : Index N) : ℝ :=
  gaussianRootMass ((t : ℝ) / 2) L (i.1.val + 1)

theorem retained_pos (N : ℕ) (L : ℝ) (t : ℝ≥0) (i : Index N) :
    0 < retained N L t i := gaussianRootMass_pos _ _ _

theorem retained_le_one (N : ℕ) (L : ℝ) (t : ℝ≥0) (i : Index N) :
    retained N L t i ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg t.property (by norm_num))) (sq_nonneg _)) (sq_nonneg L)

@[simp] theorem retained_zero (N : ℕ) (L : ℝ) (i : Index N) :
    retained N L 0 i = 1 := by simp [retained, gaussianRootMass]

theorem retained_add (N : ℕ) (L : ℝ) (s t : ℝ≥0) (i : Index N) :
    retained N L (s + t) i = retained N L s i * retained N L t i := by
  unfold retained gaussianRootMass
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem retained_intensity (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (i : Index N) :
    retained N L t i * intensity N alpha L i * retained N L t i =
      intensity N (alpha + (t : ℝ)) L i := by
  unfold retained intensity HistoryPhaseResponse.intensity gaussianRootMass
  have he : Real.exp (-((t : ℝ) / 2) * ((i.1.val + 1 : ℕ) : ℝ) ^ 2 / L ^ 2) *
      Real.exp (-alpha * ((i.1.val + 1 : ℕ) : ℝ) ^ 2 / L ^ 2) *
      Real.exp (-((t : ℝ) / 2) * ((i.1.val + 1 : ℕ) : ℝ) ^ 2 / L ^ 2) =
      Real.exp (-(alpha + (t : ℝ)) * ((i.1.val + 1 : ℕ) : ℝ) ^ 2 / L ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-((t : ℝ) / 2) * ((i.1.val + 1 : ℕ) : ℝ) ^ 2 / L ^ 2) *
        Real.exp (-alpha * ((i.1.val + 1 : ℕ) : ℝ) ^ 2 / L ^ 2) *
        Real.exp (-((t : ℝ) / 2) * ((i.1.val + 1 : ℕ) : ℝ) ^ 2 / L ^ 2)) *
        HistoryPhaseBundle.probability i.2 := by ring
    _ = _ := by rw [he]

def retentionMatrix (N : ℕ) (L : ℝ) (t : ℝ≥0) : Mat (Index N) :=
  realDiagonal (retained N L t)

@[simp] theorem retentionMatrix_star (N : ℕ) (L : ℝ) (t : ℝ≥0) :
    (retentionMatrix N L t).conjTranspose = retentionMatrix N L t := by
  simp [retentionMatrix, realDiagonal]

@[simp] theorem retentionMatrix_zero (N : ℕ) (L : ℝ) : retentionMatrix N L 0 = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [retentionMatrix, realDiagonal]
  · simp [retentionMatrix, realDiagonal, h]

def heat (N : ℕ) (L : ℝ) (t : ℝ≥0) : Mat (Index N) →ₗ[ℂ] Mat (Index N) where
  toFun K := retentionMatrix N L t * K * retentionMatrix N L t
  map_add' K J := by simp [mul_add, add_mul]
  map_smul' c K := by simp

theorem heat_apply (N : ℕ) (L : ℝ) (t : ℝ≥0) (K : Mat (Index N)) :
    heat N L t K = retentionMatrix N L t * K * retentionMatrix N L t := rfl

theorem heat_entry (N : ℕ) (L : ℝ) (t : ℝ≥0) (K : Mat (Index N)) (i j : Index N) :
    heat N L t K i j = (retained N L t i : ℂ) * K i j * (retained N L t j : ℂ) := by
  simp [heat, retentionMatrix, realDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]

@[simp] theorem heat_zero (N : ℕ) (L : ℝ) (K : Mat (Index N)) : heat N L 0 K = K := by
  simp [heat]

theorem heat_add (N : ℕ) (L : ℝ) (s t : ℝ≥0) (K : Mat (Index N)) :
    heat N L (s + t) K = heat N L s (heat N L t K) := by
  ext i j
  simp only [heat_entry, retained_add, Complex.ofReal_mul]
  ring

theorem heat_hermitian (N : ℕ) (L : ℝ) (t : ℝ≥0) {K : Mat (Index N)}
    (hK : K.IsHermitian) : (heat N L t K).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul (retentionMatrix N L t) hK
  simpa only [retentionMatrix_star, heat_apply] using h

theorem heat_positive (N : ℕ) (L : ℝ) (t : ℝ≥0) {K : Mat (Index N)}
    (hK : K.PosSemidef) : (heat N L t K).PosSemidef := by
  have h := hK.conjTranspose_mul_mul_same (retentionMatrix N L t)
  simpa only [retentionMatrix_star, heat_apply] using h

def observationHeat (N : ℕ) (L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)) : Hermitian (Index N) :=
  ⟨heat N L t (K : Mat (Index N)), (heat_hermitian N L t (hermitian_isHermitian _ K)).isSelfAdjoint⟩

@[simp] theorem observationHeat_zero (N : ℕ) (L : ℝ) (K : Hermitian (Index N)) :
    observationHeat N L 0 K = K := by
  apply Subtype.ext
  exact heat_zero N L K

theorem observationHeat_add (N : ℕ) (L : ℝ) (s t : ℝ≥0) (K : Hermitian (Index N)) :
    observationHeat N L (s + t) K = observationHeat N L s (observationHeat N L t K) := by
  apply Subtype.ext
  exact heat_add N L s t K

def reference (N : ℕ) (alpha L : ℝ) : Mat (Index N) :=
  realDiagonal (intensity N alpha L)

theorem reference_eq_exp (N : ℕ) (alpha L : ℝ) :
    reference N alpha L = NormedSpace.exp (realDiagonal (logIntensity N alpha L)) := by
  rw [GibbsExponentialDifferentiation.exp_realDiagonal]
  simp only [exp_logIntensity]
  rfl

/-- The existing unnormalized source, including its history law, is
transported exactly to the next Gaussian resolution. -/
theorem reference_transport (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) :
    heat N L t (reference N alpha L) = reference N (alpha + (t : ℝ)) L := by
  ext i j
  rw [heat_entry]
  by_cases h : i = j
  · subst j
    simpa only [reference, realDiagonal, Matrix.diagonal_apply_eq, ← Complex.ofReal_mul] using
      congrArg Complex.ofReal (retained_intensity N alpha L t i)
  · simp [reference, realDiagonal, h]

/-- The positive reference capacity remains the actual partition sum. -/
theorem reference_trace (N : ℕ) (alpha L : ℝ) :
    Matrix.trace (reference N alpha L) = (GibbsTraceForm.Z (logIntensity N alpha L) : ℂ) := by
  simp [reference, realDiagonal, Matrix.trace, GibbsTraceForm.Z, exp_logIntensity]

/-- Every lost channel is charged to the same reference intensity. -/
theorem capacity_loss (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) :
    GibbsTraceForm.Z (logIntensity N alpha L) -
        GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) =
      ∑ i, intensity N alpha L i * (1 - retained N L t i ^ 2) := by
  simp only [GibbsTraceForm.Z, exp_logIntensity, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← retained_intensity N alpha L t i]
  ring

theorem capacity_nonincreasing (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) :
    GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) ≤
      GibbsTraceForm.Z (logIntensity N alpha L) := by
  have h : 0 ≤ GibbsTraceForm.Z (logIntensity N alpha L) -
      GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) := by
    rw [capacity_loss]
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (le_of_lt (intensity_pos N alpha L i))
    nlinarith [retained_le_one N L t i, retained_pos N L t i]
  linarith

def normalizedReference (N : ℕ) (alpha L : ℝ) : Mat (Index N) :=
  ((GibbsTraceForm.Z (logIntensity N alpha L))⁻¹ : ℂ) • reference N alpha L

/-- The partition ratio is retained when the actual normalized state is
transported. Resolution does not silently replace that ratio by one. -/
theorem normalized_reference_transport (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) :
    heat N L t (normalizedReference N alpha L) =
      ((GibbsTraceForm.Z (logIntensity N (alpha + (t : ℝ)) L) /
        GibbsTraceForm.Z (logIntensity N alpha L) : ℝ) : ℂ) •
        normalizedReference N (alpha + (t : ℝ)) L := by
  rw [normalizedReference, map_smul, reference_transport, normalizedReference, smul_smul]
  congr 1
  push_cast
  field_simp [GibbsTraceForm.Z_ne_zero (logIntensity N (alpha + (t : ℝ)) L)]

def lost (N : ℕ) (L : ℝ) (t : ℝ≥0) : Mat (Index N) :=
  realDiagonal (fun i => 1 - retained N L t i ^ 2)

theorem lost_eq (N : ℕ) (L : ℝ) (t : ℝ≥0) :
    lost N L t = 1 - retentionMatrix N L t * retentionMatrix N L t := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [lost, retentionMatrix, realDiagonal, pow_two]
  · simp [lost, retentionMatrix, realDiagonal, h]

theorem lost_positive (N : ℕ) (L : ℝ) (t : ℝ≥0) : (lost N L t).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  change 0 ≤ ((1 - retained N L t i ^ 2 : ℝ) : ℂ)
  exact_mod_cast (show (0 : ℝ) ≤ 1 - retained N L t i ^ 2 by
    nlinarith [retained_le_one N L t i, retained_pos N L t i])

def productDefect (N : ℕ) (L : ℝ) (t : ℝ≥0) (K J : Mat (Index N)) : Mat (Index N) :=
  heat N L t (K * J) - heat N L t K * heat N L t J

/-- All intermediate channels remain in the exact nonlinear product defect. -/
theorem product_defect_eq (N : ℕ) (L : ℝ) (t : ℝ≥0) (K J : Mat (Index N)) :
    productDefect N L t K J = retentionMatrix N L t * K * lost N L t * J * retentionMatrix N L t := by
  rw [productDefect, lost_eq]
  simp only [heat_apply]
  noncomm_ring

theorem product_square_defect_positive (N : ℕ) (L : ℝ) (t : ℝ≥0) (K : Mat (Index N)) :
    (productDefect N L t K.conjTranspose K).PosSemidef := by
  rw [product_defect_eq]
  have h := (lost_positive N L t).conjTranspose_mul_mul_same (K * retentionMatrix N L t)
  simpa only [Matrix.conjTranspose_mul, retentionMatrix_star, Matrix.mul_assoc] using h

def matrixResponse (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index N)) : Mat (Index N) :=
  GibbsFiniteResponse.response (Index N) (logIntensity N alpha L) K

@[simp] theorem matrixResponse_zero (N : ℕ) (alpha L : ℝ) :
    matrixResponse N alpha L 0 = reference N alpha L := by
  rw [reference_eq_exp]
  simp [matrixResponse, GibbsFiniteResponse.response]

def compensation (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)) : Mat (Index N) :=
  heat N L t (matrixResponse N alpha L K) -
    matrixResponse N (alpha + (t : ℝ)) L (observationHeat N L t K)

@[simp] theorem compensation_zero_time (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index N)) :
    compensation N alpha L 0 K = 0 := by simp [compensation]

/-- The reference state itself has no unexplained response defect. -/
@[simp] theorem compensation_zero_observation (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) :
    compensation N alpha L t 0 = 0 := by
  have h0 : observationHeat N L t 0 = 0 := by
    apply Subtype.ext
    exact map_zero (heat N L t)
  simp [compensation, h0, reference_transport]

theorem compensation_cocycle (N : ℕ) (alpha L : ℝ) (s t : ℝ≥0) (K : Hermitian (Index N)) :
    compensation N alpha L (s + t) K =
      heat N L s (compensation N alpha L t K) +
        compensation N (alpha + (t : ℝ)) L s (observationHeat N L t K) := by
  simp only [compensation, heat_add, observationHeat_add, map_sub, NNReal.coe_add]
  have he : alpha + ((s : ℝ) + (t : ℝ)) = alpha + (t : ℝ) + (s : ℝ) := by ring
  rw [he]
  abel

abbrev State (N : ℕ) := Hermitian (Index N) × Mat (Index N)

def resolution (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (state : State N) : State N :=
  (observationHeat N L t state.1, heat N L t state.2 + compensation N alpha L t state.1)

@[simp] theorem resolution_zero (N : ℕ) (alpha L : ℝ) (state : State N) :
    resolution N alpha L 0 state = state := by simp [resolution]

theorem resolution_add (N : ℕ) (alpha L : ℝ) (s t : ℝ≥0) (state : State N) :
    resolution N alpha L (s + t) state =
      resolution N (alpha + (t : ℝ)) L s (resolution N alpha L t state) := by
  apply Prod.ext
  · exact observationHeat_add N L s t state.1
  · change heat N L (s + t) state.2 + compensation N alpha L (s + t) state.1 = _
    rw [heat_add, compensation_cocycle]
    simp only [resolution, map_add]
    abel

theorem complete_response_transport (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (state : State N) :
    matrixResponse N (alpha + (t : ℝ)) L (resolution N alpha L t state).1 +
        (resolution N alpha L t state).2 =
      heat N L t (matrixResponse N alpha L state.1 + state.2) := by
  simp only [resolution, compensation, map_add]
  abel

theorem residual_unique (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N))
    (R S : Mat (Index N))
    (h : matrixResponse N (alpha + (t : ℝ)) L (observationHeat N L t K) + S =
      heat N L t (matrixResponse N alpha L K + R)) :
    S = heat N L t R + compensation N alpha L t K := by
  rw [map_add] at h
  unfold compensation
  calc
    S = (matrixResponse N (alpha + (t : ℝ)) L (observationHeat N L t K) + S) -
        matrixResponse N (alpha + (t : ℝ)) L (observationHeat N L t K) := by abel
    _ = _ := by rw [h]; abel

/-- The closed generated record starts with zero unresolved response.
Its residual is computed from the original complete matrix response. -/
def generatedState (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)) : State N :=
  resolution N alpha L t (K, 0)

theorem generated_complete_response (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)) :
    matrixResponse N (alpha + (t : ℝ)) L (generatedState N alpha L t K).1 +
        (generatedState N alpha L t K).2 = heat N L t (matrixResponse N alpha L K) := by
  simpa only [generatedState, add_zero] using complete_response_transport N alpha L t (K, 0)

structure Conclusions : Prop where
  actual_reference_transport : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0),
    heat N L t (reference N alpha L) = reference N (alpha + (t : ℝ)) L
  actual_product_defect : ∀ (N : ℕ) (L : ℝ) (t : ℝ≥0) (K J : Mat (Index N)),
    productDefect N L t K J = retentionMatrix N L t * K * lost N L t * J * retentionMatrix N L t
  positive_square_defect : ∀ (N : ℕ) (L : ℝ) (t : ℝ≥0) (K : Mat (Index N)),
    (productDefect N L t K.conjTranspose K).PosSemidef
  exact_composition : ∀ (N : ℕ) (alpha L : ℝ) (s t : ℝ≥0) (state : State N),
    resolution N alpha L (s + t) state =
      resolution N (alpha + (t : ℝ)) L s (resolution N alpha L t state)
  closed_generated_response : ∀ (N : ℕ) (alpha L : ℝ) (t : ℝ≥0) (K : Hermitian (Index N)),
    matrixResponse N (alpha + (t : ℝ)) L (generatedState N alpha L t K).1 +
      (generatedState N alpha L t K).2 = heat N L t (matrixResponse N alpha L K)

theorem generated : Conclusions where
  actual_reference_transport := reference_transport
  actual_product_defect := product_defect_eq
  positive_square_defect := product_square_defect_positive
  exact_composition := resolution_add
  closed_generated_response := generated_complete_response

end GeneratedFoundations.Analysis.HistoryPrefixResolution
