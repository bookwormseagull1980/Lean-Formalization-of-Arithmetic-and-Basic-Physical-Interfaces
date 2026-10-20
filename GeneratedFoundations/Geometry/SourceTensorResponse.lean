module

public import GeneratedFoundations.Geometry.SourceAxisTT
public import Mathlib.Tactic

/-!
# TT response endpoint and massless pole

This module formalizes the algebraic part of the tensor-response interface
of the common generated geometry.  The internal kernel is expressed in
the mass fraction `y`; its mass-weighted response has the unique maximum
`4/27` at `y = 1/3`.  Consequently every positive fixed spectral coefficient
has one positive endpoint.

The endpoint zero is kept distinct from the TT propagator.  On the
two-dimensional TT carrier already derived from the constraints, a positive
kinetic coefficient gives inverse covariance `Z q²`.  Its only momentum zero
is `q² = 0`, and the exact rescaled inverse has positive residue `1/Z`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Geometry.SourceTensorResponse

open SourceAxisTT

/-- The source-normalized transverse--traceless kernel. -/
def ttKernel (q2 m2 : ℝ) : ℝ := q2 ^ 2 / (q2 + m2) ^ 2

/-- Fraction of the total quadratic scale carried by the mass insertion. -/
def massFraction (q2 m2 : ℝ) : ℝ := m2 / (q2 + m2)

/-- The mass-weighted response selected by the TT kernel. -/
def massWeightedResponse (y : ℝ) : ℝ := y * (1 - y) ^ 2

theorem ttKernel_eq_massFraction (q2 m2 : ℝ) (hden : q2 + m2 ≠ 0) :
    ttKernel q2 m2 = (1 - massFraction q2 m2) ^ 2 := by
  rw [ttKernel, massFraction]
  field_simp
  ring

theorem massFraction_mem_unitInterval {q2 m2 : ℝ}
    (hq : 0 ≤ q2) (hm : 0 ≤ m2) (hden : 0 < q2 + m2) :
    0 ≤ massFraction q2 m2 ∧ massFraction q2 m2 ≤ 1 := by
  constructor
  · exact div_nonneg hm hden.le
  · rw [massFraction, div_le_one hden]
    linarith

theorem ttKernel_nonnegative (q2 m2 : ℝ) : 0 ≤ ttKernel q2 m2 := by
  exact div_nonneg (sq_nonneg q2) (sq_nonneg (q2 + m2))

theorem ttKernel_le_one {q2 m2 : ℝ}
    (hq : 0 ≤ q2) (hm : 0 ≤ m2) (hden : 0 < q2 + m2) :
    ttKernel q2 m2 ≤ 1 := by
  rw [ttKernel_eq_massFraction q2 m2 hden.ne']
  obtain ⟨hy0, hy1⟩ := massFraction_mem_unitInterval hq hm hden
  nlinarith [sq_nonneg (massFraction q2 m2)]

theorem response_factorization (y : ℝ) :
    (4 : ℝ) / 27 - massWeightedResponse y =
      (y - 1 / 3) ^ 2 * (4 / 3 - y) := by
  rw [massWeightedResponse]
  ring

/-- The exact TT response bound on the generated mass-fraction interval. -/
theorem massWeightedResponse_le {y : ℝ} (_hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    massWeightedResponse y ≤ (4 : ℝ) / 27 := by
  rw [← sub_nonneg]
  rw [response_factorization]
  exact mul_nonneg (sq_nonneg _) (by linarith)

@[simp] theorem massWeightedResponse_oneThird :
    massWeightedResponse ((1 : ℝ) / 3) = (4 : ℝ) / 27 := by
  norm_num [massWeightedResponse]

/-- Equality in the response bound determines the unique maximizing mass
fraction. -/
theorem massWeightedResponse_eq_critical_iff {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    massWeightedResponse y = (4 : ℝ) / 27 ↔ y = 1 / 3 := by
  constructor
  · intro h
    have hz : (y - 1 / 3) ^ 2 * (4 / 3 - y) = 0 := by
      rw [← response_factorization]
      linarith
    rcases mul_eq_zero.mp hz with hs | hl
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    · exfalso
      nlinarith
  · rintro rfl
    exact massWeightedResponse_oneThird

theorem unique_response_maximizer :
    ∃! y : Set.Icc (0 : ℝ) 1,
      massWeightedResponse y = (4 : ℝ) / 27 := by
  refine ⟨⟨1 / 3, by constructor <;> norm_num⟩, massWeightedResponse_oneThird, ?_⟩
  intro y hy
  apply Subtype.ext
  exact massWeightedResponse_eq_critical_iff y.2.1 y.2.2 |>.mp hy

/-- Residual of a fixed positive spectral coefficient against the canonical
TT response threshold. -/
def endpointResidual (A c : ℝ) : ℝ := A / c - 4 / 27

def endpointRoot (A : ℝ) : ℝ := 27 * A / 4

theorem endpointRoot_pos {A : ℝ} (hA : 0 < A) : 0 < endpointRoot A := by
  simp [endpointRoot]
  positivity

@[simp] theorem endpointResidual_root {A : ℝ} (hA : 0 < A) :
    endpointResidual A (endpointRoot A) = 0 := by
  rw [endpointResidual, endpointRoot]
  field_simp [hA.ne']
  ring

theorem endpointResidual_eq_zero_iff {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    endpointResidual A c = 0 ↔ c = endpointRoot A := by
  constructor
  · intro h
    rw [endpointResidual] at h
    have hc0 : c ≠ 0 := hc.ne'
    field_simp [hc0] at h
    rw [endpointRoot]
    linarith
  · rintro rfl
    exact endpointResidual_root hA

/-- Every positive spectral coefficient fixes exactly one positive response
endpoint. -/
theorem existsUnique_positive_endpoint {A : ℝ} (hA : 0 < A) :
    ∃! c : {x : ℝ // 0 < x}, endpointResidual A c = 0 := by
  refine ⟨⟨endpointRoot A, endpointRoot_pos hA⟩, endpointResidual_root hA, ?_⟩
  intro c hc
  apply Subtype.ext
  exact endpointResidual_eq_zero_iff hA c.2 |>.mp hc

/-! ## TT inverse covariance and its pole -/

/-- Scalar inverse covariance on the two-dimensional TT carrier. -/
def ttInverseCovariance (Z q2 : ℝ) (h : TTMode) : TTMode := (Z * q2) • h

theorem ttInverseCovariance_zero_momentum (Z : ℝ) (h : TTMode) :
    ttInverseCovariance Z 0 h = 0 := by simp [ttInverseCovariance]

theorem ttInverseCovariance_injective {Z q2 : ℝ} (hZ : Z ≠ 0) (hq : q2 ≠ 0) :
    Function.Injective (ttInverseCovariance Z q2) := by
  intro h k heq
  exact smul_right_injective TTMode (mul_ne_zero hZ hq) heq

/-- Away from zero momentum the inverse covariance has its explicit inverse. -/
def ttPropagator (Z q2 : ℝ) (h : TTMode) : TTMode := (Z * q2)⁻¹ • h

theorem ttInverseCovariance_propagator {Z q2 : ℝ} (hZ : Z ≠ 0) (hq : q2 ≠ 0)
    (h : TTMode) :
    ttInverseCovariance Z q2 (ttPropagator Z q2 h) = h := by
  rw [ttInverseCovariance, ttPropagator, smul_smul]
  rw [mul_inv_cancel₀ (mul_ne_zero hZ hq), one_smul]

/-- Algebraic simple-pole certificate: multiplying the scalar propagator by
`q²` gives the nonzero residue `1/Z`. -/
theorem tt_simplePole_certificate {Z q2 : ℝ} (hZ : Z ≠ 0) (hq : q2 ≠ 0) :
    q2 * (Z * q2)⁻¹ = Z⁻¹ := by
  field_simp

theorem tt_poleResidue_pos {Z : ℝ} (hZ : 0 < Z) : 0 < Z⁻¹ := by
  exact inv_pos.mpr hZ

/-- The generated TT carrier, endpoint rigidity and algebraic massless pole
collected as propositions for the common source theorem. -/
structure Properties : Prop where
  tt_dimension : Module.finrank ℝ TTMode = 2
  response_bound : ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
    massWeightedResponse y ≤ (4 : ℝ) / 27
  response_unique : ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
    (massWeightedResponse y = (4 : ℝ) / 27 ↔ y = 1 / 3)
  endpoint_unique : ∀ A : ℝ, 0 < A →
    ∃! c : {x : ℝ // 0 < x}, endpointResidual A c = 0
  pole_zero : ∀ Z : ℝ, ∀ h : TTMode, ttInverseCovariance Z 0 h = 0
  pole_residue : ∀ Z q2 : ℝ, Z ≠ 0 → q2 ≠ 0 →
    q2 * (Z * q2)⁻¹ = Z⁻¹

theorem sourceTensorResponseEndpointProperties : Properties where
  tt_dimension := SourceAxisTT.ttMode_finrank
  response_bound := fun _ => massWeightedResponse_le
  response_unique := fun _ => massWeightedResponse_eq_critical_iff
  endpoint_unique := fun _ => existsUnique_positive_endpoint
  pole_zero := ttInverseCovariance_zero_momentum
  pole_residue := fun _ _ => tt_simplePole_certificate

end GeneratedFoundations.Geometry.SourceTensorResponse
