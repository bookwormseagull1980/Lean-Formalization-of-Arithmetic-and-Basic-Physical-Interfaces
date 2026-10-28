module

public import GeneratedFoundations.Arithmetic.HistoryCliffordAction
public import GeneratedFoundations.Geometry.SourceScalarResolution

/-!
# Joint resolution of the full arithmetic connection and section response

The index is the actual history--phase/source carrier. All matrix entries,
all section components and all even scalar source coefficients are kept.
The connection bracket and covariant derivative are evaluated on continuous
representatives before passing to the original Haar space. No nonlinear
output is projected back into a finite core.

Resolution is the original source heat map. The unresolved response is its
unique exact compensation, with a cocycle and joint semigroup. These are
response-transport identities, not an assertion that nonlinear response
commutes with heat or that resolution is arithmetic generation time.
-/

@[expose] public section
noncomputable section
open scoped BigOperators NNReal
open GeneratedFoundations.Geometry.SourceSpinCentre GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceScalarResolution

namespace GeneratedFoundations.Arithmetic.HistoryFieldResolution

abbrev Index (N : ℕ) := HistoryCliffordAction.Index N

variable (N : ℕ)

abbrev Connection := Fin 3 → (Index N × Index N) → ScalarCore
abbrev Matter := Index N → ScalarCore
abbrev Fields := Connection N × Matter N
abbrev CurvatureFields := Fin 3 → (Index N × Index N) → QuotientL2
abbrev MatterResponseFields := Fin 3 → Index N → QuotientL2
abbrev Responses := CurvatureFields N × MatterResponseFields N

def fieldsHeat (t : ℝ≥0) (U : Fields N) : Fields N :=
  (fun j a => coreHeat t (U.1 j a), fun i => coreHeat t (U.2 i))

@[simp] theorem fieldsHeat_zero (U : Fields N) : fieldsHeat N 0 U = U := by
  apply Prod.ext <;> funext i <;> simp [fieldsHeat]

theorem fieldsHeat_add (s t : ℝ≥0) (U : Fields N) :
    fieldsHeat N (s + t) U = fieldsHeat N s (fieldsHeat N t U) := by
  apply Prod.ext
  · funext j a
    exact coreHeat_add s t (U.1 j a)
  · funext i
    exact coreHeat_add s t (U.2 i)

def responseHeat (t : ℝ≥0) : Responses N →ₗ[ℂ] Responses N where
  toFun R :=
    (fun j a => Geometry.SourceQuotientCasimir.heat t (R.1 j a),
     fun j i => Geometry.SourceQuotientCasimir.heat t (R.2 j i))
  map_add' R S := by
    apply Prod.ext <;> funext j a <;> exact map_add _ _ _
  map_smul' c R := by
    apply Prod.ext
    · funext j a
      exact map_smul (Geometry.SourceQuotientCasimir.heat t) c (R.1 j a)
    · funext j a
      exact map_smul (Geometry.SourceQuotientCasimir.heat t) c (R.2 j a)

@[simp] theorem responseHeat_zero (R : Responses N) : responseHeat N 0 R = R := by
  apply Prod.ext <;> funext j a <;> exact Geometry.SourceQuotientCasimir.heat_zero _

theorem responseHeat_add (s t : ℝ≥0) (R : Responses N) :
    responseHeat N (s + t) R = responseHeat N s (responseHeat N t R) := by
  apply Prod.ext <;> funext j a <;> exact Geometry.SourceQuotientCasimir.heat_add s t _

theorem responseHeat_sub (t : ℝ≥0) (R S : Responses N) :
    responseHeat N t (R - S) = responseHeat N t R - responseHeat N t S := by
  apply Prod.ext
  · funext j a
    exact map_sub (Geometry.SourceQuotientCasimir.heat t) (R.1 j a) (S.1 j a)
  · funext j i
    exact map_sub (Geometry.SourceQuotientCasimir.heat t) (R.2 j i) (S.2 j i)

/-- The complete native history/source operation acts on every component. -/
def matrixProduct (A : (Index N × Index N) → ScalarCore)
    (psi : Matter N) (i : Index N) : C(CentralQuotient, ℂ) :=
  ∑ d : Index N, representative (A (i, d)) * representative (psi d)

/-- Both orders of the full nonabelian product are evaluated before Haar
inclusion. No finite core projection is applied to the nonlinear output. -/
def curvature (L : ℝ) (A : Connection N) : CurvatureFields N := fun j a =>
  ContinuousMap.toLp 2 quotientHaar ℂ
    (derivative L j (A (j + 1) a) - derivative L (j + 1) (A j a) -
      ((2 / L : ℝ) : ℂ) • representative (A (j + 2) a) +
      ∑ d : Index N,
        (representative (A j (a.1, d)) * representative (A (j + 1) (d, a.2)) -
        (representative (A (j + 1) (a.1, d)) * representative (A j (d, a.2))))

)

def matterDerivative (L : ℝ) (U : Fields N) : MatterResponseFields N := fun j i =>
  ContinuousMap.toLp 2 quotientHaar ℂ
    (derivative L j (U.2 i) + matrixProduct N (U.1 j) U.2 i)

def response (L : ℝ) (U : Fields N) : Responses N :=
  (curvature N L U.1, matterDerivative N L U)

def compensation (L : ℝ) (t : ℝ≥0) (U : Fields N) : Responses N :=
  responseHeat N t (response N L U) - response N L (fieldsHeat N t U)

@[simp] theorem compensation_zero (L : ℝ) (U : Fields N) : compensation N L 0 U = 0 := by
  simp [compensation]

/-- The two defects on successive resolutions add after transporting
the first defect by the same source heat map. -/
theorem compensation_cocycle (L : ℝ) (s t : ℝ≥0) (U : Fields N) :
    compensation N L (s + t) U =
      responseHeat N s (compensation N L t U) + compensation N L s (fieldsHeat N t U) := by
  change responseHeat N (s + t) (response N L U) - response N L (fieldsHeat N (s + t) U) =
    responseHeat N s (responseHeat N t (response N L U) - response N L (fieldsHeat N t U)) +
      (responseHeat N s (response N L (fieldsHeat N t U)) -
        response N L (fieldsHeat N s (fieldsHeat N t U)))
  rw [responseHeat_add N, fieldsHeat_add N, responseHeat_sub N]
  abel

def resolution (L : ℝ) (t : ℝ≥0) (state : Fields N × Responses N) : Fields N × Responses N :=
  (fieldsHeat N t state.1, responseHeat N t state.2 + compensation N L t state.1)

@[simp] theorem resolution_zero (L : ℝ) (state : Fields N × Responses N) :
    resolution N L 0 state = state := by
  simp [resolution]

theorem resolution_add (L : ℝ) (s t : ℝ≥0) (state : Fields N × Responses N) :
    resolution N L (s + t) state = resolution N L s (resolution N L t state) := by
  apply Prod.ext
  · exact fieldsHeat_add N s t state.1
  · change responseHeat N (s + t) state.2 + compensation N L (s + t) state.1 = _
    rw [responseHeat_add N, compensation_cocycle N]
    simp only [resolution, map_add]
    abel

/-- Response plus residual is transported exactly; the response itself
need not have a constant value as the resolution changes. -/
theorem complete_response_transport (L : ℝ) (t : ℝ≥0) (state : Fields N × Responses N) :
    response N L (resolution N L t state).1 + (resolution N L t state).2 =
      responseHeat N t (response N L state.1 + state.2) := by
  simp only [resolution, compensation, map_add]
  abel

/-- Once the field heat map and complete response are fixed, there is
exactly one compatible unresolved response. -/
theorem residual_unique (L : ℝ) (t : ℝ≥0) (U : Fields N) (R S : Responses N)
    (h : response N L (fieldsHeat N t U) + S = responseHeat N t (response N L U + R)) :
    S = responseHeat N t R + compensation N L t U := by
  calc
    S = (response N L (fieldsHeat N t U) + S) - response N L (fieldsHeat N t U) := by abel
    _ = responseHeat N t (response N L U + R) - response N L (fieldsHeat N t U) := by rw [h]
    _ = responseHeat N t R + compensation N L t U := by
      rw [map_add]
      dsimp [compensation]
      abel

structure Conclusions : Prop where
  exact_cocycle : ∀ N L s t U,
    compensation N L (s + t) U =
      responseHeat N s (compensation N L t U) + compensation N L s (fieldsHeat N t U)
  joint_semigroup : ∀ N L s t state,
    resolution N L (s + t) state = resolution N L s (resolution N L t state)
  full_response : ∀ N L t state,
    response N L (resolution N L t state).1 + (resolution N L t state).2 =
      responseHeat N t (response N L state.1 + state.2)
  unique_residual : ∀ N L t U R S,
    response N L (fieldsHeat N t U) + S = responseHeat N t (response N L U + R) →
    S = responseHeat N t R + compensation N L t U

theorem generated : Conclusions where
  exact_cocycle := compensation_cocycle
  joint_semigroup := resolution_add
  full_response := complete_response_transport
  unique_residual := residual_unique

end GeneratedFoundations.Arithmetic.HistoryFieldResolution
