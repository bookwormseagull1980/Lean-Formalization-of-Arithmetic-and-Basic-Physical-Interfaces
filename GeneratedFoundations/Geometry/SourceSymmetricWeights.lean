module

public import GeneratedFoundations.Geometry.SourceSymmetricPowers
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Weights and differential operators on the source homogeneous carriers

The vectors in this file are actual binary homogeneous polynomials. Their
weights come from the determinant-one unitary source action. The raising
and lowering operators are restrictions of multiplication followed by
formal polynomial differentiation; their coefficients are computed from
the exponents rather than specified as matrices.

The substitution chain rule relates these differential operations to every
actual source operation. It does not identify a formal derivative with an
analytic derivative of a source orbit. In particular, no invariance under
these differential operators is assumed as a substitute for invariance
under the source group.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate
open Module MvPolynomial
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers

namespace GeneratedFoundations.Geometry.SourceSymmetricWeights

/-- The exponent-indexed vectors in the actual homogeneous carrier. -/
def mode (m : ℕ) (k : Fin (m + 1)) : Carrier m :=
  ⟨MvPolynomial.monomial (exponentOfIndex m k).val 1,
    MvPolynomial.isHomogeneous_monomial 1 (exponentOfIndex m k).property⟩

@[simp]
theorem exponent_zero (m : ℕ) (k : Fin (m + 1)) :
    (exponentOfIndex m k).val 0 = m - k.val := by
  simp [exponentOfIndex]

@[simp]
theorem exponent_one (m : ℕ) (k : Fin (m + 1)) :
    (exponentOfIndex m k).val 1 = k.val := by
  simp [exponentOfIndex]

theorem exponent_index_injective (m : ℕ) :
    Function.Injective (fun k : Fin (m + 1) => (exponentOfIndex m k).val) := by
  intro k l h
  apply Fin.ext
  simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 1) h

theorem mode_coe (m : ℕ) (k : Fin (m + 1)) :
    (mode m k : PolynomialSpace) = X 0 ^ (m - k.val) * X 1 ^ k.val := by
  simp [mode, monomial_binary]

theorem mode_coefficient (m : ℕ) (k l : Fin (m + 1)) :
    (mode m k : PolynomialSpace).coeff (exponentOfIndex m l).val =
      if k = l then 1 else 0 := by
  simp [mode, MvPolynomial.coeff_monomial, (exponent_index_injective m).eq_iff]

theorem mode_ne_zero (m : ℕ) (k : Fin (m + 1)) : mode m k ≠ 0 := by
  intro h
  have hc := congrArg
    (fun p : Carrier m => (p : PolynomialSpace).coeff (exponentOfIndex m k).val) h
  simp [mode_coefficient] at hc

/-- The explicit polynomial vectors span the whole carrier, not merely a
chosen invariant subspace of the dimension stated in the source family. -/
theorem mode_span (m : ℕ) :
    Submodule.span ℂ (Set.range (mode m)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (mode m))
  let T := S.map (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ m).subtype
  apply top_unique
  intro p _
  have hp : (p : PolynomialSpace) ∈ T := by
    rw [(p : PolynomialSpace).as_sum]
    apply T.sum_mem
    intro d hd
    have hddeg : d.degree = m := by
      simpa only [Finsupp.degree_apply] using
        (p.property.degree_eq_sum_deg_support hd).symm
    let k := exponentEquiv m ⟨d, hddeg⟩
    have he : (exponentOfIndex m k).val = d :=
      congrArg Subtype.val ((exponentEquiv m).symm_apply_apply ⟨d, hddeg⟩)
    have hm : (p : PolynomialSpace).coeff d • mode m k ∈ S :=
      S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
    apply Submodule.mem_map.mpr
    refine ⟨(p : PolynomialSpace).coeff d • mode m k, hm, ?_⟩
    change (p : PolynomialSpace).coeff d •
      MvPolynomial.monomial (exponentOfIndex m k).val 1 =
        MvPolynomial.monomial d ((p : PolynomialSpace).coeff d)
    rw [he, MvPolynomial.smul_monomial]
    simp
  obtain ⟨q, hq, hqp⟩ := Submodule.mem_map.mp hp
  have hqp' : q = p := Subtype.ext hqp
  exact hqp' ▸ hq

/-- Equality of linear operators can be checked on the actual monomials. -/
theorem linearMap_ext_modes {m : ℕ} {F G : Module.End ℂ (Carrier m)}
    (h : ∀ k, F (mode m k) = G (mode m k)) : F = G :=
  LinearMap.ext_on_range (mode_span m) h

/-- A diagonal unit source operation; its determinant and unitarity follow
from the same source-group construction used for the two source axes. -/
def diagonalSource (z : ℂ) (hz : ‖z‖ = 1) : SU2 :=
  ⟨canonical z 0, canonical_mem_specialUnitary z 0 (by simp [hz])⟩

theorem diagonal_variable_zero (z : ℂ) :
    variableImage (canonical z 0) 0 = C z * X 0 := by
  simp [variableImage, canonical, Fin.sum_univ_two]

theorem diagonal_variable_one (z : ℂ) :
    variableImage (canonical z 0) 1 = C (conj z) * X 1 := by
  simp [variableImage, canonical, Fin.sum_univ_two]

theorem diagonalAction_mode (m : ℕ) (z : ℂ) (k : Fin (m + 1)) :
    degreeAction m (canonical z 0) (mode m k) =
      (z ^ (m - k.val) * conj z ^ k.val) • mode m k := by
  apply Subtype.ext
  change polynomialAction (canonical z 0) (mode m k : PolynomialSpace) =
    (z ^ (m - k.val) * conj z ^ k.val) • (mode m k : PolynomialSpace)
  simp only [mode_coe]
  simp only [map_mul, map_pow, polynomialAction_X, diagonal_variable_zero,
    diagonal_variable_one, mul_pow, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring

/-- All-degree source weights, including both endpoint weights. -/
theorem source_diagonal_weight (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1)
    (k : Fin (m + 1)) :
    sourceRepresentation m (diagonalSource z hz) (mode m k) =
      (z ^ (m - k.val) * conj z ^ k.val) • mode m k :=
  diagonalAction_mode m z k

/-- The weight formula applies directly to the original diagonal source
axis, with its half-angle normalization retained. -/
theorem source_z_axis_weight (m : ℕ) (t : ℝ) (k : Fin (m + 1)) :
    sourceRepresentation m (zElement t) (mode m k) =
      (Complex.exp (-Complex.I * (t : ℂ) / 2) ^ (m - k.val) *
        Complex.exp (Complex.I * (t : ℂ) / 2) ^ k.val) • mode m k := by
  apply Subtype.ext
  change polynomialAction (zRotation t) (mode m k : PolynomialSpace) =
    (Complex.exp (-Complex.I * (t : ℂ) / 2) ^ (m - k.val) *
      Complex.exp (Complex.I * (t : ℂ) / 2) ^ k.val) • (mode m k : PolynomialSpace)
  simp [mode_coe, variableImage, zRotation, Fin.sum_univ_two,
    Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_pow]
  ring

/-- The formal chain rule uses the entries of the actual substitution
matrix, with the same column convention as `sourceRepresentation`. -/
theorem pderiv_polynomialAction (M : Mat2) (p : PolynomialSpace) (i : Fin 2) :
    pderiv i (polynomialAction M p) =
      C (M i 0) * polynomialAction M (pderiv 0 p) +
        C (M i 1) * polynomialAction M (pderiv 1 p) := by
  revert i
  induction p using MvPolynomial.induction_on with
  | C c =>
      intro i
      simp
  | add p q hp hq =>
      intro i
      simp only [map_add, hp, hq]
      ring
  | mul_X p j hp =>
      intro i
      fin_cases i <;> fin_cases j <;>
        simp [hp, variableImage, Fin.sum_univ_two] <;> ring

theorem source_pderiv_chain_rule (m : ℕ) (U : SU2) (p : Carrier m) (i : Fin 2) :
    pderiv i (sourceRepresentation m U p : PolynomialSpace) =
      C ((U : Mat2) i 0) * polynomialAction (U : Mat2) (pderiv 0 p) +
        C ((U : Mat2) i 1) * polynomialAction (U : Mat2) (pderiv 1 p) :=
  pderiv_polynomialAction (U : Mat2) p i

theorem transfer_homogeneous {m : ℕ} {p : PolynomialSpace}
    (hp : p.IsHomogeneous m) (target origin : Fin 2) :
    (X target * pderiv origin p).IsHomogeneous m := by
  cases m with
  | zero =>
      rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous,
        MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hp
      rw [hp, MvPolynomial.pderiv_C, mul_zero]
      apply MvPolynomial.isHomogeneous_zero
  | succ n =>
      simpa [Nat.succ_eq_add_one, Nat.add_comm] using
        (MvPolynomial.isHomogeneous_X ℂ target).mul (hp.pderiv (i := origin))

/-- Transfer one polynomial degree from `origin` to `target`. -/
def transfer (m : ℕ) (target origin : Fin 2) : Module.End ℂ (Carrier m) where
  toFun (p : Carrier m) :=
    ⟨(X target : PolynomialSpace) * pderiv origin (p : PolynomialSpace),
      transfer_homogeneous (m := m) (p := (p : PolynomialSpace)) p.property target origin⟩
  map_add' p q := by
    apply Subtype.ext
    change X target * pderiv origin ((p : PolynomialSpace) + (q : PolynomialSpace)) =
      X target * pderiv origin (p : PolynomialSpace) +
        X target * pderiv origin (q : PolynomialSpace)
    simp [map_add, mul_add]
  map_smul' c p := by
    apply Subtype.ext
    change X target * pderiv origin (c • (p : PolynomialSpace)) =
      c • (X target * pderiv origin p)
    rw [(pderiv origin).map_smul, mul_smul_comm]

@[simp]
theorem transfer_coe (m : ℕ) (target origin : Fin 2) (p : Carrier m) :
    (transfer m target origin p : PolynomialSpace) = X target * pderiv origin p := rfl

def raising (m : ℕ) : Module.End ℂ (Carrier m) := transfer m 0 1

def lowering (m : ℕ) : Module.End ℂ (Carrier m) := transfer m 1 0

def weightOperator (m : ℕ) : Module.End ℂ (Carrier m) :=
  transfer m 0 0 - transfer m 1 1

def predecessor {m : ℕ} (k : Fin (m + 1)) : Fin (m + 1) :=
  ⟨k.val - 1, by omega⟩

def successor {m : ℕ} (k : Fin (m + 1)) (hk : k.val < m) : Fin (m + 1) :=
  ⟨k.val + 1, by omega⟩

theorem raising_mode {m : ℕ} (k : Fin (m + 1)) (hk : 0 < k.val) :
    raising m (mode m k) = (k.val : ℂ) • mode m (predecessor k) := by
  have he : Finsupp.single 0 1 +
      ((exponentOfIndex m k).val - Finsupp.single 1 1) =
        (exponentOfIndex m (predecessor k)).val := by
    ext i
    fin_cases i <;> simp [exponentOfIndex, predecessor]
    omega
  apply Subtype.ext
  change X 0 * pderiv 1 (MvPolynomial.monomial (exponentOfIndex m k).val (1 : ℂ)) =
    (k.val : ℂ) • MvPolynomial.monomial (exponentOfIndex m (predecessor k)).val (1 : ℂ)
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.smul_monomial, he]
  simp

theorem raising_mode_zero (m : ℕ) :
    raising m (mode m ⟨0, by omega⟩) = 0 := by
  apply Subtype.ext
  change X 0 * pderiv 1 (MvPolynomial.monomial
    (exponentOfIndex m ⟨0, by omega⟩).val (1 : ℂ)) = 0
  simp

theorem lowering_mode {m : ℕ} (k : Fin (m + 1)) (hk : k.val < m) :
    lowering m (mode m k) = ((m - k.val : ℕ) : ℂ) • mode m (successor k hk) := by
  have he : Finsupp.single 1 1 +
      ((exponentOfIndex m k).val - Finsupp.single 0 1) =
        (exponentOfIndex m (successor k hk)).val := by
    ext i
    fin_cases i <;> simp [exponentOfIndex, successor] <;> omega
  apply Subtype.ext
  change X 1 * pderiv 0 (MvPolynomial.monomial (exponentOfIndex m k).val (1 : ℂ)) =
    ((m - k.val : ℕ) : ℂ) •
      MvPolynomial.monomial (exponentOfIndex m (successor k hk)).val (1 : ℂ)
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.smul_monomial, he]
  simp

theorem lowering_mode_top (m : ℕ) :
    lowering m (mode m ⟨m, by omega⟩) = 0 := by
  apply Subtype.ext
  change X 1 * pderiv 0 (MvPolynomial.monomial
    (exponentOfIndex m ⟨m, by omega⟩).val (1 : ℂ)) = 0
  simp

theorem diagonal_transfer_mode (m : ℕ) (k : Fin (m + 1)) (i : Fin 2) :
    transfer m i i (mode m k) = ((exponentOfIndex m k).val i : ℂ) • mode m k := by
  apply Subtype.ext
  change X i * pderiv i (MvPolynomial.monomial (exponentOfIndex m k).val (1 : ℂ)) =
    ((exponentOfIndex m k).val i : ℂ) •
      MvPolynomial.monomial (exponentOfIndex m k).val (1 : ℂ)
  rw [MvPolynomial.X_mul_pderiv_monomial, Nat.cast_smul_eq_nsmul]

theorem weightOperator_mode (m : ℕ) (k : Fin (m + 1)) :
    weightOperator m (mode m k) = ((m : ℂ) - 2 * (k.val : ℂ)) • mode m k := by
  have hk : k.val ≤ m := by omega
  simp only [weightOperator, LinearMap.sub_apply, diagonal_transfer_mode,
    exponent_zero, exponent_one, Nat.cast_sub hk]
  calc
    _ = (((m : ℂ) - (k.val : ℂ)) - (k.val : ℂ)) • mode m k :=
      (sub_smul ((m : ℂ) - (k.val : ℂ)) (k.val : ℂ) (mode m k)).symm
    _ = _ := congrArg (fun z : ℂ => z • mode m k) (by ring)

/-- Euler's identity fixes the sum of the two actual degree transfers on
the whole carrier. -/
theorem total_degree_operator (m : ℕ) :
    transfer m 0 0 + transfer m 1 1 = (m : ℂ) • (1 : Module.End ℂ (Carrier m)) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change X 0 * pderiv 0 (p : PolynomialSpace) +
    X 1 * pderiv 1 (p : PolynomialSpace) = (m : ℂ) • (p : PolynomialSpace)
  simpa only [Fin.sum_univ_two, Nat.cast_smul_eq_nsmul] using
    p.property.sum_X_mul_pderiv

end GeneratedFoundations.Geometry.SourceSymmetricWeights
