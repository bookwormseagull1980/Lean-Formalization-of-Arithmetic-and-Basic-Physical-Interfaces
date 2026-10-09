module

public import GeneratedFoundations.Geometry.SourceSpinCentre
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Ring.Parity
public import Lean.Elab.Tactic.Omega

/-!
# Homogeneous powers of the generated source representation

The source matrix acts on the two polynomial generators by its columns.
Restriction to each homogeneous degree gives an actual representation of
the generated determinant-one unitary group. The monomial basis determines
its dimension, and the central sign acts by degree parity.

These constructions supply the representation family used in the source
harmonic analysis. Irreducibility, completeness of matrix coefficients and
the spectrum of the differential Casimir are separate assertions.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Module MvPolynomial
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSpinCentre

namespace GeneratedFoundations.Geometry.SourceSymmetricPowers

abbrev PolynomialSpace := MvPolynomial (Fin 2) ℂ

abbrev Carrier (m : ℕ) := MvPolynomial.homogeneousSubmodule (Fin 2) ℂ m

/-- The image of a source basis vector in the degree-one polynomial space. -/
def variableImage (M : Mat2) (i : Fin 2) : PolynomialSpace :=
  ∑ j, C (M j i) * X j

def polynomialAction (M : Mat2) : PolynomialSpace →ₐ[ℂ] PolynomialSpace :=
  MvPolynomial.aeval (variableImage M)

@[simp]
theorem polynomialAction_X (M : Mat2) (i : Fin 2) :
    polynomialAction M (X i) = variableImage M i :=
  MvPolynomial.aeval_X _ _

@[simp]
theorem polynomialAction_C (M : Mat2) (c : ℂ) :
    polynomialAction M (C c) = C c := by
  simp [polynomialAction, MvPolynomial.algebraMap_eq]

theorem polynomialAction_one : polynomialAction (1 : Mat2) = AlgHom.id ℂ _ := by
  ext i
  fin_cases i <;> simp [polynomialAction, variableImage, Fin.sum_univ_two]

/-- Column substitution has the same multiplication order as the source
matrices. In particular, the construction is a representation, not an
opposite action. -/
theorem polynomialAction_mul (M N : Mat2) :
    polynomialAction (M * N) = (polynomialAction M).comp (polynomialAction N) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [polynomialAction, variableImage, Matrix.mul_apply, Fin.sum_univ_two,
      MvPolynomial.algebraMap_eq] <;> ring

theorem variableImage_homogeneous (M : Mat2) (i : Fin 2) :
    (variableImage M i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

theorem polynomialAction_homogeneous (M : Mat2) {m : ℕ} {p : PolynomialSpace}
    (hp : p.IsHomogeneous m) : (polynomialAction M p).IsHomogeneous m := by
  simpa only [polynomialAction, one_mul] using
    hp.aeval (variableImage M) (variableImage_homogeneous M)

def degreeAction (m : ℕ) (M : Mat2) : Module.End ℂ (Carrier m) where
  toFun p := ⟨polynomialAction M p, polynomialAction_homogeneous M p.property⟩
  map_add' p q := Subtype.ext ((polynomialAction M).map_add p q)
  map_smul' c p := Subtype.ext ((polynomialAction M).toLinearMap.map_smul c p)

@[simp]
theorem degreeAction_coe (m : ℕ) (M : Mat2) (p : Carrier m) :
    (degreeAction m M p : PolynomialSpace) = polynomialAction M p := rfl

theorem degreeAction_one (m : ℕ) : degreeAction m 1 = 1 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change polynomialAction (1 : Mat2) p = p
  rw [polynomialAction_one]
  rfl

theorem degreeAction_mul (m : ℕ) (M N : Mat2) :
    degreeAction m (M * N) = degreeAction m M * degreeAction m N := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change polynomialAction (M * N) p = polynomialAction M (polynomialAction N p)
  rw [polynomialAction_mul]
  rfl

/-- The homogeneous representation is restricted from the actual source
matrix group, with no irreducibility or spectral data included as input. -/
def sourceRepresentation (m : ℕ) : Representation ℂ SU2 (Carrier m) where
  toFun U := degreeAction m (U : Mat2)
  map_one' := degreeAction_one m
  map_mul' U V := degreeAction_mul m (U : Mat2) (V : Mat2)

def degreeOnePolynomial (v : Fin 2 → ℂ) : Carrier 1 :=
  ⟨∑ i, C (v i) * X i, by
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    exact MvPolynomial.isHomogeneous_C_mul_X _ _⟩

def degreeOneLinear : (Fin 2 → ℂ) →ₗ[ℂ] Carrier 1 where
  toFun := degreeOnePolynomial
  map_add' v w := by
    apply Subtype.ext
    simp [degreeOnePolynomial, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    apply Subtype.ext
    simp [degreeOnePolynomial, Algebra.smul_def, map_mul, mul_assoc, mul_add]

theorem degreeOne_coefficient (v : Fin 2 → ℂ) (i : Fin 2) :
    (degreeOnePolynomial v : PolynomialSpace).coeff (Finsupp.single i 1) = v i := by
  fin_cases i <;> simp [degreeOnePolynomial, Fin.sum_univ_two]

theorem degreeOne_injective : Function.Injective degreeOneLinear := by
  intro v w h
  funext i
  have hc := congrArg
    (fun p : Carrier 1 => (p : PolynomialSpace).coeff (Finsupp.single i 1)) h
  change (degreeOnePolynomial v : PolynomialSpace).coeff (Finsupp.single i 1) =
    (degreeOnePolynomial w : PolynomialSpace).coeff (Finsupp.single i 1) at hc
  simpa only [degreeOne_coefficient] using hc

theorem degreeOne_surjective : Function.Surjective degreeOneLinear := by
  let f : (Fin 2 → ℂ) →ₗ[ℂ] PolynomialSpace :=
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ 1).subtype.comp degreeOneLinear
  have hspan : Submodule.span ℂ (Set.range (X : Fin 2 → PolynomialSpace)) ≤
      LinearMap.range f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    change (degreeOnePolynomial (Pi.single i 1) : PolynomialSpace) = X i
    fin_cases i <;> simp [degreeOnePolynomial, Fin.sum_univ_two]
  intro p
  have hp : (p : PolynomialSpace) ∈ Submodule.span ℂ (Set.range (X : Fin 2 → PolynomialSpace)) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact p.property
  obtain ⟨v, hv⟩ := hspan hp
  exact ⟨v, Subtype.ext hv⟩

/-- The first homogeneous carrier is linearly equivalent to the original
two-component source carrier. -/
def degreeOneEquiv : (Fin 2 → ℂ) ≃ₗ[ℂ] Carrier 1 :=
  LinearEquiv.ofBijective degreeOneLinear ⟨degreeOne_injective, degreeOne_surjective⟩

/-- Degree one is the original column action on the two source modes. -/
theorem degreeOne_intertwines (U : SU2) (v : Fin 2 → ℂ) :
    sourceRepresentation 1 U (degreeOnePolynomial v) =
      degreeOnePolynomial ((U : Mat2).mulVec v) := by
  apply Subtype.ext
  change polynomialAction (U : Mat2) (∑ i, C (v i) * X i) =
    ∑ i, C (((U : Mat2).mulVec v) i) * X i
  simp [polynomialAction, variableImage, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, MvPolynomial.algebraMap_eq]
  ring

abbrev DegreeExponents (m : ℕ) := {d : Fin 2 →₀ ℕ // d.degree = m}

theorem degreeExponents_sum {m : ℕ} (d : DegreeExponents m) :
    d.val 0 + d.val 1 = m := by
  simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using d.property

def exponentOfIndex (m : ℕ) (k : Fin (m + 1)) : DegreeExponents m :=
  ⟨Finsupp.single 0 (m - k.val) + Finsupp.single 1 k.val, by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    omega⟩

def exponentEquiv (m : ℕ) : DegreeExponents m ≃ Fin (m + 1) where
  toFun d := ⟨d.val 1, by have := degreeExponents_sum d; omega⟩
  invFun := exponentOfIndex m
  left_inv d := by
    apply Subtype.ext
    ext i
    have hd := degreeExponents_sum d
    fin_cases i
    · simp [exponentOfIndex]
      omega
    · simp [exponentOfIndex]
  right_inv k := by
    apply Fin.ext
    simp [exponentOfIndex]

def monomialBasis (m : ℕ) : Basis (Fin (m + 1)) ℂ (Carrier m) := by
  let b : Basis (DegreeExponents m) ℂ (Carrier m) := by
    change Basis (DegreeExponents m) ℂ
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ m)
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact MvPolynomial.basisRestrictSupport ℂ {d : Fin 2 →₀ ℕ | d.degree = m}
  exact b.reindex (exponentEquiv m)

instance carrier_finiteDimensional (m : ℕ) : FiniteDimensional ℂ (Carrier m) :=
  Module.Finite.of_basis (monomialBasis m)

theorem carrier_finrank (m : ℕ) : Module.finrank ℂ (Carrier m) = m + 1 := by
  simpa using Module.finrank_eq_card_basis (monomialBasis m)

theorem exponent_decomposition (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext i
  fin_cases i <;> simp

theorem monomial_binary (d : Fin 2 →₀ ℕ) (c : ℂ) :
    (MvPolynomial.monomial d c : PolynomialSpace) = C c * X 0 ^ d 0 * X 1 ^ d 1 := by
  conv_lhs => rw [exponent_decomposition d]
  rw [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem variableImage_scalar (c : ℂ) (i : Fin 2) :
    variableImage (c • (1 : Mat2)) i = C c * X i := by
  fin_cases i <;> simp [variableImage, Fin.sum_univ_two]

theorem scalarAction_monomial (c a : ℂ) (d : Fin 2 →₀ ℕ) :
    polynomialAction (c • (1 : Mat2)) (MvPolynomial.monomial d a) =
      c ^ d.degree • MvPolynomial.monomial d a := by
  simp only [monomial_binary, map_mul, map_pow,
    polynomialAction_C, polynomialAction_X, variableImage_scalar]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, Finsupp.degree_eq_sum,
    Fin.sum_univ_two, pow_add, mul_pow, map_mul, map_pow]
  ring

theorem scalarAction_homogeneous (c : ℂ) {m : ℕ} {p : PolynomialSpace}
    (hp : p.IsHomogeneous m) :
    polynomialAction (c • (1 : Mat2)) p = c ^ m • p := by
  calc
    polynomialAction (c • (1 : Mat2)) p =
        ∑ d ∈ p.support,
          polynomialAction (c • (1 : Mat2)) (MvPolynomial.monomial d (p.coeff d)) := by
      conv_lhs => rw [p.as_sum]
      simp only [map_sum]
    _ = ∑ d ∈ p.support, c ^ m • MvPolynomial.monomial d (p.coeff d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hddeg : d.degree = m := by
        simpa only [Finsupp.degree_apply] using (hp.degree_eq_sum_deg_support hd).symm
      rw [scalarAction_monomial, hddeg]
    _ = c ^ m • p := by rw [← Finset.smul_sum, ← p.as_sum]

/-- The central parity formula holds on the whole homogeneous carrier. -/
theorem sourceRepresentation_centre (m : ℕ) (p : Carrier m) :
    sourceRepresentation m negativeIdentity p = (-1 : ℂ) ^ m • p := by
  apply Subtype.ext
  change polynomialAction (negativeIdentity : Mat2) (p : PolynomialSpace) =
    (-1 : ℂ) ^ m • (p : PolynomialSpace)
  have hcentre : (negativeIdentity : Mat2) = (-1 : ℂ) • (1 : Mat2) := by simp
  rw [hcentre]
  exact scalarAction_homogeneous (-1) p.property

theorem sourceRepresentation_centre_even {m : ℕ} (hm : Even m) (p : Carrier m) :
    sourceRepresentation m negativeIdentity p = p := by
  rw [sourceRepresentation_centre, hm.neg_one_pow, one_smul]

theorem sourceRepresentation_centre_odd {m : ℕ} (hm : Odd m) (p : Carrier m) :
    sourceRepresentation m negativeIdentity p = -p := by
  rw [sourceRepresentation_centre, hm.neg_one_pow]
  exact neg_one_smul ℂ p

end GeneratedFoundations.Geometry.SourceSymmetricPowers
