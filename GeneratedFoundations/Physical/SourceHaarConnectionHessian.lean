module

public import GeneratedFoundations.Geometry.SourceOneFormHodgeEnergy
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsGap

/-!
# The connection Hessian on the original Haar field space

The finite operator is identified with the square of the actual source curl,
scaled by the generated radius, and the Gaussian colour-covariance response.
Its unique closed extension acts on the existing divergence kernel. Thus
the closed-domain lower bound is a field-space statement rather than an
estimate on an independently labelled shell sequence.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate LinearPMap
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum
open GeneratedFoundations.Geometry.SourceOneFormClosedHodge
open GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum
open GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
open GeneratedFoundations.Geometry.SourceOneFormHodgeEnergy
open GeneratedFoundations.Operations
open GeneratedFoundations.Physical.SourceGeneratedYangMillsGap

namespace GeneratedFoundations.Physical.SourceHaarConnectionHessian

def responseEigenvalue (L z : ℝ) (a : CoclosedIndex) : ℝ :=
  hodgeEigenvalue a / L ^ 2 + coclosedResponseShift L z

def finiteOperator (L z : ℝ) : coclosedField →ₗ.[ℂ] coclosedField :=
  FiniteEigenbasisCore.finiteMultiplier coclosedHilbertBasis (responseEigenvalue L z)

theorem finiteOperator_core (L z : ℝ) (A : Core) :
    finiteOperator L z A =
      ((1 / L ^ 2 : ℝ) : ℂ) • finiteHodge A +
        (coclosedResponseShift L z : ℂ) • (A : coclosedField) := by
  have h : ((finiteOperator L z).toFun : Core →ₗ[ℂ] coclosedField) =
      ((1 / L ^ 2 : ℝ) : ℂ) •
          (Core.subtype.comp (coreCurl.comp coreCurl)) +
        (coclosedResponseShift L z : ℂ) •
          (FiniteEigenbasisCore.finiteSpan coclosedHilbertBasis).subtype := by
    apply coreBasis.ext
    intro a
    have hb : coreBasis a =
        (⟨coclosedHilbertBasis a,
          FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis
            (responseEigenvalue L z) a⟩ : (finiteOperator L z).domain) :=
      Subtype.ext (FiniteEigenbasisCore.finiteBasis_coe coclosedHilbertBasis a)
    have hh : finiteHodge (coreBasis a) =
        (hodgeEigenvalue a : ℂ) • coclosedHilbertBasis a := by
      have hb' : coreBasis a =
          (⟨coclosedHilbertBasis a,
            FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis hodgeEigenvalue a⟩ :
              finiteHodge.domain) :=
        Subtype.ext (FiniteEigenbasisCore.finiteBasis_coe coclosedHilbertBasis a)
      rw [hb']
      exact FiniteEigenbasisCore.basis_action coclosedHilbertBasis hodgeEigenvalue a
    have ha : finiteOperator L z (coreBasis a) =
        (responseEigenvalue L z a : ℂ) • coclosedHilbertBasis a := by
      rw [hb]
      exact FiniteEigenbasisCore.basis_action coclosedHilbertBasis (responseEigenvalue L z) a
    change finiteOperator L z (coreBasis a) = _
    rw [ha]
    change (responseEigenvalue L z a : ℂ) • coclosedHilbertBasis a =
      ((1 / L ^ 2 : ℝ) : ℂ) •
          ((coreCurl.comp coreCurl (coreBasis a) : Core) : coclosedField) +
        (coclosedResponseShift L z : ℂ) • (coreBasis a : coclosedField)
    rw [← finiteHodge_core, hh]
    simp only [coreBasis, FiniteEigenbasisCore.finiteBasis_coe, responseEigenvalue,
      Complex.ofReal_add, smul_smul, div_eq_mul_inv, one_mul, ← add_smul]
    congr 1
    push_cast
    ring
  rw [finiteHodge_core]
  exact LinearMap.congr_fun h A

/-- The local differential term retains the actual intermediate curl domain. -/
theorem finiteOperator_differential (L z : ℝ) (A : Core) :
    (finiteOperator L z A : OneFormL2) =
      ((1 / L ^ 2 : ℝ) : ℂ) • closedCurl (coreToCurlDomain (coreCurl A)) +
        (coclosedResponseShift L z : ℂ) • includeCore A := by
  rw [finiteOperator_core]
  change ((1 / L ^ 2 : ℝ) : ℂ) • (finiteHodge A : OneFormL2) +
    (coclosedResponseShift L z : ℂ) • includeCore A = _
  rw [finiteHodge_is_twice_curl]

theorem finiteOperator_energy (L z : ℝ) (A : Core) :
    (inner ℂ (A : coclosedField) (finiteOperator L z A)).re =
      ‖(coreCurl A : coclosedField)‖ ^ 2 / L ^ 2 +
        coclosedResponseShift L z * ‖(A : coclosedField)‖ ^ 2 := by
  rw [finiteOperator_core, inner_add_right, inner_smul_right, inner_smul_right]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  rw [finiteHodge_energy]
  have hn : (inner ℂ (A : coclosedField) (A : coclosedField)).re =
      ‖(A : coclosedField)‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (A : coclosedField)).symm
  rw [hn]
  ring

def operator (L z : ℝ) : coclosedField →ₗ.[ℂ] coclosedField :=
  (finiteOperator L z).closure

theorem operator_selfAdjoint (L z : ℝ) : IsSelfAdjoint (operator L z) :=
  FiniteEigenbasisCore.closure_selfAdjoint coclosedHilbertBasis (responseEigenvalue L z)

theorem operator_unique (L z : ℝ) (S : coclosedField →ₗ.[ℂ] coclosedField)
    (hS : IsSelfAdjoint S) (hcore : finiteOperator L z ≤ S) :
    S = operator L z :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique coclosedHilbertBasis
    (responseEigenvalue L z) S hS hcore

theorem operator_domain (L z : ℝ) (A : coclosedField) :
    A ∈ (operator L z).domain ↔
      Summable (fun a : CoclosedIndex => responseEigenvalue L z a ^ 2 *
        ‖inner ℂ (coclosedHilbertBasis a) A‖ ^ 2) :=
  FiniteEigenbasisCore.closure_domain_iff_summable coclosedHilbertBasis
    (responseEigenvalue L z) A

theorem eigenvalue_lower (L z : ℝ) (a : CoclosedIndex) :
    4 / L ^ 2 + coclosedResponseShift L z ≤ responseEigenvalue L z a := by
  unfold responseEigenvalue
  exact add_le_add
    (div_le_div_of_nonneg_right (coclosed_eigenvalue_sq_ge_four a) (sq_nonneg L)) le_rfl

/-- The full-domain field estimate; its constant has no dependence on the
number of source rows or the differential cutoff. -/
theorem complete_coercivity (L z : ℝ) (A : (operator L z).domain) :
    (4 / L ^ 2 + coclosedResponseShift L z) * ‖(A : coclosedField)‖ ^ 2 ≤
      (inner ℂ (A : coclosedField) (operator L z A)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound coclosedHilbertBasis
    (responseEigenvalue L z) _ (eigenvalue_lower L z) A

theorem responseEigenvalue_lowest (L z : ℝ) :
    responseEigenvalue L z lowestIndex = 4 / L ^ 2 + coclosedResponseShift L z := by
  rw [responseEigenvalue, hodgeEigenvalue_lowest]

theorem lowest_mem_domain (L z : ℝ) :
    coclosedHilbertBasis lowestIndex ∈ (operator L z).domain :=
  (FiniteEigenbasisCore.le_closure coclosedHilbertBasis (responseEigenvalue L z)).1
    (FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis
      (responseEigenvalue L z) lowestIndex)

theorem operator_lowest (L z : ℝ) :
    operator L z ⟨coclosedHilbertBasis lowestIndex, lowest_mem_domain L z⟩ =
      ((4 / L ^ 2 + coclosedResponseShift L z : ℝ) : ℂ) •
        coclosedHilbertBasis lowestIndex := by
  have h := (FiniteEigenbasisCore.le_closure coclosedHilbertBasis
    (responseEigenvalue L z)).2
    (x := ⟨coclosedHilbertBasis lowestIndex,
      FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis
        (responseEigenvalue L z) lowestIndex⟩)
    (y := ⟨coclosedHilbertBasis lowestIndex, lowest_mem_domain L z⟩) rfl
  calc
    operator L z ⟨coclosedHilbertBasis lowestIndex, lowest_mem_domain L z⟩ =
        finiteOperator L z ⟨coclosedHilbertBasis lowestIndex,
          FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis
            (responseEigenvalue L z) lowestIndex⟩ := h.symm
    _ = (responseEigenvalue L z lowestIndex : ℂ) •
        coclosedHilbertBasis lowestIndex :=
      FiniteEigenbasisCore.basis_action coclosedHilbertBasis (responseEigenvalue L z) lowestIndex
    _ = ((4 / L ^ 2 + coclosedResponseShift L z : ℝ) : ℂ) •
        coclosedHilbertBasis lowestIndex := by rw [responseEigenvalue_lowest]

end GeneratedFoundations.Physical.SourceHaarConnectionHessian
