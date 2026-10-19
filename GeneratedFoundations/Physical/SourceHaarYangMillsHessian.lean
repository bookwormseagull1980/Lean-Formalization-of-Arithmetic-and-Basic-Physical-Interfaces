module

public import GeneratedFoundations.Physical.SourceHaarYangMillsAction
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The closed Hessian on the original radial and colour field space

The connection space is the eightfold Hilbert product of the actual
coclosed quotient Haar fields. Its basis is assembled from the complete
differential curl basis, retaining every matrix-coefficient row and colour.
The radial direction is adjoined with the metric fixed by the source
response. No replacement sequence space or prescribed shell multiplicity
is used in constructing this operator.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate LinearPMap
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormClosedHodge
open GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum
open GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
open GeneratedFoundations.Geometry.SourceOneFormHodgeEnergy (lowestIndex)
open GeneratedFoundations.Operations
open GeneratedFoundations.Physical.SourceGeneratedYangMillsGap

namespace GeneratedFoundations.Physical.SourceHaarYangMillsHessian

abbrev ConnectionL2 := PiLp 2 (fun _ : Fin 8 => coclosedField)
abbrev ConnectionIndex := Fin 8 × CoclosedIndex

def connectionVector (a : ConnectionIndex) : ConnectionL2 :=
  PiLp.single 2 a.1 (coclosedHilbertBasis a.2)

theorem single_inner (a : Fin 8) (v : coclosedField) (A : ConnectionL2) :
    inner ℂ (PiLp.single 2 a v : ConnectionL2) A = inner ℂ v (A a) := by
  classical
  change (∑ i : Fin 8, inner ℂ ((PiLp.single 2 a v : ConnectionL2) i) (A i)) = _
  rw [Finset.sum_eq_single a]
  · simp only [PiLp.single_eq_same]
  · intro i _ hia
    simp only [PiLp.single_eq_of_ne _ hia, inner_zero_left]
  · simp

theorem connectionVector_orthonormal : Orthonormal ℂ connectionVector := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    simpa only [connectionVector, single_inner, PiLp.single_eq_same,
      Prod.mk.injEq, true_and] using
      orthonormal_iff_ite.mp coclosedHilbertBasis.orthonormal i j
  · have hpair : (a, i) ≠ (b, j) := fun h => hab (congrArg Prod.fst h)
    simp only [connectionVector, single_inner, PiLp.single_eq_of_ne _ hab, inner_zero_right,
      ite_eq_right hpair]

theorem connection_span_orthogonal :
    (Submodule.span ℂ (Set.range connectionVector))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  have hall (a : Fin 8) (i : CoclosedIndex) :
      inner ℂ (coclosedHilbertBasis i) (A a) = 0 := by
    have h := (Submodule.mem_orthogonal _ A).mp hA
      (connectionVector (a, i)) (Submodule.subset_span (Set.mem_range_self (a, i)))
    simpa only [connectionVector, single_inner] using h
  have hz (a : Fin 8) : A a = 0 := by
    apply coclosedHilbertBasis.repr.injective
    apply lp.ext
    funext i
    simp only [HilbertBasis.repr_apply_apply, hall, inner_zero_right]
  change A = 0
  apply (WithLp.equiv 2 (Fin 8 → coclosedField)).injective
  exact funext hz

def connectionBasis : HilbertBasis ConnectionIndex ℂ ConnectionL2 :=
  HilbertBasis.mkOfOrthogonalEqBot connectionVector_orthonormal connection_span_orthogonal

@[simp] theorem connectionBasis_apply (a : ConnectionIndex) :
    connectionBasis a = connectionVector a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    connectionVector_orthonormal connection_span_orthogonal) a

abbrev ResponseL2 := WithLp 2 (ℂ × ConnectionL2)
abbrev ResponseIndex := Option ConnectionIndex

def responseVector : ResponseIndex → ResponseL2
  | none => WithLp.toLp 2 (1, 0)
  | some a => WithLp.toLp 2 (0, connectionBasis a)

theorem radial_inner (x : ResponseL2) :
    inner ℂ (responseVector none) x = (WithLp.ofLp x).1 := by
  simp [responseVector, WithLp.prod_inner_apply]

theorem connection_inner (a : ConnectionIndex) (x : ResponseL2) :
    inner ℂ (responseVector (some a)) x =
      inner ℂ (connectionBasis a) (WithLp.ofLp x).2 := by
  simp [responseVector, WithLp.prod_inner_apply]

theorem responseVector_orthonormal : Orthonormal ℂ responseVector := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | none =>
      cases j with
      | none => simp [responseVector]
      | some b => simp [responseVector]
  | some a =>
      cases j with
      | none => simp [responseVector]
      | some b =>
          simp only [responseVector, WithLp.prod_inner_apply, inner_zero_left, zero_add,
            Option.some.injEq]
          exact orthonormal_iff_ite.mp connectionBasis.orthonormal a b

theorem response_span_orthogonal :
    (Submodule.span ℂ (Set.range responseVector))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hall (a : ResponseIndex) : inner ℂ (responseVector a) x = 0 :=
    (Submodule.mem_orthogonal _ x).mp hx (responseVector a)
      (Submodule.subset_span (Set.mem_range_self a))
  have hr : (WithLp.ofLp x).1 = 0 := by simpa only [radial_inner] using hall none
  have hc : (WithLp.ofLp x).2 = 0 := by
    apply connectionBasis.repr.injective
    apply lp.ext
    funext a
    simp only [HilbertBasis.repr_apply_apply, ← connection_inner, hall, inner_zero_right]
  change x = 0
  apply (WithLp.equiv 2 (ℂ × ConnectionL2)).injective
  exact Prod.ext hr hc

def responseBasis : HilbertBasis ResponseIndex ℂ ResponseL2 :=
  HilbertBasis.mkOfOrthogonalEqBot responseVector_orthonormal response_span_orthogonal

@[simp] theorem responseBasis_apply (a : ResponseIndex) : responseBasis a = responseVector a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    responseVector_orthonormal response_span_orthogonal) a

abbrev ResponseCore := FiniteEigenbasisCore.finiteSpan responseBasis

def responseCoreBasis : Module.Basis ResponseIndex ℂ ResponseCore :=
  FiniteEigenbasisCore.finiteBasis responseBasis

def radialProjection : ResponseL2 →ₗ[ℂ] ℂ where
  toFun x := (WithLp.ofLp x).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def connectionProjection (a : Fin 8) : ResponseL2 →ₗ[ℂ] coclosedField where
  toFun x := (WithLp.ofLp x).2 a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem connectionProjection_core_mem (a : Fin 8) (x : ResponseCore) :
    connectionProjection a (x : ResponseL2) ∈ Core := by
  classical
  have hs : ResponseCore ≤ Core.comap (connectionProjection a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change connectionProjection a (responseBasis i) ∈ Core
    rw [responseBasis_apply]
    cases i with
    | none =>
        change (0 : coclosedField) ∈ Core
        exact Core.zero_mem
    | some i =>
        by_cases ha : a = i.1
        · subst a
          change (connectionBasis i) i.1 ∈ Core
          rw [connectionBasis_apply, connectionVector, PiLp.single_eq_same]
          exact FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis
            hodgeEigenvalue i.2
        · change (connectionBasis i) a ∈ Core
          rw [connectionBasis_apply, connectionVector, PiLp.single_eq_of_ne _ ha]
          exact Core.zero_mem
  exact hs x.property

/-- Restriction of an original colour component to its actual differential
core. Membership follows from the full response core, rather than being
assumed for an arbitrary Haar field. -/
def coreConnection (a : Fin 8) : ResponseCore →ₗ[ℂ] Core where
  toFun x := ⟨connectionProjection a (x : ResponseL2), connectionProjection_core_mem a x⟩
  map_add' x y := Subtype.ext (map_add (connectionProjection a) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (connectionProjection a) c x.val)

@[simp] theorem coreConnection_basis (a : Fin 8) (i : ResponseIndex) :
    coreConnection a (responseCoreBasis i) =
      match i with
      | none => 0
      | some j => if a = j.1 then coreBasis j.2 else 0 := by
  classical
  apply Subtype.ext
  cases i with
  | none =>
      simp [coreConnection, responseCoreBasis, connectionProjection, responseVector]
  | some j =>
      by_cases ha : a = j.1
      · subst a
        simp [coreConnection, responseCoreBasis, connectionProjection, responseVector,
          connectionVector, coreBasis]
      · simp [coreConnection, responseCoreBasis, connectionProjection, responseVector,
        connectionVector, ha]

@[simp] theorem radialProjection_basis (i : ResponseIndex) :
    radialProjection (responseCoreBasis i : ResponseL2) =
      match i with | none => 1 | some _ => 0 := by
  cases i <;> simp [radialProjection, responseCoreBasis, responseVector]

def responseEigenvalue (L z : ℝ) : ResponseIndex → ℝ
  | none => normalizedRadialMassSq z
  | some a => SourceHaarConnectionHessian.responseEigenvalue L z a.2

def finiteOperator (L z : ℝ) : ResponseL2 →ₗ.[ℂ] ResponseL2 :=
  FiniteEigenbasisCore.finiteMultiplier responseBasis (responseEigenvalue L z)

/-- Reconstruct the differentiated operator on the original colour fields,
with the source radial coefficient on its one-dimensional factor. -/
def differentialCore (L z : ℝ) : ResponseCore →ₗ[ℂ] ResponseL2 where
  toFun x := WithLp.toLp 2
    ((normalizedRadialMassSq z : ℂ) * radialProjection x.val,
      WithLp.toLp 2 (fun a => SourceHaarConnectionHessian.finiteOperator L z
        (coreConnection a x)))
  map_add' x y := by
    apply (WithLp.linearEquiv 2 ℂ (ℂ × ConnectionL2)).injective
    apply Prod.ext
    · change (normalizedRadialMassSq z : ℂ) * radialProjection (x.val + y.val) =
        (normalizedRadialMassSq z : ℂ) * radialProjection x.val +
          (normalizedRadialMassSq z : ℂ) * radialProjection y.val
      rw [map_add, mul_add]
    · apply (WithLp.linearEquiv 2 ℂ (Fin 8 → coclosedField)).injective
      funext a
      change SourceHaarConnectionHessian.finiteOperator L z
        (coreConnection a (x + y)) =
          SourceHaarConnectionHessian.finiteOperator L z (coreConnection a x) +
            SourceHaarConnectionHessian.finiteOperator L z (coreConnection a y)
      rw [map_add]
      exact map_add (SourceHaarConnectionHessian.finiteOperator L z).toFun _ _
  map_smul' c x := by
    apply (WithLp.linearEquiv 2 ℂ (ℂ × ConnectionL2)).injective
    apply Prod.ext
    · change (normalizedRadialMassSq z : ℂ) * radialProjection (c • x.val) =
        c * ((normalizedRadialMassSq z : ℂ) * radialProjection x.val)
      rw [map_smul]
      simp only [smul_eq_mul]
      ring
    · apply (WithLp.linearEquiv 2 ℂ (Fin 8 → coclosedField)).injective
      funext a
      change SourceHaarConnectionHessian.finiteOperator L z
        (coreConnection a (c • x)) =
          c • SourceHaarConnectionHessian.finiteOperator L z (coreConnection a x)
      rw [map_smul]
      exact map_smul (SourceHaarConnectionHessian.finiteOperator L z).toFun c _

/-- Equality on every finite source field, proved before closing either
graph. The connection coefficients were already identified with two
applications of the original source curl. -/
theorem finiteOperator_eq_differentialCore (L z : ℝ) :
    (finiteOperator L z).toFun = differentialCore L z := by
  classical
  apply responseCoreBasis.ext
  intro i
  have hb : responseCoreBasis i =
      (⟨responseBasis i,
        FiniteEigenbasisCore.basis_mem_domain responseBasis (responseEigenvalue L z) i⟩ :
        (finiteOperator L z).domain) :=
    Subtype.ext (FiniteEigenbasisCore.finiteBasis_coe responseBasis i)
  have ha : finiteOperator L z (responseCoreBasis i) =
      (responseEigenvalue L z i : ℂ) • responseBasis i := by
    rw [hb]
    exact FiniteEigenbasisCore.basis_action responseBasis (responseEigenvalue L z) i
  change finiteOperator L z (responseCoreBasis i) = _
  rw [ha]
  rw [responseBasis_apply]
  cases i with
  | none =>
      apply (WithLp.linearEquiv 2 ℂ (ℂ × ConnectionL2)).injective
      apply Prod.ext
      · change (normalizedRadialMassSq z : ℂ) * 1 =
          (normalizedRadialMassSq z : ℂ) * radialProjection (responseCoreBasis none).val
        rw [radialProjection_basis]
      · apply (WithLp.linearEquiv 2 ℂ (Fin 8 → coclosedField)).injective
        funext a
        change ((normalizedRadialMassSq z : ℂ) • (0 : ConnectionL2)) a =
          SourceHaarConnectionHessian.finiteOperator L z
            (coreConnection a (responseCoreBasis none))
        rw [smul_zero, coreConnection_basis]
        exact (map_zero (SourceHaarConnectionHessian.finiteOperator L z).toFun).symm
  | some j =>
      apply (WithLp.linearEquiv 2 ℂ (ℂ × ConnectionL2)).injective
      apply Prod.ext
      · change (responseEigenvalue L z (some j) : ℂ) * 0 =
          (normalizedRadialMassSq z : ℂ) * radialProjection (responseCoreBasis (some j)).val
        rw [radialProjection_basis, mul_zero, mul_zero]
      · apply (WithLp.linearEquiv 2 ℂ (Fin 8 → coclosedField)).injective
        funext a
        change ((responseEigenvalue L z (some j) : ℂ) • connectionBasis j) a =
          SourceHaarConnectionHessian.finiteOperator L z
            (coreConnection a (responseCoreBasis (some j)))
        simp only [coreConnection_basis]
        rw [connectionBasis_apply]
        change (responseEigenvalue L z (some j) : ℂ) •
          (PiLp.single 2 j.1 (coclosedHilbertBasis j.2) : ConnectionL2) a = _
        by_cases ha : a = j.1
        · subst a
          have hc : coreBasis j.2 =
              (⟨coclosedHilbertBasis j.2,
                FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis
                  (SourceHaarConnectionHessian.responseEigenvalue L z) j.2⟩ :
                (SourceHaarConnectionHessian.finiteOperator L z).domain) :=
            Subtype.ext (FiniteEigenbasisCore.finiteBasis_coe coclosedHilbertBasis j.2)
          rw [PiLp.single_eq_same, ite_eq_left rfl]
          change (SourceHaarConnectionHessian.responseEigenvalue L z j.2 : ℂ) •
            coclosedHilbertBasis j.2 = _
          rw [hc]
          exact (FiniteEigenbasisCore.basis_action coclosedHilbertBasis
            (SourceHaarConnectionHessian.responseEigenvalue L z) j.2).symm
        · rw [PiLp.single_eq_of_ne _ ha, ite_eq_right ha, smul_zero]
          exact (map_zero (SourceHaarConnectionHessian.finiteOperator L z).toFun).symm

theorem finiteOperator_energy (L z : ℝ) (x : ResponseCore) :
    (inner ℂ (x : ResponseL2) (finiteOperator L z x)).re =
      normalizedRadialMassSq z * ‖radialProjection x.val‖ ^ 2 +
        ∑ a : Fin 8, (inner ℂ (coreConnection a x : coclosedField)
          (SourceHaarConnectionHessian.finiteOperator L z (coreConnection a x))).re := by
  have hr (r : ℂ) :
      (inner ℂ r ((normalizedRadialMassSq z : ℂ) * r)).re =
        normalizedRadialMassSq z * ‖r‖ ^ 2 := by
    change (inner ℂ r ((normalizedRadialMassSq z : ℂ) • r)).re = _
    rw [inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hn : (inner ℂ r r).re = ‖r‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) r).symm
    rw [hn]
  have hx := LinearMap.congr_fun (finiteOperator_eq_differentialCore L z) x
  change finiteOperator L z x = differentialCore L z x at hx
  rw [hx]
  change (inner ℂ (x : ResponseL2) (differentialCore L z x)).re = _
  rw [WithLp.prod_inner_apply]
  change (inner ℂ (radialProjection x.val)
      ((normalizedRadialMassSq z : ℂ) * radialProjection x.val) +
    ∑ a : Fin 8, inner ℂ (coreConnection a x : coclosedField)
      (SourceHaarConnectionHessian.finiteOperator L z (coreConnection a x))).re = _
  rw [Complex.add_re, hr]
  congr 1

/-- On the real radial slice, the actual nonlinear-action Hessian is
exactly the form of the full field operator. No mixed block has been
discarded in identifying these two forms. -/
theorem action_quadratic_eq_operator (L z radial : ℝ) (x : ResponseCore)
    (hr : radialProjection x.val = (radial : ℂ)) :
    SourceHaarYangMillsAction.quadratic L z radial (fun a => coreConnection a x) =
      (inner ℂ (x : ResponseL2) (finiteOperator L z x)).re := by
  rw [SourceHaarYangMillsAction.quadratic_eq_operator, finiteOperator_energy, hr]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  congr 1

/-- The equality is obtained by differentiating the full nonlinear action
at the generated radial source, rather than by defining a quadratic action. -/
theorem action_secondDeriv {z : ℝ} (hz : 0 < z) (L radial : ℝ)
    (x : ResponseCore) (hr : radialProjection x.val = (radial : ℂ)) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ =>
      SourceHaarYangMillsAction.action L z (u * radial)
        ((u : ℂ) • (fun a => coreConnection a x))) t)
      (inner ℂ (x : ResponseL2) (finiteOperator L z x)).re 0 := by
  rw [← action_quadratic_eq_operator L z radial x hr]
  exact SourceHaarYangMillsAction.action_secondDeriv hz L radial
    (fun a => coreConnection a x)

def operator (L z : ℝ) : ResponseL2 →ₗ.[ℂ] ResponseL2 :=
  (finiteOperator L z).closure

theorem operator_selfAdjoint (L z : ℝ) : IsSelfAdjoint (operator L z) :=
  FiniteEigenbasisCore.closure_selfAdjoint responseBasis (responseEigenvalue L z)

theorem operator_unique (L z : ℝ) (S : ResponseL2 →ₗ.[ℂ] ResponseL2)
    (hS : IsSelfAdjoint S) (hcore : finiteOperator L z ≤ S) : S = operator L z :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique responseBasis
    (responseEigenvalue L z) S hS hcore

theorem operator_domain (L z : ℝ) (x : ResponseL2) :
    x ∈ (operator L z).domain ↔
      Summable (fun a : ResponseIndex => responseEigenvalue L z a ^ 2 *
        ‖inner ℂ (responseBasis a) x‖ ^ 2) :=
  FiniteEigenbasisCore.closure_domain_iff_summable responseBasis (responseEigenvalue L z) x

theorem eigenvalue_lower (L z : ℝ) (a : ResponseIndex) :
    generatedYangMillsGapSq L z ≤ responseEigenvalue L z a := by
  cases a with
  | none => exact generatedYangMillsGapSq_le_radial L z
  | some a =>
      have h : generatedYangMillsGapSq L z ≤
          4 / L ^ 2 + coclosedResponseShift L z := by
        simpa only [coclosedMassIndex, SourceRP3FieldSpectrum.vectorEigenvalue_one] using
          (generatedYangMillsGapSq_le_coclosed (L := L) (z := z) (l := 1) (by norm_num))
      exact h.trans (SourceHaarConnectionHessian.eigenvalue_lower L z a.2)

/-- The full closed graph, on the original fields, obeys the same bound.
All matrix-coefficient and colour directions are included in its domain. -/
theorem complete_coercivity (L z : ℝ) (x : (operator L z).domain) :
    generatedYangMillsGapSq L z * ‖(x : ResponseL2)‖ ^ 2 ≤
      (inner ℂ (x : ResponseL2) (operator L z x)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound responseBasis
    (responseEigenvalue L z) _ (eigenvalue_lower L z) x

def minimizingIndex (L z : ℝ) : ResponseIndex :=
  if normalizedRadialMassSq z ≤ 4 / L ^ 2 + coclosedResponseShift L z then none
  else some (0, lowestIndex)

theorem eigenvalue_minimizingIndex (L z : ℝ) :
    responseEigenvalue L z (minimizingIndex L z) = generatedYangMillsGapSq L z := by
  have hc : coclosedMassIndex L z 1 = 4 / L ^ 2 + coclosedResponseShift L z := by
    rw [coclosedMassIndex, SourceRP3FieldSpectrum.vectorEigenvalue_one]
  unfold minimizingIndex generatedYangMillsGapSq
  rw [hc]
  split_ifs with h
  · exact (min_eq_left h).symm
  · simpa only [responseEigenvalue, SourceHaarConnectionHessian.responseEigenvalue_lowest]
      using (min_eq_right (le_of_not_ge h)).symm

theorem basis_mem_domain (L z : ℝ) (a : ResponseIndex) :
    responseBasis a ∈ (operator L z).domain :=
  (FiniteEigenbasisCore.le_closure responseBasis (responseEigenvalue L z)).1
    (FiniteEigenbasisCore.basis_mem_domain responseBasis (responseEigenvalue L z) a)

theorem operator_basis (L z : ℝ) (a : ResponseIndex) :
    operator L z ⟨responseBasis a, basis_mem_domain L z a⟩ =
      (responseEigenvalue L z a : ℂ) • responseBasis a := by
  have h := (FiniteEigenbasisCore.le_closure responseBasis (responseEigenvalue L z)).2
    (x := ⟨responseBasis a,
      FiniteEigenbasisCore.basis_mem_domain responseBasis (responseEigenvalue L z) a⟩)
    (y := ⟨responseBasis a, basis_mem_domain L z a⟩) rfl
  exact h.symm.trans (FiniteEigenbasisCore.basis_action responseBasis (responseEigenvalue L z) a)

/-- The lower edge is attained by a radial or an actual constant-frame
Haar field in one generated colour direction. -/
theorem gap_attained (L z : ℝ) :
    operator L z ⟨responseBasis (minimizingIndex L z),
      basis_mem_domain L z (minimizingIndex L z)⟩ =
      (generatedYangMillsGapSq L z : ℂ) • responseBasis (minimizingIndex L z) := by
  rw [operator_basis, eigenvalue_minimizingIndex]

end GeneratedFoundations.Physical.SourceHaarYangMillsHessian
