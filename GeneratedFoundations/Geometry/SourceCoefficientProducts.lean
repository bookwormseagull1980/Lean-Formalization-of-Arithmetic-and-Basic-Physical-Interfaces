module

public import GeneratedFoundations.Geometry.SourceClebschGordan
public import GeneratedFoundations.Geometry.SourceSymmetricUnitary

/-!
# Products of coefficients of the actual source representations

A coefficient is a linear functional evaluated on the actual homogeneous
polynomial source orbit. Continuity follows from the complete polynomial
coefficient coordinates already constructed for that orbit. The linear span
contains the constant function and all entries of the original source matrix.

Multiplication by a degree-one coefficient preserves this same all-degree
span. For positive degree this is proved by the explicit Clebsch–Gordan
equivalence, applied to the tensor of the two functionals. Degree zero uses
the proved constancy of the actual degree-zero source action.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open Module
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceClebschGordan

namespace GeneratedFoundations.Geometry.SourceCoefficientProducts

theorem coefficient_continuous (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier m) :
    Continuous (fun U : SU2 => φ (sourceRepresentation m U v)) := by
  let F : Coordinate m →ₗ[ℂ] ℂ := φ.comp (coefficientEquiv m).symm.toLinearMap
  have h := F.continuous_of_finiteDimensional.comp (coefficientOrbit_continuous m v)
  change Continuous (fun U : SU2 =>
    φ ((coefficientEquiv m).symm (coefficientVector m (sourceRepresentation m U v)))) at h
  simpa only [← coefficientEquiv_apply, LinearEquiv.symm_apply_apply] using h

def coefficient (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier m) : C(SU2, ℂ) :=
  ⟨fun U => φ (sourceRepresentation m U v), coefficient_continuous m φ v⟩

@[simp] theorem coefficient_apply (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ)
    (v : Carrier m) (U : SU2) :
    coefficient m φ v U = φ (sourceRepresentation m U v) := rfl

def coefficientGenerators : Set C(SU2, ℂ) :=
  {f | ∃ (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier m), f = coefficient m φ v}

def coefficientSpan : Submodule ℂ C(SU2, ℂ) :=
  Submodule.span ℂ coefficientGenerators

theorem coefficient_mem (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier m) :
    coefficient m φ v ∈ coefficientSpan :=
  Submodule.subset_span ⟨m, φ, v, rfl⟩

theorem coefficient_constant_one :
    coefficient 0 constantEquiv.toLinearMap (constantEquiv.symm 1) = 1 := by
  ext U
  change constantEquiv (sourceRepresentation 0 U (constantEquiv.symm 1)) = 1
  rw [source_degreeZero, LinearEquiv.apply_symm_apply]

theorem one_mem : (1 : C(SU2, ℂ)) ∈ coefficientSpan := by
  rw [← coefficient_constant_one]
  exact coefficient_mem _ _ _

def coordinateFunctional (i : Fin 2) : Carrier 1 →ₗ[ℂ] ℂ :=
  (LinearMap.proj i).comp degreeOneEquiv.symm.toLinearMap

def coordinateVector (j : Fin 2) : Carrier 1 :=
  degreeOnePolynomial (Pi.single j 1)

/-- Every entry is a coefficient of the original two-dimensional source
action, through the actual degree-one polynomial identification. -/
theorem coefficient_sourceEntry (i j : Fin 2) :
    coefficient 1 (coordinateFunctional i) (coordinateVector j) = sourceEntry i j := by
  ext U
  change (degreeOneEquiv.symm
      (sourceRepresentation 1 U (degreeOnePolynomial (Pi.single j 1)))) i = (U : Mat2) i j
  rw [degreeOne_intertwines]
  change (degreeOneEquiv.symm (degreeOneEquiv ((U : Mat2).mulVec (Pi.single j 1)))) i = _
  rw [LinearEquiv.symm_apply_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sourceEntry_mem (i j : Fin 2) : sourceEntry i j ∈ coefficientSpan := by
  rw [← coefficient_sourceEntry]
  exact coefficient_mem _ _ _

/-- The tensor of the two given functionals, evaluated by scalar multiplication. -/
def tensorFunctional (m : ℕ) (φ : Carrier 1 →ₗ[ℂ] ℂ) (ψ : Carrier m →ₗ[ℂ] ℂ) :
    Carrier 1 ⊗[ℂ] Carrier m →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map φ ψ)

@[simp] theorem tensorFunctional_tmul (m : ℕ) (φ : Carrier 1 →ₗ[ℂ] ℂ)
    (ψ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier 1) (w : Carrier m) :
    tensorFunctional m φ ψ (v ⊗ₜ[ℂ] w) = φ v * ψ w := by
  simp [tensorFunctional, smul_eq_mul]

/-- Pull the tensor functional back through the explicit polynomial splitting. -/
def splitFunctional (k : ℕ) (φ : Carrier 1 →ₗ[ℂ] ℂ)
    (ψ : Carrier (k + 1) →ₗ[ℂ] ℂ) : Carrier (k + 2) × Carrier k →ₗ[ℂ] ℂ :=
  (tensorFunctional (k + 1) φ ψ).comp (clebschGordanLinear k).symm.toLinearMap

def upperFunctional (k : ℕ) (φ : Carrier 1 →ₗ[ℂ] ℂ)
    (ψ : Carrier (k + 1) →ₗ[ℂ] ℂ) : Carrier (k + 2) →ₗ[ℂ] ℂ :=
  (splitFunctional k φ ψ).comp (LinearMap.inl ℂ (Carrier (k + 2)) (Carrier k))

def lowerFunctional (k : ℕ) (φ : Carrier 1 →ₗ[ℂ] ℂ)
    (ψ : Carrier (k + 1) →ₗ[ℂ] ℂ) : Carrier k →ₗ[ℂ] ℂ :=
  (splitFunctional k φ ψ).comp (LinearMap.inr ℂ (Carrier (k + 2)) (Carrier k))

theorem splitFunctional_pair (k : ℕ) (φ : Carrier 1 →ₗ[ℂ] ℂ)
    (ψ : Carrier (k + 1) →ₗ[ℂ] ℂ) (v : Carrier (k + 2)) (w : Carrier k) :
    splitFunctional k φ ψ (v, w) = upperFunctional k φ ψ v + lowerFunctional k φ ψ w := by
  change splitFunctional k φ ψ (v, w) =
    splitFunctional k φ ψ (v, 0) + splitFunctional k φ ψ (0, w)
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using
    (splitFunctional k φ ψ).map_add (v, 0) (0, w)

/-- The product is explicitly the sum of two coefficients of the actual
upper and lower homogeneous source representations. -/
theorem degreeOne_mul_coefficient_succ (k : ℕ) (φ : Carrier 1 →ₗ[ℂ] ℂ)
    (v : Carrier 1) (ψ : Carrier (k + 1) →ₗ[ℂ] ℂ) (w : Carrier (k + 1)) :
    coefficient 1 φ v * coefficient (k + 1) ψ w =
      coefficient (k + 2) (upperFunctional k φ ψ)
          (clebschGordanLinear k (v ⊗ₜ[ℂ] w)).1 +
        coefficient k (lowerFunctional k φ ψ)
          (clebschGordanLinear k (v ⊗ₜ[ℂ] w)).2 := by
  ext U
  let s := clebschGordanLinear k (v ⊗ₜ[ℂ] w)
  have hcg := Representation.IntertwiningMap.isIntertwining _ _
    (clebschGordan k).toIntertwiningMap U (v ⊗ₜ[ℂ] w)
  change clebschGordanLinear k
      (((sourceRepresentation 1).tprod (sourceRepresentation (k + 1))) U (v ⊗ₜ[ℂ] w)) =
    (sourceRepresentation (k + 2) U s.1, sourceRepresentation k U s.2) at hcg
  have hback :
      ((sourceRepresentation 1).tprod (sourceRepresentation (k + 1))) U (v ⊗ₜ[ℂ] w) =
        (clebschGordanLinear k).symm
          (sourceRepresentation (k + 2) U s.1, sourceRepresentation k U s.2) := by
    apply (clebschGordanLinear k).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hcg
  change φ (sourceRepresentation 1 U v) * ψ (sourceRepresentation (k + 1) U w) =
    upperFunctional k φ ψ (sourceRepresentation (k + 2) U s.1) +
      lowerFunctional k φ ψ (sourceRepresentation k U s.2)
  calc
    _ = tensorFunctional (k + 1) φ ψ
        (sourceRepresentation 1 U v ⊗ₜ[ℂ] sourceRepresentation (k + 1) U w) :=
      (tensorFunctional_tmul _ _ _ _ _).symm
    _ = tensorFunctional (k + 1) φ ψ
        (((sourceRepresentation 1).tprod (sourceRepresentation (k + 1))) U (v ⊗ₜ[ℂ] w)) := rfl
    _ = splitFunctional k φ ψ
        (sourceRepresentation (k + 2) U s.1, sourceRepresentation k U s.2) := by
      exact congrArg (tensorFunctional (k + 1) φ ψ) hback
    _ = _ := splitFunctional_pair _ _ _ _ _

theorem degreeOne_mul_coefficient_zero (φ : Carrier 1 →ₗ[ℂ] ℂ) (v : Carrier 1)
    (ψ : Carrier 0 →ₗ[ℂ] ℂ) (w : Carrier 0) :
    coefficient 1 φ v * coefficient 0 ψ w = coefficient 1 ((ψ w) • φ) v := by
  ext U
  simp only [ContinuousMap.mul_apply, coefficient_apply, source_degreeZero,
    LinearMap.smul_apply, smul_eq_mul, mul_comm]

theorem degreeOne_mul_coefficient_mem (m : ℕ) (φ : Carrier 1 →ₗ[ℂ] ℂ)
    (v : Carrier 1) (ψ : Carrier m →ₗ[ℂ] ℂ) (w : Carrier m) :
    coefficient 1 φ v * coefficient m ψ w ∈ coefficientSpan := by
  cases m with
  | zero =>
      rw [degreeOne_mul_coefficient_zero]
      exact coefficient_mem _ _ _
  | succ k =>
      rw [degreeOne_mul_coefficient_succ]
      exact coefficientSpan.add_mem (coefficient_mem _ _ _) (coefficient_mem _ _ _)

/-- The proved product formula extends to every element of the same linear span. -/
theorem degreeOne_mul_mem (φ : Carrier 1 →ₗ[ℂ] ℂ) (v : Carrier 1)
    {f : C(SU2, ℂ)} (hf : f ∈ coefficientSpan) :
    coefficient 1 φ v * f ∈ coefficientSpan := by
  change f ∈ Submodule.span ℂ coefficientGenerators at hf
  refine Submodule.span_induction
    (fun g hg => ?_) ?_ (fun f g _ _ hfg hgg => ?_) (fun c f _ hcf => ?_) hf
  · obtain ⟨m, ψ, w, rfl⟩ := hg
    exact degreeOne_mul_coefficient_mem m φ v ψ w
  · rw [mul_zero]
    exact coefficientSpan.zero_mem
  · rw [mul_add]
    exact coefficientSpan.add_mem hfg hgg
  · rw [mul_smul_comm]
    exact coefficientSpan.smul_mem c hcf

theorem sourceEntry_mul_mem (i j : Fin 2) {f : C(SU2, ℂ)}
    (hf : f ∈ coefficientSpan) : sourceEntry i j * f ∈ coefficientSpan := by
  rw [← coefficient_sourceEntry]
  exact degreeOne_mul_mem _ _ hf

end GeneratedFoundations.Geometry.SourceCoefficientProducts
