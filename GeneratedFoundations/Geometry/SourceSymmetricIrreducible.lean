module

public import GeneratedFoundations.Geometry.SourceSymmetricMixing
public import GeneratedFoundations.Geometry.SourceSymmetricUnitary
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducibility of all homogeneous source representations

A single actual diagonal source operation has distinct weights on every
fixed homogeneous degree. Its Lagrange polynomials are exactly the
coefficient projections onto the original polynomial modes. Consequently,
every source-invariant subspace is preserved by these projections.

The fixed rational mixing source connects every mode to the first one and
the first one to every mode. These two facts prove irreducibility directly
from invariance under the source group, without assuming invariance under
formal differential operators.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Module
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricWeights
open GeneratedFoundations.Geometry.SourceSymmetricMixing
open GeneratedFoundations.Geometry.SourceSymmetricUnitary

namespace GeneratedFoundations.Geometry.SourceSymmetricIrreducible

/-- The angle retains the half-angle convention of the original source axis. -/
def separatingSource (m : ℕ) : SU2 :=
  zElement (2 * Real.pi / ((m : ℝ) + 1))

def weightPhase (m : ℕ) (k : Fin (m + 1)) : ℝ :=
  (2 * (k.val : ℝ) - (m : ℝ)) * Real.pi / ((m : ℝ) + 1)

def weight (m : ℕ) (k : Fin (m + 1)) : ℂ :=
  Complex.exp (Complex.I * (weightPhase m k : ℂ))

theorem weightPhase_bounds (m : ℕ) (k : Fin (m + 1)) :
    -Real.pi < weightPhase m k ∧ weightPhase m k < Real.pi := by
  have hd : 0 < (m : ℝ) + 1 := by positivity
  have hk0 : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
  have hkm : (k.val : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ k.isLt
  constructor
  · apply (lt_div_iff₀ hd).mpr
    nlinarith [Real.pi_pos, mul_nonneg hk0 Real.pi_pos.le]
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hkm) Real.pi_pos.le]

theorem weight_injective (m : ℕ) : Function.Injective (weight m) := by
  intro k l h
  have hk := weightPhase_bounds m k
  have hl := weightPhase_bounds m l
  have hz : Complex.I * (weightPhase m k : ℂ) =
      Complex.I * (weightPhase m l : ℂ) :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by simpa using hk.1) (by simpa using hk.2.le)
      (by simpa using hl.1) (by simpa using hl.2.le) h
  have hr : weightPhase m k = weightPhase m l := by
    simpa using congrArg Complex.im hz
  have hd : (m : ℝ) + 1 ≠ 0 := by positivity
  have hnum : (2 * (k.val : ℝ) - (m : ℝ)) * Real.pi =
      (2 * (l.val : ℝ) - (m : ℝ)) * Real.pi := (div_left_inj' hd).mp hr
  have hkval : (k.val : ℝ) = (l.val : ℝ) := by
    have := mul_right_cancel₀ Real.pi_ne_zero hnum
    linarith
  apply Fin.ext
  exact_mod_cast hkval

theorem separatingSource_mode (m : ℕ) (k : Fin (m + 1)) :
    sourceRepresentation m (separatingSource m) (mode m k) =
      weight m k • mode m k := by
  rw [separatingSource, source_z_axis_weight]
  have hk : k.val ≤ m := Nat.le_of_lt_succ k.isLt
  have he :
      Complex.exp (-Complex.I * ((2 * Real.pi / ((m : ℝ) + 1) : ℝ) : ℂ) / 2) ^
          (m - k.val) *
        Complex.exp (Complex.I * ((2 * Real.pi / ((m : ℝ) + 1) : ℝ) : ℂ) / 2) ^
          k.val = weight m k := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    unfold weight weightPhase
    congr 1
    simp only [Nat.cast_sub hk, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_ofNat]
    ring
  rw [he]

/-- Projection defined using actual coefficients in the original carrier. -/
def modeProjection (m : ℕ) (k : Fin (m + 1)) : Module.End ℂ (Carrier m) where
  toFun p := (p : PolynomialSpace).coeff (exponentOfIndex m k).val • mode m k
  map_add' p q := by simp [add_smul]
  map_smul' c p := by simp [smul_smul]

@[simp] theorem modeProjection_apply (m : ℕ) (k : Fin (m + 1)) (p : Carrier m) :
    modeProjection m k p =
      (p : PolynomialSpace).coeff (exponentOfIndex m k).val • mode m k := rfl

/-- A polynomial in a concrete source operation, not an independently
postulated diagonal operator. -/
def weightProjector (m : ℕ) (k : Fin (m + 1)) : Module.End ℂ (Carrier m) :=
  Polynomial.aeval (sourceRepresentation m (separatingSource m))
    (Lagrange.basis Finset.univ (weight m) k)

theorem weightProjector_eq_modeProjection (m : ℕ) (k : Fin (m + 1)) :
    weightProjector m k = modeProjection m k := by
  apply linearMap_ext_modes
  intro j
  rw [weightProjector,
    Module.End.aeval_apply_of_mem_apply_eq_smul (separatingSource_mode m j)]
  by_cases h : k = j
  · subst j
    rw [Lagrange.eval_basis_self (weight_injective m).injOn (Finset.mem_univ k)]
    simp [mode_coefficient]
  · rw [Lagrange.eval_basis_of_ne h (Finset.mem_univ j)]
    simp [mode_coefficient, Ne.symm h]

/-- A subspace stable under one actual group operation is stable under all
polynomials in that operation. -/
theorem aeval_mem_of_source_invariant {m : ℕ} (S : Submodule ℂ (Carrier m))
    (U : SU2)
    (hS : ∀ p ∈ S, sourceRepresentation m U p ∈ S)
    (P : Polynomial ℂ) {p : Carrier m} (hp : p ∈ S) :
    Polynomial.aeval (sourceRepresentation m U) P p ∈ S := by
  refine P.induction_on ?_ ?_ ?_
  · intro a
    simpa only [Polynomial.aeval_C, Module.algebraMap_end_apply] using S.smul_mem a hp
  · intro P Q hP hQ
    simpa only [map_add, LinearMap.add_apply] using S.add_mem hP hQ
  · intro n a hn
    have hpoly : Polynomial.C a * Polynomial.X ^ (n + 1) =
        Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
    rw [hpoly, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact hS _ hn

theorem modeProjection_mem_of_source_invariant {m : ℕ}
    (S : Submodule ℂ (Carrier m))
    (hS : ∀ U : SU2, ∀ p ∈ S, sourceRepresentation m U p ∈ S)
    (k : Fin (m + 1)) {p : Carrier m} (hp : p ∈ S) :
    modeProjection m k p ∈ S := by
  rw [← weightProjector_eq_modeProjection]
  exact aeval_mem_of_source_invariant S (separatingSource m)
    (hS (separatingSource m)) _ hp

theorem mode_mem_of_coefficient_ne_zero {m : ℕ}
    (S : Submodule ℂ (Carrier m))
    (hS : ∀ U : SU2, ∀ p ∈ S, sourceRepresentation m U p ∈ S)
    (k : Fin (m + 1)) {p : Carrier m} (hp : p ∈ S)
    (hc : (p : PolynomialSpace).coeff (exponentOfIndex m k).val ≠ 0) :
    mode m k ∈ S :=
  (S.smul_mem_iff hc).mp (modeProjection_mem_of_source_invariant S hS k hp)

theorem exists_mode_coefficient_ne_zero {m : ℕ} {p : Carrier m} (hp : p ≠ 0) :
    ∃ k : Fin (m + 1), (p : PolynomialSpace).coeff (exponentOfIndex m k).val ≠ 0 := by
  have hp' : (p : PolynomialSpace) ≠ 0 := fun h => hp (Subtype.ext h)
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hp'
  have hdeg : d.degree = m := by
    by_contra h
    exact hd (p.property.coeff_eq_zero h)
  let k := exponentEquiv m ⟨d, hdeg⟩
  have he : (exponentOfIndex m k).val = d :=
    congrArg Subtype.val ((exponentEquiv m).symm_apply_apply ⟨d, hdeg⟩)
  exact ⟨k, by simpa only [he] using hd⟩

/-- Every nonzero invariant subspace of the original degree-`m` polynomial
carrier contains all modes and is therefore the entire carrier. -/
theorem invariant_eq_top {m : ℕ} (S : Submodule ℂ (Carrier m))
    (hS : ∀ U : SU2, ∀ p ∈ S, sourceRepresentation m U p ∈ S)
    (hne : S ≠ ⊥) : S = ⊤ := by
  obtain ⟨p, hp, hpn⟩ := S.ne_bot_iff.mp hne
  obtain ⟨k, hkcoeff⟩ := exists_mode_coefficient_ne_zero hpn
  have hk : mode m k ∈ S := mode_mem_of_coefficient_ne_zero S hS k hp hkcoeff
  have h0 : mode m 0 ∈ S := mode_mem_of_coefficient_ne_zero S hS 0
    (hS mixingSource _ hk) (mixing_to_top_ne_zero m k)
  have hall : ∀ j : Fin (m + 1), mode m j ∈ S := fun j =>
    mode_mem_of_coefficient_ne_zero S hS j
      (hS mixingSource _ h0) (mixing_from_top_ne_zero m j)
  have hspan : Submodule.span ℂ (Set.range (mode m)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hall j
  rw [mode_span] at hspan
  exact top_unique hspan

theorem invariant_eq_bot_or_top {m : ℕ} (S : Submodule ℂ (Carrier m))
    (hS : ∀ U : SU2, ∀ p ∈ S, sourceRepresentation m U p ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  rcases eq_or_ne S ⊥ with h | h
  · exact Or.inl h
  · exact Or.inr (invariant_eq_top S hS h)

/-- Irreducibility in the standard representation-theoretic sense, on the
original homogeneous submodule and for every natural degree. -/
theorem sourceRepresentation_irreducible (m : ℕ) :
    Representation.IsIrreducible (sourceRepresentation m) := by
  have hbt : (⊥ : Subrepresentation (sourceRepresentation m)) ≠ ⊤ := by
    intro h
    have hm : mode m 0 ∈ (⊤ : Subrepresentation (sourceRepresentation m)) :=
      Submodule.mem_top
    rw [← h] at hm
    exact mode_ne_zero m 0 ((Submodule.mem_bot ℂ).mp hm)
  let : Nontrivial (Subrepresentation (sourceRepresentation m)) := ⟨⟨⊥, ⊤, hbt⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  apply Subrepresentation.toSubmodule_injective
  change S.toSubmodule = ⊤
  apply invariant_eq_top S.toSubmodule (fun U p hp => S.apply_mem_toSubmodule U hp)
  intro hsub
  exact hS (Subrepresentation.toSubmodule_injective hsub)

/-- The already constructed unitary action, viewed as a linear representation. -/
def hilbertRepresentation (m : ℕ) : Representation ℂ SU2 (HilbertCarrier m) where
  toFun U := (unitaryAction m U).toLinearEquiv.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro p
    exact congrArg (fun e : HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m => e p)
      (unitaryRepresentation m).map_one
  map_mul' U V := by
    apply LinearMap.ext
    intro p
    exact congrArg (fun e : HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m => e p)
      ((unitaryRepresentation m).map_mul U V)

/-- The equivalence is the actual Haar orbit embedding onto its range. -/
def carrierRepresentationEquiv (m : ℕ) :
    (sourceRepresentation m).Equiv (hilbertRepresentation m) :=
  Representation.Equiv.mk (carrierEquiv m) (by
    intro U
    apply LinearMap.ext
    intro p
    exact (unitaryAction_apply_carrier m U p).symm)

/-- Irreducibility is retained by the continuous unitary Hilbert realization. -/
theorem hilbertRepresentation_irreducible (m : ℕ) :
    Representation.IsIrreducible (hilbertRepresentation m) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  let F := Representation.IntertwiningMap.equivLinearMapAsModule
    (sourceRepresentation m) (hilbertRepresentation m)
    (carrierRepresentationEquiv m).toIntertwiningMap
  have hF : Function.Bijective F := (carrierEquiv m).bijective
  have hsimple : IsSimpleModule (MonoidAlgebra ℂ SU2) (sourceRepresentation m).asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule (sourceRepresentation m)).mp
      (sourceRepresentation_irreducible m)
  exact (F.isSimpleModule_iff_of_bijective hF).mp hsimple

end GeneratedFoundations.Geometry.SourceSymmetricIrreducible
