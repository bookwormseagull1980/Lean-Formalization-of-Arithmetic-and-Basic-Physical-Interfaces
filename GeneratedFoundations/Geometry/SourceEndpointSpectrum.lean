module

public import GeneratedFoundations.Geometry.SourceEndpointCasimir
public import GeneratedFoundations.Geometry.SourceQuotientSpectrum

/-!
# Full quotient spectrum at the generated endpoint radius

The bounded inverse is obtained from the actual unit-radius quotient
resolvent. Its range lies in the complete rescaled differential domain,
and both inverse identities hold there. Scaling therefore preserves the
eigenspaces and their multiplicities as well as compactness of the
resolvent. The endpoint formula is a specialization to the previously
generated global correlation length.
-/

@[expose] public section

noncomputable section

open scoped BigOperators LinearPMap
open GeneratedFoundations.Operations
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceEndpointCasimir
open GeneratedFoundations.Geometry.SourceCasimirClosure (energy)

namespace GeneratedFoundations.Geometry.SourceEndpointSpectrum

private theorem coefficient_ne_zero {R : ℝ} (hR : R ≠ 0) :
    (inverseSquare R : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (inverseSquare_ne_zero hR)

def shifted (R : ℝ) (z : ℂ) : (operator R).domain →ₗ[ℂ] QuotientL2 :=
  (operator R).toFun - z • (operator R).domain.subtype

theorem unscaled_regular {R : ℝ} (hR : R ≠ 0) (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ)) :
    ∀ m : ℕ, Even m → z / (inverseSquare R : ℂ) ≠ (energy m : ℂ) := by
  intro m hm he
  apply hz m hm
  have h := (div_eq_iff (coefficient_ne_zero hR)).mp he
  simpa only [scaledEnergy, Complex.ofReal_mul, mul_comm] using h

def resolvent {R : ℝ} (hR : R ≠ 0) (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ)) :
    QuotientL2 →L[ℂ] QuotientL2 :=
  (inverseSquare R : ℂ)⁻¹ •
    SourceQuotientSpectrum.resolvent (z / (inverseSquare R : ℂ)) (unscaled_regular hR z hz)

theorem resolvent_coefficients {R : ℝ} (hR : R ≠ 0) (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ))
    (f : QuotientL2) (a : EvenIndex) :
    inner ℂ (quotientBasisVector a) (resolvent hR z hz f) =
      ((scaledEnergy R a.val.1 : ℂ) - z)⁻¹ * inner ℂ (quotientBasisVector a) f := by
  simp only [resolvent, _root_.smul_apply, inner_smul_right,
    SourceQuotientSpectrum.resolvent_coefficients, SourceCasimirResolvent.inverseCoefficient]
  have hc := coefficient_ne_zero hR
  have hd : (energy a.val.1 : ℂ) - z / (inverseSquare R : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (unscaled_regular hR z hz a.val.1 a.property).symm
  have hs : (scaledEnergy R a.val.1 : ℂ) - z ≠ 0 :=
    sub_ne_zero.mpr (hz a.val.1 a.property).symm
  simp only [scaledEnergy, Complex.ofReal_mul] at hs ⊢
  field_simp [hc, hd, hs]

theorem resolvent_mem_domain {R : ℝ} (hR : R ≠ 0) (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ)) (f : QuotientL2) :
    resolvent hR z hz f ∈ (operator R).domain := by
  apply (operator_domain_iff hR _).mpr
  exact SourceQuotientCasimir.operator.domain.smul_mem (inverseSquare R : ℂ)⁻¹
    (SourceQuotientSpectrum.resolvent_mem_domain
      (z / (inverseSquare R : ℂ)) (unscaled_regular hR z hz) f)

theorem resolvent_right_inverse {R : ℝ} (hR : R ≠ 0) (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ)) (f : QuotientL2) :
    shifted R z ⟨resolvent hR z hz f, resolvent_mem_domain hR z hz f⟩ = f := by
  apply EigenbasisClosure.eq_of_coefficients quotientBasis
  intro a
  rw [quotientBasis_apply]
  change inner ℂ (quotientBasisVector a)
    (operator R ⟨resolvent hR z hz f, resolvent_mem_domain hR z hz f⟩ -
      z • resolvent hR z hz f) = _
  rw [inner_sub_right, operator_coefficients, inner_smul_right, resolvent_coefficients]
  have hd : (scaledEnergy R a.val.1 : ℂ) - z ≠ 0 :=
    sub_ne_zero.mpr (hz a.val.1 a.property).symm
  field_simp [hd]

theorem resolvent_left_inverse {R : ℝ} (hR : R ≠ 0) (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ)) (u : (operator R).domain) :
    resolvent hR z hz (shifted R z u) = (u : QuotientL2) := by
  apply EigenbasisClosure.eq_of_coefficients quotientBasis
  intro a
  rw [quotientBasis_apply, resolvent_coefficients]
  change ((scaledEnergy R a.val.1 : ℂ) - z)⁻¹ *
    inner ℂ (quotientBasisVector a) (operator R u - z • (u : QuotientL2)) = _
  rw [inner_sub_right, operator_coefficients, inner_smul_right]
  have hd : (scaledEnergy R a.val.1 : ℂ) - z ≠ 0 :=
    sub_ne_zero.mpr (hz a.val.1 a.property).symm
  field_simp [hd]

structure IsResolvent (R : ℝ) (z : ℂ) (S : QuotientL2 →L[ℂ] QuotientL2) : Prop where
  mem_domain : ∀ f, S f ∈ (operator R).domain
  right_inverse : ∀ f, shifted R z ⟨S f, mem_domain f⟩ = f
  left_inverse : ∀ u : (operator R).domain, S (shifted R z u) = (u : QuotientL2)

theorem resolvent_spec {R : ℝ} (hR : R ≠ 0) (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ)) :
    IsResolvent R z (resolvent hR z hz) where
  mem_domain := resolvent_mem_domain hR z hz
  right_inverse := resolvent_right_inverse hR z hz
  left_inverse := resolvent_left_inverse hR z hz

theorem IsResolvent.unique {R : ℝ} {z : ℂ} {S T : QuotientL2 →L[ℂ] QuotientL2}
    (hS : IsResolvent R z S) (hT : IsResolvent R z T) : S = T := by
  apply ContinuousLinearMap.ext
  intro f
  calc
    S f = S (shifted R z ⟨T f, hT.mem_domain f⟩) := by rw [hT.right_inverse]
    _ = T f := hS.left_inverse ⟨T f, hT.mem_domain f⟩

theorem IsResolvent.not_eigenvalue {R : ℝ} {z : ℂ} {S : QuotientL2 →L[ℂ] QuotientL2}
    (hS : IsResolvent R z S) (m : ℕ) (hm : Even m) : z ≠ (scaledEnergy R m : ℂ) := by
  intro hz
  subst z
  let a : EvenIndex := ⟨⟨m, 0, 0⟩, hm⟩
  let u : (operator R).domain := ⟨quotientBasisVector a, basis_mem_domain R a⟩
  have hu : shifted R (scaledEnergy R m : ℂ) u = 0 := by
    change operator R ⟨quotientBasisVector a, basis_mem_domain R a⟩ -
      (scaledEnergy R a.val.1 : ℂ) • quotientBasisVector a = 0
    rw [operator_basis, sub_self]
  have h := hS.left_inverse u
  rw [hu, map_zero] at h
  exact quotientBasisVector_orthonormal.ne_zero a h.symm

def resolventSet (R : ℝ) : Set ℂ := {z | ∃ S, IsResolvent R z S}

def spectrum (R : ℝ) : Set ℂ := (resolventSet R)ᶜ

theorem mem_resolventSet_iff {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    z ∈ resolventSet R ↔ ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ) := by
  constructor
  · rintro ⟨S, hS⟩ m hm
    exact hS.not_eigenvalue m hm
  · intro hz
    exact ⟨resolvent hR z hz, resolvent_spec hR z hz⟩

theorem mem_spectrum_iff {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    z ∈ spectrum R ↔ ∃ m : ℕ, Even m ∧ z = (scaledEnergy R m : ℂ) := by
  change (¬ z ∈ resolventSet R) ↔ _
  simp only [mem_resolventSet_iff hR, not_forall, not_not, exists_prop]

theorem mem_spectrum_iff_even_degree {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    z ∈ spectrum R ↔ ∃ n : ℕ, z = (scaledEnergy R (2 * n) : ℂ) := by
  rw [mem_spectrum_iff hR]
  constructor
  · rintro ⟨m, ⟨n, hn⟩, hz⟩
    exact ⟨n, by simpa only [hn, two_mul] using hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨2 * n, ⟨n, by omega⟩, hz⟩

theorem endpoint_spectrum {b : ℝ} (hb : 0 < b) :
    spectrum (radius b) = Set.range (fun n : ℕ =>
      ((((2 * (n : ℝ) + 1) ^ 2 - 1) / radius b ^ 2 : ℝ) : ℂ)) := by
  ext z
  rw [mem_spectrum_iff_even_degree (radius_pos hb).ne']
  simp only [endpoint_even_energy, Set.mem_range]
  exact exists_congr (fun _ => eq_comm)

theorem resolvent_isCompact {R : ℝ} (hR : R ≠ 0) (z : ℂ)
    (hz : ∀ m : ℕ, Even m → z ≠ (scaledEnergy R m : ℂ)) :
    IsCompactOperator (resolvent hR z hz) :=
  (SourceQuotientSpectrum.resolvent_isCompact
    (z / (inverseSquare R : ℂ)) (unscaled_regular hR z hz)).smul (inverseSquare R : ℂ)⁻¹

theorem IsResolvent.isCompact {R : ℝ} (hR : R ≠ 0) {z : ℂ}
    {S : QuotientL2 →L[ℂ] QuotientL2} (hS : IsResolvent R z S) : IsCompactOperator S := by
  rw [hS.unique (resolvent_spec hR z hS.not_eigenvalue)]
  exact resolvent_isCompact hR z hS.not_eigenvalue

theorem has_compact_resolvent {R : ℝ} (hR : R ≠ 0) :
    ∃ S : QuotientL2 →L[ℂ] QuotientL2, IsResolvent R (-1) S ∧ IsCompactOperator S := by
  have hz : ∀ m : ℕ, Even m → (-1 : ℂ) ≠ (scaledEnergy R m : ℂ) := by
    intro m _ he
    have hre := congrArg Complex.re he
    have hm : 0 ≤ scaledEnergy R m :=
      mul_nonneg (sq_nonneg R⁻¹) (SourceCasimirClosure.energy_nonneg m)
    norm_num at hre
    linarith
  exact ⟨resolvent hR (-1) hz, resolvent_spec hR (-1) hz, resolvent_isCompact hR (-1) hz⟩

def eigenspace (R : ℝ) (z : ℂ) : Submodule ℂ QuotientL2 :=
  (LinearMap.ker (shifted R z)).map (operator R).domain.subtype

theorem mem_eigenspace_iff (R : ℝ) (z : ℂ) (f : QuotientL2) :
    f ∈ eigenspace R z ↔ ∃ u : (operator R).domain,
      operator R u = z • (u : QuotientL2) ∧ (u : QuotientL2) = f := by
  constructor
  · rintro ⟨u, hu, huf⟩
    exact ⟨u, by simpa [LinearMap.mem_ker, shifted, sub_eq_zero] using hu, huf⟩
  · rintro ⟨u, hu, huf⟩
    exact ⟨u, by simpa [LinearMap.mem_ker, shifted, sub_eq_zero] using hu, huf⟩

private theorem scale_eigenvector_iff (c z : ℂ) (hc : c ≠ 0) (x y : QuotientL2) :
    c • x = z • y ↔ x = (z / c) • y := by
  constructor
  · intro h
    have he := congrArg (fun v : QuotientL2 => c⁻¹ • v) h
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul] at he
    simpa only [div_eq_mul_inv, mul_comm] using he
  · intro h
    rw [h, smul_smul]
    congr 1
    field_simp [hc]

/-- The actual eigenspace is unchanged; no dimension count substitutes for this equality. -/
theorem eigenspace_eq {R : ℝ} (hR : R ≠ 0) (z : ℂ) :
    eigenspace R z = SourceQuotientSpectrum.eigenspace (z / (inverseSquare R : ℂ)) := by
  ext f
  rw [mem_eigenspace_iff, SourceQuotientSpectrum.mem_eigenspace_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    let v : SourceQuotientCasimir.operator.domain :=
      ⟨u, (operator_domain_iff hR u).mp u.property⟩
    refine ⟨v, ?_, rfl⟩
    apply (scale_eigenvector_iff (inverseSquare R : ℂ) z (coefficient_ne_zero hR)
      (SourceQuotientCasimir.operator v) (u : QuotientL2)).mp
    simpa only [operator_apply hR] using hu
  · rintro ⟨v, hv, rfl⟩
    let u : (operator R).domain := ⟨v, (operator_domain_iff hR v).mpr v.property⟩
    refine ⟨u, ?_, rfl⟩
    rw [operator_apply hR]
    exact (scale_eigenvector_iff (inverseSquare R : ℂ) z (coefficient_ne_zero hR)
      (SourceQuotientCasimir.operator v) (v : QuotientL2)).mpr hv

theorem eigenspace_scaled_energy {R : ℝ} (hR : R ≠ 0) (m : ℕ) :
    eigenspace R (scaledEnergy R m : ℂ) = SourceQuotientSpectrum.eigenspace (energy m : ℂ) := by
  rw [eigenspace_eq hR]
  congr 1
  simp only [scaledEnergy, Complex.ofReal_mul]
  field_simp [coefficient_ne_zero hR]

theorem eigenspace_finrank {R : ℝ} (hR : R ≠ 0) (m : ℕ) (hm : Even m) :
    Module.finrank ℂ (eigenspace R (scaledEnergy R m : ℂ)) = (m + 1) ^ 2 := by
  rw [eigenspace_scaled_energy hR]
  exact SourceQuotientSpectrum.eigenspace_finrank m hm

theorem endpoint_multiplicity {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Module.finrank ℂ (eigenspace (radius b)
      ((((2 * (n : ℝ) + 1) ^ 2 - 1) / radius b ^ 2 : ℝ) : ℂ)) = (2 * n + 1) ^ 2 := by
  rw [← endpoint_even_energy]
  exact eigenspace_finrank (radius_pos hb).ne' (2 * n) ⟨n, by omega⟩

end GeneratedFoundations.Geometry.SourceEndpointSpectrum
