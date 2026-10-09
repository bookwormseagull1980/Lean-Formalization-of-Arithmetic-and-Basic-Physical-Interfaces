module

public import GeneratedFoundations.Geometry.SourceIrreducibleClassification

/-!
# Minimal centre-sensitive source representations

The comparison class consists of all finite-dimensional continuous
irreducible unitary representations of the actual source group. The centre
test is an equality of whole operators. Classification supplies a degree;
its central parity and dimension then select degree one at the minimum.

Minimality is stated as comparison with the entire class, not as a
prescribed two-dimensional carrier. The equivalence is unitary and
intertwines the same source group. No preferred intertwining map is claimed.
-/

@[expose] public section

noncomputable section

open Module
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSymmetricIrreducible
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceIrreducibleClassification

namespace GeneratedFoundations.Geometry.SourceMinimalSpin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

def CentreSensitive (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ρ negativeIdentity ≠ 1

theorem source_centre_action (m : ℕ) (v : HilbertCarrier m) :
    unitaryAction m negativeIdentity v = (-1 : ℂ) ^ m • v := by
  obtain ⟨p, rfl⟩ := (carrierEquiv m).surjective v
  rw [unitaryAction_apply_carrier, sourceRepresentation_centre, map_smul]

theorem source_centreSensitive_iff (m : ℕ) :
    CentreSensitive (unitaryRepresentation m) ↔ Odd m := by
  constructor
  · intro hs
    rcases Nat.even_or_odd m with he | ho
    · exfalso
      apply hs
      apply LinearIsometryEquiv.ext
      intro v
      change unitaryAction m negativeIdentity v = v
      rw [source_centre_action, he.neg_one_pow, one_smul]
    · exact ho
  · intro ho htriv
    let v := sourceBasis m 0
    have hv : inner ℂ v v = 1 := by
      simp [v]
    have he : unitaryAction m negativeIdentity v = v :=
      congrArg (fun U : HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m => U v) htriv
    rw [source_centre_action, ho.neg_one_pow] at he
    have hi := congrArg (fun w => inner ℂ v w) he
    have hs : inner ℂ v ((-1 : ℂ) • v) = (-1 : ℂ) * inner ℂ v v :=
      inner_smul_right (𝕜 := ℂ) v v (-1 : ℂ)
    have hi' : (-1 : ℂ) * inner ℂ v v = 1 := hs.symm.trans (hi.trans hv)
    rw [hv] at hi'
    norm_num at hi'

omit [FiniteDimensional ℂ H] in
theorem centre_trivial_iff {ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)} {m : ℕ}
    (U : UnitaryIntertwiner ρ m) :
    ρ negativeIdentity = 1 ↔ unitaryRepresentation m negativeIdentity = 1 := by
  constructor
  · intro h
    apply LinearIsometryEquiv.ext
    intro v
    change unitaryAction m negativeIdentity v = v
    apply U.val.injective
    rw [U.property, h]
    rfl
  · intro h
    apply LinearIsometryEquiv.ext
    intro v
    change ρ negativeIdentity v = v
    obtain ⟨w, rfl⟩ := U.val.surjective v
    rw [← U.property negativeIdentity w]
    have hs : unitaryAction m negativeIdentity w = w :=
      congrArg (fun T : HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m => T w) h
    rw [hs]

omit [FiniteDimensional ℂ H] in
theorem centreSensitive_iff_odd {ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)} {m : ℕ}
    (U : UnitaryIntertwiner ρ m) : CentreSensitive ρ ↔ Odd m := by
  change (ρ negativeIdentity ≠ 1) ↔ Odd m
  rw [ne_eq, centre_trivial_iff U, ← ne_eq]
  exact source_centreSensitive_iff m

/-- Every allowed centre-sensitive representation has dimension at least two. -/
theorem centreSensitive_finrank_ge_two (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H))
    (hcont : ∀ v : H, Continuous (fun g : SU2 => ρ g v))
    [Representation.IsIrreducible (linearRepresentation ρ)]
    (hs : CentreSensitive ρ) : 2 ≤ Module.finrank ℂ H := by
  obtain ⟨m, ⟨U⟩, _⟩ := exists_unique_degree ρ hcont
  have ho := (centreSensitive_iff_odd U).mp hs
  have hd := U.val.toLinearEquiv.finrank_eq
  rw [hilbertCarrier_finrank] at hd
  rcases ho with ⟨k, hk⟩
  omega

/-- The two-dimensional equality case is precisely the actual degree-one source. -/
theorem finrank_two_iff_degree_one (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H))
    (hcont : ∀ v : H, Continuous (fun g : SU2 => ρ g v))
    [Representation.IsIrreducible (linearRepresentation ρ)] :
    Module.finrank ℂ H = 2 ↔ Nonempty (UnitaryIntertwiner ρ 1) := by
  constructor
  · intro hd
    obtain ⟨m, ⟨U⟩, _⟩ := exists_unique_degree ρ hcont
    have hm := U.val.toLinearEquiv.finrank_eq
    rw [hilbertCarrier_finrank, hd] at hm
    have hm1 : m = 1 := by omega
    subst m
    exact ⟨U⟩
  · rintro ⟨U⟩
    have hd := U.val.toLinearEquiv.finrank_eq
    rw [hilbertCarrier_finrank] at hd
    exact hd.symm

theorem degree_one_centreSensitive : CentreSensitive (unitaryRepresentation 1) :=
  (source_centreSensitive_iff 1).mpr (by decide)

/-- Least dimension in the declared representation class. -/
def IsLeastCentreSensitive (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  (∀ v : H, Continuous (fun g : SU2 => ρ g v)) ∧
    Representation.IsIrreducible (linearRepresentation ρ) ∧ CentreSensitive ρ ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
      (σ : SU2 →* (E ≃ₗᵢ[ℂ] E)),
      (∀ v : E, Continuous (fun g : SU2 => σ g v)) →
      Representation.IsIrreducible (linearRepresentation σ) → CentreSensitive σ →
      Module.finrank ℂ H ≤ Module.finrank ℂ E

/-- The minimum is attained by the source degree-one representation. -/
theorem degree_one_isLeast : IsLeastCentreSensitive (unitaryRepresentation 1) := by
  have hirr : Representation.IsIrreducible (linearRepresentation (unitaryRepresentation 1)) :=
    hilbertRepresentation_irreducible 1
  refine ⟨unitaryAction_orbit_continuous 1, hirr, degree_one_centreSensitive, ?_⟩
  intro E _ _ _ σ hcont hσ hs
  let := hσ
  simpa only [hilbertCarrier_finrank] using centreSensitive_finrank_ge_two σ hcont hs

theorem least_finrank_two (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H))
    (hρ : IsLeastCentreSensitive ρ) : Module.finrank ℂ H = 2 := by
  let := hρ.2.1
  have hle := hρ.2.2.2 (HilbertCarrier 1) (unitaryRepresentation 1)
    (unitaryAction_orbit_continuous 1) (hilbertRepresentation_irreducible 1)
    degree_one_centreSensitive
  rw [hilbertCarrier_finrank] at hle
  exact Nat.le_antisymm hle (centreSensitive_finrank_ge_two ρ hρ.1 hρ.2.2.1)

theorem least_unitarilyEquivalentToDegreeOne (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H))
    (hρ : IsLeastCentreSensitive ρ) : Nonempty (UnitaryIntertwiner ρ 1) := by
  let := hρ.2.1
  exact (finrank_two_iff_degree_one ρ hρ.1).mp (least_finrank_two ρ hρ)

variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [FiniteDimensional ℂ H']

/-- The attained minimum compares with every allowed Hilbert carrier,
including carriers in a different universe from the defining source. -/
theorem least_le (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)) (hρ : IsLeastCentreSensitive ρ)
    (σ : SU2 →* (H' ≃ₗᵢ[ℂ] H'))
    (hcont : ∀ v : H', Continuous (fun g : SU2 => σ g v))
    [Representation.IsIrreducible (linearRepresentation σ)]
    (hs : CentreSensitive σ) : Module.finrank ℂ H ≤ Module.finrank ℂ H' := by
  rw [least_finrank_two ρ hρ]
  exact centreSensitive_finrank_ge_two σ hcont hs

/-- Uniqueness of a least centre-sensitive representation means existence
of a unitary intertwiner; its phase is not fixed by minimality. -/
theorem least_unique (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)) (hρ : IsLeastCentreSensitive ρ)
    (σ : SU2 →* (H' ≃ₗᵢ[ℂ] H')) (hσ : IsLeastCentreSensitive σ) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g v, U (ρ g v) = σ g (U v) := by
  obtain ⟨U⟩ := least_unitarilyEquivalentToDegreeOne ρ hρ
  obtain ⟨V⟩ := least_unitarilyEquivalentToDegreeOne σ hσ
  refine ⟨U.val.symm.trans V.val, ?_⟩
  intro g v
  obtain ⟨w, rfl⟩ := U.val.surjective v
  change V.val (U.val.symm (ρ g (U.val w))) = σ g (V.val (U.val.symm (U.val w)))
  rw [← U.property g w, U.val.symm_apply_apply, U.val.symm_apply_apply]
  exact V.property g w

end GeneratedFoundations.Geometry.SourceMinimalSpin
