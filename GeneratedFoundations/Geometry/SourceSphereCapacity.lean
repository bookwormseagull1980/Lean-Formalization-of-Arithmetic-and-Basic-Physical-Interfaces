module

public import GeneratedFoundations.Geometry.SourceEndpointSpectrum
public import GeneratedFoundations.Operations.SourceResponseCapacity
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega

/-!
# Capacity and affine uniqueness in the specified spherical spectral class

The multiplicity is the full factorial formula for the normalized scalar
sphere spectrum. The dimension ranges over every natural number at least
two. No conclusion about the dimension or the affine coefficients is built
into the assumptions.

Degree two already decides the capacity condition. For an affine response,
degrees zero, two and four suffice: degree zero fixes the intercept, and
eliminating the slope from degrees two and four gives a polynomial with
exactly one admissible dimension. This also proves uniqueness when only
even degrees are retained. At dimension three, the factorial formula gives
the claimed identity at every degree.

These are characterizations within the spherical spectral data specified
in the manuscript's isotropic capacity class. They do not formalize the
constant-curvature space-form theorem, derive that class from arbitrary
spaces, or identify the Neumann window Hilbert space with the sphere space.
The final statements match these numbers to the actual finite Gaussian
corner and the actual even endpoint eigenspaces already constructed.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.SourceSphereCapacity

/-- The complete scalar spherical multiplicity formula. It is used below
only under the dimension condition `2 ≤ d`. -/
def sphereMultiplicity (d l : ℕ) : ℝ :=
  (2 * (l : ℝ) + (d : ℝ) - 1) * ((l + d - 2).factorial : ℝ) /
    ((l.factorial : ℝ) * ((d - 1).factorial : ℝ))

def sphereEigenvalue (d l : ℕ) : ℝ := (l : ℝ) * ((l : ℝ) + (d : ℝ) - 1)

/-- Writing `d = k + 2` removes natural-number truncation from the factorial indices. -/
theorem multiplicity_add_two (k l : ℕ) :
    sphereMultiplicity (k + 2) l =
      (2 * (l : ℝ) + (k : ℝ) + 1) * ((l + k).factorial : ℝ) /
        ((l.factorial : ℝ) * ((k + 1).factorial : ℝ)) := by
  have hnum : l + (k + 2) - 2 = l + k := by omega
  have hden : k + 2 - 1 = k + 1 := by omega
  rw [sphereMultiplicity, hnum, hden]
  push_cast
  ring

private theorem factorial_cast_ne_zero (k : ℕ) : (k.factorial : ℝ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero k

theorem multiplicity_zero (d : ℕ) (hd : 2 ≤ d) : sphereMultiplicity d 0 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 2 :=
    ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [multiplicity_add_two, Nat.zero_add, Nat.factorial_zero, Nat.factorial_succ]
  push_cast
  field_simp [factorial_cast_ne_zero k, hk]
  ring

theorem multiplicity_two (d : ℕ) (hd : 2 ≤ d) :
    sphereMultiplicity d 2 = (d : ℝ) * ((d : ℝ) + 3) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 2 :=
    ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
  rw [multiplicity_add_two, Nat.add_comm 2 k, Nat.factorial_succ (k + 1),
    Nat.factorial_two]
  push_cast
  field_simp [factorial_cast_ne_zero (k + 1)]
  ring

theorem multiplicity_four (d : ℕ) (hd : 2 ≤ d) :
    sphereMultiplicity d 4 =
      (d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 2) * ((d : ℝ) + 7) / 24 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 2 :=
    ⟨d - 2, (Nat.sub_add_cancel hd).symm⟩
  rw [multiplicity_add_two, Nat.add_comm 4 k, Nat.factorial_succ (k + 3),
    Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1),
    show Nat.factorial 4 = 24 by rfl]
  push_cast
  field_simp [factorial_cast_ne_zero (k + 1)]
  ring

@[simp] theorem eigenvalue_zero (d : ℕ) : sphereEigenvalue d 0 = 0 := by
  simp [sphereEigenvalue]

theorem eigenvalue_two (d : ℕ) : sphereEigenvalue d 2 = 2 * ((d : ℝ) + 1) := by
  norm_num [sphereEigenvalue]
  ring

theorem eigenvalue_four (d : ℕ) : sphereEigenvalue d 4 = 4 * ((d : ℝ) + 3) := by
  norm_num [sphereEigenvalue]
  ring

/-- The converse uses the factorial formula at every degree, not just the
three degrees used for the uniqueness argument. -/
theorem multiplicity_three (l : ℕ) : sphereMultiplicity 3 l = ((l : ℝ) + 1) ^ 2 := by
  change sphereMultiplicity (1 + 2) l = _
  rw [multiplicity_add_two, Nat.factorial_succ l]
  norm_num only [Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul]
  field_simp [factorial_cast_ne_zero l]
  ring

theorem multiplicity_three_affine (l : ℕ) :
    sphereMultiplicity 3 l = sphereEigenvalue 3 l + 1 := by
  rw [multiplicity_three]
  norm_num [sphereEigenvalue]
  ring

/-- Capacity at the first positive even degree already selects dimension three. -/
theorem capacity_two_unique (d : ℕ) (hd : 2 ≤ d)
    (hcapacity : sphereMultiplicity d 2 = 9) : d = 3 := by
  rw [multiplicity_two d hd] at hcapacity
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hfactor : ((d : ℝ) - 3) * ((d : ℝ) + 6) = 0 := by
    linear_combination 2 * hcapacity
  have hsecond : (d : ℝ) + 6 ≠ 0 := by linarith
  have hdim : (d : ℝ) = 3 := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hsecond)
  exact_mod_cast hdim

def affineObstruction (x : ℝ) : ℝ :=
  x ^ 4 + 14 * x ^ 3 + 51 * x ^ 2 + 46 * x - 40

theorem affineObstruction_pos {x : ℝ} (hx : 2 ≤ x) : 0 < affineObstruction x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hpoly : 0 ≤ x ^ 4 + 14 * x ^ 3 + 51 * x ^ 2 := by positivity
  unfold affineObstruction
  linarith

/-- Directly checked factorization of the slope-elimination polynomial. -/
theorem affine_elimination_factorization (x : ℝ) :
    x * (x + 1) ^ 2 * (x + 2) * (x + 7) -
        24 * x * (x + 3) ^ 2 - 24 * (x + 1) + 48 * (x + 3) =
      (x - 3) * affineObstruction x := by
  unfold affineObstruction
  ring

/-- All competing dimensions and affine coefficients are quantified. The
three equations even force the slope to be positive, without assuming it. -/
theorem affine_zero_two_four_unique (d : ℕ) (hd : 2 ≤ d) (a c : ℝ)
    (hzero : sphereMultiplicity d 0 = a * sphereEigenvalue d 0 + c)
    (htwo : sphereMultiplicity d 2 = a * sphereEigenvalue d 2 + c)
    (hfour : sphereMultiplicity d 4 = a * sphereEigenvalue d 4 + c) :
    d = 3 ∧ a = 1 ∧ c = 1 := by
  have hc : c = 1 := by
    simpa only [multiplicity_zero d hd, eigenvalue_zero, mul_zero, zero_add] using hzero.symm
  rw [multiplicity_two d hd, eigenvalue_two, hc] at htwo
  rw [multiplicity_four d hd, eigenvalue_four, hc] at hfour
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hfactor : ((d : ℝ) - 3) * affineObstruction (d : ℝ) = 0 := by
    rw [← affine_elimination_factorization]
    linear_combination 24 * ((d : ℝ) + 1) * hfour - 48 * ((d : ℝ) + 3) * htwo
  have hdim : (d : ℝ) = 3 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right
      (ne_of_gt (affineObstruction_pos hdreal)))
  have hdthree : d = 3 := by exact_mod_cast hdim
  have ha : a = 1 := by
    rw [hdthree] at htwo
    norm_num at htwo
    linarith
  exact ⟨hdthree, ha, hc⟩

theorem capacity_all_iff (d : ℕ) (hd : 2 ≤ d) :
    (∀ l : ℕ, sphereMultiplicity d l = ((l : ℝ) + 1) ^ 2) ↔ d = 3 := by
  constructor
  · intro h
    apply capacity_two_unique d hd
    have htwo := h 2
    norm_num at htwo
    exact htwo
  · rintro rfl
    exact multiplicity_three

theorem capacity_even_iff (d : ℕ) (hd : 2 ≤ d) :
    (∀ l : ℕ, Even l → sphereMultiplicity d l = ((l : ℝ) + 1) ^ 2) ↔ d = 3 := by
  constructor
  · intro h
    apply capacity_two_unique d hd
    have htwo := h 2 ⟨1, rfl⟩
    norm_num at htwo
    exact htwo
  · rintro rfl
    intro l _hl
    exact multiplicity_three l

theorem affine_all_iff (d : ℕ) (hd : 2 ≤ d) (a c : ℝ) :
    (0 < a ∧ ∀ l : ℕ, sphereMultiplicity d l = a * sphereEigenvalue d l + c) ↔
      d = 3 ∧ a = 1 ∧ c = 1 := by
  constructor
  · rintro ⟨_ha, h⟩
    exact affine_zero_two_four_unique d hd a c (h 0) (h 2) (h 4)
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨by norm_num, ?_⟩
    intro l
    simpa only [one_mul] using multiplicity_three_affine l

theorem affine_even_iff (d : ℕ) (hd : 2 ≤ d) (a c : ℝ) :
    (0 < a ∧ ∀ l : ℕ, Even l → sphereMultiplicity d l = a * sphereEigenvalue d l + c) ↔
      d = 3 ∧ a = 1 ∧ c = 1 := by
  constructor
  · rintro ⟨_ha, h⟩
    exact affine_zero_two_four_unique d hd a c
      (h 0 ⟨0, rfl⟩) (h 2 ⟨1, rfl⟩) (h 4 ⟨2, rfl⟩)
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨by norm_num, ?_⟩
    intro l _hl
    simpa only [one_mul] using multiplicity_three_affine l

theorem affine_all_exists_iff (d : ℕ) (hd : 2 ≤ d) :
    (∃ a c : ℝ, 0 < a ∧ ∀ l : ℕ,
      sphereMultiplicity d l = a * sphereEigenvalue d l + c) ↔ d = 3 := by
  constructor
  · rintro ⟨a, c, h⟩
    exact ((affine_all_iff d hd a c).mp h).1
  · intro hdthree
    exact ⟨1, 1, (affine_all_iff d hd 1 1).mpr ⟨hdthree, rfl, rfl⟩⟩

theorem affine_even_exists_iff (d : ℕ) (hd : 2 ≤ d) :
    (∃ a c : ℝ, 0 < a ∧ ∀ l : ℕ, Even l →
      sphereMultiplicity d l = a * sphereEigenvalue d l + c) ↔ d = 3 := by
  constructor
  · rintro ⟨a, c, h⟩
    exact ((affine_even_iff d hd a c).mp h).1
  · intro hdthree
    exact ⟨1, 1, (affine_even_iff d hd 1 1).mpr ⟨hdthree, rfl, rfl⟩⟩

open GeneratedFoundations.Operations

/-- The capacity is the dimension of the actual generated source corner's
operator algebra, as obtained in the joint response-capacity theorem. -/
theorem source_corner_capacity {b : ℝ} (hb : 0 < b) (l : ℕ) :
    (Module.finrank ℂ (SourceFiniteCornerAlgebra.Carrier hb l →ₗ[ℂ]
      SourceFiniteCornerAlgebra.Carrier hb l) : ℝ) = sphereMultiplicity 3 l := by
  simpa only [multiplicity_three, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    congrArg (fun n : ℕ => (n : ℝ))
      (SourceResponseCapacity.finiteCorner_responseCapacity hb l 0).2.1

/-- Comparing every retained even spherical degree with the actual source
operator dimension still has exactly one dimension in the specified class. -/
theorem source_capacity_even_iff {b : ℝ} (hb : 0 < b) (d : ℕ) (hd : 2 ≤ d) :
    (∀ l : ℕ, Even l → sphereMultiplicity d l =
      (Module.finrank ℂ (SourceFiniteCornerAlgebra.Carrier hb l →ₗ[ℂ]
        SourceFiniteCornerAlgebra.Carrier hb l) : ℝ)) ↔ d = 3 := by
  constructor
  · intro h
    apply (capacity_even_iff d hd).mp
    intro l hl
    rw [← multiplicity_three, ← source_corner_capacity hb l]
    exact h l hl
  · rintro rfl
    intro l _hl
    exact (source_corner_capacity hb l).symm

theorem source_energy_eq (l : ℕ) :
    SourceCasimirClosure.energy l = sphereEigenvalue 3 l := by
  norm_num only [SourceCasimirClosure.energy, sphereEigenvalue, Nat.cast_ofNat]
  ring

/-- The endpoint fixes the scale of the already constructed source Casimir;
this is an equality of eigenvalues, not an identification of Hilbert spaces. -/
theorem scaled_source_energy_eq (R : ℝ) (l : ℕ) :
    SourceEndpointCasimir.scaledEnergy R l = sphereEigenvalue 3 l / R ^ 2 := by
  rw [SourceEndpointCasimir.scaledEnergy, SourceEndpointCasimir.inverseSquare_eq,
    source_energy_eq]
  simpa only [div_eq_mul_inv] using
    (mul_comm ((R ^ 2)⁻¹) (sphereEigenvalue 3 l))

/-- Multiplicity is the dimension of the actual endpoint operator's even
eigenspace, with the same degree as the finite source capacity. -/
theorem endpoint_eigenspace_capacity {b : ℝ} (hb : 0 < b) (l : ℕ) (hl : Even l) :
    (Module.finrank ℂ (SourceEndpointSpectrum.eigenspace (SourceEndpointCasimir.radius b)
      ((sphereEigenvalue 3 l / SourceEndpointCasimir.radius b ^ 2 : ℝ) : ℂ)) : ℝ) =
      sphereMultiplicity 3 l := by
  rw [← scaled_source_energy_eq]
  simpa only [multiplicity_three, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    congrArg (fun n : ℕ => (n : ℝ))
      (SourceEndpointSpectrum.eigenspace_finrank
        (SourceEndpointCasimir.radius_pos hb).ne' l hl)

/-- The two independently constructed finite dimensions agree. The source
operator corner and geometric eigenspace remain distinct spaces. -/
theorem source_corner_endpoint_finrank {b : ℝ} (hb : 0 < b) (l : ℕ) (hl : Even l) :
    Module.finrank ℂ (SourceFiniteCornerAlgebra.Carrier hb l →ₗ[ℂ]
      SourceFiniteCornerAlgebra.Carrier hb l) =
    Module.finrank ℂ (SourceEndpointSpectrum.eigenspace (SourceEndpointCasimir.radius b)
      ((sphereEigenvalue 3 l / SourceEndpointCasimir.radius b ^ 2 : ℝ) : ℂ)) := by
  rw [← scaled_source_energy_eq, SourceFiniteCornerAlgebra.finrank_endomorphisms,
    SourceEndpointSpectrum.eigenspace_finrank (SourceEndpointCasimir.radius_pos hb).ne' l hl]

end GeneratedFoundations.Geometry.SourceSphereCapacity
