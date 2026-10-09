module

public import GeneratedFoundations.Spectral.NeumannSpectralProjections

/-!
# Scale transport of the original Neumann dynamics

The complete cosine bases define a unitary between the two interval spaces.
The original Sobolev domains are transported using their proved coefficient
criteria. Division by the first positive energy gives the same unbounded
operator, while the Gaussian change parameter is multiplied by the ratio of
the energy units. No new differential domain or evolution is introduced.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap NNReal
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Spectral.NeumannScaleTransport

open NeumannHeatSemigroup NeumannSpectralProjections

variable (L M : ℝ) [hL : Fact (0 < L)] [hM : Fact (0 < M)]

def unitary : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] ComplexIntervalL2 0 M :=
  (coefficients L).trans (coefficients M).symm

theorem coefficients_unitary (f : ComplexIntervalL2 0 L) :
    coefficients M (unitary L M f) = coefficients L f := by
  simp [unitary]

theorem inner_unitary (n : ℕ) (f : ComplexIntervalL2 0 L) :
    inner ℂ (neumannCosineMode M n) (unitary L M f) =
      inner ℂ (neumannCosineMode L n) f := by
  simpa only [coefficients_apply] using
    congrArg (fun v : Sequence => v n) (coefficients_unitary L M f)

@[simp]
theorem unitary_cosine (n : ℕ) :
    unitary L M (neumannCosineMode L n) = neumannCosineMode M n := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis M)
  intro k
  simp only [coe_neumannCosineBasis, inner_unitary]
  exact (orthonormal_iff_ite.mp (neumannCosineMode_orthonormal L) k n).trans
    (orthonormal_iff_ite.mp (neumannCosineMode_orthonormal M) k n).symm

@[simp]
theorem unitary_self (f : ComplexIntervalL2 0 L) : unitary L L f = f := by
  simp [unitary]

theorem unitary_trans (N : ℝ) [Fact (0 < N)] (f : ComplexIntervalL2 0 L) :
    unitary M N (unitary L M f) = unitary L N f := by
  apply (coefficients N).injective
  simp only [coefficients_unitary]

theorem unitary_unique
    (V : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] ComplexIntervalL2 0 M)
    (hV : ∀ n, V (neumannCosineMode L n) = neumannCosineMode M n) :
    V = unitary L M := by
  apply LinearIsometryEquiv.ext
  intro f
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis M)
  intro n
  simp only [coe_neumannCosineBasis]
  calc
    inner ℂ (neumannCosineMode M n) (V f) =
        inner ℂ (neumannCosineMode L n) f := by
      rw [← hV n, V.inner_map_map]
    _ = inner ℂ (neumannCosineMode M n) (unitary L M f) :=
      (inner_unitary L M n f).symm

theorem unitary_existsUnique :
    ∃! V : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] ComplexIntervalL2 0 M,
      ∀ n, V (neumannCosineMode L n) = neumannCosineMode M n :=
  ⟨unitary L M, unitary_cosine L M, fun V hV => unitary_unique L M V hV⟩

def energyUnit : ℝ := neumannEigenvalue L 1

theorem energyUnit_pos : 0 < energyUnit L := neumannEigenvalue_pos L (by norm_num)

omit hL in
theorem eigenvalue_factor (n : ℕ) :
    neumannEigenvalue L n = energyUnit L * (n : ℝ) ^ 2 := by
  simp only [neumannEigenvalue, energyUnit, Nat.cast_one, one_mul]
  ring

theorem normalized_eigenvalue (n : ℕ) :
    neumannEigenvalue L n / energyUnit L = (n : ℝ) ^ 2 := by
  rw [eigenvalue_factor]
  exact mul_div_cancel_left₀ _ (energyUnit_pos L).ne'

/-- This criterion is derived from the original Neumann Sobolev domain. -/
theorem normalized_domain_iff (f : ComplexIntervalL2 0 L) :
    f ∈ (complexNeumannOperator hL.out).domain ↔
      Summable (fun n : ℕ => (n : ℝ) ^ 4 *
        ‖inner ℂ (neumannCosineMode L n) f‖ ^ 2) := by
  rw [complexNeumann_domain_iff]
  have hfun : (fun n : ℕ => (neumannEigenvalue L n) ^ 2 *
      ‖inner ℂ (neumannCosineMode L n) f‖ ^ 2) =
      (fun n : ℕ => energyUnit L ^ 2 *
        ((n : ℝ) ^ 4 * ‖inner ℂ (neumannCosineMode L n) f‖ ^ 2)) := by
    funext n
    rw [eigenvalue_factor]
    ring
  rw [hfun, summable_mul_left_iff (pow_ne_zero 2 (energyUnit_pos L).ne')]

theorem unitary_mem_domain_iff (f : ComplexIntervalL2 0 L) :
    unitary L M f ∈ (complexNeumannOperator hM.out).domain ↔
      f ∈ (complexNeumannOperator hL.out).domain := by
  simp only [normalized_domain_iff, inner_unitary]

def domainEquiv :
    (complexNeumannOperator hL.out).domain ≃ₗ[ℂ]
      (complexNeumannOperator hM.out).domain where
  toFun f := ⟨unitary L M f, (unitary_mem_domain_iff L M f).mpr f.property⟩
  invFun f := ⟨unitary M L f, (unitary_mem_domain_iff M L f).mpr f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact (unitary_trans L M L f).trans (unitary_self L f)
  right_inv f := by
    apply Subtype.ext
    exact (unitary_trans M L M f).trans (unitary_self M f)
  map_add' f g := by
    apply Subtype.ext
    exact map_add (unitary L M) (f : ComplexIntervalL2 0 L) (g : ComplexIntervalL2 0 L)
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (unitary L M) c (f : ComplexIntervalL2 0 L)

@[simp]
theorem domainEquiv_coe (f : (complexNeumannOperator hL.out).domain) :
    (domainEquiv L M f : ComplexIntervalL2 0 M) = unitary L M f := rfl

theorem normalized_operator_coefficient
    (f : (complexNeumannOperator hL.out).domain) (n : ℕ) :
    inner ℂ (neumannCosineMode L n)
      ((energyUnit L : ℂ)⁻¹ • complexNeumannOperator hL.out f) =
      ((n : ℝ) ^ 2 : ℂ) * inner ℂ (neumannCosineMode L n)
        (f : ComplexIntervalL2 0 L) := by
  have hu : (energyUnit L : ℂ) ≠ 0 := by exact_mod_cast (energyUnit_pos L).ne'
  rw [inner_smul_right, complexNeumannOperator_coefficients, eigenvalue_factor,
    Complex.ofReal_mul]
  simp only [← mul_assoc, inv_mul_cancel₀ hu, one_mul, Complex.ofReal_pow]

/-- Equality is asserted on the full original domains, identified by `domainEquiv`. -/
theorem normalized_operator_intertwining
    (f : (complexNeumannOperator hL.out).domain) :
    unitary L M ((energyUnit L : ℂ)⁻¹ • complexNeumannOperator hL.out f) =
      (energyUnit M : ℂ)⁻¹ • complexNeumannOperator hM.out (domainEquiv L M f) := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis M)
  intro n
  simp only [coe_neumannCosineBasis, inner_unitary,
    normalized_operator_coefficient, domainEquiv_coe]

/-- A nonnegative change parameter, with its dimensional scale retained. -/
def changeParameter (t : ℝ≥0) : ℝ≥0 :=
  ⟨(t : ℝ) * (energyUnit L / energyUnit M),
    mul_nonneg t.property (div_pos (energyUnit_pos L) (energyUnit_pos M)).le⟩

@[simp]
theorem changeParameter_coe (t : ℝ≥0) :
    (changeParameter L M t : ℝ) = (t : ℝ) * (energyUnit L / energyUnit M) := rfl

theorem energyUnit_ratio : energyUnit L / energyUnit M = (M / L) ^ 2 := by
  simp only [energyUnit, neumannEigenvalue, Nat.cast_one, one_mul]
  field_simp [hL.out.ne', hM.out.ne', Real.pi_ne_zero]

theorem changeParameter_length_ratio (t : ℝ≥0) :
    (changeParameter L M t : ℝ) = (t : ℝ) * (M / L) ^ 2 := by
  rw [changeParameter_coe, energyUnit_ratio]

theorem decay_changeParameter (t : ℝ≥0) (n : ℕ) :
    decay M (changeParameter L M t) n = decay L t n := by
  unfold decay
  congr 1
  rw [changeParameter_coe, eigenvalue_factor M, eigenvalue_factor L]
  field_simp [(energyUnit_pos M).ne']

theorem heat_intertwining (t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    unitary L M (heat L t f) = heat M (changeParameter L M t) (unitary L M f) := by
  apply EigenbasisClosure.eq_of_coefficients (neumannCosineBasis M)
  intro n
  simp only [coe_neumannCosineBasis, inner_unitary, heat_coefficient,
    decay_changeParameter]

theorem projection_intertwining (n : ℕ) (f : ComplexIntervalL2 0 L) :
    unitary L M (cosineProjection L n f) = cosineProjection M n (unitary L M f) := by
  simp only [cosineProjection_apply, map_smul, unitary_cosine, inner_unitary]

@[simp]
theorem changeParameter_self (t : ℝ≥0) : changeParameter L L t = t := by
  apply Subtype.ext
  change (t : ℝ) * (energyUnit L / energyUnit L) = t
  rw [div_self (energyUnit_pos L).ne', mul_one]

theorem changeParameter_trans (N : ℝ) [Fact (0 < N)] (t : ℝ≥0) :
    changeParameter M N (changeParameter L M t) = changeParameter L N t := by
  apply Subtype.ext
  change (t : ℝ) * (energyUnit L / energyUnit M) * (energyUnit M / energyUnit N) =
    (t : ℝ) * (energyUnit L / energyUnit N)
  rw [mul_assoc, div_mul_div_cancel₀ (energyUnit_pos M).ne']

/-- The order is the intrinsic heat-response order on actual spectral projections. -/
def componentTransport : Component L ≃o Component M :=
  (orderCoordinate L).trans (enumerationOrderIso M)

theorem componentTransport_apply (P : Component L) :
    componentTransport L M P = mode M (coordinate L P) := rfl

@[simp]
theorem componentTransport_mode (n : ℕ) :
    componentTransport L M (mode L n) = mode M n := by
  rw [componentTransport_apply, coordinate_mode]

@[simp]
theorem coordinate_componentTransport (P : Component L) :
    coordinate M (componentTransport L M P) = coordinate L P := by
  rw [componentTransport_apply, coordinate_mode]

theorem componentTransport_unique (c : Component L ≃o Component M) :
    c = componentTransport L M := by
  have hc := orderCoordinate_unique L (c.trans (orderCoordinate M))
  apply OrderIso.ext
  funext P
  apply (enumeration M).symm.injective
  change coordinate M (c P) = coordinate M (componentTransport L M P)
  rw [coordinate_componentTransport]
  exact congrArg (fun e : Component L ≃o ℕ => e P) hc

theorem componentTransport_existsUnique : ∃! _c : Component L ≃o Component M, True :=
  ⟨componentTransport L M, trivial, fun c _ => componentTransport_unique L M c⟩

theorem componentTransport_successor (P : Component L) :
    componentTransport L M (successor L P) = successor M (componentTransport L M P) := by
  simp only [successor, componentTransport_mode, coordinate_componentTransport]

/-- The intrinsic order comparison is realized by conjugation of the original projections. -/
theorem componentTransport_intertwining (P : Component L) (f : ComplexIntervalL2 0 L) :
    unitary L M (P.val f) = (componentTransport L M P).val (unitary L M f) := by
  obtain ⟨n, rfl⟩ := (mode_bijective L).surjective P
  rw [componentTransport_mode]
  exact projection_intertwining L M n f

theorem componentTransport_normalized_energy (P : Component L) :
    energy M (componentTransport L M P) / energyUnit M = energy L P / energyUnit L := by
  simp only [energy, coordinate_componentTransport, normalized_eigenvalue]

theorem componentTransport_response (P : Component L) (t : ℝ≥0) :
    response M (componentTransport L M P) (changeParameter L M t) = response L P t := by
  obtain ⟨n, rfl⟩ := (mode_bijective L).surjective P
  simp only [componentTransport_mode, response_mode, decay_changeParameter]

end GeneratedFoundations.Spectral.NeumannScaleTransport
