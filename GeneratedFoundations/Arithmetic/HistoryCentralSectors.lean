module

public import GeneratedFoundations.Arithmetic.HistoryRootSectors
public import GeneratedFoundations.Arithmetic.GeneratedPrimeParity
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Central sectors of the actual complete history--phase carrier

Every coefficient retains its positive root, its complete ordered history
and its finite phase. The central sign is the parity of the root's generated
prime occupation. It is constant on a root fibre, whereas history reflection
reverses the ordered vertices inside that fibre. The two operations commute;
they are not identified.

The central projections below are restrictions of the existing coefficient
space. No second copy, equal-sector dimension or independent exchange is
inserted. Their direct-sum coordinates are unitary, so all coefficient inner
products and the full action of an operator are retained by conjugation.
Gaussian multiplication preserves the two sectors. Operators that change
occupation parity have off-diagonal blocks, proved by the grading equation.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryCentralSectors

abbrev Label (N : ℕ) := Σ b : HistoryRootSectors.Roots N,
  HistoryModuleRepresentation.Index b.val

abbrev Space (N : ℕ) := EuclideanSpace ℂ (Label N)

noncomputable instance (N : ℕ) : DecidableEq (Label N) := Classical.decEq _

/-- Flattening the actual root fibres changes coordinates, not the carrier. -/
def nativeCoordinates (N : ℕ) : HistoryRootSectors.NativeSpace N ≃ₗᵢ[ℂ] Space N :=
  (LinearIsometryEquiv.piLpCurry ℂ 2
    (fun (b : HistoryRootSectors.Roots N) (_ : HistoryModuleRepresentation.Index b.val) => ℂ)).symm

@[simp] theorem nativeCoordinates_apply (N : ℕ)
    (x : HistoryRootSectors.NativeSpace N) (i : Label N) :
    nativeCoordinates N x i = x i.1 i.2 := rfl

def sign (n : ℕ) : ℂ := (-1) ^ GeneratedPrimeParity.rootPrimeCount (n + 1)

theorem sign_cases (n : ℕ) : sign n = 1 ∨ sign n = -1 :=
  neg_one_pow_eq_or ℂ _

theorem sign_eq_rootCentre (n : ℕ) :
    sign n = (GeneratedPrimeParity.rootCentre (n + 1) : ℂ) := by
  simp [sign, GeneratedPrimeParity.rootCentre]

@[simp] theorem sign_star (n : ℕ) : star (sign n) = sign n := by
  simp [sign]

@[simp] theorem sign_square (n : ℕ) : sign n * sign n = 1 := by
  rcases sign_cases n with h | h <;> simp [h]

def Positive {N : ℕ} (i : Label N) : Prop := sign i.1.val = 1

noncomputable instance (N : ℕ) : DecidablePred (@Positive N) := Classical.decPred _

abbrev PositiveLabel (N : ℕ) := {i : Label N // Positive i}
abbrev NegativeLabel (N : ℕ) := {i : Label N // ¬Positive i}
abbrev PositiveSpace (N : ℕ) := EuclideanSpace ℂ (PositiveLabel N)
abbrev NegativeSpace (N : ℕ) := EuclideanSpace ℂ (NegativeLabel N)
abbrev SectorSpace (N : ℕ) := WithLp 2 (PositiveSpace N × NegativeSpace N)

/-- Restrict to the two intrinsic occupation characters, retaining every
    history and phase in the corresponding root fibres. -/
def sectorCoordinates (N : ℕ) : Space N ≃ₗᵢ[ℂ] SectorSpace N :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.sumCompl (@Positive N)).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : PositiveLabel N ⊕ NegativeLabel N => ℂ))

@[simp] theorem sectorCoordinates_positive (N : ℕ) (x : Space N) (i : PositiveLabel N) :
    (WithLp.ofLp (sectorCoordinates N x)).1 i = x i.val := rfl

@[simp] theorem sectorCoordinates_negative (N : ℕ) (x : Space N) (i : NegativeLabel N) :
    (WithLp.ofLp (sectorCoordinates N x)).2 i = x i.val := rfl

def grading (N : ℕ) : Module.End ℂ (Space N) where
  toFun x := WithLp.toLp 2 fun i => sign i.1.val * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_left_comm]

@[simp] theorem grading_apply (N : ℕ) (x : Space N) (i : Label N) :
    grading N x i = sign i.1.val * x i := rfl

def positiveProjection (N : ℕ) : Module.End ℂ (Space N) where
  toFun x := WithLp.toLp 2 fun i => if Positive i then x i else 0
  map_add' x y := by ext i; by_cases hi : Positive i <;> simp [hi]
  map_smul' c x := by ext i; by_cases hi : Positive i <;> simp [hi]

def negativeProjection (N : ℕ) : Module.End ℂ (Space N) where
  toFun x := WithLp.toLp 2 fun i => if Positive i then 0 else x i
  map_add' x y := by ext i; by_cases hi : Positive i <;> simp [hi]
  map_smul' c x := by ext i; by_cases hi : Positive i <;> simp [hi]

@[simp] theorem positiveProjection_apply (N : ℕ) (x : Space N) (i : Label N) :
    positiveProjection N x i = if Positive i then x i else 0 := rfl

@[simp] theorem negativeProjection_apply (N : ℕ) (x : Space N) (i : Label N) :
    negativeProjection N x i = if Positive i then 0 else x i := rfl

theorem positiveProjection_square (N : ℕ) :
    positiveProjection N * positiveProjection N = positiveProjection N := by
  ext x i
  by_cases hi : Positive i <;> simp [hi]

theorem negativeProjection_square (N : ℕ) :
    negativeProjection N * negativeProjection N = negativeProjection N := by
  ext x i
  by_cases hi : Positive i <;> simp [hi]

theorem projections_mul (N : ℕ) : positiveProjection N * negativeProjection N = 0 := by
  ext x i
  by_cases hi : Positive i <;> simp [hi]

theorem projections_mul_reverse (N : ℕ) : negativeProjection N * positiveProjection N = 0 := by
  ext x i
  by_cases hi : Positive i <;> simp [hi]

theorem projections_sum (N : ℕ) : positiveProjection N + negativeProjection N = 1 := by
  ext x i
  by_cases hi : Positive i <;> simp [hi]

theorem grading_eq_projections (N : ℕ) :
    grading N = positiveProjection N - negativeProjection N := by
  ext x i
  by_cases hi : Positive i
  · simp [hi, (show sign i.1.val = 1 from hi)]
  · have hn : sign i.1.val = -1 := (sign_cases i.1.val).resolve_left hi
    simp [hi, hn]

theorem grading_square (N : ℕ) : grading N * grading N = 1 := by
  ext x i
  simp [← mul_assoc]

theorem positiveProjection_inner (N : ℕ) (x y : Space N) :
    inner ℂ (positiveProjection N x) y = inner ℂ x (positiveProjection N y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Positive i <;> simp [hi]

theorem negativeProjection_inner (N : ℕ) (x y : Space N) :
    inner ℂ (negativeProjection N x) y = inner ℂ x (negativeProjection N y) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Positive i <;> simp [hi]

theorem grading_adjoint (N : ℕ) : (grading N).adjoint = grading N := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [grading_eq_projections]
  simp only [LinearMap.sub_apply, inner_sub_left, inner_sub_right,
    positiveProjection_inner, negativeProjection_inner]

theorem positiveProjection_adjoint (N : ℕ) :
    (positiveProjection N).adjoint = positiveProjection N := by
  symm
  exact (LinearMap.eq_adjoint_iff _ _).mpr (positiveProjection_inner N)

theorem negativeProjection_adjoint (N : ℕ) :
    (negativeProjection N).adjoint = negativeProjection N := by
  symm
  exact (LinearMap.eq_adjoint_iff _ _).mpr (negativeProjection_inner N)

theorem sectors_orthogonal (N : ℕ) (x y : Space N) :
    inner ℂ (positiveProjection N x) (negativeProjection N y) = 0 := by
  rw [positiveProjection_inner]
  have h : positiveProjection N (negativeProjection N y) = 0 :=
    LinearMap.congr_fun (projections_mul N) y
  rw [h]
  simp

theorem sector_reconstruction (N : ℕ) (x : Space N) :
    positiveProjection N x + negativeProjection N x = x :=
  LinearMap.congr_fun (projections_sum N) x

theorem sector_energy (N : ℕ) (x : Space N) :
    ‖x‖ ^ 2 = ‖positiveProjection N x‖ ^ 2 + ‖negativeProjection N x‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 = ‖positiveProjection N x + negativeProjection N x‖ ^ 2 :=
      congrArg (fun y : Space N => ‖y‖ ^ 2) (sector_reconstruction N x).symm
    _ = _ := by
      simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        _ _ (sectors_orthogonal N x x)

theorem positive_formula (N : ℕ) :
    positiveProjection N = (1 / 2 : ℂ) • (1 + grading N) := by
  ext x i
  by_cases hi : Positive i
  · simp [hi, (show sign i.1.val = 1 from hi)]; ring
  · have hn : sign i.1.val = -1 := (sign_cases i.1.val).resolve_left hi
    simp [hi, hn]

theorem negative_formula (N : ℕ) :
    negativeProjection N = (1 / 2 : ℂ) • (1 - grading N) := by
  ext x i
  by_cases hi : Positive i
  · simp [hi, (show sign i.1.val = 1 from hi)]
  · have hn : sign i.1.val = -1 := (sign_cases i.1.val).resolve_left hi
    simp [hi, hn]; ring

theorem sector_finrank (N : ℕ) :
    Module.finrank ℂ (Space N) =
      Fintype.card (PositiveLabel N) + Fintype.card (NegativeLabel N) := by
  rw [(sectorCoordinates N).toLinearEquiv.finrank_eq]
  rw [(WithLp.linearEquiv 2 ℂ (PositiveSpace N × NegativeSpace N)).finrank_eq,
    Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace]

/-- The full operator, including off-diagonal sector blocks, has one
    compatible transport once the actual sector coordinates are fixed. -/
def operatorCoordinates (N : ℕ) :
    Module.End ℂ (Space N) ≃ₐ[ℂ] Module.End ℂ (SectorSpace N) :=
  (sectorCoordinates N).toLinearEquiv.conjAlgEquiv ℂ

theorem operatorCoordinates_intertwines (N : ℕ) (T : Module.End ℂ (Space N)) (x : Space N) :
    sectorCoordinates N (T x) = operatorCoordinates N T (sectorCoordinates N x) := by
  simp [operatorCoordinates, LinearEquiv.conjAlgEquiv_apply]

theorem operatorCoordinates_unique (N : ℕ) (T : Module.End ℂ (Space N)) :
    ∃! A : Module.End ℂ (SectorSpace N),
      ∀ x, A (sectorCoordinates N x) = sectorCoordinates N (T x) := by
  refine ⟨operatorCoordinates N T, fun x => (operatorCoordinates_intertwines N T x).symm, ?_⟩
  intro A hA
  ext y
  obtain ⟨x, rfl⟩ := (sectorCoordinates N).surjective y
  exact (hA x).trans (operatorCoordinates_intertwines N T x)

theorem sectorCoordinates_positiveProjection (N : ℕ) (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (positiveProjection N x)) =
      ((WithLp.ofLp (sectorCoordinates N x)).1, 0) := by
  apply Prod.ext
  · ext i
    change positiveProjection N x i.val = x i.val
    simp [i.property]
  · ext i
    change positiveProjection N x i.val = 0
    simp [i.property]

theorem sectorCoordinates_negativeProjection (N : ℕ) (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (negativeProjection N x)) =
      (0, (WithLp.ofLp (sectorCoordinates N x)).2) := by
  apply Prod.ext
  · ext i
    change negativeProjection N x i.val = 0
    simp [i.property]
  · ext i
    change negativeProjection N x i.val = x i.val
    simp [i.property]

theorem sectorCoordinates_grading (N : ℕ) (x : Space N) :
    WithLp.ofLp (sectorCoordinates N (grading N x)) =
      ((WithLp.ofLp (sectorCoordinates N x)).1,
        -(WithLp.ofLp (sectorCoordinates N x)).2) := by
  apply Prod.ext
  · ext i
    change sign i.val.1.val * x i.val = x i.val
    simp [show sign i.val.1.val = 1 from i.property]
  · ext i
    change sign i.val.1.val * x i.val = -x i.val
    have hi : sign i.val.1.val = -1 := (sign_cases i.val.1.val).resolve_left i.property
    simp [hi]

def matrixAction (N : ℕ) : Matrix (Label N) (Label N) ℂ ≃ₐ[ℂ]
    Module.End ℂ (Space N) :=
  Matrix.toLinAlgEquiv'.trans ((WithLp.linearEquiv 2 ℂ (Label N → ℂ)).symm.conjAlgEquiv ℂ)

@[simp] theorem matrixAction_apply (N : ℕ) (A : Matrix (Label N) (Label N) ℂ)
    (x : Space N) (i : Label N) :
    matrixAction N A x i = ∑ j, A i j * x j := rfl

theorem matrixAction_coefficient (N : ℕ) (A : Matrix (Label N) (Label N) ℂ)
    (i j : Label N) : matrixAction N A (PiLp.single 2 j 1) i = A i j := by
  simp [PiLp.single_apply]

/-- This equivalence quantifies over every matrix entry, including cross-root
    and cross-sector entries. No diagonal truncation is made. -/
theorem matrix_central_iff (N : ℕ) (A : Matrix (Label N) (Label N) ℂ) :
    grading N * matrixAction N A = matrixAction N A * grading N ↔
      ∀ i j, sign i.1.val * A i j = A i j * sign j.1.val := by
  constructor
  · intro h i j
    have he := congrArg (fun T : Module.End ℂ (Space N) => T (PiLp.single 2 j 1) i) h
    simpa [PiLp.single_apply, Finset.mul_sum, Finset.sum_mul] using he
  · intro h
    ext x i
    simp only [Module.End.mul_apply, grading_apply, matrixAction_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      sign i.1.val * (A i j * x j) = (sign i.1.val * A i j) * x j := by ring
      _ = (A i j * sign j.1.val) * x j := congrArg (fun z : ℂ => z * x j) (h i j)
      _ = A i j * (sign j.1.val * x j) := by ring

theorem matrix_odd_iff (N : ℕ) (A : Matrix (Label N) (Label N) ℂ) :
    grading N * matrixAction N A = -(matrixAction N A * grading N) ↔
      ∀ i j, sign i.1.val * A i j = -(A i j * sign j.1.val) := by
  constructor
  · intro h i j
    have he := congrArg (fun T : Module.End ℂ (Space N) => T (PiLp.single 2 j 1) i) h
    simpa [PiLp.single_apply, Finset.mul_sum, Finset.sum_mul] using he
  · intro h
    ext x i
    simp only [Module.End.mul_apply, LinearMap.neg_apply, PiLp.neg_apply,
      grading_apply, matrixAction_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    calc
      sign i.1.val * (A i j * x j) = (sign i.1.val * A i j) * x j := by ring
      _ = -(A i j * sign j.1.val) * x j := congrArg (fun z : ℂ => z * x j) (h i j)
      _ = -(A i j * (sign j.1.val * x j)) := by ring

/-- Oddness exchanges the actual sectors. It is a property to prove for
    an operator, not an independently assumed exchange of two copies. -/
theorem odd_exchanges (N : ℕ) (T : Module.End ℂ (Space N))
    (hT : grading N * T = -(T * grading N)) :
    positiveProjection N * T = T * negativeProjection N ∧
      negativeProjection N * T = T * positiveProjection N := by
  constructor
  · rw [positive_formula, negative_formula, smul_mul_assoc, mul_smul_comm,
      add_mul, mul_sub, one_mul, mul_one, hT]
    simp [sub_eq_add_neg]
  · rw [positive_formula, negative_formula, smul_mul_assoc, mul_smul_comm,
      sub_mul, mul_add, one_mul, mul_one, hT]
    simp

def gaussian (N : ℕ) (t : ℝ) : Module.End ℂ (Space N) where
  toFun x := WithLp.toLp 2 fun i =>
    (Real.exp (-t * (i.1.val + 1 : ℝ) ^ 2) : ℂ) * x i
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_left_comm]

theorem gaussian_central (N : ℕ) (t : ℝ) :
    grading N * gaussian N t = gaussian N t * grading N := by
  ext x i
  change sign i.1.val * (_ * x i) = _ * (sign i.1.val * x i)
  ring

theorem gaussian_positive (N : ℕ) (t : ℝ) :
    positiveProjection N * gaussian N t = gaussian N t * positiveProjection N := by
  ext x i
  by_cases hi : Positive i <;> simp [gaussian, hi]

theorem gaussian_negative (N : ℕ) (t : ℝ) :
    negativeProjection N * gaussian N t = gaussian N t * negativeProjection N := by
  ext x i
  by_cases hi : Positive i <;> simp [gaussian, hi]

theorem gaussian_zero (N : ℕ) : gaussian N 0 = 1 := by
  ext x i
  simp [gaussian]

theorem gaussian_semigroup (N : ℕ) (s t : ℝ) :
    gaussian N (s + t) = gaussian N s * gaussian N t := by
  ext x i
  simp only [Module.End.mul_apply]
  change (Real.exp (-(s + t) * (i.1.val + 1 : ℝ) ^ 2) : ℂ) * x i =
    (Real.exp (-s * (i.1.val + 1 : ℝ) ^ 2) : ℂ) *
      ((Real.exp (-t * (i.1.val + 1 : ℝ) ^ 2) : ℂ) * x i)
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  have he : -(s + t) * (i.1.val + 1 : ℝ) ^ 2 =
      -s * (i.1.val + 1 : ℝ) ^ 2 + -t * (i.1.val + 1 : ℝ) ^ 2 := by ring
  rw [he]

/-- Reversing every ordered vertex acts within the original root and phase. -/
def reflectLabel {N : ℕ} (i : Label N) : Label N :=
  ⟨i.1, HistoryPhaseBundle.reflection i.1.val i.2⟩

@[simp] theorem reflectLabel_twice {N : ℕ} (i : Label N) :
    reflectLabel (reflectLabel i) = i := by
  rcases i with ⟨b, h, z⟩
  change (⟨b, (CompleteHistoryGeometry.reflect (CompleteHistoryGeometry.reflect h), z)⟩ :
    Label N) = ⟨b, (h, z)⟩
  rw [HistoryObservation.reflect_involutive]

def reflectionEquiv (N : ℕ) : Label N ≃ Label N where
  toFun := reflectLabel
  invFun := reflectLabel
  left_inv := reflectLabel_twice
  right_inv := reflectLabel_twice

def reflectionUnitary (N : ℕ) : Space N ≃ₗᵢ[ℂ] Space N :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (reflectionEquiv N)

def reflection (N : ℕ) : Module.End ℂ (Space N) :=
  (reflectionUnitary N).toLinearEquiv.toLinearMap

@[simp] theorem reflection_apply (N : ℕ) (x : Space N) (i : Label N) :
    reflection N x i = x (reflectLabel i) := rfl

theorem reflection_square (N : ℕ) : reflection N * reflection N = 1 := by
  ext x i
  simp

theorem reflection_adjoint (N : ℕ) : (reflection N).adjoint = reflection N := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have h := (reflectionUnitary N).inner_map_map x (reflection N y)
  have hi : reflectionUnitary N (reflection N y) = y :=
    LinearMap.congr_fun (reflection_square N) y
  change inner ℂ (reflection N x) (reflectionUnitary N (reflection N y)) =
    inner ℂ x (reflection N y) at h
  rwa [hi] at h

/-- Ordered-history reversal is even for prime occupation parity. -/
theorem reflection_central (N : ℕ) :
    grading N * reflection N = reflection N * grading N := by
  ext x i
  rfl

theorem reflection_positive (N : ℕ) :
    positiveProjection N * reflection N = reflection N * positiveProjection N := by
  ext x i
  rfl

theorem reflection_negative (N : ℕ) :
    negativeProjection N * reflection N = reflection N * negativeProjection N := by
  ext x i
  rfl

theorem reflection_gaussian (N : ℕ) (t : ℝ) :
    reflection N * gaussian N t = gaussian N t * reflection N := by
  ext x i
  rfl

structure Conclusions : Prop where
  character : ∀ n, sign n = (GeneratedPrimeParity.rootCentre (n + 1) : ℂ)
  self_adjoint : ∀ N, (grading N).adjoint = grading N
  involution : ∀ N, grading N * grading N = 1
  complete_sectors : ∀ N, positiveProjection N + negativeProjection N = 1
  orthogonal_sectors : ∀ N (x y : Space N),
    inner ℂ (positiveProjection N x) (negativeProjection N y) = 0
  energy_reconstruction : ∀ N (x : Space N),
    ‖x‖ ^ 2 = ‖positiveProjection N x‖ ^ 2 + ‖negativeProjection N x‖ ^ 2
  derived_dimensions : ∀ N, Module.finrank ℂ (Space N) =
    Fintype.card (PositiveLabel N) + Fintype.card (NegativeLabel N)
  gaussian_compatibility : ∀ N t, grading N * gaussian N t = gaussian N t * grading N
  independent_reflection : ∀ N, grading N * reflection N = reflection N * grading N
  reflection_isometry : ∀ N (x : Space N), ‖reflection N x‖ = ‖x‖
  complete_transport : ∀ N (T : Module.End ℂ (Space N)),
    ∃! A : Module.End ℂ (SectorSpace N),
      ∀ x, A (sectorCoordinates N x) = sectorCoordinates N (T x)
  odd_blocks : ∀ N (A : Matrix (Label N) (Label N) ℂ),
    grading N * matrixAction N A = -(matrixAction N A * grading N) ↔
      ∀ i j, sign i.1.val * A i j = -(A i j * sign j.1.val)
  gaussian_composition : ∀ N s t, gaussian N (s + t) = gaussian N s * gaussian N t

theorem generated : Conclusions where
  character := sign_eq_rootCentre
  self_adjoint := grading_adjoint
  involution := grading_square
  complete_sectors := projections_sum
  orthogonal_sectors := sectors_orthogonal
  energy_reconstruction := sector_energy
  derived_dimensions := sector_finrank
  gaussian_compatibility := gaussian_central
  independent_reflection := reflection_central
  reflection_isometry := fun N x => (reflectionUnitary N).norm_map x
  complete_transport := operatorCoordinates_unique
  odd_blocks := matrix_odd_iff
  gaussian_composition := gaussian_semigroup

end GeneratedFoundations.Arithmetic.HistoryCentralSectors
