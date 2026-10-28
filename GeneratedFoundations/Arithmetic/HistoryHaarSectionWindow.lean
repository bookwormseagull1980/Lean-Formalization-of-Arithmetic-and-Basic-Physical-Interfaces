module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionJointHessian
public import GeneratedFoundations.Arithmetic.HistorySpectralWindow

/-!
# Exhaustive source windows of the position-dependent action

The observation is formed on the complete basis of the actual joint
Hessian. The source cutoff uses the kinetic index; the restoring Casimir
stays in the resolvent denominator. All scalar source rows, both coclosed
curl branches and all history matrix entries are enumerated. The finite
Gaussian trace below is not identified with an effective-action coefficient
or a physical normalization without a separate derivation of that vertex.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionWindow

open Geometry.SourceQuotientHilbert
open HistoryHaarSectionJointHessian (Index eigenvalue)

def kinetic (N : ℕ) : Index N → ℝ :=
  Sum.elim (HistoryHaarClosedHessian.eigenvalue N)
    (fun a => Geometry.SourceCasimirClosure.energy a.2.val.1)

def restoring (N : ℕ) : Index N → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => HistoryDefiningResponse.coefficient N)

theorem source_response_decomposition (N : ℕ) (i : Index N) :
    eigenvalue N i = kinetic N i + restoring N i := by
  cases i <;> simp [eigenvalue, kinetic, restoring, HistoryHaarSectionHessian.eigenvalue]

theorem kinetic_nonneg (N : ℕ) (i : Index N) : 0 ≤ kinetic N i := by
  cases i with
  | inl a => exact (HistoryHaarClosedHessian.eigenvalue_pos N a).le
  | inr a => exact Geometry.SourceCasimirClosure.energy_nonneg _

theorem restoring_nonneg (N : ℕ) (i : Index N) : 0 ≤ restoring N i := by
  cases i with
  | inl a => exact le_refl 0
  | inr a => exact (HistoryDefiningResponse.coefficient_pos N).le

def scalarCandidates (D : ℕ) : Finset EvenIndex := by
  classical
  exact (Finset.range D).biUnion fun m =>
    if hm : Even m then
      Finset.univ.image fun p : Fin (m + 1) × Fin (m + 1) =>
        (⟨⟨m, p.1, p.2⟩, hm⟩ : EvenIndex)
    else ∅

@[simp] theorem mem_scalarCandidates (D : ℕ) (a : EvenIndex) :
    a ∈ scalarCandidates D ↔ a.val.1 < D := by
  classical
  unfold scalarCandidates
  constructor
  · intro h
    obtain ⟨m, hm, ha⟩ := Finset.mem_biUnion.mp h
    split_ifs at ha with he
    · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ha
      have hd := congrArg (fun b : EvenIndex => b.val.1) hp
      simpa only [← hd] using Finset.mem_range.mp hm
    · simp at ha
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨a.val.1, Finset.mem_range.mpr h, ?_⟩
    simp only [dite_eq_left a.property]
    exact Finset.mem_image.mpr ⟨(a.val.2.1, a.val.2.2), Finset.mem_univ _, rfl⟩

def candidates (N D : ℕ) : Finset (Index N) := by
  classical
  exact ((Finset.univ : Finset (HistoryHaarClosedHessian.Label N)) ×ˢ
    HistorySpectralWindow.fieldCandidates D).disjSum
      ((Finset.univ : Finset (HistoryHaarSectionHessian.Label N)) ×ˢ scalarCandidates D)

theorem cutoff_mem_candidates (N : ℕ) (B : ℝ) (i : Index N)
    (hi : kinetic N i < B) :
    i ∈ candidates N (HistorySpectralWindow.enumerationBound B) := by
  classical
  cases i with
  | inl a =>
    have hm := HistorySpectralWindow.cutoff_mem_candidates N B (.inl a) hi
    simpa [HistorySpectralWindow.jointCandidates, candidates] using hm
  | inr a =>
    have he : Geometry.SourceCasimirClosure.energy a.2.val.1 < B := hi
    have hm : (0 : ℝ) ≤ a.2.val.1 := Nat.cast_nonneg _
    have hb : B < (HistorySpectralWindow.enumerationBound B : ℝ) := by
      have hceil : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
      simp only [HistorySpectralWindow.enumerationBound, Nat.cast_add, Nat.cast_one]
      linarith
    have hd : a.2.val.1 < HistorySpectralWindow.enumerationBound B := by
      by_contra hnot
      have hn := Nat.le_of_not_gt hnot
      have hc : (HistorySpectralWindow.enumerationBound B : ℝ) ≤ a.2.val.1 := by
        exact_mod_cast hn
      have hone : (1 : ℝ) ≤ a.2.val.1 := by
        exact_mod_cast (show 1 ≤ a.2.val.1 by
          have : 1 ≤ HistorySpectralWindow.enumerationBound B := by
            unfold HistorySpectralWindow.enumerationBound
            omega
          omega)
      unfold Geometry.SourceCasimirClosure.energy at he
      nlinarith
    simp [candidates, hd]

def support (N : ℕ) (B : ℝ) : Finset (Index N) := by
  classical
  exact (candidates N (HistorySpectralWindow.enumerationBound B)).filter
    fun i => kinetic N i < B

@[simp] theorem mem_support (N : ℕ) (B : ℝ) (i : Index N) :
    i ∈ support N B ↔ kinetic N i < B := by
  classical
  simp only [support, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨cutoff_mem_candidates N B i h, h⟩⟩

theorem support_unique (N : ℕ) (B : ℝ) (S : Finset (Index N))
    (hS : ∀ i, i ∈ S ↔ kinetic N i < B) : S = support N B := by
  ext i
  exact (hS i).trans (mem_support N B i).symm

theorem support_mono (N : ℕ) {B C : ℝ} (hBC : B ≤ C) :
    support N B ⊆ support N C := by
  intro i hi
  exact (mem_support N C i).mpr (lt_of_lt_of_le ((mem_support N B i).mp hi) hBC)

def positionIndex (N j : ℕ) (a : HistoryHaarSectionAction.PositionLabels N j) : Index N :=
  .inr (a.1, ⟨⟨2 * j, a.2.1, a.2.2⟩, by
    change Even (2 * j)
    exact ⟨j, by omega⟩⟩)

theorem positionIndex_injective (N j : ℕ) : Function.Injective (positionIndex N j) := by
  rintro ⟨i, r, c⟩ ⟨i', r', c'⟩ h
  simpa [positionIndex] using h

theorem kinetic_positionIndex (N j : ℕ)
    (a : HistoryHaarSectionAction.PositionLabels N j) :
    kinetic N (positionIndex N j a) = Geometry.SourceScalarKineticForm.position j := rfl

/-- Every coefficient in a row is retained together, with no quotient of
its history labels or its two matrix-coefficient coordinates. -/
theorem position_membership (N j : ℕ) (B : ℝ)
    (a : HistoryHaarSectionAction.PositionLabels N j) :
    positionIndex N j a ∈ support N B ↔
      Geometry.SourceScalarKineticForm.position j < B := by
  rw [mem_support, kinetic_positionIndex]

theorem positions_plateau (m : ℕ) (B : ℝ) :
    (∀ j, Geometry.SourceScalarKineticForm.position j < B ↔ j < m + 1) ↔
      Geometry.SourceScalarKineticForm.position m < B ∧
      B ≤ Geometry.SourceScalarKineticForm.position (m + 1) :=
  Geometry.SourceScalarKineticForm.position_plateau_iff m B

def kernel (N : ℕ) (i : Index N) (u : ℝ) : ℝ :=
  ((u ^ 2 + kinetic N i) / (u ^ 2 + eigenvalue N i)) ^ 2 *
    Real.exp (-(u ^ 2 + kinetic N i))

theorem kernel_nonneg (N : ℕ) (i : Index N) (u : ℝ) : 0 ≤ kernel N i u :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem kernel_continuous (N : ℕ) (i : Index N) : Continuous (kernel N i) := by
  have hd : ∀ u : ℝ, u ^ 2 + eigenvalue N i ≠ 0 := by
    intro u
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg u)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15 / 8)
        (HistoryHaarSectionJointHessian.eigenvalue_lower N i)))
  unfold kernel
  fun_prop (disch := exact hd _)

def branchIntegral (N : ℕ) (B : ℝ) (i : Index N) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i), kernel N i u

theorem branchIntegral_nonneg (N : ℕ) (B : ℝ) (i : Index N) :
    0 ≤ branchIntegral N B i :=
  intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _) (kernel_nonneg N i)

/-- Below a branch's kinetic birth its integral vanishes, including at the
strict cutoff boundary itself. -/
theorem branchIntegral_eq_zero (N : ℕ) (B : ℝ) (i : Index N)
    (hi : B ≤ kinetic N i) : branchIntegral N B i = 0 := by
  simp only [branchIntegral, Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr hi),
    intervalIntegral.integral_same]

theorem branchIntegral_mono (N : ℕ) (i : Index N) :
    Monotone (fun B => branchIntegral N B i) := by
  intro B C hBC
  apply intervalIntegral.integral_mono_interval le_rfl (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt (sub_le_sub_right hBC _))
  · exact Filter.Eventually.of_forall (kernel_nonneg N i)
  · exact (kernel_continuous N i).intervalIntegrable _ _

theorem branchIntegral_strictMonoOn (N : ℕ) (i : Index N) :
    StrictMonoOn (fun B => branchIntegral N B i) (Set.Ici (kinetic N i)) := by
  intro B hB C _ hBC
  have hs : Real.sqrt (B - kinetic N i) < Real.sqrt (C - kinetic N i) :=
    Real.sqrt_lt_sqrt (sub_nonneg.mpr hB) (sub_lt_sub_right hBC _)
  have hp : 0 < ∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i),
      kernel N i u := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((kernel_continuous N i).intervalIntegrable _ _) (fun u hu => ?_) hs
    have hu' : 0 < u := lt_of_le_of_lt (Real.sqrt_nonneg _) hu.1
    exact mul_pos (sq_pos_of_pos (div_pos
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu') (kinetic_nonneg N i))
      (add_pos_of_nonneg_of_pos (sq_nonneg u)
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15 / 8)
          (HistoryHaarSectionJointHessian.eigenvalue_lower N i))))) (Real.exp_pos _)
  have ha : (∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i), kernel N i u) +
      (∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i), kernel N i u) =
      ∫ u in (0 : ℝ)..Real.sqrt (C - kinetic N i), kernel N i u :=
    intervalIntegral.integral_add_adjacent_intervals
    ((kernel_continuous N i).intervalIntegrable 0 (Real.sqrt (B - kinetic N i)))
    ((kernel_continuous N i).intervalIntegrable
      (Real.sqrt (B - kinetic N i)) (Real.sqrt (C - kinetic N i)))
  dsimp [branchIntegral]
  linarith

theorem branchIntegral_pos (N : ℕ) (B : ℝ) (i : Index N)
    (hi : i ∈ support N B) : 0 < branchIntegral N B i := by
  have hcut : 0 < B - kinetic N i := sub_pos.mpr ((mem_support N B i).mp hi)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((kernel_continuous N i).intervalIntegrable _ _) (fun u hu => ?_)
    (Real.sqrt_pos.mpr hcut)
  apply mul_pos (sq_pos_of_pos (div_pos
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu.1) (kinetic_nonneg N i))
    (add_pos_of_nonneg_of_pos (sq_nonneg u)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15 / 8)
        (HistoryHaarSectionJointHessian.eigenvalue_lower N i))))) (Real.exp_pos _)

/-- The unnormalized complete finite spectral response. Any effective
vertex normalization must be derived before calling this a coupling. -/
def responseTrace (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ support N B, branchIntegral N B i

/-- Enlargement keeps all earlier branches and the exact contribution of
each new birth. Earlier integrals extend by zero below their own birth. -/
theorem responseTrace_eq_larger_sum (N : ℕ) {B C : ℝ} (hBC : B ≤ C) :
    responseTrace N B = ∑ i ∈ support N C, branchIntegral N B i := by
  classical
  apply Finset.sum_subset (support_mono N hBC)
  intro i _ hnot
  exact branchIntegral_eq_zero N B i
    (le_of_not_gt (fun hi => hnot ((mem_support N B i).mpr hi)))

theorem responseTrace_mono (N : ℕ) : Monotone (responseTrace N) := by
  intro B C hBC
  rw [responseTrace_eq_larger_sum N hBC]
  exact Finset.sum_le_sum (fun i _ => branchIntegral_mono N i hBC)

theorem responseTrace_strictMonoOn (N : ℕ) :
    StrictMonoOn (responseTrace N) (Set.Ici 0) := by
  classical
  intro B hB C hC hBC
  change 0 ≤ B at hB
  change 0 ≤ C at hC
  let a : HistoryHaarSectionAction.PositionLabels N 0 := Classical.arbitrary _
  let i : Index N := positionIndex N 0 a
  have hi0 : kinetic N i = 0 := by
    change Geometry.SourceScalarKineticForm.position 0 = 0
    norm_num [Geometry.SourceScalarKineticForm.position_eq]
  have hi : i ∈ support N C := (mem_support N C i).mpr (by rw [hi0]; linarith)
  rw [responseTrace_eq_larger_sum N hBC.le]
  exact Finset.sum_lt_sum
    (fun j _ => branchIntegral_mono N j hBC.le)
    ⟨i, hi, branchIntegral_strictMonoOn N i (by simpa only [Set.mem_Ici, hi0] using hB)
      (by simpa only [Set.mem_Ici, hi0] using hC) hBC⟩

def positionIntegral (N j : ℕ) (B : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - Geometry.SourceScalarKineticForm.position j),
    ((u ^ 2 + Geometry.SourceScalarKineticForm.position j) /
      (u ^ 2 + (Geometry.SourceScalarKineticForm.position j +
        HistoryDefiningResponse.coefficient N))) ^ 2 *
      Real.exp (-(u ^ 2 + Geometry.SourceScalarKineticForm.position j))

theorem branchIntegral_positionIndex (N j : ℕ) (B : ℝ)
    (a : HistoryHaarSectionAction.PositionLabels N j) :
    branchIntegral N B (positionIndex N j a) = positionIntegral N j B := rfl

/-- The trace on one complete source row counts its actual orthonormal
coefficients. The multiplicity is inherited from the source, not fitted. -/
theorem complete_position_trace (N j : ℕ) (B : ℝ) :
    (∑ a : HistoryHaarSectionAction.PositionLabels N j,
      branchIntegral N B (positionIndex N j a)) =
      (HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2 : ℕ) *
        positionIntegral N j B := by
  simp only [branchIntegral_positionIndex, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, HistoryHaarSectionAction.position_multiplicity]

theorem scalar_first_shell (a : EvenIndex) {B : ℝ} (hlo : 0 < B) (hhi : B ≤ 8) :
    Geometry.SourceCasimirClosure.energy a.val.1 < B ↔ a.val.1 = 0 := by
  obtain ⟨j, hj⟩ := a.property
  have hm : a.val.1 = 2 * j := by omega
  have he : Geometry.SourceCasimirClosure.energy a.val.1 =
      Geometry.SourceScalarKineticForm.position j := by rw [hm]; rfl
  rw [he]
  have hp := (Geometry.SourceScalarKineticForm.first_position_plateau_iff B).mpr ⟨hlo, hhi⟩ j
  exact hp.trans (by omega)

theorem scalar_two_shells (a : EvenIndex) {B : ℝ} (hlo : 8 < B) (hhi : B ≤ 24) :
    Geometry.SourceCasimirClosure.energy a.val.1 < B ↔
      a.val.1 = 0 ∨ a.val.1 = 2 := by
  obtain ⟨j, hj⟩ := a.property
  have hm : a.val.1 = 2 * j := by omega
  have he : Geometry.SourceCasimirClosure.energy a.val.1 =
      Geometry.SourceScalarKineticForm.position j := by rw [hm]; rfl
  rw [he]
  have hp := (Geometry.SourceScalarKineticForm.position_plateau_iff 1 B).mpr
    (by norm_num [Geometry.SourceScalarKineticForm.position_eq]; exact ⟨hlo, hhi⟩)
  exact (hp j).trans (by omega)

/-- The full support between the first connection shell and the next
scalar shell. Every matrix/history coefficient remains present. -/
theorem mem_support_first_plateau (N : ℕ) {B : ℝ} (hlo : 4 < B) (hhi : B ≤ 8)
    (i : Index N) :
    i ∈ support N B ↔ Sum.elim
      (fun a => Geometry.SourceOneFormHodgeLaplacian.hodgeEigenvalue a.2 = 4)
      (fun a => a.2.val.1 = 0) i := by
  rw [mem_support]
  cases i with
  | inl a => exact HistorySpectralWindow.field_first_shell a.2 hlo (by linarith)
  | inr a => exact scalar_first_shell a.2 (by linarith) hhi

/-- After degree two is born, the next actual birth is the connection
shell at sixteen. The restoring Casimir does not alter these edges. -/
theorem mem_support_second_plateau (N : ℕ) {B : ℝ} (hlo : 8 < B) (hhi : B ≤ 16)
    (i : Index N) :
    i ∈ support N B ↔ Sum.elim
      (fun a => Geometry.SourceOneFormHodgeLaplacian.hodgeEigenvalue a.2 = 4)
      (fun a => a.2.val.1 = 0 ∨ a.2.val.1 = 2) i := by
  rw [mem_support]
  cases i with
  | inl a => exact HistorySpectralWindow.field_first_shell a.2 (by linarith) hhi
  | inr a => exact scalar_two_shells a.2 hlo (by linarith)

theorem second_plateau_support_constant (N : ℕ) {B C : ℝ}
    (hBlo : 8 < B) (hBhi : B ≤ 16) (hClo : 8 < C) (hChi : C ≤ 16) :
    support N B = support N C := by
  ext i
  exact (mem_support_second_plateau N hBlo hBhi i).trans
    (mem_support_second_plateau N hClo hChi i).symm

theorem responseTrace_pos (N : ℕ) (B : ℝ) (h : (support N B).Nonempty) :
    0 < responseTrace N B :=
  Finset.sum_pos (fun i hi => branchIntegral_pos N B i hi) h

structure Conclusions : Prop where
  actual_spectral_decomposition : ∀ N i,
    eigenvalue N i = kinetic N i + restoring N i
  exhaustive_support : ∀ N B i, i ∈ support N B ↔ kinetic N i < B
  unique_support : ∀ N B S, (∀ i, i ∈ S ↔ kinetic N i < B) → S = support N B
  full_position_rows : ∀ N j B a, positionIndex N j a ∈ support N B ↔
    Geometry.SourceScalarKineticForm.position j < B
  actual_position_trace : ∀ N j B,
    (∑ a : HistoryHaarSectionAction.PositionLabels N j,
      branchIntegral N B (positionIndex N j a)) =
      (HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2 : ℕ) *
        positionIntegral N j B
  finite_response_positive : ∀ N B, (support N B).Nonempty → 0 < responseTrace N B
  complete_window_response_monotone : ∀ N,
    StrictMonoOn (responseTrace N) (Set.Ici 0)
  first_joint_plateau : ∀ N B, 4 < B → B ≤ 8 → ∀ i,
    i ∈ support N B ↔ Sum.elim
      (fun a => Geometry.SourceOneFormHodgeLaplacian.hodgeEigenvalue a.2 = 4)
      (fun a => a.2.val.1 = 0) i
  second_joint_plateau : ∀ N B, 8 < B → B ≤ 16 → ∀ i,
    i ∈ support N B ↔ Sum.elim
      (fun a => Geometry.SourceOneFormHodgeLaplacian.hodgeEigenvalue a.2 = 4)
      (fun a => a.2.val.1 = 0 ∨ a.2.val.1 = 2) i

theorem generated : Conclusions where
  actual_spectral_decomposition := source_response_decomposition
  exhaustive_support := mem_support
  unique_support := support_unique
  full_position_rows := position_membership
  actual_position_trace := complete_position_trace
  finite_response_positive := responseTrace_pos
  complete_window_response_monotone := responseTrace_strictMonoOn
  first_joint_plateau := fun N _ hlo hhi => mem_support_first_plateau N hlo hhi
  second_joint_plateau := fun N _ hlo hhi => mem_support_second_plateau N hlo hhi

end GeneratedFoundations.Arithmetic.HistoryHaarSectionWindow
