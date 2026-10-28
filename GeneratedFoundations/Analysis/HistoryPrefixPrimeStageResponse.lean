module

public import GeneratedFoundations.Analysis.HistoryPrefixSubsetResponse
public import GeneratedFoundations.Analysis.CapacityRestoredWindowBudget

/-!
# True maximum-prime births in the complete prefix response

The original positive prefix state contains all roots and their history--phase
fibres. The maximum-prime stage and its birth are projectors in that same
observation algebra. Their mixed Hessian is computed with the native Mobius
probe before any estimate. Multiplication by the actual prime reverses this
probe, transports its Gaussian mass to L/p, and leaves the old cutoff boundary
in the old state. The restored conditional response agrees with the existing
opposite-center capacity ledger, including its exact mixing square.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryPrefixPrimeStageResponse

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open HistoryPrefixGibbsResponse
open GeneratedMobiusObservation CenterEndpointPotential MaximumPrimeFactorStage
open HistoryPrefixSubsetResponse

def oldPair (N : ℕ) (alpha L : ℝ) (p : ℕ) : CentrePair :=
  beforePair (gaussianRootMass alpha L) p (N + 1)

def returnedPair (N : ℕ) (alpha L : ℝ) (p : ℕ) : CentrePair :=
  returnPair (gaussianRootMass alpha L) p (N + 1)

def stagePair (N : ℕ) (alpha L : ℝ) (p : ℕ) : CentrePair :=
  sectorPairOn (gaussianRootMass alpha L) (stageAfter p (N + 1))

def nativeProbe (n : ℕ) : ℝ := (generatedMoebius n : ℝ)

def birthMark (N p n : ℕ) : ℝ := by
  classical
  exact if n ∈ stageBirth p (N + 1) then 1 else 0

def stageResponse (N : ℕ) (alpha L : ℝ) (p : ℕ) (f g : ℕ → ℝ) : ℝ :=
  GibbsTraceForm.Z (logIntensity N alpha L) *
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (centeredObservation N alpha L (stageAfter p (N + 1)) f)
      (centeredObservation N alpha L (stageAfter p (N + 1)) g)

theorem stageBirth_squarefree {p N n : ℕ} (hp : p.Prime)
    (hn : n ∈ stageBirth p N) : Squarefree n := by
  obtain ⟨m, hm, rfl⟩ := mem_stageBirth.mp hn
  apply generatedMoebius_ne_zero_iff_squarefree.mp
  rw [generatedMoebius_stage_mul hp hm]
  exact neg_ne_zero.mpr (generatedMoebius_ne_zero_iff_squarefree.mpr
    (mem_stagePairedBase.mp hm).2.2.1)

theorem stageAfter_squarefree {p N n : ℕ} (hp : p.Prime)
    (hn : n ∈ stageAfter p N) : Squarefree n := by
  rcases Finset.mem_union.mp hn with ho | hb
  · exact (mem_stageBefore.mp ho).2.2.1
  · exact stageBirth_squarefree hp hb

theorem stage_subset (N : ℕ) {p : ℕ} (hp : p.Prime) :
    stageAfter p (N + 1) ⊆ SignedGaussianEnergy.rootRange (N + 1) :=
  CapacityRestoredWindowBudget.stageAfter_subset_rootRange hp

theorem unit_mem_old (N p : ℕ) : 1 ∈ stageBefore p (N + 1) := by
  rw [mem_stageBefore]
  simp [factorsBelow]

theorem stage_capacity_pos (N : ℕ) (alpha L : ℝ) (p : ℕ) :
    0 < capacity alpha L (stageAfter p (N + 1)) :=
  capacity_pos alpha L ⟨1, Finset.mem_union_left _ (unit_mem_old N p)⟩

/-- All members here belong to the actual native square-free support.
No nonsquarefree root is removed from the full positive reference state. -/
theorem sector_capacity (alpha L : ℝ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n) :
    CentrePair.capacity (sectorPairOn (gaussianRootMass alpha L) S) =
      capacity alpha L S := by
  classical
  unfold CentrePair.capacity sectorPairOn capacity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hne := generatedMoebius_ne_zero_iff_squarefree.mpr (hS n hn)
  have hc := ArithmeticFunction.moebius_eq_or n
  rw [← generatedMoebius_eq_moebius] at hc
  rcases hc with h | h | h
  · exact False.elim (hne h)
  · simp [h]
  · simp [h]

theorem stage_capacity (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    capacity alpha L (stageAfter p (N + 1)) = CentrePair.capacity (stagePair N alpha L p) :=
  (sector_capacity alpha L _ (fun _ hn => stageAfter_squarefree hp hn)).symm

theorem stage_signed_moment (N : ℕ) (alpha L : ℝ) (p : ℕ) :
    moment alpha L (stageAfter p (N + 1)) nativeProbe = CentrePair.signed (stagePair N alpha L p) := by
  rw [stagePair, sectorPairOn_signed]
  unfold moment nativeProbe
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem stage_probe_square_moment (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    moment alpha L (stageAfter p (N + 1)) (fun n => nativeProbe n * nativeProbe n) =
      CentrePair.capacity (stagePair N alpha L p) := by
  rw [← stage_capacity N alpha L hp]
  unfold moment capacity
  apply Finset.sum_congr rfl
  intro n hn
  have hs := generatedSquarefree_iff_squarefree.mpr (stageAfter_squarefree hp hn)
  have hh : generatedMoebius n * generatedMoebius n = 1 := by
    simpa only [pow_two, squarefreeProjector_of_generatedSquarefree hs] using generatedMoebius_sq n
  have hr : nativeProbe n * nativeProbe n = 1 := by
    change (generatedMoebius n : ℝ) * (generatedMoebius n : ℝ) = 1
    exact_mod_cast hh
  change gaussianRootMass alpha L n * (nativeProbe n * nativeProbe n) = _
  rw [hr, mul_one]

theorem stage_eq_oppositeMix (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    stagePair N alpha L p = CentrePair.oppositeMix (oldPair N alpha L p) (returnedPair N alpha L p) := by
  rw [stagePair, stageAfter, sectorPairOn_union _ (disjoint_stageBefore_stageBirth hp),
    sectorPairOn_stageBirth_eq_birthPair _ hp]
  rfl

theorem birth_moment (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    moment alpha L (stageAfter p (N + 1)) (birthMark N p) =
      CentrePair.capacity (returnedPair N alpha L p) := by
  classical
  have hsub : stageBirth p (N + 1) ⊆ stageAfter p (N + 1) := Finset.subset_union_right
  change (∑ n ∈ stageAfter p (N + 1), gaussianRootMass alpha L n *
    (if n ∈ stageBirth p (N + 1) then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  change capacity alpha L (stageBirth p (N + 1)) = _
  rw [← sector_capacity alpha L _ (fun _ hn => stageBirth_squarefree hp hn),
    sectorPairOn_stageBirth_eq_birthPair _ hp, birthPair, CentrePair.capacity_swap]
  rfl

theorem birth_square_moment (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    moment alpha L (stageAfter p (N + 1)) (fun n => birthMark N p n * birthMark N p n) =
      CentrePair.capacity (returnedPair N alpha L p) := by
  have he : (fun n => birthMark N p n * birthMark N p n) = birthMark N p := by
    classical
    funext n
    by_cases hn : n ∈ stageBirth p (N + 1) <;> simp [birthMark, hn]
  rw [he, birth_moment N alpha L hp]

/-- The negative return is forced by the native prime generation rule;
it is not a sign assigned to a freely chosen comparison state. -/
theorem mixed_moment (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    moment alpha L (stageAfter p (N + 1)) (fun n => nativeProbe n * birthMark N p n) =
      -CentrePair.signed (returnedPair N alpha L p) := by
  classical
  have hsub : stageBirth p (N + 1) ⊆ stageAfter p (N + 1) := Finset.subset_union_right
  change (∑ n ∈ stageAfter p (N + 1), gaussianRootMass alpha L n *
    (nativeProbe n * (if n ∈ stageBirth p (N + 1) then 1 else 0))) = _
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  have he : (∑ n ∈ stageBirth p (N + 1), gaussianRootMass alpha L n * nativeProbe n) =
      CentrePair.signed (sectorPairOn (gaussianRootMass alpha L) (stageBirth p (N + 1))) := by
    rw [sectorPairOn_signed]
    apply Finset.sum_congr rfl
    intro n _
    unfold nativeProbe
    ring
  rw [he, sectorPairOn_stageBirth_eq_birthPair _ hp, birthPair_signed]
  rfl

theorem stage_response (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) (f g : ℕ → ℝ) :
    stageResponse N alpha L p f g =
      moment alpha L (stageAfter p (N + 1)) (fun n => f n * g n) -
        moment alpha L (stageAfter p (N + 1)) f *
          moment alpha L (stageAfter p (N + 1)) g / CentrePair.capacity (stagePair N alpha L p) := by
  unfold stageResponse
  rw [restored_centered_hessian N alpha L _ (stage_subset N hp)
    (stage_capacity_pos N alpha L p).ne', stage_capacity N alpha L hp]

theorem centre_response (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    stageResponse N alpha L p nativeProbe nativeProbe =
      CentrePair.capacity (stagePair N alpha L p) -
        CentrePair.signed (stagePair N alpha L p) ^ 2 / CentrePair.capacity (stagePair N alpha L p) := by
  rw [stage_response N alpha L hp, stage_probe_square_moment N alpha L hp,
    stage_signed_moment, pow_two]

theorem birth_response (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    stageResponse N alpha L p (birthMark N p) (birthMark N p) =
      CentrePair.capacity (returnedPair N alpha L p) -
        CentrePair.capacity (returnedPair N alpha L p) ^ 2 / CentrePair.capacity (stagePair N alpha L p) := by
  rw [stage_response N alpha L hp, birth_square_moment N alpha L hp,
    birth_moment N alpha L hp, pow_two]

theorem mixed_response (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    stageResponse N alpha L p nativeProbe (birthMark N p) =
      -CentrePair.signed (returnedPair N alpha L p) -
        CentrePair.signed (stagePair N alpha L p) * CentrePair.capacity (returnedPair N alpha L p) /
          CentrePair.capacity (stagePair N alpha L p) := by
  rw [stage_response N alpha L hp, mixed_moment N alpha L hp,
    stage_signed_moment, birth_moment N alpha L hp]

theorem old_capacity_pos (N : ℕ) (alpha L : ℝ) (p : ℕ) :
    0 < CentrePair.capacity (oldPair N alpha L p) := by
  change 0 < CentrePair.capacity (sectorPairOn (gaussianRootMass alpha L) (stageBefore p (N + 1)))
  rw [sector_capacity alpha L _ (fun _ hn => (mem_stageBefore.mp hn).2.2.1)]
  exact capacity_pos alpha L ⟨1, unit_mem_old N p⟩

theorem returned_nonnegative (N : ℕ) (alpha L : ℝ) (p : ℕ) :
    0 ≤ (returnedPair N alpha L p).positive ∧ 0 ≤ (returnedPair N alpha L p).negative :=
  sectorPairOn_nonnegative _ _ (fun n _ => (gaussianRootMass_pos alpha L (p * n)).le)

theorem joint_capacity_pos (N : ℕ) (alpha L : ℝ) (p : ℕ) :
    0 < CentrePair.capacity (oldPair N alpha L p) + CentrePair.capacity (returnedPair N alpha L p) :=
  add_pos_of_pos_of_nonneg (old_capacity_pos N alpha L p)
    (CentrePair.capacity_nonneg _ (returned_nonnegative N alpha L p).1
      (returned_nonnegative N alpha L p).2)

theorem mixed_response_factorized (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    stageResponse N alpha L p nativeProbe (birthMark N p) =
      -(CentrePair.capacity (oldPair N alpha L p) * CentrePair.signed (returnedPair N alpha L p) +
        CentrePair.signed (oldPair N alpha L p) * CentrePair.capacity (returnedPair N alpha L p)) /
      (CentrePair.capacity (oldPair N alpha L p) + CentrePair.capacity (returnedPair N alpha L p)) := by
  rw [mixed_response N alpha L hp, stage_eq_oppositeMix N alpha L hp,
    CentrePair.capacity_oppositeMix, CentrePair.signed_oppositeMix]
  field_simp [(joint_capacity_pos N alpha L p).ne']
  ring

theorem birth_response_factorized (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    stageResponse N alpha L p (birthMark N p) (birthMark N p) =
      CentrePair.capacity (oldPair N alpha L p) * CentrePair.capacity (returnedPair N alpha L p) /
      (CentrePair.capacity (oldPair N alpha L p) + CentrePair.capacity (returnedPair N alpha L p)) := by
  rw [birth_response N alpha L hp, stage_eq_oppositeMix N alpha L hp,
    CentrePair.capacity_oppositeMix]
  field_simp [(joint_capacity_pos N alpha L p).ne']
  ring

/-- The actual Schur square is precisely the already generated
opposite-center mixing loss. The empty birth is included with value zero. -/
theorem mixed_square_eq_mixing (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    stageResponse N alpha L p nativeProbe (birthMark N p) ^ 2 /
        stageResponse N alpha L p (birthMark N p) (birthMark N p) =
      CentrePair.mixingDissipation (oldPair N alpha L p) (returnedPair N alpha L p) := by
  rw [mixed_response_factorized N alpha L hp, birth_response_factorized N alpha L hp]
  by_cases hR : CentrePair.capacity (returnedPair N alpha L p) = 0
  · have hB := CapacityEnergyLedger.signed_eq_zero_of_capacity_eq_zero _
      (returned_nonnegative N alpha L p).1 (returned_nonnegative N alpha L p).2 hR
    simp [hR, hB, CentrePair.mixingDissipation]
  · unfold CentrePair.mixingDissipation CentrePair.bias
    field_simp [(old_capacity_pos N alpha L p).ne', hR, (joint_capacity_pos N alpha L p).ne']
    ring

theorem stageResponse_eq_form (N : ℕ) (alpha L : ℝ) (p : ℕ) (f g : ℕ → ℝ) :
    stageResponse N alpha L p f g = GibbsTraceForm.Z (logIntensity N alpha L) *
      HistoryPrefixResponseReduction.form N alpha L
        (centeredObservation N alpha L (stageAfter p (N + 1)) f)
        (centeredObservation N alpha L (stageAfter p (N + 1)) g) := by
  rw [HistoryPrefixResponseReduction.form_hessian]
  rfl

/-- Orthogonal birth elimination in the original full Hessian. The
removed response is retained as the exact native mixing square. -/
theorem prime_birth_schur_identity (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    GibbsTraceForm.Z (logIntensity N alpha L) *
      HistoryPrefixResponseReduction.form N alpha L
        (HistoryPrefixResponseReduction.residual alpha L
          (centeredObservation N alpha L (stageAfter p (N + 1)) nativeProbe)
          (centeredObservation N alpha L (stageAfter p (N + 1)) (birthMark N p)))
        (HistoryPrefixResponseReduction.residual alpha L
          (centeredObservation N alpha L (stageAfter p (N + 1)) nativeProbe)
          (centeredObservation N alpha L (stageAfter p (N + 1)) (birthMark N p))) +
      CentrePair.mixingDissipation (oldPair N alpha L p) (returnedPair N alpha L p) =
      stageResponse N alpha L p nativeProbe nativeProbe := by
  let K := centeredObservation N alpha L (stageAfter p (N + 1)) nativeProbe
  let J := centeredObservation N alpha L (stageAfter p (N + 1)) (birthMark N p)
  have hs := HistoryPrefixResponseReduction.schur_identity alpha L K J
  have hz := GibbsTraceForm.Z_ne_zero (logIntensity N alpha L)
  have he : (GibbsTraceForm.Z (logIntensity N alpha L) *
      HistoryPrefixResponseReduction.form N alpha L K J) ^ 2 /
      (GibbsTraceForm.Z (logIntensity N alpha L) * HistoryPrefixResponseReduction.form N alpha L J J) =
      GibbsTraceForm.Z (logIntensity N alpha L) *
        (HistoryPrefixResponseReduction.form N alpha L K J ^ 2 /
          HistoryPrefixResponseReduction.form N alpha L J J) := by
    by_cases hJ : HistoryPrefixResponseReduction.form N alpha L J J = 0
    · simp [hJ]
    · field_simp [hz, hJ]
  rw [← mixed_square_eq_mixing N alpha L hp,
    stageResponse_eq_form, stageResponse_eq_form, stageResponse_eq_form]
  change _ + (GibbsTraceForm.Z (logIntensity N alpha L) *
    HistoryPrefixResponseReduction.form N alpha L K J) ^ 2 /
      (GibbsTraceForm.Z (logIntensity N alpha L) * HistoryPrefixResponseReduction.form N alpha L J J) = _
  rw [he, ← mul_add, ← hs]

/-- The full conditional fluctuation is the old fluctuation, the true
returned fluctuation, and their positive between-birth mixing square. -/
theorem restored_stage_response_ledger (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    stageResponse N alpha L p nativeProbe nativeProbe =
      CapacityEnergyLedger.transverseCapacity (oldPair N alpha L p) +
        CapacityEnergyLedger.transverseCapacity (returnedPair N alpha L p) +
        CentrePair.mixingDissipation (oldPair N alpha L p) (returnedPair N alpha L p) := by
  rw [centre_response N alpha L hp]
  change CapacityEnergyLedger.transverseCapacity (stagePair N alpha L p) = _
  rw [stage_eq_oppositeMix N alpha L hp]
  apply CapacityRestoredWindowBudget.CentrePair.transverse_mixing_identity
  · exact (sectorPairOn_nonnegative _ _ (fun n _ => (gaussianRootMass_pos alpha L n).le)).1
  · exact (sectorPairOn_nonnegative _ _ (fun n _ => (gaussianRootMass_pos alpha L n).le)).2
  · exact (sectorPairOn_nonnegative _ _ (fun n _ => (gaussianRootMass_pos alpha L (p * n)).le)).1
  · exact (sectorPairOn_nonnegative _ _ (fun n _ => (gaussianRootMass_pos alpha L (p * n)).le)).2

theorem prime_birth_reduced_response (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    GibbsTraceForm.Z (logIntensity N alpha L) *
      HistoryPrefixResponseReduction.form N alpha L
        (HistoryPrefixResponseReduction.residual alpha L
          (centeredObservation N alpha L (stageAfter p (N + 1)) nativeProbe)
          (centeredObservation N alpha L (stageAfter p (N + 1)) (birthMark N p)))
        (HistoryPrefixResponseReduction.residual alpha L
          (centeredObservation N alpha L (stageAfter p (N + 1)) nativeProbe)
          (centeredObservation N alpha L (stageAfter p (N + 1)) (birthMark N p))) =
      CapacityEnergyLedger.transverseCapacity (oldPair N alpha L p) +
        CapacityEnergyLedger.transverseCapacity (returnedPair N alpha L p) := by
  have hs := prime_birth_schur_identity N alpha L hp
  rw [restored_stage_response_ledger N alpha L hp] at hs
  linarith

theorem gaussian_mass_prime_mul (alpha L : ℝ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    gaussianRootMass alpha L (p * n) = gaussianRootMass alpha (L / (p : ℝ)) n := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  by_cases hL : L = 0
  · simp [gaussianRootMass, hL]
  · unfold gaussianRootMass
    congr 1
    push_cast
    field_simp [hL, hpR]

theorem gaussian_return_scale (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    returnedPair N alpha L p = pairedPair (gaussianRootMass alpha (L / (p : ℝ))) p (N + 1) := by
  have he : (fun n => gaussianRootMass alpha L (p * n)) = gaussianRootMass alpha (L / (p : ℝ)) :=
    funext (gaussian_mass_prime_mul alpha L hp)
  change sectorPairOn (fun n => gaussianRootMass alpha L (p * n)) _ = _
  rw [he]
  rfl

theorem old_boundary_retained (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    oldPair N alpha L p = CentrePair.add (pairedPair (gaussianRootMass alpha L) p (N + 1))
      (cutoffBoundaryPair (gaussianRootMass alpha L) p (N + 1)) :=
  beforePair_eq_add _ hp.pos

def birthBlock (N p : ℕ) (i : Index N) : Bool := by
  classical
  exact decide (i.1.val + 1 ∈ stageBirth p (N + 1))

/-- Arbitrary history--phase and cross-root entries stay in the full state.
The false block includes both the old stage and every unresolved root. -/
theorem full_matrix_response (N : ℕ) (alpha L : ℝ) (p : ℕ) (K : Hermitian (Index N)) :
    HistoryPrefixResponseReduction.form N alpha L K K =
      HistoryPrefixResponseReduction.form N alpha L
        (GibbsBlockResponse.block (birthBlock N p) K) (GibbsBlockResponse.block (birthBlock N p) K) +
      HistoryPrefixResponseReduction.form N alpha L
        (GibbsBlockResponse.off (birthBlock N p) K) (GibbsBlockResponse.off (birthBlock N p) K) :=
  GibbsBlockResponse.response_decomposition (logIntensity N alpha L) (birthBlock N p) K

theorem unresolved_capacity_retained (N : ℕ) (alpha L : ℝ) {p : ℕ} (hp : p.Prime) :
    CentrePair.capacity (stagePair N alpha L p) +
        capacity alpha L (SignedGaussianEnergy.rootRange (N + 1) \ stageAfter p (N + 1)) =
      GibbsTraceForm.Z (logIntensity N alpha L) := by
  rw [← stage_capacity N alpha L hp]
  exact complete_capacity_partition N alpha L _ (stage_subset N hp)

structure Conclusions : Prop where
  actual_mixed_response : ∀ (N : ℕ) (alpha L : ℝ) {p : ℕ}, p.Prime →
    stageResponse N alpha L p nativeProbe (birthMark N p) =
      -CentrePair.signed (returnedPair N alpha L p) -
        CentrePair.signed (stagePair N alpha L p) * CentrePair.capacity (returnedPair N alpha L p) /
          CentrePair.capacity (stagePair N alpha L p)
  actual_schur_square : ∀ (N : ℕ) (alpha L : ℝ) {p : ℕ}, p.Prime →
    stageResponse N alpha L p nativeProbe (birthMark N p) ^ 2 /
        stageResponse N alpha L p (birthMark N p) (birthMark N p) =
      CentrePair.mixingDissipation (oldPair N alpha L p) (returnedPair N alpha L p)
  actual_restored_response : ∀ (N : ℕ) (alpha L : ℝ) {p : ℕ}, p.Prime →
    stageResponse N alpha L p nativeProbe nativeProbe =
      CapacityEnergyLedger.transverseCapacity (oldPair N alpha L p) +
        CapacityEnergyLedger.transverseCapacity (returnedPair N alpha L p) +
        CentrePair.mixingDissipation (oldPair N alpha L p) (returnedPair N alpha L p)
  actual_gaussian_return : ∀ (N : ℕ) (alpha L : ℝ) {p : ℕ}, p.Prime →
    returnedPair N alpha L p = pairedPair (gaussianRootMass alpha (L / (p : ℝ))) p (N + 1)
  complete_matrix_response : ∀ (N : ℕ) (alpha L : ℝ) (p : ℕ) (K : Hermitian (Index N)),
    HistoryPrefixResponseReduction.form N alpha L K K =
      HistoryPrefixResponseReduction.form N alpha L
        (GibbsBlockResponse.block (birthBlock N p) K) (GibbsBlockResponse.block (birthBlock N p) K) +
      HistoryPrefixResponseReduction.form N alpha L
        (GibbsBlockResponse.off (birthBlock N p) K) (GibbsBlockResponse.off (birthBlock N p) K)

theorem generated : Conclusions where
  actual_mixed_response := mixed_response
  actual_schur_square := mixed_square_eq_mixing
  actual_restored_response := restored_stage_response_ledger
  actual_gaussian_return := gaussian_return_scale
  complete_matrix_response := full_matrix_response

end GeneratedFoundations.Analysis.HistoryPrefixPrimeStageResponse
