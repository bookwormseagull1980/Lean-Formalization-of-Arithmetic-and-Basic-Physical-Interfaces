module

public import GeneratedFoundations.Analysis.NaturalCutoffPrimeDescent
public import GeneratedFoundations.Analysis.CenterEndpointPotential

/-!
# Maximum-prime-factor generation stages

`NaturalCutoffPrimeDescent` gives an exact decomposition of a complete natural
prefix along an arbitrary prime direction.  That operation is not yet a
generation stage: its unoccupied sector may contain labels with prime factors
larger than the selected prime.

This module adds the missing stage condition.  Before a prime `p` is opened,
every occupied prime direction is strictly below `p`.  The old state then
splits into a paired interior and a cutoff boundary, while the genuine birth
source is the `p`-image of the paired interior.  The last part records the
exact central-potential ledger.  No estimate and no external source is used.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace GeneratedFoundations.Analysis.MaximumPrimeFactorStage

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Analysis.GeneratedMobiusObservation
open GeneratedFoundations.Analysis.NaturalCutoffPrimeDescent
open GeneratedFoundations.Analysis.CenterEndpointPotential
open GeneratedFoundations.Analysis.SignedGaussianEnergy
open GeneratedFoundations.Analysis.CanonicalMobiusReadout
open GeneratedFoundations.Arithmetic.JointOccupationScale

private theorem centrePair_ext {x y : CentrePair}
    (hpos : x.positive = y.positive) (hneg : x.negative = y.negative) : x = y := by
  cases x
  cases y
  simp_all

/-- Every prime direction occupied by `n` is strictly below `p`. -/
def factorsBelow (p n : ℕ) : Prop :=
  ∀ q ∈ n.primeFactors, q < p

/-- The squarefree natural-prefix state immediately before the prime `p` is
opened. -/
def stageBefore (p N : ℕ) : Finset ℕ := by
  classical
  exact (rootRange N).filter fun n => Squarefree n ∧ factorsBelow p n

/-- Old labels whose `p`-image remains inside the same natural cutoff. -/
def stagePairedBase (p N : ℕ) : Finset ℕ := stageBefore p (N / p)

/-- Old labels whose `p`-image lies beyond the natural cutoff.  This is an
endpoint remainder of the old state, not a newly born source. -/
def stageCutoffBoundary (p N : ℕ) : Finset ℕ :=
  (stageBefore p N).filter fun n => N / p < n

/-- The genuine new labels born when the prime direction `p` is opened. -/
def stageBirth (p N : ℕ) : Finset ℕ :=
  (stagePairedBase p N).image fun n => p * n

/-- The state after the `p` stage, defined from the actual generated update. -/
def stageAfter (p N : ℕ) : Finset ℕ :=
  stageBefore p N ∪ stageBirth p N

theorem mem_stageBefore {p N n : ℕ} :
    n ∈ stageBefore p N ↔
      1 ≤ n ∧ n ≤ N ∧ Squarefree n ∧ factorsBelow p n := by
  classical
  simp [stageBefore, rootRange, and_assoc]

theorem mem_stagePairedBase {p N n : ℕ} :
    n ∈ stagePairedBase p N ↔
      1 ≤ n ∧ n ≤ N / p ∧ Squarefree n ∧ factorsBelow p n := by
  simp [stagePairedBase, mem_stageBefore]

theorem mem_stageCutoffBoundary {p N n : ℕ} :
    n ∈ stageCutoffBoundary p N ↔
      1 ≤ n ∧ n ≤ N ∧ Squarefree n ∧ factorsBelow p n ∧ N / p < n := by
  simp [stageCutoffBoundary, mem_stageBefore, and_assoc]

/-- The pre-stage state is exactly the paired interior plus its cutoff
boundary. -/
theorem stageBefore_eq_union (p N : ℕ) (_hp : 0 < p) :
    stageBefore p N =
      stagePairedBase p N ∪ stageCutoffBoundary p N := by
  ext n
  simp only [mem_stageBefore, Finset.mem_union, mem_stagePairedBase,
    mem_stageCutoffBoundary]
  constructor
  · rintro ⟨hn1, hnN, hsq, hfac⟩
    by_cases hsmall : n ≤ N / p
    · exact Or.inl ⟨hn1, hsmall, hsq, hfac⟩
    · exact Or.inr ⟨hn1, hnN, hsq, hfac, Nat.lt_of_not_ge hsmall⟩
  · rintro (h | h)
    · exact ⟨h.1, le_trans h.2.1 (Nat.div_le_self N p), h.2.2.1,
        h.2.2.2⟩
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem disjoint_stagePairedBase_cutoffBoundary (p N : ℕ) :
    Disjoint (stagePairedBase p N) (stageCutoffBoundary p N) := by
  rw [Finset.disjoint_left]
  intro n hnpaired hnboundary
  have hp := mem_stagePairedBase.mp hnpaired
  have hb := mem_stageCutoffBoundary.mp hnboundary
  omega

theorem mem_stageBirth {p N n : ℕ} :
    n ∈ stageBirth p N ↔
      ∃ m ∈ stagePairedBase p N, p * m = n := by
  simp [stageBirth]

/-- A label present before the prime `p` is opened cannot already contain
that prime direction. -/
theorem stagePairedBase_not_dvd {p N m : ℕ} (hp : p.Prime)
    (hm : m ∈ stagePairedBase p N) : ¬p ∣ m := by
  intro hpm
  have hmdata := mem_stagePairedBase.mp hm
  have hm0 : m ≠ 0 := by omega
  have hmem : p ∈ m.primeFactors := hp.mem_primeFactors hpm hm0
  exact (Nat.lt_irrefl p) (hmdata.2.2.2 p hmem)

/-- The generated centre character reverses on every genuine maximum-prime
birth. -/
theorem generatedMoebius_stage_mul {p N m : ℕ} (hp : p.Prime)
    (hm : m ∈ stagePairedBase p N) :
    generatedMoebius (p * m) = -generatedMoebius m :=
  generatedMoebius_prime_mul hp (stagePairedBase_not_dvd hp hm)

/-- A genuine birth is not already present before its largest prime direction
is opened. -/
theorem disjoint_stageBefore_stageBirth {p N : ℕ} (hp : p.Prime) :
    Disjoint (stageBefore p N) (stageBirth p N) := by
  rw [Finset.disjoint_left]
  intro n hnold hnbirth
  obtain ⟨m, hm, rfl⟩ := mem_stageBirth.mp hnbirth
  have hold := mem_stageBefore.mp hnold
  have hmdata := mem_stagePairedBase.mp hm
  have hm0 : m ≠ 0 := by omega
  have hpm0 : p * m ≠ 0 := mul_ne_zero hp.ne_zero hm0
  have hpmem : p ∈ (p * m).primeFactors :=
    hp.mem_primeFactors (dvd_mul_right p m) hpm0
  exact (Nat.lt_irrefl p) (hold.2.2.2 p hpmem)

/-- A positive source resolved into its two generated center sectors on an
arbitrary finite set of labels. -/
def sectorPairOn (w : ℕ → ℝ) (S : Finset ℕ) : CentrePair where
  positive := ∑ n ∈ S, if generatedMoebius n = 1 then w n else 0
  negative := ∑ n ∈ S, if generatedMoebius n = -1 then w n else 0

private theorem generatedMoebius_cases (n : ℕ) :
    generatedMoebius n = 0 ∨ generatedMoebius n = 1 ∨
      generatedMoebius n = -1 := by
  simpa only [generatedMoebius_eq_moebius] using
    ArithmeticFunction.moebius_eq_or n

theorem sectorPairOn_signed (w : ℕ → ℝ) (S : Finset ℕ) :
    CentrePair.signed (sectorPairOn w S) =
      ∑ n ∈ S, (generatedMoebius n : ℝ) * w n := by
  change (∑ n ∈ S, if generatedMoebius n = 1 then w n else 0) -
      (∑ n ∈ S, if generatedMoebius n = -1 then w n else 0) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rcases generatedMoebius_cases n with hn | hn | hn <;> simp [hn]

theorem sectorPairOn_union (w : ℕ → ℝ) {S T : Finset ℕ}
    (hdisj : Disjoint S T) :
    sectorPairOn w (S ∪ T) =
      CentrePair.add (sectorPairOn w S) (sectorPairOn w T) := by
  apply centrePair_ext <;>
    simp [sectorPairOn, CentrePair.add, Finset.sum_union hdisj]

theorem sectorPairOn_nonnegative (w : ℕ → ℝ) (S : Finset ℕ)
    (hw : ∀ n ∈ S, 0 ≤ w n) :
    0 ≤ (sectorPairOn w S).positive ∧
      0 ≤ (sectorPairOn w S).negative := by
  constructor <;>
    apply Finset.sum_nonneg <;>
    intro n hn <;>
    split <;> simp [hw n hn]

def pairedPair (w : ℕ → ℝ) (p N : ℕ) : CentrePair :=
  sectorPairOn w (stagePairedBase p N)

def cutoffBoundaryPair (w : ℕ → ℝ) (p N : ℕ) : CentrePair :=
  sectorPairOn w (stageCutoffBoundary p N)

def returnPair (w : ℕ → ℝ) (p N : ℕ) : CentrePair :=
  sectorPairOn (fun n => w (p * n)) (stagePairedBase p N)

/-- The center label reverses on the true birth source. -/
def birthPair (w : ℕ → ℝ) (p N : ℕ) : CentrePair :=
  CentrePair.swap (returnPair w p N)

def beforePair (w : ℕ → ℝ) (p N : ℕ) : CentrePair :=
  sectorPairOn w (stageBefore p N)

theorem beforePair_eq_add (w : ℕ → ℝ) {p N : ℕ} (hp : 0 < p) :
    beforePair w p N = CentrePair.add (pairedPair w p N)
      (cutoffBoundaryPair w p N) := by
  rw [beforePair, pairedPair, cutoffBoundaryPair, stageBefore_eq_union p N hp]
  exact sectorPairOn_union w (disjoint_stagePairedBase_cutoffBoundary p N)

theorem pairedPair_signed (w : ℕ → ℝ) (p N : ℕ) :
    CentrePair.signed (pairedPair w p N) =
      ∑ n ∈ stagePairedBase p N,
        (generatedMoebius n : ℝ) * w n :=
  sectorPairOn_signed w (stagePairedBase p N)

theorem cutoffBoundaryPair_signed (w : ℕ → ℝ) (p N : ℕ) :
    CentrePair.signed (cutoffBoundaryPair w p N) =
      ∑ n ∈ stageCutoffBoundary p N,
        (generatedMoebius n : ℝ) * w n :=
  sectorPairOn_signed w (stageCutoffBoundary p N)

theorem returnPair_signed (w : ℕ → ℝ) (p N : ℕ) :
    CentrePair.signed (returnPair w p N) =
      ∑ n ∈ stagePairedBase p N,
        (generatedMoebius n : ℝ) * w (p * n) :=
  sectorPairOn_signed (fun n => w (p * n)) (stagePairedBase p N)

@[simp] theorem birthPair_signed (w : ℕ → ℝ) (p N : ℕ) :
    CentrePair.signed (birthPair w p N) =
      -CentrePair.signed (returnPair w p N) := by
  simp [birthPair]

theorem beforePair_signed (w : ℕ → ℝ) {p N : ℕ} (hp : 0 < p) :
    CentrePair.signed (beforePair w p N) =
      CentrePair.signed (pairedPair w p N) +
        CentrePair.signed (cutoffBoundaryPair w p N) := by
  rw [beforePair_eq_add w hp]
  simp

/-- The formal centre flip is exactly the positive-sector resolution of the
actual birth set.  This is where primality, rather than an arbitrary integer
multiplier, enters the stage construction. -/
theorem sectorPairOn_stageBirth_eq_birthPair (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) :
    sectorPairOn w (stageBirth p N) = birthPair w p N := by
  apply centrePair_ext
  · change
      (∑ n ∈ stageBirth p N,
        if generatedMoebius n = 1 then w n else 0) =
      ∑ m ∈ stagePairedBase p N,
        if generatedMoebius m = -1 then w (p * m) else 0
    symm
    refine Finset.sum_bij (fun m _hm => p * m) ?_ ?_ ?_ ?_
    · intro m hm
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
    · intro n hn
      obtain ⟨m, hm, hmn⟩ := mem_stageBirth.mp hn
      exact ⟨m, hm, hmn⟩
    · intro m hm
      rw [generatedMoebius_stage_mul hp hm]
      by_cases hneg : generatedMoebius m = -1
      · simp [hneg]
      · have hnotpos : -generatedMoebius m ≠ 1 := by
          intro h
          apply hneg
          omega
        simp [hneg, hnotpos]
  · change
      (∑ n ∈ stageBirth p N,
        if generatedMoebius n = -1 then w n else 0) =
      ∑ m ∈ stagePairedBase p N,
        if generatedMoebius m = 1 then w (p * m) else 0
    symm
    refine Finset.sum_bij (fun m _hm => p * m) ?_ ?_ ?_ ?_
    · intro m hm
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
    · intro n hn
      obtain ⟨m, hm, hmn⟩ := mem_stageBirth.mp hn
      exact ⟨m, hm, hmn⟩
    · intro m hm
      rw [generatedMoebius_stage_mul hp hm]
      by_cases hpos : generatedMoebius m = 1
      · simp [hpos]
      · have hnotneg : -generatedMoebius m ≠ -1 := by
          intro h
          apply hpos
          omega
        simp [hpos, hnotneg]

/-- The signed readout after one genuine prime stage.  All three pieces are
still combined before any square is formed. -/
def afterStagePair (w : ℕ → ℝ) (p N : ℕ) : CentrePair :=
  CentrePair.add
    (CentrePair.oppositeMix (pairedPair w p N) (returnPair w p N))
    (cutoffBoundaryPair w p N)

/-- The constructed after-stage pair is the positive-sector resolution of
the actual generated set, not merely an algebraically convenient pair. -/
theorem sectorPairOn_stageAfter_eq_afterStagePair (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) :
    sectorPairOn w (stageAfter p N) = afterStagePair w p N := by
  calc
    sectorPairOn w (stageAfter p N) =
        CentrePair.add (beforePair w p N) (birthPair w p N) := by
      rw [stageAfter, sectorPairOn_union w
        (disjoint_stageBefore_stageBirth hp)]
      rw [beforePair, sectorPairOn_stageBirth_eq_birthPair w hp]
    _ = afterStagePair w p N := by
      rw [beforePair_eq_add w hp.pos]
      apply centrePair_ext <;>
        simp [afterStagePair, birthPair, CentrePair.oppositeMix,
          CentrePair.add, CentrePair.swap]
      <;> ring

theorem afterStagePair_signed (w : ℕ → ℝ) (p N : ℕ) :
    CentrePair.signed (afterStagePair w p N) =
      CentrePair.signed (pairedPair w p N) -
        CentrePair.signed (returnPair w p N) +
        CentrePair.signed (cutoffBoundaryPair w p N) := by
  simp [afterStagePair]

@[simp] theorem quadraticPotential_swap (x : CentrePair) :
    CentrePair.quadraticPotential (CentrePair.swap x) =
      CentrePair.quadraticPotential x := by
  simp [CentrePair.quadraticPotential]

private def zeroPair : CentrePair := ⟨0, 0⟩

private theorem eq_zeroPair_of_nonnegative_capacity_eq_zero
    (x : CentrePair) (hxpos : 0 ≤ x.positive) (hxneg : 0 ≤ x.negative)
    (hcap : CentrePair.capacity x = 0) : x = zeroPair := by
  apply centrePair_ext <;> simp only [zeroPair]
  · dsimp [CentrePair.capacity] at hcap
    linarith
  · dsimp [CentrePair.capacity] at hcap
    linarith

/-- The mixing identity with the empty-sector cases included.  This is the
form needed by a genuine generation history, whose cutoff boundary may be
empty. -/
theorem quadraticPotential_mixing_identity_nonnegative (x y : CentrePair)
    (hxpos : 0 ≤ x.positive) (hxneg : 0 ≤ x.negative)
    (hypos : 0 ≤ y.positive) (hyneg : 0 ≤ y.negative) :
    CentrePair.quadraticPotential x + CentrePair.quadraticPotential y -
        CentrePair.quadraticPotential (CentrePair.oppositeMix x y) =
      CentrePair.mixingDissipation x y := by
  have hxc : 0 ≤ CentrePair.capacity x :=
    CentrePair.capacity_nonneg x hxpos hxneg
  have hyc : 0 ≤ CentrePair.capacity y :=
    CentrePair.capacity_nonneg y hypos hyneg
  by_cases hx0 : CentrePair.capacity x = 0
  · rw [eq_zeroPair_of_nonnegative_capacity_eq_zero x hxpos hxneg hx0]
    have hswap := sub_eq_zero.mpr (quadraticPotential_swap y).symm
    simpa [zeroPair, CentrePair.quadraticPotential,
      CentrePair.mixingDissipation, CentrePair.bias,
      CentrePair.capacity, CentrePair.signed, CentrePair.oppositeMix,
      CentrePair.add, CentrePair.swap] using hswap
  · by_cases hy0 : CentrePair.capacity y = 0
    · rw [eq_zeroPair_of_nonnegative_capacity_eq_zero y hypos hyneg hy0]
      simp [zeroPair, CentrePair.quadraticPotential,
        CentrePair.mixingDissipation, CentrePair.bias,
        CentrePair.capacity, CentrePair.signed, CentrePair.oppositeMix,
        CentrePair.add, CentrePair.swap]
    · have hxpos' : 0 < CentrePair.capacity x :=
        lt_of_le_of_ne hxc (Ne.symm hx0)
      have hypos' : 0 < CentrePair.capacity y :=
        lt_of_le_of_ne hyc (Ne.symm hy0)
      exact CentrePair.quadraticPotential_mixing_identity x y hx0 hy0
        (ne_of_gt (add_pos hxpos' hypos'))

/-- Zero-capacity-safe ordinary joining identity. -/
theorem quadraticPotential_join_identity_nonnegative (x y : CentrePair)
    (hxpos : 0 ≤ x.positive) (hxneg : 0 ≤ x.negative)
    (hypos : 0 ≤ y.positive) (hyneg : 0 ≤ y.negative) :
    CentrePair.quadraticPotential x + CentrePair.quadraticPotential y -
        CentrePair.quadraticPotential (CentrePair.add x y) =
      CentrePair.joinDissipation x y := by
  have hxc : 0 ≤ CentrePair.capacity x :=
    CentrePair.capacity_nonneg x hxpos hxneg
  have hyc : 0 ≤ CentrePair.capacity y :=
    CentrePair.capacity_nonneg y hypos hyneg
  by_cases hx0 : CentrePair.capacity x = 0
  · rw [eq_zeroPair_of_nonnegative_capacity_eq_zero x hxpos hxneg hx0]
    simp [zeroPair, CentrePair.quadraticPotential,
      CentrePair.joinDissipation, CentrePair.bias,
      CentrePair.capacity, CentrePair.signed, CentrePair.add]
  · by_cases hy0 : CentrePair.capacity y = 0
    · rw [eq_zeroPair_of_nonnegative_capacity_eq_zero y hypos hyneg hy0]
      simp [zeroPair, CentrePair.quadraticPotential,
        CentrePair.joinDissipation, CentrePair.bias,
        CentrePair.capacity, CentrePair.signed, CentrePair.add]
    · have hxpos' : 0 < CentrePair.capacity x :=
        lt_of_le_of_ne hxc (Ne.symm hx0)
      have hypos' : 0 < CentrePair.capacity y :=
        lt_of_le_of_ne hyc (Ne.symm hy0)
      exact CentrePair.quadraticPotential_join_identity x y hx0 hy0
        (ne_of_gt (add_pos hxpos' hypos'))

/-- The complete stage ledger for nonnegative sources, including empty
paired, returned or boundary sectors. -/
theorem stage_birth_mixing_endpoint_ledger_nonnegative (x y rho : CentrePair)
    (hxpos : 0 ≤ x.positive) (hxneg : 0 ≤ x.negative)
    (hypos : 0 ≤ y.positive) (hyneg : 0 ≤ y.negative)
    (hrpos : 0 ≤ rho.positive) (hrneg : 0 ≤ rho.negative) :
    CentrePair.quadraticPotential
          (CentrePair.add (CentrePair.oppositeMix x y) rho) -
        CentrePair.quadraticPotential (CentrePair.add x rho) =
      CentrePair.quadraticPotential y -
        CentrePair.mixingDissipation x y +
        CentrePair.joinDissipation x rho -
        CentrePair.joinDissipation (CentrePair.oppositeMix x y) rho := by
  have hmix := quadraticPotential_mixing_identity_nonnegative x y
    hxpos hxneg hypos hyneg
  have hold := quadraticPotential_join_identity_nonnegative x rho
    hxpos hxneg hrpos hrneg
  have hmixpos : 0 ≤ (CentrePair.oppositeMix x y).positive := by
    simp [CentrePair.oppositeMix, CentrePair.add, CentrePair.swap]
    positivity
  have hmixneg : 0 ≤ (CentrePair.oppositeMix x y).negative := by
    simp [CentrePair.oppositeMix, CentrePair.add, CentrePair.swap]
    positivity
  have hnew := quadraticPotential_join_identity_nonnegative
    (CentrePair.oppositeMix x y) rho hmixpos hmixneg hrpos hrneg
  linarith

/-- Exact potential increment when the true birth source is added to the old
state. -/
theorem stage_quadratic_increment (old returned : CentrePair)
    (hold : CentrePair.capacity old ≠ 0)
    (hreturned : CentrePair.capacity returned ≠ 0)
    (hnext : CentrePair.capacity old + CentrePair.capacity returned ≠ 0) :
    CentrePair.quadraticPotential
          (CentrePair.add old (CentrePair.swap returned)) -
        CentrePair.quadraticPotential old =
      CentrePair.quadraticPotential returned -
        CentrePair.joinDissipation old (CentrePair.swap returned) := by
  have hswap : CentrePair.capacity (CentrePair.swap returned) ≠ 0 := by
    simpa using hreturned
  have hjoin := CentrePair.quadraticPotential_join_identity old
    (CentrePair.swap returned) hold hswap (by simpa using hnext)
  rw [quadraticPotential_swap] at hjoin
  linarith

/-- Scalar form of the complete-stage increment.  It isolates the only term
whose sign is not fixed by positivity: the signed correlation of the old
state with its returned source. -/
theorem stage_quadratic_increment_correlation (old returned : CentrePair)
    (hold : CentrePair.capacity old ≠ 0)
    (hreturned : CentrePair.capacity returned ≠ 0)
    (hnext : CentrePair.capacity old + CentrePair.capacity returned ≠ 0) :
    CentrePair.quadraticPotential
          (CentrePair.add old (CentrePair.swap returned)) -
        CentrePair.quadraticPotential old =
      CentrePair.capacity returned /
          (CentrePair.capacity old + CentrePair.capacity returned) *
        (CentrePair.quadraticPotential returned -
          CentrePair.quadraticPotential old) -
      2 * CentrePair.signed old * CentrePair.signed returned /
        (CentrePair.capacity old + CentrePair.capacity returned) := by
  simp only [CentrePair.quadraticPotential, CentrePair.capacity_add,
    CentrePair.signed_add, CentrePair.capacity_swap, CentrePair.signed_swap]
  field_simp [hold, hreturned, hnext]
  ring

/-- The finite birth--mixing--endpoint identity.  `x` is the paired old
interior, `y` its returned copy before the center flip, and `rho` is the old
cutoff boundary.  The birth self-potential, paired mixing loss, and endpoint
return are combined before any estimate is taken. -/
theorem stage_birth_mixing_endpoint_ledger (x y rho : CentrePair)
    (hx : CentrePair.capacity x ≠ 0)
    (hy : CentrePair.capacity y ≠ 0)
    (hxy : CentrePair.capacity x + CentrePair.capacity y ≠ 0)
    (hrho : CentrePair.capacity rho ≠ 0)
    (hxr : CentrePair.capacity x + CentrePair.capacity rho ≠ 0)
    (hnext : CentrePair.capacity x + CentrePair.capacity y +
      CentrePair.capacity rho ≠ 0) :
    CentrePair.quadraticPotential
          (CentrePair.add (CentrePair.oppositeMix x y) rho) -
        CentrePair.quadraticPotential (CentrePair.add x rho) =
      CentrePair.quadraticPotential y -
        CentrePair.mixingDissipation x y +
        CentrePair.joinDissipation x rho -
        CentrePair.joinDissipation (CentrePair.oppositeMix x y) rho := by
  have hmix := CentrePair.quadraticPotential_mixing_identity x y hx hy hxy
  have hold := CentrePair.quadraticPotential_join_identity x rho hx hrho hxr
  have hmixed : CentrePair.capacity (CentrePair.oppositeMix x y) ≠ 0 := by
    simpa using hxy
  have hmixedrho :
      CentrePair.capacity (CentrePair.oppositeMix x y) +
          CentrePair.capacity rho ≠ 0 := by
    simpa [add_assoc] using hnext
  have hnew := CentrePair.quadraticPotential_join_identity
    (CentrePair.oppositeMix x y) rho hmixed hrho hmixedrho
  linarith

/-- The abstract ledger evaluated on the actual maximum-prime-factor stage. -/
theorem generated_stage_potential_ledger (w : ℕ → ℝ) {p N : ℕ}
    (hx : CentrePair.capacity (pairedPair w p N) ≠ 0)
    (hy : CentrePair.capacity (returnPair w p N) ≠ 0)
    (hxy : CentrePair.capacity (pairedPair w p N) +
      CentrePair.capacity (returnPair w p N) ≠ 0)
    (hrho : CentrePair.capacity (cutoffBoundaryPair w p N) ≠ 0)
    (hxr : CentrePair.capacity (pairedPair w p N) +
      CentrePair.capacity (cutoffBoundaryPair w p N) ≠ 0)
    (hnext : CentrePair.capacity (pairedPair w p N) +
      CentrePair.capacity (returnPair w p N) +
      CentrePair.capacity (cutoffBoundaryPair w p N) ≠ 0) :
    CentrePair.quadraticPotential (afterStagePair w p N) -
        CentrePair.quadraticPotential
          (CentrePair.add (pairedPair w p N) (cutoffBoundaryPair w p N)) =
      CentrePair.quadraticPotential (returnPair w p N) -
        CentrePair.mixingDissipation
          (pairedPair w p N) (returnPair w p N) +
        CentrePair.joinDissipation
          (pairedPair w p N) (cutoffBoundaryPair w p N) -
        CentrePair.joinDissipation
          (CentrePair.oppositeMix (pairedPair w p N) (returnPair w p N))
          (cutoffBoundaryPair w p N) := by
  exact stage_birth_mixing_endpoint_ledger
    (pairedPair w p N) (returnPair w p N) (cutoffBoundaryPair w p N)
    hx hy hxy hrho hxr hnext

/-- The actual maximum-prime-factor update, with empty sectors allowed.  The
new state is joined to the complete old state before the potential is read;
this compact identity therefore already contains the endpoint cross terms. -/
theorem generated_stage_complete_join_ledger (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) (hw : ∀ n, 0 ≤ w n) :
    CentrePair.quadraticPotential (sectorPairOn w (stageAfter p N)) -
        CentrePair.quadraticPotential (sectorPairOn w (stageBefore p N)) =
      CentrePair.quadraticPotential (returnPair w p N) -
        CentrePair.joinDissipation
          (sectorPairOn w (stageBefore p N)) (birthPair w p N) := by
  have hold := sectorPairOn_nonnegative w (stageBefore p N)
    (fun n _hn => hw n)
  have hreturn := sectorPairOn_nonnegative (fun n => w (p * n))
    (stagePairedBase p N) (fun n _hn => hw (p * n))
  have hbirth :
      0 ≤ (birthPair w p N).positive ∧ 0 ≤ (birthPair w p N).negative := by
    constructor
    · simpa only [birthPair, CentrePair.swap, returnPair] using hreturn.2
    · simpa only [birthPair, CentrePair.swap, returnPair] using hreturn.1
  have hjoin := quadraticPotential_join_identity_nonnegative
    (sectorPairOn w (stageBefore p N)) (birthPair w p N)
    hold.1 hold.2 hbirth.1 hbirth.2
  have hafter :
      sectorPairOn w (stageAfter p N) =
        CentrePair.add (sectorPairOn w (stageBefore p N))
          (birthPair w p N) := by
    rw [stageAfter, sectorPairOn_union w
      (disjoint_stageBefore_stageBirth hp)]
    rw [sectorPairOn_stageBirth_eq_birthPair w hp]
  have hbirthpot :
      CentrePair.quadraticPotential (birthPair w p N) =
        CentrePair.quadraticPotential (returnPair w p N) := by
    simp [birthPair]
  rw [hbirthpot] at hjoin
  rw [hafter]
  linarith

/-- Expanded zero-capacity-safe form of the same actual stage. -/
theorem generated_stage_potential_ledger_nonnegative (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) (hw : ∀ n, 0 ≤ w n) :
    CentrePair.quadraticPotential (sectorPairOn w (stageAfter p N)) -
        CentrePair.quadraticPotential (sectorPairOn w (stageBefore p N)) =
      CentrePair.quadraticPotential (returnPair w p N) -
        CentrePair.mixingDissipation
          (pairedPair w p N) (returnPair w p N) +
        CentrePair.joinDissipation
          (pairedPair w p N) (cutoffBoundaryPair w p N) -
        CentrePair.joinDissipation
          (CentrePair.oppositeMix (pairedPair w p N) (returnPair w p N))
          (cutoffBoundaryPair w p N) := by
  have hx := sectorPairOn_nonnegative w (stagePairedBase p N)
    (fun n _hn => hw n)
  have hy := sectorPairOn_nonnegative (fun n => w (p * n))
    (stagePairedBase p N) (fun n _hn => hw (p * n))
  have hr := sectorPairOn_nonnegative w (stageCutoffBoundary p N)
    (fun n _hn => hw n)
  have hledger := stage_birth_mixing_endpoint_ledger_nonnegative
    (pairedPair w p N) (returnPair w p N) (cutoffBoundaryPair w p N)
    hx.1 hx.2 hy.1 hy.2 hr.1 hr.2
  rw [sectorPairOn_stageAfter_eq_afterStagePair w hp]
  change CentrePair.quadraticPotential (afterStagePair w p N) -
    CentrePair.quadraticPotential (beforePair w p N) = _
  rw [beforePair_eq_add w hp.pos]
  exact hledger

/-- In the native Gaussian observation, the returned positive pair is exactly
the paired pair at the transported scale `L / p`. -/
theorem gaussian_returnPair_eq_scale_transport (L : PositiveScale)
    {p N : ℕ} (hp : p.Prime) :
    returnPair (gaussianWindowMass L.1) p N =
      pairedPair (gaussianWindowMass (L.1 / (p : ℝ))) p N := by
  apply centrePair_ext <;>
    simp only [returnPair, pairedPair, sectorPairOn]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [gaussianWindowMass_prime_mul L hp n]
  · apply Finset.sum_congr rfl
    intro n _hn
    rw [gaussianWindowMass_prime_mul L hp n]

/-- Algebraic nonempty-sector version of the Gaussian ledger.  The actual
prime-stage theorem, including empty boundaries, is stated below. -/
theorem gaussian_generated_stage_potential_ledger (L : PositiveScale)
    {p N : ℕ}
    (hx : CentrePair.capacity
      (pairedPair (gaussianWindowMass L.1) p N) ≠ 0)
    (hy : CentrePair.capacity
      (returnPair (gaussianWindowMass L.1) p N) ≠ 0)
    (hxy : CentrePair.capacity
        (pairedPair (gaussianWindowMass L.1) p N) +
      CentrePair.capacity
        (returnPair (gaussianWindowMass L.1) p N) ≠ 0)
    (hrho : CentrePair.capacity
      (cutoffBoundaryPair (gaussianWindowMass L.1) p N) ≠ 0)
    (hxr : CentrePair.capacity
        (pairedPair (gaussianWindowMass L.1) p N) +
      CentrePair.capacity
        (cutoffBoundaryPair (gaussianWindowMass L.1) p N) ≠ 0)
    (hnext : CentrePair.capacity
        (pairedPair (gaussianWindowMass L.1) p N) +
      CentrePair.capacity
        (returnPair (gaussianWindowMass L.1) p N) +
      CentrePair.capacity
        (cutoffBoundaryPair (gaussianWindowMass L.1) p N) ≠ 0) :
    CentrePair.quadraticPotential
          (afterStagePair (gaussianWindowMass L.1) p N) -
        CentrePair.quadraticPotential
          (CentrePair.add
            (pairedPair (gaussianWindowMass L.1) p N)
            (cutoffBoundaryPair (gaussianWindowMass L.1) p N)) =
      CentrePair.quadraticPotential
          (returnPair (gaussianWindowMass L.1) p N) -
        CentrePair.mixingDissipation
          (pairedPair (gaussianWindowMass L.1) p N)
          (returnPair (gaussianWindowMass L.1) p N) +
        CentrePair.joinDissipation
          (pairedPair (gaussianWindowMass L.1) p N)
          (cutoffBoundaryPair (gaussianWindowMass L.1) p N) -
        CentrePair.joinDissipation
          (CentrePair.oppositeMix
            (pairedPair (gaussianWindowMass L.1) p N)
            (returnPair (gaussianWindowMass L.1) p N))
          (cutoffBoundaryPair (gaussianWindowMass L.1) p N) := by
  exact generated_stage_potential_ledger (gaussianWindowMass L.1)
    hx hy hxy hrho hxr hnext

/-- The actual Gaussian stage ledger, including empty boundaries and the
unique scale return carried by a prime birth. -/
theorem gaussian_generated_stage_complete_join_ledger (L : PositiveScale)
    {p N : ℕ} (hp : p.Prime) :
    CentrePair.quadraticPotential
          (sectorPairOn (gaussianWindowMass L.1) (stageAfter p N)) -
        CentrePair.quadraticPotential
          (sectorPairOn (gaussianWindowMass L.1) (stageBefore p N)) =
      CentrePair.quadraticPotential
          (pairedPair (gaussianWindowMass (L.1 / (p : ℝ))) p N) -
        CentrePair.joinDissipation
          (sectorPairOn (gaussianWindowMass L.1) (stageBefore p N))
          (birthPair (gaussianWindowMass L.1) p N) := by
  have h := generated_stage_complete_join_ledger
    (gaussianWindowMass L.1) (N := N) hp (fun n => by
      change 0 ≤ endpointWeight L.1 n
      exact endpointWeight_nonneg L.1 n)
  rw [gaussian_returnPair_eq_scale_transport L hp] at h
  exact h

/-- Bundled finite-stage output.  It fixes the object that any subsequent
all-scale argument must accumulate; none of its fields assumes the desired
global estimate. -/
structure StageConclusions : Prop where
  stage_partition : ∀ p N, 0 < p →
    stageBefore p N =
      stagePairedBase p N ∪ stageCutoffBoundary p N
  true_birth_disjoint : ∀ {p N}, p.Prime →
    Disjoint (stageBefore p N) (stageBirth p N)
  source_additivity : ∀ (w : ℕ → ℝ) {S T : Finset ℕ},
    Disjoint S T →
      sectorPairOn w (S ∪ T) =
        CentrePair.add (sectorPairOn w S) (sectorPairOn w T)
  source_nonnegative : ∀ (w : ℕ → ℝ) (S : Finset ℕ),
    (∀ n ∈ S, 0 ≤ w n) →
      0 ≤ (sectorPairOn w S).positive ∧
        0 ≤ (sectorPairOn w S).negative
  old_state_split : ∀ (w : ℕ → ℝ) {p N}, 0 < p →
    beforePair w p N = CentrePair.add (pairedPair w p N)
      (cutoffBoundaryPair w p N)
  actual_birth_pair : ∀ (w : ℕ → ℝ) {p N}, p.Prime →
    sectorPairOn w (stageBirth p N) = birthPair w p N
  actual_after_pair : ∀ (w : ℕ → ℝ) {p N}, p.Prime →
    sectorPairOn w (stageAfter p N) = afterStagePair w p N
  complete_signed_stage : ∀ (w : ℕ → ℝ) {p N}, p.Prime →
    CentrePair.signed (sectorPairOn w (stageAfter p N)) =
      CentrePair.signed (pairedPair w p N) -
        CentrePair.signed (returnPair w p N) +
        CentrePair.signed (cutoffBoundaryPair w p N)
  gaussian_return : ∀ (L : PositiveScale) {p N}, p.Prime →
    returnPair (gaussianWindowMass L.1) p N =
      pairedPair (gaussianWindowMass (L.1 / (p : ℝ))) p N
  exact_stage_potential : ∀ (x y rho : CentrePair),
    0 ≤ x.positive → 0 ≤ x.negative →
    0 ≤ y.positive → 0 ≤ y.negative →
    0 ≤ rho.positive → 0 ≤ rho.negative →
    CentrePair.quadraticPotential
          (CentrePair.add (CentrePair.oppositeMix x y) rho) -
        CentrePair.quadraticPotential (CentrePair.add x rho) =
      CentrePair.quadraticPotential y -
        CentrePair.mixingDissipation x y +
        CentrePair.joinDissipation x rho -
        CentrePair.joinDissipation (CentrePair.oppositeMix x y) rho
  actual_stage_potential : ∀ (w : ℕ → ℝ) {p N}, p.Prime →
    (∀ n, 0 ≤ w n) →
    CentrePair.quadraticPotential (sectorPairOn w (stageAfter p N)) -
        CentrePair.quadraticPotential (sectorPairOn w (stageBefore p N)) =
      CentrePair.quadraticPotential (returnPair w p N) -
        CentrePair.joinDissipation
          (sectorPairOn w (stageBefore p N)) (birthPair w p N)
  gaussian_actual_stage : ∀ (L : PositiveScale) {p N}, p.Prime →
    CentrePair.quadraticPotential
          (sectorPairOn (gaussianWindowMass L.1) (stageAfter p N)) -
        CentrePair.quadraticPotential
          (sectorPairOn (gaussianWindowMass L.1) (stageBefore p N)) =
      CentrePair.quadraticPotential
          (pairedPair (gaussianWindowMass (L.1 / (p : ℝ))) p N) -
        CentrePair.joinDissipation
          (sectorPairOn (gaussianWindowMass L.1) (stageBefore p N))
          (birthPair (gaussianWindowMass L.1) p N)

theorem conclusions : StageConclusions where
  stage_partition := stageBefore_eq_union
  true_birth_disjoint := disjoint_stageBefore_stageBirth
  source_additivity := sectorPairOn_union
  source_nonnegative := sectorPairOn_nonnegative
  old_state_split := beforePair_eq_add
  actual_birth_pair := sectorPairOn_stageBirth_eq_birthPair
  actual_after_pair := sectorPairOn_stageAfter_eq_afterStagePair
  complete_signed_stage := fun w {_p _N} hp => by
    rw [sectorPairOn_stageAfter_eq_afterStagePair w hp]
    exact afterStagePair_signed w _ _
  gaussian_return := gaussian_returnPair_eq_scale_transport
  exact_stage_potential := stage_birth_mixing_endpoint_ledger_nonnegative
  actual_stage_potential := generated_stage_complete_join_ledger
  gaussian_actual_stage := gaussian_generated_stage_complete_join_ledger

end GeneratedFoundations.Analysis.MaximumPrimeFactorStage
