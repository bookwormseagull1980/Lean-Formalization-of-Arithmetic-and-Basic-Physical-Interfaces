module

public import GeneratedFoundations.Analysis.CanonicalMobiusReadout

/-!
# Prime descent at the generated natural cutoff

A complete prime cylinder is useful for identifying the exact occupation--
scale symmetry, but it is not the initial segment of the generated natural
order.  This file performs the same prime flip on the legal cutoff `1 <= n <=
N`.  The result separates the already-born labels from the unique birth
boundary and retains the complete cross term after squaring.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace GeneratedFoundations.Analysis.NaturalCutoffPrimeDescent

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.JointOccupationScale
open GeneratedFoundations.Analysis.GeneratedMobiusObservation
open GeneratedFoundations.Analysis.SignedGaussianEnergy
open GeneratedFoundations.Analysis.CanonicalMobiusReadout

/-- Generated labels in the legal prefix which are squarefree and do not yet
occupy the prime direction `p`. -/
def unoccupiedPrefix (p N : ℕ) : Finset ℕ :=
  (rootRange N).filter fun n => Squarefree n ∧ ¬p ∣ n

/-- The already-born part of the unoccupied sector.  Its labels remain in the
prefix after insertion of `p`. -/
def pairedBase (p N : ℕ) : Finset ℕ := unoccupiedPrefix p (N / p)

/-- The only labels in the unoccupied sector which have no returned partner
inside the same natural cutoff. -/
def birthBoundary (p N : ℕ) : Finset ℕ :=
  (unoccupiedPrefix p N).filter fun n => N / p < n

/-- Squarefree labels in the legal prefix which already occupy `p`. -/
def occupiedPrefix (p N : ℕ) : Finset ℕ :=
  (rootRange N).filter fun n => Squarefree n ∧ p ∣ n

/-- A finite generated Mobius readout with an arbitrary real observation. -/
def cutoffAmplitude (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, (generatedMoebius n : ℝ) * f n

/-- The paired old/returned response.  The two terms share the same generated
coefficient and are combined before any estimate is taken. -/
def pairedResponse (f : ℕ → ℝ) (p N : ℕ) : ℝ :=
  ∑ n ∈ pairedBase p N,
    (generatedMoebius n : ℝ) * (f n - f (p * n))

/-- The genuine birth boundary left by the natural cutoff. -/
def boundaryResponse (f : ℕ → ℝ) (p N : ℕ) : ℝ :=
  ∑ n ∈ birthBoundary p N, (generatedMoebius n : ℝ) * f n

/-- Complete response of the sector in which `p` is still unoccupied. -/
def unoccupiedResponse (f : ℕ → ℝ) (p N : ℕ) : ℝ :=
  ∑ n ∈ unoccupiedPrefix p N, (generatedMoebius n : ℝ) * f n

theorem mem_unoccupiedPrefix {p N n : ℕ} :
    n ∈ unoccupiedPrefix p N ↔ 1 ≤ n ∧ n ≤ N ∧ Squarefree n ∧ ¬p ∣ n := by
  simp [unoccupiedPrefix, rootRange, and_assoc]

theorem mem_pairedBase {p N n : ℕ} :
    n ∈ pairedBase p N ↔
      1 ≤ n ∧ n ≤ N / p ∧ Squarefree n ∧ ¬p ∣ n := by
  simp [pairedBase, mem_unoccupiedPrefix]

theorem mem_birthBoundary {p N n : ℕ} :
    n ∈ birthBoundary p N ↔
      1 ≤ n ∧ n ≤ N ∧ Squarefree n ∧ ¬p ∣ n ∧ N / p < n := by
  simp [birthBoundary, mem_unoccupiedPrefix, and_assoc]

theorem mem_occupiedPrefix {p N n : ℕ} :
    n ∈ occupiedPrefix p N ↔
      1 ≤ n ∧ n ≤ N ∧ Squarefree n ∧ p ∣ n := by
  simp [occupiedPrefix, rootRange, and_assoc]

/-- Multiplication by a prime reverses the generated center character on the
unoccupied squarefree sector. -/
theorem generatedMoebius_prime_mul {p n : ℕ} (hp : p.Prime)
    (hpn : ¬p ∣ n) :
    generatedMoebius (p * n) = -generatedMoebius n := by
  have hcop : Nat.Coprime p n := hp.coprime_iff_not_dvd.mpr hpn
  simp only [generatedMoebius_eq_moebius]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- Non-squarefree labels contribute zero to every generated Mobius
observation. -/
theorem generatedMoebius_eq_zero_of_not_squarefree {n : ℕ}
    (hn : ¬Squarefree n) : generatedMoebius n = 0 := by
  rw [generatedMoebius_eq_moebius,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

/-- The legal unoccupied prefix is the disjoint union of the paired base and
the birth boundary. -/
theorem unoccupiedPrefix_eq_union (p N : ℕ) (hp : 0 < p) :
    unoccupiedPrefix p N = pairedBase p N ∪ birthBoundary p N := by
  ext n
  simp only [mem_unoccupiedPrefix, Finset.mem_union, mem_pairedBase,
    mem_birthBoundary]
  constructor
  · rintro ⟨hn1, hnN, hsq, hnp⟩
    by_cases hsmall : n ≤ N / p
    · exact Or.inl ⟨hn1, hsmall, hsq, hnp⟩
    · exact Or.inr ⟨hn1, hnN, hsq, hnp, Nat.lt_of_not_ge hsmall⟩
  · rintro (h | h)
    · exact ⟨h.1, le_trans h.2.1 (Nat.div_le_self N p), h.2.2.1, h.2.2.2⟩
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem disjoint_pairedBase_birthBoundary (p N : ℕ) :
    Disjoint (pairedBase p N) (birthBoundary p N) := by
  rw [Finset.disjoint_left]
  intro n hnpaired hnbirth
  have hp := mem_pairedBase.mp hnpaired
  have hb := mem_birthBoundary.mp hnbirth
  omega

/-- Removing non-squarefree labels and splitting by occupation of `p` loses
nothing: the omitted generated coefficients are exactly zero. -/
theorem cutoffAmplitude_eq_unoccupied_add_occupied
    (f : ℕ → ℝ) (p N : ℕ) :
    cutoffAmplitude f N =
      (∑ n ∈ unoccupiedPrefix p N,
        (generatedMoebius n : ℝ) * f n) +
      ∑ n ∈ occupiedPrefix p N,
        (generatedMoebius n : ℝ) * f n := by
  let g : ℕ → ℝ := fun n => (generatedMoebius n : ℝ) * f n
  have hsquarefree :
      cutoffAmplitude f N =
        ∑ n ∈ (rootRange N).filter Squarefree, g n := by
    unfold cutoffAmplitude
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hsq : Squarefree n
    · simp [hsq, g]
    · rw [if_neg hsq, generatedMoebius_eq_zero_of_not_squarefree hsq]
      simp [g]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((rootRange N).filter Squarefree) (fun n => p ∣ n) g
  rw [hsquarefree]
  simpa [unoccupiedPrefix, occupiedPrefix, g, Finset.filter_filter,
    and_comm, and_left_comm, and_assoc, add_comm] using hsplit.symm

/-- The occupied squarefree sector is exactly the prime image of the paired
base, and the center character reverses along this bijection. -/
theorem occupied_sum_eq_return (f : ℕ → ℝ) {p N : ℕ} (hp : p.Prime) :
    (∑ n ∈ occupiedPrefix p N,
      (generatedMoebius n : ℝ) * f n) =
      -∑ n ∈ pairedBase p N,
        (generatedMoebius n : ℝ) * f (p * n) := by
  have hbij :
      (∑ n ∈ pairedBase p N,
        -((generatedMoebius n : ℝ) * f (p * n))) =
        ∑ n ∈ occupiedPrefix p N,
          (generatedMoebius n : ℝ) * f n := by
    refine Finset.sum_bij (fun n _hn => p * n) ?_ ?_ ?_ ?_
    · intro n hn
      have h := mem_pairedBase.mp hn
      have hmulpos : 0 < p * n := Nat.mul_pos hp.pos (by omega)
      apply mem_occupiedPrefix.mpr
      refine ⟨by omega, ?_, ?_, dvd_mul_right p n⟩
      · simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hp.pos).mp h.2.1
      exact (Nat.squarefree_mul (hp.coprime_iff_not_dvd.mpr h.2.2.2)).2
        ⟨hp.squarefree, h.2.2.1⟩
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
    · intro n hn
      have h := mem_occupiedPrefix.mp hn
      let m := n / p
      have hpm : p * m = n := Nat.mul_div_cancel' h.2.2.2
      have hcop : Nat.Coprime p m := by
        apply Nat.coprime_of_squarefree_mul
        rw [hpm]
        exact h.2.2.1
      have hmnot : ¬p ∣ m := hp.coprime_iff_not_dvd.mp hcop
      have hmpos : 1 ≤ m := by
        have hnpos : 0 < n := by omega
        rw [← hpm] at hnpos
        exact Nat.one_le_iff_ne_zero.mpr fun hmzero => by simp [hmzero] at hnpos
      have hmle : m ≤ N / p := by
        apply (Nat.le_div_iff_mul_le hp.pos).2
        calc
          m * p = n := by simpa [Nat.mul_comm] using hpm
          _ ≤ N := h.2.1
      have hmsq : Squarefree m := by
        have hsqpm : Squarefree (p * m) := by rw [hpm]; exact h.2.2.1
        exact (Nat.squarefree_mul hcop).1 hsqpm |>.2
      refine ⟨m, mem_pairedBase.mpr ⟨hmpos, hmle, hmsq, hmnot⟩, hpm⟩
    · intro n hn
      rw [generatedMoebius_prime_mul hp (mem_pairedBase.mp hn).2.2.2]
      push_cast
      ring
  rw [← hbij, Finset.sum_neg_distrib]

/-- Exact descent at the generated natural prefix.  Every already-born label
is paired with its true prime return; the only remainder is the actual birth
boundary of the cutoff. -/
theorem cutoffAmplitude_descent (f : ℕ → ℝ) {p N : ℕ} (hp : p.Prime) :
    cutoffAmplitude f N =
      pairedResponse f p N + boundaryResponse f p N := by
  rw [cutoffAmplitude_eq_unoccupied_add_occupied f p N,
    unoccupiedPrefix_eq_union p N hp.pos,
    Finset.sum_union (disjoint_pairedBase_birthBoundary p N),
    occupied_sum_eq_return f hp]
  unfold pairedResponse boundaryResponse
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Equivalent unsplit form of the legal prime update.  It has no artificial
remainder: the full unoccupied prefix at `N` is compared with the same sector
returned through multiplication by `p` at cutoff `N / p`. -/
theorem cutoffAmplitude_eq_unoccupied_difference
    (f : ℕ → ℝ) {p N : ℕ} (hp : p.Prime) :
    cutoffAmplitude f N =
      unoccupiedResponse f p N -
        unoccupiedResponse (fun n => f (p * n)) p (N / p) := by
  rw [cutoffAmplitude_eq_unoccupied_add_occupied f p N,
    occupied_sum_eq_return f hp]
  rfl

/-- The coherent energy of the unsplit legal update, with its true cross term. -/
theorem cutoffEnergy_eq_unoccupied_difference
    (f : ℕ → ℝ) {p N : ℕ} (hp : p.Prime) :
    cutoffAmplitude f N ^ 2 =
      unoccupiedResponse f p N ^ 2 +
      unoccupiedResponse (fun n => f (p * n)) p (N / p) ^ 2 -
      2 * unoccupiedResponse f p N *
        unoccupiedResponse (fun n => f (p * n)) p (N / p) := by
  rw [cutoffAmplitude_eq_unoccupied_difference f hp]
  ring

/-- The exact coherent-energy ledger for the legal natural cutoff. -/
theorem cutoffEnergy_descent (f : ℕ → ℝ) {p N : ℕ} (hp : p.Prime) :
    cutoffAmplitude f N ^ 2 =
      pairedResponse f p N ^ 2 + boundaryResponse f p N ^ 2 +
        2 * pairedResponse f p N * boundaryResponse f p N := by
  rw [cutoffAmplitude_descent f hp]
  ring

/-- The native Gaussian endpoint window transports multiplication by `p`
exactly into division of the observation scale by `p`. -/
theorem gaussianWindowMass_prime_mul (L : PositiveScale) {p : ℕ}
    (hp : p.Prime) (n : ℕ) :
    gaussianWindowMass L.1 (p * n) =
      gaussianWindowMass (L.1 / (p : ℝ)) n := by
  unfold gaussianWindowMass gaussianRootMass
  have hL : L.1 ≠ 0 := ne_of_gt L.2
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  congr 1 <;> congr 1 <;> push_cast <;> field_simp [hL, hpR] <;> ring

/-- Exact natural-cutoff descent specialized to the two native Gaussian
endpoints.  The interior is a same-source scale difference; only the legal
birth boundary remains outside that transport. -/
theorem gaussianCutoffAmplitude_descent (L : PositiveScale) {p N : ℕ}
    (hp : p.Prime) :
    cutoffAmplitude (gaussianWindowMass L.1) N =
      (∑ n ∈ pairedBase p N,
        (generatedMoebius n : ℝ) *
          (gaussianWindowMass L.1 n -
            gaussianWindowMass (L.1 / (p : ℝ)) n)) +
      boundaryResponse (gaussianWindowMass L.1) p N := by
  rw [cutoffAmplitude_descent (gaussianWindowMass L.1) hp]
  congr 1
  unfold pairedResponse
  apply Finset.sum_congr rfl
  intro n _hn
  rw [gaussianWindowMass_prime_mul L hp n]

/-- Unsplit generated Gaussian recursion.  Prime occupation is precisely a
translation in scale, while the cutoff follows the generated natural order. -/
theorem gaussianCutoffAmplitude_eq_scale_difference
    (L : PositiveScale) {p N : ℕ} (hp : p.Prime) :
    cutoffAmplitude (gaussianWindowMass L.1) N =
      unoccupiedResponse (gaussianWindowMass L.1) p N -
      unoccupiedResponse (gaussianWindowMass (L.1 / (p : ℝ))) p (N / p) := by
  rw [cutoffAmplitude_eq_unoccupied_difference (gaussianWindowMass L.1) hp]
  congr 1
  unfold unoccupiedResponse
  apply Finset.sum_congr rfl
  intro n _hn
  change (generatedMoebius n : ℝ) * gaussianWindowMass L.1 (p * n) = _
  rw [gaussianWindowMass_prime_mul L hp n]

/-- The corresponding coherent Gaussian energy, with the boundary interaction
retained exactly. -/
theorem gaussianCutoffEnergy_descent (L : PositiveScale) {p N : ℕ}
    (hp : p.Prime) :
    cutoffAmplitude (gaussianWindowMass L.1) N ^ 2 =
      pairedResponse (gaussianWindowMass L.1) p N ^ 2 +
      boundaryResponse (gaussianWindowMass L.1) p N ^ 2 +
      2 * pairedResponse (gaussianWindowMass L.1) p N *
        boundaryResponse (gaussianWindowMass L.1) p N :=
  cutoffEnergy_descent (gaussianWindowMass L.1) hp

/-- The exact prime descent available at every legal generated prefix. -/
structure Conclusions : Prop where
  center_flip : ∀ {p n : ℕ}, p.Prime → ¬p ∣ n →
    generatedMoebius (p * n) = -generatedMoebius n
  prefix_partition : ∀ p N, 0 < p →
    unoccupiedPrefix p N = pairedBase p N ∪ birthBoundary p N
  amplitude_ledger : ∀ (f : ℕ → ℝ) {p N : ℕ}, p.Prime →
    cutoffAmplitude f N = pairedResponse f p N + boundaryResponse f p N
  unsplit_amplitude_ledger : ∀ (f : ℕ → ℝ) {p N : ℕ}, p.Prime →
    cutoffAmplitude f N =
      unoccupiedResponse f p N -
        unoccupiedResponse (fun n => f (p * n)) p (N / p)
  coherent_energy_ledger : ∀ (f : ℕ → ℝ) {p N : ℕ}, p.Prime →
    cutoffAmplitude f N ^ 2 =
      pairedResponse f p N ^ 2 + boundaryResponse f p N ^ 2 +
        2 * pairedResponse f p N * boundaryResponse f p N
  gaussian_scale_transport : ∀ (L : PositiveScale) {p : ℕ}, p.Prime → ∀ n,
    gaussianWindowMass L.1 (p * n) =
      gaussianWindowMass (L.1 / (p : ℝ)) n
  gaussian_amplitude_ledger : ∀ (L : PositiveScale) {p N : ℕ}, p.Prime →
    cutoffAmplitude (gaussianWindowMass L.1) N =
      (∑ n ∈ pairedBase p N,
        (generatedMoebius n : ℝ) *
          (gaussianWindowMass L.1 n -
            gaussianWindowMass (L.1 / (p : ℝ)) n)) +
      boundaryResponse (gaussianWindowMass L.1) p N
  gaussian_unsplit_ledger : ∀ (L : PositiveScale) {p N : ℕ}, p.Prime →
    cutoffAmplitude (gaussianWindowMass L.1) N =
      unoccupiedResponse (gaussianWindowMass L.1) p N -
      unoccupiedResponse (gaussianWindowMass (L.1 / (p : ℝ))) p (N / p)

theorem conclusions : Conclusions where
  center_flip := fun hp hpn => generatedMoebius_prime_mul hp hpn
  prefix_partition := unoccupiedPrefix_eq_union
  amplitude_ledger := fun f {_p _N} hp => cutoffAmplitude_descent f hp
  unsplit_amplitude_ledger := fun f {_p _N} hp =>
    cutoffAmplitude_eq_unoccupied_difference f hp
  coherent_energy_ledger := fun f {_p _N} hp => cutoffEnergy_descent f hp
  gaussian_scale_transport := fun L {_p} hp n =>
    gaussianWindowMass_prime_mul L hp n
  gaussian_amplitude_ledger := fun L {_p _N} hp =>
    gaussianCutoffAmplitude_descent L hp
  gaussian_unsplit_ledger := fun L {_p _N} hp =>
    gaussianCutoffAmplitude_eq_scale_difference L hp

/-- Squaring the exact natural-cutoff ledger retains the complete interaction
between the paired interior and the birth boundary. -/
theorem energy_of_amplitude_descent (f : ℕ → ℝ) (p N : ℕ)
    (hdescent : cutoffAmplitude f N =
      pairedResponse f p N + boundaryResponse f p N) :
    cutoffAmplitude f N ^ 2 =
      pairedResponse f p N ^ 2 + boundaryResponse f p N ^ 2 +
        2 * pairedResponse f p N * boundaryResponse f p N := by
  rw [hdescent]
  ring

end GeneratedFoundations.Analysis.NaturalCutoffPrimeDescent
