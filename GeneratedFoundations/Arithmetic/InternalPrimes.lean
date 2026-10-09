module

public import GeneratedFoundations.Arithmetic.InternalEuclid
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Tactic.Push

/-!
# Irreducibility and unique factorization of native modes

Irreducibility refers to composition of the actual circle maps. Euclid's
divisor property follows from the native Bézout certificate. Factorizations
are constructed by descent in the native order and are unique up to
permutation, or strictly unique as multisets. No natural-number primality
or factorization theorem is used.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.NativeModes

def NativeIrreducible (p : Mode) : Prop :=
  p ≠ 0 ∧ p ≠ 1 ∧ ∀ a b : Mode, p = a * b → a = 1 ∨ b = 1

theorem native_one_le {x : Mode} (hx : x ≠ 0) : 1 ≤ x := by
  change index 1 ≤ index x
  rw [index_one]
  exact Nat.pos_of_ne_zero ((index_eq_zero_iff x).not.mpr hx)

theorem native_one_lt {x : Mode} (hx : x ≠ 0) (hx1 : x ≠ 1) : 1 < x :=
  lt_of_le_of_ne (native_one_le hx) (Ne.symm hx1)

theorem native_dvd_one_iff {x : Mode} : x ∣ 1 ↔ x = 1 := by
  constructor
  · intro hx
    exact native_dvd_antisymm hx (one_dvd x)
  · rintro rfl
    exact dvd_refl _

theorem native_irreducible_divisor {p d : Mode} (hp : NativeIrreducible p)
    (hd : d ∣ p) : d = 1 ∨ d = p := by
  obtain ⟨q, hq⟩ := hd
  rcases hp.2.2 d q hq with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [h] using hq.symm)

theorem native_irreducible_dvd_eq {p q : Mode}
    (hp : NativeIrreducible p) (hq : NativeIrreducible q) (h : p ∣ q) : p = q := by
  rcases native_irreducible_divisor hq h with h1 | heq
  · exact (hp.2.1 h1).elim
  · exact heq

/-- The positive-part Bézout equality suffices for Euclid's lemma in the
original semiring. The difference-ring interpretation is not needed here. -/
theorem native_euclid {p u v : Mode} (hp : NativeIrreducible p)
    (hprod : p ∣ u * v) : p ∣ u ∨ p ∣ v := by
  by_cases hpu : p ∣ u
  · exact Or.inl hpu
  · right
    obtain ⟨g, hg, a, b, c, d, hbez⟩ := native_gcd_bezout p u
    have hg1 : g = 1 := by
      rcases native_irreducible_divisor hp hg.1 with h1 | hgp
      · exact h1
      · exact (hpu (hgp ▸ hg.2.1)).elim
    subst g
    have hcv : p ∣ c * p * v := ⟨c * v, by ring⟩
    have hav : p ∣ a * p * v := ⟨a * v, by ring⟩
    have hdv : p ∣ d * (u * v) := by
      simpa only [mul_comm (u * v) d] using native_dvd_mul_right hprod d
    have hbv : p ∣ b * (u * v) := by
      simpa only [mul_comm (u * v) b] using native_dvd_mul_right hprod b
    have heq : v + (c * p * v + d * (u * v)) = a * p * v + b * (u * v) := by
      calc
        _ = (1 + c * p + d * u) * v := by ring
        _ = (a * p + b * u) * v := congrArg (fun w : Mode => w * v) hbez
        _ = _ := by ring
    apply native_dvd_of_dvd_add (native_dvd_add hcv hdv)
    rw [add_comm, heq]
    exact native_dvd_add hav hbv

theorem native_factorization_exists {x : Mode} (hx : x ≠ 0) :
    ∃ l : List Mode, (∀ p ∈ l, NativeIrreducible p) ∧ l.prod = x := by
  classical
  have hrec : ∀ n : ℕ, ∀ x : Mode, index x = n → x ≠ 0 →
      ∃ l : List Mode, (∀ p ∈ l, NativeIrreducible p) ∧ l.prod = x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hindex hx0
      by_cases hx1 : x = 1
      · exact ⟨[], by simp, by simpa using hx1.symm⟩
      by_cases hp : NativeIrreducible x
      · exact ⟨[x], by simpa using hp, by simp⟩
      have hf : ∃ a b : Mode, x = a * b ∧ a ≠ 1 ∧ b ≠ 1 := by
        have hnot : ¬∀ a b : Mode, x = a * b → a = 1 ∨ b = 1 :=
          fun h => hp ⟨hx0, hx1, h⟩
        push Not at hnot
        exact hnot
      obtain ⟨a, b, hab, ha1, hb1⟩ := hf
      have ha0 : a ≠ 0 := by
        intro h
        exact hx0 (by simp [hab, h])
      have hb0 : b ≠ 0 := by
        intro h
        exact hx0 (by simp [hab, h])
      have hax : a < x := by
        simpa [hab] using (native_mul_strictMono ha0) (native_one_lt hb0 hb1)
      have hbx : b < x := by
        simpa [hab, mul_comm] using (native_mul_strictMono hb0) (native_one_lt ha0 ha1)
      obtain ⟨la, hla, hpa⟩ := ih (index a) (hindex ▸ hax) a rfl ha0
      obtain ⟨lb, hlb, hpb⟩ := ih (index b) (hindex ▸ hbx) b rfl hb0
      refine ⟨la ++ lb, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with h | h
        · exact hla p h
        · exact hlb p h
      · simp [List.prod_append, hpa, hpb, hab]
  exact hrec (index x) x rfl hx

theorem native_irreducible_dvd_prod {p : Mode} (hp : NativeIrreducible p)
    {l : List Mode} (h : p ∣ l.prod) : ∃ q ∈ l, p ∣ q := by
  induction l with
  | nil => exact (hp.2.1 (native_dvd_one_iff.mp h)).elim
  | cons q l ih =>
    rcases native_euclid hp h with hq | hl
    · exact ⟨q, by simp, hq⟩
    · obtain ⟨r, hr, hpr⟩ := ih hl
      exact ⟨r, List.mem_cons_of_mem _ hr, hpr⟩

theorem native_factorization_unique {l k : List Mode}
    (hl : ∀ p ∈ l, NativeIrreducible p)
    (hk : ∀ p ∈ k, NativeIrreducible p) (hprod : l.prod = k.prod) : l.Perm k := by
  classical
  induction l generalizing k with
  | nil =>
    cases k with
    | nil => exact List.Perm.refl _
    | cons p k =>
      have hp := hk p (by simp)
      have hd : p ∣ (1 : Mode) := ⟨k.prod, hprod⟩
      exact (hp.2.1 (native_dvd_one_iff.mp hd)).elim
  | cons p l ih =>
    have hp := hl p (by simp)
    have hd : p ∣ k.prod := ⟨l.prod, hprod.symm⟩
    obtain ⟨q, hq, hpq⟩ := native_irreducible_dvd_prod hp hd
    have hpqeq : p = q := native_irreducible_dvd_eq hp (hk q hq) hpq
    have hmem : p ∈ k := hpqeq ▸ hq
    have hperm : k.Perm (p :: k.erase p) := List.perm_cons_erase hmem
    have htail : l.prod = (k.erase p).prod := by
      apply native_mul_cancel_left hp.1
      exact hprod.trans hperm.prod_eq
    have hi := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      (fun q hq => hk q (List.mem_of_mem_erase hq)) htail
    exact (hi.cons p).trans hperm.symm

/-- A factor multiset records exactly the finite prime multiplicities;
permutations of the list do not create distinct factorizations. -/
theorem native_factor_multiset_existsUnique {x : Mode} (hx : x ≠ 0) :
    ∃! s : Multiset Mode, (∀ p ∈ s, NativeIrreducible p) ∧ s.prod = x := by
  obtain ⟨l, hl, hprod⟩ := native_factorization_exists hx
  refine ⟨(l : Multiset Mode), ⟨by simpa using hl, hprod⟩, ?_⟩
  intro s hs
  have hperm : s.toList.Perm l := native_factorization_unique
    (fun p hp => hs.1 p (Multiset.mem_toList.mp hp)) hl
    (by rw [Multiset.prod_toList, hs.2, hprod])
  have hcoe := Multiset.coe_eq_coe.mpr hperm
  simpa only [Multiset.coe_toList] using hcoe

theorem native_exponent_profile_existsUnique {x : Mode} (hx : x ≠ 0) :
    ∃! f : Mode →₀ ℕ, (∀ p ∈ f.support, NativeIrreducible p) ∧
      f.prod (fun p n => p ^ n) = x := by
  classical
  obtain ⟨s, hs, hunique⟩ := native_factor_multiset_existsUnique hx
  refine ⟨s.toFinsupp, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    exact hs.1 p (by simpa only [Multiset.toFinsupp_support, Multiset.mem_toFinset] using hp)
  · rw [← Finsupp.prod_toMultiset, Multiset.toFinsupp_toMultiset, hs.2]
  · intro f hf
    have heq : f.toMultiset = s := hunique f.toMultiset
      ⟨fun p hp => hf.1 p ((Finsupp.mem_toMultiset f p).mp hp),
        by simpa only [Finsupp.prod_toMultiset] using hf.2⟩
    simpa only [Finsupp.toMultiset_toFinsupp] using congrArg Multiset.toFinsupp heq

theorem native_irreducible_product_ne_zero {l : List Mode}
    (hl : ∀ p ∈ l, NativeIrreducible p) : l.prod ≠ 0 := by
  induction l with
  | nil =>
    intro h
    have hi := congrArg index h
    norm_num at hi
  | cons p l ih =>
    exact native_mul_ne_zero (hl p (by simp)).1
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem native_prime_outside_list (l : List Mode)
    (hl : ∀ p ∈ l, NativeIrreducible p) :
    ∃ p : Mode, NativeIrreducible p ∧ p ∉ l := by
  classical
  have hprod := native_irreducible_product_ne_zero hl
  have hnext1 : successor l.prod ≠ 1 := by
    intro h
    apply hprod
    apply successor_injective
    simpa [successor] using h
  obtain ⟨k, hk, hkp⟩ := native_factorization_exists (successor_ne_zero l.prod)
  cases k with
  | nil => exact (hnext1 hkp.symm).elim
  | cons p k =>
    have hp := hk p (by simp)
    refine ⟨p, hp, ?_⟩
    intro hmem
    have hpdiv : p ∣ l.prod := ⟨(l.erase p).prod, (List.prod_erase hmem).symm⟩
    have hpnext : p ∣ l.prod + 1 := ⟨k.prod, hkp.symm⟩
    exact hp.2.1 (native_dvd_one_iff.mp (native_dvd_of_dvd_add hpdiv hpnext))

theorem native_irreducibles_infinite : Set.Infinite {p : Mode | NativeIrreducible p} := by
  classical
  intro hf
  let l := hf.toFinset.toList
  have hl : ∀ p ∈ l, NativeIrreducible p := by
    intro p hp
    simpa only [l, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hp
  obtain ⟨p, hp, hnot⟩ := native_prime_outside_list l hl
  apply hnot
  simpa only [l, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hp

end GeneratedFoundations.Arithmetic.NativeModes
