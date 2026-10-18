module

public import GeneratedFoundations.Arithmetic.JointOccupationScale
public import GeneratedFoundations.Analysis.SignedGaussianEnergy

/-!
# Canonical Mobius readout from the complete occupation source

The complete source consists of positive finite prime occupations together
with scale.  This file proves that its value map is a canonical coordinate on
the positive squarefree integers and that the derived center character is
exactly the already generated Mobius observation in that coordinate.  The
Gaussian response is transported along the same map.

No signed sequence is introduced as source data: the sign and the fixed-scale
window are both read from the complete positive occupation--scale state.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius

namespace GeneratedFoundations.Analysis.CanonicalMobiusReadout

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.JointOccupationScale
open GeneratedFoundations.Analysis.GeneratedMobiusObservation
open GeneratedFoundations.Analysis.SignedGaussianEnergy

/-- The ordinary prime values carried by a finite prime occupation. -/
def primeValues (nu : Occupation) : Finset ℕ :=
  nu.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem primeValues_card (nu : Occupation) :
    (primeValues nu).card = nu.card := by
  simp [primeValues]

theorem label_eq_primeValues_prod (nu : Occupation) :
    label nu = ∏ p ∈ primeValues nu, p := by
  simp [label, primeValues]

theorem primeValues_prime (nu : Occupation) :
    ∀ p ∈ primeValues nu, Nat.Prime p := by
  intro p hp
  simp only [primeValues, Finset.mem_map] at hp
  obtain ⟨q, _hq, rfl⟩ := hp
  exact q.2

/-- A finite occupation has a squarefree positive value. -/
theorem label_squarefree (nu : Occupation) : Squarefree (label nu) := by
  unfold label
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p _hp q _hq hpq => ?_) (fun p _hp => p.2.squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes p.2 q.2).2 fun hpqv =>
    hpq (Subtype.ext hpqv)

/-- The prime support of an occupation value is exactly the occupation. -/
theorem primeFactors_label (nu : Occupation) :
    (label nu).primeFactors = primeValues nu := by
  rw [label_eq_primeValues_prod]
  exact Nat.primeFactors_prod (primeValues_prime nu)

/-- The number of generated prime factors is the occupation number. -/
theorem cardFactors_label (nu : Occupation) :
    ArithmeticFunction.cardFactors (label nu) = nu.card := by
  have hnodup := (label_squarefree nu).nodup_primeFactorsList
  calc
    ArithmeticFunction.cardFactors (label nu) =
        (label nu).primeFactorsList.length := rfl
    _ = (label nu).primeFactors.card :=
      (List.toFinset_card_of_nodup hnodup).symm
    _ = (primeValues nu).card := congrArg Finset.card (primeFactors_label nu)
    _ = nu.card := primeValues_card nu

theorem centerCharacter_eq_neg_one_pow_card (nu : Occupation) :
    centerCharacter nu = (-1 : ℤ) ^ nu.card := by
  simp [centerCharacter]

/-- The generated Mobius observation is precisely the center readout of the
unique finite prime occupation with that value. -/
theorem generatedMoebius_label (nu : Occupation) :
    generatedMoebius (label nu) = centerCharacter nu := by
  rw [generatedMoebius_eq_moebius,
    ArithmeticFunction.moebius_apply_of_squarefree (label_squarefree nu),
    cardFactors_label, centerCharacter_eq_neg_one_pow_card]

/-- The value map does not identify distinct prime occupations. -/
theorem label_injective : Function.Injective label := by
  intro nu eta h
  have hsets : primeValues nu = primeValues eta := by
    rw [← primeFactors_label nu, ← primeFactors_label eta, h]
  ext p
  have hp := Finset.ext_iff.mp hsets p.1
  simpa [primeValues] using hp

/-- Positive squarefree labels, including the multiplicative unit. -/
abbrev SquarefreePositive := {n : ℕ // Squarefree n}

/-- The canonical label map into positive squarefree integers. -/
def toSquarefree (nu : Occupation) : SquarefreePositive :=
  ⟨label nu, label_squarefree nu⟩

/-- Embed the prime support of a squarefree value into the generated prime
occupation type. -/
def factorPrimeEmbedding (n : SquarefreePositive) :
    {p : ℕ // p ∈ n.1.primeFactors} ↪ PrimeIndex where
  toFun p := ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩
  inj' _ _ h := Subtype.ext (congrArg (fun r : PrimeIndex => r.1) h)

/-- Recover the complete prime occupation of a squarefree value. -/
def occupationOfSquarefree (n : SquarefreePositive) : Occupation :=
  n.1.primeFactors.attach.map (factorPrimeEmbedding n)

theorem label_occupationOfSquarefree (n : SquarefreePositive) :
    label (occupationOfSquarefree n) = n.1 := by
  rw [label, occupationOfSquarefree, Finset.prod_map]
  change (∏ p ∈ n.1.primeFactors.attach, p.1) = n.1
  calc
    (∏ p ∈ n.1.primeFactors.attach, p.1) =
        ∏ p ∈ n.1.primeFactors, p := by
          simpa using Finset.prod_attach n.1.primeFactors (fun p : ℕ => p)
    _ = n.1 := Nat.prod_primeFactors_of_squarefree n.2

theorem toSquarefree_bijective : Function.Bijective toSquarefree := by
  constructor
  · intro nu eta h
    apply label_injective
    exact congrArg Subtype.val h
  · intro n
    refine ⟨occupationOfSquarefree n, ?_⟩
    apply Subtype.ext
    exact label_occupationOfSquarefree n

/-- Finite prime occupations and positive squarefree generated values are
canonically equivalent. -/
def occupationSquarefreeEquiv : Occupation ≃ SquarefreePositive :=
  Equiv.ofBijective toSquarefree toSquarefree_bijective

/-- The native two-endpoint Gaussian window on a generated root. -/
def gaussianWindowMass (L : ℝ) (n : ℕ) : ℝ :=
  gaussianRootMass 1 L n - gaussianRootMass Real.pi L n

/-- The occupation--scale Gaussian is exactly the native square-spectrum
window after canonical descent to the root label. -/
theorem gaussianResponse_eq_window (nu : Occupation) (L : PositiveScale) :
    gaussianResponse (nu, L) = gaussianWindowMass L.1 (label nu) := by
  simp only [gaussianResponse, ratio, gaussianWindowMass, gaussianRootMass]
  have hL : L.1 ≠ 0 := ne_of_gt L.2
  congr 1 <;> field_simp

/-- The center-weighted joint response descends exactly to the generated
Mobius--Gaussian root response at every positive scale. -/
theorem centerGaussian_descends_to_Mobius (nu : Occupation)
    (L : PositiveScale) :
    (centerCharacter nu : ℝ) * gaussianResponse (nu, L) =
      (generatedMoebius (label nu) : ℝ) * gaussianWindowMass L.1 (label nu) := by
  rw [gaussianResponse_eq_window, generatedMoebius_label]

/-! ## Finite coherent readout -/

/-- The canonical occupation term over an arbitrary generated root.  On a
squarefree root the unique occupation is used; outside the squarefree support
the central readout is zero. -/
def canonicalOccupationTerm (L : PositiveScale) (n : ℕ) : ℝ :=
  if hn : Squarefree n then
    let nu := occupationSquarefreeEquiv.symm ⟨n, hn⟩
    (centerCharacter nu : ℝ) * gaussianResponse (nu, L)
  else
    0

/-- Each canonical occupation term is exactly the generated
Mobius--Gaussian term with no sign replacement. -/
theorem canonicalOccupationTerm_eq_Mobius (L : PositiveScale) (n : ℕ) :
    canonicalOccupationTerm L n =
      (generatedMoebius n : ℝ) * gaussianWindowMass L.1 n := by
  by_cases hn : Squarefree n
  · let x : SquarefreePositive := ⟨n, hn⟩
    let nu : Occupation := occupationSquarefreeEquiv.symm x
    have hcoord : occupationSquarefreeEquiv nu = x :=
      occupationSquarefreeEquiv.apply_symm_apply x
    have hlabel : label nu = n := congrArg Subtype.val hcoord
    simp only [canonicalOccupationTerm, hn, ↓reduceDIte]
    change (centerCharacter nu : ℝ) * gaussianResponse (nu, L) = _
    rw [centerGaussian_descends_to_Mobius, hlabel]
  · rw [canonicalOccupationTerm]
    simp only [hn, ↓reduceDIte]
    rw [generatedMoebius_eq_moebius,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    norm_num

/-- Finite coherent scalar readout of the complete positive occupation source.
The center signs are summed before squaring. -/
def canonicalOccupationAmplitude (L : PositiveScale) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, canonicalOccupationTerm L n

/-- The same finite response in the generated-root coordinate. -/
def rootMobiusWindowAmplitude (L : PositiveScale) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N,
    (generatedMoebius n : ℝ) * gaussianWindowMass L.1 n

/-- Canonical occupation descent preserves the complete signed amplitude. -/
theorem canonicalOccupationAmplitude_eq_root (L : PositiveScale) (N : ℕ) :
    canonicalOccupationAmplitude L N = rootMobiusWindowAmplitude L N := by
  apply Finset.sum_congr rfl
  intro n _hn
  exact canonicalOccupationTerm_eq_Mobius L n

/-- The coherent finite energy is formed only after all occupation channels
have been combined. -/
def canonicalOccupationEnergy (L : PositiveScale) (N : ℕ) : ℝ :=
  canonicalOccupationAmplitude L N ^ 2

/-- Root-coordinate form of the same coherent energy. -/
def rootMobiusWindowEnergy (L : PositiveScale) (N : ℕ) : ℝ :=
  rootMobiusWindowAmplitude L N ^ 2

/-- The canonical descent preserves the full coherent energy and therefore
all diagonal and off-diagonal cross terms. -/
theorem canonicalOccupationEnergy_eq_root (L : PositiveScale) (N : ℕ) :
    canonicalOccupationEnergy L N = rootMobiusWindowEnergy L N := by
  rw [canonicalOccupationEnergy, rootMobiusWindowEnergy,
    canonicalOccupationAmplitude_eq_root]

/-- The canonical occupation coordinate, center readout and Gaussian descent
form one exact object-level bridge. -/
structure Conclusions : Prop where
  occupation_coordinate : Function.Bijective toSquarefree
  center_descent : ∀ nu : Occupation,
    generatedMoebius (label nu) = centerCharacter nu
  gaussian_descent : ∀ (nu : Occupation) (L : PositiveScale),
    gaussianResponse (nu, L) = gaussianWindowMass L.1 (label nu)
  signed_descent : ∀ (nu : Occupation) (L : PositiveScale),
    (centerCharacter nu : ℝ) * gaussianResponse (nu, L) =
      (generatedMoebius (label nu) : ℝ) * gaussianWindowMass L.1 (label nu)
  coherent_amplitude : ∀ (L : PositiveScale) (N : ℕ),
    canonicalOccupationAmplitude L N = rootMobiusWindowAmplitude L N
  coherent_energy : ∀ (L : PositiveScale) (N : ℕ),
    canonicalOccupationEnergy L N = rootMobiusWindowEnergy L N

theorem canonicalMobiusReadoutConclusions : Conclusions where
  occupation_coordinate := toSquarefree_bijective
  center_descent := generatedMoebius_label
  gaussian_descent := gaussianResponse_eq_window
  signed_descent := centerGaussian_descends_to_Mobius
  coherent_amplitude := canonicalOccupationAmplitude_eq_root
  coherent_energy := canonicalOccupationEnergy_eq_root

end GeneratedFoundations.Analysis.CanonicalMobiusReadout
