module

public import GeneratedFoundations.Arithmetic.GeneratedModes
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Prime exponent profiles under source-mode transport

Prime multiplicities are indexed by the actual lifted source modes. Their
transport changes the scale of each source mode and leaves its exponent
unchanged. The equality of the transported and target profiles follows from
the internal unique factorization theorem and preservation of composition.
No natural-number factorization or degree coding is used to construct the
profiles or their transport.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.GeneratedFactorTransport

open GeneratedModes

variable (L : ℝ) [Fact (0 < L)]

/-- A finite multiplicity profile whose composition is the specified source mode. -/
def IsPrimeProfile (x : SourceMode L) (f : SourceMode L →₀ ℕ) : Prop :=
  (∀ p ∈ f.support, SourceIrreducible L p) ∧ f.prod (fun p n => p ^ n) = x

/-- The unique profile supplied by internal factorization on the source family. -/
def primeProfile (x : SourceMode L) (hx : x ≠ 0) : SourceMode L →₀ ℕ :=
  Classical.choose (exponentProfile_existsUnique L hx).exists

theorem primeProfile_spec (x : SourceMode L) (hx : x ≠ 0) :
    IsPrimeProfile L x (primeProfile L x hx) :=
  Classical.choose_spec (exponentProfile_existsUnique L hx).exists

theorem primeProfile_unique {x : SourceMode L} (hx : x ≠ 0)
    (f : SourceMode L →₀ ℕ) (hf : IsPrimeProfile L x f) :
    f = primeProfile L x hx :=
  (exponentProfile_existsUnique L hx).unique hf (primeProfile_spec L x hx)

theorem primeProfile_proof_irrel (x : SourceMode L) (hx hx' : x ≠ 0) :
    primeProfile L x hx = primeProfile L x hx' := rfl

/-- Infinitude is inherited from the internal Euclidean argument on the same maps. -/
theorem sourceIrreducibles_infinite :
    Set.Infinite {p : SourceMode L | SourceIrreducible L p} := by
  refine Set.infinite_of_injOn_mapsTo (f := fromNative L) ?_ ?_
    NativeModes.native_irreducibles_infinite
  · intro p hp q hq hpq
    simpa only [toNative_fromNative] using congrArg (toNative L) hpq
  · intro p hp
    apply (sourceIrreducible_iff L (fromNative L p)).mpr
    change NativeModes.NativeIrreducible p at hp
    simpa only [toNative_fromNative] using hp

variable (M : ℝ) [Fact (0 < M)]

/-- Reindex by the source-map transport, without replacing a source mode by its degree. -/
def transportProfile : (SourceMode L →₀ ℕ) ≃+ (SourceMode M →₀ ℕ) :=
  Finsupp.domCongr (transport L M).toEquiv

theorem transportProfile_apply_symm (f : SourceMode L →₀ ℕ) (q : SourceMode M) :
    transportProfile L M f q = f ((transport L M).symm q) := rfl

@[simp] theorem transportProfile_apply (f : SourceMode L →₀ ℕ) (p : SourceMode L) :
    transportProfile L M f (transport L M p) = f p := by
  change f ((transport L M).symm (transport L M p)) = f p
  rw [RingEquiv.symm_apply_apply]

theorem transportProfile_support (f : SourceMode L →₀ ℕ) :
    (transportProfile L M f).support =
      f.support.map (transport L M).toEquiv.toEmbedding := rfl

theorem mem_transportProfile_support (f : SourceMode L →₀ ℕ) (p : SourceMode L) :
    transport L M p ∈ (transportProfile L M f).support ↔ p ∈ f.support := by
  simp only [Finsupp.mem_support_iff, transportProfile_apply]

/-- Finite multiplication commutes with the actual semiring transport. -/
theorem transportProfile_prod (f : SourceMode L →₀ ℕ) :
    (transportProfile L M f).prod (fun p n => p ^ n) =
      transport L M (f.prod (fun p n => p ^ n)) := by
  change (Finsupp.equivMapDomain (transport L M).toEquiv f).prod (fun p n => p ^ n) = _
  rw [Finsupp.prod_equivMapDomain, map_finsuppProd]
  apply Finsupp.prod_congr
  intro p hp
  exact (map_pow (transport L M) p (f p)).symm

theorem transportProfile_spec {x : SourceMode L} {f : SourceMode L →₀ ℕ}
    (hf : IsPrimeProfile L x f) :
    IsPrimeProfile M (transport L M x) (transportProfile L M f) := by
  constructor
  · intro q hq
    obtain ⟨p, rfl⟩ := (transport L M).surjective q
    apply (transport_irreducible_iff L M p).mpr
    exact hf.1 p ((mem_transportProfile_support L M f p).mp hq)
  · rw [transportProfile_prod, hf.2]

theorem transport_ne_zero {x : SourceMode L} (hx : x ≠ 0) : transport L M x ≠ 0 := by
  intro h
  apply hx
  apply (transport L M).injective
  simpa only [map_zero] using h

/-- The target profile is the transported source profile by unique factorization. -/
theorem primeProfile_transport (x : SourceMode L) (hx : x ≠ 0) :
    primeProfile M (transport L M x) (transport_ne_zero L M hx) =
      transportProfile L M (primeProfile L x hx) := by
  symm
  apply primeProfile_unique M (transport_ne_zero L M hx)
  exact transportProfile_spec L M (primeProfile_spec L x hx)

/-- A prime source mode retains its multiplicity after scale transport. -/
theorem primeProfile_transport_apply (x : SourceMode L) (hx : x ≠ 0)
    (p : SourceMode L) :
    primeProfile M (transport L M x) (transport_ne_zero L M hx) (transport L M p) =
      primeProfile L x hx p := by
  rw [primeProfile_transport, transportProfile_apply]

theorem primeProfile_transport_support (x : SourceMode L) (hx : x ≠ 0) :
    (primeProfile M (transport L M x) (transport_ne_zero L M hx)).support =
      (primeProfile L x hx).support.map (transport L M).toEquiv.toEmbedding := by
  rw [primeProfile_transport, transportProfile_support]

@[simp] theorem transportProfile_self (f : SourceMode L →₀ ℕ) :
    transportProfile L L f = f := by
  ext p
  simpa only [transport_self] using transportProfile_apply L L f p

theorem transportProfile_trans (N : ℝ) [Fact (0 < N)] (f : SourceMode L →₀ ℕ) :
    transportProfile M N (transportProfile L M f) = transportProfile L N f := by
  ext p
  obtain ⟨q, rfl⟩ := (transport L N).surjective p
  calc
    transportProfile M N (transportProfile L M f) (transport L N q) =
        transportProfile L M f (transport L M q) := by
      rw [← transport_trans L M N q, transportProfile_apply]
    _ = f q := transportProfile_apply L M f q
    _ = transportProfile L N f (transport L N q) :=
      (transportProfile_apply L N f q).symm

end GeneratedFoundations.Arithmetic.GeneratedFactorTransport
