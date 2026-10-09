module

public import GeneratedFoundations.Spectral.OrientedLift
public import GeneratedFoundations.Spectral.NeumannScaleTransport
public import GeneratedFoundations.Arithmetic.InternalPrimes
public import GeneratedFoundations.Arithmetic.WindingCertification
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Arithmetic on the lifted source modes

An element is a continuous circle endomorphism represented by the oriented
lift of a canonical eigenvector of the original Neumann operator. Modulation
and cascade are defined on these maps themselves. The comparison with the
nonnegative power family preserves the underlying maps and carries the
internal recursion and factorization results to the source family.

The order is the heat-response order of the corresponding actual spectral
projections. Scale transport preserves the normalized circle maps and agrees
with the unitary transport of their original interval representatives and
the rescaling of the Gaussian change parameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology NNReal
open GeneratedFoundations.Spectral

namespace GeneratedFoundations.Arithmetic.GeneratedModes

variable (L : ℝ) [hL : Fact (0 < L)]

def SourceMode := {u : Circle →ₜ* Circle // OrientedLift.IsLiftedSourceMode L u}

instance : CoeFun (SourceMode L) (fun _ => Circle → Circle) := ⟨fun u => u.val⟩

@[ext] theorem ext {u v : SourceMode L} (h : ∀ z : Circle, u z = v z) : u = v := by
  apply Subtype.ext
  exact DFunLike.ext _ _ h

/-- Only the proved equivalent membership property changes. -/
def toNative (u : SourceMode L) : NativeModes.Mode :=
  ⟨u.val, (OrientedLift.isLiftedSourceMode_iff L u.val).mp u.property⟩

def fromNative (u : NativeModes.Mode) : SourceMode L :=
  ⟨u.val, OrientedLift.nativeMode_has_source L u⟩

@[simp] theorem toNative_val (u : SourceMode L) : (toNative L u).val = u.val := rfl
@[simp] theorem fromNative_val (u : NativeModes.Mode) : (fromNative L u).val = u.val := rfl

@[simp] theorem fromNative_toNative (u : SourceMode L) :
    fromNative L (toNative L u) = u := rfl

@[simp] theorem toNative_fromNative (u : NativeModes.Mode) :
    toNative L (fromNative L u) = u := rfl

theorem toNative_injective : Function.Injective (toNative L) := by
  intro u v h
  exact Subtype.ext (congrArg (fun w : NativeModes.Mode => w.val) h)

theorem toNative_surjective : Function.Surjective (toNative L) :=
  fun u => ⟨fromNative L u, rfl⟩

def zeroMode : SourceMode L :=
  ⟨1, (OrientedLift.isLiftedSourceMode_iff L 1).mpr ⟨0, by ext z; simp⟩⟩

def unitMode : SourceMode L :=
  ⟨ContinuousMonoidHom.id Circle,
    (OrientedLift.isLiftedSourceMode_iff L _).mpr ⟨1, by ext z; simp⟩⟩

/-- Addition of source modes is pointwise multiplication of their values. -/
def modulate (u v : SourceMode L) : SourceMode L :=
  ⟨u.val * v.val,
    (OrientedLift.isLiftedSourceMode_iff L _).mpr
      ((toNative L u) + (toNative L v)).property⟩

/-- Multiplication of source modes is composition of their actual circle maps. -/
def compose (u v : SourceMode L) : SourceMode L :=
  ⟨u.val.comp v.val,
    (OrientedLift.isLiftedSourceMode_iff L _).mpr
      ((toNative L u) * (toNative L v)).property⟩

instance : Zero (SourceMode L) := ⟨zeroMode L⟩
instance : One (SourceMode L) := ⟨unitMode L⟩
instance : Add (SourceMode L) := ⟨modulate L⟩
instance : Mul (SourceMode L) := ⟨compose L⟩

@[simp] theorem zero_apply (z : Circle) : (0 : SourceMode L) z = 1 := rfl
@[simp] theorem one_apply (z : Circle) : (1 : SourceMode L) z = z := rfl
@[simp] theorem add_apply (u v : SourceMode L) (z : Circle) :
    (u + v) z = u z * v z := rfl
@[simp] theorem mul_apply (u v : SourceMode L) (z : Circle) :
    (u * v) z = u (v z) := rfl

@[simp] theorem toNative_zero : toNative L 0 = 0 := rfl
@[simp] theorem toNative_one : toNative L 1 = 1 := rfl
@[simp] theorem toNative_add (u v : SourceMode L) :
    toNative L (u + v) = toNative L u + toNative L v := rfl
@[simp] theorem toNative_mul (u v : SourceMode L) :
    toNative L (u * v) = toNative L u * toNative L v := rfl
@[simp] theorem fromNative_zero : fromNative L 0 = 0 := rfl
@[simp] theorem fromNative_one : fromNative L 1 = 1 := rfl
@[simp] theorem fromNative_add (u v : NativeModes.Mode) :
    fromNative L (u + v) = fromNative L u + fromNative L v := rfl
@[simp] theorem fromNative_mul (u v : NativeModes.Mode) :
    fromNative L (u * v) = fromNative L u * fromNative L v := rfl

def powerMode (n : ℕ) : SourceMode L := fromNative L (NativeModes.powerMode n)

@[simp] theorem powerMode_apply (n : ℕ) (z : Circle) : powerMode L n z = z ^ n :=
  NativeModes.powerMode_apply n z

@[simp] theorem toNative_powerMode (n : ℕ) :
    toNative L (powerMode L n) = NativeModes.powerMode n := rfl

@[simp] theorem powerMode_zero : powerMode L 0 = 0 := by
  simp only [powerMode, NativeModes.powerMode_zero, fromNative_zero]

@[simp] theorem powerMode_one : powerMode L 1 = 1 := by
  simp only [powerMode, NativeModes.powerMode_one, fromNative_one]

theorem powerMode_add (m n : ℕ) : powerMode L (m + n) = powerMode L m + powerMode L n := by
  apply toNative_injective L
  simp only [toNative_add, toNative_powerMode, NativeModes.powerMode_add]

theorem powerMode_mul (m n : ℕ) : powerMode L (m * n) = powerMode L m * powerMode L n := by
  apply toNative_injective L
  simp only [toNative_mul, toNative_powerMode, NativeModes.powerMode_mul]

instance : CommSemiring (SourceMode L) where
  add_assoc u v w := by ext z; simp [mul_assoc]
  zero_add u := by ext z; simp
  add_zero u := by ext z; simp
  add_comm u v := by ext z; simp [mul_comm]
  nsmul := nsmulRec
  mul_assoc u v w := by ext z; rfl
  one_mul u := by ext z; rfl
  mul_one u := by ext z; rfl
  npow := npowRec
  left_distrib u v w := by
    apply ext
    intro z
    exact u.val.map_mul (v z) (w z)
  right_distrib u v w := by ext z; rfl
  zero_mul u := by ext z; rfl
  mul_zero u := by
    apply ext
    intro z
    exact u.val.map_one
  mul_comm u v := by
    apply toNative_injective L
    simp only [toNative_mul, mul_comm]
  natCast := powerMode L
  natCast_zero := powerMode_zero L
  natCast_succ n := by rw [powerMode_add, powerMode_one]

/-- The equivalence fixes every actual circle map and preserves the already
defined modulation and cascade operations. -/
def nativeEquiv : SourceMode L ≃+* NativeModes.Mode where
  toFun := toNative L
  invFun := fromNative L
  left_inv := fromNative_toNative L
  right_inv := toNative_fromNative L
  map_mul' := toNative_mul L
  map_add' := toNative_add L

@[simp] theorem nativeEquiv_apply (u : SourceMode L) : nativeEquiv L u = toNative L u := rfl
@[simp] theorem nativeEquiv_symm_apply (u : NativeModes.Mode) :
    (nativeEquiv L).symm u = fromNative L u := rfl

@[simp] theorem toNative_eq_zero_iff (u : SourceMode L) : toNative L u = 0 ↔ u = 0 := by
  rw [← toNative_zero L]
  exact (toNative_injective L).eq_iff

@[simp] theorem toNative_eq_one_iff (u : SourceMode L) : toNative L u = 1 ↔ u = 1 := by
  rw [← toNative_one L]
  exact (toNative_injective L).eq_iff

def successor (u : SourceMode L) : SourceMode L := u + 1

@[simp] theorem toNative_successor (u : SourceMode L) :
    toNative L (successor L u) = NativeModes.successor (toNative L u) := rfl

@[simp] theorem fromNative_successor (u : NativeModes.Mode) :
    fromNative L (NativeModes.successor u) = successor L (fromNative L u) := rfl

theorem successor_injective : Function.Injective (successor L) := by
  intro u v h
  apply toNative_injective L
  apply NativeModes.successor_injective
  exact congrArg (toNative L) h

theorem successor_ne_zero (u : SourceMode L) : successor L u ≠ 0 := by
  intro h
  apply NativeModes.successor_ne_zero (toNative L u)
  simpa only [toNative_successor, toNative_zero] using congrArg (toNative L) h

theorem successor_induction {P : SourceMode L → Prop} (hzero : P 0)
    (hstep : ∀ u, P u → P (successor L u)) : ∀ u, P u := by
  have h : ∀ v : NativeModes.Mode, P (fromNative L v) :=
    NativeModes.successor_induction (by simpa only [fromNative_zero] using hzero)
      (fun v hv => by simpa only [fromNative_successor] using hstep (fromNative L v) hv)
  intro u
  simpa only [fromNative_toNative] using h (toNative L u)

def fold {X : Type*} (xzero : X) (step : X → X) (u : SourceMode L) : X :=
  NativeModes.fold xzero step (toNative L u)

@[simp] theorem fold_zero {X : Type*} (xzero : X) (step : X → X) :
    fold L xzero step 0 = xzero := by
  simp only [fold, toNative_zero, NativeModes.fold_zero]

@[simp] theorem fold_successor {X : Type*} (xzero : X) (step : X → X) (u : SourceMode L) :
    fold L xzero step (successor L u) = step (fold L xzero step u) := by
  simp only [fold, toNative_successor, NativeModes.fold_successor]

theorem recursion_existsUnique {X : Type*} (xzero : X) (step : X → X) :
    ∃! f : SourceMode L → X, f 0 = xzero ∧
      ∀ u, f (successor L u) = step (f u) := by
  refine ⟨fold L xzero step, ⟨fold_zero L _ _, fold_successor L _ _⟩, ?_⟩
  intro f hf
  funext u
  apply successor_induction L (P := fun v => f v = fold L xzero step v) ?_ ?_ u
  · simpa only [fold_zero] using hf.1
  · intro v hv
    rw [hf.2, fold_successor, hv]

/-- Irreducibility refers to composition of the source maps themselves. -/
def SourceIrreducible (p : SourceMode L) : Prop :=
  p ≠ 0 ∧ p ≠ 1 ∧ ∀ a b : SourceMode L, p = a * b → a = 1 ∨ b = 1

theorem sourceIrreducible_iff (p : SourceMode L) :
    SourceIrreducible L p ↔ NativeModes.NativeIrreducible (toNative L p) := by
  constructor
  · rintro ⟨hp0, hp1, hp⟩
    refine ⟨fun h => hp0 ((toNative_eq_zero_iff L p).mp h),
      fun h => hp1 ((toNative_eq_one_iff L p).mp h), ?_⟩
    intro a b hab
    have hab' : p = fromNative L a * fromNative L b := by
      apply toNative_injective L
      simpa only [toNative_mul, toNative_fromNative] using hab
    rcases hp (fromNative L a) (fromNative L b) hab' with ha | hb
    · exact Or.inl (by simpa only [toNative_fromNative, toNative_one] using congrArg (toNative L) ha)
    · exact Or.inr (by simpa only [toNative_fromNative, toNative_one] using congrArg (toNative L) hb)
  · rintro ⟨hp0, hp1, hp⟩
    refine ⟨fun h => hp0 (by rw [h, toNative_zero]),
      fun h => hp1 (by rw [h, toNative_one]), ?_⟩
    intro a b hab
    have hab' : toNative L p = toNative L a * toNative L b := by
      rw [hab, toNative_mul]
    rcases hp (toNative L a) (toNative L b) hab' with ha | hb
    · exact Or.inl ((toNative_eq_one_iff L a).mp ha)
    · exact Or.inr ((toNative_eq_one_iff L b).mp hb)

/-- The imported factorization is the internal Euclidean construction on
actual maps; the multiset here is indexed by source modes. -/
theorem factorMultiset_existsUnique {x : SourceMode L} (hx : x ≠ 0) :
    ∃! s : Multiset (SourceMode L),
      (∀ p ∈ s, SourceIrreducible L p) ∧ s.prod = x := by
  classical
  obtain ⟨s, hs, hunique⟩ := NativeModes.native_factor_multiset_existsUnique
    ((toNative_eq_zero_iff L x).not.mpr hx)
  refine ⟨s.map (nativeEquiv L).symm, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    apply (sourceIrreducible_iff L _).mpr
    simpa only [nativeEquiv_symm_apply, toNative_fromNative] using hs.1 q hq
  · rw [Multiset.prod_hom, hs.2]
    exact fromNative_toNative L x
  · intro k hk
    have hkmap : k.map (nativeEquiv L) = s := hunique _ (by
      constructor
      · intro p hp
        obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
        exact (sourceIrreducible_iff L q).mp (hk.1 q hq)
      · rw [Multiset.prod_hom, hk.2]
        rfl)
    apply Multiset.map_injective (nativeEquiv L).injective
    have hinverse : (s.map (nativeEquiv L).symm).map (nativeEquiv L) = s := by
      rw [Multiset.map_map]
      have hid : (nativeEquiv L) ∘ (nativeEquiv L).symm = id := by
        funext p
        exact (nativeEquiv L).apply_symm_apply p
      rw [hid, Multiset.map_id]
    exact hkmap.trans hinverse.symm

/-- Finite prime multiplicities are strictly unique on the same source family. -/
theorem exponentProfile_existsUnique {x : SourceMode L} (hx : x ≠ 0) :
    ∃! f : SourceMode L →₀ ℕ, (∀ p ∈ f.support, SourceIrreducible L p) ∧
      f.prod (fun p n => p ^ n) = x := by
  classical
  obtain ⟨s, hs, hunique⟩ := factorMultiset_existsUnique L hx
  refine ⟨s.toFinsupp, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    exact hs.1 p (by simpa only [Multiset.toFinsupp_support, Multiset.mem_toFinset] using hp)
  · rw [← Finsupp.prod_toMultiset, Multiset.toFinsupp_toMultiset, hs.2]
  · intro f hf
    have heq : f.toMultiset = s := hunique f.toMultiset
      ⟨fun p hp => hf.1 p ((Finsupp.mem_toMultiset f p).mp hp),
        by simpa only [Finsupp.prod_toMultiset] using hf.2⟩
    simpa only [Finsupp.toMultiset_toFinsupp] using congrArg Multiset.toFinsupp heq

/-- The corresponding projection is a member of the original, unlabeled
spectral projection class. Its coordinate is supplied by the proved classification. -/
def component (u : SourceMode L) : NeumannSpectralProjections.Component L :=
  NeumannSpectralProjections.mode L (NativeModes.index (toNative L u))

def fromComponent (P : NeumannSpectralProjections.Component L) : SourceMode L :=
  powerMode L (NeumannSpectralProjections.coordinate L P)

@[simp] theorem coordinate_component (u : SourceMode L) :
    NeumannSpectralProjections.coordinate L (component L u) =
      NativeModes.index (toNative L u) := NeumannSpectralProjections.coordinate_mode L _

def componentEquiv : SourceMode L ≃ NeumannSpectralProjections.Component L where
  toFun := component L
  invFun := fromComponent L
  left_inv u := by
    apply toNative_injective L
    simp only [fromComponent, toNative_powerMode, coordinate_component, NativeModes.powerMode_index]
  right_inv P := by
    simp only [component, fromComponent, toNative_powerMode, NativeModes.index_powerMode,
      NeumannSpectralProjections.mode_coordinate]

/-- The order is obtained from the finite-dimensional heat traces on the
actual source eigenspaces. -/
instance : LinearOrder (SourceMode L) :=
  LinearOrder.lift' (component L) (componentEquiv L).injective

theorem source_le_iff_component (u v : SourceMode L) :
    u ≤ v ↔ component L u ≤ component L v := Iff.rfl

theorem source_lt_iff_component (u v : SourceMode L) :
    u < v ↔ component L u < component L v := Iff.rfl

theorem source_le_iff_native (u v : SourceMode L) :
    u ≤ v ↔ toNative L u ≤ toNative L v := by
  rw [source_le_iff_component, NeumannSpectralProjections.component_le_iff,
    coordinate_component, coordinate_component]
  rfl

theorem source_lt_iff_native (u v : SourceMode L) :
    u < v ↔ toNative L u < toNative L v := by
  rw [source_lt_iff_component, NeumannSpectralProjections.component_lt_iff,
    coordinate_component, coordinate_component]
  rfl

theorem source_le_iff_exists_add (u v : SourceMode L) :
    u ≤ v ↔ ∃ w : SourceMode L, v = u + w := by
  rw [source_le_iff_native, NativeModes.native_le_iff_exists_add]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fromNative L w, (toNative_injective L) ?_⟩
    simpa only [toNative_add, toNative_fromNative] using hw
  · rintro ⟨w, rfl⟩
    exact ⟨toNative L w, toNative_add L u w⟩

theorem source_order_response (u v : SourceMode L) {t : ℝ≥0} (ht : 0 < t) :
    u ≤ v ↔ NeumannSpectralProjections.response L (component L v) t ≤
      NeumannSpectralProjections.response L (component L u) t :=
  (source_le_iff_component L u v).trans
    (NeumannSpectralProjections.response_weak_order_time_independent L _ _ ht)

theorem source_strict_order_response (u v : SourceMode L) {t : ℝ≥0} (ht : 0 < t) :
    u < v ↔ NeumannSpectralProjections.response L (component L v) t <
      NeumannSpectralProjections.response L (component L u) t :=
  (source_lt_iff_component L u v).trans
    (NeumannSpectralProjections.response_order_time_independent L _ _ ht)

def representative (u : SourceMode L) : (complexNeumannOperator hL.out).domain :=
  neumannCosineDomainVector L (NativeModes.index (toNative L u))

theorem representative_lifts (u : SourceMode L) :
    OrientedLift.lift L (representative L u : ComplexIntervalL2 0 L) =ᵐ[AddCircle.haarAddCircle]
      OrientedLift.endomorphismRepresentative L u.val := by
  apply (OrientedLift.liftedMode_endomorphism_iff L _ u.val).mpr
  exact (congrArg Subtype.val (NativeModes.powerMode_index (toNative L u))).symm

theorem representative_mem_component (u : SourceMode L) :
    (representative L u : ComplexIntervalL2 0 L) ∈ (component L u).val.range := by
  rw [NeumannSpectralProjections.component_range, coordinate_component]
  exact Submodule.subset_span (Set.mem_singleton _)

theorem representative_norm (u : SourceMode L) :
    ‖(representative L u : ComplexIntervalL2 0 L)‖ = 1 :=
  (neumannCosineMode_orthonormal L).norm_eq_one _

theorem representative_endpoint_positive (u : SourceMode L) :
    ∃ r : ℝ, 0 < r ∧ neumannLeftTrace L (representative L u) = (r : ℂ) :=
  ⟨neumannModeEndpoint L _, neumannModeEndpoint_pos L _, neumannLeftTrace_cosine L _⟩

theorem representative_unique (u : SourceMode L)
    (f : (complexNeumannOperator hL.out).domain)
    (hf : (f : ComplexIntervalL2 0 L) ∈ (component L u).val.range)
    (hn : ‖(f : ComplexIntervalL2 0 L)‖ = 1)
    (hp : ∃ r : ℝ, 0 < r ∧ neumannLeftTrace L f = (r : ℂ)) : f = representative L u := by
  apply neumannCanonicalMode_unique L _ f _ hn hp
  have heig := (NeumannSpectralProjections.domain_mem_range_iff L (component L u) f).mp hf
  simpa only [NeumannSpectralProjections.energy, coordinate_component] using heig

@[simp] theorem component_zero :
    component L 0 = NeumannSpectralProjections.mode L 0 := by
  simp only [component, toNative_zero, NativeModes.index_zero]

@[simp] theorem component_one :
    component L 1 = NeumannSpectralProjections.mode L 1 := by
  simp only [component, toNative_one, NativeModes.index_one]

@[simp] theorem component_successor (u : SourceMode L) :
    component L (successor L u) =
      NeumannSpectralProjections.successor L (component L u) := by
  simp only [component, toNative_successor, NativeModes.index_successor,
    NeumannSpectralProjections.successor, NeumannSpectralProjections.coordinate_mode]

theorem source_zero_energy_iff (u : SourceMode L) :
    NeumannSpectralProjections.energy L (component L u) = 0 ↔ u = 0 := by
  rw [NeumannSpectralProjections.energy_eq_zero_iff, ← component_zero L]
  exact (componentEquiv L).injective.eq_iff

theorem successor_spec (u : SourceMode L) :
    u < successor L u ∧ ∀ v : SourceMode L, u < v → successor L u ≤ v := by
  have h := NeumannSpectralProjections.successor_spec L (component L u)
  constructor
  · change component L u < component L (successor L u)
    rw [component_successor]
    exact h.1
  · intro v hv
    change component L (successor L u) ≤ component L v
    rw [component_successor]
    exact h.2 (component L v) hv

theorem immediate_successor_existsUnique (u : SourceMode L) :
    ∃! v : SourceMode L, u < v ∧ ∀ w : SourceMode L, u < w → v ≤ w := by
  refine ⟨successor L u, successor_spec L u, ?_⟩
  intro v hv
  exact le_antisymm (hv.2 _ (successor_spec L u).1) ((successor_spec L u).2 v hv.1)

theorem unit_first_positive :
    (0 : SourceMode L) < 1 ∧ ∀ u : SourceMode L, 0 < u → 1 ≤ u := by
  simpa only [successor, zero_add] using successor_spec L 0

theorem unit_first_positive_unique (u : SourceMode L)
    (hu : 0 < u ∧ ∀ v : SourceMode L, 0 < v → u ≤ v) : u = 1 :=
  le_antisymm (hu.2 1 (unit_first_positive L).1) ((unit_first_positive L).2 u hu.1)

/-- The integral is evaluated on the actual source map, after its operations
and its spectral representative have already been constructed. -/
theorem degreeIntegral_source (u : SourceMode L) :
    WindingCertification.degreeIntegral u.val = (NativeModes.index (toNative L u) : ℂ) :=
  WindingCertification.degreeIntegral_native (toNative L u)

theorem source_degree_energy (u : SourceMode L) :
    (NativeModes.index (toNative L u) : ℝ) =
      Real.sqrt (NeumannSpectralProjections.energy L (component L u) /
        NeumannScaleTransport.energyUnit L) := by
  simpa only [WindingCertification.degreeEquiv_eq_index,
    NeumannSpectralProjections.energy, coordinate_component] using
    WindingCertification.degree_from_energy L (toNative L u)

theorem degreeIntegral_energy (u : SourceMode L) :
    WindingCertification.degreeIntegral u.val =
      (Real.sqrt (NeumannSpectralProjections.energy L (component L u) /
        NeumannScaleTransport.energyUnit L) : ℂ) := by
  rw [degreeIntegral_source, ← source_degree_energy L u]
  norm_cast

theorem degreeIntegral_injective :
    Function.Injective (fun u : SourceMode L => WindingCertification.degreeIntegral u.val) := by
  intro u v h
  apply toNative_injective L
  exact WindingCertification.degreeIntegral_injective h

variable (M : ℝ) [hM : Fact (0 < M)]

theorem transport_leftInverse (u : SourceMode L) :
    fromNative L (toNative M (fromNative M (toNative L u))) = u :=
  (congrArg (fromNative L) (toNative_fromNative M (toNative L u))).trans
    (fromNative_toNative L u)

theorem transport_preserves_mul (u v : SourceMode L) :
    fromNative M (toNative L (u * v)) =
      fromNative M (toNative L u) * fromNative M (toNative L v) :=
  (congrArg (fromNative M) (toNative_mul L u v)).trans
    (fromNative_mul M (toNative L u) (toNative L v))

theorem transport_preserves_add (u v : SourceMode L) :
    fromNative M (toNative L (u + v)) =
      fromNative M (toNative L u) + fromNative M (toNative L v) :=
  (congrArg (fromNative M) (toNative_add L u v)).trans
    (fromNative_add M (toNative L u) (toNative L v))

/-- Scale transport retains the actual circle map in the shared normalized coordinate. -/
def transport : SourceMode L ≃+* SourceMode M where
  toFun u := fromNative M (toNative L u)
  invFun u := fromNative L (toNative M u)
  left_inv := transport_leftInverse L M
  right_inv := transport_leftInverse M L
  map_mul' := transport_preserves_mul L M
  map_add' := transport_preserves_add L M

@[simp] theorem transport_val (u : SourceMode L) : (transport L M u).val = u.val :=
  (fromNative_val M (toNative L u)).trans (toNative_val L u)
@[simp] theorem transport_apply (u : SourceMode L) (z : Circle) : transport L M u z = u z :=
  congrArg (fun f : Circle →ₜ* Circle => f z) (transport_val L M u)
@[simp] theorem toNative_transport (u : SourceMode L) :
    toNative M (transport L M u) = toNative L u :=
  Subtype.ext (transport_val L M u)

@[simp] theorem transport_zero : transport L M 0 = 0 := map_zero _
@[simp] theorem transport_one : transport L M 1 = 1 := map_one _
theorem transport_add (u v : SourceMode L) :
    transport L M (u + v) = transport L M u + transport L M v := map_add _ _ _
theorem transport_mul (u v : SourceMode L) :
    transport L M (u * v) = transport L M u * transport L M v := map_mul _ _ _

@[simp] theorem transport_successor (u : SourceMode L) :
    transport L M (successor L u) = successor M (transport L M u) := by
  simp only [successor, map_add, map_one]

theorem transport_unique (f : SourceMode L → SourceMode M)
    (hzero : f 0 = 0) (hstep : ∀ u, f (successor L u) = successor M (f u)) :
    f = transport L M := by
  funext u
  apply successor_induction L (P := fun u => f u = transport L M u) ?_ ?_ u
  · simpa only [map_zero] using hzero
  · intro v hv
    rw [hstep, transport_successor, hv]

theorem transport_existsUnique :
    ∃! f : SourceMode L → SourceMode M,
      f 0 = 0 ∧ ∀ u, f (successor L u) = successor M (f u) :=
  ⟨transport L M, ⟨map_zero _, transport_successor L M⟩,
    fun f hf => transport_unique L M f hf.1 hf.2⟩

theorem transport_le_iff (u v : SourceMode L) :
    transport L M u ≤ transport L M v ↔ u ≤ v := by
  simp only [source_le_iff_native, toNative_transport]

def transportOrderIso : SourceMode L ≃o SourceMode M where
  toEquiv := (transport L M).toEquiv
  map_rel_iff' := fun {u v} => transport_le_iff L M u v

theorem transport_irreducible_iff (u : SourceMode L) :
    SourceIrreducible M (transport L M u) ↔ SourceIrreducible L u := by
  simp only [sourceIrreducible_iff, toNative_transport]

theorem transport_component (u : SourceMode L) :
    component M (transport L M u) =
      NeumannScaleTransport.componentTransport L M (component L u) := by
  simp only [component, toNative_transport, NeumannScaleTransport.componentTransport_mode]

theorem transport_representative (u : SourceMode L) :
    NeumannScaleTransport.unitary L M (representative L u : ComplexIntervalL2 0 L) =
      (representative M (transport L M u) : ComplexIntervalL2 0 M) := by
  change NeumannScaleTransport.unitary L M
      (neumannCosineMode L (NativeModes.index (toNative L u))) =
    neumannCosineMode M (NativeModes.index (toNative M (transport L M u)))
  rw [NeumannScaleTransport.unitary_cosine, toNative_transport]

theorem transport_normalized_energy (u : SourceMode L) :
    NeumannSpectralProjections.energy M (component M (transport L M u)) /
        NeumannScaleTransport.energyUnit M =
      NeumannSpectralProjections.energy L (component L u) /
        NeumannScaleTransport.energyUnit L := by
  rw [transport_component]
  exact NeumannScaleTransport.componentTransport_normalized_energy L M (component L u)

theorem transport_response (u : SourceMode L) (t : ℝ≥0) :
    NeumannSpectralProjections.response M (component M (transport L M u))
        (NeumannScaleTransport.changeParameter L M t) =
      NeumannSpectralProjections.response L (component L u) t := by
  rw [transport_component]
  exact NeumannScaleTransport.componentTransport_response L M (component L u) t

@[simp] theorem transport_degreeIntegral (u : SourceMode L) :
    WindingCertification.degreeIntegral (transport L M u).val =
      WindingCertification.degreeIntegral u.val := by rw [transport_val]

@[simp] theorem transport_self (u : SourceMode L) : transport L L u = u :=
  Subtype.ext (transport_val L L u)

theorem transport_trans (N : ℝ) [Fact (0 < N)] (u : SourceMode L) :
    transport M N (transport L M u) = transport L N u := by
  apply Subtype.ext
  rw [transport_val, transport_val, transport_val]

end GeneratedFoundations.Arithmetic.GeneratedModes
