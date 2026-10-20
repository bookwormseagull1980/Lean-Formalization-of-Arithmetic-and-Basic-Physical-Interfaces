module

public import GeneratedFoundations.Arithmetic.HistoryChargeSectors

/-!
# Continuous joint charge action on all arithmetic histories

The integer character is realized on the same invariant/detail projections
and source coordinates as the charge operator. The flow keeps every
history coefficient. Its group law, complete inner product and coordinate
derivative are derived before the neutral sector is selected.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryJointPhaseFlow

open HistoryJointCharge HistoryJointChargeLattice
open HistoryPhaseProjection (projection residual)
open HistoryRelativePhase (scalar)

def componentFlow (n : ℕ) (r b : ℤ) (t : ℝ) (s : Spin) :
    Module.End ℂ (Fibre n) :=
  HistoryRelativePhase.block n
    (scalar (weight n r b (false, s)) t,
      scalar (weight n r b (true, s)) t)

def flow (n : ℕ) (r b : ℤ) (t : ℝ) : Module.End ℂ (Space n) :=
  blocks n (componentFlow n r b t)

theorem flow_apply (n : ℕ) (r b : ℤ) (t : ℝ) (x : Space n) (s : Spin) :
    flow n r b t x s =
      scalar (weight n r b (false, s)) t • projection n (x s) +
        scalar (weight n r b (true, s)) t • residual n (x s) := by
  rw [flow, blocks_apply]
  rfl

theorem flow_zero (n : ℕ) (r b : ℤ) : flow n r b 0 = 1 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp [flow_apply, HistoryPhaseProjection.full_reconstruction]

theorem flow_add (n : ℕ) (r b : ℤ) (t u : ℝ) :
    flow n r b (t + u) = flow n r b t * flow n r b u := by
  rw [flow, flow, flow, HistoryJointChargeQuotient.blocks_mul]
  congr 1
  funext s
  unfold componentFlow
  rw [HistoryRelativePhase.scalar_add, HistoryRelativePhase.scalar_add]
  exact (HistoryRelativePhase.block n).map_mul
    (scalar (weight n r b (false, s)) t, scalar (weight n r b (true, s)) t)
    (scalar (weight n r b (false, s)) u, scalar (weight n r b (true, s)) u)

theorem flow_inverse (n : ℕ) (r b : ℤ) (t : ℝ) :
    flow n r b (-t) * flow n r b t = 1 := by
  rw [← flow_add, neg_add_cancel, flow_zero]

theorem componentFlow_inner (n : ℕ) (r b : ℤ) (t : ℝ) (s : Spin)
    (x y : Fibre n) :
    inner ℂ (componentFlow n r b t s x) (componentFlow n r b t s y) =
      inner ℂ x y := by
  have hex : inner ℂ x y =
      inner ℂ (projection n x) (projection n y) +
        inner ℂ (residual n x) (residual n y) := by
    conv_lhs => rw [← HistoryPhaseProjection.full_reconstruction n x,
      ← HistoryPhaseProjection.full_reconstruction n y]
    simp only [inner_add_left, inner_add_right,
      HistoryPhaseProjection.projection_residual_inner,
      HistoryRelativePhase.mixed_inner_zero, add_zero, zero_add]
  unfold componentFlow
  rw [HistoryRelativePhase.block_apply,
    HistoryRelativePhase.block_apply, hex]
  simp only [inner_add_left, inner_add_right, inner_smul_left (𝕜 := ℂ),
    inner_smul_right (𝕜 := ℂ), HistoryPhaseProjection.projection_residual_inner,
    HistoryRelativePhase.mixed_inner_zero, mul_zero, zero_add, add_zero]
  calc
    _ = ((starRingEnd ℂ) (scalar (weight n r b (false, s)) t) *
          scalar (weight n r b (false, s)) t) *
        inner ℂ (projection n x) (projection n y) +
        ((starRingEnd ℂ) (scalar (weight n r b (true, s)) t) *
          scalar (weight n r b (true, s)) t) *
        inner ℂ (residual n x) (residual n y) := by ring
    _ = _ := by rw [HistoryRelativePhase.scalar_conj_mul,
      HistoryRelativePhase.scalar_conj_mul, one_mul, one_mul]

theorem flow_inner (n : ℕ) (r b : ℤ) (t : ℝ) (x y : Space n) :
    inner ℂ (flow n r b t x) (flow n r b t y) = inner ℂ x y := by
  change (∑ s : Spin, inner ℂ (flow n r b t x s) (flow n r b t y s)) =
    ∑ s : Spin, inner ℂ (x s) (y s)
  exact Finset.sum_congr rfl fun s _ => by
    simpa only [flow, blocks_apply] using componentFlow_inner n r b t s (x s) (y s)

theorem flow_norm (n : ℕ) (r b : ℤ) (t : ℝ) (x : Space n) :
    ‖flow n r b t x‖ = ‖x‖ := by
  have h := congrArg Complex.re (flow_inner n r b t x x)
  have hs : ‖flow n r b t x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa only [← RCLike.re_eq_complex_re, inner_self_eq_norm_sq (𝕜 := ℂ)] using h
  nlinarith [norm_nonneg (flow n r b t x), norm_nonneg x]

theorem flow_coordinate_hasDerivAt (n : ℕ) (r b : ℤ) (t : ℝ)
    (x : Space n) (s : Spin) (h : HistoryModuleRepresentation.Index n) :
    HasDerivAt (fun u : ℝ => flow n r b u x s h)
      (Complex.I * (response n r b (flow n r b t x) s h)) t := by
  have hs (w : ℝ) :=
    Operations.FinitePhaseFlow.phase_hasDerivAt (fun _ : Unit => w) t ()
  have hd := ((hs (weight n r b (false, s))).mul_const (projection n (x s) h)).add
    ((hs (weight n r b (true, s))).mul_const (residual n (x s) h))
  convert hd using 1
  · ext u
    simp [flow_apply, scalar]
  · simp only [response, blocks_apply, component, HistoryRelativePhase.block_apply,
      flow, blocks_apply, componentFlow]
    simp only [map_add, map_smul,
      ← Module.End.mul_apply, HistoryPhaseProjection.projection_idempotent,
      HistoryPhaseProjection.projection_residual, HistoryPhaseProjection.residual_projection,
      HistoryPhaseProjection.residual_idempotent, LinearMap.zero_apply,
      smul_zero, add_zero, zero_add]
    simp [scalar, mul_add, mul_assoc]

/-- Continuity holds in the norm of the complete carrier, rather than only
on a chosen basis vector or after scalar observation. -/
theorem flow_continuous (n : ℕ) (r b : ℤ) (x : Space n) :
    Continuous (fun t : ℝ => flow n r b t x) := by
  have hf : (fun t : ℝ => flow n r b t x) = (fun t : ℝ =>
      WithLp.toLp 2 (fun s : Spin =>
    scalar (weight n r b (false, s)) t • projection n (x s) +
      scalar (weight n r b (true, s)) t • residual n (x s))) := by
    funext t
    apply PiLp.ext
    intro s
    exact flow_apply n r b t x s
  rw [hf]
  apply (PiLp.continuous_toLp 2 (fun _ : Spin => Fibre n)).comp
  apply continuous_pi
  intro s
  have hc (w : ℤ) : Continuous (fun t : ℝ => scalar w t) :=
    continuous_iff_continuousAt.mpr fun t => by
      simpa only [scalar] using
        (Operations.FinitePhaseFlow.phase_hasDerivAt (fun _ : Unit => (w : ℝ)) t ()).continuousAt
  exact ((hc _).smul continuous_const).add ((hc _).smul continuous_const)

def unitary (n : ℕ) (r b : ℤ) (t : ℝ) : Space n ≃ₗᵢ[ℂ] Space n where
  toFun := flow n r b t
  invFun := flow n r b (-t)
  left_inv x := LinearMap.congr_fun (flow_inverse n r b t) x
  right_inv x := by
    have h := LinearMap.congr_fun (flow_inverse n r b (-t)) x
    change (flow n r b t * flow n r b (-t)) x = (1 : Module.End ℂ (Space n)) x
    simpa only [neg_neg] using h
  map_add' := (flow n r b t).map_add
  map_smul' := (flow n r b t).map_smul
  norm_map' := flow_norm n r b t

theorem flow_upperSection (n : ℕ) (r b : ℤ) (t : ℝ)
    (f : HistoryPhaseProjection.HistorySpace n) :
    flow n r b t (HistoryChargeRealization.upperSection n f) =
      scalar (r - (n : ℤ) * b) t • HistoryChargeRealization.upperSection n f := by
  have hp : projection n (HistoryPhaseProjection.lift n f) =
      HistoryPhaseProjection.lift n f := by
    change (HistoryPhaseProjection.lift n)
      (((HistoryPhaseProjection.average n).comp (HistoryPhaseProjection.lift n)) f) = _
    rw [HistoryPhaseProjection.average_lift]
    rfl
  have hr : residual n (HistoryPhaseProjection.lift n f) = 0 := by
    simp [HistoryPhaseProjection.residual, hp]
  apply PiLp.ext
  intro s
  by_cases he : s = (.inr 0 : Spin)
  · subst s
    simp [flow_apply, HistoryChargeRealization.upperSection, inclusion, hp, hr]
  · simp [flow_apply, HistoryChargeRealization.upperSection, inclusion, he]

theorem generatedFlow_fixes_upper (n : ℕ) (t : ℝ)
    (f : HistoryPhaseProjection.HistorySpace n) :
    flow n n 1 t (HistoryChargeRealization.upperSection n f) =
      HistoryChargeRealization.upperSection n f := by
  rw [flow_upperSection]
  simp [scalar, Operations.FinitePhaseFlow.phase]

abbrev End (n : ℕ) := Space n →L[ℂ] Space n

local instance (n : ℕ) : NormedRing (End n) := ContinuousLinearMap.toNormedRing
local instance (n : ℕ) : NormedAlgebra ℂ (End n) := ContinuousLinearMap.toNormedAlgebra
local instance (n : ℕ) : IsTopologicalRing (End n) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

def continuousModel (n : ℕ) : Module.End ℂ (Space n) ≃ₐ[ℂ] End n :=
  Module.End.toContinuousLinearMap (Space n)

/-- The algebra of all eight spectral sectors acts on the original
carrier, with its original multiplicities. -/
def sectorAlgebra (n : ℕ) : (Spin → ℂ × ℂ) →ₐ[ℂ] Module.End ℂ (Space n) where
  toFun z := blocks n (fun s => HistoryRelativePhase.block n (z s))
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro s
    simp
  map_one' := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro s
    simp
  map_add' z v := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro s
    simp
  map_mul' z v := by
    rw [HistoryJointChargeQuotient.blocks_mul]
    congr 1
    funext s
    exact (HistoryRelativePhase.block n).map_mul (z s) (v s)
  commutes' c := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro s
    simp
    rw [← smul_add, HistoryPhaseProjection.full_reconstruction]

def continuousSectorAlgebra (n : ℕ) : (Spin → ℂ × ℂ) →ₐ[ℂ] End n :=
  (continuousModel n).toAlgHom.comp (sectorAlgebra n)

theorem flow_eq_exp (n : ℕ) (r b : ℤ) (t : ℝ) :
    continuousModel n (flow n r b t) =
      NormedSpace.exp ((Complex.I * (t : ℂ)) • continuousModel n (response n r b)) := by
  let z : Spin → ℂ × ℂ := fun s =>
    ((weight n r b (false, s) : ℂ), (weight n r b (true, s) : ℂ))
  have hz : sectorAlgebra n z = response n r b := rfl
  have hc : Continuous (continuousSectorAlgebra n) :=
    (continuousSectorAlgebra n).toLinearMap.continuous_of_finiteDimensional
  have he := Operations.FinitePhaseFlow.map_exp (continuousSectorAlgebra n) hc
    ((Complex.I * (t : ℂ)) • z)
  have hf : sectorAlgebra n (NormedSpace.exp ((Complex.I * (t : ℂ)) • z)) =
      flow n r b t := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro s
    simp only [sectorAlgebra, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, blocks_apply, Pi.coe_exp, Pi.smul_apply,
      flow, blocks_apply, componentFlow]
    apply congrArg (fun v : ℂ × ℂ => HistoryRelativePhase.block n v (x s))
    apply Prod.ext <;>
      simp [z, scalar, Operations.FinitePhaseFlow.phase, ← Complex.exp_eq_exp_ℂ,
        mul_comm, mul_left_comm, mul_assoc]
  change continuousModel n (sectorAlgebra n (NormedSpace.exp _)) =
    NormedSpace.exp (continuousModel n (sectorAlgebra n _)) at he
  rw [hf, map_smul, hz, map_smul] at he
  exact he

structure Conclusions : Prop where
  group_law : ∀ n r b t u, flow n r b (t + u) = flow n r b t * flow n r b u
  all_pairings : ∀ n r b t x y,
    inner ℂ (flow n r b t x) (flow n r b t y) = inner ℂ x y
  coordinate_generator : ∀ n r b t x s h,
    HasDerivAt (fun u : ℝ => flow n r b u x s h)
      (Complex.I * (response n r b (flow n r b t x) s h)) t
  strong_continuity : ∀ n r b x, Continuous (fun t : ℝ => flow n r b t x)
  exact_exponential : ∀ n r b t, continuousModel n (flow n r b t) =
    NormedSpace.exp ((Complex.I * (t : ℂ)) • continuousModel n (response n r b))
  canonical_fixed_sector : ∀ n t f,
    flow n n 1 t (HistoryChargeRealization.upperSection n f) =
      HistoryChargeRealization.upperSection n f

theorem generated : Conclusions where
  group_law := flow_add
  all_pairings := flow_inner
  coordinate_generator := flow_coordinate_hasDerivAt
  strong_continuity := flow_continuous
  exact_exponential := flow_eq_exp
  canonical_fixed_sector := generatedFlow_fixes_upper

end GeneratedFoundations.Arithmetic.HistoryJointPhaseFlow
