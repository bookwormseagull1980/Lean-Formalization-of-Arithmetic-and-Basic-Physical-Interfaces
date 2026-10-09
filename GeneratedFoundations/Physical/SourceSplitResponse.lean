module

public import GeneratedFoundations.Physical.SourceExchangeConnectorTransport
public import Mathlib.LinearAlgebra.Prod

/-!
# Generated responses that preserve the exchange split

The independent source responses generate all endomorphisms of the source
tensor square.  Within that generated algebra, commuting with tensor exchange
is equivalent to preserving its two eigenspaces.  The established unitary
exchange decomposition identifies this subalgebra with `End W × End L`.

Tensoring these same operators with the retained spin carrier gives exactly
the split-colour responses on the joint carrier.  Both identifications are
operator identities through the existing exchange unitary.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open GeneratedFoundations.Geometry.SourceQuadraticSplit
open GeneratedFoundations.Physical.SourceJointResponse (W L S)
open GeneratedFoundations.Physical.SourceMinimalRepresentation (SourceCarrier)
open GeneratedFoundations.Physical.SourceExchangeConnectorTransport
  (colourSplit exchangeUnitary operatorTransport)

namespace GeneratedFoundations.Physical.SourceSplitResponse

abbrev C := SourcePreExchangeResponse.C
abbrev SplitColour := SourceJointResponse.SplitColour
abbrev FullCarrier := SourcePreExchangeResponse.FullCarrier

/-- Coordinates of the established unitary exchange decomposition. -/
def colourPair : C ≃ₗ[ℂ] W × L :=
  colourSplit.toLinearEquiv.trans (WithLp.linearEquiv 2 ℂ (W × L))

@[simp] theorem colourPair_apply (c : C) :
    colourPair c = WithLp.ofLp (colourSplit c) := rfl

theorem colourPair_symmetric (c : symmetricSpace) :
    colourPair (c : C) = (symmetricUnitary c, 0) := by
  rw [colourPair_apply, SourceExchangeConnectorTransport.colourSplit_symmetric]

theorem colourPair_alternating (c : alternatingSpace) :
    colourPair (c : C) = (0, alternatingUnitary c) := by
  rw [colourPair_apply, SourceExchangeConnectorTransport.colourSplit_alternating]

def exchangeOperator : Module.End ℂ C := flip.toLinearEquiv.toLinearMap

private theorem exchange_sum_coordinates {E A B : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B) (F : Module.End ℂ E)
    (x y : E) (a : A) (b : B) (hx : F x = x) (hy : F y = -y)
    (hex : e x = (a, 0)) (hey : e y = (0, b)) :
    e (F (x + y)) = ((e (x + y)).1, -(e (x + y)).2) := by
  apply Prod.ext <;>
    simp only [map_add, hx, hy, map_neg, hex, hey, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg, zero_add, add_zero, neg_zero]

/-- Exchange has opposite signs on the two established source summands. -/
theorem colourPair_exchange (c : C) :
    colourPair (exchangeOperator c) = ((colourPair c).1, -(colourPair c).2) := by
  obtain ⟨⟨x, y⟩, rfl⟩ := sumEquiv.surjective c
  simpa only [sumEquiv_apply] using
    exchange_sum_coordinates colourPair exchangeOperator (x : C) (y : C)
      (symmetricUnitary x) (alternatingUnitary y)
      ((mem_symmetricSpace x).mp x.property) ((mem_alternatingSpace y).mp y.property)
      (colourPair_symmetric x) (colourPair_alternating y)

theorem exchangeOperator_pair (x : W × L) :
    exchangeOperator (colourPair.symm x) = colourPair.symm (x.1, -x.2) := by
  apply colourPair.injective
  simp only [colourPair_exchange, colourPair.apply_symm_apply]

-- Use the established coordinate identities below without unfolding the
-- underlying Haar-space realization of the exchange equivalence.
attribute [local irreducible] colourPair

/-- The exchange-preserving part of the algebra generated before splitting. -/
def retainedAlgebra : Subalgebra ℂ (Module.End ℂ C) :=
  SourcePreExchangeResponse.responseAlgebra ⊓
    Subalgebra.centralizer ℂ ({exchangeOperator} : Set (Module.End ℂ C))

theorem mem_retainedAlgebra (T : Module.End ℂ C) :
    T ∈ retainedAlgebra ↔ exchangeOperator * T = T * exchangeOperator := by
  change (T ∈ SourcePreExchangeResponse.responseAlgebra ∧
    T ∈ Subalgebra.centralizer ℂ ({exchangeOperator} : Set (Module.End ℂ C))) ↔ _
  simp only [
    SourcePreExchangeResponse.end_mem_responseAlgebra, true_and,
    Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

/-- Block operators transported through a fixed linear decomposition. -/
def pairBlockResponse {E A B : Type*}
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B) :
    (Module.End ℂ A × Module.End ℂ B) →ₐ[ℂ] Module.End ℂ E where
  toFun a :=
    { toFun := fun x => e.symm (a.1 (e x).1, a.2 (e x).2)
      map_add' := by intros; apply e.injective; simp
      map_smul' := by intros; apply e.injective; simp }
  map_zero' := by apply LinearMap.ext; intro x; simp
  map_one' := by apply LinearMap.ext; intro x; simp
  map_add' := by intros; apply LinearMap.ext; intro x; apply e.injective; simp
  map_mul' := by intros; apply LinearMap.ext; intro x; simp
  commutes' := by
    intro z
    apply LinearMap.ext
    intro x
    apply e.injective
    simp
    rfl

/-- Block operators transported back to the original source tensor square. -/
abbrev splitOperator : SplitColour →ₐ[ℂ] Module.End ℂ C :=
  pairBlockResponse (E := C) (A := W) (B := L) colourPair

private theorem pair_conjugate_apply {E A B : Type*}
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B)
    (a : Module.End ℂ A × Module.End ℂ B) (x : E) :
    e (pairBlockResponse e a x) =
      (a.1 (e x).1, a.2 (e x).2) := by
  change e (e.symm _) = _
  exact e.apply_symm_apply _

private theorem pair_operators_commute {E A B : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B)
    (F T : Module.End ℂ E) (a : Module.End ℂ A × Module.End ℂ B)
    (hF : ∀ x, e (F x) = ((e x).1, -(e x).2))
    (hT : ∀ x, e (T x) = (a.1 (e x).1, a.2 (e x).2)) : F * T = T * F := by
  apply LinearMap.ext
  intro x
  apply e.injective
  change e (F (T x)) = e (T (F x))
  simp only [hF, hT, map_neg]

theorem colourPair_splitOperator (a : SplitColour) (c : C) :
    colourPair (splitOperator a c) =
      (a.1 (colourPair c).1, a.2 (colourPair c).2) := by
  exact colourPair.apply_symm_apply (a.1 (colourPair c).1, a.2 (colourPair c).2)

theorem splitOperator_mem (a : SplitColour) : splitOperator a ∈ retainedAlgebra := by
  exact (mem_retainedAlgebra _).mpr
    (pair_operators_commute (E := C) (A := W) (B := L)
      colourPair exchangeOperator (splitOperator a) a
      colourPair_exchange (colourPair_splitOperator a))

theorem splitOperator_injective : Function.Injective splitOperator := by
  intro a b hab
  apply Prod.ext
  · apply LinearMap.ext
    intro w
    have h := congrArg (fun T : Module.End ℂ C =>
      (colourPair (T (colourPair.symm (w, 0)))).1) hab
    simpa only [colourPair_splitOperator, colourPair.apply_symm_apply] using h
  · apply LinearMap.ext
    intro l
    have h := congrArg (fun T : Module.End ℂ C =>
      (colourPair (T (colourPair.symm (0, l)))).2) hab
    simpa only [colourPair_splitOperator, colourPair.apply_symm_apply] using h

/-- The diagonal restrictions associated with a fixed linear decomposition. -/
def pairDiagonalResponse {E A B : Type*}
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B)
    (T : Module.End ℂ E) : Module.End ℂ A × Module.End ℂ B :=
  ({ toFun := fun a => (e (T (e.symm (a, 0)))).1
     map_add' := by
       intro a b
       have h : (a + b, (0 : B)) = (a, (0 : B)) + (b, 0) := by simp
       rw [h, map_add, map_add, map_add]
       rfl
     map_smul' := by
       intro z a
       have h : (z • a, (0 : B)) = z • (a, (0 : B)) := by simp
       rw [h, map_smul, map_smul, map_smul]
       rfl },
   { toFun := fun b => (e (T (e.symm (0, b)))).2
     map_add' := by
       intro a b
       have h : ((0 : A), a + b) = ((0 : A), a) + (0, b) := by simp
       rw [h, map_add, map_add, map_add]
       rfl
     map_smul' := by
       intro z b
       have h : ((0 : A), z • b) = z • ((0 : A), b) := by simp
       rw [h, map_smul, map_smul, map_smul]
       rfl })

/-- Restrictions in the two exchange coordinates of an arbitrary source map. -/
abbrev diagonalBlocks (T : Module.End ℂ C) : SplitColour :=
  pairDiagonalResponse (E := C) (A := W) (B := L) colourPair T

private theorem pair_restriction_fst {E A B : Type*}
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B) (T : Module.End ℂ E) (a : A) :
    (pairDiagonalResponse e T).1 a =
      (e (T (e.symm (a, 0)))).1 := rfl

private theorem pair_restriction_snd {E A B : Type*}
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid A] [Module ℂ A]
    [AddCommMonoid B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B) (T : Module.End ℂ E) (b : B) :
    (pairDiagonalResponse e T).2 b =
      (e (T (e.symm (0, b)))).2 := rfl

theorem diagonalBlocks_fst_apply (T : Module.End ℂ C) (w : W) :
    (diagonalBlocks T).1 w = (colourPair (T (colourPair.symm (w, 0)))).1 := by
  rfl

theorem diagonalBlocks_snd_apply (T : Module.End ℂ C) (l : L) :
    (diagonalBlocks T).2 l = (colourPair (T (colourPair.symm (0, l)))).2 := by
  rfl

private theorem eq_zero_of_neg_eq_self {V : Type*} [AddCommGroup V] [Module ℂ V]
    {v : V} (h : -v = v) : v = 0 := by
  have hz : (2 : ℂ) • v = 0 := by
    calc
      (2 : ℂ) • v = v + v := by module
      _ = -v + v := congrArg (fun x => x + v) h.symm
      _ = 0 := neg_add_cancel v
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

private theorem commuting_involution_blocks {E A B : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B) (F T : Module.End ℂ E)
    (hF : ∀ x, e (F x) = ((e x).1, -(e x).2)) (hcomm : F * T = T * F) :
    (∀ a : A, (e (T (e.symm (a, 0)))).2 = 0) ∧
    (∀ b : B, (e (T (e.symm (0, b)))).1 = 0) ∧
    (∀ c : E, e (T c) = ((e (T (e.symm ((e c).1, 0)))).1,
      (e (T (e.symm (0, (e c).2)))).2)) := by
  have comm_at (x : E) : F (T x) = T (F x) := LinearMap.congr_fun hcomm x
  have hleft (a : A) : (e (T (e.symm (a, 0)))).2 = 0 := by
    have hFx : F (e.symm (a, 0)) = e.symm (a, 0) := by
      apply e.injective
      simp [hF]
    have hc := congrArg (fun x : E => (e x).2) (comm_at (e.symm (a, 0)))
    apply eq_zero_of_neg_eq_self
    simpa [hF, hFx] using hc
  have hright (b : B) : (e (T (e.symm (0, b)))).1 = 0 := by
    have hFx : F (e.symm (0, b)) = -e.symm (0, b) := by
      apply e.injective
      simp [hF]
    have hc := congrArg (fun x : E => (e x).1) (comm_at (e.symm (0, b)))
    apply eq_zero_of_neg_eq_self
    simpa [hF, hFx] using hc.symm
  refine ⟨hleft, hright, ?_⟩
  intro c
  have hsplit : c = e.symm ((e c).1, 0) + e.symm (0, (e c).2) := by
    apply e.injective
    apply Prod.ext <;> simp
  calc
    e (T c) = e (T (e.symm ((e c).1, 0) + e.symm (0, (e c).2))) :=
      congrArg (fun x : E => e (T x)) hsplit
    _ = e (T (e.symm ((e c).1, 0))) + e (T (e.symm (0, (e c).2))) := by
      rw [map_add, map_add]
    _ = ((e (T (e.symm ((e c).1, 0)))).1,
        (e (T (e.symm (0, (e c).2)))).2) := by
      apply Prod.ext <;> simp [hleft, hright]

private theorem end_eq_of_coordinates {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (A B : Module.End ℂ E)
    (h : ∀ x, e (A x) = e (B x)) : A = B :=
  LinearMap.ext (fun x => e.injective (h x))

private theorem pairBlockResponse_diagonal {E A B : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : E ≃ₗ[ℂ] A × B) (F T : Module.End ℂ E)
    (hF : ∀ x, e (F x) = ((e x).1, -(e x).2)) (hcomm : F * T = T * F) :
    pairBlockResponse e (pairDiagonalResponse e T) = T := by
  have hblocks := (commuting_involution_blocks e F T hF hcomm).2.2
  apply end_eq_of_coordinates e
  intro c
  exact (pair_conjugate_apply e (pairDiagonalResponse e T) c).trans
    ((congrArg₂ Prod.mk (pair_restriction_fst e T (e c).1)
      (pair_restriction_snd e T (e c).2)).trans (hblocks c).symm)

/-- Every retained source response is its two diagonal restrictions. -/
theorem splitOperator_diagonalBlocks (T : Module.End ℂ C)
    (hT : T ∈ retainedAlgebra) : splitOperator (diagonalBlocks T) = T := by
  simpa only [splitOperator, diagonalBlocks] using!
    (pairBlockResponse_diagonal (E := C) (A := W) (B := L)
      colourPair exchangeOperator T colourPair_exchange ((mem_retainedAlgebra T).mp hT))

theorem mem_retainedAlgebra_iff_existsUnique (T : Module.End ℂ C) :
    T ∈ retainedAlgebra ↔ ∃! a : SplitColour, splitOperator a = T := by
  constructor
  · intro hT
    refine ⟨diagonalBlocks T, splitOperator_diagonalBlocks T hT, ?_⟩
    intro a ha
    exact splitOperator_injective (ha.trans (splitOperator_diagonalBlocks T hT).symm)
  · rintro ⟨a, rfl, _⟩
    exact splitOperator_mem a

theorem splitOperator_range : splitOperator.range = retainedAlgebra := by
  ext T
  change (∃ a, splitOperator a = T) ↔ T ∈ retainedAlgebra
  constructor
  · rintro ⟨a, rfl⟩
    exact splitOperator_mem a
  · intro hT
    exact ⟨diagonalBlocks T, splitOperator_diagonalBlocks T hT⟩

def splitToRetained : SplitColour →ₐ[ℂ] retainedAlgebra :=
  splitOperator.codRestrict retainedAlgebra splitOperator_mem

theorem splitToRetained_bijective : Function.Bijective splitToRetained := by
  constructor
  · intro a b h
    exact splitOperator_injective (congrArg Subtype.val h)
  · intro T
    refine ⟨diagonalBlocks T, ?_⟩
    apply Subtype.ext
    exact splitOperator_diagonalBlocks T T.property

/-- Algebra equivalence obtained from the actual source exchange coordinates. -/
def retainedEquiv : retainedAlgebra ≃ₐ[ℂ] SplitColour :=
  (AlgEquiv.ofBijective splitToRetained splitToRetained_bijective).symm

private theorem tensor_left_apply {E F : Type*}
    [AddCommMonoid E] [Module ℂ E] [AddCommMonoid F] [Module ℂ F]
    (A : Module.End ℂ E) (x : E) (y : F) :
    TensorProduct.map A (1 : Module.End ℂ F) (x ⊗ₜ[ℂ] y) = A x ⊗ₜ[ℂ] y := by
  simp only [TensorProduct.map_tmul, Module.End.one_apply]

private theorem source_colourAction_tmul (A : Module.End ℂ C) (c : C) (s : S) :
    SourcePreExchangeResponse.colourAction A (c ⊗ₜ[ℂ] s) = A c ⊗ₜ[ℂ] s := by
  dsimp only [SourcePreExchangeResponse.colourAction, AlgHom.coe_mk,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  exact tensor_left_apply (E := C) (F := S) A c s

private theorem tensor_intertwines_of_tmul {E F G : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G] (u : E ⊗[ℂ] F →ₗ[ℂ] G)
    (A : Module.End ℂ (E ⊗[ℂ] F)) (B : Module.End ℂ G)
    (h : ∀ x y, u (A (x ⊗ₜ[ℂ] y)) = B (u (x ⊗ₜ[ℂ] y))) (z : E ⊗[ℂ] F) :
    u (A z) = B (u z) := by
  have he : u.comp A = B.comp u := by
    apply TensorProduct.ext'
    exact h
  exact LinearMap.congr_fun he z

private theorem exchangeUnitary_pair_tmul (c : C) (s : S) :
    WithLp.ofLp (exchangeUnitary (c ⊗ₜ[ℂ] s)) =
      ((colourPair c).1 ⊗ₜ[ℂ] s, (colourPair c).2 ⊗ₜ[ℂ] s) := by
  rw [colourPair_apply]
  exact SourceExchangeConnectorTransport.exchangeUnitary_tmul c s

private theorem source_colour_tmul_coordinates (a : SplitColour) (c : C) (s : S) :
    WithLp.ofLp (SourceMinimalRepresentation.sourceCarrierRepresentation
      (SourceJointResponse.colourResponse a) (exchangeUnitary (c ⊗ₜ[ℂ] s))) =
      (a.1 (colourPair c).1 ⊗ₜ[ℂ] s, a.2 (colourPair c).2 ⊗ₜ[ℂ] s) := by
  exact (SourceMinimalRepresentation.sourceCarrierRepresentation_apply
      (SourceJointResponse.colourResponse a) (exchangeUnitary (c ⊗ₜ[ℂ] s))).trans
    ((congrArg (fun p : (W ⊗[ℂ] S) × (L ⊗[ℂ] S) =>
        ((SourceJointResponse.colourResponse a).1 p.1,
          (SourceJointResponse.colourResponse a).2 p.2))
      (exchangeUnitary_pair_tmul c s)).trans
      (Prod.ext (tensor_left_apply a.1 (colourPair c).1 s)
        (tensor_left_apply a.2 (colourPair c).2 s)))

/-- The retained source operators act as the existing joint-colour responses. -/
theorem exchangeUnitary_colourAction (a : SplitColour) (x : FullCarrier) :
    exchangeUnitary (SourcePreExchangeResponse.colourAction (splitOperator a) x) =
      SourceMinimalRepresentation.sourceCarrierRepresentation
        (SourceJointResponse.colourResponse a) (exchangeUnitary x) := by
  refine tensor_intertwines_of_tmul (E := C) (F := S) (G := SourceCarrier)
    exchangeUnitary.toLinearEquiv.toLinearMap
    (SourcePreExchangeResponse.colourAction (splitOperator a))
    (SourceMinimalRepresentation.sourceCarrierRepresentation
      (SourceJointResponse.colourResponse a)) ?_ x
  intro c s
  apply WithLp.ofLp_injective 2
  have ht : SourcePreExchangeResponse.colourAction (splitOperator a) (c ⊗ₜ[ℂ] s) =
      splitOperator a c ⊗ₜ[ℂ] s := source_colourAction_tmul (splitOperator a) c s
  have hl := (congrArg (fun y : FullCarrier => WithLp.ofLp (exchangeUnitary y)) ht).trans
    (exchangeUnitary_pair_tmul (splitOperator a c) s)
  exact hl.trans
    ((congrArg (fun p : W × L => (p.1 ⊗ₜ[ℂ] s, p.2 ⊗ₜ[ℂ] s))
      (colourPair_splitOperator a c)).trans (source_colour_tmul_coordinates a c s).symm)

theorem operatorTransport_colourAction (a : SplitColour) :
    operatorTransport (SourcePreExchangeResponse.colourAction (splitOperator a)) =
      SourceMinimalRepresentation.sourceCarrierRepresentation
        (SourceJointResponse.colourResponse a) := by
  apply LinearMap.ext
  intro y
  exact (SourceExchangeConnectorTransport.operatorTransport_apply
    (SourcePreExchangeResponse.colourAction (splitOperator a)) y).trans
    ((exchangeUnitary_colourAction a (exchangeUnitary.symm y)).trans
      (congrArg (SourceMinimalRepresentation.sourceCarrierRepresentation
        (SourceJointResponse.colourResponse a)) (exchangeUnitary.apply_symm_apply y)))

/-- Algebra classification and its action on the common source carrier. -/
structure SplitConclusions : Prop where
  response_range : splitOperator.range = retainedAlgebra
  response_unique : ∀ T : Module.End ℂ C,
    T ∈ retainedAlgebra ↔ ∃! a : SplitColour, splitOperator a = T
  tensor_intertwining : ∀ (a : SplitColour) (x : FullCarrier),
    exchangeUnitary (SourcePreExchangeResponse.colourAction (splitOperator a) x) =
      SourceMinimalRepresentation.sourceCarrierRepresentation
        (SourceJointResponse.colourResponse a) (exchangeUnitary x)

theorem generated_split : SplitConclusions :=
  ⟨splitOperator_range, mem_retainedAlgebra_iff_existsUnique,
    exchangeUnitary_colourAction⟩

end GeneratedFoundations.Physical.SourceSplitResponse
