module

public import GeneratedFoundations.Geometry.SourceClebschGordan
public import GeneratedFoundations.Geometry.SourceSymmetricUnitary
public import GeneratedFoundations.Geometry.SourceIrreducibleClassification
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Tactic.Module

/-!
# Symmetric and alternating source tensors

The degree-zero Clebsch–Gordan summand is identified with the actual
negative eigenspace of tensor-factor exchange.  The degree-two summand
is its positive eigenspace.  These identifications use the polynomial
splitting and its inverse, not a dimension comparison.

On the existing Haar Hilbert realization, exchange is unitary and the
two eigenspaces form an orthogonal Hilbert sum.  They are unitarily
identified with the degree-two and degree-zero sources.  The degree-two
identification uses the proved positive Gram normalization of the actual
Clebsch–Gordan intertwiner, rather than assuming that its original scale
preserves the inner product.
-/

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct
open Module MvPolynomial
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceClebschGordan

namespace GeneratedFoundations.Geometry.SourceQuadraticSplit

abbrev PolynomialTensor := Carrier 1 ⊗[ℂ] Carrier 1
abbrev Spin := HilbertCarrier 1
abbrev TensorSquare := Spin ⊗[ℂ] Spin

def polynomialFlip : PolynomialTensor ≃ₗ[ℂ] PolynomialTensor :=
  TensorProduct.comm ℂ (Carrier 1) (Carrier 1)

abbrev polynomialSplit := clebschGordanLinear 0

/-- Tensor exchange has the asserted signs on the actual polynomial
Clebsch–Gordan components. -/
theorem polynomialSplit_flip (t : PolynomialTensor) :
    polynomialSplit (polynomialFlip t) =
      ((polynomialSplit t).1, -(polynomialSplit t).2) := by
  have hmaps : polynomialSplit.toLinearMap.comp polynomialFlip.toLinearMap =
      (LinearMap.prodMap (LinearMap.id : Module.End ℂ (Carrier 2))
        (-LinearMap.id : Module.End ℂ (Carrier 0))).comp polynomialSplit.toLinearMap := by
    apply TensorProduct.ext'
    intro f g
    obtain ⟨v, rfl⟩ := degreeOneEquiv.surjective f
    obtain ⟨w, rfl⟩ := degreeOneEquiv.surjective g
    change splitPair 0 (tensorPairEquiv 1
        (degreeOnePolynomial w ⊗ₜ[ℂ] degreeOnePolynomial v)) =
      ((splitPair 0 (tensorPairEquiv 1
        (degreeOnePolynomial v ⊗ₜ[ℂ] degreeOnePolynomial w))).1,
       -(splitPair 0 (tensorPairEquiv 1
        (degreeOnePolynomial v ⊗ₜ[ℂ] degreeOnePolynomial w))).2)
    rw [tensorPairEquiv_tmul, tensorPairEquiv_tmul]
    apply Prod.ext <;> apply Subtype.ext
    · change X 0 * (w 0 • (degreeOnePolynomial v : PolynomialSpace)) +
          X 1 * (w 1 • (degreeOnePolynomial v : PolynomialSpace)) =
        X 0 * (v 0 • (degreeOnePolynomial w : PolynomialSpace)) +
          X 1 * (v 1 • (degreeOnePolynomial w : PolynomialSpace))
      simp only [degreeOnePolynomial, Fin.sum_univ_two, smul_eq_C_mul]
      ring
    · simp [splitPair, curlPair, derivative, degreeOnePolynomial,
        Fin.sum_univ_two, smul_eq_C_mul]
      ring
  exact LinearMap.congr_fun hmaps t

private theorem neg_eq_self_iff_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (v : V) :
    -v = v ↔ v = 0 := by
  constructor
  · intro h
    have hz : (2 : ℂ) • v = 0 := by
      calc
        (2 : ℂ) • v = v + v := by module
        _ = -v + v := congrArg (fun x => x + v) h.symm
        _ = 0 := neg_add_cancel v
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  · rintro rfl
    exact neg_zero

theorem polynomialFlip_fixed_iff (t : PolynomialTensor) :
    polynomialFlip t = t ↔ (polynomialSplit t).2 = 0 := by
  rw [← polynomialSplit.injective.eq_iff, polynomialSplit_flip]
  constructor
  · intro h
    exact (neg_eq_self_iff_zero _).mp (congrArg Prod.snd h)
  · intro h
    apply Prod.ext
    · rfl
    · simp only [h, neg_zero]

theorem polynomialFlip_negative_iff (t : PolynomialTensor) :
    polynomialFlip t = -t ↔ (polynomialSplit t).1 = 0 := by
  have hn : polynomialSplit (-t) = -polynomialSplit t := polynomialSplit.map_neg t
  rw [← polynomialSplit.injective.eq_iff, polynomialSplit_flip, hn]
  constructor
  · intro h
    exact (neg_eq_self_iff_zero _).mp (congrArg Prod.fst h).symm
  · intro h
    apply Prod.ext
    · simp only [h, neg_zero, Prod.fst_neg]
    · rfl

/-- The established Haar realization, applied to both tensor factors. -/
def tensorRealization : PolynomialTensor ≃ₗ[ℂ] TensorSquare :=
  TensorProduct.congr (carrierEquiv 1) (carrierEquiv 1)

def flip : TensorSquare ≃ₗᵢ[ℂ] TensorSquare :=
  TensorProduct.commIsometry ℂ Spin Spin

theorem tensorRealization_flip (t : PolynomialTensor) :
    tensorRealization (polynomialFlip t) = flip (tensorRealization t) := by
  induction t using TensorProduct.inductionOn with
  | tmul p q => rfl
  | add t u ht hu => simp only [map_add, ht, hu]

def hilbertSplit : TensorSquare ≃ₗ[ℂ] HilbertCarrier 2 × HilbertCarrier 0 :=
  tensorRealization.symm.trans
    (polynomialSplit.trans (LinearEquiv.prodCongr (carrierEquiv 2) (carrierEquiv 0)))

theorem hilbertSplit_realization (t : PolynomialTensor) :
    hilbertSplit (tensorRealization t) =
      (carrierEquiv 2 (polynomialSplit t).1, carrierEquiv 0 (polynomialSplit t).2) := by
  simp [hilbertSplit]

theorem hilbertSplit_flip (t : TensorSquare) :
    hilbertSplit (flip t) = ((hilbertSplit t).1, -(hilbertSplit t).2) := by
  obtain ⟨p, rfl⟩ := tensorRealization.surjective t
  rw [← tensorRealization_flip, hilbertSplit_realization, polynomialSplit_flip,
    hilbertSplit_realization]
  simp only [map_neg]

def symmetricSpace : Submodule ℂ TensorSquare := by
  exact Module.End.eigenspace (R := ℂ) (M := TensorSquare)
    (by exact flip.toLinearEquiv.toLinearMap) 1

/-- In characteristic zero the alternating square is realized as the
negative eigenspace of exchange in the actual tensor product. -/
def alternatingSpace : Submodule ℂ TensorSquare := by
  exact Module.End.eigenspace (R := ℂ) (M := TensorSquare)
    (by exact flip.toLinearEquiv.toLinearMap) (-1)

instance symmetricSpaceNormed : NormedAddCommGroup symmetricSpace := by
  exact Submodule.normedAddCommGroup (𝕜 := ℂ) (E := TensorSquare) (by exact symmetricSpace)

instance alternatingSpaceNormed : NormedAddCommGroup alternatingSpace := by
  exact Submodule.normedAddCommGroup (𝕜 := ℂ) (E := TensorSquare) (by exact alternatingSpace)

instance symmetricSpaceInner : InnerProductSpace ℂ symmetricSpace := by
  exact Submodule.innerProductSpace (𝕜 := ℂ) (E := TensorSquare) (by exact symmetricSpace)

instance alternatingSpaceInner : InnerProductSpace ℂ alternatingSpace := by
  exact Submodule.innerProductSpace (𝕜 := ℂ) (E := TensorSquare) (by exact alternatingSpace)

theorem mem_symmetricSpace (t : TensorSquare) :
    t ∈ symmetricSpace ↔ flip t = t := by
  simp only [symmetricSpace, Module.End.mem_eigenspace_iff, one_smul]
  rfl

theorem mem_alternatingSpace (t : TensorSquare) :
    t ∈ alternatingSpace ↔ flip t = -t := by
  simp only [alternatingSpace, Module.End.mem_eigenspace_iff, neg_one_smul]
  rfl

theorem symmetricSpace_iff_component_zero (t : TensorSquare) :
    t ∈ symmetricSpace ↔ (hilbertSplit t).2 = 0 := by
  rw [mem_symmetricSpace, ← hilbertSplit.injective.eq_iff, hilbertSplit_flip]
  constructor
  · intro h
    exact (neg_eq_self_iff_zero _).mp (congrArg Prod.snd h)
  · intro h
    apply Prod.ext
    · rfl
    · simp only [h, neg_zero]

theorem alternatingSpace_iff_component_zero (t : TensorSquare) :
    t ∈ alternatingSpace ↔ (hilbertSplit t).1 = 0 := by
  have hn : hilbertSplit (-t) = -hilbertSplit t := hilbertSplit.map_neg t
  rw [mem_alternatingSpace, ← hilbertSplit.injective.eq_iff, hilbertSplit_flip, hn]
  constructor
  · intro h
    exact (neg_eq_self_iff_zero _).mp (congrArg Prod.fst h).symm
  · intro h
    apply Prod.ext
    · simp only [h, neg_zero, Prod.fst_neg]
    · rfl

/-- Restriction of the actual Clebsch–Gordan map, with its explicit inverse. -/
def symmetricEquiv : symmetricSpace ≃ₗ[ℂ] HilbertCarrier 2 where
  toFun x := (hilbertSplit x).1
  map_add' x y := by simp only [Submodule.coe_add, map_add, Prod.fst_add]
  map_smul' c x := by simp only [Submodule.coe_smul, map_smul, Prod.smul_fst, RingHom.id_apply]
  invFun p := ⟨hilbertSplit.symm (p, 0), by
    rw [symmetricSpace_iff_component_zero, hilbertSplit.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply hilbertSplit.injective
    rw [hilbertSplit.apply_symm_apply]
    exact Prod.ext rfl ((symmetricSpace_iff_component_zero x).mp x.property).symm
  right_inv p := congrArg Prod.fst (hilbertSplit.apply_symm_apply (p, 0))

def alternatingEquiv : alternatingSpace ≃ₗ[ℂ] HilbertCarrier 0 where
  toFun x := (hilbertSplit x).2
  map_add' x y := by simp only [Submodule.coe_add, map_add, Prod.snd_add]
  map_smul' c x := by simp only [Submodule.coe_smul, map_smul, Prod.smul_snd, RingHom.id_apply]
  invFun p := ⟨hilbertSplit.symm (0, p), by
    rw [alternatingSpace_iff_component_zero, hilbertSplit.apply_symm_apply]⟩
  left_inv x := by
    apply Subtype.ext
    apply hilbertSplit.injective
    rw [hilbertSplit.apply_symm_apply]
    exact Prod.ext ((alternatingSpace_iff_component_zero x).mp x.property).symm rfl
  right_inv p := congrArg Prod.snd (hilbertSplit.apply_symm_apply (0, p))

instance symmetricSpaceFiniteDimensional : FiniteDimensional ℂ symmetricSpace :=
  symmetricEquiv.symm.finiteDimensional

instance alternatingSpaceFiniteDimensional : FiniteDimensional ℂ alternatingSpace :=
  alternatingEquiv.symm.finiteDimensional

theorem symmetricSpace_finrank : Module.finrank ℂ symmetricSpace = 3 := by
  rw [symmetricEquiv.finrank_eq, hilbertCarrier_finrank]

theorem alternatingSpace_finrank : Module.finrank ℂ alternatingSpace = 1 := by
  rw [alternatingEquiv.finrank_eq, hilbertCarrier_finrank]

def tensorAction (U : SU2) : TensorSquare ≃ₗᵢ[ℂ] TensorSquare :=
  TensorProduct.congrIsometry (unitaryAction 1 U) (unitaryAction 1 U)

theorem tensorAction_realization (U : SU2) (t : PolynomialTensor) :
    tensorAction U (tensorRealization t) = tensorRealization
      (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U t) := by
  induction t using TensorProduct.inductionOn with
  | tmul p q =>
      change unitaryAction 1 U (carrierEquiv 1 p) ⊗ₜ[ℂ]
          unitaryAction 1 U (carrierEquiv 1 q) =
        carrierEquiv 1 (sourceRepresentation 1 U p) ⊗ₜ[ℂ]
          carrierEquiv 1 (sourceRepresentation 1 U q)
      rw [unitaryAction_apply_carrier, unitaryAction_apply_carrier]
  | add t u ht hu => simp only [map_add, ht, hu]

theorem polynomialSplit_intertwines (U : SU2) (p : PolynomialTensor) :
    polynomialSplit (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p) =
      (sourceRepresentation 2 U (polynomialSplit p).1,
        sourceRepresentation 0 U (polynomialSplit p).2) := by
  change splitPair 0 (tensorPairEquiv 1
      (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)) =
    (sourceRepresentation 2 U (splitPair 0 (tensorPairEquiv 1 p)).1,
      sourceRepresentation 0 U (splitPair 0 (tensorPairEquiv 1 p)).2)
  rw [tensorPairEquiv_intertwines, splitPair_intertwines]

theorem hilbertSplit_tensorAction_realization (U : SU2) (p : PolynomialTensor) :
    hilbertSplit (tensorAction U (tensorRealization p)) =
      (carrierEquiv 2 (polynomialSplit
        (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).1,
       carrierEquiv 0 (polynomialSplit
        (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).2) := by
  calc
    _ = hilbertSplit (tensorRealization
        (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)) :=
      congrArg hilbertSplit (tensorAction_realization U p)
    _ = (carrierEquiv 2 (polynomialSplit
          (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).1,
        carrierEquiv 0 (polynomialSplit
          (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).2) :=
      hilbertSplit_realization _

theorem polynomialSplit_intertwines_fst (U : SU2) (p : PolynomialTensor) :
    (polynomialSplit (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).1 =
      sourceRepresentation 2 U (polynomialSplit p).1 :=
  congrArg Prod.fst (polynomialSplit_intertwines U p)

theorem polynomialSplit_intertwines_snd (U : SU2) (p : PolynomialTensor) :
    (polynomialSplit (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).2 =
      sourceRepresentation 0 U (polynomialSplit p).2 :=
  congrArg Prod.snd (polynomialSplit_intertwines U p)

theorem polynomialSplit_action_carrier_fst (U : SU2) (p : PolynomialTensor) :
    carrierEquiv 2 (polynomialSplit
      (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).1 =
      unitaryAction 2 U (carrierEquiv 2 (polynomialSplit p).1) := by
  calc
    _ = carrierEquiv 2 (sourceRepresentation 2 U (polynomialSplit p).1) :=
      congrArg (carrierEquiv 2 : Carrier 2 → HilbertCarrier 2)
        (polynomialSplit_intertwines_fst U p)
    _ = _ := (unitaryAction_apply_carrier 2 U (polynomialSplit p).1).symm

theorem polynomialSplit_action_carrier_snd (U : SU2) (p : PolynomialTensor) :
    carrierEquiv 0 (polynomialSplit
      (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).2 =
      unitaryAction 0 U (carrierEquiv 0 (polynomialSplit p).2) := by
  calc
    _ = carrierEquiv 0 (sourceRepresentation 0 U (polynomialSplit p).2) :=
      congrArg (carrierEquiv 0 : Carrier 0 → HilbertCarrier 0)
        (polynomialSplit_intertwines_snd U p)
    _ = _ := (unitaryAction_apply_carrier 0 U (polynomialSplit p).2).symm

theorem polynomialSplit_action_carrier (U : SU2) (p : PolynomialTensor) :
    (carrierEquiv 2 (polynomialSplit
        (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).1,
      carrierEquiv 0 (polynomialSplit
        (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).2) =
      (unitaryAction 2 U (carrierEquiv 2 (polynomialSplit p).1),
        unitaryAction 0 U (carrierEquiv 0 (polynomialSplit p).2)) :=
  Prod.ext (polynomialSplit_action_carrier_fst U p) (polynomialSplit_action_carrier_snd U p)

theorem hilbertSplit_intertwines_realization (U : SU2) (p : PolynomialTensor) :
    hilbertSplit (tensorAction U (tensorRealization p)) =
      (unitaryAction 2 U (hilbertSplit (tensorRealization p)).1,
        unitaryAction 0 U (hilbertSplit (tensorRealization p)).2) := by
  apply Prod.ext
  · calc
      _ = carrierEquiv 2 (polynomialSplit
          (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).1 :=
        congrArg Prod.fst (hilbertSplit_tensorAction_realization U p)
      _ = unitaryAction 2 U (carrierEquiv 2 (polynomialSplit p).1) :=
        polynomialSplit_action_carrier_fst U p
      _ = _ := congrArg (unitaryAction 2 U : HilbertCarrier 2 → HilbertCarrier 2)
        (congrArg Prod.fst (hilbertSplit_realization p)).symm
  · calc
      _ = carrierEquiv 0 (polynomialSplit
          (((sourceRepresentation 1).tprod (sourceRepresentation 1)) U p)).2 :=
        congrArg Prod.snd (hilbertSplit_tensorAction_realization U p)
      _ = unitaryAction 0 U (carrierEquiv 0 (polynomialSplit p).2) :=
        polynomialSplit_action_carrier_snd U p
      _ = _ := congrArg (unitaryAction 0 U : HilbertCarrier 0 → HilbertCarrier 0)
        (congrArg Prod.snd (hilbertSplit_realization p)).symm

theorem hilbertSplit_intertwines (U : SU2) (t : TensorSquare) :
    hilbertSplit (tensorAction U t) =
      (unitaryAction 2 U (hilbertSplit t).1, unitaryAction 0 U (hilbertSplit t).2) := by
  obtain ⟨p, rfl⟩ := tensorRealization.surjective t
  exact hilbertSplit_intertwines_realization U p

theorem symmetricSpace_invariant (U : SU2) {t : TensorSquare} (ht : t ∈ symmetricSpace) :
    tensorAction U t ∈ symmetricSpace := by
  rw [symmetricSpace_iff_component_zero, hilbertSplit_intertwines]
  rw [(symmetricSpace_iff_component_zero t).mp ht, map_zero]

theorem alternatingSpace_invariant (U : SU2) {t : TensorSquare}
    (ht : t ∈ alternatingSpace) : tensorAction U t ∈ alternatingSpace := by
  rw [alternatingSpace_iff_component_zero, hilbertSplit_intertwines]
  rw [(alternatingSpace_iff_component_zero t).mp ht, map_zero]

theorem symmetricEquiv_intertwines (U : SU2) (x : symmetricSpace) :
    symmetricEquiv ⟨tensorAction U x, symmetricSpace_invariant U x.property⟩ =
      unitaryAction 2 U (symmetricEquiv x) :=
  congrArg Prod.fst (hilbertSplit_intertwines U x)

theorem alternatingEquiv_intertwines (U : SU2) (x : alternatingSpace) :
    alternatingEquiv ⟨tensorAction U x, alternatingSpace_invariant U x.property⟩ =
      unitaryAction 0 U (alternatingEquiv x) :=
  congrArg Prod.snd (hilbertSplit_intertwines U x)

def symmetricLinearAction (U : SU2) : symmetricSpace ≃ₗ[ℂ] symmetricSpace :=
  symmetricEquiv.trans ((unitaryAction 2 U).toLinearEquiv.trans symmetricEquiv.symm)

private theorem symmetricLinearAction_apply (U : SU2) (x : symmetricSpace) :
    symmetricLinearAction U x =
      ⟨tensorAction U x, symmetricSpace_invariant U x.property⟩ := by
  apply symmetricEquiv.injective
  change symmetricEquiv (symmetricEquiv.symm (unitaryAction 2 U (symmetricEquiv x))) = _
  rw [symmetricEquiv.apply_symm_apply]
  exact (symmetricEquiv_intertwines U x).symm

/-- The actual tensor action restricted to the positive exchange eigenspace,
with the inherited tensor norm. -/
def symmetricAction (U : SU2) : symmetricSpace ≃ₗᵢ[ℂ] symmetricSpace where
  toLinearEquiv := symmetricLinearAction U
  norm_map' x := by
    change ‖symmetricLinearAction U x‖ = ‖x‖
    rw [symmetricLinearAction_apply]
    exact (tensorAction U).norm_map (x : TensorSquare)

theorem symmetricAction_apply (U : SU2) (x : symmetricSpace) :
    symmetricAction U x =
      ⟨tensorAction U x, symmetricSpace_invariant U x.property⟩ :=
  symmetricLinearAction_apply U x

theorem symmetricAction_equiv (U : SU2) (x : symmetricSpace) :
    symmetricEquiv (symmetricAction U x) = unitaryAction 2 U (symmetricEquiv x) :=
  symmetricEquiv.apply_symm_apply _

private theorem unitaryAction_one_apply (m : ℕ) (p : HilbertCarrier m) :
    unitaryAction m 1 p = p :=
  congrArg (fun e : HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m => e p)
    (unitaryRepresentation m).map_one

private theorem unitaryAction_mul_apply (m : ℕ) (U V : SU2) (p : HilbertCarrier m) :
    unitaryAction m (U * V) p = unitaryAction m U (unitaryAction m V p) :=
  congrArg (fun e : HilbertCarrier m ≃ₗᵢ[ℂ] HilbertCarrier m => e p)
    ((unitaryRepresentation m).map_mul U V)

theorem symmetricAction_one_apply (x : symmetricSpace) : symmetricAction 1 x = x := by
  apply symmetricEquiv.injective
  exact (symmetricAction_equiv 1 x).trans (unitaryAction_one_apply 2 (symmetricEquiv x))

theorem symmetricAction_mul_apply (U V : SU2) (x : symmetricSpace) :
    symmetricAction (U * V) x = symmetricAction U (symmetricAction V x) := by
  apply symmetricEquiv.injective
  calc
    _ = unitaryAction 2 (U * V) (symmetricEquiv x) := symmetricAction_equiv (U * V) x
    _ = unitaryAction 2 U (unitaryAction 2 V (symmetricEquiv x)) :=
      unitaryAction_mul_apply 2 U V (symmetricEquiv x)
    _ = unitaryAction 2 U (symmetricEquiv (symmetricAction V x)) :=
      congrArg (unitaryAction 2 U : HilbertCarrier 2 → HilbertCarrier 2)
        (symmetricAction_equiv V x).symm
    _ = _ := (symmetricAction_equiv U (symmetricAction V x)).symm

def symmetricRepresentation : SU2 →* (symmetricSpace ≃ₗᵢ[ℂ] symmetricSpace) where
  toFun := symmetricAction
  map_one' := LinearIsometryEquiv.ext symmetricAction_one_apply
  map_mul' U V := LinearIsometryEquiv.ext (symmetricAction_mul_apply U V)

/-- The inverse of the explicit Clebsch–Gordan restriction, before its
positive normalization. -/
def symmetricIntertwiner : Representation.IntertwiningMap
    (SourceSymmetricIrreducible.hilbertRepresentation 2)
    (SourceIrreducibleClassification.linearRepresentation symmetricRepresentation) where
  toLinearMap := symmetricEquiv.symm.toLinearMap
  isIntertwining' U := by
    apply LinearMap.ext
    intro p
    apply symmetricEquiv.injective
    change symmetricEquiv (symmetricEquiv.symm (unitaryAction 2 U p)) =
      symmetricEquiv (symmetricAction U (symmetricEquiv.symm p))
    rw [symmetricEquiv.apply_symm_apply, symmetricAction_equiv,
      symmetricEquiv.apply_symm_apply]

theorem symmetric_unitary_exists : Nonempty
    (SourceIrreducibleClassification.UnitaryIntertwiner symmetricRepresentation 2) :=
  SourceIrreducibleClassification.unitaryIntertwiner_of_bijective
    symmetricRepresentation symmetricIntertwiner symmetricEquiv.symm.bijective

/-- A unitary version of the same degree-two correspondence, obtained from
the Gram normalization theorem on the inherited Hilbert structures. -/
def symmetricUnitary : symmetricSpace ≃ₗᵢ[ℂ] HilbertCarrier 2 :=
  (Classical.choice symmetric_unitary_exists).val.symm

private theorem unitaryIntertwiner_inverse_intertwines
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)) (m : ℕ)
    (E : SourceIrreducibleClassification.UnitaryIntertwiner ρ m)
    (U : SU2) (x : H) :
    E.val.symm (ρ U x) = unitaryAction m U (E.val.symm x) := by
  apply E.val.injective
  calc
    _ = ρ U x := E.val.apply_symm_apply (ρ U x)
    _ = ρ U (E.val (E.val.symm x)) :=
      congrArg (ρ U : H → H) (E.val.apply_symm_apply x).symm
    _ = _ := (E.property U (E.val.symm x)).symm

theorem symmetricUnitary_intertwines (U : SU2) (x : symmetricSpace) :
    symmetricUnitary ⟨tensorAction U x, symmetricSpace_invariant U x.property⟩ =
      unitaryAction 2 U (symmetricUnitary x) := by
  let E := Classical.choice symmetric_unitary_exists
  change E.val.symm ⟨tensorAction U x, symmetricSpace_invariant U x.property⟩ =
    unitaryAction 2 U (E.val.symm x)
  calc
    _ = E.val.symm (symmetricAction U x) :=
      congrArg (E.val.symm : symmetricSpace → HilbertCarrier 2)
        (symmetricAction_apply U x).symm
    _ = _ := unitaryIntertwiner_inverse_intertwines symmetricRepresentation 2 E U x

theorem degreeZero_unitaryAction (U : SU2) (p : HilbertCarrier 0) :
    unitaryAction 0 U p = p := by
  obtain ⟨q, rfl⟩ := (carrierEquiv 0).surjective p
  rw [unitaryAction_apply_carrier, source_degreeZero]

/-- Triviality is proved for the induced source action on the actual
alternating tensors, rather than attached as a new representation datum. -/
theorem alternating_source_fixed (U : SU2) (x : alternatingSpace) :
    tensorAction U (x : TensorSquare) = x := by
  apply hilbertSplit.injective
  rw [hilbertSplit_intertwines]
  apply Prod.ext
  · simp only [(alternatingSpace_iff_component_zero x).mp x.property, map_zero]
  · exact degreeZero_unitaryAction U _

theorem symmetric_alternating_inner (x : symmetricSpace) (y : alternatingSpace) :
    inner ℂ (x : TensorSquare) (y : TensorSquare) = 0 := by
  have h : inner ℂ (flip (x : TensorSquare)) (flip (y : TensorSquare)) =
      inner ℂ (x : TensorSquare) (y : TensorSquare) :=
    TensorProduct.inner_comm_comm (𝕜 := ℂ) _ _
  rw [(mem_symmetricSpace x).mp x.property, (mem_alternatingSpace y).mp y.property] at h
  exact (neg_eq_self_iff_zero _).mp
    ((inner_neg_right (𝕜 := ℂ) (x : TensorSquare) (y : TensorSquare)).symm.trans h)

/-- The linear sum map on the two actual subspaces. -/
def sumEquiv : (symmetricSpace × alternatingSpace) ≃ₗ[ℂ] TensorSquare :=
  (LinearEquiv.prodCongr symmetricEquiv alternatingEquiv).trans hilbertSplit.symm

theorem sumEquiv_apply (x : symmetricSpace) (y : alternatingSpace) :
    sumEquiv (x, y) = (x : TensorSquare) + (y : TensorSquare) := by
  apply hilbertSplit.injective
  change hilbertSplit (hilbertSplit.symm (symmetricEquiv x, alternatingEquiv y)) = _
  rw [hilbertSplit.apply_symm_apply, map_add]
  apply Prod.ext
  · change (hilbertSplit x).1 = (hilbertSplit x).1 + (hilbertSplit y).1
    have hy : (hilbertSplit (y : TensorSquare)).1 = 0 :=
      (alternatingSpace_iff_component_zero y).mp y.property
    exact ((congrArg (fun v : HilbertCarrier 2 => (hilbertSplit x).1 + v) hy).trans
      (add_zero _)).symm
  · change (hilbertSplit y).2 = (hilbertSplit x).2 + (hilbertSplit y).2
    have hx : (hilbertSplit (x : TensorSquare)).2 = 0 :=
      (symmetricSpace_iff_component_zero x).mp x.property
    exact ((congrArg (fun v : HilbertCarrier 0 => v + (hilbertSplit y).2) hx).trans
      (zero_add _)).symm

private theorem inner_add_of_cross_zero {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (a b c d : E)
    (had : inner ℂ a d = 0) (hbc : inner ℂ b c = 0) :
    inner ℂ (a + b) (c + d) = inner ℂ a c + inner ℂ b d := by
  simp only [inner_add_left (𝕜 := ℂ), inner_add_right (𝕜 := ℂ), had, hbc,
    add_zero, zero_add]

theorem sumEquiv_inner (x y : symmetricSpace × alternatingSpace) :
    inner ℂ (sumEquiv x) (sumEquiv y) = inner ℂ x.1 y.1 + inner ℂ x.2 y.2 := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  calc
    _ = inner ℂ ((x₁ : TensorSquare) + (x₂ : TensorSquare))
        ((y₁ : TensorSquare) + (y₂ : TensorSquare)) :=
      congrArg₂ (fun a b : TensorSquare => inner ℂ a b)
        (sumEquiv_apply x₁ x₂) (sumEquiv_apply y₁ y₂)
    _ = _ := inner_add_of_cross_zero (x₁ : TensorSquare) (x₂ : TensorSquare)
      (y₁ : TensorSquare) (y₂ : TensorSquare) (symmetric_alternating_inner x₁ y₂)
      ((inner_eq_zero_symm (𝕜 := ℂ)).mpr (symmetric_alternating_inner y₁ x₂))

/-- Complete orthogonal Hilbert splitting with the inherited tensor inner
products on the two eigenspaces. -/
def orthogonalSum : WithLp 2 (symmetricSpace × alternatingSpace) ≃ₗᵢ[ℂ] TensorSquare := by
  refine LinearEquiv.isometryOfInner (𝕜 := ℂ)
    (E := WithLp 2 (symmetricSpace × alternatingSpace)) (E' := TensorSquare)
    (by exact (WithLp.linearEquiv 2 ℂ (symmetricSpace × alternatingSpace)).trans sumEquiv) ?_
  intro x y
  exact (sumEquiv_inner (WithLp.ofLp x) (WithLp.ofLp y)).trans
    (WithLp.prod_inner_apply x y).symm

/-- A normalized unitary identification of the actual alternating line.
Its phase depends on the orthonormal basis choice; the source action is
trivial on both sides, so this choice does not affect intertwining. -/
def alternatingUnitary : alternatingSpace ≃ₗᵢ[ℂ] HilbertCarrier 0 :=
  (stdOrthonormalBasis ℂ alternatingSpace).equiv
    (stdOrthonormalBasis ℂ (HilbertCarrier 0)) (finCongr alternatingEquiv.finrank_eq)

theorem alternatingUnitary_intertwines (U : SU2) (x : alternatingSpace) :
    alternatingUnitary ⟨tensorAction U x, alternatingSpace_invariant U x.property⟩ =
      unitaryAction 0 U (alternatingUnitary x) := by
  rw [degreeZero_unitaryAction]
  apply congrArg alternatingUnitary
  exact Subtype.ext (alternating_source_fixed U x)

end GeneratedFoundations.Geometry.SourceQuadraticSplit
