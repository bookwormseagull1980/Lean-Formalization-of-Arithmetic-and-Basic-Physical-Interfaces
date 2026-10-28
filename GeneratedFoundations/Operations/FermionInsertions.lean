module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! Fermionic insertion operations and the unique lift of a one-matter operator. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Operations.FermionInsertions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev Fock (E : Type*) [AddCommGroup E] [Module ℂ E] := ExteriorAlgebra ℂ E

def vacuum : Fock E := 1

def create (v : E) (x : Fock E) : Fock E :=
  ExteriorAlgebra.ι ℂ v * x

def remove (v : E) : Fock E →ₗ[ℂ] Fock E :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ E))
    (innerSL ℂ v).toLinearMap

theorem create_square (v : E) (x : Fock E) :
    create v (create v x) = 0 := by
  simp only [create, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem create_anticommute (v w : E) (x : Fock E) :
    create v (create w x) + create w (create v x) = 0 := by
  simp only [create, ← mul_assoc, ← add_mul,
    ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem remove_square (v : E) (x : Fock E) :
    remove v (remove v x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft (Q := (0 : QuadraticForm ℂ E))
    (innerSL ℂ v).toLinearMap x

theorem remove_anticommute (v w : E) (x : Fock E) :
    remove v (remove w x) + remove w (remove v x) = 0 := by
  change
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ E))
        (innerSL ℂ v).toLinearMap
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ E))
          (innerSL ℂ w).toLinearMap x) +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ E))
        (innerSL ℂ w).toLinearMap
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ E))
          (innerSL ℂ v).toLinearMap x) = 0
  rw [CliffordAlgebra.contractLeft_comm, neg_add_cancel]

theorem mixed_car (v w : E) (x : Fock E) :
    remove v (create w x) + create w (remove v x) =
      inner ℂ v w • x := by
  change
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ E))
        (innerSL ℂ v).toLinearMap
        (CliffordAlgebra.ι (0 : QuadraticForm ℂ E) w * x) +
      CliffordAlgebra.ι (0 : QuadraticForm ℂ E) w *
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ E))
          (innerSL ℂ v).toLinearMap x = _
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  rfl

theorem remove_vacuum (v : E) : remove v vacuum = 0 :=
  CliffordAlgebra.contractLeft_one _ _

theorem vacuum_pair (v w : E) :
    remove v (create w vacuum) =
      algebraMap ℂ (Fock E) (inner ℂ v w) := by
  simp only [create, vacuum, mul_one, remove,
    CliffordAlgebra.contractLeft_ι]
  rfl

/-- The existing source operator is lifted by exterior functoriality. -/
def transport (U : E →ₗ[ℂ] E) : Fock E →ₐ[ℂ] Fock E :=
  ExteriorAlgebra.map U

theorem transport_create (U : E →ₗ[ℂ] E) (v : E) (x : Fock E) :
    transport U (create v x) = create (U v) (transport U x) := by
  change ExteriorAlgebra.map U (ExteriorAlgebra.ι ℂ v * x) =
    ExteriorAlgebra.ι ℂ (U v) * ExteriorAlgebra.map U x
  rw [map_mul, ExteriorAlgebra.map_apply_ι]

theorem transport_vacuum (U : E →ₗ[ℂ] E) :
    transport U vacuum = vacuum := map_one _

theorem transport_comp (U V : E →ₗ[ℂ] E) (x : Fock E) :
    transport U (transport V x) = transport (U.comp V) x := by
  exact congrArg (fun f : Fock E →ₐ[ℂ] Fock E => f x)
    (ExteriorAlgebra.map_comp_map V U)

/-- Agreement on all one-matter insertions fixes the full algebra action. -/
theorem transport_unique (U : E →ₗ[ℂ] E)
    (F : Fock E →ₐ[ℂ] Fock E)
    (h : ∀ v, F (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (U v)) :
    F = transport U := by
  apply ExteriorAlgebra.hom_ext
  ext v
  exact (h v).trans (ExteriorAlgebra.map_apply_ι U v).symm

theorem remove_create (v w : E) (x : Fock E) :
    remove v (create w x) = inner ℂ v w • x - create w (remove v x) := by
  exact eq_sub_iff_add_eq.mpr (mixed_car v w x)

theorem create_swap (v w : E) (x : Fock E) :
    create v (create w x) = -create w (create v x) := by
  exact eq_neg_iff_add_eq_zero.mpr (create_anticommute v w x)

/-- The derivation induced by the original one-matter source operator. -/
def oneBody {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E)
    (A : E →ₗ[ℂ] E) : Fock E →ₗ[ℂ] Fock E :=
  ∑ i, ((Algebra.lmul ℂ (Fock E)) (ExteriorAlgebra.ι ℂ (A (e i)))).comp
    (remove (e i))

theorem oneBody_apply {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E)
    (A : E →ₗ[ℂ] E) (x : Fock E) :
    oneBody e A x = ∑ i, create (A (e i)) (remove (e i) x) := by
  simp [oneBody, create]

theorem oneBody_vacuum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E)
    (A : E →ₗ[ℂ] E) : oneBody e A vacuum = 0 := by
  simp [oneBody_apply, remove_vacuum, create]

/-- The lifted source current changes an insertion by the original source matrix. -/
theorem oneBody_create {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E)
    (A : E →ₗ[ℂ] E) (v : E) (x : Fock E) :
    oneBody e A (create v x) =
      create (A v) x + create v (oneBody e A x) := by
  have hterm (i : ι) :
      create (A (e i)) (remove (e i) (create v x)) =
        inner ℂ (e i) v • create (A (e i)) x +
          create v (create (A (e i)) (remove (e i) x)) := by
    rw [remove_create]
    simp only [create, mul_sub, mul_smul_comm]
    have hswap := create_swap (A (e i)) v (remove (e i) x)
    change ExteriorAlgebra.ι ℂ (A (e i)) *
        (ExteriorAlgebra.ι ℂ v * remove (e i) x) =
      -(ExteriorAlgebra.ι ℂ v *
        (ExteriorAlgebra.ι ℂ (A (e i)) * remove (e i) x)) at hswap
    rw [hswap, sub_neg_eq_add]
  have hsum : ∑ i, inner ℂ (e i) v • create (A (e i)) x = create (A v) x := by
    calc
      _ = create (A (∑ i, inner ℂ (e i) v • e i)) x := by
        simp [create, map_sum, map_smul, Finset.sum_mul]
      _ = _ := by rw [e.sum_repr']
  rw [oneBody_apply]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hsum, oneBody_apply]
  simp only [create, Finset.mul_sum]

/-- Vacuum value and the source action on insertions determine the lift uniquely. -/
theorem oneBody_unique {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E)
    (A : E →ₗ[ℂ] E) (K : Fock E →ₗ[ℂ] Fock E)
    (hv : K vacuum = 0)
    (hi : ∀ v x, K (create v x) = create (A v) x + create v (K x)) :
    K = oneBody e A := by
  ext x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul]
      change c • K vacuum = c • oneBody e A vacuum
      rw [hv, oneBody_vacuum]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul x v hx =>
      change K (create v x) = oneBody e A (create v x)
      rw [hi, oneBody_create, hx]

theorem oneBody_basis_independent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (A : E →ₗ[ℂ] E) : oneBody e A = oneBody f A :=
  oneBody_unique f A (oneBody e A) (oneBody_vacuum e A) (oneBody_create e A)

theorem oneBody_one_matter {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ E) (A : E →ₗ[ℂ] E) (v : E) :
    oneBody e A (create v vacuum) = create (A v) vacuum := by
  rw [oneBody_create, oneBody_vacuum]
  simp [create]

/-- The lift respects the original ordinary product on the full exterior algebra. -/
theorem oneBody_mul {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E)
    (A : E →ₗ[ℂ] E) (x y : Fock E) :
    oneBody e A (x * y) = oneBody e A x * y + x * oneBody e A y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c =>
      have hunit : oneBody e A (1 : Fock E) = 0 := oneBody_vacuum e A
      simp [Algebra.algebraMap_eq_smul_one, map_smul, hunit]
  | add x z hx hz =>
      simp only [add_mul, map_add, hx, hz]
      abel
  | ι_mul x v hx =>
      rw [mul_assoc]
      change oneBody e A (create v (x * y)) =
        oneBody e A (create v x) * y + create v x * oneBody e A y
      rw [oneBody_create, oneBody_create, hx]
      simp [create, mul_add, add_mul, mul_assoc, add_assoc]

/-- The unit value follows from the product law, rather than an added normalization. -/
theorem oneBody_unique_derivation {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ E) (A : E →ₗ[ℂ] E) (K : Fock E →ₗ[ℂ] Fock E)
    (hprod : ∀ x y, K (x * y) = K x * y + x * K y)
    (hsource : ∀ v, K (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (A v)) :
    K = oneBody e A := by
  have hv : K vacuum = 0 := by
    have h : K (1 : Fock E) + K 1 = K 1 := by
      simpa only [one_mul, mul_one] using (hprod 1 1).symm
    exact add_left_cancel (h.trans (add_zero _).symm)
  apply oneBody_unique e A K hv
  intro v x
  change K (ExteriorAlgebra.ι ℂ v * x) = _
  rw [hprod, hsource]
  rfl

end GeneratedFoundations.Operations.FermionInsertions
