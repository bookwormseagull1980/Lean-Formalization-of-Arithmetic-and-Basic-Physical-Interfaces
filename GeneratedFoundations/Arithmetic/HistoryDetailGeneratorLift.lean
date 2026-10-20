module

public import GeneratedFoundations.Arithmetic.HistoryChargeSectors

/-!
# Complete lift of the intrinsic detail operation algebra

The detail algebra acts on its actual residual subspace and is extended
by zero to the invariant part. The complete source carrier retains that
action at every original source coordinate. In particular the lift of
the detail identity is the detail projection, rather than the full
identity. Multiplication, adjoints and the entire quadratic generator
sum are preserved with this precise support.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryDetailGeneratorLift

open HistoryJointCharge HistoryJointChargeLattice
open HistoryDetailCasimir (Detail BasisIndex)

def fullLift (n : ℕ) : Module.End ℂ (Detail n) →ₗ[ℂ] Module.End ℂ (Space n) where
  toFun A := blocks n (fun _ => HistoryDetailCasimir.extend n A)
  map_add' A B := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro s
    simp
  map_smul' c A := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro s
    simp

set_option maxHeartbeats 1000000 in
theorem fullLift_apply (n : ℕ) (A : Module.End ℂ (Detail n))
    (x : Space n) (s : Spin) :
    fullLift n A x s = HistoryDetailCasimir.extend n A (x s) := by
  change blocks n (fun _ : Spin => HistoryDetailCasimir.extend n A) x s = _
  exact blocks_apply n (fun _ : Spin => HistoryDetailCasimir.extend n A) x s

theorem fullLift_mul (n : ℕ) (A B : Module.End ℂ (Detail n)) :
    fullLift n (A * B) = fullLift n A * fullLift n B := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [Module.End.mul_apply, fullLift_apply, HistoryDetailCasimir.extend_mul]

theorem fullLift_one (n : ℕ) :
    fullLift n 1 = blocks n (fun _ => HistoryPhaseProjection.residual n) := by
  unfold fullLift
  simp only [LinearMap.coe_mk, AddHom.coe_mk, HistoryDetailCasimir.extend_one]

theorem fullLift_adjoint (n : ℕ) (A : Module.End ℂ (Detail n)) :
    (fullLift n A).adjoint = fullLift n
      (LinearMap.adjoint (𝕜 := ℂ) (E := Detail n) (F := Detail n) A) := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  change (∑ s : Spin, inner ℂ (fullLift n _ x s) (y s)) =
    ∑ s : Spin, inner ℂ (x s) (fullLift n A y s)
  apply Finset.sum_congr rfl
  intro s _
  rw [fullLift_apply, fullLift_apply, ← HistoryDetailCasimir.extend_adjoint]
  exact LinearMap.adjoint_inner_left (HistoryDetailCasimir.extend n A) (y s) (x s)

def generator (n : ℕ) (i j : BasisIndex n) : Module.End ℂ (Space n) :=
  fullLift n (Operations.FiniteDefiningResponse.generator (HistoryDetailCasimir.basis n) i j)

def quadraticResponse (n : ℕ) : Module.End ℂ (Space n) :=
  (1 / 2 : ℂ) • ∑ i, ∑ j, generator n i j * generator n j i

theorem quadraticResponse_eq (n : ℕ) : quadraticResponse n =
    HistoryChargedCasimirResponse.detailResponse n := by
  have h := congrArg (fullLift n)
    (Operations.FiniteDefiningResponse.response_intrinsic (HistoryDetailCasimir.basis n))
  have hq : quadraticResponse n =
    (HistoryDetailCasimir.coefficient n : ℂ) •
      blocks n (fun _ => HistoryPhaseProjection.residual n) := by
    simpa only [Operations.FiniteDefiningResponse.response, quadraticResponse,
      generator, map_smul, map_sum, fullLift_mul, fullLift_one,
      HistoryDetailCasimir.coefficient] using h
  rw [hq]
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  simp only [LinearMap.smul_apply, PiLp.smul_apply, blocks_apply,
    HistoryChargedCasimirResponse.detailResponse, blocks_apply,
    HistoryDetailCasimir.response_eq, LinearMap.smul_apply]

theorem generator_adjoint (n : ℕ) (i j : BasisIndex n) :
    (generator n i j).adjoint = generator n j i := by
  rw [generator, fullLift_adjoint]
  congr 1
  change LinearMap.adjoint (Matrix.toLin (HistoryDetailCasimir.basis n).toBasis
    (HistoryDetailCasimir.basis n).toBasis
    (Operations.MatrixDefiningCasimir.centredUnit i j)) = _
  rw [← Matrix.toLin_conjTranspose (HistoryDetailCasimir.basis n)
    (HistoryDetailCasimir.basis n)]
  change Matrix.toLin (HistoryDetailCasimir.basis n).toBasis
    (HistoryDetailCasimir.basis n).toBasis
    (Operations.MatrixDefiningCasimir.centredUnit i j).conjTranspose = _
  rw [Operations.MatrixDefiningCasimir.centredUnit_adjoint]
  rfl

structure Conclusions : Prop where
  supported_identity : ∀ n, fullLift n 1 =
    blocks n (fun _ => HistoryPhaseProjection.residual n)
  complete_product : ∀ n A B, fullLift n (A * B) = fullLift n A * fullLift n B
  actual_adjoint : ∀ n A, (fullLift n A).adjoint = fullLift n
    (LinearMap.adjoint (𝕜 := ℂ) (E := Detail n) (F := Detail n) A)
  complete_response : ∀ n, quadraticResponse n = HistoryChargedCasimirResponse.detailResponse n

theorem generated : Conclusions where
  supported_identity := fullLift_one
  complete_product := fullLift_mul
  actual_adjoint := fullLift_adjoint
  complete_response := quadraticResponse_eq

end GeneratedFoundations.Arithmetic.HistoryDetailGeneratorLift
