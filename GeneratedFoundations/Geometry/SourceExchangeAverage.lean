module

public import GeneratedFoundations.Geometry.SourceSplitResponse
public import Mathlib.Tactic.NoncommRing

/-!
# Unbiased exchange averaging on the complete source response algebra

Both terms use the original tensor exchange. Their normalized average is a
linear idempotent with exactly the previously constructed retained algebra as
its image. Its uniqueness is among linear maps that fix exchange invariant
responses and identify the two exchange representatives. These properties
describe the averaging operation, rather than all possible physical responses.
-/

@[expose] public section
noncomputable section

namespace GeneratedFoundations.Geometry.SourceExchangeAverage

open SourceSplitResponse

set_option maxHeartbeats 1500000

theorem exchange_square : exchangeOperator * exchangeOperator = 1 := by
  apply LinearMap.ext
  intro x
  apply colourPair.injective
  simp only [Module.End.mul_apply, Module.End.one_apply, colourPair_exchange, neg_neg]

def conjugate : Module.End ℂ C →ₗ[ℂ] Module.End ℂ C where
  toFun T := exchangeOperator * T * exchangeOperator
  map_add' T S := by simp only [mul_add, add_mul]
  map_smul' z T := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

theorem conjugate_involutive (T : Module.End ℂ C) :
    conjugate (conjugate T) = T := by
  change exchangeOperator * (exchangeOperator * T * exchangeOperator) * exchangeOperator = T
  calc
    _ = (exchangeOperator * exchangeOperator) * T *
        (exchangeOperator * exchangeOperator) := by noncomm_ring
    _ = T := by rw [exchange_square, one_mul, mul_one]

def average : Module.End ℂ C →ₗ[ℂ] Module.End ℂ C :=
  (1 / 2 : ℂ) • (LinearMap.id + conjugate)

theorem average_apply (T : Module.End ℂ C) :
    average T = (1 / 2 : ℂ) • (T + conjugate T) := rfl

theorem conjugate_average (T : Module.End ℂ C) :
    conjugate (average T) = average T := by
  rw [average_apply, map_smul, map_add, conjugate_involutive]
  exact congrArg (fun S : Module.End ℂ C => (1 / 2 : ℂ) • S)
    (add_comm (conjugate T) T)

theorem conjugate_fixed_iff (T : Module.End ℂ C) :
    conjugate T = T ↔ T ∈ retainedAlgebra := by
  rw [mem_retainedAlgebra]
  constructor
  · intro h
    have h' := congrArg (fun S : Module.End ℂ C => S * exchangeOperator) h
    simpa only [conjugate, LinearMap.coe_mk, AddHom.coe_mk,
      mul_assoc, exchange_square, mul_one] using h'
  · intro h
    change exchangeOperator * T * exchangeOperator = T
    rw [h, mul_assoc, exchange_square, mul_one]

theorem average_mem (T : Module.End ℂ C) : average T ∈ retainedAlgebra :=
  (conjugate_fixed_iff _).mp (conjugate_average T)

theorem average_eq_self (T : Module.End ℂ C) (hT : T ∈ retainedAlgebra) :
    average T = T := by
  rw [average_apply, (conjugate_fixed_iff T).mpr hT, ← two_smul ℂ T, smul_smul]
  norm_num

theorem average_idempotent (T : Module.End ℂ C) : average (average T) = average T :=
  average_eq_self _ (average_mem T)

theorem average_exchange (T : Module.End ℂ C) : average (conjugate T) = average T := by
  rw [average_apply, conjugate_involutive, average_apply]
  exact congrArg (fun S : Module.End ℂ C => (1 / 2 : ℂ) • S)
    (add_comm (conjugate T) T)

theorem range_average : LinearMap.range average = retainedAlgebra.toSubmodule := by
  ext T
  constructor
  · rintro ⟨S, rfl⟩
    exact average_mem S
  · intro hT
    exact ⟨T, average_eq_self T hT⟩

theorem average_unique (F : Module.End ℂ C →ₗ[ℂ] Module.End ℂ C)
    (hfix : ∀ T, T ∈ retainedAlgebra → F T = T)
    (hexchange : ∀ T, F (conjugate T) = F T) : F = average := by
  apply LinearMap.ext
  intro T
  have h := hfix (average T) (average_mem T)
  rw [average_apply, map_smul, map_add, hexchange, ← two_smul ℂ (F T), smul_smul] at h
  norm_num at h
  simpa only [average_apply, smul_add] using h

end GeneratedFoundations.Geometry.SourceExchangeAverage
