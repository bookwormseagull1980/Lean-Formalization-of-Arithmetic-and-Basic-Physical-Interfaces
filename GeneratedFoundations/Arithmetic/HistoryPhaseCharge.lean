module

public import GeneratedFoundations.Arithmetic.HistoryJointPhaseFlow
public import GeneratedFoundations.Operations.PhaseCharge

/-!
# Conserved charge of the actual complete phase flow

The charge operator and flow act on every source, history and phase
coordinate. Their commutation is derived from the same complementary
phase algebra. Conservation holds for every pair of states before a
neutral quotient or scalar observation is taken. The real-pair work
identity in the common operation layer supplies the residual form.
-/

@[expose] public section
noncomputable section
namespace GeneratedFoundations.Arithmetic.HistoryPhaseCharge

open HistoryJointCharge HistoryJointPhaseFlow

theorem response_flow (n : ℕ) (r b : ℤ) (t : ℝ) :
    response n r b * flow n r b t = flow n r b t * response n r b := by
  rw [response, flow, HistoryJointChargeQuotient.blocks_mul,
    HistoryJointChargeQuotient.blocks_mul]
  congr 1
  funext s
  unfold component componentFlow
  rw [← map_mul, ← map_mul, mul_comm]

def chargePairing (n : ℕ) (r b : ℤ) (x y : Space n) : ℂ :=
  inner ℂ x (response n r b y)

theorem chargePairing_conserved (n : ℕ) (r b : ℤ) (t : ℝ) (x y : Space n) :
    chargePairing n r b (flow n r b t x) (flow n r b t y) =
      chargePairing n r b x y := by
  unfold chargePairing
  have hc := LinearMap.congr_fun (response_flow n r b t) y
  change response n r b (flow n r b t y) = flow n r b t (response n r b y) at hc
  rw [hc, flow_inner]

def charge (n : ℕ) (r b : ℤ) (x : Space n) : ℝ :=
  (chargePairing n r b x x).re

theorem charge_conserved (n : ℕ) (r b : ℤ) (t : ℝ) (x : Space n) :
    charge n r b (flow n r b t x) = charge n r b x :=
  congrArg Complex.re (chargePairing_conserved n r b t x x)

theorem charge_hasDerivAt (n : ℕ) (r b : ℤ) (x : Space n) (t : ℝ) :
    HasDerivAt (fun u => charge n r b (flow n r b u x)) 0 t := by
  have he : (fun u => charge n r b (flow n r b u x)) = fun _ => charge n r b x :=
    funext fun u => charge_conserved n r b u x
  rw [he]
  exact hasDerivAt_const _ _

structure Conclusions : Prop where
  actual_commutation : ∀ n r b t,
    response n r b * flow n r b t = flow n r b t * response n r b
  complete_pairing : ∀ n r b t x y,
    chargePairing n r b (flow n r b t x) (flow n r b t y) = chargePairing n r b x y
  conserved_charge : ∀ n r b t x, charge n r b (flow n r b t x) = charge n r b x
  derivative_zero : ∀ n r b x t,
    HasDerivAt (fun u => charge n r b (flow n r b u x)) 0 t

theorem generated : Conclusions where
  actual_commutation := response_flow
  complete_pairing := chargePairing_conserved
  conserved_charge := charge_conserved
  derivative_zero := charge_hasDerivAt

end GeneratedFoundations.Arithmetic.HistoryPhaseCharge
