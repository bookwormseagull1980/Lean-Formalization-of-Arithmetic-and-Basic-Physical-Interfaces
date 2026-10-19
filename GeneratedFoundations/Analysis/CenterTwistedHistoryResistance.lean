module

public import GeneratedFoundations.Analysis.CanonicalMobiusReadout

/-!
# Centre-twisted shared-edge resistance

The generated history restoration argument combines all requests using a
physical edge before squaring the resulting load.  This file records the
finite inequality which permits the canonical occupation centre character to
be inserted without increasing that complete edge energy.  Thus the sign is
kept inside every shared-edge sum; it is not replaced by a diagonal or by a
sum of separately squared channels.

The statement is deliberately independent of a cutoff and of a Gaussian
scale.  Those data enter only through the nonnegative request magnitudes and
the positive physical conductances.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.CenterTwistedHistoryResistance

open GeneratedFoundations.Arithmetic.JointOccupationScale
open GeneratedFoundations.Analysis.CanonicalMobiusReadout

variable {I E : Type*} [Fintype I] [Fintype E]

/-- The complete load on one edge after all centre phases have been combined. -/
def twistedEdgeLoad (phase : I → ℝ) (request : I → E → ℝ) (e : E) : ℝ :=
  ∑ i, phase i * request i e

/-- The corresponding same-magnitude load before inserting centre phases. -/
def untwistedEdgeLoad (request : I → E → ℝ) (e : E) : ℝ :=
  ∑ i, request i e

/-- Conductance-weighted energy.  Cross terms sharing an edge are formed
before the edge energies are added. -/
def resistanceEnergy (conductance : E → ℝ) (load : E → ℝ) : ℝ :=
  ∑ e, load e ^ 2 / conductance e

omit [Fintype E] in
/-- A unit-modulus centre phase cannot increase the complete load on any
physical edge.  The phase remains inside the shared-edge sum. -/
theorem abs_twistedEdgeLoad_le_untwistedEdgeLoad
    (phase : I → ℝ) (request : I → E → ℝ)
    (hphase : ∀ i, |phase i| = 1)
    (hrequest : ∀ i e, 0 ≤ request i e) (e : E) :
    |twistedEdgeLoad phase request e| ≤ untwistedEdgeLoad request e := by
  calc
    |twistedEdgeLoad phase request e| =
        |∑ i, phase i * request i e| := rfl
    _ ≤ ∑ i, |phase i * request i e| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, request i e := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul, hphase i, one_mul, abs_of_nonneg (hrequest i e)]
    _ = untwistedEdgeLoad request e := rfl

/-- Centre twisting preserves the full shared-edge cross-term budget: after
division by every true positive conductance, the signed energy is bounded by
the energy of the same requests with their magnitudes coherently aligned. -/
theorem twisted_resistanceEnergy_le_untwisted
    (phase : I → ℝ) (request : I → E → ℝ) (conductance : E → ℝ)
    (hphase : ∀ i, |phase i| = 1)
    (hrequest : ∀ i e, 0 ≤ request i e)
    (hconductance : ∀ e, 0 < conductance e) :
    resistanceEnergy conductance (twistedEdgeLoad phase request) ≤
      resistanceEnergy conductance (untwistedEdgeLoad request) := by
  apply Finset.sum_le_sum
  intro e _he
  have hload := abs_twistedEdgeLoad_le_untwistedEdgeLoad
    phase request hphase hrequest e
  have hpositive : 0 ≤ untwistedEdgeLoad request e := by
    exact Finset.sum_nonneg fun i _hi => hrequest i e
  have hsquare : twistedEdgeLoad phase request e ^ 2 ≤
      untwistedEdgeLoad request e ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hpositive).mpr hload
  exact div_le_div_of_nonneg_right hsquare (le_of_lt (hconductance e))

/-- The canonical centre character of every finite prime occupation has unit
absolute value. -/
theorem abs_centerCharacter_real (nu : Occupation) :
    |(centerCharacter nu : ℝ)| = 1 := by
  rw [centerCharacter_eq_neg_one_pow_card]
  simp

/-- Specialization to the source-generated occupation centre character.  By
`generatedMoebius_label`, this is exactly the nonzero generated Mobius sign in
the canonical squarefree root coordinate. -/
theorem occupationCenter_resistanceEnergy_le_untwisted
    (occupation : I → Occupation) (request : I → E → ℝ)
    (conductance : E → ℝ)
    (hrequest : ∀ i e, 0 ≤ request i e)
    (hconductance : ∀ e, 0 < conductance e) :
    resistanceEnergy conductance
        (twistedEdgeLoad (fun i => (centerCharacter (occupation i) : ℝ)) request) ≤
      resistanceEnergy conductance (untwistedEdgeLoad request) := by
  exact twisted_resistanceEnergy_le_untwisted
    (fun i => (centerCharacter (occupation i) : ℝ)) request conductance
    (fun i => abs_centerCharacter_real (occupation i)) hrequest hconductance

structure Conclusions : Prop where
  phase_stability : ∀ {I E : Type*} [Fintype I] [Fintype E]
      (occupation : I → Occupation) (request : I → E → ℝ)
      (conductance : E → ℝ),
    (∀ i e, 0 ≤ request i e) → (∀ e, 0 < conductance e) →
      resistanceEnergy conductance
          (twistedEdgeLoad
            (fun i => (centerCharacter (occupation i) : ℝ)) request) ≤
        resistanceEnergy conductance (untwistedEdgeLoad request)

theorem centerTwistedHistoryResistanceConclusions : Conclusions where
  phase_stability := occupationCenter_resistanceEnergy_le_untwisted

end GeneratedFoundations.Analysis.CenterTwistedHistoryResistance
