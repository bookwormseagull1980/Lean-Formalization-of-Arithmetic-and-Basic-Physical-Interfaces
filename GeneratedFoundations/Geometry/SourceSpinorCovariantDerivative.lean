module

public import GeneratedFoundations.Geometry.SourceSpinorDifferential

/-!
# Clifford contraction of the generated covariant spin derivative

The matrix connection is the Koszul connection computed from the original
source frame. Its action on the two coefficient slots is contracted before
the constant term of the Dirac operator is identified.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceClebschGordan
open GeneratedFoundations.Geometry.SourceSpinorConnection
open GeneratedFoundations.Geometry.SourceSpinorDifferential

namespace GeneratedFoundations.Geometry.SourceSpinorCovariantDerivative

def connectionPair (m : ℕ) (i : Fin 3) : Module.End ℂ (PairCarrier m) :=
  ((spinConnection i 0 0) • (LinearMap.fst ℂ (Carrier m) (Carrier m)) +
    (spinConnection i 0 1) • (LinearMap.snd ℂ (Carrier m) (Carrier m))).prod
      ((spinConnection i 1 0) • (LinearMap.fst ℂ (Carrier m) (Carrier m)) +
        (spinConnection i 1 1) • (LinearMap.snd ℂ (Carrier m) (Carrier m)))

def covariantPair (m : ℕ) (i : Fin 3) : Module.End ℂ (PairCarrier m) :=
  (polynomialAxis m i).prodMap (polynomialAxis m i) + connectionPair m i

theorem contracted_connection_pair (m : ℕ) :
    (∑ i : Fin 3, (cliffordPair m i).comp (connectionPair m i)) =
      (3 / 2 : ℂ) • (1 : Module.End ℂ (PairCarrier m)) := by
  apply LinearMap.ext
  intro p
  apply Prod.ext <;>
    simp [connectionPair, cliffordPair, spinConnection_eq, clifford, unitAxis, axisVelocity,
      spinMatrix, spinMatrix1, spinMatrix2, spinMatrix3, Fin.sum_univ_three, smul_smul] <;>
    match_scalars <;> ring_nf <;> norm_num

/-- The entire finite Dirac operator is obtained by contracting the actual
covariant source derivative; its zero-order term is therefore derived. -/
theorem polynomialDirac_eq_contraction (m : ℕ) :
    polynomialDirac m =
      ∑ i : Fin 3, (cliffordPair m i).comp (covariantPair m i) := by
  simp only [covariantPair, LinearMap.comp_add, Finset.sum_add_distrib,
    ← polynomialKinetic_eq_contraction, contracted_connection_pair, polynomialDirac]

end GeneratedFoundations.Geometry.SourceSpinorCovariantDerivative
