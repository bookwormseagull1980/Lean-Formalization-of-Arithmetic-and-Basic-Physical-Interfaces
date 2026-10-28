module

public import GeneratedFoundations.Physical.SourceChiralCarrier
public import GeneratedFoundations.Operations.CovariantCompression

/-!
# Complete covariant compression on the generated matter carrier

The scalar source summand in each chiral copy determines the complete
lepton projection. Its neutral direction is retained. The same projection
commutes with the elementary connector, before taking a charged quotient.

In orthonormal finite coordinates, compression of a covariant first jet
has both a retained connection and an orthogonal leakage. Their sum
recovers the original jet. The square of the jet contains the leakage
Gram term, including the interference between the original connection
and the moving readout. All coefficients in these identities are fixed.
The connection and its jets are field configurations, not new root data.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace GeneratedFoundations.Physical.SourceMatterCompression

open SourceChiralCarrier SourceMinimalRepresentation SourceJointResponse

/-- Projection onto the actual scalar-spin source summand. -/
def scalarSourceProjection : Module.End ℂ SourceCarrier :=
  sourceCarrierRepresentation (0, 1)

theorem scalarSourceProjection_square :
    scalarSourceProjection * scalarSourceProjection = scalarSourceProjection := by
  unfold scalarSourceProjection
  rw [← map_mul]
  rfl

theorem scalarSourceProjection_adjoint :
    scalarSourceProjection.adjoint = scalarSourceProjection := by
  rw [scalarSourceProjection, sourceCarrierRepresentation_adjoint]
  congr 1
  apply Prod.ext
  · change (0 : Module.End ℂ Coloured).adjoint = 0
    exact map_zero LinearMap.adjoint
  · change (1 : Module.End ℂ Scalar).adjoint = 1
    exact LinearMap.adjoint_one

/-- Both chiral scalar-spin summands, including the neutral source line. -/
def leptonProjection : Module.End ℂ FullMatter :=
  diagonalBlocks scalarSourceProjection scalarSourceProjection

theorem leptonProjection_square :
    leptonProjection * leptonProjection = leptonProjection := by
  simp only [leptonProjection, diagonalBlocks_mul, scalarSourceProjection_square]

theorem leptonProjection_adjoint :
    leptonProjection.adjoint = leptonProjection := by
  simp only [leptonProjection, diagonalBlocks_adjoint, scalarSourceProjection_adjoint]

theorem scalarSourceProjection_spin (h : Module.End ℂ S) :
    scalarSourceProjection * spinOnSource h = spinOnSource h * scalarSourceProjection := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  change ((0 : Module.End ℂ Coloured) (TensorProduct.map 1 h (WithLp.ofLp x).1),
      (1 : Module.End ℂ Scalar) (TensorProduct.map 1 h (WithLp.ofLp x).2)) =
    (TensorProduct.map 1 h ((0 : Module.End ℂ Coloured) (WithLp.ofLp x).1),
      TensorProduct.map 1 h ((1 : Module.End ℂ Scalar) (WithLp.ofLp x).2))
  simp

/-- The complete lepton carrier is preserved by the actual common connector. -/
theorem leptonProjection_connector (h : Module.End ℂ S) :
    leptonProjection * connector h = connector h * leptonProjection := by
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  change (scalarSourceProjection (spinOnSource h (WithLp.ofLp x).2),
      scalarSourceProjection (spinOnSource h.adjoint (WithLp.ofLp x).1)) =
    (spinOnSource h (scalarSourceProjection (WithLp.ofLp x).2),
      spinOnSource h.adjoint (scalarSourceProjection (WithLp.ofLp x).1))
  exact Prod.ext
    (LinearMap.congr_fun (scalarSourceProjection_spin h) (WithLp.ofLp x).2)
    (LinearMap.congr_fun (scalarSourceProjection_spin h.adjoint) (WithLp.ofLp x).1)

/-- A response supported on the coloured source summand, in both chiral copies. -/
def colouredResponse (a : Module.End ℂ Coloured) : Module.End ℂ FullMatter :=
  diagonalBlocks (sourceCarrierRepresentation (a, 0))
    (sourceCarrierRepresentation (a, 0))

theorem leptonProjection_colouredResponse (a : Module.End ℂ Coloured) :
    leptonProjection * colouredResponse a = 0 := by
  have h : scalarSourceProjection * sourceCarrierRepresentation (a, 0) = 0 := by
    unfold scalarSourceProjection
    rw [← map_mul]
    have hp : ((0, 1) : JointEnd) * (a, 0) = 0 := by
      apply Prod.ext
      · exact zero_mul a
      · exact mul_zero (1 : Module.End ℂ Scalar)
    exact (congrArg sourceCarrierRepresentation hp).trans
      (map_zero sourceCarrierRepresentation)
  simp only [leptonProjection, colouredResponse, diagonalBlocks_mul, h]
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

theorem colouredResponse_leptonProjection (a : Module.End ℂ Coloured) :
    colouredResponse a * leptonProjection = 0 := by
  have h : sourceCarrierRepresentation (a, 0) * scalarSourceProjection = 0 := by
    unfold scalarSourceProjection
    rw [← map_mul]
    have hp : ((a, 0) : JointEnd) * (0, 1) = 0 := by
      apply Prod.ext
      · exact mul_zero a
      · exact zero_mul (1 : Module.End ℂ Scalar)
    exact (congrArg sourceCarrierRepresentation hp).trans
      (map_zero sourceCarrierRepresentation)
  simp only [leptonProjection, colouredResponse, diagonalBlocks_mul, h]
  apply LinearMap.ext
  intro x
  apply WithLp.ofLp_injective 2
  rfl

open GeneratedFoundations.Operations.CovariantCompression

/-- The generated projection and its complete finite-coordinate connection
interface. The fields quantify over configurations; no configuration is
added to the root package. -/
structure Conclusions : Prop where
  projection_square : leptonProjection * leptonProjection = leptonProjection
  projection_adjoint : leptonProjection.adjoint = leptonProjection
  connector_preserved : ∀ h : Module.End ℂ S,
    leptonProjection * connector h = connector h * leptonProjection
  colour_left_zero : ∀ a : Module.End ℂ Coloured,
    leptonProjection * colouredResponse a = 0
  colour_right_zero : ∀ a : Module.End ℂ Coloured,
    colouredResponse a * leptonProjection = 0
  reconstruction : ∀ (n r : ℕ) (R dR : Matrix (Fin n) (Fin r) ℂ)
      (A : Matrix (Fin n) (Fin n) ℂ),
    R * retainedConnection R dR A + complementConnection R dR A = covariantJet R dR A
  orthogonal : ∀ (n r : ℕ) (R dR : Matrix (Fin n) (Fin r) ℂ)
      (A : Matrix (Fin n) (Fin n) ℂ), Rᴴ * R = 1 →
    Rᴴ * complementConnection R dR A = 0
  decomposition_unique : ∀ (n r : ℕ) (R dR : Matrix (Fin n) (Fin r) ℂ)
      (A : Matrix (Fin n) (Fin n) ℂ), Rᴴ * R = 1 →
    ∀ (a : Matrix (Fin r) (Fin r) ℂ) (b : Matrix (Fin n) (Fin r) ℂ),
      covariantJet R dR A = R * a + b → Rᴴ * b = 0 →
      a = retainedConnection R dR A ∧ b = complementConnection R dR A
  quadratic_split : ∀ (n r : ℕ) (R dR : Matrix (Fin n) (Fin r) ℂ)
      (A : Matrix (Fin n) (Fin n) ℂ), Rᴴ * R = 1 →
    (covariantJet R dR A)ᴴ * covariantJet R dR A =
      (retainedConnection R dR A)ᴴ * retainedConnection R dR A +
      (complementConnection R dR A)ᴴ * complementConnection R dR A
  passive_transport : ∀ (n r : ℕ) (U dU : Matrix (Fin n) (Fin n) ℂ)
      (R dR : Matrix (Fin n) (Fin r) ℂ) (A : Matrix (Fin n) (Fin n) ℂ),
    U * Uᴴ = 1 →
      covariantJet (Uᴴ * R) (passiveReadoutDerivative U dU R dR)
        (passiveConnection U dU A) = Uᴴ * covariantJet R dR A

theorem generated : Conclusions where
  projection_square := leptonProjection_square
  projection_adjoint := leptonProjection_adjoint
  connector_preserved := leptonProjection_connector
  colour_left_zero := leptonProjection_colouredResponse
  colour_right_zero := colouredResponse_leptonProjection
  reconstruction := fun _ _ => covariantJet_reconstruction
  orthogonal := fun _ _ => complementConnection_orthogonal
  decomposition_unique := fun _ _ => covariantJet_decomposition_unique
  quadratic_split := fun _ _ => covariantJet_gram
  passive_transport := fun _ _ => covariantJet_passive

end GeneratedFoundations.Physical.SourceMatterCompression
