module

public import GeneratedFoundations.Geometry.SourceJointResponse

/-!
# Orthonormal bases of the common symmetric and alternating source factors

The dimensions are derived from the actual degree-two and degree-zero Haar
carriers. These are bases of the original source factors. Arithmetic history
multiplicities are independent indices and are not replaced by these factors.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.SourceFactorBases

open SourceJointResponse (W L)
open SourceSymmetricUnitary (hilbertCarrier_finrank)

def colourBasis : OrthonormalBasis (Fin 3) ℂ W :=
  (stdOrthonormalBasis ℂ W).reindex (finCongr (hilbertCarrier_finrank 2))

def lineBasis : OrthonormalBasis (Fin 1) ℂ L :=
  (stdOrthonormalBasis ℂ L).reindex (finCongr (hilbertCarrier_finrank 0))

end GeneratedFoundations.Geometry.SourceFactorBases
