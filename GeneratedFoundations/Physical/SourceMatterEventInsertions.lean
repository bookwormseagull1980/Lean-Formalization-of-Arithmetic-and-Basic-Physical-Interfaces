module

public import GeneratedFoundations.Physical.SourceMatterInsertions

/-!
# Ordered insertions through the complete matter transport

These words use the existing source fibre, insertions and exterior
transport. The propagators denote the retained one-matter event maps;
their dynamical construction is not a premise hidden in this identity.
At coincident insertion times the complete ordered sum is the same
transported CAR product. Any common linear source average or preparation
functional therefore preserves its normalisation.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceMatterEventInsertions

open SourceMatterInsertions

set_option maxRecDepth 4096

def removalInsertion (before middle after : Matter →ₗ[ℂ] Matter)
    (v w : Matter) (x : Fock) : Fock :=
  transport after (remove v (transport middle (create w (transport before x))))

def insertionRemoval (before middle after : Matter →ₗ[ℂ] Matter)
    (v w : Matter) (x : Fock) : Fock :=
  transport after (create w (transport middle (remove v (transport before x))))

theorem transport_identity (x : Fock) :
    transport (LinearMap.id : Matter →ₗ[ℂ] Matter) x = x := by
  have h : coordinateOperator (LinearMap.id : Matter →ₗ[ℂ] Matter) = LinearMap.id := by
    ext v
    simp [coordinateOperator]
  simp [transport, h, ExteriorAlgebra.map_id]

/-- The two orders have one common contact normalisation, before source averaging. -/
theorem coincident_pair (before after : Matter →ₗ[ℂ] Matter)
    (v w : Matter) (x : Fock) :
    removalInsertion before LinearMap.id after v w x +
      insertionRemoval before LinearMap.id after v w x =
      inner ℂ v w • transport after (transport before x) := by
  simp only [removalInsertion, insertionRemoval, transport_identity]
  rw [← map_add, mixed_car]
  exact (transport after).toLinearMap.map_smul _ _

/-- Any one linear preparation functional preserves the transported contact relation. -/
theorem prepared_coincident_pair (before after : Matter →ₗ[ℂ] Matter)
    (v w : Matter) (x : Fock) (preparation : Fock →ₗ[ℂ] ℂ) :
    preparation (removalInsertion before LinearMap.id after v w x) +
      preparation (insertionRemoval before LinearMap.id after v w x) =
      inner ℂ v w * preparation (transport after (transport before x)) := by
  rw [← map_add, coincident_pair, map_smul]
  rfl

end GeneratedFoundations.Physical.SourceMatterEventInsertions
