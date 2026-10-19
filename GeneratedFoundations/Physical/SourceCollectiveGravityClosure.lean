module

public import GeneratedFoundations.Physical.SourceLinearizedGravity
public import GeneratedFoundations.Physical.SourceTransverseTraceless

/-!
# Collective linear gravity closure

This module names the local closure of the **collective** gravity response.
It deliberately does not introduce an independent graviton field or a
separate gravitational Fock space: the two TT polarizations are the
collective tensor channel of the generated source, and the local response is
the Fierz--Pauli/linear Einstein operator on that channel.

What is closed here:

* the TT carrier has dimension two;
* the linearized operator annihilates pure gauge;
* it satisfies the linearized conservation/Bianchi identity;
* it is the unique local two-derivative operator in the stated
  five-coefficient class;
* on TT it reduces to `Q^2 I_2` and has the massless simple pole.

The nonlinear Einstein completion and the stress-tensor null-shell
exclusion are **not** claimed here; they belong to the effective macroscopic
completion layer, not to an independent microscopic gravitational field.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceCollectiveGravityClosure

open SourceLinearizedGravity SourceTransverseTraceless

/-- The local collective gravity response. -/
structure Conclusions : Prop where
  tt_dimension : Module.finrank ℝ TTMode = 2
  linearized : SourceLinearizedGravity.Properties

theorem generated : Conclusions where
  tt_dimension := ttMode_finrank
  linearized := sourceLinearizedGravityProperties

end GeneratedFoundations.Physical.SourceCollectiveGravityClosure
