module

public import GeneratedFoundations.Probability.CompositionalGaussian
public import GeneratedFoundations.Probability.SourceContinuity
public import GeneratedFoundations.Probability.GeneratedTangentLaw
public import GeneratedFoundations.Source.MinimalCarrier
public import GeneratedFoundations.Source.ComplexStructure
public import GeneratedFoundations.Source.OriginalLieFlow
public import GeneratedFoundations.Source.CarrierOrientation
public import GeneratedFoundations.Correlation.ComplexGaussianStates
public import GeneratedFoundations.Operations.GaussianOrderNeutral
public import GeneratedFoundations.Operations.HermitePhaseFlow
public import GeneratedFoundations.Operations.SourceSpinCornerFlow
public import GeneratedFoundations.Geometry.SourceSpinCentre
public import GeneratedFoundations.Physical.MatrixModuleClassification
public import GeneratedFoundations.Physical.MinimalFaithfulModule
public import GeneratedFoundations.Physical.ReversalRealConnector
public import GeneratedFoundations.Physical.SourcePhysicalInterface

/-!
# Physical interface: common source construction and classifications

The carrier action, source law, actual two-mode Gaussian source and its
compressed differential operations are exposed here. The affine lowering
operator is classified on its actual Schwartz core, with the generated vacuum
and Hilbert adjoint explicitly identified. Its successive raising operations
give a complete Hermite basis in the actual Lebesgue space. The order-neutral
differential oscillator has a unique self-adjoint extension, equal to its
graph closure, with the weighted square-summable coefficient domain. Its unitary
group is strongly continuous on the whole Hilbert space; differentiability at
zero characterizes precisely this generator domain. The central sign at a full
turn and identity at two full turns hold on the whole space.
The first two actual Hermite states support the compressed source spin
operators. Their exponentials generate all determinant-one unitary matrices,
and the controlled action on the full source space is faithful. The bounded
compressed Hamiltonian gives the local cycle `I - 2P`, retaining the identity
on its orthogonal complement. The operation group's centre is exactly
`{I, -I}`, and its algebraic central quotient has precisely the corresponding
two-element fibres. Its rotation double cover and projective-space
identification are separate geometric assertions.
`SourcePhysicalInterface.fromMinimalUnbiasedChange` takes only the minimal
unbiased compositional change datum. For every orientation and positive width,
it collects the
source geometry, exchange-retained response, frame classifications, least
faithful matter, vacuum phase lift and elementary connector. The source maps
identify their actual actions, rather than only matching dimensions. The
constructed frame transitions satisfy their cocycle without an extra cocycle
premise. Endpoints and reflecting evolution are constructed internally.
Classifications of competing realizations retain their stated
comparison classes and unitary equivalences.

The same Gaussian modes support the four-real-coordinate Hermitian readout and
its determinant-preserving congruence. This is the basic algebraic interface
for relativistic kinematics; subsequent spacetime and dynamical interpretation
belongs to the manuscript. This import graph includes the implemented proof sources.
Its current kernel-verification status is governed by a fresh build and axiom
audit, not by the presence of this entry point.
-/
