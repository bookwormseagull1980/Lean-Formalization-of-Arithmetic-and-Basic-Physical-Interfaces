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
The physical component of `CommonFoundation.fromMinimalUnbiasedChange` takes
only the minimal unbiased compositional change datum. For every orientation
and positive width, it collects the
source geometry, exchange-retained response, frame classifications, least
faithful matter, vacuum phase lift and elementary connector. The source maps
identify their actual actions, rather than only matching dimensions. The
constructed frame transitions satisfy their cocycle without an extra cocycle
premise. The exact six-element gauge kernel and the unique realization of the
intrinsic effective operator group are included in the same output. Endpoints
and reflecting evolution are constructed internally.
Classifications of competing realizations retain their stated
comparison classes and unitary equivalences.

The same Gaussian modes support the four-real-coordinate Hermitian readout and
its determinant-preserving congruence.  The resulting four-carrier supports the
generated gauge connection and its locally covariant colour Yang--Mills
curvature.  On its three spatial directions, the transverse--traceless
constraints have exactly two polarization amplitudes.  The tensor response
endpoint, the uniquely selected local linear Einstein operator, its pure-gauge
identity, TT reduction and massless simple pole are included in the compiled
physical root output. The generated left--right source representations supply
a complete bidegree family with calculated dimensions, central characters and
Casimir operators. The actual projective scalar spectrum and both its finite
and complete conformal restoring responses are connected to the closed source
quotient operator. The complete response is continuous, strictly increasing
and unbounded on the nonnegative line; every positive source drive therefore
has one positive balance, whose positive curvature supplies the normalized
spectral bottom of the complete even scalar tower. At the unit of the generated
response coordinate this selects a canonical balance and positive spectral
bottom without an additional coupling or scale datum. The generated critical
radius and colour feedback then select a unique condensed Yang--Mills
coordinate. The normalized radial/scalar block and the complete positive-odd
coclosed colour-connection tower have a common strictly positive direct-sum
spectral bottom. Field-type branch labels
remain outside the root package until their
differential-operator classification is derived. This import graph includes
the implemented proof sources.
Its current kernel-verification status is governed by a fresh build and axiom
audit, not by the presence of this entry point.
-/
