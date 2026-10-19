module

public import GeneratedFoundations.Probability.CompositionalGaussian
public import GeneratedFoundations.Probability.GaussianEntropy
public import GeneratedFoundations.Probability.SourceContinuity
public import GeneratedFoundations.Probability.GeneratedTangentLaw
public import GeneratedFoundations.Source.MinimalCarrier
public import GeneratedFoundations.Source.ComplexStructure
public import GeneratedFoundations.Source.OriginalLieFlow
public import GeneratedFoundations.Source.CarrierOrientation
public import GeneratedFoundations.Source.GeneratedSpectralCircle
public import GeneratedFoundations.Source.MinimalUnbiasedChange
public import GeneratedFoundations.Arithmetic.GeneratedFoundation
public import GeneratedFoundations.Arithmetic.ReducedExpressionFoundation
public import GeneratedFoundations.Arithmetic.CompleteHistorySource
public import GeneratedFoundations.Arithmetic.CompleteNaturalObject
public import GeneratedFoundations.Arithmetic.CompleteHistoryGeometry
public import GeneratedFoundations.Arithmetic.CompleteHistoryTransport
public import GeneratedFoundations.Arithmetic.CompleteHistoryDynamics
public import GeneratedFoundations.Arithmetic.JointOccupationScale
public import GeneratedFoundations.Arithmetic.InternalPrimes
public import GeneratedFoundations.Arithmetic.DifferenceOrder
public import GeneratedFoundations.Arithmetic.DifferenceUniversal
public import GeneratedFoundations.Correlation.Endpoints
public import GeneratedFoundations.Correlation.ComplexGaussianStates
public import GeneratedFoundations.Spectral.NeumannDomain
public import GeneratedFoundations.Spectral.DirichletMetric
public import GeneratedFoundations.Spectral.ComplexIntervalSobolev
public import GeneratedFoundations.Spectral.NeumannPoisson
public import GeneratedFoundations.Spectral.CircleOperator
public import GeneratedFoundations.Spectral.NeumannSpectrum
public import GeneratedFoundations.Spectral.NeumannCanonicalModes
public import GeneratedFoundations.Spectral.NeumannHeatSemigroup
public import GeneratedFoundations.Spectral.NeumannSpectralProjections
public import GeneratedFoundations.Spectral.NeumannHeatTrace
public import GeneratedFoundations.Spectral.GaussianHeatConvolution
public import GeneratedFoundations.Analysis.PrimeCapacity
public import GeneratedFoundations.Analysis.GaussianWindowCapacity
public import GeneratedFoundations.Analysis.GaussianPrefixTail
public import GeneratedFoundations.Analysis.NaturalSourceScaleBudget

/-!
# Arithmetic foundation from minimal unbiased compositional change

The arithmetic component of `CommonFoundation.generated` is a zero-input
conclusion. The canonical minimal change action and its unique compositional
law are generated internally; unit covariance fixes the dimensionless width
and the original complex rotation fixes the orientation. The endpoints,
reflecting operator and arithmetic objects are constructed internally. The
endpoint and boundary comparisons retain the calibrated readout definitions
and separated homogeneous boundary class used in those constructions.

The source results include the minimal carrier's group-action classification,
automatic smoothness and the representation differential in the original Lie
atlas, the trace inner product and oriented unit generators, and the global
left-invariant flow with its derived phase formula. Each orientation of the
actual carrier selects a unique trace-unit Lie generator. The entry also provides
the unique positive-parameter compositional Gaussian law on that actual trace
Lie line, its continuous Dirac extension and its expression on the original
tangent space, as well as entropy uniqueness and Gaussian overlap.
The complex Neumann operator is constructed on its Sobolev domain,
including the unique mean-zero solution for every mean-zero square-integrable
source. Reflection identifies the actual operator graph with the even part of
the independently constructed periodic second derivative. The measure ratio
gives a unitary normalization onto the Haar-even circle space, whose complete
Fourier basis yields the actual interval cosine basis. The original differential
operator is nonnegative and self-adjoint, has the exact weighted coefficient
domain, and admits a compact inverse of `I + A`. Its full spectrum consists
exactly of the simple cosine eigenvalues.
Every other complex shift has a unique bounded compact two-sided inverse on
the original domain. The heat multipliers form a strongly continuous,
self-adjoint contraction semigroup on the original interval space, preserve
constants, and have exactly the original Neumann domain as their strong
right-generator domain, with generator `-A/2`. At every positive parameter,
their basis-independent positive trace is finite and equals the complete
Gaussian spectral sum. The nonzero orthogonal projections onto original
eigenspaces form an intrinsic class with a unique natural-number order
coordinate, a unique zero mode, and unique immediate successors. The response
order is the same for every positive parameter and agrees with energy order.
The actual periodized source Gaussian has the required Fourier coefficients;
its Bochner convolution on each probability-Haar circle preserves constants
and nonnegative real functions. The Gaussian average of the actual original
change action is identified with that convolution and, through the reflection
isometry, with the Neumann heat operator on every interval input.
Unit norm and
positive real endpoint trace select a unique vector in each eigenline. Arithmetic is
defined on circle maps, and unique quotient-remainder
pairs are constructed by their native successor induction. Euclidean descent
constructs a unique gcd and a positive-part Bézout certificate; native descent
and the resulting divisor property give unique finite prime exponent profiles.
The actual pair quotient is an ordered integral domain with the universal
group and ring extension properties. The original oriented Lie flow also
determines a unique continuous group comparison with the reflecting spectral
circle, including its exact covering kernel and Fourier power characters.
The smooth source-circle comparison, shifted-window eigenmodes, oriented
positive angular observations and native arithmetic are joined in
`Arithmetic.GeneratedFoundation`. Its source statements include the original
Gaussian heat average on the generated window. Its arithmetic statements give
Peano recursion, unique finite prime profiles, infinitely many prime modes,
and a unique source-spectral transport between independent realizations.
The reduced-expression continuation retains ordered bracketing before
evaluation, removes only the six unit and absorbing-zero rules, has unique
normal forms and finite evaluation fibres, recovers the native mode semiring
as its evaluation quotient, and commutes with canonical scale and orientation
transport. Complete ordered histories above positive values carry both the
normalized flat conditional law and its persistent Gaussian root intensity.
Their complete finite fibres retain the canonical phase kernel together with
leaf charge, the two native node counts, orientation and capacity defect.
The source boundary and internal square-energy defects form an exact
telescoping ledger, so the complete transport descends to the root square
spectrum while the unresolved internal part does not.  The same positive
source uniquely fixes the detailed-balance merge rate for unit reverse split
rate.  A recursively renormalized Gaussian directory remains available only
as a fixed-scale local identity. The generated signed observation, exact
capacity-weighted energy, complete natural-prefix scale capacity and
cutoff-independent Gaussian tails are imported by this root. Finite harmonic
readouts remain separate research extensions.
These are statements about the defined generated construction, with each
classification's comparison class retained in its theorem.
-/
