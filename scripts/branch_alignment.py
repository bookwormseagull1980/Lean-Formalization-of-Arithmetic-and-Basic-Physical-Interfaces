#!/usr/bin/env python3
"""Inventory the two Lean branches without treating correspondence as proof.

Every physical source module must be assigned explicitly.  Every ordinary
named declaration receives its own record, including its exact source hash.
Candidate mathematical modules are a work queue; only declaration-specific
review records can change a declaration's correspondence status.  This audit
also rejects imports from either branch into the other branch's entry.

No Lean build is launched by this script.  Its output is a source inventory,
not a compiled proof manifest.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from scripts import verify_foundations as verify


ROOT = Path(__file__).resolve().parents[1]
PREFIX = "GeneratedFoundations."
MATH_ENTRY = PREFIX + "ArithmeticFoundation"
PHYSICS_ENTRY = PREFIX + "PhysicalInterface"
COMMON_SOURCE = PREFIX + "Source.CommonSource"
REVIEW_STATUSES = frozenset({"shared_result", "proved_analogue", "physical_specific_result",
    "pending_construction", "pending_declaration_review"})
COMPLETE_REVIEW_STATUSES = frozenset({"shared_result", "proved_analogue", "physical_specific_result"})

# Assignments are explicit, so a newly added physical file cannot silently
# acquire a reviewed or completed status through a fallback category.
FAMILIES = {
    "A": {
        "method": "canonical source, law, correlation and endpoint construction",
        "physical": "SourceOrigin",
        "mathematical": ["Source.CanonicalRealization", "Arithmetic.GeneratedFoundation"],
    },
    "B": {
        "method": "actual operation algebra, prepared response and connected Hessian",
        "physical": "SourceQuadraticResponse SourcePreExchangeResponse SourceJointResponse "
            "SourceSplitResponse SourceInternalResponse SourcePhaseLift SourceSpinIdentification "
            "SourceVacuumTransport SourceCliffordChirality SourceCliffordConnector "
            "SourceExchangeConnectorTransport",
        "mathematical": ["Operations.SourceResponseCapacity", "Operations.SourceCoherentObservations",
            "Analysis.HistoryGibbsResponse", "Arithmetic.HistoryObservation"],
    },
    "C": {
        "method": "complete carriers, faithful actions, actual fibres and quotient properties",
        "physical": "CanonicalMatterBundle ColourNaturalConnector GlobalGaugeKernel "
            "MatrixModuleClassification MinimalFaithfulModule ReversalRealConnector "
            "SourceChargedQuotient SourceChargeLattice SourceChiralCarrier "
            "SourceColourPhase SourceCompleteMatterExactSequence SourceComplexColourCoordinates "
            "SourceFrameConstruction SourceGaugeCocycle SourceGaugeTransport SourceGaugeUnitary "
            "SourceGeneratedGaugeGroup SourceGlobalGaugeGroup SourceLocalizedFrames "
            "SourceLocalizedMatter SourceMatterCharge SourceMatterPhaseExponential "
            "SourceMinimalChiralPair SourceMinimalRepresentation SourcePhaseFrames "
            "SourcePseudorealCharts SourceReversalIsometry SourceReversalRealConnector "
            "SourceScalarConnector SourceScalarGaugeCovariance SourceScalarInvariant",
        "mathematical": ["Arithmetic.CompleteNaturalObject", "Arithmetic.HistoryPhaseBundle",
            "Arithmetic.GeneratedPrimeParity", "Analysis.FiniteResidueFourier",
            "Operations.SourceFiniteCornerAlgebra"],
    },
    "D": {
        "method": "actual differential geometry, closed domains and complete spectral systems",
        "physical": "SourceColourAdjointCasimir SourceColourCasimir SourceFourDimensionalGaugeKinematics "
            "SourceFrameConnection SourceGeneratedCoclosedOneForm SourceHermitianReadout "
            "SourceLorentzCarrier SourceRP3FieldSpectrum SourceTransverseTraceless",
        "mathematical": ["Geometry.SourceOneFormSystem", "Geometry.SourceSpinorSystem",
            "Geometry.SourceTensorTTSystem", "Spectral.NeumannSpectrum",
            "Spectral.NeumannHeatSemigroup", "Spectral.NeumannScaleTransport"],
    },
    "E": {
        "method": "common action, full variation, actual operator and covariance",
        "physical": "CanonicalYangMills SourceChargedResponse SourceCollectiveGravityClosure "
            "SourceConformalResponse SourceFourDimensionalYangMills SourceGeneratedRadialVariation "
            "SourceGeneratedYangMillsAction SourceGeneratedYangMillsFrameResponse "
            "SourceGeneratedYangMillsFullReduction SourceGeneratedYangMillsPhysicalHessian "
            "SourceGeneratedYangMillsResponseHessian SourceHaarConnectionHessian "
            "SourceHaarCurvatureTrace SourceHaarYangMillsAction SourceHaarYangMillsHessian "
            "SourceInternalYangMillsResponse SourceLinearizedGravity SourceNonlinearTensorAction "
            "SourceRadialMassIntertwiner",
        "mathematical": ["Analysis.HistoryGibbsResponse", "Analysis.HistoryReactionForm",
            "Analysis.HistoryReactionOperator", "Operations.GibbsConnectedResponse"],
    },
    "F": {
        "method": "rates, conservation, semigroups and finite/full operator scope",
        "physical": "SourceGeneratedYangMillsClosure SourceGeneratedYangMillsCoercivity "
            "SourceGeneratedYangMillsEquation SourceGeneratedYangMillsFlow "
            "SourceGeneratedYangMillsFock SourceGeneratedYangMillsGap SourceHaarYangMillsFock "
            "SourceYangMillsFockSemigroup",
        "mathematical": ["Arithmetic.CompleteHistoryDynamics", "Analysis.HistoryReactionOperator",
            "Analysis.HistoryReflectionFlow", "Arithmetic.JointOccupationScale",
            "Spectral.NeumannHeatSemigroup"],
    },
    "G": {
        "method": "capacity, observation windows, internal selection and certificates",
        "physical": "CanonicalYangMillsTT CanonicalYangMillsUnits SourceClosedCenterResponse "
            "SourceGaussianResponseDomain SourceGeneratedYangMillsNewtonAnchor "
            "SourcePhysicalInterface SourceResponseLevel SourceTensorResponseEndpoint "
            "SourceTorsionContent SourceTTEndpointInterval SourceTTGaussianCoefficient SourceTTResponse",
        "mathematical": ["Analysis.PrimeCapacity", "Analysis.GaussianWindowCapacity",
            "Analysis.GaussianPrefixTail", "Analysis.CapacityRestoredWindowBudget",
            "MathematicalInterface"],
    },
}

FEATURES = {
    "A": ["minimal carrier and classification", "complex orientation and original flow",
        "compositional probability law", "state and correlation", "UV/IR endpoints",
        "reflection window and boundary operator", "scale coordinates", "zero-input root"],
    "B": ["original differential operations", "ladders and finite corners",
        "Hermite and Neumann representations", "finite operation algebra", "central character",
        "coherent preparation and full observation", "finite Gibbs source", "connected Hessian"],
    "C": ["complete carrier", "central sectors", "kernel and quotient", "characters and charges",
        "faithful representation", "frames and transitions", "concrete bundle", "effective action"],
    "D": ["inner product and measure", "connection", "curvature identities", "scalar operator",
        "one-form Hodge system", "graded Dirac system", "tensor constraints", "domain and spectrum"],
    "E": ["same-source response", "common action", "first variation", "mixed Hessian",
        "equilibrium and stability", "Hessian/operator identity", "retained reduction", "nonlinear covariance"],
    "F": ["actual generation rates", "global detailed balance", "generator and domain",
        "semigroup", "conservation and exchange", "energy and dissipation", "occupation lift", "limits"],
    "G": ["capacity and response rank", "fluctuation/response", "window and tails",
        "internal selection", "certificate interface", "normalization and units",
        "complete observation reconstruction", "public interface and audit"],
}


def graph_closure(graph: dict[str, set[str]], entry: str) -> set[str]:
    found: set[str] = set()
    todo = [entry]
    while todo:
        item = todo.pop()
        if item not in found:
            found.add(item)
            todo.extend(graph.get(item, set()) - found)
    return found


def physical_assignments() -> dict[str, str]:
    result: dict[str, str] = {}
    for family, spec in FAMILIES.items():
        for name in spec["physical"].split():
            module = PREFIX + "Physical." + name
            if module in result:
                raise verify.VerificationError(f"Duplicate physical assignment: {module}")
            result[module] = family
    return result


def inventory(project: Path, reviews: dict | None = None, features: dict | None = None) -> dict:
    modules = verify.discover_modules(project)
    code = {m: verify.lean_code(p.read_text(encoding="utf-8-sig")) for m, p in modules.items()}
    graph = {m: verify.imports(c) & modules.keys() for m, c in code.items()}
    declaration_modules = {name: m for m, c in code.items()
        for name in verify.source_declarations(c)}
    all_names = declaration_modules.keys()
    assignments = physical_assignments()
    physical = {m for m in modules if m.startswith(PREFIX + "Physical.")}
    if physical != assignments.keys():
        raise verify.VerificationError(
            f"Physical assignments differ: new={sorted(physical - assignments.keys())}; "
            f"missing={sorted(assignments.keys() - physical)}")
    math_reachable = graph_closure(graph, MATH_ENTRY)
    physics_reachable = graph_closure(graph, PHYSICS_ENTRY)
    if COMMON_SOURCE not in math_reachable or COMMON_SOURCE not in physics_reachable:
        raise verify.VerificationError("Both branches must import the same common source entry")
    source_reachable = graph_closure(graph, COMMON_SOURCE)
    # General analysis lemmas (for example NonnegativeAdditive) belong to the
    # common mathematical library. A directory called Analysis is not itself
    # the arithmetic response branch.
    branch_modules = {m for m in modules if m.startswith(
        (PREFIX + "Arithmetic.", PREFIX + "Physical."))}
    branch_modules.update({MATH_ENTRY, PHYSICS_ENTRY, PREFIX + "MathematicalInterface"})
    if source_reachable & branch_modules:
        raise verify.VerificationError(
            f"Common source depends on a branch: {sorted(source_reachable & branch_modules)}")
    physical_imports = sorted(math_reachable & physical)
    if physical_imports:
        raise verify.VerificationError(f"Mathematical entry imports physical branch: {physical_imports}")
    arithmetic = {m for m in modules if m.startswith(PREFIX + "Arithmetic.")}
    arithmetic.update({MATH_ENTRY, PREFIX + "MathematicalInterface"})
    arithmetic_imports = sorted(physics_reachable & arithmetic)
    if arithmetic_imports:
        raise verify.VerificationError(f"Physical entry imports mathematical branch: {arithmetic_imports}")

    reviews = reviews or {}
    rows = []
    for module in sorted(physical):
        family = assignments[module]
        targets = [PREFIX + m for m in FAMILIES[family]["mathematical"]]
        for target in targets:
            if target not in modules:
                raise verify.VerificationError(f"Missing candidate module {target}")
        source_hash = hashlib.sha256(modules[module].read_bytes()).hexdigest()
        for name in sorted(verify.source_declarations(code[module])):
            review = reviews.get(name)
            if review:
                if review.get("source_sha256") != source_hash:
                    raise verify.VerificationError(f"Stale declaration review: {name}")
                for proof in review.get("mathematical_declarations", []):
                    if proof not in all_names:
                        raise verify.VerificationError(f"Missing mathematical declaration: {proof}")
                    if declaration_modules[proof] not in math_reachable:
                        raise verify.VerificationError(f"Mathematical declaration outside entry: {proof}")
                if review.get("status") not in REVIEW_STATUSES:
                    raise verify.VerificationError(f"Unknown declaration review status: {name}")
                if review["status"] in COMPLETE_REVIEW_STATUSES:
                    if not review.get("mathematical_declarations"):
                        raise verify.VerificationError(f"Review has no actual mathematical declarations: {name}")
                    for field in ("objects", "comparison", "hypotheses_and_scope"):
                        if not isinstance(review.get(field), str) or not review[field].strip():
                            raise verify.VerificationError(f"Review missing {field}: {name}")
            rows.append({
                "physical_declaration": name,
                "physical_module": module,
                "source_sha256": source_hash,
                "family": family,
                "candidate_mathematical_modules": targets,
                "correspondence_review": review or {"status": "pending_declaration_review"},
            })

    unknown = reviews.keys() - {r["physical_declaration"] for r in rows}
    if unknown:
        raise verify.VerificationError(f"Reviews refer to removed declarations: {sorted(unknown)}")
    feature_titles = {f"{g}{i}": title for g, titles in FEATURES.items()
        for i, title in enumerate(titles, 1)}
    if features is not None:
        if features.keys() != feature_titles.keys():
            raise verify.VerificationError("Feature ledger must cover all 56 explicit features")
        for feature, record in features.items():
            if record.get("scope_class") not in {
                    "shared_construction", "arithmetic_instance", "distinct_outputs", "partial_scope"}:
                raise verify.VerificationError(f"Unknown feature scope: {feature}")
            proofs = record.get("mathematical_declarations")
            if not isinstance(proofs, list) or not proofs:
                raise verify.VerificationError(f"Feature has no actual declarations: {feature}")
            for proof in proofs:
                if proof not in all_names or declaration_modules[proof] not in math_reachable:
                    raise verify.VerificationError(f"Feature target outside mathematical entry: {proof}")
            for field in ("objects", "construction", "hypotheses_and_scope"):
                if not isinstance(record.get(field), str) or not record[field].strip():
                    raise verify.VerificationError(f"Feature {feature} missing {field}")
    return {
        "schema_version": 1,
        "evidence": "source_inventory_only",
        "mathematical_entry": MATH_ENTRY,
        "physical_entry": PHYSICS_ENTRY,
        "common_source_entry": COMMON_SOURCE,
        "common_source_independent_of_branches": True,
        "mathematical_entry_independent_of_physical": True,
        "physical_entry_independent_of_mathematical": True,
        "physical_modules": len(physical),
        "physical_declarations": len(rows),
        "review_status_counts": dict(Counter(r["correspondence_review"]["status"] for r in rows)),
        "unreviewed_or_unconstructed": sum(r["correspondence_review"]["status"]
            not in COMPLETE_REVIEW_STATUSES for r in rows),
        "features": feature_titles,
        "feature_proof_ledger": features,
        "shared_dependencies": sorted(math_reachable & physics_reachable),
        "declarations": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=ROOT)
    parser.add_argument("--reviews", type=Path)
    parser.add_argument("--feature-ledger", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()
    reviews = json.loads(args.reviews.read_text(encoding="utf-8")) if args.reviews else {}
    features = json.loads(args.feature_ledger.read_text(encoding="utf-8")) if args.feature_ledger else None
    report = inventory(args.project, reviews, features)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    summary = {k: v for k, v in report.items()
        if k not in {"declarations", "shared_dependencies", "features", "feature_proof_ledger"}}
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    if args.require_complete and report["unreviewed_or_unconstructed"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
