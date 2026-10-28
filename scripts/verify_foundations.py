#!/usr/bin/env python3
"""Verify the separately pinned generated-foundations Lean library.

This does not run physical calculations or change V5 verification records.
Source-only success is explicitly NOT a compiled-proof result. The declaration
index contains implemented claims; its optional ``planned`` list is not audited
as a list of proved claims. Mathematical adequacy of the printed hypotheses
still requires review, independently of kernel checking and axiom hygiene.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from uuid import uuid4


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROJECT = ROOT
VERIFIER_PATH = Path(__file__).resolve()
MANIFEST_NAME = "verification-manifest.json"
AUDIT_LOG = ".lake/foundations-audit.txt"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.34.0"
EXPECTED_VERSION = "4.34.0"
EXPECTED_MATHLIB_REV = "5ed2965256430c3649e86755f9576b54eca72435"
LIBRARY = "GeneratedFoundations"
BUILD_BATCH_SIZE = 2
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
ENVIRONMENT_PREFIX = "FOUNDATIONS_ENVIRONMENT "
NAMED_PREFIX = "FOUNDATIONS_NAMED "
ENVIRONMENT_METHOD = "import_all_local_modules_then_enumerate_environment_constants"
# Ordinary Lean identifiers may contain Unicode letters and numeric subscripts.
# Keep the whole identifier when generating the kernel's declaration audit.
NAME = r"[^\W\d][\w']*(?:\.[^\W\d][\w']*)*"
FORBIDDEN = re.compile(r"(?<![\w'])\b(?:sorry|admit|axiom)\b(?![\w'])")


class VerificationError(RuntimeError):
    """A check failed, or the evidence needed to perform it is missing."""


@dataclass(frozen=True)
class SourceState:
    modules: dict[str, Path]
    entries: tuple[str, ...]
    declarations: tuple[str, ...]
    indexed: tuple[str, ...]
    snapshot: dict[str, str]


def lean_code(text: str, *, keep_strings: bool = False) -> str:
    """Mask comments and strings, preserving newlines and character offsets.

Lean block comments nest. Ordinary escaped strings and raw r#"..."# strings
are masked too. This is source hygiene, not a replacement for Lean parsing or
the compiled, transitive axiom audit (which also catches generated sorryAx).
"""
    chars = list(text)
    i = 0

    def mask(start: int, end: int) -> None:
        for j in range(start, end):
            if chars[j] not in "\r\n":
                chars[j] = " "

    while i < len(text):
        start = i
        if text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0:
                i = len(text)
            mask(start, i)
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise VerificationError("Unterminated Lean block comment")
            mask(start, i)
        elif text[i] == '"' or re.match(r'r#+"', text[i:]):
            raw = re.match(r'r(#+)"', text[i:])
            if raw:
                end_marker = '"' + raw.group(1)
                i += len(raw.group(0))
                end = text.find(end_marker, i)
                if end < 0:
                    raise VerificationError("Unterminated Lean raw string")
                i = end + len(end_marker)
            else:
                i += 1
                while i < len(text):
                    if text[i] == "\\":
                        i += 2
                    elif text[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                else:
                    raise VerificationError("Unterminated Lean string")
            if not keep_strings:
                mask(start, min(i, len(text)))
        else:
            i += 1
    return "".join(chars)


def imports(code: str) -> set[str]:
    result: set[str] = set()
    pattern = rf"^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?({NAME}(?:[ \t]+{NAME})*)[ \t]*$"
    for match in re.finditer(pattern, code, re.MULTILINE):
        result.update(match.group(1).split())
    # Fail closed for unfamiliar import syntax instead of overlooking an edge.
    import_lines = re.findall(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b[^\n]*", code, re.MULTILINE)
    if len(import_lines) != len(list(re.finditer(pattern, code, re.MULTILINE))):
        raise VerificationError("Unsupported import syntax; use one import statement per line")
    return result


def source_declarations(code: str) -> set[str]:
    """Collect ordinary explicitly named declarations for extra type checks.

Exact indexed-name existence is ultimately checked by Lean. This source
inventory supplements, and does not bound, the complete compiled-environment
audit of private, local, anonymous-instance and macro-generated constants.
"""
    scopes: list[tuple[str, str]] = []
    names: set[str] = set()
    exported: list[str] | None = None
    for line in code.splitlines():
        stripped = line.strip()
        stripped = re.sub(r"^(?:@\[[^\]]*\]\s*)+", "", stripped)
        # Re-exported compatibility names remain part of the public source
        # API. They resolve to the original common proof in Lean, and must
        # not disappear from branch inventories when that proof is moved.
        export = re.match(rf"^export\s+{NAME}\s*\((.*)$", stripped)
        if export:
            exported = []
            stripped = export.group(1)
        if exported is not None:
            closed = ")" in stripped
            exported.extend(stripped.split(")", 1)[0].split())
            if closed:
                prefix = ".".join(value for kind, value in scopes if kind == "namespace")
                for name in exported:
                    if not re.fullmatch(NAME, name):
                        raise VerificationError(f"Unsupported exported declaration name: {name}")
                    names.add(f"{prefix}.{name}" if prefix else name)
                exported = None
            continue
        scope = re.match(rf"^(?:(?:noncomputable|public|private)\s+)*(namespace|section)\b(?:\s+({NAME}))?", stripped)
        if scope:
            scopes.append((scope.group(1), scope.group(2) or ""))
            continue
        if re.match(r"^mutual\b", stripped):
            scopes.append(("mutual", ""))
            continue
        if re.match(r"^end(?:\s|$)", stripped):
            if scopes:
                scopes.pop()
            continue
        # Attributes may precede a declaration on its line; other lines are
        # intentionally not interpreted as declarations inside tactic bodies.
        decl = re.match(
            rf"^(?:(?:protected|private|public|noncomputable|unsafe|partial)\s+)*"
            rf"(?:theorem|lemma|def|abbrev|opaque|structure|inductive|class|instance)\s+({NAME})(?![\w'.])",
            stripped,
        )
        if decl and not re.match(r"^(?:private|unsafe)\b", stripped):
            name = decl.group(1)
            if name.startswith("_root_."):
                name = name.removeprefix("_root_.")
            else:
                prefix = ".".join(value for kind, value in scopes if kind == "namespace")
                name = f"{prefix}.{name}" if prefix else name
            names.add(name)
    if exported is not None:
        raise VerificationError("Unterminated export declaration list")
    return names


def discover_modules(project: Path) -> dict[str, Path]:
    result = {}
    for path in sorted(project.rglob("*.lean")):
        relative = path.relative_to(project)
        if ".lake" in relative.parts or relative.as_posix() == "lakefile.lean":
            continue
        # Standalone command-line audit scripts are not library modules.
        # Their saved Lean output is checked separately; importing the
        # library under audit does not make that script a dependency.
        if relative.parts[0] == "verification" and path.name.endswith("-audit.lean"):
            continue
        if not path.resolve().is_relative_to(project.resolve()):
            raise VerificationError(f"Source symlink escapes project: {relative}")
        module = ".".join(relative.with_suffix("").parts)
        if not re.fullmatch(NAME, module):
            raise VerificationError(f"Unsupported module filename: {relative}")
        result[module] = path
    if not result:
        raise VerificationError("No local Lean modules found")
    return result


def fingerprint(project: Path) -> dict[str, str]:
    paths = list(discover_modules(project).values())
    paths += [project / name for name in (
        "lean-toolchain", "lakefile.lean", "lake-manifest.json", "theorem-index.json"
    )]
    return {path.relative_to(project).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def check_locks(project: Path) -> None:
    if (project / "lean-toolchain").read_text(encoding="utf-8-sig").strip() != EXPECTED_TOOLCHAIN:
        raise VerificationError(f"lean-toolchain must equal {EXPECTED_TOOLCHAIN}")
    lakefile = lean_code((project / "lakefile.lean").read_text(encoding="utf-8-sig"), keep_strings=True)
    pin = re.search(r'require\s+mathlib\s+from\s+git\s+"https://github\.com/leanprover-community/mathlib4\.git"\s*@\s*"([0-9a-f]{40})"', lakefile)
    if not pin or pin.group(1) != EXPECTED_MATHLIB_REV:
        raise VerificationError("lakefile.lean does not pin the expected mathlib revision")
    implicit_options = re.findall(r"⟨\s*`autoImplicit\s*,\s*(true|false)\s*⟩", lakefile)
    if implicit_options != ["false"]:
        raise VerificationError("The foundation library must set autoImplicit to false exactly once")
    manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    packages = manifest.get("packages", [])
    if not isinstance(packages, list):
        raise VerificationError("Invalid Lake manifest packages")
    mathlib = [p for p in packages if isinstance(p, dict) and p.get("name") == "mathlib"]
    if len(mathlib) != 1 or mathlib[0].get("rev") != EXPECTED_MATHLIB_REV:
        raise VerificationError("Lake manifest mathlib revision does not match the pin")
    if mathlib[0].get("type") != "git":
        raise VerificationError("mathlib must be a locked git dependency")
    for package in packages:
        if not isinstance(package, dict) or package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", str(package.get("rev", ""))):
            raise VerificationError("Every dependency must have an exact git revision in the manifest")


def check_sources(project: Path) -> SourceState:
    check_locks(project)
    modules = discover_modules(project)
    codes = {name: lean_code(path.read_text(encoding="utf-8-sig")) for name, path in modules.items()}
    for name, code in codes.items():
        if not re.search(r"^\s*module\s*$", code, re.MULTILINE):
            raise VerificationError(f"Local module must use the pinned Lean module system: {name}")
        if re.search(r"\bset_option\s+autoImplicit\s+true\b", code):
            raise VerificationError(f"Local autoImplicit true override is forbidden: {name}")
        forbidden = FORBIDDEN.search(code)
        if forbidden:
            line = code.count("\n", 0, forbidden.start()) + 1
            raise VerificationError(f"Forbidden {forbidden.group()} in {name}:{line}")
    index = json.loads((project / "theorem-index.json").read_text(encoding="utf-8-sig"))
    if index.get("schema_version") != 1:
        raise VerificationError("Unsupported theorem index schema_version")
    entries = index.get("entry_modules")
    if not isinstance(entries, list) or not entries or not all(isinstance(n, str) and n in modules for n in entries):
        raise VerificationError("entry_modules must name existing local modules")
    if LIBRARY not in entries:
        raise VerificationError(f"entry_modules must include {LIBRARY}")
    graph = {name: imports(code) for name, code in codes.items()}
    for name, dependencies in graph.items():
        missing = sorted(d for d in dependencies if (d == LIBRARY or d.startswith(LIBRARY + ".")) and d not in modules)
        if missing:
            raise VerificationError(f"Missing local imports in {name}: {missing}")
    visited: set[str] = set()
    pending = list(entries)
    while pending:
        name = pending.pop()
        if name not in visited:
            visited.add(name)
            pending.extend(graph[name] & modules.keys() - visited)
    uncovered = sorted(modules.keys() - visited)
    if uncovered:
        raise VerificationError(f"Local modules missing from entry import coverage: {uncovered}")
    claims = index.get("declarations")
    if not isinstance(claims, list) or not claims:
        raise VerificationError("The index must contain implemented declarations")
    module_decls = {name: source_declarations(code) for name, code in codes.items()}
    indexed = []
    for claim in claims:
        if not isinstance(claim, dict):
            raise VerificationError("Invalid declaration index entry")
        name, module = claim.get("name"), claim.get("module")
        if not isinstance(name, str) or not re.fullmatch(NAME, name) or module not in modules:
            raise VerificationError(f"Invalid indexed declaration: {claim}")
        if name not in module_decls[module]:
            raise VerificationError(f"Indexed declaration not found in stated source module: {name} ({module})")
        if name in indexed:
            raise VerificationError(f"Duplicate indexed declaration: {name}")
        for field in ("paper", "label", "scope"):
            if not isinstance(claim.get(field), str) or not claim[field].strip():
                raise VerificationError(f"Missing {field} for indexed declaration {name}")
        indexed.append(name)
    if "planned" in index and not isinstance(index["planned"], list):
        raise VerificationError("planned must be a list, separate from implemented declarations")
    declarations = set(indexed).union(*module_decls.values())
    return SourceState(modules, tuple(entries), tuple(sorted(declarations)), tuple(indexed), fingerprint(project))


def audit_source(state: SourceState) -> str:
    lines = ["module", ""] + [f"public import {module}" for module in sorted(state.modules)]
    # Public imports retain the ordinary name/type checks below. `import all`
    # additionally loads private and implementation constants in Lean's module
    # system; namespace prefixes and source regexes cannot enumerate those.
    lines += [f"import all {module}" for module in sorted(state.modules)]
    lines += ["public import Lean.Elab.Command", "public import Lean.Util.CollectAxioms",
              "public import Lean.Data.Json", "public meta import Lean.Elab.Command",
              "public meta import Lean.Util.CollectAxioms", "public meta import Lean.Data.Json"]
    lines += ["", "public section", "", "set_option format.width 160", "",
              "meta section", "open Lean Elab Command", "",
              'elab "foundations_progress " stage:str : command => do',
              '  IO.eprintln s!"FOUNDATIONS_PROGRESS {stage.getString} at {← IO.monoMsNow} ms"',
              '',
              'elab "foundations_named_axioms " requested:str id:ident : command => do',
              '  let names ← liftCoreM <| realizeGlobalConstWithInfos id',
              '  unless names.length == 1 do',
              '    throwError "Expected one resolved declaration for {requested.getString}"',
              '  let name := names.head!',
              '  let axioms ← Lean.collectAxioms name',
              f'  IO.println ("{NAMED_PREFIX}" ++ (Json.mkObj',
              '    [("name", toJson requested.getString), ("resolved", toJson name.toString),',
              '     ("axioms", toJson (axioms.map Name.toString))]).compress)',
              "end", "",
              f'foundations_progress "named declarations 0/{len(state.declarations)}"']
    for position, name in enumerate(state.declarations, 1):
        # Keep every signature check without expanding implementation-level
        # implicit instances in its display. Proof checking and the complete
        # transitive axiom inventory do not depend on pretty-printing options.
        lines += ["set_option pp.all false in", f"#check {name}",
                  "set_option pp.all false in", "set_option pp.universes false in",
                  f"#print axioms {name}", f'foundations_named_axioms "{name}" {name}']
        if position % 250 == 0 or position == len(state.declarations):
            lines.append(f'foundations_progress "named declarations {position}/{len(state.declarations)}"')
    module_names = ", ".join(f"`{module}" for module in sorted(state.modules))
    # The exhaustive utility elaborates a literal containing every local module.
    # Its work grows with the audit inventory, not with a theorem's proof search.
    # Remove the per-command heartbeat cap only for this generated utility and
    # its invocation; the subprocess wall-clock timeout remains enforced.
    lines += ["", "meta section", "open Lean Elab Command", "",
              "set_option maxHeartbeats 0 in",
              'elab "foundations_environment_audit" : command => do',
              '  IO.eprintln s!"FOUNDATIONS_PROGRESS environment inventory start at {← IO.monoMsNow} ms"',
              "  let env := (← getEnv).setExporting false",
              f"  let modules : Array Name := #[{module_names}]",
              "  let mut moduleIndices : Std.HashSet Nat := {}",
              "  for modName in modules do",
              "    let some idx := env.getModuleIdx? modName",
              '      | throwError "Audit module was not imported: {modName}"',
              "    unless env.header.modules[idx.toNat]!.importAll do",
              '      throwError "Audit module was not imported with all declarations: {modName}"',
              "    moduleIndices := moduleIndices.insert idx.toNat",
              "  let declarations := env.constants.toList.toArray.filter fun entry =>",
              "    match env.getModuleIdxFor? entry.1 with",
              "    | some idx => moduleIndices.contains idx.toNat",
              "    | none => false",
              "  let declarations := declarations.qsort fun a b => Name.lt a.1 b.1",
              '  IO.eprintln s!"FOUNDATIONS_PROGRESS environment selected {declarations.size} constants at {← IO.monoMsNow} ms"',
              "  let mut counts := Array.replicate env.header.moduleNames.size (0 : Nat)",
              "  for (name, _) in declarations do",
              "    let some idx := env.getModuleIdxFor? name",
              '      | throwError "Missing origin module for {name}"',
              "    counts := counts.modify idx.toNat (· + 1)",
              f'  IO.println ("{ENVIRONMENT_PREFIX}" ++ (Json.mkObj',
              '    [("event", toJson "begin"), ("count", toJson declarations.size)]).compress)',
              "  for modName in modules do",
              "    let some idx := env.getModuleIdx? modName",
              '      | throwError "Audit module was not imported: {modName}"',
              "    let count := counts[idx.toNat]!",
              f'    IO.println ("{ENVIRONMENT_PREFIX}" ++ (Json.mkObj',
              '      [("event", toJson "module"), ("module", toJson modName.toString),',
              '       ("count", toJson count), ("import_all", toJson true)]).compress)',
              "  let mut audited := 0",
              "  for (name, info) in declarations do",
              "    let some idx := env.getModuleIdxFor? name",
              '      | throwError "Missing origin module for {name}"',
              "    unless (env.checked.get.find? name).isSome do",
              '      throwError "Declaration absent from checked environment: {name}"',
              "    let axioms ← Lean.collectAxioms name",
              "    let kind := match info with",
              '      | .axiomInfo _ => "axiom"',
              '      | .defnInfo _ => "definition"',
              '      | .thmInfo _ => "theorem"',
              '      | .opaqueInfo _ => "opaque"',
              '      | .quotInfo _ => "quotient"',
              '      | .inductInfo _ => "inductive"',
              '      | .ctorInfo _ => "constructor"',
              '      | .recInfo _ => "recursor"',
              f'    IO.println ("{ENVIRONMENT_PREFIX}" ++ (Json.mkObj',
              '      [("event", toJson "declaration"), ("name", toJson name.toString),',
              '       ("module", toJson env.header.moduleNames[idx.toNat]!.toString),',
              '       ("kind", toJson kind), ("unsafe", toJson info.isUnsafe),',
              '       ("partial", toJson info.isPartial),',
              '       ("axioms", toJson (axioms.map Name.toString))]).compress)',
              "    audited := audited + 1",
              "    if audited % 500 == 0 || audited == declarations.size then",
              '      IO.eprintln s!"FOUNDATIONS_PROGRESS axioms {audited}/{declarations.size} at {← IO.monoMsNow} ms"',
              f'  IO.println ("{ENVIRONMENT_PREFIX}" ++ (Json.mkObj',
              '    [("event", toJson "end"), ("count", toJson declarations.size)]).compress)',
              "", "set_option maxHeartbeats 0 in", "foundations_environment_audit", ""]
    return "\n".join(lines) + "\n"


def module_build_order(state: SourceState) -> tuple[str, ...]:
    """Return local modules after their local imports; reject import cycles."""
    ordered: list[str] = []
    visited: set[str] = set()
    visiting: set[str] = set()

    def visit(module: str) -> None:
        if module in visiting:
            raise VerificationError(f"Local Lean import cycle at {module}")
        if module in visited:
            return
        visiting.add(module)
        code = lean_code(state.modules[module].read_text(encoding="utf-8-sig"))
        for dependency in sorted(imports(code)):
            if dependency in state.modules:
                visit(dependency)
        visiting.remove(module)
        visited.add(module)
        ordered.append(module)

    for module in sorted(state.modules):
        visit(module)
    return tuple(ordered)


def named_axiom_records(output: str, expected: tuple[str, ...]) -> dict[str, dict]:
    """Read Lean's resolved names, including exports which add no new constant.

    An alias is checked by Lean's name resolver, then linked to its actual
    compiled constant. The full environment audit still checks that constant,
    its origin module and every transitive axiom independently of source names.
    """
    records = {}
    expected_names = set(expected)
    for line in output.splitlines():
        if not line.startswith(NAMED_PREFIX):
            continue
        try:
            item = json.loads(line[len(NAMED_PREFIX):])
        except json.JSONDecodeError as exc:
            raise VerificationError("Malformed resolved declaration report") from exc
        if (not isinstance(item, dict) or set(item) != {"name", "resolved", "axioms"}
                or not isinstance(item.get("name"), str) or item["name"] not in expected_names
                or item["name"] in records or not isinstance(item.get("resolved"), str)
                or not re.fullmatch(NAME, item["resolved"])
                or not isinstance(item.get("axioms"), list)
                or not all(isinstance(ax, str) for ax in item["axioms"])
                or len(set(item["axioms"])) != len(item["axioms"])):
            raise VerificationError("Invalid or repeated resolved declaration report")
        unexpected = set(item["axioms"]) - ALLOWED_AXIOMS
        if unexpected:
            raise VerificationError(
                f"Disallowed transitive axioms for {item['name']}: {sorted(unexpected)}")
        records[item["name"]] = item
    if records and set(records) != expected_names:
        raise VerificationError("Incomplete resolved declaration coverage")
    return records


def check_axiom_output(output: str, expected: tuple[str, ...]) -> dict[str, list[str]]:
    resolved = named_axiom_records(output, expected)
    if resolved:
        return {name: sorted(item["axioms"]) for name, item in resolved.items()}
    # Scan the audit log once: rescanning it for every declaration makes the
    # parser quadratic in a complete library's otherwise modest report size.
    reports: dict[str, list[str]] = {name: [] for name in expected}
    pattern = rf"'({NAME})' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    for match in re.finditer(pattern, output):
        if match.group(1) in reports:
            reports[match.group(1)].append(match.group(2) or "")
    result = {}
    for name in expected:
        matches = reports[name]
        if len(matches) != 1:
            raise VerificationError(f"Expected one compiled axiom report for {name}, got {len(matches)}")
        used = {part.strip() for part in matches[0].split(",") if part.strip()}
        unexpected = used - ALLOWED_AXIOMS
        if unexpected:
            raise VerificationError(f"Disallowed transitive axioms for {name}: {sorted(unexpected)}")
        result[name] = sorted(used)
    return result


def check_environment_output(output: str, state: SourceState) -> tuple[dict, dict[str, list[str]]]:
    """Validate a complete compiled inventory, separately from named type checks.

    Module ownership comes from Lean, not declaration spelling. This includes
    private names, local/anonymous instances and macro-generated declarations
    retained in the compiled environment. Anonymous `example` commands which
    create no constant are checked while compiling their modules, not counted
    as declarations. This is Lean's own dependency audit, not an independent
    implementation of its kernel or an external proof-checker result.
    """
    records = []
    for line in output.splitlines():
        if line.startswith(ENVIRONMENT_PREFIX):
            try:
                records.append(json.loads(line[len(ENVIRONMENT_PREFIX):]))
            except json.JSONDecodeError as exc:
                raise VerificationError("Malformed compiled environment report") from exc
    if len(records) < 2 or not all(isinstance(item, dict) for item in records):
        raise VerificationError("Missing complete compiled environment report")
    first, last = records[0], records[-1]
    if (set(first) != {"event", "count"} or first.get("event") != "begin"
            or set(last) != {"event", "count"} or last.get("event") != "end"
            or type(first.get("count")) is not int or first["count"] < 0
            or type(last.get("count")) is not int or first["count"] != last["count"]):
        raise VerificationError("Incomplete or inconsistent compiled environment boundaries")
    module_counts: dict[str, int] = {}
    declarations: dict[str, dict] = {}
    axioms: dict[str, list[str]] = {}
    actual_counts = dict.fromkeys(state.modules, 0)
    kinds = {"axiom", "definition", "theorem", "opaque", "quotient", "inductive", "constructor", "recursor"}
    for item in records[1:-1]:
        module = item.get("module")
        if not isinstance(module, str) or module not in state.modules:
            raise VerificationError("Unexpected module in compiled environment report")
        if item.get("event") == "module":
            if (set(item) != {"event", "module", "count", "import_all"}
                    or module in module_counts or type(item.get("count")) is not int
                    or item["count"] < 0 or item.get("import_all") is not True):
                raise VerificationError("Invalid or repeated compiled module inventory")
            module_counts[module] = item["count"]
        elif item.get("event") == "declaration":
            name, used = item.get("name"), item.get("axioms")
            if (set(item) != {"event", "name", "module", "kind", "unsafe", "partial", "axioms"}
                    or not isinstance(name, str) or not name or name in declarations
                    or item.get("kind") not in kinds
                    or type(item.get("unsafe")) is not bool or type(item.get("partial")) is not bool
                    or not isinstance(used, list) or not all(isinstance(ax, str) for ax in used)
                    or len(used) != len(set(used))):
                raise VerificationError("Invalid or repeated compiled declaration inventory")
            unexpected = set(used) - ALLOWED_AXIOMS
            if unexpected:
                raise VerificationError(f"Disallowed transitive axioms for {name}: {sorted(unexpected)}")
            declarations[name] = {key: item[key] for key in ("module", "kind", "unsafe", "partial")}
            axioms[name] = sorted(used)
            actual_counts[module] += 1
        else:
            raise VerificationError("Unexpected compiled environment event")
    if module_counts != actual_counts or first["count"] != len(declarations):
        raise VerificationError("Compiled environment module or declaration coverage is incomplete")
    resolved = named_axiom_records(output, state.declarations)
    name_map = {name: resolved[name]["resolved"] if resolved else name for name in state.declarations}
    missing = set(name_map.values()) - declarations.keys()
    if missing:
        raise VerificationError(f"Named declarations missing from compiled environment: {sorted(missing)}")
    named_axioms = check_axiom_output(output, state.declarations)
    if any(axioms[name_map[name]] != used for name, used in named_axioms.items()):
        raise VerificationError("Named and complete environment axiom reports disagree")
    return ({"method": ENVIRONMENT_METHOD, "modules": dict(sorted(module_counts.items())),
             "declarations": dict(sorted(declarations.items())),
             "named_resolutions": dict(sorted(name_map.items())),
             "independent_checker": "not_run"}, dict(sorted(axioms.items())))


def stop_owned_process_tree(process: subprocess.Popen) -> None:
    """Stop only the process tree/session created for this logged command."""
    if os.name == "nt":
        subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                       text=True, capture_output=True, encoding="utf-8", errors="replace",
                       timeout=15, check=True)
    else:
        # Logged children start a new session, so this is never our caller's group.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    process.wait(timeout=10)


def run_logged_result(command: list[str], project: Path, timeout: int,
                      output_path: Path) -> tuple[int, str]:
    """Stream audit progress while retaining stdout + stderr log ordering."""
    options = {"creationflags": subprocess.CREATE_NEW_PROCESS_GROUP} if os.name == "nt" else {
        "start_new_session": True}
    process = subprocess.Popen(command, cwd=project, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               encoding="utf-8", errors="replace", bufsize=1,
                               env={**os.environ, "LEAN_NUM_THREADS": "1"}, **options)
    chunks: tuple[list[str], list[str]] = ([], [])
    reader_errors: list[str] = []
    progress_lock = threading.Lock()

    def collect(stream, destination: list[str]) -> None:
        try:
            for line in iter(stream.readline, ""):
                destination.append(line)
                if line.startswith("FOUNDATIONS_PROGRESS"):
                    with progress_lock:
                        print(line.rstrip("\r\n"), flush=True)
        except (OSError, ValueError) as error:
            reader_errors.append(str(error))
        finally:
            stream.close()

    readers = [threading.Thread(target=collect, args=(stream, destination), daemon=True)
               for stream, destination in zip((process.stdout, process.stderr), chunks)]
    deadline = time.monotonic() + timeout
    for reader in readers:
        reader.start()
    try:
        code = process.wait(timeout=timeout)
        for reader in readers:
            reader.join(timeout=max(0, deadline - time.monotonic()))
        if any(reader.is_alive() for reader in readers):
            raise subprocess.TimeoutExpired(command, timeout)
    except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
        cleanup_error = None
        try:
            stop_owned_process_tree(process)
        except (OSError, subprocess.SubprocessError) as failure:
            cleanup_error = str(failure)
        for reader in readers:
            reader.join(timeout=5)
        output = "".join(chunks[0]) + "".join(chunks[1])
        reason = (f"command timed out after {timeout} seconds"
                  if isinstance(error, subprocess.TimeoutExpired) else "command interrupted")
        marker = f"FOUNDATIONS_AUDIT_INCOMPLETE: {reason}\n"
        if cleanup_error is not None:
            marker += f"Process-tree cleanup failed: {cleanup_error}\n"
        if any(reader.is_alive() for reader in readers):
            marker += "Output readers did not finish; captured output may be truncated.\n"
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(marker + output, encoding="utf-8", newline="\n")
        print(f"Incomplete audit output saved: {output_path}", flush=True)
        if cleanup_error is not None:
            print(f"Process-tree cleanup failed: {cleanup_error}", file=sys.stderr, flush=True)
        raise
    output = "".join(chunks[0]) + "".join(chunks[1])
    output_path.parent.mkdir(parents=True, exist_ok=True)
    if reader_errors:
        output_path.write_text("FOUNDATIONS_AUDIT_INCOMPLETE: output capture failed\n" + output,
                               encoding="utf-8", newline="\n")
        raise VerificationError("Audit output capture failed: " + "; ".join(reader_errors))
    output_path.write_text(output, encoding="utf-8", newline="\n")
    return code, output


def run_result(command: list[str], project: Path, timeout: int,
               *, output_path: Path | None = None) -> tuple[int, str]:
    """Capture a process without interpreting its exit code.

    Only the Lake freshness probe may interpret code 3 as a rebuild request.
    All other callers must use ``run`` to reject any nonzero exit code.
    """
    print("RUN " + subprocess.list2cmdline(command), flush=True)
    if output_path is not None:
        code, output = run_logged_result(command, project, timeout, output_path)
        print(f"Complete declaration and axiom output: {output_path}", flush=True)
        diagnostics = re.findall(r"^.*(?:error:|warning:).*$", output, re.MULTILINE)
        for diagnostic in diagnostics:
            print(diagnostic, flush=True)
    else:
        result = subprocess.run(command, cwd=project, text=True, capture_output=True,
                                encoding="utf-8", errors="replace", timeout=timeout,
                                env={**os.environ, "LEAN_NUM_THREADS": "1"})
        code, output = result.returncode, result.stdout + result.stderr
        if output.strip():
            print(output.rstrip(), flush=True)
    return code, output


def run(command: list[str], project: Path, timeout: int,
        *, output_path: Path | None = None) -> str:
    code, output = run_result(command, project, timeout, output_path=output_path)
    if code:
        raise VerificationError(f"Command failed with exit code {code}")
    return output


def check_actual_dependencies(project: Path, timeout: int) -> dict[str, dict]:
    git = shutil.which("git")
    if not git:
        raise VerificationError("git is required to verify the actual dependency revisions")
    manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    packages_dir = project / manifest.get("packagesDir", ".lake/packages")
    if not packages_dir.resolve().is_relative_to(project.resolve()):
        raise VerificationError("Lake dependency directory escapes the project")
    evidence = {}
    for package in manifest["packages"]:
        name = package["name"]
        if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", name):
            raise VerificationError("Unsafe dependency name in manifest")
        folder = packages_dir / name
        if not folder.resolve().is_relative_to(project.resolve()):
            raise VerificationError(f"Dependency escapes project: {name}")
        actual = run([git, "-C", str(folder), "rev-parse", "HEAD"], project, timeout).strip()
        if actual != package["rev"]:
            raise VerificationError(f"Actual dependency revision differs from manifest: {name}")
        dirty = run([git, "-C", str(folder), "status", "--porcelain", "--untracked-files=no"], project, timeout).strip()
        if dirty:
            raise VerificationError(f"Tracked dependency files have local changes: {name}")
        if name in evidence:
            raise VerificationError(f"Duplicate dependency name in manifest: {name}")
        evidence[name] = {"revision": actual, "tracked_clean": True}
    mathlib_toolchain = (packages_dir / "mathlib" / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    if mathlib_toolchain != EXPECTED_TOOLCHAIN:
        raise VerificationError("Actual mathlib checkout requests another Lean toolchain")
    return evidence


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def resolve_lake(lake_exe: str | None) -> str:
    lake = str(Path(lake_exe).resolve()) if lake_exe else shutil.which("lake")
    if not lake or not Path(lake).is_file():
        raise VerificationError("Lake not found; pass --lake-exe or provide it on PATH")
    return lake


def tool_evidence(lake: str, project: Path, timeout: int) -> dict[str, str]:
    """Record actual versions and binaries without publishing host paths."""
    version = run([lake, "env", "lean", "--version"], project, timeout)
    if not re.search(rf"\bversion {re.escape(EXPECTED_VERSION)}(?:,|\))", version):
        raise VerificationError("Actual Lake environment uses the wrong Lean version")
    lake_version = run([lake, "--version"], project, timeout)
    if not re.search(rf"\bLean version {re.escape(EXPECTED_VERSION)}(?:,|\))", lake_version):
        raise VerificationError("Lake executable is not built for the pinned Lean version")
    prefix = run([lake, "env", "lean", "--print-prefix"], project, timeout).strip()
    lean = Path(prefix) / "bin" / ("lean.exe" if os.name == "nt" else "lean")
    return {"lean_version": version.strip(), "lake_version": lake_version.strip(),
            "lean_sha256": sha256_file(lean), "lake_sha256": sha256_file(Path(lake))}


def affected_build_order(state: SourceState, order: tuple[str, ...], output: str) -> tuple[str, ...]:
    """Restrict rebuilds to the stale local frontier and its dependents.

    Lake still checks the entire library before and after these rebuilds.
    Unrecognized output falls back to the complete topological order; this
    optimization never establishes freshness or replaces the compiled audit.
    """
    reported = set(re.findall(r"\bBuilding ([\w.]+)", output))
    if not reported or not reported <= state.modules.keys():
        return order
    affected = set(reported)
    for module in order:
        code = lean_code(state.modules[module].read_text(encoding="utf-8-sig"))
        if imports(code) & affected:
            affected.add(module)
    return tuple(module for module in order if module in affected)


def module_build_batches(state: SourceState, order: tuple[str, ...]) -> tuple[tuple[str, ...], ...]:
    """Batch only independent ready targets; never race an unfinished import."""
    pending = set(order)
    dependencies = {module: imports(lean_code(state.modules[module].read_text(encoding="utf-8-sig")))
                    & pending for module in order}
    batches = []
    while pending:
        batch = tuple(module for module in order
                      if module in pending and not dependencies[module] & pending)[:BUILD_BATCH_SIZE]
        if not batch:
            raise VerificationError("Local import cycle prevents a ready build batch")
        batches.append(batch)
        pending.difference_update(batch)
    return tuple(batches)


def build_modules(lake: str, project: Path, state: SourceState, timeout: int) -> tuple[str, tuple[str, ...]]:
    # Computing the complete graph first preserves cycle detection on a fresh build.
    order = module_build_order(state)
    code, output = run_result(
        [lake, "--no-cache", "--no-build", "build", LIBRARY] + ["+" + module for module in order],
        project, timeout)
    if code == 0:
        if re.search(r"\bwarning:", output, re.IGNORECASE):
            raise VerificationError("Lean freshness check emitted warnings")
        return "up_to_date", order
    if code != 3:
        raise VerificationError(f"Lake freshness check failed with exit code {code}")
    # In pinned Lake 4.34.0, code 3 requests a rebuild. It can coexist with other
    # errors, so it never establishes success or justifies skipping any target.
    # Submit bounded batches in topological order. Imports outside a batch have
    # already been built (or were fresh at the probe); independent targets can
    # compile together without starting the entire stale frontier at once.
    # Lean's worker limit alone does not bound Lake's compiler subprocesses.
    rebuild_order = affected_build_order(state, order, output)
    print(f"BATCH REBUILD: {len(rebuild_order)} affected local modules of {len(order)}; up to {BUILD_BATCH_SIZE} targets per batch; complete library check retained.", flush=True)
    warning_targets = []
    for batch in module_build_batches(state, rebuild_order):
        output = run([lake, "--no-cache", "build"] + ["+" + module for module in batch], project, timeout)
        if re.search(r"\bwarning:", output, re.IGNORECASE):
            warning_targets.extend(batch)
    output = run([lake, "--no-cache", "build", LIBRARY], project, timeout)
    if re.search(r"\bwarning:", output, re.IGNORECASE):
        warning_targets.append(LIBRARY)
    # Finish collecting diagnostics in the single build batch. Warnings still
    # reject verification before any axiom audit or success record is published.
    if warning_targets:
        raise VerificationError("Lean build emitted warnings in: " + ", ".join(warning_targets))
    return "batched_build", order


def manifest_target(project: Path, path: Path | None) -> Path:
    target = (path if path is not None else project / MANIFEST_NAME).resolve()
    protected = {p.resolve() for p in discover_modules(project).values()}
    protected.update((project / name).resolve() for name in
                     ("lean-toolchain", "lakefile.lean", "lake-manifest.json", "theorem-index.json", AUDIT_LOG))
    lock = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    packages = (project / lock.get("packagesDir", ".lake/packages")).resolve()
    if (target in protected or target == VERIFIER_PATH.resolve()
            or target.name.casefold() == "run_manifest.json" or target.suffix.casefold() != ".json"
            or target.is_relative_to(packages)):
        raise VerificationError("The independent manifest must not overwrite source, dependency, or numerical records")
    return target


def publish_manifest(path: Path, record: dict) -> None:
    """Replace only a complete success record; preserve the previous one on failure."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                         dir=path.parent, prefix="." + path.name + ".",
                                         suffix=".tmp", delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(record, stream, ensure_ascii=False, indent=2, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


def verify(project: Path, lake_exe: str | None, source_only: bool, timeout: int,
           *, manifest_path: Path | None = None) -> dict | None:
    state = check_sources(project)
    print(f"SOURCE CHECKS OK: {len(state.modules)} modules, {len(state.indexed)} indexed declarations", flush=True)
    if source_only:
        print("NOT COMPILED: source-only mode; no kernel or compiled axiom result is claimed.", flush=True)
        return None
    target = manifest_target(project, manifest_path)
    verifier_sha = sha256_file(VERIFIER_PATH)
    lake = resolve_lake(lake_exe)
    tools = tool_evidence(lake, project, timeout)
    dependencies = check_actual_dependencies(project, timeout)
    build_mode, order = build_modules(lake, project, state, timeout)
    with tempfile.TemporaryDirectory(prefix="generated-foundations-audit-") as temporary:
        audit = Path(temporary) / "FoundationsAudit.lean"
        audit.write_text(audit_source(state), encoding="utf-8", newline="\n")
        # Lake supplies the module setup, including public import information.
        # Direct `lake env lean` omits that setup for an external audit file.
        output = run([lake, "--no-cache", "lean", str(audit)], project, timeout,
                     output_path=project / AUDIT_LOG)
    if re.search(r"\bwarning:", output, re.IGNORECASE):
        raise VerificationError("Compiled declaration audit emitted warnings")
    environment_audit, axioms = check_environment_output(output, state)
    # Dependencies and tools are checked again to reject changes during a long build.
    if check_actual_dependencies(project, timeout) != dependencies:
        raise VerificationError("Dependency evidence changed during verification")
    if tool_evidence(lake, project, timeout) != tools:
        raise VerificationError("Tool evidence changed during verification")
    if fingerprint(project) != state.snapshot:
        raise VerificationError("Local sources or lock/index files changed during verification")
    if sha256_file(VERIFIER_PATH) != verifier_sha:
        raise VerificationError("Verifier changed during verification")
    # Bind the actual saved log, not a hash of a summary of its contents.
    log = project / AUDIT_LOG
    if log.read_bytes() != output.encode("utf-8"):
        raise VerificationError("Saved declaration audit log differs from compiler output")
    record = {
        "schema_version": 1, "kind": "generated-foundations-verification", "status": "passed",
        "verification_id": uuid4().hex, "verified_at": datetime.now(timezone.utc).isoformat(),
        "scope": "current_implemented_library", "semantic_review": "not_certified",
        "source_files": state.snapshot,
        "verifier": {"path": "scripts/verify_foundations.py", "sha256": verifier_sha},
        "tools": tools, "dependencies": dependencies, "build_mode": build_mode,
        "module_build_order": list(order), "entry_modules": list(state.entries),
        "indexed_declarations": list(state.indexed), "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "declaration_axioms": axioms,
        "environment_audit": environment_audit,
        "audit": {"path": AUDIT_LOG, "sha256": sha256_file(log),
                  "probe_sha256": hashlib.sha256(audit_source(state).encode("utf-8")).hexdigest()},
    }
    publish_manifest(target, record)
    print("FOUNDATIONS VERIFY PASSED", flush=True)
    print(f"Build mode: {build_mode}; {len(state.modules)} explicit modules; audited {len(axioms)} compiled declarations and checked {len(state.declarations)} named types.", flush=True)
    print(f"Independent verification record: {target}", flush=True)
    print(f"Indexed claims: {len(state.indexed)}. Planned entries are not counted as proved.", flush=True)
    print("Allowed axioms: " + ", ".join(sorted(ALLOWED_AXIOMS)), flush=True)
    print("Scope: current implemented library only; review printed theorem hypotheses separately.", flush=True)
    return record


def check_manifest(project: Path, path: Path | None, lake_exe: str | None, timeout: int) -> dict:
    """Recheck a historical success record without building or claiming a new proof run."""
    state = check_sources(project)
    target = manifest_target(project, path)
    record = json.loads(target.read_text(encoding="utf-8"))
    if not isinstance(record, dict):
        raise VerificationError("Manifest is not a complete verification record")
    required = {
        "schema_version": 1, "kind": "generated-foundations-verification", "status": "passed",
        "scope": "current_implemented_library", "semantic_review": "not_certified",
        "source_files": state.snapshot,
        "verifier": {"path": "scripts/verify_foundations.py", "sha256": sha256_file(VERIFIER_PATH)},
        "module_build_order": list(module_build_order(state)), "entry_modules": list(state.entries),
        "indexed_declarations": list(state.indexed), "allowed_axioms": sorted(ALLOWED_AXIOMS),
    }
    for name, expected in required.items():
        if record.get(name) != expected:
            raise VerificationError(f"Manifest is stale or incomplete: {name}")
    if not re.fullmatch(r"[0-9a-f]{32}", str(record.get("verification_id", ""))):
        raise VerificationError("Manifest has no valid verification identity")
    verified_at = datetime.fromisoformat(record.get("verified_at", ""))
    if verified_at.tzinfo is None or verified_at > datetime.now(timezone.utc):
        raise VerificationError("Manifest has an invalid verification time")
    if record.get("build_mode") not in {"up_to_date", "serial_build", "batched_build"}:
        raise VerificationError("Manifest has no successful build mode")
    log = project / AUDIT_LOG
    expected_audit = {"path": AUDIT_LOG, "sha256": sha256_file(log),
                      "probe_sha256": hashlib.sha256(audit_source(state).encode("utf-8")).hexdigest()}
    if record.get("audit") != expected_audit:
        raise VerificationError("Manifest audit log or probe is stale")
    output = log.read_text(encoding="utf-8")
    if re.search(r"\b(?:warning|error):", output, re.IGNORECASE):
        raise VerificationError("Saved audit log contains compiler diagnostics")
    environment_audit, axioms = check_environment_output(output, state)
    if record.get("environment_audit") != environment_audit:
        raise VerificationError("Manifest compiled environment coverage is incomplete or differs from the log")
    if record.get("declaration_axioms") != axioms:
        raise VerificationError("Manifest declaration axiom coverage is incomplete or differs from the log")
    lake = resolve_lake(lake_exe)
    if record.get("tools") != tool_evidence(lake, project, timeout):
        raise VerificationError("Manifest tool evidence is stale")
    if record.get("dependencies") != check_actual_dependencies(project, timeout):
        raise VerificationError("Manifest dependency evidence is stale")
    if fingerprint(project) != state.snapshot or sha256_file(VERIFIER_PATH) != required["verifier"]["sha256"]:
        raise VerificationError("Sources or verifier changed during manifest checking")
    if sha256_file(log) != expected_audit["sha256"] or json.loads(target.read_text(encoding="utf-8")) != record:
        raise VerificationError("Manifest or audit log changed during manifest checking")
    print("FOUNDATIONS MANIFEST CURRENT: recorded evidence matches the checked sources and environment.", flush=True)
    print(f"Verification identity: {record['verification_id']}. No new compilation or proof audit was performed.", flush=True)
    print("This does not establish manuscript coverage, full-chain completion, or numerical-run validity.", flush=True)
    return record


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=DEFAULT_PROJECT)
    parser.add_argument("--lake-exe", help="explicit path to the pinned lake executable")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--source-only", action="store_true", help="check sources and locks only; do not compile or claim proof verification")
    modes.add_argument("--check-manifest", action="store_true", help="recheck a saved record against current sources, tools and dependencies without compiling")
    parser.add_argument("--manifest", type=Path, help="independent proof record (default: project verification-manifest.json)")
    parser.add_argument("--timeout", type=int, default=1800, help="per-command timeout in seconds")
    args = parser.parse_args(argv)
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.source_only and args.manifest is not None:
        parser.error("--source-only does not write a verification manifest")
    try:
        if args.check_manifest:
            check_manifest(args.project_root.resolve(), args.manifest, args.lake_exe, args.timeout)
        else:
            verify(args.project_root.resolve(), args.lake_exe, args.source_only, args.timeout,
                   manifest_path=args.manifest)
    except (VerificationError, OSError, ValueError, TypeError, KeyError, subprocess.TimeoutExpired) as error:
        label = "FOUNDATIONS MANIFEST STALE OR INVALID" if args.check_manifest else "FOUNDATIONS VERIFY FAILED"
        print(f"{label}: {error}", file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    # Lean reports and mathematical declaration types contain Unicode symbols.
    # Redirected Windows streams otherwise inherit an incompatible code page.
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")
    raise SystemExit(main())
