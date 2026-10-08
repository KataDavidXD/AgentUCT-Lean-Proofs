"""Inventory Lean proof declarations and inspect their compiler-reported dependencies.

This is a proof audit, with no experiment admission, source equality or digest check.
Prepare before the WSL build; finish after AuditAllProject.lean has been checked.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

THEORY = Path(__file__).resolve().parents[1]
SOURCE = THEORY / "lean"
EVIDENCE = THEORY / "evidence" / "proof-guide-20261004"
GUIDE = "AgentUCTProofGuide"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def lean_code(text: str) -> str:
    """Mask nested comments and strings, retaining source line positions."""
    result: list[str] = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            result.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            result.append(" ")
            i += 1
            while i < len(text):
                ch = text[i]
                result.append("\n" if ch == "\n" else " ")
                i += 1
                if ch == "\\" and i < len(text):
                    result.append(" ")
                    i += 1
                elif ch == '"':
                    break
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def prepare() -> dict:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    files = [SOURCE / "AgentUCT.lean", *sorted((SOURCE / "AgentUCTPaper").glob("*.lean"))]
    declarations = []
    forbidden = []
    for path in files:
        namespaces = []
        for line, code in enumerate(lean_code(path.read_text(encoding="utf-8")).splitlines(), 1):
            namespace = re.match(r"^\s*namespace\s+(\S+)", code)
            ending = re.match(r"^\s*end\s+(\S+)", code)
            if namespace:
                namespaces.append(namespace[1])
            elif ending and namespaces and ending[1] == namespaces[-1]:
                namespaces.pop()
            declaration = re.match(
                r"^\s*(?:@\[[^]]*\]\s*)*(theorem|lemma)\s+([\w.']+)", code
            )
            if declaration:
                declarations.append({
                    "name": ".".join([*namespaces, declaration[2]]),
                    "file": path.relative_to(SOURCE).as_posix(), "line": line,
                })
            if re.search(r"\b(sorry|admit|axiom)\b", code):
                forbidden.append({"file": path.relative_to(SOURCE).as_posix(), "line": line})
    guide_code = lean_code((SOURCE / (GUIDE + ".lean")).read_text(encoding="utf-8"))
    guide_refs = re.findall(r"^#check\s+(\S+)", guide_code, re.MULTILINE)
    report = {
        "date": "2026-10-04", "proof_source_files": len(files),
        "declaration_count": len(declarations), "declarations": declarations,
        "guide_reference_count": len(guide_refs), "guide_references": guide_refs,
        "entry_module": GUIDE,
        "proof_placeholders_or_custom_axioms": forbidden,
        "scope": "All public theorem/lemma declarations in AgentUCT and AgentUCTPaper modules",
        "policy": "CPU proof tooling only; no model calls, GPU changes, experiment digests, "
                  "source-equality gates or predicted-cost admission checks.",
        "verification": "pending compiler build and dependency audit",
    }
    (EVIDENCE / "source-inventory.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    (EVIDENCE / "AuditAllProject.lean").write_text(
        "import " + GUIDE + "\n\n" + "\n".join(
            "#print axioms " + declaration["name"] for declaration in declarations
        ) + "\n", encoding="utf-8"
    )
    if forbidden:
        raise RuntimeError(f"Lean source contains {len(forbidden)} proof audit findings")
    return report


def finish() -> dict:
    report = json.loads((EVIDENCE / "source-inventory.json").read_text(encoding="utf-8"))
    log = (EVIDENCE / "lean-axioms.log").read_text(encoding="utf-8")
    records = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)
    records += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    checked = {name: {a.strip() for a in axioms.split(",") if a.strip()}
               for name, axioms in records}
    expected = {decl["name"] for decl in report["declarations"]}
    missing = sorted(expected - checked.keys())
    unexpected = sorted({axiom for axioms in checked.values() for axiom in axioms} - STANDARD_AXIOMS)
    build = (EVIDENCE / "lean-build.log").read_text(encoding="utf-8")
    report.update({
        "dependency_checked_count": len(expected & checked.keys()),
        "missing_dependency_checks": missing, "nonstandard_axioms": unexpected,
        "axioms": sorted({axiom for axioms in checked.values() for axiom in axioms}),
        "build_completed": "Build completed successfully" in build,
        "verification": "passed" if not missing and not unexpected and
                        "Build completed successfully" in build else "failed",
    })
    (EVIDENCE / "verification.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    if report["verification"] != "passed":
        raise RuntimeError(f"Proof verification failed: missing={missing}, axioms={unexpected}")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["prepare", "finish"])
    parser.add_argument("--guide", default=GUIDE)
    parser.add_argument("--evidence", default=EVIDENCE.name)
    args = parser.parse_args()
    GUIDE = args.guide
    EVIDENCE = THEORY / "evidence" / args.evidence
    result = prepare() if args.mode == "prepare" else finish()
    print(json.dumps({k: result[k] for k in (
        "verification", "proof_source_files", "declaration_count", "guide_reference_count"
    )}, ensure_ascii=False))
