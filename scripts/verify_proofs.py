"""Build/audit the archived Lean project, using CPU tooling and no model calls."""

from __future__ import annotations

import argparse
from datetime import datetime
import json
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "theory" / "lean"
sys.path.insert(0, str(ROOT / "theory" / "scripts"))
from audit_proof_guide import lean_code

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def inventory(paths: list[Path]) -> list[dict]:
    declarations = []
    for path in paths:
        namespaces = []
        for number, line in enumerate(lean_code(path.read_text(encoding="utf-8")).splitlines(), 1):
            begin = re.match(r"^\s*namespace\s+(\S+)", line)
            end = re.match(r"^\s*end\s+(\S+)", line)
            if begin:
                namespaces.append(begin[1])
            elif end and namespaces and end[1] == namespaces[-1]:
                namespaces.pop()
            decl = re.match(r"^\s*(?:@\[[^]]*\]\s*)*(theorem|lemma)\s+([\w.']+)", line)
            if decl:
                declarations.append({"name": ".".join([*namespaces, decl[2]]),
                                     "file": path.relative_to(SOURCE).as_posix(), "line": number})
    if not declarations or len({x["name"] for x in declarations}) != len(declarations):
        raise RuntimeError("Missing or duplicate public theorem inventory")
    return declarations


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bootstrap", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = (args.output or ROOT / "evidence" / datetime.now().strftime("verification-%Y%m%d")).resolve()
    output.mkdir(parents=True, exist_ok=True)
    lake = shutil.which("lake")
    lean = shutil.which("lean")
    if not lake or not lean:
        raise RuntimeError("Install elan and add lean/lake to PATH")
    all_sources = sorted(SOURCE.glob("*.lean")) + sorted((SOURCE / "AgentUCTPaper").glob("*.lean"))
    math_sources = [SOURCE / "AgentUCT.lean", *sorted((SOURCE / "AgentUCTPaper").glob("*.lean"))]
    declarations = inventory(math_sources)
    forbidden = []
    for path in all_sources:
        for number, line in enumerate(lean_code(path.read_text(encoding="utf-8")).splitlines(), 1):
            if re.search(r"\b(sorry|admit|axiom)\b", line) and not line.lstrip().startswith("#print axioms "):
                forbidden.append({"file": path.relative_to(SOURCE).as_posix(), "line": number})
    config = tomllib.loads((SOURCE / "lakefile.toml").read_text(encoding="utf-8"))
    report = {"date": datetime.now().astimezone().isoformat(), "status": "running",
              "policy": "CPU proof tooling only; no model calls, GPU changes, custom experiment "
                        "fingerprint/SHA/source-byte gates, or predicted-cost admission checks.",
              "source_files": len(all_sources), "mathematical_source_files": len(math_sources),
              "public_theorems": len(declarations), "declarations": declarations,
              "default_targets": config["defaultTargets"], "checks": [],
              "proof_placeholders_or_custom_axioms": forbidden}

    def save() -> None:
        (output / "verification.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n",
                                                   encoding="utf-8")

    def run(label: str, command: list[str]) -> str:
        print(label, flush=True)
        log = output / (label + ".log")
        with log.open("wb") as stream:
            result = subprocess.run(command, cwd=SOURCE, stdout=stream,
                                    stderr=subprocess.STDOUT, check=False)
        text = log.read_text(encoding="utf-8", errors="replace")
        report["checks"].append({"label": label, "command": command, "returncode": result.returncode,
                                 "log": log.name})
        save()
        if result.returncode:
            print(text[-6000:], file=sys.stderr)
            raise RuntimeError(f"{label} failed: {log}")
        return text

    save()
    try:
        if forbidden:
            raise RuntimeError("Source proof placeholders or custom axioms found")
        report["lean_version"] = run("lean-version", [lean, "--version"]).strip()
        report["lake_version"] = run("lake-version", [lake, "--version"]).strip()
        if args.bootstrap:
            cache_roots = sorted({dependency for path in all_sources for dependency in
                                  re.findall(r"^import\s+(\S+)", lean_code(path.read_text(encoding="utf-8")), re.M)
                                  if dependency.startswith("Mathlib.")})
            run("mathlib-cache", [lake, "exe", "cache", "get", *cache_roots])
        build = run("lake-build", [lake, "build"])
        report["build_completed"] = "Build completed successfully" in build
        if not report["build_completed"]:
            raise RuntimeError("Lake did not report a completed build")
        modules = {p.relative_to(SOURCE).with_suffix("").as_posix().replace("/", "."): p for p in all_sources}
        covered = set()

        def cover(module: str) -> None:
            if module not in modules or module in covered:
                return
            covered.add(module)
            for dep in re.findall(r"^import\s+(\S+)", lean_code(modules[module].read_text(encoding="utf-8")), re.M):
                cover(dep)

        for target in config["defaultTargets"]:
            cover(target)
        report["default_build_source_files"] = len(covered)
        for module in sorted(modules.keys() - covered):
            run(module, [lake, "env", "lean", str(modules[module].relative_to(SOURCE))])
        guides = {}
        for module in ("AgentUCTProofGuide", "AgentUCTProofGuideEN"):
            run(module, [lake, "env", "lean", module + ".lean"])
            guides[module] = len(re.findall(r"^#check\s+", lean_code(modules[module].read_text(encoding="utf-8")), re.M))
        report["guide_references"] = guides
        expected = {item["name"] for item in declarations}
        report["axiom_audits"] = []
        for label, module in (("modular", "AgentUCTPaper"), ("english", "AgentUCTCompleteProofsEN")):
            audit = output / ("AuditAll-" + label + ".lean")
            audit.write_text("import " + module + "\n\n" + "\n".join(
                "#print axioms " + item["name"] for item in declarations) + "\n", encoding="utf-8")
            text = run("all-public-axioms-" + label, [lake, "env", "lean", str(audit)])
            records = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
            records += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
            seen = {name for name, _ in records}
            axioms = {a.strip() for _, deps in records for a in deps.split(",") if a.strip()}
            missing, unexpected = sorted(expected - seen), sorted(axioms - STANDARD_AXIOMS)
            report["axiom_audits"].append({"edition": label, "checked_theorems": len(expected & seen),
                                            "missing": missing, "axioms": sorted(axioms),
                                            "nonstandard_axioms": unexpected})
            if missing or unexpected:
                raise RuntimeError(f"Incomplete/nonstandard axiom audit: {label}")
        run("tactics-example", [lake, "env", "lean", str(ROOT / "workflow" / "examples" / "Tactics.lean")])
        diagnostics = []
        for check in report["checks"]:
            for line in (output / check["log"]).read_text(encoding="utf-8", errors="replace").splitlines():
                if re.search(r"\b(?:error|warning):", line):
                    diagnostics.append({"log": check["log"], "message": line})
        report["diagnostics"] = diagnostics
        if diagnostics:
            raise RuntimeError("Compiler reported error/warning diagnostics")
        report["checked_source_files"] = len(all_sources)
        report["status"] = "passed"
        save()
        print(json.dumps({"status": report["status"], "checked_source_files": len(all_sources),
                          "public_theorems_per_edition": len(declarations), "guide_references": guides}))
    except Exception as exc:
        report["status"] = "failed"
        report["failure"] = str(exc)
        save()
        raise


if __name__ == "__main__":
    main()
