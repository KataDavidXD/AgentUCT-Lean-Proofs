"""Build both retained proof editions and audit public theorem axioms."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "theory" / "lean"
sys.path.insert(0, str(ROOT / "theory" / "scripts"))
from audit_proof_guide import lean_code

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def inventory(paths: list[Path]) -> list[str]:
    names = []
    for path in paths:
        namespaces = []
        for line in lean_code(path.read_text(encoding="utf-8")).splitlines():
            begin = re.match(r"^\s*namespace\s+(\S+)", line)
            end = re.match(r"^\s*end\s+(\S+)", line)
            if begin:
                namespaces.append(begin[1])
            elif end and namespaces and end[1] == namespaces[-1]:
                namespaces.pop()
            decl = re.match(r"^\s*(?:@\[[^]]*\]\s*)*(?:theorem|lemma)\s+([\w.']+)", line)
            if decl:
                names.append(".".join([*namespaces, decl[1]]))
    if not names or len(set(names)) != len(names):
        raise RuntimeError("Missing or duplicate public theorem names")
    return names


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bootstrap", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / ".verification")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    lake = shutil.which("lake")
    if not lake or not shutil.which("lean"):
        raise RuntimeError("Install elan and add lean/lake to PATH")

    sources = sorted(SOURCE.glob("*.lean")) + sorted((SOURCE / "AgentUCTPaper").glob("*.lean"))
    mathematical = [SOURCE / "AgentUCT.lean", *sorted((SOURCE / "AgentUCTPaper").glob("*.lean"))]
    names = inventory(mathematical)
    report = {"date_utc": datetime.now(timezone.utc).isoformat(), "status": "running",
              "source_files": len(sources), "public_theorems_per_edition": len(names),
              "checks": [], "axiom_audits": []}

    def save() -> None:
        (output / "verification.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8")

    def run(label: str, command: list[str]) -> str:
        print(label, flush=True)
        log = output / (label + ".log")
        with log.open("wb") as stream:
            result = subprocess.run(command, cwd=SOURCE, stdout=stream,
                                    stderr=subprocess.STDOUT, check=False)
        text = log.read_text(encoding="utf-8", errors="replace")
        report["checks"].append({"label": label, "returncode": result.returncode})
        save()
        if result.returncode or re.search(r"\b(?:error|warning):", text):
            print(text[-4000:], file=sys.stderr)
            raise RuntimeError(f"{label} failed; inspect {log}")
        return text

    save()
    try:
        for path in sources:
            if re.search(r"\b(sorry|admit|axiom)\b", lean_code(path.read_text(encoding="utf-8"))):
                raise RuntimeError(f"Proof placeholder or custom axiom: {path.name}")
        report["lean_version"] = run("lean-version", [lake, "env", "lean", "--version"]).strip()
        if args.bootstrap:
            cache_roots = sorted({dep for path in sources for dep in re.findall(
                r"^import\s+(\S+)", lean_code(path.read_text(encoding="utf-8")), re.M)
                if dep.startswith("Mathlib.")})
            run("mathlib-cache", [lake, "exe", "cache", "get", *cache_roots])
        build = run("lake-build", [lake, "build"])
        if "Build completed successfully" not in build:
            raise RuntimeError("Lake did not report a completed build")
        config = tomllib.loads((SOURCE / "lakefile.toml").read_text(encoding="utf-8"))
        # All mathematical modules are imported by the configured entry point.
        # Check every additional root source, including all Audit modules.
        for path in sorted(SOURCE.glob("*.lean")):
            if path.stem not in config["defaultTargets"]:
                run(path.stem, [lake, "env", "lean", path.name])
        for label, module in (("modular", "AgentUCTPaper"),
                              ("english", "AgentUCTCompleteProofsEN")):
            audit = output / ("AuditAll-" + label + ".lean")
            audit.write_text("import " + module + "\n" + "\n".join(
                "#print axioms " + name for name in names) + "\n", encoding="utf-8")
            text = run("axioms-" + label, [lake, "env", "lean", str(audit)])
            records = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)
            records += [(name, "") for name in re.findall(
                r"'([^']+)' does not depend on any axioms", text)]
            seen = {name for name, _ in records}
            axioms = {a.strip() for _, deps in records for a in deps.split(",") if a.strip()}
            missing = sorted(set(names) - seen)
            unexpected = sorted(axioms - STANDARD_AXIOMS)
            report["axiom_audits"].append({"edition": label, "checked": len(set(names) & seen),
                                            "missing": missing, "nonstandard": unexpected})
            if missing or unexpected:
                raise RuntimeError(f"Incomplete or nonstandard axiom audit: {label}")
        report["status"] = "passed"
        save()
        print(json.dumps({key: report[key] for key in
                          ("status", "source_files", "public_theorems_per_edition")}))
    except Exception as exc:
        report["status"] = "failed"
        report["failure"] = str(exc)
        save()
        raise


if __name__ == "__main__":
    main()
