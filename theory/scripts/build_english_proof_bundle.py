"""Make a dependency-ordered English reading copy of all project Lean proofs.

Canonical declarations remain in AgentUCT.lean and AgentUCTPaper/*.lean.
This script formats proof sources; it does not perform experiment admission.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from audit_proof_guide import lean_code

THEORY = Path(__file__).resolve().parents[1]
SOURCE = THEORY / "lean"
EVIDENCE = THEORY.parent / ".verification" / "reading-edition"

# English counterparts of the explanatory Chinese inline comments, in source order.
COMMENTS = {
    "OnlineMean": [
        "Q9.1: card + 1 is positive; the prior and every physical prediction sample lie in [0, cap].",
        "Q9.2a: Expand the index-based sample law, then exchange the two finite sums.",
        "Q9.2b: Each valid sample matches exactly one completion; repeated completions keep their separate indices.",
        "Q9.2: Apply the expectation identity to the constant bill 1; positive sample size gives total mass 1.",
        "Q9.3: Supply nonnegative history-dependent prices and their fixed envelope; pass the other hypotheses unchanged.",
    ],
    "DynamicCompletion": [
        "Q9 extension 1: Reduce history-dependent live prices to domination by fixed base completion cold costs.",
        "Extension 2: Nonnegative live prices, law weights, and gamma give a nonnegative actual penalty.",
        "Extension 3: Sum the resourcewise live <= base bounds in the same cache and law, then multiply by nonnegative gamma.",
    ],
    "TreeAllocation": [
        "Q2.2: The low-count child's bonus exceeds H + 2; Q >= 0 and penalty <= H make its index exceed 2.",
        "Q2.3: The selected child has Q <= 1 and a nonnegative penalty; its bonus must exceed 1 to reach that index.",
        "Q2.4: If the target still has count <= m at U, every selected child in the window has a logarithmic count bound.",
        "Q2.5: Sum the possible selections over children; the result is smaller than U - L, a contradiction.",
    ],
    "TreeCoverage": [
        "Q3.1: Induct on remaining depth; the terminal antichain forces a terminal observation to be that terminal itself.",
        "Q3.2: Remove the parent's at-most-one birth event; enough visits remain for the entire exploration window.",
        "Q3.3: Each child exceeds the recursive coverage threshold; apply induction at its smaller remaining depth.",
        "Q4.1: Persistent caches identify published resources with restorable resources, turning publication coverage into restoration coverage.",
    ],
    "TreeDecisionValue": [
        "L1: Ordinary index maximality gives a nonnegative index loss; U includes a bonus and is not a quality estimate alone.",
        "L2: Rearrange priced-index maximality to bound this loss by gamma times predicted cost saving.",
        "L3: With gamma > 0, ca > cb would make the upper bound negative, contradicting L1 and L2.",
        "L4: Assemble the three named intermediate conclusions.",
        "L5: Expand both absolute-error bounds; subtract their radii from predicted saving to bound physical saving.",
        "L6: Also control quality errors; weight cost errors by nonnegative gamma and rearrange the net-value bound.",
    ],
    "TreeForecast": [
        "Q4.2: All terminal demands are restorable after coverage, so every legal completion has an empty missing set.",
        "Q4.3: The empty finite sum is zero, and gamma times zero is zero; no forecast accuracy is needed for this step.",
    ],
    "TreeRate": [
        "Q7.1: Use the final parent count to fix the common logarithm and the suboptimal-child count bounds.",
        "Q7.2: Each child count is at most the parent count, so the same parent logarithm bounds its induction term.",
        "Q7.3: A positive gap uses Q6 and gap <= 1; a zero gap contributes exactly zero to N * gap.",
        "Q7.4: Retain birth deficit <= 1 in the actual parent decomposition; sum over the finite children and collect coefficients.",
        "Q7.5: Quantify over all histories and nodes during induction, so the hypothesis applies to every pre-selection prefix.",
        "Base case: Remaining depth zero forces a terminal; the antichain and fixed rewards give deficit zero.",
        "Induction step: Every legal child has smaller remaining depth; restrict run, reward table, and zero penalties to history prefixes.",
        "Use the tree-wide maximum branching factor for constants independent of the particular history and horizon T.",
        "Q8.1: Fix an instance-level positive delta before quantifying over events; it cannot be chosen again for each history or T.",
        "Q1: Combine the fixed table, legal execution, actual allocation rule, and common penalty envelope into a bounded run.",
        "Q3/Q4: Obtain zero penalties from successful persistent publication and coverage, using more than penalty boundedness.",
        "Q8.2: Every complete event backs up the root once; root count is T and root deficit is training-quality regret.",
    ],
    "TreeRateStep": [
        "Q6.1: The local action stream preserves actual child choices; burn-in covers cache coverage and mean-bias phases.",
        "Q5: The finite exploration window makes every child exceed the bias threshold; local and backed counts agree.",
        "The optimal child's D / N <= delta / 4 gives Q >= V(parent) - delta / 4 by the actual mean identity.",
        "Q6.2: Use actual index maximality; both completion cold penalties are zero after coverage.",
        "Q6.3: The squared-bonus identity bounds the current count; the final parent logarithm dominates earlier prefixes.",
        "Q6.4: Return to actual global counts; the counting lemma already includes early burn-in and the final increment +1.",
    ],
    "TreeSharedCache": [
        "Q8 domination 1: Fix delta before every history; dominate the actual penalty by a common nonnegative completion cold bill.",
        "Q4 domination 2: This tree's persistent publications cover all resources; union with extra shared resources preserves coverage.",
        "Actual penalty lies between zero and a zero complete cold penalty; antisymmetry gives zero, then apply Q7 induction.",
    ],
    "TreeRateAlgebra": [
        "Q5.1: The three terms in m ensure a positive denominator, A * log / n <= delta / 8, and B / n <= delta / 8.",
        "Q5.2: Use log(n + 1) <= 4 * sqrt(n), retaining all sign conditions when multiplying and dividing.",
        "Q6.2: Gap >= delta and optimal mean loss <= delta / 4 force a large bonus for the selected suboptimal child.",
        "Q6.3: Check nonnegative sides before squaring, multiply by the positive count, and eliminate the square root using bonus_sq.",
        "Q6.4: Split early and late selections; late pre-selection counts are <= cap, with +1 for the final update.",
    ],
}


def build() -> dict:
    ordered: list[tuple[str, Path]] = []
    external: list[str] = []
    seen: set[str] = set()
    active: set[str] = set()

    def visit(module: str) -> None:
        if module in seen:
            return
        if module in active:
            raise ValueError(f"Cyclic Lean imports: {module}")
        path = SOURCE / (module.replace(".", "/") + ".lean")
        active.add(module)
        for dependency in re.findall(
            r"^import\s+(\S+)", lean_code(path.read_text(encoding="utf-8")), re.MULTILINE
        ):
            if dependency == "AgentUCT" or dependency.startswith("AgentUCTPaper"):
                visit(dependency)
            elif dependency not in external:
                external.append(dependency)
        active.remove(module)
        seen.add(module)
        if module != "AgentUCTPaper":
            ordered.append((module, path))

    visit("AgentUCTPaper")
    lines = [*("import " + module for module in external), "", "/-!",
             "# AgentUCT: complete formal proofs, English reading edition",
             "",
             "All mathematical declarations and proof bodies from the project's 45 source",
             "modules follow in dependency order. The only edits are import consolidation,",
             "file-local section boundaries, and translation of explanatory comments.",
             "Canonical edits belong in AgentUCT.lean and AgentUCTPaper/*.lean; regenerate",
             "this reading edition with theory/scripts/build_english_proof_bundle.py.",
             "",
             "Read AgentUCTProofGuideEN.lean first for assumptions, conclusions, and open",
             "questions. Each SOURCE banner below identifies the original editable module.",
             "This edition imports Mathlib only. Import this edition OR AgentUCTPaper in",
             "a downstream module: they define the same public project declarations.",
             "Compiler verification establishes the stated conditional mathematics; the",
             "guide records which empirical and implementation guarantees remain open.",
             "-/", ""]
    source_map = []
    for index, (module, path) in enumerate(ordered, 1):
        original = path.read_text(encoding="utf-8")
        translated = []
        replacements = iter(COMMENTS.get(path.stem, []))
        for line in original.splitlines():
            if re.search(r"[\u3400-\u9fff]", line):
                if "--" not in line:
                    raise ValueError(f"Non-inline translation required in {module}")
                line = line.split("--", 1)[0] + "-- " + next(replacements)
            translated.append(line)
        if list(replacements):
            raise ValueError(f"Unused English translations for {module}")
        body = "\n".join(translated)
        code = lean_code(body)
        stack = []
        kept = []
        for line, code_line in zip(translated, code.splitlines()):
            if re.match(r"^import\s", code_line):
                continue
            opening = re.match(r"^(?:noncomputable\s+)?(section|namespace)(?:\s+(\S+))?\s*$", code_line)
            closing = re.match(r"^end(?:\s+(\S+))?\s*$", code_line)
            if opening:
                stack.append((opening[1], opening[2]))
            elif closing:
                kind, name = stack.pop()
                if closing[1] and closing[1] != name:
                    raise ValueError(f"Unmatched end in {module}")
            kept.append(line)
        if any(kind != "section" for kind, _ in stack):
            raise ValueError(f"Unclosed namespace in {module}")
        wrapper = f"CompleteProofSource{index:02d}"
        lines.extend(["/-!", f"## SOURCE {index:02d}: {path.relative_to(SOURCE).as_posix()}",
                      "Original definitions, theorem statements, and complete proof bodies.", "-/",
                      f"section {wrapper}"])
        start = len(lines) + 1
        lines.extend(kept)
        end = len(lines)
        lines.extend("end" + (" " + name if name else "") for _, name in reversed(stack))
        lines.extend([f"end {wrapper}", ""])
        source_map.append({"module": module, "canonical_file": path.relative_to(SOURCE).as_posix(),
                           "bundle_start_line": start, "bundle_end_line": end})
    output = SOURCE / "AgentUCTCompleteProofsEN.lean"
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    result = {"bundle": output.name, "module_count": len(ordered), "line_count": len(lines),
              "external_imports": external, "source_map": source_map}
    (EVIDENCE / "source-map.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return {key: result[key] for key in ("bundle", "module_count", "line_count")}


if __name__ == "__main__":
    print(json.dumps(build()))
