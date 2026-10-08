"""Inspect the archived reading PDFs; rendering/layout evidence is recorded separately."""

import argparse
from datetime import datetime
import json
from pathlib import Path

from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {"AgentUCT_Proof_Sections_EN.pdf": 8,
            "AgentUCT_Supplement_Only_EN.pdf": 40}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "evidence" /
                        datetime.now().strftime("verification-%Y%m%d") / "pdf-inventory.json")
    args = parser.parse_args()
    report = {"pdf_edition": "2026-10-04 independent readers", "documents": [], "status": "passed"}
    for name, pages in EXPECTED.items():
        path = ROOT / "materials" / "pdf" / name
        reader = PdfReader(path)
        texts = [page.extract_text() or "" for page in reader.pages]
        valid = len(reader.pages) == pages and not reader.is_encrypted and all(text.strip() for text in texts)
        report["documents"].append({"file": path.relative_to(ROOT).as_posix(), "pages": len(reader.pages),
                                     "bytes": path.stat().st_size, "all_pages_have_text": all(text.strip() for text in texts),
                                     "status": "passed" if valid else "failed"})
        if not valid:
            report["status"] = "failed"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, ensure_ascii=False))
    if report["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
