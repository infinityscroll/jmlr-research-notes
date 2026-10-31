"""Check the frozen review package's integrity; this is not a proof checker."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def check(path, expected):
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Hash mismatch: {path.relative_to(ROOT)}")


def main():
    review = json.loads((ROOT / "review_manifest.json").read_text())
    for item in review["files"]:
        check(ROOT / item["path"], item["sha256"])

    sources = json.loads((ROOT / "source_manifest.json").read_text())
    for item in sources["files"]:
        if item.get("bundled_path"):
            check(ROOT / item["bundled_path"], item["sha256"])

    audits = json.loads((ROOT / "AUDIT_RECORD.json").read_text())
    for item in audits["files"]:
        check(ROOT / item["path"], item["sha256"])

    capsule = ROOT / "dependency_review"
    result = subprocess.run(
        [sys.executable, str(capsule / "verify_review.py")],
        cwd=capsule, text=True, capture_output=True, check=True,
    )
    evidence = json.loads(result.stdout)
    assert evidence["verified_internal_sources"] == 34
    assert evidence["acyclic_section_dependency_map"] is True
    assert evidence["full_external_articles_copied"] == 0
    print("PASS: manuscript, internal sources, audit records, and 34-source dependency map.")
    print("This checks file integrity and dependency metadata, not mathematical correctness.")


if __name__ == "__main__":
    main()
