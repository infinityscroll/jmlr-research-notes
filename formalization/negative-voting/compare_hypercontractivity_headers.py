#!/usr/bin/env python3
"""Conservative source-header comparison for the attributed compatibility port."""
from pathlib import Path
import collections
import json
import re
from verify_hypercontractivity import stripped_lean

ROOT = Path(__file__).resolve().parent
START = re.compile(r"(?m)^[ \t]*((?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)(theorem|lemma|def|abbrev|opaque)\s+([\w'.]+)")


def headers(source):
    source = stripped_lean(source)
    found = {}
    counter = collections.Counter()
    for match in START.finditer(source):
        level = 0
        at = match.end()
        end = None
        while at < len(source):
            char = source[at]
            if level == 0 and source.startswith(":=", at):
                end = at
                break
            if level == 0 and source.startswith("where", at) and (at == 0 or source[at-1].isspace()):
                end = at
                break
            if char in "([{⟨":
                level += 1
            elif char in ")]}⟩":
                level -= 1
            at += 1
        if end is None:
            raise SystemExit("Cannot parse declaration header: " + match.group(3))
        key = match.group(2) + " " + match.group(3)
        counter[key] += 1
        key += " #" + str(counter[key])
        found[key] = {"private": "private" in match.group(1),
                      "header": " ".join(source[match.start():end].split())}
    return found


def main():
    provenance = json.loads((ROOT / "HYPERCONTRACTIVITY_PROVENANCE.json").read_text())
    reports = []
    for entry in provenance["files"]:
        path = entry["path"]
        original = headers((ROOT / "third_party/markov-semigroups/originals" / path).read_text())
        current = headers((ROOT / path).read_text())
        changed = [{"name": name, "before": value, "after": current[name]}
                   for name, value in original.items() if name in current and value != current[name]]
        reports.append({"path": path, "original_count": len(original), "ported_count": len(current),
                        "changed": changed,
                        "removed": [name for name in original if name not in current],
                        "added": [name for name in current if name not in original]})
    result = {"method": "Whitespace-normalized declaration headers before top-level := or where; comments stripped with nesting. Public theorem/lemma/def/abbrev/opaque headers, plus private headers; structures and anonymous instances are outside this source-level comparison.",
              "files": reports}
    (ROOT / "HYPERCONTRACTIVITY_DECLARATION_HEADER_COMPARISON.json").write_text(json.dumps(result, indent=2) + "\n")
    for report in reports:
        if report["changed"] or report["removed"] or report["added"]:
            print(report["path"], json.dumps({k: report[k] for k in ("changed", "removed", "added")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
