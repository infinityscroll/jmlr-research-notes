from pathlib import Path
import json, hashlib
BASE=Path(__file__).resolve().parent
j=json.loads((BASE/"SOURCE_MAP.json").read_text())
rows=j["internal_sources"]; by={r["id"]:r for r in rows}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for r in rows:
    p=BASE/r["review_copy"]
    assert sha(p)==r["sha256"], f"Copy hash mismatch: {p}"
    original=Path(r["original_path"])
    if original.exists(): assert sha(original)==r["sha256"], f"Original changed: {original}"
    assert all(d in by for d in r["dependencies"]), f"Unresolved dependency: {r['id']}"
seen=set(); stack=set()
def visit(k):
    assert k not in stack, f"Cycle at {k}"
    if k in seen: return
    stack.add(k)
    for d in by[k]["dependencies"]: visit(d)
    stack.remove(k); seen.add(k)
for k in by: visit(k)
assert not list(BASE.rglob("*.html")), "External HTML copy found"
assert not list(BASE.rglob("*.pdf")), "External PDF copy found"
print(json.dumps({"verified_internal_sources":len(rows),"missing_from_manuscript_snapshot":sum(not r["already_in_manuscript"] for r in rows),"acyclic_section_dependency_map":True,"full_external_articles_copied":0},indent=2))
