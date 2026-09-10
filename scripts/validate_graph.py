#!/usr/bin/env python3
import csv
from collections import defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
rows = list(csv.DictReader((ROOT / "NODE_SPEC.csv").open(encoding="utf-8")))
deps = {r["node"]: [x for x in r["dependencies"].split(";") if x] for r in rows}
children = defaultdict(list)
indeg = {k: len(v) for k,v in deps.items()}
for k, ds in deps.items():
    for d in ds: children[d].append(k)
q = deque(k for k,v in indeg.items() if v == 0)
order = []
while q:
    k = q.popleft(); order.append(k)
    for c in children[k]:
        indeg[c] -= 1
        if indeg[c] == 0: q.append(c)
if len(order) != len(rows):
    raise SystemExit("GRAPH CHECK FAILED: dependency cycle detected")

# Every node must be an ancestor of the final main node.
reachable = set()
stack = ["mod:main"]
while stack:
    k = stack.pop()
    if k in reachable: continue
    reachable.add(k); stack.extend(deps[k])
missing = sorted(set(deps) - reachable)
if missing:
    raise SystemExit("GRAPH CHECK FAILED: nodes unreachable from mod:main: " + ", ".join(missing))
print(f"GRAPH CHECK PASSED: {len(rows)} nodes, {sum(len(v) for v in deps.values())} edges, no cycles, all nodes feed mod:main")
