#!/usr/bin/env python3
"""Compile a one-branch extension problem directly to DIMACS CNF.

This encoder has no OR-Tools dependency and introduces no auxiliary variables.  A
Boolean variable m(i,a,b), a<b, means that the new branch matching p_{i,q} contains
the symbol edge {a,b}.  All cardinality constraints are expanded to ordinary clauses.

The encoding is intended to match the corrected Boolean exact-cover CP-SAT model.
SAT models are decoded and replayed by decode_dimacs_model.py + verify_solution.py.
"""

from __future__ import annotations

import argparse
import itertools
import json
import shutil
import tempfile
from pathlib import Path

from verify_solution import verify_certificate


def old_image(sol: dict[str, list[int]], i: int, j: int, x: int) -> int:
    if i == j:
        return x
    a, b = sorted((i, j))
    return int(sol[f"{a}-{b}"][x])


def pairwise_negative(writer, ids: list[int]) -> int:
    count = 0
    for a_idx in range(len(ids)):
        a = ids[a_idx]
        for b in ids[a_idx + 1 :]:
            writer((-a, -b))
            count += 1
    return count


def compile_cnf(seed: dict, output: Path, metadata: Path) -> dict:
    checked = verify_certificate(seed)
    if not checked["certificate_valid"]:
        raise ValueError(f"invalid seed: {checked['failures'][:5]}")

    n = int(seed["n_symbols"])
    t = int(seed["t_selected_branches"])
    sol = seed["solution"]

    occupied: list[set[tuple[int, int]]] = []
    for i in range(t):
        used: set[tuple[int, int]] = set()
        for j in range(t):
            if j == i:
                continue
            for x in range(n):
                y = old_image(sol, i, j, x)
                if x < y:
                    used.add((x, y))
        occupied.append(used)

    # Deterministic variable numbering.
    var_id: dict[tuple[int, int, int], int] = {}
    id_to_edge: list[list[int]] = []
    incident: list[list[list[tuple[int, int]]]] = [[[] for _ in range(n)] for _ in range(t)]
    by_edge: dict[tuple[int, int], list[int]] = {}
    next_id = 1
    for i in range(t):
        for a in range(n):
            for b in range(a + 1, n):
                if (a, b) in occupied[i]:
                    continue
                vid = next_id
                next_id += 1
                var_id[(i, a, b)] = vid
                id_to_edge.append([i, a, b])
                incident[i][a].append((b, vid))
                incident[i][b].append((a, vid))
                by_edge.setdefault((a, b), []).append(vid)

    def edge_var(i: int, a: int, b: int) -> int | None:
        if a == b:
            return None
        aa, bb = (a, b) if a < b else (b, a)
        return var_id.get((i, aa, bb))

    output.parent.mkdir(parents=True, exist_ok=True)
    metadata.parent.mkdir(parents=True, exist_ok=True)

    clause_count = 0
    stats = {
        "at_least_one": 0,
        "matching_at_most_one": 0,
        "new_star_edge_disjoint": 0,
        "stationary_forbidden": 0,
        "route_at_most_one": 0,
        "old_pair_holonomy": 0,
    }

    with tempfile.NamedTemporaryFile("w", encoding="ascii", delete=False) as tmp:
        tmp_path = Path(tmp.name)

        def emit(lits) -> None:
            nonlocal clause_count
            vals = list(lits)
            if not vals:
                raise ValueError("attempted to emit empty clause unexpectedly")
            tmp.write(" ".join(map(str, vals)) + " 0\n")
            clause_count += 1

        # Each q_i is a perfect matching: exactly one incident selected edge per symbol.
        for i in range(t):
            for x in range(n):
                ids = [vid for _, vid in incident[i][x]]
                if not ids:
                    raise ValueError(f"no candidate edge for matching={i}, symbol={x}")
                emit(ids)
                stats["at_least_one"] += 1
                c = pairwise_negative(emit, ids)
                stats["matching_at_most_one"] += c

        # New-star edge-disjointness.
        for ids in by_edge.values():
            c = pairwise_negative(emit, ids)
            stats["new_star_edge_disjoint"] += c

        # Pair (i,q) route distinctness.  The constant stationary endpoint is x.
        for i in range(t):
            for x in range(n):
                terms: list[tuple[int, int]] = [(i, x)]
                for k in range(t):
                    if k != i:
                        terms.append((k, old_image(sol, i, k, x)))
                for y in range(n):
                    ids: list[int] = []
                    for matching_index, input_symbol in terms:
                        vid = edge_var(matching_index, input_symbol, y)
                        if vid is not None:
                            ids.append(vid)
                    if y == x:
                        for vid in ids:
                            emit((-vid,))
                            stats["stationary_forbidden"] += 1
                    else:
                        c = pairwise_negative(emit, ids)
                        stats["route_at_most_one"] += c

        # Old pair (i,j): the new two-step route via q cannot hit an existing endpoint.
        for i in range(t):
            for j in range(i + 1, t):
                for x in range(n):
                    forbidden = {x, old_image(sol, i, j, x)}
                    for k in range(t):
                        if k in (i, j):
                            continue
                        forbidden.add(old_image(sol, k, j, old_image(sol, i, k, x)))
                    for a, vi in incident[i][x]:
                        for b in forbidden:
                            vj = edge_var(j, a, b)
                            if vj is not None:
                                emit((-vi, -vj))
                                stats["old_pair_holonomy"] += 1

    with output.open("w", encoding="ascii") as out, tmp_path.open("r", encoding="ascii") as body:
        out.write(f"p cnf {next_id - 1} {clause_count}\n")
        shutil.copyfileobj(body, out, length=1024 * 1024)
    tmp_path.unlink(missing_ok=True)

    meta = {
        "n_symbols": n,
        "parent_branches": t,
        "target_branches": t + 1,
        "variables": next_id - 1,
        "clauses": clause_count,
        "clause_stats": stats,
        "id_to_edge": id_to_edge,
    }
    metadata.write_text(json.dumps(meta, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps({k: v for k, v in meta.items() if k != "id_to_edge"}, indent=2, sort_keys=True))
    return meta


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("seed_report", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--metadata", type=Path, required=True)
    args = ap.parse_args()
    seed = json.loads(args.seed_report.read_text(encoding="utf-8"))
    compile_cnf(seed, args.output, args.metadata)


if __name__ == "__main__":
    main()
