#!/usr/bin/env python3
"""Boolean exact-cover encoding for adding one branch to a verified certificate.

Unlike extend_one_cp_sat.py, this model has no permutation IntVars and no Element
constraints. Each unknown p_{i,q} is represented directly as a perfect matching of
K_n: one Boolean variable for every symbol edge not already used at the old star i.

The remaining Moore constraints involving the new branch are compiled into:
  * exact-one incidence constraints for each new perfect matching;
  * edge-disjointness of the new matchings at the new star;
  * exact route distinctness, including exclusion of the stationary endpoint;
  * binary clauses forbidding old-pair holonomy collisions through the new branch.

The returned certificate is always replayed through verify_solution.py, whose checker
has no OR-Tools dependency.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model

from verify_solution import verify_certificate


def ekey(a: int, b: int) -> tuple[int, int]:
    if a == b:
        raise ValueError("matching edges have distinct endpoints")
    return (a, b) if a < b else (b, a)


def old_image(sol: dict[str, list[int]], i: int, j: int, x: int) -> int:
    if i == j:
        return x
    a, b = sorted((i, j))
    return int(sol[f"{a}-{b}"][x])


def solve(seed: dict, seconds: float, workers: int, random_seed: int) -> dict:
    checked = verify_certificate(seed)
    if not checked["certificate_valid"]:
        raise ValueError(f"invalid seed: {checked['failures'][:5]}")

    n = int(seed["n_symbols"])
    t = int(seed["t_selected_branches"])
    sol = seed["solution"]
    q = t
    model = cp_model.CpModel()

    # Existing star matchings exclude these symbol edges from the new matching q_i.
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

    var: dict[tuple[int, int, int], cp_model.IntVar] = {}
    incident: list[list[list[tuple[int, cp_model.IntVar]]]] = [
        [[] for _ in range(n)] for _ in range(t)
    ]
    by_edge: dict[tuple[int, int], list[cp_model.IntVar]] = {}

    for i in range(t):
        for a in range(n):
            for b in range(a + 1, n):
                if (a, b) in occupied[i]:
                    continue
                v = model.NewBoolVar(f"m_{i}_{a}_{b}")
                var[(i, a, b)] = v
                incident[i][a].append((b, v))
                incident[i][b].append((a, v))
                by_edge.setdefault((a, b), []).append(v)

    # Each q_i is a perfect matching.
    for i in range(t):
        for x in range(n):
            model.AddExactlyOne([v for _, v in incident[i][x]])

    # The t new matchings are edge-disjoint at branch q.
    for vs in by_edge.values():
        if len(vs) > 1:
            model.AddAtMostOne(vs)

    def edge_var(i: int, a: int, b: int):
        aa, bb = ekey(a, b)
        return var.get((i, aa, bb))

    # Pair (i,q): the route list contains the constant stationary endpoint x,
    # the direct endpoint q_i(x), and all q_k(p_ik(x)).  For every target y,
    # at most one variable route may end at y; when y=x, zero may end there
    # because the stationary endpoint has already occupied that symbol.
    route_amo = 0
    stationary_forbidden_literals = 0
    for i in range(t):
        for x in range(n):
            terms: list[tuple[int, int]] = [(i, x)]
            for k in range(t):
                if k != i:
                    terms.append((k, old_image(sol, i, k, x)))
            for y in range(n):
                lits = []
                for matching_index, input_symbol in terms:
                    if y == input_symbol:
                        continue
                    v = edge_var(matching_index, input_symbol, y)
                    if v is not None:
                        lits.append(v)
                if y == x:
                    for v in lits:
                        model.Add(v == 0)
                        stationary_forbidden_literals += 1
                elif len(lits) > 1:
                    model.AddAtMostOne(lits)
                    route_amo += 1

    # Old pair (i,j): the new two-step route q_j(q_i(x)) must avoid every
    # endpoint already occupied by the seed routes for that old pair.
    holonomy_clauses = 0
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
                        if b == a:
                            continue
                        vj = edge_var(j, a, b)
                        if vj is not None:
                            model.AddBoolOr([vi.Not(), vj.Not()])
                            holonomy_clauses += 1

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = random_seed
    solver.parameters.log_search_progress = False

    start = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - start
    report = {
        "n_symbols": n,
        "t_selected_branches": t + 1,
        "parent_branches": t,
        "encoding": "boolean-edge-exact-cover-v2",
        "boolean_vars": len(var),
        "route_at_most_one_constraints": route_amo,
        "stationary_forbidden_literals": stationary_forbidden_literals,
        "holonomy_binary_clauses": holonomy_clauses,
        "status": solver.StatusName(status),
        "wall_seconds_python": elapsed,
        "wall_seconds_solver": solver.WallTime(),
        "conflicts": solver.NumConflicts(),
        "branches": solver.NumBranches(),
        "workers": workers,
        "seed": random_seed,
        "time_limit_seconds": seconds,
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        out = {k: [int(v) for v in arr] for k, arr in sol.items()}
        for i in range(t):
            arr = [-1] * n
            for a in range(n):
                for b, v in incident[i][a]:
                    if solver.Value(v):
                        arr[a] = b
                        break
            if any(v < 0 for v in arr):
                raise RuntimeError(f"matching {i}-{q} was not fully decoded")
            out[f"{i}-{q}"] = arr
        report["solution"] = out
        post = verify_certificate(report)
        report["independent_model_postcheck"] = post
        if not post["certificate_valid"]:
            raise RuntimeError(f"Boolean model produced invalid certificate: {post['failures'][:5]}")

    return report


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("seed_report", type=Path)
    ap.add_argument("--seconds", type=float, default=300.0)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--seed", type=int, default=101)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    seed = json.loads(args.seed_report.read_text(encoding="utf-8"))
    report = solve(seed, args.seconds, args.workers, args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
