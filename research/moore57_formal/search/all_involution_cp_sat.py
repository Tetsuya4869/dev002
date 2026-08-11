#!/usr/bin/env python3
"""CP-SAT search for restricted all-involution Moore matching systems.

A full degree-57 all-involution solution would have n=t=56.  Any such solution
restricts to every t-subset of the 56 non-base branches, so UNSAT for any
(t,n=56) already rules out the full all-involution case.

Variables p_{ij}(x) encode the fixed-point-free involution attached to branch
edge {i,j}.  The model imposes:
  * each p_{ij} is a fixed-point-free involution;
  * at each branch i and symbol x, the values p_{ij}(x) are distinct;
  * for each branch pair i<j and symbol x, the stationary route x, direct
    route p_{ij}(x), and all two-step routes p_{kj}(p_{ik}(x)) through the
    other selected branches are all distinct.

The last global-cardinality constraint packages all triangle and 4-cycle
holonomy restrictions among the selected branches.  For t=n it is exactly the
route-exhaustion bijection formalized in Moore57.RouteExhaustion.
"""

from __future__ import annotations

import argparse
import json
import os
import time
from pathlib import Path

from ortools.sat.python import cp_model


def key(i: int, j: int) -> tuple[int, int]:
    if i == j:
        raise ValueError("branch edge requires distinct endpoints")
    return (i, j) if i < j else (j, i)


def build_model(n: int, t: int, fix_first_matching: bool = True):
    if n % 2:
        raise ValueError("n must be even for a fixed-point-free involution")
    if not 2 <= t <= n:
        raise ValueError("require 2 <= t <= n")

    model = cp_model.CpModel()
    p: dict[tuple[int, int], list[cp_model.IntVar]] = {}

    # One fixed-point-free involution per selected branch edge.
    for i in range(t):
        for j in range(i + 1, t):
            arr = [model.NewIntVar(0, n - 1, f"p_{i}_{j}_{x}") for x in range(n)]
            p[(i, j)] = arr
            model.AddAllDifferent(arr)
            for x in range(n):
                model.Add(arr[x] != x)
                # p[p[x]] = x. This also implies bijectivity, but AllDifferent
                # is retained because it propagates strongly in CP-SAT.
                model.AddElement(arr[x], arr, x)

    # WLOG under a global relabeling of the n symbols, fix one involution to
    # the canonical matching (0 1)(2 3)...(n-2 n-1).
    if fix_first_matching and t >= 2:
        arr = p[(0, 1)]
        for x in range(n):
            model.Add(arr[x] == (x ^ 1))

    def image(i: int, j: int, x: int):
        return p[key(i, j)][x]

    # Short cycles through the normalized base branch: for fixed i,x the
    # incident matching images are pairwise distinct.
    for i in range(t):
        for x in range(n):
            model.AddAllDifferent([image(i, j, x) for j in range(t) if j != i])

    # Residual holonomy: all selected routes i -> j at a fixed x have distinct
    # endpoints. This simultaneously excludes the relevant triangles and C4s.
    route_aux = 0
    for i in range(t):
        for j in range(i + 1, t):
            for x in range(n):
                route_values = [x, image(i, j, x)]
                for k in range(t):
                    if k == i or k == j:
                        continue
                    z = model.NewIntVar(0, n - 1, f"route_{i}_{j}_{k}_{x}")
                    model.AddElement(image(i, k, x), p[key(k, j)], z)
                    route_values.append(z)
                    route_aux += 1
                model.AddAllDifferent(route_values)

    stats = {
        "n_symbols": n,
        "t_selected_branches": t,
        "branch_edges": t * (t - 1) // 2,
        "permutation_int_vars": (t * (t - 1) // 2) * n,
        "route_aux_vars": route_aux,
        "fixed_first_matching": fix_first_matching,
    }
    return model, p, stats


def solve(n: int, t: int, seconds: float, workers: int, seed: int, output: Path):
    model, p, stats = build_model(n, t)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = seed
    solver.parameters.log_search_progress = False

    start = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - start
    status_name = solver.StatusName(status)

    report = {
        **stats,
        "status": status_name,
        "wall_seconds_python": elapsed,
        "wall_seconds_solver": solver.WallTime(),
        "conflicts": solver.NumConflicts(),
        "branches": solver.NumBranches(),
        "seed": seed,
        "workers": workers,
        "time_limit_seconds": seconds,
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        # Store compact cycle-free involution tables. This is enough to replay
        # and independently verify the returned restricted system.
        report["solution"] = {
            f"{i}-{j}": [solver.Value(v) for v in arr]
            for (i, j), arr in sorted(p.items())
        }

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))

    # UNKNOWN is not a mathematical failure; preserve the report and return 0.
    # MODEL_INVALID/other unexpected statuses should fail CI.
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE, cp_model.INFEASIBLE, cp_model.UNKNOWN):
        raise SystemExit(2)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--t", type=int, required=True)
    ap.add_argument("--seconds", type=float, default=120.0)
    ap.add_argument("--workers", type=int, default=max(1, min(8, os.cpu_count() or 1)))
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    solve(args.n, args.t, args.seconds, args.workers, args.seed, args.output)
