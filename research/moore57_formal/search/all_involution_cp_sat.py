#!/usr/bin/env python3
"""CP-SAT search for restricted all-involution Moore matching systems.

A full degree-57 all-involution solution would have n=t=56. Any such solution
restricts to every t-subset of the 56 non-base branches, so a rigorously verified
UNSAT result for any (t,n=56) would rule out the full normalized all-involution
subcase.

Variables p_{ij}(x) encode the fixed-point-free involution attached to branch
edge {i,j}. The model imposes:
  * each p_{ij} is a fixed-point-free involution;
  * at each branch i and symbol x, the values p_{ij}(x) are distinct;
  * for each branch pair i<j and symbol x, the stationary route x, direct
    route p_{ij}(x), and all two-step routes p_{kj}(p_{ik}(x)) through the
    other selected branches are all distinct.

The optional --fix-report argument freezes all branch-edge permutations from an
existing smaller certificate. This is useful for adversarial extension tests: it
asks whether one concrete t0-branch solution embeds into a larger t-branch one.
Such a failed extension does NOT by itself prove the full subcase impossible.
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

    for i in range(t):
        for j in range(i + 1, t):
            arr = [model.NewIntVar(0, n - 1, f"p_{i}_{j}_{x}") for x in range(n)]
            p[(i, j)] = arr
            model.AddAllDifferent(arr)
            for x in range(n):
                model.Add(arr[x] != x)
                model.AddElement(arr[x], arr, x)

    # WLOG under one global relabeling of symbols.
    if fix_first_matching and t >= 2:
        arr = p[(0, 1)]
        for x in range(n):
            model.Add(arr[x] == (x ^ 1))

    def image(i: int, j: int, x: int):
        return p[key(i, j)][x]

    for i in range(t):
        for x in range(n):
            model.AddAllDifferent([image(i, j, x) for j in range(t) if j != i])

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


def apply_fixed_report(model, p, n: int, t: int, report_path: Path | None) -> dict:
    if report_path is None:
        return {"fixed_report": None, "fixed_branches": 0, "fixed_values": 0}

    data = json.loads(report_path.read_text(encoding="utf-8"))
    if int(data["n_symbols"]) != n:
        raise ValueError("fixed report symbol count does not match --n")
    t0 = int(data["t_selected_branches"])
    if t0 > t:
        raise ValueError("fixed report uses more branches than target --t")
    sol = data.get("solution")
    if not isinstance(sol, dict):
        raise ValueError("fixed report has no solution")

    fixed_values = 0
    for i in range(t0):
        for j in range(i + 1, t0):
            name = f"{i}-{j}"
            arr = sol.get(name)
            if not isinstance(arr, list) or len(arr) != n:
                raise ValueError(f"fixed report has invalid {name}")
            for x, value in enumerate(arr):
                value = int(value)
                if not 0 <= value < n:
                    raise ValueError(f"fixed report {name}[{x}] out of range")
                model.Add(p[(i, j)][x] == value)
                fixed_values += 1

    return {
        "fixed_report": str(report_path),
        "fixed_branches": t0,
        "fixed_values": fixed_values,
    }


def solve(
    n: int,
    t: int,
    seconds: float,
    workers: int,
    seed: int,
    output: Path,
    fix_report: Path | None,
):
    model, p, stats = build_model(n, t)
    stats.update(apply_fixed_report(model, p, n, t, fix_report))

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
        report["solution"] = {
            f"{i}-{j}": [solver.Value(v) for v in arr]
            for (i, j), arr in sorted(p.items())
        }

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))

    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE, cp_model.INFEASIBLE, cp_model.UNKNOWN):
        raise SystemExit(2)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--t", type=int, required=True)
    ap.add_argument("--seconds", type=float, default=120.0)
    ap.add_argument("--workers", type=int, default=max(1, min(8, os.cpu_count() or 1)))
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--fix-report", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    solve(args.n, args.t, args.seconds, args.workers, args.seed, args.output, args.fix_report)
