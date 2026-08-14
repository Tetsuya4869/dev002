#!/usr/bin/env python3
"""Specialized one-branch extension solver for verified Moore certificates.

Given a valid restricted all-involution certificate on t branches, this model adds
only one new branch q=t.  The old permutations are constants; the only CP-SAT
permutation variables are q_i = p_{i,q}, i<t.  This is logically equivalent to the
full restricted model with the old certificate fixed, but substantially smaller.

Every returned certificate should still be checked by verify_solution.py, which does
not import OR-Tools.
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

from ortools.sat.python import cp_model

from verify_solution import verify_certificate


def old_image(sol: dict[str, list[int]], i: int, j: int, x: int) -> int:
    if i == j:
        return x
    a, b = sorted((i, j))
    return int(sol[f"{a}-{b}"][x])


def extend_one(seed: dict, seconds: float, workers: int, random_seed: int) -> dict:
    checked = verify_certificate(seed)
    if not checked["certificate_valid"]:
        raise ValueError(f"invalid seed certificate: {checked['failures'][:5]}")

    n = int(seed["n_symbols"])
    t = int(seed["t_selected_branches"])
    sol = seed["solution"]
    q = t

    model = cp_model.CpModel()
    newp: list[list[cp_model.IntVar]] = []

    # q_i is the fixed-point-free involution p_{i,q}.
    for i in range(t):
        arr = [model.NewIntVar(0, n - 1, f"q_{i}_{x}") for x in range(n)]
        newp.append(arr)
        model.AddAllDifferent(arr)
        for x in range(n):
            model.Add(arr[x] != x)
            model.AddElement(arr[x], arr, x)

    # Star constraint at every old branch: the new matching image cannot reuse
    # any image already occupied by an old incident matching.
    for i in range(t):
        for x in range(n):
            occupied = {old_image(sol, i, j, x) for j in range(t) if j != i}
            for y in occupied:
                model.Add(newp[i][x] != y)

    # Star constraint at the new branch.
    for x in range(n):
        model.AddAllDifferent([newp[i][x] for i in range(t)])

    route_aux = 0

    # For each old pair i,j, the new two-step route through q must avoid all
    # existing route endpoints.  Existing endpoints are constants because the
    # seed has already been independently verified.
    for i in range(t):
        for j in range(i + 1, t):
            for x in range(n):
                occupied = {x, old_image(sol, i, j, x)}
                for k in range(t):
                    if k in (i, j):
                        continue
                    occupied.add(old_image(sol, k, j, old_image(sol, i, k, x)))
                z = model.NewIntVar(0, n - 1, f"oldpair_{i}_{j}_via_q_{x}")
                model.AddElement(newp[i][x], newp[j], z)
                route_aux += 1
                for y in occupied:
                    model.Add(z != y)

    # For each pair i,q, all routes through the old branches must be distinct
    # from the stationary endpoint x and the direct endpoint q_i(x), and from
    # one another.
    for i in range(t):
        for x in range(n):
            vals: list[cp_model.LinearExpr] = [x, newp[i][x]]
            for k in range(t):
                if k == i:
                    continue
                # p_{k,q}(p_{i,k}(x)); the inner image is a seed constant.
                vals.append(newp[k][old_image(sol, i, k, x)])
            model.AddAllDifferent(vals)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = workers
    solver.parameters.random_seed = random_seed
    solver.parameters.log_search_progress = False

    start = time.time()
    status = solver.Solve(model)
    elapsed = time.time() - start
    status_name = solver.StatusName(status)

    report = {
        "n_symbols": n,
        "t_selected_branches": t + 1,
        "parent_branches": t,
        "status": status_name,
        "wall_seconds_python": elapsed,
        "wall_seconds_solver": solver.WallTime(),
        "conflicts": solver.NumConflicts(),
        "branches": solver.NumBranches(),
        "new_permutation_int_vars": t * n,
        "route_aux_vars": route_aux,
        "workers": workers,
        "seed": random_seed,
        "time_limit_seconds": seconds,
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        out_sol = {k: [int(v) for v in arr] for k, arr in sol.items()}
        for i in range(t):
            out_sol[f"{i}-{q}"] = [solver.Value(v) for v in newp[i]]
        report["solution"] = out_sol

        # Internal belt-and-suspenders check.  CI performs the same verification
        # again in a fresh process that does not import OR-Tools.
        post = verify_certificate(report)
        report["internal_postcheck_valid"] = post["certificate_valid"]
        if not post["certificate_valid"]:
            raise RuntimeError(f"solver result failed independent model check: {post['failures'][:5]}")

    return report


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("seed_report", type=Path)
    ap.add_argument("--seconds", type=float, default=120.0)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--seed", type=int, default=31)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()

    seed = json.loads(args.seed_report.read_text(encoding="utf-8"))
    report = extend_one(seed, args.seconds, args.workers, args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
