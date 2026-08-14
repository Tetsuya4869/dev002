#!/usr/bin/env python3
"""Independent verifier for restricted all-involution search certificates.

This module intentionally does not import OR-Tools.  It checks a solver-produced JSON
certificate directly, and when t == n reconstructs the complete rooted graph (including
the normalized base branch) and verifies the Moore parameters from scratch.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def edge_key(i: int, j: int) -> str:
    if i == j:
        raise ValueError("branch edge requires distinct endpoints")
    a, b = sorted((i, j))
    return f"{a}-{b}"


def load_permutations(report: dict) -> tuple[int, int, dict[tuple[int, int], list[int]]]:
    n = int(report["n_symbols"])
    t = int(report["t_selected_branches"])
    sol = report.get("solution")
    if not isinstance(sol, dict):
        raise ValueError("report contains no solution certificate")
    p: dict[tuple[int, int], list[int]] = {}
    for i in range(t):
        for j in range(i + 1, t):
            key = f"{i}-{j}"
            if key not in sol:
                raise ValueError(f"missing permutation {key}")
            arr = [int(v) for v in sol[key]]
            if len(arr) != n:
                raise ValueError(f"{key}: expected length {n}, got {len(arr)}")
            p[(i, j)] = arr
    return n, t, p


def image(p: dict[tuple[int, int], list[int]], i: int, j: int, x: int) -> int:
    return p[tuple(sorted((i, j)))][x]


def verify_certificate(report: dict) -> dict:
    n, t, p = load_permutations(report)
    failures: list[str] = []

    # Every table is a fixed-point-free involutive permutation.
    for (i, j), arr in sorted(p.items()):
        if sorted(arr) != list(range(n)):
            failures.append(f"{i}-{j}: not a permutation")
            continue
        for x, y in enumerate(arr):
            if y == x:
                failures.append(f"{i}-{j}: fixed point at {x}")
            if arr[y] != x:
                failures.append(f"{i}-{j}: not involutive at {x}")

    # At each selected branch and symbol, incident matching images are distinct.
    for i in range(t):
        for x in range(n):
            vals = [image(p, i, j, x) for j in range(t) if j != i]
            if len(vals) != len(set(vals)):
                failures.append(f"star collision: branch={i} symbol={x}")

    # Exact restricted route constraints used by the CP-SAT model.
    for i in range(t):
        for j in range(i + 1, t):
            for x in range(n):
                vals = [x, image(p, i, j, x)]
                vals.extend(
                    image(p, k, j, image(p, i, k, x))
                    for k in range(t)
                    if k not in (i, j)
                )
                if len(vals) != len(set(vals)):
                    failures.append(f"route collision: i={i} j={j} x={x}")

    # Direct holonomy checks, independent of the route formulation.
    triangle_violations = 0
    for i, j, k in itertools.permutations(range(t), 3):
        if not (i < j < k):
            continue
        # Check both orientations through all starts; reversal is involutive, but
        # verifying explicitly avoids relying on that reasoning here.
        for a, b, c in ((i, j, k), (i, k, j)):
            for x in range(n):
                y = image(p, a, b, x)
                z = image(p, b, c, y)
                w = image(p, c, a, z)
                if w == x:
                    triangle_violations += 1

    quadrilateral_violations = 0
    # Canonicalize each 4-set only to control runtime; test all six cyclic orders
    # starting at its smallest vertex.
    for quad in itertools.combinations(range(t), 4):
        a = min(quad)
        rest = [q for q in quad if q != a]
        for perm in itertools.permutations(rest):
            b, c, d = perm
            for x in range(n):
                y = image(p, a, b, x)
                z = image(p, b, c, y)
                w = image(p, c, d, z)
                q = image(p, d, a, w)
                if q == x:
                    quadrilateral_violations += 1

    if triangle_violations:
        failures.append(f"triangle holonomy fixed points: {triangle_violations}")
    if quadrilateral_violations:
        failures.append(f"quadrilateral holonomy fixed points: {quadrilateral_violations}")

    result = {
        "n_symbols": n,
        "t_selected_branches": t,
        "certificate_valid": not failures,
        "failures": failures[:100],
        "failure_count": len(failures),
        "triangle_holonomy_violations": triangle_violations,
        "quadrilateral_holonomy_violations": quadrilateral_violations,
    }

    if t == n and not failures:
        result["reconstructed_graph"] = verify_full_graph(n, p)

    return result


def verify_full_graph(n: int, p: dict[tuple[int, int], list[int]]) -> dict:
    """Reconstruct the degree-(n+1) rooted graph from a full normalized system."""

    # Vertices: root; n+1 branch vertices (last is normalized base); and
    # (n+1)*n leaves.  Leaves are represented by (branch, symbol).
    base = n
    root = ("r",)
    branches = [("b", i) for i in range(n + 1)]
    leaves = [("l", i, x) for i in range(n + 1) for x in range(n)]
    vertices = [root, *branches, *leaves]
    adj = {v: set() for v in vertices}

    def add(u, v):
        if u == v:
            raise AssertionError("loop requested")
        adj[u].add(v)
        adj[v].add(u)

    for b in branches:
        add(root, b)
    for i in range(n + 1):
        for x in range(n):
            add(("b", i), ("l", i, x))

    # Matchings among non-base branches.
    for i in range(n):
        for j in range(i + 1, n):
            for x in range(n):
                add(("l", i, x), ("l", j, image(p, i, j, x)))

    # Normalized matchings between the distinguished base branch and every
    # non-base branch are identities.
    for i in range(n):
        for x in range(n):
            add(("l", base, x), ("l", i, x))

    degrees = [len(adj[v]) for v in vertices]
    target_degree = n + 1
    regular = all(d == target_degree for d in degrees)

    triangle_count_times3 = 0
    for u in vertices:
        for v in adj[u]:
            triangle_count_times3 += len(adj[u] & adj[v])
    triangle_count = triangle_count_times3 // 6

    lambda_values: set[int] = set()
    mu_values: set[int] = set()
    diameter_at_most_two = True
    for ai, u in enumerate(vertices):
        nu = adj[u]
        for v in vertices[ai + 1 :]:
            common = len(nu & adj[v])
            if v in nu:
                lambda_values.add(common)
            else:
                mu_values.add(common)
                if common == 0:
                    diameter_at_most_two = False

    expected_vertices = (n + 1) ** 2 + 1
    expected_edges = expected_vertices * target_degree // 2
    edge_count = sum(degrees) // 2
    moore_parameters = (
        len(vertices) == expected_vertices
        and edge_count == expected_edges
        and regular
        and triangle_count == 0
        and lambda_values == {0}
        and mu_values == {1}
        and diameter_at_most_two
    )

    return {
        "vertices": len(vertices),
        "edges": edge_count,
        "degree": target_degree,
        "regular": regular,
        "triangle_count": triangle_count,
        "lambda_values": sorted(lambda_values),
        "mu_values": sorted(mu_values),
        "diameter_at_most_two": diameter_at_most_two,
        "moore_parameters_verified": moore_parameters,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("report", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    report = json.loads(args.report.read_text(encoding="utf-8"))
    result = verify_certificate(report)
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    if not result["certificate_valid"]:
        raise SystemExit(1)
    graph = result.get("reconstructed_graph")
    if graph is not None and not graph["moore_parameters_verified"]:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
