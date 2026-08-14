#!/usr/bin/env python3
"""Decode a CaDiCaL witness for extend_one_dimacs.py into a Moore certificate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from verify_solution import verify_certificate


def positive_model_literals(path: Path) -> set[int]:
    positives: set[int] = set()
    status = None
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if line.startswith("s "):
            status = line[2:].strip()
        elif line.startswith("v "):
            for token in line[2:].split():
                lit = int(token)
                if lit > 0:
                    positives.add(lit)
    if status != "SATISFIABLE":
        raise ValueError(f"witness is not SATISFIABLE: {status!r}")
    return positives


def decode(seed: dict, meta: dict, witness: Path) -> dict:
    positives = positive_model_literals(witness)
    n = int(seed["n_symbols"])
    t = int(seed["t_selected_branches"])
    if int(meta["parent_branches"]) != t or int(meta["n_symbols"]) != n:
        raise ValueError("metadata does not match seed")

    out = {k: [int(v) for v in arr] for k, arr in seed["solution"].items()}
    arrays = [[-1] * n for _ in range(t)]
    for vid, triple in enumerate(meta["id_to_edge"], start=1):
        if vid not in positives:
            continue
        i, a, b = map(int, triple)
        if arrays[i][a] != -1 or arrays[i][b] != -1:
            raise ValueError(f"witness selects multiple matching edges for i={i}")
        arrays[i][a] = b
        arrays[i][b] = a

    q = t
    for i, arr in enumerate(arrays):
        if any(v < 0 for v in arr):
            raise ValueError(f"witness did not complete matching {i}-{q}")
        out[f"{i}-{q}"] = arr

    report = {
        "n_symbols": n,
        "t_selected_branches": t + 1,
        "encoding": "direct-dimacs-pairwise",
        "solution": out,
    }
    checked = verify_certificate(report)
    report["independent_verification"] = checked
    if not checked["certificate_valid"]:
        raise ValueError(f"decoded SAT witness failed independent verification: {checked['failures'][:10]}")
    return report


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("seed_report", type=Path)
    ap.add_argument("metadata", type=Path)
    ap.add_argument("witness", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    seed = json.loads(args.seed_report.read_text(encoding="utf-8"))
    meta = json.loads(args.metadata.read_text(encoding="utf-8"))
    report = decode(seed, meta, args.witness)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(report["independent_verification"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
