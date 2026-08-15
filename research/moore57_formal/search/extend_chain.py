#!/usr/bin/env python3
"""Iteratively extend a verified restricted Moore certificate one branch at a time."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from extend_one_cp_sat import extend_one


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("seed_report", type=Path)
    ap.add_argument("--max-t", type=int, required=True)
    ap.add_argument("--seconds-per-step", type=float, default=180.0)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--seed", type=int, default=41)
    ap.add_argument("--output-dir", type=Path, required=True)
    args = ap.parse_args()

    current = json.loads(args.seed_report.read_text(encoding="utf-8"))
    t = int(current["t_selected_branches"])
    args.output_dir.mkdir(parents=True, exist_ok=True)

    summary = []
    while t < args.max_t:
        target = t + 1
        report = extend_one(
            current,
            seconds=args.seconds_per_step,
            workers=args.workers,
            random_seed=args.seed + target,
        )
        out = args.output_dir / f"moore56-t{target}.json"
        out.write_text(json.dumps(report, indent=2, sort_keys=True), encoding="utf-8")
        summary.append({
            "target": target,
            "status": report["status"],
            "wall_seconds_solver": report["wall_seconds_solver"],
            "conflicts": report["conflicts"],
            "branches": report["branches"],
        })
        print(json.dumps(summary[-1], sort_keys=True), flush=True)
        if "solution" not in report:
            break
        current = report
        t = target

    (args.output_dir / "chain-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8"
    )
    print(json.dumps({"chain": summary}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
