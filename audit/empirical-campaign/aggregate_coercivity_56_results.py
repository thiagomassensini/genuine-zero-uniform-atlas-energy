#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import glob
import json
from pathlib import Path
from typing import Any


def load_rows(folder: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path_text in sorted(glob.glob(str(folder / "M*_c*.json"))):
        path = Path(path_text)
        with path.open(encoding="utf-8") as handle:
            report = json.load(handle)
        row = report["cutoff_rows"][0]
        cert = row.get("coercivity_certificate") or {}
        witness = row.get("microscopic_upper_witness") or {}
        rows.append(
            {
                "file": path.name,
                "cutoff": int(row["cutoff"]),
                "ambient_dimension": int(row["ambient_dimension"]),
                "coefficient": float(cert.get("coefficient", float("nan"))),
                "status": cert.get("status", "MISSING"),
                "certified": bool(cert.get("certified", False)),
                "cells_created": cert.get("cells_created"),
                "maximum_depth": cert.get("maximum_depth"),
                "elapsed_seconds": cert.get("elapsed_seconds"),
                "smallest_certified_cell_lower_bound": cert.get(
                    "smallest_certified_cell_lower_bound"
                ),
                "upper_witness_quotient": witness.get("longdouble_quotient"),
                "upper_witness_sigma": witness.get("sigma"),
                "upper_witness_time": witness.get("time"),
                "counterexample_quotient": (
                    (cert.get("counterexample") or {}).get("quotient")
                ),
            }
        )
    return sorted(rows, key=lambda item: (item["cutoff"], item["coefficient"]))


def threshold_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for cutoff in sorted({row["cutoff"] for row in rows}):
        group = [row for row in rows if row["cutoff"] == cutoff]
        passed = [row["coefficient"] for row in group if row["certified"]]
        counter = [
            row["coefficient"]
            for row in group
            if row["status"] == "COUNTEREXAMPLE_FOUND"
        ]
        unresolved = [
            row["coefficient"]
            for row in group
            if row["status"] == "RESOURCE_LIMIT_UNRESOLVED"
        ]
        witnesses = [
            row["upper_witness_quotient"]
            for row in group
            if row["upper_witness_quotient"] is not None
        ]
        output.append(
            {
                "cutoff": cutoff,
                "ambient_dimension": group[0]["ambient_dimension"],
                "highest_certified_coefficient": max(passed) if passed else None,
                "lowest_counterexample_coefficient": min(counter) if counter else None,
                "microscopic_upper_witness": min(witnesses) if witnesses else None,
                "unresolved_coefficients": ",".join(map(str, unresolved)),
            }
        )
    return output


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("folder", type=Path)
    args = parser.parse_args()
    rows = load_rows(args.folder)
    if not rows:
        raise SystemExit(f"no M*_c*.json files found in {args.folder}")
    thresholds = threshold_rows(rows)
    write_csv(args.folder / "all_attempts.csv", rows)
    write_csv(args.folder / "threshold_summary.csv", thresholds)
    (args.folder / "threshold_summary.json").write_text(
        json.dumps(thresholds, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print(
        "cutoff  ambient    highest_pass  first_counterexample  upper_witness  unresolved"
    )
    for row in thresholds:
        print(
            f"{row['cutoff']:6d}  {row['ambient_dimension']:8d}  "
            f"{str(row['highest_certified_coefficient']):>12}  "
            f"{str(row['lowest_counterexample_coefficient']):>20}  "
            f"{str(row['microscopic_upper_witness']):>13}  "
            f"{row['unresolved_coefficients']}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
