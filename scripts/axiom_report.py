#!/usr/bin/env python3
"""Generate an inventory of Lean axioms in the project tree."""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, List, Sequence


AXIOM_PATTERN = re.compile(r"^\s*axiom\s+([A-Za-z0-9_`.]+)")


def iter_lean_files(root: Path, include_old: bool, extra_roots: Sequence[Path]) -> Iterable[Path]:
    candidates: List[Path] = []

    def include_dir(path: Path) -> bool:
        parts = path.parts
        if any(part.startswith(".") for part in parts):
            return False
        if "lake-packages" in parts:
            return False
        if not include_old and "old-rh" in parts:
            return False
        return True

    search_roots: List[Path] = []
    if extra_roots:
        search_roots.extend(extra_roots)
    else:
        search_roots.append(root)

    for search_root in search_roots:
        for path in sorted(search_root.rglob("*.lean")):
            if include_dir(path.parent):
                candidates.append(path)

    return candidates


def find_axioms(path: Path) -> List[Dict[str, object]]:
    axioms: List[Dict[str, object]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except UnicodeDecodeError:
        return axioms

    for idx, line in enumerate(lines, start=1):
        match = AXIOM_PATTERN.match(line)
        if match:
            axioms.append({
                "name": match.group(1),
                "line_no": idx,
                "signature": line.strip(),
            })
    return axioms


def build_report(root: Path, files: Iterable[Path]) -> Dict[str, object]:
    report_files: List[Dict[str, object]] = []
    by_name: Dict[str, List[str]] = defaultdict(list)

    total_axioms = 0
    for file_path in files:
        axioms = find_axioms(file_path)
        if not axioms:
            continue

        total_axioms += len(axioms)
        rel_path = str(file_path.relative_to(root))
        report_files.append({
            "path": rel_path,
            "axioms": axioms,
            "count": len(axioms),
        })

        for ax in axioms:
            by_name[ax["name"]].append(rel_path)

    duplicates = {
        name: locations
        for name, locations in sorted(by_name.items())
        if len(locations) > 1
    }

    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": str(root),
        "total_axioms": total_axioms,
        "file_count": len(report_files),
        "files": report_files,
        "duplicate_names": duplicates,
    }

    return report


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Project root (defaults to repository root)",
    )
    parser.add_argument(
        "--include-old",
        action="store_true",
        help="Include the archived `old-rh` directory in the scan",
    )
    parser.add_argument(
        "--extra",
        type=Path,
        nargs="*",
        default=None,
        help="Additional search roots (defaults to scanning the entire project)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Optional path to write the JSON report",
    )
    parser.add_argument(
        "--summary",
        action="store_true",
        help="Print a human-readable summary in addition to JSON",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str]) -> int:
    args = parse_args(argv)
    root = args.root.resolve()

    if args.extra:
        extra_roots = [path.resolve() for path in args.extra]
    else:
        extra_roots = [root]

    lean_files = iter_lean_files(root, args.include_old, extra_roots)
    report = build_report(root, lean_files)

    json_output = json.dumps(report, indent=2, sort_keys=True)

    if args.output:
        args.output.write_text(json_output + "\n", encoding="utf-8")

    print(json_output)

    if args.summary:
        print()
        print(f"Total axiom declarations: {report['total_axioms']}")
        print(f"Files containing axioms: {report['file_count']}")
        if report["duplicate_names"]:
            print("Duplicate axiom names detected:")
            for name, locations in report["duplicate_names"].items():
                joined = ", ".join(locations)
                print(f"  {name}: {joined}")
        else:
            print("No duplicate axiom names detected.")

    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))


