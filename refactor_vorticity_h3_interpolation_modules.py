from pathlib import Path

script = r'''#!/usr/bin/env python3
"""
Refactor the flat PrimeTensor H^3 order-three interpolation module family into
a hierarchical Lean module tree.

Dry-run is the default.  Pass --apply to perform the moves and import rewrites.

Examples
--------
  python scripts/refactor_vorticity_h3_interpolation_modules.py
  python scripts/refactor_vorticity_h3_interpolation_modules.py --apply

The production mapping is:

  PrimeTensor/Fluid/
    VorticityH3EnergyTransportOrderThreeInterpolationLandauHolderClosure.lean

becomes:

  PrimeTensor/Fluid/Vorticity/H3/Energy/Transport/Order/Three/
    Interpolation/Landau/Holder/Closure.lean

and the corresponding Lean import changes from:

  PrimeTensor.Fluid.VorticityH3EnergyTransportOrderThreeInterpolationLandauHolderClosure

to:

  PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation.Landau.Holder.Closure

Files ending in "Probe.lean" under this exact family are diagnostic scratch
files.  They are moved outside the PrimeTensor library tree to
scratch/lean-probes/ rather than promoted into the production hierarchy.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


OLD_PREFIX = "VorticityH3EnergyTransportOrderThreeInterpolation"
OLD_MODULE_PREFIX = "PrimeTensor.Fluid." + OLD_PREFIX

# Put Interpolation at the end of the module stem so both
#   .../Interpolation.lean
# and
#   .../Interpolation/Landau/...
# are valid simultaneously.
NEW_BASE_PATH = Path(
    "PrimeTensor/Fluid/Vorticity/H3/Energy/Transport/Order/Three"
)
NEW_MODULE_PREFIX = (
    "PrimeTensor.Fluid.Vorticity.H3.Energy.Transport.Order.Three.Interpolation"
)

SOURCE_DIR = Path("PrimeTensor/Fluid")
PROBE_ARCHIVE = Path("scratch/lean-probes")

TOKEN_RE = re.compile(
    r"[A-Z]+[0-9]+|[A-Z]?[a-z]+|[A-Z]+(?=[A-Z]|$)|[0-9]+"
)


@dataclass(frozen=True)
class Move:
    src: Path
    dst: Path
    old_module: str | None
    new_module: str | None
    probe: bool = False


def run_git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=check,
    )


def repo_root() -> Path:
    p = run_git("rev-parse", "--show-toplevel")
    return Path(p.stdout.strip()).resolve()


def split_suffix(suffix: str) -> list[str]:
    if not suffix:
        return []
    tokens = TOKEN_RE.findall(suffix)
    if "".join(tokens) != suffix:
        raise ValueError(
            f"Cannot split module suffix safely: {suffix!r}; parsed {tokens!r}"
        )
    return tokens


def is_tracked(path: Path) -> bool:
    p = run_git("ls-files", "--error-unmatch", str(path), check=False)
    return p.returncode == 0


def production_destination(stem: str) -> tuple[Path, str]:
    suffix = stem[len(OLD_PREFIX):]
    tokens = split_suffix(suffix)

    if tokens:
        dst = NEW_BASE_PATH / "Interpolation" / Path(*tokens[:-1]) / f"{tokens[-1]}.lean"
        new_module = NEW_MODULE_PREFIX + "." + ".".join(tokens)
    else:
        dst = NEW_BASE_PATH / "Interpolation.lean"
        new_module = NEW_MODULE_PREFIX

    return dst, new_module


def collect_moves(root: Path) -> list[Move]:
    source_dir = root / SOURCE_DIR
    if not source_dir.is_dir():
        raise RuntimeError(f"Expected source directory not found: {source_dir}")

    files = sorted(source_dir.glob(f"{OLD_PREFIX}*.lean"))
    if not files:
        raise RuntimeError(
            f"No files matching {SOURCE_DIR}/{OLD_PREFIX}*.lean"
        )

    moves: list[Move] = []

    for abs_src in files:
        src = abs_src.relative_to(root)
        stem = abs_src.stem

        if stem.endswith("Probe"):
            dst = PROBE_ARCHIVE / abs_src.name
            moves.append(Move(src, dst, None, None, probe=True))
            continue

        dst, new_module = production_destination(stem)
        old_module = "PrimeTensor.Fluid." + stem
        moves.append(Move(src, dst, old_module, new_module))

    return moves


def preflight(root: Path, moves: list[Move]) -> None:
    destinations: dict[Path, Path] = {}

    for move in moves:
        if move.dst in destinations:
            raise RuntimeError(
                f"Destination collision:\n"
                f"  {destinations[move.dst]}\n"
                f"  {move.src}\n"
                f"both map to {move.dst}"
            )
        destinations[move.dst] = move.src

        abs_dst = root / move.dst
        if abs_dst.exists() and move.src != move.dst:
            raise RuntimeError(
                f"Destination already exists: {move.dst}\n"
                f"Refusing to overwrite anything."
            )

    # Check module-name collisions too.
    modules: dict[str, str] = {}
    for move in moves:
        if move.new_module is None:
            continue
        if move.new_module in modules:
            raise RuntimeError(
                f"Module collision: {move.new_module}\n"
                f"  {modules[move.new_module]}\n"
                f"  {move.src}"
            )
        modules[move.new_module] = str(move.src)


def print_plan(root: Path, moves: list[Move]) -> None:
    prod = [m for m in moves if not m.probe]
    probes = [m for m in moves if m.probe]

    print(f"repo: {root}")
    print()
    print(f"production modules to move: {len(prod)}")
    for m in prod:
        print(f"  MOVE   {m.src}")
        print(f"      -> {m.dst}")
        print(f"  IMPORT {m.old_module}")
        print(f"      -> {m.new_module}")

    print()
    print(f"diagnostic probes to archive: {len(probes)}")
    for m in probes:
        print(f"  PROBE  {m.src}")
        print(f"      -> {m.dst}")

    print()
    print("No files have been changed.")


def move_one(root: Path, move: Move) -> None:
    src = root / move.src
    dst = root / move.dst
    dst.parent.mkdir(parents=True, exist_ok=True)

    if is_tracked(move.src):
        p = run_git("mv", str(move.src), str(move.dst), check=False)
        if p.returncode != 0:
            raise RuntimeError(
                f"git mv failed:\n  {move.src}\n  -> {move.dst}\n{p.stderr}"
            )
    else:
        shutil.move(str(src), str(dst))


def rewrite_imports(root: Path, mapping: dict[str, str]) -> list[Path]:
    changed: list[Path] = []

    # Longest first prevents one old module name from being a prefix of another.
    replacements = sorted(
        mapping.items(),
        key=lambda kv: len(kv[0]),
        reverse=True,
    )

    for path in sorted(root.rglob("*.lean")):
        # Skip build/cache/vendor trees.
        rel = path.relative_to(root)
        if any(part in {".lake", ".git"} for part in rel.parts):
            continue

        text = path.read_text(encoding="utf-8")
        new_text = text

        for old, new in replacements:
            # Module names consist of identifier segments separated by dots.
            # The boundaries stop accidental replacement inside a longer name.
            pattern = re.compile(
                rf"(?<![A-Za-z0-9_'.]){re.escape(old)}(?![A-Za-z0-9_'])"
            )
            new_text = pattern.sub(new, new_text)

        if new_text != text:
            path.write_text(new_text, encoding="utf-8")
            changed.append(rel)

    return changed


def verify_no_old_imports(root: Path, mapping: dict[str, str]) -> list[tuple[Path, str]]:
    leftovers: list[tuple[Path, str]] = []

    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root)
        if any(part in {".lake", ".git"} for part in rel.parts):
            continue
        text = path.read_text(encoding="utf-8")
        for old in mapping:
            if old in text:
                leftovers.append((rel, old))

    return leftovers


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--apply",
        action="store_true",
        help="perform the moves and import rewrites (default is dry-run)",
    )
    args = parser.parse_args()

    root = repo_root()
    moves = collect_moves(root)
    preflight(root, moves)

    if not args.apply:
        print_plan(root, moves)
        return 0

    mapping = {
        m.old_module: m.new_module
        for m in moves
        if m.old_module is not None and m.new_module is not None
    }

    print(f"Applying refactor in {root}")
    print(f"Moving {sum(not m.probe for m in moves)} production modules...")
    for move in moves:
        if not move.probe:
            move_one(root, move)

    probes = [m for m in moves if m.probe]
    if probes:
        print(f"Archiving {len(probes)} diagnostic probe files...")
        for move in probes:
            move_one(root, move)

    changed = rewrite_imports(root, mapping)

    leftovers = verify_no_old_imports(root, mapping)
    if leftovers:
        print()
        print("ERROR: old module references remain:")
        for path, old in leftovers:
            print(f"  {path}: {old}")
        print()
        print("The moves are left in the working tree for inspection.")
        return 2

    print()
    print("Refactor applied.")
    print(f"Import-bearing files rewritten: {len(changed)}")
    for path in changed:
        print(f"  {path}")

    print()
    print("Recommended verification:")
    print("  git diff --stat")
    print("  git diff --check")
    print("  lake build")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
'''

path = Path("/mnt/data/refactor_vorticity_h3_interpolation_modules.py")
path.write_text(script)
print(f"Created {path}")
