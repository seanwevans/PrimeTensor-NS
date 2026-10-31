#!/usr/bin/env python3
"""Idempotently protect the baseline source fingerprint from Python bytecode.

Use --apply once, then --check as a reproducible regression guard.
This intentionally does not edit Lean sources or the proof index.
"""
from __future__ import annotations

import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
GITIGNORE = ROOT / '.gitignore'
BASELINE = ROOT / 'tools/audit/baseline.sh'

IGNORE_BLOCK = (
    '# Generated Python bytecode is not a source input.\n'
    '__pycache__/\n'
    '*.py[cod]\n'
)
ENV_BLOCK = (
    '# Keep audit-helper imports from mutating the source inventory mid-baseline.\n'
    'export PYTHONDONTWRITEBYTECODE=1\n'
)


def expected_files() -> tuple[tuple[Path, str, str], ...]:
    return (
        (GITIGNORE, IGNORE_BLOCK, ''),
        (BASELINE, ENV_BLOCK, 'set -euo pipefail\n'),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()

    for path, addition, anchor in expected_files():
        if not path.is_file():
            parser.error(f'missing expected file: {path}')
        content = path.read_text()
        if path == GITIGNORE:
            required = ('__pycache__/', '*.py[cod]')
            present = [line for line in content.splitlines() if line in required]
            if 0 < len(present) < 2:
                parser.error(f'partial Python ignore policy in {path}; inspect manually')
            complete = all(content.splitlines().count(line) == 1 for line in required)
            if args.apply and not complete:
                path.write_text(content.rstrip('\n') + '\n\n' + addition)
                complete = True
        else:
            complete = (content.count('export PYTHONDONTWRITEBYTECODE=1') == 1 and
                        content.index('export PYTHONDONTWRITEBYTECODE=1') <
                        content.index('python3 tools/audit/inspect_source.py "$report"')) if (
                            'export PYTHONDONTWRITEBYTECODE=1' in content and
                            'python3 tools/audit/inspect_source.py "$report"' in content
                        ) else False
            if args.apply and not complete:
                if 'PYTHONDONTWRITEBYTECODE' in content:
                    parser.error(f'existing bytecode setting in {path}; inspect manually')
                if content.count(anchor) != 1:
                    parser.error(f'unexpected baseline header: {path}')
                path.write_text(content.replace(anchor, anchor + ENV_BLOCK, 1))
                complete = True
        if not complete:
            parser.error(f'missing CI fingerprint hygiene in {path}; run --apply')
        print(f'PASS: {path.relative_to(ROOT)}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
