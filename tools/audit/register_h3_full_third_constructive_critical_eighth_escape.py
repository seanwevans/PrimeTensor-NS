#!/usr/bin/env python3
"""Register explicit critical-eighth source/escape theorem and audit dependencies."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
MODULE = 'FullThirdSolenoidalTerminalProfileConstructiveCriticalEighthEscape'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullConstructiveCriticalEighthProfile_pos244',
    'thirdFullConstructiveCriticalEighthProfile_atTop244',
    'thirdFullConstructiveCriticalEighthProfile_lower244',
    'thirdFullPhysical_noH3Trace_constructiveCriticalEighthSourceEscape244',
)
DEFINITION = 'thirdFullConstructiveCriticalEighthProfile244'
IMPORT = 'import ' + PREFIX + MODULE
CHECKS = tuple(line for name in (DEFINITION,) + THEOREMS for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    addition = [line for line in lines if line not in seen]
    if addition:
        block = '\n'.join(addition) + '\n'
        path.write_text(block + old if prepend else
                        old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (root, audit):
        if not path.is_file():
            parser.error(f'missing {path}')
    path = ROOT / (PREFIX.replace('.', '/') + MODULE + '.lean')
    if not path.is_file():
        parser.error(f'missing {path}')
    source = path.read_text(encoding='utf-8')
    for kind, names in (('def', (DEFINITION,)), ('theorem', THEOREMS)):
        for name in names:
            matches = re.findall(r'(?m)^' + kind + r'\s+' + re.escape(name) + r'\b', source)
            if len(matches) != 1:
                parser.error(f'missing/repeated {kind} {name}: {path}')
    stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', stripped):
        parser.error(f'proof placeholder in {path}')
    if any(line.rstrip() != line for line in source.splitlines()):
        parser.error(f'trailing whitespace in {path}')
    if args.apply:
        ensure_once(root, (IMPORT,))
        ensure_once(audit, (IMPORT,), prepend=True)
        ensure_once(audit, CHECKS)
    for path, lines in ((root, (IMPORT,)), (audit, (IMPORT,) + CHECKS)):
        body = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if body.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    print(f'PASS: 1 module, {len(THEOREMS)} theorems, 1 definition, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
