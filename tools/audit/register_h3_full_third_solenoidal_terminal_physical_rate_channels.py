#!/usr/bin/env python3
"""Register H3 terminal actual physical quintic/eighth-rate alternatives."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
ITEMS = (
    ('FullThirdSolenoidalTerminalProfilePhysicalRatePolynomial', (
        'thirdFull_quadraticPDESum_forces_quinticOrEighth244',
        'thirdFull_quadraticPDESum_forces_sourceOrSpectralGains244',
    )),
    ('FullThirdSolenoidalTerminalProfilePhysicalRateBarrier', (
        'thirdFullPhysical_noH3Trace_profileClock_or_physicalQuinticEighth244',
    )),
)
IMPORTS = tuple('import ' + PREFIX + module for module, _ in ITEMS)
NAMES = tuple(name for _, names in ITEMS for name in names)
CHECKS = tuple(line for name in NAMES for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_lines(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    new = [line for line in lines if line not in seen]
    if new:
        addition = '\n'.join(new) + '\n'
        path.write_text(addition + old if prepend else
                        old.rstrip('\n') + '\n' + addition, encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root_file = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (root_file, audit):
        if not path.is_file():
            parser.error(f'missing {path}')
    for module, names in ITEMS:
        source = ROOT / (PREFIX.replace('.', '/') + module + '.lean')
        if not source.is_file():
            parser.error(f'missing {source}')
        src = source.read_text(encoding='utf-8')
        for name in names:
            if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src)) != 1:
                parser.error(f'missing or repeated theorem {name} in {source}')
        without_comments = re.sub(r'/-.*?-/', '', src, flags=re.S)
        if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', without_comments):
            parser.error(f'proof placeholder in {source}')
        for number, line in enumerate(src.splitlines(), 1):
            if line.rstrip() != line:
                parser.error(f'trailing whitespace {source}:{number}')
    if args.apply:
        ensure_lines(root_file, IMPORTS)
        ensure_lines(audit, IMPORTS, prepend=True)
        ensure_lines(audit, CHECKS)
    for path, lines in ((root_file, IMPORTS), (audit, IMPORTS + CHECKS)):
        body = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if body.count(line) != 1:
                parser.error(f'expected one {line!r} in {path}')
    print(f'PASS: {len(ITEMS)} modules, {len(NAMES)} theorems, '
          f'{len(CHECKS)} declaration/axiom audit lines')


if __name__ == '__main__':
    main()
