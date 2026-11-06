#!/usr/bin/env python3
"""Register moving raw Fourier tightness and critical-eighth escape theorems."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
ITEMS = (
    ('FullThirdSolenoidalTerminalProfileMovingRawFourierTightness', (
        'thirdFullPhysical_movingRawHighpass_norm_tendsto_zero244',
        'thirdFull_bandRawKineticMass_le_three_highpass244',
        'thirdFullPhysical_actualRawFourierVector_eq_physical244',
        'thirdFullPhysical_movingBandRawMass_tendsto_zero_of_L2Trace244',
    )),
    ('FullThirdSolenoidalTerminalProfileCriticalEighthTightEscape', (
        'thirdFullPhysical_noH3Trace_criticalEighthMinimalCarrier_outerEscape244',
    )),
)
IMPORTS = tuple('import ' + PREFIX + name for name, _ in ITEMS)
DECLARATIONS = tuple(name for _, names in ITEMS for name in names)
CHECKS = tuple(line for name in DECLARATIONS for line in (
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
    for module, names in ITEMS:
        path = ROOT / (PREFIX.replace('.', '/') + module + '.lean')
        if not path.is_file():
            parser.error(f'missing {path}')
        source = path.read_text(encoding='utf-8')
        for name in names:
            matches = re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)
            if len(matches) != 1:
                parser.error(f'missing/repeated theorem {name}: {path}')
        stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
        if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', stripped):
            parser.error(f'proof placeholder in {path}')
        if any(line.rstrip() != line for line in source.splitlines()):
            parser.error(f'trailing whitespace in {path}')
    if args.apply:
        ensure_once(root, IMPORTS)
        ensure_once(audit, IMPORTS, prepend=True)
        ensure_once(audit, CHECKS)
    for path, lines in ((root, IMPORTS), (audit, IMPORTS + CHECKS)):
        body = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if body.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    print(f'PASS: {len(ITEMS)} modules, {len(DECLARATIONS)} theorems, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
