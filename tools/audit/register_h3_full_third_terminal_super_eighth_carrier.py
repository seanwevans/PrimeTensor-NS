#!/usr/bin/env python3
"""Audit the arbitrary-profile physical kinetic eighth-power carrier escape."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
ITEMS = (
    ('FullThirdSolenoidalTerminalProfileKineticEighthAnchor', (
        'thirdFullPhysical_profileAnnulus_kineticEighthAnchor244',
        'thirdFullPhysical_profileCofinalAnnuli_kineticEighthAnchor244',
    )),
    ('FullThirdSolenoidalTerminalProfileSuperEighthCarrierEscape', (
        'thirdFull_superEighthProfile_kineticCost_forces_outerEscape244',
        'thirdFullPhysical_noH3Trace_superEighthMinimalCarrierEscape244',
    )),
)
IMPORTS = tuple('import ' + PREFIX + name for name, _ in ITEMS)
DECLARATIONS = tuple(decl for _, names in ITEMS for decl in names)
CHECKS = tuple(line for decl in DECLARATIONS for line in (
    '#check ' + NAMESPACE + decl,
    '#print axioms ' + NAMESPACE + decl,
))


def ensure_once(path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    new = [line for line in lines if line not in seen]
    if new:
        new_text = '\n'.join(new) + '\n'
        path.write_text(new_text + old if prepend else
                        old.rstrip('\n') + '\n' + new_text,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    mainfile = ROOT / 'PrimeTensor.lean'
    auditfile = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for file in (mainfile, auditfile):
        if not file.is_file():
            parser.error(f'missing {file}')
    for module, names in ITEMS:
        path = ROOT / (PREFIX.replace('.', '/') + module + '.lean')
        if not path.is_file():
            parser.error(f'missing {path}')
        source = path.read_text(encoding='utf-8')
        for name in names:
            if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
                parser.error(f'missing or repeated theorem {name}: {path}')
        stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
        if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', stripped):
            parser.error(f'proof placeholder in {path}')
        if any(line.rstrip() != line for line in source.splitlines()):
            parser.error(f'trailing whitespace in {path}')
    if args.apply:
        ensure_once(mainfile, IMPORTS)
        ensure_once(auditfile, IMPORTS, prepend=True)
        ensure_once(auditfile, CHECKS)
    for path, lines in ((mainfile, IMPORTS), (auditfile, IMPORTS + CHECKS)):
        text = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if text.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    print(f'PASS: {len(ITEMS)} modules, {len(DECLARATIONS)} theorems, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
