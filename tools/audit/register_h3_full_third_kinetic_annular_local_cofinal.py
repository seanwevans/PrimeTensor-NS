#!/usr/bin/env python3
"""Register kinetic-only local annular PDE charges without terminal H3 integrability."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticAnnularLocalCofinal'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_highRadialSnapshot_kineticLocalAnnularWindow244',
    'thirdFullPhysical_secondaryTwoSlice_kineticLocalAnnularWindow244',
    'thirdFullPhysical_kineticLocalAnnular_forces_outerEscape244',
    'thirdFullPhysical_noH3Trace_kineticLocalAnnularCofinal244',
)
DEFS = ('ThirdFullKineticNaturalAnnularLocalWitness244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS + DEFS for line in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in lines if line not in existing]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + old if prepend else old.rstrip('\n') + '\n' + block,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source_file = ROOT / (MODULE.replace('.', '/') + '.lean')
    root_file = ROOT / 'PrimeTensor.lean'
    audit_file = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source_file, root_file, audit_file):
        if not path.is_file():
            parser.error(f'missing file: {path}')
    source = source_file.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing or repeated theorem: {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing or repeated definition: {name}')
    stripped = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', stripped):
        parser.error('proof placeholder or unsafe axiom detected')
    if any(line.rstrip() != line for line in source.splitlines()):
        parser.error('trailing whitespace in source')
    if args.apply:
        ensure_once(root_file, (IMPORT,))
        ensure_once(audit_file, (IMPORT,), prepend=True)
        ensure_once(audit_file, CHECKS)
    for path, required in ((root_file, (IMPORT,)), (audit_file, (IMPORT,) + CHECKS)):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f'expected once: {line} in {path}')
    print(f'PASS: kinetic local annular cofinal; '
          f'{len(THEOREMS)} theorems, {len(DEFS)} definitions, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
