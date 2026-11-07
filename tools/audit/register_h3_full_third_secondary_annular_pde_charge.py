#!/usr/bin/env python3
"""Register secondary attained high-radial PDE annular persistence/charge."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfilePrescribedGaugeLateViscousSecondaryAnnularPDECharge'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_secondaryHighRadialSpike_annularPDECharge244',
    'thirdFullPhysical_secondaryTwoSlice_forcesAnnularPDECharge244',
)
DEFS = ('ThirdFullSecondaryHighRadialAnnularPDECharge244',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(s for name in THEOREMS + DEFS for s in (
    '#check ' + NAMESPACE + name,
    '#print axioms ' + NAMESPACE + name,
))


def ensure_once(path: Path, lines, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    new = [line for line in lines if line not in seen]
    if new:
        block = '\n'.join(new) + '\n'
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
            parser.error(f'missing {path}')
    source = source_file.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing/repeated theorem: ' + name)
    for name in DEFS:
        if len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing/repeated definition: ' + name)
    without_comments = re.sub(r'/-.*?-/', '', source, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', without_comments):
        parser.error('proof placeholder found')
    if any(line.rstrip() != line for line in source.splitlines()):
        parser.error('trailing whitespace found')
    if args.apply:
        ensure_once(root_file, (IMPORT,))
        ensure_once(audit_file, (IMPORT,), prepend=True)
        ensure_once(audit_file, CHECKS)
    for path, lines in ((root_file, (IMPORT,)), (audit_file, (IMPORT,) + CHECKS)):
        data = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if data.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    print(f'PASS: secondary annular PDE charge, {len(THEOREMS)} theorems, '
          f'{len(DEFS)} definitions, {len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
