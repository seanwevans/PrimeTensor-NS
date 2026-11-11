#!/usr/bin/env python3
"""Register the derivative-free critical H3 highpass fifth/phase balance."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalHighpassFifthPhaseBalance'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_cubic_le_twoFifthPhase_density244',
    'thirdFullKinetic_bandCubic_le_twoFifthPhase244',
    'thirdFullPhysical_highCubic_le_twoHighFifthPhase_coordinate244',
    'thirdFullPhysical_highCubic_le_twoHighFifthPhase244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS
               for line in ('#check ' + NS + name, '#print axioms ' + NS + name))


def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
    if missing:
        added = '\n'.join(missing) + '\n'
        path.write_text(added + old if prepend else old.rstrip('\n') + '\n' + added,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (src, root, audit):
        if not p.is_file():
            parser.error(f'missing file: {p}')
    code = src.read_text(encoding='utf-8')
    code = re.sub(r'/-.*?-/', '', code, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    if re.search(r'\b(?:sorry|admit|axiom)\b', code):
        parser.error('unexpected placeholder or axiom')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code)) != 1:
            parser.error(f'missing or duplicate theorem: {name}')
    if args.apply:
        register(root, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for path, wanted in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for entry in wanted:
            if lines.count(entry) != 1:
                parser.error(f'missing or duplicate {entry} in {path}')
    print(f'PASS: critical highpass fifth/phase balance ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
