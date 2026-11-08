#!/usr/bin/env python3
"""Register the native mixed low-max radial sixth-flux budget and its audit."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticLowMaxMixedRadialBudget'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('thirdFullKineticMixedPolarSixthBudget244',)
THEOREMS = (
    'thirdFullKineticMixedPolarSixthBudget_nonneg244',
    'thirdFullKineticMixedPolarSixthFlux_radialSpread_le244',
    'thirdFullKinetic_lowMax_squareRadiusAndSpread_le244',
    'thirdFullKinetic_lowMax_mixedFlux_le_radiusBudget244',
    'thirdFullKinetic_lowMax_mixedIntegral_le_radiusBudget244',
    'thirdFullKinetic_lowMax_difference_le_threeRadiusBudgets244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*DEFS, *THEOREMS)
               for line in ('#check ' + NAMESPACE + name,
                            '#print axioms ' + NAMESPACE + name))


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
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
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    root = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for path in (source, root, audit):
        if not path.is_file():
            parser.error(f'missing file: {path}')
    code = source.read_text(encoding='utf-8')
    for kind, names in ((r'noncomputable\s+def', DEFS), (r'theorem', THEOREMS)):
        for name in names:
            pat = r'(?m)^' + kind + r'\s+' + re.escape(name) + r'\b'
            if len(re.findall(pat, code)) != 1:
                parser.error(f'declaration missing or repeated: {name}')
    without_comments = re.sub(r'/-.*?-/', '', code, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', without_comments):
        parser.error('proof placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        add_missing(root, [IMPORT])
        add_missing(audit, [IMPORT], prepend=True)
        add_missing(audit, CHECKS)
    for path, wanted in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                parser.error(f'missing or duplicate registration: {path} {line}')
    print(f'PASS: kinetic low-max mixed radial budget: '
          f'{len(DEFS)} definition, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} audit declarations')


if __name__ == '__main__':
    main()
