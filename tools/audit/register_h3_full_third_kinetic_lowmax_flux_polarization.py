#!/usr/bin/env python3
"""Register native low-max complex sixth-flux polarization identities."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticLowMaxFluxPolarization'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('thirdFullKineticMixedPolarSixthFlux244',)
THEOREMS = (
    'thirdFullComplexSixthPowerFlux_firstSub244',
    'thirdFullComplexSixthPowerFlux_middleSub244',
    'thirdFullComplexSixthPowerFlux_lastSub244',
    'thirdFullComplexSixthPowerFlux_subTelescope244',
    'thirdFullKineticMixedPolarSixthFlux_schwartz244',
    'thirdFullKineticMixedPolarSixthFlux_telescope244',
    'thirdFullKinetic_lowMax_allFrequenciesBelow244',
    'thirdFullKinetic_lowMax_polarKernel_congr244',
    'thirdFullKinetic_lowMax_polarIntegral_congr244',
    'thirdFullKinetic_lowMax_integralTelescope244',
    'thirdFullKinetic_lowMax_integralDifferenceBudget244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(
    line for name in (*DEFS, *THEOREMS)
    for line in ('#check ' + NAMESPACE + name,
                 '#print axioms ' + NAMESPACE + name)
)


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
    if missing:
        new = '\n'.join(missing) + '\n'
        path.write_text(new + old if prepend else old.rstrip('\n') + '\n' + new,
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
    for file in (source, root, audit):
        if not file.is_file():
            parser.error(f'missing file: {file}')
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
    for path, required in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f'missing or duplicate registration in {path}: {line}')
    print(f'PASS: native low-max sixth flux polarization: '
          f'{len(DEFS)} definition, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} audit declarations')


if __name__ == '__main__':
    main()
