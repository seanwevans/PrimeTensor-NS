#!/usr/bin/env python3
"""Register three-profile native Fourier sixth-flux Schwartz integrability."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticMixedSchwartzIntegrability'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
DEFS = (
    'thirdFullKineticMixedSchwartzFirstContraction244',
    'thirdFullKineticMixedSchwartzSecondContraction244',
    'thirdFullKineticMixedSchwartzThirdContraction244',
)
THEOREMS = (
    'thirdFullKinetic_mixedSchwartz_first_integrable244',
    'thirdFullKinetic_mixedSchwartz_second_integrable244',
    'thirdFullKinetic_mixedSchwartz_third_integrable244',
    'thirdFullKinetic_mixedSchwartzBudget_eq_norms244',
    'thirdFullKinetic_mixedSchwartzBudget_integrable244',
    'thirdFullKinetic_mixedSchwartzFlux_aestronglyMeasurable244',
    'thirdFullKinetic_lowMax_mixedSchwartzFlux_integrable244',
    'thirdFullKinetic_lowMax_mixedSchwartzFlux_autoWeightedH3_244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(
    line for name in (*DEFS, *THEOREMS)
    for line in ('#check ' + NS + name, '#print axioms ' + NS + name)
)


def add_missing(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [line for line in wanted if line not in present]
    if missing:
        lines = '\n'.join(missing) + '\n'
        path.write_text(lines + old if prepend else old.rstrip('\n') + '\n' + lines,
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
    for decl, names in ((r'noncomputable\s+def', DEFS), (r'theorem', THEOREMS)):
        for name in names:
            matches = re.findall(r'(?m)^' + decl + r'\s+' + re.escape(name) + r'\b', code)
            if len(matches) != 1:
                parser.error(f'missing or duplicated declaration: {name}')
    without_comments = re.sub(r'/-.*?-/', '', code, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', without_comments):
        parser.error('proof placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace in Lean source')
    if args.apply:
        add_missing(root, [IMPORT])
        add_missing(audit, [IMPORT], prepend=True)
        add_missing(audit, CHECKS)
    for path, wanted in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in wanted:
            if lines.count(line) != 1:
                parser.error(f'missing/duplicated registration in {path}: {line}')
    print('PASS: mixed Schwartz sixth flux: ' +
          f'{len(DEFS)} definitions, {len(THEOREMS)} theorems, ' +
          f'{len(CHECKS)} audit declarations')


if __name__ == '__main__':
    main()
