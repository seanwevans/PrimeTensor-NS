#!/usr/bin/env python3
"""Register actual weighted-H3 Fourier inputs for the asymmetric mixed sixth flux."""
import argparse
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticMixedWeightedSpectralBridge'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
DEFS = ('thirdFullKineticSchwartzPolarization244',)
THEOREMS = (
    'thirdFullKineticSchwartzPolarization_amplitude244',
    'thirdFullKineticSchwartzPolarization_moments_integrable244',
    'thirdFullKineticWeightedSchwartz_scalarFourierL1_le244',
    'thirdFullKineticWeightedSchwartz_vectorFourierL1_le244',
    'thirdFullKineticWeightedSchwartz_vectorFourierL2_le244',
    'thirdFullKineticWeightedSchwartz_vectorMoments_le244',
    'thirdFullKineticWeightedSchwartz_velocityMoments_le244',
    'thirdFullKinetic_lowMax_mixedSchwartzFlux_le_weightedH3_244',
    'thirdFullKinetic_lowMax_mixedSchwartzFlux_le_spectralVelocities244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(
    line for name in (*DEFS, *THEOREMS)
    for line in ('#check ' + NAMESPACE + name,
                 '#print axioms ' + NAMESPACE + name)
)


def add_missing(path: Path, wanted, prepend=False):
    original = path.read_text(encoding='utf-8')
    existing = set(original.splitlines())
    missing = [line for line in wanted if line not in existing]
    if missing:
        block = '\n'.join(missing) + '\n'
        path.write_text(block + original if prepend else
                        original.rstrip('\n') + '\n' + block,
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
    cleaned = re.sub(r'/-.*?-/', '', code, flags=re.S)
    if re.search(r'\b(?:sorry|admit)\b|\bunsafe\s+axiom\b', cleaned):
        parser.error('proof placeholder or unsafe axiom')
    if any(line != line.rstrip() for line in code.splitlines()):
        parser.error('trailing whitespace')
    if args.apply:
        add_missing(root, [IMPORT])
        add_missing(audit, [IMPORT], prepend=True)
        add_missing(audit, CHECKS)
    for file, required in ((root, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = file.read_text(encoding='utf-8').splitlines()
        for line in required:
            if lines.count(line) != 1:
                parser.error(f'missing or repeated registration: {file}: {line}')
    print(f'PASS: mixed weighted spectral bridge: {len(DEFS)} definition, '
          f'{len(THEOREMS)} theorems, {len(CHECKS)} audit declarations')


if __name__ == '__main__':
    main()
