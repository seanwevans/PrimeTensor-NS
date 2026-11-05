#!/usr/bin/env python3
"""Idempotent registrar for the solenoidal full-third minimum-frequency partition."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = ('PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
          'FullThirdSolenoidalMinimumFrequencyPartition')
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
DEFS = (
    'thirdFullMinFirstSector244',
    'thirdFullMinMiddleSector244',
    'thirdFullMinLastSector244',
)
THEOREMS = (
    'thirdFullMinFirstSector_measurable244',
    'thirdFullMinMiddleSector_measurable244',
    'thirdFullMinLastSector_measurable244',
    'thirdFullMinFirstMiddle_disjoint244',
    'thirdFullMinFirstLast_disjoint244',
    'thirdFullMinMiddleLast_disjoint244',
    'thirdFullMinFirstMiddleUnionLast_disjoint244',
    'thirdFullMinSectors_cover244',
    'thirdFullMinFirstSector_isLow244',
    'thirdFullMinMiddleSector_isLow244',
    'thirdFullMinLastSector_isLow244',
    'thirdFullSchwartzSixthPowerFlux_minSectorIntegralSplit244',
    'thirdFullSchwartzSixthPowerFlux_globalMinSectorMomentBound244',
    'thirdFullWeightedSchwartz_globalMinSectorIntegral_le244',
    'exists_thirdFullPhysicalSnapshot_globalMinSectorH3Bound244',
)
IMPORT = 'import ' + MODULE
CHECKS = [s for name in DEFS + THEOREMS for s in (
    '#check PrimeTensor.FirstMonomialTriad.' + name,
    '#print axioms PrimeTensor.FirstMonomialTriad.' + name,
)]


def ensure_lines(path: Path, entries, prepend=False):
    old = path.read_text(encoding='utf-8')
    seen = set(old.splitlines())
    missing = [entry for entry in entries if entry not in seen]
    if missing:
        payload = '\n'.join(missing) + '\n'
        path.write_text((payload + old) if prepend else
                        (old.rstrip('\n') + '\n' + payload), encoding='utf-8')


def main():
    parser = argparse.ArgumentParser()
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--apply', action='store_true')
    choice.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error(f'missing {path}')
    if args.apply:
        ensure_lines(ROOT_LEAN, (IMPORT,))
        ensure_lines(AUDIT, (IMPORT,), prepend=True)
        ensure_lines(AUDIT, CHECKS)
    for path, entries in ((ROOT_LEAN, (IMPORT,)),
                          (AUDIT, (IMPORT,) + tuple(CHECKS))):
        lines = path.read_text(encoding='utf-8').splitlines()
        for line in entries:
            if lines.count(line) != 1:
                parser.error(f'expected exactly one {line!r} in {path}')
    src = SOURCE.read_text(encoding='utf-8')
    for name in DEFS:
        n = len(re.findall(r'(?m)^(?:noncomputable\s+)?def\s+' + re.escape(name) + r'\b', src))
        if n != 1:
            parser.error(f'missing or duplicate def {name} ({n})')
    for name in THEOREMS:
        n = len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', src))
        if n != 1:
            parser.error(f'missing or duplicate theorem {name} ({n})')
    if re.search(r'\b(sorry|admit)\b|\bunsafe\s+axiom\b', src):
        parser.error('proof placeholders prohibited')
    print(f'PASS: {len(DEFS)} defs, {len(THEOREMS)} theorems, '
          f'{len(CHECKS)} declaration/axiom checks')


if __name__ == '__main__':
    main()
