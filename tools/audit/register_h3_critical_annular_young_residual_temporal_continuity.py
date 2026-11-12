#!/usr/bin/env python3
"""Register actual Fourier Young-residual continuity and sharp annular L² bridge."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungResidualTemporalContinuity'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_annularYoungResidualFourier_sub_norm_le244',
    'thirdFullPhysical_annularYoungResidualFourier_continuous244',
    'thirdFullPhysical_annularYoungResidualBand_continuous244',
    'thirdFullPhysical_actualAnnularYoungResidualBand_continuousAt244',
    'thirdFullPhysical_actualAnnularYoungResidualBandSquare_continuousAt244',
    'thirdFullPhysical_annularYoungResidualFourier_ae244',
    'thirdFullKinetic_sharpFourierAnnulusCutoff_ae244',
    'thirdFullKinetic_sharpFourierAnnulusCutoff_norm_sq_eq_integral244',
    'thirdFullPhysical_actualAnnularYoungResidualIntegral_continuousAt244',
)
DEFS = (
    'thirdFullPhysicalAnnularYoungResidualFourierL2244',
    'thirdFullPhysicalAnnularYoungResidualBandFourierL2244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in (*THEOREMS, *DEFS)
               for line in ('#check ' + NS + name,
                            '#print axioms ' + NS + name))


def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    present = set(old.splitlines())
    missing = [entry for entry in wanted if entry not in present]
    if missing:
        added = '\n'.join(missing) + '\n'
        path.write_text(
            added + old if prepend else old.rstrip('\n') + '\n' + added,
            encoding='utf-8'
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--apply', action='store_true')
    group.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = ROOT / (MODULE.replace('.', '/') + '.lean')
    pt = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for f in (src, pt, audit):
        if not f.is_file():
            parser.error(f'missing path: {f}')
    source = src.read_text(encoding='utf-8')
    source = re.sub(r'/-.*?-/', '', source, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    if re.search(r'\b(?:sorry|admit|axiom)\b', source):
        parser.error('placeholder proof or added axiom detected')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing/duplicate theorem {name}')
    for name in DEFS:
        if len(re.findall(r'(?m)^noncomputable def\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error(f'missing/duplicate definition {name}')
    if args.apply:
        register(pt, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for f, wanted in ((pt, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = f.read_text(encoding='utf-8').splitlines()
        for entry in wanted:
            if lines.count(entry) != 1:
                parser.error(f'missing/duplicate entry {entry} in {f}')
    print(f'PASS: annular Fourier Young residual ({len(THEOREMS)} theorems; {len(DEFS)} definitions)')


if __name__ == '__main__':
    main()
