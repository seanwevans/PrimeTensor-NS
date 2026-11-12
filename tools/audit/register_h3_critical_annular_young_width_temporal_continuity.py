#!/usr/bin/env python3
"""Register actual cubic-weighted annular Young gap and width continuity."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularYoungWidthTemporalContinuity'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullKinetic_finiteCubicRootSymbol_mem_Icc244',
    'thirdFullKinetic_finiteCubicRootSymbol_measurable244',
    'thirdFullKinetic_finiteCubicRootMultiplier_memLp244',
    'thirdFullKinetic_finiteCubicRootMultiplier_ae244',
    'thirdFullKinetic_finiteCubicRootMultiplier_norm_le244',
    'thirdFullKinetic_finiteCubicRootMultiplier_add244',
    'thirdFullKinetic_finiteCubicRootMultiplier_smul244',
    'thirdFullKinetic_finiteCubicRootMultiplierCLM_apply244',
    'thirdFullKinetic_sharpAnnulusCubicWeight_normSq244',
    'thirdFullPhysical_annularYoungResidualWeightedIntegral_eq_normSq244',
    'thirdFullPhysical_annularYoungWidthHilbertCost_continuous244',
    'thirdFullPhysical_actualYoungWidthCost_eq_hilbert244',
    'thirdFullPhysical_actualAnnularYoungWidthCost_continuousAt244',
    'thirdFullPhysical_actualAnnularKineticDeficit_continuousAt244',
    'thirdFullPhysical_annularDeficit_snapshotRightWindowCharge_auto244',
)
DEFS = (
    'thirdFullKineticFiniteCubicRootSymbol244',
    'thirdFullKineticFiniteCubicRootMultiplierApply244',
    'thirdFullKineticFiniteCubicRootMultiplierCLM244',
    'thirdFullPhysicalAnnularYoungWidthHilbertCost244',
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
    print(f'PASS: annular Young width ({len(THEOREMS)} theorems; {len(DEFS)} definitions)')


if __name__ == '__main__':
    main()
