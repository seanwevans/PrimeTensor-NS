#!/usr/bin/env python3
"""Register the genuine terminal-normalized critical annular clock obstruction."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalTerminalScaleRigidity'
)
NAMESPACE = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFull_scalar_terminalNormalizedClock_product244',
    'thirdFull_scalar_terminalNormalizedClock_min_le_sqrt244',
    'thirdFull_scalar_terminalCriticalHeight_relativeWidth_tendsto_zero244',
    'thirdFull_scalar_terminalNoncompression_scaledHeight_tendsto_zero244',
    'thirdFullPhysical_cofinalOptimalInnerClock_minTerminalScale_tendsto_zero244',
    'thirdFullPhysical_cofinalOptimalInnerClock_criticalHeight_forcesWidthCollapse244',
    'thirdFullPhysical_cofinalOptimalInnerClock_noncompression_forcesHeightCollapse244',
    'thirdFullPhysical_cofinalAnnularSnapshotMargins_terminalScaleCollapse244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for thm in THEOREMS for line in (
    '#check ' + NAMESPACE + thm,
    '#print axioms ' + NAMESPACE + thm))


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
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--apply', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = ROOT / (MODULE.replace('.', '/') + '.lean')
    rootlean = ROOT / 'PrimeTensor.lean'
    auditlean = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for p in (source, rootlean, auditlean):
        if not p.is_file():
            parser.error(f'missing {p}')
    content = source.read_text(encoding='utf-8')
    sanitized = re.sub(r'/-.*?-/', '', content, flags=re.S)
    sanitized = re.sub(r'--[^\n]*', '', sanitized)
    if re.search(r'\b(?:sorry|admit|axiom)\b', sanitized):
        parser.error('placeholder or unproved axiom found in the Lean source')
    for thm in THEOREMS:
        count = len(re.findall(r'(?m)^theorem\s+' + re.escape(thm) + r'\b', sanitized))
        if count != 1:
            parser.error(f'theorem missing/duplicated: {thm}: {count}')
    if args.apply:
        register(rootlean, (IMPORT,))
        register(auditlean, (IMPORT,), prepend=True)
        register(auditlean, CHECKS)
    for p, expected in ((rootlean, (IMPORT,)), (auditlean, (IMPORT, *CHECKS))):
        lines = p.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line) != 1:
                parser.error(f'expected exactly one {line} in {p}')
    print(f'PASS: cofinal terminal-scale rigidity ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
