#!/usr/bin/env python3
"""Register optimal inner-radius normalization and cofinal physical tail clocks."""
from pathlib import Path
import argparse
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = (
    'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.'
    'FullThirdSolenoidalTerminalProfileKineticSignedLowMaxCriticalAnnularCofinalOptimalInnerClock'
)
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
    'thirdFullPhysical_outerViscousCapSlope_nonneg244',
    'thirdFullPhysical_annularCapClockFactor_mono_inner244',
    'thirdFullPhysical_annularClockHeight_antitone_inner244',
    'thirdFull_scalar_rightWindowHeight_le_terminalTail244',
    'thirdFull_scalar_tailCost_forces_widthCompression244',
    'thirdFullPhysical_actualAnnularDeficit_optimalInnerClockRightWindow244',
    'thirdFullPhysical_cofinalAnnularUniformSnapshots_optimalInnerClocks244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS
               for line in ('#check ' + NS + name,
                            '#print axioms ' + NS + name))


def register(path: Path, wanted, prepend=False):
    old = path.read_text(encoding='utf-8')
    existing = set(old.splitlines())
    missing = [line for line in wanted if line not in existing]
    if missing:
        extra = '\n'.join(missing) + '\n'
        path.write_text(extra + old if prepend else old.rstrip('\n') + '\n' + extra,
                        encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = ROOT / (MODULE.replace('.', '/') + '.lean')
    pt = ROOT / 'PrimeTensor.lean'
    audit = ROOT / 'tools/audit/FirstMonomialTriad.lean'
    for f in (src, pt, audit):
        if not f.is_file():
            parser.error(f'missing {f}')
    source = src.read_text(encoding='utf-8')
    code = re.sub(r'/-.*?-/', '', source, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    if re.search(r'\b(?:sorry|admit|axiom)\b', code):
        parser.error('placeholder proof or added axiom detected')
    for name in THEOREMS:
        n = len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', code))
        if n != 1:
            parser.error(f'missing/duplicate theorem: {name} ({n})')
    if args.apply:
        register(pt, (IMPORT,))
        register(audit, (IMPORT,), prepend=True)
        register(audit, CHECKS)
    for f, expected in ((pt, (IMPORT,)), (audit, (IMPORT, *CHECKS))):
        lines = f.read_text(encoding='utf-8').splitlines()
        for line in expected:
            if lines.count(line) != 1:
                parser.error(f'missing/duplicate entry: {line} in {f}')
    print(f'PASS: optimal inner cofinal clock ({len(THEOREMS)} theorems)')


if __name__ == '__main__':
    main()
