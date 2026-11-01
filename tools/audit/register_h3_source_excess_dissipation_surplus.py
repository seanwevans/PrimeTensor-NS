#!/usr/bin/env python3
"""Register quantitative physical high-radial H3 dissipation source-excess costs."""
from pathlib import Path
import argparse
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessDissipationSurplus'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = (
    'h3Critical_actualHighpassSourceExcess_le_highRadialDissipationSurplus',
    'h3Critical_strictSourceExcess_forces_quantitativeHighRadialSurplus',
    'h3Critical_sourceMassExcess_forces_quantitativeHighRadialSurplus',
    'h3Critical_noL2Trace_sourceExcess_disjointEnhancedFullDissipationCosts',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))

def install(path, entries, prepend=False):
    content = path.read_text(encoding='utf-8')
    existing = set(content.splitlines())
    missing = [line for line in entries if line not in existing]
    if missing:
        chunk = '\n'.join(missing) + '\n'
        path.write_text(chunk + content if prepend else content.rstrip('\n') + '\n' + chunk,
                        encoding='utf-8')

def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path in (SOURCE, ROOT_LEAN, AUDIT):
        if not path.is_file():
            parser.error('missing: ' + str(path))
    if args.apply:
        install(ROOT_LEAN, (IMPORT,))
        install(AUDIT, (IMPORT,), prepend=True)
        install(AUDIT, CHECKS)
    for path, lines in ((ROOT_LEAN, (IMPORT,)), (AUDIT, (IMPORT,) + CHECKS)):
        content = path.read_text(encoding='utf-8').splitlines()
        for line in lines:
            if content.count(line) != 1:
                parser.error('expected exactly one ' + repr(line) + ' in ' + str(path))
    source = SOURCE.read_text(encoding='utf-8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+' + re.escape(name) + r'\b', source)) != 1:
            parser.error('missing/duplicate theorem: ' + name)
    for pat in (r'\bsorry\b', r'\badmit\b', r'\bunsafe\s+axiom\b'):
        if re.search(pat, source):
            parser.error('forbidden proof hole: ' + pat)
    print('PASS:', len(THEOREMS), 'theorems;', len(CHECKS), 'audit checks')

if __name__ == '__main__':
    main()
