#!/usr/bin/env python3
"""Register sharp square-root quartic source-peak calibration."""
from pathlib import Path
import argparse
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourcePeakSquareRootQuarticCalibration'
SOURCE = ROOT / (MODULE.replace('.', '/') + '.lean')
ROOT_LEAN = ROOT / 'PrimeTensor.lean'
AUDIT = ROOT / 'tools/audit/FirstMonomialTriad.lean'
THEOREMS = ('h3Critical_positiveSourceMargin_squareRootDominantQuarticRadius', 'h3Critical_squareRootRadius_exactFourthPowerIdentity', 'h3Critical_squareRootRadius_fourthPowerPolynomialCeiling', 'h3Critical_squareRootRadius_le_old_of_costDominance', 'h3Critical_squareRootQuarticWidth_ge_old_of_costDominance', 'h3Critical_strictSourcePeak_squareRootCalibratedQuarticPersistence', 'h3Critical_noL2Trace_cofinalSquareRootQuarticWidths_and_fullCosts', 'h3Critical_squareRootFiniteCharge_forces_width_or_quarticMargin', 'h3Critical_squareRootPhysicalCharge_forces_width_or_quarticMargin')
DEFS = ('h3CriticalSourcePeakSquareRootRadius',)
IMPORT = 'import ' + MODULE
CHECKS = tuple(line for name in THEOREMS for line in (
    '#check PrimeTensor.Bridge.Euclidean.' + name,
    '#print axioms PrimeTensor.Bridge.Euclidean.' + name,
))

def install(path, lines, prepend=False):
    content = path.read_text(encoding='utf-8')
    existing = set(content.splitlines())
    missing = [x for x in lines if x not in existing]
    if missing:
        blob = '\n'.join(missing) + '\n'
        path.write_text(blob + content if prepend else content.rstrip('\n') + '\n' + blob, encoding='utf-8')

def main():
    p=argparse.ArgumentParser()
    m=p.add_mutually_exclusive_group(required=True)
    m.add_argument('--apply',action='store_true')
    m.add_argument('--check',action='store_true')
    a=p.parse_args()
    for f in (SOURCE,ROOT_LEAN,AUDIT):
        if not f.is_file(): p.error('missing: '+str(f))
    if a.apply:
        install(ROOT_LEAN,(IMPORT,))
        install(AUDIT,(IMPORT,),prepend=True)
        install(AUDIT,CHECKS)
    for f,entries in ((ROOT_LEAN,(IMPORT,)),(AUDIT,(IMPORT,)+CHECKS)):
        lines=f.read_text().splitlines()
        for x in entries:
            if lines.count(x)!=1: p.error('expected exactly one: '+x+' in '+str(f))
    src=SOURCE.read_text()
    for x in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+'+re.escape(x)+r'\b',src))!=1:
            p.error('missing theorem '+x)
    for x in DEFS:
        if len(re.findall(r'(?m)^noncomputable def\s+'+re.escape(x)+r'\b',src))!=1:
            p.error('missing definition '+x)
    for bad in (r'\bsorry\b',r'\badmit\b',r'\bunsafe\s+axiom\b'):
        if re.search(bad,src): p.error('forbidden placeholder: '+bad)
    print('PASS',len(THEOREMS),'theorems',len(CHECKS),'axiom checks')

if __name__ == '__main__': main()
