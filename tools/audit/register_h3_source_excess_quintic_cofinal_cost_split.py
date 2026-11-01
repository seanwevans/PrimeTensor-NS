#!/usr/bin/env python3
"""Register cofinal quintic three-way physical PDE concentration gates."""
from pathlib import Path
import argparse, re, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE='PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalActualSourceExcessQuinticCofinalCostSplit'
SOURCE=ROOT/(MODULE.replace('.', '/')+'.lean')
ROOT_LEAN=ROOT/'PrimeTensor.lean'
AUDIT=ROOT/'tools/audit/FirstMonomialTriad.lean'
THEOREMS=('h3Critical_quinticMargin_cutoffOrPDECost', 'h3Critical_quinticCutoffBranch_normalizesToLinearSource', 'h3Critical_quinticMargin_normalizedCutoffOrPDECost', 'h3Critical_quinticMargin_largeSource_forces_PDECost', 'h3Critical_noL2Trace_cofinalFivefoldSource_quinticThreeWayCostGate')
IMPORT='import '+MODULE
CHECKS=tuple(line for name in THEOREMS for line in (
 '#check PrimeTensor.Bridge.Euclidean.'+name,
 '#print axioms PrimeTensor.Bridge.Euclidean.'+name))

def install(path, entries, prepend=False):
    old=path.read_text(encoding='utf8'); present=set(old.splitlines())
    missing=[x for x in entries if x not in present]
    if missing:
        extra='\n'.join(missing)+'\n'
        path.write_text(extra+old if prepend else old.rstrip('\n')+'\n'+extra,encoding='utf8')

def main():
    parser=argparse.ArgumentParser()
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--apply',action='store_true');mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    for p in (SOURCE,ROOT_LEAN,AUDIT):
        if not p.is_file():parser.error('missing: '+str(p))
    if args.apply:
        install(ROOT_LEAN,(IMPORT,));install(AUDIT,(IMPORT,),prepend=True)
        install(AUDIT,CHECKS)
    for p,entries in ((ROOT_LEAN,(IMPORT,)),(AUDIT,(IMPORT,)+CHECKS)):
        lines=p.read_text(encoding='utf8').splitlines()
        for x in entries:
            if lines.count(x)!=1:parser.error('expected exactly one '+repr(x)+' in '+str(p))
    source=SOURCE.read_text(encoding='utf8')
    for name in THEOREMS:
        if len(re.findall(r'(?m)^theorem\s+'+re.escape(name)+r'\b',source))!=1:
            parser.error('missing or duplicate theorem: '+name)
    for bad in (r'\bsorry\b',r'\badmit\b',r'\bunsafe\s+axiom\b'):
        if re.search(bad,source):parser.error('forbidden proof placeholder: '+bad)
    print('PASS:',len(THEOREMS),'theorems,',len(CHECKS),'axiom checks')
if __name__=='__main__':main()
