#!/usr/bin/env python3
"""Idempotently register genuine kinetic-low-frequency quadratic Fourier estimates."""
from pathlib import Path
import argparse
import sys
sys.dont_write_bytecode = True
ROOT=Path(__file__).resolve().parents[2]
MODULE='PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Energy.TerminalLowRadialQuadraticKineticBound'
FILE=ROOT/(MODULE.replace('.', '/')+'.lean')
NAMES=('h3Critical_rawFourierReflectedShift_norm_eq', 'h3Critical_rawProductConvolution_le_rawL2Product', 'h3Critical_actual_rawConvolution_le_kineticAnchor', 'h3Critical_actual_lowRadial_derivativeConvolution_le_kineticAnchor')
IMPORT='import '+MODULE
AUDIT=tuple(x for n in NAMES for x in (
    '#check PrimeTensor.Bridge.Euclidean.'+n,
    '#print axioms PrimeTensor.Bridge.Euclidean.'+n))
def append(path, lines, front=False):
    old=path.read_text(); existing=set(old.splitlines())
    need=[l for l in lines if l not in existing]
    if need:
        part='\n'.join(need)+'\n'
        path.write_text(part+old if front else old.rstrip('\n')+'\n'+part)
def main():
    ap=argparse.ArgumentParser()
    g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--apply',action='store_true')
    g.add_argument('--check',action='store_true')
    args=ap.parse_args()
    root=ROOT/'PrimeTensor.lean'; audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
    for p in (root,audit,FILE):
        if not p.is_file(): ap.error('missing '+str(p))
    if args.apply:
        append(root,(IMPORT,))
        append(audit,(IMPORT,),front=True)
        append(audit,AUDIT)
    for p,required in ((root,(IMPORT,)),(audit,(IMPORT,)+AUDIT)):
        ls=p.read_text().splitlines()
        for s in required:
            if ls.count(s)!=1: ap.error(str(p)+': expected exactly one '+s)
    s=FILE.read_text()
    for n in NAMES:
        if s.count('theorem '+n+'\n')!=1:
            ap.error('missing or duplicate '+n)
    for word in ('sorry','admit','unsafe axiom'):
        if word in s: ap.error('placeholder '+word)
    print('PASS: 4 raw-convolution kinetic Fourier theorems and audit registration')
if __name__ == '__main__': main()
