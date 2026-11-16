#!/usr/bin/env python3
"""Register genuine Z3 Fourier Wiener and ordered derivative convolution theorems."""
from pathlib import Path
import argparse, re, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[2]
MODULE='PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3WienerOrderedConvolution'
NS='PrimeTensor.FirstMonomialTriad.'
THEOREMS=(
 'thirdFullThreeBand_z3Degree_nonneg244',
 'thirdFullThreeBand_z3Degree_add_le244',
 'thirdFullThreeBand_z3Weight_pos244',
 'thirdFullThreeBand_z3Weight_monotone244',
 'thirdFullThreeBand_z3Weight_add_le_mul244',
 'thirdFullThreeBand_z3OrderedWienerBound244',
 'thirdFullThreeBand_z3OrderedDerivativeWienerBound244',
 'thirdFullThreeBand_z3GalerkinSourceMajorant244',
)
DEFS=('thirdFullThreeBandZ3Degree244','thirdFullThreeBandZ3Weight244')
IMPORT='import '+MODULE
CHECKS=tuple(l for n in (*DEFS,*THEOREMS)
  for l in ('#check '+NS+n,'#print axioms '+NS+n))
def add_missing(path,entries,prepend=False):
 old=path.read_text(encoding='utf-8'); lines=set(old.splitlines())
 missing=[x for x in entries if x not in lines]
 if missing:
  block='\n'.join(missing)+'\n'
  path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,encoding='utf-8')
def main():
 p=argparse.ArgumentParser(description=__doc__)
 mode=p.add_mutually_exclusive_group(required=True)
 mode.add_argument('--apply',action='store_true')
 mode.add_argument('--check',action='store_true')
 args=p.parse_args()
 src=ROOT/(MODULE.replace('.','/')+'.lean')
 root=ROOT/'PrimeTensor.lean'
 audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
 for path in (src,root,audit):
  if not path.is_file():p.error(f'missing {path}')
 code=src.read_text(encoding='utf-8')
 stripped=re.sub(r'/-.*?-/', '', code, flags=re.S)
 stripped=re.sub(r'--[^\n]*','',stripped)
 if re.search(r'\b(?:sorry|admit|axiom)\b',stripped):p.error('placeholder proof or axiom')
 if any(line!=line.rstrip() for line in code.splitlines()):p.error('trailing whitespace')
 for kw,names in (('theorem',THEOREMS),('def',DEFS)):
  for n in names:
   if len(re.findall(r'(?m)^'+kw+r'\s+'+re.escape(n)+r'\b',code))!=1:
    p.error('missing or duplicate '+kw+' '+n)
 if args.apply:
  add_missing(root,[IMPORT]);add_missing(audit,[IMPORT],prepend=True)
  add_missing(audit,CHECKS)
 for path,required in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
  lines=path.read_text(encoding='utf-8').splitlines()
  for line in required:
   if lines.count(line)!=1:p.error('missing or duplicate registration: '+str(path)+' '+line)
 print(f'PASS: concrete Z3 Wiener geometry: {len(THEOREMS)} theorems, {len(DEFS)} definitions, {len(CHECKS)} trust probes')
if __name__=='__main__':main()
