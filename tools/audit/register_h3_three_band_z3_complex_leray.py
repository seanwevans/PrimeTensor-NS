#!/usr/bin/env python3
"""Register genuine complex Euclidean Leray contraction and ordered Wiener source."""
from pathlib import Path
import argparse, re, sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
MODULE = 'PrimeTensor.Fluid.Vorticity.Continuation.H3.Critical.Transport.FullThirdSolenoidalKineticThreeBandZ3ComplexLerayWiener'
NS = 'PrimeTensor.FirstMonomialTriad.'
THEOREMS = (
 'thirdFullThreeBand_z3ComplexLeray_norm_le244',
 'thirdFullThreeBand_z3ComplexLeray_operatorNorm_le244',
 'thirdFullThreeBand_z3ComplexTransport_norm_le244',
 'thirdFullThreeBand_z3ComplexOrderedWienerBound244',
)
DEFS = (
 'thirdFullThreeBandZ3ComplexFrequency244',
 'thirdFullThreeBandZ3ComplexLeray244',
 'thirdFullThreeBandZ3ComplexTransport244',
)
IMPORT = 'import ' + MODULE
CHECKS = tuple(item for name in (*DEFS, *THEOREMS)
  for item in ('#check '+NS+name, '#print axioms '+NS+name))

def add_missing(path, lines, prepend=False):
 old=path.read_text(encoding='utf-8'); existing=set(old.splitlines())
 missing=[line for line in lines if line not in existing]
 if missing:
  block='\n'.join(missing)+'\n'
  path.write_text(block+old if prepend else old.rstrip('\n')+'\n'+block,encoding='utf-8')

def main():
 p=argparse.ArgumentParser(description=__doc__)
 mode=p.add_mutually_exclusive_group(required=True)
 mode.add_argument('--apply',action='store_true')
 mode.add_argument('--check',action='store_true')
 args=p.parse_args()
 source=ROOT/(MODULE.replace('.','/')+'.lean')
 root=ROOT/'PrimeTensor.lean'; audit=ROOT/'tools/audit/FirstMonomialTriad.lean'
 for path in (source,root,audit):
  if not path.is_file():p.error('missing '+str(path))
 code=source.read_text(encoding='utf-8')
 stripped=re.sub(r'/-.*?-/', '', code, flags=re.S)
 stripped=re.sub(r'--[^\n]*','',stripped)
 if re.search(r'\b(?:sorry|admit|axiom)\b',stripped):p.error('placeholder proof or axiom')
 for n in THEOREMS:
  if len(re.findall(r'(?m)^theorem\s+'+re.escape(n)+r'\b',code))!=1:
   p.error('missing or duplicate theorem '+n)
 for n in DEFS:
  if len(re.findall(r'(?m)^def\s+'+re.escape(n)+r'\b',code))!=1:
   p.error('missing or duplicate def '+n)
 if any(line!=line.rstrip() for line in code.splitlines()):p.error('trailing whitespace')
 if args.apply:
  add_missing(root,(IMPORT,)); add_missing(audit,(IMPORT,),prepend=True)
  add_missing(audit,CHECKS)
 for path,required in ((root,(IMPORT,)),(audit,(IMPORT,*CHECKS))):
  lines=path.read_text(encoding='utf-8').splitlines()
  for line in required:
   if lines.count(line)!=1:p.error('missing/duplicate registration '+str(path)+' '+line)
 print(f'PASS: Z3 complex Leray source ({len(THEOREMS)} theorems, '
       f'{len(DEFS)} definitions, {len(CHECKS)} trust probes)')

if __name__=='__main__': main()
