"""RamanujanTools replay with explicit CMF multiplication orders.

This verifies finite identities, not an all-N divisibility claim.
Dependency: ramanujantools revision e87622c8637b9a292364deea85cb201a00ca3ffc.
Run from this folder: python rt_blocks.py --depths 1 2 3
"""
import argparse,json,sys,time
from pathlib import Path
import sympy as sp
from flint import fmpq,fmpq_mat
from ramanujantools import Position
from ramanujantools.cmf.pfq import pFq

HERE=Path(__file__).resolve().parent
from core import START,DIRECTION,R,endpoint,segment,encode

AXES=sp.symbols('x0 x1 x2 x3 y0 y1 y2')
def rt_path(cmf,N,t):
    w=list(START);W=fmpq_mat([[1,0,0],[0,1,0],[0,0,1]]);moves=0
    for count,direction in [(t*N,(1,1,1,0,0,0,0)),(N,(0,0,0,0,2,1,3)),
                            (N,(10-t,9-t,11-t,0,0,0,0)),(11*N,(0,0,0,-1,0,0,0))]:
        for _ in range(count):
            for axis,amount in enumerate(direction):
                sign=amount>=0
                for _ in range(abs(amount)):
                    substitutions=Position(dict(zip(AXES,w)))
                    E=cmf.M(AXES[axis],sign).subs(substitutions)
                    E=fmpq_mat([[fmpq(str(E[i,j])) for j in range(3)] for i in range(3)])
                    W=W*E;w[axis]+=1 if sign else -1;moves+=1
    assert tuple(w)==endpoint(N)
    return W,moves

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--depths',type=int,nargs='+',default=[1,2,3])
    parser.add_argument('--output',type=Path,default=HERE/'rt_checks.json')
    args=parser.parse_args();cmf=pFq(4,3,1);checks=[]
    for N in args.depths:
        reference=segment(START,endpoint(N))
        for t in (3,4):
            start=time.perf_counter();W,moves=rt_path(cmf,N,t);assert W==reference
            checks.append(dict(N=N,plateau=t,unit_moves=moves,all_nine_entries_equal=True,
                               readout=str((R*W)[0,0]/(R*W)[1,0]),seconds=time.perf_counter()-start))
            print({k:v for k,v in checks[-1].items() if k!='readout'},flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(checks,indent=2))

if __name__=='__main__':main()
