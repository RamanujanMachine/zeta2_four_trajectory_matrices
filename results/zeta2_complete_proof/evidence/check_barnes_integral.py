"""Independent numerical diagnostic for the sign/normalization in (A2).
The proof is in analytic_argument.tex; numerical quadrature is not used there.
"""
from pathlib import Path
import json,sys
import mpmath as mp
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/zeta2_orders_10911'))
from core import R,START,endpoint,segment,C
mp.mp.dps=140

def mpq(q):return mp.mpf(int(q.numerator))/int(q.denominator)

def main():
    rows=[]
    for N in (1,2):
        w=endpoint(N);state=R*segment(START,w);cn=mp.mpf(C(w));fac=mp.factorial(8*N)**3
        for r in range(3):
            expected=cn*(mp.zeta(2)*mpq(state[1,r])-mpq(state[0,r]))/2
            def integrand(y):
                t=6*N+1j*y
                gammas=mp.fprod(mp.gamma(t-v*N)*mp.gamma((v+8)*N+1-t) for v in (1,2,3))
                return mp.re((-t)**r*mp.beta(t,11*N+1)*gammas*mp.sin(mp.pi*t)/fac)
            actual=mp.quad(integrand,[0,N,2*N,4*N,8*N,16*N,mp.inf])/(mp.pi**2)
            relative=abs((actual-expected)/expected)
            assert relative<mp.mpf('1e-40'),(N,r,relative)
            rows.append({'N':N,'column':r,'scaled_error':mp.nstr(expected,30),'barnes_integral':mp.nstr(actual,30),'relative_difference':mp.nstr(relative,10)})
            print(rows[-1],flush=True)
    Path(__file__).with_name('barnes_integral_checks.json').write_text(json.dumps({'dps':mp.mp.dps,'checks':rows,'all_checks_passed':True},indent=2)+'\n')
if __name__=='__main__':main()
