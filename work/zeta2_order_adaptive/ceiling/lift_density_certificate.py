"""Exact rational bounds for the periodic-shell density, conditional mu arithmetic.

The finite density sum and tail estimate are exact. Application to CMF
integrality is a separate argument and is not inferred by this script.
"""
import json,sys
from fractions import Fraction as F
from pathlib import Path
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
OUT=Path(__file__).resolve().parent
BASE=((2,8,1),(3,9,2),(4,10,3),(5,8,3),(6,9,4),(12,9,8))
M=100000;SCALE=10**24
partial_units=0
for k,a,b in BASE:
 numerator=a*k-13*b
 for t in range(1,M+1):
  partial_units+=(SCALE*numerator)//((a*t+b)*(13*t+k))
lo=F(partial_units,SCALE)+sum(F(a*k-13*b,a*(13*M+13+k)) for k,a,b in BASE)
hi=F(partial_units+len(BASE)*M,SCALE)+sum(F(a*k-13*b,13*a*M) for k,a,b in BASE)
assert lo<hi
# Published finite carry-profile enclosure, used without altering its file.
gamma=F(json.loads((ROOT/'results/zeta2_proof_strategy/rate_certificate.json').read_text())['gamma_lower'])
c_upper=25-gamma-F(233,120)
analytic=json.loads((ROOT/'work/zeta2_completion/analytic/analytic_certificates.json').read_text())
a_upper=F('38.168732909647');minus_b_lower=F('24.467842131921')
assert F(analytic['scaled_coefficient_exponent_upper_enclosure']['upper'])<a_upper
assert -F(analytic['scaled_error_exponent_upper_enclosure']['upper'])>minus_b_lower
sigma=a_upper+c_upper-lo
tau=minus_b_lower-c_upper+lo
mu_upper=1+sigma/tau
assert mu_upper<F('4.589897')
assert c_upper-lo<F('10.821223')
readable_sigma=F('48.989956');readable_tau=F('13.646619')
readable_mu=1+readable_sigma/readable_tau
assert readable_mu==F(62636575,13646619)
assert readable_mu<F('4.589897')
result=dict(status='NUMERICAL_CANDIDATE',series_terms_per_shell=M,rounding_scale=SCALE,
 shell_triples=BASE,partial_floor_sum_units=partial_units,density_lower=str(lo),density_upper=str(hi),
 density_lower_decimal=float(lo),density_upper_decimal=float(hi),enclosure_width=float(hi-lo),
 gamma_lower=str(gamma),old_arithmetic_c_upper=str(c_upper),new_arithmetic_c_upper=str(c_upper-lo),
 a_upper=str(a_upper),minus_b_lower=str(minus_b_lower),sigma_upper=str(sigma),tau_lower=str(tau),
 conditional_mu_upper=str(mu_upper),conditional_mu_decimal=float(mu_upper),target='4.589897',
 readable_arithmetic_c_upper='10.821223',readable_sigma_upper=str(readable_sigma),
 readable_tau_lower=str(readable_tau),readable_mu_upper=str(readable_mu),readable_mu_decimal=float(readable_mu),
 inequalities_verified=True,
 scope='Exact series enclosure and rational implication. Conditional on uniform lifted-shell integer normalization and analytic hypotheses; finite endpoint tests do not establish these hypotheses.')
(OUT/'lift_density_certificate.json').write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if k not in ('sigma_upper','tau_lower','conditional_mu_upper')},indent=2))
