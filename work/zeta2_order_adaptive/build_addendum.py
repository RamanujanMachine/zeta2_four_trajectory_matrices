"""Assemble the order-search report and uniform periodic-divisor addendum."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'results/zeta2_order_adaptive'
OUT.mkdir(exist_ok=True)

intro=r'''\documentclass[11pt]{article}
\usepackage[margin=24mm]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern,amsmath,amssymb,amsthm,mathtools,booktabs,microtype,hyperref}
\hypersetup{colorlinks=true,linkcolor=blue!50!black,urlcolor=blue!50!black}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\newcommand{\Z}{\mathbb Z}
\newcommand{\Q}{\mathbb Q}
\newcommand{\Fp}{\mathbb F_p}
\newcommand{\lcm}{\operatorname{lcm}}
\allowdisplaybreaks
\setlength{\emergencystretch}{2em}
\title{Adaptive CMF multiplication orders and a stronger arithmetic divisor\\
\large An addendum for the direction $(10,9,11,-11;2,1,3)$}
\author{Exact path experiments and a uniform arithmetic extension}
\date{10 October 2026}
\begin{document}
\maketitle

\begin{abstract}
We test literal changes of native CMF path, independently for each prime
and each prescribed initial row. Prime-dependent path selection strictly
improves finite divisibility certificates. Different rows can have
incompatible maximizing paths and a strictly better path-only divisor;
after adjoining the previous arithmetic normalization, separate row
choices give no further common-divisor gain in the tested families.
The residual prime pattern leads to a uniform extension of the previous
six-interval arithmetic lemma to all integer translates of its carry
chambers. Combined with the previously established analytic estimates,
the extension gives
$\mu(\zeta(2))\le62636575/13646619<4.589897$.
The path experiments and the uniform readout argument are distinguished
throughout: the new measure bound is not attributed to an unproved
row-dependent ordering rule.
\end{abstract}

\section{What was tested, and what improved}
The CMF is the native $\mathrm{pFq}(4,3,1)$ field, with
\[
w_0=(1,1,1,0;1,1,1),\quad v=(10,9,11,-11;2,1,3),\quad
R=\begin{pmatrix}0&2&-1\\2&0&0\end{pmatrix}.
\]
Write $W_N=W(w_0,w_0+Nv)$ and
$(p_N^{\rm raw},q_N^{\rm raw})^T=RW_Ne_0$.
Conservation identifies admissible paths with the same endpoint.
It does not permit unshifted matrices to be commuted.

For each cut vertex $w$, compute the complete native products
$A_w=W(w_0,w)$ and $B_w=W(w,w_0+Nv)$, and verify all nine entries
of $A_wB_w=W_N$ exactly. At this cut the certificate for initial row
$r$ and prime $p$ is
\[
b_{p,r}(w)=\min_{0\le i\le2}
 v_p\bigl((RA_w)_{r,i}(B_w)_{i,0}\bigr).
\]
It bounds the valuation of the endpoint scalar, since it bounds every
term in the three-term sum. Entire blocks are evaluated before taking
this minimum. The suffix always retains at least $2N$ negative-upper
moves; a cut immediately before the endpoint is excluded.

The two optimizations compared are
\[
 \max_w\min_r b_{p,r}(w),\qquad
 \min_r\max_w b_{p,r}(w).
\]
The first uses one path at each prime for both rows. The second also
allows a different path for each row. They can differ strictly, as the
example below shows. After adjoining the previous arithmetic certificate,
the resulting common-divisor bounds agree in these tests. This is a
finding about the tested certificates, not a general CMF theorem.

We used 89 structured cuts at each of
$N=20,40,80,160,320,640$, and 240 seeded random cuts at each of
$N=20,40,80,160,320,640,1280$. The random cuts also vary the progress
of the three lower parameters separately. All arithmetic in these
certificates is exact rational arithmetic. The 89-path search found
strict gains from prime-dependent selection. Beyond the previous
arithmetic normalization, the extra gain factor from row-dependent
selection was one at every tested depth. The random family gave the
same conclusion about that additional gain.

\subsection{A literal prime-dependent order witness}
At $N=80$, let path $A$ first increase each of $x_0,x_1,x_2$ by
$3N$, in that order; it then completes the remaining positive-upper
moves, the lower moves, and the negative-upper moves.
Path $B$ uses $4N$ instead of $3N$ for that initial block.
The cut is taken after the initial block. These are different
multiplication orders, since the remaining $x_0$ moves are performed
after some $x_1,x_2$ moves, with a different split in the two paths.
The suffix has all $11N$ negative-upper moves.
Their common-row valuation certificates are
\[
\begin{array}{c|rr}
 &p=2&p=59\\\hline
A&-19&-3\\
B&-25&-2
\end{array}
\]
Use $A$ at 2 and $B$ at 59. In the full 89-path search the sets of
maximizers at these two primes are disjoint. Thus this benefit is not
an artifact of choosing different names for tied optimal paths.
At $N=80$, prime adaptation improves the common factor over the best
single fixed path (after including the previous arithmetic bound)
by the factor $147649788$.

\subsection{A strict row-dependent order improvement}
At $N=40,p=491$, compare the cuts
\[
 w_A=w_0+N(3,3,3,-3;0,0,0),\qquad
 w_B=w_0+N(3,3,3,0;0,0,0).
\]
The first moves $3N$ negative-upper steps before completing the remaining
positive-upper and lower moves; the second postpones all negative-upper
moves until after those moves. Their certificates are
\[
\begin{array}{c|rr}
 &\text{numerator row}&\text{denominator row}\\\hline
A&-1&-2\\
B&-2&0
\end{array}
\]
In the entire 89-path family, the best common-path minimum is $-2$.
Choosing $A$ for the numerator and $B$ for the denominator gives $-1$.
Thus independent row choices improve the path-only common-divisor
certificate by a factor of $491$. The earlier arithmetic normalization
already certifies valuation $-1$ at this prime, so this gain does not
improve that normalization further.

For a second illustration, at $N=80,p=883$, a path with cut
\[
w=w_0+N(6,6,6,-9;2,1,3)
\]
has row certificates $(-2,-2)$, whereas the $3N$ initial-upper
path above has $(-3,0)$. The first better certifies the numerator
row, the second the denominator row. The sets of row maximizers in
the 89-path family are disjoint. Nevertheless the common minimum
remains $-2$: row adaptation adds no common factor in this example.
The numerator remains the limiting row in the aggregate experiments.

\subsection{Finite gains against the previous six-interval bound}
Each certificate is combined prime by prime with the earlier
normalization. The following are natural logarithms of upper bounds
on the \emph{reduced} denominator; the actual reduced denominator is
computed independently from the endpoint rational number.
\begin{center}
\begin{tabular}{rrrr}
\toprule
$N$&Previous bound&89-path bound&Actual $\log q_N$\\\midrule
'''

rows=[]
for N in (20,40,80,160,320,640):
    d=json.loads((HERE/f'orders/summary_{N}.json').read_text())
    rows.append(f"{N}&{d['baseline_log_q_bound']:.6f}&{d['improved_log_q_bound']:.6f}&{d['actual_reduced_log_q']:.6f}\\\\")

bridge=r'''
\bottomrule
\end{tabular}
\end{center}
These finite gains include primes omitted by the cutoff $p^2>50N$;
that part contributes no exponential-rate improvement. It must not be
extrapolated as a constant saving per depth. The next section isolates
a uniform additional divisor among the eligible larger primes.

There is an important distinction: at $N=320,640$, every newly explained
large-prime factor is already exposed by the \emph{single} cut after all
positive-upper and lower moves, before the entire negative-upper block.
Different prime-dependent paths improve other finite factors, but the
new asymptotic divisor below does not require changing the path by prime.
It is therefore not evidence that adaptive orders are necessary for the
stronger irrationality measure.

\section{The uniform arithmetic extension}
This is an addendum to the supplied full manuscript
\emph{CMF conservation as an arithmetic tool}, saved as
\texttt{zeta2\_complete\_proof.tex} in the accompanying bundle.
We use its exact native readout, baseline normalization, eight-cell
signature table, and local-kernel lemma. Those statements include the
initial conditions and all native generator identities. The following
argument proves the extension needed here; it does not infer it from
the finite path tests.
'''

tail=r'''
\section{Reproducibility and limits of the search}
The bundle includes the previous complete derivation, the present
addendum, all new search programs, exact checkpoints, the translated
kernel checks, and the rational density certificate. It also records
the eight-depth prime-pattern checks for all three output columns.
The pattern checks are numerical discovery evidence; the translated
finite-field argument above supplies the all-depth statement.

The requested new attachment
\texttt{zeta2\_cmf\_matrix\_proof (4).tex} was an empty file on disk.
The previous nonempty attachment was inspected as background. No
claim is made about the contents of the empty file.

The search changes arithmetic descriptions of the same endpoint,
so it cannot change the exact reduced approximants or their actual
delta values. No new delta search was performed. The previous values
were $\delta_{3000}=0.278673337629$,
$\delta_{4000}=0.279047437501$,
$\delta_{6000}=0.278946586656$, with last-three-depth slope estimate
$0.279152068816$. These numerical scores are separate from the
irrationality-measure conclusion proved using upper bounds.

No extra common-divisor benefit from independent row choice \emph{beyond
the previous arithmetic normalization} has been found in the tested
families. That remains a target for a richer lattice or residue
certificate. The precise next region is: keep the
same field, start, and direction; test $N=640,1280,2560$; retain at
least $2N$ negative-upper suffix moves; refine cut coordinates in
quarter-$N$ increments and allow one or two leading $p$-adic residue
digits. Examine primes outside the periodic divisor with $p^2>50N$.
At $N=6000$, remaining eligible residual primes include 1583 in all
three columns and 11743 in column 0. A new uniform rule is needed
before either can affect the stated measure bound.
\end{document}
'''

proof=(HERE/'arithmetic/periodic_lift_proof.tex').read_text()
density=(HERE/'ceiling/lift_density_and_audit.tex').read_text()
density=density[density.index('\\paragraph{Density of the lifted prime intervals.}'):]
rate=(HERE/'ceiling/rate_consequence.tex').read_text().replace('\\widetilde H_{N,r}', 'H^*_{N,r}')
(OUT/'zeta2_adaptive_orders_addendum.tex').write_text(intro+'\n'.join(rows)+bridge+proof+'\\section{The improved rate}\n'+density+rate+tail)
print(OUT/'zeta2_adaptive_orders_addendum.tex')
