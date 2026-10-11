# Audit of the periodic lift of the uniform shell argument

The existing finite-field proof in `work/zeta2_completion/all_shells.tex` extends to the column-corrected periodic lifts. This observation is about the arithmetic readout proof. It is separate from the experiment selecting actual multiplication routes for each row and prime.

Fix an eligible prime p with p²>50N. Write N/p=t+f with t a nonnegative integer and 0≤f<1. Suppose f lies in one of the eight open subregions of the existing chamber table. Its quantities translate as

- a=8t+a₀ and M=11t+M₀;
- b=8N−ap and d=11N−Mp depend only on f;
- the minimum carry h and the support signatures e,δ are unchanged;
- λᵤ=ut+λᵤ,₀ on the minimal-carry support.

The polynomial quotient and local rational kernel are therefore defined exactly as before. Their critical integer becomes

    K=3a−M+h=13t+K₀.

The strict degree condition for column r is

    13N+r < (13t+K₀)p.

Together with the lower fractional endpoint f>B/A of the corresponding original shell, this gives the open prime interval

    (13N+r)/(13t+K₀) < p < AN/(B+At).

The six triples (K₀,A,B) are (2,8,1), (3,9,2), (4,10,3), (5,8,3), (6,9,4), (12,9,8).

## Denominator and endpoint checks

For t≥1, p<N and x=N/p≥1. The cutoff p²>50N gives p>50x. Hence a+δ≤8x+1<p and M≤11x<p; the factorial denominators and the distinct high-digit kernel poles remain units. The same bounds cover the high digits used at the Newton nodes. Values of the integer factors appearing there have absolute value below 24N+r<50N<p².

Choose η=p ceil(2N/p). Then 2N≤η<2N+p≤3N for t≥1, so η is in the admitted interval [2N,9N]. All harmonic indices are below 14N<p². The Newton degree remains at most 13N+r−1<p². Thus the baseline integer-valued interpolation and the substitution s=k+pV continue to justify reduction at derivative nodes.

The special fractional split points f=5/11 or 10/11 would force p=11 and N=11t+5 or 11t+10. They fail p²>50N, so no eligible prime is omitted at an internal split.

The quotient degree is

    deg(X^r Q)=13N+r−(13t+K₀−1)p−1 < p−1.

The complete finite-field sum consequently vanishes. The harmonic and polynomial leading residues factor through that same sum exactly as in the existing argument. This supplies one additional p for each eligible prime in the lifted intervals.

## Scope

This audit supports a uniform extension of the arithmetic divisor, including the necessary column correction r. It does not establish that a particular multiplication route exposes every factor by componentwise valuations alone. That latter question is the separate route-search experiment. It also does not by itself certify a decimal irrationality-measure bound; the periodic integral and the unchanged analytic inputs must be combined independently.
