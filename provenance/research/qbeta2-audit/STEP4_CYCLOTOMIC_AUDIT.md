# Independent audit of the step-4 q-beta(2) cyclotomic estimate

11 October 2026. Audited source: `qbeta2/REPORT.md`, constant C=2.512881890003484. This is a mathematical rederivation, not a claim of external publication review or formal verification.

## Verdict

I found no error in the stated local parity cancellation, odd-order savings, even-order rank upper bounds, or the final cubic sum. The bound still exceeds 7/3. It cannot finish the step-4 construction using those estimates.

## The potentially delicate interpolation step

At a primitive even-order dth root omega, write z=omega exp(tau). Within one collision class a=c+kh, the coefficient of tau^r in the finite tail S_(4a) is a polynomial in a of degree <=r+1. This follows from weighted sums of a periodic sequence over an integer number of full periods, plus a fixed residue-class remainder. The relevant period is d for 4|d and 2d when v_2(d)=1.

If P_r(a) denotes that coefficient polynomial, substitute

a=log(x/rho)/(4tau),  rho=omega^(4c).

Then tau sum_(r>=0)tau^r P_r(log(x/rho)/(4tau)) belongs to the formal power-series ring C[[tau,x-rho]]: each monomial has nonnegative tau exponent because deg P_r<=r+1, and total degree at least r+1. Thus the source's integral interpolant is justified as a formal local construction; there is no hidden negative-power series.

When v_2(d)=1, pairing b with b+d changes chi_4's sign and leaves omega^(-b) unchanged. The full-period average vanishes for every coefficient r, reducing the polynomial degree to <=r. The same substitution is integral without the leading tau. Consequently proper-part divided differences and polynomial moments are regular. The zero exponent at these cyclotomic orders is valid.

## Re-derivation of the residue for d=4h

Define

G_1(y)=sum_(b=1)^d chi_4(b)g_1(omega^(-b)y).

The finite character Fourier sum gives G_1(y)=c h y^h/(1+y^(2h)), with nonzero c. The highest-degree coefficient of P_r is proportional to the full-period average of chi_4(b)g_(r+2)(omega^(-b)). Summing these coefficients after the interpolation substitution gives explicitly

H_0(x)=[G_1(1)-G_1(rho/x)]/d.

Because rho^h=1, this is proportional to

1/2-x^h/(1+x^(2h))=(x^h-1)^2/[2(1+x^(2h))].

This independently verifies the asserted double zero at every collision center, including its order and regular denominator. The sign difference from the displayed source expression is an irrelevant nonzero factor.

For a cluster of size m, the residue matrix therefore has zero entries when j+k>m-3. Its final two rows vanish, and rank is at most (m-2)_+. Summing clusters gives (K-2h)_+.

The entire polynomial residue form has a common radical containing degree<=h polynomials because the first singular moment index is h; its rank is <=(K-h-1)_+. All matrix entries have at most simple poles. Thus the total determinant pole order is bounded by

min(K,(K-2h)_++(K-h-1)_+).

This is an upper bound, with no assertion that the two residue ranks are attained or additive in the actual matrix.

## Odd-order and asymptotic checks

At odd d there are no singular polynomial moments. The cluster cost is

f(m)=floor((m+2)^2/4)=2m+sum_(a>=3 odd)(m-a)_+.

If the first pole index a satisfies 4a<d, its tail is analytic. The upper-node final vector leaves only that lower-node contribution, so setting its weight to zero saves exactly (3-m)_+. Counting those clusters yields the source's finite exponent formula.

The limiting savings have three regions: d/K in (4/9,1/2), (1/2,1), and (4/5,1). Direct integration gives 4759/(12150pi^2). The outer odd range K<d<=4K contributes 18/pi^2. These combine into

C_odd=1/12+(64/3-4759/12150)/pi^2.

For the even range, sum_(h<=H)phi(4h)~8H^2/pi^2. Integrating the piecewise rank cap gives

C_even=(16/pi^2)[1/18+11/216+1/12]=82/(27pi^2).

The total is the source's C=2.512881890003484, exceeding 7/3 by 0.179548556670151. None of these estimates establishes asymptotic growth of primitive values.
