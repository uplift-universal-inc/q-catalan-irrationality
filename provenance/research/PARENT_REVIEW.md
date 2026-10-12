# Parent reconstruction and scope review

11 October 2026. This records actual independent derivations, not an
upgrade to repository VERIFIED status.

## Step-two q-beta candidate

I independently reconstructed the pure moment identity by shifting the
character through 2a. The resulting coefficient of the placeholder is
(-1)^a on both target and tail, rather than a common residue. This explains
why the step-four p-content theorem cannot simply be reused.

In the monic denominator basis, the summand is y_a^(k-1)/F'(y_a), including
the exponent minus one. Its valuation divided by v_ell(p) is
a^2+(2k-2K-1)a. Minimizing gives -(K-k)_+((K-k)_++1), and the concavity
exchange on a pair of crossed assignments shows that the identity
permutation gives the worst total. This yields the stated exact c_K.

For the cyclotomic cost I rederived the three contributions. The unsaved
odd range below K gives 1/12+10/(3 pi^2); singleton tails between K and
2K add 8/(3 pi^2). The orders 2h with h odd add 1/12. The orders 4u add

    (16/pi^2) [int_0^(1/5) x dx
       +int_(1/5)^(1/4) x(2-5x) dx
       +int_(1/4)^1 x(1-x) dx] = 409/(150 pi^2).

The total is 1/6+1309/(150 pi^2), strictly below 7/6. The optional low-odd
saving was independently integrated as 1219/(1350 pi^2), reproducing the
sharper cost; it is unnecessary for the main candidate.

I also checked the formal interpolation argument. A Taylor coefficient
of the finite tail is polynomial in its endpoint N of degree at most r+1.
In tau times the series, substitution N=log(x/rho)/tau gives only
nonnegative powers of tau, with finitely many contributions to every
two-variable coefficient. The constant term is the stated Fourier sum
primitive, whose double zero at rho bounds the proper residue rank.
The polynomial quotient's radical is a separate argument and must be
added; it cannot be discarded. Original exact denominators are monic
cyclotomic factors and powers of z, so local divisibility implies integer
Laurent coefficient clearing by monic polynomial division.

For nonvanishing I rechecked the degree bound in the consecutive-size
cross polynomial. Each interpolation error is O(1/z), making the cross
polynomial have degree at most n-1 despite its initially larger algebraic
expression. Its n exterior zeros force it to vanish. Eventual singularity
would then force a fixed nonzero error at infinity and bounded-degree
polynomial multipliers with unboundedly many exterior zeros. No positivity
or assertion about a finite determinant sign is required.

The normalized polynomials have degree K and genuinely integer
coefficients. Thus multiplication by a hypothetical fixed rational target's
denominator to the Kth power costs only O(K) in the logarithm, while the
negative term has size K^3. The contradiction is correctly scaled.

## Mixed beta(1)/beta(2) extension

I reconstructed the reciprocal g_0 identity, including the finite
character sum (1-epsilon)/2. Its common residue correction is -A/2;
after monic partial fractions it contributes -A/(2F_K(0)) at M_0, which
is not integral but exactly fits the existing worst entry bound. Taking
A even is legitimate after scaling any proposed rational relation.

At d=4u, the beta(1) residue is a local primitive of the Fourier sum,
with a simple zero at the collision center. The beta(2) residue retains
its double zero. Therefore the mixed proper residue rank bound is K-2u,
and the polynomial part still costs at most K-u-1. Integrating the capped
sum gives 82/(27 pi^2), hence the total 1/6+244/(27 pi^2)<7/6.
This supplies the changed arithmetic ingredient, rather than assuming
that the pure beta(2) cost remains unchanged.

The independent analytic challenge is documented in
qbeta2-audit/MIXTURE_FINAL_AUDIT.md. In particular, early-node terms of
f(q^m)-f(0) do not vanish; they are controlled using bounded partial sums
of the character. The mixed theorem is a separate candidate with this
additional argument, not an automatic consequence of individual
irrationality.

## Other attempts

I independently derived the Euler--Gompertz reciprocal-factorial leading
coefficient for the K=2n positive determinant, including its superfactorial
normalization obstruction. The other agent extended the lower-bound
argument uniformly to K>=n; that broader proof is recorded separately.

For conductor three I independently derived all three starting moments:
M00=(5/4)L(2,chi_-3), M10=(2/3)(1+log(2/3)), and
M01=(zeta(2)+2Li2(1/3))/4. A second derivation found the additional log3
direction at M20, which I also recovered by integration by parts. Thus
the initial three-period guess was too small. The resulting obstruction
is retained rather than silently treating the new seed as pure.

The beta4 dyadic smoothing proposal is explicitly provisional and has not
received this parent's full all-index audit. Its finite checks do not
establish its asymptotic theorem or an irrationality conclusion.

