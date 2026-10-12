# Final independent challenge: renormalized q-beta(1)/q-beta(2) extension

11 October 2026. Source audited: `qbeta-mixture/MIXTURE_EXTENSION.md`. Assigned scope: real decay, the renormalized zeroth-order functional, its Cauchy transform, and moving-denominator nonvanishing. Arithmetic and cyclotomic normalization are reviewed separately by the parent.

## Verdict

I found no analytic or nonvanishing obstruction. The renormalization is necessary and has been handled correctly. In particular the early-node zeroth-order contributions are not zero, but they do not spoil the determinant estimate. The argument also survives the cancellation-sensitive case A+B=0 and the pure zeroth-order case B=0.

Conditional only on the separately audited all-size arithmetic bounds, these analytic ingredients support the claimed Q-linear-independence assembly. This audit is not an assertion of novelty, publication acceptance, or formal verification.

## 1. An explicit uniform entry bound

Put S=|A|+|B|>0. Keep the source's double-root basis B_j, powers a_j, and W_K=1/D_K. The step-two derivative estimate proved in `STEP2_ANALYTIC_NORMALITY.md` gives, at every surviving odd node and throughout the interval from zero to that node,

|theta(B_i B_j W_K)(x)|
 <= exp(4/21)(i+j+8/21)q^(a_i+a_j) x/q^R,

where R is the largest odd root index (R=0 for i=j=0, handled directly). Dividing this by x and integrating proves the same bound for

|(B_i B_j W_K)(x)-(B_i B_j W_K)(0)|.

Before the first surviving odd node, the product and its theta derivative vanish; its renormalized zeroth-order value is therefore minus its value at zero. The sum of the character over that finite initial segment has absolute value <=1. This part contributes at most |A|q^(a_i+a_j).

Summing the surviving odd geometric progression costs at most 4/3. Consequently the complete mixed functional satisfies the explicit bound

|L(B_i B_j/D_K)|
 <=3S(i+j+1)q^(a_i+a_j).

The special i=j=0 entry obeys the same inequality using W_K-1=O(x) and theta W_K=O(x). No constant summand is illegally summed over an infinite tail.

Thus the determinant has the fully explicit all-size bound

|Delta_K(Xi)|
 <=[3S(2K-1)sqrt(K)]^K q^[K(K-1)(2K-1)/6+floor(K/2)].

This yields exactly the claimed cubic analytic exponent -K^3(log p)/3. The coefficients A,B are fixed in each rationality contradiction, so their appearance in the prefactor contributes only O_(A,B)(K log K).

## 2. Cauchy transform and continuity

For a function analytic near [0,q],

|f(q^m)-f(0)|<=q^m sup_[0,q]|f'|.

Hence the renormalized sum is absolutely convergent and continuous under uniform control of first derivatives. The derivative part has the same property. Therefore the geometric Cauchy-kernel expansion and its differentiated version may be passed through L on every exterior domain |z|>=r>q. This supplies the continuity justification needed by the moving-denominator argument.

The exact transform is

F(z)=A sum_m chi(m)[(z-q^m)^(-1)-z^(-1)]
     +B sum_m chi(m)q^m(z-q^m)^(-2).

On compact sets avoiding zero and the odd nodes, every tail summand is O(q^m), so the series is locally normal. At an odd node:

- B!=0 leaves the genuine double-pole coefficient B chi(m)q^m;
- B=0, A!=0 leaves the genuine simple-pole coefficient A chi(m).

The subtraction at zero cannot cancel either principal part. Thus F is nonrational. It is analytic at infinity and O(z^-2). If A+B=0, its first Laurent coefficient vanishes, but the next coefficient is nonzero: mu_2=(A+2B)q^2/(1+q^4)=Bq^2/(1+q^4). This strengthens its vanishing order and causes no difficulty.

## 3. Nonvanishing has no missing correction term

The pointwise identity

FQ-T_n=D_n R_n

is obtained by applying the entire renormalized linear functional to the usual divided-difference identity. Its evaluation-at-zero subtraction is automatically present on both sides. There is no additional uncancelled 1/z term.

Kernel orthogonality includes j=0. Thus even the constant coefficient of the geometric expansion of R_n is annihilated, giving R_n=O(z^(-n-1)) and FQ_n-T_n=O(z^-1). The polynomial T_n still has degree <=n-1 because L acts linearly on its finitely many rational-in-x coefficients.

The exterior interpolation zeros remain p^2,...,p^(2n). The consecutive-size cross polynomial has degree <=n-1 and n distinct zeros, hence vanishes. An eventual singular tail would force a fixed rational T/Q and bounded-degree polynomial multipliers, contradicted by the growing number of exterior zeros. This proof uses only nonrationality and analyticity of F established above; it does not require positivity or a nonzero first Laurent coefficient.

## 4. Independent finite challenge checks

`mixed_check.py` evaluates the actual renormalized functional directly on every matrix entry and compares it with the exact mixed partial-fraction moments. It independently encloses the target through

Xi=sum_(j>=1)(A+Bj)q^j/(1+q^(2j)),

with an absolute tail bound separating |A| and |B|. The direct functional tail is bounded by

2(|A|+|B|)(k+1)q^(N+1)/(1-q)

for the x^k/D_K entry.

All 128 entries in 32 cases passed, using p=2,3; K=1,...,4; and (A,B)=(2,0),(2,-2),(2,3),(-2,1). This includes pure zeroth order, cancellation of the leading Laurent term, and both signs. The checks support the formulas but are not used to infer the all-size statements.

The copied exact moment constructor is in `source/mixed_exact.py`; the direct functional and target-tail evaluators are independent audit code. `mixed_checks.json` records the checks. Both scripts are portable with Python 3 and python-flint.
