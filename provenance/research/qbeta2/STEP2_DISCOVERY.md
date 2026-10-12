# Step-two poles: a promising q-beta(2) proof candidate

2026-10-11. Discovery note; independent agents are auditing each all-index ingredient. The step-four report's negative quantitative result must not be transferred to this altered construction.

## Construction

For p>=2, q=1/p, let

    B = sum_(n>=1) n q^n/(1+q^(2n)),
    L(f)=sum_(m>=1)chi_4(m) theta f(q^m),
    D_K(x)=prod_(a=1)^K(1-p^(-2a)x),
    Delta_K(X)=det[L_X(x^(i+j)/D_K)]_(0<=i,j<K).

The finite data are

    S_(2a)=sum_(b=1)^(2a)chi_4(b) g_2(q^b),
    L_X(1/(1-p^(-2a)x))=(-1)^a(X-S_(2a)),
    L_X(x^j)=j p^j/(1+p^(2j)), j>=1; L_X(1)=0.

The alternating X coefficient is essential. The step-four proof's common-term interpolation does not apply, but a direct valuation bound replaces it.

## All-index p-content lower bound (independent audit requested)

Let r_a=p^(2a), F=prod_a(x-r_a), A=K(K+1)/2 and U=X-Z, where p-adically

    Z=sum_(b>=1)chi_4(b)g_2(p^b),
    H(t)=sum_(j>=1) [j p^j/(1+p^(2j))] t^j.

Eulerian reciprocity gives

    S_(2a)=Z-(-1)^a H(r_a).

Thus the monic-F moments have the form

    M_k=L_X(x^k/F)
       =-U sum_a (-1)^a r_a^(k-1)/F'(r_a) + R_k,

where R_k is integral at every prime dividing p. Indeed H begins at degree one, so its divided differences involve only nonnegative powers and are complete homogeneous symmetric functions of the p-integral nodes; polynomial quotient moments are also integral.

For a prime ell|p, normalized by v_ell(p), the displayed summand has valuation

    2a(k-1)-[a(a-1)+2a(K-a)]
       =a^2+(2k-2K-1)a.

Taking its minimum over 1<=a<=K gives

    v_ell(M_k)/v_ell(p) >= -w_K(k),
    w_K(k)=(K-k)_+((K-k)_++1).

(The bound is coefficientwise in U and hence in X because Z is integral.) The sequence -w_K(k) is concave. Rearrangement therefore gives, for every permutation pi,

    sum_i -w_K(i+pi(i)) >= sum_i -w_K(2i).

The determinant expansion consequently gives coefficientwise divisibility

    p^(c_K) divides Delta_K(X) p-integrally,
    c_K=K^2(K+1)-sum_(i=0)^(K-1)(K-2i)_+((K-2i)_++1)
       =(5/6)K^3+O(K^2).

This bound is weaker than observed primitive content but is enough if the independent cyclotomic estimate is correct.

## Quantitative assembly under audit

The independent arithmetic agent reports a complete cyclotomic coefficient-clearer with

    log C_K(p) = [1/6+5281/(675pi^2)+o(1)] K^3 log p,

whose constant is approximately .9593735864. The functional's support is the odd geometric lattice, so the double-zero basis gives

    log|Delta_K(B)| <= -(1/3)K^3 log p+O_p(K^2).

Consequently the integer polynomials P_K=C_K(p)p^(-c_K)Delta_K would obey

    log|P_K(B)| <= [-delta+o(1)]K^3 log p,
    delta =1-5281/(675pi^2) = .2072930802... >0.

The same nested-pole interpolation proof as in the source applies to p^2,p^4,... and to this fixed character functional. Its Cauchy transform has genuine double poles at every odd support node. It therefore supplies infinitely many nonzero actual determinants. If all three independent audits confirm these ingredients, the usual rationality contradiction proves the candidate assertion B notin Q for every integer p>=2.

This assertion concerns the q-series B, not ordinary Catalan's constant. No q->1 irrationality transfer is claimed.

## Certified finite values

`step2.py` constructs exact rational moment data. `step2_scan.py` computes the primitive integer polynomial and uses the rigorous Arb enclosure from `scan.py`. `step2_scan.jsonl` records all enclosures and precision settings.

| K | log absolute primitive value | certified nonzero |
|---:|---:|:---:|
|2|-1.7152624685|yes|
|4|-4.1350833283|yes|
|8|-67.9646564325|yes|
|12|-257.9801542461|yes|
|16|-636.6412787209|yes|
|24|-2311.8428552708|yes|
|32|-5626.6550214982|yes|
|48|-19520.4761172934|yes|

At K48 the primitive value is enclosed near 2.31706456337800408658276*10^(-8478). These finite checks are corroboration only; they do not replace any all-index proof.
