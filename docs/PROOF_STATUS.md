# Proof and verification status

Assessment date: 12 October 2026 (UTC).

The mathematical claim is a **complete written proof candidate with internal mathematical review**. No external acceptance, comprehensive novelty certification, or complete formal proof is claimed. The manuscript states the theorem and gives the all-index argument; these status descriptions concern the evidence and review process.

## Frozen theorem

For each integer p ≥ 2, including composite integers, the real number

`β₁/ₚ(2) = Σ_{n≥1} n p^n/(p^(2n)+1)`

is irrational. The result uses precisely this normalization and only positive reciprocal integers.

## Proof dependency map

| Paper statement | Source obligation | Review and disposition |
|---|---|---|
| Proposition 2.1 | Formal moment identity and exact leading coefficient `(-1)^K p^(K(K²−1))` | Independently reconstructed in both bounded reviews; retained unchanged |
| Proposition 3.1 | Coefficientwise content `c_K = [10K³+3K²−10K−3(K mod2)]/12` | Arithmetic review verifies the local translation, integral remainder, concavity argument, and composite bases |
| Proposition 4.1 | Complete cyclotomic clearer, including polynomial quotients and orders 4u | Arithmetic review verifies all congruence classes, formal interpolation, double zero, residue rank, and global monic cancellation |
| Proposition 5.1 | Cost `C=1/6+1309/(150π²)` and integer normalization | Both bounded reviews reconstruct the cost; arithmetic review checks integrality |
| Proposition 6.1 | All-size real bound and cubic exponent 1/3 | Analytic review checks the double-root basis, constants, and Hadamard bound |
| Proposition 7.1 | Infinitely many nonzero actual determinants | Analytic review checks all degrees, common kernel zeros, transform domain, and eventual-singularity contradiction |
| Theorem 1.1 | Integer contradiction with degree K and positive margin | Both reviews check the assembly; fresh final reader checks the canonical manuscript |

The manuscript does not assume that every determinant is nonzero, use positivity of the signed functional, discard the polynomial quotient, or infer an all-index conclusion from finite computations.

## Review records and corrections

- [Analytic review](../reviews/analysis.md): no blocker. QC-AN-001 requested a precise continuation domain and locally uniform convergence, with geometric expansions restricted to exterior regions. Section 7 incorporates it.
- [Arithmetic review](../reviews/arithmetic.md): no blocker in the conservative construction. It independently derives the proof's arithmetic dependencies and records its own bounded formula checks.
- [Final linear-reader review](../reviews/final-reader.md): no blocker in the complete canonical TeX. A missing multiplication space in the entry valuation was corrected before its final fingerprints were recorded.
- [Editorial and rendering record](../reviews/editorial-release.md): source identities, scope of corrections, build, and visual checks.

The first analytic review read an earlier export of the candidate with one additional trailing newline; the mathematical text is identical to the commit-pinned source. The byte-verified source has Git blob `8f944b8d7555814a0ab7dabc4edec25a7ea581fe`. See the [source manifest](../provenance/source-manifest.json) for exact hashes. Reviewer reports explicitly limited their independent source-authentication scope; the manifest supplies the subsequent editorial byte verification.

## Computational evidence replayed in this preparation

| Check | Exact scope | Result |
|---|---|---|
| Conservative coefficient normalization | p=2,3,4,5,6; K=1,…,20 | 100 passed |
| Independent `Fraction` reconstruction and prime-by-prime content | p=2,3,4,6; K=1,…,10 | 40 passed |
| Direct derivative functional versus affine moments | p=2,3,4,6; K=1,…,6; all matrix moment indices | 144 interval overlaps |
| Determinant versus polynomial evaluation | 12 selected cases, X=0,1,2/3 | 36 exact equalities |
| Primitive-polynomial nonzero enclosures | 12 selected cases in functional replay | All intervals exclude zero |
| Large primitive-polynomial enclosure | p=2, K=48 | Nonzero interval reproduced at 155,413 bits |
| Source fingerprints | 29 commit-pinned blobs, plus auxiliary export hashes | All matched |

The direct functional checks use a separate positive-series target and a derivative-series enclosure. The high-precision check instead uses exact divisor coefficients `σ(n)=Σ_{d|n}d χ(n/d)`, with `|σ(n)|≤n²` and an explicit geometric-ratio tail. Both use Arb outward-rounded balls through python-flint. No floating-point sign is treated as a proof.

The `K=48` polynomial is primitive, so its displayed value is not asserted to be the value of the conservative `P_K` used in the proof. Its canonical comma-separated coefficient fingerprint is in [large-enclosure-replay.json](../certificates/large-enclosure-replay.json).

## Formalization and external review

There is no complete Lean formalization of this q-beta theorem in this package. No unrelated q-zeta Lean scaffold is presented as evidence for it. The finite verification workflow is not a proof checker. External mathematical review and a dedicated priority investigation remain separate future work.
