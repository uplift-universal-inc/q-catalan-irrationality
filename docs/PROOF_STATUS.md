# Proof and verification status

Assessment date: 12 October 2026 (UTC).

The main irrationality theorem now has a **complete Lean proof**, using the conservative arithmetic variant documented below. The full project build passed; all 16 inspected declarations, including the three public irrationality theorems, depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom axiom, or unproved approximation hypothesis is used. The sharper denominator estimate in the main manuscript remains a separate written result. External acceptance and comprehensive novelty certification remain separate matters.

The public pen name is **uplift-universal**. The original Open Problems research-project attribution and source snapshots are preserved in `provenance/`; the byline update does not rewrite their history.

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

## Dedicated Lean development

The formal target is

```lean
∀ p : ℕ, 2 ≤ p → Irrational (QCatalan.xi p)
```

`xi` is the actual series `∑' n : ℕ, (n+1) * p^(n+1) / (p^(2*(n+1))+1)`, with real coercions. `QCatalan.hasSum_xi` proves its convergence and intended value; the theorem is not intended to rely on the default value of a nonsummable `tsum`.

### Exact difference from the sharp written normalization

The original definitions `E`, `CK`, and `PK` remain intact. The implementation's conservative definitions are `rawE`, `rawCK`, and `rawPK`. Put

`R(K,h) = Σ_{a≥1, a odd} max(K−ah,0)`.

The odd and twice-odd exponent formulas are unchanged. For a positive integer `u`, the fourth class is replaced by

`rawE(K,4u) = R(K,2u) + max(K−u−1,0)`.

This directly clears the proper cluster terms with integer row weights `max(floor(m/2)−j,0)` and column weights `max(floor((m−1)/2)−j,0)`, whose exact total is `floor(m²/4)`. The polynomial quotient is retained, including its rank contribution `max(K−u−1,0)`. The formal route does not assert the paper's sharper double-zero residue cancellation or the exact asymptotic cost `1/6+1309/(150π²)`.

A finite periodic sieve using the prime factors 2, 3, 5, and 7, together with the proved finite odd reciprocal-square bound `89/72`, gives the sufficient cubic upper bound

`115552/99225 < 7/6`, with exact remaining margin `421/198450 > 0`.

The real bound may use the weaker prefactor `K! [6(2K−1)]^K`; this changes only a term of order `K log K`, while preserving the exact exponent `bK`. The target, determinant, base-prime content, and infinite nonvanishing statement are unchanged.

### Source-to-Lean mapping

Names are in namespace `QCatalan` unless indicated. The following components are integrated into the checked main theorem.

| Source assertion | Formal declarations or modules | Relationship |
|---|---|---|
| Target convergence and reciprocal normalization | `hasSum_xi`, `hasSum_reciprocal` in `Series.lean` | Actual positive series |
| Signed monomial and simple-pole moments | `hasSum_monomial`, `hasSum_simplePole`, `hasSum_fraction_DK` | Includes the quotient and finite signed tails |
| Actual Gram determinant equals the formal polynomial at the target | `gram_det_eq` in `GramIdentity.lean` | Connects the analytic functional with `Delta` |
| Degree K and exact leading coefficient | `natDegree_Delta`, `leading_coeff` | Same polynomial as the manuscript |
| Content at every prime dividing p | `content_coeff` in `Content.lean` | Includes composite bases; direct integral residue bounds |
| Exact content and analytic exponents | `cK_exact`, `aj_exact`, `bK_exact`, `cK_add_bK_exact` | Proves the full `7/6` cubic budget |
| Convex permutation bound in the content calculation | `sum_weight_perm_le_diag` | Equivalent midpoint-convexity proof |
| Conservative local cyclotomic clearing | `RawCyclotomicWeights`, `RawEvenCyclotomic`, odd-order local modules | Uses `rawE`, not the original sharper fourth class |
| Finite denominator growth | `RawTotientSieve`, `OddReciprocals`, `RawRamp`, `RawOddGrowth`, `RawClusterGrowth`, `RawGrowth` | Explicit all-index error bounds; no asymptotic totient input |
| Double-root analytic estimate | `doubleRootGram_det_bound` and the Gram identification | Allows the weaker subcubic prefactor stated above |
| Genuine signed double poles and nonrational Cauchy transform | `cauchySeries_double_pole`, `cauchySeries_nonrational` | At every odd support point; no positivity assumption |
| Infinitely many nonzero actual determinants | `frequently_ne_zero` in `Nonvanishing.lean` | Actual `Delta` evaluated at `xi` |
| Final irrationality criterion | `QZeta3.irrational_of_poly_approx` | General integer-polynomial criterion; Main discharges every hypothesis |
| Final concrete q-Catalan theorem | `irrational_xi`, `irrational_qCatalan`, `irrational_qBeta_two` in `Main.lean` | **Full build and transitive axiom audit passed** |

### Verified release

Run `cd lean && bash scripts/audit.sh` after installing the pinned toolchain and Mathlib cache. This builds the full library, rejects placeholder and unsafe proof tokens in delivered sources, checks all 16 fresh transitive axiom reports, and compiles explicit composite-base examples at p=4 and p=6. The final theorem has only the stated hypothesis `2 ≤ p`. See [the audit output](../lean/blueprint/axioms.txt) and [independent statement audit](../lean/blueprint/audit-notes.md).

External mathematical review and a dedicated priority investigation remain separate from formal verification. The mixed q-beta linear-independence statement and sharper companion estimates are not implied by the pure theorem's formalization.
