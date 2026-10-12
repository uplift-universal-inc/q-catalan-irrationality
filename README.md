# Irrationality of the q-Catalan value β₁/ₚ(2)

A focused research manuscript and reproducibility package for the claim that, for every integer **p ≥ 2**,

\[
\beta_{1/p}(2)=\sum_{n=1}^{\infty}\frac{n p^n}{p^{2n}+1}
\]

is irrational. This is Jouhet–Mosaki's Lambert-series normalization of the q-beta value; it is different from combinatorial q-Catalan numbers.

**Public byline:** uplift-universal.

**Status:** complete Lean proof of the irrationality theorem for every integer p ≥ 2. The full project build and final theorem axiom audit passed. The proof uses the conservative cyclotomic variant described below. The manuscript’s sharper denominator estimate is kept separate. This AI-assisted project makes no claim of external peer review or certified priority.

## Read the result

- [Lean proof and build guide](lean/README.md) · [Main theorem](lean/QCatalan/Main.lean)
- [Paper (PDF)](paper/main.pdf) · [LaTeX source](paper/main.tex)
- [Proof and verification status](docs/PROOF_STATUS.md)
- [Attribution and historical context](docs/ATTRIBUTION.md)
- [Companion results for later papers](docs/FUTURE_RESULTS.md)
- [Original research notes](provenance/research/qbeta2/PROOF_CANDIDATE.md) · [Source manifest](provenance/source-manifest.json)
- [Analytic review](reviews/analysis.md) · [Arithmetic review](reviews/arithmetic.md)

## What makes the argument work

A signed Euler-derivative functional yields determinant polynomials of exact degree K. The proof controls all coefficients, including the polynomial-quotient contribution.

| Ingredient | Cubic exponent, in units of K³ log p |
|---|---:|
| Real determinant decay | 1/3 |
| Common content at primes dividing p | 5/6 |
| Cyclotomic denominator cost | C = 1/6 + 1309/(150π²) |
| Remaining decay | δ = 1 − 1309/(150π²) > 41/1350 |

At roots of unity of order divisible by four, a residue interpolant has a double zero. This limits the singular rank and makes the denominator cost small enough. A rational-interpolation argument proves infinitely many nonzero determinant values without positivity.

The integer polynomials satisfy `log |P_K(β₁/ₚ(2))| ≤ (−δ + o(1)) K³ log p`, with infinitely many nonzero values. A rational target of denominator b would make `b^K P_K` a nonzero integer tending to zero, which is impossible. See the paper for all-index proofs.

## Lean formalization

The Lean proof uses the same target, signed functional, determinant polynomials, real decay, common base-prime content, and nonvanishing argument. At orders divisible by four it uses a direct, more conservative pole bound. A finite sieve at the primes 2, 3, 5, and 7 proves the sufficient cubic denominator cost

\[
C_{\mathrm{Lean}}=\frac{115552}{99225},\qquad
\frac76-C_{\mathrm{Lean}}=\frac{421}{198450}>0.
\]

The formal polynomials are named `rawPK`; the paper’s original sharper polynomials remain named `PK`. The final theorem has only the hypothesis `2 ≤ p`. The [formal proof guide](lean/README.md) maps the mathematical steps to their declarations and distinguishes the two normalizations.

Requires Lean and Mathlib v4.34.1, pinned in the project:

```sh
cd lean
lake exe cache get
lake build
bash scripts/audit.sh
```

## Reproduce the finite checks

Requires Python 3.10+ and `python-flint==0.9.0`. A TeX installation with `pdflatex`, standard AMS packages, `lmodern`, `microtype`, and `fancyhdr` builds the paper.

```sh
python -m pip install -r requirements.txt
make verify
make verify-large
make paper
```

`make verify` performs:

- 100 exact degree, leading-coefficient, and conservative integer-normalization cases: p = 2,3,4,5,6; K = 1,…,20.
- 40 independently reconstructed content cases using Python `Fraction`: p = 2,3,4,6; K = 1,…,10.
- 144 direct functional-entry comparisons, 36 exact determinant evaluations, and 12 nonzero primitive-polynomial enclosures.
- Verification of the hashes of all 29 recovered source blobs.

`make verify-large` also replays p = 2, K = 48, yielding a rigorously nonzero primitive-polynomial interval centered at approximately `2.31706456337800408658 × 10^−8478`. It uses 155,413-bit ball arithmetic and 155,605 target-series terms. Its primitive normalization differs from the safe normalization used in the theorem.

Results are in [certificates](certificates). Finite checks corroborate formulas and implementations; they do not prove the infinite theorem. The finite-check workflow remains separate from the Lean build and axiom-audit workflow. Local build results are recorded in the formal proof guide; no remote CI run is claimed.

## Scope

The paper covers every integer p ≥ 2, including composite bases. It does not prove arbitrary rational-q cases, transcendence, every even q-beta value, an effective irrationality measure, or any new statement about classical Catalan's constant. The classical result and recent reports about it are discussed with precise attribution in the introduction.

The mixed result for `1, β₁/ₚ(1), β₁/ₚ(2)` and a stronger denominator saving are preserved as companion research notes, with their own status, in the [future-results inventory](docs/FUTURE_RESULTS.md). The related [q-zeta(3) repository](https://github.com/uplift-universal-inc/qzeta3-irrationality) is a separate project.

The public byline is the user-selected alias uplift-universal; the preceding research-project attribution is preserved in the provenance. Original notes, editorial work, finite verification, internal review, and established literature are distinguished in [ATTRIBUTION.md](docs/ATTRIBUTION.md). No individual human authorship is inferred.
