# Lean source provenance and reuse

The Lean software in this directory includes infrastructure from
[uplift-universal-inc/qzeta3-irrationality](https://github.com/uplift-universal-inc/qzeta3-irrationality),
at the verified commit
`7ab34f1e5a03482dff08ffe469125cbafd54cb63` (`7ab34f1`), whose commit author and
public project pen name are `uplift-universal-inc`. The source paths are
`lean/QZeta3/` and `lean/LICENSE` at that commit.

The retained `QZeta3/*.lean` files are unmodified copies of the corresponding
tracked Git blobs. Their contents, and the accompanying `LICENSE`, were checked
against that exact revision.

The accompanying `LICENSE` is the upstream Apache License, Version 2.0, preserved
unchanged. This software notice does not grant or change the rights applying to
the manuscript, its historical research records, or external cited sources.
Upstream source comments and attribution within the retained files are
preserved. Lean and mathlib retain their own licenses; their versions are pinned
by `lean-toolchain` and `lake-manifest.json`.

## Scope of the reused infrastructure

The final import closure of `QCatalan.Main` uses 38 upstream `QZeta3` modules.
They provide general polynomial and determinant algebra, local rings and
cyclotomic pole estimates, integer-fraction descent, interpolation and
meromorphic continuation tools, finite sieve estimates, and elementary analytic
bounds. Some complete upstream modules also contain auxiliary declarations about
the original q-zeta construction. Their presence does not substitute that target
for the q-Catalan series.

The imported theorem `QZeta3.irrational_of_poly_approx` is a general irrationality
criterion for an arbitrary real number and a sequence of integral polynomials.
`QCatalan.Main` supplies its hypotheses using the concrete q-Catalan series and
polynomials. The final q-zeta irrationality theorem is not used. In particular,
the unused upstream `QZeta3.Main`, `QZeta3.Frozen.Theorem11`, and
`QZeta3.ElementarySecondProof` files have been excluded, along with the other
upstream modules outside the final import closure.

The retained upstream modules are:

```text
AnalyticDeterminant       AnalyticWeight          CauchyAtInfinity
CauchyExterior           CauchyMeromorphic       CauchyPole
ClusterBasis             ClusterCounts           Content
ContentProof             Criterion               CyclotomicBounds
CyclotomicLocal          Defs                    Denominators
DividedDifferences       Elementary              Functional
GenericGram              GenericMoments          GenericSpecialization
GeometricTail            Imports                 IntegerFractions
Leading                  LocalClusterTransport   LocalDeterminants
LocalEvaluation          LocalGramBounds         LocalPoleDescent
LowClusterEntries        MovingClusterBasis      MovingProper
NonvanishingAlgebra      NonvanishingAnalytic    PolynomialMomentRank
Purity                   TotientSieve
```

All names in this list have the `QZeta3.` prefix. The original snapshot contained
73 Lean modules; 35 unused modules were removed. The source import closure has
no missing local modules. Import analysis is a provenance and packaging check;
the Lean build and axiom audit are separate verification steps.

## q-Catalan-specific work and adapted proofs

The `QCatalan/` namespace contains the actual target and its proof. Its character
is zero on even indices and alternates on odd indices. Its functional uses the
first Euler derivative, its exterior nodes are `p^(2*a)`, and its Cauchy
transform has double poles on the odd reciprocal lattice. These definitions and
their identities are checked for this target, including the extra denominators
`1 + z^(2*j)`.

Several proofs adapt the structure of the upstream development. The following
table records the main adaptations; it is not a claim that the mathematical
ideas of the upstream proofs originated in this package.

| q-Catalan modules | Reused proof structure and substantive adaptation |
| --- | --- |
| `Series` | Elementary summability, Euler derivatives, and functional linearity from the upstream `Elementary`, `Purity`, and `Functional` development; the signed first-derivative moments and their double-series identities are proved for q-Catalan. |
| `GramIdentity` | The upstream Gram/partial-fraction assembly, specialized to squared nodes and signed pole values; polynomial quotient terms are retained. |
| `CauchyAtInfinity`, `CauchyExterior`, `CauchyPole`, `CauchyNonrational`, `CauchyFunctional`, `MomentDecay`, `CauchyInterpolation`, `Nonvanishing` | The upstream Cauchy-transform and interpolation route, rebuilt with q-Catalan moments, double poles, and odd support. |
| `GenericSpecialization` | The upstream localization/specialization framework, extended to squared nodes and the inverses of `1 + z^(2*j)`. |
| `GenericEvaluation`, `IntegerFractions` | Evaluation and monic integer-denominator arguments for the actual q-Catalan determinant, including its additional denominators. |
| `DenominatorDescent` | The upstream local-pole-to-integral-coefficient descent, using the q-Catalan determinant and `rawCK`, with cyclotomic orders through `4*K`. |
| `Normalization` | The general coprime-denominator gluing argument used in the upstream final assembly, combined here with the proved q-Catalan base-prime content theorem. |

The `Raw*` modules supply an explicit conservative arithmetic variant. Its proved
cubic cost is `115552/99225`, strictly below the available budget `7/6` by
`421/198450`. This establishes the target irrationality theorem without claiming
that the manuscript's sharper cyclotomic exponent formula has been formalized.
The proof guide in `README.md` explains that distinction and lists the final
theorem interfaces.

The development was produced with AI assistance. Attribution and source
provenance are distinct from the public Git author name and manuscript byline.
