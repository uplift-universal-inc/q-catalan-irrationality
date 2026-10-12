# Companion results and future papers

This inventory records the related results already present in the source snapshot, with their evidence level. “Written proof candidate” means an all-index written argument exists; it does not mean external acceptance or complete formal verification.

| Result | Exact scope | Current evidence | Intended treatment |
|---|---|---|---|
| Pure q-Catalan irrationality | `β₁/ₚ(2)` for every integer p≥2 | Complete Lean proof via the conservative cyclotomic variant; full build and final axiom audit passed; written sharper argument and finite replays retained | Main paper in this repository |
| Improved pure cyclotomic cost | Replace `C=1/6+1309/(150π²)` by `C'=1/6+5281/(675π²)` | All-index source derivation with upper-node savings; historical 100-case exact check; fresh arithmetic review inspected the refinement, but the main paper uses the simpler bound | Optional technical refinement or appendix in a later version |
| Mixed q-beta linear independence | `1, β₁/ₚ(1), β₁/ₚ(2)` are linearly independent over Q for each integer p≥2 | Complete companion proof candidate and original internal final audit; preserved historical finite checks; not freshly replayed or independently reviewed in full during this editorial pass | Separate focused paper with a new full review |
| Weight-one transcendence | `β_q(1)` for algebraic q with 0<|q|<1 | Already discussed in Jouhet–Mosaki through theta functions and Nesterenko's theorem | Established background; not a new discovery to claim |
| Arbitrary rational parameters | q=a/b outside the reciprocal-integer family | No proof supplied in this q-beta package | Open extension of this construction |
| Individual even weights 4,6,…; transcendence at weight two; effective measures | Beyond the displayed pure/mixed theorems | No proof supplied here | Future research, not theorem entries |

## Refined arithmetic source

The [cost report](../provenance/research/qbeta2-step2-cost/REPORT.md) retains a saving of `1219/(1350π²)` from selected odd-order clusters. It gives `C'=1/6+5281/(675π²)` and remaining margin `1−5281/(675π²)`. The conservative theorem already has a strictly positive margin, so this extra case analysis is unnecessary for the present conclusion. Finite results in the original [check.json](../provenance/research/qbeta2-step2-cost/check.json) are preserved as historical evidence, not mislabeled as a fresh replay of the sharper formula.

## Mixed source and its additional obligations

The [mixed extension](../provenance/research/qbeta-mixture/MIXTURE_EXTENSION.md) uses

`L(f) = A Σ χ(m)[f(q^m)−f(0)] + B Σ χ(m) θf(q^m)`

to address every nonzero integer combination `A β₁/ₚ(1)+B β₁/ₚ(2)`. Requiring A even loses no rational relation because the relation can be multiplied by two. The [original final audit](../provenance/research/qbeta2-audit/MIXTURE_FINAL_AUDIT.md) records the following essential differences from the pure argument:

- The local zeroth moment has an extra term `−A/(2F_K(0))`. Its remainder is not simply integral, although the same content bound still accommodates it.
- The renormalization subtracts `f(0)` and must be retained even where the basis vanishes on the early support.
- At orders 4u the residue interpolation has a simple zero in general; the proper-part rank cost changes from `(K−4u)_+` to `(K−2u)_+`.
- The resulting sufficient cost is `1/6+244/(27π²)`, leaving positive margin `1−244/(27π²)`.
- Nonvanishing must cover every fixed nonzero pair (A,B), including either coefficient being zero.

These obligations should be carried explicitly into the separate manuscript. The pure theorem's fresh review is not a substitute for a fresh review of them.

## Relationship to the other repository

The [q-zeta(3) repository](https://github.com/uplift-universal-inc/qzeta3-irrationality) contains a distinct Lambert-series target and its own companion inventory. Its rational-parameter extensions and incomplete Lean development are not proofs for this q-beta theorem. This repository keeps the q-beta source and proof status separate.
