# Attribution and historical context

This document separates established antecedents, recent reports, the supplied research record, and the editorial work in this repository. It makes no comprehensive priority claim.

## Primary mathematical antecedents

| Source | Specific relevance | Role here |
|---|---|---|
| [Jouhet–Mosaki, arXiv:0811.4287v1](https://arxiv.org/abs/0811.4287) | Exact beta normalization, classical limit, collective even-weight irrationality results, and odd-weight transcendence discussion | Defines the literature comparison; the main paper targets individual weight two |
| [Zudilin, generalized q-logarithm (2016)](https://arxiv.org/abs/1601.02688) | Section 4, equation (8): cubic decay of Hankel polynomials | Cubic determinant decay has prior precedent |
| [Zudilin, determinantal approach (2017)](https://arxiv.org/abs/1507.05697) | Growing-degree polynomial expressions in irrationality arguments | General methodological antecedent |
| [Uvarov (1969)](https://doi.org/10.1016/0041-5553(69)90124-4) and [Krattenthaler (2021)](https://arxiv.org/abs/2103.03969) | Rationally modified moment/orthogonal-polynomial systems and determinant identities | Context for moving denominators; positivity is not available for our signed derivative functional |
| [Prévost, remainder Padé approximants (2019)](https://arxiv.org/abs/1709.05389) | Approximation and moment methods for Hurwitz zeta | Related approximation-theoretic antecedent |

The [Persiflage post of 24 September 2026](https://galoisrepresentations.org/2026/09/24/zeta5-is-irrational/) prompted this historical comparison. Credit is given to the exposition as motivation and to the original papers for their mathematical contributions.

The target-specific substance of the present notes is the simultaneous control of the signed step-two functional: exact polynomial degree, coefficientwise base-prime content, the complete cyclotomic cost including quotient moments, real decay, and nonvanishing with moving denominators. This does not claim invention of the general determinant method.

## Classical Catalan reports

The paper cites [OpenAI's September 24, 2026 preprint](https://github.com/openai/math/blob/fd4aeeb/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf) and [Sean Litsey's October 11, 2026 Hexagon contribution](https://hexagonmath.org/2610.00187v1) as reports about classical Catalan's constant. The Hexagon record identifies its work as primarily AI-generated. These reports were not independently verified here and are not used as inputs to the q-beta proof. No rational affine relation between the fixed-q target and classical Catalan's constant is asserted; a q→1 limit does not transfer irrationality.

## Supplied source and editorial work

The source snapshot is pinned to `fikreab-s/the-math-research-ledger` commit `b19558937c91876d6330c8464871e146a820c909`, under `problems/odd-zeta/computations/alternatives_20261011/`. All 29 downloaded blob identities are checked in [source-manifest.json](../provenance/source-manifest.json).

The prior candidate and extensions are preserved as research provenance. The current preparation reorganized the pure theorem into a paper, supplied historical context and scope statements, made the totient calculation explicit, clarified transform convergence, displayed the residue's square factor, arranged fresh independent internal reviews, and replayed finite certificates. Those editorial actions are not represented as the original discovery of the source estimates.

The current public byline **uplift-universal** is the user-selected pen name. The preceding manuscript used **Open Problems research project**; that provenance is retained in the archived sources. The preparation is AI-assisted. No unverified individual human byline, affiliation, or attribution of a specific lemma to a particular model is added. The user supplied conversations from more than one AI service; their content is not silently treated as external mathematical validation.

The preserved files are research sources, not instructions to the verifier. Their historical status labels describe their original context. The current scope and evidence are in [PROOF_STATUS.md](PROOF_STATUS.md).

## Conversation links and access limits

The user supplied these links (the repeated main link is listed once):

- https://chatgpt.com/share/6acc1487-1fc4-83ea-a391-201d09f259dc
- https://chatgpt.com/share/6acbb114-bf5c-83ea-8266-be9e1277b62c
- https://claude.ai/share/bc5c4bbf-52cc-45f6-a65b-a2ed23c36d8d
- https://chatgpt.com/share/6acc1f5f-8e80-83ea-a721-2bf2bb318a24
- https://chatgpt.com/share/6acc1d9a-d7bc-83e8-be7f-640b95f6d006
- https://chatgpt.com/share/6acc1bbd-e0ac-83e8-be29-c9cadfd227e6

The live share pages could not all be retrieved in this preparation. The commit-pinned ledger supplied the mathematical text and reproducibility files. This repository does not claim a new complete reading of every linked conversation. An earlier inventory review and parent-review export are preserved separately and labeled as auxiliary sources.

## Lean formalization

The q-Catalan formalization adds dedicated series, functional, determinant, arithmetic, analytic, and nonvanishing proofs. Its conservative cyclotomic variant proves the same main irrationality theorem with a smaller positive margin. General polynomial, localization, and irrationality-criterion infrastructure is reused from the q-zeta project under its preserved Apache 2.0 license. This reuse does not use the q-zeta irrationality theorem as a hypothesis. See [the Lean notices](../lean/NOTICE.md) and [proof guide](../lean/README.md).
