# q-Catalan Lean statement and dependency audit

Final audit: 12 October 2026. The root library built successfully (3453 build
jobs). The delivered audit script then compiled the public theorem queries and
composite-base examples, checked 121 project Lean sources, and accepted all
sixteen transitive axiom reports. The fresh output is in `axioms.txt`.
This is an internal formalization review, not external peer review.

## Mathematical target

The definitions printed by Lean are exactly

```lean
def QCatalan.term (p n : ℕ) : ℝ :=
  (n : ℝ) * (p : ℝ)^n / ((p : ℝ)^(2*n) + 1)

def QCatalan.xi (p : ℕ) : ℝ :=
  ∑' n : ℕ, QCatalan.term p (n+1)
```

Thus the target is the specified Lambert-series q-Catalan value at `q = 1/p`.
It is not the classical Catalan constant, a combinatorial q-Catalan number,
or an unspecified real number satisfying an approximation hypothesis.

`QCatalan.hasSum_xi` proves convergence for every natural number `p ≥ 2`, so
Lean's default value for a nonsummable `tsum` is not being used. The hypotheses
of the concrete convergence, degree, content, decay, and nonvanishing theorems
are `2 ≤ p`; none requires `Nat.Prime p`. As direct type checks, convergence
was instantiated at `p = 4`, and arbitrary-large nonzero determinant values
were instantiated at `p = 6`.

## Verified links to the actual construction

| Component | Reviewed declaration or bridge | Result |
|---|---|---|
| Actual convergent target | `hasSum_xi` | The concrete series converges. |
| Character and derivative | `chi`, `theta`, `Lfun` | Character modulo four and the **first** Euler derivative are used. |
| Signed pole moments | `hasSum_simplePole` | The value is `(-1)^a * (xi p - S p (2*a))`; both the sign and even tail cutoff are retained. |
| Rational moments | `mConst`, `mLin`, `momentPolynomial_monomial` | The polynomial quotient is included along with all simple-pole terms. |
| Generic specialization | `Generic.Delta_natCast`, `Generic.Specialization.map_Delta` | The generic determinant specializes to the actual rational determinant. |
| Real determinant | `gram_det_eq` | The real functional determinant equals `DeltaR p K (xi p)`. |
| Exact degree | `natDegree_Delta`, `leading_coeff` | Degree is `K`, with coefficient `(-1)^K * p^(K*(K^2-1))`. |
| Base-prime content | `content_coeff` | The denominator of each coefficient divided by `p^(cK K)` is coprime to `p`, including composite bases. |
| Actual analytic estimate | `DeltaR_decay`, `DeltaR_cubic_decay` | Unconditional cubic decay for the actual target value. |
| Actual nonvanishing | `frequently_ne_zero` | For every `N`, some `K ≥ N` has nonzero target determinant value. |
| Even local cyclotomic bounds | `Generic.fourfold_Delta_rawE_coeff_mem`, `Generic.twice_odd_Delta_rawE_coeff_mem` | Actual determinant coefficients satisfy the conservative local bound. |
| Integer denominator construction | `Generic.Delta_coeff_integerMonicFraction` | Only monic integer polynomial denominators occur before local cancellation. |
| Finite sieve | `oddRawSieve_*Moment_bounds`, `fourRawSieve_*Moment_bounds` | All-index first/second moment inequalities, with explicit errors and exact rational leading constants. |
| All local cyclotomic bounds | `Generic.raw_cyclotomic_coeff_bound` | All positive orders, including odd orders, satisfy the actual coefficient bound. |
| Global integer normalization | `rawPK_coeff_den` | Every coefficient of the actual `rawPK` polynomial has denominator one. |
| Concrete denominator growth | `log_rawCK_le` | The actual raw clearer has cubic cost `115552/99225 < 7/6`. |
| Asymptotic assembly | `tendsto_pow_mul_rawEps_of_cost` | The concrete growth theorem discharges its explicit cost hypothesis in `irrational_xi`. |
| Public theorem | `irrational_xi`, `irrational_qCatalan`, `irrational_qBeta_two` | Irrationality holds for every natural base `p ≥ 2`, with no additional mathematical assumptions. |

## Differences from the sharper manuscript route

The analytic proof uses the conservative finite determinant bound

\[
 K!\,[6(2K-1)]^K p^{-b_K}
\]

instead of the manuscript's sharper Hadamard prefactor. The exact cubic exponent
`bK` is unchanged. A kernel-checked consequence is

\[
 |\Delta_K(\xi_p)|\le
 \exp\!\left[-\frac{\log p}{3}K^3+
 \left(\log 12+2+\frac32\log p\right)K^2\right].
\]

The denominator route uses `rawE`, `rawCK`, and `rawPK`. At orders divisible by
four it directly clears proper fractions with cluster weights and separately
bounds the polynomial quotient contribution by `K-u-1`. This is larger than the
manuscript's double-zero residue bound. The stronger finite sieve proves the
rational upper cost `115552/99225 < 7/6`, leaving the strictly positive cubic
margin `421/198450`. These constants are the ones used by the completed proof.

The formal double-zero identity and residue-rank lemmas in `Cyclotomic.lean`
do **not**, by themselves, identify the finite character-tail interpolant with
that residue. The conservative route does not invoke this missing identification.
Consequently, the completed conservative theorem does not constitute formal
verification of every sharper `E`/`CK` estimate in the manuscript.

## Local arithmetic review

The even-order review checked the following details in the source:

- Collision geometry uses squared nodes `z^(2*a)` and the order of `ω^2`.
- A factor `1 + z^(2*j)` has at most a simple pole away from zero; the first
  possible singular polynomial moment at order `4*u` has index `u`.
- At even orders the finite character tail is regular because all potentially
  singular even-index summands have character zero.
- Row and column scaling applies to the complete proper matrix. The quotient
  contribution is retained and receives its own rank bound.
- The locally invertible polynomial basis is connected back to the original
  determinant; regularity is not merely asserted for an unrelated matrix.
- Generic specialization explicitly includes the additional plus denominators.
- Descent must check every nonzero finite point, including points that are not
  roots of unity, before applying monic integer polynomial division.

No statement-fidelity inconsistency was found in these inspected components.

## Kernel and source audit

`QCatalan/Audit.lean` imports the completed root theorem and executes
`#print axioms` for:

- `QCatalan.irrational_xi`
- `QCatalan.irrational_qCatalan`
- `QCatalan.irrational_qBeta_two`
- `QCatalan.hasSum_xi`
- `QCatalan.hasSum_simplePole`
- `QCatalan.leading_coeff`
- `QCatalan.natDegree_Delta`
- `QCatalan.content_coeff`
- `QCatalan.DeltaR_cubic_decay`
- `QCatalan.frequently_ne_zero`
- `QCatalan.Generic.raw_cyclotomic_coeff_bound`
- `QCatalan.Generic.Delta_coeff_integerMonicFraction`
- `QCatalan.rawPK_coeff_den`
- `QCatalan.rawPK_frequently_ne_zero`
- `QCatalan.log_rawCK_le`
- `QCatalan.tendsto_pow_mul_rawEps_of_cost`

Every query returned exactly `propext`, `Classical.choice`, and `Quot.sound`.
The public irrationality theorem was also instantiated at the composite bases
4 and 6. The source gate found no code tokens introducing `sorry`, `admit`,
`native_decide`, a custom `axiom`, or an `unsafe` implementation in any delivered
project Lean source. It ignores nested comments and string/character literals;
the transitive kernel query is the authoritative check of theorem dependencies.

`./scripts/audit.sh` rebuilds the library and generates a fresh axiom report.
The Python checker rejects disallowed axioms, missing or repeated reports,
omitted public theorem queries, and Lean errors. Its rejection paths were
checked with synthetic reports containing an unknown axiom, an admitted proof,
a missing query, and a duplicate query. The separate GitHub Actions workflow
installs version-pinned elan, uses the pinned Lean/mathlib versions, fetches the
mathlib build cache, and runs the same audit. The workflow has not been run
remotely as part of this local verification.

The imported `QZeta3` namespace contains reusable algebra, local-ring,
interpolation, and analysis lemmas. Its q-zeta irrationality theorem is not a
substitute for any q-Catalan theorem. The signed moments, odd support, double
poles, squared exterior nodes, and the q-Catalan determinant bridges are proved
in the `QCatalan` namespace.

## Final integration check

All final gates passed:

1. `QCatalan.Main` and the root `QCatalan` library compiled successfully.
2. Lean printed the public theorem type as
   `QCatalan.irrational_xi {p : ℕ} (hp : 2 ≤ p) : Irrational (QCatalan.xi p)`.
   The explicit Lambert-series and reciprocal-q versions have the same sole
   mathematical restriction on the base.
3. All three public theorems have only the standard three transitive axioms.
4. `irrational_xi` discharges integer coefficients through the complete local
   bounds and descent, growth through `log_rawCK_le`, nonvanishing through
   `rawPK_frequently_ne_zero`, and decay through the actual determinant estimate.
   Every normalization link uses the same `rawPK`/`rawCK` construction.
5. The completed conservative proof remains explicitly distinguished from the
   sharper manuscript estimates that it does not require.
