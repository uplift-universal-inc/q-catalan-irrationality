# Lean formalization of the q-Catalan irrationality argument

The target is the Lambert-series q-analogue of Catalan's constant:

\[
\xi_p=\beta_{1/p}(2)=\sum_{n=1}^{\infty}\frac{n p^n}{p^{2n}+1},
\qquad p\in\mathbb N,\quad p\ge2.
\]

This is a fixed reciprocal-integer parameter. It is distinct from the classical
Catalan constant and from combinatorial q-Catalan numbers. Composite bases are
included throughout.

**Verified status:** the complete project and final irrationality theorem have
built successfully with the pinned toolchain. The final theorem interfaces are
`QCatalan.irrational_xi`, `QCatalan.irrational_qCatalan`, and
`QCatalan.irrational_qBeta_two`. Their kernel axiom audits report only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or additional
mathematical axioms. This records a local build and audit; it does not report a
remote CI run.

## Definitions and statement fidelity

`QCatalan/Defs.lean` defines the actual real summand and target:

```lean
noncomputable def term (p n : ℕ) : ℝ :=
  (n : ℝ) * (p : ℝ) ^ n / ((p : ℝ) ^ (2 * n) + 1)

noncomputable def xi (p : ℕ) : ℝ :=
  ∑' n : ℕ, term p (n + 1)
```

`Series.lean` proves `summable_term`, `hasSum_xi`, and `xi_pos` for every base
`p ≥ 2`. Thus the target has the intended convergent sum; the formalization does
not rely on the default value assigned to an unsummable `tsum`.
`hasSum_reciprocal` identifies the equivalent normalization
`n q^n / (1 + q^(2*n))`, with `q = p⁻¹`.

The explicit final theorem can be used after `import QCatalan`:

```lean
example (p : ℕ) (hp : 2 ≤ p) :
    Irrational (∑' n : ℕ,
      ((n+1 : ℕ) : ℝ) * (p : ℝ)^(n+1) /
        ((p : ℝ)^(2*(n+1)) + 1)) :=
  QCatalan.irrational_qCatalan p hp
```

`QCatalan.irrational_qBeta_two` states the corresponding reciprocal-q formula.

The signed functional is the first Euler derivative,

\[
\mathcal L(f)=\sum_{m\ge1}\chi(m)q^m f'(q^m),
\qquad \chi(2m)=0,\quad\chi(2m+1)=(-1)^m.
\]

It is not the second-derivative positive functional used by the companion
q-zeta(3) proof. The signed geometric sums and the absolutely convergent double
series are proved explicitly. In particular, `hasSum_monomial` and
`hasSum_simplePole` certify the exact polynomial and pole moments.

## Proof organization

| Modules | Role |
| --- | --- |
| `Defs`, `Series` | Concrete target, convergence, character identities, and exact signed moments. |
| `Polynomial`, `PartialFractions`, `GramIdentity` | Formal determinant and its identification with the actual real functional; polynomial quotient terms are retained. |
| `Analytic`, `Decay`, `AnalyticAsymptotics` | Double-root basis, signed entry estimates, determinant decay, and explicit exponential envelope. |
| `Content`, `ContentAuxRearrangement` | Common coefficient content at all primes dividing the base. |
| `CyclotomicAuxGeneric`, `GenericSpecialization`, `GenericEvaluation` | Generic rational-function formulas and exact specialization back to integer bases. |
| `RawDefs`, `RawCyclotomicCost`, `RawCyclotomicWeights`, `RawEvenCyclotomic` | Conservative direct cluster denominator for the signed functional. |
| `RawTotientSieve`, `OddReciprocals`, `RawRamp`, `RawOddGrowth`, `RawClusterGrowth`, `RawGrowth` | Finite arithmetic bounds for the conservative cyclotomic cost. |
| `CauchyAtInfinity`, `CauchyExterior`, `CauchyPole`, `CauchyNonrational`, `MomentDecay`, `CauchyInterpolation`, `Nonvanishing` | Double poles at infinitely many odd lattice points; interpolation excludes eventual determinant singularity. |
| `DenominatorDescent`, `IntegerFractions`, `Normalization`, `Asymptotics` | Descent to actual integral polynomial coefficients and normalized decay. |

`QCatalan.frequently_ne_zero` has the unconditional conclusion

```lean
∀ N : ℕ, ∃ K, N ≤ K ∧ QCatalan.DeltaR p K (QCatalan.xi p) ≠ 0
```

under the sole base hypothesis `2 ≤ p`. No positivity of the signed determinant
and no claim that every size is nonsingular is needed.

The `QZeta3/` modules supply previously checked general algebra, analytic tools,
and finite-sieve lemmas. The q-Catalan-specific functional identities, signs,
squared exterior nodes, arithmetic formulas, and real target are defined and
checked in `QCatalan/`.
`NOTICE.md` records the upstream revision, retained source files, and adapted
proofs.

## Conservative arithmetic variant

The manuscript's sharper normalization `E`, `CK`, and `PK` remains separately
defined. The current assembly uses the explicit alternative `rawE`, `rawCK`,
and `rawPK`. At orders divisible by four it uses direct cluster bounds, avoiding
the manuscript's sharper formal tail-interpolation calculation.

A finite sieve using the primes 2, 3, 5, and 7 gives the rational cubic cost

\[
C_{\mathrm{raw}}=
\frac{43168}{99225}+\frac{1024}{3675}
+2\left(\frac{256}{3675}\frac{89}{72}\right)
+\frac{1024}{3675}
=\frac{115552}{99225}.
\]

Here `89/72` is a proved finite upper bound for the sum of odd reciprocal squares.
It is obtained by keeping the first two terms and telescoping the remaining
terms. The sieve estimates are finite periodic sums, with explicit error bounds;
this route does not assume a totient asymptotic.

The cubic real decay contributes `1/3` and the base-prime content contributes
`5/6`. Their combined budget exceeds this conservative cost:

\[
\frac13+\frac56-C_{\mathrm{raw}}
=\frac76-\frac{115552}{99225}
=\frac{421}{198450}>0.
\]

The proof therefore needs the strict inequality, rather than the manuscript's
sharper numerical margin. Do not identify `rawE` with `E` or cite this route as a
formal proof of the sharper cyclotomic exponent formula.

## Build and inspect

Use the toolchain pinned in `lean-toolchain` and the dependency revision in
`lake-manifest.json`: Lean `v4.34.1` and mathlib `v4.34.1`.

From this `lean/` directory:

```bash
lake exe cache get
lake build
```

Individual completed components can be checked with:

```bash
lake build QCatalan.Series QCatalan.GramIdentity QCatalan.Decay QCatalan.Nonvanishing
lake build QCatalan.GenericEvaluation QCatalan.RawRamp
```

Run the included full build, source, and axiom audit with:

```bash
bash scripts/audit.sh
```

The saved local result is in [blueprint/axioms.txt](blueprint/axioms.txt).

A minimal independent audit file can also contain:

```lean
import QCatalan

#print axioms QCatalan.irrational_xi
#print axioms QCatalan.irrational_qCatalan
#print axioms QCatalan.irrational_qBeta_two
#print axioms QCatalan.hasSum_xi
#print axioms QCatalan.hasSum_simplePole
#print axioms QCatalan.gram_det_eq
#print axioms QCatalan.frequently_ne_zero
```

Run it with `lake env lean path/to/audit.lean`. The audited declarations above
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
