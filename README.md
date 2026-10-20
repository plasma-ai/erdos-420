# Erdős Problem 420: divisor counts of shifted factorials

This Lean 4 project concerns [Erdős Problem 420](https://www.erdosproblems.com/420), as cataloged by Thomas F. Bloom. Let `τ(n)` count the divisors of `n`, and let `F(f, n) = τ((n + ⌊f(n)⌋)!) / τ(n!)`. Erdős and Graham asked whether `F((log n)^C, n) → ∞` for large `C`, whether `F(log n, n)` is dense in `(1, ∞)`, and more generally whether `F(f, n)` is dense for every monotone `f(n) ≤ log n` with `f(n) → ∞`. We prove that the answer to the last two questions is yes:

> Let `f` be monotone with `f(n) → ∞` and `f(n) ≤ log n` for all large `n`. Then for every `R > 1`, every `ε > 0`, and every `N`, there is `n ≥ N` with `|F(f, n) − R| < ε`.

In particular `F(log n, n)` is dense in `(1, ∞)`. The first question, about `(log n)^C`, is not addressed.

The analytic input is Theorem 1.1 of OpenAI's [*The Quasi-Riemann Hypothesis*](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) (30 September 2026): every Dirichlet L-function is zero-free in `re s > 7/8`, apart from the principal pole at `1`. That theorem is not assumed here. Its Lean proof from [openai/math](https://github.com/openai/math) is vendored and builds as part of this project. From it we derive, in Lean, the prime number theorem in arithmetic progressions with a power saving, uniformly in the modulus: `θ(Y; q, c) = Y / φ(q) + O(Y^{15/16} log² Y)` for all `q ≤ Y`.

The [blueprint](blueprint/proof.md) explains the proof in prose, following the Lean development module by module. It identifies the input from the zero-free theorem and Maynard's sieve and the additional covering, tail estimates, and sliding-window argument.

## Literature and scope

Erdős and Graham posed the questions in *Old and new problems and results in combinatorial number theory* (1980). Erdős, Graham, Ivić, and Pomerance (*On the number of divisors of n!*, 1996) proved `τ(n!) / τ((n − 1)!) = 1 + P(n)/n + O(n^{−1/2})`, where `P(n)` is the largest prime factor of `n`, and `liminf F(c log n, n) = 1` for every `c > 0`. The [discussion thread](https://www.erdosproblems.com/forum/thread/420) had no proof claims for the density questions when we checked it on 2026-10-13. We make no claim about priority or the status of the problem.

**Proof outline.** Fix `R > 1`. Each prime `p` with `p² > n + h` divides at most one `x` in the window `(n, n + h]`, and multiplies the ratio by exactly `1 + p/x`. So `log F(f, n) ≈ Σ_{x in the window} P(x)/x`, and an `x = kp` with `p` prime contributes `log(1 + 1/k)`.
- **Covering.** A covering of Westzynthius type by primes in `[(log u)^{r+3}, u]`, with `u ≍ log X`, leaves exactly a fixed set of holes `k bᵢ` uncovered in a slab of length `log X`. Every other integer in the slab has a large cofactor.
- **Prime holes.** Maynard's sieve, with the covering modulus as a CRT modulus up to `X^{1/64}`, puts primes `a + bᵢ` at `m` of the holes. Its level of distribution comes from the uniform estimate above.
- **Small tail.** A Selberg upper sieve shows that the integers outside the holes contribute `o(1)` on weighted average. Maynard's roughness bound (Proposition 6.1(4) of *Dense clusters of primes in subsets*) handles the composite holes.
- **Sliding window.** Moving the window across the holes changes `log F` by steps of `log(1 + 1/k)` and passes within `ε` of `log R`.

## Publication layout

`Challenge.lean` states the results using only Mathlib imports. Its two `sorry` proofs are deliberate: this file contains the statements to audit. No formal statement of Problem 420 was available, so `F` and both statements are written here. Density in `(1, ∞)` is stated as `Set.Ioi 1 ⊆ closure _`. `Solution.lean` imports the proof development and supplies both theorems. `comparator.json` selects their names and the allowed axioms for [Comparator](https://github.com/leanprover/comparator).

The proof development lives under `Erdos420/`:

- `Erdos420/FinalAssembly.lean`, `GoodAnchor.lean`, `SlabWeights.lean`, and `SlabTail.lean` carry out the sliding window, the extraction of a good anchor, and the weighted slab tail.
- `Erdos420/DivisorRatio.lean` is the divisor ratio of shifted factorials.
- `Erdos420/Covering.lean` and `Erdos420/Covering/` are the protected covering.
- `Erdos420/Sieve/` is the Selberg upper sieve for linear forms and the anchor count built on it. `Erdos420/Elementary/` holds Mertens' theorems.
- `Erdos420/Analytic/` derives the uniform estimate in progressions from the vendored zero-free half-plane. It generalizes erdos-770's explicit formula to every primitive character and to `ζ`.
- `Erdos420/Maynard/` builds Maynard's weights from the generalized PrimeGapsLib sieve. It contains `M_k ≥ log k − 2 log log k − 2`, the sharp bound on the weights, and the roughness bound.
- `Erdos420/Asymptotics.lean` holds the elementary estimates shared across these parts: the growth of `log`, `log 4 < 2`, and the tail bound `∑_{n > K} 1/n² ≤ 2 / (K + 1)`.

Four vendored libraries live under `vendor/`, each with its upstream license and a provenance README:

- `vendor/OAI/` holds the import closure of the Dirichlet seven-eighths theorem from [openai/math](https://github.com/openai/math), ported to this toolchain.
- `vendor/PrimeNumberTheoremAnd/` holds the Perron formula, the rectangle residue calculus, and the Wiener closure, from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
- `vendor/RellichKondrachov/` holds the Rellich–Kondrachov closure the OAI library imports, from [rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov).
- `vendor/PrimeGapsLib/` holds Maynard's sieve from [AxiomMath/PrimeGapsLib](https://github.com/AxiomMath/PrimeGapsLib). It is generalized in place from the fixed `W`-trick modulus to a general modulus `Q`, with a power-saving level of distribution and the prime number theorem as hypotheses that `Erdos420/` discharges. Its README records every statement change.

`Challenge.lean`, `Erdos420/Statement.lean`, and the files of `Erdos420/` that import only Mathlib use the module system. Files that depend on the non-module vendored libraries are ordinary files.

`formalization.yaml` records the mathematical sources, authorship, AI use, source fidelity, and review status for a registry submission.

The Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The full build includes `Challenge` and therefore reports its intentional `sorry` warnings. The proofs in `Solution` can also be built directly with `lake build Solution`.
