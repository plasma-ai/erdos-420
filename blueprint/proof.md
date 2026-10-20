# Blueprint: density of divisor ratios of shifted factorials

This document explains, in prose, the two theorems that Comparator checks,
following the Lean development and naming its modules and declarations. The
density construction is Plasma AI's. Its analytic input is OpenAI's
seven-eighths zero-free theorem, proved in the vendored OAI library; its
Maynard weights use the generalized sieve in the vendored PrimeGapsLib.
Neither input is an extra hypothesis of the final statements.

**Conventions.** `τ(n)` counts positive divisors. The function `F f n` is
`τ((n + ⌊f n⌋₊)!)/τ(n!)`, where `⌊·⌋₊` is natural-number floor. A prime hole
(`IsPrimeHole k x`) is an integer `x = k p` with `p` prime and `p > k`.
Write `c_k = log(1 + 1/k)`. The scale `X` tends to infinity; the cofactor
`k`, the desired number `m` of prime holes, and the detector tuple of size
`r` are fixed first. `M` is the covering modulus; `Q` is the sieve modulus,
which also includes the small primes. Intervals `Ioc` and `Ico` mean
`(a, b]` and `[a, b)`. All logarithms are natural.

Module paths below are relative to `Erdos420/`, except where a full path is
given. The declarations are in namespace `Erdos420` unless otherwise noted.

---

## 1. The challenge and the factorial window

`Challenge.lean`, `Solution.lean`, `Statement.lean`.

- **The statements.** `erdos_420.parts.iii` states that, for every
  nondecreasing `f : ℕ → ℝ` tending to infinity and eventually bounded by
  `log n`, and every `N`,

      Set.Ioi 1 ⊆ closure (F f '' Set.Ici N).

  Thus every tail is dense in `(1, ∞)`. `erdos_420.parts.ii` specializes to
  `f n = log n`, with the range over all `n`. These are the second and third
  questions of Problem 420. The first, divergence for shifts `(log n)^C`,
  is not addressed. Natural floor agrees with ordinary floor once `f` is
  nonnegative, which follows eventually from `f(n) → ∞`.
- **The proof interface.** `Challenge.lean` uses only Mathlib and contains
  the two intentional proof placeholders. `Solution.lean` imports
  `FinalAssembly.lean` and proves the same statements by `parts_iii_proved`
  and `parts_ii_proved`.

`Basic.lean`.

- **Large-prime contribution** (`bigPrimeRatio`). This is the sum

      bigPrimeRatio Y x = ∑_{p | x, Y < p²} p/x.

  It need not consist only of the largest prime of `x`: when `x > Y`,
  more than one prime can occur. Retaining the sum is important for the
  slab estimate.
- **The slab tail** (`slabTail`). Sum `bigPrimeRatio A x` over
  `x ∈ (A − H, A + B]`, omitting exactly those `x > A` that are prime
  holes. The tail is nonnegative and increases with `H`
  (`slabTail_nonneg`, `slabTail_mono`). It includes every unwanted
  large-prime contribution, including composite detector positions.

`DivisorRatio.lean`.

**The factorial comparison** (`exists_log_divisor_ratio_bounds`). For
`n ≥ 1` and `h² ≤ n`, put

    L(n,h) = ∑_{n < x ≤ n+h} ∑_{p | x, n+h < p²} log(1 + p/x).

Then

    L(n,h) ≤ log(τ((n+h)!)/τ(n!))
           ≤ L(n,h) + 4h log(n+h)/√n.

This is the form of the factorial-divisor estimate of Erdős, Graham, Ivić
and Pomerance used by the development, re-proved here.

- Write the divisor ratio as a product of
  `(v_p((n+h)!) + 1)/(v_p(n!) + 1)`.
- For `p² > n+h`, the valuation is `⌊v/p⌋` for every `v ≤ n+h`
  (`factorization_factorial_of_lt_sq`). Its factors telescope over the
  multiples `x` of `p`, giving the terms `log(1 + p/x)`
  (`log_factor_eq_sum`).
- For `p² ≤ n+h`, the hypothesis `h² ≤ n` bounds its logarithmic factor
  by `2(v_p((n+h)!) − v_p(n!))/√n` (`log_factor_le`). Weight the valuation
  increments by `log p ≥ log 2` and use
  `log((n+h)!/n!) ≤ h log(n+h)` (`log_factorial_add_le`). This gives the
  displayed error. All omitted terms are nonnegative, giving the lower
  bound too.

---

## 2. From the zero-free theorem to uniform prime counts

`Analytic/QuasiRH.lean`, `Analytic/ZeroFree.lean`.

- **The external theorem** (`LFunction_ne_zero_of_seven_eighths_lt_re`).
  Every Dirichlet L-function is nonzero in `Re s > 7/8`, apart from the
  principal pole at `1`. The wrapper invokes the vendored Lean proof of
  OpenAI's Theorem 1.1. This blueprint uses that theorem rather than
  reproducing its proof.
- **The reflected strip** (`LFunction_ne_zero_of_re_lt_one_eighth`). The
  functional equation excludes zeros of primitive L-functions in
  `0 < Re s < 1/8`, including the conductor-one case for zeta.

`Analytic/Growth.lean`, `Analytic/CenterLowerBound.lean`,
`Analytic/ZetaGrowth.lean`, `Analytic/Admissible.lean`.

- **Growth and a center value** (`norm_LFunction_le`, `le_norm_LFunction`).
  Partial summation bounds a nonprincipal L-function by `q‖s‖/Re s` in
  `Re s > 0`. To the right of `1`, the Dirichlet series of `μχ` inverts
  `L(s,χ)` and is bounded by `ζ(Re s) ≤ Re s/(Re s − 1)`. This supplies
  a lower bound at the centers used for zero counting.
- **The principal character** (`norm_LFunctionTrivChar₁_le`). Partial
  summation against `⌊t⌋ = t − {t}` gives a bound for the entire function
  `(s − 1)ζ(s)`, with its pole removed.
- **Admissibility** (`admissible_LFunction`,
  `admissible_LFunctionTrivChar₁`). The preceding bounds make each
  nonprincipal primitive L-function admissible with its conductor, and
  `(s − 1)ζ(s)` admissible with conductor parameter `3`. Here admissibility
  means that zeros in the right half-plane lie in `[1/8, 7/8]` and that
  growth on fixed disks centered at `9/8 + iT`, relative to the center
  value, is bounded by a fixed power of `Q(|T|+3)`.

`Analytic/LocalFormula.lean`, `Analytic/LineBounds.lean`.

- **Local logarithmic derivative** (`exists_norm_logDeriv_sub_sum_le`).
  Factor off the zeros in a disk and take a holomorphic logarithm of the
  remaining nonvanishing factor. A bound on its real part bounds its
  derivative. Thus `f'/f` differs from the sum of `1/(s−ρ)` over the nearby
  zeros, with multiplicities, by a constant times the logarithmic growth.
- **Zero and line bounds** (`exists_sum_divisor_closedBall_le`,
  `exists_norm_logDeriv_le_of_re_eq`, `exists_good_height`,
  `exists_sum_divisor_rectangle_le`). Jensen's formula bounds the local
  zero count by `O(log(Q(|T|+3)))`. On `Re s = 1/16`, the zeros are a fixed
  distance away, so `f'/f = O(log(Q(|t|+3)))`. Some height in each interval
  `[T₀,T₀+1]` avoids the zeros on both horizontal edges and gives the bound
  `O(log²(Q(T+3)))` there. Summing local zero counts with weight
  `(1+|Im ρ|)⁻²` gives total weight `O(log Q)` in the contour rectangle.

`Analytic/Perron.lean`, `Analytic/Rectangle.lean`,
`Analytic/ExplicitBound.lean`, `Analytic/ZetaExplicitBound.lean`.

- **The integral** (`verticalIntegral_perronIntegrand`,
  `exists_norm_verticalIntegral_sub_le`). The sum
  `∑_{n≤x} Λ(n)χ(n)(1−n/x)` is the Perron integral of
  `−(L'/L)(s,χ)x^s/(s(s+1))` on `Re s = 2`. Truncation at height `T`
  costs `O(x²/T)`.
- **Moving the contour** (`rectangleIntegral_logDeriv_mul`,
  `exists_norm_vIntegral_logDeriv_le`). Shift to `Re s = 1/16` at a good
  height of order `Qx²`. Each zero contributes `x^ρ/(ρ(ρ+1))`, bounded by
  `O(x^{7/8})` times its zero-count weight. The left edge is
  `O(x^{1/16} log Q)` and the horizontal edges are `O(1)`.
- **Smoothed sums** (`exists_norm_sum_vonMangoldt_le`,
  `exists_norm_sum_vonMangoldt_sub_le`). For a nonprincipal primitive
  character the result is `O(x^{7/8} log q)`. For zeta, write
  `−ζ'/ζ = −f'/f + 1/(s−1)` with `f=(s−1)ζ`; the pole contributes `x/2`,
  giving `x/2 + O(x^{7/8})`.

`Analytic/Unsmoothing.lean`, `Analytic/CharacterSums.lean`.

- **Unsmoothing** (`norm_sum_sub_mul_le`). Multiplying the smoothed sum
  by `y` gives `δy²/2 + O(By^{15/8})`. Difference this at half-integers
  separated by `h ≍ y^{15/16}`. The new terms cost `O(h² log y)` before
  division by `h`, since `|a_n| ≤ Λ(n) ≤ log n`. The result is
  `δx + O((1+log x+B)x^{15/16})`.
- **All characters** (`norm_sum_sub_sum_primitiveCharacter_le`,
  `exists_norm_sum_vonMangoldt_mul_char_sub_le`). An imprimitive
  character differs from its inducing primitive character only at prime
  powers supported on the modulus. Their total contribution is at most
  `2√x log x + log q`. Thus, uniformly for every character modulo `q ≤ x`,

      ∑_{n≤x} Λ(n)χ(n) = δχ x + O(x^{15/16} log x).

`Analytic/PrimesInAP.lean`, `Analytic/PrimeCounting.lean`,
`Maynard/Hypotheses.lean`.

- **Progressions** (`exists_abs_sum_vonMangoldt_modEq_sub_le`,
  `exists_abs_thetaAP_sub_le`). Average the character sums using
  orthogonality. The factor `1/φ(q)` cancels the number of characters,
  preserving uniformity. Removing higher prime powers gives
  `θ(x;q,c) = x/φ(q) + O(x^{15/16} log²x)` for `(c,q)=1`, `q≤x`.
- **Unweighted counts** (`exists_abs_primeCountingAP_sub_le_of_le`,
  `exists_abs_primeCountingZMod_sub_le`). Apply Abel summation to
  `(1_{p≡c} − 1/φ(q)) log p`. Above `q`, the theta estimates bound its
  partial sums; below `q`, the class contains at most one prime. This gives
  `π(x;q,c) = π(x)/φ(q) + O(x^{15/16} log²x)`, including the uniform
  estimates for shorter intervals needed in the proof. The main term here
  is the ordinary prime count, not an assumed asymptotic for fixed `q`.
- **The sieve hypotheses** (`primeCountingEstimate`,
  `hasPowerSavingLevel`). The case `q=1` also gives
  `π(x)=x/log x+O(x/log²x)`. Absorb `log²x` into `x^{1/16−ϖ}` for
  `ϖ<1/16`. This proves the library's `Nat.HasPowerSavingLevel θ ϖ`
  for `θ≤1`: an individual uniform error `O(x^{1−ϖ})` for `q≤x^θ`.

---

## 3. The protected covering

`Elementary/Mertens/First.lean`, `Elementary/Mertens.lean`,
`Asymptotics.lean`.

**Elementary estimates.** `abs_sum_primesLE_log_div_sub_log_le` proves
`|∑_{p≤n} log p/p − log n| ≤ 3` from Legendre's factorial formula and
Chebyshev bounds. Partial summation then proves
`∑_{p≤x} 1/p = log log x + O(1)`
(`exists_abs_sum_inv_prime_sub_log_log_le`). The shared asymptotics compare
fixed powers of logarithms with positive powers and bound
`∑_{n>K} 1/n² ≤ 2/(K+1)` (`sum_one_div_sq_le_of_lt`).

`Covering/Estimates.lean`, `Covering/Residues.lean`, `Covering.lean`.

**The covering** (`eventually_exists_protected_cover`). For any fixed
finite set of positive holes `H`, a bound `B` on them, an integer `a≥2`,
and a fixed `C`, let

    coverModulus a u = ∏_{(log u)^a ≤ q ≤ u} q.

For large `u`, there is an integer `z` such that `z+h` is coprime to this
modulus for every hole, but every `z+s` with `−Cu≤s≤B` outside the holes
shares a prime with it. This fixed-multiple interval is enough for the
factorial slab; no covering of length `u log u` is needed.

1. **Initial residues** (`card_survivors_le`). Set `y=(log u)^A`, with a
   fixed exponent `A` to be chosen large. Prescribe residue zero at primes
   `y<q≤u/4`. The survivors among negative offsets have absolute values
   that are either `y`-smooth or of the form `cp`, where `c≤4C` and
   `p>u/4` is prime. Rankin's trick with exponent `1−1/(2A)` bounds the
   smooth numbers (`eventually_card_smoothNumbersUpTo_le`); Chebyshev
   bounds the remaining primes. Including `[0,B]`, at most `Du/log u`
   offsets survive, with `D=16C²+2`.
2. **Middle residues** (`exists_middle_residues`). For primes between
   `(log u)^a` and `y`, average over residues avoiding every hole. Each
   survivor is congruent to a hole at only a controlled number of primes:
   a nonzero difference has at most `log|s−h|/log 2` prime divisors.
   Successive averaging leaves at most twice the initial survivor count
   times `∏(1−1/q)`. The reciprocal-prime estimates
   `exists_le_sum_Ioc_sq` and `exists_le_sum_Ioc_pow` allow `A` to be
   chosen so that `∑1/q≥log(16D)`. At most `u/(8log u)` survivors remain.
3. **Cleanup** (`exists_cleanup_residues`). There are at least
   `u/(4log u)` primes in `(u/4,u]`
   (`eventually_div_log_le_card_primes`). For a survivor `s` and a hole
   `h`, at most one such prime divides `s−h`, since `|s−h|≤(u/4)²` for
   large `u` (`card_filter_dvd_le_one_of_abs_le_sq`). Assign distinct
   primes to survivors, avoiding these finitely many exclusions. Each
   chosen residue covers its survivor and preserves all holes.
4. **CRT** (`exists_int_forall_dvd_sub`, `exists_cover_of_residues`).
   Combine the residues at distinct primes into one `z`.

`SlabTail.lean` proves `coverModulus_le`: the modulus is at most the
primorial of `u`, hence at most `4^u`. Taking
`u=log X/(64 log 4)` gives `M≤X^{1/64}` without an asymptotic for `log M`.

---

## 4. Maynard weights for the growing modulus

The vendored PrimeGapsLib supplies the multidimensional sieve, its first
and prime moments, and the passage from the variational constant to smooth
weights. Its `README.md` records the generalization from a fixed small-prime
modulus to `PrimeGaps.ModulusHyp` and a power-saving distribution hypothesis.
The following modules discharge those hypotheses and supply the additional
estimates used by the factorial argument.

`Maynard/Variational.lean`.

**The dimension can be chosen large** (`log_sub_two_log_log_sub_two_le_M`,
`tendsto_M_atTop`). Maynard's variational constant satisfies
`M_r≥log r−2log log r−2` for large `r`. Use the product witness
`F(t)=∏g(rt_i)`, with `g(v)=1/(1+Av)` on `[0,T]`,
`A=log r−2log log r`, and `T=(exp A−1)/A`. Its one-dimensional integral is
one. The product integral bounds `I(F)` from above; restricting to
`∑t_i≤1−T/r` bounds each `J_i(F)` from below. Chebyshev's inequality for
the independent coordinates with density proportional to `g²` bounds the
lost mass. The explicit integrals give the displayed lower bound. Thus a
fixed dimension can give any prescribed prime surplus.

`Maynard/Modulus.lean`, `Maynard/Classes.lean`.

- **Completing the modulus** (`sieveCofactor`, `exists_modulusHyp`). Put
  `Q=M W'`, where `W'` is the product of primes at most
  `D₀(N')=log log log N'` that do not divide `M`. Then `Q` is squarefree,
  contains all the required small primes, and is at most `(N')^η` for
  any fixed `η>1/64`, when `N'` is comparable to `X`. Mertens' estimates
  give `Q/φ(Q)≪log log N'` and the required weighted sum over its primes.
- **The tuple** (`isAdmissible_factorialTuple`). Use
  `b_i=(i+1)r!`, `i : Fin r`. For primes at most `r`, the tuple misses
  residue `1`; for larger primes it occupies fewer than all residues.
- **All valid classes** (`validClasses`, `sum_Ico_eq_sum_validClasses`,
  `exists_le_card_validClasses`). To treat `a₀+Mt`, sum over every
  residue `v mod Q` above `a₀ mod M` for which all `v+b_i` are coprime to
  `Q`. CRT counts these classes as `∏_{p|W'}(p−ν_p)`. Admissibility
  and convergence of `∑1/p²` bound this below by a positive constant
  times `W'(φ(W')/W')^r`. Summing over all these classes retains the
  mass needed for a uniform pointwise normalization.

`Maynard/SharpLambda.lean`, `Maynard/Pointwise.lean`.

- **Sharp coefficient bound** (`exists_abs_l₀_le`). The inverse sieve
  transform has
  `|λ_d|≪((φ(Q)/Q)log R_s)^r`. Factor each coordinate sum using
  `r_i=d_i s_i`; the identity
  `m/φ(m)=∑_{e|m} μ²(e)/φ(e)` injects the products `e s_i` into squarefree
  integers at most `Q R_s`. The bound for their reciprocal totients
  (`sum_squarefree_inv_totient_le`) preserves the factor `φ(Q)/Q`.
- **Rough pointwise bound** (`card_divisors_le_of_rough`,
  `weight_le_of_abs_le`). If all detector primes exceed `X^ρ` and the
  detectors are at most `X²`, each detector has boundedly many divisors.
  Bounding the divisor sum defining the weight by its number of terms
  times `max|λ_d|` shows that division by
  `((φ(Q)/Q)log R_s)^{2r}` makes the weights uniformly bounded on rough
  anchors.

`Maynard/RoughnessBound/Kernel.lean`, `Shift.lean`, `ShiftBound.lean`,
`FirstMoment.lean`, `Local.lean`, `PrimeSums.lean`, and
`Maynard/RoughnessBound.lean`.

**Removing small prime factors** (`exists_sum_weight_nonrough_le`). For
every small mass tolerance, choose `ρ>0` so that anchors with a prime
factor at most `X^ρ` in any detector have at most that fraction of the
mass scale. This is the roughness estimate in Maynard's Proposition 6.1(4),
proved here for the generalized weights.

1. **Kernel** (`sum_yToL_eq_sum_divKernel`). Express the divisor sum in
   the sieve variables `y` using
   `κ(r,a)=φ(r)⁻¹∑_{e|(r,a)}μ(e)e`. At a prime, this is `−1` if the
   prime divides `a` and `1/(p−1)` otherwise.
2. **Shift** (`sum_yToL_eq_sum_yToL_shiftY`). On `p|n+b_m`, the prime
   divides no other detector once the small-prime cutoff exceeds the
   tuple differences. Decompose the squarefree support according to
   whether a coordinate contains `p`. The divisor sum becomes the sum
   for modulus `Qp` with variables

       z_r = (y_r − y_{r p e_m}) + (p−1)⁻¹∑_{j≠m} y_{r p e_j}.

3. **Size** (`abs_shiftY_y₀_le`). For the smooth simplex-supported
   witness, Lipschitz continuity gives
   `|z_r|≤L log p/log R_s+(r−1)F₀/(p−1)`. This also holds at the edge of
   the support, because the witness vanishes outside the simplex.
4. **Local mass** (`exists_S₁_le`, `exists_sum_weight_dvd_le`). The
   usual modulus hypothesis need not hold for `Qp`, so use a separate
   upper bound for its first moment. CRT contributes its main quadratic
   form and an error bounded by the square of the coefficient sum. The
   resulting bound is controlled by the square of the preceding estimate
   for `z_r`.
5. **Summing over primes** (`sum_primesLE_log_sq_div_le`,
   `sum_sq_div_le`). Mertens bounds the `log²p/p` sum, and the inverse
   square tail controls the other terms. The main contribution tends
   to zero as `ρ` tends to zero and the small-prime cutoff tends to
   infinity. Choose `ρ` small enough that the sum of the local errors
   is absorbed by the power saving as well.

`Maynard/Weights.lean`.

**The assembled weights** (`exists_maynard_weights`). For each `m`, choose
`r`, the fixed tuple `b`, and positive constants `γ,c_M`. For every roughness
mass tolerance there are `ρ>0`, a bound `C_W`, and nonnegative weights on
`t∈[N,2N)` for all sufficiently large `X`, provided

    M≤X^{1/64},  M squarefree,  p|M ⇒ p≤log X/2,
    a₀<M,  X≤MN≤2X,  (a₀+b_i,M)=1.

Writing `D(t)` for the number of prime detectors `a₀+Mt+b_i`, they satisfy

    ∑ W(t)(D(t)−(m−1)) ≥ γ∑W,
    ∑W ≥ c_M N/(log X)^r,
    W(t) ≤ C_W on rough anchors,
    ∑_{nonrough t} W(t) ≤ tolerance · ∑W.

The actual library parameters are `θ=5/128`, `δ=3/256`,
`η_Q=5/256`, and `ϖ=3/64`; hence `R_s=(N')^{1/128}`, `θ<ϖ<1/16`,
and `1/64<η_Q<2δ`. The scale is `N'=a₀+M(N−1)`. Weights are restricted
also to `a₀+Mt∈(N',2N']` and summed over the valid classes above.

---

## 5. The uniform upper sieve and prime-cofactor pairs

`Sieve/Selberg/Count.lean`, `LambdaSquared.lean`, `Mass.lean`,
`Sieve/Selberg.lean`.

**The sieve bound** (`exists_card_sifted_linear_forms_le`). Suppose no
prime above `v₀` divides a leading coefficient or a pair determinant of
`κ` linear forms. The count in an interval of length `V` of integers for
which none of the forms has a prime factor in `(v₀,Z]` is

    ≪_κ V (log v₀/log Z)^κ + Z³,

under the size conditions in the theorem, satisfied by the choices below.

- **Roots** (`card_formsProd_eq_zero`,
  `abs_card_filter_dvd_formsProd_sub_le`). Each prime has `κ` distinct
  roots. CRT gives `κ^{ω(d)}` roots for squarefree `d`; counting interval
  points in each class gives density `ν(d)=∏_{p|d}κ/p` with error at
  most `d`.
- **Weights** (`selbergWeight`, `mainSum_selbergWeight`,
  `card_filter_coprime_le`). Möbius inversion over multiples diagonalizes
  the Selberg quadratic form. The minimizing weights have `λ₁=1`,
  vanish above the level `y`, satisfy `|λ_d|≤ν(d)⁻¹≤d`, and give main
  term `1/G(y)`. The crude summed remainder is at most `y⁶`.
- **Mass** (`prod_one_add_selbergTerms_le`, `exp_sum_nu_le_prod`).
  Sift only with primes up to `T=Z^{1/(24κ)}` and take `y=√Z`.
  Mertens' first theorem gives `∑g(p)log p≤(log y)/2` for
  `g(p)=κ/(p−κ)`. Markov's inequality shows that at least half of the
  Euler-product mass lies below `y`. Mertens' second theorem then gives
  `G(y)≫(log Z/log v₀)^κ`. The remainder is `y⁶=Z³`. This deliberately
  coarse power is enough for the later sum.

`Sieve/PairCount.lean`.

**One offset and cofactor** (`exists_card_anchor_pair_le`). Fix an offset
`s≠kb_i` and a cofactor `ℓ≤(log X)^D`. Write `A_t=k(a₀+Mt)` and
`g=gcd(ℓ,kM)`. The condition `ℓ|A_t+s` either has no solutions or puts
`t` in one class modulo `ℓ/g`. Substituting `t=t₀+(ℓ/g)v` leaves an
interval of length at most `Ng/ℓ+1`. The quotient and the `r` detectors
are `r+1` linear forms, with pair determinants, up to sign,

    (Mℓ/g)(b_j−b_i),    (M/g)(s−kb_i).

These are nonzero. For `|s|≤(log X)²`, all prime factors of coefficients
and determinants are at most `v₀=(log X)^{D+3}`. Apply the sieve with
`Z=X^c`, `0<c<1/4`. If the detectors are `X^c`-rough and the quotient is
a prime exceeding `X^c`, the anchor is sifted. Its count is therefore

    ≪ (Ng/ℓ+1)(log log X/log X)^{r+1} + X^{3c},

uniformly in `M,a₀,N,ℓ,s` subject to the stated conditions. No asymptotic
for a tuple of primes is needed.

---

## 6. Summing the slab tail

`SlabTail.lean`.

- **At most two large primes** (`card_filter_primeFactors_le_two`,
  `bigPrimeRatio_le`). For the slab range, `x²<(A+1)³`. Three distinct
  prime factors with squares exceeding `A` would contradict this. Split
  the sum defining `bigPrimeRatio A x` at cofactor `Λ`: the cofactors
  above `Λ` contribute at most `2/Λ`, and the others contribute `1/ℓ`.
- **Which cofactors remain** (`slabTail_le`). A composite rough detector
  has every relevant cofactor above `Λ=(log X)³` for large `X`. Outside
  the protected offsets, if `x=ℓp` with `ℓ≤Λ`, then `p>u`. A covering
  prime `q≤u` dividing `x` must divide `ℓ`, so
  `ℓ≥(log u)^{r+3}`.
- **Compatible offsets** (`card_filter_dvd_add_le`,
  `sum_sum_pair_bound_le`). For each `ℓ`, only offsets satisfying
  `gcd(ℓ,kM)|ka₀+s` can occur. Their number is at most `(H+B)/g+1`.
  Multiply the pair bound by `1/ℓ` and sum. Use `g≤ℓ`, the inverse
  square tail, and `∑_{ℓ≤Λ}1/ℓ≤1+log Λ` (`sum_Icc_one_div_le`).
- **The limit** (`eventually_pair_sum_le`). Put
  `E=(log log X/log X)^{r+1}` and `Y=X^{3c}`. The bound has the form

      O((H+B)NE/L + (NE+(H+B+1)(E+Y))(1+log Λ)),

  with `L≥(log u)^{r+3}`. For `H=O(log X)`, `N≥X^{63/64}` and
  `c≤1/8`, this is `o(N/(log X)^r)`. The errors are controlled after
  summing over offsets and cofactors, not merely for each pair separately.

`SlabWeights.lean`.

**Weighted anchors** (`sum_mul_slabTail_le_at`, `exists_slab_weights`).
Fix `k,m`. Choose the tuple from §4 and set `B=k∑b_i`. Put

    u=log X/(64 log 4),    M=coverModulus (r+3) u,
    H=⌈log(8kX)⌉₊.

Use §3 with a sufficiently large fixed `C` so that the covering contains
all offsets of the slab. Since every prime of `M` eventually exceeds `k`,
CRT lifts the covering residue to `a₀<M` with `ka₀≡z mod M`
(`exists_lt_dvd_mul_sub`). Choose `N` with `X≤MN≤2X`, and take the
Maynard weights at the anchors `A_t=k(a₀+Mt)`.

Restrict to rough anchors. Their removed mass can be chosen small enough
to preserve half the prime surplus, since a tuple has only `r` detectors.
Each prime detector gives a distinct prime hole in `(A_t,A_t+B]`
(`card_prime_detectors_le`). Apply the pair estimate with
`c=min(ρ/2,1/8)` and the preceding tail sum. Thus, for any `η>0` and all
sufficiently large `X`, there are distinct anchors in `[X,8kX]` and weights
with

    0≤W≤C_W,    ∑W≥√X,
    ∑ W(t)(#{prime holes in (A_t,A_t+B]}−(m−1)) ≥ γ∑W,
    ∑ W(t) slabTail k B A_t H ≤ η∑W.

The lower mass bound follows from `N≥X^{63/64}` and the fixed logarithmic
power in §4. Constants `B,γ,C_W` are independent of `X` and of the
requested tail tolerance.

---

## 7. A good anchor and the final sliding window

`GoodAnchor.lean`.

**A constant shift on the slab** (`sum_window_increment_le`,
`exists_good_anchor`). Let `g : ℕ → ℕ` be nondecreasing, tend to infinity,
and eventually satisfy `g(n)≤log n`. For every tolerance and lower bound,
there is an anchor `A` beyond that bound with

    B<g(A),
    g(n)=g(A) for A−g(A)≤n≤A+B,
    at least m prime holes in (A,A+B],
    slabTail k B A (g(A)) ≤ tolerance.

To prove this, take §6 with tail tolerance
`η=γ·tolerance/(4(B+1))` and discard two sets of anchors.

- **Jump slabs.** Distinct anchor slabs overlap at most `H+B` deep.
  Telescope the increments of `g` over each slab and interchange the
  sums. Their total is at most `H+B` times the increase of `g` across
  the whole range, hence `O(log²X)`. A nonconstant slab contributes an
  integer increment at least one, and its weight is bounded. These
  anchors have negligible weight against `∑W≥√X`.
- **Large tails.** Markov's inequality bounds their mass by
  `γ/(4(B+1))` of the total. Each anchor has at most `B` prime holes,
  so removing both bad sets preserves positive surplus.

Some remaining anchor therefore has at least `m` prime holes. Monotonicity
makes `g` constant on its slab. For large `X`, `g(A)>B` and `g(A)≤H`, so
the shorter slab required in the conclusion inherits the tail bound.

`FinalAssembly.lean`.

**The density theorem** (`parts_iii_proved`). Given `R>1` and an error
`ε>0`, choose `ε₁=min(1,ε/(2R))`, then `k` so that `c_k<ε₁/3` and `m`
so that `m c_k>log R`. Apply the good-anchor theorem to `g(n)=⌊f(n)⌋₊`
with sufficiently small tail tolerance, taking `A` large enough for the
factorial comparison and for the desired lower bound on the final index.

Set `h₀=g(A)` and, for `0≤e≤B`, `n_e=A+e−h₀`. The shift is constant on
the slab, so `g(n_e)=h₀`, and the factorial window is
`(A+e−h₀,A+e]`. Since `h₀>B`, it contains exactly the prime holes in
`(A,A+e]`. Their count starts at zero, reaches at least `m`, and increases
by at most one at each integer step.

- **Prime holes** (`sum_log_primeHole`). For large `A`, the prime in
  `x=kp` has `p²>A+e`, and every other prime factor divides `k` and is
  below the large-prime threshold. Its exact contribution is `c_k`.
- **The other terms** (`sum_log_le_bigPrimeRatio`, `window_sum_bounds`).
  Use `log(1+p/x)≤p/x` and enlarge the window to the slab. If `C(e)` is
  its prime-hole count, the large-prime logarithmic sum lies between
  `c_k C(e)` and `c_k C(e)+slabTail k B A h₀`.
- **First crossing.** Choose the first `e` with `c_k C(e)≥log R`.
  Then `log R≤c_k C(e)<log R+c_k`. The factorial comparison adds at
  most `O(log²A/√A)`, so, with the choices above,

      log R ≤ log(F f n_e) < log R+ε₁.

- **Return to ratios** (`abs_sub_lt_of_log`). Positivity and the
  exponential estimate on `[0,1]` give `|F f n_e−R|<2Rε₁≤ε`.
  The anchor can be chosen so large that `n_e≥N`. This is the metric
  characterization of membership in the closure of every tail.

**The logarithmic shift** (`parts_ii_proved`). On the natural numbers,
`log n` is nondecreasing, including Mathlib's convention `log 0=0`, and
it tends to infinity. Apply `parts_iii_proved` and enlarge the tail image
to the full range. `Solution.lean` exposes these two proved statements
under the names checked by Comparator.

---

## 8. What is supplied by the dependencies

The zero-free half-plane is OpenAI's theorem. PrimeGapsLib supplies the
Maynard sieve framework, adapted to a growing modulus as recorded in its
vendoring notes. The factorial comparison and protected covering follow
Erdős, Graham, Ivić and Pomerance; the variational and roughness estimates
follow Maynard. The analytic modules derive the uniform progression estimate
needed by this application from the vendored zero-free theorem.

The density argument combines these inputs with the uniform cofactor-pair
sieve, its weighted sum across the whole slab, the deletion of jump slabs,
and the final sliding window. The formal proof uses the fixed-length
covering `Cu`, the coarse `Z³` sieve remainder, and the cutoff
`(log u)^(r+3)` described above. These choices suffice with the weaker mass
bound `N/(log X)^r`; the tail argument does not need a sharp varying
singular series or a prime-tuple asymptotic. The development proves the two
density questions and leaves the polylogarithmic divergence question open.
