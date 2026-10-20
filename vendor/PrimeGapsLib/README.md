# PrimeGapsLib source provenance

The 191 upstream Lean modules in this directory are taken from
[AxiomMath/PrimeGapsLib](https://github.com/AxiomMath/PrimeGapsLib) at commit
`1faa7b14e82ddebc2772dfb9153922f01b106477` (2026-08-18). Its
`formalization.yaml` lists the authors as Evan Chen, Sidharth Hariharan, Kenny
Lau, Bhavik Mehta, Ken Ono, Ashvin Swaminathan, Jesse Thorner, and Yunzhou Xie,
and records that the proofs were produced by Axiom Math's formalizers together
with AxiomProver. They are distributed under the Apache License 2.0, whose full
text is in [LICENSE](LICENSE).

They are the import closure of `PrimeGapsTheory.Endgame.MainProp`,
`PrimeGapsTheory.Endgame.ManyPrimes`, `PrimeGapsTheory.Variational.MkApprox`,
and the six `PrimeGapsTheory.Variational.M016Asymp.*` modules, not the whole
upstream library, and keep their upstream module names: 188 modules under
`PrimeGapsTheory/` and 3 under `PrimeGapsCert/`, with the certificate data
`PrimeGapsCert/Gap600/k105d20n15.json` that `PrimeGapsCert.Gap600.Witness`
reads at elaboration time. Upstream, this is Maynard's sieve for the
`W`-tricked forms `W n + w₀ + hᵢ`, `n ∈ (N, 2N]`, with
`W = primorial ⌊log log log N⌋₊`: the asymptotics of `S₁` and `S₂`
(`MainProp.prop_main_prop`), the passage from `S₂ − ρ S₁ > 0` to many primes
(`lem_S_positive_implies_primes`), and the variational problem for `M_k`
(`MkApprox`, `M016Asymp`), with the Bombieri–Vinogradov input as the hypothesis
`Nat.HasLevelOfDistribution`. Here the sieve is generalized to the residue
classes `n ≡ w₀ (mod Q)` for a general modulus `Q`; see
[Generalization](#generalization).

## Replacement of the `PrimeNumberTheoremAnd` dependency

Upstream depends on AxiomMath's fork of `PrimeNumberTheoremAnd`, whose module
names (`Fourier`, `Sobolev`, `SmoothExistence`, `Rectangle`,
`ResidueCalcOnRectangles`) clash with the upstream `PrimeNumberTheoremAnd`
vendored in `vendor/PrimeNumberTheoremAnd/`, so the fork is not vendored. The
closure reaches it through two imports:

- `NumberTheory/PrimeCountingZMod.lean` imports `PrimeNumberTheoremAnd.Defs`
  only for `pi x = Nat.primeCounting ⌊x⌋₊`, behind the `π(x)` notation. It now
  imports `PrimeGapsTheory.Vendored.PNTDefs`, a new module that copies that
  definition verbatim and imports the Mathlib modules `Defs` brought in
  transitively.
- `NumberTheory/PNT.lean` imports `PrimeNumberTheoremAnd.MediumPNT` to prove
  `PNT.primeCounting`: `|π(N) − N / log N| ≤ C N / (log N)²` for `N ≥ N₀`. Its
  import is replaced by `Mathlib.NumberTheory.Chebyshev`, and the theorem by
  the definition `PNT.PrimeCountingEstimate` of the same statement, which is
  taken as a hypothesis `hPNT` by `NumberTheory/DyadicPNT.lean`,
  `Sieve/PNT.lean`, and everything downstream of them, up to
  `MainProp.prop_main_prop`. It follows by partial summation from the case
  `q = 1` of the power-saving estimate `Erdos420.exists_abs_thetaAP_sub_le`, and
  is discharged from it in `Erdos420`.

## Porting changes

Upstream pins Lean `v4.33.0-rc1` and Mathlib commit `288f16d`. This project pins
Lean and Mathlib `v4.35.0-rc4`, and 27 further modules were changed to build
here. The changes follow Lean and Mathlib changes and keep every statement:

- Mathlib renamed the ordered-semiring product lemmas to `₀` forms, giving the
  old names to the ordered-monoid versions. Fifteen modules use
  `Finset.prod_le_prod₀` for `Finset.prod_le_prod`; `Sieve/Transforms/YmFromY.lean`,
  `Sieve/Transforms/YmAjNeRj/Kernel.lean`, and
  `Variational/M016Asymp/IkTensorUpperBound.lean` use `Finset.prod_le_one₀` for
  `Finset.prod_le_one`; and `ArithmeticFunction/Estimates.lean`,
  `Arithmetic/HAsymptotic/Summability.lean`, and `Sieve/S2m/SecondMoment.lean`
  use `prod_le_prod_of_subset_of_one_le₀` for `prod_le_prod_of_subset_of_one_le`.
- `MemLp f p μ` is now `eLpNorm f p μ < ∞`, with measurability folded into
  `eLpNorm`. `Analysis/Tonelli/LpGeneral.lean` uses `hf.aestronglyMeasurable`
  for `hf.1` and `hf` for `hf.2`, passes measurability to
  `eLpNorm_exponent_top`, `eLpNorm_eq_lintegral_rpow_enorm_toReal`, and
  `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`, and passes
  `hMS.nullMeasurableSet` to `memLp_indicator_iff_restrict` and
  `eLpNorm_indicator_eq_eLpNorm_restrict`. In `Lp.integralLeftₗ`, elaborating
  `memLp_indicator_iff_restrict … |>.mpr (Lp.memLp f)` inside `filter_upwards`
  now times out, so the two instances are stated first as `have`s with their
  types. `Variational/SmoothApprox.lean` passes the measurability hypothesis
  to `eLpNorm_eq_lintegral_rpow_enorm_toReal` and drops the measurability
  arguments `eLpNorm_add_le` no longer takes.
- Under the module system, lemmas and `fun_prop` attributes from modules that
  are no longer imported transitively are missing. `Analysis/Zeta.lean` imports
  `Mathlib.Analysis.PSeriesComplex`, `Arithmetic/Mertens/TauK.lean` imports
  `Mathlib.Analysis.Calculus.FDeriv.Extend` and
  `Mathlib.MeasureTheory.Function.Floor`,
  `Arithmetic/Mertens/CoprimeHarmonic.lean` imports
  `Mathlib.Algebra.Order.Floor.Semifield`, and
  `Variational/Marginal/Infra.lean` imports
  `Mathlib.Analysis.Calculus.ContDiff.WithLp`. `Tactic/Utils.lean` imports
  `Lean.Meta.Tactic.Util`, since a non-`meta` definition may no longer use
  `MVarId.getType` through a `meta` import.
- Batteries removed `Batteries.Data.Nat.Gcd`, so
  `Arithmetic/HAsymptotic/ConvForm.lean` and `Sieve/S2m/QFactor.lean` import
  `Mathlib.Data.Nat.GCD.Basic` instead.
- `convert … using 2` now produces two goals instead of three, so
  `Analysis/SpecificSums.lean` drops the leading `rfl` case.

No `axiom` or heartbeat option was added, and the leanOptions upstream sets in
its lakefile are not needed.

## Generalization

The sieve is generalized in place from the modulus `W N = primorial ⌊D₀ N⌋₊`
(`D₀ N = log log log N`) to a parameter modulus `Q`, uniformly in `Q` and in the
residue `w₀ : ZMod Q`, so that it applies to the moduli of
`Erdos420.exists_maynard_weights`. The definitions `W`, `D₀`, `sieveTruncation`
(`R = N ^ (θ / 2 − δ)`) and `mainScale` are unchanged; every statement that
named `W N` now quantifies over `Q`.

### Hypotheses

- `PrimeGaps.ModulusHyp CQ η N Q` (`Sieve/PermissibleSupport/FunctionW.lean`)
  collects what the sieve needs of `Q` at scale `N`: `Q` is squarefree,
  `primorial ⌊D₀ N⌋₊ ∣ Q`, `Q ≤ N ^ η`, `Q ≤ CQ · log log N · φ(Q)`, every prime
  factor of `Q` is at most `log N`, and
  `∑_{p ∣ Q} log p / (p − 1) ≤ CQ · log log N`. Its consequences are
  `ModulusHyp.pos`, `ne_zero`, `one_le_totient`, `totient_pos`,
  `prime_dvd_of_le_D₀`, `two_dvd`, and, in the new module
  `Sieve/PermissibleSupport/ModulusSize.lean`,
  `eventually_primeFactors_le_rpow` and
  `eventually_one_le_totient_div_mul_log`.
- `Nat.HasPowerSavingLevel θ ϖ` (`NumberTheory/LevelOfDistribution.lean`):
  `|π(x; q, a) − π(x) / φ(q)| ≤ C x ^ (1 − ϖ)` for `x ≥ 3`, `1 ≤ q ≤ x ^ θ` and
  `a : (ZMod q)ˣ`. It replaces `Nat.HasLevelOfDistribution` in the `S₂` error
  term, since a Bombieri–Vinogradov average gives no saving of `1 / Q` and the
  `S₂` error must now be `O(N / (Q (log N) ^ A))`. With `ϖ > θ` and `η < 2 δ`
  the pointwise bound suffices. It follows by partial summation from
  `Erdos420.exists_abs_thetaAP_sub_le` for every `ϖ < 1 / 16`.
- `PNT.PrimeCountingEstimate` (`NumberTheory/PNT.lean`), described above.

### Top-level statements

`Endgame/MainProp.lean`: `prop_main_prop`, `lem_S_asymptotic` and
`lem_S_positive` take `(hPNT : PNT.PrimeCountingEstimate)` first and
`(CQ η ϖ : ℝ) (hη : η < 2 * δ) (hPS : Nat.HasPowerSavingLevel θ ϖ) (hϖ : θ < ϖ)`
in place of the level-of-distribution hypothesis, and conclude, for
`N ≥ N₀`, `∀ Q : ℕ, ModulusHyp CQ η N Q → ∀ w₀ : ZMod Q,
(∀ i, ((w₀.val : ℤ) + h i).gcd Q = 1) → …` with `Q` in place of `W N`
throughout (in `l₀ R Q`, `mainScale k N R Q`, and the `S₂` main term
`φ(Q) ^ k N (log R) ^ (k + 1) / (Q ^ (k + 1) log N)`). The bridge instance
`instNeZeroW_bridge` is removed. `Endgame/ManyPrimes.lean`:
`exists_prime_count_gt_of_S_pos` takes `{Q} (w₀ : ZMod Q)`, and
`maynardTao_endgame` takes `(Q : ℕ → ℕ) (v₀ : ∀ N, ZMod (Q N))`.

### Error budget

Upstream bounds the partial-summation errors at `V = W N` by `log D₀ N`, using
`τ(W N) = N ^ o(1)` and `ℓ_W ≪ log D₀ N`. For general `Q` the budget is
`log log N`, through `Q / φ(Q) ≪ log log N` and `ℓ_Q ≪ log log N`; downstream
only `budget · D₀ N = o(log R)` is used. Lemmas whose budget changed say so in
their docstrings.

The `τ(V)` factors of the datum-level partial summation are not `o(log R)` at
`V = Q`, since `Q` may have all `π(log N)` primes up to `log N` as factors, and
then `τ(Q) = 2 ^ π(log N)`. They all come from the error `5 τ(m) / Z` of
`coprime_reciprocal_sum_asymptotic`, and are replaced by the Euler product
`P_σ(m) = ∑_{d ∣ m} d ^ (σ - 1) = ∏_{p ∣ m} (1 + p ^ (σ - 1))` for
`0 < σ ≤ 1 / 4`, along the chain

- `Arithmetic/Mertens/CoprimeHarmonic.lean`:
  `coprime_reciprocal_sum_asymptotic_rpow`, with error
  `(5 / σ) Z ^ (-σ) P_σ(m)`, from `per_divisor_error_rpow`. The Möbius
  reindexing shared with `coprime_reciprocal_sum_asymptotic` is the new
  `coprimeReciprocalSum_sub_eq_sum`.
- `Arithmetic/Mertens/CoprimeDensity`: `gKernel_rpow_partial_bound`
  (`∑_{d ≤ X} |g(d)| d ^ (1/4)` is bounded, dyadically from
  `gKernel_sqrtnorm_partial_bound`; `dyTail_dyadic_decomp_general` is now
  public) and `exists_abs_sumA_sub_le_rpow`, with error
  `C (φ(m)/m (1 + ℓ_m) + x ^ (-σ) / σ · P_σ(m))`. The tail estimate shared
  with `exists_abs_sumA_sub_le` is the new private `exists_abs_tailSum_le`.
- `Arithmetic/HAsymptotic/Assembly.lean`: `termwise_bound_rpow` and
  `slem_H_error_assembly_rpow`,
  `|S.H z - 𝔖 log z| ≤ C₁ 𝔖 (1 + ℓ_V) + C₂ z ^ (-σ) / σ · P_σ(V)`, using
  `P_σ(V e) = P_σ(V) P_σ(e) ≤ P_σ(V) τ(e)`. The summation over `e` shared with
  `slem_H_error_assembly` is the new private `abs_H_sub_le_of_termwise`.
- `Sieve/Common/SieveDatumEval/EulerProductError.lean` (new):
  `S1_partial_sum_sharp_rpow` and `sieveDatum_kfold_partial_sum_rpow`, the
  versions of `S1_partial_sum_sharp` and `sieveDatum_kfold_partial_sum` with
  `τ(V)` errors replaced by `P_σ(V) / (σ² log z)`: the Abel tail gives
  `∫₂^z t ^ (-σ - 1) ≤ 1 / σ` and the endpoint `z ^ (-σ) ≤ 1 / (σ log z)`.
  They use `abs_partialSum_sub_integral_le_of_smooth` and
  `S1_intTail_one_two_le` (`SieveDatumEval/PartialSummation.lean`) and
  `sieveE_layer_step_le` (`SieveDatumEval/KFold.lean`), which are now public.

At `σ = 1 / log log N` every prime factor of `Q` is at most `e ^ (1 / σ)`, so
`P_σ(Q) ≤ (Q / φ(Q)) ^ 3` (`sum_divisors_rpow_le_cube`, in the new module
`Arithmetic/Mertens/DivisorPowerSum.lean`), and the residual
`P_σ(Q) / (σ² log R) ≤ (φ(Q)/Q) log log N` once
`(CQ log log N) ^ 4 log log N ≤ log R`. The new module
`Sieve/PermissibleSupport/ModulusEulerFactor.lean` proves this as
`ModulusHyp.eventually_sum_divisors_rpow_div_le`, with
`ModulusHyp.one_add_ellV_le` (`1 + ℓ_Q ≤ (1 + |CQ|) log log N`), and bundles
both at `R` in `ModulusHyp.exists_euler_regime`. With them `S1_aggregate`,
`lem_S2m_g_coord`, `Ydisc_approx` and `sieveE_split_bound` are proved with
their stated `log log N` budgets.

### Statement changes

Unless noted, a lemma that took `N` and used `W N` now takes `Q` with
`(hQ : ModulusHyp CQ η N Q)`, or the weaker `(hQD : primorial ⌊D₀ N⌋₊ ∣ Q)` it
needs, and an asymptotic lemma that held for `N ≥ N₀` now takes `(CQ η : ℝ)`
and holds for `N ≥ N₀`, `∀ Q, ModulusHyp CQ η N Q → …`, with `N₀` independent
of `Q`. Lemmas that compared `W` to `R` or `N` take an exponent constraint on
`η`: `hη : η < 2 * δ` (`S₂` chain) or `hη : 2 * (θ / 2 - δ) + η < 1` (`S₁`
chain); `η ≤ 4 * (θ / 2 - δ)` in `TdDecomposition`.

- Foundations and arithmetic.
  - `Foundations/MaynardSieveDatum.lean`: `maynardSieveDatum`, `_γ`, `_V`,
    `_A₁`, `_A₃` and `_γ_prime` take `(Q) (h2 : 2 ∣ Q) (hQ : Squarefree Q)`,
    with `L = maynardM + ∑_{p ∣ Q} log p / p`. New: `maynardGamma_mertens`,
    `maynardM`, `maynardM_nonneg`, `maynardGamma_mertens_bound`.
  - `Arithmetic/SingularSeries.lean`: `gFactor`, `gTerm`, `gTermND`, `gTermD`,
    `tailProduct` and their lemmas are indexed by `Q` (the tail runs over
    `p ∤ Q`); `lt_of_not_dvd_W` becomes `lt_of_not_dvd (N Q hQD)`, plus
    `two_lt_of_not_dvd`; `finite_prime_dvd_W` becomes `finite_prime_dvd`;
    `singularSeries_maynardSieveDatum_γ_asymptotic` is uniform over `Q` with
    `2 ∣ Q`, `Squarefree Q` and `primorial ⌊D₀ N⌋₊ ∣ Q`.
  - `Arithmetic/GammaDensity.lean`: the datum lemmas take `(Q h2 hQ)`.
  - `Arithmetic/RestrictedReciprocalSum.lean`: `mertens_core` is `∀ Q d`.
  - `Arithmetic/TdDecomposition`: `Decomp.doubleSum_ll_log_div_rpow` is
    `∀ Q d`; `SizeHyp.slem_T_d_inner_size_hyp`, `slem_T_d_inner_w_sum`,
    `Summands.W_eventually_ge_exp1` and `Eval.slem_T_d_eval*` are over `Q`.
  - New: `Analysis/SingularSeries.singularSeries_gammaW_of_ne_zero`,
    `Arithmetic/GammaLogSum.killed_density_mertens`.
- Transforms (`Sieve/CRT.lean`, `Sieve/Sums.lean`, `Sieve/Transforms`).
  `S₁`, `S₂` and `S₂m` take `{Q : ℕ} (w₀ : ZMod Q)`. `primeFactor_large`,
  `lcm_prime_factor_large`, `primorial_D0_prime_factor_gt` and
  `crFactor_sub_one_le` take `hQD`. `Harmonic.modulus_primeFactors_le_Rval`
  replaces `primorial_D0_primeFactors_le_Rval`. `sumT_le_main` and
  `sumB_sumT_le` take a `W` with `primorial ⌊D₀ N⌋₊ ∣ W`.
  `phi_logRval_ge_one_of_large`, `sumA_le`, `offDiagKernel_le(_of_two_le)`,
  `offDiagonal_bound`, `exists_large_N0_for_ym`, `maynard_ym_identity` and
  `exists_abs_ym_sub_yInverseSum_le` are over `Q`.
- `S₁` chain (`Sieve/S1`, `Sieve/Substitution/FirstMoment.lean`,
  `Sieve/SijD0/FirstMoment.lean`).
  - `CRT.lem_noncoprime_branch` takes the coprimality of `∏ d` and `∏ e` to `W`
    in place of `W = primorial ⌊D₀ N⌋₊`.
  - `CRT.eventually_master` is
    `R² (log R) ^ (3k) Q ^ (k + 1) D₀ ≤ φ(Q) ^ k N` over `Q`, and
    `crt_assembly` takes that bound in place of separate `φ(W)` and `N`
    bounds.
  - `S1_datum_facts` takes `(W) (hW : W ≠ 0)`.
  - `SijDichotomy`, `pair_pointwise_majorant`, `pair_master`,
    `prime_gt_floor_D0_of_dvd`, `sum_notCoprime_le_sum_over_primes_dvd` and
    `couplingPair_le` take `hW : primorial ⌊D₀ N⌋₊ ∣ W`.
  - `Smoothing.eventually_D0_mul_loglog_le` replaces
    `eventually_D0_mul_logD0_le`.
  - `lem_S1_CRT`, `crt_error_negligible`, `lem_per_pair`, `lem_agg_reduce`,
    `lem_error_bound`, `main_S1_asymptotic`, `lem_S1_substitute_y`,
    `mertens_factor`, `lem_S1_sij_D0(_pair)`, `tsum_truncated_eq_diag`,
    `lem_S1_from_y`, `lem_S1_substitute_smooth_y`, `drop_uij_coupling_bound`,
    `S1_aggregate` and `lem_S1_smooth` are over `Q`.
- `S₂` chain (`Sieve/S2m`, `Sieve/PNT.lean`, `Sieve/Common`,
  `Variational/Marginal/YdiscApprox.lean`).
  - `Error/Basic.lean`: `SieveWeights k N θ δ Q` is supported at `Q`;
    `modulus_Rsq_lt_Npow` replaces `primorial_D0_Rsq_lt_Npow`;
    `collapse_to_modulus_sum` and `exists_totalErrorContribution_le` are over
    `Q`, the latter with error `C y² N / (Q (log N) ^ A)` under `hPS`.
  - `Error/WindowError.lean`, `Error/Main.lean`: the new
    `windowDisc_le_hPS` bounds `windowError N q - 1` pointwise by
    `C ((2N) ^ (1 - ϖ) + N ^ (1 - ϖ))` for `q ≤ N ^ θ`. With it
    `exists_totalErrorContribution_le` no longer sums over moduli: each of the
    `≪ R² (log N) ^ (2k)` pairs `(d, e)` of the support has
    `|λ_d λ_e| ≪ y² (log N) ^ (2k)` and `qMod Q d e < N ^ θ`, so the total is
    `≪ y² N ^ (θ - 2δ + 1 - min ϖ 1) (log N) ^ (4k)`, which is
    `O(y² N / (Q (log N) ^ A))` as `Q ≤ N ^ η`, `η < 2δ` and `θ < ϖ`. The
    level-of-distribution lemmas `collapse_to_modulus_sum`,
    `weighted_modulus_sum_bound`, `windowDisc_sum_le_hLoD` and their
    `TauGrowth`/`TauFourSums` inputs are kept unchanged but no longer used.
  - `MainCRT.lean`: the expansion lemmas take `{Q} [NeZero Q] (wt₀ : ZMod Q)`;
    `S₂m_CRT_main_term_BV_error` is over `Q` with error
    `/ (Q (log N) ^ A)`, as are `lem_S2m_substitute_ym` and
    `lem_S2m_from_ym`.
  - `Substitution.lean`, `ExpandDrop`, `SijD0`: the lemmas that used
    `W N`'s prime factors take `hQD`; `floor_D0_lt_of_prime_coprime`,
    `gSum_le`, `collisionMass_le_tail`, `failure_le_majorant_tail`,
    `lem_S2m_drop_couplings_bound`, `lem_S2m_expand_drop`, `mertens_factor_g`,
    `exists_primeCountingIoc_div_totient_W_le` and `lem_S2m_sij_D0` are over
    `Q`.
  - `GCoord.lean`: `sum_h_eq_muSq_g` takes `(Q h2 hQ)`;
    `singularSeries_maynard_asymptotic` and `lem_S2m_g_coord` are over `Q`.
    `sharp_partial_sum` takes `∀ σ, 0 < σ → σ ≤ 1 / 4 →` after `2 ≤ z`, and
    its two `τ(V)` errors
    `C₂ τ(V) z ^ (-1/8) log (2 V z) Gmax G + C₃ τ(V) log (2 V) / log z · Gmax G`
    become the single `C₂ P_σ(V) / (σ² log z) · Gmax G`, with
    `P_σ(V) = ∑_{d ∣ V} d ^ (σ - 1)`.
  - `Common/S2mEvalAssembly.lean`: `S2m_h_eq`, `S2m_h_eq'`, `M_eq_sieveE` and
    `sieveE_Tm_zero` take `(Q h2 hQ)`.
  - `Eval.lean`: new `D0_loglog_scaled`; `W_ratio_pos` takes `hQ`;
    `Sg_tsum_le`, `boxmass_le`, `cross_error`, `sieveE_split_bound` and
    `lem_S2m_eval` are over `Q`.
  - `Smooth.lean`: `Q_pow_D0_le`,
    `Q ^ k D₀ ≤ φ(Q) ^ k (log N) ^ (2k + 3)` over `Q`, replaces `W_pow_D0_le`,
    which is false for general `Q`; `ym_sup_le_of_maxRealAbs`, `ym_sup_le` and
    `lem_S2m_smooth` are over `Q`.
  - `lem_S2m_second_moment`, `lem_S2m_PNT`, `ymWeightedSum_to_diagonal` and
    `Ydisc_approx` are over `Q`.

### Removed

These lemmas are specific to `W N` and unused after the generalization:

- `MaynardSieveDatum`: `maynardGammaFamily`, `maynardGammaFamily_isWTricked`,
  `maynardA₂_bound`, `maynardL_exists`.
- `Arithmetic/SingularSeries.not_dvd_W_of_mem_tail`.
- `Harmonic.primorial_D0_le_log_rpow` (private).
- `YmFromY.primorial_D0_primeFactor_le_D0`.
- `TdDecomposition/SizeHyp.eventually_const_mul_rpow_mul_loglog_rpow_le`
  (private).
- `S2m/GCoord.lean`: `card_divisors_sq_le_pow_four`,
  `log_two_mul_le_three_mul`, `tau_sq_log_le_logR`, `tau_sq_rpow_log_le_log2`,
  `one_div_card_divisors_le_totient_ratio_mul_log`,
  `residual_boundary_le_const`, `residual_integral_le_const`,
  `ellV_W_le_const_log_D0`.
- `S2m/Smooth.W_pow_D0_le`.

`Arithmetic/Mertens/W.lean`, the `S1_OB_*` lemmas of
`Sieve/S1/ApplyPartialSum.lean`, `W_le_R_eventually`, `D0_logD0_scaled` and the
`Nat.HasLevelOfDistribution` error lemmas of `Sieve/S2m/Error` still compile
unchanged and are kept. So are the `τ(V)`-error `S1_partial_sum_sharp`,
`sieveDatum_kfold_partial_sum` and `slem_H_error_assembly`, which hold for every
`SieveDatum` but are no longer used on the path to `prop_main_prop`.
