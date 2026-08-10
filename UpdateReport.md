# Audit of `blueprint-pass3.tex`

Date: 2026-08-09

This is a read-only audit report.  The source was restricted to
`Preliminaries` (lines 418--3028) and `The main argument` (lines 3029--4557)
of `blueprint/blueprint-pass3.tex`.  The Introduction, the reduction, and all
other sections were ignored.

I counted every labeled `definition`, `theorem`, `proposition`, and `lemma`
environment in those ranges.  Thus propositions and lemmas are listed as
theorem-like results, in accordance with `Instructions.md`.  Equation labels
inside their statements are not separate entries.  A `match` means that the
current Lean code has a recognizable public declaration for the source item;
it does not mean that the new source statement has been completely proved.
`Partial` means that only some claims or supporting definitions are present.
`Missing` means that no public declaration was found, even if a name occurs in
`Status.md` or in a docstring.  `Unmapped` means that a recognizable current
declaration exists but the source label is absent from `Status.md`.

## Summary

Pass 3 contains 118 labeled theorem-like environments: 31 definitions, 60
propositions, 26 lemmas, and one theorem.

The existing formalization covers most of the basic notation, Wiener-space,
`K`-kernel, `M`-kernel, and spaced-sequence material.  The Gaussian and bump
estimate subsections are only partially represented.  In the main argument,
the principal data definitions are present, but the telescoping/positivity
results, the multiplier results, Gaussian-domination results, and main
induction results are largely absent as public theorems.

There are eight pass-3 `auto:` labels absent from `Status.md`.  Seven of them
have recognizable current definitions or preliminary results; the eighth,
`auto:N-kernel-well-definedness`, is missing.  Pass 3 also adds eleven labeled
constant lemmas, none of which has a corresponding public theorem in the
current code.

## Preliminaries

### Notation

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `closed ball` (551) | `Metric.closedBall` | Match; the manuscript notion is supplied by mathlib. `Status.md` maps this to `Metric.closedBall`. |
| `gaussian` (559) | `Codex.Preliminaries.Notation.gaussian` | Match; `Status.md`: Completed. |
| `bracket bump` (581) | `bracketBump`, `scaledBracketBump`, `scaledBracketBumpReal` | Match; `Status.md`: Completed. |

### The Wiener space `W_0`

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `auto:Wiener-space-definition` (623) | `wienerEnvelope`, `MemW0`, `wienerNorm`, `wienerNormOne` in `WienerSpace.lean` | Semantically present but Unmapped: no corresponding source entry is in `Status.md`. |
| `auto:convolution-along-vector-definition` (892) | `convolutionAlongVector` | Semantically present but Unmapped: no corresponding source entry is in `Status.md`. |

#### Theorem-like results

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `auto:local-supremum-measurability` (602) | `measurable_wienerEnvelope` | Semantically present but Unmapped. |
| `W_0 radius independence` (641) | `wienerNorm_le_max_one_three_mul_div_pow_mul`, `memW0_iff_integrable_wienerEnvelope` | Match; `Status.md`: Proof completed. |
| `P:lp-embedding` (684) | `MemW0.memLp` | Match; `Status.md`: Proof completed. |
| `W_0 fiber integrals` (718) | `exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound` | Match; `Status.md`: Proof completed. |
| `tensor Wiener` (784) | `MemW0.fintype_tensor`, `fintype_tensor_wienerNorm_le` | Match; `Status.md`: Proof completed. |
| `W_0 Brascamp Lieb` (816) | `exists_brascamp_lieb_memW0` | Match; `Status.md`: Proof completed. |
| `P:schwartz-into-wiener` (872) | `SchwartzMap.memW0` | Match; `Status.md`: Proof completed. |
| `convolution vector` (897) | `memW0_convolutionAlongVector`, `fourier_convolutionAlongVector` | Match; `Status.md`: Proof completed. |

### `K` kernels

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `normalized function tuples` (914) | `normalizedFunctionTuples` (and the supporting `NormalizedFunctionTuple`) | Match; `Status.md`: Completed. The Lean encoding uses `eLpNorm` and Schwartz maps. |
| `cube Brascamp--Lieb` (931) | `cubeBrascampLiebForm` | Match; `Status.md`: Completed. |
| `prism Brascamp--Lieb` (967) | `prismBrascampLiebForm` | Match; `Status.md`: Completed. |

#### Theorem-like results

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `cube BL inequality` (939) | `cubeBLInequality` | Match; `Status.md`: Proof completed. |
| `prism BL inequality` (982) | `prismBLInequality` | Match; `Status.md`: Proof completed. |
| `simplification 1 prism` (1031) | `simplificationOnePrism` | Match; `Status.md`: Proof completed. |
| `single cancellative Cauchy-Schwarz` (1055) | `singlyCancellativeKernel_memW0`, `singlyCancellativeLift_memW0`, `singlyCancellativeCauchySchwarz_bound` | Match; `Status.md`: Proof completed. |
| `doubly cancellative Cauchy-Schwarz` (1116) | `doublyCancellativeKernel_memW0`, `doublyCancellativeLift_memW0`, `doublyCancellativeCauchySchwarz_bound` | Match in the Lean code. The `Status.md` mapping is stale: it lists `cauchySchwarzLift_memW0` instead of `doublyCancellativeLift_memW0`. |
| `Positivity K` (1176) | `positivityKernel_memW0`, `positivityKernel_nonnegative` | Match; `Status.md`: Proof completed. |
| `Monotonicity K` (1202) | `monotonicityK` | Match; `Status.md`: Proof completed. |

### `M` kernels

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `auto:prism-form-definition` (1244) | `prismForm` | Semantically present but Unmapped: no corresponding source entry is in `Status.md`. |

#### Theorem-like results

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `M to K` (1214) | `mToK`, `mToK_integrand_memW0`, `mToK_memW0`, `mToK_eLpNorm_one_le` | Match; `Status.md`: Proof completed. |
| `Positivity M` (1249) | `positivityM_memW0`, `positivityM_nonnegative` | Match; `Status.md`: Proof completed. |
| `Cauchy-Schwarz at k` (1266) | `cauchySchwarzKernel_memW0`, `cauchySchwarzLift_memW0`, `cauchySchwarzAtK_bound` | Match; `Status.md`: Proof completed. |
| `Cauchy-Schwarz at n-1` (1304) | `doublyCancellativeKernel_memW0`, `doublyCancellativeLift_memW0`, `cauchySchwarzAtNMinusOne_bound`, `cauchySchwarzAtNMinusOne` | Match in the Lean code. The `Status.md` entry repeats `cauchySchwarzLift_memW0`, which is the wrong lift theorem for this result. |

### Multiplicatively spaced monotone sequences

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `multiplicatively spaced monotone sequences` (1346) | `SpacedSequence`, `A` | Match; `Status.md`: Completed. |
| `Distance of spaced sequences` (1439) | `WithinSequenceDistance`, `SequenceDistance` | Match; `Status.md`: Completed. |
| `closed balls in A` (1578) | `sequenceDistanceBall` | Match; `Status.md`: Completed. |

#### Theorem-like results

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `Extension of sequences` (1355) | `extensionOfSequences` | Match; `Status.md`: Proof completed. |
| `Operations on spaced sequences` (1402) | `max_mem_A`, `smul_mem_A`, `shift_mem_A`, `sqrt_sq_add_sq_mem_A` | Match; `Status.md`: Proof completed. |
| `Properties of distance of sequences` (1447) | `sequenceDistance_zero_eq`, `sequenceDistance_comm`, `sequenceDistance_triangle`, `sequenceDistance_shift_le`, `sequenceDistance_smul`, `sequenceDistance_pow_two_smul_le` | Match; `Status.md`: Proof completed. |

### Gaussians

There are no labeled `definition` environments in this subsection; the
following are all theorem-like source items.

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `square root one minus Gaussian` (1587) | `sqrtOneMinusGaussian`, `continuous_sqrtOneMinusGaussian`, `sqrtOneMinusGaussian_lower`, `sqrtOneMinusGaussian_bounds` | Match; `Status.md`: Proof completed. |
| `Gaussian bump decay` (1627) | No `gaussianBumpDecay` theorem; only supporting constants/elementary estimates are present | Missing; `Status.md`: Todo. |
| `Elementary Gaussian properties` (1713) | `gaussian_memW0`, `gaussian_fourier_fixed` are present; `gaussianRescale_convolution` and `gaussianRescale_fourier` are absent | Partial; `Status.md` lists all four names, but only two public theorem declarations were found. |
| `poisson to abel` (1785) | `poissonKernel`, `poissonKernel_fourier` | Match; `Status.md`: Proof completed. |
| `auxiliary function B` (1822) | `auxiliaryFunctionB_properties` (with the supporting `B` definitions) | Match; `Status.md`: Proof completed. |
| `square root of Gaussian decay` (1946) | No `sqrtGaussianDecay` theorem; supporting `sqrtGaussianKernel` definitions and a continuity result are present | Missing; `Status.md`: Todo. |

### Bumps and their estimates

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `standard bump` (2185) | `standardBumpFinite`, `standardBump`, `standardBumpRescale` | Match as definitions; `Status.md`: Completed. The source properties proposition below is separate and is missing. |

#### Theorem-like results

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `lem:smoothdecay` (2062) | None | Missing; `Status.md`: Todo. |
| `lem: min and bracket` (2102) | `min_and_bracket` | Match; `Status.md`: Proof completed. |
| `lem:smoothdecay2` (2115) | None | Missing; `Status.md`: Todo. |
| `mean value bump estimate 2` (2138) | None | Missing; `Status.md`: Todo. |
| `standard bump properties` (2201) | None | Missing; `Status.md`: Todo. |
| `compare brackets` (2264) | `compare_brackets` | Match; `Status.md`: Proof completed. |
| `two bump estimate` (2279) | None | Missing; `Status.md`: Todo. |
| `orthogonal domination` (2311) | None | Missing; `Status.md`: Todo. |
| `orthogonal decay` (2348) | None | Missing; `Status.md`: Todo. |
| `bump triangle` (2365) | `bump_triangle` | Match; `Status.md`: Proof completed. |
| `Gaussian domination` (2393) | None | Missing; `Status.md`: Todo. |
| `diagonal square root` (2412) | `diagonalSquareRootFrequency` and `diagonalSquareRoot` definitions | Partial: the supporting kernel definition exists, but the source proposition (`W_0` membership and decay estimate) is missing; `Status.md` currently maps the proposition to the definition. |
| `constant diagonal square root` (2467) | `C_diagonalSquareRoot` definition only | Missing as a theorem: the source bound lemma is absent. |
| `derivative of diagonal square root` (2502) | None | Missing; `Status.md`: Todo. |
| `constant derivative diagonal square root` (2636) | `C_derivativeDiagonalSquareRoot` definition only | Missing as a theorem: the source bound lemma is absent. |
| `L:gaussian-estimate` (2666) | None | Missing; `Status.md`: Todo. |
| `L:gaussian-bump-estimate` (2682) | None | Missing; `Status.md`: Todo. |
| `constant gaussian bump estimate` (2700) | `C_gaussianBumpEstimate` definition only | Missing as a theorem: the source bound lemma is absent. |
| `L:derivative-estimate-for-G` (2719) | None | Missing; `Status.md`: Todo. |
| `L:faa-di-bruno` (2744) | None | Missing; `Status.md`: Todo. |
| `constant faa di bruno` (2794) | `C_faaDiBruno` definition only | Missing as a theorem: the source bound lemma is absent. |
| `L:second-gaussian-estimate` (2820) | None | Missing; `Status.md`: Todo. |
| `constant second gaussian estimate` (2855) | `C_secondGaussianEstimate` definition only | Missing as a theorem: the source bound lemma is absent. |
| `L:gaussian-bump-decomposition` (2881) | Supporting `fourScaleGaussian...` definitions exist, but no public theorem | Partial at the implementation level; source lemma missing. |
| `four scale Gaussian kernel` (2916) | `C_fourScaleGaussianKernel` definition only | Missing as a theorem; `Status.md`: Todo. |
| `constant four scale Gaussian kernel` (2946) | `C_fourScaleGaussianKernel` definition only | Missing as a theorem: the source bound lemma is absent. |
| `mean four scale Gaussian kernel` (2963) | `C_meanFourScaleGaussianKernel` definition only | Missing as a theorem; `Status.md`: Todo. |
| `constant mean four scale Gaussian kernel` (3014) | `C_meanFourScaleGaussianKernel` definition only | Missing as a theorem: the source bound lemma is absent. |

## The main argument

### The sandwich kernel

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `geometric parameters` (3037) | `GeometricParameters`, `sequencePairDistance`, `geometricDelta` | Match; `Status.md`: Completed. |
| `auto:unitary-matrices-definition` (3044) | `W` plus the supporting continuous-linear equivalences | Match semantically but Unmapped. |
| `double sequence of 2D functions` (3053) | `DoubleSequence`, `MemDoubleSequence` | Match; `Status.md`: Completed. |
| `kernel sequences` (3066) | `KernelSequence`, `MemKernelSequence`, `kernelSequenceSeminorm` | Match in intended role; `Status.md`: Completed. The seminorm is encoded as an `ENNReal` supremum rather than a real-valued supremum. |
| `2D Gaussians` (3079) | `twoDimensionalGaussian`, `gammaGaussian` | Match; `Status.md`: Completed. |
| `sandwich kernel` (3090) | `sandwichKernel` | Match; `Status.md`: Completed. |
| `auto:Gaussian-difference-kernel-definition` (3100) | `gaussianDifference` | Match semantically but Unmapped. |

#### Theorem-like results

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `telescoping terms` (3105) | None; `aux_product_telescope` is only an algebraic helper | Missing; `Status.md`: Todo. |
| `positive terms` (3127) | None | Missing; `Status.md`: Todo. |

### Multipliers `H`, `L`, `N`

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `square root Gaussian difference` (3142) | `squareRootGaussianDifference` | Match; `Status.md`: Completed. |
| `s multiplier` (3148) | `sMultiplier` | Match; `Status.md`: Completed. |
| `H multiplier` (3177) | `hMultiplier` | Match; `Status.md`: Completed. |
| `auto:L-kernel-definition` (3225) | `lMultiplierAtScale` | Match semantically but Unmapped. |
| `L multiplier` (3289) | `multiplierIndexSet`, `lMultiplier` | Match; `Status.md`: Completed. |
| `summation-definition` (3316) | `sumOverMultiplierIndex` | Match; `Status.md`: Completed. |
| `N multiplier` (3401) | `sigmaMultiplier`, `nMultiplier` | Match; `Status.md`: Completed. |

#### Theorem-like results

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `square root Gaussian difference W0` (3165) | No public `squareRootGaussianDifference_memW0` or `sMultiplier_memW0` theorem | Missing; `Status.md`: Todo. |
| `H-in-X` (3187) | None | Missing; `Status.md`: Todo. |
| `H vanishing` (3195) | None | Missing; `Status.md`: Todo. |
| `H vanishing integral` (3213) | None | Missing; `Status.md`: Todo. |
| `L:F_t` (3232) | None | Missing; `Status.md`: Todo. |
| `L:ft-infty` (3260) | None | Missing; `Status.md`: Todo. |
| `sum L multiplier convergence-L1` (3325) | None | Missing; `Status.md`: Todo. |
| `sandwich sums L1` (3347) | None | Missing; `Status.md`: Todo. |
| `prism sum le sum prism-L1` (3373) | None | Missing; `Status.md`: Todo. |
| `auto:N-kernel-well-definedness` (3418) | None | Missing and Unmapped. |

### Gaussian domination

All nine source environments in this subsection are theorem-like results.

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `H kernel estimate Gaussian domination` (3435) | Supporting constants and auxiliary estimates in `GaussianDomination.lean`, but no `hKernelEstimateGaussianDomination` theorem | Missing; `Status.md`: Todo. |
| `constant H kernel estimate Gaussian domination` (3548) | `C_hKernelEstimateGaussianDomination` definition only | Missing as a theorem. |
| `H kernel derivative estimate Gaussian domination` (3564) | Supporting constants/auxiliary estimates, but no `hKernelDerivativeEstimateGaussianDomination` theorem | Missing; `Status.md`: Todo. |
| `constant H kernel derivative estimate Gaussian domination` (3619) | `C_hKernelDerivativeEstimateGaussianDomination` definition only | Missing as a theorem. |
| `Gaussian domination combined` (3639) | Constants and auxiliary witness infrastructure, but no `gaussianDominationCombined` theorem | Missing; `Status.md`: Todo. |
| `Gauss domination case 1` (3673) | `C_gaussDominationCase1` definition only | Missing as a theorem; `Status.md`: Todo. |
| `Gauss domination case 2` (3810) | `C_gaussDominationCase2` definition only | Missing as a theorem; `Status.md`: Todo. |
| `Gauss domination case 3` (3967) | `C_gaussDominationCase3` definition only | Missing as a theorem; `Status.md`: Todo. |
| `Gauss domination constant` (4104) | None | Missing; `Status.md`: Todo. |

The current constants do not yet match the new source constants.  Pass 3 uses
`C_{combined,0}=28`, `C_{combined,1}=2`, and
`C_{combined,2}=2^153`; the current code uses a cardinality constant of 30
and `(100 : R)^100` for the combined constant.  The case constants are
defined, but their source estimates and the final common-constant lemma are
not formalized.

### Main induction

#### Definitions

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `induct positive terms` (4166) | `InductPositiveTerms` | Match in intended statement; `Status.md`: Completed. |
| `vanishing diagonal` (4177) | `VanishingDiagonal` | Match in intended statement; `Status.md`: Completed. |
| `diagonal band` (4189) | `DiagonalBand` | Match in intended statement; `Status.md`: Completed. |
| `increase data` (4203) | `IncreaseData`, with `aux_increaseDataKernel` | Match in intended statement; `Status.md`: Completed. The current `natAbs` expression for the first index coordinate corresponds to the pass-3 `|\iota_0|` formula. |

#### Theorem-like results

| Pass-3 label (line) | Current Lean representation | Audit |
|---|---|---|
| `vanishing diagonal implies induct positive terms` (4234) | No theorem; only `C_vanishingDiagonalImpliesInductPositiveTerms` and an auxiliary admissibility lemma | Missing; `Status.md`: Todo. |
| `diagonal band implies vanishing diagonal` (4254) | None | Missing; `Status.md`: Todo. |
| `vanishing kernel integral` (4267) | None | Missing; `Status.md`: Todo. |
| `increase data implies diagonal band` (4299) | No theorem; only `C_increaseDataImpliesDiagonalBand` | Missing, and the constant helper is stale: the pass-3 nonterminal bound uses `2^15 sqrt(C_{combined,2}) sqrt(C)`, whereas the current helper uses `2^10 sqrt(C)`. |
| `induct positive terms imply increase data` (4388) | No theorem; only `C_inductPositiveTermsImplyIncreaseData` | Missing, and the current constant uses the old Gaussian-domination values (`30` and `100^100`) instead of the pass-3 values (`28` and `2^153`). |
| `constant induct positive terms imply increase data` (4446) | None | Missing as a theorem. |
| `P:C_k-induction` (4461) | No theorem; only `C_inductPositiveTermsByInduction` | Missing, and the recursion is stale: the pass-3 interior step has the factor `2^15 sqrt(C_{combined,2})`, while the current definition uses `2^10` and omits that factor. |
| `P:better-induction` (4486) | No `betterInduction` theorem; current `C_betterInduction` is an old constant definition | Mismatch in both label meaning and statement. In pass 3 this label is a lemma bounding the recursively defined `C_k`; in pass 0 it denoted the better-induction proposition. The current code follows the old role/formula and does not formalize the pass-3 lemma. |
| `induct positive terms theorem` (4526) | No theorem; only `C_inductPositiveTermsTheorem` | Missing, and the current constant uses the old `(2^12 sqrt(C)+sqrt 2)^2` formula. Pass 3 uses `(2^17 sqrt(C_{combined,2} C_{induct...})+sqrt 2)^2`. |
| `constant induct positive terms theorem` (4539) | None | Missing as a theorem. |

## Status and mapping issues found

These are reported for the audit only; `Status.md` was not changed.

1. `Status.md` omits the eight pass-3 auto-labeled environments listed above:
   `auto:local-supremum-measurability`,
   `auto:Wiener-space-definition`,
   `auto:convolution-along-vector-definition`,
   `auto:prism-form-definition`,
   `auto:unitary-matrices-definition`,
   `auto:Gaussian-difference-kernel-definition`,
   `auto:L-kernel-definition`, and
   `auto:N-kernel-well-definedness`.
2. `Status.md` omits the eleven new pass-3 constant lemmas: `constant diagonal
   square root`, `constant derivative diagonal square root`, `constant
   gaussian bump estimate`, `constant faa di bruno`, `constant second
   gaussian estimate`, `constant four scale Gaussian kernel`, `constant mean
   four scale Gaussian kernel`, `constant H kernel estimate Gaussian
   domination`, `constant H kernel derivative estimate Gaussian domination`,
   `constant induct positive terms imply increase data`, and `constant induct
   positive terms theorem`. (The source count is eleven labels; the wrapped list
   above contains all eleven.)
3. The `Cauchy-Schwarz at n-1` status entry maps to the `k`-level lift theorem
   instead of the current `doublyCancellativeLift_memW0` declaration.
4. The pass-3 label `P:better-induction` has been repurposed from the old
   pass-0 proposition to a constant lemma.  The current status/name mapping
   `betterInduction` therefore cannot be carried over unchanged.
5. The two status labels `A_def` and `thm:nct main real` do not occur in this
   report because they belong to the Introduction, which was explicitly
   excluded from this audit.
