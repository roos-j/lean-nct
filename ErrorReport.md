# Blueprint errors

## Resolved in pass 8 — mean-value bump constant

The prior report concerned `blueprint-pass5.tex`. It no longer applies to the
authoritative source: `blueprint/blueprint-pass8.tex`, lines 2297–2308, now
includes the Leibniz binomial coefficients and derives the weighted factor
$(1+(2\pi)^{-1})^N$. The Lean formalization has been updated to the pass-8
constant, so this is not an unresolved blueprint error.

## `prism sum le sum prism-L1`: nonnegative series may be infinite

The proposition in `blueprint.tex` assumes only that the symmetric partial
sums of `M_\iota` converge in $L^1$, but concludes an inequality with the
real-valued series $\sum_\iota |\Lambda_k(M_\iota)(\mathbf F)|$. That series
need not converge in $\mathbb R$: taking nonzero $f\in W_0$ and terms
$(-1)^h f/h$ along one horizontal index ray gives conditional $L^1$
convergence while the absolute prism-form series is harmonic. Therefore the
right-hand side must be interpreted as an extended nonnegative sum. The Lean
correction uses the supremum of the symmetric finite partial sums in
`ℝ≥0∞`, which may be infinite; the blueprint text is left unchanged.

## `Gaussian domination combined`: case-1 multiset cardinality

Reported: 2026-08-11 07:17:19 EDT.  Source: `blueprint/blueprint.tex`,
lines 4060 and 4188--4213.

The proof of the positive horizontal case asserts that its multiset
`\mathcal M_2` has at most 16 elements and hence that
`\mathcal M_1\sqcup\mathcal M_2` has at most 22. This is false for the
displayed construction. When `u(i)=0`, all six terms in the preceding
H-kernel package have orientation 0, and the construction creates four
`\mathcal M_2` terms per input term (24), plus one `\mathcal M_1` term per
input term (6), for a total of 30.

The Case-1 construction itself has the directly justified cardinality `30`,
rather than the blueprint's `28`. The shared formal cap is now
`C_gaussianDominationCombinedCard = 36`, because the independently displayed
Case-3 construction below requires 36 multiplicity-preserving slots. The
blueprint text is left unchanged. A smaller count would require a new
coefficient-sensitive compression argument, which is not provided by the
displayed proof.

## `Gauss domination case 1`: leading factor two

Reported: 2026-08-11 11:16:34 EDT. Source: `blueprint/blueprint.tex`,
lines 4088--4100 and 4518--4522.

The direct formal case-one assembly gives twice the displayed case-one
constant: the orientation branches are combined by an absolute bound with a
leading factor `2`. Accordingly, Lean defines
`C_gaussDominationCase1` as `2` times the product printed in the blueprint.
A sharper numerical estimate nevertheless proves the displayed bound
`C_gaussDominationCase1 < 2^117`; the common domination constant remains
`2^153`. The blueprint text is left unchanged.

## `Gauss domination case 2`: local U0 coefficient and label count

Reported: 2026-08-11 14:54:45 EDT. Source: `blueprint/blueprint.tex`,
lines 4298--4323 and 4339--4341.

For an orientation-zero H-package occurrence, the blueprint's displayed
three-bump/orthogonal-decay bound has leading coefficient
`8 C_{bump triangle,1,1,2,2} C_{two bump estimate,2,2}`. The checked Lean
argument establishes the same three displayed outputs with coefficient `9`
instead (a factor `9/8` loss). The later Gaussian-majorant step is sharper:
it gives a local coefficient `216`, which is at most the displayed public
case-two coefficient `3*2^7 = 384`. Thus `C_gaussDominationCase2` and the
common `2^153` bound remain unchanged.

The claim `#\mathcal B\le14` is valid only in the nonzero physical-
orientation branch. In the canonical orientation-zero H package all six
occurrences have orientation zero, and each produces three active labels,
giving 18. Lean therefore uses the already-safe padded `range 30` witness;
the blueprint text is left unchanged.

## `Gauss domination case 3`: local coefficient and multiset cardinality

Reported: 2026-08-11 16:46:00 EDT. Source: `blueprint/blueprint.tex`,
lines 4444--4479.

For an orientation-zero H-package occurrence, the displayed three-bump and
orthogonal-decay estimate has leading coefficient
`8 C_{bump triangle,1,1,2,2} C_{two bump estimate,2,2}`. The checked Lean
split gives the same three products with coefficient `9` instead. This does
not alter `C_gaussDominationCase3`: the subsequent Gaussian majorant has
factor `8`, and `9*8 = 72 <= 2^7`.

The claimed `#\mathcal B\le28` also cannot be justified by the displayed
construction when the physical orientation is zero. The canonical H package
then has six orientation-zero occurrences; each of the two central rho
scales produces three multiplicity-preserving outputs, for 36 slots. The
attempted max-scale collection drops repeated terms and is not
coefficient-valid. Lean therefore uses the shared cardinality cap `36`.
The blueprint text is left unchanged.

## `constant induct positive terms imply increase data`: cardinality bound

Reported: 2026-08-11 16:46:00 EDT. Source: `blueprint/blueprint.tex`,
lines 4887--4897.

The manuscript evaluates this constant with the displayed cardinality 28.
With the verified shared Lean cap 36, the defining value is
`2^10 * 36 * 9 * 2^153 = 324 * 2^163`, which is not less than `2^171`.
(The prior shared cap 30 already also exceeded that bound.) The direct
replacement bound is `< 2^172`, a factor-two relaxation. The blueprint text
is left unchanged.

## `constant induct positive terms theorem`: final constant bound

Reported: 2026-08-11 17:37:33 EDT. Source: `blueprint/blueprint.tex`,
lines 4983--5006.

With the verified shared cap `C_gaussianDominationCombinedCard = 36`, the
aligned defining value has
`C_inductPositiveTermsImplyIncreaseData = 324 * 2^163`. Hence the leading
summand in the final constant is
`2^17 * sqrt(2^153 * 324 * 2^163) = 18 * 2^175`, whose square is
`324 * 2^350 = (324 / 256) * 2^358 > 2^358`. Thus the manuscript bound
`< (253 / 256) * 2^358 < 2^358` is false; Lean proves `< 2^359`, a
factor-two relaxation. The blueprint text is left unchanged.
