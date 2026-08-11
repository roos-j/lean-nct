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

The Lean formalization therefore uses the directly justified cardinality
constant `C_gaussianDominationCombinedCard = 30` rather than the blueprint's
`28`. The blueprint text is left unchanged. A smaller count would require a
new coefficient-sensitive compression argument, which is not provided by the
displayed proof.

## `Gauss domination case 1`: leading factor two

Reported: 2026-08-11 11:16:34 EDT. Source: `blueprint/blueprint.tex`,
lines 4088--4100 and 4518--4522.

The direct formal case-one assembly gives twice the displayed case-one
constant: the orientation branches are combined by an absolute bound with a
leading factor `2`. Accordingly, Lean defines
`C_gaussDominationCase1` as `2` times the product printed in the blueprint
and proves the corresponding bound `C_gaussDominationCase1 < 2^118`, rather
than the displayed `< 2^117`. The common domination constant remains
`2^153`, so no later combined constant changes. The blueprint text is left
unchanged.
