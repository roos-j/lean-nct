/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

module

public import LeanNct.Defs
import LeanNct.Codex.RealToErgodic

/-!
# Main theorems

In this file we formulate the main theorems

* `nCT.main_ergodic_theorem` -- the main ergodic theorem for multiple commuting transformations
* `nCT.main_twisted_theorem` -- the main real-variable harmonic analysis theorem

The formulations use the definitions and notations in `Defs.lean`.
Some notational shorthands have been introduced to increase readability and
simplify comparison with the on-paper formulations.

This file was entirely human-written. The proofs are contained in the `Codex` directory.
-/

namespace nCT

@[expose] public noncomputable section

open MeasureTheory Set ENNReal
open scoped SchwartzMap

variable {n : ℕ}

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The constant appearing in the main ergodic theorem, `nCT.main_ergodic_theorem`. -/
def C_main_ergodic_theorem (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal <| if n = 2 then 2 ^ 344
  else 2 ^ (4 * n + 337) * ((r / (r - (2 : ℝ) ^ ((n : ℝ) - 1))) ^ r⁻¹)

/-- The constant appearing in the main ergodic theorem is finite. -/
theorem C_main_ergodic_theorem_finite (n : ℕ) (r : ℝ) : C_main_ergodic_theorem n r < ∞ :=
  ENNReal.ofReal_lt_top

/--
**Theorem (Main ergodic theorem).**

Let $n\ge 2$ be an integer and let $r>2^{n-1}$, or $r\ge 2$ if $n=2$.
Let $(X,\Sigma,\mu)$ be a $\sigma$-finite measure space,
let $(T_j)_{j\in [n)}$ be an $n$-tuple of mutually commuting measure
preserving transformations on $X$, and let $\mathbf{f}=(f_j)_{j\in [n)}$ be an $n$-tuple
of complex-valued measurable functions on $X$
such that $\|f_j\|_{L^{2n}(X)}<\infty$ for all $j\in[n)$. Then $M_N(\mathbf{f})$ is measurable
with finite $L^2(X)$ norm for every positive integer $N$ and
$$
 \| M_{N} (\mathbf{f}) \|_{V_{r}(L^2(X))}
\le C_{\text{Main ergodic theorem},n,r}
 \prod_{j=0}^{n-1} \|f_j\|_{2n},
$$
where the constant is defined in [`nCT.C_main_ergodic_theorem`].
-/
theorem main_ergodic_theorem (hn : 2 ≤ n) {r : ℝ} (hr : 2 ^ (n - 1) < r ∨ (n = 2 ∧ 2 ≤ r))
    [SigmaFinite μ] {T : Fin n → X → X} (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hT' : ∀ i j x, (T i) (T j x) = (T j) (T i x)) {f : Fin n → X → ℂ}
    (hf : ∀ i, MemLp (f i) (2 * n) μ) :
    ∀ N, MemLp (multipleErgodicAverage f T N) 2 μ ∧
    variationSeminorm (eLpNorm · 2 μ) r (multipleErgodicAverage f T)
      ≤ C_main_ergodic_theorem n r * ∏ i, eLpNorm (f i) (2 * n) μ :=
  Codex.aux_nCT_main_ergodic_theorem hn hr hT hT' hf

/--
**Theorem (Main twisted theorem).**

Let $n\ge 2$ be an integer. For every $J\in\mathbb{N}$,
positive real numbers $t_0<t_1<\cdots<t_J$, and every
$n$-tuple of real-valued Schwartz functions
${\mathbf f}=(f_i)_{i\in[n)}$ satisfying
$$\|f_i\|_{2^{i+\min(n-i,2)}}=1$$
for $i\in[n)$, we have
$$\sum_{j\in[J)}\|A_{t_{j+1}}(\mathbf 1_{[0,1]},\mathbf f) -
  A_{t_j}(\mathbf 1_{[0,1]},\mathbf f)\|_{L^2(\mathbb{R}^n)}^2
\le C_{\text{Main twisted theorem}}J^{1-2^{-n+2}},
$$
where
$C_{\text{Main twisted theorem}}=2^{666}.$

*Implementation notes:* 1. The Lean formulation of $L^p$ norms here (`MeasureTheory.eLpNorm`) uses
the lower Lebesgue integral, which exists regardless of measurability of the integrated function.
This differs from standard mathematical convention. In this theorem, this does not make
a difference, because the integrated function
$A_{t_{j+1}}(\mathbf 1_{[0,1]},\mathbf f) - A_{t_j}(\mathbf 1_{[0,1]},\mathbf f)$ is again Schwartz
for every $j\in [J)$, and in particular measurable with finite $L^2(\mathbb{R}^n)$ norm.
2. We allow $J = 0$ where the conclusion holds trivially.
-/
theorem main_twisted_theorem (hn : 2 ≤ n) {J : ℕ}
    {t : Fin (J + 1) → ℝ} (ht : ∀ i, 0 < t i) (ht' : StrictMono t)
    {f : Fin n → 𝓢(ℝ^n, ℝ)} (hf : ∀ i, eLpNorm (f i) (2 ^ (i + min (n - i) 2)) volume = 1) :
    ∑ j : Fin J, eLpNorm (𝐀 (t (j.succ))  (𝟙 (Icc 0 1)) (f ·)
      - 𝐀 (t j.castSucc) (𝟙 (Icc 0 1)) (f ·)) 2 volume ^ 2
        ≤ 2 ^ 666 * J ^ (1 - (2 : ℝ) ^ (-(n : ℝ) + 2)) :=
  Codex.aux_nCT_main_twisted_theorem hn ht ht' hf

end

end nCT
