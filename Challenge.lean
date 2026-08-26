/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Floris van Doorn
-/

module

public import Mathlib


/-!
# Comparactor Challenge File

In this file we formulate the main theorems without proofs.
We also copy the definitions in `Defs`.
-/


namespace nCT

@[expose] public noncomputable section

open MeasureTheory Set ENNReal

variable {n : ℕ}

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/--
**Definition (Multiple ergodic average).**

Let $\mathbf{f}=(f_j)_{j\in [n)}$ be an $n$-tuple of complex-valued functions
on $X$ and let $(T_j)_{j\in [n)}$ be an $n$-tuple of maps $X\to X$. For every positive integer
$N$ and every $x\in X$, define the multiple ergodic average
$$M_{N}(\mathbf{f})(x) = N^{-1} \sum_{0\le i<N} \prod_{0\le j<n} f_j(T_j^i x).$$

*Implementation note:* The Lean formulation also allows $N = 0$
where the value is $0$ by junk value conventions.
-/
def multipleErgodicAverage (f : Fin n → X → ℂ) (T : Fin n → X → X) (N : ℕ) (x : X) :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, ∏ j : Fin n, (f j) ((T j)^[i] x)

/--
**Definition ($r$-variation seminorms for sequences on the positive integers).**

Define
$$\|a\|_{V_{r}(B)} = \sup_{J\in\mathbb{N}}\ \sup_{\substack{t_0<\cdots<t_J,\\
t_j\in \mathbb{N}_{\ge 1}\;
\text{for all}\;j\in [J+1)}} \Big(\sum_{j\in[J)} \|a(t_{j+1})- a(t_{j})\|^r\Big)^{1/r}.$$
Note we will only use this for $r\ge 1$.

*Implementation note:* We prefer `AddCommGroup` over `SeminormedAddCommGroup` here because
we want to use an `ENNReal`-valued norm. It is more convenient to use `MeasureTheory.eLpNorm`
and avoid the type `MeasureTheory.Lp`.
-/
def variationSeminorm {B : Type*} [AddCommGroup B]
    (enorm : B → ℝ≥0∞) (r : ℝ) (a : ℕ → B) :=
  ⨆ (J : ℕ) (t : {t : Fin (J + 1) → ℕ // StrictMono t ∧ ∀ j, 0 < t j}),
    (∑ j : Fin J, enorm (a (t.1 j.succ) - a (t.1 j.castSucc)) ^ r) ^ r⁻¹

/-- Real Euclidean space $\mathbb{R}^n$ -/
scoped notation:max "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- $\chi_{(t)}(x)=t^{-1}\chi(t^{-1}x)$ -/
def rescale (χ : ℝ → ℝ) (t : ℝ) (x : ℝ) := t⁻¹ * χ (t⁻¹ * x)

/-- $i$th standard unit vector -/
abbrev unitVector (i : Fin n) : ℝ^n := EuclideanSpace.single i (1 : ℝ)

@[inherit_doc unitVector]
scoped notation "𝐞" => unitVector

/-- Characteristic function of a set of real numbers as a real-valued function. -/
scoped notation "𝟙" => indicator (f := (1 : ℝ → ℝ))

/--
**Definition (Twisted average).**

Let $n\in\mathbb{N}$. For an $n$-tuple of real-valued functions
$\mathbf f = (f_i)_{i\in \mathbb{N}, i<n}$ on $\mathbb{R}^n$, a function
$\chi:\mathbb{R}\to\mathbb{R}$
and $x\in\mathbb{R}^n$ denote
$$A(\chi,\mathbf f)(x) = \int_{\mathbb{R}} \chi(s)\Big(\prod_{i\in [n)} f_i(x+se_i)\Big)\,ds,$$
whenever the integrand is measurable and integrable.
Also set $A_t(\chi,\mathbf{f})=A(\chi_{(t)},\mathbf{f})$,
where $\chi_{(t)}(x)=t^{-1}\chi(t^{-1}x)$ for $t>0$.

*Implementation note:* The Lean formulation uses the Bochner integral, which takes the
junk value $0$ when the integrand is not integrable.

See also `nCT.rescaledTwistedAverage`.
-/
def twistedAverage (χ : ℝ → ℝ) (f : Fin n → ℝ^n → ℝ)
    (x : ℝ^n) := ∫ s, χ s * ∏ i, f i (x + s • 𝐞 i)

/--
**Definition (Twisted average).**

Let $n\in\mathbb{N}$. For an $n$-tuple of real-valued functions
$\mathbf f = (f_i)_{i\in \mathbb{N}, i<n}$ on $\mathbb{R}^n$, a function
$\chi:\mathbb{R}\to\mathbb{R}$
and $x\in\mathbb{R}^n$ denote
$$A(\chi,\mathbf f)(x) = \int_{\mathbb{R}} \chi(s)\Big(\prod_{i\in [n)} f_i(x+se_i)\Big)\,ds,$$
whenever the integrand is measurable and integrable.
Also set $A_t(\chi,\mathbf{f})=A(\chi_{(t)},\mathbf{f})$,
where $\chi_{(t)}(x)=t^{-1}\chi(t^{-1}x)$ for $t>0$.

See also `nCT.twistedAverage`.
-/
def rescaledTwistedAverage (t : ℝ) (χ : ℝ → ℝ) (f : Fin n → ℝ^n → ℝ) :=
    twistedAverage (rescale χ t) f

@[inherit_doc rescaledTwistedAverage]
scoped notation "𝐀" => rescaledTwistedAverage

open scoped SchwartzMap

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
preserving transformations on $X$,
and let $\mathbf{f}=(f_j)_{j\in [n)}$ be an $n$-tuple
of complex-valued measurable functions on $X$
such that $\|f_j\|_{L^{2n}(X)}<\infty$ for all $j\in[n)$.
Then $M_N(\mathbf{f})$ is measurable with
finite $L^2(X)$ norm for every
positive integer $N$ and
$$
 \| M_{N} (\mathbf{f}) \|_{V_{r}(L^2(X))}
\le C_{n,r}
 \prod_{j\in [n)} \|f_j\|_{2n},
$$
where the constant is defined in `nCT.C_main_ergodic_theorem`.
-/
theorem main_ergodic_theorem (hn : 2 ≤ n) {r : ℝ} (hr : 2 ^ (n - 1) < r ∨ (n = 2 ∧ 2 ≤ r))
    [SigmaFinite μ] {T : Fin n → X → X} (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hT' : ∀ i j x, (T i) (T j x) = (T j) (T i x)) {f : Fin n → X → ℂ}
    (hf : ∀ i, MemLp (f i) (2 * n) μ) :
    ∀ N, MemLp (multipleErgodicAverage f T N) 2 μ ∧
    variationSeminorm (eLpNorm · 2 μ) r (multipleErgodicAverage f T)
      ≤ C_main_ergodic_theorem n r * ∏ i, eLpNorm (f i) (2 * n) μ :=
  sorry

/--
**Theorem (Main twisted theorem).**

Let $n\ge 2$ be an integer. For every $J\in\mathbb{N}$,
positive real numbers $t_0<t_1<\cdots<t_J$, and every
$n$-tuple of real-valued Schwartz functions
${\mathbf f}=(f_i)_{i\in[n)}$ satisfying
$$\|f_i\|_{2^{\min(n,i+2)}}=1$$
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
    {f : Fin n → 𝓢(ℝ^n, ℝ)} (hf : ∀ i, eLpNorm (f i) (2 ^ min n (i + 2)) volume = 1) :
    ∑ j : Fin J, eLpNorm (𝐀 (t (j.succ))  (𝟙 (Icc 0 1)) (f ·)
      - 𝐀 (t j.castSucc) (𝟙 (Icc 0 1)) (f ·)) 2 volume ^ 2
        ≤ 2 ^ 666 * J ^ (1 - (2 : ℝ) ^ (-(n : ℝ) + 2)) :=
  sorry

end

end nCT
