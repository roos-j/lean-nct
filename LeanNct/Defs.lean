/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/

module

public import Mathlib

/-!
# Main definitions

In this file we give the definitions needed to state the main theorems:

* `nCT.multipleErgodicAverage`
* `nCT.rescaledTwistedAverage`

These definitions were human-generated and match the mathematical content
of the blueprint's definitions.
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

See also [`nCT.rescaledTwistedAverage`].
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

See also [`nCT.twistedAverage`].
-/
def rescaledTwistedAverage (t : ℝ) (χ : ℝ → ℝ) (f : Fin n → ℝ^n → ℝ) :=
    twistedAverage (rescale χ t) f

@[inherit_doc rescaledTwistedAverage]
scoped notation "𝐀" => rescaledTwistedAverage

end

end nCT
