/-
Copyright (c) 2026 Joris Roos, Polona Durcik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Polona Durcik
-/

import Mathlib
import LeanNct.Preliminaries.Notation
import LeanNct.Reduction.TwistedAverages
import LeanNct.Reduction.FinalReduction

/-!
# Introduction

The twisted averages and the main twisted theorem from the introduction of the manuscript.
-/

namespace Codex.Introduction

open MeasureTheory Set
open scoped BigOperators ENNReal

/--
\begin{definition}[Twisted averages]
Let $n\geq 1$. For an $n$-tuple of real-valued Schwartz functions
$\mathbf f = (f_0,f_1,\dots,f_{n-1})$ on $\R^n$, a bounded measurable
function $\chi$ and $x\in\mathbb{R}^n$ denote
\begin{equation}\label{A_def}
A(\chi,\mathbf f)(x) = \int_{\mathbb{R}} \chi(s)\Big(\prod_{i\in [n)} f_i(x+se_i)\Big)\,ds.
\end{equation}
\end{definition}
-/
noncomputable def twistedAverage {n : ℕ} (χ : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  Codex.Reduction.TwistedAverages.twistedAverage χ f

/--
\begin{definition}[Twisted averages]
Also, $A_t(\chi,\mathbf{f})=A(\chi_{(t)},\mathbf{f})$, where $\chi_{(t)}(x)=t^{-1}\chi(t^{-1}x)$.
\end{definition}
-/
noncomputable def twistedAverageAtScale {n : ℕ} (t : ℝ) (χ : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  Codex.Reduction.TwistedAverages.twistedAverageAtScale t χ f

/--
\begin{theorem}[Main twisted theorem]\label{thm:nct main real}
    Let $n\ge 2$ be an integer. There exists a $C\in (0,\infty)$ such that the following holds.
    For every positive integer $J$ and positive real numbers $t_0<t_1<\cdots < t_J$,
    for every $n$-tuple of Schwartz functions ${\mathbf f}=(f_i)_{i \in [n)}$
    with \[ \|f_{i}\|_{2^{i+\min(n-i,2)}}=1 \] for $i\in [n)$,
    \begin{equation}\label{e:ncommuting_real}
    \sum_{j \in [J)} \|A_{t_{j + 1}}(\mathbf{1}_{[0,1]},\mathbf{f}) -
      A_{t_{j}}(\mathbf{1}_{[0,1]},\mathbf f)\|_{{L}^2(\R^n)}^2
      \leq C J^{1-2^{-n+2}}.
    \end{equation}
\end{theorem}
-/
theorem mainTwistedTheorem {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ), 0 < J → ∀ (t : Fin (J + 1) → ℝ),
      StrictMono t → (∀ j, 0 < t j) →
      ∀ f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ,
        (∀ i, eLpNorm (f i) ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2)) volume = 1) →
        ∑ j : Fin J, eLpNorm
            (fun x ↦ twistedAverageAtScale (t j.succ)
                ((Icc (0 : ℝ) 1).indicator fun _ ↦ (1 : ℝ))
                (fun i x ↦ f i x) x -
              twistedAverageAtScale (t j.castSucc)
                ((Icc (0 : ℝ) 1).indicator fun _ ↦ (1 : ℝ))
                (fun i x ↦ f i x) x)
            2 volume ^ 2 ≤
          ENNReal.ofReal C * ENNReal.ofReal
            ((J : ℝ) ^ (1 - (2 : ℝ) ^ (-(n : ℝ) + 2))) := by
  simpa only [twistedAverageAtScale,
    Codex.Reduction.FinalReduction.unitIntervalIndicator] using
    Codex.Reduction.FinalReduction.mainTwistedTheoremReduction hn

end Codex.Introduction
