/-
Copyright (c) 2026 Joris Roos, Polona Durcik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Polona Durcik
-/

import LeanNct.Preliminaries.Notation

/-!
# Twisted averages

The shared definitions from the introduction, placed below the reduction
modules so that the final reduction can prove the introductory theorem
without creating an import cycle.
-/

namespace Codex.Reduction.TwistedAverages

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/--
\begin{definition}[Twisted averages]
Let $n\geq 1$. For an $n$-tuple of real-valued Schwartz functions
$\mathbf f = (f_0,f_1,\dots,f_{n-1})$ on $\R^n$, a bounded measurable
function $\chi$ and $x\in\mathbb{R}^n$ denote
\begin{equation}\label{A_def}
A(\chi,\mathbf f)(x) = \int_{\mathbb{R}} \chi(s)
  \Big(\prod_{i\in [n)} f_i(x+se_i)\Big)\,ds.
\end{equation}
\end{definition}
-/
noncomputable def twistedAverage {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ ∫ s : ℝ, chi s * ∏ i,
    f i (x + s • WithLp.toLp 2 (Pi.single i (1 : ℝ)))

/--
\begin{definition}[Twisted averages]
Also, $A_t(\chi,\mathbf{f})=A(\chi_{(t)},\mathbf{f})$, where
$\chi_{(t)}(x)=t^{-1}\chi(t^{-1}x)$.
\end{definition}
-/
noncomputable def twistedAverageAtScale {n : ℕ} (t : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  twistedAverage (fun s ↦ t⁻¹ * chi (t⁻¹ * s)) f

/-- A positive, strictly increasing finite scale chain. -/
def TwistedScaleChain (J : ℕ) :=
  {t : Fin (J + 1) → ℝ // StrictMono t ∧ ∀ j, 0 < t j}

/-- The squared (L^2) jump energy of one finite scale chain. -/
noncomputable def twistedJumpEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (J : ℕ)
    (t : TwistedScaleChain J) : ℝ≥0∞ :=
  ∑ j : Fin J,
    eLpNorm
      (fun x ↦ twistedAverageAtScale (t.1 j.succ) chi f x -
        twistedAverageAtScale (t.1 j.castSucc) chi f x)
      2 volume ^ 2

/-- The finite-(J) (L^2) variation energy, written as a supremum over scale chains. -/
noncomputable def twistedVariationEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (J : ℕ) : ℝ≥0∞ :=
  ⨆ t : TwistedScaleChain J, twistedJumpEnergy chi f J t

/-- A strictly increasing finite chain of dyadic exponents. -/
def TwistedDyadicChain (J : ℕ) :=
  {k : Fin (J + 1) → ℤ // StrictMono k}

/-- The squared (L^2) jump energy along a dyadic scale chain. -/
noncomputable def twistedDyadicJumpEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (J : ℕ)
    (k : TwistedDyadicChain J) : ℝ≥0∞ :=
  ∑ j : Fin J,
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) chi f x -
        twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) chi f x)
      2 volume ^ 2

/-- The finite-(J) dyadic variation energy. -/
noncomputable def twistedDyadicVariationEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (J : ℕ) : ℝ≥0∞ :=
  ⨆ k : TwistedDyadicChain J, twistedDyadicJumpEnergy chi f J k

end

end Codex.Reduction.TwistedAverages
