import LeanNct.Preliminaries.BumpsAndEstimates

/-!
# Windows and pairs

Formalization of the ``Windows and pairs'' subsection of the reduction argument.
-/

namespace Codex.Reduction.WindowsAndPairs

open scoped FourierTransform Real

noncomputable section

/--
\begin{definition}[$(c,N)$-window]\label{def:cn-window}
Let $c > 0$, $N\in\mathbb{N}$. A {\em $(c,N)$-window} is a Schwartz function
$\phi:\mathbb{R}\to\mathbb{R}$ such that $\widehat\phi$ is real-valued, takes values in
$[0,1]$, is supported in $[-1,1]$, equals $1$ on $[-1/2,1/2]$, and for all
$\xi\in[-1,1]$ and $m\leq N$,
\[
  |\widehat\phi^{(m)}(\xi)|\leq c.
\]
\end{definition}
-/
def cnWindow (c : ℝ) (N : ℕ) (φ : SchwartzMap ℝ ℝ) : Prop :=
  0 < c ∧
  (∀ ξ : ℝ, ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧
    FourierTransform.fourier (fun x : ℝ => (φ x : ℂ)) ξ = r) ∧
  Function.support (FourierTransform.fourier (fun x : ℝ => (φ x : ℂ))) ⊆
    Set.Icc (-1 : ℝ) 1 ∧
  (∀ ξ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
    FourierTransform.fourier (fun x : ℝ => (φ x : ℂ)) ξ = 1) ∧
  ∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ∀ m : ℕ, m ≤ N →
    ‖iteratedDeriv m (FourierTransform.fourier (fun x : ℝ => (φ x : ℂ))) ξ‖ ≤ c

/--
\begin{definition}[$(c,N)$-pair]\label{def:cpair}
Let $c > 0$, $N\in\mathbb{N}$. A pair $(\phi_0,\phi_1)$ of $(c,N)$-windows is a
{\em $(c,N)$-pair} if
\[
(\widehat{\phi_0})^2+(1-\widehat{\phi_1})^2=1.
\]
\end{definition}
-/
def cPair (c : ℝ) (N : ℕ) (φ₀ φ₁ : SchwartzMap ℝ ℝ) : Prop :=
  cnWindow c N φ₀ ∧ cnWindow c N φ₁ ∧
    ∀ ξ : ℝ,
      FourierTransform.fourier (fun x : ℝ => (φ₀ x : ℂ)) ξ ^ 2 +
        (1 - FourierTransform.fourier (fun x : ℝ => (φ₁ x : ℂ)) ξ) ^ 2 = 1

/-- The order fixed in Definition \ref{def:unipair}. -/
def N_uniPair : ℕ := 3

/-- The derivative constant fixed in Definition \ref{def:unipair}. -/
def C_uniPair : ℝ := 2 ^ 15

/--
\begin{definition}[Universal pair]\label{def:unipair}
Set $N_{\ref{def:unipair}}=3$ and $C_{\ref{def:unipair}}=2^{15}$.
A universal pair is a $(C_{\ref{def:unipair}},N_{\ref{def:unipair}})$-pair.
\end{definition}
-/
def uniPair (φ₀ φ₁ : SchwartzMap ℝ ℝ) : Prop :=
  cPair C_uniPair N_uniPair φ₀ φ₁

/--
\begin{definition}[Windows]\label{def:window}
A function is a window if it is one of the two components of a universal pair.
\end{definition}
-/
def window (φ : SchwartzMap ℝ ℝ) : Prop :=
  ∃ φ₀ φ₁ : SchwartzMap ℝ ℝ, uniPair φ₀ φ₁ ∧ (φ = φ₀ ∨ φ = φ₁)

/--
\begin{lemma}[Existence of a universal pair]\label{lem:cpair}
There exists a universal pair.
\end{lemma}
-/
theorem existsUniversalPair : ∃ φ₀ φ₁ : SchwartzMap ℝ ℝ, uniPair φ₀ φ₁ := by
  sorry

end

end Codex.Reduction.WindowsAndPairs
