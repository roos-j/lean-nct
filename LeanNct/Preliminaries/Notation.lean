import Mathlib

/-!
# Notation

The manuscript's coordinate and analytic notation that is not already supplied by mathlib.
-/

namespace Codex.Preliminaries.Notation

open MeasureTheory
open scoped BigOperators ENNReal

/--
For $x\in \R^n$ let
\begin{equation}\label{auto:coordinate-sum}\Sigma(x)=\sum_{i\in[n)} x_i.\end{equation}
-/
noncomputable def coordinateSum {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, x i

/--
For a subset $I\subset [n)$ (which inherits the natural order on $[m)$) and a $x\in \R^n$ we use notation
\begin{equation}\label{auto:coordinate-subvector} x_I = (x_{i})_{i\in I} \in \mathbb{R}^{|I|} \end{equation}
and when $I\subset [n)$ and $i\in [n)$ we also write $I\setminus i$ for the set $I$ without the index $i$.
-/
noncomputable def coordinateRestriction {n : ℕ} (I : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 fun i ↦ x i

/--
\begin{definition}\label{gaussian}
The standard Gaussian on $\R$ is defined by
\begin{equation}\label{standard Gaussian formula}
\g(x)=e^{-\pi x^2}
\end{equation}
for $x\in\R$. This is chosen so that $\int_{\R} \g=1$.
\end{definition}
-/
noncomputable def gaussian (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * x ^ 2)

/--
For $t>0$ and a function $\psi$ on $\R^n$ define the rescaled function
\begin{equation}\label{auto:L1-normalized-dilation}
\psi_{(t)}(x)=t^{-n} \psi(t^{-1}x).
\end{equation}
This is chosen so that $\int_{\R^n} \psi_{(t)} = \int_{\R^n} \psi$.
-/
noncomputable def rescaled {n : ℕ} (t : ℝ)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ t⁻¹ ^ n * ψ (t⁻¹ • x)

/--
If $\phi:\R^n\to \C, \psi:\R^m\to\C$ are functions, then $\phi\otimes \psi:\R^{n+m}\to\C$
denotes their tensor product
\begin{equation}\label{auto:tensor-product-formula} (\phi\otimes \psi)(x,y) = \phi(x)\psi(y), \end{equation}
where we have identified $\R^{n+m}$ with $\R^n\times \R^m$.
-/
noncomputable def tensorProduct {n m : ℕ} {𝕜 : Type*} [Mul 𝕜]
    (φ : EuclideanSpace ℝ (Fin n) → 𝕜) (ψ : EuclideanSpace ℝ (Fin m) → 𝕜) :
    EuclideanSpace ℝ (Fin (n + m)) → 𝕜 :=
  fun z ↦ φ (EuclideanSpace.finAddEquivProd z).1 * ψ (EuclideanSpace.finAddEquivProd z).2

/--
For $d\in\N$ also define
\begin{equation}\label{auto:tensor-power-formula}\chi^{\otimes d} = \underbrace{\chi \otimes \cdots \otimes \chi}_{d\;\text{times}}.\end{equation}
-/
noncomputable def tensorPower {𝕜 : Type*} [CommMonoid 𝕜]
    (χ : ℝ → 𝕜) (d : ℕ) : EuclideanSpace ℝ (Fin d) → 𝕜 :=
  fun x ↦ ∏ i, χ (x i)

/--
\begin{definition}[bracket bump]\label{bracket bump}
Define
\begin{equation}\label{auto:bracket-weight-definition}
    \left<x\right>:=(1+|x|)^{-1}\, .
\end{equation}
We agree on the following parsing, which interprets the power first:
\begin{equation}\label{auto:scaled-bracket-weight}
    \left<x\right>^N_{(s)}:=(\left< .\right>^N)_{(s)}(x)=s^{-1}(1+|s^{-1}x|)^{-N}\, .
\end{equation}
\end{definition}
-/
noncomputable def bracketBump (x : ℝ) : ℝ :=
  (1 + |x|)⁻¹

/-- The scaled component of Definition \ref{bracket bump}, jointly formalized by
'bracketBump' and 'scaledBracketBump'. -/
noncomputable def scaledBracketBump (N : ℕ) (s x : ℝ) : ℝ :=
  s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N

/-- Auxiliary real-exponent variant of the scaled component of Definition \ref{bracket bump}.
It is kept for a possible real-exponent analytic estimate; 'scaledBracketBump' is the
formalization of the manuscript's natural-exponent notation. -/
noncomputable def scaledBracketBumpReal (N s x : ℝ) : ℝ :=
  s⁻¹ * Real.rpow (1 + |s⁻¹ * x|) (-N)

end Codex.Preliminaries.Notation
