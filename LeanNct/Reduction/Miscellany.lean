import LeanNct.Reduction.TwistedAverages
import LeanNct.Reduction.VariationSeminorms
import LeanNct.Reduction.WindowsAndPairs
import LeanNct.Preliminaries.MKernels

/-!
# Miscellany for the reduction

Formalization of the ``Miscellany'' subsection of the reduction argument.
-/

namespace Codex.Reduction.Miscellany

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal FourierTransform Real

open Codex.Reduction.TwistedAverages
open Codex.Reduction.VariationSeminorms
open Codex.Reduction.WindowsAndPairs
open Codex.Preliminaries.KKernels
open Codex.Preliminaries.MKernels
open Codex.Preliminaries.Notation

noncomputable section

/-- The one-dimensional $L^1$ normalized dilation used in the reduction. -/
noncomputable def aux_oneRescaled (lambda : ℝ) (phi : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ lambda⁻¹ * phi (lambda⁻¹ * x)

/-- The logarithmic derivative $T\phi=(x\phi(x))'$ used in the reduction. -/
noncomputable def aux_tBump (phi : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ deriv (fun u ↦ u * phi u) x

/-- The $L^p$ finite variation of a family of twisted averages. -/
noncomputable def aux_twistedVariation {n : ℕ} (phi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (p : ℝ≥0∞) (r : ℝ) (J : ℕ) : ℝ≥0∞ :=
  ⨆ t : {u : Fin (J + 1) → Set.Ioi (0 : ℝ) // StrictMono u},
    (∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale (t.1 j.succ) phi f x -
          twistedAverageAtScale (t.1 j.castSucc) phi f x) p volume) ^ r

/--
\begin{lemma}[Rescaling]\label{lem:rescaling}
Let $\phi\in L^1(\mathbb R)$.  For all $r,q,\lambda>0$, the variation
seminorm of $A_t(\phi_{(\lambda)})$ agrees with that of $A_t(\phi)$.
\end{lemma}
-/
theorem rescaling {n : ℕ} (phi : ℝ → ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (r : ℝ) (J : ℕ) (lambda : ℝ) (hlambda : 0 < lambda) :
    aux_twistedVariation (aux_oneRescaled lambda phi) f 2 r J =
      aux_twistedVariation phi f 2 r J := by
  sorry

/--
\begin{lemma}\label{lem:norm_A_sum_le_sum}
If $\phi=\sum_j\phi_j$ in $L^2$, then
$\|A(\phi,\mathbf f)\|_2\le\sum_j\|A(\phi_j,\mathbf f)\|_2$.
\end{lemma}
-/
theorem normASumLeSum {n : ℕ} (phi : ℝ → ℝ) (phiJ : ℕ → ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hphi : HasSum phiJ phi) :
    eLpNorm (twistedAverage phi (fun i x ↦ f i x)) 2 volume ≤
      ∑' j, eLpNorm (twistedAverage (phiJ j) (fun i x ↦ f i x)) 2 volume := by
  sorry

/--
\begin{lemma}\label{lem:form_pos}
If a real $W_0$ kernel $\Psi$ has nonnegative quadratic forms against every
bounded measurable one-dimensional test function, then its one-prism form is
nonnegative.  In particular this applies to tensor squares $\psi^{\otimes2}$.
\end{lemma}
-/
theorem formPos {n : ℕ} (hn : 1 ≤ n) (Psi : MKernel 1) (hPsi : MemW0 Psi)
    (hquad : ∀ g : ℝ → ℝ,
      Measurable g → BddAbove (Set.range g) →
      0 ≤ ∫ u : RealVector 1 × RealVector 1, g (u.1 0) * g (u.2 0) * Psi u)
    (F : Fin n → RealVector n → ℝ) :
    0 ≤ prismForm n 1 (by omega) hn Psi F := by
  sorry

/-- The tensor-square specialization in Lemma \ref{lem:form_pos}. -/
theorem aux_formPos_tensorSquare {n : ℕ} (hn : 1 ≤ n) (psi : ℝ → ℝ)
    (hpsi : MemW0 psi) (F : Fin n → RealVector n → ℝ) :
    0 ≤ prismForm n 1 (by omega) hn
      (fun u ↦ psi (u.1 0) * psi (u.2 0)) F := by
  sorry

/--
\begin{lemma}\label{lem:ftc_ATphi}
For $a(t)=A_t(\phi)(x)$, the $L^2(dt/t)$ norm of $t a'(t)$ on a dyadic
interval is the corresponding integral of $A_{2^k t}(T\phi)$.
\end{lemma}
-/
theorem ftcATphi {n : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : ℤ) :
    (∫ t : ℝ in Set.Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)),
      |t * deriv (fun s ↦
        twistedAverageAtScale s (fun u ↦ phi u) (fun i y ↦ f i y) x) t| ^ 2 * t⁻¹) =
      ∫ t : ℝ in Set.Icc 1 2,
        |twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi) (fun i y ↦ f i y) x| ^ 2 * t⁻¹ := by
  sorry

/-- The fixed constant in Lemma \ref{lem:Phij_prop}. -/
noncomputable def C_phiJProperties : ℝ := 2 ^ 12 * C_uniPair

/--
\begin{lemma}\label{lem:Phij_prop}
Under the symmetry, positivity, annular Fourier-support, and derivative
assumptions of the manuscript, a universal pair produces the auxiliary even
Schwartz function $\psi$ with the stated Fourier-square identity and bounds.
\end{lemma}
-/
theorem phiJProperties (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (Psi : EuclideanSpace ℝ (Fin 2) → ℝ) (hPsi : Psi ≠ 0)
    (hsym : ∀ u, Psi u = Psi (WithLp.toLp 2 ![u 1, u 0])) :
    ∃ psi : SchwartzMap ℝ ℝ,
      (∀ xi : ℝ,
        FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ)) xi ^ 2 =
          2 * (FourierTransform.fourier (fun x : ℝ ↦ (phi0 x : ℂ)) (2 ^ (-5 : ℤ) * xi) -
            FourierTransform.fourier (fun x : ℝ ↦ (phi1 x : ℂ)) (2 ^ (5 : ℤ) * xi)) ^ 2 -
            FourierTransform.fourier (fun x : EuclideanSpace ℝ (Fin 2) ↦ (Psi x : ℂ))
              (WithLp.toLp 2 ![xi, -xi])) ∧
      (∀ xi : ℝ, ‖iteratedDeriv 0
        (FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ))) xi‖ ≤ C_phiJProperties) := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:Phij_prop}}$ \auto]
\label{constant Phij proposition}
The constant in Lemma \ref{lem:Phij_prop} is $2^{27}$.
\end{lemma}
-/
theorem constantPhiJProposition : C_phiJProperties = (2 : ℝ) ^ 27 := by
  sorry

/--
\begin{lemma}[Bootstrapping]\label{lem:bootstrap}
The dyadic $2$-variation of $A_t(\phi)$ is controlled by four times the
supremum of the corresponding finite increasing dyadic square sum.
\end{lemma}
-/
theorem bootstrap {n : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (J : ℕ) :
    aux_twistedVariation (fun x ↦ phi x) (fun i x ↦ f i x) 2 2 J ≤
      4 * ⨆ ks : {u : Fin J → ℤ // StrictMono u},
        ∑ j, eLpNorm
          (twistedAverageAtScale ((2 : ℝ) ^ (ks.1 j)) (fun x ↦ phi x)
            (fun i x ↦ f i x)) 2 volume ^ 2 := by
  sorry

end

end Codex.Reduction.Miscellany
