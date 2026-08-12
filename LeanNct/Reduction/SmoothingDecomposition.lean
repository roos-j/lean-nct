import LeanNct.Reduction.WindowsAndPairs
import LeanNct.Reduction.BumpFunctions

/-!
# A smoothing decomposition

Formalization of the ``A smoothing decomposition'' subsection of the reduction
argument.
-/

namespace Codex.Reduction.SmoothingDecomposition

open MeasureTheory Filter Set
open scoped BigOperators FourierTransform Real

open Codex.Preliminaries.Notation
open Codex.Reduction.WindowsAndPairs
open Codex.Reduction.BumpFunctions

noncomputable section

/-- The raw one-dimensional, $L^1$-normalized rescaling used throughout
Definition \ref{defn:window based bump functions}. -/
noncomputable def aux_realRescaled (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ t⁻¹ * f (t⁻¹ * x)

/-- The raw scalar convolution used to state the bump-function definitions. -/
noncomputable def aux_realConvolution (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ y : ℝ, f y * g (x - y)

/-- The real-valued characteristic function of a set. -/
noncomputable def aux_indicator (s : Set ℝ) : ℝ → ℝ :=
  s.indicator (fun _ : ℝ ↦ 1)

/-- The compact frequency annulus occurring in this subsection. -/
def aux_frequencyAnnulus : Set ℝ :=
  Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1

/-- The one-dimensional annulus convention shared with the integral-kernel estimates. -/
abbrev aux_annulusOne (r R : ℝ) : Set ℝ :=
  Codex.Reduction.BumpFunctions.aux_annulusOne r R

/-- The raw operator $T f=(x f(x))'$ needed in the Fourier estimates below. -/
noncomputable def aux_T (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ deriv (fun y ↦ y * f y) x

/-- Uniform convergence of a sequence of real functions, expressed directly through
the epsilon--$N$ condition. -/
def aux_uniformlyConverges (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |f n x - g x| < ε

/-- Convergence in the $L^2$ sense used for the two decomposition identities. -/
def aux_convergesInL2 (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  Tendsto (fun N ↦ eLpNorm (fun x ↦ f N x - g x) 2 volume) atTop (nhds 0)

/-- A finite integer-indexed sum of scalar functions. -/
noncomputable def aux_integerIntervalSum (f : ℤ → ℝ → ℝ) (a b : ℤ) : ℝ → ℝ :=
  fun x ↦ ∑ j ∈ Finset.Icc a b, f j x

/--
\begin{definition}[Window-based bump functions]\label{defn:window based bump functions}
Let $(\phi_0,\phi_1)$ be a universal pair.  The fields of this structure fix that
pair; the associated functions below are the functions in
\eqref{eqn:thetadef}--\eqref{eqn:varphi4kdef}.
\end{definition}
-/
structure windowBasedBumpFunctions where
  phi0 : SchwartzMap ℝ ℝ
  phi1 : SchwartzMap ℝ ℝ
  universalPair : uniPair phi0 phi1

namespace windowBasedBumpFunctions

/-- The function $\theta=\phi_0-(\phi_0)_{(2)}$ from
\eqref{eqn:thetadef}. -/
noncomputable def theta (b : windowBasedBumpFunctions) : ℝ → ℝ :=
  fun x ↦ b.phi0 x - aux_realRescaled 2 (fun y ↦ b.phi0 y) x

/-- The primitive $\widetilde\theta=\mathbf 1_{[0,\infty)}*\theta$ fixed in
Definition \ref{defn:window based bump functions}. -/
noncomputable def thetaTilde (b : windowBasedBumpFunctions) : ℝ → ℝ :=
  aux_realConvolution (aux_indicator (Set.Ici 0)) (theta b)

/-- The function $\varphi_{0,k}$ from \eqref{eqn:varphi0kdef}. -/
noncomputable def phiZero (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  aux_realConvolution
    (fun x ↦
      aux_realConvolution (aux_indicator (Set.Ico 0 1)) (fun y ↦ b.phi0 y) x - b.phi0 x)
    (aux_realRescaled ((2 : ℝ) ^ k) (theta b))

/-- The function $\varphi_{1,k}$ from \eqref{eqn:varphi1kdef}. -/
noncomputable def phiOne (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  aux_realConvolution (aux_indicator (Set.Ici 0))
    (aux_realRescaled ((2 : ℝ) ^ k) (theta b))

/-- The function $\varphi_{2,k}$ from \eqref{eqn:varphi2kdef}. -/
noncomputable def phiTwo (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  fun x ↦ -aux_realConvolution (aux_indicator (Set.Ici 1))
    (aux_realRescaled ((2 : ℝ) ^ k) (theta b)) x

/-- The function $\varphi_{3,k}$ from \eqref{eqn:varphi3def}. -/
noncomputable def phiThree (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  fun x ↦ ((2 : ℝ) ^ k) *
    aux_realRescaled ((2 : ℝ) ^ (-k)) (phiZero b k) x

/-- The function $\varphi_{4,k}$ from \eqref{eqn:varphi4kdef}. -/
noncomputable def phiFour (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  fun u ↦ ((2 : ℝ) ^ k) * thetaTilde b (u - (2 : ℝ) ^ (-k))

/-- The simultaneous partial sum in the smoothing decomposition. -/
noncomputable def smoothingPartialSum (b : windowBasedBumpFunctions) (N : ℕ) : ℝ → ℝ :=
  fun x ↦
    b.phi0 x +
      aux_integerIntervalSum (phiZero b) (-2) (N : ℤ) x +
      aux_integerIntervalSum (fun k ↦ fun y ↦ phiOne b k y + phiTwo b k y)
        (-(N : ℤ)) (-1) x

end windowBasedBumpFunctions

/-- The constant in Lemma \ref{lem:theta_decay}. -/
def C_thetaDecay (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * N + 2) * C_uniPair

/-- The four explicit constants in Lemma \ref{lem:abs_deriv_ft_phi3_le}. -/
def C_absDerivFourierPhiThreeLe : ℕ → ℝ
  | 0 => 4
  | 1 => 28 * C_uniPair + 4
  | 2 => 96 * C_uniPair ^ 2 + 140 * C_uniPair + 86
  | 3 => 69 * (2 : ℝ) ^ 4 * C_uniPair ^ 2 + 47 * 2 * 5 ^ 2 * C_uniPair + 2 ^ 11
  | _ + 4 => 0

/-- The constants in Lemma \ref{lem:abs_deriv_ft_Tphi3_le}. -/
def C_absDerivFourierTPhiThreeLe (m : ℕ) : ℝ :=
  m * C_absDerivFourierPhiThreeLe m + C_absDerivFourierPhiThreeLe (m + 1)

/-- The constant in Lemma \ref{lem:theta_prim}. -/
def C_thetaPrimitive (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (5 * N + 6) * C_uniPair

/--
\begin{lemma}\label{lem:bumpbasic}
Let $\theta$ be as in \eqref{eqn:thetadef}.  Its Fourier transform is supported in
$[-1,-2^{-2}]\cup[2^{-2},1]$, and for every $m\in\mathbb Z$ the uniformly
convergent series $\sum_{\ell=m}^\infty\theta_{(2^\ell)}$ equals
$(\phi_0)_{(2^m)}$.
\end{lemma}
-/
theorem bumpBasic (b : windowBasedBumpFunctions) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.theta b x : ℂ))) ⊆ aux_frequencyAnnulus ∧
    ∀ m : ℤ,
      aux_uniformlyConverges
        (fun N ↦ aux_integerIntervalSum
          (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell)
            (windowBasedBumpFunctions.theta b)) m (m + (N : ℤ)))
        (aux_realRescaled ((2 : ℝ) ^ m) (fun x ↦ b.phi0 x)) := by
  sorry

/--
\begin{lemma}\label{lem:chardecomp}
With $\phi_0,\theta$ as in Definition \ref{defn:window based bump functions},
\[\mathbf 1_{[0,1]}=\mathbf 1_{[0,1]}*\phi_0+
\sum_{\ell=-\infty}^{-1}\mathbf 1_{[0,1]}*\theta_{(2^\ell)}\]
in $L^2$.
\end{lemma}
-/
theorem charDecomp (b : windowBasedBumpFunctions) :
    aux_convergesInL2
      (fun N ↦ fun x ↦
        aux_realConvolution (aux_indicator (Set.Icc 0 1)) (fun y ↦ b.phi0 y) x +
          aux_integerIntervalSum
            (fun ell ↦ aux_realConvolution (aux_indicator (Set.Icc 0 1))
              (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b)))
            (-(N : ℤ)) (-1) x)
      (aux_indicator (Set.Icc 0 1)) := by
  sorry

/--
\begin{lemma}[Smoothing decomposition]\label{lem:smoothingdecomp}
The identity
\[\mathbf 1_{[0,1]}=\phi_0+\sum_{k=-2}^\infty\varphi_{0,k}+
\sum_{k=-\infty}^{-1}\varphi_{1,k}+
\sum_{k=-\infty}^{-1}\varphi_{2,k}\]
holds in the $L^2$ sense.
\end{lemma}
-/
theorem smoothingDecomp (b : windowBasedBumpFunctions) :
    aux_convergesInL2 (windowBasedBumpFunctions.smoothingPartialSum b)
      (aux_indicator (Set.Icc 0 1)) := by
  sorry

/--
\begin{lemma}\label{lem:theta_decay}
For $1\le N\le3$ and every $u\in\mathbb R$,
$|\theta(u)|\le C_{\ref{lem:theta_decay},N}\langle u\rangle^N$, where
$C_{\ref{lem:theta_decay},N}=2^{2N+2}C_{\ref{def:unipair}}$.
\end{lemma}
-/
theorem thetaDecay (b : windowBasedBumpFunctions) (N : ℕ)
    (hN_one : 1 ≤ N) (hN_three : N ≤ 3) :
    ∀ u : ℝ, |windowBasedBumpFunctions.theta b u| ≤
      C_thetaDecay N * bracketBump u ^ N := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:theta_decay},N}$ \auto]
\label{constant theta decay}
For $1\le N\le3$, $C_{\ref{lem:theta_decay},N}\le2^{2N+17}$.
\end{lemma}
-/
theorem constantThetaDecay (N : ℕ) (hN_one : 1 ≤ N) (hN_three : N ≤ 3) :
    C_thetaDecay N ≤ (2 : ℝ) ^ (2 * N + 17) := by
  sorry

/--
\begin{lemma}\label{lem:ft_phi3_eq}
For $k\in\mathbb Z$ and $\xi\in\mathbb R$,
\[\widehat{\varphi_{3,k}}(\xi)=2^k
(\widehat{\mathbf1_{[0,1)}}-1)(2^{-k}\xi)
\widehat{\phi_0}(2^{-k}\xi)\widehat\theta(\xi).\]
\end{lemma}
-/
theorem fourierPhiThreeEq (b : windowBasedBumpFunctions) (k : ℤ) (ξ : ℝ) :
    FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ)) ξ =
      (↑((2 : ℝ) ^ k) : ℂ) *
        (FourierTransform.fourier
          (fun x : ℝ ↦ (aux_indicator (Set.Ico 0 1) x : ℂ))
          ((2 : ℝ) ^ (-k) * ξ) - 1) *
        FourierTransform.fourier (fun x : ℝ ↦ (b.phi0 x : ℂ))
          ((2 : ℝ) ^ (-k) * ξ) *
        FourierTransform.fourier
          (fun x : ℝ ↦ (windowBasedBumpFunctions.theta b x : ℂ)) ξ := by
  sorry

/--
\begin{lemma}\label{lem:abs_deriv_ft_phi3_le}
For $m<4$, $k\in\mathbb Z$, and $|\xi|\le1$,
$|\widehat{\varphi_{3,k}}^{(m)}(\xi)|\le
C_{\ref{lem:abs_deriv_ft_phi3_le},m}$, with the four displayed constants from
the manuscript.
\end{lemma}
-/
theorem absDerivFourierPhiThreeLe (b : windowBasedBumpFunctions) (m : ℕ)
    (hm : m < 4) (k : ℤ) (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    ‖iteratedDeriv m
      (FourierTransform.fourier
        (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) ξ‖ ≤
      C_absDerivFourierPhiThreeLe m := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:abs_deriv_ft_phi3_le},m}$ \auto]
\label{constant phi three derivative}
The constants for $m=0,1,2,3$ are respectively $2^2$, less than $2^{20}$,
less than $2^{37}$, and less than $2^{41}$.
\end{lemma}
-/
theorem constantPhiThreeDerivative :
    C_absDerivFourierPhiThreeLe 0 = (2 : ℝ) ^ 2 ∧
    C_absDerivFourierPhiThreeLe 1 < (2 : ℝ) ^ 20 ∧
    C_absDerivFourierPhiThreeLe 2 < (2 : ℝ) ^ 37 ∧
    C_absDerivFourierPhiThreeLe 3 < (2 : ℝ) ^ 41 := by
  sorry

/--
\begin{lemma}\label{lem:abs_deriv_ft_Tphi3_le}
For $m<3$, $k\in\mathbb Z$, and $|\xi|\le1$,
$|\widehat{T\varphi_{3,k}}^{(m)}(\xi)|\le
C_{\ref{lem:abs_deriv_ft_Tphi3_le},m}$, where
$C_{\ref{lem:abs_deriv_ft_Tphi3_le},m}=
mC_{\ref{lem:abs_deriv_ft_phi3_le},m}+
C_{\ref{lem:abs_deriv_ft_phi3_le},m+1}$.
\end{lemma}
-/
theorem absDerivFourierTPhiThreeLe (b : windowBasedBumpFunctions) (m : ℕ)
    (hm : m < 3) (k : ℤ) (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    ‖iteratedDeriv m
      (FourierTransform.fourier
        (fun x : ℝ ↦ (aux_T (windowBasedBumpFunctions.phiThree b k) x : ℂ))) ξ‖ ≤
      C_absDerivFourierTPhiThreeLe m := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:abs_deriv_ft_Tphi3_le},m}$ \auto]
\label{constant T phi three derivative}
For $m=0,1,2$, these constants are respectively less than $2^{20}$,
$2^{37}$, and $2^{41}$.
\end{lemma}
-/
theorem constantTPhiThreeDerivative :
    C_absDerivFourierTPhiThreeLe 0 < (2 : ℝ) ^ 20 ∧
    C_absDerivFourierTPhiThreeLe 1 < (2 : ℝ) ^ 37 ∧
    C_absDerivFourierTPhiThreeLe 2 < (2 : ℝ) ^ 41 := by
  sorry

/--
\begin{lemma}\label{lem:theta_prim}
The primitive $\widetilde\theta$ and $T\widetilde\theta$ have Fourier support in
$[-1,-2^{-2}]\cup[2^{-2},1]\subset\operatorname{Ann}_1(1,2^2)$.  For
$2\le N<N_{\ref{def:unipair}}$, both satisfy the decay bound with constant
$C_{\ref{lem:theta_prim},N}=2^{5N+6}C_{\ref{def:unipair}}$.
\end{lemma}
-/
theorem thetaPrimitive (b : windowBasedBumpFunctions) (N : ℕ)
    (hN_two : 2 ≤ N) (hN_uni : N < N_uniPair) :
    (Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.thetaTilde b x : ℂ))) ⊆ aux_frequencyAnnulus ∧
      aux_frequencyAnnulus ⊆ aux_annulusOne 1 ((2 : ℝ) ^ 2)) ∧
    (Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (aux_T (windowBasedBumpFunctions.thetaTilde b) x : ℂ))) ⊆
        aux_frequencyAnnulus ∧
      aux_frequencyAnnulus ⊆ aux_annulusOne 1 ((2 : ℝ) ^ 2)) ∧
    (∀ u : ℝ, |windowBasedBumpFunctions.thetaTilde b u| ≤
      C_thetaPrimitive N * bracketBump u ^ N) ∧
    ∀ u : ℝ, |aux_T (windowBasedBumpFunctions.thetaTilde b) u| ≤
      C_thetaPrimitive N * bracketBump u ^ N := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:theta_prim},N}$ \auto]
\label{constant theta primitive}
For $2\le N<N_{\ref{def:unipair}}$,
$C_{\ref{lem:theta_prim},N}\le2^{5N+21}$; in particular
$C_{\ref{lem:theta_prim},2}\le2^{31}$.
\end{lemma}
-/
theorem constantThetaPrimitive (N : ℕ) (hN_two : 2 ≤ N) (hN_uni : N < N_uniPair) :
    C_thetaPrimitive N ≤ (2 : ℝ) ^ (5 * N + 21) ∧
    C_thetaPrimitive 2 ≤ (2 : ℝ) ^ 31 := by
  sorry

/--
\begin{lemma}\label{lem:phi4_supp}
For every $k\in\mathbb Z$, both $\widehat{\varphi_{4,k}}$ and
$\widehat{T\varphi_{4,k}}$ are supported in
$[-1,-2^{-2}]\cup[2^{-2},1]$.
\end{lemma}
-/
theorem phiFourSupport (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.phiFour b k x : ℂ))) ⊆
        aux_frequencyAnnulus ∧
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (aux_T (windowBasedBumpFunctions.phiFour b k) x : ℂ))) ⊆
        aux_frequencyAnnulus := by
  sorry

end

end Codex.Reduction.SmoothingDecomposition
