import LeanNct.MainArgument.SandwichKernel
import LeanNct.Preliminaries.BumpsAndEstimates

/-!
# Multipliers `H`, `L`, and `N`

Formalization of the first part of the subsection ``Multipliers `H`, `L`, `N``.
-/

namespace Codex.MainArgument.MultipliersHLN

open MeasureTheory
open scoped BigOperators ENNReal Real

open Codex.Preliminaries.Notation
open Codex.Preliminaries.Gaussians
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.Preliminaries.BumpsAndEstimates
open Codex.MainArgument.SandwichKernel

noncomputable section

/--
\begin{definition}[square root Gaussian difference]\label{square root Gaussian difference}
Let $a\in A$ and $j\in\Z$.
Define the function $s(a,j):\R \to \R$ by
\[s(a,j) = \mathcal{F}^{-1}(\xi \mapsto \sqrt{\g(a(j-1)\xi)-\g(a(j) \xi)}).\]
\end{definition}
-/
noncomputable def squareRootGaussianDifference (a : ℤ → ℝ) (_ha : SpacedSequence a) (j : ℤ) :
    ℝ → ℝ := fun x =>
  ∫ ξ : ℝ,
    Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
      Codex.Preliminaries.Notation.gaussian (a j * ξ)) *
      Real.cos (2 * Real.pi * x * ξ)

/-- This auxiliary Fourier identity turns the real part of the inverse Fourier transform of a
real-valued integrable function into the cosine integral used by
`squareRootGaussianDifference`.  It bridges the manuscript's two equivalent notations. -/
theorem aux_realInverseFourier_eq_cosineIntegral {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    (FourierTransformInv.fourierInv (fun ξ : ℝ => (f ξ : ℂ)) x).re =
      ∫ ξ : ℝ, f ξ * Real.cos (2 * Real.pi * x * ξ) := by
  let e : ℝ → ℂ := fun ξ =>
    Complex.exp ((↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I)
  have he : Continuous e := by
    dsimp [e]
    fun_prop
  have he_bound : ∀ ξ : ℝ, ‖e ξ‖ ≤ (1 : ℝ) := by
    intro ξ
    rw [show e ξ = Complex.exp ((↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I) by rfl,
      Complex.norm_exp]
    norm_num
  have h_integrable : Integrable (fun ξ : ℝ => e ξ * (f ξ : ℂ)) :=
    hf.ofReal.bdd_mul he.aestronglyMeasurable (ae_of_all _ he_bound)
  have h_integrable' : Integrable (fun ξ : ℝ =>
      Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) * (f ξ : ℂ)) := by
    simpa [e, Real.inner_apply, mul_assoc, mul_left_comm, mul_comm] using h_integrable
  rw [Real.fourierInv_eq']
  change (∫ ξ : ℝ,
    Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) * (f ξ : ℂ)).re = _
  calc
    (∫ ξ : ℝ,
      Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) * (f ξ : ℂ)).re =
        ∫ ξ : ℝ,
          (Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) *
            (f ξ : ℂ)).re :=
      (integral_re h_integrable').symm
    _ = ∫ ξ : ℝ, f ξ * Real.cos (2 * Real.pi * x * ξ) := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [Complex.exp_ofReal_mul_I_re]
      rw [Real.inner_apply]
      ring

/-- This auxiliary lemma supplies the integrability needed to identify the manuscript's
cosine-integral definition of `s(a,j)` with the inverse Fourier transform in the diagonal
square-root estimate. -/
theorem aux_squareRootGaussianDifference_integrable {a : ℤ → ℝ}
    (ha : SpacedSequence a) (j : ℤ) :
    Integrable (fun ξ : ℝ =>
      Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
        Codex.Preliminaries.Notation.gaussian (a j * ξ))) := by
  have ht₀ : 0 < a (j - 1) := (ha (j - 1)).1
  have hscale : 2 * a (j - 1) ≤ a j := by
    convert (ha (j - 1)).2 using 1 <;> ring
  have hrad (ξ : ℝ) :
      0 ≤ Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
        Codex.Preliminaries.Notation.gaussian (a j * ξ) :=
    aux_diagonalSquareRootFrequency_nonneg (by nlinarith) hscale ξ
  have hcontinuous : Continuous (fun ξ : ℝ =>
      Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
        Codex.Preliminaries.Notation.gaussian (a j * ξ))) := by
    apply Continuous.sqrt
    exact (gaussian_continuous.comp
      (continuous_const.mul continuous_id)).sub
      (gaussian_continuous.comp (continuous_const.mul continuous_id))
  have hcoefficient : 0 < Real.pi * a (j - 1) ^ 2 / 2 := by
    positivity
  have hmajorant : Integrable (fun ξ : ℝ =>
      Real.exp (-(Real.pi * a (j - 1) ^ 2 / 2) * ξ ^ 2)) :=
    integrable_exp_neg_mul_sq hcoefficient
  refine hmajorant.mono' hcontinuous.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
        Codex.Preliminaries.Notation.gaussian (a j * ξ)) ≤
        Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ)) :=
      Real.sqrt_le_sqrt (sub_le_self _ (aux_gaussian_pos _).le)
    _ = Real.exp (-Real.pi * (a (j - 1) * ξ) ^ 2 / 2) := by
      change Real.sqrt (Real.exp (-Real.pi * (a (j - 1) * ξ) ^ 2)) = _
      rw [← Real.exp_half]
    _ = Real.exp (-(Real.pi * a (j - 1) ^ 2 / 2) * ξ ^ 2) := by
      congr 1
      ring

/-- This auxiliary equality identifies `squareRootGaussianDifference` with the diagonal
square-root kernel from the preliminary estimates, so their decay theorems apply directly to
the multipliers `s_\gamma`. -/
theorem aux_squareRootGaussianDifference_eq_diagonalSquareRoot {a : ℤ → ℝ}
    (ha : SpacedSequence a) (j : ℤ) (x : ℝ) :
    squareRootGaussianDifference a ha j x =
      diagonalSquareRoot (a (j - 1)) (a j) x := by
  simpa only [squareRootGaussianDifference, diagonalSquareRoot,
    diagonalSquareRootFrequency] using
    (aux_realInverseFourier_eq_cosineIntegral
      (aux_squareRootGaussianDifference_integrable ha j) x).symm

/-- This auxiliary derivative identity transfers the derivative estimate for the diagonal
square-root kernel to the cosine-integral multiplier `s(a,j)`. -/
theorem aux_squareRootGaussianDifference_deriv_eq_diagonalSquareRoot {a : ℤ → ℝ}
    (ha : SpacedSequence a) (j : ℤ) (x : ℝ) :
    deriv (squareRootGaussianDifference a ha j) x =
      deriv (diagonalSquareRoot (a (j - 1)) (a j)) x := by
  congr 1
  funext y
  exact aux_squareRootGaussianDifference_eq_diagonalSquareRoot ha j y

/--
\begin{definition}[$s$ multiplier]\label{s multiplier}
    Let $\gamma=(k,u,a)\in \Gamma$. Let $i\in [k)$ and
    $j\in \Z$. Define  $(s_{\gamma})_{i,j}: \R \to \R$ by
\begin{equation}\label{E:b-definition}
   (s_{\gamma})_{i,j}=s(b,j)
\end{equation}
with
\begin{equation}
   b(j)=\sqrt{a_{i}^0(j)^2 + a_{i}^1(j)^2}
\end{equation}
if $u_i=0$, and by
\begin{equation}
   (s_{\gamma})_{i,j}=s(\sqrt{2}a_{i}^1,j)
\end{equation}
if $u_i=1$.
\end{definition}
-/
noncomputable def sMultiplier {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) :
    ℝ → ℝ :=
  if h : γ.orientation i = 0 then
    squareRootGaussianDifference
      (fun r => Real.sqrt ((γ.scales i 0 r) ^ 2 + (γ.scales i 1 r) ^ 2))
      (sqrt_sq_add_sq_mem_A (γ.scales_spaced i 0) (γ.scales_spaced i 1)) j
  else
    squareRootGaussianDifference
      (fun r => Real.sqrt 2 * γ.scales i 1 r)
      (smul_mem_A (γ.scales_spaced i 1) (Real.sqrt_pos.2 (by norm_num))) j

/--
\begin{definition}[H multiplier]\label{H multiplier}
Let $\gamma=(k,u,a)\in \Gamma$. Define
    $H_{\gamma}=(H_\gamma)_{i\in [k),j\in \Z}$ by
\begin{equation}
(H_{\gamma})_{i,j}:=(s_{\gamma})_{i,j}\otimes (s_{\gamma})_{i,j}
  -(Y_{\gamma})_{i,j}
\end{equation}
for every $i\in [k), j\in\mathbb{Z}$.
\end{definition}
-/
noncomputable def hMultiplier {n : ℕ} (γ : GeometricParameters n) : DoubleSequence γ.k :=
  fun i j v => sMultiplier γ i j v.1 * sMultiplier γ i j v.2 - gaussianDifference γ i j v

/--
Let $\gamma=(k,u,a)\in \Gamma$, $i\in [k)$, $j\in \Z$. For $t>0$, we set
\[
(L_{\gamma,t})_{i,j} =(H_{\gamma})_{i,j} \ast_{(1,1)} \Phi_{(t)}.
\]
-/
noncomputable def lMultiplierAtScale {n : ℕ} (γ : GeometricParameters n) (t : ℝ) :
    DoubleSequence γ.k := fun i j v =>
  ∫ p : ℝ, hMultiplier γ i j (v.1 - p, v.2 - p) * standardBumpRescale t p

/--
\begin{definition}[L multiplier]\label{L multiplier}
Let $\gamma=(k,u,a)\in \Gamma$.
Define the index set
\[\mathcal{I}_{\gamma} = \{(m,0)\,:\,m\in\mathbb{Z}, m\not=0\} \cup \{(0,l)\,:\,|l|\le \Delta_{\gamma}\} \subset \mathbb{Z}^2.\]
\end{definition}
-/
def multiplierIndexSet {n : ℕ} (γ : GeometricParameters n) : Set (ℤ × ℤ) :=
  {ι | (ι.1 ≠ 0 ∧ ι.2 = 0) ∨ (ι.1 = 0 ∧ ι.2.natAbs ≤ geometricDelta γ)}

/-- An index belonging to the manuscript's set `\mathcal I_\gamma`. -/
abbrev MultiplierIndex {n : ℕ} (γ : GeometricParameters n) :=
  {ι : ℤ × ℤ // ι ∈ multiplierIndexSet γ}

/-- The finite truncation by `|\iota|\le N` used to define the manuscript sum. -/
noncomputable def aux_multiplierIndexTruncation {n : ℕ} (γ : GeometricParameters n) (N : ℕ) :
    Finset (ℤ × ℤ) := by
  classical
  exact
    ((Finset.Icc (-(N : ℤ)) N).product (Finset.Icc (-(N : ℤ)) N)).filter
      (fun ι => ι ∈ multiplierIndexSet γ)

/--
\begin{definition}[Summation over $\mathcal I_{\gamma}$]\label{summation-definition}
Let $X$ be a normed $\R$-vector space.
Let $\gamma=(k,u,a)\in \Gamma$ and let $D_\iota \in X$ for $\iota \in \mathcal{I}_{\gamma}$. We define
\[
\sum_{\iota \in \mathcal{I}_{\gamma}} D_{\iota}:=\lim_{N\to \infty} \sum_{\iota\in\mathcal{I}_{\gamma}, ~|\iota| \leq N} D_{\iota},
\]
where the limit is taken in $X$.
\end{definition}
-/
noncomputable def sumOverMultiplierIndex {n : ℕ} {X : Type*} [NormedAddCommGroup X]
    (γ : GeometricParameters n) (D : MultiplierIndex γ → X) : X := by
  classical
  exact Filter.limUnder Filter.atTop fun N =>
    ∑ ι ∈ aux_multiplierIndexTruncation γ N,
      if hι : ι ∈ multiplierIndexSet γ then D ⟨ι, hι⟩ else 0

/--
\begin{definition}[L multiplier]\label{L multiplier}
For every $\iota \in\mathcal{I}_{\gamma}$, we define  $L_{\gamma,\iota}=(L_{\gamma,\iota})_{i\in [k),j\in \Z}$
such that for $|l|\le \Delta_{\gamma}$,
\begin{equation}
  (L_{\gamma,(0,l)})_{i,j}:= (H_{\gamma})_{i,j} \ast_{(1,1)} (\Phi_{(a_i^1(j+l-1))}-\Phi_{(a_i^1(j+l))})\, ,
 \end{equation}
if $h>0$, then
\begin{equation}
(L_{\gamma,(h,0)})_{i,j}:= (H_{\gamma})_{i,j} \ast_{(1,1)} (\Phi_{(2^{h-1}a_i^1(j+\Delta_{\gamma}))}-\Phi_{(2^{h}a_i^1(j+\Delta_{\gamma}))})\, ,
\end{equation}
and if $h<0$, then
\begin{equation}
 (L_{\gamma,(h,0)})_{i,j}:= (H_{\gamma})_{i,j} \ast_{(1,1)} (\Phi_{(2^{h}a_i^1(j-\Delta_{\gamma}-1))}-\Phi_{(2^{h+1}a_i^1(j-\Delta_{\gamma}-1))})\, .
\end{equation}
\end{definition}
-/
noncomputable def lMultiplier {n : ℕ} (γ : GeometricParameters n) (ι : MultiplierIndex γ) :
    DoubleSequence γ.k := fun i j v =>
  if hzero : ι.1.1 = 0 then
    ∫ p : ℝ, hMultiplier γ i j (v.1 - p, v.2 - p) *
      (standardBumpRescale (γ.scales i 1 (j + ι.1.2 - 1)) p -
        standardBumpRescale (γ.scales i 1 (j + ι.1.2)) p)
  else if hpositive : 0 < ι.1.1 then
    ∫ p : ℝ, hMultiplier γ i j (v.1 - p, v.2 - p) *
      (standardBumpRescale ((2 : ℝ) ^ (ι.1.1 - 1) *
          γ.scales i 1 (j + (geometricDelta γ : ℤ))) p -
        standardBumpRescale ((2 : ℝ) ^ ι.1.1 *
          γ.scales i 1 (j + (geometricDelta γ : ℤ))) p)
  else
    ∫ p : ℝ, hMultiplier γ i j (v.1 - p, v.2 - p) *
      (standardBumpRescale ((2 : ℝ) ^ ι.1.1 *
          γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) p -
        standardBumpRescale ((2 : ℝ) ^ (ι.1.1 + 1) *
          γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) p)

/--
This auxiliary raw Fourier transform is needed because the sandwich kernels use the product
coordinate model `\mathbb R \times \mathbb R`; it is the manuscript's Fourier convention on
that concrete model.
-/
noncomputable def aux_fourierPlane (f : RealPlane → ℝ) (ξ : RealPlane) : ℂ :=
  ∫ v : RealPlane, (f v : ℂ) * Complex.exp
    (-((2 : ℂ) * Real.pi * Complex.I * (v.1 * ξ.1 + v.2 * ξ.2)))

/--
This auxiliary raw inverse Fourier transform is needed to express the multiplier `N` on the
product coordinate model used for the sandwich kernels.
-/
noncomputable def aux_inverseFourierPlane (f : RealPlane → ℂ) (v : RealPlane) : ℂ :=
  ∫ ξ : RealPlane, f ξ * Complex.exp
    ((2 : ℂ) * Real.pi * Complex.I * (v.1 * ξ.1 + v.2 * ξ.2))

/--
This auxiliary raw Fourier transform is the one-dimensional specialization used for the
multiplier `\sigma_{\gamma,\iota,i,j}`.
-/
noncomputable def aux_fourierReal (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, (f x : ℂ) * Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * x * ξ))

/--
\begin{definition}[N multiplier]\label{N multiplier}
  Let $\gamma=(k,u,a)\in \Gamma$ and assume $k\le n-1$.  
Let $\nu=1$ if $k<n-1$ and $\nu=2$ if $k=n-1$ and let $i\in [k)$, $j\in \Z$.
For $\iota\in\mathcal{I}_{\gamma}$ define functions $\sigma_{\gamma,\iota,i,j}:\R\to\R$ so that
if $|l|\le \Delta_{\gamma}$,
\[ \sigma_{\gamma,(0,l),i,j} = s(a_i^1(\cdot+l), j) \]
and for $h>0$,
\[ \sigma_{\gamma,(h,0),i,j} = s(2^h a_i^1(\cdot+\Delta_{\gamma}), j) \]
and for $h<0$,
\[ \sigma_{\gamma,(h,0),i,j} = s(2^h a_i^1(\cdot-\Delta_{\gamma}), j). \]
\end{definition}
-/
noncomputable def sigmaMultiplier {n : ℕ} (γ : GeometricParameters n) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) : ℝ → ℝ :=
  if hzero : ι.1.1 = 0 then
    squareRootGaussianDifference
      (fun r => γ.scales i 1 (r + ι.1.2))
      (shift_mem_A (γ.scales_spaced i 1) ι.1.2) j
  else if hpositive : 0 < ι.1.1 then
    squareRootGaussianDifference
      (fun r => (2 : ℝ) ^ ι.1.1 * γ.scales i 1 (r + (geometricDelta γ : ℤ)))
      (smul_mem_A (shift_mem_A (γ.scales_spaced i 1) (geometricDelta γ : ℤ))
        (zpow_pos (by norm_num) _)) j
  else
    squareRootGaussianDifference
      (fun r => (2 : ℝ) ^ ι.1.1 * γ.scales i 1 (r - (geometricDelta γ : ℤ)))
      (smul_mem_A (shift_mem_A (γ.scales_spaced i 1) (-(geometricDelta γ : ℤ)))
        (zpow_pos (by norm_num) _)) j

/--
\begin{definition}[N multiplier]\label{N multiplier}
For every $\iota\in\mathcal{I}_{\gamma}$ we define $N_{\gamma,\iota}= (N_{\gamma,\iota})_{i\in [k),j\in \Z}$ such that
\begin{equation}
 (N_{\gamma,\iota})_{i,j} = 
 \mathcal F^{-1}((\xi,\eta) \mapsto \widehat{\sigma_{\gamma,\iota,i,j}}(\xi+\eta)^{-\nu}\widehat{(L_{\gamma,\iota})_{i,j}}(\xi,\eta))\, .
\end{equation}
\end{definition}
-/
noncomputable def nMultiplier {n : ℕ} (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1)
    (ι : MultiplierIndex γ) : DoubleSequence γ.k := fun i j v =>
  (aux_inverseFourierPlane (fun ξ =>
    (aux_fourierReal (sigmaMultiplier γ ι i j) (ξ.1 + ξ.2))⁻¹ ^
        (if γ.k < n - 1 then 1 else 2) *
      aux_fourierPlane (lMultiplier γ ι i j) ξ) v).re

end

end Codex.MainArgument.MultipliersHLN
