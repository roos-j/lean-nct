import LeanNct.WienerSpace
import LeanNct.Preliminaries.Notation
import LeanNct.Preliminaries.MultiplicativelySpacedMonotoneSequences
import LeanNct.Preliminaries.Gaussians
import LeanNct.Preliminaries.MKernels

/-!
# The sandwich kernel

Formalization of the subsection ``The sandwich kernel''.
-/

namespace Codex.MainArgument.SandwichKernel

open MeasureTheory
open scoped BigOperators ENNReal

open Codex.Preliminaries.Notation
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.Preliminaries.Gaussians
open Codex.Preliminaries.KKernels
open Codex.Preliminaries.MKernels

noncomputable section

/-- The coordinate model used here for `\mathbb R^2`. -/
abbrev RealPlane := ℝ × ℝ

/-- A sequence pair in `\mathrm A^2`. -/
abbrev SequencePair := Fin 2 → ℤ → ℝ

/-- A double sequence of functions on `\mathbb R^2`. -/
abbrev DoubleSequence (k : ℕ) := Fin k → ℤ → RealPlane → ℝ

/-- A sequence of kernels on `(\mathbb R^2)^k`. -/
abbrev KernelSequence (k : ℕ) := ℤ → MKernel k

/--
\begin{definition}[double sequence of 2D functions]\label{double sequence of 2D functions}
  For $1\le k\le n$, let $\mathcal{X}_k$ be the set of
  double sequences
  \begin{equation}
      X=(X_{i,j})_{i\in [k),j\in \Z}
  \end{equation}
  with $X_{i,j}\in W_0(\R^2)$.
\end{definition}
-/
def MemDoubleSequence (k : ℕ) (X : DoubleSequence k) : Prop :=
  ∀ i j, Codex.MemW0 (X i j)

/--
Let ${\rm M}(k)$ be the space of sequences $\M=(M_j)_{j\in \Z}$ such that for $j\in \Z$ we have
$M_j\in W_0((\R^2)^k)$.
-/
def MemKernelSequence (k : ℕ) (M : KernelSequence k) : Prop :=
  ∀ j, Codex.MemW0 (M j)

/--
\begin{definition}[geometric parameters]\label{geometric parameters}
  Let $\Gamma$ be the set of triples $(k,u,a)$ with $k\in\N$, $1\le k\le n$, $u\in[2)^k$, $a\in ({\rm A}^{2})^k$  so that $\dist(a_{i}^0,a_{i}^1)<\infty$ for all $i\in [k)$.
\end{definition}
-/
structure GeometricParameters (n : ℕ) where
  k : ℕ
  one_le_k : 1 ≤ k
  k_le_n : k ≤ n
  orientation : Fin k → Fin 2
  scales : Fin k → SequencePair
  scales_spaced : ∀ i r, SpacedSequence (scales i r)
  finite_distance : ∀ i,
    SequenceDistance (scales i 0) (scales i 1) < ⊤

/--
For a sequence pair $\alpha=(\alpha_0,\alpha_1)\in {\rm A}^2$ we write
$\Delta(\alpha) = \mathrm{dist}(\alpha_{0}, \alpha_1)$.
-/
noncomputable def sequencePairDistance (a : SequencePair) : WithTop ℕ :=
  SequenceDistance (a 0) (a 1)

/--
For $\gamma\in\Gamma$ let
\[ \Delta_\gamma= 1+\sum_{i\in [k)} \Delta(a_i). \]
-/
noncomputable def geometricDelta {n : ℕ} (γ : GeometricParameters n) : ℕ :=
  1 + ∑ i, (sequencePairDistance (γ.scales i)).untop (ne_of_lt (γ.finite_distance i))

/--
\begin{definition}[two unitary matrices]
For $u\in [2)$ define unitary matrices $W_u\in\R^{2\times 2}$ as follows:
Let $W_0$ be the $2\times 2$ identity matrix and $W_1=\frac{1}{\sqrt{2}}\begin{pmatrix}1 & 1\\-1 & 1\end{pmatrix}$.
\end{definition}
-/
noncomputable def W (u : Fin 2) (v : RealPlane) : RealPlane :=
  if u = 0 then v else
    ((v.1 + v.2) / Real.sqrt 2, (-v.1 + v.2) / Real.sqrt 2)

/-- This auxiliary continuous linear equivalence realizes the nontrivial
matrix `W_1` from the two-unitary-matrices definition, so that Wiener-space
closure under a change of coordinates can be applied to 2D Gaussians. -/
noncomputable def aux_WOneContinuousLinearEquiv : RealPlane ≃L[ℝ] RealPlane where
  toFun := fun v =>
    ((v.1 + v.2) / Real.sqrt 2, (-v.1 + v.2) / Real.sqrt 2)
  invFun := fun v =>
    ((v.1 - v.2) / Real.sqrt 2, (v.1 + v.2) / Real.sqrt 2)
  left_inv := by
    rintro ⟨x, y⟩
    ext <;> dsimp
    all_goals
      have hroot : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      have hsq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
      field_simp
      rw [hsq]
      ring
  right_inv := by
    rintro ⟨x, y⟩
    ext <;> dsimp
    all_goals
      have hroot : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      have hsq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
      field_simp
      rw [hsq]
      ring
  map_add' := by
    rintro ⟨x, y⟩ ⟨z, w⟩
    ext <;> dsimp <;> ring
  map_smul' := by
    rintro c ⟨x, y⟩
    ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- This auxiliary equivalence packages either `W_0` or `W_1` as a linear
coordinate change for the Wiener-space proof of the 2D Gaussian facts. -/
noncomputable def aux_WContinuousLinearEquiv (u : Fin 2) : RealPlane ≃L[ℝ] RealPlane :=
  if u = 0 then ContinuousLinearEquiv.refl ℝ RealPlane else aux_WOneContinuousLinearEquiv

/-- This auxiliary identity identifies the raw matrix notation `W` with its
continuous-linear-equivalence implementation. -/
theorem aux_WContinuousLinearEquiv_apply (u : Fin 2) (v : RealPlane) :
    aux_WContinuousLinearEquiv u v = W u v := by
  unfold aux_WContinuousLinearEquiv W
  split_ifs <;> rfl

/--
\begin{definition}[2D Gaussians]\label{2D Gaussians}
For $q\in (\R_{>0})^2$ and $u\in[2)$, $v\in\mathbb{R}^2$ define
\[ G_{q,u}(v) = \g_{(q_0)}((W_u v)_0) \g_{(q_1)}((W_u v)_1). \]
\end{definition}
-/
noncomputable def twoDimensionalGaussian (q : Fin 2 → ℝ) (u : Fin 2) (v : RealPlane) : ℝ :=
  gaussianRescale (q 0) (W u v).1 * gaussianRescale (q 1) (W u v).2

/--
For $\gamma=(k,u,a)\in \Gamma$, define
\[ (G_{\gamma})_{i,j} = G_{a_i(j),u(i)}. \]
-/
noncomputable def gammaGaussian {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) :
    RealPlane → ℝ :=
  twoDimensionalGaussian (fun r => γ.scales i r j) (γ.orientation i)

/--
\begin{definition}[sandwich kernel]\label{sandwich kernel}
Let $\gamma=(k,u,a)\in \Gamma$, $X\in \mathcal{X}_k$, and $i\in [k)$. Define for  $j\in \Z$ and $y\in (\R^{2})^k$,
\[ (\M(\gamma,X,i))_j(y) =  \Big(\prod_{m\in [i)} (G_{\gamma})_{m,j}(y_m) \Big) X_{i,j}(y_i) \Big(\prod_{m=i+1}^{k-1} (G_{\gamma})_{m,j-1}(y_m) \Big).\]
\end{definition}
-/
noncomputable def sandwichKernel {n : ℕ} (γ : GeometricParameters n) (X : DoubleSequence γ.k)
    (i : Fin γ.k) : KernelSequence γ.k := fun j y =>
  (∏ m ∈ Finset.univ.filter (fun m => m < i), gammaGaussian γ m j (y.1 m, y.2 m)) *
    X i j (y.1 i, y.2 i) *
  ∏ m ∈ Finset.univ.filter (fun m => i < m), gammaGaussian γ m (j - 1) (y.1 m, y.2 m)

/--
\begin{definition}[difference of 2D Gaussians]
Let $\gamma=(k,u,a)\in \Gamma$.  For $i\in [k)$, $j\in \Z$, define
\[ (Y_\gamma)_{i,j} = (G_\gamma)_{i,j-1} - (G_\gamma)_{i,j}\ .\]
\end{definition}
-/
noncomputable def gaussianDifference {n : ℕ} (γ : GeometricParameters n) : DoubleSequence γ.k :=
  fun i j v => gammaGaussian γ i (j - 1) v - gammaGaussian γ i j v

/--
\begin{definition}[kernel sequences]\label{kernel sequences}
Let $k\in\N$ with $1\le k\le n$. Define
\begin{equation}
\|\M\|_{{\rm M}(k)}:=\sup_{J\in \N_{>0}, \F \in\mathfrak{F}}\min(1,J^{-1+2^{k-n+1}}) |\Lambda_k(\sum_{j\in [J)} M_j)(\F)| \, .
\end{equation}
\end{definition}
-/
noncomputable def kernelSequenceSeminorm (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (M : KernelSequence k) : ℝ≥0∞ :=
  ⨆ J : {J : ℕ // 0 < J}, ⨆ F : NormalizedFunctionTuple n,
    ENNReal.ofReal
      (min 1 (Real.rpow (J.1 : ℝ) (-1 + (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1))) *
        |prismForm n k hk hkn
          (fun y => ∑ j ∈ Finset.range J.1, M (j : ℤ) y)
          (fun i => F.1 i)|)

/--
This finite algebraic telescoping identity is used to turn the sum of the
Gaussian-difference sandwich terms into its two boundary products.
-/
theorem aux_product_telescope (a b : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      (∏ j ∈ Finset.range i, b j) * (a i - b i) *
        (∏ j ∈ Finset.Ico (i + 1) n, a j)) =
      (∏ j ∈ Finset.range n, a j) - ∏ j ∈ Finset.range n, b j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    have htail (i : ℕ) (hi : i < n) :
        (∏ j ∈ Finset.Ico (i + 1) (n + 1), a j) =
          (∏ j ∈ Finset.Ico (i + 1) n, a j) * a n := by
      exact Finset.prod_Ico_succ_top (f := a) (by omega)
    have hsum :
        (∑ i ∈ Finset.range n,
          (∏ j ∈ Finset.range i, b j) * (a i - b i) *
            (∏ j ∈ Finset.Ico (i + 1) (n + 1), a j)) =
          (∑ i ∈ Finset.range n,
            (∏ j ∈ Finset.range i, b j) * (a i - b i) *
              (∏ j ∈ Finset.Ico (i + 1) n, a j)) * a n := by
      calc
        (∑ i ∈ Finset.range n,
          (∏ j ∈ Finset.range i, b j) * (a i - b i) *
            (∏ j ∈ Finset.Ico (i + 1) (n + 1), a j)) =
            ∑ i ∈ Finset.range n,
              ((∏ j ∈ Finset.range i, b j) * (a i - b i) *
                (∏ j ∈ Finset.Ico (i + 1) n, a j)) * a n := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [htail i (Finset.mem_range.mp hi)]
              ring
        _ = (∑ i ∈ Finset.range n,
              (∏ j ∈ Finset.range i, b j) * (a i - b i) *
                (∏ j ∈ Finset.Ico (i + 1) n, a j)) * a n := by
              rw [Finset.sum_mul]
    rw [hsum]
    simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
    rw [ih]
    ring

end

end Codex.MainArgument.SandwichKernel
