import LeanNct.MainArgument.MultipliersHLN
import LeanNct.MainArgument.GaussianDomination

/-!
# Main induction

Formalization of the subsection ``Main induction''.
-/

namespace Codex.MainArgument.MainInduction

open MeasureTheory
open scoped BigOperators ENNReal Real

open Codex.Preliminaries.KKernels
open Codex.Preliminaries.MKernels
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN
open Codex.MainArgument.GaussianDomination

noncomputable section

/--
The raw tensor square of the one-dimensional multiplier. This auxiliary
definition is needed to express the manuscript's repeated notation
`s_\gamma \otimes s_\gamma` as a double sequence on the concrete product
coordinate model.
-/
noncomputable def aux_sMultiplierTensorSquare {n : ℕ} (γ : GeometricParameters n) :
    DoubleSequence γ.k :=
  fun i j v => sMultiplier γ i j v.1 * sMultiplier γ i j v.2

/--
The raw kernel appearing in the definition of `\mathrm{IncreaseData}`. It is
introduced only to give a Lean name to the displayed sequence
`\mathcal M_{i,\iota}` in that definition.
-/
noncomputable def aux_increaseDataKernel {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (i : Fin γ.k) (ι : MultiplierIndex γ) :
    KernelSequence (γ.k + 1) := fun j y =>
  (∏ m ∈ Finset.univ.filter (fun m => m < i),
      gammaGaussian γ m j (y.1 m.castSucc, y.2 m.castSucc)) *
    |nMultiplier γ hkn ι i j (y.1 i.castSucc, y.2 i.castSucc)| *
      (∏ m ∈ Finset.univ.filter (fun m => i < m),
        gammaGaussian γ m (j - 1) (y.1 m.castSucc, y.2 m.castSucc)) *
    tensorSquare (sigmaMultiplier γ ι i j) (y.1 (Fin.last γ.k), y.2 (Fin.last γ.k))

/--
\begin{definition}[induct positive terms]\label{induct positive terms}
Let $k\in \N$ with $1\le k\le n$ and $C\in [1,\infty)$.
We say that $\InductPositiveTerms{k,C}$ holds if
for all $\gamma=(k,u,a)\in \Gamma$, $i\in [k)$,
\begin{equation}
    \|\M(\gamma,s_{\gamma} \otimes s_{\gamma},i)\|_{{\rm M}(k)}\le C \Delta_\gamma^{2-2^{k-n+1}}.
\end{equation}
\end{definition}
-/
def InductPositiveTerms (n k : ℕ) (C : ℝ) (_hk : 1 ≤ k) (_hkn : k ≤ n) (_hC : 1 ≤ C) :
    Prop :=
  ∀ (γ : GeometricParameters n), γ.k = k → ∀ i : Fin γ.k,
    kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (sandwichKernel γ (aux_sMultiplierTensorSquare γ) i) ≤
      ENNReal.ofReal
        (C * Real.rpow (geometricDelta γ : ℝ)
          (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1)))

/--
\begin{definition}[vanishing diagonal]\label{vanishing diagonal}
Let $k\in \N$ with $1\le k\le n$ and $C\in [1,\infty)$.
We say that $\VanishingDiagonal{k,C}$ holds if
for all $\gamma=(k,u,a)\in \Gamma$, $i\in [k)$,
\begin{equation}
    \|\M(\gamma,H_\gamma,i)\|_{{\rm M}(k)}
    \le C \Delta_\gamma^{2-2^{k-n+1}} .
\end{equation}
\end{definition}
-/
def VanishingDiagonal (n k : ℕ) (C : ℝ) (_hk : 1 ≤ k) (_hkn : k ≤ n) (_hC : 1 ≤ C) :
    Prop :=
  ∀ (γ : GeometricParameters n), γ.k = k → ∀ i : Fin γ.k,
    kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (sandwichKernel γ (hMultiplier γ) i) ≤
      ENNReal.ofReal
        (C * Real.rpow (geometricDelta γ : ℝ)
          (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1)))

/--
\begin{definition}[diagonal band]\label{diagonal band}
Let $k\in \N$ with $1\le k\le n-1$ and $C\in [1,\infty)$.
We say that $\DiagonalBand{k,C}$ holds if
for all $\gamma=(k,u,a)\in \Gamma$, $i\in [k)$,
\begin{equation}
   \sum_{\iota\in\mathcal{I}_{\gamma}}
   \|\M(\gamma,L_{\gamma,\iota},i)\|_{{\rm M}(k)}
   \le C\Delta_\gamma^{2-2^{k-n+1}} .
\end{equation}
\end{definition}
-/
def DiagonalBand (n k : ℕ) (C : ℝ) (_hk : 1 ≤ k) (_hkn : k ≤ n - 1) (_hC : 1 ≤ C) :
    Prop :=
  ∀ (γ : GeometricParameters n), γ.k = k → ∀ i : Fin γ.k,
    ∑' ι : MultiplierIndex γ,
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (sandwichKernel γ (lMultiplier γ ι) i) ≤
      ENNReal.ofReal
        (C * Real.rpow (geometricDelta γ : ℝ)
          (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1)))

/--
\begin{definition}[increase data]\label{increase data}
Let $k\in \N$ with $1\le k\le n-1$ and $C\in [1,\infty)$.
We say that $\IncreaseData{k,C}$ holds if the following holds.

Let $\gamma=(k,u,a)\in \Gamma$, let $i\in [k)$, and let
\iota\in\mathcal{I}_{\gamma}$.
For $j\in\mathbb Z$ and $y\in(\mathbb R^2)^{k+1}$ define
\begin{equation}
    (\M_{i,\iota})_j(y):=
    \Big(\prod_{m\in [i)} (G_\gamma)_{m,j}(y_m)\Big)
    |(N_{\gamma,\iota})_{i,j}(y_i)|
    \Big(\prod_{m=i+1}^{k-1} (G_\gamma)_{m,j-1}(y_m)\Big)
    \bigl(\sigma_{\gamma,\iota,i,j}^{\otimes 2}\bigr)(y_{k}) .
\end{equation}
Then $\M_{i,\iota}\in {\rm M}(k+1)$ and
\begin{equation}
  \|\M_{i,\iota}\|_{{\rm M}(k+1)}
  \le C 2^{-\frac{|\iota_1|}{2}}(1+|\iota_1|)^2
  \Delta_\gamma^{2-2^{k-n+2}} .
\end{equation}
\end{definition}
-/
def IncreaseData (n k : ℕ) (C : ℝ) (_hk : 1 ≤ k) (hkn : k ≤ n - 1) (_hC : 1 ≤ C) :
    Prop :=
  ∀ (γ : GeometricParameters n) (hγ : γ.k = k) (i : Fin γ.k)
    (ι : MultiplierIndex γ),
    let hγn : γ.k ≤ n - 1 := by simpa [hγ] using hkn
    MemKernelSequence (γ.k + 1) (aux_increaseDataKernel γ hγn i ι) ∧
      kernelSequenceSeminorm n (γ.k + 1) (by omega) (by omega)
          (aux_increaseDataKernel γ hγn i ι) ≤
        ENNReal.ofReal
          (C * Real.rpow 2 (-((ι.1.1.natAbs : ℝ) / 2)) *
            (1 + (ι.1.1.natAbs : ℝ)) ^ 2 *
            Real.rpow (geometricDelta γ : ℝ)
              (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 2)))

/-- This auxiliary monotonicity lemma lets later induction steps enlarge the
constant in the conclusion of `InductPositiveTerms` without changing the
geometric data. -/
theorem aux_inductPositiveTerms_mono {n k : ℕ} {C D : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hC : 1 ≤ C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    InductPositiveTerms n k C hk hkn hC →
      InductPositiveTerms n k D hk hkn hD := by
  intro h γ hγ i
  refine (h γ hγ i).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right hCD
  exact Real.rpow_nonneg (by positivity) _

/-- This auxiliary monotonicity lemma is used to align the output constants of
the diagonal-band and positive-term implications. -/
theorem aux_vanishingDiagonal_mono {n k : ℕ} {C D : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hC : 1 ≤ C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    VanishingDiagonal n k C hk hkn hC →
      VanishingDiagonal n k D hk hkn hD := by
  intro h γ hγ i
  refine (h γ hγ i).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right hCD
  exact Real.rpow_nonneg (by positivity) _

/-- This auxiliary monotonicity lemma is used to enlarge the summation bound
in `DiagonalBand` when composing the main induction implications. -/
theorem aux_diagonalBand_mono {n k : ℕ} {C D : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n - 1) (hC : 1 ≤ C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    DiagonalBand n k C hk hkn hC →
      DiagonalBand n k D hk hkn hD := by
  intro h γ hγ i
  refine (h γ hγ i).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right hCD
  exact Real.rpow_nonneg (by positivity) _

/-- Constant from Proposition \ref{induct positive terms imply increase data}; it is used in
`inductPositiveTerms_implies_increaseData`. -/
noncomputable def C_inductPositiveTermsImplyIncreaseData : ℝ :=
  (2 : ℝ) ^ (10 : ℕ) * C_gaussianDominationCombinedCard *
    (1 + C_gaussianDominationCombinedDistance) ^ (2 : ℕ) * C_gaussianDominationCombined

/-- This auxiliary positivity fact is needed when taking square roots of the
constant in the reverse induction estimates. -/
theorem aux_C_inductPositiveTermsImplyIncreaseData_pos :
    0 < C_inductPositiveTermsImplyIncreaseData := by
  unfold C_inductPositiveTermsImplyIncreaseData
    C_gaussianDominationCombinedCard C_gaussianDominationCombinedDistance
    C_gaussianDominationCombined
  positivity

/-- This auxiliary lower bound supplies the manuscript's admissibility
condition `C ∈ [1,∞)` when the Gaussian-domination constant is fed into the
main induction. -/
theorem aux_one_le_C_inductPositiveTermsImplyIncreaseData :
    1 ≤ C_inductPositiveTermsImplyIncreaseData := by
  unfold C_inductPositiveTermsImplyIncreaseData
    C_gaussianDominationCombinedCard C_gaussianDominationCombinedDistance
    C_gaussianDominationCombined
  norm_num

/-- Constant used by Proposition \ref{P:better-induction}, formalized by
`betterInduction`. -/
noncomputable def C_betterInduction (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ (10 : ℕ) * (k + 2 : ℕ) *
      Real.sqrt C_inductPositiveTermsImplyIncreaseData + Real.sqrt 2) ^ (2 : ℕ)

/-- This auxiliary positivity fact supplies the admissibility condition on the
constant in `betterInduction`. -/
theorem aux_C_betterInduction_pos (k : ℕ) : 0 < C_betterInduction k := by
  unfold C_betterInduction
  apply sq_pos_of_pos
  apply add_pos_of_nonneg_of_pos
  · positivity
  · exact Real.sqrt_pos.2 (by norm_num)

/-- This auxiliary lower bound supplies the `C ∈ [1,∞)` hypothesis needed
when `betterInduction` invokes the preceding induction implication. -/
theorem aux_one_le_C_betterInduction (k : ℕ) : 1 ≤ C_betterInduction k := by
  unfold C_betterInduction
  have hmain : 0 ≤ (2 : ℝ) ^ (10 : ℕ) * (k + 2 : ℕ) *
      Real.sqrt C_inductPositiveTermsImplyIncreaseData := by
    positivity
  have hroot : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsum : Real.sqrt 2 ≤ (2 : ℝ) ^ (10 : ℕ) * (k + 2 : ℕ) *
      Real.sqrt C_inductPositiveTermsImplyIncreaseData + Real.sqrt 2 := by
    linarith
  have hsumnonneg : 0 ≤ (2 : ℝ) ^ (10 : ℕ) * (k + 2 : ℕ) *
      Real.sqrt C_inductPositiveTermsImplyIncreaseData + Real.sqrt 2 := by
    positivity
  have hsqrt : (Real.sqrt 2) ^ (2 : ℕ) = 2 := by
    rw [Real.sq_sqrt (by norm_num)]
  calc
    1 ≤ (Real.sqrt 2) ^ (2 : ℕ) := by rw [hsqrt]; norm_num
    _ ≤ ((2 : ℝ) ^ (10 : ℕ) * (k + 2 : ℕ) *
        Real.sqrt C_inductPositiveTermsImplyIncreaseData + Real.sqrt 2) ^ (2 : ℕ) :=
      (sq_le_sq₀ hroot hsumnonneg).2 hsum

/-- Constant in Theorem \ref{induct positive terms theorem}, formalized by
`inductPositiveTermsTheorem`. -/
noncomputable def C_inductPositiveTermsTheorem : ℝ :=
  ((2 : ℝ) ^ (12 : ℕ) * Real.sqrt C_inductPositiveTermsImplyIncreaseData +
    Real.sqrt 2) ^ (2 : ℕ)

/-- This auxiliary positivity fact supplies the admissibility condition on the
constant in `inductPositiveTermsTheorem`. -/
theorem aux_C_inductPositiveTermsTheorem_pos :
    0 < C_inductPositiveTermsTheorem := by
  unfold C_inductPositiveTermsTheorem
  apply sq_pos_of_pos
  apply add_pos_of_nonneg_of_pos
  · positivity
  · exact Real.sqrt_pos.2 (by norm_num)

/-- This auxiliary lower bound supplies the admissibility condition on the
constant used in the final `inductPositiveTermsTheorem`. -/
theorem aux_one_le_C_inductPositiveTermsTheorem :
    1 ≤ C_inductPositiveTermsTheorem := by
  unfold C_inductPositiveTermsTheorem
  have hmain : 0 ≤ (2 : ℝ) ^ (12 : ℕ) *
      Real.sqrt C_inductPositiveTermsImplyIncreaseData := by
    positivity
  have hroot : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsum : Real.sqrt 2 ≤ (2 : ℝ) ^ (12 : ℕ) *
      Real.sqrt C_inductPositiveTermsImplyIncreaseData + Real.sqrt 2 := by
    linarith
  have hsumnonneg : 0 ≤ (2 : ℝ) ^ (12 : ℕ) *
      Real.sqrt C_inductPositiveTermsImplyIncreaseData + Real.sqrt 2 := by
    positivity
  have hsqrt : (Real.sqrt 2) ^ (2 : ℕ) = 2 := by
    rw [Real.sq_sqrt (by norm_num)]
  calc
    1 ≤ (Real.sqrt 2) ^ (2 : ℕ) := by rw [hsqrt]; norm_num
    _ ≤ ((2 : ℝ) ^ (12 : ℕ) *
        Real.sqrt C_inductPositiveTermsImplyIncreaseData + Real.sqrt 2) ^ (2 : ℕ) :=
      (sq_le_sq₀ hroot hsumnonneg).2 hsum

/-- Output constant from Proposition \ref{vanishing diagonal implies induct positive terms},
formalized by `vanishingDiagonal_implies_inductPositiveTerms`. -/
def C_vanishingDiagonalImpliesInductPositiveTerms (k : ℕ) (C : ℝ) : ℝ :=
  k * C + 2

/-- This auxiliary bound verifies the admissibility condition on the output
constant of `vanishingDiagonal_implies_inductPositiveTerms`. -/
theorem aux_one_le_C_vanishingDiagonalImpliesInductPositiveTerms (k : ℕ) {C : ℝ}
    (hC : 1 ≤ C) : 1 ≤ C_vanishingDiagonalImpliesInductPositiveTerms k C := by
  unfold C_vanishingDiagonalImpliesInductPositiveTerms
  have hnonneg : 0 ≤ (k : ℝ) * C :=
    mul_nonneg (Nat.cast_nonneg k) (by linarith)
  linarith

/-- Output constant from Proposition \ref{increase data implies diagonal band}, formalized by
`increaseData_implies_diagonalBand`. -/
noncomputable def C_increaseDataImpliesDiagonalBand (k n : ℕ) (C : ℝ) : ℝ :=
  if k < n - 1 then (2 : ℝ) ^ (10 : ℕ) * Real.sqrt C else (2 : ℝ) ^ (10 : ℕ) * C

/-- This auxiliary bound verifies the `C ∈ [1,∞)` side condition for the
two constants in `increaseData_implies_diagonalBand`. -/
theorem aux_one_le_C_increaseDataImpliesDiagonalBand (k n : ℕ) {C : ℝ}
    (hC : 1 ≤ C) : 1 ≤ C_increaseDataImpliesDiagonalBand k n C := by
  unfold C_increaseDataImpliesDiagonalBand
  split_ifs
  · calc
      1 ≤ Real.sqrt C := (Real.one_le_sqrt).2 hC
      _ ≤ (2 : ℝ) ^ (10 : ℕ) * Real.sqrt C := by
        simpa using (mul_le_mul_of_nonneg_right
          (show (1 : ℝ) ≤ (2 : ℝ) ^ (10 : ℕ) by norm_num) (Real.sqrt_nonneg C))
  · calc
      1 ≤ C := hC
      _ ≤ (2 : ℝ) ^ (10 : ℕ) * C := by
        simpa using (mul_le_mul_of_nonneg_right
          (show (1 : ℝ) ≤ (2 : ℝ) ^ (10 : ℕ) by norm_num) (by linarith : 0 ≤ C))

/-- Recursive constants from Proposition \ref{P:C_k-induction}, formalized by
`inductPositiveTermsByInduction`.  The argument is the reverse distance from `n`. -/
noncomputable def C_inductPositiveTermsByInduction (n : ℕ) : ℕ → ℝ
  | 0 => (2 : ℝ) + n
  | Nat.succ 0 =>
      (2 : ℝ) + ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (10 : ℕ) *
        C_inductPositiveTermsImplyIncreaseData * C_inductPositiveTermsByInduction n 0
  | Nat.succ (Nat.succ r) =>
      (2 : ℝ) + ((n - (r + 2) : ℕ) : ℝ) * (2 : ℝ) ^ (10 : ℕ) *
      Real.sqrt
          (C_inductPositiveTermsImplyIncreaseData *
            C_inductPositiveTermsByInduction n (r + 1))

/-- This auxiliary induction establishes the admissibility side condition for
the recursive constants in `inductPositiveTermsByInduction`. -/
theorem aux_one_le_C_inductPositiveTermsByInduction (n r : ℕ) :
    1 ≤ C_inductPositiveTermsByInduction n r := by
  induction r with
  | zero =>
      change (1 : ℝ) ≤ 2 + (n : ℝ)
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  | succ r ih =>
      cases r with
      | zero =>
          simp only [C_inductPositiveTermsByInduction]
          have hinc : 0 ≤ C_inductPositiveTermsImplyIncreaseData :=
            aux_C_inductPositiveTermsImplyIncreaseData_pos.le
          have hnonneg : 0 ≤ ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (10 : ℕ) *
              C_inductPositiveTermsImplyIncreaseData * ((2 : ℝ) + n) := by
            positivity
          linarith
      | succ r =>
          simp only [C_inductPositiveTermsByInduction]
          have hprev : 0 ≤ C_inductPositiveTermsByInduction n (r + 1) := by
            linarith
          have hinc : 0 ≤ C_inductPositiveTermsImplyIncreaseData :=
            aux_C_inductPositiveTermsImplyIncreaseData_pos.le
          have hnonneg : 0 ≤ ((n - (r + 2) : ℕ) : ℝ) * (2 : ℝ) ^ (10 : ℕ) *
              Real.sqrt
                (C_inductPositiveTermsImplyIncreaseData *
                  C_inductPositiveTermsByInduction n (r + 1)) := by
            positivity
          linarith

end

end Codex.MainArgument.MainInduction
