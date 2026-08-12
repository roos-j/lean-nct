import LeanNct.Reduction.TwistedAverages
import LeanNct.Reduction.WindowsAndPairs
import LeanNct.Reduction.BumpFunctions
import LeanNct.Reduction.SmoothingDecomposition
import LeanNct.Reduction.Miscellany
import LeanNct.Reduction.OnDiagonalOffDiagonal

/-!
# Final reduction

Formalization of the ``Final reduction: proof of main theorem'' subsection of
the reduction argument.  This module deliberately depends on the shared
reduction-level twisted averages rather than `Introduction`, so that the final
reduction remains on the acyclic side of the import graph.
-/

namespace Codex.Reduction.FinalReduction

open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform Real

open Codex.Preliminaries.KKernels
open Codex.Reduction.TwistedAverages
open Codex.Reduction.WindowsAndPairs
open Codex.Reduction.BumpFunctions
open Codex.Reduction.SmoothingDecomposition
open Codex.Reduction.Miscellany
open Codex.Reduction.OnDiagonalOffDiagonal

noncomputable section

/-- The exponent $\alpha(n)=1-2^{-n+2}$ fixed in the final reduction. -/
noncomputable def variationExponent (n : ℕ) : ℝ :=
  1 - (2 : ℝ) ^ (-(n : ℝ) + 2)

/-- The indicator kernel used in the statement of the main twisted theorem. -/
noncomputable def unitIntervalIndicator : ℝ → ℝ :=
  (Set.Icc (0 : ℝ) 1).indicator fun _ ↦ (1 : ℝ)

/-- A normalized tuple of real Schwartz functions in the coordinate model used by the
reduction modules. -/
abbrev ReductionNormalizedTuple (n : ℕ) :=
  {f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ //
    ∀ i, eLpNorm (f i) ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2)) volume = 1}

/-- A finite dyadic chain for the long-variation estimates. -/
abbrev aux_dyadicChain (J : ℕ) := TwistedDyadicChain J

/-- A finite positive chain for the full variation estimates. -/
abbrev aux_scaleChain (J : ℕ) := TwistedScaleChain J

/-- The squared jump-energy along an arbitrary positive scale chain. -/
noncomputable def aux_jumpEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (J : ℕ)
    (t : aux_scaleChain J) : ℝ≥0∞ :=
  twistedJumpEnergy chi (fun i x ↦ f i x) J t

/-- The squared jump-energy along a dyadic scale chain. -/
noncomputable def aux_dyadicJumpEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (J : ℕ)
    (k : aux_dyadicChain J) : ℝ≥0∞ :=
  twistedDyadicJumpEnergy chi (fun i x ↦ f i x) J k

/-- The Fourier support/derivative hypotheses common to `mainAuxOne` and `mainAuxTwo`.
This raw-function formulation also applies directly to the logarithmic derivative
in `shortLongFtcReduction`. -/
def aux_mainAuxiliaryFourierHypotheses (psi : ℝ → ℝ) : Prop :=
  Function.support (FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ))) ⊆
      Codex.Reduction.BumpFunctions.aux_annulusOne 1 ((2 : ℝ) ^ 2) ∧
    ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m (FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ))) xi‖ ≤ 1

/-- The Schwartz-function specialization of the main auxiliary hypotheses. -/
def aux_mainAuxiliaryHypotheses (psi : SchwartzMap ℝ ℝ) : Prop :=
  aux_mainAuxiliaryFourierHypotheses (fun x ↦ psi x)

/-- The additional `T\psi` hypothesis in `mainAuxTwo`. -/
def aux_mainAuxiliaryTwoHypotheses (psi : SchwartzMap ℝ ℝ) : Prop :=
  aux_mainAuxiliaryHypotheses psi ∧
    ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m (FourierTransform.fourier
        (Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ (psi x : ℂ))) ) xi‖ ≤ 1

/-- The common finite-variation conclusion for a bump in the final reduction. -/
def aux_variationBound {n : ℕ} (C : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) : Prop :=
  ∀ J : ℕ, 0 < J → ∀ t : aux_scaleChain J,
    aux_jumpEnergy chi f J t ≤
      ENNReal.ofReal C * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)

/-- The common dyadic finite-variation conclusion for a bump. -/
def aux_dyadicVariationBound {n : ℕ} (C : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) : Prop :=
  ∀ J : ℕ, 0 < J → ∀ k : aux_dyadicChain J,
    aux_dyadicJumpEnergy chi f J k ≤
      ENNReal.ofReal C * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)

/-- The constant in Lemma \ref{lem:main_aux1}. -/
noncomputable def C_mainAuxOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 4 * C_inductPositiveTermsReductionWhitneyProduct n

/--
\begin{lemma}\label{lem:main_aux1}
If a Schwartz function $\psi$ has Fourier support in $\operatorname{Ann}_1(1,2^2)$
and Fourier derivatives through order two bounded by one, then the dyadic square sum
of $A_{2^{k_j}t}(\psi)$ is bounded by
$C_{\ref{lem:main_aux1}}J^{\alpha(n)}$.
\end{lemma}
-/
theorem mainAuxOne {n : ℕ} (hn : 2 ≤ n) (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryHypotheses psi)
    (f : ReductionNormalizedTuple n) (t : ℝ) (ht : t ∈ Set.Icc 1 2)
    (J : ℕ) (hJ : 0 < J) (k : aux_dyadicChain J) :
    ∑ j : Fin J,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ 2 ≤
      ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant main auxiliary one}. -/
theorem constantMainAuxiliaryOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxOne n < (2 : ℝ) ^ 573 := by
  sorry

/--
\begin{lemma}[Long and short variation]\label{lem:shortlongftc_reduction}
Under the `mainAuxOne` assumptions for $T\phi$, a dyadic long-variation bound
$A$ yields the full-variation bound
$2^4 C_{\ref{lem:main_aux1}}J^{\alpha(n)}+2A$.
\end{lemma}
-/
theorem shortLongFtcReduction {n : ℕ} (hn : 2 ≤ n) (phi : SchwartzMap ℝ ℝ)
    (hTphi : aux_mainAuxiliaryFourierHypotheses
      (Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ phi x)))
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J) (A : ℝ)
    (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1) :
    aux_variationBound (16 * C_mainAuxOne n + 2 * A) (fun x ↦ phi x) f.1 := by
  sorry

/-- The constant in Lemma \ref{lem:mainbump1_long1}. -/
noncomputable def C_mainBumpOneLongOne (n : ℕ) : ℝ :=
  (2 * C_uniPair) ^ 2 * C_mainAuxOne n

/-- Lemma \ref{lem:mainbump1_long1}. -/
theorem mainBumpOneLongOne {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (k : aux_dyadicChain J) :
    ∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 ≤
      ENNReal.ofReal (C_mainBumpOneLongOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant main bump one long one}. -/
theorem constantMainBumpOneLongOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLongOne n < (2 : ℝ) ^ 605 := by
  sorry

/-- The constant in Lemma \ref{lem:mainbump1_long2}. -/
noncomputable def C_mainBumpOneLongTwo (n : ℕ) : ℝ :=
  2 * C_inductPositiveTermsReductionNonWhitneySkip n

/-- Lemma \ref{lem:mainbump1_long2}. -/
theorem mainBumpOneLongTwo {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (k : aux_dyadicChain J) :
    ∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 ≤
      ENNReal.ofReal (C_mainBumpOneLongTwo n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant main bump one long two}. -/
theorem constantMainBumpOneLongTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLongTwo n < (2 : ℝ) ^ 543 := by
  sorry

/-- The constant in Lemma \ref{lem:mainbump1_long}. -/
noncomputable def C_mainBumpOneLong (n : ℕ) : ℝ :=
  2 * (C_mainBumpOneLongOne n + C_mainBumpOneLongTwo n)

/-- Lemma \ref{lem:mainbump1_long}. -/
theorem mainBumpOneLong {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) :
    aux_dyadicVariationBound (C_mainBumpOneLong n) (fun x ↦ phi0 x) f.1 := by
  sorry

/-- The numerical estimate in Lemma \ref{constant main bump one long}. -/
theorem constantMainBumpOneLong {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLong n < (2 : ℝ) ^ 606 := by
  sorry

/-- The constant in Lemma \ref{lem:mainbump1}. -/
noncomputable def C_mainBumpOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 4 * (3 * C_uniPair) ^ 2 * C_mainAuxOne n +
    2 * C_mainBumpOneLong n

/-- Lemma \ref{lem:mainbump1}. -/
theorem mainBumpOne {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) :
    aux_variationBound (C_mainBumpOne n) (fun x ↦ phi0 x) f.1 := by
  sorry

/-- The numerical estimate in Lemma \ref{constant main bump one}. -/
theorem constantMainBumpOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOne n < (2 : ℝ) ^ 610 := by
  sorry

/-- The constant in Lemma \ref{lem:main_aux2}. -/
noncomputable def C_mainAuxTwo (n : ℕ) : ℝ :=
  24 * C_mainAuxOne n

/-- Lemma \ref{lem:main_aux2}. -/
theorem mainAuxTwo {n : ℕ} (hn : 2 ≤ n) (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryTwoHypotheses psi)
    (f : ReductionNormalizedTuple n) :
    aux_variationBound (C_mainAuxTwo n) (fun x ↦ psi x) f.1 := by
  sorry

/-- The numerical estimate in Lemma \ref{constant main auxiliary two}. -/
theorem constantMainAuxiliaryTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxTwo n < (2 : ℝ) ^ 578 := by
  sorry

/-- The constant in Lemma \ref{lem:mainbump2}. -/
noncomputable def C_mainBumpTwo (n : ℕ) : ℝ :=
  C_mainAuxTwo n * C_absDerivFourierTPhiThreeLe 2 ^ 2

/-- Lemma \ref{lem:mainbump2}. -/
theorem mainBumpTwo {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : -2 ≤ k) :
    aux_variationBound (C_mainBumpTwo n * (2 : ℝ) ^ (-2 * k))
      (windowBasedBumpFunctions.phiZero b k) f.1 := by
  sorry

/-- The numerical estimate in Lemma \ref{constant main bump two}. -/
theorem constantMainBumpTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpTwo n < (2 : ℝ) ^ 658 := by
  sorry

/-- The constant in Lemma \ref{lem:leftbump}. -/
noncomputable def C_leftBump (n : ℕ) : ℝ :=
  C_mainAuxTwo n * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2

/-- Lemma \ref{lem:leftbump}. -/
theorem leftBump {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) :
    aux_variationBound (C_leftBump n * (2 : ℝ) ^ (2 * k))
      (windowBasedBumpFunctions.phiOne b k) f.1 := by
  sorry

/-- The numerical estimate in Lemma \ref{constant left bump}. -/
theorem constantLeftBump {n : ℕ} (hn : 2 ≤ n) :
    C_leftBump n < (2 : ℝ) ^ 636 := by
  sorry

/-- The first short-variation constant in Lemma \ref{lem:leftbump1_short1}. -/
noncomputable def C_leftBumpOneShortOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 2 * C_inductPositiveTermsReductionWhitney n * C_thetaPrimitive 2 ^ 2 *
    C_thetaTOffcenter

/-- Lemma \ref{lem:leftbump1_short1}. -/
theorem leftBumpOneShortOne {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (k : ℤ) (hk : k ≤ -1) (J : ℕ) (hJ : 0 < J)
    (ell : aux_dyadicChain J) :
    ∑ j : Fin J, ENNReal.ofReal ((2 : ℝ) ^ (-(3 : ℤ) * k / 2)) *
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (ell.1 j.castSucc))
        (windowBasedBumpFunctions.phiFour b k) (fun i x ↦ f.1 i x)) 2 volume ^ 2 ≤
      ENNReal.ofReal (C_leftBumpOneShortOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant left bump one short one}. -/
theorem constantLeftBumpOneShortOne {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOneShortOne n < (2 : ℝ) ^ 628 := by
  sorry

/-- The second short-variation auxiliary constant in Lemma \ref{lem:leftbump1_short2}. -/
noncomputable def C_leftBumpOneShortTwoAuxiliary : ℝ :=
  max (C_thetaPrimitive 2) (max (C_thetaDecay 2) (C_thetaDecay 3))

/-- The second short-variation constant in Lemma \ref{lem:leftbump1_short2}. -/
noncomputable def C_leftBumpOneShortTwo (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 4 * C_inductPositiveTermsReductionWhitney n * C_thetaTOffcenter *
    C_leftBumpOneShortTwoAuxiliary ^ 2

/-- Lemma \ref{lem:leftbump1_short2}. -/
theorem leftBumpOneShortTwo {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (k : ℤ) (hk : k ≤ -1) (J : ℕ) (hJ : 0 < J)
    (ell : aux_dyadicChain J) :
    ∑ j : Fin J, ENNReal.ofReal ((2 : ℝ) ^ (k / 2)) *
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (ell.1 j.castSucc))
        (Codex.Reduction.BumpFunctions.aux_T (windowBasedBumpFunctions.phiFour b k))
        (fun i x ↦ f.1 i x)) 2 volume ^ 2 ≤
      ENNReal.ofReal (C_leftBumpOneShortTwo n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant left bump one short two}. -/
theorem constantLeftBumpOneShortTwo {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOneShortTwo n < (2 : ℝ) ^ 630 := by
  sorry

/-- The long-variation constant in Lemma \ref{lem:leftbump1_long}. -/
noncomputable def C_leftBumpOneLong (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 6 * C_inductPositiveTermsReductionWhitney n * C_thetaPrimitive 2 ^ 2

/-- Lemma \ref{lem:leftbump1_long}. -/
theorem leftBumpOneLong {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) :
    aux_dyadicVariationBound (C_leftBumpOneLong n * (2 : ℝ) ^ (k / 2))
      (windowBasedBumpFunctions.phiFour b k) f.1 := by
  sorry

/-- The numerical estimate in Lemma \ref{constant left bump one long}. -/
theorem constantLeftBumpOneLong {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOneLong n < (2 : ℝ) ^ 625 := by
  sorry

/-- The constant in Lemma \ref{lem:leftbump1}. -/
noncomputable def C_leftBumpOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 7 * Real.sqrt (C_leftBumpOneShortOne n) *
      Real.sqrt (C_leftBumpOneShortTwo n) + 2 * C_leftBumpOneLong n

/-- Lemma \ref{lem:leftbump1}. -/
theorem leftBumpOne {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) :
    aux_variationBound (C_leftBumpOne n * (2 : ℝ) ^ (k / 2))
      (windowBasedBumpFunctions.phiTwo b k) f.1 := by
  sorry

/-- The numerical estimate in Lemma \ref{constant left bump one}. -/
theorem constantLeftBumpOne {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOne n < (2 : ℝ) ^ 636 := by
  sorry

/-- The final constant in the proof of Theorem \ref{thm:nct main real}. -/
noncomputable def C_mainTwistedTheorem (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 2 *
    (C_mainBumpOne n + (2 : ℝ) ^ 6 * C_mainBumpTwo n + C_leftBump n +
      (2 : ℝ) ^ 6 * C_leftBumpOne n)

/--
The reduction-side version of Theorem \ref{thm:nct main real}.  It has exactly
the same conclusion as `Codex.Introduction.mainTwistedTheorem`, but is stated
over the shared `Codex.Reduction.TwistedAverages` definitions to keep imports
acyclic.
-/
theorem mainTwistedTheoremReduction {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ), 0 < J → ∀ (t : Fin (J + 1) → ℝ),
      StrictMono t → (∀ j, 0 < t j) →
      ∀ f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ,
        (∀ i, eLpNorm (f i) ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2)) volume = 1) →
        ∑ j : Fin J, eLpNorm
            (fun x ↦ twistedAverageAtScale (t j.succ) unitIntervalIndicator
                (fun i y ↦ f i y) x -
              twistedAverageAtScale (t j.castSucc) unitIntervalIndicator
                (fun i y ↦ f i y) x)
            2 volume ^ 2 ≤
          ENNReal.ofReal C * ENNReal.ofReal
            ((J : ℝ) ^ (1 - (2 : ℝ) ^ (-(n : ℝ) + 2))) := by
  sorry

end

end Codex.Reduction.FinalReduction
