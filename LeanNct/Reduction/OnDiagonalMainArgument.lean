import LeanNct.MainArgument.MainInduction

/-!
# On-diagonal estimates from the main argument

Formalization of the subsection ``On-diagonal from main argument'' in the
reduction argument.  The shared data package below is also used by the next
subsection, which passes from these estimates to the off-diagonal estimates.
-/

namespace Codex.Reduction.OnDiagonalMainArgument

open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform Real

open Codex
open Codex.Preliminaries.Notation
open Codex.Preliminaries.BumpsAndEstimates
open Codex.Preliminaries.KKernels
open Codex.Preliminaries.MKernels
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN
open Codex.MainArgument.MainInduction

noncomputable section

/-- The exponent \(\nu\) fixed at the start of the on-diagonal reduction. -/
noncomputable def aux_reductionNu (n : ℕ) : ℝ :=
  if n = 2 then -1 else -(1 / 2 : ℝ)

/-- A member of the finite family \(\mathcal P\) in the reduction argument. -/
structure ReductionScaleTriple (a : ℤ → ℝ) where
  left : ℤ → ℝ
  right : ℤ → ℝ
  orientation : Fin 2
  left_spaced : SpacedSequence left
  right_spaced : SpacedSequence right
  left_distance : SequenceDistance a left ≤ (1 : WithTop ℕ)
  right_distance : SequenceDistance a right ≤ (1 : WithTop ℕ)
  left_le_base : ∀ j : ℤ, left j ≤ a j
  right_le_base : ∀ j : ℤ, right j ≤ a j

/--
The hypotheses on \(a\), \(\mathcal P\), and \((M_j)_j\) shared by the
reduction variants of the on-diagonal propositions.  It directly packages
the hypotheses preceding Proposition \ref{lem:increase-data-bracket-domination}.
-/
structure ReductionData where
  a : ℤ → ℝ
  a_spaced : SpacedSequence a
  triples : Finset (ReductionScaleTriple a)
  triples_card : triples.card ≤ 5
  kernel : ℤ → RealPlane → ℝ
  kernel_memW0 : ∀ j : ℤ, MemW0 (kernel j)
  diagonal_cancellation : ∀ j ξ : ℤ, ∫ v : RealPlane,
    kernel j v * Real.cos (2 * Real.pi * ((ξ : ℝ) * (v.1 - v.2))) = 0
  kernel_decay : ∀ j v, |kernel j v| ≤
    ∑ q ∈ triples,
      scaledBracketBumpReal (3 / 2 : ℝ) (q.left j) ((W q.orientation v).1) *
        scaledBracketBumpReal (3 / 2 : ℝ) (q.right j) ((W q.orientation v).2)

/-- The lower scale \(\lambda^-_{h,j}\) in the definition of \(\rho_{h,j}\). -/
noncomputable def rhoLowerScale (a : ℤ → ℝ) (h : ℕ) (j : ℤ) : ℝ :=
  if h = 0 then a (j - 1) else (2 : ℝ) ^ (h - 1) * a j

/-- The upper scale \(\lambda^+_{h,j}\) in the definition of \(\rho_{h,j}\). -/
noncomputable def rhoUpperScale (a : ℤ → ℝ) (h : ℕ) (j : ℤ) : ℝ :=
  (2 : ℝ) ^ h * a j

/-- The lower Gaussian scale \(\mu^-_{h,j}\). -/
noncomputable def rhoGaussianLowerScale (a : ℤ → ℝ) (h : ℕ) (j : ℤ) : ℝ :=
  (2 : ℝ) ^ h * a (j - 1)

/-- The upper Gaussian scale \(\mu^+_{h,j}\). -/
noncomputable def rhoGaussianUpperScale (a : ℤ → ℝ) (h : ℕ) (j : ℤ) : ℝ :=
  (2 : ℝ) ^ h * a j

/--
The kernel \(\rho_{h,j}\) of Lemma \ref{lem:rho-kernels-reduction}, expressed
through the existing four-scale Gaussian kernel construction.
-/
noncomputable def rhoKernel (n : ℕ) (a : ℤ → ℝ) (h : ℕ) (j : ℤ) : ℝ → ℝ :=
  fun x => (fourScaleGaussianRho
    (FourierTransform.fourier (fun y : ℝ => (standardBump y : ℂ)))
    (rhoGaussianLowerScale a h j) (rhoGaussianUpperScale a h j)
    (rhoLowerScale a h j) (rhoUpperScale a h j) (aux_reductionNu n) x).re

/-- The diagonal convolution producing \(N_{h,j}\) in the reduction. -/
noncomputable def reductionNKernel (n : ℕ) (D : ReductionData) (h : ℕ) (j : ℤ) :
    RealPlane → ℝ :=
  fun v => ∫ p : ℝ, D.kernel j (v.1 - p, v.2 - p) * rhoKernel n D.a h j p

/-- The square-root Gaussian multiplier \(\sigma_{h,j}=s(2^h a,j)\). -/
noncomputable def reductionSigma (D : ReductionData) (h : ℕ) (j : ℤ) : ℝ → ℝ :=
  squareRootGaussianDifference (fun r => (2 : ℝ) ^ h * D.a r)
    (smul_mem_A D.a_spaced (by positivity)) j

/-- The majorant kernel \(\widetilde M_{h,j}\) used in `increaseDataReduction`. -/
noncomputable def reductionMajorantKernel (n : ℕ) (D : ReductionData) (h : ℕ) (j : ℤ) :
    MKernel 2 :=
  fun y => |reductionNKernel n D h j (y.1 0, y.2 0)| *
    reductionSigma D h j (y.1 1) * reductionSigma D h j (y.2 1)

/-- The rescaled pair \(p_{h,b,m}\) in Gaussian expansion. -/
noncomputable def gaussianExpansionPair (beta : SequencePair) (m : Fin 2 → ℕ) : SequencePair :=
  fun r j => (2 : ℝ) ^ (m r) * beta r j

/-- The geometric weight in the two-coordinate Gaussian expansion. -/
noncomputable def gaussianExpansionWeight (m : Fin 2 → ℕ) : ℝ :=
  Real.rpow 2 (-((m 0 + m 1 : ℕ) : ℝ) / 6)

/-- The numerical constant in Lemma \ref{lem:rho-kernels-reduction}. -/
noncomputable def C_rhoKernelsReduction : ℝ :=
  (2 : ℝ) ^ (21 : ℕ) *
    (C_meanFourScaleGaussianKernel 2 + C_fourScaleGaussianKernel 2)

/--
Lemma \ref{lem:rho-kernels-reduction}.  The existing four-scale Gaussian
estimates supply this second, reduction-specific use of Gaussian domination.
-/
theorem rhoKernelsReduction {n : ℕ} (hn : 2 ≤ n) (a : ℤ → ℝ)
    (ha : SpacedSequence a) (h : ℕ) (j : ℤ) :
    MemW0 (rhoKernel n a h j) ∧
      (∀ x p : ℝ, 1 ≤ h →
        |rhoKernel n a h j (x + p) - rhoKernel n a h j x| ≤
          C_rhoKernelsReduction * min 1 ((rhoUpperScale a h j)⁻¹ * |p|) *
            (scaledBracketBumpReal 2 (rhoUpperScale a h j) (x + p) +
              scaledBracketBumpReal 2 (rhoUpperScale a h j) x)) ∧
      ∀ x : ℝ, |rhoKernel n a h j x| ≤
        C_rhoKernelsReduction *
          (scaledBracketBumpReal 2 (rhoLowerScale a h j) x +
            scaledBracketBumpReal 2 (rhoUpperScale a h j) x) := by
  sorry

/-- The explicit numerical estimate in Lemma \ref{constant rho kernels reduction}. -/
theorem constantRhoKernelsReduction : C_rhoKernelsReduction < (2 : ℝ) ^ (66 : ℕ) := by
  sorry

/--
Lemma \ref{lem:affine-diagonal-cancellation-reduction}.  The displayed
Fourier-side cancellation is represented in `ReductionData` by its real
diagonal Fourier integral.
-/
theorem affineDiagonalCancellationReduction (M : RealPlane → ℝ) (hM : MemW0 M)
    (hcancel : ∀ ξ : ℤ, ∫ v : RealPlane,
      M v * Real.cos (2 * Real.pi * ((ξ : ℝ) * (v.1 - v.2))) = 0) (x : ℝ) :
    ∫ q : ℝ, M (x + q, q) = 0 := by
  sorry

/-- The cardinality constant in bracket domination. -/
def C_increaseDataBracketDominationCard : ℕ := 2 ^ 6

/-- The pointwise constant in Proposition \ref{lem:increase-data-bracket-domination}. -/
noncomputable def C_increaseDataBracketDomination : ℝ :=
  (2 : ℝ) ^ (10 : ℕ) * C_rhoKernelsReduction

/--
Proposition \ref{lem:increase-data-bracket-domination}.  It supplies a finite
family of nearby scale pairs which dominates the reduction kernels by
products of \(7/6\)-bracket bumps.
-/
theorem increaseDataBracketDomination {n : ℕ} (hn : 2 ≤ n) (D : ReductionData)
    (h : ℕ) :
    ∃ B : Finset (SequencePair × Fin 2),
      B.card ≤ C_increaseDataBracketDominationCard ∧
      (∀ b ∈ B, ∀ r : Fin 2,
        SequenceDistance D.a (b.1 r) ≤ ((1 + h : ℕ) : WithTop ℕ)) ∧
      (∀ j : ℤ, ∀ v : RealPlane,
        |reductionNKernel n D h j v| ≤
          C_increaseDataBracketDomination * Real.rpow 2 (-(h : ℝ) / 3) *
            ∑ b ∈ B,
              scaledBracketBumpReal (7 / 6 : ℝ) (b.1 0 j) ((W b.2 v).1) *
                scaledBracketBumpReal (7 / 6 : ℝ) (b.1 1 j) ((W b.2 v).2)) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant increase data bracket domination}. -/
theorem constantIncreaseDataBracketDomination :
    C_increaseDataBracketDomination < (3 / 5 : ℝ) * (2 : ℝ) ^ (76 : ℕ) := by
  sorry

/-- The constant in Proposition \ref{lem:increase-data-Gaussian-expansion}. -/
noncomputable def C_increaseDataGaussianExpansion : ℝ :=
  (2 : ℝ) ^ (3 : ℕ) * C_gaussianDomination ^ (2 : ℕ) *
    C_increaseDataBracketDomination

/--
Proposition \ref{lem:increase-data-Gaussian-expansion}.  This is the
Gaussian-expansion version of the preceding bracket domination estimate.
-/
theorem increaseDataGaussianExpansion {n : ℕ} (hn : 2 ≤ n) (D : ReductionData)
    (h : ℕ) :
    ∃ B : Finset (SequencePair × Fin 2),
      B.card ≤ C_increaseDataBracketDominationCard ∧
      (∀ b ∈ B, ∀ m : Fin 2 → ℕ,
        SequenceDistance (b.1 0) (gaussianExpansionPair b.1 m 0) ≤
          ((m 0 : ℕ) : WithTop ℕ) ∧
        SequenceDistance (b.1 1) (gaussianExpansionPair b.1 m 1) ≤
          ((m 1 : ℕ) : WithTop ℕ)) ∧
      (∀ j : ℤ, ∀ v : RealPlane,
        |reductionNKernel n D h j v| ≤
          C_increaseDataGaussianExpansion * Real.rpow 2 (-(h : ℝ) / 3) *
            ∑' m : Fin 2 → ℕ, gaussianExpansionWeight m *
              ∑ b ∈ B,
                twoDimensionalGaussian (fun r => gaussianExpansionPair b.1 m r j) b.2 v) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant increase data Gaussian expansion}. -/
theorem constantIncreaseDataGaussianExpansion :
    C_increaseDataGaussianExpansion < (123 / 128 : ℝ) * (2 : ℝ) ^ (91 : ℕ) := by
  sorry

/-- The constant in Lemma \ref{lem:N-reduction}. -/
noncomputable def C_nReduction : ℝ := (2 : ℝ) ^ (9 : ℕ) * C_rhoKernelsReduction

/-- Lemma \ref{lem:N-reduction}. -/
theorem nReduction {n : ℕ} (hn : 2 ≤ n) (D : ReductionData) (h : ℕ) (j : ℤ) :
    MemW0 (reductionNKernel n D h j) ∧
      eLpNorm (reductionNKernel n D h j) 1 volume ≤ ENNReal.ofReal C_nReduction := by
  sorry

/-- The numerical estimate in Lemma \ref{constant N reduction}. -/
theorem constantNReduction : C_nReduction < (3 / 5 : ℝ) * (2 : ℝ) ^ (75 : ℕ) := by
  sorry

/-- The constant in Proposition \ref{P:increase-data-reduction}. -/
noncomputable def C_increaseDataReduction : ℝ :=
  (2 : ℝ) ^ (22 : ℕ) * C_inductPositiveTermsTheorem *
    C_increaseDataGaussianExpansion * C_increaseDataBracketDominationCard

/--
Proposition \ref{P:increase-data-reduction}.  Its proof is the point at
which the already proved positive-terms induction is reused.
-/
theorem increaseDataReduction {n : ℕ} (hn : 2 ≤ n) (D : ReductionData) (h : ℕ) :
    kernelSequenceSeminorm n 2 (by omega) hn
      (fun j => reductionMajorantKernel n D h j) ≤
      ENNReal.ofReal (C_increaseDataReduction * Real.rpow 2 (-(h : ℝ) / 4)) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant increase data reduction}. -/
theorem constantIncreaseDataReduction :
    C_increaseDataReduction < (31 / 32 : ℝ) * (2 : ℝ) ^ (477 : ℕ) := by
  sorry

end

end Codex.Reduction.OnDiagonalMainArgument
