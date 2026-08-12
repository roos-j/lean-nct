import LeanNct.Reduction.OnDiagonalMainArgument
import LeanNct.Reduction.WindowsAndPairs
import LeanNct.Reduction.BumpFunctions
import LeanNct.Reduction.Miscellany

/-!
# On-diagonal estimates from off-diagonal estimates

Formalization of the reduction subsection which turns the on-diagonal
estimates into the window and Whitney estimates used in the final reduction.
-/

namespace Codex.Reduction.OnDiagonalOffDiagonal

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal FourierTransform Real

open Codex
open Codex.Preliminaries.Notation
open Codex.Preliminaries.BumpsAndEstimates
open Codex.Preliminaries.KKernels
open Codex.Preliminaries.MKernels
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.MainArgument.SandwichKernel
open Codex.Reduction.OnDiagonalMainArgument
open Codex.Reduction.WindowsAndPairs
open Codex.Reduction.BumpFunctions
open Codex.Reduction.Miscellany

noncomputable section

/-- Turns a planar kernel into a one-coordinate `M` kernel. -/
noncomputable def aux_liftPlaneKernel (M : RealPlane → ℝ) : MKernel 1 :=
  fun y => M (y.1 0, y.2 0)

/-- Convolution of a planar kernel along the diagonal direction. -/
noncomputable def aux_diagonalConvolution (M : RealPlane → ℝ) (phi : ℝ → ℝ) :
    RealPlane → ℝ :=
  fun v => ∫ q : ℝ, M (v.1 - q, v.2 - q) * phi q

/-- The difference of standard-bump diagonal smoothings defining `L_{h,j}`. -/
noncomputable def aux_diagonalBandKernel (M : ℤ → RealPlane → ℝ) (a : ℤ → ℝ)
    (h : ℕ) (j : ℤ) : RealPlane → ℝ :=
  aux_diagonalConvolution (M j)
      (fun q => standardBumpRescale (rhoLowerScale a h j) q -
        standardBumpRescale (rhoUpperScale a h j) q)

/-- The `h`-th sequence of diagonal bands. -/
noncomputable def aux_diagonalBandSequence (D : ReductionData) (h : ℕ) :
    KernelSequence 1 :=
  fun j => aux_liftPlaneKernel (aux_diagonalBandKernel D.kernel D.a h j)

/-- The constant in Proposition \ref{P:diagonal-band-reduction}. -/
noncomputable def C_diagonalBandReduction : ℝ :=
  (2 : ℝ) ^ 4 * Real.sqrt (C_nReduction * C_increaseDataReduction) +
    (2 : ℝ) ^ 3 * C_increaseDataReduction

/--
Proposition \ref{P:diagonal-band-reduction}.  The sequence of all diagonal
frequency bands is controlled by the already initialized increase-data bound.
-/
theorem diagonalBandReduction {n : ℕ} (hn : 2 ≤ n) (D : ReductionData) :
    ∑' h : ℕ,
      kernelSequenceSeminorm n 1 (by omega) (by omega)
        (aux_diagonalBandSequence D h) ≤ ENNReal.ofReal C_diagonalBandReduction := by
  sorry

/-- The numerical estimate in Lemma \ref{constant diagonal band reduction}. -/
theorem constantDiagonalBandReduction :
    C_diagonalBandReduction < (63 / 64 : ℝ) * (2 : ℝ) ^ 480 := by
  sorry

/-- The large-scale standard-bump smoothing used in `lOneReduction`. -/
noncomputable def aux_largeScaleSmoothing (M : RealPlane → ℝ) (t : ℝ) : RealPlane → ℝ :=
  aux_diagonalConvolution M (standardBumpRescale t)

/--
Lemma \ref{lem:L1-reduction}.  Diagonal cancellation makes the diagonal
standard-bump smoothing tend to zero in (L^1) at large scales.
-/
theorem lOneReduction (M : RealPlane → ℝ) (hM : MemW0 M)
    (hcancel : ∀ ξ : ℝ, ∫ v : RealPlane,
      M v * Real.cos (2 * Real.pi * (ξ * (v.1 - v.2))) = 0) :
    Tendsto (fun t : ℝ => eLpNorm (aux_largeScaleSmoothing M t) 1 volume)
      atTop (nhds 0) := by
  sorry

/-- The Fourier transform of a planar kernel, transported to the canonical Euclidean model. -/
noncomputable def aux_planeFourier (M : RealPlane → ℝ) :
    EuclideanSpace ℝ (Fin 2) → ℂ :=
  FourierTransform.fourier
    (fun v : EuclideanSpace ℝ (Fin 2) => (M (v 0, v 1) : ℂ))

/-- The Fourier support hypothesis in Proposition \ref{P:vanishing-diagonal-reduction}. -/
def aux_frequencyDiagonalBound (D : ReductionData) : Prop :=
  ∀ j : ℤ,
    Function.support
      (aux_planeFourier (D.kernel j)) ⊆
        {z : EuclideanSpace ℝ (Fin 2) |
          |z 0 + z 1| ≤ (2 : ℝ)⁻¹ * (D.a (j - 1))⁻¹}

/--
Proposition \ref{P:vanishing-diagonal-reduction}.  The diagonal-band estimate
controls every reduction kernel with the stated transverse Fourier support.
-/
theorem vanishingDiagonalReduction {n : ℕ} (hn : 2 ≤ n) (D : ReductionData)
    (hsupport : aux_frequencyDiagonalBound D) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (fun j => aux_liftPlaneKernel (D.kernel j)) ≤
        ENNReal.ofReal C_diagonalBandReduction := by
  sorry

/-- The (L^1)-normalized rescaling of a window component. -/
noncomputable def aux_windowRescale (phi : SchwartzMap ℝ ℝ) (t : ℝ) : ℝ → ℝ :=
  fun x => t⁻¹ * phi (t⁻¹ * x)

/-- The telescoping window kernel from Proposition \ref{P:one-scale-estimate-window}. -/
noncomputable def aux_oneScaleWindowKernel (phi : SchwartzMap ℝ ℝ) (a : ℤ → ℝ)
    (j : ℤ) : RealPlane → ℝ :=
  fun v => tensorSquare (aux_windowRescale phi (a (j - 1))) v -
    tensorSquare (aux_windowRescale phi (a j)) v

/-- The sequence of telescoping window kernels. -/
noncomputable def aux_oneScaleWindowSequence (phi : SchwartzMap ℝ ℝ) (a : ℤ → ℝ) :
    KernelSequence 1 :=
  fun j => aux_liftPlaneKernel (aux_oneScaleWindowKernel phi a j)

/-- The constant in Proposition \ref{P:one-scale-estimate-window}. -/
noncomputable def C_oneScaleEstimateWindow : ℝ :=
  (2 : ℝ) ^ 9 * C_uniPair ^ 2

/-- Proposition \ref{P:one-scale-estimate-window}. -/
theorem oneScaleEstimateWindow {n : ℕ} (hn : 2 ≤ n) (a : ℤ → ℝ)
    (ha : SpacedSequence a) (phi0 phi1 : SchwartzMap ℝ ℝ)
    (hpair : uniPair phi0 phi1) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_oneScaleWindowSequence phi0 a) ≤ ENNReal.ofReal C_oneScaleEstimateWindow := by
  sorry

/-- The exact value in Lemma \ref{auto:constant-one-scale-window}. -/
theorem constantOneScaleWindow : C_oneScaleEstimateWindow = (2 : ℝ) ^ 39 := by
  sorry

/--
Lemma \ref{L:fourier-transform-window}, stated after the direct Fourier
transform of the difference of the two rescaled window functions.
-/
theorem fourierTransformWindow (a : ℤ → ℝ) (ha : SpacedSequence a)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (j : ℤ) (xi : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ =>
          (aux_windowRescale phi0 (a (j - 1)) x - aux_windowRescale phi1 (a j) x : ℂ)) xi ^ 2 =
      FourierTransform.fourier
          (fun x : ℝ => (aux_windowRescale phi0 (a (j - 1)) x : ℂ)) xi ^ 2 -
        FourierTransform.fourier
          (fun x : ℝ => (aux_windowRescale phi0 (a j) x : ℂ)) xi ^ 2 := by
  sorry

/-- Lemma \ref{lem:scaleest}. -/
theorem scaleEstimate (x lambda s : ℝ) (hlambda : 0 < lambda) (hs : 0 < s) :
    scaledBracketBump 2 (lambda * s) x ≤
      max lambda lambda⁻¹ * scaledBracketBump 2 s x := by
  sorry

/-- The non-Whitney window difference kernel. -/
noncomputable def aux_nonWhitneyKernel (phi0 phi1 : SchwartzMap ℝ ℝ) (a : ℤ → ℝ)
    (j : ℤ) : RealPlane → ℝ :=
  tensorSquare (fun x => aux_windowRescale phi0 (a (j - 1)) x -
    aux_windowRescale phi1 (a j) x)

/-- The non-Whitney kernel sequence. -/
noncomputable def aux_nonWhitneySequence (phi0 phi1 : SchwartzMap ℝ ℝ) (a : ℤ → ℝ) :
    KernelSequence 1 :=
  fun j => aux_liftPlaneKernel (aux_nonWhitneyKernel phi0 phi1 a j)

/-- The constant in the non-Whitney reduction estimate. -/
noncomputable def C_inductPositiveTermsReductionNonWhitney : ℝ :=
  C_oneScaleEstimateWindow +
    128 * max 1 ((C_uniPair / (2 * Real.pi)) ^ 4) * C_smoothDecay2 2 ^ 2 *
      C_diagonalBandReduction

/-- Proposition \ref{P:induct-positive-terms-reduction-non-whitney}. -/
theorem inductPositiveTermsReductionNonWhitney {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a) (phi0 phi1 : SchwartzMap ℝ ℝ)
    (hpair : uniPair phi0 phi1) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_nonWhitneySequence phi0 phi1 a) ≤
        ENNReal.ofReal C_inductPositiveTermsReductionNonWhitney := by
  sorry

/-- The numerical estimate in Lemma \ref{constant non Whitney reduction}. -/
theorem constantNonWhitneyReduction :
    C_inductPositiveTermsReductionNonWhitney <
      (8 / 9 : ℝ) * (2 : ℝ) ^ 541 := by
  sorry

/-- The skip-terms non-Whitney sequence. -/
noncomputable def aux_nonWhitneySkipSequence (phi0 phi1 : SchwartzMap ℝ ℝ)
    (a : ℤ → ℝ) : KernelSequence 1 :=
  fun j => aux_liftPlaneKernel
    (tensorSquare (fun x => aux_windowRescale phi0 (a (2 * j)) x -
      aux_windowRescale phi1 (a (2 * j + 1)) x))

/-- The constant in the skip-terms non-Whitney reduction. -/
noncomputable def C_inductPositiveTermsReductionNonWhitneySkip (n : ℕ) : ℝ :=
  Real.rpow 2 (1 - Real.rpow 2 (2 - n)) *
    C_inductPositiveTermsReductionNonWhitney

/-- Proposition \ref{P:induct-positive-terms-reduction-non-whitney-skip}. -/
theorem inductPositiveTermsReductionNonWhitneySkip {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a) (phi0 phi1 : SchwartzMap ℝ ℝ)
    (hpair : uniPair phi0 phi1) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_nonWhitneySkipSequence phi0 phi1 a) ≤
        ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant non Whitney skip reduction}. -/
theorem constantNonWhitneySkipReduction {n : ℕ} (hn : 2 ≤ n) :
    C_inductPositiveTermsReductionNonWhitneySkip n <
      (8 / 9 : ℝ) * (2 : ℝ) ^ 542 := by
  sorry

/-- The hypotheses on the base kernel in the Whitney reduction. -/
structure WhitneyKernelData where
  kernel : RealPlane → ℝ
  kernel_memW0 : MemW0 kernel
  kernel_nonzero : kernel ≠ 0
  symmetric : ∀ v : RealPlane, kernel v = kernel (v.2, v.1)
  positive : ∀ g : ℝ → ℝ, Codex.Reduction.BumpFunctions.aux_bounded g →
    0 ≤ ∫ v : RealPlane, g v.1 * g v.2 * kernel v
  fourier_support :
    Function.support (aux_planeFourier kernel) ⊆
      {v : EuclideanSpace ℝ (Fin 2) | v 0 ∈ aux_annulusOne 1 ((2 : ℝ) ^ 3) ∧
        v 1 ∈ aux_annulusOne 1 ((2 : ℝ) ^ 3)}
  diagonal_derivative : ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
    ‖iteratedDeriv m
      (fun z : ℝ => aux_planeFourier kernel (WithLp.toLp 2 ![z, -z])) xi‖ ≤ 1
  decay : ∀ v : RealPlane, |kernel v| ≤
    ∑ u : Fin 2,
      scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2)

/-- The two-dimensional normalized rescaling of a Whitney kernel. -/
noncomputable def aux_planeRescale (t : ℝ) (Psi : RealPlane → ℝ) : RealPlane → ℝ :=
  fun v => t⁻¹ ^ 2 * Psi (t⁻¹ * v.1, t⁻¹ * v.2)

/-- The sequence of Whitney rescalings. -/
noncomputable def aux_whitneySequence (Psi : RealPlane → ℝ) (a : ℤ → ℝ) :
    KernelSequence 1 :=
  fun j => aux_liftPlaneKernel (aux_planeRescale (a j) Psi)

/-- The constant in the Whitney-with-gap reduction. -/
noncomputable def C_inductPositiveTermsReductionWhitneyGap (n : ℕ) : ℝ :=
  2 * C_inductPositiveTermsReductionNonWhitneySkip n +
    (2 : ℝ) ^ 19 * (C_uniPair ^ 2 + C_phiJProperties ^ 2) *
      C_diagonalBandReduction

/-- Proposition \ref{P:induct-positive-terms-reduction-whitney-gap}. -/
theorem inductPositiveTermsReductionWhitneyGap {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a)
    (hgap : ∀ j : ℤ, (2 : ℝ) ^ 11 * a (j - 1) ≤ a j)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (Psi : WhitneyKernelData) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_whitneySequence Psi.kernel a) ≤
        ENNReal.ofReal (C_inductPositiveTermsReductionWhitneyGap n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant Whitney gap reduction}. -/
theorem constantWhitneyGapReduction {n : ℕ} (hn : 2 ≤ n) :
    C_inductPositiveTermsReductionWhitneyGap n <
      (127 / 128 : ℝ) * (2 : ℝ) ^ 553 := by
  sorry

/-- The constant in the ordinary Whitney reduction. -/
noncomputable def C_inductPositiveTermsReductionWhitney (n : ℕ) : ℝ :=
  11 * C_inductPositiveTermsReductionWhitneyGap n

/-- Proposition \ref{P:induct-positive-terms-reduction-whitney}. -/
theorem inductPositiveTermsReductionWhitney {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (Psi : WhitneyKernelData) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_whitneySequence Psi.kernel a) ≤
        ENNReal.ofReal (C_inductPositiveTermsReductionWhitney n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant Whitney reduction}. -/
theorem constantWhitneyReduction {n : ℕ} (hn : 2 ≤ n) :
    C_inductPositiveTermsReductionWhitney n < (2 : ℝ) ^ 557 := by
  sorry

/-- The product-type Whitney kernel sequence. -/
noncomputable def aux_whitneyProductSequence (psi : SchwartzMap ℝ ℝ) (a : ℤ → ℝ) :
    KernelSequence 1 :=
  fun j => aux_liftPlaneKernel
    (tensorSquare (aux_windowRescale psi (a j)))

/-- The constant in the product-type Whitney reduction. -/
noncomputable def C_inductPositiveTermsReductionWhitneyProduct (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 12 * C_inductPositiveTermsReductionWhitney n

/-- Proposition \ref{P:induct-positive-terms-reduction-whitney-product}. -/
theorem inductPositiveTermsReductionWhitneyProduct {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a) (psi : SchwartzMap ℝ ℝ)
    (hsupport : Function.support
      (FourierTransform.fourier (fun x : ℝ => (psi x : ℂ))) ⊆
        aux_annulusOne 1 ((2 : ℝ) ^ 3))
    (hderiv : ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m (FourierTransform.fourier (fun x : ℝ => (psi x : ℂ))) xi‖ ≤ 1) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_whitneyProductSequence psi a) ≤
        ENNReal.ofReal (C_inductPositiveTermsReductionWhitneyProduct n) := by
  sorry

/-- The numerical estimate in Lemma \ref{constant Whitney product reduction}. -/
theorem constantWhitneyProductReduction {n : ℕ} (hn : 2 ≤ n) :
    C_inductPositiveTermsReductionWhitneyProduct n < (2 : ℝ) ^ 569 := by
  sorry

end

end Codex.Reduction.OnDiagonalOffDiagonal
