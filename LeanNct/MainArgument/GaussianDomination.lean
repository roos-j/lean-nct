import LeanNct.MainArgument.MultipliersHLN
import LeanNct.Preliminaries.ConvolutionAlongVector

/-!
# Gaussian domination

Formalization of the subsection ``Gaussian domination''.
-/

namespace Codex.MainArgument.GaussianDomination

open MeasureTheory
open scoped BigOperators ENNReal Real FourierTransform

open Codex.Preliminaries.Notation
open Codex.Preliminaries.Gaussians
open Codex.Preliminaries.BumpsAndEstimates
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN

noncomputable section

/-- This auxiliary directional derivative is needed to write the manuscript's
`(\partial_0+\partial_1)` in the raw product-coordinate model of `\mathbb R^2`. -/
def aux_diagonalDerivative (f : RealPlane → ℝ) (v : RealPlane) : ℝ :=
  deriv (fun t : ℝ => f (v.1 + t, v.2 + t)) 0

/-- This auxiliary product-rule identity evaluates the manuscript's diagonal derivative on a
tensor product of two copies of a differentiable one-dimensional function. -/
theorem aux_diagonalDerivative_tensor {f : ℝ → ℝ} {v : RealPlane}
    (hf₀ : DifferentiableAt ℝ f v.1) (hf₁ : DifferentiableAt ℝ f v.2) :
    aux_diagonalDerivative (fun w : RealPlane => f w.1 * f w.2) v =
      deriv f v.1 * f v.2 + f v.1 * deriv f v.2 := by
  have harg₀base :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := v.1)).add (hasDerivAt_id (x := (0 : ℝ)))
  have harg₀ : HasDerivAt (fun t : ℝ => v.1 + t) 1 0 := by
    have heq : (fun t : ℝ => v.1 + t) =ᶠ[nhds 0]
        ((fun _ : ℝ => v.1) + id) := by
      filter_upwards [] with t
      rfl
    have harg₀' : HasDerivAt (fun t : ℝ => v.1 + t) (0 + 1) 0 :=
      harg₀base.congr_of_eventuallyEq heq
    simpa using harg₀'
  have harg₁base :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := v.2)).add (hasDerivAt_id (x := (0 : ℝ)))
  have harg₁ : HasDerivAt (fun t : ℝ => v.2 + t) 1 0 := by
    have heq : (fun t : ℝ => v.2 + t) =ᶠ[nhds 0]
        ((fun _ : ℝ => v.2) + id) := by
      filter_upwards [] with t
      rfl
    have harg₁' : HasDerivAt (fun t : ℝ => v.2 + t) (0 + 1) 0 :=
      harg₁base.congr_of_eventuallyEq heq
    simpa using harg₁'
  have hleft : HasDerivAt (fun t : ℝ => f (v.1 + t)) (deriv f v.1) 0 := by
    have hf₀' : HasDerivAt f (deriv f v.1) (v.1 + 0) := by
      simpa using hf₀.hasDerivAt
    have hleft₀ := hf₀'.comp 0 harg₀
    have heq : (fun t : ℝ => f (v.1 + t)) =ᶠ[nhds 0]
        (f ∘ fun t : ℝ => v.1 + t) := by
      filter_upwards [] with t
      rfl
    have hleft₁ : HasDerivAt (fun t : ℝ => f (v.1 + t)) (deriv f v.1 * 1) 0 :=
      hleft₀.congr_of_eventuallyEq heq
    simpa using hleft₁
  have hright : HasDerivAt (fun t : ℝ => f (v.2 + t)) (deriv f v.2) 0 := by
    have hf₁' : HasDerivAt f (deriv f v.2) (v.2 + 0) := by
      simpa using hf₁.hasDerivAt
    have hright₀ := hf₁'.comp 0 harg₁
    have heq : (fun t : ℝ => f (v.2 + t)) =ᶠ[nhds 0]
        (f ∘ fun t : ℝ => v.2 + t) := by
      filter_upwards [] with t
      rfl
    have hright₁ : HasDerivAt (fun t : ℝ => f (v.2 + t)) (deriv f v.2 * 1) 0 :=
      hright₀.congr_of_eventuallyEq heq
    simpa using hright₁
  have hprod := hleft.mul hright
  have hprod' : HasDerivAt (fun t : ℝ => f (v.1 + t) * f (v.2 + t))
      (deriv f v.1 * f v.2 + f v.1 * deriv f v.2) 0 := by
    have heq : (fun t : ℝ => f (v.1 + t) * f (v.2 + t)) =ᶠ[nhds 0]
        ((fun t : ℝ => f (v.1 + t)) * (fun t : ℝ => f (v.2 + t))) := by
      filter_upwards [] with t
      rfl
    have hprod₁ := hprod.congr_of_eventuallyEq heq
    simpa using hprod₁
  unfold aux_diagonalDerivative
  simpa using hprod'.deriv

/-- This auxiliary product-rule identity is the two-function version needed for differentiated
two-dimensional Gaussians. -/
theorem aux_diagonalDerivative_product {f g : ℝ → ℝ} {v : RealPlane}
    (hf : DifferentiableAt ℝ f v.1) (hg : DifferentiableAt ℝ g v.2) :
    aux_diagonalDerivative (fun w : RealPlane => f w.1 * g w.2) v =
      deriv f v.1 * g v.2 + f v.1 * deriv g v.2 := by
  have harg₀base :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := v.1)).add (hasDerivAt_id (x := (0 : ℝ)))
  have harg₀ : HasDerivAt (fun t : ℝ => v.1 + t) 1 0 := by
    have heq : (fun t : ℝ => v.1 + t) =ᶠ[nhds 0]
        ((fun _ : ℝ => v.1) + id) := by
      filter_upwards [] with t
      rfl
    have harg₀' : HasDerivAt (fun t : ℝ => v.1 + t) (0 + 1) 0 :=
      harg₀base.congr_of_eventuallyEq heq
    simpa using harg₀'
  have harg₁base :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := v.2)).add (hasDerivAt_id (x := (0 : ℝ)))
  have harg₁ : HasDerivAt (fun t : ℝ => v.2 + t) 1 0 := by
    have heq : (fun t : ℝ => v.2 + t) =ᶠ[nhds 0]
        ((fun _ : ℝ => v.2) + id) := by
      filter_upwards [] with t
      rfl
    have harg₁' : HasDerivAt (fun t : ℝ => v.2 + t) (0 + 1) 0 :=
      harg₁base.congr_of_eventuallyEq heq
    simpa using harg₁'
  have hleft : HasDerivAt (fun t : ℝ => f (v.1 + t)) (deriv f v.1) 0 := by
    have hf' : HasDerivAt f (deriv f v.1) (v.1 + 0) := by
      simpa using hf.hasDerivAt
    have hleft₀ := hf'.comp 0 harg₀
    have heq : (fun t : ℝ => f (v.1 + t)) =ᶠ[nhds 0]
        (f ∘ fun t : ℝ => v.1 + t) := by
      filter_upwards [] with t
      rfl
    have hleft₁ : HasDerivAt (fun t : ℝ => f (v.1 + t)) (deriv f v.1 * 1) 0 :=
      hleft₀.congr_of_eventuallyEq heq
    simpa using hleft₁
  have hright : HasDerivAt (fun t : ℝ => g (v.2 + t)) (deriv g v.2) 0 := by
    have hg' : HasDerivAt g (deriv g v.2) (v.2 + 0) := by
      simpa using hg.hasDerivAt
    have hright₀ := hg'.comp 0 harg₁
    have heq : (fun t : ℝ => g (v.2 + t)) =ᶠ[nhds 0]
        (g ∘ fun t : ℝ => v.2 + t) := by
      filter_upwards [] with t
      rfl
    have hright₁ : HasDerivAt (fun t : ℝ => g (v.2 + t)) (deriv g v.2 * 1) 0 :=
      hright₀.congr_of_eventuallyEq heq
    simpa using hright₁
  have hprod := hleft.mul hright
  have hprod' : HasDerivAt (fun t : ℝ => f (v.1 + t) * g (v.2 + t))
      (deriv f v.1 * g v.2 + f v.1 * deriv g v.2) 0 := by
    have heq : (fun t : ℝ => f (v.1 + t) * g (v.2 + t)) =ᶠ[nhds 0]
        ((fun t : ℝ => f (v.1 + t)) * (fun t : ℝ => g (v.2 + t))) := by
      filter_upwards [] with t
      rfl
    have hprod₁ := hprod.congr_of_eventuallyEq heq
    simpa using hprod₁
  unfold aux_diagonalDerivative
  simpa using hprod'.deriv

/-- This auxiliary product-rule identity evaluates the diagonal derivative of a two-dimensional
Gaussian in the identity orientation. -/
theorem aux_diagonalDerivative_twoDimensionalGaussian_zero
    (t : Fin 2 → ℝ) (v : RealPlane) :
    aux_diagonalDerivative (twoDimensionalGaussian t 0) v =
      deriv (gaussianRescale (t 0)) v.1 * gaussianRescale (t 1) v.2 +
        gaussianRescale (t 0) v.1 * deriv (gaussianRescale (t 1)) v.2 := by
  change aux_diagonalDerivative
      (fun w : RealPlane => gaussianRescale (t 0) w.1 * gaussianRescale (t 1) w.2) v = _
  exact aux_diagonalDerivative_product
    (f := gaussianRescale (t 0)) (g := gaussianRescale (t 1))
    (gaussianRescale_hasDerivAt (t 0) v.1).differentiableAt
    (gaussianRescale_hasDerivAt (t 1) v.2).differentiableAt

/-- This auxiliary estimate bounds the diagonal derivative of a product Gaussian in the identity
orientation by the weighted bracket product used in the derivative kernel estimate. -/
theorem aux_abs_diagonalDerivative_twoDimensionalGaussian_zero_le
    (t : Fin 2 → ℝ) (ht : ∀ r : Fin 2, 0 < t r) (v : RealPlane) :
    |aux_diagonalDerivative (twoDimensionalGaussian t 0) v| ≤
      2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
        ((t 0)⁻¹ + (t 1)⁻¹) *
          (scaledBracketBump 2 (t 0) v.1 * scaledBracketBump 2 (t 1) v.2) := by
  rw [aux_diagonalDerivative_twoDimensionalGaussian_zero]
  let b₀ : ℝ := scaledBracketBump 2 (t 0) v.1
  let b₁ : ℝ := scaledBracketBump 2 (t 1) v.2
  have hb₀ : 0 ≤ b₀ := by
    dsimp [b₀]
    exact aux_scaledBracketBump_nonneg 2 (ht 0) _
  have hb₁ : 0 ≤ b₁ := by
    dsimp [b₁]
    exact aux_scaledBracketBump_nonneg 2 (ht 1) _
  have hC₀ : 0 ≤ C_gaussianBumpDecay 0 2 := by
    unfold C_gaussianBumpDecay
    exact Real.rpow_nonneg (by positivity) _
  have hC₁ : 0 ≤ C_gaussianBumpDecay 1 2 := by
    unfold C_gaussianBumpDecay
    exact Real.rpow_nonneg (by positivity) _
  have hd₀ : |deriv (gaussianRescale (t 0)) v.1| ≤
      (t 0)⁻¹ * C_gaussianBumpDecay 1 2 * b₀ := by
    simpa [b₀] using gaussianRescale_deriv_bound (t := t 0) (x := v.1) (ht 0)
  have hd₁ : |deriv (gaussianRescale (t 1)) v.2| ≤
      (t 1)⁻¹ * C_gaussianBumpDecay 1 2 * b₁ := by
    simpa [b₁] using gaussianRescale_deriv_bound (t := t 1) (x := v.2) (ht 1)
  have hg₀ : |gaussianRescale (t 0) v.1| ≤ C_gaussianBumpDecay 0 2 * b₀ := by
    simpa [b₀] using gaussianRescale_le_C_gaussianBumpDecay_zero_two
      (t := t 0) (x := v.1) (ht 0)
  have hg₁ : |gaussianRescale (t 1) v.2| ≤ C_gaussianBumpDecay 0 2 * b₁ := by
    simpa [b₁] using gaussianRescale_le_C_gaussianBumpDecay_zero_two
      (t := t 1) (x := v.2) (ht 1)
  have hterm₀ :
      |deriv (gaussianRescale (t 0)) v.1 * gaussianRescale (t 1) v.2| ≤
        C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          (t 0)⁻¹ * (b₀ * b₁) := by
    rw [abs_mul]
    calc
      |deriv (gaussianRescale (t 0)) v.1| * |gaussianRescale (t 1) v.2| ≤
          ((t 0)⁻¹ * C_gaussianBumpDecay 1 2 * b₀) *
            (C_gaussianBumpDecay 0 2 * b₁) :=
        mul_le_mul hd₀ hg₁ (abs_nonneg _)
          (mul_nonneg (mul_nonneg (inv_nonneg.mpr (ht 0).le) hC₁) hb₀)
      _ = C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          (t 0)⁻¹ * (b₀ * b₁) := by ring
  have hterm₁ :
      |gaussianRescale (t 0) v.1 * deriv (gaussianRescale (t 1)) v.2| ≤
        C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          (t 1)⁻¹ * (b₀ * b₁) := by
    rw [abs_mul]
    calc
      |gaussianRescale (t 0) v.1| * |deriv (gaussianRescale (t 1)) v.2| ≤
          (C_gaussianBumpDecay 0 2 * b₀) *
            ((t 1)⁻¹ * C_gaussianBumpDecay 1 2 * b₁) :=
        mul_le_mul hg₀ hd₁ (abs_nonneg _)
          (mul_nonneg hC₀ hb₀)
      _ = C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          (t 1)⁻¹ * (b₀ * b₁) := by ring
  have hcore :
      C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          (t 0)⁻¹ * (b₀ * b₁) +
        C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          (t 1)⁻¹ * (b₀ * b₁) =
        C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          ((t 0)⁻¹ + (t 1)⁻¹) * (b₀ * b₁) := by ring
  have hnonneg : 0 ≤ C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
      ((t 0)⁻¹ + (t 1)⁻¹) * (b₀ * b₁) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC₀ hC₁)
        (add_nonneg (inv_nonneg.mpr (ht 0).le) (inv_nonneg.mpr (ht 1).le)))
      (mul_nonneg hb₀ hb₁)
  calc
    |deriv (gaussianRescale (t 0)) v.1 * gaussianRescale (t 1) v.2 +
        gaussianRescale (t 0) v.1 * deriv (gaussianRescale (t 1)) v.2| ≤
        |deriv (gaussianRescale (t 0)) v.1 * gaussianRescale (t 1) v.2| +
          |gaussianRescale (t 0) v.1 * deriv (gaussianRescale (t 1)) v.2| :=
      abs_add_le _ _
    _ ≤ C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          (t 0)⁻¹ * (b₀ * b₁) +
        C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          (t 1)⁻¹ * (b₀ * b₁) := add_le_add hterm₀ hterm₁
    _ = C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          ((t 0)⁻¹ + (t 1)⁻¹) * (b₀ * b₁) := hcore
    _ ≤ 2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
          ((t 0)⁻¹ + (t 1)⁻¹) * (b₀ * b₁) := by nlinarith
    _ = 2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
        ((t 0)⁻¹ + (t 1)⁻¹) *
          (scaledBracketBump 2 (t 0) v.1 * scaledBracketBump 2 (t 1) v.2) := by
      simp only [b₀, b₁]

/-- This auxiliary abbreviation records the `\ell^1` size `|m|` of an element of
`\mathbb N^2`, used in the displayed Gaussian series. -/
def aux_natPairWeight (m : Fin 2 → ℕ) : ℕ := m 0 + m 1

/-- This auxiliary weight is the coefficient `2^{-|m|/2}` in the Gaussian domination
series. -/
def aux_gaussianDominationWeight (m : Fin 2 → ℕ) : ℝ :=
  Real.rpow 2 (-((aux_natPairWeight m : ℕ) : ℝ) / 2)

/-- This auxiliary term is the two-dimensional Gaussian `G_{p(j),u}` occurring in the
Gaussian-domination conclusion. -/
def aux_dominatingGaussianTerm (p : SequencePair) (u : Fin 2) (j : ℤ)
    (v : RealPlane) : ℝ :=
  twoDimensionalGaussian (fun r => p r j) u v


/-- Constant from Proposition \ref{H kernel estimate Gaussian domination}, formalized by
`hKernelEstimateGaussianDomination`. -/
def C_hKernelEstimateGaussianDomination : ℝ :=
  4 * C_diagonalSquareRoot 2 ^ 2 + C_gaussianBumpDecay 0 2 ^ 2

/-- Constant from Proposition \ref{H kernel derivative estimate Gaussian domination}, formalized
by `hKernelDerivativeEstimateGaussianDomination`. -/
def C_hKernelDerivativeEstimateGaussianDomination : ℝ :=
  4 * C_diagonalSquareRoot 2 * C_derivativeDiagonalSquareRoot 2 +
    2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2

/-- This auxiliary sign check is needed when combining the positive component estimates into
the kernel majorant. -/
theorem aux_C_hKernelEstimateGaussianDomination_nonneg :
    0 ≤ C_hKernelEstimateGaussianDomination := by
  rw [C_hKernelEstimateGaussianDomination, C_diagonalSquareRoot,
    aux_twoBumpEstimate_two_two]
  positivity

/-- This auxiliary sign check is needed when combining the differentiated component estimates
into the derivative kernel majorant. -/
theorem aux_C_hKernelDerivativeEstimateGaussianDomination_nonneg :
    0 ≤ C_hKernelDerivativeEstimateGaussianDomination := by
  have hgaussian (m N : ℕ) : 0 ≤ C_gaussianBumpDecay m N := by
    unfold C_gaussianBumpDecay
    exact Real.rpow_nonneg (by positivity) _
  have hdiagonal : 0 ≤ C_diagonalSquareRoot 2 := by
    unfold C_diagonalSquareRoot
    exact mul_nonneg (Real.sqrt_nonneg _)
      (le_trans (hgaussian 0 2) (le_max_left _ _))
  have hderivative : 0 ≤ C_derivativeDiagonalSquareRoot 2 := by
    unfold C_derivativeDiagonalSquareRoot
    exact mul_nonneg (by norm_num)
      (le_trans (hgaussian 1 2) (le_max_left _ _))
  unfold C_hKernelDerivativeEstimateGaussianDomination
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hdiagonal) hderivative)
    (mul_nonneg (mul_nonneg (by norm_num) (hgaussian 0 2)) (hgaussian 1 2))

/-- Constant from Proposition \ref{Gaussian domination combined}, formalized by
`gaussianDominationCombined`. -/
def C_gaussianDominationCombinedCard : ℕ := 30

/-- Constant from Proposition \ref{Gaussian domination combined}, formalized by
`gaussianDominationCombined`. -/
def C_gaussianDominationCombinedDistance : ℕ := 2

/-- Constant from Proposition \ref{Gaussian domination combined}, formalized by
`gaussianDominationCombined`. -/
def C_gaussianDominationCombined : ℝ := (100 : ℝ) ^ (100 : ℕ)

/-- Constant from Proposition \ref{Gauss domination case 1}, formalized by
`gaussDominationCase1`. -/
noncomputable def C_gaussDominationCase1 : ℝ :=
  (2 : ℝ) ^ (7 : ℕ) * Real.pi * Real.exp (2 * Real.pi) *
    C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2 *
    C_hKernelEstimateGaussianDomination *
    max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
      (4 * C_bumpTriangle (-(1 / 2)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2))

/-- Constant from Proposition \ref{Gauss domination case 2}, formalized by
`gaussDominationCase2`. -/
noncomputable def C_gaussDominationCase2 : ℝ :=
  3 * (2 : ℝ) ^ (7 : ℕ) * Real.exp (2 * Real.pi) *
    C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
    C_hKernelDerivativeEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
    C_twoBumpEstimate 2 2

/-- Constant from Proposition \ref{Gauss domination case 3}, formalized by
`gaussDominationCase3`. -/
noncomputable def C_gaussDominationCase3 : ℝ :=
  (2 : ℝ) ^ (7 : ℕ) * Real.exp (2 * Real.pi) *
    C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2 *
    C_hKernelEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
    C_twoBumpEstimate 2 2

/-- This auxiliary positivity fact removes the junk-value branch of a rescaled Gaussian at
the positive scales supplied by spaced sequences. -/
theorem aux_gaussianRescale_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ gaussianRescale t x := by
  unfold gaussianRescale
  exact mul_nonneg (inv_nonneg.mpr ht.le) (aux_gaussian_pos _).le

/-- This auxiliary positivity fact is used when estimating the Gaussian-difference part of
the `H` multiplier. -/
theorem aux_gammaGaussian_nonneg {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane) :
    0 ≤ gammaGaussian γ i j v := by
  unfold gammaGaussian twoDimensionalGaussian
  exact mul_nonneg
    (aux_gaussianRescale_nonneg ((γ.scales_spaced i 0 j).1) _)
    (aux_gaussianRescale_nonneg ((γ.scales_spaced i 1 j).1) _)

/-- This auxiliary triangle-inequality estimate isolates the two Gaussian terms in the
Gaussian-difference part of the `H` multiplier. -/
theorem aux_abs_gaussianDifference_le {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane) :
    |gaussianDifference γ i j v| ≤
      gammaGaussian γ i (j - 1) v + gammaGaussian γ i j v := by
  unfold gaussianDifference
  calc
    |gammaGaussian γ i (j - 1) v - gammaGaussian γ i j v| ≤
        |gammaGaussian γ i (j - 1) v| + |gammaGaussian γ i j v| := by
          simpa using (abs_sub_le (gammaGaussian γ i (j - 1) v) 0
            (gammaGaussian γ i j v))
    _ = gammaGaussian γ i (j - 1) v + gammaGaussian γ i j v := by
      rw [abs_of_nonneg (aux_gammaGaussian_nonneg γ i (j - 1) v),
        abs_of_nonneg (aux_gammaGaussian_nonneg γ i j v)]

/-- This auxiliary estimate reduces the kernel bound to estimates for the two factors of
`s_\gamma` and the two Gaussian terms. -/
theorem aux_abs_hMultiplier_le {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane) :
    |hMultiplier γ i j v| ≤
      |sMultiplier γ i j v.1| * |sMultiplier γ i j v.2| +
        gammaGaussian γ i (j - 1) v + gammaGaussian γ i j v := by
  unfold hMultiplier
  calc
    |sMultiplier γ i j v.1 * sMultiplier γ i j v.2 - gaussianDifference γ i j v| ≤
        |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| +
          |gaussianDifference γ i j v| := by
            simpa using (abs_sub_le (sMultiplier γ i j v.1 * sMultiplier γ i j v.2) 0
              (gaussianDifference γ i j v))
    _ = |sMultiplier γ i j v.1| * |sMultiplier γ i j v.2| +
          |gaussianDifference γ i j v| := by rw [abs_mul]
    _ ≤ |sMultiplier γ i j v.1| * |sMultiplier γ i j v.2| +
          (gammaGaussian γ i (j - 1) v + gammaGaussian γ i j v) := by
      gcongr
      exact aux_abs_gaussianDifference_le γ i j v
    _ = |sMultiplier γ i j v.1| * |sMultiplier γ i j v.2| +
        gammaGaussian γ i (j - 1) v + gammaGaussian γ i j v := by ring

/-- This auxiliary lemma recovers the defining comparison at an arbitrary larger finite
distance from the `SequenceDistance` bound.  It is needed to verify the explicit multiset
used in the kernel estimate. -/
theorem aux_withinSequenceDistance_of_sequenceDistance_le {a b : ℤ → ℝ}
    (ha : SpacedSequence a) {r : ℕ}
    (h : SequenceDistance a b ≤ (r : WithTop ℕ)) : WithinSequenceDistance a b r := by
  classical
  by_cases hexists : ∃ k : ℕ, WithinSequenceDistance a b k
  · have hdistance : SequenceDistance a b = (Nat.find hexists : WithTop ℕ) := by
      simp [SequenceDistance, hexists]
    have hfind : Nat.find hexists ≤ r := by
      apply WithTop.coe_le_coe.mp
      simpa [hdistance] using h
    intro j
    constructor
    · calc
        a (j - r) ≤ a (j - Nat.find hexists) :=
          aux_spacedSequence_monotone ha (by omega)
        _ ≤ b j := (Nat.find_spec hexists j).1
    · calc
        b j ≤ a (j + Nat.find hexists) := (Nat.find_spec hexists j).2
        _ ≤ a (j + r) := aux_spacedSequence_monotone ha (by omega)
  · simp [SequenceDistance, hexists] at h

/-- This auxiliary bound says that the distance of the two scale sequences at a fixed index
is absorbed by the manuscript's global parameter `\Delta_\gamma`. -/
theorem aux_sequencePairDistance_succ_le_geometricDelta {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) :
    sequencePairDistance (γ.scales i) + 1 ≤ (geometricDelta γ : WithTop ℕ) := by
  let d : WithTop ℕ := sequencePairDistance (γ.scales i)
  have hd : d < ⊤ := γ.finite_distance i
  have hdne : d ≠ ⊤ := ne_of_lt hd
  have hterm : d.untop hdne ≤
      ∑ r, (sequencePairDistance (γ.scales r)).untop
        (ne_of_lt (γ.finite_distance r)) := by
    simpa only [d] using
      (Finset.single_le_sum
        (f := fun r => (sequencePairDistance (γ.scales r)).untop
          (ne_of_lt (γ.finite_distance r)))
        (s := Finset.univ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hnat : d.untop hdne + 1 ≤ geometricDelta γ := by
    unfold geometricDelta
    omega
  change d + 1 ≤ (geometricDelta γ : WithTop ℕ)
  rw [← WithTop.coe_untop d hdne]
  rw [← WithTop.coe_one, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr hnat

/-- This auxiliary positivity fact is used for the nonnegative Gaussian series in the combined
domination statement. -/
theorem aux_gaussianDominationWeight_nonneg (m : Fin 2 → ℕ) :
    0 ≤ aux_gaussianDominationWeight m := by
  unfold aux_gaussianDominationWeight
  exact Real.rpow_nonneg (by norm_num) _

/-- This auxiliary positivity fact verifies that every Gaussian term in the displayed
dominating series is nonnegative. -/
theorem aux_dominatingGaussianTerm_nonneg (p : SequencePair)
    (hp : ∀ r : Fin 2, SpacedSequence (p r)) (u : Fin 2) (j : ℤ)
    (v : RealPlane) :
    0 ≤ aux_dominatingGaussianTerm p u j v := by
  unfold aux_dominatingGaussianTerm twoDimensionalGaussian
  exact mul_nonneg
    (aux_gaussianRescale_nonneg ((hp 0 j).1) _)
    (aux_gaussianRescale_nonneg ((hp 1 j).1) _)

/-- This auxiliary algebraic estimate expands the product of the two two-scale bounds used
for the tensor-product term of the `H` multiplier. -/
theorem aux_abs_mul_le_four_products {f g A u₀ u₁ v₀ v₁ : ℝ}
    (hA : 0 ≤ A) (hu₀ : 0 ≤ u₀) (hu₁ : 0 ≤ u₁) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁)
    (hf : |f| ≤ A * (u₀ + u₁)) (hg : |g| ≤ A * (v₀ + v₁)) :
    |f * g| ≤ A ^ 2 * (u₀ * v₀ + u₀ * v₁ + u₁ * v₀ + u₁ * v₁) := by
  have hu : 0 ≤ u₀ + u₁ := add_nonneg hu₀ hu₁
  have hv : 0 ≤ v₀ + v₁ := add_nonneg hv₀ hv₁
  calc
    |f * g| = |f| * |g| := abs_mul _ _
    _ ≤ (A * (u₀ + u₁)) * (A * (v₀ + v₁)) :=
      mul_le_mul hf hg (abs_nonneg _) (mul_nonneg hA hu)
    _ = A ^ 2 * (u₀ * v₀ + u₀ * v₁ + u₁ * v₀ + u₁ * v₁) := by ring

/-- This auxiliary product-rule majorant is the algebraic part of the derivative kernel
estimate.  It keeps the inverse scale attached to the factor on which the derivative falls. -/
theorem aux_abs_tensorDerivative_le_four_products
    {f₀ f₁ d₀ d₁ c d a₀ a₁ b₀ b₁ u₀ u₁ v₀ v₁ : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁) (hu₀ : 0 ≤ u₀) (hu₁ : 0 ≤ u₁)
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁)
    (hf₀ : |f₀| ≤ 2 * c * (u₀ + u₁))
    (hf₁ : |f₁| ≤ 2 * c * (v₀ + v₁))
    (hd₀ : |d₀| ≤ d * (a₀ * u₀ + a₁ * u₁))
    (hd₁ : |d₁| ≤ d * (b₀ * v₀ + b₁ * v₁)) :
    |d₀ * f₁ + f₀ * d₁| ≤ 4 * c * d *
      ((a₀ + b₀) * u₀ * v₀ + (a₀ + b₁) * u₀ * v₁ +
        (a₁ + b₀) * u₁ * v₀ + (a₁ + b₁) * u₁ * v₁) := by
  have hU : 0 ≤ u₀ + u₁ := add_nonneg hu₀ hu₁
  have hV : 0 ≤ v₀ + v₁ := add_nonneg hv₀ hv₁
  have hA : 0 ≤ a₀ * u₀ + a₁ * u₁ :=
    add_nonneg (mul_nonneg ha₀ hu₀) (mul_nonneg ha₁ hu₁)
  have hB : 0 ≤ b₀ * v₀ + b₁ * v₁ :=
    add_nonneg (mul_nonneg hb₀ hv₀) (mul_nonneg hb₁ hv₁)
  have hfirst : |d₀ * f₁| ≤
      (d * (a₀ * u₀ + a₁ * u₁)) * (2 * c * (v₀ + v₁)) := by
    rw [abs_mul]
    exact mul_le_mul hd₀ hf₁ (abs_nonneg _)
      (mul_nonneg hd hA)
  have hsecond : |f₀ * d₁| ≤
      (2 * c * (u₀ + u₁)) * (d * (b₀ * v₀ + b₁ * v₁)) := by
    rw [abs_mul]
    exact mul_le_mul hf₀ hd₁ (abs_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hc) hU)
  let Q : ℝ :=
    (a₀ + b₀) * u₀ * v₀ + (a₀ + b₁) * u₀ * v₁ +
      (a₁ + b₀) * u₁ * v₀ + (a₁ + b₁) * u₁ * v₁
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (mul_nonneg (mul_nonneg (add_nonneg ha₀ hb₀) hu₀) hv₀)
          (mul_nonneg (mul_nonneg (add_nonneg ha₀ hb₁) hu₀) hv₁))
        (mul_nonneg (mul_nonneg (add_nonneg ha₁ hb₀) hu₁) hv₀))
      (mul_nonneg (mul_nonneg (add_nonneg ha₁ hb₁) hu₁) hv₁)
  calc
    |d₀ * f₁ + f₀ * d₁| ≤ |d₀ * f₁| + |f₀ * d₁| := abs_add_le _ _
    _ ≤ (d * (a₀ * u₀ + a₁ * u₁)) * (2 * c * (v₀ + v₁)) +
        (2 * c * (u₀ + u₁)) * (d * (b₀ * v₀ + b₁ * v₁)) :=
      add_le_add hfirst hsecond
    _ = 2 * c * d * Q := by
      dsimp [Q]
      ring
    _ ≤ 4 * c * d * Q := by
      nlinarith [mul_nonneg (mul_nonneg hc hd) hQ]

/-- This auxiliary estimate converts the one-dimensional Gaussian bump estimate into the
two-dimensional product estimate needed for each Gaussian entry of the kernel multiset. -/
theorem aux_twoDimensionalGaussian_le_gaussianBumpProduct (t : Fin 2 → ℝ)
    (ht : ∀ r : Fin 2, 0 < t r) (u : Fin 2) (v : RealPlane) :
    twoDimensionalGaussian t u v ≤ C_gaussianBumpDecay 0 2 ^ 2 *
      (scaledBracketBump 2 (t 0) (W u v).1 *
        scaledBracketBump 2 (t 1) (W u v).2) := by
  unfold twoDimensionalGaussian
  have hC : 0 ≤ C_gaussianBumpDecay 0 2 := by
    unfold C_gaussianBumpDecay
    exact Real.rpow_nonneg (by positivity) _
  rw [← abs_of_nonneg (aux_gaussianRescale_nonneg (ht 0) _),
    ← abs_of_nonneg (aux_gaussianRescale_nonneg (ht 1) _)]
  calc
    |gaussianRescale (t 0) (W u v).1| *
        |gaussianRescale (t 1) (W u v).2| ≤
        (C_gaussianBumpDecay 0 2 * scaledBracketBump 2 (t 0) (W u v).1) *
          (C_gaussianBumpDecay 0 2 * scaledBracketBump 2 (t 1) (W u v).2) :=
      mul_le_mul
        (gaussianRescale_le_C_gaussianBumpDecay_zero_two (ht 0))
        (gaussianRescale_le_C_gaussianBumpDecay_zero_two (ht 1))
        (abs_nonneg _) (mul_nonneg hC
          (aux_scaledBracketBump_nonneg 2 (ht 0) _))
    _ = C_gaussianBumpDecay 0 2 ^ 2 *
        (scaledBracketBump 2 (t 0) (W u v).1 *
          scaledBracketBump 2 (t 1) (W u v).2) := by ring

/-- This auxiliary arithmetic step combines the tensor-product contribution and the two
Gaussian-difference contributions into the six-term kernel majorant. -/
theorem aux_sixTermKernelMajorant {A c d S r₀ r₁ : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hS : 0 ≤ S) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hA : A ≤ 4 * c ^ 2 * S) :
    A + d ^ 2 * r₀ + d ^ 2 * r₁ ≤
      (4 * c ^ 2 + d ^ 2) * (S + r₀ + r₁) := by
  have hfourc : 0 ≤ 4 * c ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg c)
  have hdSq : 0 ≤ d ^ 2 := sq_nonneg d
  nlinarith [mul_nonneg hfourc hr₀, mul_nonneg hfourc hr₁,
    mul_nonneg hdSq hS]

/-- This auxiliary comparison replaces a scale lying between `t` and `2t` by `t` in the
second-order bracket bump.  It is the elementary scale comparison used in both orientation
cases of the kernel estimate. -/
theorem aux_scaledBracketBump_two_scale_le {t s x : ℝ}
    (ht : 0 < t) (hts : t ≤ s) (hst : s ≤ 2 * t) :
    scaledBracketBump 2 s x ≤ 2 * scaledBracketBump 2 t x := by
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have hformula (r : ℝ) (hr : 0 < r) :
      r⁻¹ * (1 + |r⁻¹ * x|)⁻¹ ^ 2 = r / (r + |x|) ^ 2 := by
    have hrne : r ≠ 0 := ne_of_gt hr
    have hsumne : r + |x| ≠ 0 := ne_of_gt
      (add_pos_of_pos_of_nonneg hr (abs_nonneg x))
    have hinnerne : 1 + r⁻¹ * |x| ≠ 0 := ne_of_gt (by positivity)
    rw [abs_mul, abs_inv, abs_of_pos hr]
    field_simp [hrne, hsumne, hinnerne]
  unfold scaledBracketBump
  rw [hformula s hs, hformula t ht]
  have htplus : 0 < t + |x| :=
    add_pos_of_pos_of_nonneg ht (abs_nonneg x)
  have hden : (t + |x|) ^ 2 ≤ (s + |x|) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc
    s / (s + |x|) ^ 2 ≤ (2 * t) / (s + |x|) ^ 2 :=
      div_le_div_of_nonneg_right hst (sq_nonneg _)
    _ ≤ (2 * t) / (t + |x|) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos htplus _) hden
    _ = 2 * (t / (t + |x|) ^ 2) := by ring

/-- This auxiliary identity writes the second-order scaled bracket bump in a form convenient for
comparing nearby scales. -/
theorem aux_scaledBracketBump_two_eq {t x : ℝ} (ht : 0 < t) :
    scaledBracketBump 2 t x = t / (t + |x|) ^ 2 := by
  unfold scaledBracketBump
  have htne : t ≠ 0 := ne_of_gt ht
  have hsumne : t + |x| ≠ 0 := ne_of_gt
    (add_pos_of_pos_of_nonneg ht (abs_nonneg x))
  have hinnerne : 1 + t⁻¹ * |x| ≠ 0 := ne_of_gt (by positivity)
  rw [abs_mul, abs_inv, abs_of_pos ht]
  field_simp [htne, hsumne, hinnerne]

/-- This auxiliary comparison is the derivative-scale version of the preceding bump comparison:
the extra inverse scale removes the loss incurred by enlarging a scale. -/
theorem aux_inv_mul_scaledBracketBump_two_le_of_le_scale {t s x : ℝ}
    (ht : 0 < t) (hts : t ≤ s) :
    s⁻¹ * scaledBracketBump 2 s x ≤ t⁻¹ * scaledBracketBump 2 t x := by
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have htplus : 0 < t + |x| :=
    add_pos_of_pos_of_nonneg ht (abs_nonneg x)
  have hsplus : 0 < s + |x| :=
    add_pos_of_pos_of_nonneg hs (abs_nonneg x)
  have hden : (t + |x|) ^ 2 ≤ (s + |x|) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  rw [aux_scaledBracketBump_two_eq hs, aux_scaledBracketBump_two_eq ht]
  have hsne : s ≠ 0 := ne_of_gt hs
  have hsdenne : (s + |x|) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hsplus)
  have htdenne : (t + |x|) ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt htplus)
  have hcancel : s⁻¹ * (s / (s + |x|) ^ 2) = 1 / (s + |x|) ^ 2 := by
    field_simp [hsne, hsdenne]
  rw [hcancel]
  have hrecip : 1 / (s + |x|) ^ 2 ≤ 1 / (t + |x|) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos htplus _) hden
  calc
    1 / (s + |x|) ^ 2 ≤ 1 / (t + |x|) ^ 2 := hrecip
    _ = t⁻¹ * (t / (t + |x|) ^ 2) := by
      field_simp [ne_of_gt ht, htdenne]

/-- This auxiliary scale comparison controls the Euclidean combination of two positive scales by
their pointwise maximum.  It is used to compare the first orientation's `s`-multiplier scales
with the two maximum sequences in the explicit multiset. -/
theorem aux_sqrt_sq_add_sq_between_max_and_two_mul_max {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max x y ≤ Real.sqrt (x ^ 2 + y ^ 2) ∧
      Real.sqrt (x ^ 2 + y ^ 2) ≤ 2 * max x y := by
  let M : ℝ := max x y
  have hM : 0 ≤ M := by
    dsimp [M]
    exact le_max_of_le_left hx
  have hsum : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have hM_sq : M ^ 2 ≤ x ^ 2 + y ^ 2 := by
    dsimp [M]
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy]
      nlinarith [sq_nonneg x]
    · rw [max_eq_left hyx]
      nlinarith [sq_nonneg y]
  have hxM : x ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hyM : y ≤ M := by
    dsimp [M]
    exact le_max_right _ _
  have hx_sq : x ^ 2 ≤ M ^ 2 := (sq_le_sq₀ hx hM).mpr hxM
  have hy_sq : y ^ 2 ≤ M ^ 2 := (sq_le_sq₀ hy hM).mpr hyM
  constructor
  · apply (sq_le_sq₀ hM (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hsum]
    exact hM_sq
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hsum]
    nlinarith

/-- This auxiliary sequence packages the two cases in the definition of the manuscript's
`s_\gamma` multiplier, so that its diagonal-square-root estimates can be applied uniformly. -/
noncomputable def aux_sMultiplierScale {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) : ℤ → ℝ :=
  if γ.orientation i = 0 then
    fun r => Real.sqrt ((γ.scales i 0 r) ^ 2 + (γ.scales i 1 r) ^ 2)
  else
    fun r => Real.sqrt 2 * γ.scales i 1 r

/-- This auxiliary fact verifies the spacedness required to use the diagonal-square-root
estimate for the uniformly packaged scale sequence. -/
theorem aux_sMultiplierScale_spaced {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) : SpacedSequence (aux_sMultiplierScale γ i) := by
  classical
  by_cases h : γ.orientation i = 0
  · simp [aux_sMultiplierScale, h]
    exact sqrt_sq_add_sq_mem_A (γ.scales_spaced i 0) (γ.scales_spaced i 1)
  · simp [aux_sMultiplierScale, h]
    exact smul_mem_A (γ.scales_spaced i 1)
      (Real.sqrt_pos.2 (by norm_num))

/-- This auxiliary identity lets the preliminary diagonal-square-root estimates be used directly
for `sMultiplier`. -/
theorem aux_sMultiplier_eq_diagonalSquareRoot {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (x : ℝ) :
    sMultiplier γ i j x =
      diagonalSquareRoot (aux_sMultiplierScale γ i (j - 1))
        (aux_sMultiplierScale γ i j) x := by
  classical
  by_cases h : γ.orientation i = 0
  · rw [sMultiplier, dif_pos h]
    rw [aux_squareRootGaussianDifference_eq_diagonalSquareRoot]
    simp [aux_sMultiplierScale, h]
  · rw [sMultiplier, dif_neg h]
    rw [aux_squareRootGaussianDifference_eq_diagonalSquareRoot]
    simp [aux_sMultiplierScale, h]

/-- This auxiliary derivative identity transfers the preliminary derivative estimate for the
diagonal-square-root kernel to the raw `sMultiplier` definition. -/
theorem aux_deriv_sMultiplier_eq_diagonalSquareRoot {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (x : ℝ) :
    deriv (sMultiplier γ i j) x =
      deriv (diagonalSquareRoot (aux_sMultiplierScale γ i (j - 1))
        (aux_sMultiplierScale γ i j)) x := by
  classical
  by_cases h : γ.orientation i = 0
  · rw [sMultiplier, dif_pos h]
    rw [aux_squareRootGaussianDifference_deriv_eq_diagonalSquareRoot]
    simp [aux_sMultiplierScale, h]
  · rw [sMultiplier, dif_neg h]
    rw [aux_squareRootGaussianDifference_deriv_eq_diagonalSquareRoot]
    simp [aux_sMultiplierScale, h]

/-- This auxiliary sign check permits the diagonal-square-root bound to be enlarged by the
scale-comparison factor in the kernel estimate. -/
theorem aux_C_diagonalSquareRoot_two_nonneg :
    0 ≤ C_diagonalSquareRoot 2 := by
  have hgaussian (m N : ℕ) : 0 ≤ C_gaussianBumpDecay m N := by
    unfold C_gaussianBumpDecay
    exact Real.rpow_nonneg (by positivity) _
  unfold C_diagonalSquareRoot
  exact mul_nonneg (Real.sqrt_nonneg _)
    (le_trans (hgaussian 0 2) (le_max_left _ _))

/-- This auxiliary predicate gives the exact membership condition
`\mathcal P\subset B_{\mathrm{dist}}(a_i^1,\Delta_\gamma)^2\times[2)`
for a multiset, including multiplicities. -/
def aux_ValidKernelGaussianPackage {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (P : Multiset (SequencePair × Fin 2)) : Prop :=
  ∀ q ∈ P,
    q.1 0 ∈ sequenceDistanceBall (γ.scales i 1) (geometricDelta γ) ∧
      q.1 1 ∈ sequenceDistanceBall (γ.scales i 1) (geometricDelta γ)

/-- This auxiliary bracket product is the summand in the two kernel estimates. -/
def aux_kernelBracketProduct (q : SequencePair × Fin 2) (j : ℤ) (v : RealPlane) : ℝ :=
  scaledBracketBump 2 (q.1 0 j) (W q.2 v).1 *
    scaledBracketBump 2 (q.1 1 j) (W q.2 v).2

/-- This auxiliary positivity fact allows finite multiset sums of kernel bracket products to
serve as nonnegative majorants. -/
theorem aux_kernelBracketProduct_nonneg (q : SequencePair × Fin 2)
    (hq : ∀ r : Fin 2, SpacedSequence (q.1 r)) (j : ℤ) (v : RealPlane) :
    0 ≤ aux_kernelBracketProduct q j v := by
  unfold aux_kernelBracketProduct
  exact mul_nonneg
    (aux_scaledBracketBump_nonneg 2 ((hq 0 j).1) _)
    (aux_scaledBracketBump_nonneg 2 ((hq 1 j).1) _)

/-- This auxiliary sequence is the shifted scale
`t_{m,\ell}(j)=a_i^\ell(j+m-1)` used to construct the six-term multiset in the
kernel Gaussian estimate. -/
def aux_hKernelShiftedScale {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k)
    (m r : Fin 2) : ℤ → ℝ :=
  fun j => γ.scales i r (j + (m : ℤ) - 1)

/-- This auxiliary scale is the manuscript's
`t_m^+=\max(t_{m,0},t_{m,1})`. -/
def aux_hKernelMaxScale {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k)
    (m : Fin 2) : ℤ → ℝ :=
  fun j => max (aux_hKernelShiftedScale γ i m 0 j)
    (aux_hKernelShiftedScale γ i m 1 j)

/-- This auxiliary theorem verifies that every shifted scale used in the six-term multiset
remains multiplicatively spaced. -/
theorem aux_hKernelShiftedScale_spaced {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (m r : Fin 2) : SpacedSequence (aux_hKernelShiftedScale γ i m r) := by
  convert shift_mem_A (γ.scales_spaced i r) ((m : ℤ) - 1) using 1
  ext j
  simp [aux_hKernelShiftedScale]
  ring

/-- This auxiliary estimate gives the one-step distance control for each of the shifted scales
appearing in the six-element multiset. -/
theorem aux_sequenceDistance_scale_hKernelShiftedScale_le_one {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (m r : Fin 2) :
    SequenceDistance (γ.scales i r) (aux_hKernelShiftedScale γ i m r) ≤ 1 := by
  fin_cases m
  · apply aux_sequenceDistance_le_of_within
    intro j
    constructor
    · norm_num [aux_hKernelShiftedScale]
    · norm_num [aux_hKernelShiftedScale]
      exact aux_spacedSequence_monotone (γ.scales_spaced i r) (by omega)
  · apply aux_sequenceDistance_le_of_within
    intro j
    constructor
    · norm_num [aux_hKernelShiftedScale]
      exact aux_spacedSequence_monotone (γ.scales_spaced i r) (by omega)
    · norm_num [aux_hKernelShiftedScale]
      exact aux_spacedSequence_monotone (γ.scales_spaced i r) (by omega)

/-- This auxiliary membership proof supplies the distance condition for each shifted scale in
the kernel Gaussian multiset. -/
theorem aux_hKernelShiftedScale_mem_sequenceDistanceBall {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (m r : Fin 2) :
    aux_hKernelShiftedScale γ i m r ∈
      sequenceDistanceBall (γ.scales i 1) (geometricDelta γ) := by
  constructor
  · exact aux_hKernelShiftedScale_spaced γ i m r
  fin_cases r
  · calc
      SequenceDistance (γ.scales i 1) (aux_hKernelShiftedScale γ i m 0) ≤
          SequenceDistance (γ.scales i 1) (γ.scales i 0) +
            SequenceDistance (γ.scales i 0) (aux_hKernelShiftedScale γ i m 0) :=
        sequenceDistance_triangle _ _ _
      _ ≤ SequenceDistance (γ.scales i 1) (γ.scales i 0) + 1 := by
        exact add_le_add_right
          (aux_sequenceDistance_scale_hKernelShiftedScale_le_one γ i m 0) _
      _ ≤ (geometricDelta γ : WithTop ℕ) := by
        rw [sequenceDistance_comm]
        simpa [sequencePairDistance] using
          aux_sequencePairDistance_succ_le_geometricDelta γ i
  · have hshift := aux_sequenceDistance_scale_hKernelShiftedScale_le_one γ i m 1
    have hdelta := aux_sequencePairDistance_succ_le_geometricDelta γ i
    calc
      SequenceDistance (γ.scales i 1) (aux_hKernelShiftedScale γ i m 1) ≤ 1 := hshift
      _ ≤ sequencePairDistance (γ.scales i) + 1 := by
        simpa using
          (add_le_add_right (show (0 : WithTop ℕ) ≤ sequencePairDistance (γ.scales i) from bot_le) 1)
      _ ≤ (geometricDelta γ : WithTop ℕ) := hdelta

/-- This auxiliary theorem verifies that the pointwise maximum scales used when `u(i)=0`
remain multiplicatively spaced. -/
theorem aux_hKernelMaxScale_spaced {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (m : Fin 2) : SpacedSequence (aux_hKernelMaxScale γ i m) := by
  exact max_mem_A (aux_hKernelShiftedScale_spaced γ i m 0)
    (aux_hKernelShiftedScale_spaced γ i m 1)

/-- This auxiliary membership proof supplies the distance condition for the maximum scales
used in the `u(i)=0` part of the kernel Gaussian multiset. -/
theorem aux_hKernelMaxScale_mem_sequenceDistanceBall {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (m : Fin 2) :
    aux_hKernelMaxScale γ i m ∈
      sequenceDistanceBall (γ.scales i 1) (geometricDelta γ) := by
  constructor
  · exact aux_hKernelMaxScale_spaced γ i m
  apply aux_sequenceDistance_le_of_within
  have hzero := aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i m 0
  have hone := aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i m 1
  have hzero_within : WithinSequenceDistance (γ.scales i 1)
      (aux_hKernelShiftedScale γ i m 0) (geometricDelta γ) :=
    aux_withinSequenceDistance_of_sequenceDistance_le (γ.scales_spaced i 1) hzero.2
  have hone_within : WithinSequenceDistance (γ.scales i 1)
      (aux_hKernelShiftedScale γ i m 1) (geometricDelta γ) :=
    aux_withinSequenceDistance_of_sequenceDistance_le (γ.scales_spaced i 1) hone.2
  intro j
  constructor
  · unfold aux_hKernelMaxScale
    exact le_max_of_le_left (hzero_within j).1
  · unfold aux_hKernelMaxScale
    exact max_le (hzero_within j).2 (hone_within j).2

/-- This auxiliary consequence translates a diagonal-square-root estimate to the two maximum
scales used in the `u(i)=0` part of the six-term kernel multiset. -/
theorem aux_sMultiplier_bound_orientation_zero_of_diagonal {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ)
    (horientation : γ.orientation i = 0)
    (hdiagonal : ∀ x : ℝ,
      |sMultiplier γ i j x| ≤ C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_sMultiplierScale γ i (j - 1)) x +
          scaledBracketBump 2 (aux_sMultiplierScale γ i j) x)) :
    ∀ x : ℝ, |sMultiplier γ i j x| ≤ 2 * C_diagonalSquareRoot 2 *
      (scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) x +
        scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) x) := by
  intro x
  have hprev :
      aux_hKernelMaxScale γ i 0 j ≤ aux_sMultiplierScale γ i (j - 1) ∧
        aux_sMultiplierScale γ i (j - 1) ≤ 2 * aux_hKernelMaxScale γ i 0 j := by
    simpa [aux_hKernelMaxScale, aux_hKernelShiftedScale, aux_sMultiplierScale,
      horientation] using
      (aux_sqrt_sq_add_sq_between_max_and_two_mul_max
        ((γ.scales_spaced i 0 (j - 1)).1).le
        ((γ.scales_spaced i 1 (j - 1)).1).le)
  have hcurr :
      aux_hKernelMaxScale γ i 1 j ≤ aux_sMultiplierScale γ i j ∧
        aux_sMultiplierScale γ i j ≤ 2 * aux_hKernelMaxScale γ i 1 j := by
    simpa [aux_hKernelMaxScale, aux_hKernelShiftedScale, aux_sMultiplierScale,
      horientation] using
      (aux_sqrt_sq_add_sq_between_max_and_two_mul_max
        ((γ.scales_spaced i 0 j).1).le
        ((γ.scales_spaced i 1 j).1).le)
  have hprevBump := aux_scaledBracketBump_two_scale_le (x := x)
    ((aux_hKernelMaxScale_spaced γ i 0 j).1) hprev.1 hprev.2
  have hcurrBump := aux_scaledBracketBump_two_scale_le (x := x)
    ((aux_hKernelMaxScale_spaced γ i 1 j).1) hcurr.1 hcurr.2
  calc
    |sMultiplier γ i j x| ≤ C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_sMultiplierScale γ i (j - 1)) x +
          scaledBracketBump 2 (aux_sMultiplierScale γ i j) x) := hdiagonal x
    _ ≤ C_diagonalSquareRoot 2 *
        (2 * scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) x +
          2 * scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) x) :=
      mul_le_mul_of_nonneg_left (add_le_add hprevBump hcurrBump)
        aux_C_diagonalSquareRoot_two_nonneg
    _ = 2 * C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) x +
          scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) x) := by ring

/-- This auxiliary consequence translates a diagonal-square-root estimate to the shifted second
scale sequences used in the `u(i)=1` part of the six-term kernel multiset. -/
theorem aux_sMultiplier_bound_orientation_one_of_diagonal {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ)
    (horientation : γ.orientation i ≠ 0)
    (hdiagonal : ∀ x : ℝ,
      |sMultiplier γ i j x| ≤ C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_sMultiplierScale γ i (j - 1)) x +
          scaledBracketBump 2 (aux_sMultiplierScale γ i j) x)) :
    ∀ x : ℝ, |sMultiplier γ i j x| ≤ 2 * C_diagonalSquareRoot 2 *
      (scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) x +
        scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) x) := by
  intro x
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hprev :
      aux_hKernelShiftedScale γ i 0 1 j ≤ aux_sMultiplierScale γ i (j - 1) ∧
        aux_sMultiplierScale γ i (j - 1) ≤
          2 * aux_hKernelShiftedScale γ i 0 1 j := by
    have hpos := (γ.scales_spaced i 1 (j - 1)).1
    constructor
    · simpa [aux_hKernelShiftedScale, aux_sMultiplierScale, horientation] using
        (mul_le_mul_of_nonneg_right hsqrtOne hpos.le)
    · simpa [aux_hKernelShiftedScale, aux_sMultiplierScale, horientation] using
        (mul_le_mul_of_nonneg_right hsqrtTwo hpos.le)
  have hcurr :
      aux_hKernelShiftedScale γ i 1 1 j ≤ aux_sMultiplierScale γ i j ∧
        aux_sMultiplierScale γ i j ≤
          2 * aux_hKernelShiftedScale γ i 1 1 j := by
    have hpos := (γ.scales_spaced i 1 j).1
    constructor
    · simpa [aux_hKernelShiftedScale, aux_sMultiplierScale, horientation] using
        (mul_le_mul_of_nonneg_right hsqrtOne hpos.le)
    · simpa [aux_hKernelShiftedScale, aux_sMultiplierScale, horientation] using
        (mul_le_mul_of_nonneg_right hsqrtTwo hpos.le)
  have hprevBump := aux_scaledBracketBump_two_scale_le (x := x)
    ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) hprev.1 hprev.2
  have hcurrBump := aux_scaledBracketBump_two_scale_le (x := x)
    ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) hcurr.1 hcurr.2
  calc
    |sMultiplier γ i j x| ≤ C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_sMultiplierScale γ i (j - 1)) x +
          scaledBracketBump 2 (aux_sMultiplierScale γ i j) x) := hdiagonal x
    _ ≤ C_diagonalSquareRoot 2 *
        (2 * scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) x +
          2 * scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) x) :=
      mul_le_mul_of_nonneg_left (add_le_add hprevBump hcurrBump)
        aux_C_diagonalSquareRoot_two_nonneg
    _ = 2 * C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) x +
          scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) x) := by ring

/-- This auxiliary sign check permits the derivative diagonal-square-root bound to be enlarged
or transported through the scale comparisons used below. -/
theorem aux_C_derivativeDiagonalSquareRoot_two_nonneg :
    0 ≤ C_derivativeDiagonalSquareRoot 2 := by
  have hgaussian (m N : ℕ) : 0 ≤ C_gaussianBumpDecay m N := by
    unfold C_gaussianBumpDecay
    exact Real.rpow_nonneg (by positivity) _
  unfold C_derivativeDiagonalSquareRoot
  exact mul_nonneg (by norm_num)
    (le_trans (hgaussian 1 2) (le_max_left _ _))

/-- This auxiliary consequence translates a derivative diagonal-square-root estimate to the
maximum scales used in the `u(i)=0` part of the derivative kernel estimate. -/
theorem aux_deriv_sMultiplier_bound_orientation_zero_of_diagonal {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ)
    (horientation : γ.orientation i = 0)
    (hdiagonal : ∀ x : ℝ,
      |deriv (sMultiplier γ i j) x| ≤ C_derivativeDiagonalSquareRoot 2 *
        ((aux_sMultiplierScale γ i (j - 1))⁻¹ *
            scaledBracketBump 2 (aux_sMultiplierScale γ i (j - 1)) x +
          (aux_sMultiplierScale γ i j)⁻¹ *
            scaledBracketBump 2 (aux_sMultiplierScale γ i j) x)) :
    ∀ x : ℝ, |deriv (sMultiplier γ i j) x| ≤ C_derivativeDiagonalSquareRoot 2 *
      ((aux_hKernelMaxScale γ i 0 j)⁻¹ *
          scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) x +
        (aux_hKernelMaxScale γ i 1 j)⁻¹ *
          scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) x) := by
  intro x
  have hprev :
      aux_hKernelMaxScale γ i 0 j ≤ aux_sMultiplierScale γ i (j - 1) := by
    simpa [aux_hKernelMaxScale, aux_hKernelShiftedScale, aux_sMultiplierScale,
      horientation] using
      (aux_sqrt_sq_add_sq_between_max_and_two_mul_max
        ((γ.scales_spaced i 0 (j - 1)).1).le
        ((γ.scales_spaced i 1 (j - 1)).1).le).1
  have hcurr :
      aux_hKernelMaxScale γ i 1 j ≤ aux_sMultiplierScale γ i j := by
    simpa [aux_hKernelMaxScale, aux_hKernelShiftedScale, aux_sMultiplierScale,
      horientation] using
      (aux_sqrt_sq_add_sq_between_max_and_two_mul_max
        ((γ.scales_spaced i 0 j).1).le
        ((γ.scales_spaced i 1 j).1).le).1
  have hprevBump := aux_inv_mul_scaledBracketBump_two_le_of_le_scale (x := x)
    ((aux_hKernelMaxScale_spaced γ i 0 j).1) hprev
  have hcurrBump := aux_inv_mul_scaledBracketBump_two_le_of_le_scale (x := x)
    ((aux_hKernelMaxScale_spaced γ i 1 j).1) hcurr
  calc
    |deriv (sMultiplier γ i j) x| ≤ C_derivativeDiagonalSquareRoot 2 *
        ((aux_sMultiplierScale γ i (j - 1))⁻¹ *
            scaledBracketBump 2 (aux_sMultiplierScale γ i (j - 1)) x +
          (aux_sMultiplierScale γ i j)⁻¹ *
            scaledBracketBump 2 (aux_sMultiplierScale γ i j) x) := hdiagonal x
    _ ≤ C_derivativeDiagonalSquareRoot 2 *
        ((aux_hKernelMaxScale γ i 0 j)⁻¹ *
            scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) x +
          (aux_hKernelMaxScale γ i 1 j)⁻¹ *
            scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) x) :=
      mul_le_mul_of_nonneg_left (add_le_add hprevBump hcurrBump)
        aux_C_derivativeDiagonalSquareRoot_two_nonneg

/-- This auxiliary consequence translates a derivative diagonal-square-root estimate to the
shifted second scales used in the `u(i)=1` part of the derivative kernel estimate. -/
theorem aux_deriv_sMultiplier_bound_orientation_one_of_diagonal {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ)
    (horientation : γ.orientation i ≠ 0)
    (hdiagonal : ∀ x : ℝ,
      |deriv (sMultiplier γ i j) x| ≤ C_derivativeDiagonalSquareRoot 2 *
        ((aux_sMultiplierScale γ i (j - 1))⁻¹ *
            scaledBracketBump 2 (aux_sMultiplierScale γ i (j - 1)) x +
          (aux_sMultiplierScale γ i j)⁻¹ *
            scaledBracketBump 2 (aux_sMultiplierScale γ i j) x)) :
    ∀ x : ℝ, |deriv (sMultiplier γ i j) x| ≤ C_derivativeDiagonalSquareRoot 2 *
      ((aux_hKernelShiftedScale γ i 0 1 j)⁻¹ *
          scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) x +
        (aux_hKernelShiftedScale γ i 1 1 j)⁻¹ *
          scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) x) := by
  intro x
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hprev :
      aux_hKernelShiftedScale γ i 0 1 j ≤ aux_sMultiplierScale γ i (j - 1) := by
    have hpos := (γ.scales_spaced i 1 (j - 1)).1
    simpa [aux_hKernelShiftedScale, aux_sMultiplierScale, horientation] using
      (mul_le_mul_of_nonneg_right hsqrtOne hpos.le)
  have hcurr :
      aux_hKernelShiftedScale γ i 1 1 j ≤ aux_sMultiplierScale γ i j := by
    have hpos := (γ.scales_spaced i 1 j).1
    simpa [aux_hKernelShiftedScale, aux_sMultiplierScale, horientation] using
      (mul_le_mul_of_nonneg_right hsqrtOne hpos.le)
  have hprevBump := aux_inv_mul_scaledBracketBump_two_le_of_le_scale (x := x)
    ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) hprev
  have hcurrBump := aux_inv_mul_scaledBracketBump_two_le_of_le_scale (x := x)
    ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) hcurr
  calc
    |deriv (sMultiplier γ i j) x| ≤ C_derivativeDiagonalSquareRoot 2 *
        ((aux_sMultiplierScale γ i (j - 1))⁻¹ *
            scaledBracketBump 2 (aux_sMultiplierScale γ i (j - 1)) x +
          (aux_sMultiplierScale γ i j)⁻¹ *
            scaledBracketBump 2 (aux_sMultiplierScale γ i j) x) := hdiagonal x
    _ ≤ C_derivativeDiagonalSquareRoot 2 *
        ((aux_hKernelShiftedScale γ i 0 1 j)⁻¹ *
            scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) x +
          (aux_hKernelShiftedScale γ i 1 1 j)⁻¹ *
            scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) x) :=
      mul_le_mul_of_nonneg_left (add_le_add hprevBump hcurrBump)
        aux_C_derivativeDiagonalSquareRoot_two_nonneg

/-- This auxiliary constructor packages two one-dimensional scale sequences into the sequence
pair that is an entry of the Gaussian-dominating multiset. -/
def aux_sequencePairOf (t₀ t₁ : ℤ → ℝ) : SequencePair :=
  fun r => if r = 0 then t₀ else t₁

/-- This auxiliary projection identity is used to read the two scale sequences from an entry
of the explicitly constructed multiset. -/
theorem aux_sequencePairOf_apply_zero (t₀ t₁ : ℤ → ℝ) :
    aux_sequencePairOf t₀ t₁ 0 = t₀ := by
  simp [aux_sequencePairOf]

/-- This auxiliary projection identity is used to read the two scale sequences from an entry
of the explicitly constructed multiset. -/
theorem aux_sequencePairOf_apply_one (t₀ t₁ : ℤ → ℝ) :
    aux_sequencePairOf t₀ t₁ 1 = t₁ := by
  simp [aux_sequencePairOf]

/-- This auxiliary multiset is exactly the six-element multiset constructed in the proof of
the kernel Gaussian estimate, with the two cases selected by `u(i)`. -/
def aux_hKernelGaussianMultiset {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) :
    Multiset (SequencePair × Fin 2) :=
  if γ.orientation i = 0 then
    ({(aux_sequencePairOf (aux_hKernelMaxScale γ i 0)
        (aux_hKernelMaxScale γ i 0), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelMaxScale γ i 0)
        (aux_hKernelMaxScale γ i 1), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelMaxScale γ i 1)
        (aux_hKernelMaxScale γ i 0), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelMaxScale γ i 1)
        (aux_hKernelMaxScale γ i 1), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelShiftedScale γ i 0 0)
        (aux_hKernelShiftedScale γ i 0 1), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelShiftedScale γ i 1 0)
        (aux_hKernelShiftedScale γ i 1 1), (0 : Fin 2))})
  else
    ({(aux_sequencePairOf (aux_hKernelShiftedScale γ i 0 1)
        (aux_hKernelShiftedScale γ i 0 1), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelShiftedScale γ i 0 1)
        (aux_hKernelShiftedScale γ i 1 1), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelShiftedScale γ i 1 1)
        (aux_hKernelShiftedScale γ i 0 1), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelShiftedScale γ i 1 1)
        (aux_hKernelShiftedScale γ i 1 1), (0 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelShiftedScale γ i 0 0)
        (aux_hKernelShiftedScale γ i 0 1), (1 : Fin 2))} +
      {(aux_sequencePairOf (aux_hKernelShiftedScale γ i 1 0)
        (aux_hKernelShiftedScale γ i 1 1), (1 : Fin 2))})

/-- This auxiliary theorem records the multiplicity-sensitive cardinality of the explicitly
constructed multiset; repetitions of sequences are retained, as in the manuscript. -/
theorem aux_hKernelGaussianMultiset_card {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) : (aux_hKernelGaussianMultiset γ i).card = 6 := by
  classical
  by_cases h : γ.orientation i = 0 <;>
    simp [aux_hKernelGaussianMultiset, h]

/-- This auxiliary theorem verifies the distance-ball membership of every entry of the explicit
six-element multiset from the proof of the kernel Gaussian estimate. -/
theorem aux_hKernelGaussianMultiset_valid {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) :
    aux_ValidKernelGaussianPackage γ i (aux_hKernelGaussianMultiset γ i) := by
  classical
  have hpair (t₀ t₁ : ℤ → ℝ) (u : Fin 2)
      (ht₀ : t₀ ∈ sequenceDistanceBall (γ.scales i 1) (geometricDelta γ))
      (ht₁ : t₁ ∈ sequenceDistanceBall (γ.scales i 1) (geometricDelta γ)) :
      (aux_sequencePairOf t₀ t₁, u).1 0 ∈
          sequenceDistanceBall (γ.scales i 1) (geometricDelta γ) ∧
        (aux_sequencePairOf t₀ t₁, u).1 1 ∈
          sequenceDistanceBall (γ.scales i 1) (geometricDelta γ) := by
    constructor
    · simpa [aux_sequencePairOf] using ht₀
    · simpa [aux_sequencePairOf] using ht₁
  unfold aux_ValidKernelGaussianPackage
  intro q hq
  by_cases horientation : γ.orientation i = 0
  · simp only [aux_hKernelGaussianMultiset, if_pos horientation,
      Multiset.mem_add, Multiset.mem_singleton] at hq
    rcases hq with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl)
    ·
      exact hpair _ _ _
        (aux_hKernelMaxScale_mem_sequenceDistanceBall γ i 0)
        (aux_hKernelMaxScale_mem_sequenceDistanceBall γ i 0)
    ·
      exact hpair _ _ _
        (aux_hKernelMaxScale_mem_sequenceDistanceBall γ i 0)
        (aux_hKernelMaxScale_mem_sequenceDistanceBall γ i 1)
    ·
      exact hpair _ _ _
        (aux_hKernelMaxScale_mem_sequenceDistanceBall γ i 1)
        (aux_hKernelMaxScale_mem_sequenceDistanceBall γ i 0)
    ·
      exact hpair _ _ _
        (aux_hKernelMaxScale_mem_sequenceDistanceBall γ i 1)
        (aux_hKernelMaxScale_mem_sequenceDistanceBall γ i 1)
    ·
      exact hpair _ _ _
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 0 0)
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 0 1)
    ·
      exact hpair _ _ _
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 1 0)
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 1 1)
  · simp only [aux_hKernelGaussianMultiset, if_neg horientation,
      Multiset.mem_add, Multiset.mem_singleton] at hq
    rcases hq with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl)
    ·
      exact hpair _ _ _
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 0 1)
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 0 1)
    ·
      exact hpair _ _ _
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 0 1)
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 1 1)
    ·
      exact hpair _ _ _
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 1 1)
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 0 1)
    ·
      exact hpair _ _ _
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 1 1)
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 1 1)
    ·
      exact hpair _ _ _
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 0 0)
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 0 1)
    ·
      exact hpair _ _ _
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 1 0)
        (aux_hKernelShiftedScale_mem_sequenceDistanceBall γ i 1 1)

/-- This auxiliary predicate is the full conclusion of the kernel estimate, with its
multiset retained to account for repeated sequence triples. -/
def aux_HKernelGaussianBound {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (P : Multiset (SequencePair × Fin 2)) : Prop :=
  aux_ValidKernelGaussianPackage γ i P ∧ P.card = 6 ∧
    ∀ v : RealPlane, ∀ j : ℤ,
      |hMultiplier γ i j v| ≤ C_hKernelEstimateGaussianDomination *
        (P.map fun q => aux_kernelBracketProduct q j v).sum

/-- This auxiliary predicate is the full conclusion of the differentiated kernel estimate. -/
def aux_HKernelDerivativeGaussianBound {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (P : Multiset (SequencePair × Fin 2)) : Prop :=
  aux_ValidKernelGaussianPackage γ i P ∧ P.card ≤ 6 ∧
    ∀ v : RealPlane, ∀ j : ℤ,
      |aux_diagonalDerivative (hMultiplier γ i j) v| ≤
        C_hKernelDerivativeEstimateGaussianDomination *
          (P.map fun q =>
            ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) * aux_kernelBracketProduct q j v).sum

/-- This auxiliary theorem carries out the `u(i)=0` algebra in the proof of the kernel estimate
after the one-dimensional diagonal-square-root estimate has been supplied. -/
theorem aux_hKernelGaussianBound_orientation_zero_of_sBounds {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (horientation : γ.orientation i = 0)
    (hs : ∀ (j : ℤ) (x : ℝ), |sMultiplier γ i j x| ≤
      2 * C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) x +
          scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) x)) :
    aux_HKernelGaussianBound γ i (aux_hKernelGaussianMultiset γ i) := by
  refine ⟨aux_hKernelGaussianMultiset_valid γ i,
    aux_hKernelGaussianMultiset_card γ i, ?_⟩
  intro v j
  let u₀ : ℝ := scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) v.1
  let u₁ : ℝ := scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) v.1
  let w₀ : ℝ := scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) v.2
  let w₁ : ℝ := scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) v.2
  let S : ℝ := u₀ * w₀ + u₀ * w₁ + u₁ * w₀ + u₁ * w₁
  let r₀ : ℝ :=
    scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 0 j) v.1 *
      scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) v.2
  let r₁ : ℝ :=
    scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 0 j) v.1 *
      scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) v.2
  have hu₀ : 0 ≤ u₀ := by
    dsimp [u₀]
    exact aux_scaledBracketBump_nonneg 2
      ((aux_hKernelMaxScale_spaced γ i 0 j).1) _
  have hu₁ : 0 ≤ u₁ := by
    dsimp [u₁]
    exact aux_scaledBracketBump_nonneg 2
      ((aux_hKernelMaxScale_spaced γ i 1 j).1) _
  have hw₀ : 0 ≤ w₀ := by
    dsimp [w₀]
    exact aux_scaledBracketBump_nonneg 2
      ((aux_hKernelMaxScale_spaced γ i 0 j).1) _
  have hw₁ : 0 ≤ w₁ := by
    dsimp [w₁]
    exact aux_scaledBracketBump_nonneg 2
      ((aux_hKernelMaxScale_spaced γ i 1 j).1) _
  have hr₀ : 0 ≤ r₀ := by
    dsimp [r₀]
    exact mul_nonneg
      (aux_scaledBracketBump_nonneg 2
        ((aux_hKernelShiftedScale_spaced γ i 0 0 j).1) _)
      (aux_scaledBracketBump_nonneg 2
        ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) _)
  have hr₁ : 0 ≤ r₁ := by
    dsimp [r₁]
    exact mul_nonneg
      (aux_scaledBracketBump_nonneg 2
        ((aux_hKernelShiftedScale_spaced γ i 1 0 j).1) _)
      (aux_scaledBracketBump_nonneg 2
        ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) _)
  have hS : 0 ≤ S := by
    dsimp [S]
    nlinarith [mul_nonneg hu₀ hw₀, mul_nonneg hu₀ hw₁,
      mul_nonneg hu₁ hw₀, mul_nonneg hu₁ hw₁]
  have hsx : |sMultiplier γ i j v.1| ≤
      2 * C_diagonalSquareRoot 2 * (u₀ + u₁) := by
    simpa [u₀, u₁] using hs j v.1
  have hsy : |sMultiplier γ i j v.2| ≤
      2 * C_diagonalSquareRoot 2 * (w₀ + w₁) := by
    simpa [w₀, w₁] using hs j v.2
  have hprodRaw :
      |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| ≤
        (2 * C_diagonalSquareRoot 2) ^ 2 *
          (u₀ * w₀ + u₀ * w₁ + u₁ * w₀ + u₁ * w₁) := by
    exact aux_abs_mul_le_four_products
      (mul_nonneg (by norm_num) aux_C_diagonalSquareRoot_two_nonneg)
      hu₀ hu₁ hw₀ hw₁ hsx hsy
  have hprod : |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| ≤
      4 * C_diagonalSquareRoot 2 ^ 2 * S := by
    calc
      |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| ≤
          (2 * C_diagonalSquareRoot 2) ^ 2 *
            (u₀ * w₀ + u₀ * w₁ + u₁ * w₀ + u₁ * w₁) := hprodRaw
      _ = 4 * C_diagonalSquareRoot 2 ^ 2 * S := by
        dsimp [S]
        ring
  have hgammaPrev : gammaGaussian γ i (j - 1) v ≤
      C_gaussianBumpDecay 0 2 ^ 2 * r₀ := by
    simpa [gammaGaussian, r₀, aux_hKernelShiftedScale, horientation, W] using
      (aux_twoDimensionalGaussian_le_gaussianBumpProduct
        (fun r => γ.scales i r (j - 1))
        (fun r => (γ.scales_spaced i r (j - 1)).1) (γ.orientation i) v)
  have hgammaCurr : gammaGaussian γ i j v ≤
      C_gaussianBumpDecay 0 2 ^ 2 * r₁ := by
    simpa [gammaGaussian, r₁, aux_hKernelShiftedScale, horientation, W] using
      (aux_twoDimensionalGaussian_le_gaussianBumpProduct
        (fun r => γ.scales i r j)
        (fun r => (γ.scales_spaced i r j).1) (γ.orientation i) v)
  have hgaussConst : 0 ≤ C_gaussianBumpDecay 0 2 := by
    unfold C_gaussianBumpDecay
    exact Real.rpow_nonneg (by positivity) _
  have hmajorant :
      |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| +
          C_gaussianBumpDecay 0 2 ^ 2 * r₀ +
          C_gaussianBumpDecay 0 2 ^ 2 * r₁ ≤
        (4 * C_diagonalSquareRoot 2 ^ 2 + C_gaussianBumpDecay 0 2 ^ 2) *
          (S + r₀ + r₁) :=
    aux_sixTermKernelMajorant aux_C_diagonalSquareRoot_two_nonneg hgaussConst hS hr₀ hr₁ hprod
  have hsum :
      ((aux_hKernelGaussianMultiset γ i).map fun q =>
        aux_kernelBracketProduct q j v).sum = S + r₀ + r₁ := by
    simp [aux_hKernelGaussianMultiset, horientation, aux_kernelBracketProduct,
      aux_sequencePairOf, W, u₀, u₁, w₀, w₁, S, r₀, r₁] <;> ring
  calc
    |hMultiplier γ i j v| ≤
        |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| +
          gammaGaussian γ i (j - 1) v + gammaGaussian γ i j v :=
      by simpa only [abs_mul] using (aux_abs_hMultiplier_le γ i j v)
    _ ≤ |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| +
          C_gaussianBumpDecay 0 2 ^ 2 * r₀ +
            C_gaussianBumpDecay 0 2 ^ 2 * r₁ := by
      exact add_le_add (add_le_add le_rfl hgammaPrev) hgammaCurr
    _ ≤ (4 * C_diagonalSquareRoot 2 ^ 2 + C_gaussianBumpDecay 0 2 ^ 2) *
          (S + r₀ + r₁) := hmajorant
    _ = C_hKernelEstimateGaussianDomination *
        ((aux_hKernelGaussianMultiset γ i).map fun q =>
          aux_kernelBracketProduct q j v).sum := by
      rw [hsum]
      unfold C_hKernelEstimateGaussianDomination
      ring

/-- This auxiliary theorem carries out the `u(i)=1` algebra in the proof of the kernel estimate
after the one-dimensional diagonal-square-root estimate has been supplied. -/
theorem aux_hKernelGaussianBound_orientation_one_of_sBounds {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (horientation : γ.orientation i ≠ 0)
    (hs : ∀ (j : ℤ) (x : ℝ), |sMultiplier γ i j x| ≤
      2 * C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) x +
          scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) x)) :
    aux_HKernelGaussianBound γ i (aux_hKernelGaussianMultiset γ i) := by
  refine ⟨aux_hKernelGaussianMultiset_valid γ i,
    aux_hKernelGaussianMultiset_card γ i, ?_⟩
  intro v j
  let u₀ : ℝ := scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) v.1
  let u₁ : ℝ := scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) v.1
  let w₀ : ℝ := scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) v.2
  let w₁ : ℝ := scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) v.2
  let S : ℝ := u₀ * w₀ + u₀ * w₁ + u₁ * w₀ + u₁ * w₁
  let r₀ : ℝ :=
    scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 0 j) (W 1 v).1 *
      scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) (W 1 v).2
  let r₁ : ℝ :=
    scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 0 j) (W 1 v).1 *
      scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) (W 1 v).2
  have hu₀ : 0 ≤ u₀ := by
    dsimp [u₀]
    exact aux_scaledBracketBump_nonneg 2
      ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) _
  have hu₁ : 0 ≤ u₁ := by
    dsimp [u₁]
    exact aux_scaledBracketBump_nonneg 2
      ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) _
  have hw₀ : 0 ≤ w₀ := by
    dsimp [w₀]
    exact aux_scaledBracketBump_nonneg 2
      ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) _
  have hw₁ : 0 ≤ w₁ := by
    dsimp [w₁]
    exact aux_scaledBracketBump_nonneg 2
      ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) _
  have hr₀ : 0 ≤ r₀ := by
    dsimp [r₀]
    exact mul_nonneg
      (aux_scaledBracketBump_nonneg 2
        ((aux_hKernelShiftedScale_spaced γ i 0 0 j).1) _)
      (aux_scaledBracketBump_nonneg 2
        ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) _)
  have hr₁ : 0 ≤ r₁ := by
    dsimp [r₁]
    exact mul_nonneg
      (aux_scaledBracketBump_nonneg 2
        ((aux_hKernelShiftedScale_spaced γ i 1 0 j).1) _)
      (aux_scaledBracketBump_nonneg 2
        ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) _)
  have hS : 0 ≤ S := by
    dsimp [S]
    nlinarith [mul_nonneg hu₀ hw₀, mul_nonneg hu₀ hw₁,
      mul_nonneg hu₁ hw₀, mul_nonneg hu₁ hw₁]
  have hsx : |sMultiplier γ i j v.1| ≤
      2 * C_diagonalSquareRoot 2 * (u₀ + u₁) := by
    simpa [u₀, u₁] using hs j v.1
  have hsy : |sMultiplier γ i j v.2| ≤
      2 * C_diagonalSquareRoot 2 * (w₀ + w₁) := by
    simpa [w₀, w₁] using hs j v.2
  have hprodRaw :
      |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| ≤
        (2 * C_diagonalSquareRoot 2) ^ 2 *
          (u₀ * w₀ + u₀ * w₁ + u₁ * w₀ + u₁ * w₁) := by
    exact aux_abs_mul_le_four_products
      (mul_nonneg (by norm_num) aux_C_diagonalSquareRoot_two_nonneg)
      hu₀ hu₁ hw₀ hw₁ hsx hsy
  have hprod : |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| ≤
      4 * C_diagonalSquareRoot 2 ^ 2 * S := by
    calc
      |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| ≤
          (2 * C_diagonalSquareRoot 2) ^ 2 *
            (u₀ * w₀ + u₀ * w₁ + u₁ * w₀ + u₁ * w₁) := hprodRaw
      _ = 4 * C_diagonalSquareRoot 2 ^ 2 * S := by
        dsimp [S]
        ring
  have hgammaPrev : gammaGaussian γ i (j - 1) v ≤
      C_gaussianBumpDecay 0 2 ^ 2 * r₀ := by
    simpa [gammaGaussian, r₀, aux_hKernelShiftedScale, horientation, W] using
      (aux_twoDimensionalGaussian_le_gaussianBumpProduct
        (fun r => γ.scales i r (j - 1))
        (fun r => (γ.scales_spaced i r (j - 1)).1) (γ.orientation i) v)
  have hgammaCurr : gammaGaussian γ i j v ≤
      C_gaussianBumpDecay 0 2 ^ 2 * r₁ := by
    simpa [gammaGaussian, r₁, aux_hKernelShiftedScale, horientation, W] using
      (aux_twoDimensionalGaussian_le_gaussianBumpProduct
        (fun r => γ.scales i r j)
        (fun r => (γ.scales_spaced i r j).1) (γ.orientation i) v)
  have hgaussConst : 0 ≤ C_gaussianBumpDecay 0 2 := by
    unfold C_gaussianBumpDecay
    exact Real.rpow_nonneg (by positivity) _
  have hmajorant :
      |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| +
          C_gaussianBumpDecay 0 2 ^ 2 * r₀ +
          C_gaussianBumpDecay 0 2 ^ 2 * r₁ ≤
        (4 * C_diagonalSquareRoot 2 ^ 2 + C_gaussianBumpDecay 0 2 ^ 2) *
          (S + r₀ + r₁) :=
    aux_sixTermKernelMajorant aux_C_diagonalSquareRoot_two_nonneg hgaussConst hS hr₀ hr₁ hprod
  have hsum :
      ((aux_hKernelGaussianMultiset γ i).map fun q =>
        aux_kernelBracketProduct q j v).sum = S + r₀ + r₁ := by
    simp [aux_hKernelGaussianMultiset, horientation, aux_kernelBracketProduct,
      aux_sequencePairOf, W, u₀, u₁, w₀, w₁, S, r₀, r₁] <;> ring
  calc
    |hMultiplier γ i j v| ≤
        |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| +
          gammaGaussian γ i (j - 1) v + gammaGaussian γ i j v :=
      by simpa only [abs_mul] using (aux_abs_hMultiplier_le γ i j v)
    _ ≤ |sMultiplier γ i j v.1 * sMultiplier γ i j v.2| +
          C_gaussianBumpDecay 0 2 ^ 2 * r₀ +
            C_gaussianBumpDecay 0 2 ^ 2 * r₁ := by
      exact add_le_add (add_le_add le_rfl hgammaPrev) hgammaCurr
    _ ≤ (4 * C_diagonalSquareRoot 2 ^ 2 + C_gaussianBumpDecay 0 2 ^ 2) *
          (S + r₀ + r₁) := hmajorant
    _ = C_hKernelEstimateGaussianDomination *
        ((aux_hKernelGaussianMultiset γ i).map fun q =>
          aux_kernelBracketProduct q j v).sum := by
      rw [hsum]
      unfold C_hKernelEstimateGaussianDomination
      ring

/-- This auxiliary structure is a direct finite-set encoding of the data in the conclusion of
Gaussian domination.  Its fields are exactly the set `\mathcal B`, orientations `u_b`, and
sequence pairs `p_{b,m}` from the manuscript. -/
structure aux_GaussianDominationWitness {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (i : Fin γ.k) (ι : MultiplierIndex γ) (C : ℝ) where
  B : Finset ℕ
  card_le : B.card ≤ C_gaussianDominationCombinedCard
  orientation : ℕ → Fin 2
  scales : ℕ → (Fin 2 → ℕ) → SequencePair
  scales_in_A : ∀ b ∈ B, ∀ m, ∀ r, SpacedSequence (scales b m r)
  distance_bound : ∀ b ∈ B, ∀ m,
    sequencePairDistance (scales b m) ≤
      (C_gaussianDominationCombinedDistance : WithTop ℕ) *
        ((geometricDelta γ + ι.1.1.natAbs + aux_natPairWeight m : ℕ) : WithTop ℕ)
  estimate : ∀ (j : ℤ) (v : RealPlane),
    |nMultiplier γ hkn ι i j v| ≤
      C * Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          ∑ b ∈ B, aux_dominatingGaussianTerm (scales b m) (orientation b) j v
  series_summable : ∀ j : ℤ, ∀ v : RealPlane,
    Summable (fun m : Fin 2 → ℕ => aux_gaussianDominationWeight m *
      ∑ b ∈ B, aux_dominatingGaussianTerm (scales b m) (orientation b) j v)
  series_integrable : ∀ j : ℤ,
    Integrable (fun v : RealPlane => ∑' m : Fin 2 → ℕ,
      aux_gaussianDominationWeight m *
        ∑ b ∈ B, aux_dominatingGaussianTerm (scales b m) (orientation b) j v)

/-- This auxiliary predicate packages precisely the conclusion of Proposition
`\ref{Gaussian domination combined}` for a fixed index. -/
def aux_GaussianDominationConclusion {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (i : Fin γ.k) (ι : MultiplierIndex γ) (C : ℝ) : Prop :=
  Nonempty (aux_GaussianDominationWitness γ hkn i ι C)

end

end Codex.MainArgument.GaussianDomination
