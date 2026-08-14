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
    exact aux_C_gaussianBumpDecay_nonneg 0 2
  have hC₁ : 0 ≤ C_gaussianBumpDecay 1 2 := by
    exact aux_C_gaussianBumpDecay_nonneg 1 2
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

/-- This auxiliary product-rule identity evaluates the diagonal derivative of a two-dimensional
Gaussian in the nontrivial orientation. -/
theorem aux_diagonalDerivative_twoDimensionalGaussian_one
    (t : Fin 2 → ℝ) (v : RealPlane) :
    aux_diagonalDerivative (twoDimensionalGaussian t 1) v =
      Real.sqrt 2 * deriv (gaussianRescale (t 0)) (W 1 v).1 *
        gaussianRescale (t 1) (W 1 v).2 := by
  have hsqrtPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  let p : ℝ → ℝ := fun s => ((v.1 + s) + (v.2 + s)) / Real.sqrt 2
  let q : ℝ → ℝ := fun s => (-(v.1 + s) + (v.2 + s)) / Real.sqrt 2
  have hv₁ : HasDerivAt (fun s : ℝ => v.1 + s) 1 0 := by
    simpa using (hasDerivAt_id 0).const_add v.1
  have hv₂ : HasDerivAt (fun s : ℝ => v.2 + s) 1 0 := by
    simpa using (hasDerivAt_id 0).const_add v.2
  have hpraw : HasDerivAt (fun s : ℝ => (v.1 + s) + (v.2 + s)) 2 0 := by
    change HasDerivAt ((fun s : ℝ => v.1 + s) + fun s => v.2 + s) 2 0
    have hsum := hv₁.add hv₂
    norm_num at hsum
    exact hsum
  have hqraw : HasDerivAt (fun s : ℝ => -(v.1 + s) + (v.2 + s)) 0 0 := by
    change HasDerivAt (-(fun s : ℝ => v.1 + s) + fun s => v.2 + s) 0 0
    have hsum := hv₁.neg.add hv₂
    norm_num at hsum
    exact hsum
  have htwoDiv : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
    field_simp
    nlinarith [hsqrtSq]
  have hp : HasDerivAt p (Real.sqrt 2) 0 := by
    simpa [p, htwoDiv] using hpraw.div_const (Real.sqrt 2)
  have hq : HasDerivAt q 0 0 := by
    simpa [q] using hqraw.div_const (Real.sqrt 2)
  have hfirstRaw := (gaussianRescale_hasDerivAt (t 0) (p 0)).comp 0 hp
  have hsecondRaw := (gaussianRescale_hasDerivAt (t 1) (q 0)).comp 0 hq
  have hprodRaw := hfirstRaw.mul hsecondRaw
  have hp0 : p 0 = (W 1 v).1 := by
    simp [p, W]
  have hq0 : q 0 = (W 1 v).2 := by
    simp [q, W]
  have hfirstDeriv : deriv (gaussianRescale (t 0)) (p 0) =
      (t 0)⁻¹ * (-2 * Real.pi * ((t 0)⁻¹ * p 0) *
        Preliminaries.Gaussians.gaussian ((t 0)⁻¹ * p 0)) * (t 0)⁻¹ :=
    (gaussianRescale_hasDerivAt (t 0) (p 0)).deriv
  have hdiag : (fun s : ℝ => twoDimensionalGaussian t 1 (v.1 + s, v.2 + s)) =
      (gaussianRescale (t 0) ∘ p) * (gaussianRescale (t 1) ∘ q) := by
    funext s
    simp [twoDimensionalGaussian, W, p, q, Function.comp_apply]
  unfold aux_diagonalDerivative
  rw [hdiag]
  rw [hprodRaw.deriv]
  simp only [Function.comp_apply]
  rw [← hfirstDeriv, hp0, hq0]
  ring

/-- This auxiliary estimate bounds the diagonal derivative of a product Gaussian in the
nontrivial orientation by the weighted bracket product used in the derivative kernel estimate. -/
theorem aux_abs_diagonalDerivative_twoDimensionalGaussian_one_le
    (t : Fin 2 → ℝ) (ht : ∀ r : Fin 2, 0 < t r) (v : RealPlane) :
    |aux_diagonalDerivative (twoDimensionalGaussian t 1) v| ≤
      2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
        ((t 0)⁻¹ + (t 1)⁻¹) *
          (scaledBracketBump 2 (t 0) (W 1 v).1 *
            scaledBracketBump 2 (t 1) (W 1 v).2) := by
  rw [aux_diagonalDerivative_twoDimensionalGaussian_one]
  let b₀ : ℝ := scaledBracketBump 2 (t 0) (W 1 v).1
  let b₁ : ℝ := scaledBracketBump 2 (t 1) (W 1 v).2
  have hb₀ : 0 ≤ b₀ := by
    dsimp [b₀]
    exact aux_scaledBracketBump_nonneg 2 (ht 0) _
  have hb₁ : 0 ≤ b₁ := by
    dsimp [b₁]
    exact aux_scaledBracketBump_nonneg 2 (ht 1) _
  have hC₀ : 0 ≤ C_gaussianBumpDecay 0 2 :=
    aux_C_gaussianBumpDecay_nonneg 0 2
  have hC₁ : 0 ≤ C_gaussianBumpDecay 1 2 :=
    aux_C_gaussianBumpDecay_nonneg 1 2
  have hinv₀ : 0 ≤ (t 0)⁻¹ := inv_nonneg.mpr (ht 0).le
  have hinv₁ : 0 ≤ (t 1)⁻¹ := inv_nonneg.mpr (ht 1).le
  have hd₀ : |deriv (gaussianRescale (t 0)) (W 1 v).1| ≤
      (t 0)⁻¹ * C_gaussianBumpDecay 1 2 * b₀ := by
    simpa [b₀] using gaussianRescale_deriv_bound
      (t := t 0) (x := (W 1 v).1) (ht 0)
  have hg₁ : |gaussianRescale (t 1) (W 1 v).2| ≤
      C_gaussianBumpDecay 0 2 * b₁ := by
    simpa [b₁] using gaussianRescale_le_C_gaussianBumpDecay_zero_two
      (t := t 1) (x := (W 1 v).2) (ht 1)
  have hsqrtNonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrtLe : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hrightNonneg : 0 ≤ (t 0)⁻¹ * C_gaussianBumpDecay 1 2 * b₀ :=
    mul_nonneg (mul_nonneg hinv₀ hC₁) hb₀
  have hrest : 0 ≤ C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * b₀ * b₁ :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₀ hC₁) hb₀) hb₁
  have hfactor : Real.sqrt (2 : ℝ) * (t 0)⁻¹ ≤
      2 * ((t 0)⁻¹ + (t 1)⁻¹) := by
    calc
      Real.sqrt (2 : ℝ) * (t 0)⁻¹ ≤ 2 * (t 0)⁻¹ :=
        mul_le_mul_of_nonneg_right hsqrtLe hinv₀
      _ ≤ 2 * ((t 0)⁻¹ + (t 1)⁻¹) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hinv₁) (by norm_num)
  calc
    |Real.sqrt 2 * deriv (gaussianRescale (t 0)) (W 1 v).1 *
        gaussianRescale (t 1) (W 1 v).2| =
        Real.sqrt 2 * (|deriv (gaussianRescale (t 0)) (W 1 v).1| *
          |gaussianRescale (t 1) (W 1 v).2|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hsqrtNonneg]
      ring
    _ ≤ Real.sqrt 2 *
        (((t 0)⁻¹ * C_gaussianBumpDecay 1 2 * b₀) *
          (C_gaussianBumpDecay 0 2 * b₁)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hd₀ hg₁ (abs_nonneg _) hrightNonneg) hsqrtNonneg
    _ = (Real.sqrt 2 * (t 0)⁻¹) *
        (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * b₀ * b₁) := by
      ring
    _ ≤ (2 * ((t 0)⁻¹ + (t 1)⁻¹)) *
        (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * b₀ * b₁) :=
      mul_le_mul_of_nonneg_right hfactor hrest
    _ = 2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
        ((t 0)⁻¹ + (t 1)⁻¹) * (b₀ * b₁) := by ring
    _ = 2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
        ((t 0)⁻¹ + (t 1)⁻¹) *
          (scaledBracketBump 2 (t 0) (W 1 v).1 *
            scaledBracketBump 2 (t 1) (W 1 v).2) := by
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
    exact aux_C_gaussianBumpDecay_nonneg m N
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
def C_gaussianDominationCombinedCard : ℕ := 36

/-- Constant from Proposition \ref{Gaussian domination combined}, formalized by
`gaussianDominationCombined`. -/
def C_gaussianDominationCombinedDistance : ℕ := 2

/-- Constant from Proposition \ref{Gaussian domination combined}, formalized by
`gaussianDominationCombined`. -/
def C_gaussianDominationCombined : ℝ := (2 : ℝ) ^ (153 : ℕ)

/-- Constant from Proposition \ref{Gauss domination case 1}, formalized by
`gaussDominationCase1`. -/
noncomputable def C_gaussDominationCase1 : ℝ :=
  2 * ((2 : ℝ) ^ (7 : ℕ) * Real.pi * Real.exp (2 * Real.pi) *
    C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2 *
    C_hKernelEstimateGaussianDomination *
    max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
      (4 * C_bumpTriangle (-(1 / 2)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2)))

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

/-- Each Gaussian term in a domination series is a Wiener function. -/
theorem aux_dominatingGaussianTerm_memW0 (p : SequencePair)
    (hp : ∀ r : Fin 2, SpacedSequence (p r)) (u : Fin 2) (j : ℤ) :
    MemW0 (aux_dominatingGaussianTerm p u j) := by
  unfold aux_dominatingGaussianTerm
  apply aux_twoDimensionalGaussian_memW0
  intro r
  exact aux_spacedSequence_pos (hp r) j

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
    exact aux_C_gaussianBumpDecay_nonneg 0 2
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

/-- This auxiliary arithmetic step combines the tensor derivative contribution and the two
Gaussian derivative contributions into the six-term differentiated-kernel majorant. -/
theorem aux_sixTermDerivativeMajorant {X c d g S r₀ r₁ : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hg : 0 ≤ g)
    (hS : 0 ≤ S) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hX : X ≤ 4 * c * d * S) :
    X + g * r₀ + g * r₁ ≤ (4 * c * d + g) * (S + r₀ + r₁) := by
  have hcd : 0 ≤ 4 * c * d := by positivity
  have hextra : 0 ≤ 4 * c * d * r₀ + 4 * c * d * r₁ + g * S := by positivity
  calc
    X + g * r₀ + g * r₁ ≤ 4 * c * d * S + g * r₀ + g * r₁ := by
      linarith
    _ ≤ (4 * c * d * S + g * r₀ + g * r₁) +
        (4 * c * d * r₀ + 4 * c * d * r₁ + g * S) :=
      le_add_of_nonneg_right hextra
    _ = (4 * c * d + g) * (S + r₀ + r₁) := by ring

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

/-- This auxiliary identity evaluates the diagonal derivative of a difference once both
restrictions to the diagonal line are differentiable. -/
theorem aux_diagonalDerivative_sub
    {f g : RealPlane → ℝ} {v : RealPlane}
    (hf : DifferentiableAt ℝ (fun t : ℝ => f (v.1 + t, v.2 + t)) 0)
    (hg : DifferentiableAt ℝ (fun t : ℝ => g (v.1 + t, v.2 + t)) 0) :
    aux_diagonalDerivative (fun w : RealPlane => f w - g w) v =
      aux_diagonalDerivative f v - aux_diagonalDerivative g v := by
  unfold aux_diagonalDerivative
  exact deriv_sub hf hg

/-- This auxiliary supplies differentiability along the diagonal line for a tensor square. -/
theorem aux_tensor_line_differentiable {f : ℝ → ℝ} {v : RealPlane}
    (hf₀ : DifferentiableAt ℝ f v.1) (hf₁ : DifferentiableAt ℝ f v.2) :
    DifferentiableAt ℝ (fun t : ℝ => f (v.1 + t) * f (v.2 + t)) 0 := by
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
  exact (hleft.mul hright).differentiableAt

/-- The scalar multiplier is differentiable, by its diagonal-square-root representation. -/
theorem aux_sMultiplier_differentiable {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) :
    Differentiable ℝ (sMultiplier γ i j) := by
  rw [show sMultiplier γ i j =
      diagonalSquareRoot (aux_sMultiplierScale γ i (j - 1))
        (aux_sMultiplierScale γ i j) by
    funext x
    exact aux_sMultiplier_eq_diagonalSquareRoot γ i j x]
  have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
  apply derivativeDiagonalSquareRoot_differentiable
  · linarith [hsp.1]
  · convert hsp.2 using 1 <;> ring

/-- Each gamma Gaussian is differentiable along every translated diagonal line. -/
theorem aux_gammaGaussian_diagonal_differentiable {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ)
    (v : RealPlane) :
    DifferentiableAt ℝ (fun t : ℝ => gammaGaussian γ i j (v.1 + t, v.2 + t)) 0 := by
  unfold gammaGaussian twoDimensionalGaussian
  by_cases h : γ.orientation i = 0
  · simp [W, h]
    apply DifferentiableAt.mul
    · apply (gaussianRescale_hasDerivAt (γ.scales i 0 j) _).differentiableAt.comp 0
      fun_prop
    · apply (gaussianRescale_hasDerivAt (γ.scales i 1 j) _).differentiableAt.comp 0
      fun_prop
  · simp [W, h]
    apply DifferentiableAt.mul
    · apply (gaussianRescale_hasDerivAt (γ.scales i 0 j) _).differentiableAt.comp 0
      fun_prop
    · apply (gaussianRescale_hasDerivAt (γ.scales i 1 j) _).differentiableAt.comp 0
      fun_prop

/-- This auxiliary identity expands the diagonal derivative of the H multiplier once its
component restrictions to the diagonal line are differentiable. -/
theorem aux_hMultiplier_diagonalDerivative_decomposition
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (v : RealPlane)
    (hs₀ : DifferentiableAt ℝ (sMultiplier γ i j) v.1)
    (hs₁ : DifferentiableAt ℝ (sMultiplier γ i j) v.2)
    (htensor : DifferentiableAt ℝ (fun t : ℝ =>
      sMultiplier γ i j (v.1 + t) * sMultiplier γ i j (v.2 + t)) 0)
    (hprev : DifferentiableAt ℝ (fun t : ℝ =>
      gammaGaussian γ i (j - 1) (v.1 + t, v.2 + t)) 0)
    (hcurr : DifferentiableAt ℝ (fun t : ℝ =>
      gammaGaussian γ i j (v.1 + t, v.2 + t)) 0) :
    aux_diagonalDerivative (hMultiplier γ i j) v =
      (deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
        sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2) -
      (aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v -
        aux_diagonalDerivative (gammaGaussian γ i j) v) := by
  change aux_diagonalDerivative (fun w : RealPlane =>
    sMultiplier γ i j w.1 * sMultiplier γ i j w.2 - gaussianDifference γ i j w) v = _
  have hgaussianDifference : aux_diagonalDerivative (gaussianDifference γ i j) v =
      aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v -
        aux_diagonalDerivative (gammaGaussian γ i j) v := by
    unfold gaussianDifference
    exact aux_diagonalDerivative_sub hprev hcurr
  have hgaussianDifferenceDiff : DifferentiableAt ℝ (fun t : ℝ =>
      gaussianDifference γ i j (v.1 + t, v.2 + t)) 0 := by
    change DifferentiableAt ℝ
      ((fun t : ℝ => gammaGaussian γ i (j - 1) (v.1 + t, v.2 + t)) -
        fun t : ℝ => gammaGaussian γ i j (v.1 + t, v.2 + t)) 0
    exact hprev.sub hcurr
  rw [aux_diagonalDerivative_sub htensor hgaussianDifferenceDiff]
  rw [aux_diagonalDerivative_tensor hs₀ hs₁, hgaussianDifference]

/-- This auxiliary triangle inequality isolates the tensor and two Gaussian derivative terms
in the differentiated H multiplier. -/
theorem aux_abs_hMultiplier_diagonalDerivative_triangle
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (v : RealPlane)
    (hs₀ : DifferentiableAt ℝ (sMultiplier γ i j) v.1)
    (hs₁ : DifferentiableAt ℝ (sMultiplier γ i j) v.2)
    (htensor : DifferentiableAt ℝ (fun t : ℝ =>
      sMultiplier γ i j (v.1 + t) * sMultiplier γ i j (v.2 + t)) 0)
    (hprev : DifferentiableAt ℝ (fun t : ℝ =>
      gammaGaussian γ i (j - 1) (v.1 + t, v.2 + t)) 0)
    (hcurr : DifferentiableAt ℝ (fun t : ℝ =>
      gammaGaussian γ i j (v.1 + t, v.2 + t)) 0) :
    |aux_diagonalDerivative (hMultiplier γ i j) v| ≤
      |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
        sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| +
      |aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v| +
        |aux_diagonalDerivative (gammaGaussian γ i j) v| := by
  rw [aux_hMultiplier_diagonalDerivative_decomposition γ i j v hs₀ hs₁ htensor hprev hcurr]
  calc
    |(deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
        sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2) -
        (aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v -
          aux_diagonalDerivative (gammaGaussian γ i j) v)| ≤
        |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
          sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| +
          |aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v -
          aux_diagonalDerivative (gammaGaussian γ i j) v| := by
      calc
        |(deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
            sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2) -
            (aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v -
              aux_diagonalDerivative (gammaGaussian γ i j) v)| ≤
            |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
              sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| +
              |0 - (aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v -
                aux_diagonalDerivative (gammaGaussian γ i j) v)| :=
          by simpa using (abs_sub_le
            (deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
              sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2)
            0
            (aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v -
              aux_diagonalDerivative (gammaGaussian γ i j) v))
        _ = _ := by
          congr 1
          rw [← abs_neg]
          congr 1
          ring
    _ ≤ |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
          sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| +
        (|aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v| +
          |aux_diagonalDerivative (gammaGaussian γ i j) v|) := by
      apply add_le_add_right
      simpa using (abs_sub_le
        (aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v) 0
        (aux_diagonalDerivative (gammaGaussian γ i j) v))
    _ = _ := by ring

/-- This auxiliary sign check permits the diagonal-square-root bound to be enlarged by the
scale-comparison factor in the kernel estimate. -/
theorem aux_C_diagonalSquareRoot_two_nonneg :
    0 ≤ C_diagonalSquareRoot 2 := by
  have hgaussian (m N : ℕ) : 0 ≤ C_gaussianBumpDecay m N := by
    exact aux_C_gaussianBumpDecay_nonneg m N
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
    exact aux_C_gaussianBumpDecay_nonneg m N
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
    exact aux_C_gaussianBumpDecay_nonneg 0 2
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
    exact aux_C_gaussianBumpDecay_nonneg 0 2
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

/-- Source label `\ref{H kernel estimate Gaussian domination}`. -/
theorem hKernelEstimateGaussianDomination {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) :
    ∃ P : Multiset (SequencePair × Fin 2), aux_HKernelGaussianBound γ i P := by
  refine ⟨aux_hKernelGaussianMultiset γ i, ?_⟩
  by_cases h : γ.orientation i = 0
  · apply aux_hKernelGaussianBound_orientation_zero_of_sBounds γ i h
    intro j x
    apply aux_sMultiplier_bound_orientation_zero_of_diagonal γ i j h
    intro y
    rw [aux_sMultiplier_eq_diagonalSquareRoot]
    have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
    apply diagonalSquareRoot_bound 2 (by norm_num)
    · linarith [hsp.1]
    · convert hsp.2 using 1 <;> ring
  · apply aux_hKernelGaussianBound_orientation_one_of_sBounds γ i h
    intro j x
    apply aux_sMultiplier_bound_orientation_one_of_diagonal γ i j h
    intro y
    rw [aux_sMultiplier_eq_diagonalSquareRoot]
    have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
    apply diagonalSquareRoot_bound 2 (by norm_num)
    · linarith [hsp.1]
    · convert hsp.2 using 1 <;> ring

/-- Source label `\ref{constant H kernel estimate Gaussian domination}`. -/
theorem constantHKernelEstimateGaussianDomination :
    C_hKernelEstimateGaussianDomination = 51 ^ 2 * 2 ^ 15 + 12 ^ 2 ∧
      C_hKernelEstimateGaussianDomination < 2 ^ 27 := by
  have hgaussian : C_gaussianBumpDecay 0 2 = 12 := by
    norm_num [C_gaussianBumpDecay]
  have hsqrt : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  constructor
  · rw [C_hKernelEstimateGaussianDomination, aux_constantDiagonalSquareRoot_two, hgaussian]
    ring_nf
    rw [hsqrt]
    norm_num
  · rw [C_hKernelEstimateGaussianDomination, aux_constantDiagonalSquareRoot_two, hgaussian]
    ring_nf
    rw [hsqrt]
    norm_num

/-- This auxiliary theorem carries out the differentiated six-term kernel algebra in the
identity-orientation case. -/
theorem aux_hKernelDerivativeGaussianBound_orientation_zero_of_sBounds {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (horientation : γ.orientation i = 0)
    (hs : ∀ (j : ℤ) (x : ℝ), |sMultiplier γ i j x| ≤
      2 * C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) x +
          scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) x))
    (hds : ∀ (j : ℤ) (x : ℝ), |deriv (sMultiplier γ i j) x| ≤
      C_derivativeDiagonalSquareRoot 2 *
        ((aux_hKernelMaxScale γ i 0 j)⁻¹ *
            scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) x +
          (aux_hKernelMaxScale γ i 1 j)⁻¹ *
            scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) x)) :
    aux_HKernelDerivativeGaussianBound γ i (aux_hKernelGaussianMultiset γ i) := by
  classical
  refine ⟨aux_hKernelGaussianMultiset_valid γ i,
    (aux_hKernelGaussianMultiset_card γ i).le, ?_⟩
  intro v j
  let a₀ : ℝ := (aux_hKernelMaxScale γ i 0 j)⁻¹
  let a₁ : ℝ := (aux_hKernelMaxScale γ i 1 j)⁻¹
  let b₀ : ℝ := (aux_hKernelMaxScale γ i 0 j)⁻¹
  let b₁ : ℝ := (aux_hKernelMaxScale γ i 1 j)⁻¹
  let u₀ : ℝ := scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) v.1
  let u₁ : ℝ := scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) v.1
  let w₀ : ℝ := scaledBracketBump 2 (aux_hKernelMaxScale γ i 0 j) v.2
  let w₁ : ℝ := scaledBracketBump 2 (aux_hKernelMaxScale γ i 1 j) v.2
  let S : ℝ :=
    (a₀ + b₀) * u₀ * w₀ + (a₀ + b₁) * u₀ * w₁ +
      (a₁ + b₀) * u₁ * w₀ + (a₁ + b₁) * u₁ * w₁
  let r₀ : ℝ :=
    ((aux_hKernelShiftedScale γ i 0 0 j)⁻¹ +
      (aux_hKernelShiftedScale γ i 0 1 j)⁻¹) *
      (scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 0 j) v.1 *
        scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) v.2)
  let r₁ : ℝ :=
    ((aux_hKernelShiftedScale γ i 1 0 j)⁻¹ +
      (aux_hKernelShiftedScale γ i 1 1 j)⁻¹) *
      (scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 0 j) v.1 *
        scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) v.2)
  have ha₀ : 0 ≤ a₀ := by
    dsimp [a₀]
    exact inv_nonneg.mpr ((aux_hKernelMaxScale_spaced γ i 0 j).1).le
  have ha₁ : 0 ≤ a₁ := by
    dsimp [a₁]
    exact inv_nonneg.mpr ((aux_hKernelMaxScale_spaced γ i 1 j).1).le
  have hb₀ : 0 ≤ b₀ := by
    dsimp [b₀]
    exact inv_nonneg.mpr ((aux_hKernelMaxScale_spaced γ i 0 j).1).le
  have hb₁ : 0 ≤ b₁ := by
    dsimp [b₁]
    exact inv_nonneg.mpr ((aux_hKernelMaxScale_spaced γ i 1 j).1).le
  have hu₀ : 0 ≤ u₀ := by
    dsimp [u₀]
    exact aux_scaledBracketBump_nonneg 2 ((aux_hKernelMaxScale_spaced γ i 0 j).1) _
  have hu₁ : 0 ≤ u₁ := by
    dsimp [u₁]
    exact aux_scaledBracketBump_nonneg 2 ((aux_hKernelMaxScale_spaced γ i 1 j).1) _
  have hw₀ : 0 ≤ w₀ := by
    dsimp [w₀]
    exact aux_scaledBracketBump_nonneg 2 ((aux_hKernelMaxScale_spaced γ i 0 j).1) _
  have hw₁ : 0 ≤ w₁ := by
    dsimp [w₁]
    exact aux_scaledBracketBump_nonneg 2 ((aux_hKernelMaxScale_spaced γ i 1 j).1) _
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hr₀ : 0 ≤ r₀ := by
    dsimp [r₀]
    apply mul_nonneg
    · exact add_nonneg
        (inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 0 0 j).1).le)
        (inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1).le)
    · exact mul_nonneg
        (aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 0 0 j).1) _)
        (aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) _)
  have hr₁ : 0 ≤ r₁ := by
    dsimp [r₁]
    apply mul_nonneg
    · exact add_nonneg
        (inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 1 0 j).1).le)
        (inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1).le)
    · exact mul_nonneg
        (aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 1 0 j).1) _)
        (aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) _)
  have hsx : |sMultiplier γ i j v.1| ≤ 2 * C_diagonalSquareRoot 2 * (u₀ + u₁) := by
    simpa [u₀, u₁] using hs j v.1
  have hsy : |sMultiplier γ i j v.2| ≤ 2 * C_diagonalSquareRoot 2 * (w₀ + w₁) := by
    simpa [w₀, w₁] using hs j v.2
  have hdsx : |deriv (sMultiplier γ i j) v.1| ≤
      C_derivativeDiagonalSquareRoot 2 * (a₀ * u₀ + a₁ * u₁) := by
    simpa [a₀, a₁, u₀, u₁] using hds j v.1
  have hdsy : |deriv (sMultiplier γ i j) v.2| ≤
      C_derivativeDiagonalSquareRoot 2 * (b₀ * w₀ + b₁ * w₁) := by
    simpa [b₀, b₁, w₀, w₁] using hds j v.2
  have htensor :
      |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
          sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| ≤
        4 * C_diagonalSquareRoot 2 * C_derivativeDiagonalSquareRoot 2 * S := by
    simpa [S] using
      (aux_abs_tensorDerivative_le_four_products
        aux_C_diagonalSquareRoot_two_nonneg
        aux_C_derivativeDiagonalSquareRoot_two_nonneg ha₀ ha₁ hb₀ hb₁ hu₀ hu₁ hw₀ hw₁
        hsx hsy hdsx hdsy)
  have hgammaPrev :
      |aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v| ≤
        (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₀ := by
    calc
      |aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v| ≤
          2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
            ((γ.scales i 0 (j - 1))⁻¹ + (γ.scales i 1 (j - 1))⁻¹) *
              (scaledBracketBump 2 (γ.scales i 0 (j - 1)) v.1 *
                scaledBracketBump 2 (γ.scales i 1 (j - 1)) v.2) := by
        simpa [gammaGaussian, horientation, W] using
          (aux_abs_diagonalDerivative_twoDimensionalGaussian_zero_le
            (fun r => γ.scales i r (j - 1))
            (fun r => (γ.scales_spaced i r (j - 1)).1) v)
      _ = (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₀ := by
        simp [r₀, aux_hKernelShiftedScale]
        ring
  have hgammaCurr :
      |aux_diagonalDerivative (gammaGaussian γ i j) v| ≤
        (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₁ := by
    calc
      |aux_diagonalDerivative (gammaGaussian γ i j) v| ≤
          2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
            ((γ.scales i 0 j)⁻¹ + (γ.scales i 1 j)⁻¹) *
              (scaledBracketBump 2 (γ.scales i 0 j) v.1 *
                scaledBracketBump 2 (γ.scales i 1 j) v.2) := by
        simpa [gammaGaussian, horientation, W] using
          (aux_abs_diagonalDerivative_twoDimensionalGaussian_zero_le
            (fun r => γ.scales i r j)
            (fun r => (γ.scales_spaced i r j).1) v)
      _ = (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₁ := by
        simp [r₁, aux_hKernelShiftedScale]
        ring
  have hsDiff₀ : DifferentiableAt ℝ (sMultiplier γ i j) v.1 :=
    (aux_sMultiplier_differentiable γ i j).differentiableAt
  have hsDiff₁ : DifferentiableAt ℝ (sMultiplier γ i j) v.2 :=
    (aux_sMultiplier_differentiable γ i j).differentiableAt
  have htensorDiff := aux_tensor_line_differentiable hsDiff₀ hsDiff₁
  have htriangle := aux_abs_hMultiplier_diagonalDerivative_triangle γ i j v
    hsDiff₀ hsDiff₁ htensorDiff
    (aux_gammaGaussian_diagonal_differentiable γ i (j - 1) v)
    (aux_gammaGaussian_diagonal_differentiable γ i j v)
  have hmain :
      |aux_diagonalDerivative (hMultiplier γ i j) v| ≤
        |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
          sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| +
          (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₀ +
          (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₁ := by
    linarith [htriangle, hgammaPrev, hgammaCurr]
  have hG : 0 ≤ 2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (aux_C_gaussianBumpDecay_nonneg 0 2))
      (aux_C_gaussianBumpDecay_nonneg 1 2)
  have hmajorant :
      |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
          sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| +
          (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₀ +
          (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₁ ≤
        (4 * C_diagonalSquareRoot 2 * C_derivativeDiagonalSquareRoot 2 +
          2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * (S + r₀ + r₁) := by
    exact aux_sixTermDerivativeMajorant
      aux_C_diagonalSquareRoot_two_nonneg
      aux_C_derivativeDiagonalSquareRoot_two_nonneg hG hS hr₀ hr₁ htensor
  have hsum :
      ((aux_hKernelGaussianMultiset γ i).map fun q =>
        ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) * aux_kernelBracketProduct q j v).sum =
        S + r₀ + r₁ := by
    simp [aux_hKernelGaussianMultiset, horientation, aux_kernelBracketProduct,
      aux_sequencePairOf, W, a₀, a₁, b₀, b₁, u₀, u₁, w₀, w₁, S, r₀, r₁] <;> ring
  calc
    |aux_diagonalDerivative (hMultiplier γ i j) v| ≤
      (4 * C_diagonalSquareRoot 2 * C_derivativeDiagonalSquareRoot 2 +
        2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * (S + r₀ + r₁) :=
      le_trans hmain hmajorant
    _ = C_hKernelDerivativeEstimateGaussianDomination *
        ((aux_hKernelGaussianMultiset γ i).map fun q =>
          ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) * aux_kernelBracketProduct q j v).sum := by
      rw [hsum]
      unfold C_hKernelDerivativeEstimateGaussianDomination
      ring
/-- This auxiliary theorem carries out the differentiated six-term kernel algebra in the
nontrivial-orientation case. -/
theorem aux_hKernelDerivativeGaussianBound_orientation_one_of_sBounds {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (horientation : γ.orientation i ≠ 0)
    (hs : ∀ (j : ℤ) (x : ℝ), |sMultiplier γ i j x| ≤
      2 * C_diagonalSquareRoot 2 *
        (scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) x +
          scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) x))
    (hds : ∀ (j : ℤ) (x : ℝ), |deriv (sMultiplier γ i j) x| ≤
      C_derivativeDiagonalSquareRoot 2 *
        ((aux_hKernelShiftedScale γ i 0 1 j)⁻¹ *
            scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) x +
          (aux_hKernelShiftedScale γ i 1 1 j)⁻¹ *
            scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) x)) :
    aux_HKernelDerivativeGaussianBound γ i (aux_hKernelGaussianMultiset γ i) := by
  classical
  refine ⟨aux_hKernelGaussianMultiset_valid γ i,
    (aux_hKernelGaussianMultiset_card γ i).le, ?_⟩
  intro v j
  let a₀ : ℝ := (aux_hKernelShiftedScale γ i 0 1 j)⁻¹
  let a₁ : ℝ := (aux_hKernelShiftedScale γ i 1 1 j)⁻¹
  let b₀ : ℝ := (aux_hKernelShiftedScale γ i 0 1 j)⁻¹
  let b₁ : ℝ := (aux_hKernelShiftedScale γ i 1 1 j)⁻¹
  let u₀ : ℝ := scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) v.1
  let u₁ : ℝ := scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) v.1
  let w₀ : ℝ := scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) v.2
  let w₁ : ℝ := scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) v.2
  let S : ℝ :=
    (a₀ + b₀) * u₀ * w₀ + (a₀ + b₁) * u₀ * w₁ +
      (a₁ + b₀) * u₁ * w₀ + (a₁ + b₁) * u₁ * w₁
  let r₀ : ℝ :=
    ((aux_hKernelShiftedScale γ i 0 0 j)⁻¹ +
      (aux_hKernelShiftedScale γ i 0 1 j)⁻¹) *
      (scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 0 j) (W 1 v).1 *
        scaledBracketBump 2 (aux_hKernelShiftedScale γ i 0 1 j) (W 1 v).2)
  let r₁ : ℝ :=
    ((aux_hKernelShiftedScale γ i 1 0 j)⁻¹ +
      (aux_hKernelShiftedScale γ i 1 1 j)⁻¹) *
      (scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 0 j) (W 1 v).1 *
        scaledBracketBump 2 (aux_hKernelShiftedScale γ i 1 1 j) (W 1 v).2)
  have ha₀ : 0 ≤ a₀ := by
    dsimp [a₀]
    exact inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1).le
  have ha₁ : 0 ≤ a₁ := by
    dsimp [a₁]
    exact inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1).le
  have hb₀ : 0 ≤ b₀ := by
    dsimp [b₀]
    exact inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1).le
  have hb₁ : 0 ≤ b₁ := by
    dsimp [b₁]
    exact inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1).le
  have hu₀ : 0 ≤ u₀ := by
    dsimp [u₀]
    exact aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) _
  have hu₁ : 0 ≤ u₁ := by
    dsimp [u₁]
    exact aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) _
  have hw₀ : 0 ≤ w₀ := by
    dsimp [w₀]
    exact aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) _
  have hw₁ : 0 ≤ w₁ := by
    dsimp [w₁]
    exact aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) _
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hr₀ : 0 ≤ r₀ := by
    dsimp [r₀]
    apply mul_nonneg
    · exact add_nonneg
        (inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 0 0 j).1).le)
        (inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1).le)
    · exact mul_nonneg
        (aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 0 0 j).1) _)
        (aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 0 1 j).1) _)
  have hr₁ : 0 ≤ r₁ := by
    dsimp [r₁]
    apply mul_nonneg
    · exact add_nonneg
        (inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 1 0 j).1).le)
        (inv_nonneg.mpr ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1).le)
    · exact mul_nonneg
        (aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 1 0 j).1) _)
        (aux_scaledBracketBump_nonneg 2 ((aux_hKernelShiftedScale_spaced γ i 1 1 j).1) _)
  have hsx : |sMultiplier γ i j v.1| ≤ 2 * C_diagonalSquareRoot 2 * (u₀ + u₁) := by
    simpa [u₀, u₁] using hs j v.1
  have hsy : |sMultiplier γ i j v.2| ≤ 2 * C_diagonalSquareRoot 2 * (w₀ + w₁) := by
    simpa [w₀, w₁] using hs j v.2
  have hdsx : |deriv (sMultiplier γ i j) v.1| ≤
      C_derivativeDiagonalSquareRoot 2 * (a₀ * u₀ + a₁ * u₁) := by
    simpa [a₀, a₁, u₀, u₁] using hds j v.1
  have hdsy : |deriv (sMultiplier γ i j) v.2| ≤
      C_derivativeDiagonalSquareRoot 2 * (b₀ * w₀ + b₁ * w₁) := by
    simpa [b₀, b₁, w₀, w₁] using hds j v.2
  have htensor :
      |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
          sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| ≤
        4 * C_diagonalSquareRoot 2 * C_derivativeDiagonalSquareRoot 2 * S := by
    simpa [S] using
      (aux_abs_tensorDerivative_le_four_products
        aux_C_diagonalSquareRoot_two_nonneg
        aux_C_derivativeDiagonalSquareRoot_two_nonneg ha₀ ha₁ hb₀ hb₁ hu₀ hu₁ hw₀ hw₁
        hsx hsy hdsx hdsy)
  have hOne : γ.orientation i = 1 := Fin.eq_one_of_ne_zero _ horientation
  have hgammaPrev :
      |aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v| ≤
        (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₀ := by
    calc
      |aux_diagonalDerivative (gammaGaussian γ i (j - 1)) v| ≤
          2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
            ((γ.scales i 0 (j - 1))⁻¹ + (γ.scales i 1 (j - 1))⁻¹) *
              (scaledBracketBump 2 (γ.scales i 0 (j - 1)) (W 1 v).1 *
                scaledBracketBump 2 (γ.scales i 1 (j - 1)) (W 1 v).2) := by
        simpa [gammaGaussian, hOne, W] using
          (aux_abs_diagonalDerivative_twoDimensionalGaussian_one_le
            (fun r => γ.scales i r (j - 1))
            (fun r => (γ.scales_spaced i r (j - 1)).1) v)
      _ = (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₀ := by
        simp [r₀, aux_hKernelShiftedScale]
        ring
  have hgammaCurr :
      |aux_diagonalDerivative (gammaGaussian γ i j) v| ≤
        (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₁ := by
    calc
      |aux_diagonalDerivative (gammaGaussian γ i j) v| ≤
          2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
            ((γ.scales i 0 j)⁻¹ + (γ.scales i 1 j)⁻¹) *
              (scaledBracketBump 2 (γ.scales i 0 j) (W 1 v).1 *
                scaledBracketBump 2 (γ.scales i 1 j) (W 1 v).2) := by
        simpa [gammaGaussian, hOne, W] using
          (aux_abs_diagonalDerivative_twoDimensionalGaussian_one_le
            (fun r => γ.scales i r j)
            (fun r => (γ.scales_spaced i r j).1) v)
      _ = (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₁ := by
        simp [r₁, aux_hKernelShiftedScale]
        ring
  have hsDiff₀ : DifferentiableAt ℝ (sMultiplier γ i j) v.1 :=
    (aux_sMultiplier_differentiable γ i j).differentiableAt
  have hsDiff₁ : DifferentiableAt ℝ (sMultiplier γ i j) v.2 :=
    (aux_sMultiplier_differentiable γ i j).differentiableAt
  have htensorDiff := aux_tensor_line_differentiable hsDiff₀ hsDiff₁
  have htriangle := aux_abs_hMultiplier_diagonalDerivative_triangle γ i j v
    hsDiff₀ hsDiff₁ htensorDiff
    (aux_gammaGaussian_diagonal_differentiable γ i (j - 1) v)
    (aux_gammaGaussian_diagonal_differentiable γ i j v)
  have hmain :
      |aux_diagonalDerivative (hMultiplier γ i j) v| ≤
        |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
          sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| +
          (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₀ +
          (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₁ := by
    linarith [htriangle, hgammaPrev, hgammaCurr]
  have hG : 0 ≤ 2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (aux_C_gaussianBumpDecay_nonneg 0 2))
      (aux_C_gaussianBumpDecay_nonneg 1 2)
  have hmajorant :
      |deriv (sMultiplier γ i j) v.1 * sMultiplier γ i j v.2 +
          sMultiplier γ i j v.1 * deriv (sMultiplier γ i j) v.2| +
          (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₀ +
          (2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * r₁ ≤
        (4 * C_diagonalSquareRoot 2 * C_derivativeDiagonalSquareRoot 2 +
          2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * (S + r₀ + r₁) := by
    exact aux_sixTermDerivativeMajorant
      aux_C_diagonalSquareRoot_two_nonneg
      aux_C_derivativeDiagonalSquareRoot_two_nonneg hG hS hr₀ hr₁ htensor
  have hsum :
      ((aux_hKernelGaussianMultiset γ i).map fun q =>
        ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) * aux_kernelBracketProduct q j v).sum =
        S + r₀ + r₁ := by
    simp [aux_hKernelGaussianMultiset, horientation, aux_kernelBracketProduct,
      aux_sequencePairOf, W, a₀, a₁, b₀, b₁, u₀, u₁, w₀, w₁, S, r₀, r₁] <;> ring
  calc
    |aux_diagonalDerivative (hMultiplier γ i j) v| ≤
      (4 * C_diagonalSquareRoot 2 * C_derivativeDiagonalSquareRoot 2 +
        2 * C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2) * (S + r₀ + r₁) :=
      le_trans hmain hmajorant
    _ = C_hKernelDerivativeEstimateGaussianDomination *
        ((aux_hKernelGaussianMultiset γ i).map fun q =>
          ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) * aux_kernelBracketProduct q j v).sum := by
      rw [hsum]
      unfold C_hKernelDerivativeEstimateGaussianDomination
      ring

/-- Source label `\ref{H kernel derivative estimate Gaussian domination}`. -/
theorem hKernelDerivativeEstimateGaussianDomination {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) :
    ∃ P : Multiset (SequencePair × Fin 2), aux_HKernelDerivativeGaussianBound γ i P := by
  refine ⟨aux_hKernelGaussianMultiset γ i, ?_⟩
  by_cases h : γ.orientation i = 0
  · apply aux_hKernelDerivativeGaussianBound_orientation_zero_of_sBounds γ i h
    · intro j x
      apply aux_sMultiplier_bound_orientation_zero_of_diagonal γ i j h
      intro y
      rw [aux_sMultiplier_eq_diagonalSquareRoot]
      have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
      apply diagonalSquareRoot_bound 2 (by norm_num)
      · linarith [hsp.1]
      · convert hsp.2 using 1 <;> ring
    · intro j x
      apply aux_deriv_sMultiplier_bound_orientation_zero_of_diagonal γ i j h
      intro y
      rw [aux_deriv_sMultiplier_eq_diagonalSquareRoot]
      have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
      apply derivativeDiagonalSquareRoot_bound 2 (by norm_num)
      · linarith [hsp.1]
      · convert hsp.2 using 1 <;> ring
  · apply aux_hKernelDerivativeGaussianBound_orientation_one_of_sBounds γ i h
    · intro j x
      apply aux_sMultiplier_bound_orientation_one_of_diagonal γ i j h
      intro y
      rw [aux_sMultiplier_eq_diagonalSquareRoot]
      have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
      apply diagonalSquareRoot_bound 2 (by norm_num)
      · linarith [hsp.1]
      · convert hsp.2 using 1 <;> ring
    · intro j x
      apply aux_deriv_sMultiplier_bound_orientation_one_of_diagonal γ i j h
      intro y
      rw [aux_deriv_sMultiplier_eq_diagonalSquareRoot]
      have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
      apply derivativeDiagonalSquareRoot_bound 2 (by norm_num)
      · linarith [hsp.1]
      · convert hsp.2 using 1 <;> ring

/-- Source label `\ref{constant H kernel derivative estimate Gaussian domination}`. -/
theorem constantHKernelDerivativeEstimateGaussianDomination :
    C_hKernelDerivativeEstimateGaussianDomination < 2 ^ 30 := by
  have hgaussian0 : C_gaussianBumpDecay 0 2 = 12 := by
    norm_num [C_gaussianBumpDecay]
  have hgaussian1 : C_gaussianBumpDecay 1 2 = 24 * Real.sqrt 19 := by
    norm_num [C_gaussianBumpDecay, Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [← Real.sqrt_eq_rpow]
    rw [show (76 : ℝ) = 4 * 19 by norm_num, Real.sqrt_mul (by norm_num)]
    have hsqrt19 : (19 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 19 := by
      rw [← Real.sqrt_eq_rpow]
    rw [hsqrt19]
    norm_num
    ring
  rw [C_hKernelDerivativeEstimateGaussianDomination,
    aux_constantDiagonalSquareRoot_two,
    aux_constantDerivativeDiagonalSquareRoot_two, hgaussian0, hgaussian1]
  have hsqrt2 : Real.sqrt (2 : ℝ) < 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt19 : Real.sqrt (19 : ℝ) < 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19),
      Real.sqrt_nonneg (19 : ℝ)]
  have hproduct : Real.sqrt (2 : ℝ) * Real.sqrt 19 < 15 / 2 := by
    calc
      Real.sqrt (2 : ℝ) * Real.sqrt 19 < (3 / 2) * Real.sqrt 19 :=
        mul_lt_mul_of_pos_right hsqrt2 (Real.sqrt_pos.2 (by norm_num))
      _ < (3 / 2) * 5 := mul_lt_mul_of_pos_left hsqrt19 (by norm_num)
      _ = 15 / 2 := by norm_num
  nlinarith

private theorem aux_gaussDominationCase1_lt_two_pow_117 :
    C_gaussDominationCase1 < (2 : ℝ) ^ (117 : ℕ) := by
  have hexpPi : Real.exp Real.pi < 55 := by
    calc
      Real.exp Real.pi < Real.exp 4 := (Real.exp_lt_exp).mpr Real.pi_lt_four
      _ = (Real.exp 1) ^ 4 := by
        rw [← Real.exp_nat_mul]
        ring_nf
      _ < (2.7182818286 : ℝ) ^ 4 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos _).le (by norm_num)
      _ < 55 := by norm_num
  have hexp : Real.exp (2 * Real.pi) < 3025 := by
    calc
      Real.exp (2 * Real.pi) = (Real.exp Real.pi) ^ 2 := by
        rw [← Real.exp_nat_mul]
        ring_nf
      _ < (55 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ hexpPi (Real.exp_pos _).le (by norm_num)
      _ = 3025 := by norm_num
  have hstd : C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) := by
    norm_num [C_standardBumpPropertiesTilde]
  have hmean : C_meanFourScaleGaussianKernel 2 < 20397963318112 :=
    aux_C_meanFourScaleGaussianKernel_two_lt_value
  have hmean0 : 0 ≤ C_meanFourScaleGaussianKernel 2 := by
    have hK : 0 ≤ C_meanValueBumpEstimate 2 := by
      unfold C_meanValueBumpEstimate
      positivity
    have hM : 0 ≤ aux_maxUpTo C_gaussianBumpEstimate 2 :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans
        (aux_le_maxUpTo C_gaussianBumpEstimate (Nat.zero_le _))
    have hT : 0 ≤ aux_maxUpTo
        (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) 2 := by
      have hzero : 0 ≤ (2 : ℝ) ^ 0 * C_secondGaussianEstimate 0 := by
        simpa using aux_C_secondGaussianEstimate_nonneg 0
      exact hzero.trans (aux_le_maxUpTo
        (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) (Nat.zero_le _))
    unfold C_meanFourScaleGaussianKernel
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hK) hM)
      (mul_nonneg (mul_nonneg (by norm_num) hK) hT)
  have hH_eq : C_hKernelEstimateGaussianDomination = 51 ^ 2 * 2 ^ 15 + 12 ^ 2 :=
    constantHKernelEstimateGaussianDomination.1
  have hH0 : 0 ≤ C_hKernelEstimateGaussianDomination :=
    aux_C_hKernelEstimateGaussianDomination_nonneg
  have htwoeq : C_twoBumpEstimate (3 / 2) (3 / 2) = 12 * Real.sqrt 2 := by
    norm_num [C_twoBumpEstimate, Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.sqrt_eq_rpow]
    norm_num
    ring
  have hsqrt2 : Real.sqrt (2 : ℝ) < 17 / 12 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have htwo : C_twoBumpEstimate (3 / 2) (3 / 2) < 17 := by
    rw [htwoeq]
    nlinarith
  have hbump : C_bumpTriangle (-(1 / 2)) (1 / 2) (3 / 2) (3 / 2) = 1 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde]
  have hmax : max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
      (4 * C_bumpTriangle (-(1 / 2)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2)) < 68 := by
    rw [hbump]
    apply max_lt
    · nlinarith
    · nlinarith
  have hmax0 : 0 ≤ max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
      (4 * C_bumpTriangle (-(1 / 2)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2)) := by
    rw [hbump, htwoeq]
    positivity
  rw [C_gaussDominationCase1, hstd, hH_eq]
  calc
    2 * ((2 : ℝ) ^ (7 : ℕ) * Real.pi * Real.exp (2 * Real.pi) * (2 : ℝ) ^ (18 : ℕ) *
        C_meanFourScaleGaussianKernel 2 * (51 ^ 2 * 2 ^ 15 + 12 ^ 2) *
        max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
          (4 * C_bumpTriangle (-(1 / 2)) (1 / 2) (3 / 2) (3 / 2) *
            C_twoBumpEstimate (3 / 2) (3 / 2))) <
      2 * ((2 : ℝ) ^ (7 : ℕ) * 4 * 3025 * (2 : ℝ) ^ (18 : ℕ) *
        20397963318112 * (51 ^ 2 * 2 ^ 15 + 12 ^ 2) * 68) := by
      gcongr
      exact Real.pi_lt_four
    _ < (2 : ℝ) ^ (117 : ℕ) := by norm_num

private theorem aux_gaussDominationCase2_lt_two_pow_153 :
    C_gaussDominationCase2 < (2 : ℝ) ^ (153 : ℕ) := by
  have hexp : Real.exp (2 * Real.pi) < 6656 := by
    calc
      Real.exp (2 * Real.pi) = (Real.exp Real.pi) ^ 2 := by
        rw [← Real.exp_nat_mul]
        ring_nf
      _ < (81 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ aux_exp_pi_lt_81 (Real.exp_pos _).le (by norm_num)
      _ = 6561 := by norm_num
      _ < 6656 := by norm_num
  have hstd : C_standardBumpPropertiesTilde 0 3 = (2 : ℝ) ^ (33 : ℕ) := by
    norm_num [C_standardBumpPropertiesTilde]
  have hfour : C_fourScaleGaussianKernel 3 < 6136564156458101504 :=
    aux_C_fourScaleGaussianKernel_three_lt_value
  have hfour0 : 0 ≤ C_fourScaleGaussianKernel 3 := by
    have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
    have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) :=
      (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
    unfold C_fourScaleGaussianKernel C_smoothDecay2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
      (mul_nonneg (by positivity) hsecond)
  have hderiv : C_hKernelDerivativeEstimateGaussianDomination < (2 : ℝ) ^ (30 : ℕ) :=
    constantHKernelDerivativeEstimateGaussianDomination
  have hderiv0 : 0 ≤ C_hKernelDerivativeEstimateGaussianDomination :=
    aux_C_hKernelDerivativeEstimateGaussianDomination_nonneg
  have htriangle : C_bumpTriangle 1 1 2 2 = 4 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  have htwo : C_twoBumpEstimate 2 2 = 16 := aux_twoBumpEstimate_two_two
  rw [C_gaussDominationCase2, hstd, htriangle, htwo]
  calc
    3 * (2 : ℝ) ^ (7 : ℕ) * Real.exp (2 * Real.pi) * (2 : ℝ) ^ (33 : ℕ) *
        C_fourScaleGaussianKernel 3 * C_hKernelDerivativeEstimateGaussianDomination * 4 * 16 <
      3 * (2 : ℝ) ^ (7 : ℕ) * 6656 * (2 : ℝ) ^ (33 : ℕ) *
        6136564156458101504 * (2 : ℝ) ^ (30 : ℕ) * 4 * 16 := by
      gcongr
    _ < (2 : ℝ) ^ (153 : ℕ) := by norm_num

private theorem aux_gaussDominationCase3_lt_two_pow_110 :
    C_gaussDominationCase3 < (2 : ℝ) ^ (110 : ℕ) := by
  have hexp : Real.exp (2 * Real.pi) < 6656 := by
    calc
      Real.exp (2 * Real.pi) = (Real.exp Real.pi) ^ 2 := by
        rw [← Real.exp_nat_mul]
        ring_nf
      _ < (81 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ aux_exp_pi_lt_81 (Real.exp_pos _).le (by norm_num)
      _ = 6561 := by norm_num
      _ < 6656 := by norm_num
  have hstd : C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) := by
    norm_num [C_standardBumpPropertiesTilde]
  have hfour : C_fourScaleGaussianKernel 2 < 637436354528 :=
    aux_C_fourScaleGaussianKernel_two_lt_value
  have hfour0 : 0 ≤ C_fourScaleGaussianKernel 2 := by
    have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 2) :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
    have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 2) :=
      (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
    unfold C_fourScaleGaussianKernel C_smoothDecay2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
      (mul_nonneg (by positivity) hsecond)
  have hH : C_hKernelEstimateGaussianDomination < (2 : ℝ) ^ (27 : ℕ) :=
    constantHKernelEstimateGaussianDomination.2
  have hH0 : 0 ≤ C_hKernelEstimateGaussianDomination :=
    aux_C_hKernelEstimateGaussianDomination_nonneg
  have htriangle : C_bumpTriangle 1 1 2 2 = 4 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  have htwo : C_twoBumpEstimate 2 2 = 16 := aux_twoBumpEstimate_two_two
  rw [C_gaussDominationCase3, hstd, htriangle, htwo]
  calc
    (2 : ℝ) ^ (7 : ℕ) * Real.exp (2 * Real.pi) * (2 : ℝ) ^ (18 : ℕ) *
        C_fourScaleGaussianKernel 2 * C_hKernelEstimateGaussianDomination * 4 * 16 <
      (2 : ℝ) ^ (7 : ℕ) * 6656 * (2 : ℝ) ^ (18 : ℕ) *
        637436354528 * (2 : ℝ) ^ (27 : ℕ) * 4 * 16 := by
      gcongr
    _ < (2 : ℝ) ^ (110 : ℕ) := by norm_num

/-- The three case constants are all bounded by the common domination constant. -/
private theorem aux_gaussDominationCaseConstants_le_combined :
    max C_gaussDominationCase1 (max C_gaussDominationCase2 C_gaussDominationCase3) ≤
      C_gaussianDominationCombined := by
  unfold C_gaussianDominationCombined
  apply max_le
  · exact aux_gaussDominationCase1_lt_two_pow_117.le.trans
      (pow_le_pow_right₀ (by norm_num) (by norm_num))
  · apply max_le
    · exact aux_gaussDominationCase2_lt_two_pow_153.le
    · exact aux_gaussDominationCase3_lt_two_pow_110.le.trans
        (pow_le_pow_right₀ (by norm_num) (by norm_num))

/-- Source label `\ref{Gauss domination constant}`. -/
theorem gaussDominationConstant :
    C_gaussDominationCase1 < (2 : ℝ) ^ (117 : ℕ) ∧
      C_gaussDominationCase2 < (2 : ℝ) ^ (153 : ℕ) ∧
      C_gaussDominationCase3 < (2 : ℝ) ^ (110 : ℕ) ∧
      max C_gaussDominationCase1
          (max C_gaussDominationCase2 C_gaussDominationCase3) ≤
        C_gaussianDominationCombined := by
  exact ⟨aux_gaussDominationCase1_lt_two_pow_117,
    aux_gaussDominationCase2_lt_two_pow_153,
    aux_gaussDominationCase3_lt_two_pow_110,
    aux_gaussDominationCaseConstants_le_combined⟩

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

/-- A Gaussian-domination witness remains valid after increasing its majorant constant. -/
theorem aux_GaussianDominationConclusion_mono {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (i : Fin γ.k)
    (ι : MultiplierIndex γ) {C C' : ℝ} (hCC' : C ≤ C') :
    aux_GaussianDominationConclusion γ hkn i ι C →
      aux_GaussianDominationConclusion γ hkn i ι C' := by
  rintro ⟨w⟩
  refine ⟨{
    B := w.B
    card_le := w.card_le
    orientation := w.orientation
    scales := w.scales
    scales_in_A := w.scales_in_A
    distance_bound := w.distance_bound
    estimate := ?_
    series_summable := w.series_summable
    series_integrable := w.series_integrable
  }⟩
  intro j v
  have hseries : 0 ≤ ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
      ∑ b ∈ w.B, aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j v := by
    apply tsum_nonneg
    intro m
    apply mul_nonneg (aux_gaussianDominationWeight_nonneg m)
    apply Finset.sum_nonneg
    intro b hb
    exact aux_dominatingGaussianTerm_nonneg (w.scales b m)
      (w.scales_in_A b hb m) (w.orientation b) j v
  have hfactor : 0 ≤ Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
      ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
        ∑ b ∈ w.B, aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j v :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) hseries
  calc
    |nMultiplier γ hkn ι i j v| ≤
        C * Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
            ∑ b ∈ w.B, aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j v :=
      w.estimate j v
    _ = C * (Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
            ∑ b ∈ w.B, aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j v) := by
      ring
    _ ≤ C' * (Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
            ∑ b ∈ w.B, aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j v) :=
      mul_le_mul_of_nonneg_right hCC' hfactor
    _ = C' * Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
            ∑ b ∈ w.B, aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j v := by
      ring

/-- The multiplier-index definition has exactly the three analytic cases used in the
Gaussian-domination argument. -/
theorem aux_multiplierIndex_cases {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) :
    (0 < ι.1.1 ∧ ι.1.2 = 0) ∨ (ι.1.1 < 0 ∧ ι.1.2 = 0) ∨
      (ι.1.1 = 0 ∧ ι.1.2.natAbs ≤ geometricDelta γ) := by
  rcases ι.property with hhorizontal | hvertical
  · rcases hhorizontal with ⟨hne, hsecond⟩
    rcases lt_trichotomy ι.1.1 0 with hneg | hzero | hpos
    · exact Or.inr (Or.inl ⟨hneg, hsecond⟩)
    · exact False.elim (hne hzero)
    · exact Or.inl ⟨hpos, hsecond⟩
  · exact Or.inr (Or.inr hvertical)

/-- Combines the three multiplier-index cases once each has been established at the
common Gaussian-domination constant. -/
private theorem aux_gaussianDominationCombined_of_cases {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (i : Fin γ.k)
    (hpositive : ∀ ι : MultiplierIndex γ,
      0 < ι.1.1 → ι.1.2 = 0 →
        aux_GaussianDominationConclusion γ hkn i ι C_gaussianDominationCombined)
    (hnegative : ∀ ι : MultiplierIndex γ,
      ι.1.1 < 0 → ι.1.2 = 0 →
        aux_GaussianDominationConclusion γ hkn i ι C_gaussianDominationCombined)
    (hzero : ∀ ι : MultiplierIndex γ,
      ι.1.1 = 0 → ι.1.2.natAbs ≤ geometricDelta γ →
        aux_GaussianDominationConclusion γ hkn i ι C_gaussianDominationCombined) :
    ∀ ι : MultiplierIndex γ,
      aux_GaussianDominationConclusion γ hkn i ι C_gaussianDominationCombined := by
  intro ι
  rcases aux_multiplierIndex_cases γ ι with hι | hι | hι
  · exact hpositive ι hι.1 hι.2
  · exact hnegative ι hι.1 hι.2
  · exact hzero ι hι.1 hι.2

/-- Diagonal cancellation converts a convolution into a difference of its one-dimensional
kernel. This is the pointwise bridge used in the Gaussian-domination cases. -/
theorem aux_diagonal_convolution_eq_difference
    {F : RealPlane → ℝ} (hF : MemW0 F)
    (hzero : ∀ x : ℝ, (∫ q : ℝ, F (x, q)) = 0)
    {rho : ℝ → ℝ} (x y : ℝ)
    (hA : Integrable (fun q : ℝ => F (x, q) * rho (y - q))) :
    (∫ q : ℝ, F (x, q) * rho (y - q)) =
      ∫ q : ℝ, F (x, q) * (rho (y - q) - rho y) := by
  have hFslice_mem : MemW0 (fun q : ℝ => F (x, q)) :=
    hF.aux_memW0_slice_of_addHaar x
  have hFslice : Integrable (fun q : ℝ => F (x, q)) :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hFslice_mem
  have hB : Integrable (fun q : ℝ => F (x, q) * rho y) := hFslice.mul_const _
  have hBzero : (∫ q : ℝ, F (x, q) * rho y) = 0 := by
    rw [integral_mul_const, hzero x, zero_mul]
  calc
    (∫ q : ℝ, F (x, q) * rho (y - q)) =
        (∫ q : ℝ, F (x, q) * rho (y - q)) -
          ∫ q : ℝ, F (x, q) * rho y := by rw [hBzero, sub_zero]
    _ = ∫ q : ℝ, F (x, q) * rho (y - q) - F (x, q) * rho y :=
      (integral_sub hA hB).symm
    _ = ∫ q : ℝ, F (x, q) * (rho (y - q) - rho y) := by
      apply integral_congr_ae
      filter_upwards [] with q
      ring

/-- The positive horizontal band of the four-scale N-kernel has the mean-difference estimate
needed for Gaussian domination. -/
theorem aux_nMultiplierRho_positive_difference_bound {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 ≠ 0) (hpositive : 0 < ι.1.1)
    (x y : ℝ) :
    |nMultiplierRho γ hkn ι i j (x + y) - nMultiplierRho γ hkn ι i j x| ≤
      C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2 *
        min 1 (2 * Real.pi *
          (((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ)))⁻¹) * |y|) *
          (scaledBracketBump 2
            ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ))) (x + y) +
            scaledBracketBump 2
              ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ))) x) := by
  let r : ℤ := j + (geometricDelta γ : ℤ)
  let h : ℤ := ι.1.1
  let a : ℤ → ℝ := γ.scales i 1
  let muMinus : ℝ := (2 : ℝ) ^ h * a (r - 1)
  let muPlus : ℝ := (2 : ℝ) ^ h * a r
  let lamMinus : ℝ := (2 : ℝ) ^ (h - 1) * a r
  let lamPlus : ℝ := (2 : ℝ) ^ h * a r
  have hnu : nMultiplierFourScaleExponent γ ∈ Set.Ico (-1 : ℝ) 0 :=
    nMultiplierFourScaleExponent_memIco γ
  have hpow : (2 : ℝ) ^ h = 2 * (2 : ℝ) ^ (h - 1) := by
    rw [show h = (h - 1) + 1 by omega, zpow_add₀ (by norm_num), zpow_one]
    ring
  have hmuMinus : 0 < muMinus := by
    dsimp [muMinus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hmuPlus : 0 < muPlus := by
    dsimp [muPlus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hlamMinus : 0 < lamMinus := by
    dsimp [lamMinus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hlamPlus : 0 < lamPlus := by
    dsimp [lamPlus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hscales : 2 * muMinus ≤ 2 * lamMinus ∧ 2 * lamMinus ≤ lamPlus ∧ lamPlus ≤ muPlus := by
    refine ⟨?_, ?_, le_rfl⟩
    · dsimp [muMinus, lamMinus, a]
      calc
        2 * ((2 : ℝ) ^ h * γ.scales i 1 (r - 1)) =
            (2 * (2 : ℝ) ^ (h - 1)) * (2 * γ.scales i 1 (r - 1)) := by
              rw [hpow]
              ring
        _ ≤ (2 * (2 : ℝ) ^ (h - 1)) * γ.scales i 1 r :=
          mul_le_mul_of_nonneg_left (by
            simpa only [sub_add_cancel] using (γ.scales_spaced i 1 (r - 1)).2) (by positivity)
        _ = 2 * ((2 : ℝ) ^ (h - 1) * γ.scales i 1 r) := by ring
    · dsimp [lamMinus, lamPlus]
      apply le_of_eq
      calc
        2 * ((2 : ℝ) ^ (h - 1) * γ.scales i 1 r) =
            (2 * (2 : ℝ) ^ (h - 1)) * γ.scales i 1 r := by ring
        _ = (2 : ℝ) ^ h * γ.scales i 1 r := by rw [hpow]
  have hlamEq : lamPlus = 2 * lamMinus := by
    dsimp [lamPlus, lamMinus]
    rw [hpow]
    ring
  have hmean := meanFourScaleGaussianKernel ((2 : ℝ) ^ 18) 2 (by norm_num)
    (fun z : ℝ => (standardBump z : ℂ))
    (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
    aux_standardBumpComplex_memW0 rfl (by positivity)
    (closure_minimal (standardBumpProperties_fourierShape).2.1 isClosed_Icc)
    (standardBumpProperties_fourierShape).2.2
    (aux_standardBumpComplex_fourier_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))
    (by
      intro m hm z
      interval_cases m
      · exact (aux_standardBump_fourier_iteratedDeriv_le_zero z).trans (by norm_num)
      · exact (aux_standardBump_fourier_iteratedDeriv_le_one z).trans (by norm_num)
      · exact aux_standardBump_fourier_iteratedDeriv_le_two z)
    muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ)
    hmuMinus hmuPlus hlamMinus hlamPlus hscales hlamEq hnu
  have hcomplex := hmean.2 x y
  have hreal :
      |(fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) (x + y)).re -
        (fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x).re| ≤
        (2 : ℝ) ^ 18 * C_meanFourScaleGaussianKernel 2 *
          min 1 (2 * Real.pi * lamPlus⁻¹ * |y|) *
            (scaledBracketBump 2 lamPlus (x + y) + scaledBracketBump 2 lamPlus x) := by
    calc
      |(fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) (x + y)).re -
        (fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x).re| =
          |(fourScaleGaussianRho
            (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
            muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) (x + y) -
            fourScaleGaussianRho
              (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
              muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x).re| := by
          simp
      _ ≤ ‖fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) (x + y) -
          fourScaleGaussianRho
            (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
            muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x‖ :=
        Complex.abs_re_le_norm _
      _ ≤ _ := hcomplex
  have hC : (2 : ℝ) ^ 18 = C_standardBumpPropertiesTilde 0 2 := by
    norm_num [C_standardBumpPropertiesTilde]
  rw [← hC]
  simpa [r, h, a, muMinus, muPlus, lamMinus, lamPlus,
    nMultiplierRho, nMultiplierRhoComplex, hzero, hpositive]
    using hreal


/-! ## Gauss domination case 1 -/

private theorem aux_caseOne_move_twoPi_out {A lambda y B : ℝ}
    (hA : 0 ≤ A) (hlambda : 0 < lambda) (hB : 0 ≤ B) :
    A * min 1 (2 * Real.pi * lambda⁻¹ * |y|) * B ≤
      (2 * Real.pi * A) * min 1 (lambda⁻¹ * |y|) * B := by
  have hmin : min 1 (2 * Real.pi * (lambda⁻¹ * |y|)) ≤
      2 * Real.pi * min 1 (lambda⁻¹ * |y|) := by
    exact (by
      have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      by_cases h : 1 ≤ lambda⁻¹ * |y|
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by nlinarith)
      · have h' : lambda⁻¹ * |y| ≤ 1 := le_of_not_ge h
        rw [min_eq_right h']
        exact min_le_right _ _)
  calc
    A * min 1 (2 * Real.pi * lambda⁻¹ * |y|) * B =
        A * min 1 (2 * Real.pi * (lambda⁻¹ * |y|)) * B := by ring
    _ ≤ A * (2 * Real.pi * min 1 (lambda⁻¹ * |y|)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hA) hB
    _ = (2 * Real.pi * A) * min 1 (lambda⁻¹ * |y|) * B := by ring

/-- Scratch: any scale in the H-kernel distance ball is smaller than a positive-band
N scale by the required factor. -/
private theorem aux_caseOne_distanceBall_scale_ratio_le {a b : ℤ → ℝ} (ha : SpacedSequence a)
    {d : ℕ} (hb : b ∈ sequenceDistanceBall a (d : WithTop ℕ))
    (h j : ℤ) :
    b j / ((2 : ℝ) ^ h * a (j + (d : ℤ))) ≤ (2 : ℝ) ^ (-h) := by
  rcases hb with ⟨_, hdist⟩
  have hwithin : WithinSequenceDistance a b d :=
    aux_withinSequenceDistance_of_sequenceDistance_le ha hdist
  have hbj : b j ≤ a (j + (d : ℤ)) := by
    simpa using (hwithin j).2
  have hden : 0 < (2 : ℝ) ^ h * a (j + (d : ℤ)) :=
    mul_pos (zpow_pos (by norm_num) _) (ha _).1
  apply (div_le_iff₀ hden).2
  calc
    b j ≤ a (j + (d : ℤ)) := hbj
    _ = ((2 : ℝ) ^ (-h) * (2 : ℝ) ^ h) * a (j + (d : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero, one_mul]
    _ = (2 : ℝ) ^ (-h) * ((2 : ℝ) ^ h * a (j + (d : ℤ))) := by ring

/-- Scratch: multiplying a second-order bracket bump by the square-root loss converts it
exactly to the real exponent `3/2` used by the two-bump estimate. -/
private theorem aux_caseOne_scaledBracketBump_two_sqrt_eq_threeHalves (t x : ℝ) (ht : 0 < t) :
    Real.rpow (1 + t⁻¹ * |x|) (1 / 2 : ℝ) * scaledBracketBump 2 t x =
      scaledBracketBumpReal (3 / 2 : ℝ) t x := by
  let z : ℝ := 1 + t⁻¹ * |x|
  have hz : 0 < z := by
    dsimp [z]
    positivity
  have habs : |t⁻¹ * x| = t⁻¹ * |x| := by
    rw [abs_mul, abs_inv, abs_of_pos ht]
  have hnegTwo : z⁻¹ ^ (2 : ℕ) = Real.rpow z (-2 : ℝ) := by
    calc
      z⁻¹ ^ (2 : ℕ) = (z ^ (2 : ℕ))⁻¹ := by rw [inv_pow]
      _ = (Real.rpow z (2 : ℝ))⁻¹ := by
        congr 1
        exact (Real.rpow_natCast z 2).symm
      _ = Real.rpow z (-2 : ℝ) := (Real.rpow_neg hz.le 2).symm
  unfold scaledBracketBump scaledBracketBumpReal
  rw [habs]
  change Real.rpow z (1 / 2 : ℝ) * (t⁻¹ * z⁻¹ ^ (2 : ℕ)) =
    t⁻¹ * Real.rpow z (-(3 / 2 : ℝ))
  rw [hnegTwo]
  calc
    Real.rpow z (1 / 2 : ℝ) * (t⁻¹ * Real.rpow z (-2 : ℝ)) =
        t⁻¹ * (Real.rpow z (1 / 2 : ℝ) * Real.rpow z (-2 : ℝ)) := by ring
    _ = t⁻¹ * Real.rpow z ((1 / 2 : ℝ) + (-2 : ℝ)) := by
      have hsum : Real.rpow z ((1 / 2 : ℝ) + (-2 : ℝ)) =
          Real.rpow z (1 / 2 : ℝ) * Real.rpow z (-2 : ℝ) :=
        Real.rpow_add hz _ _
      exact congrArg (fun r : ℝ => t⁻¹ * r) hsum.symm
    _ = t⁻¹ * Real.rpow z (-(3 / 2 : ℝ)) := by ring_nf

private theorem aux_caseOne_min_scale_half_le {t lam : ℝ} {h : ℕ} (ht : 0 < t) (hlam : 0 < lam)
    (hscale : t / lam ≤ Real.rpow 2 (-(h : ℝ))) (p : ℝ) :
    min 1 (lam⁻¹ * |p|) ≤ Real.rpow 2 (-((h : ℝ) / 2)) *
      Real.sqrt (1 + t⁻¹ * |p|) := by
  let a : ℝ := lam⁻¹ * |p|
  let b : ℝ := t⁻¹ * |p|
  let c : ℝ := Real.rpow 2 (-(h : ℝ))
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    exact Real.rpow_nonneg (by norm_num) _
  have hab : a ≤ c * b := by
    have hid : a = (t / lam) * b := by
      dsimp [a, b]
      field_simp [ne_of_gt ht, ne_of_gt hlam]
    rw [hid]
    exact mul_le_mul_of_nonneg_right hscale hb
  have hmin : min 1 a ≤ Real.sqrt a := by
    by_cases haone : a ≤ 1
    · rw [min_eq_right haone]
      exact (Real.le_sqrt_self_iff).2 haone
    · rw [min_eq_left (le_of_not_ge haone)]
      exact (Real.one_le_sqrt).2 (le_of_not_ge haone)
  have hsqrt : Real.sqrt a ≤ Real.sqrt c * Real.sqrt (1 + b) := by
    calc
      Real.sqrt a ≤ Real.sqrt (c * b) := Real.sqrt_le_sqrt hab
      _ = Real.sqrt c * Real.sqrt b := Real.sqrt_mul hc _
      _ ≤ Real.sqrt c * Real.sqrt (1 + b) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  have hroot : Real.sqrt c = Real.rpow 2 (-((h : ℝ) / 2)) := by
    dsimp [c]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simpa [a, b, hroot] using hmin.trans hsqrt

/-- A two-bump integral with the larger of the two scales chosen as output scale. -/
private theorem aux_caseOne_twoBumpIntegral_max (x₀ x₁ t₀ t₁ : ℝ)
    (ht₀ : 0 < t₀) (ht₁ : 0 < t₁) :
    (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t₀ (x₀ - p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₁ (x₁ - p)) ≤
      C_twoBumpEstimate (3 / 2) (3 / 2) *
        scaledBracketBumpReal (3 / 2 : ℝ) (max t₀ t₁) (x₀ - x₁) := by
  have hnonneg (p : ℝ) : 0 ≤
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ (x₀ - p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₁ (x₁ - p) :=
    mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ ht₀)
      (aux_scaledBracketBumpReal_nonneg _ _ _ ht₁)
  rw [← abs_of_nonneg (integral_nonneg hnonneg)]
  by_cases h : t₀ ≤ t₁
  · have htwo := twoBumpEstimate x₁ x₀ t₁ t₀ (3 / 2 : ℝ) (3 / 2 : ℝ)
      ht₁ ht₀ h (by norm_num) (by norm_num)
    calc
      |∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t₀ (x₀ - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₁ (x₁ - p)| =
          |∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t₁ (x₁ - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ (x₀ - p)| := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with p
            ring
      _ ≤ C_twoBumpEstimate (3 / 2) (3 / 2) *
          scaledBracketBumpReal (min (3 / 2 : ℝ) (3 / 2 : ℝ)) t₁ (x₁ - x₀) := htwo
      _ = C_twoBumpEstimate (3 / 2) (3 / 2) *
          scaledBracketBumpReal (3 / 2 : ℝ) (max t₀ t₁) (x₀ - x₁) := by
            rw [min_self, max_eq_right h, show x₁ - x₀ = -(x₀ - x₁) by ring,
              aux_scaledBracketBumpReal_neg]
  · have h' : t₁ ≤ t₀ := le_of_not_ge h
    have htwo := twoBumpEstimate x₀ x₁ t₀ t₁ (3 / 2 : ℝ) (3 / 2 : ℝ)
      ht₀ ht₁ h' (by norm_num) (by norm_num)
    simpa [max_eq_left h'] using htwo

/-- Exact simultaneous rescaling of a real-exponent bracket bump. -/
private theorem aux_caseOne_scaledBracketBumpReal_simul_rescale (N c s x : ℝ) (hc : 0 < c) :
    c * scaledBracketBumpReal N (c * s) (c * x) = scaledBracketBumpReal N s x := by
  unfold scaledBracketBumpReal
  have hcne : c ≠ 0 := ne_of_gt hc
  have harg : (c * s)⁻¹ * (c * x) = s⁻¹ * x := by
    field_simp [hcne]
  have hinv : c * (c * s)⁻¹ = s⁻¹ := by
    field_simp [hcne]
  rw [harg]
  calc
    c * ((c * s)⁻¹ * (1 + |s⁻¹ * x|).rpow (-N)) =
        (c * (c * s)⁻¹) * (1 + |s⁻¹ * x|).rpow (-N) := by ring
    _ = s⁻¹ * (1 + |s⁻¹ * x|).rpow (-N) := by rw [hinv]

/-- A simultaneous spatial-and-scale rescaling leaves a real-exponent bracket bump
invariant after its natural prefactor. -/
theorem aux_scaledBracketBumpReal_simul_rescale (N c s x : ℝ) (hc : 0 < c) :
    c * scaledBracketBumpReal N (c * s) (c * x) = scaledBracketBumpReal N s x :=
  aux_caseOne_scaledBracketBumpReal_simul_rescale N c s x hc

/-- A concrete scalar form of the orthogonal-coordinate dichotomy needed in case one.
It is deliberately stated directly in the `W₁` coordinates, avoiding an auxiliary
identification of `ℝ × ℝ` with Euclidean space. -/
private theorem aux_caseOne_orthogonal_dichotomy (x y : ℝ) :
    |x| ≤ 3 * |(-x + y) / Real.sqrt 2| ∨
      |(x + y) / Real.sqrt 2| ≤ 3 * |y| := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hsqrt_le : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  let a : ℝ := (x + y) / Real.sqrt 2
  let b : ℝ := (-x + y) / Real.sqrt 2
  have hx : x = y - Real.sqrt 2 * b := by
    dsimp [b]
    field_simp [ne_of_gt hsqrt]
    ring
  have ha : a = Real.sqrt 2 * y - b := by
    dsimp [a, b]
    field_simp [ne_of_gt hsqrt]
    rw [hsqrt_sq]
    ring
  by_cases hleft : |x| ≤ 3 * |b|
  · exact Or.inl (by simpa [b] using hleft)
  · right
    have hleft' : 3 * |b| < |x| := lt_of_not_ge hleft
    have hboundx : |x| ≤ |y| + Real.sqrt 2 * |b| := by
      rw [hx]
      calc
        |y - Real.sqrt 2 * b| ≤ |y| + |Real.sqrt 2 * b| := by
          simpa using (abs_sub_le y 0 (Real.sqrt 2 * b))
        _ = |y| + Real.sqrt 2 * |b| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsqrtb : Real.sqrt 2 * |b| ≤ (3 / 2 : ℝ) * |b| :=
      mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg _)
    have hbsmall : (3 / 2 : ℝ) * |b| < |y| := by
      nlinarith [hboundx, hsqrtb]
    have habound : |a| ≤ Real.sqrt 2 * |y| + |b| := by
      rw [ha]
      calc
        |Real.sqrt 2 * y - b| ≤ |Real.sqrt 2 * y| + |b| := by
          simpa using (abs_sub_le (Real.sqrt 2 * y) 0 b)
        _ = Real.sqrt 2 * |y| + |b| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsqrty : Real.sqrt 2 * |y| ≤ (3 / 2 : ℝ) * |y| :=
      mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg _)
    have hbsmall' : |b| ≤ (2 / 3 : ℝ) * |y| := by
      nlinarith [hbsmall]
    have hfinal : |a| ≤ 3 * |y| := by
      nlinarith [habound, hsqrty, hbsmall']
    simpa [a] using hfinal

/-- The two-term real-exponent orthogonal decay used to turn the remaining case-one
three-bump integral into its two `M₂` products. -/
private theorem aux_caseOne_orthogonal_decay (x y lam t : ℝ)
    (hlam : 0 < lam) (ht : 0 < t) :
    scaledBracketBumpReal (3 / 2 : ℝ) lam y *
      scaledBracketBumpReal (3 / 2 : ℝ) t ((-x + y) / Real.sqrt 2) ≤
      8 *
        (scaledBracketBumpReal (3 / 2 : ℝ) lam y *
            scaledBracketBumpReal (3 / 2 : ℝ) t x +
          scaledBracketBumpReal (3 / 2 : ℝ) lam ((x + y) / Real.sqrt 2) *
            scaledBracketBumpReal (3 / 2 : ℝ) t ((-x + y) / Real.sqrt 2)) := by
  have hraw := aux_orthogonalDecay_from_domination
    (A := (3 : ℝ)) (n₀ := (3 / 2 : ℝ)) (n₁ := (3 / 2 : ℝ))
    (s₀ := lam) (s₁ := t) (u₀ := y) (u₁ := (-x + y) / Real.sqrt 2)
    (p₀ := x) (p₁ := (x + y) / Real.sqrt 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlam ht
    (aux_caseOne_orthogonal_dichotomy x y)
  have hcoef : max (Real.rpow 3 (3 / 2 : ℝ)) (Real.rpow 3 (3 / 2 : ℝ)) ≤ 8 := by
    rw [max_self]
    have hthree : Real.rpow 3 (3 / 2 : ℝ) = 3 * Real.sqrt 3 := by
      calc
        Real.rpow 3 (3 / 2 : ℝ) = Real.rpow 3 (1 + 1 / 2 : ℝ) := by congr 1 <;> ring
        _ = Real.rpow 3 1 * Real.rpow 3 (1 / 2 : ℝ) :=
          Real.rpow_add (by norm_num) _ _
        _ = 3 * Real.sqrt 3 := by
          have hone : Real.rpow 3 (1 : ℝ) = 3 := by norm_num
          have hhalf : Real.rpow 3 (1 / 2 : ℝ) = Real.sqrt 3 :=
            (Real.sqrt_eq_rpow 3).symm
          rw [hone, hhalf]
    rw [hthree]
    have hsqrt3 : Real.sqrt (3 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    nlinarith
  have hnonneg : 0 ≤
      scaledBracketBumpReal (3 / 2 : ℝ) lam y *
          scaledBracketBumpReal (3 / 2 : ℝ) t x +
        scaledBracketBumpReal (3 / 2 : ℝ) lam ((x + y) / Real.sqrt 2) *
          scaledBracketBumpReal (3 / 2 : ℝ) t ((-x + y) / Real.sqrt 2) := by
    apply add_nonneg <;> apply mul_nonneg <;>
      apply aux_scaledBracketBumpReal_nonneg <;> assumption
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoef hnonneg)

private theorem aux_caseOne_orthogonal_decay_swap (x y lam t : ℝ)
    (hlam : 0 < lam) (ht : 0 < t) :
    scaledBracketBumpReal (3 / 2 : ℝ) lam x *
      scaledBracketBumpReal (3 / 2 : ℝ) t ((-x + y) / Real.sqrt 2) ≤
      8 *
        (scaledBracketBumpReal (3 / 2 : ℝ) lam x *
            scaledBracketBumpReal (3 / 2 : ℝ) t y +
          scaledBracketBumpReal (3 / 2 : ℝ) lam ((x + y) / Real.sqrt 2) *
            scaledBracketBumpReal (3 / 2 : ℝ) t ((-x + y) / Real.sqrt 2)) := by
  have h := aux_caseOne_orthogonal_decay y x lam t hlam ht
  have hneg : scaledBracketBumpReal (3 / 2 : ℝ) t ((x - y) / Real.sqrt 2) =
      scaledBracketBumpReal (3 / 2 : ℝ) t ((-x + y) / Real.sqrt 2) := by
    rw [show (x - y) / Real.sqrt 2 = -((-x + y) / Real.sqrt 2) by ring,
      aux_scaledBracketBumpReal_neg]
  rw [show -y + x = x - y by ring, hneg] at h
  simpa [add_comm] using h

/-- Every nonnegative-exponent real bracket bump is bounded by the reciprocal scale. -/
private theorem aux_caseOne_scaledBracketBumpReal_le_inv (N s x : ℝ) (hN : 0 ≤ N) (hs : 0 < s) :
    scaledBracketBumpReal N s x ≤ s⁻¹ := by
  unfold scaledBracketBumpReal
  have hbase : 1 ≤ 1 + |s⁻¹ * x| := by linarith [abs_nonneg (s⁻¹ * x)]
  have hpow : Real.rpow (1 + |s⁻¹ * x|) (-N) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  calc
    s⁻¹ * Real.rpow (1 + |s⁻¹ * x|) (-N) ≤ s⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hs.le)
    _ = s⁻¹ := by ring

/-- Integrability of a product of translated real-exponent bracket bumps. -/
private theorem aux_caseOne_scaledBracketBumpReal_product_integrable
    (n₀ n₁ s₀ s₁ x₀ x₁ : ℝ) (hn₀ : 1 < n₀) (hn₁ : 0 ≤ n₁)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) :
    Integrable (fun p : ℝ => scaledBracketBumpReal n₀ s₀ (x₀ - p) *
      scaledBracketBumpReal n₁ s₁ (x₁ - p)) := by
  have hbase : Integrable (fun p : ℝ => scaledBracketBumpReal n₀ s₀ (x₀ - p)) :=
    aux_integrable_scaledBracketBumpReal_translate n₀ s₀ x₀ hn₀ hs₀
  refine (hbase.const_mul s₁⁻¹).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hleftBase : Continuous (fun p : ℝ => 1 + |s₀⁻¹ * (x₀ - p)|) := by fun_prop
    have hrightBase : Continuous (fun p : ℝ => 1 + |s₁⁻¹ * (x₁ - p)|) := by fun_prop
    have hleft : Continuous (fun p : ℝ => scaledBracketBumpReal n₀ s₀ (x₀ - p)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact hleftBase.continuousAt.rpow_const (Or.inl (by positivity))
    have hright : Continuous (fun p : ℝ => scaledBracketBumpReal n₁ s₁ (x₁ - p)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact hrightBase.continuousAt.rpow_const (Or.inl (by positivity))
    exact hleft.mul hright
  · filter_upwards [] with p
    have hleft : 0 ≤ scaledBracketBumpReal n₀ s₀ (x₀ - p) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hs₀
    have hright : 0 ≤ scaledBracketBumpReal n₁ s₁ (x₁ - p) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hs₁
    have hle := aux_caseOne_scaledBracketBumpReal_le_inv n₁ s₁ (x₁ - p) hn₁ hs₁
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft hright)]
    calc
      scaledBracketBumpReal n₀ s₀ (x₀ - p) *
          scaledBracketBumpReal n₁ s₁ (x₁ - p) ≤
        scaledBracketBumpReal n₀ s₀ (x₀ - p) * s₁⁻¹ :=
          mul_le_mul_of_nonneg_left hle hleft
      _ = s₁⁻¹ * scaledBracketBumpReal n₀ s₀ (x₀ - p) := by ring

/-- The three-bump integral in the orientation-zero H-kernel case, before the final
orthogonal-coordinate splitting. -/
private theorem aux_caseOne_threeBumpIntegral_bound (w₀ w₁ lam t₀ t₁ : ℝ)
    (hlam : 0 < lam) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁)
    (ht₀lam : t₀ ≤ lam) (ht₁lam : t₁ ≤ lam) :
    (∫ p : ℝ, scaledBracketBumpReal 2 lam (w₀ + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)) ≤
      C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + w₁) *
              scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁ +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ - w₁) *
              scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁) := by
  let C : ℝ := C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2)
  let B : ℝ := C_twoBumpEstimate (3 / 2) (3 / 2)
  let f : ℝ → ℝ := fun p => scaledBracketBumpReal 2 lam (w₀ + p) *
    scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p) *
    scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)
  let g₀ : ℝ → ℝ := fun p =>
    (scaledBracketBumpReal 2 lam (w₀ + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p)) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁
  let g₁ : ℝ → ℝ := fun p =>
    (scaledBracketBumpReal 2 lam (w₀ + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁
  have hC : 0 ≤ C := by
    have htilde : 0 ≤ C_bumpTriangleTilde (-(1 / 2 : ℝ)) (1 / 2) := by
      unfold C_bumpTriangleTilde
      positivity
    dsimp [C, C_bumpTriangle]
    exact (Real.rpow_nonneg htilde _).trans (le_max_left _ _)
  have hB : 0 ≤ B := by
    dsimp [B, C_twoBumpEstimate]
    norm_num
    positivity
  have hfnon (p : ℝ) : 0 ≤ f p := by
    dsimp [f]
    apply mul_nonneg
    · apply mul_nonneg
      · exact aux_scaledBracketBumpReal_nonneg _ _ _ hlam
      · exact aux_scaledBracketBumpReal_nonneg _ _ _ ht₀
    · exact aux_scaledBracketBumpReal_nonneg _ _ _ ht₁
  have hprod₀ : Integrable (fun p : ℝ =>
      scaledBracketBumpReal 2 lam (w₀ + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p)) := by
    have h := aux_caseOne_scaledBracketBumpReal_product_integrable
      2 (3 / 2 : ℝ) lam t₀ (-w₀) (-w₁) (by norm_num) (by norm_num) hlam ht₀
    convert h using 1
    funext p
    rw [show (-w₀) - p = -(w₀ + p) by ring, aux_scaledBracketBumpReal_neg]
  have hprod₁ : Integrable (fun p : ℝ =>
      scaledBracketBumpReal 2 lam (w₀ + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)) := by
    have h := aux_caseOne_scaledBracketBumpReal_product_integrable
      2 (3 / 2 : ℝ) lam t₁ (-w₀) w₁ (by norm_num) (by norm_num) hlam ht₁
    convert h using 1
    funext p
    rw [show (-w₀) - p = -(w₀ + p) by ring, aux_scaledBracketBumpReal_neg]
  have hg₀ : Integrable g₀ := by
    convert hprod₀.const_mul (scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁) using 1
    funext p
    dsimp [g₀]
    ring
  have hg₁ : Integrable g₁ := by
    convert hprod₁.const_mul (scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁) using 1
    funext p
    dsimp [g₁]
    ring
  have hmajor : Integrable (fun p : ℝ => C * (g₀ p + g₁ p)) :=
    (hg₀.add hg₁).const_mul C
  have hpoint (p : ℝ) : f p ≤ C * (g₀ p + g₁ p) := by
    have htri := aux_bumpTriangleReal
      (n₀ := (3 / 2 : ℝ)) (n₁ := (3 / 2 : ℝ))
      (c₀ := -(1 / 2 : ℝ)) (c₁ := (1 / 2 : ℝ))
      (u := -w₁ - p) (v := w₁ - p) (w := w₁) (s₀ := t₀) (s₁ := t₁)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht₀ ht₁
      (by ring)
    have hlamB : 0 ≤ scaledBracketBumpReal 2 lam (w₀ + p) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hlam
    dsimp [f, g₀, g₁]
    calc
      scaledBracketBumpReal 2 lam (w₀ + p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p) =
          scaledBracketBumpReal 2 lam (w₀ + p) *
            (scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p) *
              scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)) := by ring
      _ ≤ scaledBracketBumpReal 2 lam (w₀ + p) *
          (C * (scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁ +
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁ *
              scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p))) :=
          mul_le_mul_of_nonneg_left htri hlamB
      _ = C * (((scaledBracketBumpReal 2 lam (w₀ + p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p)) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁) +
          ((scaledBracketBumpReal 2 lam (w₀ + p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)) *
              scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁)) := by ring
  have hint : (∫ p : ℝ, f p) ≤ ∫ p : ℝ, C * (g₀ p + g₁ p) :=
    integral_mono_of_nonneg (ae_of_all _ hfnon) hmajor (ae_of_all _ hpoint)
  have hnon₀ (p : ℝ) : 0 ≤
      scaledBracketBumpReal 2 lam (w₀ + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p) := by
    exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
      (aux_scaledBracketBumpReal_nonneg _ _ _ ht₀)
  have hnon₁ (p : ℝ) : 0 ≤
      scaledBracketBumpReal 2 lam (w₀ + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p) := by
    exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
      (aux_scaledBracketBumpReal_nonneg _ _ _ ht₁)
  have htwo₀raw := twoBumpEstimate (-w₀) (-w₁) lam t₀ 2 (3 / 2 : ℝ)
    hlam ht₀ ht₀lam (by norm_num) (by norm_num)
  have htwo₁raw := twoBumpEstimate (-w₀) w₁ lam t₁ 2 (3 / 2 : ℝ)
    hlam ht₁ ht₁lam (by norm_num) (by norm_num)
  have htwo₀ : (∫ p : ℝ,
      scaledBracketBumpReal 2 lam (w₀ + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p)) ≤
      B * scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ - w₁) := by
    rw [← abs_of_nonneg (integral_nonneg hnon₀)]
    calc
      |∫ p : ℝ, scaledBracketBumpReal 2 lam (w₀ + p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p)| =
          |∫ p : ℝ, scaledBracketBumpReal 2 lam ((-w₀) - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ ((-w₁) - p)| := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with p
            rw [show w₀ + p = -((-w₀) - p) by ring, aux_scaledBracketBumpReal_neg]
      _ ≤ C_twoBumpEstimate 2 (3 / 2 : ℝ) *
          scaledBracketBumpReal (min 2 (3 / 2 : ℝ)) lam ((-w₀) - (-w₁)) := htwo₀raw
      _ = B * scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ - w₁) := by
        dsimp [B, C_twoBumpEstimate]
        rw [show -w₀ - -w₁ = -(w₀ - w₁) by ring, aux_scaledBracketBumpReal_neg]
        norm_num
  have htwo₁ : (∫ p : ℝ,
      scaledBracketBumpReal 2 lam (w₀ + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)) ≤
      B * scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + w₁) := by
    rw [← abs_of_nonneg (integral_nonneg hnon₁)]
    calc
      |∫ p : ℝ, scaledBracketBumpReal 2 lam (w₀ + p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)| =
          |∫ p : ℝ, scaledBracketBumpReal 2 lam ((-w₀) - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)| := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with p
            rw [show w₀ + p = -((-w₀) - p) by ring, aux_scaledBracketBumpReal_neg]
      _ ≤ C_twoBumpEstimate 2 (3 / 2 : ℝ) *
          scaledBracketBumpReal (min 2 (3 / 2 : ℝ)) lam ((-w₀) - w₁) := htwo₁raw
      _ = B * scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + w₁) := by
        dsimp [B, C_twoBumpEstimate]
        rw [show -w₀ - w₁ = -(w₀ + w₁) by ring, aux_scaledBracketBumpReal_neg]
        norm_num
  have hg₀bound : (∫ p : ℝ, g₀ p) ≤
      B * scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ - w₁) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁ := by
    rw [show (∫ p : ℝ, g₀ p) =
      (∫ p : ℝ, scaledBracketBumpReal 2 lam (w₀ + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁ by
      rw [integral_mul_const]
      ]
    exact mul_le_mul_of_nonneg_right htwo₀
      (aux_scaledBracketBumpReal_nonneg _ _ _ ht₁)
  have hg₁bound : (∫ p : ℝ, g₁ p) ≤
      B * scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + w₁) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁ := by
    rw [show (∫ p : ℝ, g₁ p) =
      (∫ p : ℝ, scaledBracketBumpReal 2 lam (w₀ + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁ by
      rw [integral_mul_const]
      ]
    exact mul_le_mul_of_nonneg_right htwo₁
      (aux_scaledBracketBumpReal_nonneg _ _ _ ht₀)
  dsimp [f] at hint
  calc
    (∫ p : ℝ, scaledBracketBumpReal 2 lam (w₀ + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ (-w₁ - p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₁ (w₁ - p)) = ∫ p : ℝ, f p := by rfl
    _ ≤ ∫ p : ℝ, C * (g₀ p + g₁ p) := hint
    _ = C * ((∫ p : ℝ, g₀ p) + ∫ p : ℝ, g₁ p) := by
      rw [integral_const_mul, integral_add hg₀ hg₁]
    _ ≤ C * ((B * scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ - w₁) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁) +
      (B * scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + w₁) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁)) :=
      mul_le_mul_of_nonneg_left (add_le_add hg₀bound hg₁bound) hC
    _ = C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + w₁) *
              scaledBracketBumpReal (3 / 2 : ℝ) t₀ w₁ +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ - w₁) *
              scaledBracketBumpReal (3 / 2 : ℝ) t₁ w₁) := by
      dsimp [C, B]
      ring

/-- The orientation-zero three-bump contribution is controlled by the four `M₂` terms
arising from the orthogonal-coordinate split.  The harmless `√2` rescalings make the
coordinate identities exact in the formal `W 1` convention. -/
private theorem aux_caseOne_threeBump_to_fourM2 (w0 w1 lam t0 t1 : ℝ)
    (hlam : 0 < lam) (ht0 : 0 < t0) (ht1 : 0 < t1)
    (ht0lam : t0 ≤ lam) (ht1lam : t1 ≤ lam) :
    (∫ p : ℝ, scaledBracketBumpReal 2 lam (w0 + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) ≤
      16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0)
                (Real.sqrt 2 * w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1)
                (Real.sqrt 2 * w1)) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_le_two : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have ht0' : 0 < Real.sqrt 2 * t0 := mul_pos hsqrt ht0
  have ht1' : 0 < Real.sqrt 2 * t1 := mul_pos hsqrt ht1
  have htriangle : 0 ≤ C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) := by
    have htilde : 0 ≤ C_bumpTriangleTilde (-(1 / 2 : ℝ)) (1 / 2) := by
      unfold C_bumpTriangleTilde
      positivity
    unfold C_bumpTriangle
    exact (Real.rpow_nonneg htilde _).trans (le_max_left _ _)
  have htwo : 0 ≤ C_twoBumpEstimate (3 / 2) (3 / 2) := by
    unfold C_twoBumpEstimate
    norm_num
    positivity
  have hC : 0 ≤ C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
      C_twoBumpEstimate (3 / 2) (3 / 2) :=
    mul_nonneg htriangle htwo
  have hres0 := aux_caseOne_scaledBracketBumpReal_simul_rescale
    (3 / 2 : ℝ) (Real.sqrt 2) t0 w1 hsqrt
  have hres1 := aux_caseOne_scaledBracketBumpReal_simul_rescale
    (3 / 2 : ℝ) (Real.sqrt 2) t1 w1 hsqrt
  have hcoord0 : (-(w0 - w1) + (w0 + w1)) / Real.sqrt 2 =
      Real.sqrt 2 * w1 := by
    apply (div_eq_iff (ne_of_gt hsqrt)).2
    calc
      -(w0 - w1) + (w0 + w1) = 2 * w1 := by ring
      _ = (Real.sqrt 2)^2 * w1 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * w1 * Real.sqrt 2 := by ring
  have hcoord1 : ((w0 - w1) + (w0 + w1)) / Real.sqrt 2 =
      Real.sqrt 2 * w0 := by
    apply (div_eq_iff (ne_of_gt hsqrt)).2
    calc
      (w0 - w1) + (w0 + w1) = 2 * w0 := by ring
      _ = (Real.sqrt 2)^2 * w0 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * w0 * Real.sqrt 2 := by ring
  have hdecay0 := aux_caseOne_orthogonal_decay (w0 - w1) (w0 + w1) lam
    (Real.sqrt 2 * t0) hlam ht0'
  have hdecay1 := aux_caseOne_orthogonal_decay_swap (w0 - w1) (w0 + w1) lam
    (Real.sqrt 2 * t1) hlam ht1'
  rw [hcoord0, hcoord1] at hdecay0 hdecay1
  have hsumNonneg : 0 ≤
      scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
          scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
        scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
          scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
        scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
          scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (Real.sqrt 2 * w1) +
        scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
          scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (Real.sqrt 2 * w1) := by
    refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
    · exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ ht0')
        (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
    · exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
        (aux_scaledBracketBumpReal_nonneg _ _ _ ht1')
    · exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
        (aux_scaledBracketBumpReal_nonneg _ _ _ ht0')
    · exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
        (aux_scaledBracketBumpReal_nonneg _ _ _ ht1')
  have hsum :
      scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) *
          scaledBracketBumpReal (3 / 2 : ℝ) t0 w1 +
        scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 w1 ≤
      8 * Real.sqrt 2 *
        (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
            scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
          scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
            scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
          scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
            scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (Real.sqrt 2 * w1) +
          scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
            scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (Real.sqrt 2 * w1)) := by
    calc
      scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) *
          scaledBracketBumpReal (3 / 2 : ℝ) t0 w1 +
        scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 w1 =
          Real.sqrt 2 *
            (scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0)
                  (Real.sqrt 2 * w1) +
              scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1)
                  (Real.sqrt 2 * w1)) := by
            rw [← hres0, ← hres1]
            ring
      _ ≤ Real.sqrt 2 *
          (8 * (scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) +
              scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0)
                  (Real.sqrt 2 * w1)) +
            8 * (scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
              scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1)
                  (Real.sqrt 2 * w1))) :=
            mul_le_mul_of_nonneg_left (add_le_add hdecay0 hdecay1) (le_of_lt hsqrt)
      _ = 8 * Real.sqrt 2 *
          (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (Real.sqrt 2 * w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (Real.sqrt 2 * w1)) := by
            ring
  have hcoeff : 8 * Real.sqrt 2 ≤ (16 : ℝ) := by
    nlinarith
  have hscale :
      8 * Real.sqrt 2 *
          (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (Real.sqrt 2 * w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (Real.sqrt 2 * w1)) ≤
      16 *
          (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (Real.sqrt 2 * w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (Real.sqrt 2 * w1)) :=
    mul_le_mul_of_nonneg_right hcoeff hsumNonneg
  calc
    (∫ p : ℝ, scaledBracketBumpReal 2 lam (w0 + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) ≤
        C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2) *
            (scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) *
                scaledBracketBumpReal (3 / 2 : ℝ) t0 w1 +
              scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
                scaledBracketBumpReal (3 / 2 : ℝ) t1 w1) :=
      aux_caseOne_threeBumpIntegral_bound w0 w1 lam t0 t1 hlam ht0 ht1 ht0lam ht1lam
    _ ≤ C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2) *
            (8 * Real.sqrt 2 *
              (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
                  scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
                scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
                  scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
                scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
                  scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (Real.sqrt 2 * w1) +
                scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
                  scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (Real.sqrt 2 * w1))) :=
      mul_le_mul_of_nonneg_left hsum hC
    _ ≤ C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2) *
            (16 *
              (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
                  scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
                scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
                  scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
                scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
                  scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (Real.sqrt 2 * w1) +
                scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
                  scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (Real.sqrt 2 * w1))) :=
      mul_le_mul_of_nonneg_left hscale hC
    _ = 16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (w0 - w1) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (w0 + w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t0) (Real.sqrt 2 * w1) +
            scaledBracketBumpReal (3 / 2 : ℝ) lam (Real.sqrt 2 * w0) *
              scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * t1) (Real.sqrt 2 * w1)) := by
      ring

/-- Exact rescaling of the orientation-one M₁ term coming from an orientation-zero
H occurrence. -/
private theorem aux_caseOne_M1_zero_rescale (w0 w1 lam t0 t1 : ℝ) :
    scaledBracketBumpReal (3 / 2 : ℝ) lam w0 *
        scaledBracketBumpReal (3 / 2 : ℝ) (max t0 t1) (2 * w1) =
      scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w0) *
        scaledBracketBumpReal (3 / 2 : ℝ) ((max t0 t1) / Real.sqrt 2)
          (Real.sqrt 2 * w1) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hfirst := aux_caseOne_scaledBracketBumpReal_simul_rescale
    (3 / 2 : ℝ) (Real.sqrt 2) lam w0 hsqrt
  have hsecond := aux_caseOne_scaledBracketBumpReal_simul_rescale
    (3 / 2 : ℝ) (Real.sqrt 2) ((max t0 t1) / Real.sqrt 2)
      (Real.sqrt 2 * w1) hsqrt
  have hfirst' :
      Real.sqrt 2 * scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam)
        (Real.sqrt 2 * w0) = scaledBracketBumpReal (3 / 2 : ℝ) lam w0 := by
    exact hfirst
  have hsecond' :
      Real.sqrt 2 * scaledBracketBumpReal (3 / 2 : ℝ) (max t0 t1) (2 * w1) =
        scaledBracketBumpReal (3 / 2 : ℝ) ((max t0 t1) / Real.sqrt 2)
          (Real.sqrt 2 * w1) := by
    have hscale : Real.sqrt 2 * ((max t0 t1) / Real.sqrt 2) = max t0 t1 := by
      field_simp [ne_of_gt hsqrt]
    have harg : Real.sqrt 2 * (Real.sqrt 2 * w1) = 2 * w1 := by
      calc
        Real.sqrt 2 * (Real.sqrt 2 * w1) = (Real.sqrt 2)^2 * w1 := by ring
        _ = 2 * w1 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hscale, harg] at hsecond
    exact hsecond
  rw [← hfirst', ← hsecond']
  ring

/-- The exact orientation-one M₁ second scale.  In the orientation-zero branch the
normalization of `W 1` contributes a reciprocal square-root factor. -/
private def aux_caseOneExactM1Scale (q : SequencePair × Fin 2) : ℤ → ℝ :=
  if q.2 = 0 then
    fun j => (Real.sqrt 2)⁻¹ * max (q.1 0 j) (q.1 1 j)
  else q.1 1

/-- The five exact real-exponent slots reserved for one occurrence of the six-term H
majorant: one M₁ term and four M₂ terms.  Orientation-one occurrences use M₁ as
nonnegative padding in the remaining four slots. -/
private def aux_caseOneExactSlotOf (lam : ℤ → ℝ) (q : SequencePair × Fin 2) (r : Fin 5) :
    SequencePair × Fin 2 :=
  if r = 0 then
    (aux_sequencePairOf (fun j => Real.sqrt 2 * lam j) (aux_caseOneExactM1Scale q),
      (1 : Fin 2))
  else if q.2 = 0 then
    if r = 1 then (aux_sequencePairOf (fun j => Real.sqrt 2 * q.1 0 j) lam, (0 : Fin 2))
    else if r = 2 then (aux_sequencePairOf lam (fun j => Real.sqrt 2 * q.1 1 j), (0 : Fin 2))
    else if r = 3 then (aux_sequencePairOf lam (fun j => Real.sqrt 2 * q.1 0 j), (1 : Fin 2))
    else (aux_sequencePairOf lam (fun j => Real.sqrt 2 * q.1 1 j), (1 : Fin 2))
  else
    (aux_sequencePairOf (fun j => Real.sqrt 2 * lam j) (aux_caseOneExactM1Scale q),
      (1 : Fin 2))

private theorem aux_caseOneExactM1Scale_spaced (q : SequencePair × Fin 2)
    (hq : ∀ r : Fin 2, SpacedSequence (q.1 r)) :
    SpacedSequence (aux_caseOneExactM1Scale q) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  by_cases hu : q.2 = 0
  · simp [aux_caseOneExactM1Scale, hu]
    exact smul_mem_A (max_mem_A (hq 0) (hq 1)) (inv_pos.mpr hsqrt)
  · simpa [aux_caseOneExactM1Scale, hu] using hq 1

private theorem aux_caseOneExactSlotOf_spaced (lam : ℤ → ℝ) (hlam : SpacedSequence lam)
    (q : SequencePair × Fin 2) (hq : ∀ r : Fin 2, SpacedSequence (q.1 r)) (r : Fin 5) :
    ∀ s : Fin 2, SpacedSequence ((aux_caseOneExactSlotOf lam q r).1 s) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  by_cases hr0 : r = 0
  · intro s
    fin_cases s
    · simpa [aux_caseOneExactSlotOf, hr0, aux_sequencePairOf] using
        smul_mem_A hlam hsqrt
    · simpa [aux_caseOneExactSlotOf, hr0, aux_sequencePairOf] using
        aux_caseOneExactM1Scale_spaced q hq
  by_cases hu : q.2 = 0
  · simp only [aux_caseOneExactSlotOf, if_neg hr0, if_pos hu]
    by_cases hr1 : r = 1
    · intro s
      fin_cases s
      · simpa [hr1, aux_sequencePairOf] using smul_mem_A (hq 0) hsqrt
      · simpa [hr1, aux_sequencePairOf] using hlam
    by_cases hr2 : r = 2
    · intro s
      fin_cases s
      · simpa [hr1, hr2, aux_sequencePairOf] using hlam
      · simpa [hr1, hr2, aux_sequencePairOf] using smul_mem_A (hq 1) hsqrt
    by_cases hr3 : r = 3
    · intro s
      fin_cases s
      · simpa [hr1, hr2, hr3, aux_sequencePairOf] using hlam
      · simpa [hr1, hr2, hr3, aux_sequencePairOf] using smul_mem_A (hq 0) hsqrt
    · intro s
      fin_cases s
      · simpa [hr1, hr2, hr3, aux_sequencePairOf] using hlam
      · simpa [hr1, hr2, hr3, aux_sequencePairOf] using smul_mem_A (hq 1) hsqrt
  · intro s
    fin_cases s
    · simpa [aux_caseOneExactSlotOf, hr0, hu, aux_sequencePairOf] using
        smul_mem_A hlam hsqrt
    · simpa [aux_caseOneExactSlotOf, hr0, hu, aux_sequencePairOf] using
        aux_caseOneExactM1Scale_spaced q hq

private theorem aux_caseOne_sum_fin5 (f : Fin 5 → ℝ) :
    (∑ r : Fin 5, f r) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ]
  ring

/-- Coordinates of the first orthogonal transform at the case-one parametrization. -/
private theorem aux_caseOne_Wone (w0 w1 : ℝ) :
    W (1 : Fin 2) (w0 - w1, w0 + w1) =
      (Real.sqrt 2 * w0, Real.sqrt 2 * w1) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  ext
  · apply (div_eq_iff (ne_of_gt hsqrt)).2
    change ((w0 - w1) + (w0 + w1)) = Real.sqrt 2 * w0 * Real.sqrt 2
    calc
      (w0 - w1) + (w0 + w1) = 2 * w0 := by ring
      _ = (Real.sqrt 2)^2 * w0 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * w0 * Real.sqrt 2 := by ring
  · apply (div_eq_iff (ne_of_gt hsqrt)).2
    change (-(w0 - w1) + (w0 + w1)) = Real.sqrt 2 * w1 * Real.sqrt 2
    calc
      -(w0 - w1) + (w0 + w1) = 2 * w1 := by ring
      _ = (Real.sqrt 2)^2 * w1 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * w1 * Real.sqrt 2 := by ring

/-- The real-exponent bracket product associated to one exact case-one slot. -/
private def aux_caseOneExactSlotTerm (lam : ℤ → ℝ) (q : SequencePair × Fin 2)
    (j : ℤ) (v : RealPlane) (r : Fin 5) : ℝ :=
  scaledBracketBumpReal (3 / 2 : ℝ) ((aux_caseOneExactSlotOf lam q r).1 0 j)
      (W (aux_caseOneExactSlotOf lam q r).2 v).1 *
    scaledBracketBumpReal (3 / 2 : ℝ) ((aux_caseOneExactSlotOf lam q r).1 1 j)
      (W (aux_caseOneExactSlotOf lam q r).2 v).2

private theorem aux_caseOneExactSlotTerm_nonneg (lam : ℤ → ℝ) (hlam : SpacedSequence lam)
    (q : SequencePair × Fin 2) (hq : ∀ s : Fin 2, SpacedSequence (q.1 s))
    (j : ℤ) (v : RealPlane) (r : Fin 5) :
    0 ≤ aux_caseOneExactSlotTerm lam q j v r := by
  have hslot := aux_caseOneExactSlotOf_spaced lam hlam q hq r
  unfold aux_caseOneExactSlotTerm
  exact mul_nonneg
    (aux_scaledBracketBumpReal_nonneg _ _ _ ((hslot 0 j).1))
    (aux_scaledBracketBumpReal_nonneg _ _ _ ((hslot 1 j).1))

/-- The four non-padding slots of an orientation-zero occurrence are exactly the four
real-exponent products output by `aux_caseOne_threeBump_to_fourM2`. -/
private theorem aux_caseOneExactSlotTerms_M2 (lam : ℤ → ℝ) (q : SequencePair × Fin 2)
    (j : ℤ) (w0 w1 : ℝ) (hu : q.2 = 0) :
    scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * q.1 0 j) (w0 - w1) *
        scaledBracketBumpReal (3 / 2 : ℝ) (lam j) (w0 + w1) +
      scaledBracketBumpReal (3 / 2 : ℝ) (lam j) (w0 - w1) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * q.1 1 j) (w0 + w1) +
      scaledBracketBumpReal (3 / 2 : ℝ) (lam j) (Real.sqrt 2 * w0) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * q.1 0 j)
          (Real.sqrt 2 * w1) +
      scaledBracketBumpReal (3 / 2 : ℝ) (lam j) (Real.sqrt 2 * w0) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * q.1 1 j)
          (Real.sqrt 2 * w1) =
      aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
        aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
        aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
        aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4 := by
  have hWzero : W (0 : Fin 2) (w0 - w1, w0 + w1) = (w0 - w1, w0 + w1) := by
    simp [W]
  have hWone := aux_caseOne_Wone w0 w1
  simp [aux_caseOneExactSlotTerm, aux_caseOneExactSlotOf, hu,
    aux_sequencePairOf, hWzero, hWone]

/-- The orientation-zero three-bump contribution is bounded by the same five-slot
occurrence package used for the final thirty-slot witness. -/
private theorem aux_caseOne_threeBump_to_exactSlots (lam : ℤ → ℝ)
    (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (j : ℤ) (w0 w1 : ℝ)
    (hu : q.2 = 0) (ht0lam : q.1 0 j ≤ lam j) (ht1lam : q.1 1 j ≤ lam j) :
    (∫ p : ℝ, scaledBracketBumpReal 2 (lam j) (w0 + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) (q.1 0 j) (-w1 - p) *
      scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (w1 - p)) ≤
      16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          ∑ r : Fin 5,
            aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r := by
  have hraw := aux_caseOne_threeBump_to_fourM2 w0 w1 (lam j) (q.1 0 j) (q.1 1 j)
    (hlam j).1 (hq 0 j).1 (hq 1 j).1 ht0lam ht1lam
  have hterms := aux_caseOneExactSlotTerms_M2 lam q j w0 w1 hu
  have hzero : 0 ≤ aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 0 :=
    aux_caseOneExactSlotTerm_nonneg lam hlam q hq j (w0 - w1, w0 + w1) 0
  have htriangle : 0 ≤ C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) := by
    have htilde : 0 ≤ C_bumpTriangleTilde (-(1 / 2 : ℝ)) (1 / 2) := by
      unfold C_bumpTriangleTilde
      positivity
    unfold C_bumpTriangle
    exact (Real.rpow_nonneg htilde _).trans (le_max_left _ _)
  have htwo : 0 ≤ C_twoBumpEstimate (3 / 2) (3 / 2) := by
    unfold C_twoBumpEstimate
    norm_num
    positivity
  have hC : 0 ≤ 16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
      C_twoBumpEstimate (3 / 2) (3 / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) htriangle) htwo
  have hsum := aux_caseOne_sum_fin5
    (fun r : Fin 5 => aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r)
  have hpad :
      aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4 ≤
        aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 0 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4 := by
    calc
      aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4 =
          0 + (aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
            aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
            aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
            aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4) := by ring
      _ ≤ aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 0 +
          (aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
            aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
            aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
            aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4) :=
          by nlinarith [hzero]
      _ = aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 0 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4 := by ring
  calc
    (∫ p : ℝ, scaledBracketBumpReal 2 (lam j) (w0 + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) (q.1 0 j) (-w1 - p) *
      scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (w1 - p)) ≤
        16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2) *
            (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * q.1 0 j) (w0 - w1) *
                scaledBracketBumpReal (3 / 2 : ℝ) (lam j) (w0 + w1) +
              scaledBracketBumpReal (3 / 2 : ℝ) (lam j) (w0 - w1) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * q.1 1 j) (w0 + w1) +
              scaledBracketBumpReal (3 / 2 : ℝ) (lam j) (Real.sqrt 2 * w0) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * q.1 0 j)
                  (Real.sqrt 2 * w1) +
              scaledBracketBumpReal (3 / 2 : ℝ) (lam j) (Real.sqrt 2 * w0) *
                scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * q.1 1 j)
                  (Real.sqrt 2 * w1)) := hraw
    _ = 16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2) *
            (aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
              aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
              aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
              aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4) := by
          rw [hterms]
    _ ≤ 16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2) *
            (aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 0 +
              aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 1 +
              aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 2 +
              aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 3 +
              aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 4) :=
          mul_le_mul_of_nonneg_left hpad hC
    _ = 16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2) *
            ∑ r : Fin 5,
              aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r := by
          rw [hsum]

/-- The M₁ contribution of an orientation-zero H occurrence.  The two-bump integral is
placed in exact `W 1` coordinates using the max-scale output. -/
private theorem aux_caseOne_m1_orientation_zero (w0 w1 lam t0 t1 : ℝ)
    (hlam : 0 < lam) (ht0 : 0 < t0) (ht1 : 0 < t1) :
    scaledBracketBumpReal 2 lam w0 *
        (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) ≤
      C_twoBumpEstimate (3 / 2) (3 / 2) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w0) *
          scaledBracketBumpReal (3 / 2 : ℝ) ((max t0 t1) / Real.sqrt 2)
            (Real.sqrt 2 * w1) := by
  have hJnonneg : 0 ≤
      ∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
    apply integral_nonneg
    intro p
    exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ ht0)
      (aux_scaledBracketBumpReal_nonneg _ _ _ ht1)
  have hreduce : scaledBracketBumpReal 2 lam w0 ≤
      scaledBracketBumpReal (3 / 2 : ℝ) lam w0 :=
    aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 lam w0 hlam (by norm_num)
  have htwo := aux_caseOne_twoBumpIntegral_max (-w1) w1 t0 t1 ht0 ht1
  have htwo' :
      (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
        scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) ≤
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          scaledBracketBumpReal (3 / 2 : ℝ) (max t0 t1) (2 * w1) := by
    simpa [show -w1 - w1 = -(2 * w1) by ring, aux_scaledBracketBumpReal_neg] using htwo
  have hbase :
      scaledBracketBumpReal 2 lam w0 *
          (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) ≤
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ) lam w0 *
            scaledBracketBumpReal (3 / 2 : ℝ) (max t0 t1) (2 * w1)) := by
    calc
      scaledBracketBumpReal 2 lam w0 *
          (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) ≤
          scaledBracketBumpReal (3 / 2 : ℝ) lam w0 *
            (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
              scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) :=
        mul_le_mul_of_nonneg_right hreduce hJnonneg
      _ ≤ scaledBracketBumpReal (3 / 2 : ℝ) lam w0 *
            (C_twoBumpEstimate (3 / 2) (3 / 2) *
              scaledBracketBumpReal (3 / 2 : ℝ) (max t0 t1) (2 * w1)) :=
        mul_le_mul_of_nonneg_left htwo' (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
      _ = C_twoBumpEstimate (3 / 2) (3 / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ) lam w0 *
            scaledBracketBumpReal (3 / 2 : ℝ) (max t0 t1) (2 * w1)) := by ring
  calc
    scaledBracketBumpReal 2 lam w0 *
        (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) ≤
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ) lam w0 *
            scaledBracketBumpReal (3 / 2 : ℝ) (max t0 t1) (2 * w1)) := hbase
    _ = C_twoBumpEstimate (3 / 2) (3 / 2) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w0) *
          scaledBracketBumpReal (3 / 2 : ℝ) ((max t0 t1) / Real.sqrt 2)
            (Real.sqrt 2 * w1) := by
      rw [aux_caseOne_M1_zero_rescale]
      ring

/-- The orientation-zero M₁ contribution is absorbed by the same five exact slots as
the M₂ contribution. -/
private theorem aux_caseOne_m1_zero_to_exactSlots (lam : ℤ → ℝ)
    (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (j : ℤ) (w0 w1 : ℝ)
    (hu : q.2 = 0) :
    scaledBracketBumpReal 2 (lam j) w0 *
        (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) (q.1 0 j) (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (w1 - p)) ≤
      C_twoBumpEstimate (3 / 2) (3 / 2) *
        ∑ r : Fin 5,
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r := by
  have hraw := aux_caseOne_m1_orientation_zero w0 w1 (lam j) (q.1 0 j) (q.1 1 j)
    (hlam j).1 (hq 0 j).1 (hq 1 j).1
  have hterm0 :
      aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 0 =
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam j) (Real.sqrt 2 * w0) *
          scaledBracketBumpReal (3 / 2 : ℝ) ((max (q.1 0 j) (q.1 1 j)) / Real.sqrt 2)
            (Real.sqrt 2 * w1) := by
    have hWone := aux_caseOne_Wone w0 w1
    have hscale : (Real.sqrt 2)⁻¹ * max (q.1 0 j) (q.1 1 j) =
        max (q.1 0 j) (q.1 1 j) / Real.sqrt 2 := by
      rw [div_eq_mul_inv]
      ring
    simp [aux_caseOneExactSlotTerm, aux_caseOneExactSlotOf, hu,
      aux_caseOneExactM1Scale, aux_sequencePairOf, hWone, hscale]
  have hsum := aux_caseOne_sum_fin5
    (fun r : Fin 5 => aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r)
  have hnon1 := aux_caseOneExactSlotTerm_nonneg lam hlam q hq j (w0 - w1, w0 + w1) 1
  have hnon2 := aux_caseOneExactSlotTerm_nonneg lam hlam q hq j (w0 - w1, w0 + w1) 2
  have hnon3 := aux_caseOneExactSlotTerm_nonneg lam hlam q hq j (w0 - w1, w0 + w1) 3
  have hnon4 := aux_caseOneExactSlotTerm_nonneg lam hlam q hq j (w0 - w1, w0 + w1) 4
  have hsumle : aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 0 ≤
      ∑ r : Fin 5, aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r := by
    rw [hsum]
    nlinarith
  have hCtwo : 0 ≤ C_twoBumpEstimate (3 / 2) (3 / 2) := by
    unfold C_twoBumpEstimate
    norm_num
    positivity
  calc
    scaledBracketBumpReal 2 (lam j) w0 *
        (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) (q.1 0 j) (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (w1 - p)) ≤
        C_twoBumpEstimate (3 / 2) (3 / 2) *
          aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) 0 := by
      rw [hterm0]
      simpa only [mul_assoc] using hraw
    _ ≤ C_twoBumpEstimate (3 / 2) (3 / 2) *
        ∑ r : Fin 5, aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r :=
      mul_le_mul_of_nonneg_left hsumle hCtwo

/-- Uniformly absorbs the M₁ and M₂ coefficients of one orientation-zero occurrence
into the case-one max constant.  The slack is deliberately kept explicit for the outer
multiset summation. -/
private theorem aux_caseOne_zero_coefficients_absorb (S X Y : ℝ) (hS : 0 ≤ S)
    (hX : X ≤ C_twoBumpEstimate (3 / 2) (3 / 2) * S)
    (hY : Y ≤ 16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
      C_twoBumpEstimate (3 / 2) (3 / 2) * S) :
    X + Y ≤ 8 *
      max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
        (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2)) * S := by
  let Ctwo : ℝ := C_twoBumpEstimate (3 / 2) (3 / 2)
  let Ctri : ℝ := C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2)
  let K : ℝ := max (Ctwo + 4) (4 * Ctri * Ctwo)
  have htwo : 0 ≤ Ctwo := by
    dsimp [Ctwo, C_twoBumpEstimate]
    norm_num
    positivity
  have htri : 0 ≤ Ctri := by
    dsimp [Ctri]
    have htilde : 0 ≤ C_bumpTriangleTilde (-(1 / 2 : ℝ)) (1 / 2) := by
      unfold C_bumpTriangleTilde
      positivity
    unfold C_bumpTriangle
    exact (Real.rpow_nonneg htilde _).trans (le_max_left _ _)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact le_trans (by positivity : 0 ≤ Ctwo + 4) (le_max_left _ _)
  have hCtwo : Ctwo ≤ K := by
    calc
      Ctwo ≤ Ctwo + 4 := by linarith
      _ ≤ K := le_max_left _ _
  have hCtri : 4 * Ctri * Ctwo ≤ K := le_max_right _ _
  have hYcoef : 16 * Ctri * Ctwo ≤ 4 * K := by
    calc
      16 * Ctri * Ctwo = 4 * (4 * Ctri * Ctwo) := by ring
      _ ≤ 4 * K := mul_le_mul_of_nonneg_left hCtri (by norm_num)
  have hX' : X ≤ K * S := by
    calc
      X ≤ Ctwo * S := by simpa [Ctwo] using hX
      _ ≤ K * S := mul_le_mul_of_nonneg_right hCtwo hS
  have hY' : Y ≤ (4 * K) * S := by
    calc
      Y ≤ 16 * Ctri * Ctwo * S := by simpa [Ctri, Ctwo] using hY
      _ ≤ (4 * K) * S := mul_le_mul_of_nonneg_right hYcoef hS
  have hsum : X + Y ≤ 5 * K * S := by
    calc
      X + Y ≤ K * S + (4 * K) * S := add_le_add hX' hY'
      _ = 5 * K * S := by ring
  have hfive : 5 * K * S ≤ 8 * K * S := by
    have hKS : 0 ≤ K * S := mul_nonneg hK hS
    nlinarith
  exact hsum.trans (by simpa [Ctwo, Ctri, K] using hfive)

/-- Subadditivity of the clipped linear factor used to split the cancellation gain
between the two orientation-zero H coordinates. -/
private theorem aux_caseOne_min_one_subadd (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  by_cases ha : 1 ≤ a
  · calc
      min 1 (a + b) ≤ 1 := min_le_left _ _
      _ ≤ min 1 a + min 1 b := by
        rw [min_eq_left ha]
        linarith [le_min (by norm_num : (0 : ℝ) ≤ 1) hb0]
  by_cases hb : 1 ≤ b
  · calc
      min 1 (a + b) ≤ 1 := min_le_left _ _
      _ ≤ min 1 a + min 1 b := by
        rw [min_eq_left hb]
        linarith [le_min (by norm_num : (0 : ℝ) ≤ 1) ha0]
  · have ha' : a ≤ 1 := le_of_not_ge ha
    have hb' : b ≤ 1 := le_of_not_ge hb
    rw [min_eq_right ha', min_eq_right hb']
    exact min_le_right _ _

/-- Splits the cancellation factor between the two translated horizontal coordinates. -/
private theorem aux_caseOne_min_split (lam p w1 : ℝ) (hlam : 0 < lam) :
    min 1 (lam⁻¹ * |p|) ≤
      min 1 ((2 * lam)⁻¹ * |-w1 - p|) +
        min 1 ((2 * lam)⁻¹ * |w1 - p|) := by
  let a : ℝ := (2 * lam)⁻¹ * |-w1 - p|
  let b : ℝ := (2 * lam)⁻¹ * |w1 - p|
  have hfactor : 0 ≤ (2 * lam)⁻¹ := inv_nonneg.mpr (by positivity)
  have ha : 0 ≤ a := mul_nonneg hfactor (abs_nonneg _)
  have hb : 0 ≤ b := mul_nonneg hfactor (abs_nonneg _)
  have habs : 2 * |p| ≤ |-w1 - p| + |w1 - p| := by
    calc
      2 * |p| = |(-2 : ℝ) * p| := by rw [abs_mul]; norm_num
      _ = |(-w1 - p) + (w1 - p)| := by congr 1 <;> ring
      _ ≤ |-w1 - p| + |w1 - p| := abs_add_le _ _
  have hlin := mul_le_mul_of_nonneg_left habs hfactor
  have hlin' : lam⁻¹ * |p| ≤ a + b := by
    dsimp [a, b]
    calc
      lam⁻¹ * |p| = (2 * lam)⁻¹ * (2 * |p|) := by
        field_simp [ne_of_gt hlam]
      _ ≤ (2 * lam)⁻¹ * (|-w1 - p| + |w1 - p|) := hlin
      _ = (2 * lam)⁻¹ * |-w1 - p| + (2 * lam)⁻¹ * |w1 - p| := by ring
  calc
    min 1 (lam⁻¹ * |p|) ≤ min 1 (a + b) := min_le_min_left _ hlin'
    _ ≤ min 1 a + min 1 b := aux_caseOne_min_one_subadd a b ha hb
    _ = min 1 ((2 * lam)⁻¹ * |-w1 - p|) +
        min 1 ((2 * lam)⁻¹ * |w1 - p|) := by rfl

/-- The square-root cancellation gain turns the two orientation-zero second-order
bracket factors into real exponent `3/2` factors. -/
private theorem aux_caseOne_u0_min_product (d : ℕ) (lam t0 t1 p w1 : ℝ)
    (hlam : 0 < lam) (ht0 : 0 < t0) (ht1 : 0 < t1)
    (hscale0 : t0 / (2 * lam) ≤ Real.rpow 2 (-(d : ℝ)))
    (hscale1 : t1 / (2 * lam) ≤ Real.rpow 2 (-(d : ℝ))) :
    min 1 (lam⁻¹ * |p|) *
        scaledBracketBump 2 t0 (-w1 - p) * scaledBracketBump 2 t1 (w1 - p) ≤
      2 * Real.rpow 2 (-((d : ℝ) / 2)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
  let r : ℝ := Real.rpow 2 (-((d : ℝ) / 2))
  let z0 : ℝ := 1 + t0⁻¹ * |-w1 - p|
  let z1 : ℝ := 1 + t1⁻¹ * |w1 - p|
  have hlam2 : 0 < 2 * lam := by positivity
  have hsplit := aux_caseOne_min_split lam p w1 hlam
  have hmin0 := aux_caseOne_min_scale_half_le ht0 hlam2 hscale0 (-w1 - p)
  have hmin1 := aux_caseOne_min_scale_half_le ht1 hlam2 hscale1 (w1 - p)
  have hmin : min 1 (lam⁻¹ * |p|) ≤ r * Real.sqrt z0 + r * Real.sqrt z1 := by
    calc
      min 1 (lam⁻¹ * |p|) ≤
          min 1 ((2 * lam)⁻¹ * |-w1 - p|) +
            min 1 ((2 * lam)⁻¹ * |w1 - p|) := hsplit
      _ ≤ r * Real.sqrt z0 + r * Real.sqrt z1 := by
        dsimp [r, z0, z1]
        exact add_le_add hmin0 hmin1
  have hB0 : 0 ≤ scaledBracketBump 2 t0 (-w1 - p) :=
    aux_scaledBracketBump_nonneg 2 ht0 _
  have hB1 : 0 ≤ scaledBracketBump 2 t1 (w1 - p) :=
    aux_scaledBracketBump_nonneg 2 ht1 _
  have hprod : 0 ≤ scaledBracketBump 2 t0 (-w1 - p) *
      scaledBracketBump 2 t1 (w1 - p) := mul_nonneg hB0 hB1
  have hfirst := mul_le_mul_of_nonneg_right hmin hprod
  have hred0 : scaledBracketBump 2 t0 (-w1 - p) ≤
      scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) := by
    rw [← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
    exact aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 t0 (-w1 - p)
      ht0 (by norm_num)
  have hred1 : scaledBracketBump 2 t1 (w1 - p) ≤
      scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
    rw [← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
    exact aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 t1 (w1 - p)
      ht1 (by norm_num)
  have hreal0 := aux_caseOne_scaledBracketBump_two_sqrt_eq_threeHalves t0 (-w1 - p) ht0
  have hreal1 := aux_caseOne_scaledBracketBump_two_sqrt_eq_threeHalves t1 (w1 - p) ht1
  have hreal0' : Real.sqrt z0 * scaledBracketBump 2 t0 (-w1 - p) =
      scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) := by
    dsimp [z0]
    rw [Real.sqrt_eq_rpow]
    exact hreal0
  have hreal1' : Real.sqrt z1 * scaledBracketBump 2 t1 (w1 - p) =
      scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
    dsimp [z1]
    rw [Real.sqrt_eq_rpow]
    exact hreal1
  have hr : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num) _
  have hR0 : r * Real.sqrt z0 * scaledBracketBump 2 t0 (-w1 - p) *
      scaledBracketBump 2 t1 (w1 - p) ≤
        r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
    calc
      r * Real.sqrt z0 * scaledBracketBump 2 t0 (-w1 - p) *
          scaledBracketBump 2 t1 (w1 - p) =
          r * (Real.sqrt z0 * scaledBracketBump 2 t0 (-w1 - p)) *
            scaledBracketBump 2 t1 (w1 - p) := by ring
      _ = r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
            scaledBracketBump 2 t1 (w1 - p) := by
          rw [hreal0']
      _ ≤ r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
          exact mul_le_mul_of_nonneg_left hred1
            (mul_nonneg hr (aux_scaledBracketBumpReal_nonneg _ _ _ ht0))
  have hR1 : r * Real.sqrt z1 * scaledBracketBump 2 t0 (-w1 - p) *
      scaledBracketBump 2 t1 (w1 - p) ≤
        r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
    calc
      r * Real.sqrt z1 * scaledBracketBump 2 t0 (-w1 - p) *
          scaledBracketBump 2 t1 (w1 - p) =
          r * scaledBracketBump 2 t0 (-w1 - p) *
            (Real.sqrt z1 * scaledBracketBump 2 t1 (w1 - p)) := by ring
      _ = r * scaledBracketBump 2 t0 (-w1 - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
          rw [hreal1']
      _ ≤ r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by
          calc
            r * scaledBracketBump 2 t0 (-w1 - p) *
                scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) =
                (r * scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) *
                  scaledBracketBump 2 t0 (-w1 - p) := by ring
            _ ≤ (r * scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) *
                  scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) :=
              mul_le_mul_of_nonneg_left hred0
                (mul_nonneg hr (aux_scaledBracketBumpReal_nonneg _ _ _ ht1))
            _ = r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
                  scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by ring
  calc
    min 1 (lam⁻¹ * |p|) * scaledBracketBump 2 t0 (-w1 - p) *
        scaledBracketBump 2 t1 (w1 - p) ≤
        (r * Real.sqrt z0 + r * Real.sqrt z1) *
          (scaledBracketBump 2 t0 (-w1 - p) * scaledBracketBump 2 t1 (w1 - p)) := by
      simpa only [mul_assoc] using hfirst
    _ = r * Real.sqrt z0 * scaledBracketBump 2 t0 (-w1 - p) *
          scaledBracketBump 2 t1 (w1 - p) +
        r * Real.sqrt z1 * scaledBracketBump 2 t0 (-w1 - p) *
          scaledBracketBump 2 t1 (w1 - p) := by ring
    _ ≤ r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) +
        r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) :=
      add_le_add hR0 hR1
    _ = 2 * r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by ring
    _ = 2 * Real.rpow 2 (-((d : ℝ) / 2)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p) := by rfl

/-- Full orientation-zero occurrence estimate in the common five-slot case-one package.
This is the analytic input used before summing the six H-kernel occurrences. -/
private theorem aux_caseOne_u0_occurrence (d : ℕ) (lam : ℤ → ℝ)
    (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (j : ℤ) (w0 w1 : ℝ)
    (hu : q.2 = 0)
    (hscale0 : q.1 0 j / lam j ≤ Real.rpow 2 (-(d : ℝ)))
    (hscale1 : q.1 1 j / lam j ≤ Real.rpow 2 (-(d : ℝ))) :
    (∫ p : ℝ, min 1 ((lam j)⁻¹ * |p|) *
      (scaledBracketBumpReal 2 (lam j) w0 +
        scaledBracketBumpReal 2 (lam j) (w0 + p)) *
      scaledBracketBump 2 (q.1 0 j) (-w1 - p) *
      scaledBracketBump 2 (q.1 1 j) (w1 - p)) ≤
      16 * Real.rpow 2 (-((d : ℝ) / 2)) *
        max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
          (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
            C_twoBumpEstimate (3 / 2) (3 / 2)) *
          ∑ r : Fin 5, aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r := by
  let t0 : ℝ := q.1 0 j
  let t1 : ℝ := q.1 1 j
  let L : ℝ := lam j
  let r : ℝ := Real.rpow 2 (-((d : ℝ) / 2))
  let T : ℝ → ℝ := fun p =>
    scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)
  let A : ℝ := scaledBracketBumpReal 2 L w0
  let B : ℝ → ℝ := fun p => scaledBracketBumpReal 2 L (w0 + p)
  let X : ℝ := A * ∫ p : ℝ, T p
  let Y : ℝ := ∫ p : ℝ, B p * T p
  let S : ℝ := ∑ r : Fin 5, aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r
  let f : ℝ → ℝ := fun p => min 1 (L⁻¹ * |p|) * (A + B p) *
    scaledBracketBump 2 t0 (-w1 - p) * scaledBracketBump 2 t1 (w1 - p)
  let g0 : ℝ → ℝ := fun p => A * T p
  let g1 : ℝ → ℝ := fun p => B p * T p
  have hL : 0 < L := by exact (hlam j).1
  have ht0 : 0 < t0 := by exact (hq 0 j).1
  have ht1 : 0 < t1 := by exact (hq 1 j).1
  have hpowle : Real.rpow 2 (-(d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have ht0L : t0 ≤ L := by
    have hquot : t0 / L ≤ 1 := by simpa [t0, L] using hscale0.trans hpowle
    calc
      t0 = (t0 / L) * L := by field_simp [ne_of_gt hL]
      _ ≤ 1 * L := mul_le_mul_of_nonneg_right hquot hL.le
      _ = L := by ring
  have ht1L : t1 ≤ L := by
    have hquot : t1 / L ≤ 1 := by simpa [t1, L] using hscale1.trans hpowle
    calc
      t1 = (t1 / L) * L := by field_simp [ne_of_gt hL]
      _ ≤ 1 * L := mul_le_mul_of_nonneg_right hquot hL.le
      _ = L := by ring
  have ht0half : t0 / (2 * L) ≤ Real.rpow 2 (-(d : ℝ)) := by
    calc
      t0 / (2 * L) = (1 / 2 : ℝ) * (t0 / L) := by
        field_simp [ne_of_gt hL]
      _ ≤ t0 / L := by
        have hnon : 0 ≤ t0 / L := div_nonneg ht0.le hL.le
        nlinarith
      _ ≤ Real.rpow 2 (-(d : ℝ)) := by simpa [t0, L] using hscale0
  have ht1half : t1 / (2 * L) ≤ Real.rpow 2 (-(d : ℝ)) := by
    calc
      t1 / (2 * L) = (1 / 2 : ℝ) * (t1 / L) := by
        field_simp [ne_of_gt hL]
      _ ≤ t1 / L := by
        have hnon : 0 ≤ t1 / L := div_nonneg ht1.le hL.le
        nlinarith
      _ ≤ Real.rpow 2 (-(d : ℝ)) := by simpa [t1, L] using hscale1
  have hTnon (p : ℝ) : 0 ≤ T p := by
    dsimp [T]
    exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ ht0)
      (aux_scaledBracketBumpReal_nonneg _ _ _ ht1)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact aux_scaledBracketBumpReal_nonneg _ _ _ hL
  have hB (p : ℝ) : 0 ≤ B p := by
    dsimp [B]
    exact aux_scaledBracketBumpReal_nonneg _ _ _ hL
  have hT : Integrable T := by
    have hbase := aux_caseOne_scaledBracketBumpReal_product_integrable
      (3 / 2 : ℝ) (3 / 2 : ℝ) t0 t1 (-w1) w1 (by norm_num) (by norm_num) ht0 ht1
    simpa [T] using hbase
  have hg0 : Integrable g0 := by
    simpa [g0] using hT.const_mul A
  have hg1 : Integrable g1 := by
    have hmajor : Integrable (fun p : ℝ => L⁻¹ * T p) := hT.const_mul L⁻¹
    refine hmajor.mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have hBbase : Continuous (fun p : ℝ => 1 + |L⁻¹ * (w0 + p)|) := by fun_prop
      have ht0base : Continuous (fun p : ℝ => 1 + |t0⁻¹ * (-w1 - p)|) := by fun_prop
      have ht1base : Continuous (fun p : ℝ => 1 + |t1⁻¹ * (w1 - p)|) := by fun_prop
      have hBcont : Continuous (fun p : ℝ => scaledBracketBumpReal 2 L (w0 + p)) := by
        unfold scaledBracketBumpReal
        apply continuous_const.mul
        rw [continuous_iff_continuousAt]
        intro p
        exact hBbase.continuousAt.rpow_const (Or.inl (by positivity))
      have ht0cont : Continuous (fun p : ℝ =>
          scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p)) := by
        unfold scaledBracketBumpReal
        apply continuous_const.mul
        rw [continuous_iff_continuousAt]
        intro p
        exact ht0base.continuousAt.rpow_const (Or.inl (by positivity))
      have ht1cont : Continuous (fun p : ℝ =>
          scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) := by
        unfold scaledBracketBumpReal
        apply continuous_const.mul
        rw [continuous_iff_continuousAt]
        intro p
        exact ht1base.continuousAt.rpow_const (Or.inl (by positivity))
      change Continuous (fun p : ℝ => B p * T p)
      dsimp [B, T]
      convert hBcont.mul (ht0cont.mul ht1cont) using 1
      ext p
      rfl
    · filter_upwards [] with p
      have hle := aux_caseOne_scaledBracketBumpReal_le_inv 2 L (w0 + p) (by norm_num) hL
      have hmajorNonneg : 0 ≤ L⁻¹ * T p := mul_nonneg (inv_nonneg.mpr hL.le) (hTnon p)
      have hg1Nonneg : 0 ≤ g1 p := mul_nonneg (hB p) (hTnon p)
      simpa only [Real.norm_eq_abs, abs_of_nonneg hg1Nonneg, abs_of_nonneg hmajorNonneg] using
        mul_le_mul_of_nonneg_right hle (hTnon p)
  have hr : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num) _
  have hmajor : Integrable (fun p : ℝ => 2 * r * (g0 p + g1 p)) :=
    (hg0.add hg1).const_mul (2 * r)
  have hfn (p : ℝ) : 0 ≤ f p := by
    dsimp [f]
    have hmin : 0 ≤ min 1 (L⁻¹ * |p|) :=
      le_min (by norm_num) (mul_nonneg (inv_nonneg.mpr hL.le) (abs_nonneg _))
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hmin (add_nonneg hA (hB p)))
        (aux_scaledBracketBump_nonneg 2 ht0 _))
      (aux_scaledBracketBump_nonneg 2 ht1 _)
  have hpoint (p : ℝ) : f p ≤ 2 * r * (g0 p + g1 p) := by
    have hmin := aux_caseOne_u0_min_product d L t0 t1 p w1 hL ht0 ht1 ht0half ht1half
    have hAB : 0 ≤ A + B p := add_nonneg hA (hB p)
    dsimp [f, g0, g1, T]
    calc
      min 1 (L⁻¹ * |p|) * (A + B p) *
          scaledBracketBump 2 t0 (-w1 - p) * scaledBracketBump 2 t1 (w1 - p) =
          (A + B p) *
            (min 1 (L⁻¹ * |p|) * scaledBracketBump 2 t0 (-w1 - p) *
              scaledBracketBump 2 t1 (w1 - p)) := by ring
      _ ≤ (A + B p) *
          (2 * r * scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) :=
        mul_le_mul_of_nonneg_left hmin hAB
      _ = 2 * r *
          (A * (scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p)) +
            B p * (scaledBracketBumpReal (3 / 2 : ℝ) t0 (-w1 - p) *
              scaledBracketBumpReal (3 / 2 : ℝ) t1 (w1 - p))) := by ring
  have hint : (∫ p : ℝ, f p) ≤ ∫ p : ℝ, 2 * r * (g0 p + g1 p) :=
    integral_mono_of_nonneg (ae_of_all _ hfn) hmajor (ae_of_all _ hpoint)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun r _ =>
      aux_caseOneExactSlotTerm_nonneg lam hlam q hq j (w0 - w1, w0 + w1) r
  have hX : X ≤ C_twoBumpEstimate (3 / 2) (3 / 2) * S := by
    dsimp [X, A, T, S]
    simpa [t0, t1, L] using aux_caseOne_m1_zero_to_exactSlots lam hlam q hq j w0 w1 hu
  have hY : Y ≤ 16 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
      C_twoBumpEstimate (3 / 2) (3 / 2) * S := by
    dsimp [Y, B, T, S]
    simpa [t0, t1, L, mul_assoc] using
      aux_caseOne_threeBump_to_exactSlots lam hlam q hq j w0 w1 hu ht0L ht1L
  have habsorb := aux_caseOne_zero_coefficients_absorb S X Y hS hX hY
  calc
    (∫ p : ℝ, min 1 ((lam j)⁻¹ * |p|) *
      (scaledBracketBumpReal 2 (lam j) w0 + scaledBracketBumpReal 2 (lam j) (w0 + p)) *
      scaledBracketBump 2 (q.1 0 j) (-w1 - p) *
      scaledBracketBump 2 (q.1 1 j) (w1 - p)) = ∫ p : ℝ, f p := by rfl
    _ ≤ ∫ p : ℝ, 2 * r * (g0 p + g1 p) := hint
    _ = 2 * r * (X + Y) := by
      rw [integral_const_mul, integral_add hg0 hg1]
      dsimp only [g0, g1, X, Y]
      rw [integral_const_mul]
    _ ≤ 2 * r *
        (8 * max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
          (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
            C_twoBumpEstimate (3 / 2) (3 / 2)) * S) :=
      mul_le_mul_of_nonneg_left habsorb (mul_nonneg (by norm_num) hr)
    _ = 16 * Real.rpow 2 (-((d : ℝ) / 2)) *
        max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
          (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
            C_twoBumpEstimate (3 / 2) (3 / 2)) *
          ∑ r : Fin 5, aux_caseOneExactSlotTerm lam q j (w0 - w1, w0 + w1) r := by
      dsimp [r, S]
      ring

/-- The orientation-zero five-slot occurrence estimate with its dyadic loss obtained
directly from a member of an H-kernel Gaussian package. -/
private theorem aux_caseOne_u0_occurrence_of_package {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hpositive : 0 < ι.1.1)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (hqu : q.2 = 0)
    (lambda : ℝ)
    (hlambda : lambda = (2 : ℝ) ^ ι.1.1 *
      γ.scales i 1 (j + (geometricDelta γ : ℤ))) (w0 w1 : ℝ) :
    (∫ p : ℝ, min 1 (lambda⁻¹ * |p|) *
      (scaledBracketBumpReal 2 lambda w0 +
        scaledBracketBumpReal 2 lambda (w0 + p)) *
      scaledBracketBump 2 (q.1 0 j) (-w1 - p) *
      scaledBracketBump 2 (q.1 1 j) (w1 - p)) ≤
      16 * Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
        max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
          (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
            C_twoBumpEstimate (3 / 2) (3 / 2)) *
          ∑ r : Fin 5,
            aux_caseOneExactSlotTerm
              (fun k => (2 : ℝ) ^ ι.1.1 *
                γ.scales i 1 (k + (geometricDelta γ : ℤ))) q j
              (w0 - w1, w0 + w1) r := by
  let lamSeq : ℤ → ℝ := fun k => (2 : ℝ) ^ ι.1.1 *
    γ.scales i 1 (k + (geometricDelta γ : ℤ))
  have hlam : SpacedSequence lamSeq := by
    intro k
    refine ⟨?_, ?_⟩
    · dsimp [lamSeq]
      exact mul_pos (zpow_pos (by norm_num) _) (γ.scales_spaced i 1 _).1
    · dsimp [lamSeq]
      calc
        2 * ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (k + (geometricDelta γ : ℤ))) =
            (2 : ℝ) ^ ι.1.1 *
              (2 * γ.scales i 1 (k + (geometricDelta γ : ℤ))) := by ring
        _ ≤ (2 : ℝ) ^ ι.1.1 *
              γ.scales i 1 ((k + (geometricDelta γ : ℤ)) + 1) :=
            mul_le_mul_of_nonneg_left
              (γ.scales_spaced i 1 (k + (geometricDelta γ : ℤ))).2 (by positivity)
        _ = (2 : ℝ) ^ ι.1.1 *
              γ.scales i 1 ((k + 1) + (geometricDelta γ : ℤ)) := by
            congr 1
            ring
  rcases hP.1 q hqmem with ⟨hqball0, hqball1⟩
  have hq : ∀ s : Fin 2, SpacedSequence (q.1 s) := by
    intro s
    fin_cases s
    · exact hqball0.1
    · exact hqball1.1
  have hpow : (2 : ℝ) ^ (-ι.1.1) =
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ)) := by
    have hnat : (ι.1.1.natAbs : ℤ) = ι.1.1 :=
      Int.natAbs_of_nonneg hpositive.le
    have hnatR : ((ι.1.1.natAbs : ℕ) : ℝ) = (ι.1.1 : ℝ) := by
      calc
        ((ι.1.1.natAbs : ℕ) : ℝ) = ((ι.1.1.natAbs : ℤ) : ℝ) := by norm_num
        _ = (ι.1.1 : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hnat
    calc
      (2 : ℝ) ^ (-ι.1.1) = Real.rpow 2 ((-ι.1.1 : ℤ) : ℝ) :=
        (Real.rpow_intCast _ _).symm
      _ = Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ)) := by
        congr 1
        rw [Int.cast_neg, ← hnatR]
  have hratio0 := aux_caseOne_distanceBall_scale_ratio_le
    (γ.scales_spaced i 1) hqball0 ι.1.1 j
  have hratio1 := aux_caseOne_distanceBall_scale_ratio_le
    (γ.scales_spaced i 1) hqball1 ι.1.1 j
  have hscale0 : q.1 0 j / lamSeq j ≤
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ)) := by
    change q.1 0 j / ((2 : ℝ) ^ ι.1.1 *
      γ.scales i 1 (j + (geometricDelta γ : ℤ))) ≤ _
    exact hratio0.trans_eq hpow
  have hscale1 : q.1 1 j / lamSeq j ≤
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ)) := by
    change q.1 1 j / ((2 : ℝ) ^ ι.1.1 *
      γ.scales i 1 (j + (geometricDelta γ : ℤ))) ≤ _
    exact hratio1.trans_eq hpow
  have hmain := aux_caseOne_u0_occurrence (ι.1.1.natAbs) lamSeq hlam q hq j w0 w1
    hqu hscale0 hscale1
  have hExponent : -(((ι.1.1.natAbs : ℕ) : ℝ) / 2) =
      -((ι.1.1.natAbs : ℕ) : ℝ) / 2 := by ring
  rw [hExponent] at hmain
  simpa [lamSeq, hlambda] using hmain

private theorem aux_caseOne_u0_real_integrand_integrable
    (w0 w1 lambda t0 t1 : ℝ) (hlambda : 0 < lambda)
    (ht0 : 0 < t0) (ht1 : 0 < t1) :
    Integrable (fun p : ℝ =>
      min 1 (lambda⁻¹ * |p|) *
        (scaledBracketBumpReal 2 lambda w0 +
          scaledBracketBumpReal 2 lambda (w0 + p)) *
        scaledBracketBumpReal 2 t0 (-w1 - p) *
        scaledBracketBumpReal 2 t1 (w1 - p)) := by
  let T : ℝ → ℝ := fun p =>
    scaledBracketBumpReal 2 t0 (-w1 - p) *
      scaledBracketBumpReal 2 t1 (w1 - p)
  let f : ℝ → ℝ := fun p =>
    min 1 (lambda⁻¹ * |p|) *
      (scaledBracketBumpReal 2 lambda w0 +
        scaledBracketBumpReal 2 lambda (w0 + p)) *
      scaledBracketBumpReal 2 t0 (-w1 - p) *
      scaledBracketBumpReal 2 t1 (w1 - p)
  let g : ℝ → ℝ := fun p => 2 * lambda⁻¹ * T p
  change Integrable f
  have hT : Integrable T := by
    have hbase := aux_caseOne_scaledBracketBumpReal_product_integrable
      2 2 t0 t1 (-w1) w1 (by norm_num) (by norm_num) ht0 ht1
    simpa [T] using hbase
  have hmajor : Integrable g := by
    simpa [g] using hT.const_mul (2 * lambda⁻¹)
  refine hmajor.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hmin : Continuous (fun p : ℝ => min 1 (lambda⁻¹ * |p|)) := by fun_prop
    have hlambdaBase : Continuous (fun p : ℝ => 1 + |lambda⁻¹ * (w0 + p)|) := by
      fun_prop
    have ht0Base : Continuous (fun p : ℝ => 1 + |t0⁻¹ * (-w1 - p)|) := by
      fun_prop
    have ht1Base : Continuous (fun p : ℝ => 1 + |t1⁻¹ * (w1 - p)|) := by
      fun_prop
    have hsum : Continuous (fun p : ℝ =>
        scaledBracketBumpReal 2 lambda w0 +
          scaledBracketBumpReal 2 lambda (w0 + p)) := by
      have hconst : Continuous (fun _ : ℝ => scaledBracketBumpReal 2 lambda w0) :=
        continuous_const
      have hvar : Continuous (fun p : ℝ => scaledBracketBumpReal 2 lambda (w0 + p)) := by
        unfold scaledBracketBumpReal
        apply continuous_const.mul
        rw [continuous_iff_continuousAt]
        intro p
        exact hlambdaBase.continuousAt.rpow_const (Or.inl (by positivity))
      exact hconst.add hvar
    have hT0 : Continuous (fun p : ℝ => scaledBracketBumpReal 2 t0 (-w1 - p)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact ht0Base.continuousAt.rpow_const (Or.inl (by positivity))
    have hT1 : Continuous (fun p : ℝ => scaledBracketBumpReal 2 t1 (w1 - p)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact ht1Base.continuousAt.rpow_const (Or.inl (by positivity))
    dsimp [f]
    convert (hmin.mul hsum).mul (hT0.mul hT1) using 1
    ext p
    change min 1 (lambda⁻¹ * |p|) *
        (scaledBracketBumpReal 2 lambda w0 + scaledBracketBumpReal 2 lambda (w0 + p)) *
        scaledBracketBumpReal 2 t0 (-w1 - p) *
        scaledBracketBumpReal 2 t1 (w1 - p) =
      (min 1 (lambda⁻¹ * |p|) *
        (scaledBracketBumpReal 2 lambda w0 + scaledBracketBumpReal 2 lambda (w0 + p))) *
        (scaledBracketBumpReal 2 t0 (-w1 - p) *
          scaledBracketBumpReal 2 t1 (w1 - p))
    ring
  · filter_upwards [] with p
    have hTnon : 0 ≤ T p := by
      dsimp [T]
      exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ ht0)
        (aux_scaledBracketBumpReal_nonneg _ _ _ ht1)
    have hminnon : 0 ≤ min 1 (lambda⁻¹ * |p|) :=
      le_min (by norm_num) (mul_nonneg (inv_nonneg.mpr hlambda.le) (abs_nonneg _))
    have hsumNonneg : 0 ≤ scaledBracketBumpReal 2 lambda w0 +
        scaledBracketBumpReal 2 lambda (w0 + p) :=
      add_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hlambda)
        (aux_scaledBracketBumpReal_nonneg _ _ _ hlambda)
    have hsumle : scaledBracketBumpReal 2 lambda w0 +
        scaledBracketBumpReal 2 lambda (w0 + p) ≤ 2 * lambda⁻¹ := by
      calc
        scaledBracketBumpReal 2 lambda w0 + scaledBracketBumpReal 2 lambda (w0 + p) ≤
            lambda⁻¹ + lambda⁻¹ :=
          add_le_add
            (aux_caseOne_scaledBracketBumpReal_le_inv 2 lambda w0 (by norm_num) hlambda)
            (aux_caseOne_scaledBracketBumpReal_le_inv 2 lambda (w0 + p) (by norm_num) hlambda)
        _ = 2 * lambda⁻¹ := by ring
    have hminsum : min 1 (lambda⁻¹ * |p|) *
        (scaledBracketBumpReal 2 lambda w0 +
          scaledBracketBumpReal 2 lambda (w0 + p)) ≤ 2 * lambda⁻¹ := by
      calc
        min 1 (lambda⁻¹ * |p|) *
            (scaledBracketBumpReal 2 lambda w0 +
              scaledBracketBumpReal 2 lambda (w0 + p)) ≤
            1 * (scaledBracketBumpReal 2 lambda w0 +
              scaledBracketBumpReal 2 lambda (w0 + p)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hsumNonneg
        _ = scaledBracketBumpReal 2 lambda w0 +
              scaledBracketBumpReal 2 lambda (w0 + p) := by ring
        _ ≤ 2 * lambda⁻¹ := hsumle
    have hfnon : 0 ≤ f p := by
      dsimp [f]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hminnon hsumNonneg)
          (aux_scaledBracketBumpReal_nonneg _ _ _ ht0))
        (aux_scaledBracketBumpReal_nonneg _ _ _ ht1)
    have hgnon : 0 ≤ g p := by
      dsimp [g]
      exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hlambda.le)) hTnon
    have hfg : f p ≤ g p := by
      dsimp [f, g, T]
      calc
        min 1 (lambda⁻¹ * |p|) *
            (scaledBracketBumpReal 2 lambda w0 +
              scaledBracketBumpReal 2 lambda (w0 + p)) *
            scaledBracketBumpReal 2 t0 (-w1 - p) *
            scaledBracketBumpReal 2 t1 (w1 - p) =
            (min 1 (lambda⁻¹ * |p|) *
              (scaledBracketBumpReal 2 lambda w0 +
                scaledBracketBumpReal 2 lambda (w0 + p))) *
              (scaledBracketBumpReal 2 t0 (-w1 - p) *
                scaledBracketBumpReal 2 t1 (w1 - p)) := by ring
        _ ≤ (2 * lambda⁻¹) *
              (scaledBracketBumpReal 2 t0 (-w1 - p) *
                scaledBracketBumpReal 2 t1 (w1 - p)) :=
          mul_le_mul_of_nonneg_right hminsum hTnon
    simpa only [Real.norm_eq_abs, abs_of_nonneg hfnon, abs_of_nonneg hgnon] using hfg

/-- The rho-difference estimate lifted through one orientation-zero occurrence of an
H-kernel Gaussian package, in the common exact five-slot majorant. -/
private theorem aux_caseOne_u0_rho_occurrence_of_package {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hpositive : 0 < ι.1.1)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (hqu : q.2 = 0)
    (lambda : ℝ)
    (hlambda : lambda = (2 : ℝ) ^ ι.1.1 *
      γ.scales i 1 (j + (geometricDelta γ : ℤ))) (w0 w1 : ℝ) :
    (∫ p : ℝ,
      |nMultiplierRho γ hkn ι i j (w0 + p) - nMultiplierRho γ hkn ι i j w0| *
        aux_kernelBracketProduct q j (-w1 - p, w1 - p)) ≤
      (32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
        C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2)) *
          ∑ r : Fin 5,
            aux_caseOneExactSlotTerm
              (fun k => (2 : ℝ) ^ ι.1.1 *
                γ.scales i 1 (k + (geometricDelta γ : ℤ))) q j
              (w0 - w1, w0 + w1) r := by
  let A : ℝ := C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2
  let t0 : ℝ := q.1 0 j
  let t1 : ℝ := q.1 1 j
  let f : ℝ → ℝ := fun p =>
    |nMultiplierRho γ hkn ι i j (w0 + p) - nMultiplierRho γ hkn ι i j w0| *
      aux_kernelBracketProduct q j (-w1 - p, w1 - p)
  let g : ℝ → ℝ := fun p =>
    min 1 (lambda⁻¹ * |p|) *
      (scaledBracketBumpReal 2 lambda w0 +
        scaledBracketBumpReal 2 lambda (w0 + p)) *
      scaledBracketBumpReal 2 t0 (-w1 - p) *
      scaledBracketBumpReal 2 t1 (w1 - p)
  rcases hP.1 q hqmem with ⟨hqball0, hqball1⟩
  have ht0 : 0 < t0 := by simpa [t0] using hqball0.1 j |>.1
  have ht1 : 0 < t1 := by simpa [t1] using hqball1.1 j |>.1
  have hlambda_pos : 0 < lambda := by
    rw [hlambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hA : 0 ≤ A := by
    have hK : 0 ≤ C_meanValueBumpEstimate 2 := by
      unfold C_meanValueBumpEstimate
      positivity
    have hM : 0 ≤ aux_maxUpTo C_gaussianBumpEstimate 2 :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans
        (aux_le_maxUpTo C_gaussianBumpEstimate (Nat.zero_le _))
    have hT : 0 ≤ aux_maxUpTo
        (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) 2 := by
      have hzero : 0 ≤ (2 : ℝ) ^ 0 * C_secondGaussianEstimate 0 := by
        simpa using aux_C_secondGaussianEstimate_nonneg 0
      exact hzero.trans
        (aux_le_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l)
          (Nat.zero_le _))
    have hmean : 0 ≤ C_meanFourScaleGaussianKernel 2 := by
      unfold C_meanFourScaleGaussianKernel
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hK) hM)
        (mul_nonneg (mul_nonneg (by norm_num) hK) hT)
    dsimp [A]
    rw [show C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity
  have hqterm (p : ℝ) :
      aux_kernelBracketProduct q j (-w1 - p, w1 - p) =
        scaledBracketBump 2 t0 (-w1 - p) *
          scaledBracketBump 2 t1 (w1 - p) := by
    dsimp [t0, t1]
    simp [aux_kernelBracketProduct, hqu, W]
  have hfnon (p : ℝ) : 0 ≤ f p := by
    dsimp [f]
    rw [hqterm]
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg (aux_scaledBracketBump_nonneg 2 ht0 _)
        (aux_scaledBracketBump_nonneg 2 ht1 _))
  have hpoint (p : ℝ) : f p ≤ (2 * Real.pi * A) * g p := by
    have hrho := aux_nMultiplierRho_positive_difference_bound γ hkn ι i j
      (ne_of_gt hpositive) hpositive w0 p
    rw [← hlambda] at hrho
    have hqnon : 0 ≤ aux_kernelBracketProduct q j (-w1 - p, w1 - p) := by
      rw [hqterm]
      exact mul_nonneg (aux_scaledBracketBump_nonneg 2 ht0 _)
        (aux_scaledBracketBump_nonneg 2 ht1 _)
    have hmul := mul_le_mul_of_nonneg_right hrho hqnon
    have hB : 0 ≤
        (scaledBracketBump 2 lambda (w0 + p) + scaledBracketBump 2 lambda w0) *
          aux_kernelBracketProduct q j (-w1 - p, w1 - p) := by
      apply mul_nonneg
      · exact add_nonneg (aux_scaledBracketBump_nonneg 2 hlambda_pos _)
          (aux_scaledBracketBump_nonneg 2 hlambda_pos _)
      · exact hqnon
    have hpi := aux_caseOne_move_twoPi_out (A := A) (lambda := lambda) (y := p)
      (B := (scaledBracketBump 2 lambda (w0 + p) + scaledBracketBump 2 lambda w0) *
        aux_kernelBracketProduct q j (-w1 - p, w1 - p)) hA hlambda_pos hB
    have hconvert :
        (scaledBracketBump 2 lambda (w0 + p) + scaledBracketBump 2 lambda w0) *
            aux_kernelBracketProduct q j (-w1 - p, w1 - p) =
          (scaledBracketBumpReal 2 lambda w0 +
            scaledBracketBumpReal 2 lambda (w0 + p)) *
              scaledBracketBumpReal 2 t0 (-w1 - p) *
                scaledBracketBumpReal 2 t1 (w1 - p) := by
      rw [hqterm]
      rw [← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq,
        ← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq,
        ← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq,
        ← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
      ring
    dsimp [f, g]
    have hmul' :
        |nMultiplierRho γ hkn ι i j (w0 + p) - nMultiplierRho γ hkn ι i j w0| *
            aux_kernelBracketProduct q j (-w1 - p, w1 - p) ≤
          (C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2 *
            min 1 (2 * Real.pi * lambda⁻¹ * |p|)) *
              ((scaledBracketBump 2 lambda (w0 + p) + scaledBracketBump 2 lambda w0) *
                aux_kernelBracketProduct q j (-w1 - p, w1 - p)) := by
      calc
        _ ≤ C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2 *
            min 1 (2 * Real.pi * lambda⁻¹ * |p|) *
              (scaledBracketBump 2 lambda (w0 + p) + scaledBracketBump 2 lambda w0) *
                aux_kernelBracketProduct q j (-w1 - p, w1 - p) := hmul
        _ = _ := by ring
    calc
      |nMultiplierRho γ hkn ι i j (w0 + p) - nMultiplierRho γ hkn ι i j w0| *
          aux_kernelBracketProduct q j (-w1 - p, w1 - p) ≤
          A * min 1 (2 * Real.pi * lambda⁻¹ * |p|) *
            ((scaledBracketBump 2 lambda (w0 + p) + scaledBracketBump 2 lambda w0) *
              aux_kernelBracketProduct q j (-w1 - p, w1 - p)) := by
            dsimp [A]
            exact hmul'
      _ ≤ (2 * Real.pi * A) * min 1 (lambda⁻¹ * |p|) *
            ((scaledBracketBump 2 lambda (w0 + p) + scaledBracketBump 2 lambda w0) *
              aux_kernelBracketProduct q j (-w1 - p, w1 - p)) := hpi
      _ = (2 * Real.pi * A) *
            (min 1 (lambda⁻¹ * |p|) *
              ((scaledBracketBump 2 lambda (w0 + p) + scaledBracketBump 2 lambda w0) *
                aux_kernelBracketProduct q j (-w1 - p, w1 - p))) := by ring
      _ = (2 * Real.pi * A) *
            (min 1 (lambda⁻¹ * |p|) *
              ((scaledBracketBumpReal 2 lambda w0 +
                scaledBracketBumpReal 2 lambda (w0 + p)) *
                  scaledBracketBumpReal 2 t0 (-w1 - p) *
                    scaledBracketBumpReal 2 t1 (w1 - p))) := by rw [hconvert]
      _ = (2 * Real.pi * A) *
            (min 1 (lambda⁻¹ * |p|) *
              (scaledBracketBumpReal 2 lambda w0 +
                scaledBracketBumpReal 2 lambda (w0 + p)) *
                scaledBracketBumpReal 2 t0 (-w1 - p) *
                  scaledBracketBumpReal 2 t1 (w1 - p)) := by ring
  have hg : Integrable g := by
    simpa [g] using aux_caseOne_u0_real_integrand_integrable
      w0 w1 lambda t0 t1 hlambda_pos ht0 ht1
  have hmajor : Integrable (fun p : ℝ => (2 * Real.pi * A) * g p) :=
    hg.const_mul (2 * Real.pi * A)
  have hint : (∫ p : ℝ, f p) ≤ ∫ p : ℝ, (2 * Real.pi * A) * g p :=
    integral_mono_of_nonneg (ae_of_all _ hfnon) hmajor (ae_of_all _ hpoint)
  have hgeq : (∫ p : ℝ, g p) =
      ∫ p : ℝ, min 1 (lambda⁻¹ * |p|) *
        (scaledBracketBumpReal 2 lambda w0 +
          scaledBracketBumpReal 2 lambda (w0 + p)) *
        scaledBracketBump 2 (q.1 0 j) (-w1 - p) *
        scaledBracketBump 2 (q.1 1 j) (w1 - p) := by
    apply integral_congr_ae
    filter_upwards [] with p
    dsimp [g, t0, t1]
    rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq (q.1 0 j) (-w1 - p),
      aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq (q.1 1 j) (w1 - p)]
  have hnorm := aux_caseOne_u0_occurrence_of_package γ hkn ι i j hpositive
    P hP q hqmem hqu lambda hlambda w0 w1
  have hfactor : 0 ≤ 2 * Real.pi * A :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) hA
  change (∫ p : ℝ, f p) ≤ _
  calc
    (∫ p : ℝ, f p) ≤ ∫ p : ℝ, (2 * Real.pi * A) * g p := hint
    _ = (2 * Real.pi * A) * ∫ p : ℝ, g p := by rw [integral_const_mul]
    _ = (2 * Real.pi * A) *
        (∫ p : ℝ, min 1 (lambda⁻¹ * |p|) *
          (scaledBracketBumpReal 2 lambda w0 +
            scaledBracketBumpReal 2 lambda (w0 + p)) *
          scaledBracketBump 2 (q.1 0 j) (-w1 - p) *
          scaledBracketBump 2 (q.1 1 j) (w1 - p)) := by rw [hgeq]
    _ ≤ (2 * Real.pi * A) *
        (16 * Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2)) *
          ∑ r : Fin 5,
            aux_caseOneExactSlotTerm
              (fun k => (2 : ℝ) ^ ι.1.1 *
                γ.scales i 1 (k + (geometricDelta γ : ℤ))) q j
              (w0 - w1, w0 + w1) r) :=
      mul_le_mul_of_nonneg_left hnorm hfactor
    _ = (32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
        C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2)) *
          ∑ r : Fin 5,
            aux_caseOneExactSlotTerm
              (fun k => (2 : ℝ) ^ ι.1.1 *
                γ.scales i 1 (k + (geometricDelta γ : ℤ))) q j
              (w0 - w1, w0 + w1) r := by
      dsimp [A]
      ring

/-- Scratch-only occurrence enumerator retaining the multiplicities of `P`. -/
private noncomputable def caseOneOccurrence (P : Multiset (SequencePair × Fin 2))
    (k : Fin P.card) : SequencePair × Fin 2 :=
  P.toList.get (Fin.cast (Multiset.length_toList P).symm k)

private theorem caseOneOccurrence_mem (P : Multiset (SequencePair × Fin 2))
    (k : Fin P.card) : caseOneOccurrence P k ∈ P := by
  unfold caseOneOccurrence
  rw [← Multiset.mem_toList]
  exact List.get_mem _ _

/-- The exact orientation-one M₁ second scale. -/
private def caseOneExactM1Scale (q : SequencePair × Fin 2) : ℤ → ℝ :=
  if q.2 = 0 then
    fun j => (Real.sqrt 2)⁻¹ * max (q.1 0 j) (q.1 1 j)
  else q.1 1

/-- One M₁ and four M₂ slots per occurrence of the six-term H package. -/
private def caseOneExactSlotOf (lam : ℤ → ℝ) (q : SequencePair × Fin 2) (r : Fin 5) :
    SequencePair × Fin 2 :=
  if r = 0 then
    (aux_sequencePairOf (fun j => Real.sqrt 2 * lam j) (caseOneExactM1Scale q),
      (1 : Fin 2))
  else if q.2 = 0 then
    if r = 1 then (aux_sequencePairOf (fun j => Real.sqrt 2 * q.1 0 j) lam, (0 : Fin 2))
    else if r = 2 then (aux_sequencePairOf lam (fun j => Real.sqrt 2 * q.1 1 j), (0 : Fin 2))
    else if r = 3 then (aux_sequencePairOf lam (fun j => Real.sqrt 2 * q.1 0 j), (1 : Fin 2))
    else (aux_sequencePairOf lam (fun j => Real.sqrt 2 * q.1 1 j), (1 : Fin 2))
  else
    (aux_sequencePairOf (fun j => Real.sqrt 2 * lam j) (caseOneExactM1Scale q),
      (1 : Fin 2))

private theorem caseOneExactM1Scale_spaced (q : SequencePair × Fin 2)
    (hq : ∀ r : Fin 2, SpacedSequence (q.1 r)) :
    SpacedSequence (caseOneExactM1Scale q) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  by_cases hu : q.2 = 0
  · simp [caseOneExactM1Scale, hu]
    exact smul_mem_A (max_mem_A (hq 0) (hq 1)) (inv_pos.mpr hsqrt)
  · simpa [caseOneExactM1Scale, hu] using hq 1

private theorem caseOneExactSlotOf_spaced (lam : ℤ → ℝ) (hlam : SpacedSequence lam)
    (q : SequencePair × Fin 2) (hq : ∀ r : Fin 2, SpacedSequence (q.1 r)) (r : Fin 5) :
    ∀ s : Fin 2, SpacedSequence ((caseOneExactSlotOf lam q r).1 s) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  by_cases hr0 : r = 0
  · intro s
    fin_cases s
    · simpa [caseOneExactSlotOf, hr0, aux_sequencePairOf] using
        smul_mem_A hlam hsqrt
    · simpa [caseOneExactSlotOf, hr0, aux_sequencePairOf] using
        caseOneExactM1Scale_spaced q hq
  by_cases hu : q.2 = 0
  · simp only [caseOneExactSlotOf, if_neg hr0, if_pos hu]
    by_cases hr1 : r = 1
    · intro s
      fin_cases s
      · simpa [hr1, aux_sequencePairOf] using smul_mem_A (hq 0) hsqrt
      · simpa [hr1, aux_sequencePairOf] using hlam
    by_cases hr2 : r = 2
    · intro s
      fin_cases s
      · simpa [hr1, hr2, aux_sequencePairOf] using hlam
      · simpa [hr1, hr2, aux_sequencePairOf] using smul_mem_A (hq 1) hsqrt
    by_cases hr3 : r = 3
    · intro s
      fin_cases s
      · simpa [hr1, hr2, hr3, aux_sequencePairOf] using hlam
      · simpa [hr1, hr2, hr3, aux_sequencePairOf] using smul_mem_A (hq 0) hsqrt
    · intro s
      fin_cases s
      · simpa [hr1, hr2, hr3, aux_sequencePairOf] using hlam
      · simpa [hr1, hr2, hr3, aux_sequencePairOf] using smul_mem_A (hq 1) hsqrt
  · intro s
    fin_cases s
    · simpa [caseOneExactSlotOf, hr0, hu, aux_sequencePairOf] using smul_mem_A hlam hsqrt
    · simpa [caseOneExactSlotOf, hr0, hu, aux_sequencePairOf] using
        caseOneExactM1Scale_spaced q hq

/-- The scale sequence `λ(j)=2^h a(j+Δ)` used in the positive horizontal case. -/
private def caseOneLambda {n : ℕ} (γ : GeometricParameters n) (ι : MultiplierIndex γ)
    (i : Fin γ.k) : ℤ → ℝ :=
  fun j => (2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ))

private theorem caseOneLambda_spaced {n : ℕ} (γ : GeometricParameters n) (ι : MultiplierIndex γ)
    (i : Fin γ.k) : SpacedSequence (caseOneLambda γ ι i) := by
  unfold caseOneLambda
  exact smul_mem_A (shift_mem_A (γ.scales_spaced i 1) _) (zpow_pos (by norm_num) _)

/-- A scale and its `√2` rescaling are at sequence distance at most one. -/
private theorem caseOne_within_sqrt_two_smul (a : ℤ → ℝ) (ha : SpacedSequence a) :
    WithinSequenceDistance a (fun j => Real.sqrt 2 * a j) 1 := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt_two : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  intro j
  constructor
  · calc
      a (j - 1) ≤ a j := aux_spacedSequence_monotone ha (by omega)
      _ ≤ Real.sqrt 2 * a j := by
        exact le_mul_of_one_le_left (le_of_lt (ha j).1) hsqrt_one
  · calc
      Real.sqrt 2 * a j ≤ 2 * a j :=
        mul_le_mul_of_nonneg_right hsqrt_two (le_of_lt (ha j).1)
      _ ≤ a (j + 1) := (ha j).2

/-- A scale and its reciprocal-`√2` rescaling are at sequence distance at most one. -/
private theorem caseOne_within_inv_sqrt_two_smul (a : ℤ → ℝ) (ha : SpacedSequence a) :
    WithinSequenceDistance a (fun j => (Real.sqrt 2)⁻¹ * a j) 1 := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_two : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hinv_one : (Real.sqrt 2)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hsqrt_pos).2 hsqrt_one
  intro j
  constructor
  · have hmul : Real.sqrt 2 * a (j - 1) ≤ a j := by
      calc
        Real.sqrt 2 * a (j - 1) ≤ 2 * a (j - 1) :=
          mul_le_mul_of_nonneg_right hsqrt_two (le_of_lt (ha (j - 1)).1)
        _ ≤ a ((j - 1) + 1) := (ha (j - 1)).2
        _ = a j := by congr 1; ring
    have hdiv : a (j - 1) ≤ a j / Real.sqrt 2 :=
      (le_div_iff₀ hsqrt_pos).2 (by simpa [mul_comm] using hmul)
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  · calc
      (Real.sqrt 2)⁻¹ * a j ≤ a j := by
        rw [← one_mul (a j)]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hinv_one (le_of_lt (ha j).1)
      _ ≤ a (j + 1) := aux_spacedSequence_le_succ ha j

private theorem caseOne_within_shift (a : ℤ → ℝ) (ha : SpacedSequence a) (d : ℕ) :
    WithinSequenceDistance a (fun j => a (j + d)) d := by
  intro j
  constructor
  · exact aux_spacedSequence_monotone ha (by omega)
  · exact le_rfl

private theorem caseOne_within_max {a q₀ q₁ : ℤ → ℝ} {d : ℕ}
    (hq₀ : WithinSequenceDistance a q₀ d) (hq₁ : WithinSequenceDistance a q₁ d) :
    WithinSequenceDistance a (fun j => max (q₀ j) (q₁ j)) d := by
  intro j
  constructor
  · exact (hq₀ j).1.trans (le_max_left _ _)
  · exact max_le (hq₀ j).2 (hq₁ j).2

/-- The `λ` scale lies within `Δ+h` of the original scale sequence. -/
private theorem caseOneLambda_within {n : ℕ} (γ : GeometricParameters n) (ι : MultiplierIndex γ)
    (i : Fin γ.k) :
    WithinSequenceDistance (γ.scales i 1) (caseOneLambda γ ι i)
      (geometricDelta γ + ι.1.1.natAbs) := by
  let a : ℤ → ℝ := γ.scales i 1
  let d : ℕ := geometricDelta γ
  let h : ℤ := ι.1.1
  let ashift : ℤ → ℝ := fun j => a (j + (d : ℤ))
  have ha : SpacedSequence a := γ.scales_spaced i 1
  have hashift : SpacedSequence ashift := shift_mem_A ha _
  have hshift : WithinSequenceDistance a ashift d := caseOne_within_shift a ha d
  have hpow_dist : SequenceDistance ashift (fun j => (2 : ℝ) ^ h * ashift j) ≤
      (h.natAbs : WithTop ℕ) := sequenceDistance_pow_two_smul_le hashift h
  have hpow : WithinSequenceDistance ashift (fun j => (2 : ℝ) ^ h * ashift j) h.natAbs :=
    aux_withinSequenceDistance_of_sequenceDistance_le hashift hpow_dist
  change WithinSequenceDistance (γ.scales i 1)
    (fun j => (2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ)))
    (geometricDelta γ + ι.1.1.natAbs)
  simpa [a, d, h, ashift] using aux_withinSequenceDistance_trans hshift hpow

/-- A `√2`-rescaled H scale is within the uniform case-one distance budget of `λ`. -/
private theorem caseOne_distance_sqrt_q_lam {a q lam : ℤ → ℝ} {d h : ℕ}
    (hq : WithinSequenceDistance a q d)
    (hlam : WithinSequenceDistance a lam (d + h)) (hlam_mem : SpacedSequence lam)
    (hone : 1 ≤ h) :
    SequenceDistance (fun j => Real.sqrt 2 * q j) lam ≤
      ((2 * (d + h) : ℕ) : WithTop ℕ) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hqa : SequenceDistance q a ≤ (d : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    exact aux_sequenceDistance_le_of_within hq
  have hsqrtqa : SequenceDistance (fun j => Real.sqrt 2 * q j)
      (fun j => Real.sqrt 2 * a j) ≤ (d : WithTop ℕ) := by
    rw [sequenceDistance_smul q a hsqrt]
    exact hqa
  have halam : SequenceDistance a lam ≤ ((d + h : ℕ) : WithTop ℕ) :=
    aux_sequenceDistance_le_of_within hlam
  have hsq : SequenceDistance (fun j => Real.sqrt 2 * lam j) lam ≤ (1 : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    exact aux_sequenceDistance_le_of_within (caseOne_within_sqrt_two_smul lam hlam_mem)
  have hmiddle : SequenceDistance (fun j => Real.sqrt 2 * a j)
      (fun j => Real.sqrt 2 * lam j) ≤ ((d + h : ℕ) : WithTop ℕ) := by
    rw [sequenceDistance_smul a lam hsqrt]
    exact halam
  have htail : SequenceDistance (fun j => Real.sqrt 2 * a j)
      (fun j => Real.sqrt 2 * lam j) +
        SequenceDistance (fun j => Real.sqrt 2 * lam j) lam ≤
      ((d + h : ℕ) : WithTop ℕ) + 1 :=
    add_le_add hmiddle hsq
  calc
    SequenceDistance (fun j => Real.sqrt 2 * q j) lam ≤
        SequenceDistance (fun j => Real.sqrt 2 * q j) (fun j => Real.sqrt 2 * a j) +
          SequenceDistance (fun j => Real.sqrt 2 * a j) lam :=
      sequenceDistance_triangle _ _ _
    _ ≤ (d : WithTop ℕ) +
          (SequenceDistance (fun j => Real.sqrt 2 * a j) (fun j => Real.sqrt 2 * lam j) +
            SequenceDistance (fun j => Real.sqrt 2 * lam j) lam) := by
      gcongr
      exact sequenceDistance_triangle _ _ _
    _ ≤ (d : WithTop ℕ) + ((d + h : ℕ) : WithTop ℕ) + 1 := by
      simpa [add_assoc] using htail
    _ ≤ ((2 * (d + h) : ℕ) : WithTop ℕ) := by
      norm_cast
      omega

/-- The M₁ slot made from `λ` and the maximum of two H scales obeys the same budget. -/
private theorem caseOne_distance_sqrt_lam_inv_sqrt_max {a q₀ q₁ lam : ℤ → ℝ} {d h : ℕ}
    (hq₀ : WithinSequenceDistance a q₀ d) (hq₁ : WithinSequenceDistance a q₁ d)
    (hlam : WithinSequenceDistance a lam (d + h)) (hlam_mem : SpacedSequence lam)
    (hone : 1 ≤ h) :
    SequenceDistance (fun j => Real.sqrt 2 * lam j)
      (fun j => (Real.sqrt 2)⁻¹ * max (q₀ j) (q₁ j)) ≤
      ((2 * (d + h) : ℕ) : WithTop ℕ) := by
  let qmax : ℤ → ℝ := fun j => max (q₀ j) (q₁ j)
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hmax : WithinSequenceDistance a qmax d := caseOne_within_max hq₀ hq₁
  have hmaxdist : SequenceDistance a qmax ≤ (d : WithTop ℕ) :=
    aux_sequenceDistance_le_of_within hmax
  have hlamdist : SequenceDistance a lam ≤ ((d + h : ℕ) : WithTop ℕ) :=
    aux_sequenceDistance_le_of_within hlam
  have htwo : SequenceDistance lam (fun j => (2 : ℝ) * lam j) ≤ (1 : WithTop ℕ) := by
    have h := sequenceDistance_pow_two_smul_le hlam_mem (1 : ℤ)
    norm_num at h ⊢
    simpa using h
  have htworev : SequenceDistance (fun j => (2 : ℝ) * lam j) lam ≤ (1 : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    exact htwo
  have hlammax : SequenceDistance lam qmax ≤ ((d + h : ℕ) : WithTop ℕ) + d := by
    calc
      SequenceDistance lam qmax ≤ SequenceDistance lam a + SequenceDistance a qmax :=
        sequenceDistance_triangle _ _ _
      _ ≤ ((d + h : ℕ) : WithTop ℕ) + d := by
        apply add_le_add
        · rw [sequenceDistance_comm]
          exact hlamdist
        · exact hmaxdist
  have hscaled : SequenceDistance (fun j => Real.sqrt 2 * lam j)
      (fun j => (Real.sqrt 2)⁻¹ * qmax j) =
      SequenceDistance (fun j => (2 : ℝ) * lam j) qmax := by
    calc
      SequenceDistance (fun j => Real.sqrt 2 * lam j)
          (fun j => (Real.sqrt 2)⁻¹ * qmax j) =
          SequenceDistance
            (fun j => Real.sqrt 2 * (Real.sqrt 2 * lam j))
            (fun j => Real.sqrt 2 * ((Real.sqrt 2)⁻¹ * qmax j)) :=
        (sequenceDistance_smul _ _ hsqrt).symm
      _ = SequenceDistance (fun j => (2 : ℝ) * lam j) qmax := by
        congr 2
        · funext j
          rw [← mul_assoc, hsqrt_sq]
        · funext j
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsqrt), one_mul]
  change SequenceDistance (fun j => Real.sqrt 2 * lam j)
      (fun j => (Real.sqrt 2)⁻¹ * qmax j) ≤ _
  rw [hscaled]
  calc
    SequenceDistance (fun j => (2 : ℝ) * lam j) qmax ≤
        SequenceDistance (fun j => (2 : ℝ) * lam j) lam + SequenceDistance lam qmax :=
      sequenceDistance_triangle _ _ _
    _ ≤ (1 : WithTop ℕ) + (((d + h : ℕ) : WithTop ℕ) + d) := by
      exact add_le_add htworev hlammax
    _ ≤ (1 : WithTop ℕ) + ((d + h : ℕ) : WithTop ℕ) + d := by
      simp [add_assoc]
    _ ≤ ((2 * (d + h) : ℕ) : WithTop ℕ) := by
      norm_cast
      omega

/-- The orientation-one M₁ slot has the same uniform distance budget. -/
private theorem caseOne_distance_sqrt_lam_q {a q lam : ℤ → ℝ} {d h : ℕ}
    (hq : WithinSequenceDistance a q d)
    (hlam : WithinSequenceDistance a lam (d + h)) (hlam_mem : SpacedSequence lam)
    (hone : 1 ≤ h) :
    SequenceDistance (fun j => Real.sqrt 2 * lam j) q ≤
      ((2 * (d + h) : ℕ) : WithTop ℕ) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : SequenceDistance (fun j => Real.sqrt 2 * lam j) lam ≤ (1 : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    exact aux_sequenceDistance_le_of_within (caseOne_within_sqrt_two_smul lam hlam_mem)
  have hlamdist : SequenceDistance lam a ≤ ((d + h : ℕ) : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    exact aux_sequenceDistance_le_of_within hlam
  have haq : SequenceDistance a q ≤ (d : WithTop ℕ) :=
    aux_sequenceDistance_le_of_within hq
  have htail : SequenceDistance lam a + SequenceDistance a q ≤
      ((d + h : ℕ) : WithTop ℕ) + d :=
    add_le_add hlamdist haq
  calc
    SequenceDistance (fun j => Real.sqrt 2 * lam j) q ≤
        SequenceDistance (fun j => Real.sqrt 2 * lam j) lam + SequenceDistance lam q :=
      sequenceDistance_triangle _ _ _
    _ ≤ (1 : WithTop ℕ) + (SequenceDistance lam a + SequenceDistance a q) := by
      gcongr
      exact sequenceDistance_triangle _ _ _
    _ ≤ (1 : WithTop ℕ) + ((d + h : ℕ) : WithTop ℕ) + d := by
      simpa [add_assoc] using htail
    _ ≤ ((2 * (d + h) : ℕ) : WithTop ℕ) := by
      norm_cast
      omega

/-- Each of the five exact slots has base-pair distance at most `2(Δ+h)`. -/
private theorem caseOneExactSlotOf_distance_bound {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (hpositive : 0 < ι.1.1)
    (q : SequencePair × Fin 2) (hq : q ∈ aux_hKernelGaussianMultiset γ i) (r : Fin 5) :
    sequencePairDistance (caseOneExactSlotOf (caseOneLambda γ ι i) q r).1 ≤
      ((2 * (geometricDelta γ + ι.1.1.natAbs) : ℕ) : WithTop ℕ) := by
  let a : ℤ → ℝ := γ.scales i 1
  let d : ℕ := geometricDelta γ
  let h : ℕ := ι.1.1.natAbs
  let lam : ℤ → ℝ := caseOneLambda γ ι i
  have ha : SpacedSequence a := γ.scales_spaced i 1
  have hlam : WithinSequenceDistance a lam (d + h) := by
    simpa [a, d, h, lam] using caseOneLambda_within γ ι i
  have hlam_mem : SpacedSequence lam := by
    simpa [lam] using caseOneLambda_spaced γ ι i
  have hh : 1 ≤ h := by
    dsimp [h]
    have hnatpos : 0 < ι.1.1.natAbs := Int.natAbs_pos.mpr (ne_of_gt hpositive)
    omega
  have hvalid := aux_hKernelGaussianMultiset_valid γ i q hq
  have hq₀ : WithinSequenceDistance a (q.1 0) d := by
    apply aux_withinSequenceDistance_of_sequenceDistance_le ha
    simpa [a, d] using hvalid.1.2
  have hq₁ : WithinSequenceDistance a (q.1 1) d := by
    apply aux_withinSequenceDistance_of_sequenceDistance_le ha
    simpa [a, d] using hvalid.2.2
  have hM1zero := caseOne_distance_sqrt_lam_inv_sqrt_max hq₀ hq₁ hlam hlam_mem hh
  have hM1one := caseOne_distance_sqrt_lam_q hq₁ hlam hlam_mem hh
  have hM2zero := caseOne_distance_sqrt_q_lam hq₀ hlam hlam_mem hh
  have hM2one := caseOne_distance_sqrt_q_lam hq₁ hlam hlam_mem hh
  change sequencePairDistance (caseOneExactSlotOf lam q r).1 ≤ ((2 * (d + h) : ℕ) : WithTop ℕ)
  unfold sequencePairDistance
  by_cases hr0 : r = 0
  · by_cases hu : q.2 = 0
    · simpa [caseOneExactSlotOf, hr0, hu, caseOneExactM1Scale, aux_sequencePairOf] using hM1zero
    · simpa [caseOneExactSlotOf, hr0, hu, caseOneExactM1Scale, aux_sequencePairOf] using hM1one
  by_cases hu : q.2 = 0
  · by_cases hr1 : r = 1
    · simpa [caseOneExactSlotOf, hr0, hu, hr1, aux_sequencePairOf] using hM2zero
    by_cases hr2 : r = 2
    · rw [sequenceDistance_comm]
      simpa [caseOneExactSlotOf, hr0, hu, hr1, hr2, aux_sequencePairOf] using hM2one
    by_cases hr3 : r = 3
    · rw [sequenceDistance_comm]
      simpa [caseOneExactSlotOf, hr0, hu, hr1, hr2, hr3, aux_sequencePairOf] using hM2zero
    · rw [sequenceDistance_comm]
      simpa [caseOneExactSlotOf, hr0, hu, hr1, hr2, hr3, aux_sequencePairOf] using hM2one
  · simpa [caseOneExactSlotOf, hr0, hu, caseOneExactM1Scale, aux_sequencePairOf] using hM1one

/-- The `Nat` carrier used by the public witness: six occurrence rows and five slots each. -/
private def caseOneSlotIndex (b : ℕ) : Fin 6 × Fin 5 :=
  (⟨(b / 5) % 6, Nat.mod_lt _ (by norm_num)⟩,
    ⟨b % 5, Nat.mod_lt _ (by norm_num)⟩)

/-- The exact slot selected by a natural-number carrier index. -/
private noncomputable def caseOneSlotNat {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (b : ℕ) : SequencePair × Fin 2 :=
  caseOneExactSlotOf (caseOneLambda γ ι i)
    (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
      (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm (caseOneSlotIndex b).1))
    (caseOneSlotIndex b).2

private def caseOneB : Finset ℕ := Finset.range 30

private def caseOneOrientation {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (b : ℕ) : Fin 2 :=
  (caseOneSlotNat γ ι i b).2

private def caseOneScales {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (b : ℕ) (m : Fin 2 → ℕ) : SequencePair :=
  fun r j => (2 : ℝ) ^ (m r) * (caseOneSlotNat γ ι i b).1 r j

private theorem caseOneB_card : caseOneB.card ≤ C_gaussianDominationCombinedCard := by
  norm_num [caseOneB, C_gaussianDominationCombinedCard]

private theorem caseOneSlotNat_spaced {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (b : ℕ) :
    ∀ r : Fin 2, SpacedSequence ((caseOneSlotNat γ ι i b).1 r) := by
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let k : Fin P.card := Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm
    (caseOneSlotIndex b).1
  let q : SequencePair × Fin 2 := caseOneOccurrence P k
  have hqmem : q ∈ P := by
    exact caseOneOccurrence_mem P k
  have hvalid := aux_hKernelGaussianMultiset_valid γ i q hqmem
  have hq : ∀ r : Fin 2, SpacedSequence (q.1 r) := by
    intro r
    fin_cases r
    · exact hvalid.1.1
    · exact hvalid.2.1
  have hslot := caseOneExactSlotOf_spaced (caseOneLambda γ ι i)
    (caseOneLambda_spaced γ ι i) q hq (caseOneSlotIndex b).2
  simpa [caseOneSlotNat, P, k, q] using hslot

private theorem caseOneScales_spaced {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (b : ℕ) (m : Fin 2 → ℕ) (r : Fin 2) :
    SpacedSequence (caseOneScales γ ι i b m r) := by
  unfold caseOneScales
  exact smul_mem_A (caseOneSlotNat_spaced γ ι i b r) (pow_pos (by norm_num) _)

private theorem caseOneSlotNat_distance_bound {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (hpositive : 0 < ι.1.1) (b : ℕ) :
    sequencePairDistance (caseOneSlotNat γ ι i b).1 ≤
      ((2 * (geometricDelta γ + ι.1.1.natAbs) : ℕ) : WithTop ℕ) := by
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let k : Fin P.card := Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm
    (caseOneSlotIndex b).1
  let q : SequencePair × Fin 2 := caseOneOccurrence P k
  have hqmem : q ∈ P := caseOneOccurrence_mem P k
  have hslot := caseOneExactSlotOf_distance_bound γ ι i hpositive q (by
    simpa [P] using hqmem) (caseOneSlotIndex b).2
  simpa [caseOneSlotNat, P, k, q] using hslot

/-- The dyadically rescaled slot data satisfies exactly the witness distance field. -/
private theorem caseOneScales_distance_bound {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (hpositive : 0 < ι.1.1)
    (b : ℕ) (m : Fin 2 → ℕ) :
    sequencePairDistance (caseOneScales γ ι i b m) ≤
      (C_gaussianDominationCombinedDistance : WithTop ℕ) *
        ((geometricDelta γ + ι.1.1.natAbs + aux_natPairWeight m : ℕ) : WithTop ℕ) := by
  let p : SequencePair := (caseOneSlotNat γ ι i b).1
  let d : ℕ := geometricDelta γ
  let h : ℕ := ι.1.1.natAbs
  have hp₀ : SpacedSequence (p 0) := by
    simpa [p] using caseOneSlotNat_spaced γ ι i b 0
  have hp₁ : SpacedSequence (p 1) := by
    simpa [p] using caseOneSlotNat_spaced γ ι i b 1
  have hbase : SequenceDistance (p 0) (p 1) ≤ ((2 * (d + h) : ℕ) : WithTop ℕ) := by
    simpa [sequencePairDistance, p, d, h] using
      caseOneSlotNat_distance_bound γ ι i hpositive b
  have hleft : SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j) (p 0) ≤
      ((m 0 : ℕ) : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    have h := sequenceDistance_pow_two_smul_le hp₀ ((m 0 : ℕ) : ℤ)
    simpa [zpow_natCast, Int.natAbs_natCast] using h
  have hright : SequenceDistance (p 1) (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤
      ((m 1 : ℕ) : WithTop ℕ) := by
    have h := sequenceDistance_pow_two_smul_le hp₁ ((m 1 : ℕ) : ℤ)
    simpa [zpow_natCast, Int.natAbs_natCast] using h
  change SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j)
      (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤ _
  calc
    SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j)
        (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤
        SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j) (p 0) +
          SequenceDistance (p 0) (fun j => (2 : ℝ) ^ (m 1) * p 1 j) :=
      sequenceDistance_triangle _ _ _
    _ ≤ (m 0 : WithTop ℕ) +
          (SequenceDistance (p 0) (p 1) +
            SequenceDistance (p 1) (fun j => (2 : ℝ) ^ (m 1) * p 1 j)) := by
      gcongr
      exact sequenceDistance_triangle _ _ _
    _ ≤ (m 0 : WithTop ℕ) + ((2 * (d + h) : ℕ) : WithTop ℕ) + m 1 := by
      simpa [add_assoc] using add_le_add hbase hright
    _ ≤ (C_gaussianDominationCombinedDistance : WithTop ℕ) *
          ((d + h + aux_natPairWeight m : ℕ) : WithTop ℕ) := by
      norm_num [C_gaussianDominationCombinedDistance]
      norm_cast
      simp only [aux_natPairWeight]
      omega

/-- The first three fields of the case-one Gaussian-domination witness, ready to be paired
with the analytic estimate and Gaussian-series convergence proofs. -/
private theorem caseOne_witness_side_conditions {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (hpositive : 0 < ι.1.1) :
    caseOneB.card ≤ C_gaussianDominationCombinedCard ∧
      (∀ b ∈ caseOneB, ∀ m : Fin 2 → ℕ, ∀ r : Fin 2,
        SpacedSequence (caseOneScales γ ι i b m r)) ∧
      (∀ b ∈ caseOneB, ∀ m : Fin 2 → ℕ,
        sequencePairDistance (caseOneScales γ ι i b m) ≤
          (C_gaussianDominationCombinedDistance : WithTop ℕ) *
            ((geometricDelta γ + ι.1.1.natAbs + aux_natPairWeight m : ℕ) : WithTop ℕ)) := by
  refine ⟨caseOneB_card, ?_, ?_⟩
  · intro b _ m r
    exact caseOneScales_spaced γ ι i b m r
  · intro b _ m
    exact caseOneScales_distance_bound γ ι i hpositive b m

/-- The range carrier decodes the expected occurrence-slot pair on its 30 valid indices. -/
private theorem caseOneSlotIndex_encode (k : Fin 6) (r : Fin 5) :
    caseOneSlotIndex (k.1 * 5 + r.1) = (k, r) := by
  apply Prod.ext <;> apply Fin.ext <;> simp [caseOneSlotIndex]
  · omega

private theorem caseOneSlotNat_encode {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (k : Fin 6) (r : Fin 5) :
    caseOneSlotNat γ ι i (k.1 * 5 + r.1) =
      caseOneExactSlotOf (caseOneLambda γ ι i)
        (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
          (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r := by
  unfold caseOneSlotNat
  rw [caseOneSlotIndex_encode]

/-- Reindex the 30 natural-number witness slots as six multiset occurrences with five slots
each.  This preserves the occurrence multiplicities of the H-kernel package. -/
private theorem caseOne_sum_range30_reindex {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) {R : Type*} [AddCommMonoid R]
    (F : SequencePair × Fin 2 → R) :
    ∑ b ∈ caseOneB, F (caseOneSlotNat γ ι i b) =
      ∑ k : Fin 6, ∑ r : Fin 5,
        F (caseOneExactSlotOf (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r) := by
  classical
  calc
    ∑ b ∈ caseOneB, F (caseOneSlotNat γ ι i b) =
        ∑ b : Fin 30, F (caseOneSlotNat γ ι i b) := by
      simpa [caseOneB] using
        (Finset.sum_range (fun b : ℕ => F (caseOneSlotNat γ ι i b)))
    _ = ∑ kr : Fin 6 × Fin 5,
        F (caseOneExactSlotOf (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm kr.1)) kr.2) := by
      let e : Fin 6 × Fin 5 ≃ Fin 30 := finProdFinEquiv
      symm
      refine Fintype.sum_equiv e
        (fun kr => F (caseOneExactSlotOf (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm kr.1)) kr.2))
        (fun b => F (caseOneSlotNat γ ι i b)) ?_
      intro kr
      apply congrArg F
      have he : (e kr).1 = kr.1.1 * 5 + kr.2.1 := by
        change kr.2.1 + 5 * kr.1.1 = kr.1.1 * 5 + kr.2.1
        omega
      rw [he, caseOneSlotNat_encode]
    _ = ∑ k : Fin 6, ∑ r : Fin 5,
        F (caseOneExactSlotOf (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r) := by
      simpa using (Fintype.sum_prod_type (fun kr : Fin 6 × Fin 5 =>
        F (caseOneExactSlotOf (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm kr.1)) kr.2)))

noncomputable def aux_finTwoNatEquivProd : (Fin 2 → ℕ) ≃ (ℕ × ℕ) where
  toFun := fun m => (m 0, m 1)
  invFun := fun p r => if r = 0 then p.1 else p.2
  left_inv := by
    intro m
    funext r
    fin_cases r <;> simp
  right_inv := by
    rintro ⟨a, b⟩
    rfl

theorem aux_summable_finTwo_product {f₀ f₁ : ℕ → ℝ}
    (h₀nonneg : ∀ a, 0 ≤ f₀ a) (h₁nonneg : ∀ a, 0 ≤ f₁ a)
    (h₀ : Summable f₀) (h₁ : Summable f₁) :
    Summable (fun m : Fin 2 → ℕ => f₀ (m 0) * f₁ (m 1)) := by
  refine (aux_finTwoNatEquivProd.symm.summable_iff
    (f := fun m : Fin 2 → ℕ => f₀ (m 0) * f₁ (m 1))).mp ?_
  change Summable (fun p : ℕ × ℕ => f₀ p.1 * f₁ p.2)
  refine (summable_prod_of_nonneg ?_).2 ?_
  · rintro ⟨a, b⟩
    exact mul_nonneg (h₀nonneg a) (h₁nonneg b)
  constructor
  · intro a
    simpa using h₁.mul_left (f₀ a)
  · simpa only [tsum_mul_left] using h₀.mul_right (∑' b, f₁ b)

theorem aux_dyadic_gaussian_pair_summable
    (p : SequencePair) (hp : ∀ r : Fin 2, SpacedSequence (p r))
    (u : Fin 2) (j : ℤ) (v : RealPlane) :
    Summable (fun m : Fin 2 → ℕ =>
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v) := by
  let f₀ : ℕ → ℝ := fun a =>
    Real.rpow 2 (-(((a : ℕ) : ℝ) / 2)) *
      gaussianRescale ((2 : ℝ) ^ a * p 0 j) (W u v).1
  let f₁ : ℕ → ℝ := fun a =>
    Real.rpow 2 (-(((a : ℕ) : ℝ) / 2)) *
      gaussianRescale ((2 : ℝ) ^ a * p 1 j) (W u v).2
  have hp₀ : 0 < p 0 j := aux_spacedSequence_pos (hp 0) j
  have hp₁ : 0 < p 1 j := aux_spacedSequence_pos (hp 1) j
  have hhalf (a : ℕ) : (1 - (3 / 2 : ℝ)) * (a : ℝ) = -((a : ℝ) / 2) := by
    ring
  have hf₀ : Summable f₀ := by
    simpa [f₀, hhalf] using
      aux_gaussianDomination_weight_summable (3 / 2 : ℝ) (p 0 j) (W u v).1
        (by norm_num) hp₀
  have hf₁ : Summable f₁ := by
    simpa [f₁, hhalf] using
      aux_gaussianDomination_weight_summable (3 / 2 : ℝ) (p 1 j) (W u v).2
        (by norm_num) hp₁
  have hf₀nonneg (a : ℕ) : 0 ≤ f₀ a := by
    dsimp [f₀]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hp₀) _)
  have hf₁nonneg (a : ℕ) : 0 ≤ f₁ a := by
    dsimp [f₁]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hp₁) _)
  have hprod := aux_summable_finTwo_product hf₀nonneg hf₁nonneg hf₀ hf₁
  convert hprod using 1
  funext m
  have hweight :
      aux_gaussianDominationWeight m =
        Real.rpow 2 (-(((m 0 : ℕ) : ℝ) / 2)) *
          Real.rpow 2 (-(((m 1 : ℕ) : ℝ) / 2)) := by
    unfold aux_gaussianDominationWeight aux_natPairWeight
    calc
      Real.rpow 2 (-((m 0 + m 1 : ℕ) : ℝ) / 2) =
          Real.rpow 2 (-(((m 0 : ℕ) : ℝ) / 2) +
            -(((m 1 : ℕ) : ℝ) / 2)) := by
        congr 1
        push_cast
        ring
      _ = _ := Real.rpow_add (by norm_num) _ _
  rw [hweight]
  simp only [aux_dominatingGaussianTerm, twoDimensionalGaussian]
  dsimp [f₀, f₁]
  ring

theorem aux_finite_dyadic_gaussian_series_summable
    (B : Finset ℕ) (p : ℕ → SequencePair)
    (hp : ∀ b ∈ B, ∀ r : Fin 2, SpacedSequence (p b r))
    (u : ℕ → Fin 2) (j : ℤ) (v : RealPlane) :
    Summable (fun m : Fin 2 → ℕ =>
      aux_gaussianDominationWeight m *
        ∑ b ∈ B, aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p b r k) (u b) j v) := by
  classical
  let F : ℕ → (Fin 2 → ℕ) → ℝ := fun b m =>
    aux_gaussianDominationWeight m *
      aux_dominatingGaussianTerm
        (fun r k => (2 : ℝ) ^ (m r) * p b r k) (u b) j v
  have hF (b : ℕ) (hb : b ∈ B) : Summable (F b) := by
    simpa [F] using aux_dyadic_gaussian_pair_summable (p b) (hp b hb) (u b) j v
  have hsum (s : Finset ℕ) (hs : ∀ b ∈ s, Summable (F b)) :
      Summable (fun m => ∑ b ∈ s, F b m) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert b s hb ih =>
      simp only [Finset.sum_insert hb]
      exact (hs b (Finset.mem_insert_self b s)).add
        (ih (fun c hc => hs c (Finset.mem_insert_of_mem hc)))
  have hmain := hsum B hF
  convert hmain using 1
  funext m
  dsimp [F]
  rw [Finset.mul_sum]

theorem aux_gaussianDominationWeight_summable :
    Summable aux_gaussianDominationWeight := by
  let r : ℝ := Real.rpow 2 (-(1 / 2 : ℝ))
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr : |r| < 1 := by simpa [abs_of_pos hrpos] using hrlt
  have hgeom : Summable (fun a : ℕ => r ^ a) :=
    summable_geometric_of_abs_lt_one hr
  have hterm (a : ℕ) : r ^ a = Real.rpow 2 (-((a : ℝ) / 2)) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hprod := aux_summable_finTwo_product
    (fun a => (pow_nonneg hrpos.le a)) (fun a => (pow_nonneg hrpos.le a)) hgeom hgeom
  convert hprod using 1
  funext m
  unfold aux_gaussianDominationWeight aux_natPairWeight
  rw [hterm (m 0), hterm (m 1)]
  calc
    Real.rpow 2 (-((m 0 + m 1 : ℕ) : ℝ) / 2) =
        Real.rpow 2 (-(((m 0 : ℕ) : ℝ) / 2) +
          -(((m 1 : ℕ) : ℝ) / 2)) := by
      congr 1
      push_cast
      ring
    _ = _ := Real.rpow_add (by norm_num) _ _

private theorem aux_gaussianWeightMoment_finTwo_tsum_product {f₀ f₁ : ℕ → ℝ}
    (h₀nonneg : ∀ a, 0 ≤ f₀ a) (h₁nonneg : ∀ a, 0 ≤ f₁ a)
    (h₀ : Summable f₀) (h₁ : Summable f₁) :
    (∑' a : ℕ, f₀ a) * (∑' a : ℕ, f₁ a) =
      ∑' m : Fin 2 → ℕ, f₀ (m 0) * f₁ (m 1) := by
  have hprod : Summable (fun m : Fin 2 → ℕ => f₀ (m 0) * f₁ (m 1)) :=
    aux_summable_finTwo_product h₀nonneg h₁nonneg h₀ h₁
  have hprodPair : Summable (fun z : ℕ × ℕ => f₀ z.1 * f₁ z.2) := by
    refine (aux_finTwoNatEquivProd.symm.summable_iff
      (f := fun m : Fin 2 → ℕ => f₀ (m 0) * f₁ (m 1))).mpr ?_
    exact hprod
  calc
    (∑' a : ℕ, f₀ a) * (∑' a : ℕ, f₁ a) =
        ∑' z : ℕ × ℕ, f₀ z.1 * f₁ z.2 := h₀.tsum_mul_tsum h₁ hprodPair
    _ = ∑' m : Fin 2 → ℕ, f₀ (m 0) * f₁ (m 1) := by
      simpa [aux_finTwoNatEquivProd] using
        (aux_finTwoNatEquivProd.symm.tsum_eq
          (fun m : Fin 2 → ℕ => f₀ (m 0) * f₁ (m 1)))

private theorem aux_gaussianWeightMoment_square_summable :
    Summable (fun a : ℕ => ((a : ℝ) + 1) ^ (2 : ℕ) * (17 / 24 : ℝ) ^ a) := by
  let r : ℝ := 17 / 24
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    norm_num [Real.norm_eq_abs]
  have h₁ := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr
  have h₂ := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr
  have hsum := (h₂.mul_left (2 : ℝ)).sub h₁
  apply hsum.summable.congr
  intro a
  norm_num [Nat.cast_choose_two]
  ring

private theorem aux_gaussianWeightMoment_square_tsum :
    (∑' a : ℕ, ((a : ℝ) + 1) ^ (2 : ℕ) * (17 / 24 : ℝ) ^ a) =
      23616 / 343 := by
  let r : ℝ := 17 / 24
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    norm_num [Real.norm_eq_abs]
  have h₁ := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr
  have h₂ := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr
  have hsum := (h₂.mul_left (2 : ℝ)).sub h₁
  have hterm (a : ℕ) :
      ((a : ℝ) + 1) ^ (2 : ℕ) * r ^ a =
        2 * ((↑((a + 2).choose 2) : ℝ) * r ^ a) -
          (↑((a + 1).choose 1) : ℝ) * r ^ a := by
    rw [Nat.cast_choose_two]
    simp
    ring
  calc
    (∑' a : ℕ, ((a : ℝ) + 1) ^ (2 : ℕ) * (17 / 24 : ℝ) ^ a) =
        2 * (1 / (1 - r) ^ (2 + 1)) - 1 / (1 - r) ^ (1 + 1) := by
      rw [← hsum.tsum_eq]
      apply tsum_congr
      intro a
      exact hterm a
    _ = 23616 / 343 := by
      dsimp [r]
      norm_num

private theorem aux_gaussianWeightMoment_half_le :
    Real.rpow 2 (-(1 / 2 : ℝ)) ≤ (17 / 24 : ℝ) := by
  change (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (17 / 24 : ℝ)
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.sqrt_eq_rpow]
  apply (inv_le_iff_one_le_mul₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))).mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

/-- The weighted second moment of the dyadic Gaussian-domination series is summable. -/
theorem aux_gaussianDominationWeight_secondMoment_summable :
    Summable (fun m : Fin 2 → ℕ => aux_gaussianDominationWeight m *
      (1 + (aux_natPairWeight m : ℝ)) ^ (2 : ℕ)) := by
  let q : ℝ := Real.rpow 2 (-(1 / 2 : ℝ))
  let r : ℝ := 17 / 24
  let f0 : ℕ → ℝ := fun a => r ^ a
  let f2 : ℕ → ℝ := fun a => ((a : ℝ) + 1) ^ (2 : ℕ) * r ^ a
  have hrnonneg : 0 ≤ r := by dsimp [r]; norm_num
  have hrlt : ‖r‖ < 1 := by dsimp [r]; norm_num [Real.norm_eq_abs]
  have hf0 : Summable f0 := by
    dsimp [f0]
    exact summable_geometric_of_norm_lt_one hrlt
  have hf2 : Summable f2 := by
    dsimp [f2, r]
    exact aux_gaussianWeightMoment_square_summable
  have hf0nonneg (a : ℕ) : 0 ≤ f0 a := by
    exact pow_nonneg hrnonneg a
  have hf2nonneg (a : ℕ) : 0 ≤ f2 a := by
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hrnonneg a)
  have hprod : Summable (fun m : Fin 2 → ℕ =>
      2 * (f2 (m 0) * f0 (m 1) + f0 (m 0) * f2 (m 1))) := by
    exact Summable.mul_left 2
      ((aux_summable_finTwo_product hf2nonneg hf0nonneg hf2 hf0).add
        (aux_summable_finTwo_product hf0nonneg hf2nonneg hf0 hf2))
  have hmajorantPoint (m : Fin 2 → ℕ) :
      r ^ (m 0 + m 1) * (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤
        2 * (f2 (m 0) * f0 (m 1) + f0 (m 0) * f2 (m 1)) := by
    have hpow : r ^ (m 0 + m 1) = r ^ (m 0) * r ^ (m 1) := by
      rw [pow_add]
    have hsq : (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤
        2 * (((m 0 : ℝ) + 1) ^ (2 : ℕ)) +
          2 * (((m 1 : ℝ) + 1) ^ (2 : ℕ)) := by
      push_cast
      have hb : 0 ≤ (m 1 : ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg ((m 0 : ℝ) + 1 - (m 1 : ℝ))]
    rw [hpow]
    dsimp [f0, f2]
    calc
      r ^ m 0 * r ^ m 1 * (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤
          r ^ m 0 * r ^ m 1 *
            (2 * (((m 0 : ℝ) + 1) ^ (2 : ℕ)) +
              2 * (((m 1 : ℝ) + 1) ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hsq
          (mul_nonneg (pow_nonneg hrnonneg _) (pow_nonneg hrnonneg _))
      _ = 2 * ((((m 0 : ℝ) + 1) ^ (2 : ℕ) * r ^ m 0) * r ^ m 1 +
          r ^ m 0 * (((m 1 : ℝ) + 1) ^ (2 : ℕ) * r ^ m 1)) := by ring
  have hmajorant : Summable (fun m : Fin 2 → ℕ =>
      r ^ (m 0 + m 1) * (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ)) :=
    Summable.of_nonneg_of_le (fun m => by
      exact mul_nonneg (pow_nonneg hrnonneg _) (sq_nonneg _)) hmajorantPoint hprod
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (by norm_num) _
  have hqle : q ≤ r := by
    dsimp [q, r]
    exact aux_gaussianWeightMoment_half_le
  have hterm (a : ℕ) : q ^ a = Real.rpow 2 (-((a : ℝ) / 2)) := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hweight (m : Fin 2 → ℕ) :
      aux_gaussianDominationWeight m = q ^ (m 0 + m 1) := by
    unfold aux_gaussianDominationWeight aux_natPairWeight
    convert (hterm (m 0 + m 1)).symm using 1
    congr 1
    ring
  have hpoint (m : Fin 2 → ℕ) :
      aux_gaussianDominationWeight m *
          (1 + (aux_natPairWeight m : ℝ)) ^ (2 : ℕ) ≤
        r ^ (m 0 + m 1) *
          (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
    rw [hweight]
    simp only [aux_natPairWeight]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hqnonneg hqle _)
      (sq_nonneg _)
  exact Summable.of_nonneg_of_le (fun m => by
    exact mul_nonneg (aux_gaussianDominationWeight_nonneg m) (sq_nonneg _))
    hpoint hmajorant

/-- The dyadic two-parameter Gaussian weight has the second moment used in the
main induction. -/
theorem aux_gaussianDominationWeight_secondMoment_le_two_pow_ten :
    (∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
      (1 + (aux_natPairWeight m : ℝ)) ^ (2 : ℕ)) ≤ (2 : ℝ) ^ (10 : ℕ) := by
  let q : ℝ := Real.rpow 2 (-(1 / 2 : ℝ))
  let r : ℝ := 17 / 24
  let f₀ : ℕ → ℝ := fun a => r ^ a
  let f₂ : ℕ → ℝ := fun a => ((a : ℝ) + 1) ^ (2 : ℕ) * r ^ a
  have hrnonneg : 0 ≤ r := by dsimp [r]; norm_num
  have hrlt : ‖r‖ < 1 := by dsimp [r]; norm_num [Real.norm_eq_abs]
  have hf₀ : Summable f₀ := by
    dsimp [f₀]
    exact summable_geometric_of_norm_lt_one hrlt
  have hf₂ : Summable f₂ := by
    dsimp [f₂, r]
    exact aux_gaussianWeightMoment_square_summable
  have hf₀nonneg (a : ℕ) : 0 ≤ f₀ a := by
    exact pow_nonneg hrnonneg a
  have hf₂nonneg (a : ℕ) : 0 ≤ f₂ a := by
    exact mul_nonneg (sq_nonneg _) (pow_nonneg hrnonneg a)
  have hprod : Summable (fun m : Fin 2 → ℕ =>
      2 * (f₂ (m 0) * f₀ (m 1) + f₀ (m 0) * f₂ (m 1))) := by
    exact Summable.mul_left 2
      ((aux_summable_finTwo_product hf₂nonneg hf₀nonneg hf₂ hf₀).add
        (aux_summable_finTwo_product hf₀nonneg hf₂nonneg hf₀ hf₂))
  have hmajorantPoint (m : Fin 2 → ℕ) :
      r ^ (m 0 + m 1) * (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤
        2 * (f₂ (m 0) * f₀ (m 1) + f₀ (m 0) * f₂ (m 1)) := by
    have hpow : r ^ (m 0 + m 1) = r ^ (m 0) * r ^ (m 1) := by
      rw [pow_add]
    have hsq : (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤
        2 * (((m 0 : ℝ) + 1) ^ (2 : ℕ)) +
          2 * (((m 1 : ℝ) + 1) ^ (2 : ℕ)) := by
      push_cast
      have hb : 0 ≤ (m 1 : ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg ((m 0 : ℝ) + 1 - (m 1 : ℝ))]
    rw [hpow]
    dsimp [f₀, f₂]
    calc
      r ^ m 0 * r ^ m 1 * (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) ≤
          r ^ m 0 * r ^ m 1 *
            (2 * (((m 0 : ℝ) + 1) ^ (2 : ℕ)) +
              2 * (((m 1 : ℝ) + 1) ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hsq
          (mul_nonneg (pow_nonneg hrnonneg _) (pow_nonneg hrnonneg _))
      _ = 2 * ((((m 0 : ℝ) + 1) ^ (2 : ℕ) * r ^ m 0) * r ^ m 1 +
          r ^ m 0 * (((m 1 : ℝ) + 1) ^ (2 : ℕ) * r ^ m 1)) := by ring
  have hmajorant : Summable (fun m : Fin 2 → ℕ =>
      r ^ (m 0 + m 1) * (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ)) :=
    Summable.of_nonneg_of_le (fun m => by
      exact mul_nonneg (pow_nonneg hrnonneg _) (sq_nonneg _)) hmajorantPoint hprod
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (by norm_num) _
  have hqle : q ≤ r := by
    dsimp [q, r]
    exact aux_gaussianWeightMoment_half_le
  have hterm (a : ℕ) : q ^ a = Real.rpow 2 (-((a : ℝ) / 2)) := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hweight (m : Fin 2 → ℕ) :
      aux_gaussianDominationWeight m = q ^ (m 0 + m 1) := by
    unfold aux_gaussianDominationWeight aux_natPairWeight
    convert (hterm (m 0 + m 1)).symm using 1
    congr 1
    ring
  have hpoint (m : Fin 2 → ℕ) :
      aux_gaussianDominationWeight m *
          (1 + (aux_natPairWeight m : ℝ)) ^ (2 : ℕ) ≤
        r ^ (m 0 + m 1) *
          (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) := by
    rw [hweight]
    simp only [aux_natPairWeight]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hqnonneg hqle _)
      (sq_nonneg _)
  have hsum := Summable.tsum_le_tsum hpoint
    (Summable.of_nonneg_of_le (fun m => by
      exact mul_nonneg (aux_gaussianDominationWeight_nonneg m) (sq_nonneg _))
      hpoint hmajorant)
    hmajorant
  have h₀ : (∑' a : ℕ, f₀ a) = 24 / 7 := by
    dsimp [f₀, r]
    have hr : ‖(17 / 24 : ℝ)‖ < 1 := by norm_num [Real.norm_eq_abs]
    rw [tsum_geometric_of_norm_lt_one hr]
    norm_num
  have h₂ : (∑' a : ℕ, f₂ a) = 23616 / 343 := by
    dsimp [f₂, r]
    exact aux_gaussianWeightMoment_square_tsum
  have hproduct₂₀ := aux_gaussianWeightMoment_finTwo_tsum_product
    hf₂nonneg hf₀nonneg hf₂ hf₀
  have hproduct₀₂ := aux_gaussianWeightMoment_finTwo_tsum_product
    hf₀nonneg hf₂nonneg hf₀ hf₂
  calc
    (∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
        (1 + (aux_natPairWeight m : ℝ)) ^ (2 : ℕ)) ≤
        ∑' m : Fin 2 → ℕ, r ^ (m 0 + m 1) *
          (1 + ((m 0 + m 1 : ℕ) : ℝ)) ^ (2 : ℕ) := hsum
    _ ≤ ∑' m : Fin 2 → ℕ,
        2 * (f₂ (m 0) * f₀ (m 1) + f₀ (m 0) * f₂ (m 1)) :=
      Summable.tsum_le_tsum hmajorantPoint hmajorant hprod
    _ = 2 * ((∑' m : Fin 2 → ℕ, f₂ (m 0) * f₀ (m 1)) +
        ∑' m : Fin 2 → ℕ, f₀ (m 0) * f₂ (m 1)) := by
      rw [tsum_mul_left]
      rw [Summable.tsum_add
        (aux_summable_finTwo_product hf₂nonneg hf₀nonneg hf₂ hf₀)
        (aux_summable_finTwo_product hf₀nonneg hf₂nonneg hf₀ hf₂)]
    _ = 2 * ((∑' a : ℕ, f₂ a) * (∑' a : ℕ, f₀ a) +
        (∑' a : ℕ, f₀ a) * (∑' a : ℕ, f₂ a)) := by
      rw [← hproduct₂₀, ← hproduct₀₂]
    _ ≤ (2 : ℝ) ^ (10 : ℕ) := by
      rw [h₀, h₂]
      norm_num

theorem aux_dyadic_gaussian_term_measurable
    (p : SequencePair) (hp : ∀ r : Fin 2, SpacedSequence (p r))
    (u : Fin 2) (j : ℤ) (m : Fin 2 → ℕ) :
    Measurable (fun v : RealPlane =>
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v) := by
  have hq (r : Fin 2) : 0 < (2 : ℝ) ^ (m r) * p r j :=
    mul_pos (pow_pos (by norm_num) _) (aux_spacedSequence_pos (hp r) j)
  have hmem := aux_twoDimensionalGaussian_memW0
    (fun r => (2 : ℝ) ^ (m r) * p r j) u hq
  simpa [aux_dominatingGaussianTerm] using
    (hmem.aux_continuous.const_mul (aux_gaussianDominationWeight m)).measurable

theorem aux_dyadic_gaussian_term_integrable
    (p : SequencePair) (hp : ∀ r : Fin 2, SpacedSequence (p r))
    (u : Fin 2) (j : ℤ) (m : Fin 2 → ℕ) :
    Integrable (fun v : RealPlane =>
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v) := by
  have hq (r : Fin 2) : 0 < (2 : ℝ) ^ (m r) * p r j :=
    mul_pos (pow_pos (by norm_num) _) (aux_spacedSequence_pos (hp r) j)
  have hmem := aux_twoDimensionalGaussian_memW0
    (fun r => (2 : ℝ) ^ (m r) * p r j) u hq
  have hint : Integrable (twoDimensionalGaussian
      (fun r => (2 : ℝ) ^ (m r) * p r j) u) :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hmem
  simpa [aux_dominatingGaussianTerm] using
    hint.const_mul (aux_gaussianDominationWeight m)

theorem aux_integral_dyadic_gaussian_term
    (p : SequencePair) (hp : ∀ r : Fin 2, SpacedSequence (p r))
    (u : Fin 2) (j : ℤ) (m : Fin 2 → ℕ) :
    (∫ v : RealPlane,
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v) =
      aux_gaussianDominationWeight m := by
  have hq (r : Fin 2) : 0 < (2 : ℝ) ^ (m r) * p r j :=
    mul_pos (pow_pos (by norm_num) _) (aux_spacedSequence_pos (hp r) j)
  rw [integral_const_mul]
  simpa [aux_dominatingGaussianTerm] using
    congrArg (fun z : ℝ => aux_gaussianDominationWeight m * z)
      (aux_integral_twoDimensionalGaussian
        (fun r => (2 : ℝ) ^ (m r) * p r j) u hq)

theorem aux_integrable_tsum_of_nonneg
    {ι α : Type*} [Countable ι] [MeasurableSpace α] {μ : Measure α}
    (f : ι → α → ℝ)
    (hmeas : ∀ k, Measurable (f k))
    (hnonneg : ∀ k x, 0 ≤ f k x)
    (hsum : ∀ x, Summable (fun k => f k x))
    (hint : ∀ k, Integrable (f k) μ)
    (hintsum : Summable (fun k => ∫ x, f k x ∂μ)) :
    Integrable (fun x => ∑' k, f k x) μ := by
  refine ⟨(Measurable.tsum hmeas).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    ∫⁻ x, ENNReal.ofReal ‖∑' k, f k x‖ ∂μ =
        ∫⁻ x, ∑' k, ENNReal.ofReal (f k x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun k => hnonneg k x)]
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hnonneg k x) (hsum x)]
    _ = ∑' k, ∫⁻ x, ENNReal.ofReal (f k x) ∂μ :=
      lintegral_tsum fun k => (hmeas k).aemeasurable.ennreal_ofReal
    _ = ∑' k, ENNReal.ofReal (∫ x, f k x ∂μ) := by
      apply tsum_congr
      intro k
      exact (ofReal_integral_eq_lintegral_ofReal (hint k)
        (ae_of_all _ fun x => hnonneg k x)).symm
    _ < ∞ := hintsum.tsum_ofReal_lt_top

theorem aux_finite_dyadic_gaussian_series_integrable
    (B : Finset ℕ) (p : ℕ → SequencePair)
    (hp : ∀ b ∈ B, ∀ r : Fin 2, SpacedSequence (p b r))
    (u : ℕ → Fin 2) (j : ℤ) :
    Integrable (fun v : RealPlane =>
      ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
        ∑ b ∈ B, aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p b r k) (u b) j v) := by
  classical
  let F : (Fin 2 → ℕ) → RealPlane → ℝ := fun m v =>
    ∑ b ∈ B, aux_gaussianDominationWeight m *
      aux_dominatingGaussianTerm
        (fun r k => (2 : ℝ) ^ (m r) * p b r k) (u b) j v
  have hmeas (m : Fin 2 → ℕ) : Measurable (F m) := by
    apply Finset.measurable_sum
    intro b hb
    exact aux_dyadic_gaussian_term_measurable (p b) (hp b hb) (u b) j m
  have hnonneg (m : Fin 2 → ℕ) (v : RealPlane) : 0 ≤ F m v := by
    apply Finset.sum_nonneg
    intro b hb
    apply mul_nonneg (aux_gaussianDominationWeight_nonneg m)
    apply aux_twoDimensionalGaussian_nonneg
    intro r
    exact mul_pos (pow_pos (by norm_num) _)
      (aux_spacedSequence_pos (hp b hb r) j)
  have hsum (v : RealPlane) : Summable (fun m : Fin 2 → ℕ => F m v) := by
    simpa [F, Finset.mul_sum] using
      aux_finite_dyadic_gaussian_series_summable B p hp u j v
  have hint (m : Fin 2 → ℕ) : Integrable (F m) := by
    dsimp [F]
    apply integrable_finsetSum
    intro b hb
    exact aux_dyadic_gaussian_term_integrable (p b) (hp b hb) (u b) j m
  have hFint (m : Fin 2 → ℕ) :
      (∫ v : RealPlane, F m v) = (B.card : ℝ) * aux_gaussianDominationWeight m := by
    dsimp [F]
    rw [integral_finsetSum]
    · calc
        ∑ b ∈ B, ∫ v : RealPlane,
            aux_gaussianDominationWeight m *
              aux_dominatingGaussianTerm
                (fun r k => (2 : ℝ) ^ (m r) * p b r k) (u b) j v =
            ∑ b ∈ B, aux_gaussianDominationWeight m := by
              apply Finset.sum_congr rfl
              intro b hb
              exact aux_integral_dyadic_gaussian_term (p b) (hp b hb) (u b) j m
        _ = (B.card : ℝ) * aux_gaussianDominationWeight m := by
          simp [nsmul_eq_mul]
    · intro b hb
      exact aux_dyadic_gaussian_term_integrable (p b) (hp b hb) (u b) j m
  have hintsum : Summable (fun m : Fin 2 → ℕ => ∫ v : RealPlane, F m v) := by
    refine (aux_gaussianDominationWeight_summable.mul_left (B.card : ℝ)).congr ?_
    intro m
    exact (hFint m).symm
  have hmain := aux_integrable_tsum_of_nonneg F hmeas hnonneg hsum hint hintsum
  have hfun :
      (fun v : RealPlane => ∑' m : Fin 2 → ℕ, F m v) =
        (fun v : RealPlane => ∑' m : Fin 2 → ℕ,
          aux_gaussianDominationWeight m *
            ∑ b ∈ B, aux_dominatingGaussianTerm
              (fun r k => (2 : ℝ) ^ (m r) * p b r k) (u b) j v) := by
    funext v
    apply tsum_congr
    intro m
    dsimp [F]
    rw [Finset.mul_sum]
  rw [← hfun]
  exact hmain

/-- Wrapper in the exact `aux_GaussianDominationWitness.scales` shape: the scale pair at
`m` is obtained from a fixed base pair by coordinatewise dyadic dilation. -/
theorem aux_finite_dyadic_gaussian_series_summable_of_scales
    (B : Finset ℕ) (p : ℕ → SequencePair)
    (hp : ∀ b ∈ B, ∀ r : Fin 2, SpacedSequence (p b r))
    (u : ℕ → Fin 2) (scales : ℕ → (Fin 2 → ℕ) → SequencePair)
    (hscales : ∀ b ∈ B, ∀ m r k,
      scales b m r k = (2 : ℝ) ^ (m r) * p b r k)
    (j : ℤ) (v : RealPlane) :
    Summable (fun m : Fin 2 → ℕ =>
      aux_gaussianDominationWeight m *
        ∑ b ∈ B, aux_dominatingGaussianTerm (scales b m) (u b) j v) := by
  have hbase := aux_finite_dyadic_gaussian_series_summable B p hp u j v
  convert hbase using 1
  funext m
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  congr 2
  funext r k
  exact hscales b hb m r k

theorem aux_finite_dyadic_gaussian_series_integrable_of_scales
    (B : Finset ℕ) (p : ℕ → SequencePair)
    (hp : ∀ b ∈ B, ∀ r : Fin 2, SpacedSequence (p b r))
    (u : ℕ → Fin 2) (scales : ℕ → (Fin 2 → ℕ) → SequencePair)
    (hscales : ∀ b ∈ B, ∀ m r k,
      scales b m r k = (2 : ℝ) ^ (m r) * p b r k)
    (j : ℤ) :
    Integrable (fun v : RealPlane => ∑' m : Fin 2 → ℕ,
      aux_gaussianDominationWeight m *
        ∑ b ∈ B, aux_dominatingGaussianTerm (scales b m) (u b) j v) := by
  have hbase := aux_finite_dyadic_gaussian_series_integrable B p hp u j
  have hfun :
      (fun v : RealPlane => ∑' m : Fin 2 → ℕ,
        aux_gaussianDominationWeight m *
          ∑ b ∈ B, aux_dominatingGaussianTerm (scales b m) (u b) j v) =
        (fun v : RealPlane => ∑' m : Fin 2 → ℕ,
          aux_gaussianDominationWeight m *
            ∑ b ∈ B, aux_dominatingGaussianTerm
              (fun r k => (2 : ℝ) ^ (m r) * p b r k) (u b) j v) := by
    funext v
    apply tsum_congr
    intro m
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    congr 2
    funext r k
    exact hscales b hb m r k
  rw [hfun]
  exact hbase

/-- The two analytic tail fields of a Gaussian-domination witness, for any finite family of
base scale pairs and their coordinatewise dyadic dilates. -/
theorem aux_finite_dyadic_gaussian_series
    (B : Finset ℕ) (p : ℕ → SequencePair)
    (hp : ∀ b ∈ B, ∀ r : Fin 2, SpacedSequence (p b r))
    (u : ℕ → Fin 2) (scales : ℕ → (Fin 2 → ℕ) → SequencePair)
    (hscales : ∀ b ∈ B, ∀ m r k,
      scales b m r k = (2 : ℝ) ^ (m r) * p b r k) :
    (∀ j : ℤ, ∀ v : RealPlane,
      Summable (fun m : Fin 2 → ℕ =>
        aux_gaussianDominationWeight m *
          ∑ b ∈ B, aux_dominatingGaussianTerm (scales b m) (u b) j v)) ∧
    (∀ j : ℤ, Integrable (fun v : RealPlane => ∑' m : Fin 2 → ℕ,
      aux_gaussianDominationWeight m *
        ∑ b ∈ B, aux_dominatingGaussianTerm (scales b m) (u b) j v)) := by
  constructor
  · intro j v
    exact aux_finite_dyadic_gaussian_series_summable_of_scales
      B p hp u scales hscales j v
  · intro j
    exact aux_finite_dyadic_gaussian_series_integrable_of_scales
      B p hp u scales hscales j

/-- Coordinatewise dyadic dilation preserves membership in the spaced-sequence class. -/
theorem aux_dyadic_scales_in_A
    (B : Finset ℕ) (p : ℕ → SequencePair)
    (hp : ∀ b ∈ B, ∀ r : Fin 2, SpacedSequence (p b r)) :
    ∀ b ∈ B, ∀ m : Fin 2 → ℕ, ∀ r : Fin 2,
      SpacedSequence (fun k => (2 : ℝ) ^ (m r) * p b r k) := by
  intro b hb m r
  exact smul_mem_A (hp b hb r) (pow_pos (by norm_num) _)

/-- In the orientation-one case the kernel sees `√2 * p`; this only improves
the real bracket profile. -/
private theorem aux_caseOne_m1_sqrt_arg_le (N t p : ℝ)
    (hN : 0 ≤ N) (ht : 0 < t) :
    scaledBracketBumpReal N t (Real.sqrt 2 * p) ≤
      scaledBracketBumpReal N t p := by
  have hsqrt0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrt1 : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hbase : 1 + |t⁻¹ * p| ≤ 1 + |t⁻¹ * (Real.sqrt 2 * p)| := by
    rw [abs_mul, abs_mul, abs_mul, abs_inv, abs_of_pos ht,
      abs_of_nonneg hsqrt0]
    gcongr
    simpa using mul_le_mul_of_nonneg_right hsqrt1 (abs_nonneg p)
  unfold scaledBracketBumpReal
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  · exact inv_nonneg.mpr ht.le

/-- Exact simultaneous rescaling used to express the first M₁ coordinate in
the formal `W 1` coordinates. -/
private theorem aux_caseOne_m1_simul_rescale (N c s x : ℝ) (hc : 0 < c) :
    c * scaledBracketBumpReal N (c * s) (c * x) =
      scaledBracketBumpReal N s x := by
  unfold scaledBracketBumpReal
  have hcne : c ≠ 0 := ne_of_gt hc
  have harg : (c * s)⁻¹ * (c * x) = s⁻¹ * x := by
    field_simp [hcne]
  have hinv : c * (c * s)⁻¹ = s⁻¹ := by
    field_simp [hcne]
  rw [harg]
  calc
    c * ((c * s)⁻¹ * (1 + |s⁻¹ * x|).rpow (-N)) =
        (c * (c * s)⁻¹) * (1 + |s⁻¹ * x|).rpow (-N) := by ring
    _ = s⁻¹ * (1 + |s⁻¹ * x|).rpow (-N) := by rw [hinv]

private theorem aux_caseOne_m1_le_inv (N s x : ℝ) (hN : 0 ≤ N) (hs : 0 < s) :
    scaledBracketBumpReal N s x ≤ s⁻¹ := by
  unfold scaledBracketBumpReal
  have hbase : 1 ≤ 1 + |s⁻¹ * x| := by linarith [abs_nonneg (s⁻¹ * x)]
  have hpow : Real.rpow (1 + |s⁻¹ * x|) (-N) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  calc
    s⁻¹ * Real.rpow (1 + |s⁻¹ * x|) (-N) ≤ s⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hs.le)
    _ = s⁻¹ := by ring

private theorem aux_caseOne_m1_product_integrable
    (a s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) :
    Integrable (fun p : ℝ =>
      scaledBracketBumpReal (3 / 2 : ℝ) s₀ (a + p) *
        scaledBracketBumpReal (3 / 2 : ℝ) s₁ p) := by
  have hbase : Integrable (fun p : ℝ => scaledBracketBumpReal (3 / 2 : ℝ) s₁ p) :=
    aux_integrable_scaledBracketBumpReal (3 / 2 : ℝ) s₁ (by norm_num) hs₁
  refine (hbase.const_mul s₀⁻¹).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hleftBase : Continuous (fun p : ℝ => 1 + |s₀⁻¹ * (a + p)|) := by fun_prop
    have hrightBase : Continuous (fun p : ℝ => 1 + |s₁⁻¹ * p|) := by fun_prop
    have hleft : Continuous (fun p : ℝ =>
        scaledBracketBumpReal (3 / 2 : ℝ) s₀ (a + p)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact hleftBase.continuousAt.rpow_const (Or.inl (by positivity))
    have hright : Continuous (fun p : ℝ =>
        scaledBracketBumpReal (3 / 2 : ℝ) s₁ p) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact hrightBase.continuousAt.rpow_const (Or.inl (by positivity))
    exact hleft.mul hright
  · filter_upwards [] with p
    have hleft : 0 ≤ scaledBracketBumpReal (3 / 2 : ℝ) s₀ (a + p) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hs₀
    have hright : 0 ≤ scaledBracketBumpReal (3 / 2 : ℝ) s₁ p :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hs₁
    have hle := aux_caseOne_m1_le_inv (3 / 2 : ℝ) s₀ (a + p) (by norm_num) hs₀
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft hright)]
    calc
      scaledBracketBumpReal (3 / 2 : ℝ) s₀ (a + p) *
          scaledBracketBumpReal (3 / 2 : ℝ) s₁ p ≤
        s₀⁻¹ * scaledBracketBumpReal (3 / 2 : ℝ) s₁ p := by
          nlinarith [mul_le_mul_of_nonneg_right hle hright]

/-- The single orientation-one occurrence in the positive-horizontal case is
controlled by its M₁ term in exact `W 1` coordinates.  The factor `2` only
absorbs `√2 ≤ 2`; the output scale pair is `(√2 * λ, t₁)`. -/
private theorem aux_caseOne_m1_orientation_one (w₀ w₁ lam t₀ t₁ : ℝ)
    (hlam : 0 < lam) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁) (ht₀lam : t₀ ≤ lam) :
    (∫ p : ℝ,
      (scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
          scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)) ≤
      2 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w₀) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₁ (Real.sqrt 2 * w₁) := by
  let A₀ : ℝ := scaledBracketBumpReal (3 / 2 : ℝ) lam w₀
  let D : ℝ := scaledBracketBumpReal (3 / 2 : ℝ) t₁ (Real.sqrt 2 * w₁)
  let f : ℝ → ℝ := fun p =>
    (scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
        scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)
  let g₀ : ℝ → ℝ := fun p => A₀ * scaledBracketBumpReal (3 / 2 : ℝ) t₀ p
  let g₁ : ℝ → ℝ := fun p =>
    scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ p
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_le_two : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hCtwo : 0 ≤ C_twoBumpEstimate (3 / 2) (3 / 2) := by
    unfold C_twoBumpEstimate
    norm_num
    positivity
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    exact aux_scaledBracketBumpReal_nonneg _ _ _ hlam
  have hD : 0 ≤ D := by
    dsimp [D]
    exact aux_scaledBracketBumpReal_nonneg _ _ _ ht₁
  have hg₀ : Integrable g₀ := by
    have hbase := aux_integrable_scaledBracketBumpReal (3 / 2 : ℝ) t₀ (by norm_num) ht₀
    simpa [g₀] using hbase.const_mul A₀
  have hg₁ : Integrable g₁ := by
    simpa [g₁] using aux_caseOne_m1_product_integrable w₀ lam t₀ hlam ht₀
  have hfnon (p : ℝ) : 0 ≤ f p := by
    dsimp [f]
    apply mul_nonneg
    · apply mul_nonneg
      · apply add_nonneg <;> apply aux_scaledBracketBumpReal_nonneg <;> exact hlam
      · exact aux_scaledBracketBumpReal_nonneg _ _ _ ht₀
    · exact aux_scaledBracketBumpReal_nonneg _ _ _ ht₁
  have hpoint (p : ℝ) : f p ≤ D * (g₀ p + g₁ p) := by
    have hfirst₀ : scaledBracketBumpReal 2 lam w₀ ≤
        scaledBracketBumpReal (3 / 2 : ℝ) lam w₀ :=
      aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 lam w₀ hlam (by norm_num)
    have hfirst₁ : scaledBracketBumpReal 2 lam (w₀ + p) ≤
        scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p) :=
      aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 lam (w₀ + p) hlam (by norm_num)
    have hsecond : scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) ≤
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ p :=
      aux_caseOne_m1_sqrt_arg_le (3 / 2 : ℝ) t₀ p (by norm_num) ht₀
    have hthird : scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) ≤ D := by
      dsimp [D]
      exact aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 t₁
        (Real.sqrt 2 * w₁) ht₁ (by norm_num)
    have hsum : scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p) ≤
        A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p) := by
      dsimp [A₀]
      exact add_le_add hfirst₀ hfirst₁
    have hsumNonneg : 0 ≤ A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p) :=
      add_nonneg hA₀ (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
    have hsecondNonneg : 0 ≤ scaledBracketBumpReal (3 / 2 : ℝ) t₀
        (Real.sqrt 2 * p) := aux_scaledBracketBumpReal_nonneg _ _ _ ht₀
    have hthirdNonneg : 0 ≤ scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ ht₁
    dsimp [f, g₀, g₁]
    calc
      (scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
            scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) ≤
          (A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p)) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
              scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsum hsecondNonneg) hthirdNonneg
      _ ≤ (A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p)) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ p *
              scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsecond hsumNonneg) hthirdNonneg
      _ ≤ (A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p)) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ p * D := by
            exact mul_le_mul_of_nonneg_left hthird
              (mul_nonneg hsumNonneg
                (aux_scaledBracketBumpReal_nonneg _ _ _ ht₀))
      _ = D * (g₀ p + g₁ p) := by ring
  have hmajor : Integrable (fun p : ℝ => D * (g₀ p + g₁ p)) :=
    (hg₀.add hg₁).const_mul D
  have hint : (∫ p : ℝ, f p) ≤ ∫ p : ℝ, D * (g₀ p + g₁ p) :=
    integral_mono_of_nonneg (ae_of_all _ hfnon) hmajor (ae_of_all _ hpoint)
  have hmass : (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t₀ p) = 4 := by
    have h := aux_integral_scaledBracketBumpReal_eq (3 / 2 : ℝ) t₀ 0 (by norm_num) ht₀
    calc
      (∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) t₀ p) =
          2 / ((3 / 2 : ℝ) - 1) := by
            simpa [aux_scaledBracketBumpReal_neg] using h
      _ = 4 := by norm_num
  have hg₀val : (∫ p : ℝ, g₀ p) = A₀ * 4 := by
    dsimp [g₀]
    rw [integral_const_mul, hmass]
  have hg₁non (p : ℝ) : 0 ≤ g₁ p := by
    dsimp [g₁]
    exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
      (aux_scaledBracketBumpReal_nonneg _ _ _ ht₀)
  have htwoRaw := twoBumpEstimate (-w₀) 0 lam t₀ (3 / 2 : ℝ) (3 / 2 : ℝ)
    hlam ht₀ ht₀lam (by norm_num) (by norm_num)
  have hg₁bound : (∫ p : ℝ, g₁ p) ≤
      C_twoBumpEstimate (3 / 2) (3 / 2) * A₀ := by
    rw [← abs_of_nonneg (integral_nonneg hg₁non)]
    calc
      |∫ p : ℝ, g₁ p| =
          |∫ p : ℝ, scaledBracketBumpReal (3 / 2 : ℝ) lam ((-w₀) - p) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ (0 - p)| := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with p
            dsimp [g₁]
            rw [show (-w₀) - p = -(w₀ + p) by ring,
              show 0 - p = -p by ring,
              aux_scaledBracketBumpReal_neg, aux_scaledBracketBumpReal_neg]
      _ ≤ C_twoBumpEstimate (3 / 2) (3 / 2) *
          scaledBracketBumpReal (min (3 / 2 : ℝ) (3 / 2 : ℝ)) lam ((-w₀) - 0) := htwoRaw
      _ = C_twoBumpEstimate (3 / 2) (3 / 2) * A₀ := by
        dsimp [A₀]
        rw [min_self, show -w₀ - 0 = -w₀ by ring, aux_scaledBracketBumpReal_neg]
  have hraw : (∫ p : ℝ, f p) ≤
      (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) * A₀ * D := by
    calc
      (∫ p : ℝ, f p) ≤ ∫ p : ℝ, D * (g₀ p + g₁ p) := hint
      _ = D * ((∫ p : ℝ, g₀ p) + ∫ p : ℝ, g₁ p) := by
        rw [integral_const_mul, integral_add hg₀ hg₁]
      _ ≤ D * (A₀ * 4 + C_twoBumpEstimate (3 / 2) (3 / 2) * A₀) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_of_eq hg₀val) hg₁bound) hD
      _ = (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) * A₀ * D := by ring
  have hres := aux_caseOne_m1_simul_rescale (3 / 2 : ℝ) (Real.sqrt 2) lam w₀ hsqrt
  have hcore : 0 ≤ (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) *
      scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w₀) * D := by
    apply mul_nonneg
    · apply mul_nonneg
      · linarith
      · exact aux_scaledBracketBumpReal_nonneg _ _ _ (mul_pos hsqrt hlam)
    · exact hD
  change (∫ p : ℝ, f p) ≤ _
  calc
    (∫ p : ℝ, f p) ≤ (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) * A₀ * D := hraw
    _ = Real.sqrt 2 * ((C_twoBumpEstimate (3 / 2) (3 / 2) + 4) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w₀) * D) := by
      dsimp [A₀]
      rw [← hres]
      ring
    _ ≤ 2 * ((C_twoBumpEstimate (3 / 2) (3 / 2) + 4) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w₀) * D) :=
      mul_le_mul_of_nonneg_right hsqrt_le_two hcore
    _ = 2 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w₀) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₁ (Real.sqrt 2 * w₁) := by
      dsimp [D]
      ring

/-- Pulls the `2π` in the positive rho estimate outside the minimum. -/
private theorem aux_caseOne_m1_move_twoPi_out {A lambda y B : ℝ}
    (hA : 0 ≤ A) (hlambda : 0 < lambda) (hB : 0 ≤ B) :
    A * min 1 (2 * Real.pi * lambda⁻¹ * |y|) * B ≤
      (2 * Real.pi * A) * min 1 (lambda⁻¹ * |y|) * B := by
  have hmin : min 1 (2 * Real.pi * (lambda⁻¹ * |y|)) ≤
      2 * Real.pi * min 1 (lambda⁻¹ * |y|) := by
    have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    by_cases h : 1 ≤ lambda⁻¹ * |y|
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by nlinarith)
    · have h' : lambda⁻¹ * |y| ≤ 1 := le_of_not_ge h
      rw [min_eq_right h']
      exact min_le_right _ _
  calc
    A * min 1 (2 * Real.pi * lambda⁻¹ * |y|) * B =
        A * min 1 (2 * Real.pi * (lambda⁻¹ * |y|)) * B := by ring
    _ ≤ A * (2 * Real.pi * min 1 (lambda⁻¹ * |y|)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hA) hB
    _ = (2 * Real.pi * A) * min 1 (lambda⁻¹ * |y|) * B := by ring

/-- A scale in the H-kernel distance ball is smaller than the positive-band
N scale by the required dyadic factor. -/
private theorem aux_caseOne_m1_distanceBall_scale_ratio_le {a b : ℤ → ℝ}
    (ha : SpacedSequence a) {d : ℕ} (hb : b ∈ sequenceDistanceBall a (d : WithTop ℕ))
    (h j : ℤ) :
    b j / ((2 : ℝ) ^ h * a (j + (d : ℤ))) ≤ (2 : ℝ) ^ (-h) := by
  rcases hb with ⟨_, hdist⟩
  have hwithin : WithinSequenceDistance a b d :=
    aux_withinSequenceDistance_of_sequenceDistance_le ha hdist
  have hbj : b j ≤ a (j + (d : ℤ)) := by
    simpa using (hwithin j).2
  have hden : 0 < (2 : ℝ) ^ h * a (j + (d : ℤ)) :=
    mul_pos (zpow_pos (by norm_num) _) (ha _).1
  apply (div_le_iff₀ hden).2
  calc
    b j ≤ a (j + (d : ℤ)) := hbj
    _ = ((2 : ℝ) ^ (-h) * (2 : ℝ) ^ h) * a (j + (d : ℤ)) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero, one_mul]
    _ = (2 : ℝ) ^ (-h) * ((2 : ℝ) ^ h * a (j + (d : ℤ))) := by ring

/-- The square-root loss converts the second-order H bump into the `3/2` bump
needed by the M₁ integral theorem. -/
private theorem aux_caseOne_m1_two_sqrt_eq_threeHalves (t x : ℝ) (ht : 0 < t) :
    Real.rpow (1 + t⁻¹ * |x|) (1 / 2 : ℝ) * scaledBracketBump 2 t x =
      scaledBracketBumpReal (3 / 2 : ℝ) t x := by
  let z : ℝ := 1 + t⁻¹ * |x|
  have hz : 0 < z := by
    dsimp [z]
    positivity
  have habs : |t⁻¹ * x| = t⁻¹ * |x| := by
    rw [abs_mul, abs_inv, abs_of_pos ht]
  have hnegTwo : z⁻¹ ^ (2 : ℕ) = Real.rpow z (-2 : ℝ) := by
    calc
      z⁻¹ ^ (2 : ℕ) = (z ^ (2 : ℕ))⁻¹ := by rw [inv_pow]
      _ = (Real.rpow z (2 : ℝ))⁻¹ := by
        congr 1
        exact (Real.rpow_natCast z 2).symm
      _ = Real.rpow z (-2 : ℝ) := (Real.rpow_neg hz.le 2).symm
  unfold scaledBracketBump scaledBracketBumpReal
  rw [habs]
  change Real.rpow z (1 / 2 : ℝ) * (t⁻¹ * z⁻¹ ^ (2 : ℕ)) =
    t⁻¹ * Real.rpow z (-(3 / 2 : ℝ))
  rw [hnegTwo]
  calc
    Real.rpow z (1 / 2 : ℝ) * (t⁻¹ * Real.rpow z (-2 : ℝ)) =
        t⁻¹ * (Real.rpow z (1 / 2 : ℝ) * Real.rpow z (-2 : ℝ)) := by ring
    _ = t⁻¹ * Real.rpow z ((1 / 2 : ℝ) + (-2 : ℝ)) := by
      have hsum : Real.rpow z ((1 / 2 : ℝ) + (-2 : ℝ)) =
          Real.rpow z (1 / 2 : ℝ) * Real.rpow z (-2 : ℝ) :=
        Real.rpow_add hz _ _
      exact congrArg (fun r : ℝ => t⁻¹ * r) hsum.symm
    _ = t⁻¹ * Real.rpow z (-(3 / 2 : ℝ)) := by ring_nf

private theorem aux_caseOne_m1_min_scale_half_le {t lam : ℝ} {h : ℕ}
    (ht : 0 < t) (hlam : 0 < lam)
    (hscale : t / lam ≤ Real.rpow 2 (-(h : ℝ))) (p : ℝ) :
    min 1 (lam⁻¹ * |p|) ≤ Real.rpow 2 (-((h : ℝ) / 2)) *
      Real.sqrt (1 + t⁻¹ * |p|) := by
  let a : ℝ := lam⁻¹ * |p|
  let b : ℝ := t⁻¹ * |p|
  let c : ℝ := Real.rpow 2 (-(h : ℝ))
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    exact Real.rpow_nonneg (by norm_num) _
  have hab : a ≤ c * b := by
    have hid : a = (t / lam) * b := by
      dsimp [a, b]
      field_simp [ne_of_gt ht, ne_of_gt hlam]
    rw [hid]
    exact mul_le_mul_of_nonneg_right hscale hb
  have hmin : min 1 a ≤ Real.sqrt a := by
    by_cases haone : a ≤ 1
    · rw [min_eq_right haone]
      exact (Real.le_sqrt_self_iff).2 haone
    · rw [min_eq_left (le_of_not_ge haone)]
      exact (Real.one_le_sqrt).2 (le_of_not_ge haone)
  have hsqrt : Real.sqrt a ≤ Real.sqrt c * Real.sqrt (1 + b) := by
    calc
      Real.sqrt a ≤ Real.sqrt (c * b) := Real.sqrt_le_sqrt hab
      _ = Real.sqrt c * Real.sqrt b := Real.sqrt_mul hc _
      _ ≤ Real.sqrt c * Real.sqrt (1 + b) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  have hroot : Real.sqrt c = Real.rpow 2 (-((h : ℝ) / 2)) := by
    dsimp [c]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simpa [a, b, hroot] using hmin.trans hsqrt

/-- Combines the loss based on `p` with the orientation-one H bump, whose first
coordinate is `√2 p`. -/
private theorem aux_caseOne_m1_sqrt_loss_bump (t p : ℝ) (ht : 0 < t) :
    Real.sqrt (1 + t⁻¹ * |p|) * scaledBracketBump 2 t (-Real.sqrt 2 * p) ≤
      scaledBracketBumpReal (3 / 2 : ℝ) t (Real.sqrt 2 * p) := by
  have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_one : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hbase : 1 + t⁻¹ * |p| ≤ 1 + t⁻¹ * |Real.sqrt 2 * p| := by
    rw [abs_mul, abs_of_nonneg hsqrt]
    gcongr
    simpa using mul_le_mul_of_nonneg_right hsqrt_one (abs_nonneg p)
  have hroot : Real.sqrt (1 + t⁻¹ * |p|) ≤
      Real.sqrt (1 + t⁻¹ * |Real.sqrt 2 * p|) :=
    Real.sqrt_le_sqrt hbase
  have hB : 0 ≤ scaledBracketBump 2 t (-Real.sqrt 2 * p) :=
    aux_scaledBracketBump_nonneg 2 ht _
  have hneg : scaledBracketBump 2 t (-Real.sqrt 2 * p) =
      scaledBracketBump 2 t (Real.sqrt 2 * p) := by
    unfold scaledBracketBump
    rw [show t⁻¹ * (-Real.sqrt 2 * p) = -(t⁻¹ * (Real.sqrt 2 * p)) by ring,
      abs_neg]
  calc
    Real.sqrt (1 + t⁻¹ * |p|) * scaledBracketBump 2 t (-Real.sqrt 2 * p) ≤
        Real.sqrt (1 + t⁻¹ * |Real.sqrt 2 * p|) *
          scaledBracketBump 2 t (-Real.sqrt 2 * p) :=
      mul_le_mul_of_nonneg_right hroot hB
    _ = Real.sqrt (1 + t⁻¹ * |Real.sqrt 2 * p|) *
          scaledBracketBump 2 t (Real.sqrt 2 * p) := by rw [hneg]
    _ = scaledBracketBumpReal (3 / 2 : ℝ) t (Real.sqrt 2 * p) := by
      have hpow : Real.sqrt (1 + t⁻¹ * |Real.sqrt 2 * p|) =
          Real.rpow (1 + t⁻¹ * |Real.sqrt 2 * p|) (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        rfl
      rw [hpow]
      exact aux_caseOne_m1_two_sqrt_eq_threeHalves t (Real.sqrt 2 * p) ht

private theorem aux_caseOne_m1_integrand_integrable (w₀ w₁ lam t₀ t₁ : ℝ)
    (hlam : 0 < lam) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁) :
    Integrable (fun p : ℝ =>
      (scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
          scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)) := by
  let A₀ : ℝ := scaledBracketBumpReal (3 / 2 : ℝ) lam w₀
  let D : ℝ := scaledBracketBumpReal (3 / 2 : ℝ) t₁ (Real.sqrt 2 * w₁)
  let f : ℝ → ℝ := fun p =>
    (scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
        scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)
  let g₀ : ℝ → ℝ := fun p => A₀ * scaledBracketBumpReal (3 / 2 : ℝ) t₀ p
  let g₁ : ℝ → ℝ := fun p =>
    scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p) *
      scaledBracketBumpReal (3 / 2 : ℝ) t₀ p
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    exact aux_scaledBracketBumpReal_nonneg _ _ _ hlam
  have hD : 0 ≤ D := by
    dsimp [D]
    exact aux_scaledBracketBumpReal_nonneg _ _ _ ht₁
  have hg₀ : Integrable g₀ := by
    have hbase := aux_integrable_scaledBracketBumpReal (3 / 2 : ℝ) t₀ (by norm_num) ht₀
    simpa [g₀] using hbase.const_mul A₀
  have hg₁ : Integrable g₁ := by
    simpa [g₁] using aux_caseOne_m1_product_integrable w₀ lam t₀ hlam ht₀
  have hmajor : Integrable (fun p : ℝ => D * (g₀ p + g₁ p)) :=
    (hg₀.add hg₁).const_mul D
  refine hmajor.mono_nonneg ?_ (ae_of_all _ ?_) (ae_of_all _ ?_)
  · apply Continuous.aestronglyMeasurable
    have hfirstBase : Continuous (fun p : ℝ => 1 + |lam⁻¹ * (w₀ + p)|) := by fun_prop
    have hsecondBase : Continuous (fun p : ℝ => 1 + |t₀⁻¹ * (Real.sqrt 2 * p)|) := by
      fun_prop
    have hfirst : Continuous (fun p : ℝ =>
        scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) := by
      have hconst : Continuous (fun _ : ℝ => scaledBracketBumpReal 2 lam w₀) := continuous_const
      have hvar : Continuous (fun p : ℝ => scaledBracketBumpReal 2 lam (w₀ + p)) := by
        unfold scaledBracketBumpReal
        apply continuous_const.mul
        rw [continuous_iff_continuousAt]
        intro p
        exact hfirstBase.continuousAt.rpow_const (Or.inl (by positivity))
      exact hconst.add hvar
    have hsecond : Continuous (fun p : ℝ =>
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact hsecondBase.continuousAt.rpow_const (Or.inl (by positivity))
    exact (hfirst.mul hsecond).mul continuous_const
  · intro p
    apply mul_nonneg
    · apply mul_nonneg
      · apply add_nonneg <;> apply aux_scaledBracketBumpReal_nonneg <;> exact hlam
      · exact aux_scaledBracketBumpReal_nonneg _ _ _ ht₀
    · exact aux_scaledBracketBumpReal_nonneg _ _ _ ht₁
  · intro p
    have hfirst₀ : scaledBracketBumpReal 2 lam w₀ ≤
        scaledBracketBumpReal (3 / 2 : ℝ) lam w₀ :=
      aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 lam w₀ hlam (by norm_num)
    have hfirst₁ : scaledBracketBumpReal 2 lam (w₀ + p) ≤
        scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p) :=
      aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 lam (w₀ + p) hlam (by norm_num)
    have hsecond : scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) ≤
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ p :=
      aux_caseOne_m1_sqrt_arg_le (3 / 2 : ℝ) t₀ p (by norm_num) ht₀
    have hthird : scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) ≤ D := by
      dsimp [D]
      exact aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 t₁
        (Real.sqrt 2 * w₁) ht₁ (by norm_num)
    have hsum : scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p) ≤
        A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p) := by
      dsimp [A₀]
      exact add_le_add hfirst₀ hfirst₁
    have hsumNonneg : 0 ≤ A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p) :=
      add_nonneg hA₀ (aux_scaledBracketBumpReal_nonneg _ _ _ hlam)
    have hsecondNonneg : 0 ≤ scaledBracketBumpReal (3 / 2 : ℝ) t₀
        (Real.sqrt 2 * p) := aux_scaledBracketBumpReal_nonneg _ _ _ ht₀
    have hthirdNonneg : 0 ≤ scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ ht₁
    dsimp [f, g₀, g₁]
    calc
      (scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
            scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) ≤
          (A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p)) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
              scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsum hsecondNonneg) hthirdNonneg
      _ ≤ (A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p)) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ p *
              scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsecond hsumNonneg) hthirdNonneg
      _ ≤ (A₀ + scaledBracketBumpReal (3 / 2 : ℝ) lam (w₀ + p)) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ p * D := by
            exact mul_le_mul_of_nonneg_left hthird
              (mul_nonneg hsumNonneg
                (aux_scaledBracketBumpReal_nonneg _ _ _ ht₀))
      _ = D * (g₀ p + g₁ p) := by ring

private theorem aux_caseOne_m1_integral_le_of_pointwise
    (w₀ w₁ lam t₀ t₁ K : ℝ) (hlam : 0 < lam) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁)
    (ht₀lam : t₀ ≤ lam) (hK : 0 ≤ K) (f : ℝ → ℝ)
    (hfnon : ∀ p, 0 ≤ f p)
    (hpoint : ∀ p, f p ≤ K *
      ((scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
          scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁))) :
    (∫ p : ℝ, f p) ≤ K *
      (2 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) *
        scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w₀) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₁ (Real.sqrt 2 * w₁)) := by
  have hI := aux_caseOne_m1_integrand_integrable w₀ w₁ lam t₀ t₁ hlam ht₀ ht₁
  have hmajor : Integrable (fun p : ℝ => K *
      ((scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
          scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁))) := hI.const_mul K
  have hint : (∫ p : ℝ, f p) ≤ ∫ p : ℝ, K *
      ((scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
          scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)) :=
    integral_mono_of_nonneg (ae_of_all _ hfnon) hmajor (ae_of_all _ hpoint)
  have hM1 := aux_caseOne_m1_orientation_one w₀ w₁ lam t₀ t₁ hlam ht₀ ht₁ ht₀lam
  calc
    (∫ p : ℝ, f p) ≤ ∫ p : ℝ, K *
        ((scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
            scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)) := hint
    _ = K * ∫ p : ℝ,
        ((scaledBracketBumpReal 2 lam w₀ + scaledBracketBumpReal 2 lam (w₀ + p)) *
          scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
            scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)) := by
          rw [integral_const_mul]
    _ ≤ K *
        (2 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) *
          scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam) (Real.sqrt 2 * w₀) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₁ (Real.sqrt 2 * w₁)) :=
      mul_le_mul_of_nonneg_left hM1 hK

/-- The rho-difference estimate applied to one orientation-one H occurrence.
The supplied `hminloss` is exactly the scale-ratio consequence of membership in
the H-package distance ball; the conclusion is in the M₁ coordinates shared by
the five-slot case-one package. -/
private theorem aux_caseOne_m1_orientation_one_rho_occurrence {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 ≠ 0) (hpositive : 0 < ι.1.1)
    (q : SequencePair × Fin 2) (hq₀ : SpacedSequence (q.1 0))
    (hq₁ : SpacedSequence (q.1 1)) (hqu : q.2 = 1) (lambda r : ℝ)
    (hlambda : lambda = (2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ)))
    (hr : 0 ≤ r)
    (hminloss : ∀ p : ℝ, min 1 (lambda⁻¹ * |p|) ≤
      r * Real.sqrt (1 + (q.1 0 j)⁻¹ * |p|))
    (ht₀lambda : q.1 0 j ≤ lambda) (w₀ w₁ : ℝ) :
    (∫ p : ℝ,
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) ≤
      (4 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
        C_meanFourScaleGaussianKernel 2 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)) * r *
          (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lambda) (Real.sqrt 2 * w₀) *
            scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (Real.sqrt 2 * w₁)) := by
  let A : ℝ := C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2
  let t₀ : ℝ := q.1 0 j
  let t₁ : ℝ := q.1 1 j
  let K : ℝ := 2 * Real.pi * A * r
  have hlambda_pos : 0 < lambda := by
    rw [hlambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have ht₀ : 0 < t₀ := by simpa [t₀] using (hq₀ j).1
  have ht₁ : 0 < t₁ := by simpa [t₁] using (hq₁ j).1
  have hA : 0 ≤ A := by
    have hK : 0 ≤ C_meanValueBumpEstimate 2 := by
      unfold C_meanValueBumpEstimate
      positivity
    have hM : 0 ≤ aux_maxUpTo C_gaussianBumpEstimate 2 :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans
        (aux_le_maxUpTo C_gaussianBumpEstimate (Nat.zero_le _))
    have hT : 0 ≤ aux_maxUpTo
        (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) 2 := by
      have hzero : 0 ≤ (2 : ℝ) ^ 0 * C_secondGaussianEstimate 0 := by
        simpa using aux_C_secondGaussianEstimate_nonneg 0
      exact hzero.trans
        (aux_le_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l)
          (Nat.zero_le _))
    have hmean : 0 ≤ C_meanFourScaleGaussianKernel 2 := by
      unfold C_meanFourScaleGaussianKernel
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hK) hM)
        (mul_nonneg (mul_nonneg (by norm_num) hK) hT)
    dsimp [A]
    rw [show C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hqterm (p : ℝ) : aux_kernelBracketProduct q j (-w₁ - p, w₁ - p) =
      scaledBracketBump 2 t₀ (-Real.sqrt 2 * p) *
        scaledBracketBump 2 t₁ (Real.sqrt 2 * w₁) := by
    have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hsquare : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
    have hfirst : (W q.2 (-w₁ - p, w₁ - p)).1 = -Real.sqrt 2 * p := by
      rw [hqu]
      simp only [W, Fin.isValue, if_false]
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      calc
        (-w₁ - p) + (w₁ - p) = -2 * p := by ring
        _ = -(Real.sqrt 2)^2 * p := by rw [hsquare]
        _ = (-Real.sqrt 2 * p) * Real.sqrt 2 := by ring
    have hsecond : (W q.2 (-w₁ - p, w₁ - p)).2 = Real.sqrt 2 * w₁ := by
      rw [hqu]
      simp only [W, Fin.isValue, if_false]
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      calc
        -(-w₁ - p) + (w₁ - p) = 2 * w₁ := by ring
        _ = (Real.sqrt 2)^2 * w₁ := by rw [hsquare]
        _ = (Real.sqrt 2 * w₁) * Real.sqrt 2 := by ring
    simp [aux_kernelBracketProduct, t₀, t₁, hfirst, hsecond]
  let f : ℝ → ℝ := fun p =>
    |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
      aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)
  have hfnon (p : ℝ) : 0 ≤ f p := by
    dsimp [f]
    rw [hqterm]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg
      (aux_scaledBracketBump_nonneg 2 ht₀ _) (aux_scaledBracketBump_nonneg 2 ht₁ _))
  have hpoint (p : ℝ) : f p ≤ K *
      ((scaledBracketBumpReal 2 lambda w₀ + scaledBracketBumpReal 2 lambda (w₀ + p)) *
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
          scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)) := by
    have hrho := aux_nMultiplierRho_positive_difference_bound γ hkn ι i j hzero hpositive w₀ p
    rw [← hlambda] at hrho
    have hqnon : 0 ≤ aux_kernelBracketProduct q j (-w₁ - p, w₁ - p) := by
      rw [hqterm]
      exact mul_nonneg (aux_scaledBracketBump_nonneg 2 ht₀ _)
        (aux_scaledBracketBump_nonneg 2 ht₁ _)
    have hmul := mul_le_mul_of_nonneg_right hrho hqnon
    have hB : 0 ≤
        (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
          aux_kernelBracketProduct q j (-w₁ - p, w₁ - p) := by
      apply mul_nonneg
      · apply add_nonneg <;> apply aux_scaledBracketBump_nonneg <;> exact hlambda_pos
      · exact hqnon
    have hpi := aux_caseOne_m1_move_twoPi_out (A := A) (lambda := lambda) (y := p)
      (B := (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) hA hlambda_pos hB
    have hmin := hminloss p
    have hpiA : 0 ≤ 2 * Real.pi * A := by positivity
    have hafterMin :
        (2 * Real.pi * A) * min 1 (lambda⁻¹ * |p|) *
          ((scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
            aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) ≤
          (2 * Real.pi * A) * (r * Real.sqrt (1 + t₀⁻¹ * |p|)) *
            ((scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
              aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin hpiA) hB
    have hsumNonneg : 0 ≤ scaledBracketBump 2 lambda (w₀ + p) +
        scaledBracketBump 2 lambda w₀ :=
      add_nonneg (aux_scaledBracketBump_nonneg 2 hlambda_pos _)
        (aux_scaledBracketBump_nonneg 2 hlambda_pos _)
    have hlast : Real.sqrt (1 + t₀⁻¹ * |p|) *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p) ≤
        scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
          scaledBracketBump 2 t₁ (Real.sqrt 2 * w₁) := by
      rw [hqterm]
      calc
        Real.sqrt (1 + t₀⁻¹ * |p|) *
            (scaledBracketBump 2 t₀ (-Real.sqrt 2 * p) *
              scaledBracketBump 2 t₁ (Real.sqrt 2 * w₁)) =
            (Real.sqrt (1 + t₀⁻¹ * |p|) *
              scaledBracketBump 2 t₀ (-Real.sqrt 2 * p)) *
              scaledBracketBump 2 t₁ (Real.sqrt 2 * w₁) := by ring
        _ ≤ scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
              scaledBracketBump 2 t₁ (Real.sqrt 2 * w₁) :=
          mul_le_mul_of_nonneg_right (aux_caseOne_m1_sqrt_loss_bump t₀ p ht₀)
            (aux_scaledBracketBump_nonneg 2 ht₁ _)
    have hconvert :
        (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
            (scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
              scaledBracketBump 2 t₁ (Real.sqrt 2 * w₁)) =
          (scaledBracketBumpReal 2 lambda w₀ + scaledBracketBumpReal 2 lambda (w₀ + p)) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
              scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁) := by
      rw [← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq,
        ← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq,
        ← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
      ring
    dsimp [f, K]
    have hmul' :
        |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
            aux_kernelBracketProduct q j (-w₁ - p, w₁ - p) ≤
          (C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2 *
            min 1 (2 * Real.pi * lambda⁻¹ * |p|)) *
            ((scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
              aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) := by
      calc
        _ ≤ C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2 *
            min 1 (2 * Real.pi * lambda⁻¹ * |p|) *
              (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
                aux_kernelBracketProduct q j (-w₁ - p, w₁ - p) := hmul
        _ = _ := by ring
    calc
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
          aux_kernelBracketProduct q j (-w₁ - p, w₁ - p) ≤
          A * min 1 (2 * Real.pi * lambda⁻¹ * |p|) *
            ((scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
              aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) := by
            dsimp [A]
            exact hmul'
      _ ≤ (2 * Real.pi * A) * min 1 (lambda⁻¹ * |p|) *
            ((scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
              aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) := hpi
      _ ≤ (2 * Real.pi * A) * (r * Real.sqrt (1 + t₀⁻¹ * |p|)) *
            ((scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
              aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) := hafterMin
      _ = (2 * Real.pi * A * r) *
            ((scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
              (Real.sqrt (1 + t₀⁻¹ * |p|) *
                aux_kernelBracketProduct q j (-w₁ - p, w₁ - p))) := by ring
      _ ≤ (2 * Real.pi * A * r) *
            ((scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) *
              (scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
                scaledBracketBump 2 t₁ (Real.sqrt 2 * w₁))) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hlast hsumNonneg
            · positivity
      _ = (2 * Real.pi * A * r) *
            ((scaledBracketBumpReal 2 lambda w₀ + scaledBracketBumpReal 2 lambda (w₀ + p)) *
              scaledBracketBumpReal (3 / 2 : ℝ) t₀ (Real.sqrt 2 * p) *
                scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)) := by rw [hconvert]
  have hmain := aux_caseOne_m1_integral_le_of_pointwise w₀ w₁ lambda t₀ t₁ K
    hlambda_pos ht₀ ht₁ (by simpa [t₀] using ht₀lambda) hK f hfnon hpoint
  change (∫ p : ℝ, f p) ≤ _
  calc
    (∫ p : ℝ, f p) ≤ K *
        (2 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) *
          scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lambda) (Real.sqrt 2 * w₀) *
            scaledBracketBumpReal (3 / 2 : ℝ) t₁ (Real.sqrt 2 * w₁)) := hmain
    _ = (4 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
        C_meanFourScaleGaussianKernel 2 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)) * r *
          (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lambda) (Real.sqrt 2 * w₀) *
            scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (Real.sqrt 2 * w₁)) := by
      dsimp [K, A, t₁]
      ring

private theorem aux_caseOne_m1_hminloss_of_distanceBall {n : ℕ}
    (γ : GeometricParameters n) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ)
    (hpositive : 0 < ι.1.1) (q : SequencePair × Fin 2)
    (hq₀ : SpacedSequence (q.1 0))
    (hqball : q.1 0 ∈ sequenceDistanceBall (γ.scales i 1)
      (geometricDelta γ : WithTop ℕ))
    (lambda : ℝ)
    (hlambda : lambda = (2 : ℝ) ^ ι.1.1 *
      γ.scales i 1 (j + (geometricDelta γ : ℤ))) :
    ∀ p : ℝ, min 1 (lambda⁻¹ * |p|) ≤
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
        Real.sqrt (1 + (q.1 0 j)⁻¹ * |p|) := by
  have hlambda_pos : 0 < lambda := by
    rw [hlambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have ht : 0 < q.1 0 j := (hq₀ j).1
  have hratio := aux_caseOne_m1_distanceBall_scale_ratio_le
    (γ.scales_spaced i 1) hqball ι.1.1 j
  have hpow : (2 : ℝ) ^ (-ι.1.1) =
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ)) := by
    have hnat : (ι.1.1.natAbs : ℤ) = ι.1.1 :=
      Int.natAbs_of_nonneg hpositive.le
    have hnatR : ((ι.1.1.natAbs : ℕ) : ℝ) = (ι.1.1 : ℝ) := by
      calc
        ((ι.1.1.natAbs : ℕ) : ℝ) = ((ι.1.1.natAbs : ℤ) : ℝ) := by norm_num
        _ = (ι.1.1 : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hnat
    calc
      (2 : ℝ) ^ (-ι.1.1) = Real.rpow 2 ((-ι.1.1 : ℤ) : ℝ) :=
        (Real.rpow_intCast _ _).symm
      _ = Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ)) := by
        congr 1
        rw [Int.cast_neg, ← hnatR]
  have hscale : q.1 0 j / lambda ≤
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ)) := by
    rw [hlambda]
    exact hratio.trans_eq hpow
  intro p
  convert aux_caseOne_m1_min_scale_half_le ht hlambda_pos hscale p using 1 <;> ring

/-- The orientation-one occurrence bound with the dyadic loss obtained directly
from its membership in the H-kernel Gaussian package. -/
private theorem aux_caseOne_m1_orientation_one_rho_occurrence_of_package {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hpositive : 0 < ι.1.1)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (hqu : q.2 = 1)
    (lambda : ℝ)
    (hlambda : lambda = (2 : ℝ) ^ ι.1.1 *
      γ.scales i 1 (j + (geometricDelta γ : ℤ))) (w₀ w₁ : ℝ) :
    (∫ p : ℝ,
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) ≤
      (4 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
        C_meanFourScaleGaussianKernel 2 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lambda) (Real.sqrt 2 * w₀) *
            scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (Real.sqrt 2 * w₁)) := by
  rcases hP.1 q hqmem with ⟨hqball₀, hqball₁⟩
  have hlambda_pos : 0 < lambda := by
    rw [hlambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hratio := aux_caseOne_m1_distanceBall_scale_ratio_le
    (γ.scales_spaced i 1) hqball₀ ι.1.1 j
  have hpowle : (2 : ℝ) ^ (-ι.1.1) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have ht₀lambda : q.1 0 j ≤ lambda := by
    apply (div_le_one₀ hlambda_pos).mp
    rw [hlambda]
    exact hratio.trans hpowle
  exact aux_caseOne_m1_orientation_one_rho_occurrence
    (γ := γ) (hkn := hkn) (ι := ι) (i := i) (j := j)
    (hzero := ne_of_gt hpositive) (hpositive := hpositive) (q := q)
    (hq₀ := hqball₀.1) (hq₁ := hqball₁.1) (hqu := hqu)
    (lambda := lambda)
    (r := Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2))
    (hlambda := hlambda) (hr := Real.rpow_nonneg (by norm_num) _)
    (hminloss := aux_caseOne_m1_hminloss_of_distanceBall
      (γ := γ) (ι := ι) (i := i) (j := j) (hpositive := hpositive)
      (q := q) (hq₀ := hqball₀.1) (hqball := hqball₀)
      (lambda := lambda) (hlambda := hlambda))
    (ht₀lambda := ht₀lambda) (w₀ := w₀) (w₁ := w₁)

/-- Integrability of a finite multiset sum follows from integrability of its
occurrences. -/
private theorem aux_caseOne_integrable_multiset_sum {α : Type*} (P : Multiset α)
    (g : α → ℝ → ℝ) (hg : ∀ q ∈ P, Integrable (g q)) :
    Integrable (fun x : ℝ => (P.map fun q => g q x).sum) := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      apply Integrable.add
      · exact hg a (by simp)
      · apply ih
        intro q hq
        exact hg q (by simp [hq])

/-- Integration commutes with the finite multiset sum used by the H package. -/
private theorem aux_caseOne_integral_multiset_sum {α : Type*} (P : Multiset α)
    (g : α → ℝ → ℝ) (hg : ∀ q ∈ P, Integrable (g q)) :
    (∫ x : ℝ, (P.map fun q => g q x).sum) =
      (P.map fun q => ∫ x : ℝ, g q x).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
      have hgP : ∀ q ∈ P, Integrable (g q) := by
        intro q hq
        exact hg q (by simp [hq])
      have hsumP : Integrable (fun x : ℝ => (P.map fun q => g q x).sum) :=
        aux_caseOne_integrable_multiset_sum P g hgP
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [integral_add (hg a (by simp)) hsumP, ih hgP]

/-- Pulling a scalar through a finite multiset sum. -/
private theorem aux_caseOne_mul_multiset_sum {α : Type*} (a : ℝ) (P : Multiset α)
    (g : α → ℝ) :
    a * (P.map g).sum = (P.map fun q => a * g q).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons q P ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [mul_add, ih]

/-- A finite H-package pointwise bound may be integrated occurrence-by-occurrence. -/
private theorem aux_caseOne_finite_multiset_integral_bridge {α : Type*}
    (P : Multiset α) (C : ℝ) (rho H : ℝ → ℝ) (B : α → ℝ → ℝ)
    (hC : 0 ≤ C) (hrho : ∀ p, 0 ≤ rho p) (hH : ∀ p, 0 ≤ H p)
    (hbound : ∀ p, H p ≤ C * (P.map fun q => B q p).sum)
    (hint : ∀ q ∈ P, Integrable (fun p : ℝ => rho p * B q p)) :
    (∫ p : ℝ, rho p * H p) ≤
      C * (P.map fun q => ∫ p : ℝ, rho p * B q p).sum := by
  let S : ℝ → ℝ := fun p => (P.map fun q => rho p * B q p).sum
  have hS : Integrable S := by
    dsimp [S]
    exact aux_caseOne_integrable_multiset_sum P (fun q p => rho p * B q p) hint
  have hpoint (p : ℝ) : rho p * H p ≤ C * S p := by
    have h := mul_le_mul_of_nonneg_left (hbound p) (hrho p)
    change rho p * H p ≤ rho p * (C * (P.map fun q => B q p).sum) at h
    calc
      rho p * H p ≤ rho p * (C * (P.map fun q => B q p).sum) := h
      _ = C * (rho p * (P.map fun q => B q p).sum) := by ring
      _ = C * S p := by
        dsimp [S]
        rw [aux_caseOne_mul_multiset_sum]
  have hleft (p : ℝ) : 0 ≤ rho p * H p := mul_nonneg (hrho p) (hH p)
  calc
    (∫ p : ℝ, rho p * H p) ≤ ∫ p : ℝ, C * S p :=
      integral_mono_of_nonneg (ae_of_all _ hleft) (hS.const_mul C)
        (ae_of_all _ hpoint)
    _ = C * (∫ p : ℝ, S p) := by rw [integral_const_mul]
    _ = C * (P.map fun q => ∫ p : ℝ, rho p * B q p).sum := by
      rw [aux_caseOne_integral_multiset_sum P (fun q p => rho p * B q p) hint]

/-- Sum occurrence bounds while preserving every multiplicity of the H package. -/
private theorem aux_caseOne_multiset_sum_le_scaled {α : Type*} (P : Multiset α)
    (f g : α → ℝ) (D : ℝ) (h : ∀ q ∈ P, f q ≤ D * g q) :
    (P.map f).sum ≤ D * (P.map g).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
      have hP : ∀ q ∈ P, f q ≤ D * g q := by
        intro q hq
        exact h q (by simp [hq])
      simp only [Multiset.map_cons, Multiset.sum_cons]
      calc
        f a + (P.map f).sum ≤ D * g a + D * (P.map g).sum :=
          add_le_add (h a (by simp)) (ih hP)
        _ = D * (g a + (P.map g).sum) := by ring

/-- Cancellation plus an H-package estimate reduces the positive-band N bound
to the finite sum of its occurrence integrals. -/
private theorem aux_caseOne_outer_from_occurrences {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (w₀ w₁ : ℝ)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelGaussianBound γ i P)
    (D : ℝ) (S : (SequencePair × Fin 2) → ℝ)
    (hint : ∀ q ∈ P, Integrable (fun p : ℝ =>
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)))
    (hocc : ∀ q ∈ P, (∫ p : ℝ,
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) ≤ D * S q) :
    |nMultiplier γ hkn ι i j (w₀ - w₁, w₀ + w₁)| ≤
      C_hKernelEstimateGaussianDomination * D * (P.map S).sum := by
  rw [aux_nMultiplier_caseOne_cancellation]
  let rho : ℝ → ℝ := fun p =>
    |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀|
  let H : ℝ → ℝ := fun p => |hMultiplier γ i j (-w₁ - p, w₁ - p)|
  let B : (SequencePair × Fin 2) → ℝ → ℝ := fun q p =>
    aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)
  have hHbound (p : ℝ) : H p ≤ C_hKernelEstimateGaussianDomination *
      (P.map fun q => B q p).sum := by
    dsimp [H, B]
    exact hP.2.2 (-w₁ - p, w₁ - p) j
  have hbridge := aux_caseOne_finite_multiset_integral_bridge P
    C_hKernelEstimateGaussianDomination rho H B
    aux_C_hKernelEstimateGaussianDomination_nonneg (fun p => abs_nonneg _)
    (fun p => abs_nonneg _) hHbound (by
      intro q hq
      simpa [rho, B] using hint q hq)
  have hsum := aux_caseOne_multiset_sum_le_scaled P
    (fun q => ∫ p : ℝ, rho p * B q p) S D (by
      intro q hq
      simpa [rho, B] using hocc q hq)
  calc
    |∫ p : ℝ,
        (nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀) *
          hMultiplier γ i j (-w₁ - p, w₁ - p)| ≤
        ∫ p : ℝ,
          |(nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀) *
            hMultiplier γ i j (-w₁ - p, w₁ - p)| :=
      abs_integral_le_integral_abs
    _ = ∫ p : ℝ, rho p * H p := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp [rho, H, abs_mul]
    _ ≤ C_hKernelEstimateGaussianDomination *
        (P.map fun q => ∫ p : ℝ, rho p * B q p).sum := hbridge
    _ ≤ C_hKernelEstimateGaussianDomination * (D * (P.map S).sum) :=
      mul_le_mul_of_nonneg_left hsum aux_C_hKernelEstimateGaussianDomination_nonneg
    _ = C_hKernelEstimateGaussianDomination * D * (P.map S).sum := by ring

/-- Each one-dimensional slice of an H-package bracket product is integrable.
This is the only integrability input needed to pass from the pointwise H bound
to the finite sum of occurrence integrals. -/
private theorem aux_caseOne_kernelBracketProduct_integrable
    (q : SequencePair × Fin 2) (j : ℤ) (w₁ : ℝ)
    (hq₀ : SpacedSequence (q.1 0)) (hq₁ : SpacedSequence (q.1 1)) :
    Integrable (fun p : ℝ => aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) := by
  let t₀ : ℝ := q.1 0 j
  let t₁ : ℝ := q.1 1 j
  have ht₀ : 0 < t₀ := by simpa [t₀] using (hq₀ j).1
  have ht₁ : 0 < t₁ := by simpa [t₁] using (hq₁ j).1
  by_cases hu : q.2 = 0
  · have hprod := aux_caseOne_scaledBracketBumpReal_product_integrable
      2 2 t₀ t₁ (-w₁) w₁ (by norm_num) (by norm_num) ht₀ ht₁
    convert hprod using 1
    funext p
    simp [aux_kernelBracketProduct, W, hu, t₀, t₁,
      ← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
  · have hu' : q.2 = 1 := by
      exact Fin.eq_one_of_ne_zero q.2 hu
    have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hbase : Integrable (fun x : ℝ => scaledBracketBumpReal 2 t₀ x) :=
      aux_integrable_scaledBracketBumpReal 2 t₀ (by norm_num) ht₀
    have hscaled : Integrable (fun p : ℝ =>
        scaledBracketBumpReal 2 t₀ (-Real.sqrt 2 * p)) := by
      convert hbase.comp_mul_left' (neg_ne_zero.mpr (ne_of_gt hsqrt)) using 1
    have hconst : Integrable (fun p : ℝ =>
        scaledBracketBumpReal 2 t₀ (-Real.sqrt 2 * p) *
          scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁)) := by
      simpa [mul_comm] using hscaled.mul_const
        (scaledBracketBumpReal 2 t₁ (Real.sqrt 2 * w₁))
    convert hconst using 1
    funext p
    have hsquare : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
    have hfirst : (W q.2 (-w₁ - p, w₁ - p)).1 = -Real.sqrt 2 * p := by
      rw [hu']
      simp only [W, Fin.isValue, if_false]
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      calc
        (-w₁ - p) + (w₁ - p) = -2 * p := by ring
        _ = -(Real.sqrt 2)^2 * p := by rw [hsquare]
        _ = (-Real.sqrt 2 * p) * Real.sqrt 2 := by ring
    have hsecond : (W q.2 (-w₁ - p, w₁ - p)).2 = Real.sqrt 2 * w₁ := by
      rw [hu']
      simp only [W, Fin.isValue, if_false]
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      calc
        -(-w₁ - p) + (w₁ - p) = 2 * w₁ := by ring
        _ = (Real.sqrt 2)^2 * w₁ := by rw [hsquare]
        _ = (Real.sqrt 2 * w₁) * Real.sqrt 2 := by ring
    simp [aux_kernelBracketProduct, t₀, t₁, hfirst, hsecond,
      ← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]

/-- We use the explicit six-occurrence H-package so its multiplicities agree
with the range-30 witness decoder. -/
private theorem aux_caseOne_HPackage_explicit {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) :
    aux_HKernelGaussianBound γ i (aux_hKernelGaussianMultiset γ i) := by
  by_cases h : γ.orientation i = 0
  · apply aux_hKernelGaussianBound_orientation_zero_of_sBounds γ i h
    intro j x
    apply aux_sMultiplier_bound_orientation_zero_of_diagonal γ i j h
    intro y
    rw [aux_sMultiplier_eq_diagonalSquareRoot]
    have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
    apply diagonalSquareRoot_bound 2 (by norm_num)
    · linarith [hsp.1]
    · convert hsp.2 using 1 <;> ring
  · apply aux_hKernelGaussianBound_orientation_one_of_sBounds γ i h
    intro j x
    apply aux_sMultiplier_bound_orientation_one_of_diagonal γ i j h
    intro y
    rw [aux_sMultiplier_eq_diagonalSquareRoot]
    have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
    apply diagonalSquareRoot_bound 2 (by norm_num)
    · linarith [hsp.1]
    · convert hsp.2 using 1 <;> ring

/-- The orientation-one M₁ product is exactly slot zero of the shared
five-slot occurrence package. -/
private theorem aux_caseOne_m1_slot_zero
    (lam : ℤ → ℝ) (q : SequencePair × Fin 2) (j : ℤ) (w₀ w₁ : ℝ)
    (hqu : q.2 = 1) :
    scaledBracketBumpReal (3 / 2 : ℝ) (Real.sqrt 2 * lam j) (Real.sqrt 2 * w₀) *
        scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (Real.sqrt 2 * w₁) =
      aux_caseOneExactSlotTerm lam q j (w₀ - w₁, w₀ + w₁) 0 := by
  simp [aux_caseOneExactSlotTerm, aux_caseOneExactSlotOf,
    aux_caseOneExactM1Scale, hqu, aux_sequencePairOf, aux_caseOne_Wone]

private theorem aux_caseOne_meanFour_nonneg :
    0 ≤ C_meanFourScaleGaussianKernel 2 := by
  have hK : 0 ≤ C_meanValueBumpEstimate 2 := by
    unfold C_meanValueBumpEstimate
    positivity
  have hM : 0 ≤ aux_maxUpTo C_gaussianBumpEstimate 2 :=
    (aux_C_gaussianBumpEstimate_nonneg 0).trans
      (aux_le_maxUpTo C_gaussianBumpEstimate (Nat.zero_le _))
  have hT : 0 ≤ aux_maxUpTo
      (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) 2 := by
    have hzero : 0 ≤ (2 : ℝ) ^ 0 * C_secondGaussianEstimate 0 := by
      simpa using aux_C_secondGaussianEstimate_nonneg 0
    exact hzero.trans
      (aux_le_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l)
        (Nat.zero_le _))
  unfold C_meanFourScaleGaussianKernel
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hK) hM)
    (mul_nonneg (mul_nonneg (by norm_num) hK) hT)

private theorem aux_caseOne_twoBump_nonneg :
    0 ≤ C_twoBumpEstimate (3 / 2) (3 / 2) := by
  norm_num [C_twoBumpEstimate]
  exact Real.rpow_nonneg (by norm_num) _

/-- Both orientation branches of one H-kernel occurrence have the same exact
five-slot majorant and the coefficient needed for the doubled Case 1 constant. -/
private theorem aux_caseOne_occurrence_uniform {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hpositive : 0 < ι.1.1)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (w₀ w₁ : ℝ) :
    (∫ p : ℝ,
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) ≤
      (32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
        C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2)) *
          ∑ r : Fin 5,
            aux_caseOneExactSlotTerm (caseOneLambda γ ι i) q j
              (w₀ - w₁, w₀ + w₁) r := by
  classical
  by_cases hqu : q.2 = 0
  · unfold caseOneLambda
    exact aux_caseOne_u0_rho_occurrence_of_package γ hkn ι i j hpositive
      P hP q hqmem hqu ((2 : ℝ) ^ ι.1.1 *
        γ.scales i 1 (j + (geometricDelta γ : ℤ))) (by rfl) w₀ w₁
  · have hqu' : q.2 = 1 := Fin.eq_one_of_ne_zero q.2 hqu
    have hraw := aux_caseOne_m1_orientation_one_rho_occurrence_of_package
      γ hkn ι i j hpositive P hP q hqmem hqu' (caseOneLambda γ ι i j) (by rfl) w₀ w₁
    rcases hP.1 q hqmem with ⟨hq₀, hq₁⟩
    have hq : ∀ s : Fin 2, SpacedSequence (q.1 s) := by
      intro s
      fin_cases s
      · exact hq₀.1
      · exact hq₁.1
    have hslotnonneg (r : Fin 5) : 0 ≤
        aux_caseOneExactSlotTerm (caseOneLambda γ ι i) q j
          (w₀ - w₁, w₀ + w₁) r :=
      aux_caseOneExactSlotTerm_nonneg (caseOneLambda γ ι i)
        (caseOneLambda_spaced γ ι i) q hq j (w₀ - w₁, w₀ + w₁) r
    have hprod : 0 ≤
        scaledBracketBumpReal (3 / 2 : ℝ)
          (Real.sqrt 2 * caseOneLambda γ ι i j) (Real.sqrt 2 * w₀) *
          scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (Real.sqrt 2 * w₁) := by
      rw [aux_caseOne_m1_slot_zero (caseOneLambda γ ι i) q j w₀ w₁ hqu']
      exact hslotnonneg 0
    have hpad :
        scaledBracketBumpReal (3 / 2 : ℝ)
          (Real.sqrt 2 * caseOneLambda γ ι i j) (Real.sqrt 2 * w₀) *
          scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (Real.sqrt 2 * w₁) ≤
          ∑ r : Fin 5,
            aux_caseOneExactSlotTerm (caseOneLambda γ ι i) q j
              (w₀ - w₁, w₀ + w₁) r := by
      rw [aux_caseOne_m1_slot_zero (caseOneLambda γ ι i) q j w₀ w₁ hqu']
      exact Finset.single_le_sum (fun r _ => hslotnonneg r) (Finset.mem_univ 0)
    have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 2 := by
      rw [show C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) by
        norm_num [C_standardBumpPropertiesTilde]]
      positivity
    have hA : 0 ≤ Real.pi * C_standardBumpPropertiesTilde 0 2 *
        C_meanFourScaleGaussianKernel 2 *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) hstd)
          aux_caseOne_meanFour_nonneg)
        (Real.rpow_nonneg (by norm_num) _)
    have hK : 0 ≤ max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
        (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2)) := by
      exact (add_nonneg aux_caseOne_twoBump_nonneg (by norm_num)).trans
        (le_max_left _ _)
    have hscalar : 4 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) ≤
        32 * max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
          (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
            C_twoBumpEstimate (3 / 2) (3 / 2)) := by
      calc
        4 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4) ≤
            4 * max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
              (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
                C_twoBumpEstimate (3 / 2) (3 / 2)) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
        _ ≤ 32 * max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
              (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
                C_twoBumpEstimate (3 / 2) (3 / 2)) := by nlinarith
    have hcoef :
        (4 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
          C_meanFourScaleGaussianKernel 2 *
          (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) ≤
        (32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
          C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2)) := by
      calc
        _ = (Real.pi * C_standardBumpPropertiesTilde 0 2 *
            C_meanFourScaleGaussianKernel 2 *
            Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)) *
          (4 * (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)) := by ring
        _ ≤ (Real.pi * C_standardBumpPropertiesTilde 0 2 *
            C_meanFourScaleGaussianKernel 2 *
            Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)) *
          (32 * max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2))) :=
          mul_le_mul_of_nonneg_left hscalar hA
        _ = _ := by ring
    have hDnonneg : 0 ≤
        (32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
          C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2)) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hstd)
            aux_caseOne_meanFour_nonneg)
          (Real.rpow_nonneg (by norm_num) _)) hK
    calc
      _ ≤ (4 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
          C_meanFourScaleGaussianKernel 2 *
          (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          (scaledBracketBumpReal (3 / 2 : ℝ)
            (Real.sqrt 2 * caseOneLambda γ ι i j) (Real.sqrt 2 * w₀) *
            scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (Real.sqrt 2 * w₁)) := hraw
      _ ≤ ((32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
          C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2))) *
          (scaledBracketBumpReal (3 / 2 : ℝ)
            (Real.sqrt 2 * caseOneLambda γ ι i j) (Real.sqrt 2 * w₀) *
            scaledBracketBumpReal (3 / 2 : ℝ) (q.1 1 j) (Real.sqrt 2 * w₁)) :=
        mul_le_mul_of_nonneg_right hcoef hprod
      _ ≤ _ := mul_le_mul_of_nonneg_left hpad hDnonneg

private def aux_caseOneSlotProduct (j : ℤ) (v : RealPlane)
    (s : SequencePair × Fin 2) : ℝ :=
  scaledBracketBumpReal (3 / 2 : ℝ) (s.1 0 j) (W s.2 v).1 *
    scaledBracketBumpReal (3 / 2 : ℝ) (s.1 1 j) (W s.2 v).2

private theorem aux_caseOneExactSlotOf_eq_caseOneExactSlotOf
    (lam : ℤ → ℝ) (q : SequencePair × Fin 2) (r : Fin 5) :
    aux_caseOneExactSlotOf lam q r = caseOneExactSlotOf lam q r := by
  unfold aux_caseOneExactSlotOf caseOneExactSlotOf
  unfold aux_caseOneExactM1Scale caseOneExactM1Scale
  rfl

private theorem aux_caseOneExactSlotTerm_eq_caseOneSlotProduct
    (lam : ℤ → ℝ) (q : SequencePair × Fin 2) (j : ℤ) (v : RealPlane) (r : Fin 5) :
    aux_caseOneExactSlotTerm lam q j v r =
      aux_caseOneSlotProduct j v (caseOneExactSlotOf lam q r) := by
  simp only [aux_caseOneExactSlotTerm, aux_caseOneSlotProduct,
    aux_caseOneExactSlotOf_eq_caseOneExactSlotOf]

private theorem aux_caseOne_multiset_sum_eq_occurrence_sum
    {R : Type*} [AddCommMonoid R] (P : Multiset (SequencePair × Fin 2))
    (F : SequencePair × Fin 2 → R) :
    (P.map F).sum = ∑ k : Fin P.card, F (caseOneOccurrence P k) := by
  rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem]
  let e : Fin P.card ≃ Fin P.toList.length :=
    finCongr (Multiset.length_toList P).symm
  symm
  refine Fintype.sum_equiv e
    (fun k => F (caseOneOccurrence P k))
    (fun l => F (P.toList.get l)) ?_
  intro k
  simp [e, caseOneOccurrence]

private theorem aux_caseOne_multiset_slot_sum_reindex {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) (v : RealPlane) :
    ((aux_hKernelGaussianMultiset γ i).map
      (fun q => ∑ r : Fin 5,
        aux_caseOneExactSlotTerm (caseOneLambda γ ι i) q j v r)).sum =
      ∑ b ∈ caseOneB,
        aux_caseOneSlotProduct j v (caseOneSlotNat γ ι i b) := by
  classical
  rw [aux_caseOne_multiset_sum_eq_occurrence_sum]
  have hsum :
      (∑ k : Fin 6, ∑ r : Fin 5,
        aux_caseOneExactSlotTerm (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) j v r) =
      ∑ k : Fin (aux_hKernelGaussianMultiset γ i).card, ∑ r : Fin 5,
        aux_caseOneExactSlotTerm (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i) k) j v r := by
    let e : Fin 6 ≃ Fin (aux_hKernelGaussianMultiset γ i).card :=
      finCongr (aux_hKernelGaussianMultiset_card γ i).symm
    refine Fintype.sum_equiv e
      (fun k => ∑ r : Fin 5,
        aux_caseOneExactSlotTerm (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) j v r)
      (fun k => ∑ r : Fin 5,
        aux_caseOneExactSlotTerm (caseOneLambda γ ι i)
          (caseOneOccurrence (aux_hKernelGaussianMultiset γ i) k) j v r) ?_
    intro k
    simp [e]
  rw [← hsum]
  rw [caseOne_sum_range30_reindex γ ι i (aux_caseOneSlotProduct j v)]
  simp_rw [aux_caseOneExactSlotTerm_eq_caseOneSlotProduct]

/-- The raw rho-difference times any one H-package bracket product is integrable.
For this bookkeeping step a uniform boundedness consequence of the positive
rho estimate is sufficient. -/
private theorem aux_caseOne_raw_occurrence_integrable {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hpositive : 0 < ι.1.1)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (w₀ w₁ : ℝ) :
    Integrable (fun p : ℝ =>
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) := by
  let lambda : ℝ := caseOneLambda γ ι i j
  have hlambda : lambda = (2 : ℝ) ^ ι.1.1 *
      γ.scales i 1 (j + (geometricDelta γ : ℤ)) := by rfl
  have hlambda_pos : 0 < lambda := by
    rw [hlambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  rcases hP.1 q hqmem with ⟨hq₀, hq₁⟩
  have hq : ∀ r : Fin 2, SpacedSequence (q.1 r) := by
    intro r
    fin_cases r
    · exact hq₀.1
    · exact hq₁.1
  let M₀ : ℝ := C_standardBumpPropertiesTilde 0 2 * C_meanFourScaleGaussianKernel 2
  have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 2 := by
    rw [show C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity
  have hM₀ : 0 ≤ M₀ := by
    dsimp [M₀]
    exact mul_nonneg hstd aux_caseOne_meanFour_nonneg
  let M : ℝ := M₀ * (2 * lambda⁻¹)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg hM₀ (mul_nonneg (by norm_num) (inv_nonneg.mpr hlambda_pos.le))
  let B : ℝ → ℝ := fun p => aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)
  have hB : Integrable B := by
    dsimp [B]
    exact aux_caseOne_kernelBracketProduct_integrable q j w₁ hq₀.1 hq₁.1
  have hrhoCont : Continuous (nMultiplierRho γ hkn ι i j) :=
    (nMultiplierRho_memW0 γ hkn ι i j).aux_continuous
  have hdiffCont : Continuous (fun p : ℝ =>
      nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀) :=
    (hrhoCont.comp (continuous_const.add continuous_id)).sub continuous_const
  have hsum_nonneg (p : ℝ) : 0 ≤
      scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀ :=
    add_nonneg
      (aux_scaledBracketBump_nonneg 2 hlambda_pos _)
      (aux_scaledBracketBump_nonneg 2 hlambda_pos _)
  have hsum_bound (p : ℝ) :
      scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀ ≤
        2 * lambda⁻¹ := by
    calc
      scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀ ≤
          lambda⁻¹ + lambda⁻¹ :=
        add_le_add
          (aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv hlambda_pos)
          (aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv hlambda_pos)
      _ = 2 * lambda⁻¹ := by ring
  have hrho_bound (p : ℝ) :
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| ≤ M := by
    have hraw := aux_nMultiplierRho_positive_difference_bound γ hkn ι i j
      (ne_of_gt hpositive) hpositive w₀ p
    rw [← hlambda] at hraw
    calc
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| ≤
          M₀ * min 1 (2 * Real.pi * lambda⁻¹ * |p|) *
            (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) := by
        simpa [M₀, mul_assoc] using hraw
      _ ≤ M₀ * (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) := by
        calc
          M₀ * min 1 (2 * Real.pi * lambda⁻¹ * |p|) *
              (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀) =
              M₀ * (min 1 (2 * Real.pi * lambda⁻¹ * |p|) *
                (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀)) := by ring
          _ ≤ M₀ * (1 *
                (scaledBracketBump 2 lambda (w₀ + p) + scaledBracketBump 2 lambda w₀)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (min_le_left _ _) (hsum_nonneg p)) hM₀
          _ = M₀ * (scaledBracketBump 2 lambda (w₀ + p) +
              scaledBracketBump 2 lambda w₀) := by ring
      _ ≤ M := by
        dsimp [M]
        exact mul_le_mul_of_nonneg_left (hsum_bound p) hM₀
  have hmajor : Integrable (fun p : ℝ => M * B p) := hB.const_mul M
  refine hmajor.mono' ?_ ?_
  · exact hdiffCont.abs.aestronglyMeasurable.mul hB.aestronglyMeasurable
  · filter_upwards [] with p
    have hBnon : 0 ≤ B p := by
      dsimp [B]
      exact aux_kernelBracketProduct_nonneg q hq j _
    have hfnon : 0 ≤
        |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| * B p :=
      mul_nonneg (abs_nonneg _) hBnon
    have hle := mul_le_mul_of_nonneg_right (hrho_bound p) hBnon
    change ‖|nMultiplierRho γ hkn ι i j (w₀ + p) -
        nMultiplierRho γ hkn ι i j w₀| * B p‖ ≤ M * B p
    simpa only [Real.norm_eq_abs, abs_of_nonneg hfnon] using hle

/-- Cancellation, the explicit six-term H package, and the two orientation
occurrence estimates give a 30-slot real-bracket majorant before Gaussian
domination is applied to its slots. -/
private theorem aux_caseOne_preGaussian_bound {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hpositive : 0 < ι.1.1) (w₀ w₁ : ℝ) :
    |nMultiplier γ hkn ι i j (w₀ - w₁, w₀ + w₁)| ≤
      C_hKernelEstimateGaussianDomination *
        ((32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
          C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2))) *
        ∑ b ∈ caseOneB,
          aux_caseOneSlotProduct j (w₀ - w₁, w₀ + w₁)
            (caseOneSlotNat γ ι i b) := by
  classical
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let D : ℝ := (32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
    C_meanFourScaleGaussianKernel 2) *
    Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
    max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
      (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2))
  let S : (SequencePair × Fin 2) → ℝ := fun q => ∑ r : Fin 5,
    aux_caseOneExactSlotTerm (caseOneLambda γ ι i) q j
      (w₀ - w₁, w₀ + w₁) r
  have hP : aux_HKernelGaussianBound γ i P := by
    dsimp [P]
    exact aux_caseOne_HPackage_explicit γ i
  have hint : ∀ q ∈ P, Integrable (fun p : ℝ =>
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) := by
    intro q hq
    exact aux_caseOne_raw_occurrence_integrable γ hkn ι i j hpositive P hP q hq w₀ w₁
  have hocc : ∀ q ∈ P, (∫ p : ℝ,
      |nMultiplierRho γ hkn ι i j (w₀ + p) - nMultiplierRho γ hkn ι i j w₀| *
        aux_kernelBracketProduct q j (-w₁ - p, w₁ - p)) ≤ D * S q := by
    intro q hq
    dsimp [D, S]
    exact aux_caseOne_occurrence_uniform γ hkn ι i j hpositive P hP q hq w₀ w₁
  have houter := aux_caseOne_outer_from_occurrences γ hkn ι i j w₀ w₁
    P hP D S hint hocc
  have hreindex : (P.map S).sum = ∑ b ∈ caseOneB,
      aux_caseOneSlotProduct j (w₀ - w₁, w₀ + w₁) (caseOneSlotNat γ ι i b) := by
    dsimp [P, S]
    exact aux_caseOne_multiset_slot_sum_reindex γ ι i j (w₀ - w₁, w₀ + w₁)
  calc
    |nMultiplier γ hkn ι i j (w₀ - w₁, w₀ + w₁)| ≤
        C_hKernelEstimateGaussianDomination * D * (P.map S).sum := houter
    _ = C_hKernelEstimateGaussianDomination * D *
        ∑ b ∈ caseOneB,
          aux_caseOneSlotProduct j (w₀ - w₁, w₀ + w₁)
            (caseOneSlotNat γ ι i b) := by rw [hreindex]
    _ = _ := by rfl

private theorem aux_caseOne_slot_gaussian_majorant
    (p : SequencePair) (hp : ∀ r : Fin 2, SpacedSequence (p r))
    (u : Fin 2) (j : ℤ) (v : RealPlane) :
    aux_caseOneSlotProduct j v (p, u) ≤
      8 * Real.exp (2 * Real.pi) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          aux_dominatingGaussianTerm
            (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
  let f₀ : ℕ → ℝ := fun a =>
    Real.rpow 2 (-((a : ℝ) / 2)) *
      gaussianRescale ((2 : ℝ) ^ a * p 0 j) (W u v).1
  let f₁ : ℕ → ℝ := fun a =>
    Real.rpow 2 (-((a : ℝ) / 2)) *
      gaussianRescale ((2 : ℝ) ^ a * p 1 j) (W u v).2
  have hp₀ : 0 < p 0 j := aux_spacedSequence_pos (hp 0) j
  have hp₁ : 0 < p 1 j := aux_spacedSequence_pos (hp 1) j
  have hhalf (a : ℕ) : (1 - (3 / 2 : ℝ)) * (a : ℝ) = -((a : ℝ) / 2) := by
    ring
  have hbr₀ := gaussianDomination (3 / 2 : ℝ) (p 0 j) (W u v).1
    (by norm_num) hp₀
  have hbr₁ := gaussianDomination (3 / 2 : ℝ) (p 1 j) (W u v).2
    (by norm_num) hp₁
  have hbr₀' : scaledBracketBumpReal (3 / 2 : ℝ) (p 0 j) (W u v).1 ≤
      C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f₀ a := by
    simpa [f₀, hhalf] using hbr₀
  have hbr₁' : scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 ≤
      C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f₁ a := by
    simpa [f₁, hhalf] using hbr₁
  have hf₀ : Summable f₀ := by
    simpa [f₀, hhalf] using
      aux_gaussianDomination_weight_summable (3 / 2 : ℝ) (p 0 j) (W u v).1
        (by norm_num) hp₀
  have hf₁ : Summable f₁ := by
    simpa [f₁, hhalf] using
      aux_gaussianDomination_weight_summable (3 / 2 : ℝ) (p 1 j) (W u v).2
        (by norm_num) hp₁
  have hf₀nonneg (a : ℕ) : 0 ≤ f₀ a := by
    dsimp [f₀]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hp₀) _)
  have hf₁nonneg (a : ℕ) : 0 ≤ f₁ a := by
    dsimp [f₁]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hp₁) _)
  have hprod : Summable (fun m : Fin 2 → ℕ => f₀ (m 0) * f₁ (m 1)) :=
    aux_summable_finTwo_product hf₀nonneg hf₁nonneg hf₀ hf₁
  have hprodPair : Summable (fun z : ℕ × ℕ => f₀ z.1 * f₁ z.2) := by
    refine (aux_finTwoNatEquivProd.symm.summable_iff
      (f := fun m : Fin 2 → ℕ => f₀ (m 0) * f₁ (m 1))).mpr ?_
    exact hprod
  have hprodEq : (∑' a : ℕ, f₀ a) * (∑' a : ℕ, f₁ a) =
      ∑' m : Fin 2 → ℕ, f₀ (m 0) * f₁ (m 1) := by
    calc
      (∑' a : ℕ, f₀ a) * (∑' a : ℕ, f₁ a) =
          ∑' z : ℕ × ℕ, f₀ z.1 * f₁ z.2 := hf₀.tsum_mul_tsum hf₁ hprodPair
      _ = ∑' m : Fin 2 → ℕ, f₀ (m 0) * f₁ (m 1) := by
        simpa [aux_finTwoNatEquivProd] using
          (aux_finTwoNatEquivProd.symm.tsum_eq
            (fun m : Fin 2 → ℕ => f₀ (m 0) * f₁ (m 1)))
  have hterm (m : Fin 2 → ℕ) : f₀ (m 0) * f₁ (m 1) =
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
    have hweight : aux_gaussianDominationWeight m =
        Real.rpow 2 (-((m 0 : ℕ) : ℝ) / 2) *
          Real.rpow 2 (-((m 1 : ℕ) : ℝ) / 2) := by
      unfold aux_gaussianDominationWeight aux_natPairWeight
      calc
        Real.rpow 2 (-((m 0 + m 1 : ℕ) : ℝ) / 2) =
            Real.rpow 2 (-((m 0 : ℕ) : ℝ) / 2 +
              -((m 1 : ℕ) : ℝ) / 2) := by
          congr 1
          push_cast
          ring
        _ = _ := Real.rpow_add (by norm_num) _ _
    rw [hweight]
    simp only [aux_dominatingGaussianTerm, twoDimensionalGaussian]
    dsimp [f₀, f₁]
    ring
  have hseriesEq : (∑' a : ℕ, f₀ a) * (∑' a : ℕ, f₁ a) =
      ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
    rw [hprodEq]
    exact tsum_congr hterm
  have hcoeffnonneg : 0 ≤ C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) := by
    rw [C_gaussianDomination]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by norm_num) _)
  have hsum₀ : 0 ≤ ∑' a : ℕ, f₀ a := tsum_nonneg hf₀nonneg
  have hpow : Real.rpow 2 (3 / 2 : ℝ) * Real.rpow 2 (3 / 2 : ℝ) = 8 := by
    change (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) = 8
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hexp : Real.exp Real.pi * Real.exp Real.pi = Real.exp (2 * Real.pi) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcoeff :
      (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) =
      8 * Real.exp (2 * Real.pi) := by
    rw [C_gaussianDomination]
    calc
      (Real.exp Real.pi * Real.rpow 2 (3 / 2 : ℝ)) *
          (Real.exp Real.pi * Real.rpow 2 (3 / 2 : ℝ)) =
          (Real.exp Real.pi * Real.exp Real.pi) *
            (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow 2 (3 / 2 : ℝ)) := by ring
      _ = _ := by rw [hexp, hpow]; ring
  calc
    aux_caseOneSlotProduct j v (p, u) =
        scaledBracketBumpReal (3 / 2 : ℝ) (p 0 j) (W u v).1 *
          scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 := rfl
    _ ≤ (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f₀ a) *
        scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 :=
      mul_le_mul_of_nonneg_right hbr₀'
        (aux_scaledBracketBumpReal_nonneg _ _ _ hp₁)
    _ ≤ (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f₀ a) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f₁ a) :=
      mul_le_mul_of_nonneg_left hbr₁' (mul_nonneg hcoeffnonneg hsum₀)
    _ = ((C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ))) *
          ((∑' a : ℕ, f₀ a) * ∑' a : ℕ, f₁ a) := by ring
    _ = (8 * Real.exp (2 * Real.pi)) *
          ((∑' a : ℕ, f₀ a) * ∑' a : ℕ, f₁ a) := by rw [hcoeff]
    _ = _ := by rw [hseriesEq]

private theorem aux_caseOne_slot_sum_gaussian_majorant {n : ℕ}
    (γ : GeometricParameters n) (ι : MultiplierIndex γ) (i : Fin γ.k)
    (j : ℤ) (v : RealPlane) :
    ∑ b ∈ caseOneB,
      aux_caseOneSlotProduct j v (caseOneSlotNat γ ι i b) ≤
      8 * Real.exp (2 * Real.pi) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          ∑ b ∈ caseOneB,
            aux_dominatingGaussianTerm (caseOneScales γ ι i b m)
              (caseOneOrientation γ ι i b) j v := by
  classical
  let T : ℕ → (Fin 2 → ℕ) → ℝ := fun b m =>
    aux_gaussianDominationWeight m *
      aux_dominatingGaussianTerm (caseOneScales γ ι i b m)
        (caseOneOrientation γ ι i b) j v
  have hslot (b : ℕ) (hb : b ∈ caseOneB) :
      aux_caseOneSlotProduct j v (caseOneSlotNat γ ι i b) ≤
        (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ, T b m := by
    have hbase := aux_caseOne_slot_gaussian_majorant
      (caseOneSlotNat γ ι i b).1 (caseOneSlotNat_spaced γ ι i b)
      (caseOneSlotNat γ ι i b).2 j v
    change aux_caseOneSlotProduct j v (caseOneSlotNat γ ι i b) ≤
      (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ,
        aux_gaussianDominationWeight m *
          aux_dominatingGaussianTerm (caseOneScales γ ι i b m)
            (caseOneOrientation γ ι i b) j v
    unfold caseOneScales caseOneOrientation
    exact hbase
  have hsum (b : ℕ) (hb : b ∈ caseOneB) : Summable (T b) := by
    have hbase := aux_dyadic_gaussian_pair_summable
      (caseOneSlotNat γ ι i b).1 (caseOneSlotNat_spaced γ ι i b)
      (caseOneSlotNat γ ι i b).2 j v
    change Summable (fun m : Fin 2 → ℕ =>
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm (caseOneScales γ ι i b m)
          (caseOneOrientation γ ι i b) j v)
    unfold caseOneScales caseOneOrientation
    exact hbase
  calc
    ∑ b ∈ caseOneB,
        aux_caseOneSlotProduct j v (caseOneSlotNat γ ι i b) ≤
        ∑ b ∈ caseOneB, (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ, T b m :=
      Finset.sum_le_sum fun b hb => hslot b hb
    _ = (8 * Real.exp (2 * Real.pi)) * ∑ b ∈ caseOneB, ∑' m : Fin 2 → ℕ, T b m := by
      rw [Finset.mul_sum]
    _ = (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ, ∑ b ∈ caseOneB, T b m := by
      rw [Summable.tsum_finsetSum hsum]
    _ = _ := by
      congr 2
      funext m
      dsimp [T]
      rw [Finset.mul_sum]

theorem gaussDominationCase1 {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (i : Fin γ.k)
    (ι : MultiplierIndex γ) (hpositive : 0 < ι.1.1) (_hvertical : ι.1.2 = 0) :
    aux_GaussianDominationConclusion γ hkn i ι (C_gaussDominationCase1) := by
  classical
  rcases caseOne_witness_side_conditions γ ι i hpositive with ⟨hcard, hscales, hdistance⟩
  have hbaseScales : ∀ b ∈ caseOneB, ∀ r : Fin 2,
      SpacedSequence ((caseOneSlotNat γ ι i b).1 r) := by
    intro b hb r
    exact caseOneSlotNat_spaced γ ι i b r
  have htail := aux_finite_dyadic_gaussian_series caseOneB
    (fun b => (caseOneSlotNat γ ι i b).1) hbaseScales
    (caseOneOrientation γ ι i) (caseOneScales γ ι i) (by
      intro b hb m r k
      rfl)
  refine ⟨{
    B := caseOneB
    card_le := hcard
    orientation := caseOneOrientation γ ι i
    scales := caseOneScales γ ι i
    scales_in_A := hscales
    distance_bound := hdistance
    estimate := ?_
    series_summable := htail.1
    series_integrable := htail.2
  }⟩
  intro j v
  let w₀ : ℝ := (v.1 + v.2) / 2
  let w₁ : ℝ := (v.2 - v.1) / 2
  have hv : (w₀ - w₁, w₀ + w₁) = v := by
    ext <;> dsimp [w₀, w₁] <;> ring
  have hpre := aux_caseOne_preGaussian_bound γ hkn ι i j hpositive w₀ w₁
  have hslot := aux_caseOne_slot_sum_gaussian_majorant γ ι i j (w₀ - w₁, w₀ + w₁)
  have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 2 := by
    rw [show C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity
  have hK : 0 ≤ max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
      (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
        C_twoBumpEstimate (3 / 2) (3 / 2)) :=
    (add_nonneg aux_caseOne_twoBump_nonneg (by norm_num)).trans (le_max_left _ _)
  have hD : 0 ≤ (32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
      C_meanFourScaleGaussianKernel 2) *
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
      max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
        (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
          C_twoBumpEstimate (3 / 2) (3 / 2)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hstd)
          aux_caseOne_meanFour_nonneg)
        (Real.rpow_nonneg (by norm_num) _)) hK
  have hprecoeff : 0 ≤ C_hKernelEstimateGaussianDomination *
      ((32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
        C_meanFourScaleGaussianKernel 2) *
        Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
        max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
          (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
            C_twoBumpEstimate (3 / 2) (3 / 2))) :=
    mul_nonneg aux_C_hKernelEstimateGaussianDomination_nonneg hD
  calc
    |nMultiplier γ hkn ι i j v| =
        |nMultiplier γ hkn ι i j (w₀ - w₁, w₀ + w₁)| := by rw [hv]
    _ ≤ C_hKernelEstimateGaussianDomination *
        ((32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
          C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2))) *
        ∑ b ∈ caseOneB,
          aux_caseOneSlotProduct j (w₀ - w₁, w₀ + w₁)
            (caseOneSlotNat γ ι i b) := hpre
    _ ≤ C_hKernelEstimateGaussianDomination *
        ((32 * Real.pi * C_standardBumpPropertiesTilde 0 2 *
          C_meanFourScaleGaussianKernel 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
          max (C_twoBumpEstimate (3 / 2) (3 / 2) + 4)
            (4 * C_bumpTriangle (-(1 / 2 : ℝ)) (1 / 2) (3 / 2) (3 / 2) *
              C_twoBumpEstimate (3 / 2) (3 / 2))) *
        ((8 * Real.exp (2 * Real.pi)) *
          ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
            ∑ b ∈ caseOneB,
              aux_dominatingGaussianTerm (caseOneScales γ ι i b m)
                (caseOneOrientation γ ι i b) j (w₀ - w₁, w₀ + w₁)) :=
      mul_le_mul_of_nonneg_left hslot hprecoeff
    _ = (C_gaussDominationCase1) *
        Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          ∑ b ∈ caseOneB,
            aux_dominatingGaussianTerm (caseOneScales γ ι i b m)
              (caseOneOrientation γ ι i b) j (w₀ - w₁, w₀ + w₁) := by
      unfold C_gaussDominationCase1
      norm_num
      ring
    _ = _ := by rw [hv]



open Filter Topology Metric

namespace aux_caseTwo
theorem scratch_integral_Ioi_scaledBracketBumpReal_three
    (s a : ℝ) (hs : 0 < s) (ha : 0 ≤ a) :
    ∫ x : ℝ in Set.Ioi a, scaledBracketBumpReal 3 s x =
      (1 / 2 : ℝ) * s * scaledBracketBumpReal 2 s a := by
  let F : ℝ → ℝ := fun x => -(1 / 2 : ℝ) * (1 + s⁻¹ * x) ^ (-2 : ℝ)
  have hderiv : ∀ x ∈ Set.Ici a, HasDerivAt F (scaledBracketBumpReal 3 s x) x := by
    intro x hx
    have hx0 : 0 ≤ x := ha.trans hx
    have hbase : 0 < 1 + s⁻¹ * x := by
      have hsInv : 0 < s⁻¹ := inv_pos.mpr hs
      nlinarith
    have hlin : HasDerivAt (fun t : ℝ => 1 + s⁻¹ * t) s⁻¹ x := by
      simpa [mul_comm, add_comm] using ((hasDerivAt_id x).const_mul s⁻¹).const_add 1
    have hpow : HasDerivAt (fun t : ℝ => (1 + s⁻¹ * t) ^ (-2 : ℝ))
        ((-2 : ℝ) * (1 + s⁻¹ * x) ^ ((-2 : ℝ) - 1) * s⁻¹) x := by
      convert hlin.rpow_const (Or.inl hbase.ne') using 1 <;> ring
    have hF := hpow.const_mul (-(1 / 2 : ℝ))
    change HasDerivAt (fun t : ℝ => -(1 / 2 : ℝ) * (1 + s⁻¹ * t) ^ (-2 : ℝ)) _ x at hF
    convert hF using 1
    · unfold scaledBracketBumpReal
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hs.le) hx0)]
      have hsInv : 0 < s⁻¹ := inv_pos.mpr hs
      norm_num
      ring
  have hlim : Tendsto F atTop (nhds 0) := by
    dsimp [F]
    have harg : Tendsto (fun x : ℝ => 1 + s⁻¹ * x) atTop atTop := by
      have harg' : Tendsto (fun x : ℝ => s⁻¹ * x + 1) atTop atTop :=
        (tendsto_id.const_mul_atTop (inv_pos.mpr hs)).atTop_add tendsto_const_nhds
      simpa [mul_comm, add_comm] using harg'
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : 0 < (2 : ℝ))).comp harg
    have hmul :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => -(1 / 2 : ℝ)) atTop (nhds (-(1 / 2 : ℝ)))).mul hpow
    convert hmul using 1 <;> simp [Function.comp_def]
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv
    (aux_integrable_scaledBracketBumpReal 3 s (by norm_num) hs).integrableOn
    hlim
  change (∫ x in Set.Ioi a, scaledBracketBumpReal 3 s x) = _
  rw [hmain]
  dsimp [F]
  unfold scaledBracketBumpReal
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hs.le) ha)]
  let Q : ℝ := (1 + s⁻¹ * a) ^ (-2 : ℝ)
  change 0 - -(1 / 2 : ℝ) * Q = (1 / 2 : ℝ) * s * (s⁻¹ * Q)
  field_simp [hs.ne']
  ring

theorem scratch_scaledBracketBump_nat_eq_real (N : ℕ) (s x : ℝ) :
    scaledBracketBump N s x = scaledBracketBumpReal (N : ℝ) s x := by
  unfold scaledBracketBump scaledBracketBumpReal
  change s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N =
    s⁻¹ * (1 + |s⁻¹ * x|) ^ (-(N : ℝ))
  rw [Real.rpow_neg (by positivity) (N : ℝ), Real.rpow_natCast]
  simp only [inv_pow]

theorem scratch_scaledBracketBump_neg (N : ℕ) (s x : ℝ) :
    scaledBracketBump N s (-x) = scaledBracketBump N s x := by
  unfold scaledBracketBump
  rw [show s⁻¹ * -x = -(s⁻¹ * x) by ring, abs_neg]

theorem scratch_integral_Ioi_scaledBracketBump_three
    (s a : ℝ) (hs : 0 < s) (ha : 0 ≤ a) :
    ∫ x : ℝ in Set.Ioi a, scaledBracketBump 3 s x =
      (1 / 2 : ℝ) * s * scaledBracketBump 2 s a := by
  have h := scratch_integral_Ioi_scaledBracketBumpReal_three s a hs ha
  convert h using 1 <;> norm_num [scratch_scaledBracketBump_nat_eq_real]

theorem scratch_primitive_Iic_bound
    {rho : ℝ → ℝ} (A s : ℝ) (hA : 0 ≤ A) (hs : 0 < s)
    (hrho : Integrable rho) (hzero : (∫ x : ℝ, rho x) = 0)
    (hdecay : ∀ x : ℝ, |rho x| ≤ A * scaledBracketBump 3 s x) (p : ℝ) :
    |∫ x : ℝ in Set.Iic p, rho x| ≤
      (A / 2) * s * scaledBracketBump 2 s p := by
  have hBint : Integrable (fun x : ℝ => A * scaledBracketBump 3 s x) := by
    convert (aux_integrable_scaledBracketBumpReal 3 s (by norm_num) hs).const_mul A using 1
    funext x
    norm_num [scratch_scaledBracketBump_nat_eq_real]
  have hmajorIoi (a : ℝ) :
      |∫ x : ℝ in Set.Ioi a, rho x| ≤
        ∫ x : ℝ in Set.Ioi a, A * scaledBracketBump 3 s x := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le (f := rho) (g := fun x : ℝ => A * scaledBracketBump 3 s x)
        hBint.integrableOn (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hdecay x))
  have hmajorIic (a : ℝ) :
      |∫ x : ℝ in Set.Iic a, rho x| ≤
        ∫ x : ℝ in Set.Iic a, A * scaledBracketBump 3 s x := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le (f := rho) (g := fun x : ℝ => A * scaledBracketBump 3 s x)
        hBint.integrableOn (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hdecay x))
  by_cases hp : 0 ≤ p
  · have hsplit := intervalIntegral.integral_Iic_add_Ioi
      hrho.integrableOn hrho.integrableOn (b := p)
    rw [hzero] at hsplit
    have hIic : (∫ x : ℝ in Set.Iic p, rho x) = -∫ x : ℝ in Set.Ioi p, rho x := by
      linarith
    rw [hIic, abs_neg]
    calc
      |∫ x : ℝ in Set.Ioi p, rho x| ≤
          ∫ x : ℝ in Set.Ioi p, A * scaledBracketBump 3 s x := hmajorIoi p
      _ = A * (∫ x : ℝ in Set.Ioi p, scaledBracketBump 3 s x) := by
        rw [integral_const_mul]
      _ = A * ((1 / 2 : ℝ) * s * scaledBracketBump 2 s p) := by
        rw [scratch_integral_Ioi_scaledBracketBump_three s p hs hp]
      _ = (A / 2) * s * scaledBracketBump 2 s p := by ring
  · have hp' : 0 ≤ -p := by linarith
    calc
      |∫ x : ℝ in Set.Iic p, rho x| ≤
          ∫ x : ℝ in Set.Iic p, A * scaledBracketBump 3 s x := hmajorIic p
      _ = ∫ x : ℝ in Set.Iic p, A * scaledBracketBump 3 s (-x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [scratch_scaledBracketBump_neg]
      _ = ∫ x : ℝ in Set.Ioi (-p), A * scaledBracketBump 3 s x := by
        simpa only using
          (integral_comp_neg_Iic p (fun x : ℝ => A * scaledBracketBump 3 s x))
      _ = A * (∫ x : ℝ in Set.Ioi (-p), scaledBracketBump 3 s x) := by
        rw [integral_const_mul]
      _ = A * ((1 / 2 : ℝ) * s * scaledBracketBump 2 s (-p)) := by
        rw [scratch_integral_Ioi_scaledBracketBump_three s (-p) hs hp']
      _ = (A / 2) * s * scaledBracketBump 2 s p := by
        rw [scratch_scaledBracketBump_neg]
        ring


namespace ScratchCase2Fourier

theorem fourScaleGaussianRho_integral_eq_zero
    (phi phiHat : ℝ → ℂ) (hphi : MemW0 phi)
    (hphiHat : phiHat = FourierTransform.fourier phi)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hplateau : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat xi = 1)
    {muMinus muPlus lambdaMinus lambdaPlus nu : ℝ}
    (hmuMinus : 0 < muMinus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧
      2 * lambdaMinus ≤ lambdaPlus ∧ lambdaPlus ≤ muPlus)
    (hrho : MemW0 (fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu)) :
    ∫ x : ℝ, fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu x = 0 := by
  let f : ℝ → ℂ := fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu
  let rho : ℝ → ℂ := fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu
  have hphiCont : Continuous phiHat :=
    aux_gaussianBumpDecomposition_phiHat_continuous phi phiHat hphi hphiHat
  have hlambdaMinus : 0 < lambdaMinus :=
    aux_gaussianBumpDecomposition_lambdaMinus_pos hmuMinus hscales.1
  have hlambdaPlus : 0 < lambdaPlus :=
    aux_gaussianBumpDecomposition_lambdaPlus_pos hmuMinus ⟨hscales.1, hscales.2.1⟩
  have hfCont : Continuous f := by
    exact aux_gaussianBumpDecomposition_rhoFrequency_continuous phiHat hphiCont hplateau
      hmuMinus hscales

  have hfSupp : HasCompactSupport f :=
    aux_gaussianBumpDecomposition_rhoFrequency_compactSupport phiHat hlambdaMinus hlambdaPlus
      hsupp muMinus muPlus nu
  have hfInt : Integrable f := hfCont.integrable_of_hasCompactSupport hfSupp
  have hrhoInt : Integrable rho := by
    exact Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hrho
  have hFourierEq : FourierTransform.fourier f = fun x : ℝ => rho (-x) := by
    funext x
    simpa [f, rho, fourScaleGaussianRho] using
      (Real.fourierInv_eq_fourier_neg f (-x)).symm
  have hFourierInt : Integrable (FourierTransform.fourier f) := by
    rw [hFourierEq]
    exact (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hrhoInt
  have hFourierRho : FourierTransform.fourier rho = f := by
    change FourierTransform.fourier (FourierTransformInv.fourierInv f) = f
    exact hfCont.fourier_fourierInv_eq hfInt hFourierInt
  have hfZero : f 0 = 0 := by
    simp [f, fourScaleGaussianRhoFrequency]
  change ∫ x : ℝ, rho x = 0
  calc
    ∫ x : ℝ, rho x = FourierTransform.fourier rho 0 := by
      rw [Real.fourier_real_eq]
      simp
    _ = f 0 := congrFun hFourierRho 0
    _ = 0 := hfZero

theorem primitive_integration_by_parts (rho g : ℝ → ℝ) (hrho : Continuous rho)
    (hg : ∀ x : ℝ, DifferentiableAt ℝ g x)
    (hprimeg : Integrable (fun x : ℝ => rho x * g x))
    (hprimitiveDeriv : Integrable (fun x : ℝ =>
      (∫ q : ℝ in (0 : ℝ)..x, rho q) * fderiv ℝ g x 1))
    (hprimitive : Integrable (fun x : ℝ => (∫ q : ℝ in (0 : ℝ)..x, rho q) * g x)) :
    (∫ x : ℝ, rho x * g x) =
      -∫ x : ℝ, (∫ q : ℝ in (0 : ℝ)..x, rho q) * fderiv ℝ g x 1 := by
  let R : ℝ → ℝ := fun x => ∫ q : ℝ in (0 : ℝ)..x, rho q
  have hRderiv (x : ℝ) : HasDerivAt R (rho x) x := by
    exact (hrho.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hRdiff (x : ℝ) : DifferentiableAt ℝ R x := (hRderiv x).differentiableAt
  have hfderiv (x : ℝ) : fderiv ℝ R x 1 = rho x := by
    rw [(hRderiv x).hasFDerivAt.fderiv]
    simp
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := R) (g := g) (v := (1 : ℝ))
    (by simpa [hfderiv] using hprimeg)
    (by simpa [R] using hprimitiveDeriv)
    (by simpa [R] using hprimitive)
    (fun x _ => hRdiff x)
    (fun x _ => hg x)
  have hparts' :
      (∫ x : ℝ, R x * fderiv ℝ g x 1) = -∫ x : ℝ, rho x * g x := by
    simpa [hfderiv] using hparts
  change (∫ x : ℝ, rho x * g x) = -∫ x : ℝ, R x * fderiv ℝ g x 1
  rw [hparts']
  ring

theorem primitive_integration_by_parts_of_bounds (rho g : ℝ → ℝ)
    (hrho : Continuous rho) (hg : ∀ x : ℝ, DifferentiableAt ℝ g x)
    (hgint : Integrable g) (C_rho C_R : ℝ)
    (hrhoBound : ∀ x : ℝ, |rho x| ≤ C_rho)
    (hRBound : ∀ x : ℝ, |∫ q : ℝ in (0 : ℝ)..x, rho q| ≤ C_R)
    (hprimitiveDeriv : Integrable (fun x : ℝ =>
      (∫ q : ℝ in (0 : ℝ)..x, rho q) * fderiv ℝ g x 1)) :
    (∫ x : ℝ, rho x * g x) =
      -∫ x : ℝ, (∫ q : ℝ in (0 : ℝ)..x, rho q) * fderiv ℝ g x 1 := by
  have hprimeg : Integrable (fun x : ℝ => rho x * g x) := by
    have hmajor : Integrable (fun x : ℝ => C_rho * |g x|) := by
      simpa [Real.norm_eq_abs] using hgint.norm.const_mul C_rho
    refine hmajor.mono'
      (hrho.aestronglyMeasurable.mul hgint.aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hrhoBound x) (abs_nonneg _)
  let R : ℝ → ℝ := fun x => ∫ q : ℝ in (0 : ℝ)..x, rho q
  have hRderiv (x : ℝ) : HasDerivAt R (rho x) x := by
    exact (hrho.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hRcont : Continuous R := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hRderiv x).continuousAt
  have hprimitive : Integrable (fun x : ℝ => R x * g x) := by
    have hmajor : Integrable (fun x : ℝ => C_R * |g x|) := by
      simpa [Real.norm_eq_abs] using hgint.norm.const_mul C_R
    refine hmajor.mono'
      (hRcont.aestronglyMeasurable.mul hgint.aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hRBound x) (abs_nonneg _)
  exact primitive_integration_by_parts rho g hrho hg hprimeg hprimitiveDeriv
    (by simpa [R] using hprimitive)

theorem iic_primitive_integration_by_parts (rho g : ℝ → ℝ) (hrho : Continuous rho)
    (hrhoInt : Integrable rho) (hg : ∀ x : ℝ, DifferentiableAt ℝ g x)
    (hprimeg : Integrable (fun x : ℝ => rho x * g x))
    (hprimitiveDeriv : Integrable (fun x : ℝ =>
      (∫ q : ℝ in Set.Iic x, rho q) * fderiv ℝ g x 1))
    (hprimitive : Integrable (fun x : ℝ => (∫ q : ℝ in Set.Iic x, rho q) * g x)) :
    (∫ x : ℝ, rho x * g x) =
      -∫ x : ℝ, (∫ q : ℝ in Set.Iic x, rho q) * fderiv ℝ g x 1 := by
  let P : ℝ → ℝ := fun x => ∫ q : ℝ in Set.Iic x, rho q
  let R : ℝ → ℝ := fun x => ∫ q : ℝ in (0 : ℝ)..x, rho q
  have hP_eq (x : ℝ) : P x = P 0 + R x := by
    have h := intervalIntegral.integral_Iic_sub_Iic (f := rho)
      (a := (0 : ℝ)) (b := x) hrhoInt.integrableOn hrhoInt.integrableOn
    dsimp [P, R]
    linarith
  have hPfun : P = fun x : ℝ => P 0 + R x := by
    funext x
    exact hP_eq x
  have hRderiv (x : ℝ) : HasDerivAt R (rho x) x := by
    exact (hrho.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hPderiv (x : ℝ) : HasDerivAt P (rho x) x := by
    have hsum := (hasDerivAt_const (x := x) (c := P 0)).add (hRderiv x)
    have heq : P =ᶠ[nhds x] ((fun _ : ℝ => P 0) + R) := by
      filter_upwards [] with y
      exact hP_eq y
    have hmain := hsum.congr_of_eventuallyEq heq
    simpa using hmain
  have hPdiff (x : ℝ) : DifferentiableAt ℝ P x := (hPderiv x).differentiableAt
  have hfderiv (x : ℝ) : fderiv ℝ P x 1 = rho x := by
    rw [(hPderiv x).hasFDerivAt.fderiv]
    simp
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := P) (g := g) (v := (1 : ℝ))
    (by simpa [hfderiv] using hprimeg)
    (by simpa [P] using hprimitiveDeriv)
    (by simpa [P] using hprimitive)
    (fun x _ => hPdiff x)
    (fun x _ => hg x)
  have hparts' :
      (∫ x : ℝ, P x * fderiv ℝ g x 1) = -∫ x : ℝ, rho x * g x := by
    simpa [hfderiv] using hparts
  change (∫ x : ℝ, rho x * g x) = -∫ x : ℝ, P x * fderiv ℝ g x 1
  rw [hparts']
  ring

theorem iic_primitive_integration_by_parts_of_bounds (rho g : ℝ → ℝ)
    (hrho : Continuous rho) (hrhoInt : Integrable rho)
    (hg : ∀ x : ℝ, DifferentiableAt ℝ g x) (hgint : Integrable g)
    (C_rho C_P : ℝ) (hrhoBound : ∀ x : ℝ, |rho x| ≤ C_rho)
    (hPBound : ∀ x : ℝ, |∫ q : ℝ in Set.Iic x, rho q| ≤ C_P)
    (hprimitiveDeriv : Integrable (fun x : ℝ =>
      (∫ q : ℝ in Set.Iic x, rho q) * fderiv ℝ g x 1)) :
    (∫ x : ℝ, rho x * g x) =
      -∫ x : ℝ, (∫ q : ℝ in Set.Iic x, rho q) * fderiv ℝ g x 1 := by
  have hprimeg : Integrable (fun x : ℝ => rho x * g x) := by
    have hmajor : Integrable (fun x : ℝ => C_rho * |g x|) := by
      simpa [Real.norm_eq_abs] using hgint.norm.const_mul C_rho
    refine hmajor.mono'
      (hrho.aestronglyMeasurable.mul hgint.aestronglyMeasurable) ?_
    filter_upwards [] with x

    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hrhoBound x) (abs_nonneg _)
  let P : ℝ → ℝ := fun x => ∫ q : ℝ in Set.Iic x, rho q
  let R : ℝ → ℝ := fun x => ∫ q : ℝ in (0 : ℝ)..x, rho q
  have hP_eq (x : ℝ) : P x = P 0 + R x := by
    have h := intervalIntegral.integral_Iic_sub_Iic (f := rho)
      (a := (0 : ℝ)) (b := x) hrhoInt.integrableOn hrhoInt.integrableOn
    dsimp [P, R]
    linarith
  have hRderiv (x : ℝ) : HasDerivAt R (rho x) x := by
    exact (hrho.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hPderiv (x : ℝ) : HasDerivAt P (rho x) x := by
    have hsum := (hasDerivAt_const (x := x) (c := P 0)).add (hRderiv x)
    have heq : P =ᶠ[nhds x] ((fun _ : ℝ => P 0) + R) := by
      filter_upwards [] with y
      exact hP_eq y
    have hmain := hsum.congr_of_eventuallyEq heq
    simpa using hmain
  have hPcont : Continuous P := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hPderiv x).continuousAt
  have hprimitive : Integrable (fun x : ℝ => P x * g x) := by
    have hmajor : Integrable (fun x : ℝ => C_P * |g x|) := by
      simpa [Real.norm_eq_abs] using hgint.norm.const_mul C_P
    refine hmajor.mono'
      (hPcont.aestronglyMeasurable.mul hgint.aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hPBound x) (abs_nonneg _)
  exact iic_primitive_integration_by_parts (rho := rho) (g := g) hrho hrhoInt hg hprimeg
    hprimitiveDeriv (by simpa only [P] using hprimitive)

theorem fderiv_translate_negDiagonal (F : ℝ × ℝ → ℝ) (w : ℝ × ℝ) (p : ℝ)
    (hF : DifferentiableAt ℝ
      (fun t : ℝ => F (w.1 - p + t, w.2 - p + t)) 0) :
    fderiv ℝ (fun q : ℝ => F (w.1 - q, w.2 - q)) p 1 =
      -aux_diagonalDerivative F (w.1 - p, w.2 - p) := by
  let z : ℝ × ℝ := (w.1 - p, w.2 - p)
  let D : ℝ → ℝ := fun t => F (z.1 + t, z.2 + t)
  have hD : HasDerivAt D (aux_diagonalDerivative F z) 0 := by
    dsimp [D, z]
    unfold aux_diagonalDerivative
    simpa using hF.hasDerivAt
  have hu : HasDerivAt (fun q : ℝ => p - q) (-1 : ℝ) p := by
    have hu0 := (hasDerivAt_const (x := p) (c := p)).sub (hasDerivAt_id p)
    have heq0 : (fun q : ℝ => p - q) =ᶠ[nhds p]
        ((fun _ : ℝ => p) - id) := by
      filter_upwards [] with q
      rfl
    have hu1 := hu0.congr_of_eventuallyEq heq0
    simpa using hu1
  have hD0 : HasDerivAt D (aux_diagonalDerivative F z) (p - p) := by
    simpa using hD
  have hcomp := hD0.comp p hu
  have hcomp' : HasDerivAt (fun q : ℝ => D (p - q))
      (aux_diagonalDerivative F z * -1) p := by
    simpa only [Function.comp_def] using hcomp
  have heq : (fun q : ℝ => F (w.1 - q, w.2 - q)) =ᶠ[nhds p]
      (fun q : ℝ => D (p - q)) := by
    filter_upwards [] with q
    dsimp [D, z]

    apply congrArg F
    ext <;> ring
  have hg := hcomp'.congr_of_eventuallyEq heq
  rw [hg.hasFDerivAt.fderiv]
  simp
  ring

theorem hMultiplier_diagonal_differentiable {n : ℕ} (gamma : GeometricParameters n)
    (i : Fin gamma.k) (j : ℤ) (v : ℝ × ℝ) :
    DifferentiableAt ℝ
      (fun t : ℝ => hMultiplier gamma i j (v.1 + t, v.2 + t)) 0 := by
  have hs0 : DifferentiableAt ℝ (sMultiplier gamma i j) v.1 :=
    (aux_sMultiplier_differentiable gamma i j).differentiableAt
  have hs1 : DifferentiableAt ℝ (sMultiplier gamma i j) v.2 :=
    (aux_sMultiplier_differentiable gamma i j).differentiableAt
  have htensor : DifferentiableAt ℝ (fun t : ℝ =>
      sMultiplier gamma i j (v.1 + t) * sMultiplier gamma i j (v.2 + t)) 0 :=
    aux_tensor_line_differentiable hs0 hs1
  have hprev := aux_gammaGaussian_diagonal_differentiable gamma i (j - 1) v
  have hcurr := aux_gammaGaussian_diagonal_differentiable gamma i j v
  have hgauss : DifferentiableAt ℝ (fun t : ℝ =>
      gaussianDifference gamma i j (v.1 + t, v.2 + t)) 0 := by
    change DifferentiableAt ℝ
      ((fun t : ℝ => gammaGaussian gamma i (j - 1) (v.1 + t, v.2 + t)) -
        fun t : ℝ => gammaGaussian gamma i j (v.1 + t, v.2 + t)) 0
    exact hprev.sub hcurr
  change DifferentiableAt ℝ
    ((fun t : ℝ => sMultiplier gamma i j (v.1 + t) * sMultiplier gamma i j (v.2 + t)) -
      fun t : ℝ => gaussianDifference gamma i j (v.1 + t, v.2 + t)) 0
  exact htensor.sub hgauss

theorem hMultiplier_fderiv_translate_negDiagonal {n : ℕ}
    (gamma : GeometricParameters n) (i : Fin gamma.k) (j : ℤ)
    (w : ℝ × ℝ) (p : ℝ) :
    fderiv ℝ (fun q : ℝ => hMultiplier gamma i j (w.1 - q, w.2 - q)) p 1 =
      -aux_diagonalDerivative (hMultiplier gamma i j) (w.1 - p, w.2 - p) := by
  apply fderiv_translate_negDiagonal
  exact hMultiplier_diagonal_differentiable gamma i j (w.1 - p, w.2 - p)

/-- The symmetric order-free two-bump estimate at the quadratic exponent. -/
theorem scratch_twoBumpIntegral_max_two (x₀ x₁ s₀ s₁ : ℝ)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) :
    (∫ p : ℝ, scaledBracketBump 2 s₀ (x₀ - p) *
      scaledBracketBump 2 s₁ (x₁ - p)) ≤
      C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max s₀ s₁) (x₀ - x₁) := by
  have hnon (p : ℝ) : 0 ≤
      scaledBracketBump 2 s₀ (x₀ - p) * scaledBracketBump 2 s₁ (x₁ - p) :=
    mul_nonneg (aux_scaledBracketBump_nonneg 2 hs₀ _)
      (aux_scaledBracketBump_nonneg 2 hs₁ _)
  rw [← abs_of_nonneg (integral_nonneg hnon)]
  by_cases h : s₀ ≤ s₁
  · have htwo := twoBumpEstimate x₁ x₀ s₁ s₀ 2 2 hs₁ hs₀ h
      (by norm_num) (by norm_num)
    calc
      |∫ p : ℝ, scaledBracketBump 2 s₀ (x₀ - p) *
          scaledBracketBump 2 s₁ (x₁ - p)| =
          |∫ p : ℝ, scaledBracketBumpReal 2 s₁ (x₁ - p) *
            scaledBracketBumpReal 2 s₀ (x₀ - p)| := by
              congr 1
              apply integral_congr_ae
              filter_upwards [] with p
              rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq,
                aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
              ring
      _ ≤ C_twoBumpEstimate 2 2 *
          scaledBracketBumpReal (min 2 2) s₁ (x₁ - x₀) := htwo
      _ = C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max s₀ s₁) (x₀ - x₁) := by
            rw [min_self, max_eq_right h,
              show x₁ - x₀ = -(x₀ - x₁) by ring, aux_scaledBracketBumpReal_neg,
              aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
  · have h' : s₁ ≤ s₀ := le_of_not_ge h
    have htwo := twoBumpEstimate x₀ x₁ s₀ s₁ 2 2 hs₀ hs₁ h'
      (by norm_num) (by norm_num)
    calc
      |∫ p : ℝ, scaledBracketBump 2 s₀ (x₀ - p) *
          scaledBracketBump 2 s₁ (x₁ - p)| =
          |∫ p : ℝ, scaledBracketBumpReal 2 s₀ (x₀ - p) *
            scaledBracketBumpReal 2 s₁ (x₁ - p)| := by
              congr 1
              apply integral_congr_ae
              filter_upwards [] with p
              rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq,
                aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
      _ ≤ C_twoBumpEstimate 2 2 *
          scaledBracketBumpReal (min 2 2) s₀ (x₀ - x₁) := htwo
      _ = C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max s₀ s₁) (x₀ - x₁) := by
            rw [min_self, max_eq_left h', aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]


theorem scratch_bumpTriangle_const_two :
    aux_C_bumpTriangleNat 1 1 2 2 = C_bumpTriangle 1 1 2 2 := by
  norm_num [aux_C_bumpTriangleNat, C_bumpTriangle, C_bumpTriangleTilde,
    Real.rpow_natCast]

/-- Integrability of a product of two translated quadratic scaled bumps. -/
theorem scratch_B2_product_integrable (x₀ x₁ s₀ s₁ : ℝ)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) :
    Integrable (fun p : ℝ => scaledBracketBump 2 s₀ (x₀ - p) *
      scaledBracketBump 2 s₁ (x₁ - p)) := by
  have hleft : Integrable (fun p : ℝ => scaledBracketBump 2 s₀ (x₀ - p)) := by
    convert aux_integrable_scaledBracketBumpReal_translate 2 s₀ x₀
      (by norm_num) hs₀ using 1
    funext p
    rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
  have hright : Integrable (fun p : ℝ => scaledBracketBump 2 s₁ (x₁ - p)) := by
    convert aux_integrable_scaledBracketBumpReal_translate 2 s₁ x₁
      (by norm_num) hs₁ using 1
    funext p
    rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
  refine hleft.mul_bdd (c := s₁⁻¹) hright.aestronglyMeasurable ?_
  filter_upwards [] with p
  rw [Real.norm_eq_abs,
    abs_of_nonneg (aux_scaledBracketBump_nonneg 2 hs₁ _)]
  exact aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv hs₁

theorem scratch_scaledBracketBump_neg (N : ℕ) (s x : ℝ) :
    scaledBracketBump N s (-x) = scaledBracketBump N s x := by
  unfold scaledBracketBump
  rw [mul_neg, abs_neg]

theorem scratch_B2_simul_rescale (c s x : ℝ) (hc : 0 < c) :
    c * scaledBracketBump 2 (c * s) (c * x) = scaledBracketBump 2 s x := by
  unfold scaledBracketBump
  have hcne : c ≠ 0 := ne_of_gt hc
  have harg : (c * s)⁻¹ * (c * x) = s⁻¹ * x := by
    field_simp [hcne]
  have hinv : c * (c * s)⁻¹ = s⁻¹ := by
    field_simp [hcne]
  rw [harg]
  calc
    c * ((c * s)⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ 2) =
        (c * (c * s)⁻¹) * (1 + |s⁻¹ * x|)⁻¹ ^ 2 := by ring
    _ = s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ 2 := by rw [hinv]

theorem scratch_B2_scale_down_sqrt_two (t x : ℝ) (ht : 0 < t) :
    scaledBracketBump 2 (t / Real.sqrt 2) x ≤
      Real.sqrt 2 * scaledBracketBump 2 t x := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_one : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  apply aux_scaledBracketBump_scale_le 2 (s := t / Real.sqrt 2)
    (t := t) (A := Real.sqrt 2)
  · exact div_pos ht hsqrt
  · exact ht
  · apply (div_le_iff₀ hsqrt).2
    nlinarith
  · exact hsqrt.le
  · apply le_of_eq
    field_simp [hsqrt.ne']

theorem scratch_caseTwo_orthogonal_dichotomy (x y : ℝ) :
    |x| ≤ 3 * |(-x + y) / Real.sqrt 2| ∨
      |(x + y) / Real.sqrt 2| ≤ 3 * |y| := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hsqrt_le : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  let a : ℝ := (x + y) / Real.sqrt 2
  let b : ℝ := (-x + y) / Real.sqrt 2
  have hx : x = y - Real.sqrt 2 * b := by
    dsimp [b]
    field_simp [ne_of_gt hsqrt]
    ring
  have ha : a = Real.sqrt 2 * y - b := by
    dsimp [a, b]
    field_simp [ne_of_gt hsqrt]
    rw [hsqrt_sq]
    ring
  by_cases hleft : |x| ≤ 3 * |b|
  · exact Or.inl (by simpa [b] using hleft)
  · right
    have hleft' : 3 * |b| < |x| := lt_of_not_ge hleft
    have hboundx : |x| ≤ |y| + Real.sqrt 2 * |b| := by
      rw [hx]
      calc
        |y - Real.sqrt 2 * b| ≤ |y| + |Real.sqrt 2 * b| := by
          simpa using (abs_sub_le y 0 (Real.sqrt 2 * b))
        _ = |y| + Real.sqrt 2 * |b| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsqrtb : Real.sqrt 2 * |b| ≤ (3 / 2 : ℝ) * |b| :=
      mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg _)
    have hbsmall : (3 / 2 : ℝ) * |b| < |y| := by
      nlinarith [hboundx, hsqrtb]
    have habound : |a| ≤ Real.sqrt 2 * |y| + |b| := by
      rw [ha]
      calc
        |Real.sqrt 2 * y - b| ≤ |Real.sqrt 2 * y| + |b| := by
          simpa using (abs_sub_le (Real.sqrt 2 * y) 0 b)
        _ = Real.sqrt 2 * |y| + |b| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsqrty : Real.sqrt 2 * |y| ≤ (3 / 2 : ℝ) * |y| :=
      mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg _)
    have hbsmall' : |b| ≤ (2 / 3 : ℝ) * |y| := by
      nlinarith [hbsmall]
    have hfinal : |a| ≤ 3 * |y| := by
      nlinarith [habound, hsqrty, hbsmall']
    simpa [a] using hfinal

theorem scratch_caseTwo_orthogonal_decay_two (x y lam t : ℝ)
    (hlam : 0 < lam) (ht : 0 < t) :
    scaledBracketBump 2 lam y *
      scaledBracketBump 2 t ((-x + y) / Real.sqrt 2) ≤
      9 *
        (scaledBracketBump 2 lam y * scaledBracketBump 2 t x +
          scaledBracketBump 2 lam ((x + y) / Real.sqrt 2) *
            scaledBracketBump 2 t ((-x + y) / Real.sqrt 2)) := by
  have hraw := aux_orthogonalDecay_from_domination
    (A := (3 : ℝ)) (n₀ := (2 : ℝ)) (n₁ := (2 : ℝ))
    (s₀ := lam) (s₁ := t) (u₀ := y) (u₁ := (-x + y) / Real.sqrt 2)
    (p₀ := x) (p₁ := (x + y) / Real.sqrt 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlam ht
    (scratch_caseTwo_orthogonal_dichotomy x y)
  have hraw' :
      scaledBracketBump 2 lam y *
          scaledBracketBump 2 t ((-x + y) / Real.sqrt 2) ≤
        max (Real.rpow 3 (2 : ℝ)) (Real.rpow 3 (2 : ℝ)) *
          (scaledBracketBump 2 lam y * scaledBracketBump 2 t x +
            scaledBracketBump 2 lam ((x + y) / Real.sqrt 2) *
              scaledBracketBump 2 t ((-x + y) / Real.sqrt 2)) := by
    simpa only [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq] using hraw
  have hcoef : max (Real.rpow 3 (2 : ℝ)) (Real.rpow 3 (2 : ℝ)) ≤ 9 := by
    norm_num [Real.rpow_natCast]
  have hnon : 0 ≤
      scaledBracketBump 2 lam y * scaledBracketBump 2 t x +
        scaledBracketBump 2 lam ((x + y) / Real.sqrt 2) *
          scaledBracketBump 2 t ((-x + y) / Real.sqrt 2) := by
    apply add_nonneg <;> apply mul_nonneg <;>
      first | exact aux_scaledBracketBump_nonneg 2 hlam _ | exact aux_scaledBracketBump_nonneg 2 ht _
  exact hraw'.trans (mul_le_mul_of_nonneg_right hcoef hnon)

/-- The required scalar orthogonal split in the Case-2 coordinates.  The
constant `9` is within the permitted harmless loss from the blueprint's `8`. -/
theorem scratch_caseTwo_orthogonal_split (v₀ v₁ lam t : ℝ)
    (hlam : 0 < lam) (ht : 0 < t) :
    scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t (v₀ - v₁) ≤
      9 *
        (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t v₁ +
          scaledBracketBump 2 lam ((v₀ + v₁) / Real.sqrt 2) *

            scaledBracketBump 2 t ((v₀ - v₁) / Real.sqrt 2)) := by
  let c : ℝ := Real.sqrt 2
  let u : ℝ := (v₀ - v₁) / c
  let z : ℝ := (v₀ + v₁) / c
  have hc : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.2 (by norm_num)
  have hcne : c ≠ 0 := ne_of_gt hc
  have hu : c * u = v₀ - v₁ := by
    dsimp [u]
    field_simp [hcne]
  have hscale : c * (t / c) = t := by
    field_simp [hcne]

  have hres := scratch_B2_simul_rescale c (t / c) u hc
  have hres' : c * scaledBracketBump 2 t (v₀ - v₁) =
      scaledBracketBump 2 (t / c) u := by
    convert hres using 1 <;> simp only [hscale, hu]
  have hleft : c *
      (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t (v₀ - v₁)) =
      scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (t / c) u := by
    rw [show c * (scaledBracketBump 2 lam v₀ *
        scaledBracketBump 2 t (v₀ - v₁)) =
        scaledBracketBump 2 lam v₀ *
          (c * scaledBracketBump 2 t (v₀ - v₁)) by ring, hres']
  have hleft' : c⁻¹ *
      (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (t / c) u) =
      scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t (v₀ - v₁) := by
    rw [← hleft]
    field_simp [hcne]
  have horth := scratch_caseTwo_orthogonal_decay_two v₁ v₀ lam (t / c)
    hlam (div_pos ht hc)
  have horth' :
      scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (t / c) u ≤
        9 * (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (t / c) v₁ +
          scaledBracketBump 2 lam z * scaledBracketBump 2 (t / c) u) := by
    convert horth using 1 <;> dsimp [u, z, c] <;> ring
  have hsmall₁ := scratch_B2_scale_down_sqrt_two t v₁ ht
  have hsmallu := scratch_B2_scale_down_sqrt_two t u ht
  have hA : 0 ≤ scaledBracketBump 2 lam v₀ :=
    aux_scaledBracketBump_nonneg 2 hlam _
  have hZ : 0 ≤ scaledBracketBump 2 lam z :=
    aux_scaledBracketBump_nonneg 2 hlam _
  have hsumscale :
      scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (t / c) v₁ +
        scaledBracketBump 2 lam z * scaledBracketBump 2 (t / c) u ≤
      c * (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t v₁ +
        scaledBracketBump 2 lam z * scaledBracketBump 2 t u) := by
    calc
      scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (t / c) v₁ +
          scaledBracketBump 2 lam z * scaledBracketBump 2 (t / c) u ≤
          scaledBracketBump 2 lam v₀ *
            (c * scaledBracketBump 2 t v₁) +
          scaledBracketBump 2 lam z *
            (c * scaledBracketBump 2 t u) :=
        add_le_add (mul_le_mul_of_nonneg_left hsmall₁ hA)
          (mul_le_mul_of_nonneg_left hsmallu hZ)
      _ = c * (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t v₁ +
        scaledBracketBump 2 lam z * scaledBracketBump 2 t u) := by ring
  have hcinv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have htargetnonneg : 0 ≤
      scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t v₁ +
        scaledBracketBump 2 lam z * scaledBracketBump 2 t u := by
    apply add_nonneg <;> apply mul_nonneg <;>
      first | exact aux_scaledBracketBump_nonneg 2 hlam _ | exact aux_scaledBracketBump_nonneg 2 ht _
  change scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t (v₀ - v₁) ≤
    9 * (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t v₁ +
      scaledBracketBump 2 lam z * scaledBracketBump 2 t u)
  calc
    scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t (v₀ - v₁) =
        c⁻¹ * (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (t / c) u) :=
      hleft'.symm
    _ ≤ c⁻¹ *
        (9 * (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (t / c) v₁ +
          scaledBracketBump 2 lam z * scaledBracketBump 2 (t / c) u)) :=
      mul_le_mul_of_nonneg_left horth' hcinv
    _ ≤ c⁻¹ *
        (9 * (c * (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t v₁ +
          scaledBracketBump 2 lam z * scaledBracketBump 2 t u))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hsumscale (by norm_num)
      · exact hcinv
    _ = 9 * (scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t v₁ +
      scaledBracketBump 2 lam z * scaledBracketBump 2 t u) := by
      field_simp [hcne]

/-- The three-bump part of a Case-2 orientation-zero occurrence, before the
orthogonal-coordinate split. -/
theorem scratch_caseTwo_u0_threeBump_raw (v₀ v₁ lam t₀ t₁ : ℝ)
    (hlam : 0 < lam) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁) :
    (∫ p : ℝ, scaledBracketBump 2 lam p *
      scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)) ≤
      C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
        (scaledBracketBump 2 t₀ v₀ *
            scaledBracketBump 2 (max lam t₁) v₁ +
          scaledBracketBump 2 lam v₀ *
            scaledBracketBump 2 (max t₀ t₁) (v₀ - v₁)) := by
  let Ktri : ℝ := aux_C_bumpTriangleNat 1 1 2 2
  let f : ℝ → ℝ := fun p => scaledBracketBump 2 lam p *
    scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)
  let g₀ : ℝ → ℝ := fun p => scaledBracketBump 2 t₀ v₀ *
    (scaledBracketBump 2 lam p * scaledBracketBump 2 t₁ (v₁ - p))
  let g₁ : ℝ → ℝ := fun p => scaledBracketBump 2 lam v₀ *
    (scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p))
  have hKtri : 0 ≤ Ktri := by
    norm_num [Ktri, aux_C_bumpTriangleNat, C_bumpTriangleTilde]
  have htri (p : ℝ) :
      scaledBracketBump 2 lam p * scaledBracketBump 2 t₀ (v₀ - p) ≤
        Ktri * (scaledBracketBump 2 lam p * scaledBracketBump 2 t₀ v₀ +
          scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t₀ (v₀ - p)) := by
    dsimp [Ktri]
    exact aux_bumpTriangleNat 2 2 (c₀ := (1 : ℝ)) (c₁ := (1 : ℝ))
      (u := p) (v := v₀ - p) (w := v₀) (s₀ := lam) (s₁ := t₀)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlam ht₀ (by ring)
  have hpoint (p : ℝ) : f p ≤ Ktri * (g₀ p + g₁ p) := by
    have hnon : 0 ≤ scaledBracketBump 2 t₁ (v₁ - p) :=
      aux_scaledBracketBump_nonneg 2 ht₁ _
    dsimp [f, g₀, g₁]
    calc
      scaledBracketBump 2 lam p * scaledBracketBump 2 t₀ (v₀ - p) *
          scaledBracketBump 2 t₁ (v₁ - p) =
          (scaledBracketBump 2 lam p * scaledBracketBump 2 t₀ (v₀ - p)) *
            scaledBracketBump 2 t₁ (v₁ - p) := by ring
      _ ≤ (Ktri * (scaledBracketBump 2 lam p * scaledBracketBump 2 t₀ v₀ +
          scaledBracketBump 2 lam v₀ * scaledBracketBump 2 t₀ (v₀ - p))) *
            scaledBracketBump 2 t₁ (v₁ - p) :=
          mul_le_mul_of_nonneg_right (htri p) hnon
      _ = Ktri * (g₀ p + g₁ p) := by ring
  have hprod₀ : Integrable (fun p : ℝ => scaledBracketBump 2 lam p *
      scaledBracketBump 2 t₁ (v₁ - p)) := by
    have hbase := scratch_B2_product_integrable 0 v₁ lam t₁ hlam ht₁
    convert hbase using 1
    funext p
    rw [show (0 : ℝ) - p = -p by ring, scratch_scaledBracketBump_neg]
  have hprod₁ : Integrable (fun p : ℝ => scaledBracketBump 2 t₀ (v₀ - p) *
      scaledBracketBump 2 t₁ (v₁ - p)) :=
    scratch_B2_product_integrable v₀ v₁ t₀ t₁ ht₀ ht₁
  have hg₀ : Integrable g₀ := by
    dsimp [g₀]
    exact hprod₀.const_mul _
  have hg₁ : Integrable g₁ := by
    dsimp [g₁]
    exact hprod₁.const_mul _
  have hmajor : Integrable (fun p : ℝ => Ktri * (g₀ p + g₁ p)) :=
    (hg₀.add hg₁).const_mul Ktri
  have hnon (p : ℝ) : 0 ≤ f p := by
    dsimp [f]
    exact mul_nonneg
      (mul_nonneg (aux_scaledBracketBump_nonneg 2 hlam _)
        (aux_scaledBracketBump_nonneg 2 ht₀ _))

      (aux_scaledBracketBump_nonneg 2 ht₁ _)
  have hint : (∫ p : ℝ, f p) ≤ ∫ p : ℝ, Ktri * (g₀ p + g₁ p) :=
    integral_mono_of_nonneg (ae_of_all _ hnon) hmajor (ae_of_all _ hpoint)
  have htwo₀base := scratch_twoBumpIntegral_max_two 0 v₁ lam t₁ hlam ht₁
  have htwo₀ : (∫ p : ℝ, scaledBracketBump 2 lam p *
      scaledBracketBump 2 t₁ (v₁ - p)) ≤
      C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max lam t₁) v₁ := by
    calc
      (∫ p : ℝ, scaledBracketBump 2 lam p * scaledBracketBump 2 t₁ (v₁ - p)) =
          ∫ p : ℝ, scaledBracketBump 2 lam (0 - p) *
            scaledBracketBump 2 t₁ (v₁ - p) := by
              apply integral_congr_ae
              filter_upwards [] with p
              rw [show (0 : ℝ) - p = -p by ring, scratch_scaledBracketBump_neg]
      _ ≤ C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max lam t₁) (0 - v₁) :=
        htwo₀base
      _ = C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max lam t₁) v₁ := by
        rw [show (0 : ℝ) - v₁ = -v₁ by ring, scratch_scaledBracketBump_neg]
  have htwo₁ := scratch_twoBumpIntegral_max_two v₀ v₁ t₀ t₁ ht₀ ht₁
  have hg₀bound : (∫ p : ℝ, g₀ p) ≤
      scaledBracketBump 2 t₀ v₀ *
        (C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max lam t₁) v₁) := by
    calc
      (∫ p : ℝ, g₀ p) = scaledBracketBump 2 t₀ v₀ *
          (∫ p : ℝ, scaledBracketBump 2 lam p * scaledBracketBump 2 t₁ (v₁ - p)) := by
            dsimp [g₀]
            rw [integral_const_mul]
      _ ≤ scaledBracketBump 2 t₀ v₀ *
          (C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max lam t₁) v₁) :=
        mul_le_mul_of_nonneg_left htwo₀ (aux_scaledBracketBump_nonneg 2 ht₀ _)
  have hg₁bound : (∫ p : ℝ, g₁ p) ≤
      scaledBracketBump 2 lam v₀ *
        (C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max t₀ t₁) (v₀ - v₁)) := by
    calc
      (∫ p : ℝ, g₁ p) = scaledBracketBump 2 lam v₀ *
          (∫ p : ℝ, scaledBracketBump 2 t₀ (v₀ - p) *
            scaledBracketBump 2 t₁ (v₁ - p)) := by
            dsimp [g₁]
            rw [integral_const_mul]
      _ ≤ scaledBracketBump 2 lam v₀ *
          (C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max t₀ t₁) (v₀ - v₁)) :=
        mul_le_mul_of_nonneg_left htwo₁ (aux_scaledBracketBump_nonneg 2 hlam _)
  have hCeq := scratch_bumpTriangle_const_two
  change (∫ p : ℝ, f p) ≤
    C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
      (scaledBracketBump 2 t₀ v₀ * scaledBracketBump 2 (max lam t₁) v₁ +
        scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (max t₀ t₁) (v₀ - v₁))
  calc
    (∫ p : ℝ, f p) ≤ ∫ p : ℝ, Ktri * (g₀ p + g₁ p) := hint
    _ = Ktri * ((∫ p : ℝ, g₀ p) + ∫ p : ℝ, g₁ p) := by
      rw [integral_const_mul, integral_add hg₀ hg₁]
    _ ≤ Ktri *
        (scaledBracketBump 2 t₀ v₀ *
            (C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max lam t₁) v₁) +
          scaledBracketBump 2 lam v₀ *
            (C_twoBumpEstimate 2 2 * scaledBracketBump 2 (max t₀ t₁) (v₀ - v₁))) :=
      mul_le_mul_of_nonneg_left (add_le_add hg₀bound hg₁bound) hKtri
    _ = C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
        (scaledBracketBump 2 t₀ v₀ * scaledBracketBump 2 (max lam t₁) v₁ +
          scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (max t₀ t₁) (v₀ - v₁)) := by
      rw [← hCeq]
      dsimp [Ktri]
      ring

/-- The complete orientation-zero Case-2 occurrence bound.  It retains the
inverse-scale factor supplied by the diagonal derivative estimate. -/
theorem scratch_caseTwo_u0_occurrence (v₀ v₁ lam t₀ t₁ : ℝ)
    (hlam : 0 < lam) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁) :
    (∫ p : ℝ, scaledBracketBump 2 lam p *
      ((t₀⁻¹ + t₁⁻¹) *
        (scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)))) ≤
      9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (t₀⁻¹ + t₁⁻¹) *
        (scaledBracketBump 2 t₀ v₀ * scaledBracketBump 2 (max lam t₁) v₁ +
          scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (max t₀ t₁) v₁ +
          scaledBracketBump 2 lam ((v₀ + v₁) / Real.sqrt 2) *
            scaledBracketBump 2 (max t₀ t₁) ((v₀ - v₁) / Real.sqrt 2)) := by
  let A : ℝ := scaledBracketBump 2 t₀ v₀ * scaledBracketBump 2 (max lam t₁) v₁
  let B : ℝ := scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (max t₀ t₁) v₁
  let C : ℝ := scaledBracketBump 2 lam ((v₀ + v₁) / Real.sqrt 2) *
    scaledBracketBump 2 (max t₀ t₁) ((v₀ - v₁) / Real.sqrt 2)
  let Braw : ℝ := scaledBracketBump 2 lam v₀ *
    scaledBracketBump 2 (max t₀ t₁) (v₀ - v₁)
  let κ : ℝ := t₀⁻¹ + t₁⁻¹
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    exact add_nonneg (inv_nonneg.mpr ht₀.le) (inv_nonneg.mpr ht₁.le)
  have hD : 0 ≤ C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, C_twoBumpEstimate,
      Real.rpow_natCast]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (aux_scaledBracketBump_nonneg 2 ht₀ _)
      (aux_scaledBracketBump_nonneg 2 (lt_max_of_lt_right ht₁) _)
  have hraw := scratch_caseTwo_u0_threeBump_raw v₀ v₁ lam t₀ t₁ hlam ht₀ ht₁
  have hraw' :
      (∫ p : ℝ, scaledBracketBump 2 lam p *
        scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)) ≤
        C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + Braw) := by
    simpa [A, Braw] using hraw
  have hsplit := scratch_caseTwo_orthogonal_split v₀ v₁ lam (max t₀ t₁)
    hlam (lt_max_of_lt_left ht₀)
  have hsplit' : Braw ≤ 9 * (B + C) := by
    simpa [Braw, B, C] using hsplit
  have hsum : A + Braw ≤ 9 * (A + B + C) := by
    calc
      A + Braw = Braw + A := by ring
      _ ≤ 9 * (B + C) + A := by
        simpa [add_comm] using add_le_add_right hsplit' A
      _ = A + 9 * (B + C) := by ring
      _ ≤ 9 * (A + B + C) := by nlinarith [hA]
  have htriple :
      (∫ p : ℝ, scaledBracketBump 2 lam p *
        scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)) ≤
        9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + B + C) := by
    calc
      (∫ p : ℝ, scaledBracketBump 2 lam p *
          scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)) ≤
          C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + Braw) := hraw'
      _ ≤ C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
          (9 * (A + B + C)) :=
        mul_le_mul_of_nonneg_left hsum hD
      _ = 9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + B + C) := by
        ring
  change (∫ p : ℝ, scaledBracketBump 2 lam p *
      (κ * (scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)))) ≤
      9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * κ * (A + B + C)
  calc
    (∫ p : ℝ, scaledBracketBump 2 lam p *
        (κ * (scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)))) =
        κ * (∫ p : ℝ, scaledBracketBump 2 lam p *
          scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      ring
    _ ≤ κ *
        (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + B + C)) :=
      mul_le_mul_of_nonneg_left htriple hκ
    _ = 9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * κ * (A + B + C) := by
      ring

end ScratchCase2Fourier

theorem scratch_nMultiplierRho_negative_decay_bound {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 ≠ 0) (hnegative : ι.1.1 < 0)
    (x : ℝ) :
    |nMultiplierRho γ hkn ι i j x| ≤
      C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
        (scaledBracketBump 3

          ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) x +
        scaledBracketBump 3
          ((2 : ℝ) ^ (ι.1.1 + 1) * γ.scales i 1
            (j - (geometricDelta γ : ℤ) - 1)) x) := by
  let r : ℤ := j - (geometricDelta γ : ℤ) - 1
  let h : ℤ := ι.1.1
  let a : ℤ → ℝ := γ.scales i 1
  let muMinus : ℝ := (2 : ℝ) ^ h * a r
  let muPlus : ℝ := (2 : ℝ) ^ h * a (r + 1)
  let lamMinus : ℝ := (2 : ℝ) ^ h * a r
  let lamPlus : ℝ := (2 : ℝ) ^ (h + 1) * a r
  have hnu : nMultiplierFourScaleExponent γ ∈ Set.Ico (-1 : ℝ) 0 :=
    nMultiplierFourScaleExponent_memIco γ
  have hpow : (2 : ℝ) ^ (h + 1) = (2 : ℝ) ^ h * 2 := by
    rw [zpow_add₀ (by norm_num), zpow_one]
  have hmuMinus : 0 < muMinus := by
    dsimp [muMinus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hmuPlus : 0 < muPlus := by
    dsimp [muPlus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hlamMinus : 0 < lamMinus := by
    dsimp [lamMinus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hlamPlus : 0 < lamPlus := by
    dsimp [lamPlus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hscales : 2 * muMinus ≤ 2 * lamMinus ∧
      2 * lamMinus ≤ lamPlus ∧ lamPlus ≤ muPlus := by
    refine ⟨le_rfl, ?_, ?_⟩
    · dsimp [lamMinus, lamPlus]
      rw [hpow]
      apply le_of_eq
      ring
    · dsimp [lamPlus, muPlus]
      rw [hpow]
      calc
        (2 : ℝ) ^ h * 2 * a r = (2 : ℝ) ^ h * (2 * a r) := by ring
        _ ≤ (2 : ℝ) ^ h * a (r + 1) :=
          mul_le_mul_of_nonneg_left (γ.scales_spaced i 1 r).2 (by positivity)
  have hphiBound : ∀ m : ℕ, m ≤ 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m
        (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ))) xi‖ ≤
        C_standardBumpPropertiesTilde 0 3 := by
    intro m hm xi
    have hraw : ‖iteratedDeriv m
        (fun u : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) ^ 0 *
          FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)) u) xi‖ ≤
        C_standardBumpPropertiesTilde 0 m := by
      by_cases hlow : m ≤ 2
      · exact aux_standardBumpMultiplier_iteratedDeriv_le_low 0 m hlow xi
      · exact aux_standardBumpMultiplier_iteratedDeriv_le_high 0 m (by omega) xi
    simpa only [zero_mul, zero_add, pow_zero, one_mul] using
      hraw.trans (aux_C_standardBumpPropertiesTilde_mono 0 m 3 hm)
  have hcomplex := fourScaleGaussianKernel (C_standardBumpPropertiesTilde 0 3) 3
    (by norm_num) (fun z : ℝ => (standardBump z : ℂ))
    (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
    aux_standardBumpComplex_memW0 rfl (by norm_num [C_standardBumpPropertiesTilde])
    (closure_minimal (standardBumpProperties_fourierShape).2.1 isClosed_Icc)
    (standardBumpProperties_fourierShape).2.2
    (aux_standardBumpComplex_fourier_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))
    hphiBound muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ)
    hmuMinus hmuPlus hlamMinus hlamPlus hscales hnu
  have hreal :
      |(fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x).re| ≤
        C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
          (scaledBracketBump 3 lamMinus x + scaledBracketBump 3 lamPlus x) := by
    calc
      |(fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x).re| ≤
          ‖fourScaleGaussianRho
            (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
            muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x‖ := by
        exact Complex.abs_re_le_norm _
      _ ≤ _ := hcomplex.2 x
  simpa [r, h, a, muMinus, muPlus, lamMinus, lamPlus,
    nMultiplierRho, nMultiplierRhoComplex, hzero,
    not_lt_of_ge hnegative.le] using hreal

theorem scratch_nMultiplierRho_negative_decay_bound_collapsed {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 ≠ 0) (hnegative : ι.1.1 < 0)
    (x : ℝ) :
    |nMultiplierRho γ hkn ι i j x| ≤
      3 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
        scaledBracketBump 3
          ((2 : ℝ) ^ (ι.1.1 + 1) * γ.scales i 1
            (j - (geometricDelta γ : ℤ) - 1)) x := by
  let lamMinus : ℝ := (2 : ℝ) ^ ι.1.1 *
    γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)
  let lamPlus : ℝ := (2 : ℝ) ^ (ι.1.1 + 1) *
    γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)
  have hminus : 0 < lamMinus := by
    dsimp [lamMinus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hplus : 0 < lamPlus := by
    dsimp [lamPlus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hhalf : lamPlus = 2 * lamMinus := by
    dsimp [lamMinus, lamPlus]
    rw [zpow_add₀ (by norm_num), zpow_one]
    ring
  have hsmall : scaledBracketBump 3 lamMinus x ≤ 2 * scaledBracketBump 3 lamPlus x := by
    apply aux_scaledBracketBump_scale_le 3 hminus hplus
    · rw [hhalf]
      linarith
    · norm_num
    · rw [hhalf]
  have hsum : scaledBracketBump 3 lamMinus x + scaledBracketBump 3 lamPlus x ≤
      3 * scaledBracketBump 3 lamPlus x := by
    calc
      scaledBracketBump 3 lamMinus x + scaledBracketBump 3 lamPlus x ≤
          2 * scaledBracketBump 3 lamPlus x + scaledBracketBump 3 lamPlus x :=
        add_le_add hsmall le_rfl
      _ = 3 * scaledBracketBump 3 lamPlus x := by ring
  have hC : 0 ≤ C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 := by
    have hK : 0 ≤ C_fourScaleGaussianKernel 3 := by
      unfold C_fourScaleGaussianKernel
      apply add_nonneg
      · exact mul_nonneg (by unfold C_smoothDecay2; positivity)
          ((aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _))
      · exact mul_nonneg (by positivity)
          ((aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _))
    exact mul_nonneg (by unfold C_standardBumpPropertiesTilde; positivity) hK
  have hraw := scratch_nMultiplierRho_negative_decay_bound γ hkn ι i j hzero hnegative x
  change |nMultiplierRho γ hkn ι i j x| ≤
    3 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
      scaledBracketBump 3 lamPlus x
  calc
    |nMultiplierRho γ hkn ι i j x| ≤
        (C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3) *
          (scaledBracketBump 3 lamMinus x + scaledBracketBump 3 lamPlus x) := by
      simpa [lamMinus, lamPlus, mul_assoc] using hraw
    _ ≤ (C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3) *
        (3 * scaledBracketBump 3 lamPlus x) :=
      mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by ring

theorem scratch_nMultiplierRho_negative_integral_zero {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)

    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 ≠ 0) (hnegative : ι.1.1 < 0) :
    (∫ x : ℝ, nMultiplierRho γ hkn ι i j x) = 0 := by
  let r : ℤ := j - (geometricDelta γ : ℤ) - 1
  let h : ℤ := ι.1.1
  let a : ℤ → ℝ := γ.scales i 1
  let muMinus : ℝ := (2 : ℝ) ^ h * a r

  let muPlus : ℝ := (2 : ℝ) ^ h * a (r + 1)
  let lamMinus : ℝ := (2 : ℝ) ^ h * a r
  let lamPlus : ℝ := (2 : ℝ) ^ (h + 1) * a r
  let phiHat : ℝ → ℂ := FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ))
  let f : ℝ → ℂ := fourScaleGaussianRhoFrequency phiHat
    muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ)
  have hmuMinus : 0 < muMinus := by
    dsimp [muMinus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hmuPlus : 0 < muPlus := by
    dsimp [muPlus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hlamMinus : 0 < lamMinus := by
    dsimp [lamMinus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hlamPlus : 0 < lamPlus := by
    dsimp [lamPlus]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hpow : (2 : ℝ) ^ (h + 1) = (2 : ℝ) ^ h * 2 := by
    rw [zpow_add₀ (by norm_num), zpow_one]
  have hscales : 2 * muMinus ≤ 2 * lamMinus ∧
      2 * lamMinus ≤ lamPlus ∧ lamPlus ≤ muPlus := by
    refine ⟨le_rfl, ?_, ?_⟩
    · dsimp [lamMinus, lamPlus]
      rw [hpow]
      apply le_of_eq
      ring
    · dsimp [lamPlus, muPlus]
      rw [hpow]
      calc
        (2 : ℝ) ^ h * 2 * a r = (2 : ℝ) ^ h * (2 * a r) := by ring
        _ ≤ (2 : ℝ) ^ h * a (r + 1) :=
          mul_le_mul_of_nonneg_left (γ.scales_spaced i 1 r).2 (by positivity)
  have hphiCont : Continuous phiHat := by
    exact aux_gaussianBumpDecomposition_phiHat_continuous
      (fun z : ℝ => (standardBump z : ℂ)) phiHat aux_standardBumpComplex_memW0 rfl
  have hfreqCont : Continuous f := by
    dsimp [f]
    exact aux_gaussianBumpDecomposition_rhoFrequency_continuous phiHat hphiCont
      (standardBumpProperties_fourierShape).2.2 hmuMinus hscales
  have hfreqSupport : HasCompactSupport f := by
    dsimp [f]
    exact aux_gaussianBumpDecomposition_rhoFrequency_compactSupport phiHat
      hlamMinus hlamPlus
      (closure_minimal (standardBumpProperties_fourierShape).2.1 isClosed_Icc)
      muMinus muPlus (nMultiplierFourScaleExponent γ)
  have hfreqInt : Integrable f := hfreqCont.integrable_of_hasCompactSupport hfreqSupport
  have hinvEq : FourierTransformInv.fourierInv f = nMultiplierRhoComplex γ hkn ι i j := by
    funext x
    simp [f, phiHat, r, h, a, muMinus, muPlus, lamMinus, lamPlus,
      nMultiplierRhoComplex, fourScaleGaussianRho, hzero, not_lt_of_ge hnegative.le]
  have hrhoComplexInt : Integrable (nMultiplierRhoComplex γ hkn ι i j) :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (nMultiplierRhoComplex_memW0 γ hkn ι i j)
  have hinvInt : Integrable (FourierTransformInv.fourierInv f) := by
    rw [hinvEq]
    exact hrhoComplexInt
  have hfourierNeg : Integrable (fun x : ℝ => FourierTransform.fourier f (-x)) := by
    have hinvPoint : (fun x : ℝ => FourierTransformInv.fourierInv f x) =
        (fun x : ℝ => FourierTransform.fourier f (-x)) := by
      funext x
      exact Real.fourierInv_eq_fourier_neg f x
    rw [← hinvPoint]
    exact hinvInt
  have hfourierInt : Integrable (FourierTransform.fourier f) := by
    simpa only [neg_neg] using hfourierNeg.comp_neg
  have hinversion : FourierTransform.fourier (FourierTransformInv.fourierInv f) = f :=
    hfreqCont.fourier_fourierInv_eq hfreqInt hfourierInt
  have hfzero : f 0 = 0 := by
    dsimp [f, phiHat]
    simp [fourScaleGaussianRhoFrequency,
      (standardBumpProperties_fourierShape).2.2 0 (by norm_num)]
  have hcomplexZero : (∫ x : ℝ, FourierTransformInv.fourierInv f x) = 0 := by
    have hzeroEval := congrFun hinversion 0
    rw [Real.fourier_real_eq] at hzeroEval
    simpa [hfzero] using hzeroEval
  have hrhoComplexZero : (∫ x : ℝ, nMultiplierRhoComplex γ hkn ι i j x) = 0 := by
    rw [← hinvEq]
    exact hcomplexZero
  have hrealZero : (∫ x : ℝ, (nMultiplierRhoComplex γ hkn ι i j x).re) = 0 := by
    change (∫ x : ℝ, RCLike.re (nMultiplierRhoComplex γ hkn ι i j x)) = 0
    rw [integral_re hrhoComplexInt, hrhoComplexZero]
    rfl
  simpa [nMultiplierRho] using hrealZero

theorem scratch_cumulativeIic_hasDerivAt {rho : ℝ → ℝ}
    (hcont : Continuous rho) (hint : Integrable rho) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ q in Set.Iic y, rho q) (rho x) x := by
  let R : ℝ → ℝ := fun y => ∫ q in Set.Iic y, rho q
  have hR_eq (y : ℝ) : R y = R 0 + ∫ q in 0..y, rho q := by
    have hdiff := intervalIntegral.integral_Iic_sub_Iic (μ := volume)
      (a := 0) (b := y) hint.integrableOn hint.integrableOn
    dsimp [R]
    linarith
  have hinterval : HasDerivAt (fun y : ℝ => ∫ q in 0..y, rho q) (rho x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      (hcont.stronglyMeasurableAtFilter volume (nhds x)) hcont.continuousAt
  have hsum : HasDerivAt (fun y : ℝ => R 0 + ∫ q in 0..y, rho q) (rho x) x := by
    exact hinterval.const_add (R 0)
  have hfun : (fun y : ℝ => ∫ q in Set.Iic y, rho q) =
      (fun y : ℝ => R 0 + ∫ q in 0..y, rho q) := by
    funext y
    exact hR_eq y
  rw [hfun]
  exact hsum

theorem scratch_integrable_multiset_sum {α : Type*} (P : Multiset α)
    (g : α → ℝ → ℝ) (hg : ∀ q ∈ P, Integrable (g q)) :
    Integrable (fun x : ℝ => (P.map fun q => g q x).sum) := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      apply Integrable.add
      · exact hg a (by simp)
      · apply ih
        intro q hq
        exact hg q (by simp [hq])

theorem scratch_integral_multiset_sum {α : Type*} (P : Multiset α)
    (g : α → ℝ → ℝ) (hg : ∀ q ∈ P, Integrable (g q)) :
    (∫ x : ℝ, (P.map fun q => g q x).sum) =
      (P.map fun q => ∫ x : ℝ, g q x).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
      have hgP : ∀ q ∈ P, Integrable (g q) := by
        intro q hq
        exact hg q (by simp [hq])
      have hsumP : Integrable (fun x : ℝ => (P.map fun q => g q x).sum) :=
        scratch_integrable_multiset_sum P g hgP
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [integral_add (hg a (by simp)) hsumP, ih hgP]

theorem scratch_mul_multiset_sum {α : Type*} (a : ℝ) (P : Multiset α)
    (g : α → ℝ) :
    a * (P.map g).sum = (P.map fun q => a * g q).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons q P ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [mul_add, ih]

theorem scratch_finite_multiset_integral_bridge {α : Type*}
    (P : Multiset α) (C : ℝ) (rho H : ℝ → ℝ) (B : α → ℝ → ℝ)
    (hC : 0 ≤ C) (hrho : ∀ p, 0 ≤ rho p) (hH : ∀ p, 0 ≤ H p)
    (hbound : ∀ p, H p ≤ C * (P.map fun q => B q p).sum)
    (hint : ∀ q ∈ P, Integrable (fun p : ℝ => rho p * B q p)) :
    (∫ p : ℝ, rho p * H p) ≤

      C * (P.map fun q => ∫ p : ℝ, rho p * B q p).sum := by
  let S : ℝ → ℝ := fun p => (P.map fun q => rho p * B q p).sum
  have hS : Integrable S := by
    dsimp [S]
    exact scratch_integrable_multiset_sum P (fun q p => rho p * B q p) hint
  have hpoint (p : ℝ) : rho p * H p ≤ C * S p := by
    have h := mul_le_mul_of_nonneg_left (hbound p) (hrho p)
    change rho p * H p ≤ rho p * (C * (P.map fun q => B q p).sum) at h
    calc
      rho p * H p ≤ rho p * (C * (P.map fun q => B q p).sum) := h
      _ = C * (rho p * (P.map fun q => B q p).sum) := by ring
      _ = C * S p := by
        dsimp [S]
        rw [scratch_mul_multiset_sum]
  have hleft (p : ℝ) : 0 ≤ rho p * H p := mul_nonneg (hrho p) (hH p)
  calc
    (∫ p : ℝ, rho p * H p) ≤ ∫ p : ℝ, C * S p :=
      integral_mono_of_nonneg (ae_of_all _ hleft) (hS.const_mul C)
        (ae_of_all _ hpoint)
    _ = C * (∫ p : ℝ, S p) := by rw [integral_const_mul]
    _ = C * (P.map fun q => ∫ p : ℝ, rho p * B q p).sum := by
      rw [scratch_integral_multiset_sum P (fun q p => rho p * B q p) hint]

theorem scratch_caseTwo_outer_from_occurrences {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (R : ℝ → ℝ)
    (hrep : nMultiplier γ hkn ι i j v = ∫ p : ℝ,
      R p * aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p))
    (hint : ∀ q ∈ P, Integrable (fun p : ℝ =>
      |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p)))) :
    |nMultiplier γ hkn ι i j v| ≤
      C_hKernelDerivativeEstimateGaussianDomination *
        (P.map fun q => ∫ p : ℝ,
          |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
            aux_kernelBracketProduct q j (v.1 - p, v.2 - p))).sum := by
  let rho : ℝ → ℝ := fun p => |R p|
  let H : ℝ → ℝ := fun p =>
    |aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p)|
  let B : (SequencePair × Fin 2) → ℝ → ℝ := fun q p =>
    ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p)
  have hHbound (p : ℝ) : H p ≤ C_hKernelDerivativeEstimateGaussianDomination *
      (P.map fun q => B q p).sum := by
    dsimp [H, B]
    exact hP.2.2 (v.1 - p, v.2 - p) j
  have hbridge := scratch_finite_multiset_integral_bridge P
    C_hKernelDerivativeEstimateGaussianDomination rho H B
    aux_C_hKernelDerivativeEstimateGaussianDomination_nonneg (fun p => abs_nonneg _)
    (fun p => abs_nonneg _) hHbound (by
      intro q hq
      simpa [rho, B] using hint q hq)
  calc
    |nMultiplier γ hkn ι i j v| =
        |∫ p : ℝ, R p * aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p)| := by
      rw [hrep]
    _ ≤ ∫ p : ℝ, |R p * aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p)| :=
      abs_integral_le_integral_abs
    _ = ∫ p : ℝ, rho p * H p := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp [rho, H, abs_mul]
    _ ≤ C_hKernelDerivativeEstimateGaussianDomination *
        (P.map fun q => ∫ p : ℝ, rho p * B q p).sum := hbridge
    _ = C_hKernelDerivativeEstimateGaussianDomination *
        (P.map fun q => ∫ p : ℝ,
          |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
            aux_kernelBracketProduct q j (v.1 - p, v.2 - p))).sum := by
      rfl

theorem scratch_multiset_sum_le_scaled {α : Type*} (P : Multiset α)
    (f g : α → ℝ) (D : ℝ) (h : ∀ q ∈ P, f q ≤ D * g q) :
    (P.map f).sum ≤ D * (P.map g).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
      have hP : ∀ q ∈ P, f q ≤ D * g q := by
        intro q hq
        exact h q (by simp [hq])
      simp only [Multiset.map_cons, Multiset.sum_cons]
      calc
        f a + (P.map f).sum ≤ D * g a + D * (P.map g).sum :=
          add_le_add (h a (by simp)) (ih hP)
        _ = D * (g a + (P.map g).sum) := by ring

theorem scratch_scale_mul_scaledBracketBump_le_one (N : ℕ) (s x : ℝ) (hs : 0 < s) :
    s * scaledBracketBump N s x ≤ 1 := by
  unfold scaledBracketBump
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  apply pow_le_one₀
  · exact inv_nonneg.mpr (by positivity)
  · apply inv_le_one_of_one_le₀
    linarith [abs_nonneg (s⁻¹ * x)]

theorem scratch_integrable_mul_of_continuous_bound

    {R K : ℝ → ℝ} {C : ℝ} (hR : Continuous R) (hC : 0 ≤ C)
    (hRbound : ∀ p : ℝ, |R p| ≤ C) (hK : Integrable K) :
    Integrable (fun p : ℝ => R p * K p) := by
  have hmajor : Integrable (fun p : ℝ => C * |K p|) := by
    simpa only [Real.norm_eq_abs] using hK.norm.const_mul C
  refine hmajor.mono' (hR.aestronglyMeasurable.mul hK.aestronglyMeasurable) ?_
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hRbound p) (abs_nonneg _)

theorem scratch_cumulativeIic_hasDerivAt_outer {rho : ℝ → ℝ}
    (hcont : Continuous rho) (hint : Integrable rho) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ q in Set.Iic y, rho q) (rho x) x := by
  let R : ℝ → ℝ := fun y => ∫ q in Set.Iic y, rho q
  have hR_eq (y : ℝ) : R y = R 0 + ∫ q in 0..y, rho q := by
    have hdiff := intervalIntegral.integral_Iic_sub_Iic (μ := volume)
      (a := 0) (b := y) hint.integrableOn hint.integrableOn
    dsimp [R]
    linarith
  have hinterval : HasDerivAt (fun y : ℝ => ∫ q in 0..y, rho q) (rho x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      (hcont.stronglyMeasurableAtFilter volume (nhds x)) hcont.continuousAt
  have hsum : HasDerivAt (fun y : ℝ => R 0 + ∫ q in 0..y, rho q) (rho x) x := by
    exact hinterval.const_add (R 0)
  have hfun : (fun y : ℝ => ∫ q in Set.Iic y, rho q) =
      (fun y : ℝ => R 0 + ∫ q in 0..y, rho q) := by
    funext y
    exact hR_eq y
  rw [hfun]
  exact hsum

theorem scratch_primitive_times_integrable
    {rho K : ℝ → ℝ} {A s : ℝ} (hcont : Continuous rho) (hrho : Integrable rho)
    (hA : 0 ≤ A) (hs : 0 < s)
    (hprimitiveBound : ∀ p : ℝ,
      |∫ q : ℝ in Set.Iic p, rho q| ≤ A * s * scaledBracketBump 2 s p)
    (hK : Integrable K) :
    Integrable (fun p : ℝ => (∫ q : ℝ in Set.Iic p, rho q) * K p) := by
  let R : ℝ → ℝ := fun p => ∫ q : ℝ in Set.Iic p, rho q
  have hRcont : Continuous R := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (scratch_cumulativeIic_hasDerivAt_outer hcont hrho p).continuousAt
  have hRbound (p : ℝ) : |R p| ≤ A := by
    calc
      |R p| ≤ A * s * scaledBracketBump 2 s p := hprimitiveBound p
      _ = A * (s * scaledBracketBump 2 s p) := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left
        (scratch_scale_mul_scaledBracketBump_le_one 2 s p hs) hA
      _ = A := by ring
  simpa [R] using scratch_integrable_mul_of_continuous_bound hRcont hA hRbound hK


theorem scratch_absPrimitive_times_integrable
    {rho K : ℝ → ℝ} {A s : ℝ} (hcont : Continuous rho) (hrho : Integrable rho)
    (hA : 0 ≤ A) (hs : 0 < s)
    (hprimitiveBound : ∀ p : ℝ,
      |∫ q : ℝ in Set.Iic p, rho q| ≤ A * s * scaledBracketBump 2 s p)
    (hK : Integrable K) :
    Integrable (fun p : ℝ => |∫ q : ℝ in Set.Iic p, rho q| * K p) := by
  let R : ℝ → ℝ := fun p => ∫ q : ℝ in Set.Iic p, rho q
  have hRcont : Continuous R := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (scratch_cumulativeIic_hasDerivAt_outer hcont hrho p).continuousAt
  have hRbound (p : ℝ) : |R p| ≤ A := by
    calc
      |R p| ≤ A * s * scaledBracketBump 2 s p := hprimitiveBound p
      _ = A * (s * scaledBracketBump 2 s p) := by ring
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left
        (scratch_scale_mul_scaledBracketBump_le_one 2 s p hs) hA
      _ = A := by ring
  simpa [R] using scratch_integrable_mul_of_continuous_bound hRcont.abs hA
    (fun p => by simpa using hRbound p) hK

theorem scratch_integrable_mul_fderiv_from_package
    {R g : ℝ → ℝ} {α : Type*} (Rcont : Continuous R)
    (P : Multiset α) (C : ℝ) (B : α → ℝ → ℝ)
    (hbound : ∀ p : ℝ,
      |fderiv ℝ g p 1| ≤ C * (P.map fun q => B q p).sum)
    (hint : ∀ q ∈ P, Integrable (fun p : ℝ => |R p| * B q p)) :
    Integrable (fun p : ℝ => R p * fderiv ℝ g p 1) := by
  let S : ℝ → ℝ := fun p => (P.map fun q => |R p| * B q p).sum
  have hS : Integrable S := by
    dsimp [S]
    exact scratch_integrable_multiset_sum P (fun q p => |R p| * B q p) hint
  have hpoint (p : ℝ) : ‖R p * fderiv ℝ g p 1‖ ≤ C * S p := by
    rw [norm_mul, Real.norm_eq_abs]
    have h := mul_le_mul_of_nonneg_left (hbound p) (abs_nonneg (R p))
    change |R p| * |fderiv ℝ g p 1| ≤
      |R p| * (C * (P.map fun q => B q p).sum) at h
    calc
      |R p| * |fderiv ℝ g p 1| ≤
          |R p| * (C * (P.map fun q => B q p).sum) := h
      _ = C * (|R p| * (P.map fun q => B q p).sum) := by ring
      _ = C * S p := by
        dsimp [S]
        rw [scratch_mul_multiset_sum]
  refine (hS.const_mul C).mono'
    (Rcont.aestronglyMeasurable.mul
      (measurable_fderiv_apply_const ℝ g 1).aestronglyMeasurable) ?_
  filter_upwards [] with p
  exact hpoint p

/-- Combines a pair of orientation-specific Case-2 occurrence estimates without losing
multiset multiplicities. -/
theorem scratch_caseTwo_occurrence_by_orientation
    {n : ℕ} (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) (v : RealPlane)
    (P : Multiset (SequencePair × Fin 2)) (q : SequencePair × Fin 2)
    (hq : q ∈ P) (R : ℝ → ℝ) (D : ℝ)
    (S : SequencePair × Fin 2 → ℝ)
    (hzero : q.2 = 0 →
      (∫ p : ℝ, |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) ≤ D * S q)
    (hone : q.2 = 1 →
      (∫ p : ℝ, |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) ≤ D * S q) :
    (∫ p : ℝ, |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) ≤ D * S q := by
  have hcases : q.2.val = 0 ∨ q.2.val = 1 := by omega
  rcases hcases with hq0 | hq1
  · apply hzero
    apply Fin.ext
    simpa using hq0
  · apply hone
    apply Fin.ext
    simpa using hq1

/-- The source-ready finite package assembly after the Case-2 integration-by-parts
representation has been established. -/
theorem scratch_caseTwo_outer_scaled_from_occurrences {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (R : ℝ → ℝ) (D : ℝ) (S : (SequencePair × Fin 2) → ℝ)
    (hrep : nMultiplier γ hkn ι i j v = ∫ p : ℝ,
      R p * aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p))
    (hint : ∀ q ∈ P, Integrable (fun p : ℝ =>
      |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *

        aux_kernelBracketProduct q j (v.1 - p, v.2 - p))))
    (hD : 0 ≤ D)
    (hocc : ∀ q ∈ P,
      (∫ p : ℝ, |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) ≤ D * S q) :
    |nMultiplier γ hkn ι i j v| ≤
      C_hKernelDerivativeEstimateGaussianDomination * D * (P.map S).sum := by
  have houter := scratch_caseTwo_outer_from_occurrences γ hkn ι i j v P hP R hrep hint
  have hsum := scratch_multiset_sum_le_scaled P
    (fun q => ∫ p : ℝ, |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) S D hocc
  calc
    |nMultiplier γ hkn ι i j v| ≤
        C_hKernelDerivativeEstimateGaussianDomination *
          (P.map fun q => ∫ p : ℝ,
            |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
              aux_kernelBracketProduct q j (v.1 - p, v.2 - p))).sum := houter
    _ ≤ C_hKernelDerivativeEstimateGaussianDomination * (D * (P.map S).sum) :=
      mul_le_mul_of_nonneg_left hsum aux_C_hKernelDerivativeEstimateGaussianDomination_nonneg
    _ = C_hKernelDerivativeEstimateGaussianDomination * D * (P.map S).sum := by ring

/-- Algebraic conversion of the decaying-primitive integration-by-parts identity into the
diagonal-derivative representation used by the derivative H package. -/
theorem scratch_caseTwo_representation_from_parts {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane) (rho : ℝ → ℝ)
    (Ptail : ℝ → ℝ)
    (hparts :
      (∫ p : ℝ, rho p * hMultiplier γ i j (v.1 - p, v.2 - p)) =
        -∫ p : ℝ, Ptail p *
          fderiv ℝ (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) p 1)
    (hfderiv : ∀ p : ℝ,
      fderiv ℝ (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) p 1 =
        -aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p))
    (hrho : rho = nMultiplierRho γ hkn ι i j) :
    nMultiplier γ hkn ι i j v = ∫ p : ℝ,
      Ptail p * aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p) := by
  unfold nMultiplier
  rw [← hrho]
  calc
    (∫ q : ℝ, hMultiplier γ i j (v.1 - q, v.2 - q) * rho q) =
        ∫ q : ℝ, rho q * hMultiplier γ i j (v.1 - q, v.2 - q) := by
      apply integral_congr_ae
      filter_upwards [] with q
      ring
    _ = -∫ p : ℝ, Ptail p *
        fderiv ℝ (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) p 1 := hparts
    _ = ∫ p : ℝ,
        Ptail p * aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p) := by
      rw [show (fun p : ℝ => Ptail p *
          fderiv ℝ (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) p 1) =
          (fun p : ℝ => -(Ptail p *
            aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p))) by
          funext p
          rw [hfderiv p]
          ring]
      rw [integral_neg]
      ring

/-- A cubic bracket tail makes the original rho-times-H term integrable whenever the
translated H slice is integrable. -/

theorem scratch_caseTwo_decay_mul_integrable
    {rho g : ℝ → ℝ} {A s : ℝ}
    (hrhoCont : Continuous rho) (hA : 0 ≤ A) (hs : 0 < s)
    (hdecay : ∀ p : ℝ, |rho p| ≤ A * scaledBracketBump 3 s p)
    (hg : Integrable g) :
    Integrable (fun p : ℝ => rho p * g p) := by
  have hB (p : ℝ) : scaledBracketBump 3 s p ≤ s⁻¹ := by
    calc
      scaledBracketBump 3 s p = s⁻¹ * (s * scaledBracketBump 3 s p) := by
        field_simp [hs.ne']
      _ ≤ s⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left
          (scratch_scale_mul_scaledBracketBump_le_one 3 s p hs) (inv_nonneg.mpr hs.le)
      _ = s⁻¹ := by ring
  have hbound (p : ℝ) : |rho p| ≤ A * s⁻¹ :=
    (hdecay p).trans (mul_le_mul_of_nonneg_left (hB p) hA)
  exact scratch_integrable_mul_of_continuous_bound hrhoCont
    (mul_nonneg hA (inv_nonneg.mpr hs.le)) hbound hg

/-- The derivative H package supplies the final integrability input of Iic integration
by parts, once every primitive-weighted occurrence has been shown integrable. -/
theorem scratch_caseTwo_primitive_fderiv_integrable {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (v : RealPlane)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (R : ℝ → ℝ) (hRcont : Continuous R)
    (hfderiv : ∀ p : ℝ,
      fderiv ℝ (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) p 1 =
        -aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p))
    (hint : ∀ q ∈ P, Integrable (fun p : ℝ =>
      |R p| * (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p)))) :
    Integrable (fun p : ℝ => R p *
      fderiv ℝ (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) p 1) := by
  let B : (SequencePair × Fin 2) → ℝ → ℝ := fun q p =>
    ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p)
  have hbound (p : ℝ) :
      |fderiv ℝ (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) p 1| ≤
        C_hKernelDerivativeEstimateGaussianDomination * (P.map fun q => B q p).sum := by
    rw [hfderiv p, abs_neg]
    simpa [B] using hP.2.2 (v.1 - p, v.2 - p) j
  apply scratch_integrable_mul_fderiv_from_package hRcont P
    C_hKernelDerivativeEstimateGaussianDomination B hbound
  intro q hq
  simpa [B] using hint q hq

/-- Translation converts the centered two-coordinate bracket slice used by the existing
Case-1 integrability lemma into the arbitrary `v-p` slice needed in Case 2. -/
theorem scratch_caseTwo_translate_integrable
    (B : RealPlane → ℝ) (v : RealPlane)
    (hcentered : Integrable (fun p : ℝ =>
      B (-(v.2 - v.1) / 2 - p, (v.2 - v.1) / 2 - p))) :
    Integrable (fun p : ℝ => B (v.1 - p, v.2 - p)) := by
  let w₀ : ℝ := (v.1 + v.2) / 2
  let w₁ : ℝ := (v.2 - v.1) / 2
  have htranslate := hcentered.comp_sub_right w₀
  have heq : (fun p : ℝ =>
      B (-(v.2 - v.1) / 2 - (p - w₀), (v.2 - v.1) / 2 - (p - w₀))) =
      (fun p : ℝ => B (v.1 - p, v.2 - p)) := by
    funext p
    dsimp [w₀]
    congr 1 <;> ring
  rw [heq] at htranslate
  exact htranslate

theorem scratch_caseTwo_u0_primitive_scalar
    (v₀ v₁ lam t₀ t₁ A r : ℝ) (R : ℝ → ℝ)
    (hlam : 0 < lam) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁)
    (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hratio : lam * (t₀⁻¹ + t₁⁻¹) ≤ r)
    (hR : ∀ p : ℝ, |R p| ≤ A * lam * scaledBracketBump 2 lam p)
    (hint : Integrable (fun p : ℝ =>
      scaledBracketBump 2 lam p *
        ((t₀⁻¹ + t₁⁻¹) *
          (scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)))) )
    (hscalar :
      (∫ p : ℝ, scaledBracketBump 2 lam p *
        ((t₀⁻¹ + t₁⁻¹) *
          (scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)))) ≤
        9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
          (t₀⁻¹ + t₁⁻¹) *
          (scaledBracketBump 2 t₀ v₀ * scaledBracketBump 2 (max lam t₁) v₁ +
            scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (max t₀ t₁) v₁ +
            scaledBracketBump 2 lam ((v₀ + v₁) / Real.sqrt 2) *
              scaledBracketBump 2 (max t₀ t₁) ((v₀ - v₁) / Real.sqrt 2))) :
    (∫ p : ℝ, |R p| *
      ((t₀⁻¹ + t₁⁻¹) *
        (scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)))) ≤
      9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
        (scaledBracketBump 2 t₀ v₀ * scaledBracketBump 2 (max lam t₁) v₁ +
          scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (max t₀ t₁) v₁ +
          scaledBracketBump 2 lam ((v₀ + v₁) / Real.sqrt 2) *
            scaledBracketBump 2 (max t₀ t₁) ((v₀ - v₁) / Real.sqrt 2)) := by
  let κ : ℝ := t₀⁻¹ + t₁⁻¹
  let K : ℝ → ℝ := fun p =>
    scaledBracketBump 2 t₀ (v₀ - p) * scaledBracketBump 2 t₁ (v₁ - p)
  let S : ℝ :=
    scaledBracketBump 2 t₀ v₀ * scaledBracketBump 2 (max lam t₁) v₁ +
      scaledBracketBump 2 lam v₀ * scaledBracketBump 2 (max t₀ t₁) v₁ +
      scaledBracketBump 2 lam ((v₀ + v₁) / Real.sqrt 2) *
        scaledBracketBump 2 (max t₀ t₁) ((v₀ - v₁) / Real.sqrt 2)
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    exact add_nonneg (inv_nonneg.mpr ht₀.le) (inv_nonneg.mpr ht₁.le)
  have hK (p : ℝ) : 0 ≤ K p := by
    dsimp [K]
    exact mul_nonneg (aux_scaledBracketBump_nonneg 2 ht₀ _)
      (aux_scaledBracketBump_nonneg 2 ht₁ _)
  have hleftNonneg (p : ℝ) : 0 ≤ |R p| * (κ * K p) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg hκ (hK p))
  have hright : Integrable (fun p : ℝ => A * lam *
      (scaledBracketBump 2 lam p * (κ * K p))) := by
    convert hint.const_mul (A * lam) using 1
  have hpoint (p : ℝ) : |R p| * (κ * K p) ≤ A * lam *
      (scaledBracketBump 2 lam p * (κ * K p)) := by
    calc
      |R p| * (κ * K p) ≤ (A * lam * scaledBracketBump 2 lam p) * (κ * K p) :=
        mul_le_mul_of_nonneg_right (hR p) (mul_nonneg hκ (hK p))
      _ = A * lam * (scaledBracketBump 2 lam p * (κ * K p)) := by ring
  have hmajor :
      (∫ p : ℝ, |R p| * (κ * K p)) ≤
        A * lam * (∫ p : ℝ, scaledBracketBump 2 lam p * (κ * K p)) := by
    calc
      (∫ p : ℝ, |R p| * (κ * K p)) ≤
          ∫ p : ℝ, A * lam * (scaledBracketBump 2 lam p * (κ * K p)) :=
        integral_mono_of_nonneg (ae_of_all _ hleftNonneg) hright (ae_of_all _ hpoint)
      _ = A * lam * (∫ p : ℝ, scaledBracketBump 2 lam p * (κ * K p)) := by
        rw [integral_const_mul]
  have hscalar' : (∫ p : ℝ, scaledBracketBump 2 lam p * (κ * K p)) ≤
      9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * κ * S := by
    simpa [κ, K, S] using hscalar
  have hS : 0 ≤ S := by
    dsimp [S]
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (aux_scaledBracketBump_nonneg 2 ht₀ _)
          (aux_scaledBracketBump_nonneg 2 (lt_max_of_lt_right ht₁) _)
      · exact mul_nonneg (aux_scaledBracketBump_nonneg 2 hlam _)
          (aux_scaledBracketBump_nonneg 2 (lt_max_of_lt_left ht₀) _)
    · exact mul_nonneg (aux_scaledBracketBump_nonneg 2 hlam _)
        (aux_scaledBracketBump_nonneg 2 (lt_max_of_lt_left ht₀) _)
  have hC : 0 ≤ C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, C_twoBumpEstimate,
      Real.rpow_natCast]
  have hAlam : 0 ≤ A * lam := mul_nonneg hA hlam.le

  have hscale : A * lam *
      (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * κ * S) ≤
      9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * S := by
    have h9A : 0 ≤ (9 : ℝ) * A := mul_nonneg (by norm_num) hA

    have hCS : 0 ≤ C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * S :=
      mul_nonneg hC hS
    calc
      A * lam * (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * κ * S) =
          9 * A * (lam * κ) * (C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * S) := by ring
      _ ≤ 9 * A * r * (C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * S) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio h9A) hCS
      _ = 9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * S := by ring
  change (∫ p : ℝ, |R p| * (κ * K p)) ≤
    9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * S
  calc
    (∫ p : ℝ, |R p| * (κ * K p)) ≤
        A * lam * (∫ p : ℝ, scaledBracketBump 2 lam p * (κ * K p)) := hmajor
    _ ≤ A * lam * (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * κ * S) :=
      mul_le_mul_of_nonneg_left hscalar' hAlam
    _ ≤ 9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * S := hscale

/-- Orientation-zero kernel-product form of the preceding primitive lifting. -/
theorem scratch_caseTwo_u0_primitive_kernelBracket
    (q : SequencePair × Fin 2) (j : ℤ) (v : RealPlane)
    (lam A r : ℝ) (R : ℝ → ℝ)
    (hqu : q.2 = 0) (hq₀ : SpacedSequence (q.1 0))
    (hq₁ : SpacedSequence (q.1 1))
    (hlam : 0 < lam) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hratio : lam * ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) ≤ r)
    (hR : ∀ p : ℝ, |R p| ≤ A * lam * scaledBracketBump 2 lam p)
    (hint : Integrable (fun p : ℝ =>
      scaledBracketBump 2 lam p *
        (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p))))
    (hscalar :
      (∫ p : ℝ, scaledBracketBump 2 lam p *
        (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
          (scaledBracketBump 2 (q.1 0 j) (v.1 - p) *
            scaledBracketBump 2 (q.1 1 j) (v.2 - p)))) ≤
        9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
          ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
          (scaledBracketBump 2 (q.1 0 j) v.1 *
              scaledBracketBump 2 (max lam (q.1 1 j)) v.2 +
            scaledBracketBump 2 lam v.1 *
              scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 +
            scaledBracketBump 2 lam ((v.1 + v.2) / Real.sqrt 2) *
              scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
                ((v.1 - v.2) / Real.sqrt 2))) :
    (∫ p : ℝ, |R p| *
      (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) ≤
      9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
        (scaledBracketBump 2 (q.1 0 j) v.1 *
            scaledBracketBump 2 (max lam (q.1 1 j)) v.2 +
          scaledBracketBump 2 lam v.1 *
            scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 +
          scaledBracketBump 2 lam ((v.1 + v.2) / Real.sqrt 2) *
            scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
              ((v.1 - v.2) / Real.sqrt 2)) := by
  have ht₀ : 0 < q.1 0 j := (hq₀ j).1
  have ht₁ : 0 < q.1 1 j := (hq₁ j).1
  have hint' : Integrable (fun p : ℝ =>
      scaledBracketBump 2 lam p *
        (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
          (scaledBracketBump 2 (q.1 0 j) (v.1 - p) *
            scaledBracketBump 2 (q.1 1 j) (v.2 - p)))) := by
    simpa [aux_kernelBracketProduct, hqu, W] using hint
  have hmain := scratch_caseTwo_u0_primitive_scalar v.1 v.2 lam (q.1 0 j) (q.1 1 j)
    A r R hlam ht₀ ht₁ hA hr hratio hR hint' hscalar
  simpa [aux_kernelBracketProduct, hqu, W] using hmain


private theorem scratch_scaledBracketBump_simul_rescale (N : ℕ) (c s x : ℝ) (hc : 0 < c) :
    c * scaledBracketBump N (c * s) (c * x) = scaledBracketBump N s x := by
  unfold scaledBracketBump
  have hcne : c ≠ 0 := ne_of_gt hc
  have harg : (c * s)⁻¹ * (c * x) = s⁻¹ * x := by
    field_simp [hcne]
  have hinv : c * (c * s)⁻¹ = s⁻¹ := by
    field_simp [hcne]
  rw [harg]
  calc
    c * ((c * s)⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N) =
        (c * (c * s)⁻¹) * (1 + |s⁻¹ * x|)⁻¹ ^ N := by ring
    _ = s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N := by rw [hinv]

private theorem scratch_integral_scale_pos (c : ℝ) (hc : 0 < c) (g : ℝ → ℝ) :
    (∫ p : ℝ, c * g (c * p)) = ∫ x : ℝ, g x := by
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  simp only [smul_eq_mul, abs_inv, abs_of_pos (inv_pos.mpr hc)]
  field_simp [hc.ne']

theorem scratch_caseTwo_u1_occurrence
    (w0 w1 lam t0 t1 : ℝ) (hlam : 0 < lam) (ht0 : 0 < t0) (ht1 : 0 < t1)
    (hlam_t0 : Real.sqrt 2 * lam ≤ t0) :
    (∫ p : ℝ, scaledBracketBump 2 lam p *
        scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) *
        scaledBracketBump 2 t1 (Real.sqrt 2 * w1)) ≤
      4 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 t0 (Real.sqrt 2 * w0) *
        scaledBracketBump 2 t1 (Real.sqrt 2 * w1) := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  let c : ℝ := Real.sqrt 2
  let g : ℝ → ℝ := fun x =>
    scaledBracketBump 2 (c * lam) x * scaledBracketBump 2 t0 (c * w0 - x)
  have hscale (p : ℝ) :
      scaledBracketBump 2 lam p * scaledBracketBump 2 t0 (c * (w0 - p)) =
        c * g (c * p) := by
    rw [show c * (w0 - p) = c * w0 - c * p by ring]
    have hres := scratch_scaledBracketBump_simul_rescale 2 c lam p hsqrt
    dsimp [g]
    calc
      scaledBracketBump 2 lam p * scaledBracketBump 2 t0 (c * w0 - c * p) =
          (c * scaledBracketBump 2 (c * lam) (c * p)) *
            scaledBracketBump 2 t0 (c * w0 - c * p) := by rw [hres]
      _ = c * g (c * p) := by ring
  have hint : Integrable g := by
    have hbase : Integrable (fun x : ℝ =>
        scaledBracketBump 2 (c * lam) x * scaledBracketBump 2 t0 (c * w0 - x)) := by
      -- a bounded product of two L1 bracket profiles
      have hleft : Integrable (fun x : ℝ => scaledBracketBump 2 (c * lam) x) := by
        convert aux_integrable_scaledBracketBumpReal 2 (c * lam) (by norm_num)
          (mul_pos hsqrt hlam) using 1
        funext x
        rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
      have hright : Integrable (fun x : ℝ => scaledBracketBump 2 t0 (c * w0 - x)) := by
        convert aux_integrable_scaledBracketBumpReal_translate 2 t0 (c * w0)
          (by norm_num) ht0 using 1
        funext x
        rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
      have hrightNonneg (x : ℝ) : 0 ≤ scaledBracketBump 2 t0 (c * w0 - x) :=
        aux_scaledBracketBump_nonneg 2 ht0 _
      have hrightBound (x : ℝ) : scaledBracketBump 2 t0 (c * w0 - x) ≤ t0⁻¹ := by
        exact aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv ht0
      refine hleft.mul_bdd (c := t0⁻¹) hright.aestronglyMeasurable ?_
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hrightNonneg x)]
      exact hrightBound x
    simpa [g] using hbase
  have htwo := twoBumpEstimate (c * w0) 0 t0 (c * lam) 2 2
    ht0 (mul_pos hsqrt hlam) hlam_t0 (by norm_num) (by norm_num)
  have htwo' :
      (∫ x : ℝ, g x) ≤
        C_twoBumpEstimate 2 2 * scaledBracketBump 2 t0 (c * w0) := by
    have hnon (x : ℝ) : 0 ≤ g x := by
      dsimp [g]
      exact mul_nonneg (aux_scaledBracketBump_nonneg 2 (mul_pos hsqrt hlam) _)
        (aux_scaledBracketBump_nonneg 2 ht0 _)
    calc
      (∫ x : ℝ, g x) = |∫ x : ℝ, g x| := (abs_of_nonneg (integral_nonneg hnon)).symm
      _ = |∫ x : ℝ,
          scaledBracketBump 2 t0 (c * w0 - x) * scaledBracketBump 2 (c * lam) (0 - x)| := by
        apply congrArg abs

        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [g]
        rw [show 0 - x = -x by ring]
        rw [show scaledBracketBump 2 (c * lam) (-x) =
            scaledBracketBump 2 (c * lam) x by
          unfold scaledBracketBump
          rw [mul_neg, abs_neg]]
        ring
      _ ≤ C_twoBumpEstimate 2 2 * scaledBracketBumpReal (min 2 2) t0 (c * w0 - 0) := by
        simpa only [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq] using htwo
      _ = C_twoBumpEstimate 2 2 * scaledBracketBump 2 t0 (c * w0) := by
        norm_num [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
  let b : ℝ := scaledBracketBump 2 t1 (c * w1)
  have hb : 0 ≤ b := aux_scaledBracketBump_nonneg 2 ht1 _
  calc
    (∫ p : ℝ, scaledBracketBump 2 lam p *
        scaledBracketBump 2 t0 (c * (w0 - p)) *
        scaledBracketBump 2 t1 (c * w1)) =

        (∫ p : ℝ, c * g (c * p)) * b := by
      rw [integral_mul_const]
      apply congrArg (fun z : ℝ => z * b)
      apply integral_congr_ae
      filter_upwards [] with p
      rw [← hscale]
    _ = (∫ x : ℝ, g x) * b := by rw [scratch_integral_scale_pos c hsqrt g]
    _ ≤ (C_twoBumpEstimate 2 2 * scaledBracketBump 2 t0 (c * w0)) * b :=
      mul_le_mul_of_nonneg_right htwo' hb
    _ ≤ 4 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 t0 (c * w0) * b := by
      have hfour : 1 ≤ (4 : ℝ) := by norm_num
      have htwoNonneg : 0 ≤ C_twoBumpEstimate 2 2 := by
        norm_num [C_twoBumpEstimate]
      have hnon : 0 ≤ C_twoBumpEstimate 2 2 * scaledBracketBump 2 t0 (c * w0) * b := by
        exact mul_nonneg (mul_nonneg htwoNonneg
          (aux_scaledBracketBump_nonneg 2 ht0 _)) hb
      nlinarith
    _ = 4 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 t0 (Real.sqrt 2 * w0) *
        scaledBracketBump 2 t1 (Real.sqrt 2 * w1) := by rfl

theorem scratch_caseTwo_u1_kernelBracket
    (q : SequencePair × Fin 2) (j : ℤ) (w0 w1 lam : ℝ)
    (hqu : q.2 = 1) (ht0 : 0 < q.1 0 j) (ht1 : 0 < q.1 1 j)
    (hlam : 0 < lam) (hscale : Real.sqrt 2 * lam ≤ q.1 0 j) :
    (∫ p : ℝ, scaledBracketBump 2 lam p *
      aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) ≤
      4 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 (q.1 0 j)
          (W q.2 (w0 - w1, w0 + w1)).1 *
        scaledBracketBump 2 (q.1 1 j)
          (W q.2 (w0 - w1, w0 + w1)).2 := by
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hWfirst (p : ℝ) :
      (W q.2 (w0 - w1 - p, w0 + w1 - p)).1 =
        Real.sqrt 2 * (w0 - p) := by
    rw [hqu]
    simp only [W, Fin.isValue, if_false]
    apply (div_eq_iff (ne_of_gt hsqrt)).2
    have hsquare : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
    calc
      (w0 - w1 - p) + (w0 + w1 - p) = 2 * (w0 - p) := by ring
      _ = (Real.sqrt 2 * (w0 - p)) * Real.sqrt 2 := by
        symm
        calc
          (Real.sqrt 2 * (w0 - p)) * Real.sqrt 2 =
              (Real.sqrt 2) ^ 2 * (w0 - p) := by ring
          _ = 2 * (w0 - p) := by rw [hsquare]
  have hWsecond (p : ℝ) :
      (W q.2 (w0 - w1 - p, w0 + w1 - p)).2 = Real.sqrt 2 * w1 := by
    rw [hqu]
    simp only [W, Fin.isValue, if_false]
    apply (div_eq_iff (ne_of_gt hsqrt)).2
    have hsquare : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
    calc
      -(w0 - w1 - p) + (w0 + w1 - p) = 2 * w1 := by ring
      _ = (Real.sqrt 2 * w1) * Real.sqrt 2 := by
        symm
        calc
          (Real.sqrt 2 * w1) * Real.sqrt 2 = (Real.sqrt 2) ^ 2 * w1 := by ring
          _ = 2 * w1 := by rw [hsquare]
  have hWbase0 : (W q.2 (w0 - w1, w0 + w1)).1 = Real.sqrt 2 * w0 := by
    simpa using hWfirst 0
  have hWbase1 : (W q.2 (w0 - w1, w0 + w1)).2 = Real.sqrt 2 * w1 := by
    simpa using hWsecond 0
  calc
    (∫ p : ℝ, scaledBracketBump 2 lam p *
      aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) =
        ∫ p : ℝ, scaledBracketBump 2 lam p *
          scaledBracketBump 2 (q.1 0 j) (Real.sqrt 2 * (w0 - p)) *
          scaledBracketBump 2 (q.1 1 j) (Real.sqrt 2 * w1) := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp [aux_kernelBracketProduct, hWfirst p, hWsecond p]
      ring
    _ ≤ 4 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 (q.1 0 j) (Real.sqrt 2 * w0) *
        scaledBracketBump 2 (q.1 1 j) (Real.sqrt 2 * w1) :=
      scratch_caseTwo_u1_occurrence w0 w1 lam (q.1 0 j) (q.1 1 j)
        hlam ht0 ht1 hscale
    _ = 4 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 (q.1 0 j)
          (W q.2 (w0 - w1, w0 + w1)).1 *
        scaledBracketBump 2 (q.1 1 j)
          (W q.2 (w0 - w1, w0 + w1)).2 := by
      rw [hWbase0, hWbase1]

theorem scratch_negative_distanceBall_sqrt_scale_le
    {a b : ℤ → ℝ} (ha : SpacedSequence a) {d : ℕ}
    (hb : b ∈ sequenceDistanceBall a (d : WithTop ℕ))
    (h : ℤ) (hh : h < 0) (j : ℤ) :
    Real.sqrt 2 * ((2 : ℝ) ^ (h + 1) * a (j - (d : ℤ) - 1)) ≤ b j := by
  rcases hb with ⟨_, hdist⟩
  have hwithin : WithinSequenceDistance a b d :=
    aux_withinSequenceDistance_of_sequenceDistance_le ha hdist
  have hlow : a (j - (d : ℤ)) ≤ b j := by
    simpa using (hwithin j).1
  have hsp := (ha (j - (d : ℤ) - 1)).2
  have hsp' : 2 * a (j - (d : ℤ) - 1) ≤ a (j - (d : ℤ)) := by

    convert hsp using 1 <;> ring
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hpowpos : 0 < (2 : ℝ) ^ (h + 1) := zpow_pos (by norm_num) _
  have hpowle : (2 : ℝ) ^ (h + 1) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hcoeff : Real.sqrt 2 * (2 : ℝ) ^ (h + 1) ≤ 2 := by
    calc
      Real.sqrt 2 * (2 : ℝ) ^ (h + 1) ≤ 2 * (2 : ℝ) ^ (h + 1) :=
        mul_le_mul_of_nonneg_right hsqrt hpowpos.le
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hpowle (by norm_num)
      _ = 2 := by ring
  calc
    Real.sqrt 2 * ((2 : ℝ) ^ (h + 1) * a (j - (d : ℤ) - 1)) =
        (Real.sqrt 2 * (2 : ℝ) ^ (h + 1)) * a (j - (d : ℤ) - 1) := by ring
    _ ≤ 2 * a (j - (d : ℤ) - 1) :=
      mul_le_mul_of_nonneg_right hcoeff (ha _).1.le
    _ ≤ a (j - (d : ℤ)) := hsp'
    _ ≤ b j := hlow

theorem scratch_negative_distanceBall_scale_ratio_le
    {a b : ℤ → ℝ} (ha : SpacedSequence a) {d : ℕ}
    (hb : b ∈ sequenceDistanceBall a (d : WithTop ℕ))
    (h : ℤ) (hh : h < 0) (j : ℤ) :
    ((2 : ℝ) ^ (h + 1) * a (j - (d : ℤ) - 1)) / b j ≤ (2 : ℝ) ^ h := by
  rcases hb with ⟨hbspaced, hdist⟩
  have hwithin : WithinSequenceDistance a b d :=
    aux_withinSequenceDistance_of_sequenceDistance_le ha hdist
  have hlow : a (j - (d : ℤ)) ≤ b j := by

    simpa using (hwithin j).1
  have hsp := (ha (j - (d : ℤ) - 1)).2
  have hsp' : 2 * a (j - (d : ℤ) - 1) ≤ a (j - (d : ℤ)) := by
    convert hsp using 1 <;> ring
  have hbpos : 0 < b j := (hbspaced j).1
  apply (div_le_iff₀ hbpos).2
  calc
    (2 : ℝ) ^ (h + 1) * a (j - (d : ℤ) - 1) =
        (2 : ℝ) ^ h * (2 * a (j - (d : ℤ) - 1)) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring
    _ ≤ (2 : ℝ) ^ h * b j :=
      mul_le_mul_of_nonneg_left (hsp'.trans hlow) (zpow_pos (by norm_num) _).le

theorem scratch_negative_scale_ratio_sum_le
    (lambda t0 t1 : ℝ) (h : ℤ) (hlambda : 0 ≤ lambda)
    (ht0 : 0 < t0) (ht1 : 0 < t1)
    (h0 : lambda / t0 ≤ (2 : ℝ) ^ h)
    (h1 : lambda / t1 ≤ (2 : ℝ) ^ h) :
    lambda * (t0⁻¹ + t1⁻¹) ≤ (2 : ℝ) ^ (h + 1) := by
  have h0' : lambda * t0⁻¹ ≤ (2 : ℝ) ^ h := by
    rw [div_eq_mul_inv] at h0
    exact h0
  have h1' : lambda * t1⁻¹ ≤ (2 : ℝ) ^ h := by
    rw [div_eq_mul_inv] at h1
    exact h1
  calc
    lambda * (t0⁻¹ + t1⁻¹) = lambda * t0⁻¹ + lambda * t1⁻¹ := by ring
    _ ≤ (2 : ℝ) ^ h + (2 : ℝ) ^ h := add_le_add h0' h1'
    _ = (2 : ℝ) ^ (h + 1) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring

theorem scratch_caseTwo_u1_kernelBracket_of_package {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (ι : MultiplierIndex γ)
    (j : ℤ) (hnegative : ι.1.1 < 0)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (hqu : q.2 = 1)
    (w0 w1 lambda : ℝ)
    (hlambda : lambda = (2 : ℝ) ^ (ι.1.1 + 1) *
      γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) :
    (∫ p : ℝ, scaledBracketBump 2 lambda p *
      aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) ≤
      4 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 (q.1 0 j)
          (W q.2 (w0 - w1, w0 + w1)).1 *
        scaledBracketBump 2 (q.1 1 j)
          (W q.2 (w0 - w1, w0 + w1)).2 := by
  rcases hP.1 q hqmem with ⟨hq0, hq1⟩
  have hq0pos : 0 < q.1 0 j := (hq0.1 j).1
  have hq1pos : 0 < q.1 1 j := (hq1.1 j).1
  have hlambda_pos : 0 < lambda := by
    rw [hlambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hscale : Real.sqrt 2 * lambda ≤ q.1 0 j := by
    rw [hlambda]
    exact scratch_negative_distanceBall_sqrt_scale_le (γ.scales_spaced i 1) hq0
      ι.1.1 hnegative j
  exact scratch_caseTwo_u1_kernelBracket q j w0 w1 lambda hqu hq0pos hq1pos
    hlambda_pos hscale

theorem scratch_caseTwo_u1_primitive_occurrence
    (q : SequencePair × Fin 2) (j : ℤ) (w0 w1 lambda A r : ℝ) (R : ℝ → ℝ)
    (hqu : q.2 = 1) (hq0 : SpacedSequence (q.1 0)) (hq1 : SpacedSequence (q.1 1))
    (hlambda : 0 < lambda) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hscale : Real.sqrt 2 * lambda ≤ q.1 0 j)
    (hratio : lambda * ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) ≤ r)
    (hR : ∀ p : ℝ, |R p| ≤ A * lambda * scaledBracketBump 2 lambda p)
    (hint : Integrable (fun p : ℝ =>
      scaledBracketBump 2 lambda p *
        aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p))) :

    (∫ p : ℝ, |R p| * ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
      aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) ≤
      4 * A * r * C_twoBumpEstimate 2 2 *
        aux_kernelBracketProduct q j (w0 - w1, w0 + w1) := by
  let L : ℝ := (q.1 0 j)⁻¹ + (q.1 1 j)⁻¹
  let B : ℝ → ℝ := fun p =>
    aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)
  let T : ℝ := aux_kernelBracketProduct q j (w0 - w1, w0 + w1)
  have ht0 : 0 < q.1 0 j := (hq0 j).1
  have ht1 : 0 < q.1 1 j := (hq1 j).1
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hB (p : ℝ) : 0 ≤ B p := by
    dsimp [B]
    exact aux_kernelBracketProduct_nonneg q (by
      intro s
      fin_cases s
      · exact hq0
      · exact hq1) j _
  have hT : 0 ≤ T := by
    dsimp [T]
    exact aux_kernelBracketProduct_nonneg q (by
      intro s
      fin_cases s
      · exact hq0
      · exact hq1) j _
  have hproductNonneg (p : ℝ) : 0 ≤ scaledBracketBump 2 lambda p * B p :=
    mul_nonneg (aux_scaledBracketBump_nonneg 2 hlambda _) (hB p)
  have hright : Integrable (fun p : ℝ => A * lambda * L *
      (scaledBracketBump 2 lambda p * B p)) := by
    exact hint.const_mul _
  have hpoint (p : ℝ) : |R p| * L * B p ≤ A * lambda * L *
      (scaledBracketBump 2 lambda p * B p) := by
    calc
      |R p| * L * B p = |R p| * (L * B p) := by ring
      _ ≤ (A * lambda * scaledBracketBump 2 lambda p) * (L * B p) :=
        mul_le_mul_of_nonneg_right (hR p) (mul_nonneg hL (hB p))
      _ = A * lambda * L * (scaledBracketBump 2 lambda p * B p) := by ring
  have hleftnon (p : ℝ) : 0 ≤ |R p| * L * B p :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hL) (hB p)
  have hU1 := scratch_caseTwo_u1_kernelBracket q j w0 w1 lambda hqu ht0 ht1
    hlambda hscale
  have hU1' : (∫ p : ℝ, scaledBracketBump 2 lambda p * B p) ≤
      4 * C_twoBumpEstimate 2 2 * T := by
    simpa [B, T, aux_kernelBracketProduct, mul_assoc] using hU1
  have hIntegralNonneg : 0 ≤ ∫ p : ℝ, scaledBracketBump 2 lambda p * B p :=
    integral_nonneg hproductNonneg
  have hCtwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  have hI :
      (∫ p : ℝ, |R p| * L * B p) ≤
        A * lambda * L * (∫ p : ℝ, scaledBracketBump 2 lambda p * B p) := by
    calc
      (∫ p : ℝ, |R p| * L * B p) ≤
          ∫ p : ℝ, A * lambda * L * (scaledBracketBump 2 lambda p * B p) :=
        integral_mono_of_nonneg (ae_of_all _ hleftnon) hright (ae_of_all _ hpoint)
      _ = A * lambda * L * (∫ p : ℝ, scaledBracketBump 2 lambda p * B p) := by
        rw [integral_const_mul]
  have hAL : 0 ≤ A * (lambda * L) := mul_nonneg hA (mul_nonneg hlambda.le hL)
  have hAr : 0 ≤ A * r := mul_nonneg hA hr
  change (∫ p : ℝ, |R p| * L * B p) ≤ 4 * A * r * C_twoBumpEstimate 2 2 * T
  calc
    (∫ p : ℝ, |R p| * L * B p) ≤
        A * lambda * L * (∫ p : ℝ, scaledBracketBump 2 lambda p * B p) := hI
    _ = A * (lambda * L) * (∫ p : ℝ, scaledBracketBump 2 lambda p * B p) := by ring
    _ ≤ A * r * (∫ p : ℝ, scaledBracketBump 2 lambda p * B p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hA) hIntegralNonneg
    _ ≤ A * r * (4 * C_twoBumpEstimate 2 2 * T) :=
      mul_le_mul_of_nonneg_left hU1' hAr
    _ = 4 * A * r * C_twoBumpEstimate 2 2 * T := by ring


namespace ScratchCase2Witness

noncomputable def caseTwoOccurrence (P : Multiset (SequencePair × Fin 2))
    (k : Fin P.card) : SequencePair × Fin 2 :=
  P.toList.get (Fin.cast (Multiset.length_toList P).symm k)


theorem caseTwoOccurrence_mem (P : Multiset (SequencePair × Fin 2))
    (k : Fin P.card) : caseTwoOccurrence P k ∈ P := by
  unfold caseTwoOccurrence
  rw [← Multiset.mem_toList]
  exact List.get_mem _ _

/-- The pointwise maximum of the two H-package scales. -/
def caseTwoMaxScale (q : SequencePair × Fin 2) : ℤ → ℝ :=
  fun j => max (q.1 0 j) (q.1 1 j)

/-- The second scale in the first orientation-zero Case 2 output. -/
def caseTwoLambdaMaxScale (lam : ℤ → ℝ) (q : SequencePair × Fin 2) : ℤ → ℝ :=
  fun j => max (lam j) (q.1 1 j)

/-- Five padded slots per occurrence.  For an orientation-zero occurrence, slots `0,1,2`
are exactly the three terms of the three-bump/orthogonal estimate.  For an orientation-one
occurrence, slot `0` is its one two-bump term.  Every other slot is harmless repetition of
the original nonnegative kernel product. -/
def caseTwoExactSlotOf (lam : ℤ → ℝ) (q : SequencePair × Fin 2) (r : Fin 5) :
    SequencePair × Fin 2 :=
  if hq : q.2 = 0 then
    if r = 0 then
      (aux_sequencePairOf (q.1 0) (caseTwoLambdaMaxScale lam q), (0 : Fin 2))
    else if r = 1 then
      (aux_sequencePairOf lam (caseTwoMaxScale q), (0 : Fin 2))
    else if r = 2 then
      (aux_sequencePairOf lam (caseTwoMaxScale q), (1 : Fin 2))
    else q
  else q

theorem caseTwoExactSlotOf_spaced (lam : ℤ → ℝ) (hlam : SpacedSequence lam)
    (q : SequencePair × Fin 2) (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (r : Fin 5) :
    ∀ s : Fin 2, SpacedSequence ((caseTwoExactSlotOf lam q r).1 s) := by
  by_cases hqu : q.2 = 0
  · by_cases hr0 : r = 0
    · intro s
      fin_cases s
      · simpa [caseTwoExactSlotOf, hqu, hr0, aux_sequencePairOf] using hq 0
      · simp only [caseTwoExactSlotOf, dif_pos hqu, if_pos hr0, aux_sequencePairOf]
        change SpacedSequence (caseTwoLambdaMaxScale lam q)
        unfold caseTwoLambdaMaxScale
        exact max_mem_A hlam (hq 1)
    · by_cases hr1 : r = 1
      · intro s
        fin_cases s
        · simpa [caseTwoExactSlotOf, hqu, hr0, hr1, aux_sequencePairOf] using hlam
        · simp only [caseTwoExactSlotOf, dif_pos hqu, if_neg hr0, if_pos hr1,
            aux_sequencePairOf]
          change SpacedSequence (caseTwoMaxScale q)
          unfold caseTwoMaxScale
          exact max_mem_A (hq 0) (hq 1)
      · by_cases hr2 : r = 2
        · intro s
          fin_cases s
          · simpa [caseTwoExactSlotOf, hqu, hr0, hr1, hr2, aux_sequencePairOf] using hlam
          · simp only [caseTwoExactSlotOf, dif_pos hqu, if_neg hr0, if_neg hr1,
              if_pos hr2, aux_sequencePairOf]
            change SpacedSequence (caseTwoMaxScale q)
            unfold caseTwoMaxScale
            exact max_mem_A (hq 0) (hq 1)
        · simpa [caseTwoExactSlotOf, hqu, hr0, hr1, hr2] using hq
  · simpa [caseTwoExactSlotOf, hqu] using hq

/-- The natural-number carrier for six occurrences and five padded slots. -/
def caseTwoSlotIndex (b : ℕ) : Fin 6 × Fin 5 :=
  (⟨(b / 5) % 6, Nat.mod_lt _ (by norm_num)⟩,
    ⟨b % 5, Nat.mod_lt _ (by norm_num)⟩)

noncomputable def caseTwoSlotNat {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (b : ℕ) : SequencePair × Fin 2 :=
  caseTwoExactSlotOf lam
    (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
      (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm (caseTwoSlotIndex b).1))
    (caseTwoSlotIndex b).2

def caseTwoB : Finset ℕ := Finset.range 30

def caseTwoOrientation {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (b : ℕ) : Fin 2 :=
  (caseTwoSlotNat γ i lam b).2

def caseTwoScales {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (b : ℕ) (m : Fin 2 → ℕ) : SequencePair :=
  fun r j => (2 : ℝ) ^ (m r) * (caseTwoSlotNat γ i lam b).1 r j

theorem caseTwoB_card : caseTwoB.card ≤ C_gaussianDominationCombinedCard := by
  norm_num [caseTwoB, C_gaussianDominationCombinedCard]

theorem caseTwoSlotNat_spaced {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (b : ℕ) :
    ∀ r : Fin 2, SpacedSequence ((caseTwoSlotNat γ i lam b).1 r) := by
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let k : Fin P.card := Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm
    (caseTwoSlotIndex b).1
  let q : SequencePair × Fin 2 := caseTwoOccurrence P k
  have hqmem : q ∈ P := caseTwoOccurrence_mem P k

  have hvalid := aux_hKernelGaussianMultiset_valid γ i q (by simpa [P] using hqmem)
  have hq : ∀ r : Fin 2, SpacedSequence (q.1 r) := by
    intro r
    fin_cases r
    · exact hvalid.1.1
    · exact hvalid.2.1
  have hslot := caseTwoExactSlotOf_spaced lam hlam q hq (caseTwoSlotIndex b).2
  simpa [caseTwoSlotNat, P, k, q] using hslot

theorem caseTwoScales_spaced {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (b : ℕ)
    (m : Fin 2 → ℕ) (r : Fin 2) :
    SpacedSequence (caseTwoScales γ i lam b m r) := by
  unfold caseTwoScales
  exact smul_mem_A (caseTwoSlotNat_spaced γ i lam hlam b r) (pow_pos (by norm_num) _)

/-- Enlarging a finite comparison radius preserves the comparison. -/
theorem caseTwo_within_mono {a q : ℤ → ℝ} {d e : ℕ} (ha : SpacedSequence a)
    (hq : WithinSequenceDistance a q d) (hde : d ≤ e) :
    WithinSequenceDistance a q e := by
  intro j
  constructor
  · calc
      a (j - e) ≤ a (j - d) := aux_spacedSequence_monotone ha (by omega)
      _ ≤ q j := (hq j).1
  · calc
      q j ≤ a (j + d) := (hq j).2
      _ ≤ a (j + e) := aux_spacedSequence_monotone ha (by omega)

/-- Pointwise maxima preserve a common finite distance-ball comparison. -/
theorem caseTwo_within_max {a q₀ q₁ : ℤ → ℝ} {d : ℕ}
    (hq₀ : WithinSequenceDistance a q₀ d) (hq₁ : WithinSequenceDistance a q₁ d) :
    WithinSequenceDistance a (fun j => max (q₀ j) (q₁ j)) d := by
  intro j
  constructor
  · exact (hq₀ j).1.trans (le_max_left _ _)
  · exact max_le (hq₀ j).2 (hq₁ j).2

/-- The three Case 2 orientation-zero outputs, the orientation-one output, and padding all
have pair distance at most `2(Δ+h)` once `λ` lies within `Δ+h` of the reference scale. -/
theorem caseTwoExactSlotOf_distance_bound {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (h : ℕ)
    (hlam : WithinSequenceDistance (γ.scales i 1) lam (geometricDelta γ + h))
    (q : SequencePair × Fin 2) (hq : q ∈ aux_hKernelGaussianMultiset γ i) (r : Fin 5) :
    sequencePairDistance (caseTwoExactSlotOf lam q r).1 ≤
      ((2 * (geometricDelta γ + h) : ℕ) : WithTop ℕ) := by
  let a : ℤ → ℝ := γ.scales i 1
  let d : ℕ := geometricDelta γ
  have ha : SpacedSequence a := γ.scales_spaced i 1
  have hvalid := aux_hKernelGaussianMultiset_valid γ i q hq
  have hq₀ : WithinSequenceDistance a (q.1 0) d := by
    apply aux_withinSequenceDistance_of_sequenceDistance_le ha

    simpa [a, d] using hvalid.1.2
  have hq₁ : WithinSequenceDistance a (q.1 1) d := by
    apply aux_withinSequenceDistance_of_sequenceDistance_le ha
    simpa [a, d] using hvalid.2.2
  have hq₀wide : WithinSequenceDistance a (q.1 0) (d + h) :=
    caseTwo_within_mono ha hq₀ (Nat.le_add_right _ _)
  have hq₁wide : WithinSequenceDistance a (q.1 1) (d + h) :=
    caseTwo_within_mono ha hq₁ (Nat.le_add_right _ _)
  have hlam' : WithinSequenceDistance a lam (d + h) := by
    simpa [a, d] using hlam
  have hmaxq : WithinSequenceDistance a (caseTwoMaxScale q) (d + h) := by
    unfold caseTwoMaxScale
    exact caseTwo_within_max hq₀wide hq₁wide
  have hmaxlam : WithinSequenceDistance a (caseTwoLambdaMaxScale lam q) (d + h) := by
    unfold caseTwoLambdaMaxScale
    exact caseTwo_within_max hlam' hq₁wide
  have hq₀a : SequenceDistance (q.1 0) a ≤ (d : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    exact aux_sequenceDistance_le_of_within hq₀
  have hq₁a : SequenceDistance (q.1 1) a ≤ (d : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    exact aux_sequenceDistance_le_of_within hq₁
  have haq₁ : SequenceDistance a (q.1 1) ≤ (d : WithTop ℕ) :=
    aux_sequenceDistance_le_of_within hq₁
  have hlam_a : SequenceDistance lam a ≤ ((d + h : ℕ) : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    exact aux_sequenceDistance_le_of_within hlam'
  have hmaxq_dist : SequenceDistance a (caseTwoMaxScale q) ≤ ((d + h : ℕ) : WithTop ℕ) :=
    aux_sequenceDistance_le_of_within hmaxq
  have hmaxlam_dist :
      SequenceDistance a (caseTwoLambdaMaxScale lam q) ≤ ((d + h : ℕ) : WithTop ℕ) :=
    aux_sequenceDistance_le_of_within hmaxlam
  have hfirst : SequenceDistance (q.1 0) (caseTwoLambdaMaxScale lam q) ≤
      ((2 * (d + h) : ℕ) : WithTop ℕ) := by
    calc
      SequenceDistance (q.1 0) (caseTwoLambdaMaxScale lam q) ≤
          SequenceDistance (q.1 0) a + SequenceDistance a (caseTwoLambdaMaxScale lam q) :=
        sequenceDistance_triangle _ _ _
      _ ≤ (d : WithTop ℕ) + ((d + h : ℕ) : WithTop ℕ) :=
        add_le_add hq₀a hmaxlam_dist
      _ ≤ ((2 * (d + h) : ℕ) : WithTop ℕ) := by
        norm_cast
        omega
  have hsecond : SequenceDistance lam (caseTwoMaxScale q) ≤
      ((2 * (d + h) : ℕ) : WithTop ℕ) := by
    calc
      SequenceDistance lam (caseTwoMaxScale q) ≤
          SequenceDistance lam a + SequenceDistance a (caseTwoMaxScale q) :=

        sequenceDistance_triangle _ _ _
      _ ≤ ((d + h : ℕ) : WithTop ℕ) + ((d + h : ℕ) : WithTop ℕ) :=
        add_le_add hlam_a hmaxq_dist
      _ = ((2 * (d + h) : ℕ) : WithTop ℕ) := by
        norm_cast
        omega
  have hpad : SequenceDistance (q.1 0) (q.1 1) ≤
      ((2 * (d + h) : ℕ) : WithTop ℕ) := by
    calc
      SequenceDistance (q.1 0) (q.1 1) ≤
          SequenceDistance (q.1 0) a + SequenceDistance a (q.1 1) :=
        sequenceDistance_triangle _ _ _
      _ ≤ (d : WithTop ℕ) + (d : WithTop ℕ) := by
        exact add_le_add hq₀a haq₁
      _ ≤ ((2 * (d + h) : ℕ) : WithTop ℕ) := by
        norm_cast
        omega
  change sequencePairDistance (caseTwoExactSlotOf lam q r).1 ≤
    ((2 * (d + h) : ℕ) : WithTop ℕ)
  unfold sequencePairDistance
  by_cases hqu : q.2 = 0
  · by_cases hr0 : r = 0
    · simp only [caseTwoExactSlotOf, dif_pos hqu, if_pos hr0, aux_sequencePairOf]
      change SequenceDistance (q.1 0) (caseTwoLambdaMaxScale lam q) ≤ _
      exact hfirst
    · by_cases hr1 : r = 1
      · simp only [caseTwoExactSlotOf, dif_pos hqu, if_neg hr0, if_pos hr1,
          aux_sequencePairOf]
        change SequenceDistance lam (caseTwoMaxScale q) ≤ _
        exact hsecond
      · by_cases hr2 : r = 2
        · simp only [caseTwoExactSlotOf, dif_pos hqu, if_neg hr0, if_neg hr1,
            if_pos hr2, aux_sequencePairOf]
          change SequenceDistance lam (caseTwoMaxScale q) ≤ _
          exact hsecond
        · simpa [caseTwoExactSlotOf, hqu, hr0, hr1, hr2] using hpad
  · simpa [caseTwoExactSlotOf, hqu] using hpad

theorem caseTwoSlotNat_distance_bound {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (h : ℕ)
    (hlam : WithinSequenceDistance (γ.scales i 1) lam (geometricDelta γ + h)) (b : ℕ) :
    sequencePairDistance (caseTwoSlotNat γ i lam b).1 ≤
      ((2 * (geometricDelta γ + h) : ℕ) : WithTop ℕ) := by
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let k : Fin P.card := Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm
    (caseTwoSlotIndex b).1
  let q : SequencePair × Fin 2 := caseTwoOccurrence P k
  have hqmem : q ∈ P := caseTwoOccurrence_mem P k
  have hslot := caseTwoExactSlotOf_distance_bound γ i lam h hlam q
    (by simpa [P] using hqmem) (caseTwoSlotIndex b).2
  simpa [caseTwoSlotNat, P, k, q] using hslot

theorem caseTwoScales_distance_bound {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (h : ℕ) (hlam_mem : SpacedSequence lam)
    (hlam : WithinSequenceDistance (γ.scales i 1) lam (geometricDelta γ + h))
    (b : ℕ) (m : Fin 2 → ℕ) :
    sequencePairDistance (caseTwoScales γ i lam b m) ≤
      (C_gaussianDominationCombinedDistance : WithTop ℕ) *
        ((geometricDelta γ + h + aux_natPairWeight m : ℕ) : WithTop ℕ) := by
  let p : SequencePair := (caseTwoSlotNat γ i lam b).1
  let d : ℕ := geometricDelta γ
  have hp₀ : SpacedSequence (p 0) := by
    simpa [p] using caseTwoSlotNat_spaced γ i lam hlam_mem b 0
  have hp₁ : SpacedSequence (p 1) := by
    simpa [p] using caseTwoSlotNat_spaced γ i lam hlam_mem b 1
  have hbase : SequenceDistance (p 0) (p 1) ≤ ((2 * (d + h) : ℕ) : WithTop ℕ) := by
    simpa [sequencePairDistance, p, d] using
      caseTwoSlotNat_distance_bound γ i lam h hlam b
  have hleft : SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j) (p 0) ≤
      ((m 0 : ℕ) : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    have hdist := sequenceDistance_pow_two_smul_le hp₀ ((m 0 : ℕ) : ℤ)
    simpa [zpow_natCast, Int.natAbs_natCast] using hdist
  have hright : SequenceDistance (p 1) (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤
      ((m 1 : ℕ) : WithTop ℕ) := by
    have hdist := sequenceDistance_pow_two_smul_le hp₁ ((m 1 : ℕ) : ℤ)
    simpa [zpow_natCast, Int.natAbs_natCast] using hdist
  change SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j)
      (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤ _
  calc
    SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j)
        (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤
        SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j) (p 0) +
          SequenceDistance (p 0) (fun j => (2 : ℝ) ^ (m 1) * p 1 j) :=
      sequenceDistance_triangle _ _ _
    _ ≤ (m 0 : WithTop ℕ) +
          (SequenceDistance (p 0) (p 1) +
            SequenceDistance (p 1) (fun j => (2 : ℝ) ^ (m 1) * p 1 j)) := by
      gcongr
      exact sequenceDistance_triangle _ _ _
    _ ≤ (m 0 : WithTop ℕ) + ((2 * (d + h) : ℕ) : WithTop ℕ) + m 1 := by
      simpa [add_assoc] using add_le_add hbase hright
    _ ≤ (C_gaussianDominationCombinedDistance : WithTop ℕ) *
          ((d + h + aux_natPairWeight m : ℕ) : WithTop ℕ) := by
      norm_num [C_gaussianDominationCombinedDistance]
      norm_cast
      simp only [aux_natPairWeight]
      omega

theorem caseTwo_witness_side_conditions {n : ℕ} (γ : GeometricParameters n)


    (i : Fin γ.k) (lam : ℤ → ℝ) (h : ℕ) (hlam_mem : SpacedSequence lam)
    (hlam : WithinSequenceDistance (γ.scales i 1) lam (geometricDelta γ + h)) :
    caseTwoB.card ≤ C_gaussianDominationCombinedCard ∧
      (∀ b ∈ caseTwoB, ∀ m : Fin 2 → ℕ, ∀ r : Fin 2,
        SpacedSequence (caseTwoScales γ i lam b m r)) ∧
      (∀ b ∈ caseTwoB, ∀ m : Fin 2 → ℕ,
        sequencePairDistance (caseTwoScales γ i lam b m) ≤
          (C_gaussianDominationCombinedDistance : WithTop ℕ) *
            ((geometricDelta γ + h + aux_natPairWeight m : ℕ) : WithTop ℕ)) := by
  refine ⟨caseTwoB_card, ?_, ?_⟩
  · intro b _ m r
    exact caseTwoScales_spaced γ i lam hlam_mem b m r
  · intro b _ m
    exact caseTwoScales_distance_bound γ i lam h hlam_mem hlam b m

theorem caseTwoSlotIndex_encode (k : Fin 6) (r : Fin 5) :
    caseTwoSlotIndex (k.1 * 5 + r.1) = (k, r) := by
  apply Prod.ext <;> apply Fin.ext <;> simp [caseTwoSlotIndex]
  · omega

theorem caseTwoSlotNat_encode {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) (k : Fin 6) (r : Fin 5) :
    caseTwoSlotNat γ i lam (k.1 * 5 + r.1) =
      caseTwoExactSlotOf lam
        (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
          (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r := by
  unfold caseTwoSlotNat
  rw [caseTwoSlotIndex_encode]

theorem caseTwo_sum_range30_reindex {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) {R : Type*} [AddCommMonoid R]
    (F : SequencePair × Fin 2 → R) :
    ∑ b ∈ caseTwoB, F (caseTwoSlotNat γ i lam b) =
      ∑ k : Fin 6, ∑ r : Fin 5,
        F (caseTwoExactSlotOf lam
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r) := by
  classical
  calc
    ∑ b ∈ caseTwoB, F (caseTwoSlotNat γ i lam b) =
        ∑ b : Fin 30, F (caseTwoSlotNat γ i lam b) := by
      simpa [caseTwoB] using
        (Finset.sum_range (fun b : ℕ => F (caseTwoSlotNat γ i lam b)))
    _ = ∑ kr : Fin 6 × Fin 5,
        F (caseTwoExactSlotOf lam
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm kr.1)) kr.2) := by
      let e : Fin 6 × Fin 5 ≃ Fin 30 := finProdFinEquiv
      symm
      refine Fintype.sum_equiv e
        (fun kr => F (caseTwoExactSlotOf lam
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm kr.1)) kr.2))
        (fun b => F (caseTwoSlotNat γ i lam b)) ?_
      intro kr
      apply congrArg F
      have he : (e kr).1 = kr.1.1 * 5 + kr.2.1 := by
        change kr.2.1 + 5 * kr.1.1 = kr.1.1 * 5 + kr.2.1
        omega
      rw [he, caseTwoSlotNat_encode]
    _ = ∑ k : Fin 6, ∑ r : Fin 5,
        F (caseTwoExactSlotOf lam
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r) := by
      simpa using (Fintype.sum_prod_type (fun kr : Fin 6 × Fin 5 =>
        F (caseTwoExactSlotOf lam
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm kr.1)) kr.2)))

/-- The unpadded Case 2 outputs: three from an orientation-zero occurrence and one from an
orientation-one occurrence. -/
def caseTwoActiveSlots (lam : ℤ → ℝ) (q : SequencePair × Fin 2) :
    Multiset (SequencePair × Fin 2) :=
  if q.2 = 0 then
    {caseTwoExactSlotOf lam q 0} + {caseTwoExactSlotOf lam q 1} +
      {caseTwoExactSlotOf lam q 2}
  else {q}

def caseTwoActivePackage (lam : ℤ → ℝ) (P : Multiset (SequencePair × Fin 2)) :
    Multiset (SequencePair × Fin 2) :=
  P.bind (caseTwoActiveSlots lam)

/-- The manuscript's `14` count applies only when the H package has its two orientation-one
entries.  In the other canonical orientation all six occurrences are orientation zero, so the
same construction has exactly `18` unpadded outputs. -/
theorem caseTwoCanonicalActivePackage_card {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lam : ℤ → ℝ) :
    (caseTwoActivePackage lam (aux_hKernelGaussianMultiset γ i)).card =
      if γ.orientation i = 0 then 18 else 14 := by
  classical
  by_cases h : γ.orientation i = 0 <;>
    simp [caseTwoActivePackage, caseTwoActiveSlots, aux_hKernelGaussianMultiset, h]
end ScratchCase2Witness

namespace ScratchCase2Cohesive
open ScratchCase2Witness

private noncomputable def scratch_caseTwoLambda {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) : ℤ → ℝ :=
  fun j => (2 : ℝ) ^ (ι.1.1 + 1) *
    γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)

private theorem scratch_caseTwoLambda_spaced {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) : SpacedSequence (scratch_caseTwoLambda γ ι i) := by
  unfold scratch_caseTwoLambda
  simpa [sub_eq_add_neg, add_assoc] using
    (smul_mem_A (shift_mem_A (γ.scales_spaced i 1)
      (-(geometricDelta γ : ℤ) - 1)) (zpow_pos (by norm_num) _))

private theorem scratch_caseTwo_within_backward_shift (a : ℤ → ℝ) (ha : SpacedSequence a)
    (d : ℕ) :
    WithinSequenceDistance a (fun j => a (j - (d : ℤ) - 1)) (d + 1) := by
  intro j
  constructor
  · apply le_of_eq
    congr 1
    push_cast
    ring
  · apply aux_spacedSequence_monotone ha
    push_cast
    omega

private theorem scratch_caseTwoLambda_within {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (hnegative : ι.1.1 < 0) :
    WithinSequenceDistance (γ.scales i 1) (scratch_caseTwoLambda γ ι i)
      (geometricDelta γ + ι.1.1.natAbs) := by
  let a : ℤ → ℝ := γ.scales i 1
  let d : ℕ := geometricDelta γ
  let h : ℤ := ι.1.1
  let ashift : ℤ → ℝ := fun j => a (j - (d : ℤ) - 1)
  let lam : ℤ → ℝ := fun j => (2 : ℝ) ^ (h + 1) * ashift j
  have ha : SpacedSequence a := γ.scales_spaced i 1
  have hashift : SpacedSequence ashift := by
    dsimp [ashift]
    simpa [sub_eq_add_neg, add_assoc] using
      (shift_mem_A ha (-(d : ℤ) - 1))
  have hshift : WithinSequenceDistance a ashift (d + 1) := by
    simpa [a, ashift] using scratch_caseTwo_within_backward_shift a ha d
  have hpowdist : SequenceDistance ashift lam ≤ ((h + 1).natAbs : WithTop ℕ) := by
    simpa [lam] using sequenceDistance_pow_two_smul_le hashift (h + 1)
  have hpow : WithinSequenceDistance ashift lam (h + 1).natAbs :=
    aux_withinSequenceDistance_of_sequenceDistance_le hashift hpowdist
  have hcomp := aux_withinSequenceDistance_trans hshift hpow
  have hle : d + 1 + (h + 1).natAbs ≤ d + h.natAbs := by omega
  have hfinal : WithinSequenceDistance a lam (d + h.natAbs) := by
    intro j
    have hc := hcomp j
    constructor
    · calc
        a (j - ((d + h.natAbs : ℕ) : ℤ)) ≤

            a (j - ((d + 1 + (h + 1).natAbs : ℕ) : ℤ)) := by
              apply aux_spacedSequence_monotone ha
              omega
        _ ≤ lam j := by
          simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hc.1
    · calc
        lam j ≤ a (j + ((d + 1 + (h + 1).natAbs : ℕ) : ℤ)) := by
          simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hc.2
        _ ≤ a (j + ((d + h.natAbs : ℕ) : ℤ)) := by
          apply aux_spacedSequence_monotone ha
          omega
  convert hfinal using 1
  funext j
  rfl

private theorem scratch_caseTwo_negative_loss {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (hnegative : ι.1.1 < 0) :
    (2 : ℝ) ^ (ι.1.1 + 1) ≤
      2 * Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) := by
  let h : ℤ := ι.1.1
  let N : ℕ := h.natAbs
  have hN : (N : ℤ) = -h := by
    simpa [N] using (Int.natAbs_of_nonneg (show 0 ≤ -h by dsimp [h]; omega))
  have hNR : (N : ℝ) = -(h : ℝ) := by
    calc
      (N : ℝ) = ((N : ℤ) : ℝ) := by norm_num
      _ = ((-h : ℤ) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hN
      _ = -(h : ℝ) := by rw [Int.cast_neg]
  have hneg : h < 0 := by simpa [h] using hnegative
  have hexp : ((h + 1 : ℤ) : ℝ) ≤ 1 - (N : ℝ) / 2 := by
    rw [hNR]
    push_cast
    linarith
  have hpow : Real.rpow 2 ((h + 1 : ℤ) : ℝ) ≤
      Real.rpow 2 (1 - (N : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  change (2 : ℝ) ^ (h + 1) ≤ 2 * Real.rpow 2 (-(N : ℝ) / 2)
  calc
    (2 : ℝ) ^ (h + 1) = Real.rpow 2 ((h + 1 : ℤ) : ℝ) :=
      (Real.rpow_intCast _ _).symm
    _ ≤ Real.rpow 2 (1 - (N : ℝ) / 2) := hpow
    _ = Real.rpow 2 (1 + (-(N : ℝ) / 2)) := by congr 1 <;> ring
    _ = Real.rpow 2 1 * Real.rpow 2 (-(N : ℝ) / 2) :=
      Real.rpow_add (by norm_num) _ _
    _ = 2 * Real.rpow 2 (-(N : ℝ) / 2) := by norm_num

private noncomputable def scratch_caseTwoPrimitive {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) : ℝ → ℝ :=
  fun p => ∫ x : ℝ in Set.Iic p, nMultiplierRho γ hkn ι i j x

private theorem scratch_caseTwoPrimitive_bound {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ)
    (hnegative : ι.1.1 < 0) (p : ℝ) :
    |scratch_caseTwoPrimitive γ hkn ι i j p| ≤
      ((3 / 2 : ℝ) * C_standardBumpPropertiesTilde 0 3 *
        C_fourScaleGaussianKernel 3) * scratch_caseTwoLambda γ ι i j *
        scaledBracketBump 2 (scratch_caseTwoLambda γ ι i j) p := by
  let A : ℝ := 3 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3
  let lam : ℝ := scratch_caseTwoLambda γ ι i j
  have hlam : 0 < lam := by
    dsimp [lam, scratch_caseTwoLambda]
    exact mul_pos (zpow_pos (by norm_num) _)
      ((γ.scales_spaced i 1) _).1
  have hA : 0 ≤ A := by
    dsimp [A]
    have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 3 := by
      rw [show C_standardBumpPropertiesTilde 0 3 = (2 : ℝ) ^ (33 : ℕ) by
        norm_num [C_standardBumpPropertiesTilde]]
      positivity
    have hfour : 0 ≤ C_fourScaleGaussianKernel 3 := by
      have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) :=
        (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
      have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) :=
        (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
      unfold C_fourScaleGaussianKernel C_smoothDecay2
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
        (mul_nonneg (by positivity) hsecond)
    positivity
  have hrho : Integrable (nMultiplierRho γ hkn ι i j) :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (nMultiplierRho_memW0 γ hkn ι i j)
  have hzero : ι.1.1 ≠ 0 := ne_of_lt hnegative
  have hdecay (x : ℝ) : |nMultiplierRho γ hkn ι i j x| ≤
      A * scaledBracketBump 3 lam x := by
    simpa [A, lam, scratch_caseTwoLambda, mul_assoc] using
      scratch_nMultiplierRho_negative_decay_bound_collapsed γ hkn ι i j hzero hnegative x
  have htail := scratch_primitive_Iic_bound A lam hA hlam hrho
    (scratch_nMultiplierRho_negative_integral_zero γ hkn ι i j hzero hnegative)
    hdecay p
  change |∫ x : ℝ in Set.Iic p, nMultiplierRho γ hkn ι i j x| ≤ _
  calc
    |∫ x : ℝ in Set.Iic p, nMultiplierRho γ hkn ι i j x| ≤
        (A / 2) * lam * scaledBracketBump 2 lam p := htail
    _ = _ := by dsimp [A, lam]; ring

private theorem scratch_caseTwoPrimitive_continuous {n : ℕ} (γ : GeometricParameters n)

    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) :
    Continuous (scratch_caseTwoPrimitive γ hkn ι i j) := by
  have hrhoCont : Continuous (nMultiplierRho γ hkn ι i j) :=
    (nMultiplierRho_memW0 γ hkn ι i j).1
  have hrhoInt : Integrable (nMultiplierRho γ hkn ι i j) :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (nMultiplierRho_memW0 γ hkn ι i j)
  have hdiff : Differentiable ℝ (scratch_caseTwoPrimitive γ hkn ι i j) := by
    intro x
    change DifferentiableAt ℝ
      (fun y : ℝ => ∫ q : ℝ in Set.Iic y, nMultiplierRho γ hkn ι i j q) x
    exact (scratch_cumulativeIic_hasDerivAt hrhoCont hrhoInt x).differentiableAt
  exact hdiff.continuous

private theorem scratch_caseTwo_ratio_of_package {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) (hnegative : ι.1.1 < 0)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) :
    scratch_caseTwoLambda γ ι i j * ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) ≤
      (2 : ℝ) ^ (ι.1.1 + 1) := by
  let lam : ℝ := scratch_caseTwoLambda γ ι i j
  rcases hP.1 q hqmem with ⟨hq0, hq1⟩
  have hlam : 0 ≤ lam := by
    dsimp [lam, scratch_caseTwoLambda]
    exact mul_nonneg (zpow_pos (by norm_num) _).le
      ((γ.scales_spaced i 1) _).1.le
  have ht0 : 0 < q.1 0 j := (hq0.1 j).1
  have ht1 : 0 < q.1 1 j := (hq1.1 j).1
  have h0 : lam / q.1 0 j ≤ (2 : ℝ) ^ ι.1.1 := by
    dsimp [lam, scratch_caseTwoLambda]
    exact scratch_negative_distanceBall_scale_ratio_le (γ.scales_spaced i 1) hq0
      ι.1.1 hnegative j
  have h1 : lam / q.1 1 j ≤ (2 : ℝ) ^ ι.1.1 := by
    dsimp [lam, scratch_caseTwoLambda]
    exact scratch_negative_distanceBall_scale_ratio_le (γ.scales_spaced i 1) hq1
      ι.1.1 hnegative j
  simpa [lam] using scratch_negative_scale_ratio_sum_le lam (q.1 0 j) (q.1 1 j)
    ι.1.1 hlam ht0 ht1 h0 h1

private theorem scratch_caseTwo_scaledBracketBumpReal_le_inv
    (N s x : ℝ) (hN : 0 ≤ N) (hs : 0 < s) :
    scaledBracketBumpReal N s x ≤ s⁻¹ := by
  unfold scaledBracketBumpReal
  have hbase : 1 ≤ 1 + |s⁻¹ * x| := by linarith [abs_nonneg (s⁻¹ * x)]
  have hpow : Real.rpow (1 + |s⁻¹ * x|) (-N) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  calc
    s⁻¹ * Real.rpow (1 + |s⁻¹ * x|) (-N) ≤ s⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hs.le)
    _ = s⁻¹ := by ring

private theorem scratch_caseTwo_scaledBracketBumpReal_product_integrable

    (n0 n1 s0 s1 x0 x1 : ℝ) (hn0 : 1 < n0) (hn1 : 0 ≤ n1)
    (hs0 : 0 < s0) (hs1 : 0 < s1) :
    Integrable (fun p : ℝ => scaledBracketBumpReal n0 s0 (x0 - p) *
      scaledBracketBumpReal n1 s1 (x1 - p)) := by
  have hbase : Integrable (fun p : ℝ => scaledBracketBumpReal n0 s0 (x0 - p)) :=
    aux_integrable_scaledBracketBumpReal_translate n0 s0 x0 hn0 hs0
  refine (hbase.const_mul s1⁻¹).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hleftBase : Continuous (fun p : ℝ => 1 + |s0⁻¹ * (x0 - p)|) := by fun_prop
    have hrightBase : Continuous (fun p : ℝ => 1 + |s1⁻¹ * (x1 - p)|) := by fun_prop
    have hleft : Continuous (fun p : ℝ => scaledBracketBumpReal n0 s0 (x0 - p)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact hleftBase.continuousAt.rpow_const (Or.inl (by positivity))
    have hright : Continuous (fun p : ℝ => scaledBracketBumpReal n1 s1 (x1 - p)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro p
      exact hrightBase.continuousAt.rpow_const (Or.inl (by positivity))
    exact hleft.mul hright
  · filter_upwards [] with p
    have hleft : 0 ≤ scaledBracketBumpReal n0 s0 (x0 - p) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hs0
    have hright : 0 ≤ scaledBracketBumpReal n1 s1 (x1 - p) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hs1
    have hle := scratch_caseTwo_scaledBracketBumpReal_le_inv n1 s1 (x1 - p) hn1 hs1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft hright)]
    calc
      scaledBracketBumpReal n0 s0 (x0 - p) *
          scaledBracketBumpReal n1 s1 (x1 - p) ≤
        scaledBracketBumpReal n0 s0 (x0 - p) * s1⁻¹ :=
          mul_le_mul_of_nonneg_left hle hleft
      _ = s1⁻¹ * scaledBracketBumpReal n0 s0 (x0 - p) := by ring

private theorem scratch_caseTwo_scaledBracketBump_le_inv
    (N : ℕ) (s x : ℝ) (hs : 0 < s) : scaledBracketBump N s x ≤ s⁻¹ := by
  have h := scratch_caseTwo_scaledBracketBumpReal_le_inv (N : ℝ) s x
    (Nat.cast_nonneg N) hs
  simpa [aux_caseTwo.scratch_scaledBracketBump_nat_eq_real] using h

private theorem scratch_caseTwo_continuous_scaledBracketBump (N : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ => scaledBracketBump N s x) := by
  unfold scaledBracketBump
  have hbase : Continuous (fun x : ℝ => 1 + |s⁻¹ * x|) := by fun_prop
  apply continuous_const.mul
  rw [continuous_iff_continuousAt]
  intro x
  exact (hbase.continuousAt.inv₀ (ne_of_gt (by positivity))).pow N

/-- The weighted bracket product needed by both Case 2 occurrence bounds is integrable. -/
private theorem scratch_caseTwo_weighted_kernel_integrable
    (q : SequencePair × Fin 2) (j : ℤ) (w0 w1 lam : ℝ)
    (hq0 : SpacedSequence (q.1 0)) (hq1 : SpacedSequence (q.1 1))
    (hlam : 0 < lam) :
    Integrable (fun p : ℝ => scaledBracketBump 2 lam p *
      aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) := by
  let t0 : ℝ := q.1 0 j
  let t1 : ℝ := q.1 1 j
  have ht0 : 0 < t0 := by simpa [t0] using (hq0 j).1
  have ht1 : 0 < t1 := by simpa [t1] using (hq1 j).1
  by_cases hu : q.2 = 0
  · have hbaseReal := scratch_caseTwo_scaledBracketBumpReal_product_integrable
      2 2 t0 t1 (w0 - w1) (w0 + w1) (by norm_num) (by norm_num) ht0 ht1
    have hbase : Integrable (fun p : ℝ =>
        scaledBracketBump 2 t0 (w0 - w1 - p) *
          scaledBracketBump 2 t1 (w0 + w1 - p)) := by
      convert hbaseReal using 1
      funext p
      norm_num [aux_caseTwo.scratch_scaledBracketBump_nat_eq_real]
    have hcont : Continuous (fun p : ℝ =>
        scaledBracketBump 2 lam p *
          (scaledBracketBump 2 t0 (w0 - w1 - p) *
            scaledBracketBump 2 t1 (w0 + w1 - p))) := by
      exact (scratch_caseTwo_continuous_scaledBracketBump 2 lam).mul
        ((scratch_caseTwo_continuous_scaledBracketBump 2 t0).comp
          (continuous_const.sub continuous_id) |>.mul
        ((scratch_caseTwo_continuous_scaledBracketBump 2 t1).comp
          (continuous_const.sub continuous_id)))
    have htarget : Integrable (fun p : ℝ =>
        scaledBracketBump 2 lam p *
          (scaledBracketBump 2 t0 (w0 - w1 - p) *
            scaledBracketBump 2 t1 (w0 + w1 - p))) := by
      refine (hbase.const_mul lam⁻¹).mono' hcont.aestronglyMeasurable ?_
      filter_upwards [] with p
      have hlamB : 0 ≤ scaledBracketBump 2 lam p :=
        aux_scaledBracketBump_nonneg 2 hlam p
      have ht0B : 0 ≤ scaledBracketBump 2 t0 (w0 - w1 - p) :=
        aux_scaledBracketBump_nonneg 2 ht0 _
      have ht1B : 0 ≤ scaledBracketBump 2 t1 (w0 + w1 - p) :=
        aux_scaledBracketBump_nonneg 2 ht1 _
      have hle := scratch_caseTwo_scaledBracketBump_le_inv 2 lam p hlam
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlamB (mul_nonneg ht0B ht1B))]
      calc
        scaledBracketBump 2 lam p *
            (scaledBracketBump 2 t0 (w0 - w1 - p) *

              scaledBracketBump 2 t1 (w0 + w1 - p)) ≤
          lam⁻¹ * (scaledBracketBump 2 t0 (w0 - w1 - p) *
              scaledBracketBump 2 t1 (w0 + w1 - p)) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg ht0B ht1B)
        _ = lam⁻¹ *
            (scaledBracketBump 2 t0 (w0 - w1 - p) *
              scaledBracketBump 2 t1 (w0 + w1 - p)) := rfl
    convert htarget using 1
    funext p
    simp [aux_kernelBracketProduct, hu, t0, t1, W]
  · have hu1 : q.2 = 1 := Fin.eq_one_of_ne_zero q.2 hu
    have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hvarReal : Integrable (fun p : ℝ =>
        scaledBracketBumpReal 2 t0 (Real.sqrt 2 * (w0 - p))) := by
      have hbase := (aux_integrable_scaledBracketBumpReal 2 t0 (by norm_num) ht0).comp_mul_left'
        (ne_of_gt hsqrt)
      convert hbase.comp_sub_left w0 using 1
    have hvar : Integrable (fun p : ℝ =>
        scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p))) := by
      convert hvarReal using 1
      funext p
      norm_num [aux_caseTwo.scratch_scaledBracketBump_nat_eq_real]
    let b1 : ℝ := scaledBracketBump 2 t1 (Real.sqrt 2 * w1)
    have hb1 : 0 ≤ b1 := by
      dsimp [b1]
      exact aux_scaledBracketBump_nonneg 2 ht1 _
    have hcont : Continuous (fun p : ℝ =>
        scaledBracketBump 2 lam p *
          (scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) * b1)) := by
      exact (scratch_caseTwo_continuous_scaledBracketBump 2 lam).mul
        ((scratch_caseTwo_continuous_scaledBracketBump 2 t0).comp
          (continuous_const.mul (continuous_const.sub continuous_id)) |>.mul continuous_const)
    have htarget : Integrable (fun p : ℝ =>
        scaledBracketBump 2 lam p *
          (scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) * b1)) := by
      refine (hvar.const_mul (lam⁻¹ * b1)).mono' hcont.aestronglyMeasurable ?_
      filter_upwards [] with p
      have hlamB : 0 ≤ scaledBracketBump 2 lam p :=
        aux_scaledBracketBump_nonneg 2 hlam p
      have ht0B : 0 ≤ scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) :=
        aux_scaledBracketBump_nonneg 2 ht0 _
      have hle := scratch_caseTwo_scaledBracketBump_le_inv 2 lam p hlam
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hlamB (mul_nonneg ht0B hb1))]
      calc
        scaledBracketBump 2 lam p * (scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) * b1) ≤
          lam⁻¹ * (scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) * b1) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg ht0B hb1)
        _ = (lam⁻¹ * b1) * scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) := by ring
    have hfirst (p : ℝ) :
        (W q.2 (w0 - w1 - p, w0 + w1 - p)).1 = Real.sqrt 2 * (w0 - p) := by
      rw [hu1]

      simp only [W, Fin.isValue, if_false]
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      have hsquare : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
      calc
        (w0 - w1 - p) + (w0 + w1 - p) = 2 * (w0 - p) := by ring
        _ = (Real.sqrt 2 * (w0 - p)) * Real.sqrt 2 := by
          calc
            2 * (w0 - p) = (Real.sqrt 2)^2 * (w0 - p) := by
              rw [show (Real.sqrt 2)^2 = 2 by norm_num]
            _ = (Real.sqrt 2 * (w0 - p)) * Real.sqrt 2 := by ring
    have hsecond (p : ℝ) :
        (W q.2 (w0 - w1 - p, w0 + w1 - p)).2 = Real.sqrt 2 * w1 := by
      rw [hu1]
      simp only [W, Fin.isValue, if_false]
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      calc
        -(w0 - w1 - p) + (w0 + w1 - p) = 2 * w1 := by ring
        _ = (Real.sqrt 2 * w1) * Real.sqrt 2 := by
          calc
            2 * w1 = (Real.sqrt 2)^2 * w1 := by
              rw [show (Real.sqrt 2)^2 = 2 by norm_num]
            _ = (Real.sqrt 2 * w1) * Real.sqrt 2 := by ring
    have heq : (fun p : ℝ => scaledBracketBump 2 lam p *
        aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) =
        (fun p : ℝ => scaledBracketBump 2 lam p *
          (scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) * b1)) := by
      funext p
      unfold aux_kernelBracketProduct
      rw [hfirst p, hsecond p]
    rw [heq]
    exact htarget

private theorem scratch_caseTwo_kernel_continuous
    (q : SequencePair × Fin 2) (j : ℤ) (w0 w1 : ℝ) :
    Continuous (fun p : ℝ =>
      aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) := by
  let t0 : ℝ := q.1 0 j
  let t1 : ℝ := q.1 1 j
  by_cases hu : q.2 = 0
  · have hcont : Continuous (fun p : ℝ =>
        scaledBracketBump 2 t0 (w0 - w1 - p) *
          scaledBracketBump 2 t1 (w0 + w1 - p)) := by
      exact ((scratch_caseTwo_continuous_scaledBracketBump 2 t0).comp
        (continuous_const.sub continuous_id)).mul
        ((scratch_caseTwo_continuous_scaledBracketBump 2 t1).comp
          (continuous_const.sub continuous_id))
    convert hcont using 1
    funext p
    simp [aux_kernelBracketProduct, hu, t0, t1, W]
  · have hu1 : q.2 = 1 := Fin.eq_one_of_ne_zero q.2 hu
    have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hfirst (p : ℝ) :
        (W q.2 (w0 - w1 - p, w0 + w1 - p)).1 = Real.sqrt 2 * (w0 - p) := by
      rw [hu1]
      simp only [W, Fin.isValue, if_false]
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      calc
        (w0 - w1 - p) + (w0 + w1 - p) = 2 * (w0 - p) := by ring
        _ = (Real.sqrt 2 * (w0 - p)) * Real.sqrt 2 := by
          calc
            2 * (w0 - p) = (Real.sqrt 2)^2 * (w0 - p) := by
              rw [show (Real.sqrt 2)^2 = 2 by norm_num]
            _ = (Real.sqrt 2 * (w0 - p)) * Real.sqrt 2 := by ring
    have hsecond (p : ℝ) :
        (W q.2 (w0 - w1 - p, w0 + w1 - p)).2 = Real.sqrt 2 * w1 := by
      rw [hu1]
      simp only [W, Fin.isValue, if_false]
      apply (div_eq_iff (ne_of_gt hsqrt)).2
      calc
        -(w0 - w1 - p) + (w0 + w1 - p) = 2 * w1 := by ring
        _ = (Real.sqrt 2 * w1) * Real.sqrt 2 := by
          calc
            2 * w1 = (Real.sqrt 2)^2 * w1 := by
              rw [show (Real.sqrt 2)^2 = 2 by norm_num]
            _ = (Real.sqrt 2 * w1) * Real.sqrt 2 := by ring
    have hcont : Continuous (fun p : ℝ =>
        scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) *
          scaledBracketBump 2 t1 (Real.sqrt 2 * w1)) := by
      exact ((scratch_caseTwo_continuous_scaledBracketBump 2 t0).comp
        (continuous_const.mul (continuous_const.sub continuous_id))).mul continuous_const
    have heq : (fun p : ℝ =>
        aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) =
        (fun p : ℝ => scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) *
          scaledBracketBump 2 t1 (Real.sqrt 2 * w1)) := by
      funext p
      unfold aux_kernelBracketProduct
      rw [hfirst p, hsecond p]
    rw [heq]
    exact hcont

private theorem scratch_caseTwo_primitive_occurrence_integrable
    (q : SequencePair × Fin 2) (j : ℤ) (w0 w1 lam A : ℝ) (R : ℝ → ℝ)
    (hq0 : SpacedSequence (q.1 0)) (hq1 : SpacedSequence (q.1 1))
    (hlam : 0 < lam) (hA : 0 ≤ A) (hRcont : Continuous R)
    (hR : ∀ p : ℝ, |R p| ≤ A * lam * scaledBracketBump 2 lam p) :
    Integrable (fun p : ℝ => |R p| *
      (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p))) := by
  let κ : ℝ := (q.1 0 j)⁻¹ + (q.1 1 j)⁻¹

  let K : ℝ → ℝ := fun p =>
    aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)
  have ht0 : 0 < q.1 0 j := (hq0 j).1
  have ht1 : 0 < q.1 1 j := (hq1 j).1
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    positivity
  have hK (p : ℝ) : 0 ≤ K p := by
    dsimp [K]
    exact aux_kernelBracketProduct_nonneg q (by
      intro r
      fin_cases r
      · exact hq0
      · exact hq1) j _
  have hbase : Integrable (fun p : ℝ => scaledBracketBump 2 lam p * K p) := by
    dsimp [K]
    exact scratch_caseTwo_weighted_kernel_integrable q j w0 w1 lam hq0 hq1 hlam
  have hKcont : Continuous K := by
    dsimp [K]
    exact scratch_caseTwo_kernel_continuous q j w0 w1
  have htargetMeas : AEStronglyMeasurable (fun p : ℝ => |R p| * (κ * K p)) :=
    hRcont.abs.aestronglyMeasurable.mul
      (continuous_const.mul hKcont).aestronglyMeasurable
  have hmajor : Integrable (fun p : ℝ => A * lam * κ *
      (scaledBracketBump 2 lam p * K p)) := by
    convert hbase.const_mul (A * lam * κ) using 1 <;> ring
  refine hmajor.mono' htargetMeas ?_
  filter_upwards [] with p
  have hleft : 0 ≤ |R p| * (κ * K p) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg hκ (hK p))
  have hright : 0 ≤ A * lam * κ * (scaledBracketBump 2 lam p * K p) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hA hlam.le) hκ)
      (mul_nonneg (aux_scaledBracketBump_nonneg 2 hlam p) (hK p))
  rw [Real.norm_eq_abs, abs_of_nonneg hleft]
  calc
    |R p| * (κ * K p) ≤ (A * lam * scaledBracketBump 2 lam p) * (κ * K p) :=
      mul_le_mul_of_nonneg_right (hR p) (mul_nonneg hκ (hK p))
    _ = A * lam * κ * (scaledBracketBump 2 lam p * K p) := by ring

private def scratch_caseTwoSlotTerm (lam : ℤ → ℝ) (q : SequencePair × Fin 2)
    (j : ℤ) (v : RealPlane) (r : Fin 5) : ℝ :=
  aux_kernelBracketProduct (ScratchCase2Witness.caseTwoExactSlotOf lam q r) j v

private theorem scratch_caseTwoSlotTerm_nonneg
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (j : ℤ) (v : RealPlane) (r : Fin 5) :
    0 ≤ scratch_caseTwoSlotTerm lam q j v r := by
  have hs := ScratchCase2Witness.caseTwoExactSlotOf_spaced lam hlam q hq r
  unfold scratch_caseTwoSlotTerm
  exact aux_kernelBracketProduct_nonneg _ hs j v


private theorem scratch_caseTwo_sum_fin5 (f : Fin 5 → ℝ) :
    (∑ r : Fin 5, f r) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ]
  ring

private theorem scratch_caseTwo_u0_output_le_slots
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s))
    (j : ℤ) (v : RealPlane) (hqu : q.2 = 0) :
    scaledBracketBump 2 (q.1 0 j) v.1 *
        scaledBracketBump 2 (max (lam j) (q.1 1 j)) v.2 +
      scaledBracketBump 2 (lam j) v.1 *
        scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 +
      scaledBracketBump 2 (lam j) ((v.1 + v.2) / Real.sqrt 2) *
        scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
          ((v.1 - v.2) / Real.sqrt 2) ≤
      ∑ r : Fin 5, scratch_caseTwoSlotTerm lam q j v r := by
  have h0 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 0
  have h1 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 1
  have h2 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 2
  have h3 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 3
  have h4 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 4
  have hW0 : W (0 : Fin 2) v = v := by simp [W]
  have hW1second : (W (1 : Fin 2) v).2 = -((v.1 - v.2) / Real.sqrt 2) := by
    simp [W]
    ring
  have hW1first : (W (1 : Fin 2) v).1 = (v.1 + v.2) / Real.sqrt 2 := by simp [W]
  have hterms :
      scratch_caseTwoSlotTerm lam q j v 0 =
        scaledBracketBump 2 (q.1 0 j) v.1 *
          scaledBracketBump 2 (max (lam j) (q.1 1 j)) v.2 ∧
      scratch_caseTwoSlotTerm lam q j v 1 =
        scaledBracketBump 2 (lam j) v.1 *
          scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 ∧
      scratch_caseTwoSlotTerm lam q j v 2 =
        scaledBracketBump 2 (lam j) ((v.1 + v.2) / Real.sqrt 2) *
          scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
            ((v.1 - v.2) / Real.sqrt 2) := by
    constructor
    · simp [scratch_caseTwoSlotTerm, ScratchCase2Witness.caseTwoExactSlotOf, hqu,
        ScratchCase2Witness.caseTwoLambdaMaxScale, ScratchCase2Witness.caseTwoMaxScale,
        aux_kernelBracketProduct, aux_sequencePairOf, hW0]
    constructor
    · simp [scratch_caseTwoSlotTerm, ScratchCase2Witness.caseTwoExactSlotOf, hqu,
        ScratchCase2Witness.caseTwoLambdaMaxScale, ScratchCase2Witness.caseTwoMaxScale,
        aux_kernelBracketProduct, aux_sequencePairOf, hW0]
    · simp [scratch_caseTwoSlotTerm, ScratchCase2Witness.caseTwoExactSlotOf, hqu,
        ScratchCase2Witness.caseTwoLambdaMaxScale, ScratchCase2Witness.caseTwoMaxScale,
        aux_kernelBracketProduct, aux_sequencePairOf, hW1first, hW1second,
        aux_caseTwo.scratch_scaledBracketBump_neg]
  rw [scratch_caseTwo_sum_fin5]
  rw [← hterms.1, ← hterms.2.1, ← hterms.2.2]
  nlinarith

private theorem scratch_caseTwo_u1_output_le_slots
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s))
    (j : ℤ) (v : RealPlane) (hqu : q.2 = 1) :
    aux_kernelBracketProduct q j v ≤
      ∑ r : Fin 5, scratch_caseTwoSlotTerm lam q j v r := by
  have h0 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 0
  have h1 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 1
  have h2 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 2
  have h3 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 3
  have h4 := scratch_caseTwoSlotTerm_nonneg lam hlam q hq j v 4
  have hslot0 : scratch_caseTwoSlotTerm lam q j v 0 = aux_kernelBracketProduct q j v := by
    have hq' : (q.1, (1 : Fin 2)) = q := by
      apply Prod.ext
      · rfl
      · exact hqu.symm
    simp [scratch_caseTwoSlotTerm, ScratchCase2Witness.caseTwoExactSlotOf, hqu, hq']
  rw [scratch_caseTwo_sum_fin5, ← hslot0]
  nlinarith

private theorem scratch_caseTwo_u0_bound_to_slots
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s))
    (j : ℤ) (v : RealPlane) (hqu : q.2 = 0)
    (I A r : ℝ) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hmain : I ≤ 9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
      (scaledBracketBump 2 (q.1 0 j) v.1 *
          scaledBracketBump 2 (max (lam j) (q.1 1 j)) v.2 +
        scaledBracketBump 2 (lam j) v.1 *
          scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 +
        scaledBracketBump 2 (lam j) ((v.1 + v.2) / Real.sqrt 2) *
          scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
            ((v.1 - v.2) / Real.sqrt 2))) :
    I ≤ 9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
      ∑ s : Fin 5, scratch_caseTwoSlotTerm lam q j v s := by
  have hslots := scratch_caseTwo_u0_output_le_slots lam hlam q hq j v hqu
  have htri : 0 ≤ C_bumpTriangle 1 1 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  have hcoef : 0 ≤ 9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hr) htri) htwo
  exact hmain.trans (mul_le_mul_of_nonneg_left hslots hcoef)

private theorem scratch_caseTwo_u1_bound_to_slots

    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s))
    (j : ℤ) (v : RealPlane) (hqu : q.2 = 1)
    (I K : ℝ) (hK : 0 ≤ K)
    (hmain : I ≤ K * aux_kernelBracketProduct q j v) :
    I ≤ K * ∑ s : Fin 5, scratch_caseTwoSlotTerm lam q j v s := by
  have hslots := scratch_caseTwo_u1_output_le_slots lam hlam q hq j v hqu
  exact hmain.trans (mul_le_mul_of_nonneg_left hslots hK)

private theorem scratch_caseTwo_occurrence_raw_to_slots {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hnegative : ι.1.1 < 0)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (w0 w1 : ℝ) :
    (∫ p : ℝ, |scratch_caseTwoPrimitive γ hkn ι i j p| *
      (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p))) ≤
      9 * ((3 / 2 : ℝ) * C_standardBumpPropertiesTilde 0 3 *
        C_fourScaleGaussianKernel 3) * (2 : ℝ) ^ (ι.1.1 + 1) *
        C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
        ∑ r : Fin 5, scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i) q j
          (w0 - w1, w0 + w1) r := by
  let lamSeq : ℤ → ℝ := scratch_caseTwoLambda γ ι i
  let lam : ℝ := lamSeq j
  let A : ℝ := (3 / 2 : ℝ) * C_standardBumpPropertiesTilde 0 3 *
    C_fourScaleGaussianKernel 3
  let r : ℝ := (2 : ℝ) ^ (ι.1.1 + 1)
  let R : ℝ → ℝ := scratch_caseTwoPrimitive γ hkn ι i j
  let v : RealPlane := (w0 - w1, w0 + w1)
  rcases hP.1 q hqmem with ⟨hqball0, hqball1⟩
  have hq : ∀ s : Fin 2, SpacedSequence (q.1 s) := by
    intro s
    fin_cases s
    · exact hqball0.1
    · exact hqball1.1
  have hlamSeq : SpacedSequence lamSeq := by
    simpa [lamSeq] using scratch_caseTwoLambda_spaced γ ι i
  have hlam : 0 < lam := by
    dsimp [lam, lamSeq, scratch_caseTwoLambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hA : 0 ≤ A := by
    dsimp [A]
    have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 3 := by
      rw [show C_standardBumpPropertiesTilde 0 3 = (2 : ℝ) ^ (33 : ℕ) by
        norm_num [C_standardBumpPropertiesTilde]]
      positivity
    have hfour : 0 ≤ C_fourScaleGaussianKernel 3 := by
      have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) :=
        (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)

      have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) :=
        (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
      unfold C_fourScaleGaussianKernel C_smoothDecay2
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
        (mul_nonneg (by positivity) hsecond)
    positivity
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hratio : lam * ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) ≤ r := by
    simpa [lam, lamSeq, r] using
      scratch_caseTwo_ratio_of_package γ ι i j hnegative P hP q hqmem
  have hR (p : ℝ) : |R p| ≤ A * lam * scaledBracketBump 2 lam p := by
    simpa [R, A, lam, lamSeq] using
      scratch_caseTwoPrimitive_bound γ hkn ι i j hnegative p
  have hint : Integrable (fun p : ℝ => scaledBracketBump 2 lam p *
      aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p)) :=
    scratch_caseTwo_weighted_kernel_integrable q j w0 w1 lam (hq 0) (hq 1) hlam
  have hintκ : Integrable (fun p : ℝ => scaledBracketBump 2 lam p *
      (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p))) := by
    convert hint.const_mul ((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) using 1
    funext p
    ring
  by_cases hqu : q.2 = 0
  · have hscalar := ScratchCase2Fourier.scratch_caseTwo_u0_occurrence
      v.1 v.2 lam (q.1 0 j) (q.1 1 j) hlam ((hq 0 j).1) ((hq 1 j).1)
    have hraw := scratch_caseTwo_u0_primitive_kernelBracket q j v lam A r R hqu
      (hq 0) (hq 1) hlam hA hr hratio hR (by
        simpa [v, mul_assoc] using hintκ) (by simpa [v] using hscalar)
    have hslots := scratch_caseTwo_u0_bound_to_slots lamSeq hlamSeq q hq j v hqu
      _ A r hA hr (by simpa [lam, lamSeq, R, v] using hraw)
    simpa [lamSeq, A, r, v] using hslots
  · have hqu1 : q.2 = 1 := Fin.eq_one_of_ne_zero q.2 hqu
    have hscale : Real.sqrt 2 * lam ≤ q.1 0 j := by
      dsimp [lam, lamSeq, scratch_caseTwoLambda]
      exact scratch_negative_distanceBall_sqrt_scale_le (γ.scales_spaced i 1) hqball0
        ι.1.1 hnegative j
    have hraw := scratch_caseTwo_u1_primitive_occurrence q j w0 w1 lam A r R hqu1
      (hq 0) (hq 1) hlam hA hr hscale hratio hR hint
    have hK : 0 ≤ 4 * A * r * C_twoBumpEstimate 2 2 := by
      have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by norm_num [C_twoBumpEstimate]
      positivity
    have hslots := scratch_caseTwo_u1_bound_to_slots lamSeq hlamSeq q hq j v hqu1
      _ (4 * A * r * C_twoBumpEstimate 2 2) hK (by simpa [v, R, mul_assoc] using hraw)
    have hsum : 0 ≤ ∑ s : Fin 5, scratch_caseTwoSlotTerm lamSeq q j v s := by
      apply Finset.sum_nonneg
      intro s _
      exact scratch_caseTwoSlotTerm_nonneg lamSeq hlamSeq q hq j v s
    have htri : C_bumpTriangle 1 1 2 2 = 4 := by
      norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
    have hcoef : 4 * A * r * C_twoBumpEstimate 2 2 ≤
        9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
      rw [htri]
      nlinarith [mul_nonneg hA hr,
        (show 0 ≤ C_twoBumpEstimate 2 2 by norm_num [C_twoBumpEstimate])]
    calc
      (∫ p : ℝ, |scratch_caseTwoPrimitive γ hkn ι i j p| *
          (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
            aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p))) ≤
          (4 * A * r * C_twoBumpEstimate 2 2) *
            ∑ s : Fin 5, scratch_caseTwoSlotTerm lamSeq q j v s := by
        simpa [R, v, mul_assoc] using hslots
      _ ≤ (9 * A * r * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
            ∑ s : Fin 5, scratch_caseTwoSlotTerm lamSeq q j v s :=
        mul_le_mul_of_nonneg_right hcoef hsum
      _ = _ := by rfl

private theorem scratch_caseTwo_occurrence_to_slots {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hnegative : ι.1.1 < 0)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (w0 w1 : ℝ) :
    (∫ p : ℝ, |scratch_caseTwoPrimitive γ hkn ι i j p| *
      (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p))) ≤
      (27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
        C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
        Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
        ∑ r : Fin 5, scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i) q j
          (w0 - w1, w0 + w1) r := by
  let S : ℝ := ∑ r : Fin 5,
    scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i) q j (w0 - w1, w0 + w1) r
  have hraw := scratch_caseTwo_occurrence_raw_to_slots γ hkn ι i j hnegative
    P hP q hqmem w0 w1
  have hseq : SpacedSequence (scratch_caseTwoLambda γ ι i) :=
    scratch_caseTwoLambda_spaced γ ι i
  rcases hP.1 q hqmem with ⟨hq0, hq1⟩
  have hq : ∀ s : Fin 2, SpacedSequence (q.1 s) := by
    intro s
    fin_cases s
    · exact hq0.1
    · exact hq1.1
  have hS : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro r _
    exact scratch_caseTwoSlotTerm_nonneg (scratch_caseTwoLambda γ ι i) hseq q hq j
      (w0 - w1, w0 + w1) r
  have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 3 := by

    rw [show C_standardBumpPropertiesTilde 0 3 = (2 : ℝ) ^ (33 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity
  have hfour : 0 ≤ C_fourScaleGaussianKernel 3 := by
    have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
    have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) :=
      (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
    unfold C_fourScaleGaussianKernel C_smoothDecay2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
      (mul_nonneg (by positivity) hsecond)
  have htri : 0 ≤ C_bumpTriangle 1 1 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  have hK : 0 ≤ C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
      C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by positivity
  have hloss := scratch_caseTwo_negative_loss γ ι hnegative
  have hcoef :
      9 * ((3 / 2 : ℝ) * C_standardBumpPropertiesTilde 0 3 *
        C_fourScaleGaussianKernel 3) * (2 : ℝ) ^ (ι.1.1 + 1) *
        C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 ≤
      (27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
        C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
        Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) := by
    calc
      9 * ((3 / 2 : ℝ) * C_standardBumpPropertiesTilde 0 3 *
          C_fourScaleGaussianKernel 3) * (2 : ℝ) ^ (ι.1.1 + 1) *
          C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 =
          (9 * (3 / 2 : ℝ) *
            (C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
              C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2)) *
            (2 : ℝ) ^ (ι.1.1 + 1) := by ring
      _ ≤ (9 * (3 / 2 : ℝ) *
            (C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
              C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2)) *
            (2 * Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hloss (by positivity)
      _ = _ := by ring
  calc
    (∫ p : ℝ, |scratch_caseTwoPrimitive γ hkn ι i j p| *
        (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
          aux_kernelBracketProduct q j (w0 - w1 - p, w0 + w1 - p))) ≤
        (9 * ((3 / 2 : ℝ) * C_standardBumpPropertiesTilde 0 3 *
          C_fourScaleGaussianKernel 3) * (2 : ℝ) ^ (ι.1.1 + 1) *
          C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) * S := by
      simpa [S] using hraw

    _ ≤ ((27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
          C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)) * S :=
      mul_le_mul_of_nonneg_right hcoef hS
    _ = _ := by rfl

private theorem scratch_caseTwo_HPackage_explicit {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) :
    aux_HKernelDerivativeGaussianBound γ i (aux_hKernelGaussianMultiset γ i) := by
  by_cases h : γ.orientation i = 0
  · apply aux_hKernelDerivativeGaussianBound_orientation_zero_of_sBounds γ i h
    · intro j x
      apply aux_sMultiplier_bound_orientation_zero_of_diagonal γ i j h
      intro y
      rw [aux_sMultiplier_eq_diagonalSquareRoot]
      have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
      apply diagonalSquareRoot_bound 2 (by norm_num)
      · linarith [hsp.1]
      · convert hsp.2 using 1 <;> ring
    · intro j x
      apply aux_deriv_sMultiplier_bound_orientation_zero_of_diagonal γ i j h
      intro y
      rw [aux_deriv_sMultiplier_eq_diagonalSquareRoot]
      have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
      apply derivativeDiagonalSquareRoot_bound 2 (by norm_num)
      · linarith [hsp.1]
      · convert hsp.2 using 1 <;> ring
  · apply aux_hKernelDerivativeGaussianBound_orientation_one_of_sBounds γ i h
    · intro j x
      apply aux_sMultiplier_bound_orientation_one_of_diagonal γ i j h
      intro y
      rw [aux_sMultiplier_eq_diagonalSquareRoot]
      have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
      apply diagonalSquareRoot_bound 2 (by norm_num)
      · linarith [hsp.1]
      · convert hsp.2 using 1 <;> ring
    · intro j x
      apply aux_deriv_sMultiplier_bound_orientation_one_of_diagonal γ i j h
      intro y
      rw [aux_deriv_sMultiplier_eq_diagonalSquareRoot]
      have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
      apply derivativeDiagonalSquareRoot_bound 2 (by norm_num)
      · linarith [hsp.1]
      · convert hsp.2 using 1 <;> ring

private theorem scratch_caseTwo_translate_negDiagonal_differentiable {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (v : RealPlane) (p : ℝ) :
    DifferentiableAt ℝ (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) p := by
  let z : RealPlane := (v.1 - p, v.2 - p)
  let D : ℝ → ℝ := fun t => hMultiplier γ i j (z.1 + t, z.2 + t)
  have hD : DifferentiableAt ℝ D 0 := by
    dsimp [D, z]
    exact ScratchCase2Fourier.hMultiplier_diagonal_differentiable γ i j
      (v.1 - p, v.2 - p)
  have hu : DifferentiableAt ℝ (fun q : ℝ => p - q) p :=
    (differentiableAt_const (c := p)).sub differentiableAt_id
  have hD0 : DifferentiableAt ℝ D (p - p) := by simpa using hD
  have hcomp := hD0.comp p hu
  have heq : (fun q : ℝ => hMultiplier γ i j (v.1 - q, v.2 - q)) =ᶠ[nhds p]
      (fun q : ℝ => D (p - q)) := by
    filter_upwards [] with q
    dsimp [D, z]
    congr 1 <;> ring
  exact hcomp.congr_of_eventuallyEq heq

private theorem scratch_caseTwo_primitive_occurrence_integrable_at {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hnegative : ι.1.1 < 0)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (v : RealPlane) :
    Integrable (fun p : ℝ => |scratch_caseTwoPrimitive γ hkn ι i j p| *
      (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) := by
  let lam : ℝ := scratch_caseTwoLambda γ ι i j
  let A : ℝ := (3 / 2 : ℝ) * C_standardBumpPropertiesTilde 0 3 *
    C_fourScaleGaussianKernel 3
  let R : ℝ → ℝ := scratch_caseTwoPrimitive γ hkn ι i j
  let w0 : ℝ := (v.1 + v.2) / 2
  let w1 : ℝ := (v.2 - v.1) / 2
  rcases hP.1 q hqmem with ⟨hq0, hq1⟩
  have hlam : 0 < lam := by
    dsimp [lam, scratch_caseTwoLambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hA : 0 ≤ A := by
    dsimp [A]
    have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 3 := by
      rw [show C_standardBumpPropertiesTilde 0 3 = (2 : ℝ) ^ (33 : ℕ) by
        norm_num [C_standardBumpPropertiesTilde]]
      positivity
    have hfour : 0 ≤ C_fourScaleGaussianKernel 3 := by
      have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) :=
        (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
      have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) :=
        (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
      unfold C_fourScaleGaussianKernel C_smoothDecay2
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
        (mul_nonneg (by positivity) hsecond)
    positivity
  have hRcont : Continuous R := by
    simpa [R] using scratch_caseTwoPrimitive_continuous γ hkn ι i j
  have hR (p : ℝ) : |R p| ≤ A * lam * scaledBracketBump 2 lam p := by

    simpa [R, A, lam] using scratch_caseTwoPrimitive_bound γ hkn ι i j hnegative p
  have hv : (w0 - w1, w0 + w1) = v := by
    ext <;> dsimp [w0, w1] <;> ring
  have hint := scratch_caseTwo_primitive_occurrence_integrable q j w0 w1 lam A R
    hq0.1 hq1.1 hlam hA hRcont hR
  have hv0 : w0 - w1 = v.1 := congrArg Prod.fst hv
  have hv1 : w0 + w1 = v.2 := congrArg Prod.snd hv
  simpa [R, hv0, hv1] using hint

private theorem scratch_caseTwo_representation {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane) (hnegative : ι.1.1 < 0)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P) :
    nMultiplier γ hkn ι i j v = ∫ p : ℝ,
      scratch_caseTwoPrimitive γ hkn ι i j p *
        aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p) := by
  let rho : ℝ → ℝ := nMultiplierRho γ hkn ι i j
  let R : ℝ → ℝ := scratch_caseTwoPrimitive γ hkn ι i j
  let g : ℝ → ℝ := fun p => hMultiplier γ i j (v.1 - p, v.2 - p)
  let lam : ℝ := scratch_caseTwoLambda γ ι i j
  let A : ℝ := 3 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3
  have hlam : 0 < lam := by
    dsimp [lam, scratch_caseTwoLambda]
    exact mul_pos (zpow_pos (by norm_num) _) ((γ.scales_spaced i 1) _).1
  have hA : 0 ≤ A := by
    dsimp [A]
    have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 3 := by
      rw [show C_standardBumpPropertiesTilde 0 3 = (2 : ℝ) ^ (33 : ℕ) by
        norm_num [C_standardBumpPropertiesTilde]]
      positivity
    have hfour : 0 ≤ C_fourScaleGaussianKernel 3 := by
      have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) :=
        (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
      have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) :=
        (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
      unfold C_fourScaleGaussianKernel C_smoothDecay2
      exact add_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
        (mul_nonneg (by positivity) hsecond)
    positivity
  have hrhoCont : Continuous rho := by
    simpa [rho] using (nMultiplierRho_memW0 γ hkn ι i j).1
  have hrhoInt : Integrable rho := by
    simpa [rho] using Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (nMultiplierRho_memW0 γ hkn ι i j)
  have hg : ∀ p : ℝ, DifferentiableAt ℝ g p := by
    intro p

    simpa [g] using scratch_caseTwo_translate_negDiagonal_differentiable γ i j v p
  have hgint : Integrable g := by
    simpa [g] using aux_hMultiplier_diagonal_translate_integrable γ i j v
  have hrhoDecay (p : ℝ) : |rho p| ≤ A * scaledBracketBump 3 lam p := by
    have hzero : ι.1.1 ≠ 0 := ne_of_lt hnegative
    simpa [rho, A, lam, scratch_caseTwoLambda, mul_assoc] using
      scratch_nMultiplierRho_negative_decay_bound_collapsed γ hkn ι i j hzero hnegative p
  have hrhoBound (p : ℝ) : |rho p| ≤ A * lam⁻¹ := by
    calc
      |rho p| ≤ A * scaledBracketBump 3 lam p := hrhoDecay p
      _ ≤ A * lam⁻¹ :=
        mul_le_mul_of_nonneg_left (scratch_caseTwo_scaledBracketBump_le_inv 3 lam p hlam) hA
  have hRBound (p : ℝ) : |∫ q : ℝ in Set.Iic p, rho q| ≤ A / 2 := by
    have hraw : |∫ q : ℝ in Set.Iic p, rho q| ≤
        (A / 2) * lam * scaledBracketBump 2 lam p := by
      have hzero : ι.1.1 ≠ 0 := ne_of_lt hnegative
      have htail := scratch_primitive_Iic_bound A lam hA hlam hrhoInt
        (scratch_nMultiplierRho_negative_integral_zero γ hkn ι i j hzero hnegative)
        hrhoDecay p
      exact htail
    have hhalf : 0 ≤ A / 2 := by positivity
    calc
      |∫ q : ℝ in Set.Iic p, rho q| ≤
          (A / 2) * lam * scaledBracketBump 2 lam p := hraw
      _ = (A / 2) * (lam * scaledBracketBump 2 lam p) := by ring
      _ ≤ (A / 2) * 1 :=
        mul_le_mul_of_nonneg_left
          (scratch_scale_mul_scaledBracketBump_le_one 2 lam p hlam) hhalf
      _ = A / 2 := by ring
  have hfderiv : ∀ p : ℝ,
      fderiv ℝ g p 1 =
        -aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p) := by
    intro p
    simpa [g] using ScratchCase2Fourier.hMultiplier_fderiv_translate_negDiagonal γ i j v p
  have hint : ∀ q ∈ P, Integrable (fun p : ℝ => |R p| *
      (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) := by
    intro q hq
    simpa [R] using scratch_caseTwo_primitive_occurrence_integrable_at γ hkn ι i j
      hnegative P hP q hq v
  have hprimitiveDeriv : Integrable (fun p : ℝ => R p * fderiv ℝ g p 1) := by
    simpa [R, g] using scratch_caseTwo_primitive_fderiv_integrable γ i j v P hP R
      (by simpa [R] using scratch_caseTwoPrimitive_continuous γ hkn ι i j) hfderiv hint
  have hparts := ScratchCase2Fourier.iic_primitive_integration_by_parts_of_bounds rho g
    hrhoCont hrhoInt hg hgint (A * lam⁻¹) (A / 2) hrhoBound hRBound hprimitiveDeriv
  apply scratch_caseTwo_representation_from_parts γ hkn ι i j v rho R hparts hfderiv
  rfl

private theorem scratch_caseTwo_occurrence_to_slots_at {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hnegative : ι.1.1 < 0)
    (P : Multiset (SequencePair × Fin 2)) (hP : aux_HKernelDerivativeGaussianBound γ i P)
    (q : SequencePair × Fin 2) (hqmem : q ∈ P) (v : RealPlane) :
    (∫ p : ℝ, |scratch_caseTwoPrimitive γ hkn ι i j p| *
      (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) ≤
      (27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
        C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
        Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
        ∑ r : Fin 5, scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i) q j v r := by
  let w0 : ℝ := (v.1 + v.2) / 2
  let w1 : ℝ := (v.2 - v.1) / 2
  have hv : (w0 - w1, w0 + w1) = v := by
    ext <;> dsimp [w0, w1] <;> ring
  have hv0 : w0 - w1 = v.1 := congrArg Prod.fst hv
  have hv1 : w0 + w1 = v.2 := congrArg Prod.snd hv
  have hraw := scratch_caseTwo_occurrence_to_slots γ hkn ι i j hnegative P hP q hqmem w0 w1
  simpa [hv0, hv1] using hraw

private theorem scratch_caseTwo_multiset_sum_eq_occurrence_sum
    {R : Type*} [AddCommMonoid R] (P : Multiset (SequencePair × Fin 2))
    (F : SequencePair × Fin 2 → R) :
    (P.map F).sum = ∑ k : Fin P.card, F (ScratchCase2Witness.caseTwoOccurrence P k) := by
  rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem]
  let e : Fin P.card ≃ Fin P.toList.length :=
    finCongr (Multiset.length_toList P).symm
  symm
  refine Fintype.sum_equiv e
    (fun k => F (ScratchCase2Witness.caseTwoOccurrence P k))
    (fun l => F (P.toList.get l)) ?_
  intro k
  simp [e, ScratchCase2Witness.caseTwoOccurrence]

private theorem scratch_caseTwo_multiset_slot_sum_reindex {n : ℕ}
    (γ : GeometricParameters n) (ι : MultiplierIndex γ) (i : Fin γ.k)
    (j : ℤ) (v : RealPlane) :
    ((aux_hKernelGaussianMultiset γ i).map
      (fun q => ∑ r : Fin 5, scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i) q j v r)).sum =
      ∑ b ∈ ScratchCase2Witness.caseTwoB,
        aux_kernelBracketProduct
          (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v := by
  classical
  rw [scratch_caseTwo_multiset_sum_eq_occurrence_sum]
  have hsum :
      (∑ k : Fin 6, ∑ r : Fin 5,
        scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i)
          (ScratchCase2Witness.caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) j v r) =
      ∑ k : Fin (aux_hKernelGaussianMultiset γ i).card, ∑ r : Fin 5,
        scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i)
          (ScratchCase2Witness.caseTwoOccurrence (aux_hKernelGaussianMultiset γ i) k) j v r := by
    let e : Fin 6 ≃ Fin (aux_hKernelGaussianMultiset γ i).card :=
      finCongr (aux_hKernelGaussianMultiset_card γ i).symm

    refine Fintype.sum_equiv e
      (fun k => ∑ r : Fin 5,
        scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i)
          (ScratchCase2Witness.caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) j v r)
      (fun k => ∑ r : Fin 5,
        scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i)
          (ScratchCase2Witness.caseTwoOccurrence (aux_hKernelGaussianMultiset γ i) k) j v r) ?_
    intro k
    simp [e]
  rw [← hsum]
  rw [ScratchCase2Witness.caseTwo_sum_range30_reindex γ i
    (scratch_caseTwoLambda γ ι i) (fun s => aux_kernelBracketProduct s j v)]
  simp only [scratch_caseTwoSlotTerm]

private theorem scratch_caseTwo_preGaussian_bound {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane) (hnegative : ι.1.1 < 0) :
    |nMultiplier γ hkn ι i j v| ≤
      C_hKernelDerivativeEstimateGaussianDomination *
        ((27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
          C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)) *
        ∑ b ∈ ScratchCase2Witness.caseTwoB,
          aux_kernelBracketProduct
            (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v := by
  classical
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let D : ℝ :=
    (27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
      C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)
  let S : (SequencePair × Fin 2) → ℝ := fun q =>
    ∑ r : Fin 5, scratch_caseTwoSlotTerm (scratch_caseTwoLambda γ ι i) q j v r
  have hP : aux_HKernelDerivativeGaussianBound γ i P := by
    dsimp [P]
    exact scratch_caseTwo_HPackage_explicit γ i
  have hrep : nMultiplier γ hkn ι i j v = ∫ p : ℝ,
      scratch_caseTwoPrimitive γ hkn ι i j p *
        aux_diagonalDerivative (hMultiplier γ i j) (v.1 - p, v.2 - p) := by
    exact scratch_caseTwo_representation γ hkn ι i j v hnegative P hP
  have hint : ∀ q ∈ P, Integrable (fun p : ℝ =>
      |scratch_caseTwoPrimitive γ hkn ι i j p| *
        (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) := by
    intro q hq

    exact scratch_caseTwo_primitive_occurrence_integrable_at γ hkn ι i j hnegative P hP q hq v
  have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 3 := by
    rw [show C_standardBumpPropertiesTilde 0 3 = (2 : ℝ) ^ (33 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity
  have hfour : 0 ≤ C_fourScaleGaussianKernel 3 := by
    have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
    have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) :=
      (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
    unfold C_fourScaleGaussianKernel C_smoothDecay2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
      (mul_nonneg (by positivity) hsecond)
  have htri : 0 ≤ C_bumpTriangle 1 1 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hocc : ∀ q ∈ P,
      (∫ p : ℝ, |scratch_caseTwoPrimitive γ hkn ι i j p| *
        (((q.1 0 j)⁻¹ + (q.1 1 j)⁻¹) *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p))) ≤ D * S q := by
    intro q hq
    simpa [D, S] using scratch_caseTwo_occurrence_to_slots_at γ hkn ι i j
      hnegative P hP q hq v
  have houter := scratch_caseTwo_outer_scaled_from_occurrences γ hkn ι i j v P hP
    (scratch_caseTwoPrimitive γ hkn ι i j) D S hrep hint hD hocc
  have hreindex : (P.map S).sum = ∑ b ∈ ScratchCase2Witness.caseTwoB,
      aux_kernelBracketProduct
        (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v := by
    dsimp [P, S]
    exact scratch_caseTwo_multiset_slot_sum_reindex γ ι i j v
  calc
    |nMultiplier γ hkn ι i j v| ≤
        C_hKernelDerivativeEstimateGaussianDomination * D * (P.map S).sum := houter
    _ = C_hKernelDerivativeEstimateGaussianDomination * D *
        ∑ b ∈ ScratchCase2Witness.caseTwoB,
          aux_kernelBracketProduct
            (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v := by
      rw [hreindex]
    _ = _ := by rfl

private theorem scratch_caseTwo_slot_gaussian_majorant
    (p : SequencePair) (hp : ∀ r : Fin 2, SpacedSequence (p r))
    (u : Fin 2) (j : ℤ) (v : RealPlane) :
    aux_kernelBracketProduct (p, u) j v ≤
      8 * Real.exp (2 * Real.pi) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          aux_dominatingGaussianTerm
            (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
  let f0 : ℕ → ℝ := fun a =>
    Real.rpow 2 (-((a : ℝ) / 2)) *
      gaussianRescale ((2 : ℝ) ^ a * p 0 j) (W u v).1
  let f1 : ℕ → ℝ := fun a =>
    Real.rpow 2 (-((a : ℝ) / 2)) *
      gaussianRescale ((2 : ℝ) ^ a * p 1 j) (W u v).2
  have hp0 : 0 < p 0 j := aux_spacedSequence_pos (hp 0) j
  have hp1 : 0 < p 1 j := aux_spacedSequence_pos (hp 1) j
  have hhalf (a : ℕ) : (1 - (3 / 2 : ℝ)) * (a : ℝ) = -((a : ℝ) / 2) := by
    ring
  have hbr0 := gaussianDomination (3 / 2 : ℝ) (p 0 j) (W u v).1
    (by norm_num) hp0
  have hbr1 := gaussianDomination (3 / 2 : ℝ) (p 1 j) (W u v).2
    (by norm_num) hp1
  have hbr0' : scaledBracketBumpReal (3 / 2 : ℝ) (p 0 j) (W u v).1 ≤
      C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f0 a := by
    simpa [f0, hhalf] using hbr0
  have hbr1' : scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 ≤
      C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f1 a := by
    simpa [f1, hhalf] using hbr1
  have hf0 : Summable f0 := by
    simpa [f0, hhalf] using
      aux_gaussianDomination_weight_summable (3 / 2 : ℝ) (p 0 j) (W u v).1
        (by norm_num) hp0
  have hf1 : Summable f1 := by
    simpa [f1, hhalf] using
      aux_gaussianDomination_weight_summable (3 / 2 : ℝ) (p 1 j) (W u v).2
        (by norm_num) hp1
  have hf0nonneg (a : ℕ) : 0 ≤ f0 a := by
    dsimp [f0]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hp0) _)
  have hf1nonneg (a : ℕ) : 0 ≤ f1 a := by
    dsimp [f1]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hp1) _)
  have hprod : Summable (fun m : Fin 2 → ℕ => f0 (m 0) * f1 (m 1)) :=
    aux_summable_finTwo_product hf0nonneg hf1nonneg hf0 hf1
  have hprodPair : Summable (fun z : ℕ × ℕ => f0 z.1 * f1 z.2) := by
    refine (aux_finTwoNatEquivProd.symm.summable_iff
      (f := fun m : Fin 2 → ℕ => f0 (m 0) * f1 (m 1))).mpr ?_
    exact hprod
  have hprodEq : (∑' a : ℕ, f0 a) * (∑' a : ℕ, f1 a) =
      ∑' m : Fin 2 → ℕ, f0 (m 0) * f1 (m 1) := by
    calc
      (∑' a : ℕ, f0 a) * (∑' a : ℕ, f1 a) =
          ∑' z : ℕ × ℕ, f0 z.1 * f1 z.2 := hf0.tsum_mul_tsum hf1 hprodPair
      _ = ∑' m : Fin 2 → ℕ, f0 (m 0) * f1 (m 1) := by
        simpa [aux_finTwoNatEquivProd] using
          (aux_finTwoNatEquivProd.symm.tsum_eq
            (fun m : Fin 2 → ℕ => f0 (m 0) * f1 (m 1)))

  have hterm (m : Fin 2 → ℕ) : f0 (m 0) * f1 (m 1) =
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
    have hweight : aux_gaussianDominationWeight m =
        Real.rpow 2 (-((m 0 : ℕ) : ℝ) / 2) *
          Real.rpow 2 (-((m 1 : ℕ) : ℝ) / 2) := by
      unfold aux_gaussianDominationWeight aux_natPairWeight
      calc
        Real.rpow 2 (-((m 0 + m 1 : ℕ) : ℝ) / 2) =
            Real.rpow 2 (-((m 0 : ℕ) : ℝ) / 2 +
              -((m 1 : ℕ) : ℝ) / 2) := by
          congr 1
          push_cast
          ring
        _ = _ := Real.rpow_add (by norm_num) _ _
    rw [hweight]
    simp only [aux_dominatingGaussianTerm, twoDimensionalGaussian]
    dsimp [f0, f1]
    ring
  have hseriesEq : (∑' a : ℕ, f0 a) * (∑' a : ℕ, f1 a) =
      ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
    rw [hprodEq]
    exact tsum_congr hterm
  have hcoeffnonneg : 0 ≤ C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) := by
    rw [C_gaussianDomination]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by norm_num) _)
  have hsum0 : 0 ≤ ∑' a : ℕ, f0 a := tsum_nonneg hf0nonneg
  have hpow : Real.rpow 2 (3 / 2 : ℝ) * Real.rpow 2 (3 / 2 : ℝ) = 8 := by
    change (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) = 8
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hexp : Real.exp Real.pi * Real.exp Real.pi = Real.exp (2 * Real.pi) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcoeff :
      (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) =
      8 * Real.exp (2 * Real.pi) := by
    rw [C_gaussianDomination]
    calc
      (Real.exp Real.pi * Real.rpow 2 (3 / 2 : ℝ)) *

          (Real.exp Real.pi * Real.rpow 2 (3 / 2 : ℝ)) =
          (Real.exp Real.pi * Real.exp Real.pi) *
            (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow 2 (3 / 2 : ℝ)) := by ring
      _ = _ := by rw [hexp, hpow]; ring
  calc
    aux_kernelBracketProduct (p, u) j v =
        scaledBracketBumpReal (2 : ℝ) (p 0 j) (W u v).1 *
          scaledBracketBumpReal (2 : ℝ) (p 1 j) (W u v).2 := by
      simp [aux_kernelBracketProduct,
        aux_caseTwo.scratch_scaledBracketBump_nat_eq_real]
    _ ≤ scaledBracketBumpReal (3 / 2 : ℝ) (p 0 j) (W u v).1 *
        scaledBracketBumpReal (2 : ℝ) (p 1 j) (W u v).2 :=
      mul_le_mul_of_nonneg_right
        (aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 (p 0 j) (W u v).1 hp0
          (by norm_num))
        (aux_scaledBracketBumpReal_nonneg _ _ _ hp1)
    _ ≤ scaledBracketBumpReal (3 / 2 : ℝ) (p 0 j) (W u v).1 *
        scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 :=
      mul_le_mul_of_nonneg_left
        (aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 (p 1 j) (W u v).2 hp1
          (by norm_num))
        (aux_scaledBracketBumpReal_nonneg _ _ _ hp0)
    _ ≤ (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f0 a) *
        scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 :=
      mul_le_mul_of_nonneg_right hbr0'
        (aux_scaledBracketBumpReal_nonneg _ _ _ hp1)
    _ ≤ (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f0 a) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f1 a) :=
      mul_le_mul_of_nonneg_left hbr1' (mul_nonneg hcoeffnonneg hsum0)
    _ = ((C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ))) *
          ((∑' a : ℕ, f0 a) * ∑' a : ℕ, f1 a) := by ring
    _ = (8 * Real.exp (2 * Real.pi)) *
          ((∑' a : ℕ, f0 a) * ∑' a : ℕ, f1 a) := by rw [hcoeff]
    _ = _ := by rw [hseriesEq]

private theorem scratch_caseTwo_slot_sum_gaussian_majorant {n : ℕ}
    (γ : GeometricParameters n) (ι : MultiplierIndex γ) (i : Fin γ.k)
    (j : ℤ) (v : RealPlane) :
    ∑ b ∈ ScratchCase2Witness.caseTwoB,
      aux_kernelBracketProduct
        (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v ≤
      8 * Real.exp (2 * Real.pi) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          ∑ b ∈ ScratchCase2Witness.caseTwoB,
            aux_dominatingGaussianTerm
              (ScratchCase2Witness.caseTwoScales γ i (scratch_caseTwoLambda γ ι i) b m)
              (ScratchCase2Witness.caseTwoOrientation γ i (scratch_caseTwoLambda γ ι i) b) j v := by
  classical
  let T : ℕ → (Fin 2 → ℕ) → ℝ := fun b m =>
    aux_gaussianDominationWeight m *
      aux_dominatingGaussianTerm
        (ScratchCase2Witness.caseTwoScales γ i (scratch_caseTwoLambda γ ι i) b m)
        (ScratchCase2Witness.caseTwoOrientation γ i (scratch_caseTwoLambda γ ι i) b) j v
  have hslot (b : ℕ) (hb : b ∈ ScratchCase2Witness.caseTwoB) :
      aux_kernelBracketProduct
        (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v ≤
        (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ, T b m := by
    have hbase := scratch_caseTwo_slot_gaussian_majorant
      (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b).1
      (ScratchCase2Witness.caseTwoSlotNat_spaced γ i (scratch_caseTwoLambda γ ι i)
        (scratch_caseTwoLambda_spaced γ ι i) b)
      (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b).2 j v
    change aux_kernelBracketProduct
        (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v ≤
      (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ,
        aux_gaussianDominationWeight m *
          aux_dominatingGaussianTerm
            (ScratchCase2Witness.caseTwoScales γ i (scratch_caseTwoLambda γ ι i) b m)
            (ScratchCase2Witness.caseTwoOrientation γ i (scratch_caseTwoLambda γ ι i) b) j v
    unfold ScratchCase2Witness.caseTwoScales ScratchCase2Witness.caseTwoOrientation
    exact hbase
  have hsum (b : ℕ) (hb : b ∈ ScratchCase2Witness.caseTwoB) : Summable (T b) := by
    have hbase := aux_dyadic_gaussian_pair_summable
      (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b).1
      (ScratchCase2Witness.caseTwoSlotNat_spaced γ i (scratch_caseTwoLambda γ ι i)
        (scratch_caseTwoLambda_spaced γ ι i) b)
      (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b).2 j v
    change Summable (fun m : Fin 2 → ℕ =>
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (ScratchCase2Witness.caseTwoScales γ i (scratch_caseTwoLambda γ ι i) b m)
          (ScratchCase2Witness.caseTwoOrientation γ i (scratch_caseTwoLambda γ ι i) b) j v)
    unfold ScratchCase2Witness.caseTwoScales ScratchCase2Witness.caseTwoOrientation
    exact hbase
  calc
    ∑ b ∈ ScratchCase2Witness.caseTwoB,
        aux_kernelBracketProduct
          (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v ≤
        ∑ b ∈ ScratchCase2Witness.caseTwoB,
          (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ, T b m :=
      Finset.sum_le_sum fun b hb => hslot b hb
    _ = (8 * Real.exp (2 * Real.pi)) *
        ∑ b ∈ ScratchCase2Witness.caseTwoB, ∑' m : Fin 2 → ℕ, T b m := by
      rw [Finset.mul_sum]
    _ = (8 * Real.exp (2 * Real.pi)) *
        ∑' m : Fin 2 → ℕ, ∑ b ∈ ScratchCase2Witness.caseTwoB, T b m := by
      rw [Summable.tsum_finsetSum hsum]
    _ = _ := by
      congr 2
      funext m
      dsimp [T]
      rw [Finset.mul_sum]

theorem scratch_gaussDominationCase2 {n : ℕ}

    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (i : Fin γ.k)
    (ι : MultiplierIndex γ) (hnegative : ι.1.1 < 0) (_hvertical : ι.1.2 = 0) :
    aux_GaussianDominationConclusion γ hkn i ι C_gaussDominationCase2 := by
  classical
  rcases ScratchCase2Witness.caseTwo_witness_side_conditions γ i
    (scratch_caseTwoLambda γ ι i) ι.1.1.natAbs
    (scratch_caseTwoLambda_spaced γ ι i)
    (scratch_caseTwoLambda_within γ ι i hnegative) with
    ⟨hcard, hscales, hdistance⟩
  have hbaseScales : ∀ b ∈ ScratchCase2Witness.caseTwoB, ∀ r : Fin 2,
      SpacedSequence ((ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b).1 r) := by
    intro b hb r
    exact ScratchCase2Witness.caseTwoSlotNat_spaced γ i (scratch_caseTwoLambda γ ι i)
      (scratch_caseTwoLambda_spaced γ ι i) b r
  have htail := aux_finite_dyadic_gaussian_series ScratchCase2Witness.caseTwoB
    (fun b => (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b).1)
    hbaseScales
    (ScratchCase2Witness.caseTwoOrientation γ i (scratch_caseTwoLambda γ ι i))
    (ScratchCase2Witness.caseTwoScales γ i (scratch_caseTwoLambda γ ι i)) (by
      intro b hb m r k
      rfl)
  refine ⟨{
    B := ScratchCase2Witness.caseTwoB
    card_le := hcard
    orientation := ScratchCase2Witness.caseTwoOrientation γ i (scratch_caseTwoLambda γ ι i)
    scales := ScratchCase2Witness.caseTwoScales γ i (scratch_caseTwoLambda γ ι i)
    scales_in_A := hscales
    distance_bound := hdistance
    estimate := ?_
    series_summable := htail.1
    series_integrable := htail.2
  }⟩
  intro j v
  let T : ℝ := ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
    ∑ b ∈ ScratchCase2Witness.caseTwoB,
      aux_dominatingGaussianTerm
        (ScratchCase2Witness.caseTwoScales γ i (scratch_caseTwoLambda γ ι i) b m)
        (ScratchCase2Witness.caseTwoOrientation γ i (scratch_caseTwoLambda γ ι i) b) j v
  have hpre := scratch_caseTwo_preGaussian_bound γ hkn ι i j v hnegative
  have hslot := scratch_caseTwo_slot_sum_gaussian_majorant γ ι i j v
  have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 3 := by
    rw [show C_standardBumpPropertiesTilde 0 3 = (2 : ℝ) ^ (33 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity

  have hfour : 0 ≤ C_fourScaleGaussianKernel 3 := by
    have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
    have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) :=
      (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
    unfold C_fourScaleGaussianKernel C_smoothDecay2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
      (mul_nonneg (by positivity) hsecond)
  have htri : 0 ≤ C_bumpTriangle 1 1 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  have hT : 0 ≤ T := by
    dsimp [T]
    apply tsum_nonneg
    intro m
    apply mul_nonneg (aux_gaussianDominationWeight_nonneg m)
    apply Finset.sum_nonneg
    intro b hb
    exact aux_dominatingGaussianTerm_nonneg
      (ScratchCase2Witness.caseTwoScales γ i (scratch_caseTwoLambda γ ι i) b m)
      (hscales b hb m)
      (ScratchCase2Witness.caseTwoOrientation γ i (scratch_caseTwoLambda γ ι i) b) j v
  have hloss : 0 ≤ Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hDbase : 0 ≤ C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
      C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hstd hfour) htri) htwo
  have hcoefbase : 0 ≤ C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
      C_hKernelDerivativeEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
      C_twoBumpEstimate 2 2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hstd hfour)
      aux_C_hKernelDerivativeEstimateGaussianDomination_nonneg) htri) htwo
  have hbase : 0 ≤ C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
      C_hKernelDerivativeEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
      C_twoBumpEstimate 2 2 * Real.exp (2 * Real.pi) *
      Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) * T := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcoefbase (Real.exp_pos _).le)
        hloss)
      hT
  have hprecoeff : 0 ≤ C_hKernelDerivativeEstimateGaussianDomination *
      ((27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
        C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
        Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)) := by
    have h27D : 0 ≤ (27 : ℝ) *
        (C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
          C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) :=
      mul_nonneg (by norm_num) hDbase
    have hD : 0 ≤ 27 * C_standardBumpPropertiesTilde 0 3 *
        C_fourScaleGaussianKernel 3 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
      convert h27D using 1 <;> ring
    exact mul_nonneg aux_C_hKernelDerivativeEstimateGaussianDomination_nonneg
      (mul_nonneg hD hloss)
  calc
    |nMultiplier γ hkn ι i j v| ≤
        C_hKernelDerivativeEstimateGaussianDomination *
          ((27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
            C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
            Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)) *
          ∑ b ∈ ScratchCase2Witness.caseTwoB,
            aux_kernelBracketProduct
              (ScratchCase2Witness.caseTwoSlotNat γ i (scratch_caseTwoLambda γ ι i) b) j v := hpre
    _ ≤ C_hKernelDerivativeEstimateGaussianDomination *
          ((27 * C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
            C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
            Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2)) *
          ((8 * Real.exp (2 * Real.pi)) * T) := by
      apply mul_le_mul_of_nonneg_left hslot hprecoeff
    _ = (216 : ℝ) *
        (C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
          C_hKernelDerivativeEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
          C_twoBumpEstimate 2 2 * Real.exp (2 * Real.pi) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) * T) := by ring
    _ ≤ (3 * (2 : ℝ) ^ (7 : ℕ)) *
        (C_standardBumpPropertiesTilde 0 3 * C_fourScaleGaussianKernel 3 *
          C_hKernelDerivativeEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
          C_twoBumpEstimate 2 2 * Real.exp (2 * Real.pi) *
          Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) * T) :=
      mul_le_mul_of_nonneg_right (by norm_num) hbase
    _ = C_gaussDominationCase2 *
        Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) * T := by
      unfold C_gaussDominationCase2
      ring
    _ = _ := by rfl
end ScratchCase2Cohesive


end aux_caseTwo

theorem gaussDominationCase2 {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (i : Fin γ.k) (ι : MultiplierIndex γ)
    (hnegative : ι.1.1 < 0) (_hvertical : ι.1.2 = 0) :
    aux_GaussianDominationConclusion γ hkn i ι C_gaussDominationCase2 := by
  exact aux_caseTwo.ScratchCase2Cohesive.scratch_gaussDominationCase2
    γ hkn i ι hnegative _hvertical


namespace aux_caseThree

open MeasureTheory
open scoped BigOperators ENNReal Real FourierTransform

open Codex.Preliminaries.Notation
open Codex.Preliminaries.Gaussians
open Codex.Preliminaries.BumpsAndEstimates
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN

noncomputable def scratch_caseThreeLambdaMinus {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) : ℤ → ℝ :=
  fun j => γ.scales i 1 (j + ι.1.2 - 1)

noncomputable def scratch_caseThreeLambdaPlus {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) : ℤ → ℝ :=
  fun j => γ.scales i 1 (j + ι.1.2)

theorem scratch_caseThreeLambdaMinus_spaced {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) :
    SpacedSequence (scratch_caseThreeLambdaMinus γ ι i) := by
  convert shift_mem_A (γ.scales_spaced i 1) (ι.1.2 - 1) using 1
  funext j
  simp [scratch_caseThreeLambdaMinus]
  ring

theorem scratch_caseThreeLambdaPlus_spaced {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) :
    SpacedSequence (scratch_caseThreeLambdaPlus γ ι i) := by
  convert shift_mem_A (γ.scales_spaced i 1) ι.1.2 using 1
  funext j
  simp [scratch_caseThreeLambdaPlus]

/-- The central-band four-scale representative has the `N = 2` two-scale decay needed
for Gaussian domination case 3. -/
theorem scratch_caseThree_nMultiplierRho_decay_bound {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 = 0) (x : ℝ) :
    |nMultiplierRho γ hkn ι i j x| ≤
      C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2 *
        (scaledBracketBump 2 (γ.scales i 1 (j + ι.1.2 - 1)) x +
          scaledBracketBump 2 (γ.scales i 1 (j + ι.1.2)) x) := by
  let r : ℤ := j + ι.1.2 - 1
  let a : ℤ → ℝ := γ.scales i 1
  let muMinus : ℝ := a r
  let muPlus : ℝ := a (r + 1)
  let lamMinus : ℝ := a r
  let lamPlus : ℝ := a (r + 1)
  have hnu : nMultiplierFourScaleExponent γ ∈ Set.Ico (-1 : ℝ) 0 :=
    nMultiplierFourScaleExponent_memIco γ
  have hmuMinus : 0 < muMinus := by
    dsimp [muMinus]
    exact (γ.scales_spaced i 1 _).1
  have hmuPlus : 0 < muPlus := by
    dsimp [muPlus]
    exact (γ.scales_spaced i 1 _).1
  have hlamMinus : 0 < lamMinus := by
    dsimp [lamMinus]
    exact (γ.scales_spaced i 1 _).1
  have hlamPlus : 0 < lamPlus := by
    dsimp [lamPlus]
    exact (γ.scales_spaced i 1 _).1
  have hscales : 2 * muMinus ≤ 2 * lamMinus ∧
      2 * lamMinus ≤ lamPlus ∧ lamPlus ≤ muPlus := by
    refine ⟨le_rfl, ?_, le_rfl⟩
    dsimp [lamMinus, lamPlus]
    exact (γ.scales_spaced i 1 r).2
  have hphiBound : ∀ m : ℕ, m ≤ 2 → ∀ xi : ℝ,
      ‖iteratedDeriv m
        (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ))) xi‖ ≤
        C_standardBumpPropertiesTilde 0 2 := by
    intro m hm xi
    have hraw : ‖iteratedDeriv m
        (fun u : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) ^ 0 *
          FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)) u) xi‖ ≤
        C_standardBumpPropertiesTilde 0 m := by
      exact aux_standardBumpMultiplier_iteratedDeriv_le_low 0 m hm xi
    simpa only [zero_mul, zero_add, pow_zero, one_mul] using
      hraw.trans (aux_C_standardBumpPropertiesTilde_mono 0 m 2 hm)
  have hcomplex := fourScaleGaussianKernel (C_standardBumpPropertiesTilde 0 2) 2
    (by norm_num) (fun z : ℝ => (standardBump z : ℂ))
    (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
    aux_standardBumpComplex_memW0 rfl (by norm_num [C_standardBumpPropertiesTilde])
    (closure_minimal (standardBumpProperties_fourierShape).2.1 isClosed_Icc)
    (standardBumpProperties_fourierShape).2.2
    (aux_standardBumpComplex_fourier_contDiff.of_le (WithTop.coe_le_coe.mpr le_top))
    hphiBound muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ)
    hmuMinus hmuPlus hlamMinus hlamPlus hscales hnu
  have hreal :
      |(fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x).re| ≤
        C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2 *
          (scaledBracketBump 2 lamMinus x + scaledBracketBump 2 lamPlus x) := by
    calc
      |(fourScaleGaussianRho
          (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
          muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x).re| ≤
          ‖fourScaleGaussianRho
            (FourierTransform.fourier (fun z : ℝ => (standardBump z : ℂ)))
            muMinus muPlus lamMinus lamPlus (nMultiplierFourScaleExponent γ) x‖ := by
        exact Complex.abs_re_le_norm _
      _ ≤ _ := hcomplex.2 x
  simpa [r, a, muMinus, muPlus, lamMinus, lamPlus,
    nMultiplierRho, nMultiplierRhoComplex, hzero] using hreal

theorem scratch_caseThree_u0_threeSlot (q : SequencePair × Fin 2) (j : ℤ)
    (v : RealPlane) (lam : ℝ) (hqu : q.2 = 0)
    (hq₀ : SpacedSequence (q.1 0)) (hq₁ : SpacedSequence (q.1 1))
    (hlam : 0 < lam) :
    (∫ p : ℝ, scaledBracketBump 2 lam p *
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
      9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 *
        (scaledBracketBump 2 (q.1 0 j) v.1 *
            scaledBracketBump 2 (max lam (q.1 1 j)) v.2 +
          scaledBracketBump 2 lam v.1 *
            scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 +
          scaledBracketBump 2 lam (W 1 v).1 *
            scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) (W 1 v).2) := by
  have ht₀ : 0 < q.1 0 j := (hq₀ j).1
  have ht₁ : 0 < q.1 1 j := (hq₁ j).1
  let A : ℝ := scaledBracketBump 2 (q.1 0 j) v.1 *
    scaledBracketBump 2 (max lam (q.1 1 j)) v.2
  let B : ℝ := scaledBracketBump 2 lam v.1 *
    scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2
  let C : ℝ := scaledBracketBump 2 lam ((v.1 + v.2) / Real.sqrt 2) *
    scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) ((v.1 - v.2) / Real.sqrt 2)
  let Braw : ℝ := scaledBracketBump 2 lam v.1 *
    scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) (v.1 - v.2)
  have hD : 0 ≤ C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, C_twoBumpEstimate,
      Real.rpow_natCast]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (aux_scaledBracketBump_nonneg 2 ht₀ _)
      (aux_scaledBracketBump_nonneg 2 (lt_max_of_lt_right ht₁) _)
  have hraw := aux_caseTwo.ScratchCase2Fourier.scratch_caseTwo_u0_threeBump_raw
    v.1 v.2 lam (q.1 0 j) (q.1 1 j) hlam ht₀ ht₁
  have hraw' :
      (∫ p : ℝ, scaledBracketBump 2 lam p *
        scaledBracketBump 2 (q.1 0 j) (v.1 - p) *
          scaledBracketBump 2 (q.1 1 j) (v.2 - p)) ≤
        C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + Braw) := by
    simpa [A, Braw] using hraw
  have hsplit := aux_caseTwo.ScratchCase2Fourier.scratch_caseTwo_orthogonal_split
    v.1 v.2 lam (max (q.1 0 j) (q.1 1 j)) hlam (lt_max_of_lt_left ht₀)
  have hsplit' : Braw ≤ 9 * (B + C) := by
    simpa [Braw, B, C] using hsplit
  have hsum : A + Braw ≤ 9 * (A + B + C) := by
    calc
      A + Braw = Braw + A := by ring
      _ ≤ 9 * (B + C) + A := by
        simpa [add_comm] using add_le_add_right hsplit' A
      _ = A + 9 * (B + C) := by ring
      _ ≤ 9 * (A + B + C) := by nlinarith [hA]
  have htriple :
      (∫ p : ℝ, scaledBracketBump 2 lam p *
        scaledBracketBump 2 (q.1 0 j) (v.1 - p) *
          scaledBracketBump 2 (q.1 1 j) (v.2 - p)) ≤
        9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + B + C) := by
    calc
      (∫ p : ℝ, scaledBracketBump 2 lam p *
          scaledBracketBump 2 (q.1 0 j) (v.1 - p) *
            scaledBracketBump 2 (q.1 1 j) (v.2 - p)) ≤
          C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + Braw) := hraw'
      _ ≤ C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (9 * (A + B + C)) :=
        mul_le_mul_of_nonneg_left hsum hD
      _ = 9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + B + C) := by
        ring
  have hmain :
      (∫ p : ℝ, scaledBracketBump 2 lam p *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
        9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 * (A + B + C) := by
    simpa [aux_kernelBracketProduct, hqu, W, mul_assoc] using htriple
  have hneg : (-v.1 + v.2) / Real.sqrt 2 = -((v.1 - v.2) / Real.sqrt 2) := by
    ring
  simpa [A, B, C, W, hneg,
    aux_caseTwo.ScratchCase2Fourier.scratch_scaledBracketBump_neg] using hmain

/-- A scale enlargement by at most two costs at most two for quadratic bracket bumps. -/
theorem scratch_scaledBracketBump_scale_le_two {r s x : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (hsr : s ≤ 2 * r) :
    scaledBracketBump 2 s x ≤ 2 * scaledBracketBump 2 r x := by
  have hcoord : r * |r⁻¹ * x| ≤ s * |s⁻¹ * x| := by
    have hrne : r ≠ 0 := ne_of_gt hr
    have hsne : s ≠ 0 := ne_of_gt hs
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hr),
      abs_of_pos (inv_pos.mpr hs)]
    field_simp [hrne, hsne]
    exact le_rfl
  have hbracket := aux_compareBracketsNat_base 2 hr hs hrs hcoord
  have hratio : s * r⁻¹ ≤ 2 := by
    calc
      s * r⁻¹ ≤ (2 * r) * r⁻¹ :=
        mul_le_mul_of_nonneg_right hsr (inv_nonneg.mpr hr.le)
      _ = 2 := by field_simp [ne_of_gt hr]
  have hnon : 0 ≤ scaledBracketBump 2 r x :=
    aux_scaledBracketBump_nonneg 2 hr _
  calc
    scaledBracketBump 2 s x = s⁻¹ * bracketBump (s⁻¹ * x) ^ 2 := by
      rfl
    _ = (s * s⁻¹ ^ 2) * bracketBump (s⁻¹ * x) ^ 2 := by
      congr 1
      field_simp [ne_of_gt hs]
    _ =
        s * (s⁻¹ ^ 2 * bracketBump (s⁻¹ * x) ^ 2) := by
      ring
    _ ≤ s * (r⁻¹ ^ 2 * bracketBump (r⁻¹ * x) ^ 2) :=
      mul_le_mul_of_nonneg_left hbracket hs.le
    _ = (s * r⁻¹) * scaledBracketBump 2 r x := by
      change s * (r⁻¹ ^ 2 * (1 + |r⁻¹ * x|)⁻¹ ^ 2) =
        (s * r⁻¹) * (r⁻¹ * (1 + |r⁻¹ * x|)⁻¹ ^ 2)
      ring
    _ ≤ 2 * scaledBracketBump 2 r x :=
      mul_le_mul_of_nonneg_right hratio hnon

private theorem scratch_caseThree_simul_rescale (N : ℕ) (c s x : ℝ) (hc : 0 < c) :
    c * scaledBracketBump N (c * s) (c * x) = scaledBracketBump N s x := by
  unfold scaledBracketBump
  have hcne : c ≠ 0 := ne_of_gt hc
  have harg : (c * s)⁻¹ * (c * x) = s⁻¹ * x := by
    field_simp [hcne]
  have hinv : c * (c * s)⁻¹ = s⁻¹ := by
    field_simp [hcne]
  rw [harg]
  calc
    c * ((c * s)⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N) =
        (c * (c * s)⁻¹) * (1 + |s⁻¹ * x|)⁻¹ ^ N := by ring
    _ = s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N := by rw [hinv]

private theorem scratch_caseThree_integral_scale_pos (c : ℝ) (hc : 0 < c)
    (g : ℝ → ℝ) :
    (∫ p : ℝ, c * g (c * p)) = ∫ x : ℝ, g x := by
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  simp only [smul_eq_mul, abs_inv, abs_of_pos (inv_pos.mpr hc)]
  field_simp [hc.ne']

/-- The central-band orientation-one occurrence uses the maximum of its scale and the
first H-package scale, at a harmless factor two. -/
theorem scratch_caseThree_u1_oneSlot (w0 w1 lam t0 t1 : ℝ)
    (hlam : 0 < lam) (ht0 : 0 < t0) (ht1 : 0 < t1) :
    (∫ p : ℝ, scaledBracketBump 2 lam p *
        scaledBracketBump 2 t0 (Real.sqrt 2 * (w0 - p)) *
        scaledBracketBump 2 t1 (Real.sqrt 2 * w1)) ≤
      2 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 (max lam t0) (Real.sqrt 2 * w0) *
        scaledBracketBump 2 t1 (Real.sqrt 2 * w1) := by
  let c : ℝ := Real.sqrt 2
  have hc : 0 < c := Real.sqrt_pos.2 (by norm_num)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hc2 : c ≤ 2 := by
    dsimp [c]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  let g : ℝ → ℝ := fun x =>
    scaledBracketBump 2 (c * lam) x * scaledBracketBump 2 t0 (c * w0 - x)
  have hscale (p : ℝ) :
      scaledBracketBump 2 lam p * scaledBracketBump 2 t0 (c * (w0 - p)) =
        c * g (c * p) := by
    rw [show c * (w0 - p) = c * w0 - c * p by ring]
    have hres := scratch_caseThree_simul_rescale 2 c lam p hc
    dsimp [g]
    calc
      scaledBracketBump 2 lam p * scaledBracketBump 2 t0 (c * w0 - c * p) =
          (c * scaledBracketBump 2 (c * lam) (c * p)) *
            scaledBracketBump 2 t0 (c * w0 - c * p) := by rw [hres]
      _ = c * g (c * p) := by ring
  have htwoBase :=
    aux_caseTwo.ScratchCase2Fourier.scratch_twoBumpIntegral_max_two
      0 (c * w0) (c * lam) t0 (mul_pos hc hlam) ht0
  have htwo :
      (∫ x : ℝ, g x) ≤
        C_twoBumpEstimate 2 2 *
          scaledBracketBump 2 (max (c * lam) t0) (c * w0) := by
    calc
      (∫ x : ℝ, g x) = ∫ x : ℝ,
          scaledBracketBump 2 (c * lam) (0 - x) *
            scaledBracketBump 2 t0 (c * w0 - x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [g]
        rw [show 0 - x = -x by ring,
          aux_caseTwo.ScratchCase2Fourier.scratch_scaledBracketBump_neg]
      _ ≤ C_twoBumpEstimate 2 2 *
          scaledBracketBump 2 (max (c * lam) t0) (0 - c * w0) := htwoBase
      _ = C_twoBumpEstimate 2 2 *
          scaledBracketBump 2 (max (c * lam) t0) (c * w0) := by
        rw [show 0 - c * w0 = -(c * w0) by ring,
          aux_caseTwo.ScratchCase2Fourier.scratch_scaledBracketBump_neg]
  let r : ℝ := max lam t0
  let s : ℝ := max (c * lam) t0
  have hr : 0 < r := lt_max_of_lt_left hlam
  have hs : 0 < s := lt_max_of_lt_left (mul_pos hc hlam)
  have hrs : r ≤ s := by
    dsimp [r, s]
    apply max_le
    · have hcl : lam ≤ c * lam := by
        simpa using (mul_le_mul_of_nonneg_right hc1 hlam.le)
      exact hcl.trans (le_max_left _ _)
    · exact le_max_right _ _
  have hsr : s ≤ 2 * r := by
    dsimp [r, s]
    apply max_le
    · calc
        c * lam ≤ 2 * lam := mul_le_mul_of_nonneg_right hc2 hlam.le
        _ ≤ 2 * max lam t0 := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    · calc
        t0 ≤ 2 * t0 := by nlinarith
        _ ≤ 2 * max lam t0 :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (show (0 : ℝ) ≤ 2 by norm_num)
  have hcompare (x : ℝ) :
      scaledBracketBump 2 s x ≤ 2 * scaledBracketBump 2 r x :=
    scratch_scaledBracketBump_scale_le_two hr hs hrs hsr
  let b : ℝ := scaledBracketBump 2 t1 (c * w1)
  have hb : 0 ≤ b := aux_scaledBracketBump_nonneg 2 ht1 _
  have htwoNonneg : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  calc
    (∫ p : ℝ, scaledBracketBump 2 lam p *
        scaledBracketBump 2 t0 (c * (w0 - p)) *
        scaledBracketBump 2 t1 (c * w1)) =
        (∫ p : ℝ, c * g (c * p)) * b := by
      rw [integral_mul_const]
      apply congrArg (fun z : ℝ => z * b)
      apply integral_congr_ae
      filter_upwards [] with p
      rw [← hscale]
    _ = (∫ x : ℝ, g x) * b := by
      rw [scratch_caseThree_integral_scale_pos c hc g]
    _ ≤ (C_twoBumpEstimate 2 2 * scaledBracketBump 2 s (c * w0)) * b := by
      exact mul_le_mul_of_nonneg_right (by simpa [s] using htwo) hb
    _ ≤ (C_twoBumpEstimate 2 2 * (2 * scaledBracketBump 2 r (c * w0))) * b := by
      apply mul_le_mul_of_nonneg_right
      exact mul_le_mul_of_nonneg_left (hcompare (c * w0)) htwoNonneg
      exact hb
    _ = 2 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 (max lam t0) (Real.sqrt 2 * w0) *
        scaledBracketBump 2 t1 (Real.sqrt 2 * w1) := by
      dsimp [b, r, c]
      ring

theorem scratch_caseThree_u1_kernelSlot (q : SequencePair × Fin 2) (j : ℤ)
    (v : RealPlane) (lam : ℝ) (hqu : q.2 = 1)
    (hq₀ : SpacedSequence (q.1 0)) (hq₁ : SpacedSequence (q.1 1))
    (hlam : 0 < lam) :
    (∫ p : ℝ, scaledBracketBump 2 lam p *
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
      2 * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 (max lam (q.1 0 j)) (W 1 v).1 *
        scaledBracketBump 2 (q.1 1 j) (W 1 v).2 := by
  let w0 : ℝ := (v.1 + v.2) / 2
  let w1 : ℝ := (v.2 - v.1) / 2
  let c : ℝ := Real.sqrt 2
  have hc : 0 < c := Real.sqrt_pos.2 (by norm_num)
  have ht0 : 0 < q.1 0 j := (hq₀ j).1
  have ht1 : 0 < q.1 1 j := (hq₁ j).1
  have hfirst (p : ℝ) :
      (W q.2 (v.1 - p, v.2 - p)).1 = c * (w0 - p) := by
    rw [hqu]
    simp only [W, Fin.isValue, if_false]
    apply (div_eq_iff hc.ne').2
    have hsquare : c ^ 2 = 2 := by
      dsimp [c]
      norm_num
    dsimp [w0]
    calc
      (v.1 - p) + (v.2 - p) = 2 * ((v.1 + v.2) / 2 - p) := by ring
      _ = c ^ 2 * ((v.1 + v.2) / 2 - p) := by rw [hsquare]
      _ = (c * ((v.1 + v.2) / 2 - p)) * c := by ring
  have hsecond (p : ℝ) :
      (W q.2 (v.1 - p, v.2 - p)).2 = c * w1 := by
    rw [hqu]
    simp only [W, Fin.isValue, if_false]
    apply (div_eq_iff hc.ne').2
    have hsquare : c ^ 2 = 2 := by
      dsimp [c]
      norm_num
    dsimp [w1]
    calc
      -(v.1 - p) + (v.2 - p) = 2 * ((v.2 - v.1) / 2) := by ring
      _ = c ^ 2 * ((v.2 - v.1) / 2) := by rw [hsquare]
      _ = (c * ((v.2 - v.1) / 2)) * c := by ring
  have hVfirst : (W 1 v).1 = c * w0 := by
    rw [show (1 : Fin 2) = q.2 by rw [hqu]]
    simpa using hfirst 0
  have hVsecond : (W 1 v).2 = c * w1 := by
    rw [show (1 : Fin 2) = q.2 by rw [hqu]]
    simpa using hsecond 0
  have hraw := scratch_caseThree_u1_oneSlot w0 w1 lam (q.1 0 j) (q.1 1 j)
    hlam ht0 ht1
  have hmain :
      (∫ p : ℝ, scaledBracketBump 2 lam p *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
        2 * C_twoBumpEstimate 2 2 *
          scaledBracketBump 2 (max lam (q.1 0 j)) (c * w0) *
          scaledBracketBump 2 (q.1 1 j) (c * w1) := by
    calc
      (∫ p : ℝ, scaledBracketBump 2 lam p *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) =
          ∫ p : ℝ, scaledBracketBump 2 lam p *
            scaledBracketBump 2 (q.1 0 j) (c * (w0 - p)) *
            scaledBracketBump 2 (q.1 1 j) (c * w1) := by
        apply integral_congr_ae
        filter_upwards [] with p
        rw [aux_kernelBracketProduct, hfirst, hsecond]
        ring
      _ ≤ _ := hraw
  simpa [hVfirst, hVsecond] using hmain

private theorem scratch_caseThree_continuous_scaledBracketBump (N : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ => scaledBracketBump N s x) := by
  unfold scaledBracketBump
  have hbase : Continuous (fun x : ℝ => 1 + |s⁻¹ * x|) := by fun_prop
  apply continuous_const.mul
  rw [continuous_iff_continuousAt]
  intro x
  exact (hbase.continuousAt.inv₀ (ne_of_gt (by positivity))).pow N

/-- Every central-rho/H-package occurrence has an integrable nonnegative majorant. -/
theorem scratch_caseThree_weighted_kernel_integrable
    (q : SequencePair × Fin 2) (j : ℤ) (v : RealPlane) (lam : ℝ)
    (hq₀ : SpacedSequence (q.1 0)) (hq₁ : SpacedSequence (q.1 1))
    (hlam : 0 < lam) :
    Integrable (fun p : ℝ => scaledBracketBump 2 lam p *
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) := by
  let t₀ : ℝ := q.1 0 j
  let t₁ : ℝ := q.1 1 j
  have ht₀ : 0 < t₀ := by simpa [t₀] using (hq₀ j).1
  have ht₁ : 0 < t₁ := by simpa [t₁] using (hq₁ j).1
  have hlamInt : Integrable (fun p : ℝ => scaledBracketBump 2 lam p) := by
    convert aux_integrable_scaledBracketBumpReal 2 lam (by norm_num) hlam using 1
    funext p
    rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
  have harg₀ : Continuous (fun p : ℝ => (W q.2 (v.1 - p, v.2 - p)).1) := by
    unfold W
    split <;> fun_prop
  have harg₁ : Continuous (fun p : ℝ => (W q.2 (v.1 - p, v.2 - p)).2) := by
    unfold W
    split <;> fun_prop
  have hBracketCont : Continuous (fun p : ℝ =>
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) := by
    unfold aux_kernelBracketProduct
    exact ((scratch_caseThree_continuous_scaledBracketBump 2 t₀).comp harg₀).mul
      ((scratch_caseThree_continuous_scaledBracketBump 2 t₁).comp harg₁)
  have hBracketNonneg (p : ℝ) :
      0 ≤ aux_kernelBracketProduct q j (v.1 - p, v.2 - p) := by
    unfold aux_kernelBracketProduct
    exact mul_nonneg
      (aux_scaledBracketBump_nonneg 2 ht₀ _)
      (aux_scaledBracketBump_nonneg 2 ht₁ _)
  have hBracketBound (p : ℝ) :
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p) ≤ t₀⁻¹ * t₁⁻¹ := by
    unfold aux_kernelBracketProduct
    calc
      scaledBracketBump 2 t₀ (W q.2 (v.1 - p, v.2 - p)).1 *
          scaledBracketBump 2 t₁ (W q.2 (v.1 - p, v.2 - p)).2 ≤
          t₀⁻¹ * scaledBracketBump 2 t₁ (W q.2 (v.1 - p, v.2 - p)).2 :=
        mul_le_mul_of_nonneg_right
          (aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv ht₀)
          (aux_scaledBracketBump_nonneg 2 ht₁ _)
      _ ≤ t₀⁻¹ * t₁⁻¹ :=
        mul_le_mul_of_nonneg_left
          (aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv ht₁)
          (inv_nonneg.mpr ht₀.le)
  refine hlamInt.mul_bdd (c := t₀⁻¹ * t₁⁻¹) hBracketCont.aestronglyMeasurable ?_
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (hBracketNonneg p)]
  exact hBracketBound p

private theorem scratch_caseThree_HPackage_explicit {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) :
    aux_HKernelGaussianBound γ i (aux_hKernelGaussianMultiset γ i) := by
  by_cases h : γ.orientation i = 0
  · apply aux_hKernelGaussianBound_orientation_zero_of_sBounds γ i h
    intro j x
    apply aux_sMultiplier_bound_orientation_zero_of_diagonal γ i j h
    intro y
    rw [aux_sMultiplier_eq_diagonalSquareRoot]
    have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
    apply diagonalSquareRoot_bound 2 (by norm_num)
    · linarith [hsp.1]
    · convert hsp.2 using 1 <;> ring
  · apply aux_hKernelGaussianBound_orientation_one_of_sBounds γ i h
    intro j x
    apply aux_sMultiplier_bound_orientation_one_of_diagonal γ i j h
    intro y
    rw [aux_sMultiplier_eq_diagonalSquareRoot]
    have hsp := aux_sMultiplierScale_spaced γ i (j - 1)
    apply diagonalSquareRoot_bound 2 (by norm_num)
    · linarith [hsp.1]
    · convert hsp.2 using 1 <;> ring

private theorem scratch_caseThree_integrable_multiset_sum {α : Type*} (P : Multiset α)
    (g : α → ℝ → ℝ) (hg : ∀ q ∈ P, Integrable (g q)) :
    Integrable (fun x : ℝ => (P.map fun q => g q x).sum) := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      apply Integrable.add
      · exact hg a (by simp)
      · apply ih
        intro q hq
        exact hg q (by simp [hq])

private theorem scratch_caseThree_integral_multiset_sum {α : Type*} (P : Multiset α)
    (g : α → ℝ → ℝ) (hg : ∀ q ∈ P, Integrable (g q)) :
    (∫ x : ℝ, (P.map fun q => g q x).sum) =
      (P.map fun q => ∫ x : ℝ, g q x).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih =>
      have hgP : ∀ q ∈ P, Integrable (g q) := by
        intro q hq
        exact hg q (by simp [hq])
      have hsumP : Integrable (fun x : ℝ => (P.map fun q => g q x).sum) :=
        scratch_caseThree_integrable_multiset_sum P g hgP
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [integral_add (hg a (by simp)) hsumP, ih hgP]

private theorem scratch_caseThree_mul_multiset_sum {α : Type*} (a : ℝ) (P : Multiset α)
    (g : α → ℝ) :
    a * (P.map g).sum = (P.map fun q => a * g q).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons q P ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [mul_add, ih]

private theorem scratch_caseThree_finite_multiset_integral_bridge {α : Type*}
    (P : Multiset α) (C : ℝ) (rho H : ℝ → ℝ) (B : α → ℝ → ℝ)
    (hC : 0 ≤ C) (hrho : ∀ p, 0 ≤ rho p) (hH : ∀ p, 0 ≤ H p)
    (hbound : ∀ p, H p ≤ C * (P.map fun q => B q p).sum)
    (hint : ∀ q ∈ P, Integrable (fun p : ℝ => rho p * B q p)) :
    (∫ p : ℝ, rho p * H p) ≤
      C * (P.map fun q => ∫ p : ℝ, rho p * B q p).sum := by
  let S : ℝ → ℝ := fun p => (P.map fun q => rho p * B q p).sum
  have hS : Integrable S := by
    dsimp [S]
    exact scratch_caseThree_integrable_multiset_sum P (fun q p => rho p * B q p) hint
  have hpoint (p : ℝ) : rho p * H p ≤ C * S p := by
    have h := mul_le_mul_of_nonneg_left (hbound p) (hrho p)
    change rho p * H p ≤ rho p * (C * (P.map fun q => B q p).sum) at h
    calc
      rho p * H p ≤ rho p * (C * (P.map fun q => B q p).sum) := h
      _ = C * (rho p * (P.map fun q => B q p).sum) := by ring
      _ = C * S p := by
        dsimp [S]
        rw [scratch_caseThree_mul_multiset_sum]
  have hleft (p : ℝ) : 0 ≤ rho p * H p := mul_nonneg (hrho p) (hH p)
  calc
    (∫ p : ℝ, rho p * H p) ≤ ∫ p : ℝ, C * S p :=
      integral_mono_of_nonneg (ae_of_all _ hleft) (hS.const_mul C)
        (ae_of_all _ hpoint)
    _ = C * (∫ p : ℝ, S p) := by rw [integral_const_mul]
    _ = C * (P.map fun q => ∫ p : ℝ, rho p * B q p).sum := by
      rw [scratch_caseThree_integral_multiset_sum P (fun q p => rho p * B q p) hint]

private theorem scratch_caseThree_fourScale_nonneg :
    0 ≤ C_fourScaleGaussianKernel 2 := by
  have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 2) :=
    (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
  have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 2) :=
    (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
  unfold C_fourScaleGaussianKernel C_smoothDecay2
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
    (mul_nonneg (by positivity) hsecond)

/-- The direct central-band convolution is reduced to the six H-package occurrence
integrals, retaining both four-scale rho terms. -/
theorem scratch_caseThree_outer_raw {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane) (hzero : ι.1.1 = 0) :
    |nMultiplier γ hkn ι i j v| ≤
      (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
        C_hKernelEstimateGaussianDomination *
        ((aux_hKernelGaussianMultiset γ i).map fun q =>
          ∫ p : ℝ,
            (scaledBracketBump 2 (γ.scales i 1 (j + ι.1.2 - 1)) p +
              scaledBracketBump 2 (γ.scales i 1 (j + ι.1.2)) p) *
              aux_kernelBracketProduct q j (v.1 - p, v.2 - p)).sum := by
  let lamMinus : ℝ := γ.scales i 1 (j + ι.1.2 - 1)
  let lamPlus : ℝ := γ.scales i 1 (j + ι.1.2)
  let A : ℝ := C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2
  let rho : ℝ → ℝ := fun p =>
    scaledBracketBump 2 lamMinus p + scaledBracketBump 2 lamPlus p
  let H : ℝ → ℝ := fun p => |hMultiplier γ i j (v.1 - p, v.2 - p)|
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let B : (SequencePair × Fin 2) → ℝ → ℝ := fun q p =>
    aux_kernelBracketProduct q j (v.1 - p, v.2 - p)
  have hlamMinus : 0 < lamMinus := by
    dsimp [lamMinus]
    exact (γ.scales_spaced i 1 _).1
  have hlamPlus : 0 < lamPlus := by
    dsimp [lamPlus]
    exact (γ.scales_spaced i 1 _).1
  have hA : 0 ≤ A := by
    dsimp [A]
    have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 2 := by
      rw [show C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) by
        norm_num [C_standardBumpPropertiesTilde]]
      positivity
    exact mul_nonneg hstd scratch_caseThree_fourScale_nonneg
  have hrhoNonneg (p : ℝ) : 0 ≤ rho p := by
    dsimp [rho]
    exact add_nonneg (aux_scaledBracketBump_nonneg 2 hlamMinus _)
      (aux_scaledBracketBump_nonneg 2 hlamPlus _)
  have hdecay (p : ℝ) : |nMultiplierRho γ hkn ι i j p| ≤ A * rho p := by
    simpa [A, rho, lamMinus, lamPlus] using
      scratch_caseThree_nMultiplierRho_decay_bound γ hkn ι i j hzero p
  have hP : aux_HKernelGaussianBound γ i P := by
    simpa [P] using scratch_caseThree_HPackage_explicit γ i
  have hint : ∀ q ∈ P, Integrable (fun p : ℝ => rho p * B q p) := by
    intro q hq
    rcases hP.1 q hq with ⟨hq₀, hq₁⟩
    have hminus := scratch_caseThree_weighted_kernel_integrable q j v lamMinus hq₀.1 hq₁.1
      hlamMinus
    have hplus := scratch_caseThree_weighted_kernel_integrable q j v lamPlus hq₀.1 hq₁.1
      hlamPlus
    have heq : (fun p : ℝ => rho p * B q p) =
        (fun p : ℝ =>
          scaledBracketBump 2 lamMinus p * aux_kernelBracketProduct q j (v.1 - p, v.2 - p) +
          scaledBracketBump 2 lamPlus p * aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) := by
      funext p
      simp [rho, B, add_mul]
    rw [heq]
    exact hminus.add hplus
  have hHbound (p : ℝ) : H p ≤ C_hKernelEstimateGaussianDomination *
      (P.map fun q => B q p).sum := by
    dsimp [H, B]
    exact hP.2.2 (v.1 - p, v.2 - p) j
  have hbridge := scratch_caseThree_finite_multiset_integral_bridge P
    C_hKernelEstimateGaussianDomination rho H B
    aux_C_hKernelEstimateGaussianDomination_nonneg hrhoNonneg (fun p => abs_nonneg _)
    hHbound hint
  have hrhoCont : Continuous rho := by
    dsimp [rho]
    exact (scratch_caseThree_continuous_scaledBracketBump 2 lamMinus).add
      (scratch_caseThree_continuous_scaledBracketBump 2 lamPlus)
  have hM : 0 ≤ lamMinus⁻¹ + lamPlus⁻¹ :=
    add_nonneg (inv_nonneg.mpr hlamMinus.le) (inv_nonneg.mpr hlamPlus.le)
  have hrhoBound (p : ℝ) : rho p ≤ lamMinus⁻¹ + lamPlus⁻¹ := by
    dsimp [rho]
    exact add_le_add
      (aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv hlamMinus)
      (aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv hlamPlus)
  have hHint : Integrable H := by
    simpa [H, Real.norm_eq_abs] using
      (aux_hMultiplier_diagonal_translate_integrable γ i j v).norm
  have hRHint : Integrable (fun p : ℝ => rho p * H p) := by
    have h := hHint.mul_bdd (c := lamMinus⁻¹ + lamPlus⁻¹)
      hrhoCont.aestronglyMeasurable (by
        filter_upwards [] with p
        rw [Real.norm_eq_abs, abs_of_nonneg (hrhoNonneg p)]
        exact hrhoBound p)
    simpa [mul_comm] using h
  have hactualMajor (p : ℝ) :
      |hMultiplier γ i j (v.1 - p, v.2 - p) * nMultiplierRho γ hkn ι i j p| ≤
        A * (rho p * H p) := by
    have h := mul_le_mul_of_nonneg_left (hdecay p)
      (abs_nonneg (hMultiplier γ i j (v.1 - p, v.2 - p)))
    change H p * |nMultiplierRho γ hkn ι i j p| ≤ H p * (A * rho p) at h
    calc
      |hMultiplier γ i j (v.1 - p, v.2 - p) * nMultiplierRho γ hkn ι i j p| =
          H p * |nMultiplierRho γ hkn ι i j p| := by
        simp [H, abs_mul]
      _ ≤ H p * (A * rho p) := h
      _ = A * (rho p * H p) := by ring
  have hmajorInt : Integrable (fun p : ℝ => A * (rho p * H p)) :=
    hRHint.const_mul A
  change |∫ p : ℝ,
    hMultiplier γ i j (v.1 - p, v.2 - p) * nMultiplierRho γ hkn ι i j p| ≤ _
  calc
    |∫ p : ℝ,
        hMultiplier γ i j (v.1 - p, v.2 - p) * nMultiplierRho γ hkn ι i j p| ≤
        ∫ p : ℝ, |hMultiplier γ i j (v.1 - p, v.2 - p) *
          nMultiplierRho γ hkn ι i j p| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p : ℝ, A * (rho p * H p) :=
      integral_mono_of_nonneg (ae_of_all _ (fun p => abs_nonneg _)) hmajorInt
        (ae_of_all _ hactualMajor)
    _ = A * (∫ p : ℝ, rho p * H p) := by rw [integral_const_mul]
    _ ≤ A *
        (C_hKernelEstimateGaussianDomination *
          (P.map fun q => ∫ p : ℝ, rho p * B q p).sum) :=
      mul_le_mul_of_nonneg_left hbridge hA
    _ = (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
        C_hKernelEstimateGaussianDomination *
        ((aux_hKernelGaussianMultiset γ i).map fun q =>
          ∫ p : ℝ,
            (scaledBracketBump 2 (γ.scales i 1 (j + ι.1.2 - 1)) p +
              scaledBracketBump 2 (γ.scales i 1 (j + ι.1.2)) p) *
              aux_kernelBracketProduct q j (v.1 - p, v.2 - p)).sum := by
      simp only [A, P, rho, B, lamMinus, lamPlus]
      ring

open scoped BigOperators ENNReal Real FourierTransform

open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open aux_caseTwo.ScratchCase2Witness

/-!
Scratch-only direct Case 3 witness interface.

The decoder deliberately keeps all multiplicities: six occurrences of the
canonical H package, the two rho scales, and three padded outputs per
occurrence.  Thus it uses `6 * 2 * 3 = 36` slots.
-/

def scratch_caseThreeLambda (lamMinus lamPlus : ℤ → ℝ) (e : Fin 2) : ℤ → ℝ :=
  if e = 0 then lamMinus else lamPlus

def scratch_caseThreeMaxScale (q : SequencePair × Fin 2) : ℤ → ℝ :=
  fun j => max (q.1 0 j) (q.1 1 j)

def scratch_caseThreeLambdaMaxSecondScale (lam : ℤ → ℝ) (q : SequencePair × Fin 2) :
    ℤ → ℝ :=
  fun j => max (lam j) (q.1 1 j)

def scratch_caseThreeLambdaMaxFirstScale (lam : ℤ → ℝ) (q : SequencePair × Fin 2) :
    ℤ → ℝ :=
  fun j => max (lam j) (q.1 0 j)

/-- The exact three-slot Case 3 occurrence decoder.  Unlike Case 2, an
orientation-one occurrence has the nontrivial first slot
`(max λ q₀, q₁, 1)`; the other two slots are harmless padding. -/
def scratch_caseThreeExactSlotOf (lam : ℤ → ℝ) (q : SequencePair × Fin 2) (r : Fin 3) :
    SequencePair × Fin 2 :=
  if _hq : q.2 = 0 then
    if r = 0 then
      (aux_sequencePairOf (q.1 0) (scratch_caseThreeLambdaMaxSecondScale lam q),
        (0 : Fin 2))
    else if r = 1 then
      (aux_sequencePairOf lam (scratch_caseThreeMaxScale q), (0 : Fin 2))
    else
      (aux_sequencePairOf lam (scratch_caseThreeMaxScale q), (1 : Fin 2))
  else if r = 0 then
    (aux_sequencePairOf (scratch_caseThreeLambdaMaxFirstScale lam q) (q.1 1),
      (1 : Fin 2))
  else q

theorem scratch_caseThreeExactSlotOf_spaced (lam : ℤ → ℝ) (hlam : SpacedSequence lam)
    (q : SequencePair × Fin 2) (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (r : Fin 3) :
    ∀ s : Fin 2, SpacedSequence ((scratch_caseThreeExactSlotOf lam q r).1 s) := by
  by_cases hqu : q.2 = 0
  · by_cases hr0 : r = 0
    · intro s
      fin_cases s
      · simpa [scratch_caseThreeExactSlotOf, hqu, hr0, aux_sequencePairOf] using hq 0
      · simp only [scratch_caseThreeExactSlotOf, dif_pos hqu, if_pos hr0,
          aux_sequencePairOf]
        change SpacedSequence (scratch_caseThreeLambdaMaxSecondScale lam q)
        unfold scratch_caseThreeLambdaMaxSecondScale
        exact max_mem_A hlam (hq 1)
    · by_cases hr1 : r = 1
      · intro s
        fin_cases s
        · simpa [scratch_caseThreeExactSlotOf, hqu, hr0, hr1, aux_sequencePairOf] using hlam
        · simp only [scratch_caseThreeExactSlotOf, dif_pos hqu, if_neg hr0, if_pos hr1,
            aux_sequencePairOf]
          change SpacedSequence (scratch_caseThreeMaxScale q)
          unfold scratch_caseThreeMaxScale
          exact max_mem_A (hq 0) (hq 1)
      · intro s
        fin_cases s
        · simpa [scratch_caseThreeExactSlotOf, hqu, hr0, hr1, aux_sequencePairOf] using hlam
        · simp only [scratch_caseThreeExactSlotOf, dif_pos hqu, if_neg hr0, if_neg hr1,
            aux_sequencePairOf]
          change SpacedSequence (scratch_caseThreeMaxScale q)
          unfold scratch_caseThreeMaxScale
          exact max_mem_A (hq 0) (hq 1)
  · by_cases hr0 : r = 0
    · intro s
      fin_cases s
      · simp only [scratch_caseThreeExactSlotOf, dif_neg hqu, if_pos hr0,
          aux_sequencePairOf]
        change SpacedSequence (scratch_caseThreeLambdaMaxFirstScale lam q)
        unfold scratch_caseThreeLambdaMaxFirstScale
        exact max_mem_A hlam (hq 0)
      · simpa [scratch_caseThreeExactSlotOf, hqu, hr0, aux_sequencePairOf] using hq 1
    · simpa [scratch_caseThreeExactSlotOf, hqu, hr0] using hq

/-- Decode a natural number into an H occurrence, one of the two rho scales,
and one of the three active/padded Case-2 output slots. -/
def scratch_caseThreeSlotIndex (b : ℕ) : (Fin 6 × Fin 2) × Fin 3 :=
  ((⟨(b / 3 / 2) % 6, Nat.mod_lt _ (by norm_num)⟩,
    ⟨(b / 3) % 2, Nat.mod_lt _ (by norm_num)⟩),
    ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩)

noncomputable def scratch_caseThreeSlotNat {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ) (b : ℕ) : SequencePair × Fin 2 :=
  scratch_caseThreeExactSlotOf
    (scratch_caseThreeLambda lamMinus lamPlus (scratch_caseThreeSlotIndex b).1.2)
    (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
      (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm
        (scratch_caseThreeSlotIndex b).1.1))
    (scratch_caseThreeSlotIndex b).2

def scratch_caseThreeB : Finset ℕ := Finset.range 36

noncomputable def scratch_caseThreeOrientation {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ) (b : ℕ) : Fin 2 :=
  (scratch_caseThreeSlotNat γ i lamMinus lamPlus b).2

noncomputable def scratch_caseThreeScales {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ) (b : ℕ) (m : Fin 2 → ℕ) :
    SequencePair :=
  fun r j => (2 : ℝ) ^ (m r) * (scratch_caseThreeSlotNat γ i lamMinus lamPlus b).1 r j

theorem scratch_caseThreeB_card : scratch_caseThreeB.card = 36 := by
  simp [scratch_caseThreeB]

theorem scratch_caseThreeSlotNat_spaced {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ)
    (hminus : SpacedSequence lamMinus) (hplus : SpacedSequence lamPlus) (b : ℕ) :
    ∀ r : Fin 2, SpacedSequence ((scratch_caseThreeSlotNat γ i lamMinus lamPlus b).1 r) := by
  let e : Fin 2 := (scratch_caseThreeSlotIndex b).1.2
  have hlam : SpacedSequence (scratch_caseThreeLambda lamMinus lamPlus e) := by
    by_cases he : e = 0
    · simpa [scratch_caseThreeLambda, he] using hminus
    · simpa [scratch_caseThreeLambda, he] using hplus
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let k : Fin P.card := Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm
    (scratch_caseThreeSlotIndex b).1.1
  let q : SequencePair × Fin 2 := caseTwoOccurrence P k
  have hqmem : q ∈ P := caseTwoOccurrence_mem P k
  have hvalid := aux_hKernelGaussianMultiset_valid γ i q (by simpa [P] using hqmem)
  have hq : ∀ r : Fin 2, SpacedSequence (q.1 r) := by
    intro r
    fin_cases r
    · exact hvalid.1.1
    · exact hvalid.2.1
  have hslot := scratch_caseThreeExactSlotOf_spaced (scratch_caseThreeLambda lamMinus lamPlus e)
    hlam q hq (scratch_caseThreeSlotIndex b).2
  simpa [scratch_caseThreeSlotNat, e, P, k, q] using hslot

theorem scratch_caseThreeScales_spaced {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ)
    (hminus : SpacedSequence lamMinus) (hplus : SpacedSequence lamPlus) (b : ℕ)
    (m : Fin 2 → ℕ) (r : Fin 2) :
    SpacedSequence (scratch_caseThreeScales γ i lamMinus lamPlus b m r) := by
  unfold scratch_caseThreeScales
  exact smul_mem_A (scratch_caseThreeSlotNat_spaced γ i lamMinus lamPlus hminus hplus b r)
    (pow_pos (by norm_num) _)

theorem scratch_caseThreeSlotIndex_encode (k : Fin 6) (e : Fin 2) (r : Fin 3) :
    scratch_caseThreeSlotIndex ((k.1 * 2 + e.1) * 3 + r.1) = ((k, e), r) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      simp [scratch_caseThreeSlotIndex]
      omega
    · apply Fin.ext
      simp [scratch_caseThreeSlotIndex]
      omega
  · apply Fin.ext
    simp [scratch_caseThreeSlotIndex]

theorem scratch_caseThreeSlotNat_encode {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ) (k : Fin 6) (e : Fin 2) (r : Fin 3) :
    scratch_caseThreeSlotNat γ i lamMinus lamPlus ((k.1 * 2 + e.1) * 3 + r.1) =
      scratch_caseThreeExactSlotOf (scratch_caseThreeLambda lamMinus lamPlus e)
        (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
          (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r := by
  unfold scratch_caseThreeSlotNat
  rw [scratch_caseThreeSlotIndex_encode]

theorem scratch_caseThree_sum_range36_reindex {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ) {R : Type*} [AddCommMonoid R]
    (F : SequencePair × Fin 2 → R) :
    ∑ b ∈ scratch_caseThreeB, F (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) =
      ∑ k : Fin 6, ∑ e : Fin 2, ∑ r : Fin 3,
        F (scratch_caseThreeExactSlotOf (scratch_caseThreeLambda lamMinus lamPlus e)
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r) := by
  classical
  calc
    ∑ b ∈ scratch_caseThreeB, F (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) =
        ∑ b : Fin 36, F (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) := by
      simpa [scratch_caseThreeB] using
        (Finset.sum_range (fun b : ℕ => F (scratch_caseThreeSlotNat γ i lamMinus lamPlus b)))
    _ = ∑ ker : (Fin 6 × Fin 2) × Fin 3,
        F (scratch_caseThreeExactSlotOf (scratch_caseThreeLambda lamMinus lamPlus ker.1.2)
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm ker.1.1)) ker.2) := by
      let e12 : Fin 6 × Fin 2 ≃ Fin 12 := finProdFinEquiv
      let E : (Fin 6 × Fin 2) × Fin 3 ≃ Fin 36 :=
        (Equiv.prodCongr e12 (Equiv.refl (Fin 3))).trans finProdFinEquiv
      symm
      refine Fintype.sum_equiv E
        (fun ker => F (scratch_caseThreeExactSlotOf
          (scratch_caseThreeLambda lamMinus lamPlus ker.1.2)
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm ker.1.1)) ker.2))
        (fun b => F (scratch_caseThreeSlotNat γ i lamMinus lamPlus b)) ?_
      intro ker
      apply congrArg F
      dsimp [E, e12, Equiv.prodCongr, finProdFinEquiv]
      convert
        (scratch_caseThreeSlotNat_encode γ i lamMinus lamPlus ker.1.1 ker.1.2 ker.2).symm using 1
      congr 1
      change ker.2.1 + 3 * (ker.1.2.1 + 2 * ker.1.1.1) =
        (ker.1.1.1 * 2 + ker.1.2.1) * 3 + ker.2.1
      omega
    _ = ∑ k : Fin 6, ∑ e : Fin 2, ∑ r : Fin 3,
        F (scratch_caseThreeExactSlotOf (scratch_caseThreeLambda lamMinus lamPlus e)
          (caseTwoOccurrence (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) r) := by
      simp only [Fintype.sum_prod_type]

open scoped BigOperators ENNReal Real FourierTransform

open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN

/-- The lower central rho scale is within the exact `2 Δ` pair-distance budget
of each basic shifted H scale.  The slack comes from the `+1` in
`geometricDelta`: the possible extra backwards shift is paid for by the
same-index scale-pair distance. -/
theorem scratch_caseThree_lambdaMinus_hKernelShiftedScale_distance {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (l : ℤ)
    (hl : l.natAbs ≤ geometricDelta γ) (m r : Fin 2) :
    SequenceDistance (fun j => γ.scales i 1 (j + l - 1))
      (aux_hKernelShiftedScale γ i m r) ≤
        ((2 * geometricDelta γ : ℕ) : WithTop ℕ) := by
  let d : ℕ := geometricDelta γ
  let δ : ℕ := (sequencePairDistance (γ.scales i)).untop
    (ne_of_lt (γ.finite_distance i))
  have hpair : sequencePairDistance (γ.scales i) = (δ : WithTop ℕ) := by
    exact (WithTop.coe_untop _ (ne_of_lt (γ.finite_distance i))).symm
  have hδ : δ + 1 ≤ d := by
    have h := aux_sequencePairDistance_succ_le_geometricDelta γ i
    have h' : ((δ + 1 : ℕ) : WithTop ℕ) ≤ (d : WithTop ℕ) := by
      simpa [d, hpair] using h
    exact WithTop.coe_le_coe.mp h'
  have hl' : l.natAbs ≤ d := by simpa [d] using hl
  have hlbounds : -(d : ℤ) ≤ l ∧ l ≤ d := (aux_int_natAbs_le_iff l d).mp hl'
  have hbase : WithinSequenceDistance (γ.scales i 1) (γ.scales i 0) δ := by
    apply aux_withinSequenceDistance_of_sequenceDistance_le (γ.scales_spaced i 1)
    rw [sequenceDistance_comm]
    simpa [sequencePairDistance] using hpair.le
  apply aux_sequenceDistance_le_of_within
  intro j
  fin_cases r
  · constructor
    · change γ.scales i 1 (j - ((2 * d : ℕ) : ℤ) + l - 1) ≤
        γ.scales i 0 (j + (m : ℤ) - 1)
      calc
        γ.scales i 1 (j - ((2 * d : ℕ) : ℤ) + l - 1) ≤
            γ.scales i 1 (j + (m : ℤ) - 1 - (δ : ℤ)) := by
          apply aux_spacedSequence_monotone (γ.scales_spaced i 1)
          omega
        _ ≤ γ.scales i 0 (j + (m : ℤ) - 1) := (hbase _).1
    · change γ.scales i 0 (j + (m : ℤ) - 1) ≤
        γ.scales i 1 (j + ((2 * d : ℕ) : ℤ) + l - 1)
      calc
        γ.scales i 0 (j + (m : ℤ) - 1) ≤
            γ.scales i 1 (j + (m : ℤ) - 1 + (δ : ℤ)) := (hbase _).2
        _ ≤ γ.scales i 1 (j + ((2 * d : ℕ) : ℤ) + l - 1) := by
          apply aux_spacedSequence_monotone (γ.scales_spaced i 1)
          omega
  · constructor
    · change γ.scales i 1 (j - ((2 * d : ℕ) : ℤ) + l - 1) ≤
        γ.scales i 1 (j + (m : ℤ) - 1)
      apply aux_spacedSequence_monotone (γ.scales_spaced i 1)
      omega
    · change γ.scales i 1 (j + (m : ℤ) - 1) ≤
        γ.scales i 1 (j + ((2 * d : ℕ) : ℤ) + l - 1)
      apply aux_spacedSequence_monotone (γ.scales_spaced i 1)
      omega

/-- Both central Case 3 rho scales have the exact `2 Δ` comparison with every
basic shifted H scale.  The `e = 0` case is `λ₋`; `e = 1` is `λ₊`. -/
theorem scratch_caseThree_centralLambda_hKernelShiftedScale_distance {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (l : ℤ)
    (hl : l.natAbs ≤ geometricDelta γ) (e m r : Fin 2) :
    SequenceDistance (fun j => γ.scales i 1 (j + l + (e : ℤ) - 1))
      (aux_hKernelShiftedScale γ i m r) ≤
        ((2 * geometricDelta γ : ℕ) : WithTop ℕ) := by
  let d : ℕ := geometricDelta γ
  let δ : ℕ := (sequencePairDistance (γ.scales i)).untop
    (ne_of_lt (γ.finite_distance i))
  have hpair : sequencePairDistance (γ.scales i) = (δ : WithTop ℕ) := by
    exact (WithTop.coe_untop _ (ne_of_lt (γ.finite_distance i))).symm
  have hδ : δ + 1 ≤ d := by
    have h := aux_sequencePairDistance_succ_le_geometricDelta γ i
    have h' : ((δ + 1 : ℕ) : WithTop ℕ) ≤ (d : WithTop ℕ) := by
      simpa [d, hpair] using h
    exact WithTop.coe_le_coe.mp h'
  have hl' : l.natAbs ≤ d := by simpa [d] using hl
  have hlbounds : -(d : ℤ) ≤ l ∧ l ≤ d := (aux_int_natAbs_le_iff l d).mp hl'
  have hbase : WithinSequenceDistance (γ.scales i 1) (γ.scales i 0) δ := by
    apply aux_withinSequenceDistance_of_sequenceDistance_le (γ.scales_spaced i 1)
    rw [sequenceDistance_comm]
    simpa [sequencePairDistance] using hpair.le
  apply aux_sequenceDistance_le_of_within
  intro j
  fin_cases r
  · constructor
    · change γ.scales i 1 (j - ((2 * d : ℕ) : ℤ) + l + (e : ℤ) - 1) ≤
        γ.scales i 0 (j + (m : ℤ) - 1)
      calc
        γ.scales i 1 (j - ((2 * d : ℕ) : ℤ) + l + (e : ℤ) - 1) ≤
            γ.scales i 1 (j + (m : ℤ) - 1 - (δ : ℤ)) := by
          apply aux_spacedSequence_monotone (γ.scales_spaced i 1)
          omega
        _ ≤ γ.scales i 0 (j + (m : ℤ) - 1) := (hbase _).1
    · change γ.scales i 0 (j + (m : ℤ) - 1) ≤
        γ.scales i 1 (j + ((2 * d : ℕ) : ℤ) + l + (e : ℤ) - 1)
      calc
        γ.scales i 0 (j + (m : ℤ) - 1) ≤
            γ.scales i 1 (j + (m : ℤ) - 1 + (δ : ℤ)) := (hbase _).2
        _ ≤ γ.scales i 1 (j + ((2 * d : ℕ) : ℤ) + l + (e : ℤ) - 1) := by
          apply aux_spacedSequence_monotone (γ.scales_spaced i 1)
          omega
  · constructor
    · change γ.scales i 1 (j - ((2 * d : ℕ) : ℤ) + l + (e : ℤ) - 1) ≤
        γ.scales i 1 (j + (m : ℤ) - 1)
      apply aux_spacedSequence_monotone (γ.scales_spaced i 1)
      omega
    · change γ.scales i 1 (j + (m : ℤ) - 1) ≤
        γ.scales i 1 (j + ((2 * d : ℕ) : ℤ) + l + (e : ℤ) - 1)
      apply aux_spacedSequence_monotone (γ.scales_spaced i 1)
      omega

theorem scratch_caseThree_centralLambda_spaced {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (l : ℤ) (e : Fin 2) :
    SpacedSequence (fun j => γ.scales i 1 (j + l + (e : ℤ) - 1)) := by
  convert shift_mem_A (γ.scales_spaced i 1) (l + (e : ℤ) - 1) using 1
  funext j
  ring

/-- The same exact `2 Δ` comparison is stable under the maximum scale used
in the orientation-zero H package. -/
theorem scratch_caseThree_centralLambda_hKernelMaxScale_distance {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (l : ℤ)
    (hl : l.natAbs ≤ geometricDelta γ) (e m : Fin 2) :
    SequenceDistance (fun j => γ.scales i 1 (j + l + (e : ℤ) - 1))
      (aux_hKernelMaxScale γ i m) ≤
        ((2 * geometricDelta γ : ℕ) : WithTop ℕ) := by
  let lam : ℤ → ℝ := fun j => γ.scales i 1 (j + l + (e : ℤ) - 1)
  let d : ℕ := geometricDelta γ
  have hlam : SpacedSequence lam := by
    simpa [lam] using scratch_caseThree_centralLambda_spaced γ i l e
  have hzero : WithinSequenceDistance lam (aux_hKernelShiftedScale γ i m 0) (2 * d) := by
    apply aux_withinSequenceDistance_of_sequenceDistance_le hlam
    simpa [lam, d] using
      scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e m 0
  have hone : WithinSequenceDistance lam (aux_hKernelShiftedScale γ i m 1) (2 * d) := by
    apply aux_withinSequenceDistance_of_sequenceDistance_le hlam
    simpa [lam, d] using
      scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e m 1
  apply aux_sequenceDistance_le_of_within
  intro j
  constructor
  · change lam (j - ((2 * d : ℕ) : ℤ)) ≤
      max (aux_hKernelShiftedScale γ i m 0 j) (aux_hKernelShiftedScale γ i m 1 j)
    exact (hzero j).1.trans (le_max_left _ _)
  · change max (aux_hKernelShiftedScale γ i m 0 j) (aux_hKernelShiftedScale γ i m 1 j) ≤
      lam (j + ((2 * d : ℕ) : ℤ))
    exact max_le (hzero j).2 (hone j).2

open scoped BigOperators ENNReal Real FourierTransform

open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.Preliminaries.Notation
open Codex.Preliminaries.BumpsAndEstimates
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN
open aux_caseTwo.ScratchCase2Witness

private theorem scratch_caseThree_centralLambda_hKernel_coordinate_distance {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (l : ℤ)
    (hl : l.natAbs ≤ geometricDelta γ) (e : Fin 2)
    (q : SequencePair × Fin 2) (hq : q ∈ aux_hKernelGaussianMultiset γ i) (s : Fin 2) :
    SequenceDistance (fun j => γ.scales i 1 (j + l + (e : ℤ) - 1)) (q.1 s) ≤
      ((2 * geometricDelta γ : ℕ) : WithTop ℕ) := by
  classical
  by_cases horientation : γ.orientation i = 0
  · simp only [aux_hKernelGaussianMultiset, if_pos horientation,
      Multiset.mem_add, Multiset.mem_singleton] at hq
    rcases hq with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl)
    · fin_cases s <;>
        simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelMaxScale_distance γ i l hl e 0
    · fin_cases s
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelMaxScale_distance γ i l hl e 0
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelMaxScale_distance γ i l hl e 1
    · fin_cases s
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelMaxScale_distance γ i l hl e 1
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelMaxScale_distance γ i l hl e 0
    · fin_cases s <;>
        simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelMaxScale_distance γ i l hl e 1
    · fin_cases s
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 0 0
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 0 1
    · fin_cases s
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 1 0
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 1 1
  · simp only [aux_hKernelGaussianMultiset, if_neg horientation,
      Multiset.mem_add, Multiset.mem_singleton] at hq
    rcases hq with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl)
    · fin_cases s <;>
        simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 0 1
    · fin_cases s
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 0 1
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 1 1
    · fin_cases s
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 1 1
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 0 1
    · fin_cases s <;>
        simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 1 1
    · fin_cases s
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 0 0
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 0 1
    · fin_cases s
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 1 0
      · simpa [aux_sequencePairOf] using
          scratch_caseThree_centralLambda_hKernelShiftedScale_distance γ i l hl e 1 1

/-- The corrected Case 3 decoder preserves a common pair-distance bound.  In
the orientation-one active branch this uses `(max λ q₀,q₁)`, rather than the
Case 2 decoder's padded `q`. -/
private theorem scratch_caseThreeExactSlotOf_distance_of_bounds
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (R : ℕ)
    (hlamq : ∀ s : Fin 2, SequenceDistance lam (q.1 s) ≤ (R : WithTop ℕ))
    (hqq : SequenceDistance (q.1 0) (q.1 1) ≤ (R : WithTop ℕ)) (r : Fin 3) :
    sequencePairDistance (scratch_caseThreeExactSlotOf lam q r).1 ≤ (R : WithTop ℕ) := by
  have hlamq₀ : WithinSequenceDistance lam (q.1 0) R :=
    aux_withinSequenceDistance_of_sequenceDistance_le hlam (hlamq 0)
  have hlamq₁ : WithinSequenceDistance lam (q.1 1) R :=
    aux_withinSequenceDistance_of_sequenceDistance_le hlam (hlamq 1)
  have hq₀lam : WithinSequenceDistance (q.1 0) lam R :=
    aux_withinSequenceDistance_symm.mp hlamq₀
  have hq₁lam : WithinSequenceDistance (q.1 1) lam R :=
    aux_withinSequenceDistance_symm.mp hlamq₁
  have hq₀q₁ : WithinSequenceDistance (q.1 0) (q.1 1) R :=
    aux_withinSequenceDistance_of_sequenceDistance_le (hq 0) hqq
  have hq₁q₀ : WithinSequenceDistance (q.1 1) (q.1 0) R :=
    aux_withinSequenceDistance_symm.mp hq₀q₁
  have hfirst : WithinSequenceDistance (q.1 0)
      (scratch_caseThreeLambdaMaxSecondScale lam q) R := by
    intro j
    constructor
    · exact (hq₀lam j).1.trans (le_max_left _ _)
    · change max (lam j) (q.1 1 j) ≤ q.1 0 (j + (R : ℤ))
      exact max_le (hq₀lam j).2 (hq₀q₁ j).2
  have hsecond : WithinSequenceDistance lam (scratch_caseThreeMaxScale q) R := by
    intro j
    constructor
    · exact (hlamq₀ j).1.trans (le_max_left _ _)
    · change max (q.1 0 j) (q.1 1 j) ≤ lam (j + (R : ℤ))
      exact max_le (hlamq₀ j).2 (hlamq₁ j).2
  have huone : WithinSequenceDistance (q.1 1)
      (scratch_caseThreeLambdaMaxFirstScale lam q) R := by
    intro j
    constructor
    · exact (hq₁lam j).1.trans (le_max_left _ _)
    · change max (lam j) (q.1 0 j) ≤ q.1 1 (j + (R : ℤ))
      exact max_le (hq₁lam j).2 (hq₁q₀ j).2
  unfold sequencePairDistance
  by_cases hqu : q.2 = 0
  · by_cases hr0 : r = 0
    · simp only [scratch_caseThreeExactSlotOf, dif_pos hqu, if_pos hr0,
        aux_sequencePairOf]
      exact aux_sequenceDistance_le_of_within hfirst
    · by_cases hr1 : r = 1
      · simp only [scratch_caseThreeExactSlotOf, dif_pos hqu, if_neg hr0, if_pos hr1,
          aux_sequencePairOf]
        exact aux_sequenceDistance_le_of_within hsecond
      · simp only [scratch_caseThreeExactSlotOf, dif_pos hqu, if_neg hr0, if_neg hr1,
          aux_sequencePairOf]
        exact aux_sequenceDistance_le_of_within hsecond
  · by_cases hr0 : r = 0
    · simp only [scratch_caseThreeExactSlotOf, dif_neg hqu, if_pos hr0,
        aux_sequencePairOf]
      rw [sequenceDistance_comm]
      exact aux_sequenceDistance_le_of_within huone
    · simpa [scratch_caseThreeExactSlotOf, hqu, hr0] using hqq

private theorem scratch_caseThree_hKernel_pair_distance {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k)
    (q : SequencePair × Fin 2) (hq : q ∈ aux_hKernelGaussianMultiset γ i) :
    SequenceDistance (q.1 0) (q.1 1) ≤
      ((2 * geometricDelta γ : ℕ) : WithTop ℕ) := by
  let a : ℤ → ℝ := γ.scales i 1
  let d : ℕ := geometricDelta γ
  have hvalid := aux_hKernelGaussianMultiset_valid γ i q hq
  have hq₀a : SequenceDistance (q.1 0) a ≤ (d : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    simpa [a, d] using hvalid.1.2
  have haq₁ : SequenceDistance a (q.1 1) ≤ (d : WithTop ℕ) := by
    simpa [a, d] using hvalid.2.2
  calc
    SequenceDistance (q.1 0) (q.1 1) ≤
        SequenceDistance (q.1 0) a + SequenceDistance a (q.1 1) :=
      sequenceDistance_triangle _ _ _
    _ ≤ (d : WithTop ℕ) + (d : WithTop ℕ) := add_le_add hq₀a haq₁
    _ = ((2 * d : ℕ) : WithTop ℕ) := by
      norm_cast
      omega

/-- Every exact corrected Case 3 slot has base pair-distance at most `2 Δ`. -/
theorem scratch_caseThreeExactSlotOf_distance_bound {n : ℕ}
    (γ : GeometricParameters n) (ι : MultiplierIndex γ) (i : Fin γ.k)
    (hcentral : ι.1.2.natAbs ≤ geometricDelta γ) (e : Fin 2)
    (q : SequencePair × Fin 2) (hq : q ∈ aux_hKernelGaussianMultiset γ i) (r : Fin 3) :
    sequencePairDistance
      (scratch_caseThreeExactSlotOf
        (scratch_caseThreeLambda (scratch_caseThreeLambdaMinus γ ι i)
          (scratch_caseThreeLambdaPlus γ ι i) e) q r).1 ≤
        ((2 * geometricDelta γ : ℕ) : WithTop ℕ) := by
  let lam : ℤ → ℝ := scratch_caseThreeLambda
    (scratch_caseThreeLambdaMinus γ ι i) (scratch_caseThreeLambdaPlus γ ι i) e
  have hlam : SpacedSequence lam := by
    fin_cases e
    · simpa [lam, scratch_caseThreeLambda] using scratch_caseThreeLambdaMinus_spaced γ ι i
    · simpa [lam, scratch_caseThreeLambda] using scratch_caseThreeLambdaPlus_spaced γ ι i
  have hlamq : ∀ s : Fin 2, SequenceDistance lam (q.1 s) ≤
      ((2 * geometricDelta γ : ℕ) : WithTop ℕ) := by
    intro s
    fin_cases e
    · change SequenceDistance (scratch_caseThreeLambdaMinus γ ι i) (q.1 s) ≤ _
      convert scratch_caseThree_centralLambda_hKernel_coordinate_distance
        γ i ι.1.2 hcentral 0 q hq s using 1
      congr 1
      funext j
      simp [scratch_caseThreeLambdaMinus]
    · change SequenceDistance (scratch_caseThreeLambdaPlus γ ι i) (q.1 s) ≤ _
      convert scratch_caseThree_centralLambda_hKernel_coordinate_distance
        γ i ι.1.2 hcentral 1 q hq s using 1
      congr 1
      funext j
      simp [scratch_caseThreeLambdaPlus]
  have hqq := scratch_caseThree_hKernel_pair_distance γ i q hq
  simpa [lam] using scratch_caseThreeExactSlotOf_distance_of_bounds lam hlam q (by
    intro s
    have hvalid := aux_hKernelGaussianMultiset_valid γ i q hq
    fin_cases s
    · exact hvalid.1.1
    · exact hvalid.2.1) (2 * geometricDelta γ) hlamq hqq r

theorem scratch_caseThreeSlotNat_distance_bound {n : ℕ}
    (γ : GeometricParameters n) (ι : MultiplierIndex γ) (i : Fin γ.k)
    (hcentral : ι.1.2.natAbs ≤ geometricDelta γ) (b : ℕ) :
    sequencePairDistance
      (scratch_caseThreeSlotNat γ i (scratch_caseThreeLambdaMinus γ ι i)
        (scratch_caseThreeLambdaPlus γ ι i) b).1 ≤
        ((2 * geometricDelta γ : ℕ) : WithTop ℕ) := by
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let k : Fin P.card := Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm
    (scratch_caseThreeSlotIndex b).1.1
  let q : SequencePair × Fin 2 := caseTwoOccurrence P k
  let e : Fin 2 := (scratch_caseThreeSlotIndex b).1.2
  have hqmem : q ∈ P := caseTwoOccurrence_mem P k
  have hslot := scratch_caseThreeExactSlotOf_distance_bound γ ι i hcentral e q
    (by simpa [P] using hqmem) (scratch_caseThreeSlotIndex b).2
  simpa [scratch_caseThreeSlotNat, P, k, q, e] using hslot

theorem scratch_caseThreeScales_distance_bound {n : ℕ}
    (γ : GeometricParameters n) (ι : MultiplierIndex γ) (i : Fin γ.k)
    (hcentral : ι.1.2.natAbs ≤ geometricDelta γ) (b : ℕ) (m : Fin 2 → ℕ) :
    sequencePairDistance
      (scratch_caseThreeScales γ i (scratch_caseThreeLambdaMinus γ ι i)
        (scratch_caseThreeLambdaPlus γ ι i) b m) ≤
      (C_gaussianDominationCombinedDistance : WithTop ℕ) *
        ((geometricDelta γ + aux_natPairWeight m : ℕ) : WithTop ℕ) := by
  let lamMinus : ℤ → ℝ := scratch_caseThreeLambdaMinus γ ι i
  let lamPlus : ℤ → ℝ := scratch_caseThreeLambdaPlus γ ι i
  let p : SequencePair := (scratch_caseThreeSlotNat γ i lamMinus lamPlus b).1
  let d : ℕ := geometricDelta γ
  have hminus : SpacedSequence lamMinus := by
    simpa [lamMinus] using scratch_caseThreeLambdaMinus_spaced γ ι i
  have hplus : SpacedSequence lamPlus := by
    simpa [lamPlus] using scratch_caseThreeLambdaPlus_spaced γ ι i
  have hp₀ : SpacedSequence (p 0) := by
    simpa [p] using scratch_caseThreeSlotNat_spaced γ i lamMinus lamPlus hminus hplus b 0
  have hp₁ : SpacedSequence (p 1) := by
    simpa [p] using scratch_caseThreeSlotNat_spaced γ i lamMinus lamPlus hminus hplus b 1
  have hbase : SequenceDistance (p 0) (p 1) ≤ ((2 * d : ℕ) : WithTop ℕ) := by
    simpa [sequencePairDistance, p, d] using
      scratch_caseThreeSlotNat_distance_bound γ ι i hcentral b
  have hleft : SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j) (p 0) ≤
      ((m 0 : ℕ) : WithTop ℕ) := by
    rw [sequenceDistance_comm]
    have hdist := sequenceDistance_pow_two_smul_le hp₀ ((m 0 : ℕ) : ℤ)
    simpa [zpow_natCast, Int.natAbs_natCast] using hdist
  have hright : SequenceDistance (p 1) (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤
      ((m 1 : ℕ) : WithTop ℕ) := by
    have hdist := sequenceDistance_pow_two_smul_le hp₁ ((m 1 : ℕ) : ℤ)
    simpa [zpow_natCast, Int.natAbs_natCast] using hdist
  change SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j)
      (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤ _
  calc
    SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j)
        (fun j => (2 : ℝ) ^ (m 1) * p 1 j) ≤
        SequenceDistance (fun j => (2 : ℝ) ^ (m 0) * p 0 j) (p 0) +
          SequenceDistance (p 0) (fun j => (2 : ℝ) ^ (m 1) * p 1 j) :=
      sequenceDistance_triangle _ _ _
    _ ≤ (m 0 : WithTop ℕ) +
          (SequenceDistance (p 0) (p 1) +
            SequenceDistance (p 1) (fun j => (2 : ℝ) ^ (m 1) * p 1 j)) := by
      gcongr
      exact sequenceDistance_triangle _ _ _
    _ ≤ (m 0 : WithTop ℕ) + ((2 * d : ℕ) : WithTop ℕ) + m 1 := by
      simpa [add_assoc] using add_le_add hbase hright
    _ ≤ (C_gaussianDominationCombinedDistance : WithTop ℕ) *
        ((d + aux_natPairWeight m : ℕ) : WithTop ℕ) := by
      norm_num [C_gaussianDominationCombinedDistance]
      norm_cast
      simp only [aux_natPairWeight]
      omega

open MeasureTheory
open scoped BigOperators ENNReal Real FourierTransform

open Codex.Preliminaries.Notation
open Codex.Preliminaries.Gaussians
open Codex.Preliminaries.BumpsAndEstimates
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN

noncomputable def scratch_caseThreeSlotTerm (lam : ℤ → ℝ)
    (q : SequencePair × Fin 2) (j : ℤ) (v : RealPlane) (r : Fin 3) : ℝ :=
  aux_kernelBracketProduct (scratch_caseThreeExactSlotOf lam q r) j v

theorem scratch_caseThreeSlotTerm_nonneg
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (j : ℤ) (v : RealPlane) (r : Fin 3) :
    0 ≤ scratch_caseThreeSlotTerm lam q j v r := by
  have hs := scratch_caseThreeExactSlotOf_spaced lam hlam q hq r
  unfold scratch_caseThreeSlotTerm
  exact aux_kernelBracketProduct_nonneg _ hs j v

private theorem scratch_caseThree_sum_fin3 (f : Fin 3 → ℝ) :
    (∑ r : Fin 3, f r) = f 0 + f 1 + f 2 := by
  simp [Fin.sum_univ_succ]
  ring

theorem scratch_caseThree_u0_output_le_slots
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s))
    (j : ℤ) (v : RealPlane) (hqu : q.2 = 0) :
    scaledBracketBump 2 (q.1 0 j) v.1 *
        scaledBracketBump 2 (max (lam j) (q.1 1 j)) v.2 +
      scaledBracketBump 2 (lam j) v.1 *
        scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 +
      scaledBracketBump 2 (lam j) ((v.1 + v.2) / Real.sqrt 2) *
        scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
          ((v.1 - v.2) / Real.sqrt 2) ≤
      ∑ r : Fin 3, scratch_caseThreeSlotTerm lam q j v r := by
  have h0 := scratch_caseThreeSlotTerm_nonneg lam hlam q hq j v 0
  have h1 := scratch_caseThreeSlotTerm_nonneg lam hlam q hq j v 1
  have h2 := scratch_caseThreeSlotTerm_nonneg lam hlam q hq j v 2
  have hW0 : W (0 : Fin 2) v = v := by simp [W]
  have hW1second : (W (1 : Fin 2) v).2 = -((v.1 - v.2) / Real.sqrt 2) := by
    simp [W]
    ring
  have hW1first : (W (1 : Fin 2) v).1 = (v.1 + v.2) / Real.sqrt 2 := by
    simp [W]
  have hterms :
      scratch_caseThreeSlotTerm lam q j v 0 =
        scaledBracketBump 2 (q.1 0 j) v.1 *
          scaledBracketBump 2 (max (lam j) (q.1 1 j)) v.2 ∧
      scratch_caseThreeSlotTerm lam q j v 1 =
        scaledBracketBump 2 (lam j) v.1 *
          scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 ∧
      scratch_caseThreeSlotTerm lam q j v 2 =
        scaledBracketBump 2 (lam j) ((v.1 + v.2) / Real.sqrt 2) *
          scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
            ((v.1 - v.2) / Real.sqrt 2) := by
    constructor
    · simp [scratch_caseThreeSlotTerm, scratch_caseThreeExactSlotOf, hqu,
        scratch_caseThreeLambdaMaxSecondScale, aux_kernelBracketProduct,
        aux_sequencePairOf, hW0]
    constructor
    · simp [scratch_caseThreeSlotTerm, scratch_caseThreeExactSlotOf, hqu,
        scratch_caseThreeMaxScale, aux_kernelBracketProduct, aux_sequencePairOf, hW0]
    · simp [scratch_caseThreeSlotTerm, scratch_caseThreeExactSlotOf, hqu,
        scratch_caseThreeMaxScale, aux_kernelBracketProduct, aux_sequencePairOf,
        hW1first, hW1second,
        aux_caseTwo.ScratchCase2Fourier.scratch_scaledBracketBump_neg]
  rw [scratch_caseThree_sum_fin3]
  rw [← hterms.1, ← hterms.2.1, ← hterms.2.2]

theorem scratch_caseThree_u1_output_le_slots
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s))
    (j : ℤ) (v : RealPlane) (hqu : q.2 = 1) :
    scaledBracketBump 2 (max (lam j) (q.1 0 j)) (W 1 v).1 *
        scaledBracketBump 2 (q.1 1 j) (W 1 v).2 ≤
      ∑ r : Fin 3, scratch_caseThreeSlotTerm lam q j v r := by
  have h0 := scratch_caseThreeSlotTerm_nonneg lam hlam q hq j v 0
  have h1 := scratch_caseThreeSlotTerm_nonneg lam hlam q hq j v 1
  have h2 := scratch_caseThreeSlotTerm_nonneg lam hlam q hq j v 2
  have hne : q.2 ≠ 0 := by omega
  have hslot0 : scratch_caseThreeSlotTerm lam q j v 0 =
      scaledBracketBump 2 (max (lam j) (q.1 0 j)) (W 1 v).1 *
        scaledBracketBump 2 (q.1 1 j) (W 1 v).2 := by
    simp [scratch_caseThreeSlotTerm, scratch_caseThreeExactSlotOf, hne,
      scratch_caseThreeLambdaMaxFirstScale, aux_kernelBracketProduct,
      aux_sequencePairOf]
  rw [scratch_caseThree_sum_fin3, ← hslot0]
  nlinarith

private theorem scratch_caseThree_u0_coefficient_nonneg :
    0 ≤ 9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
  have htri : 0 ≤ C_bumpTriangle 1 1 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  positivity

private theorem scratch_caseThree_u1_coefficient_le_u0 :
    2 * C_twoBumpEstimate 2 2 ≤
      9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by
  have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  have hscalar : (2 : ℝ) ≤ 9 * C_bumpTriangle 1 1 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  calc
    2 * C_twoBumpEstimate 2 2 ≤
        (9 * C_bumpTriangle 1 1 2 2) * C_twoBumpEstimate 2 2 :=
      mul_le_mul_of_nonneg_right hscalar htwo
    _ = 9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2 := by ring

/-- A single H-package occurrence and a single central rho scale are bounded by its
three exact Case-3 slots, uniformly in the occurrence orientation. -/
theorem scratch_caseThree_occurrence_to_slots
    (lam : ℤ → ℝ) (hlam : SpacedSequence lam) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s))
    (j : ℤ) (v : RealPlane) :
    (∫ p : ℝ, scaledBracketBump 2 (lam j) p *
      aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
      (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
        ∑ r : Fin 3, scratch_caseThreeSlotTerm lam q j v r := by
  let S : ℝ := ∑ r : Fin 3, scratch_caseThreeSlotTerm lam q j v r
  have hlamj : 0 < lam j := (hlam j).1
  have hS : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro r _
    exact scratch_caseThreeSlotTerm_nonneg lam hlam q hq j v r
  have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  by_cases hqu : q.2 = 0
  · have hraw := scratch_caseThree_u0_threeSlot q j v (lam j) hqu (hq 0) (hq 1) hlamj
    have hslots := scratch_caseThree_u0_output_le_slots lam hlam q hq j v hqu
    have hW1first : (W (1 : Fin 2) v).1 = (v.1 + v.2) / Real.sqrt 2 := by
      simp [W]
    have hW1second : (W (1 : Fin 2) v).2 =
        -((v.1 - v.2) / Real.sqrt 2) := by
      simp [W]
      ring
    have hmain :
        (∫ p : ℝ, scaledBracketBump 2 (lam j) p *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
          (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
            (scaledBracketBump 2 (q.1 0 j) v.1 *
                scaledBracketBump 2 (max (lam j) (q.1 1 j)) v.2 +
              scaledBracketBump 2 (lam j) v.1 *
                scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 +
              scaledBracketBump 2 (lam j) ((v.1 + v.2) / Real.sqrt 2) *
                scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
                  ((v.1 - v.2) / Real.sqrt 2)) := by
      simpa [hW1first, hW1second,
        aux_caseTwo.ScratchCase2Fourier.scratch_scaledBracketBump_neg,
        mul_assoc] using hraw
    have hcoef := scratch_caseThree_u0_coefficient_nonneg
    calc
      (∫ p : ℝ, scaledBracketBump 2 (lam j) p *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
          (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
            (scaledBracketBump 2 (q.1 0 j) v.1 *
                scaledBracketBump 2 (max (lam j) (q.1 1 j)) v.2 +
              scaledBracketBump 2 (lam j) v.1 *
                scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j)) v.2 +
              scaledBracketBump 2 (lam j) ((v.1 + v.2) / Real.sqrt 2) *
                scaledBracketBump 2 (max (q.1 0 j) (q.1 1 j))
                  ((v.1 - v.2) / Real.sqrt 2)) := hmain
      _ ≤ (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) * S :=
        mul_le_mul_of_nonneg_left hslots hcoef
  · have hqu' : q.2 = 1 := Fin.eq_one_of_ne_zero q.2 hqu
    have hraw := scratch_caseThree_u1_kernelSlot q j v (lam j) hqu' (hq 0) (hq 1) hlamj
    have hslots := scratch_caseThree_u1_output_le_slots lam hlam q hq j v hqu'
    have hprod : 0 ≤
        scaledBracketBump 2 (max (lam j) (q.1 0 j)) (W 1 v).1 *
          scaledBracketBump 2 (q.1 1 j) (W 1 v).2 := by
      exact mul_nonneg
        (aux_scaledBracketBump_nonneg 2 (lt_max_of_lt_right (hq 0 j).1) _)
        (aux_scaledBracketBump_nonneg 2 (hq 1 j).1 _)
    calc
      (∫ p : ℝ, scaledBracketBump 2 (lam j) p *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
          (2 * C_twoBumpEstimate 2 2) *
            (scaledBracketBump 2 (max (lam j) (q.1 0 j)) (W 1 v).1 *
              scaledBracketBump 2 (q.1 1 j) (W 1 v).2) := by
        simpa [mul_assoc] using hraw
      _ ≤ (2 * C_twoBumpEstimate 2 2) * S :=
        mul_le_mul_of_nonneg_left hslots (mul_nonneg (by norm_num) htwo)
      _ ≤ (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) * S :=
        mul_le_mul_of_nonneg_right scratch_caseThree_u1_coefficient_le_u0 hS

/-- The two central rho scales for one H-package occurrence are controlled by
the six decoder slots attached to that occurrence. -/
theorem scratch_caseThree_twoLambda_occurrence_to_slots
    (lamMinus lamPlus : ℤ → ℝ) (hminus : SpacedSequence lamMinus)
    (hplus : SpacedSequence lamPlus) (q : SequencePair × Fin 2)
    (hq : ∀ s : Fin 2, SpacedSequence (q.1 s)) (j : ℤ) (v : RealPlane) :
    (∫ p : ℝ,
      (scaledBracketBump 2 (lamMinus j) p + scaledBracketBump 2 (lamPlus j) p) *
        aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) ≤
      (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
        ∑ e : Fin 2, ∑ r : Fin 3,
          scratch_caseThreeSlotTerm (scratch_caseThreeLambda lamMinus lamPlus e) q j v r := by
  let D : ℝ := 9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2
  let Sminus : ℝ := ∑ r : Fin 3, scratch_caseThreeSlotTerm lamMinus q j v r
  let Splus : ℝ := ∑ r : Fin 3, scratch_caseThreeSlotTerm lamPlus q j v r
  have hintMinus := scratch_caseThree_weighted_kernel_integrable q j v (lamMinus j)
    (hq 0) (hq 1) ((hminus j).1)
  have hintPlus := scratch_caseThree_weighted_kernel_integrable q j v (lamPlus j)
    (hq 0) (hq 1) ((hplus j).1)
  have hminusBound := scratch_caseThree_occurrence_to_slots lamMinus hminus q hq j v
  have hplusBound := scratch_caseThree_occurrence_to_slots lamPlus hplus q hq j v
  have hsum : (∑ e : Fin 2, ∑ r : Fin 3,
      scratch_caseThreeSlotTerm (scratch_caseThreeLambda lamMinus lamPlus e) q j v r) =
      Sminus + Splus := by
    simp [Sminus, Splus, scratch_caseThreeLambda, Fin.sum_univ_succ]
  have hintegral :
      (∫ p : ℝ,
        (scaledBracketBump 2 (lamMinus j) p + scaledBracketBump 2 (lamPlus j) p) *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) =
        ∫ p : ℝ, scaledBracketBump 2 (lamMinus j) p *
            aux_kernelBracketProduct q j (v.1 - p, v.2 - p) +
          scaledBracketBump 2 (lamPlus j) p *
            aux_kernelBracketProduct q j (v.1 - p, v.2 - p) := by
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  rw [hintegral, integral_add hintMinus hintPlus]
  calc
    (∫ p : ℝ, scaledBracketBump 2 (lamMinus j) p *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p)) +
        ∫ p : ℝ, scaledBracketBump 2 (lamPlus j) p *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p) ≤ D * Sminus + D * Splus :=
      add_le_add (by simpa [D, Sminus] using hminusBound)
        (by simpa [D, Splus] using hplusBound)
    _ = D * (Sminus + Splus) := by ring
    _ = _ := by rw [hsum]

private theorem scratch_caseThree_multiset_sum_eq_occurrence_sum
    {R : Type*} [AddCommMonoid R] (P : Multiset (SequencePair × Fin 2))
    (F : SequencePair × Fin 2 → R) :
    (P.map F).sum = ∑ k : Fin P.card,
      F (aux_caseTwo.ScratchCase2Witness.caseTwoOccurrence P k) := by
  rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem]
  let e : Fin P.card ≃ Fin P.toList.length :=
    finCongr (Multiset.length_toList P).symm
  symm
  refine Fintype.sum_equiv e
    (fun k => F (aux_caseTwo.ScratchCase2Witness.caseTwoOccurrence P k))
    (fun l => F (P.toList.get l)) ?_
  intro k
  simp [e, aux_caseTwo.ScratchCase2Witness.caseTwoOccurrence]

private theorem scratch_caseThree_multiset_slot_sum_reindex {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ)
    (j : ℤ) (v : RealPlane) :
    ((aux_hKernelGaussianMultiset γ i).map
      (fun q => ∑ e : Fin 2, ∑ r : Fin 3,
        scratch_caseThreeSlotTerm (scratch_caseThreeLambda lamMinus lamPlus e) q j v r)).sum =
      ∑ b ∈ scratch_caseThreeB,
        aux_kernelBracketProduct
          (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) j v := by
  classical
  rw [scratch_caseThree_multiset_sum_eq_occurrence_sum]
  have hsum :
      (∑ k : Fin 6, ∑ e : Fin 2, ∑ r : Fin 3,
        scratch_caseThreeSlotTerm (scratch_caseThreeLambda lamMinus lamPlus e)
          (aux_caseTwo.ScratchCase2Witness.caseTwoOccurrence
            (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) j v r) =
      ∑ k : Fin (aux_hKernelGaussianMultiset γ i).card, ∑ e : Fin 2, ∑ r : Fin 3,
        scratch_caseThreeSlotTerm (scratch_caseThreeLambda lamMinus lamPlus e)
          (aux_caseTwo.ScratchCase2Witness.caseTwoOccurrence
            (aux_hKernelGaussianMultiset γ i) k) j v r := by
    let e : Fin 6 ≃ Fin (aux_hKernelGaussianMultiset γ i).card :=
      finCongr (aux_hKernelGaussianMultiset_card γ i).symm
    refine Fintype.sum_equiv e
      (fun k => ∑ e : Fin 2, ∑ r : Fin 3,
        scratch_caseThreeSlotTerm (scratch_caseThreeLambda lamMinus lamPlus e)
          (aux_caseTwo.ScratchCase2Witness.caseTwoOccurrence
            (aux_hKernelGaussianMultiset γ i)
            (Fin.cast (aux_hKernelGaussianMultiset_card γ i).symm k)) j v r)
      (fun k => ∑ e : Fin 2, ∑ r : Fin 3,
        scratch_caseThreeSlotTerm (scratch_caseThreeLambda lamMinus lamPlus e)
          (aux_caseTwo.ScratchCase2Witness.caseTwoOccurrence
            (aux_hKernelGaussianMultiset γ i) k) j v r) ?_
    intro k
    simp [e]
  rw [← hsum]
  rw [scratch_caseThree_sum_range36_reindex γ i lamMinus lamPlus
    (fun s => aux_kernelBracketProduct s j v)]
  rfl

/-- The central-band convolution is reduced to the fixed 36-slot Case-3
decoder, before applying Gaussian domination to each slot. -/
theorem scratch_caseThree_preGaussian_bound {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (v : RealPlane) (hzero : ι.1.1 = 0) :
    |nMultiplier γ hkn ι i j v| ≤
      (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
        C_hKernelEstimateGaussianDomination *
        (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
        ∑ b ∈ scratch_caseThreeB,
          aux_kernelBracketProduct
            (scratch_caseThreeSlotNat γ i
              (scratch_caseThreeLambdaMinus γ ι i)
              (scratch_caseThreeLambdaPlus γ ι i) b) j v := by
  classical
  let P : Multiset (SequencePair × Fin 2) := aux_hKernelGaussianMultiset γ i
  let lamMinus : ℤ → ℝ := scratch_caseThreeLambdaMinus γ ι i
  let lamPlus : ℤ → ℝ := scratch_caseThreeLambdaPlus γ ι i
  let D : ℝ := 9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2
  let S : (SequencePair × Fin 2) → ℝ := fun q =>
    ∑ e : Fin 2, ∑ r : Fin 3,
      scratch_caseThreeSlotTerm (scratch_caseThreeLambda lamMinus lamPlus e) q j v r
  have hminus : SpacedSequence lamMinus := by
    simpa [lamMinus] using scratch_caseThreeLambdaMinus_spaced γ ι i
  have hplus : SpacedSequence lamPlus := by
    simpa [lamPlus] using scratch_caseThreeLambdaPlus_spaced γ ι i
  have hD : 0 ≤ D := scratch_caseThree_u0_coefficient_nonneg
  have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 2 := by
    rw [show C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity
  have hfour : 0 ≤ C_fourScaleGaussianKernel 2 := by
    have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 2) :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
    have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 2) :=
      (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
    unfold C_fourScaleGaussianKernel C_smoothDecay2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
      (mul_nonneg (by positivity) hsecond)
  have houter : (P.map fun q =>
      ∫ p : ℝ,
        (scaledBracketBump 2 (lamMinus j) p + scaledBracketBump 2 (lamPlus j) p) *
          aux_kernelBracketProduct q j (v.1 - p, v.2 - p)).sum ≤
      D * (P.map S).sum := by
    apply aux_caseTwo.scratch_multiset_sum_le_scaled
    intro q hq
    have hvalid := aux_hKernelGaussianMultiset_valid γ i q (by simpa [P] using hq)
    have hqsp : ∀ r : Fin 2, SpacedSequence (q.1 r) := by
      intro r
      fin_cases r
      · exact hvalid.1.1
      · exact hvalid.2.1
    simpa [S] using
      scratch_caseThree_twoLambda_occurrence_to_slots lamMinus lamPlus hminus hplus q hqsp j v
  have hraw := scratch_caseThree_outer_raw γ hkn ι i j v hzero
  have hraw' : |nMultiplier γ hkn ι i j v| ≤
      (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
        C_hKernelEstimateGaussianDomination *
        (P.map fun q =>
          ∫ p : ℝ,
            (scaledBracketBump 2 (lamMinus j) p + scaledBracketBump 2 (lamPlus j) p) *
              aux_kernelBracketProduct q j (v.1 - p, v.2 - p)).sum := by
    simpa [P, lamMinus, lamPlus, scratch_caseThreeLambdaMinus,
      scratch_caseThreeLambdaPlus] using hraw
  have hfactor : 0 ≤
      (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
        C_hKernelEstimateGaussianDomination :=
    mul_nonneg (mul_nonneg hstd hfour) aux_C_hKernelEstimateGaussianDomination_nonneg
  have hreindex : (P.map S).sum =
      ∑ b ∈ scratch_caseThreeB,
        aux_kernelBracketProduct
          (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) j v := by
    dsimp [P, S]
    exact scratch_caseThree_multiset_slot_sum_reindex γ i lamMinus lamPlus j v
  calc
    |nMultiplier γ hkn ι i j v| ≤
        (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
          C_hKernelEstimateGaussianDomination *
          (D * (P.map S).sum) :=
      hraw'.trans (mul_le_mul_of_nonneg_left houter hfactor)
    _ = (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
          C_hKernelEstimateGaussianDomination * D * (P.map S).sum := by ring
    _ = (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
          C_hKernelEstimateGaussianDomination * D *
          ∑ b ∈ scratch_caseThreeB,
            aux_kernelBracketProduct
              (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) j v := by rw [hreindex]
    _ = _ := by rfl

private theorem scratch_caseThree_slot_gaussian_majorant
    (p : SequencePair) (hp : ∀ r : Fin 2, SpacedSequence (p r))
    (u : Fin 2) (j : ℤ) (v : RealPlane) :
    aux_kernelBracketProduct (p, u) j v ≤
      8 * Real.exp (2 * Real.pi) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          aux_dominatingGaussianTerm
            (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
  let f0 : ℕ → ℝ := fun a =>
    Real.rpow 2 (-((a : ℝ) / 2)) *
      gaussianRescale ((2 : ℝ) ^ a * p 0 j) (W u v).1
  let f1 : ℕ → ℝ := fun a =>
    Real.rpow 2 (-((a : ℝ) / 2)) *
      gaussianRescale ((2 : ℝ) ^ a * p 1 j) (W u v).2
  have hp0 : 0 < p 0 j := aux_spacedSequence_pos (hp 0) j
  have hp1 : 0 < p 1 j := aux_spacedSequence_pos (hp 1) j
  have hhalf (a : ℕ) : (1 - (3 / 2 : ℝ)) * (a : ℝ) = -((a : ℝ) / 2) := by
    ring
  have hbr0 := gaussianDomination (3 / 2 : ℝ) (p 0 j) (W u v).1
    (by norm_num) hp0
  have hbr1 := gaussianDomination (3 / 2 : ℝ) (p 1 j) (W u v).2
    (by norm_num) hp1
  have hbr0' : scaledBracketBumpReal (3 / 2 : ℝ) (p 0 j) (W u v).1 ≤
      C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f0 a := by
    simpa [f0, hhalf] using hbr0
  have hbr1' : scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 ≤
      C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f1 a := by
    simpa [f1, hhalf] using hbr1
  have hf0 : Summable f0 := by
    simpa [f0, hhalf] using
      aux_gaussianDomination_weight_summable (3 / 2 : ℝ) (p 0 j) (W u v).1
        (by norm_num) hp0
  have hf1 : Summable f1 := by
    simpa [f1, hhalf] using
      aux_gaussianDomination_weight_summable (3 / 2 : ℝ) (p 1 j) (W u v).2
        (by norm_num) hp1
  have hf0nonneg (a : ℕ) : 0 ≤ f0 a := by
    dsimp [f0]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hp0) _)
  have hf1nonneg (a : ℕ) : 0 ≤ f1 a := by
    dsimp [f1]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hp1) _)
  have hprod : Summable (fun m : Fin 2 → ℕ => f0 (m 0) * f1 (m 1)) :=
    aux_summable_finTwo_product hf0nonneg hf1nonneg hf0 hf1
  have hprodPair : Summable (fun z : ℕ × ℕ => f0 z.1 * f1 z.2) := by
    refine (aux_finTwoNatEquivProd.symm.summable_iff
      (f := fun m : Fin 2 → ℕ => f0 (m 0) * f1 (m 1))).mpr ?_
    exact hprod
  have hprodEq : (∑' a : ℕ, f0 a) * (∑' a : ℕ, f1 a) =
      ∑' m : Fin 2 → ℕ, f0 (m 0) * f1 (m 1) := by
    calc
      (∑' a : ℕ, f0 a) * (∑' a : ℕ, f1 a) =
          ∑' z : ℕ × ℕ, f0 z.1 * f1 z.2 := hf0.tsum_mul_tsum hf1 hprodPair
      _ = ∑' m : Fin 2 → ℕ, f0 (m 0) * f1 (m 1) := by
        simpa [aux_finTwoNatEquivProd] using
          (aux_finTwoNatEquivProd.symm.tsum_eq
            (fun m : Fin 2 → ℕ => f0 (m 0) * f1 (m 1)))
  have hterm (m : Fin 2 → ℕ) : f0 (m 0) * f1 (m 1) =
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
    have hweight : aux_gaussianDominationWeight m =
        Real.rpow 2 (-((m 0 : ℕ) : ℝ) / 2) *
          Real.rpow 2 (-((m 1 : ℕ) : ℝ) / 2) := by
      unfold aux_gaussianDominationWeight aux_natPairWeight
      calc
        Real.rpow 2 (-((m 0 + m 1 : ℕ) : ℝ) / 2) =
            Real.rpow 2 (-((m 0 : ℕ) : ℝ) / 2 +
              -((m 1 : ℕ) : ℝ) / 2) := by
          congr 1
          push_cast
          ring
        _ = _ := Real.rpow_add (by norm_num) _ _
    rw [hweight]
    simp only [aux_dominatingGaussianTerm, twoDimensionalGaussian]
    dsimp [f0, f1]
    ring
  have hseriesEq : (∑' a : ℕ, f0 a) * (∑' a : ℕ, f1 a) =
      ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (fun r k => (2 : ℝ) ^ (m r) * p r k) u j v := by
    rw [hprodEq]
    exact tsum_congr hterm
  have hcoeffnonneg : 0 ≤ C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) := by
    rw [C_gaussianDomination]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by norm_num) _)
  have hsum0 : 0 ≤ ∑' a : ℕ, f0 a := tsum_nonneg hf0nonneg
  have hpow : Real.rpow 2 (3 / 2 : ℝ) * Real.rpow 2 (3 / 2 : ℝ) = 8 := by
    change (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) = 8
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hexp : Real.exp Real.pi * Real.exp Real.pi = Real.exp (2 * Real.pi) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcoeff :
      (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) =
      8 * Real.exp (2 * Real.pi) := by
    rw [C_gaussianDomination]
    calc
      (Real.exp Real.pi * Real.rpow 2 (3 / 2 : ℝ)) *
          (Real.exp Real.pi * Real.rpow 2 (3 / 2 : ℝ)) =
          (Real.exp Real.pi * Real.exp Real.pi) *
            (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow 2 (3 / 2 : ℝ)) := by ring
      _ = _ := by rw [hexp, hpow]; ring
  calc
    aux_kernelBracketProduct (p, u) j v =
        scaledBracketBumpReal (2 : ℝ) (p 0 j) (W u v).1 *
          scaledBracketBumpReal (2 : ℝ) (p 1 j) (W u v).2 := by
      simp [aux_kernelBracketProduct, aux_caseTwo.scratch_scaledBracketBump_nat_eq_real]
    _ ≤ scaledBracketBumpReal (3 / 2 : ℝ) (p 0 j) (W u v).1 *
        scaledBracketBumpReal (2 : ℝ) (p 1 j) (W u v).2 :=
      mul_le_mul_of_nonneg_right
        (aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 (p 0 j) (W u v).1 hp0
          (by norm_num))
        (aux_scaledBracketBumpReal_nonneg _ _ _ hp1)
    _ ≤ scaledBracketBumpReal (3 / 2 : ℝ) (p 0 j) (W u v).1 *
        scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 :=
      mul_le_mul_of_nonneg_left
        (aux_scaledBracketBumpReal_exponent_reduce (3 / 2 : ℝ) 2 (p 1 j) (W u v).2 hp1
          (by norm_num))
        (aux_scaledBracketBumpReal_nonneg _ _ _ hp0)
    _ ≤ (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f0 a) *
        scaledBracketBumpReal (3 / 2 : ℝ) (p 1 j) (W u v).2 :=
      mul_le_mul_of_nonneg_right hbr0'
        (aux_scaledBracketBumpReal_nonneg _ _ _ hp1)
    _ ≤ (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f0 a) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ) * ∑' a : ℕ, f1 a) :=
      mul_le_mul_of_nonneg_left hbr1' (mul_nonneg hcoeffnonneg hsum0)
    _ = ((C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ)) *
        (C_gaussianDomination * Real.rpow 2 (3 / 2 : ℝ))) *
          ((∑' a : ℕ, f0 a) * ∑' a : ℕ, f1 a) := by ring
    _ = (8 * Real.exp (2 * Real.pi)) *
          ((∑' a : ℕ, f0 a) * ∑' a : ℕ, f1 a) := by rw [hcoeff]
    _ = _ := by rw [hseriesEq]

private theorem scratch_caseThree_slot_sum_gaussian_majorant {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (lamMinus lamPlus : ℤ → ℝ)
    (hminus : SpacedSequence lamMinus) (hplus : SpacedSequence lamPlus)
    (j : ℤ) (v : RealPlane) :
    ∑ b ∈ scratch_caseThreeB,
      aux_kernelBracketProduct
        (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) j v ≤
      8 * Real.exp (2 * Real.pi) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          ∑ b ∈ scratch_caseThreeB,
            aux_dominatingGaussianTerm
              (scratch_caseThreeScales γ i lamMinus lamPlus b m)
              (scratch_caseThreeOrientation γ i lamMinus lamPlus b) j v := by
  classical
  let T : ℕ → (Fin 2 → ℕ) → ℝ := fun b m =>
    aux_gaussianDominationWeight m *
      aux_dominatingGaussianTerm
        (scratch_caseThreeScales γ i lamMinus lamPlus b m)
        (scratch_caseThreeOrientation γ i lamMinus lamPlus b) j v
  have hslot (b : ℕ) (hb : b ∈ scratch_caseThreeB) :
      aux_kernelBracketProduct
        (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) j v ≤
        (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ, T b m := by
    have hbase := scratch_caseThree_slot_gaussian_majorant
      (scratch_caseThreeSlotNat γ i lamMinus lamPlus b).1
      (scratch_caseThreeSlotNat_spaced γ i lamMinus lamPlus hminus hplus b)
      (scratch_caseThreeSlotNat γ i lamMinus lamPlus b).2 j v
    change aux_kernelBracketProduct
        (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) j v ≤
      (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ,
        aux_gaussianDominationWeight m *
          aux_dominatingGaussianTerm
            (scratch_caseThreeScales γ i lamMinus lamPlus b m)
            (scratch_caseThreeOrientation γ i lamMinus lamPlus b) j v
    unfold scratch_caseThreeScales scratch_caseThreeOrientation
    exact hbase
  have hsum (b : ℕ) (hb : b ∈ scratch_caseThreeB) : Summable (T b) := by
    have hbase := aux_dyadic_gaussian_pair_summable
      (scratch_caseThreeSlotNat γ i lamMinus lamPlus b).1
      (scratch_caseThreeSlotNat_spaced γ i lamMinus lamPlus hminus hplus b)
      (scratch_caseThreeSlotNat γ i lamMinus lamPlus b).2 j v
    change Summable (fun m : Fin 2 → ℕ =>
      aux_gaussianDominationWeight m *
        aux_dominatingGaussianTerm
          (scratch_caseThreeScales γ i lamMinus lamPlus b m)
          (scratch_caseThreeOrientation γ i lamMinus lamPlus b) j v)
    unfold scratch_caseThreeScales scratch_caseThreeOrientation
    exact hbase
  calc
    ∑ b ∈ scratch_caseThreeB,
        aux_kernelBracketProduct
          (scratch_caseThreeSlotNat γ i lamMinus lamPlus b) j v ≤
        ∑ b ∈ scratch_caseThreeB,
          (8 * Real.exp (2 * Real.pi)) * ∑' m : Fin 2 → ℕ, T b m :=
      Finset.sum_le_sum fun b hb => hslot b hb
    _ = (8 * Real.exp (2 * Real.pi)) *
        ∑ b ∈ scratch_caseThreeB, ∑' m : Fin 2 → ℕ, T b m := by
      rw [Finset.mul_sum]
    _ = (8 * Real.exp (2 * Real.pi)) *
        ∑' m : Fin 2 → ℕ, ∑ b ∈ scratch_caseThreeB, T b m := by
      rw [Summable.tsum_finsetSum hsum]
    _ = _ := by
      congr 2
      funext m
      dsimp [T]
      rw [Finset.mul_sum]

private theorem scratch_caseThree_estimate_from_side_conditions {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (hzero : ι.1.1 = 0)
    (hscales : ∀ b ∈ scratch_caseThreeB, ∀ m : Fin 2 → ℕ, ∀ r : Fin 2,
      SpacedSequence
        (scratch_caseThreeScales γ i (scratch_caseThreeLambdaMinus γ ι i)
          (scratch_caseThreeLambdaPlus γ ι i) b m r))
    (j : ℤ) (v : RealPlane) :
    |nMultiplier γ hkn ι i j v| ≤
      C_gaussDominationCase3 *
        Real.rpow 2 (-((ι.1.1.natAbs : ℕ) : ℝ) / 2) *
        ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
          ∑ b ∈ scratch_caseThreeB,
            aux_dominatingGaussianTerm
              (scratch_caseThreeScales γ i (scratch_caseThreeLambdaMinus γ ι i)
                (scratch_caseThreeLambdaPlus γ ι i) b m)
              (scratch_caseThreeOrientation γ i (scratch_caseThreeLambdaMinus γ ι i)
                (scratch_caseThreeLambdaPlus γ ι i) b) j v := by
  let lamMinus : ℤ → ℝ := scratch_caseThreeLambdaMinus γ ι i
  let lamPlus : ℤ → ℝ := scratch_caseThreeLambdaPlus γ ι i
  let T : ℝ := ∑' m : Fin 2 → ℕ, aux_gaussianDominationWeight m *
    ∑ b ∈ scratch_caseThreeB,
      aux_dominatingGaussianTerm
        (scratch_caseThreeScales γ i lamMinus lamPlus b m)
        (scratch_caseThreeOrientation γ i lamMinus lamPlus b) j v
  have hminus : SpacedSequence lamMinus := by
    simpa [lamMinus] using scratch_caseThreeLambdaMinus_spaced γ ι i
  have hplus : SpacedSequence lamPlus := by
    simpa [lamPlus] using scratch_caseThreeLambdaPlus_spaced γ ι i
  have hpre := scratch_caseThree_preGaussian_bound γ hkn ι i j v hzero
  have hslot := scratch_caseThree_slot_sum_gaussian_majorant γ i lamMinus lamPlus
    hminus hplus j v
  have hstd : 0 ≤ C_standardBumpPropertiesTilde 0 2 := by
    rw [show C_standardBumpPropertiesTilde 0 2 = (2 : ℝ) ^ (18 : ℕ) by
      norm_num [C_standardBumpPropertiesTilde]]
    positivity
  have hfour : 0 ≤ C_fourScaleGaussianKernel 2 := by
    have hgauss : 0 ≤ max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 2) :=
      (aux_C_gaussianBumpEstimate_nonneg 0).trans (le_max_left _ _)
    have hsecond : 0 ≤ max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 2) :=
      (aux_C_secondGaussianEstimate_nonneg 0).trans (le_max_left _ _)
    unfold C_fourScaleGaussianKernel C_smoothDecay2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hgauss)
      (mul_nonneg (by positivity) hsecond)
  have htri : 0 ≤ C_bumpTriangle 1 1 2 2 := by
    norm_num [C_bumpTriangle, C_bumpTriangleTilde, Real.rpow_natCast]
  have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
    norm_num [C_twoBumpEstimate]
  have hT : 0 ≤ T := by
    dsimp [T]
    apply tsum_nonneg
    intro m
    apply mul_nonneg (aux_gaussianDominationWeight_nonneg m)
    apply Finset.sum_nonneg
    intro b hb
    exact aux_dominatingGaussianTerm_nonneg
      (scratch_caseThreeScales γ i lamMinus lamPlus b m)
      (by simpa [lamMinus, lamPlus] using hscales b hb m)
      (scratch_caseThreeOrientation γ i lamMinus lamPlus b) j v
  have hprecoeff : 0 ≤
      (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
        C_hKernelEstimateGaussianDomination *
        (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hstd hfour) aux_C_hKernelEstimateGaussianDomination_nonneg)
      scratch_caseThree_u0_coefficient_nonneg
  have hbase : 0 ≤
      C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2 *
        C_hKernelEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
          C_twoBumpEstimate 2 2 * Real.exp (2 * Real.pi) * T := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg hstd hfour)
              aux_C_hKernelEstimateGaussianDomination_nonneg) htri) htwo)
        (Real.exp_pos _).le)
      hT
  calc
    |nMultiplier γ hkn ι i j v| ≤
        (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2) *
          C_hKernelEstimateGaussianDomination *
          (9 * C_bumpTriangle 1 1 2 2 * C_twoBumpEstimate 2 2) *
          ((8 * Real.exp (2 * Real.pi)) * T) := by
      apply hpre.trans
      apply mul_le_mul_of_nonneg_left hslot hprecoeff
    _ = (72 : ℝ) *
        (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2 *
          C_hKernelEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
            C_twoBumpEstimate 2 2 * Real.exp (2 * Real.pi) * T) := by ring
    _ ≤ (2 : ℝ) ^ (7 : ℕ) *
        (C_standardBumpPropertiesTilde 0 2 * C_fourScaleGaussianKernel 2 *
          C_hKernelEstimateGaussianDomination * C_bumpTriangle 1 1 2 2 *
            C_twoBumpEstimate 2 2 * Real.exp (2 * Real.pi) * T) :=
      mul_le_mul_of_nonneg_right (by norm_num) hbase
    _ = C_gaussDominationCase3 * T := by
      unfold C_gaussDominationCase3
      ring
    _ = _ := by
      dsimp [T, lamMinus, lamPlus]
      rw [show ι.1.1.natAbs = 0 by simp [hzero]]
      norm_num only [Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one]

/-- All analytic Case-3 fields, parametrized only by the finite decoder's
cardinality and distance side conditions.  Once the global cardinality cap is
raised to the honest value 36, this instantiates directly. -/
theorem scratch_caseThree_witness_of_side_conditions {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (hzero : ι.1.1 = 0)
    (hcard : scratch_caseThreeB.card ≤ C_gaussianDominationCombinedCard)
    (hscales : ∀ b ∈ scratch_caseThreeB, ∀ m : Fin 2 → ℕ, ∀ r : Fin 2,
      SpacedSequence
        (scratch_caseThreeScales γ i (scratch_caseThreeLambdaMinus γ ι i)
          (scratch_caseThreeLambdaPlus γ ι i) b m r))
    (hdistance : ∀ b ∈ scratch_caseThreeB, ∀ m : Fin 2 → ℕ,
      sequencePairDistance
        (scratch_caseThreeScales γ i (scratch_caseThreeLambdaMinus γ ι i)
          (scratch_caseThreeLambdaPlus γ ι i) b m) ≤
        (C_gaussianDominationCombinedDistance : WithTop ℕ) *
          ((geometricDelta γ + ι.1.1.natAbs + aux_natPairWeight m : ℕ) : WithTop ℕ)) :
    aux_GaussianDominationConclusion γ hkn i ι C_gaussDominationCase3 := by
  classical
  let lamMinus : ℤ → ℝ := scratch_caseThreeLambdaMinus γ ι i
  let lamPlus : ℤ → ℝ := scratch_caseThreeLambdaPlus γ ι i
  have hminus : SpacedSequence lamMinus := by
    simpa [lamMinus] using scratch_caseThreeLambdaMinus_spaced γ ι i
  have hplus : SpacedSequence lamPlus := by
    simpa [lamPlus] using scratch_caseThreeLambdaPlus_spaced γ ι i
  have hbaseScales : ∀ b ∈ scratch_caseThreeB, ∀ r : Fin 2,
      SpacedSequence ((scratch_caseThreeSlotNat γ i lamMinus lamPlus b).1 r) := by
    intro b hb r
    exact scratch_caseThreeSlotNat_spaced γ i lamMinus lamPlus hminus hplus b r
  have htail := aux_finite_dyadic_gaussian_series scratch_caseThreeB
    (fun b => (scratch_caseThreeSlotNat γ i lamMinus lamPlus b).1) hbaseScales
    (scratch_caseThreeOrientation γ i lamMinus lamPlus)
    (scratch_caseThreeScales γ i lamMinus lamPlus) (by
      intro b hb m r k
      rfl)
  refine ⟨{
    B := scratch_caseThreeB
    card_le := hcard
    orientation := scratch_caseThreeOrientation γ i lamMinus lamPlus
    scales := scratch_caseThreeScales γ i lamMinus lamPlus
    scales_in_A := by
      intro b hb m r
      simpa [lamMinus, lamPlus] using hscales b hb m r
    distance_bound := by
      intro b hb m
      simpa [lamMinus, lamPlus] using hdistance b hb m
    estimate := ?_
    series_summable := htail.1
    series_integrable := htail.2
  }⟩
  intro j v
  simpa [lamMinus, lamPlus] using
    scratch_caseThree_estimate_from_side_conditions γ hkn ι i hzero hscales j v

theorem scratch_caseThree_card_le_of_cap
    (hcap : 36 ≤ C_gaussianDominationCombinedCard) :
    scratch_caseThreeB.card ≤ C_gaussianDominationCombinedCard := by
  simpa [scratch_caseThreeB] using hcap

/-- The complete Case-3 theorem, conditional only on raising the global finite
cardinality cap to the honest value 36. -/
theorem scratch_gaussDominationCase3_of_cap {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (i : Fin γ.k)
    (ι : MultiplierIndex γ) (hzero : ι.1.1 = 0)
    (hcentral : ι.1.2.natAbs ≤ geometricDelta γ)
    (hcap : 36 ≤ C_gaussianDominationCombinedCard) :
    aux_GaussianDominationConclusion γ hkn i ι C_gaussDominationCase3 := by
  apply scratch_caseThree_witness_of_side_conditions γ hkn ι i hzero
  · exact scratch_caseThree_card_le_of_cap hcap
  · intro b hb m r
    exact scratch_caseThreeScales_spaced γ i
      (scratch_caseThreeLambdaMinus γ ι i) (scratch_caseThreeLambdaPlus γ ι i)
      (scratch_caseThreeLambdaMinus_spaced γ ι i)
      (scratch_caseThreeLambdaPlus_spaced γ ι i) b m r
  · intro b hb m
    calc
      sequencePairDistance
          (scratch_caseThreeScales γ i (scratch_caseThreeLambdaMinus γ ι i)
            (scratch_caseThreeLambdaPlus γ ι i) b m) ≤
          (C_gaussianDominationCombinedDistance : WithTop ℕ) *
            ((geometricDelta γ + aux_natPairWeight m : ℕ) : WithTop ℕ) :=
        scratch_caseThreeScales_distance_bound γ ι i hcentral b m
      _ ≤ (C_gaussianDominationCombinedDistance : WithTop ℕ) *
            ((geometricDelta γ + ι.1.1.natAbs + aux_natPairWeight m : ℕ) : WithTop ℕ) := by
        gcongr
        exact Nat.le_add_right _ _

theorem scratch_gaussDominationCase3 {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1) (i : Fin γ.k)
    (ι : MultiplierIndex γ) (hzero : ι.1.1 = 0)
    (hcentral : ι.1.2.natAbs ≤ geometricDelta γ) :
    aux_GaussianDominationConclusion γ hkn i ι C_gaussDominationCase3 := by
  exact scratch_gaussDominationCase3_of_cap γ hkn i ι hzero hcentral
    (by norm_num [C_gaussianDominationCombinedCard])

end aux_caseThree

theorem gaussDominationCase3 {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (i : Fin γ.k) (ι : MultiplierIndex γ)
    (hzero : ι.1.1 = 0) (hvertical : ι.1.2.natAbs ≤ geometricDelta γ) :
    aux_GaussianDominationConclusion γ hkn i ι C_gaussDominationCase3 := by
  exact aux_caseThree.scratch_gaussDominationCase3
    γ hkn i ι hzero hvertical

/-- Source label `\ref{Gaussian domination combined}`. -/
theorem gaussianDominationCombined {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (i : Fin γ.k) :
    ∀ ι : MultiplierIndex γ,
      aux_GaussianDominationConclusion γ hkn i ι C_gaussianDominationCombined := by
  have hcommon :
      max C_gaussDominationCase1 (max C_gaussDominationCase2 C_gaussDominationCase3) ≤
        C_gaussianDominationCombined := gaussDominationConstant.2.2.2
  have hcase1 : C_gaussDominationCase1 ≤ C_gaussianDominationCombined :=
    (le_max_left _ _).trans hcommon
  have hcase2 : C_gaussDominationCase2 ≤ C_gaussianDominationCombined :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hcommon)
  have hcase3 : C_gaussDominationCase3 ≤ C_gaussianDominationCombined :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hcommon)
  intro ι
  rcases aux_multiplierIndex_cases γ ι with hι | hι | hι
  · exact aux_GaussianDominationConclusion_mono γ hkn i ι hcase1
      (gaussDominationCase1 γ hkn i ι hι.1 hι.2)
  · exact aux_GaussianDominationConclusion_mono γ hkn i ι hcase2
      (gaussDominationCase2 γ hkn i ι hι.1 hι.2)
  · exact aux_GaussianDominationConclusion_mono γ hkn i ι hcase3
      (gaussDominationCase3 γ hkn i ι hι.1 hι.2)

end

end Codex.MainArgument.GaussianDomination
