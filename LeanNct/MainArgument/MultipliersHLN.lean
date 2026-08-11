import LeanNct.MainArgument.SandwichKernel
import LeanNct.Preliminaries.BumpsAndEstimates

/-!
# Multipliers `H`, `L`, and `N`

Formalization of the first part of the subsection ``Multipliers `H`, `L`, `N``.
-/

namespace Codex.MainArgument.MultipliersHLN

open MeasureTheory Filter Topology Metric
open scoped BigOperators ENNReal Real FourierTransform RealInnerProductSpace

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
For every $a\in\mathrm{A}$ and $j\in\mathbb{Z}$
we have that $s(a,j)$ is a well-defined function in $W_0(\mathbb{R})$.
-/
theorem squareRootGaussianDifference_memW0 {a : ℤ → ℝ}
    (ha : SpacedSequence a) (j : ℤ) :
    MemW0 (squareRootGaussianDifference a ha j) := by
  rw [show squareRootGaussianDifference a ha j =
    diagonalSquareRoot (a (j - 1)) (a j) by
      funext x
      exact aux_squareRootGaussianDifference_eq_diagonalSquareRoot ha j x]
  apply diagonalSquareRoot_memW0
  · exact mul_pos (by norm_num) (ha (j - 1)).1
  · simpa using (ha (j - 1)).2

/--
Consequently, if $\gamma \in \Gamma$ and $i\in [k)$, $j\in \mathbb{Z}$,
then $(s_{\gamma})_{i,j}$ is a well-defined function in $W_0(\mathbb{R})$.
-/
theorem sMultiplier_memW0 {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) :
    MemW0 (sMultiplier γ i j) := by
  unfold sMultiplier
  split_ifs with h
  · apply squareRootGaussianDifference_memW0
  · apply squareRootGaussianDifference_memW0

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
Let $\gamma=(k,u,a)\in \Gamma$. Then $H_{\gamma}\in \mathcal{X}_k$.
-/
theorem hMultiplier_memDoubleSequence {n : ℕ} (γ : GeometricParameters n) :
    MemDoubleSequence γ.k (hMultiplier γ) := by
  intro i j
  change MemW0 (fun v : RealPlane =>
    sMultiplier γ i j v.1 * sMultiplier γ i j v.2 - gaussianDifference γ i j v)
  exact Codex.Preliminaries.KKernels.aux_memW0_sub
    ((sMultiplier_memW0 γ i j).aux_mul_prod (sMultiplier_memW0 γ i j))
    (aux_gaussianDifference_mem γ i j)

/--
Let $\gamma=(k,u,a)\in \Gamma$, $i\in [k)$, $j\in \Z$. For $t>0$, we set
\[
(L_{\gamma,t})_{i,j} =(H_{\gamma})_{i,j} \ast_{(1,1)} \Phi_{(t)}.
\]
-/
noncomputable def lMultiplierAtScale {n : ℕ} (γ : GeometricParameters n) (t : ℝ) :
    DoubleSequence γ.k := fun i j v =>
  ∫ p : ℝ, hMultiplier γ i j (v.1 - p, v.2 - p) * standardBumpRescale t p

/-- Positive rescalings of the standard bump remain in the Wiener space.  This is the
input needed for the convolution closure in `lMultiplierAtScale_memDoubleSequence`. -/
theorem aux_standardBumpRescale_memW0 {t : ℝ} (ht : 0 < t) :
    MemW0 (standardBumpRescale t) := by
  have hcont₀ : Continuous standardBump :=
    aux_standardBumpFinite_tendstoUniformly.continuous
      (Filter.Frequently.of_forall fun n => aux_continuous_standardBumpFinite n)
  have hcont : Continuous (standardBumpRescale t) := by
    unfold standardBumpRescale
    fun_prop
  have hcomplex : MemW0 (fun x : ℝ => (standardBumpRescale t x : ℂ)) := by
    apply aux_memW0_of_quadratic_decay (12 * (t + t⁻¹)) (by positivity)
    · exact Complex.continuous_ofReal.comp hcont
    · intro x
      have htinv : 0 < t⁻¹ := inv_pos.mpr ht
      have hden₁ : 0 < 1 + x ^ 2 := by positivity
      have hden₂ : 0 < 1 + (t⁻¹ * x) ^ 2 := by positivity
      have hcubic : 0 ≤ (t⁻¹) ^ 3 * x ^ 2 :=
        mul_nonneg (pow_nonneg htinv.le _) (sq_nonneg x)
      have hscale : t * (t⁻¹) ^ 2 = t⁻¹ := by
        field_simp
      have hbase : t⁻¹ * (1 + x ^ 2) ≤
          (t + t⁻¹) * (1 + (t⁻¹ * x) ^ 2) := by
        calc
          t⁻¹ * (1 + x ^ 2) = t⁻¹ + t⁻¹ * x ^ 2 := by ring
          _ ≤ (t⁻¹ + t⁻¹ * x ^ 2) + (t + (t⁻¹) ^ 3 * x ^ 2) :=
            le_add_of_nonneg_right (add_nonneg ht.le hcubic)
          _ = (t + t⁻¹) * (1 + (t⁻¹ * x) ^ 2) := by
            calc
              (t⁻¹ + t⁻¹ * x ^ 2) + (t + (t⁻¹) ^ 3 * x ^ 2) =
                  t + t⁻¹ + (t * (t⁻¹) ^ 2) * x ^ 2 + (t⁻¹) ^ 3 * x ^ 2 := by
                    rw [hscale]
                    ring
              _ = (t + t⁻¹) * (1 + (t⁻¹ * x) ^ 2) := by ring
      have hfrac : t⁻¹ * (1 + (t⁻¹ * x) ^ 2)⁻¹ ≤
          (t + t⁻¹) * (1 + x ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv]
        exact (div_le_div_iff₀ hden₂ hden₁).mpr hbase
      rw [standardBumpRescale, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos htinv]
      calc
        t⁻¹ * |standardBump (t⁻¹ * x)| ≤
            t⁻¹ * (12 * (1 + (t⁻¹ * x) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left (aux_standardBump_abs_le_majorant _) htinv.le
        _ = 12 * (t⁻¹ * (1 + (t⁻¹ * x) ^ 2)⁻¹) := by ring
        _ ≤ 12 * ((t + t⁻¹) * (1 + x ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hfrac (by norm_num)
        _ = 12 * (t + t⁻¹) * (1 + x ^ 2)⁻¹ := by ring
  refine ⟨hcont, ?_⟩
  have hEnvelope : wienerEnvelope (standardBumpRescale t) 1 =
      wienerEnvelope (fun x : ℝ => (standardBumpRescale t x : ℂ)) 1 := by
    funext x
    simp [wienerEnvelope, Real.norm_eq_abs]
  rw [hEnvelope]
  exact hcomplex.2

/-- For every positive scale, the convolution defining `L_{γ,t}` is a double sequence of
Wiener-space functions. -/
theorem lMultiplierAtScale_memDoubleSequence {n : ℕ} (γ : GeometricParameters n)
    {t : ℝ} (ht : 0 < t) :
    MemDoubleSequence γ.k (lMultiplierAtScale γ t) := by
  intro i j
  have hH : MemW0 (hMultiplier γ i j) := hMultiplier_memDoubleSequence γ i j
  have hphi : MemW0 (standardBumpRescale t) := aux_standardBumpRescale_memW0 ht
  have hconv := Codex.Preliminaries.MKernels.aux_memW0_convolutionAlong
    (hMultiplier γ i j) hH (standardBumpRescale t) hphi (1, 1)
  change MemW0 (fun v : RealPlane => ∫ p : ℝ,
    hMultiplier γ i j (v.1 - p, v.2 - p) * standardBumpRescale t p)
  convert hconv using 1
  funext v
  rcases v with ⟨v₁, v₂⟩
  simp [smul_eq_mul, sub_eq_add_neg]

/-- Translation is continuous in the ordinary `L¹` norm for Wiener functions.  This is used
for the small-scale limit in `lMultiplierAtScale_tendsto_hMultiplier`. -/
theorem aux_w0_translation_tendsto_integral_norm
    {f : RealPlane → ℝ} (hf : MemW0 f) :
    Tendsto (fun p : RealPlane => ∫ v : RealPlane, ‖f (v - p) - f v‖)
      (nhds 0) (nhds 0) := by
  let B : RealPlane → ℝ := fun v => 2 * wienerEnvelope f 1 v
  have hB_int : Integrable B := by
    exact hf.aux_integrable_envelope.const_mul 2
  have hsmall : ∀ᶠ p : RealPlane in nhds 0, ‖p‖ ≤ 1 := by
    exact Metric.eventually_nhds_iff.2 ⟨1, zero_lt_one, by
      intro p hp
      simpa [dist_zero_right] using hp.le⟩
  have hmeas : ∀ᶠ p : RealPlane in nhds 0,
      AEStronglyMeasurable (fun v : RealPlane => ‖f (v - p) - f v‖) := by
    filter_upwards [] with p
    exact ((hf.aux_continuous.comp (continuous_id.sub continuous_const)).sub
      hf.aux_continuous).norm.aestronglyMeasurable
  have hbound : ∀ᶠ p : RealPlane in nhds 0,
      ∀ᵐ v : RealPlane, ‖‖f (v - p) - f v‖‖ ≤ B v := by
    filter_upwards [hsmall] with p hp
    filter_upwards [] with v
    have hpball : v - p ∈ closedBall v 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using hp
    have hzero : v ∈ closedBall v 1 := Metric.mem_closedBall_self zero_le_one
    have hfirst : ‖f (v - p)‖ ≤ wienerEnvelope f 1 v :=
      aux_norm_le_wienerEnvelope_of_mem_closedBall hf.aux_continuous hpball
    have hsecond : ‖f v‖ ≤ wienerEnvelope f 1 v :=
      aux_norm_le_wienerEnvelope_of_mem_closedBall hf.aux_continuous hzero
    dsimp [B]
    simp only [abs_of_nonneg (abs_nonneg _)]
    calc
      ‖f (v - p) - f v‖ ≤ ‖f (v - p)‖ + ‖f v‖ := norm_sub_le _ _
      _ ≤ wienerEnvelope f 1 v + wienerEnvelope f 1 v := add_le_add hfirst hsecond
      _ = 2 * wienerEnvelope f 1 v := by ring
  have hlim : ∀ᵐ v : RealPlane,
      Tendsto (fun p : RealPlane => ‖f (v - p) - f v‖) (nhds 0) (nhds (0 : ℝ)) := by
    filter_upwards [] with v
    have harg : Tendsto (fun p : RealPlane => v - p) (nhds 0) (nhds v) := by
      have hconst : Tendsto (fun _ : RealPlane => v) (nhds 0) (nhds v) :=
        tendsto_const_nhds
      have hid : Tendsto (fun p : RealPlane => p) (nhds 0) (nhds 0) := tendsto_id
      simpa using hconst.sub hid
    have hdiff : Tendsto (fun p : RealPlane => f (v - p) - f v) (nhds 0) (nhds 0) := by
      have hconst : Tendsto (fun _ : RealPlane => f v) (nhds 0) (nhds (f v)) :=
        tendsto_const_nhds
      simpa only [Function.comp_apply, sub_self] using
        ((hf.aux_continuous.tendsto v).comp harg).sub hconst
    simpa using hdiff.norm
  simpa using
    (MeasureTheory.tendsto_integral_filter_of_dominated_convergence B hmeas hbound hB_int hlim)

/-- Change of variables for the rescaled bump convolution used in `L:F_t`. -/
theorem aux_lMultiplierAtScale_rescale_convolution
    (f : RealPlane → ℝ) (v : RealPlane) (t : ℝ) (ht : 0 < t) :
    (∫ p : ℝ, f (v.1 - p, v.2 - p) * standardBumpRescale t p) =
      ∫ q : ℝ, f (v.1 - t * q, v.2 - t * q) * standardBump q := by
  let g : ℝ → ℝ := fun q => f (v.1 - t * q, v.2 - t * q) * standardBump q
  calc
    (∫ p : ℝ, f (v.1 - p, v.2 - p) * standardBumpRescale t p) =
        ∫ p : ℝ, t⁻¹ * g (t⁻¹ * p) := by
          apply integral_congr_ae
          filter_upwards [] with p
          dsimp [g, standardBumpRescale]
          field_simp
    _ = t⁻¹ * ∫ p : ℝ, g (t⁻¹ * p) := by
          rw [integral_const_mul]
    _ = t⁻¹ * (|(t⁻¹)⁻¹| * ∫ q : ℝ, g q) := by
          rw [Measure.integral_comp_mul_left]
          simp only [smul_eq_mul]
    _ = ∫ q : ℝ, f (v.1 - t * q, v.2 - t * q) * standardBump q := by
          dsimp [g]
          rw [inv_inv, abs_of_pos ht]
          field_simp

/-- The standard bump has total mass one.  This is used in the convolution-error identity. -/
theorem aux_standardBump_integral_one :
    (∫ q : ℝ, standardBump q) = 1 := by
  have hfourier := aux_fourier_standardBump_eq_one_on 0 (by norm_num)
  rw [Real.fourier_real_eq_integral_exp_smul] at hfourier
  have hcomplex : (∫ q : ℝ, (standardBump q : ℂ)) = 1 := by
    simpa using hfourier
  exact_mod_cast hcomplex

/-- The unscaled standard bump belongs to `W₀`; derived from its positive rescalings. -/
theorem aux_standardBump_memW0 : MemW0 standardBump := by
  convert aux_standardBumpRescale_memW0 (t := 1) (by norm_num) using 1
  ext x
  simp [standardBumpRescale]

/-- A jointly integrable shear difference for the approximate-identity argument. -/
theorem aux_memW0_shear_difference
    {f : RealPlane → ℝ} (hf : MemW0 f) (t : ℝ) :
    MemW0 (fun z : RealPlane × ℝ =>
      standardBump z.2 * (f (z.1 - z.2 • (t, t)) - f z.1)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (RealPlane × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let P : RealPlane × ℝ → ℝ := fun z => f z.1 * standardBump z.2
  have hP : MemW0 P := by
    simpa [P] using hf.aux_mul_prod aux_standardBump_memW0
  have hPs : MemW0 (P ∘ Codex.Preliminaries.MKernels.aux_convolutionAlongShear (t, t)) :=
    Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hP _
  have hsub := Codex.Preliminaries.KKernels.aux_memW0_sub hPs hP
  convert hsub using 1
  funext z
  rcases z with ⟨v, q⟩
  dsimp [P, Function.comp_def, Codex.Preliminaries.MKernels.aux_convolutionAlongShear]
  simp [smul_eq_mul, sub_mul, mul_comm]

/-- Integrability of the shear difference used in `lMultiplierAtScale_tendsto_hMultiplier`. -/
theorem aux_integrable_shear_difference
    {f : RealPlane → ℝ} (hf : MemW0 f) (t : ℝ) :
    Integrable (fun z : RealPlane × ℝ =>
      standardBump z.2 * (f (z.1 - z.2 • (t, t)) - f z.1)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (RealPlane × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
    (aux_memW0_shear_difference hf t)

/-- A uniform translation bound that supplies domination for the outer integral. -/
theorem aux_translation_difference_bound
    {f : RealPlane → ℝ} (hf : MemW0 f) (p : RealPlane) :
    (∫ v : RealPlane, ‖f (v - p) - f v‖) ≤
      2 * ∫ v : RealPlane, ‖f v‖ := by
  have hf_int : Integrable f :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hf
  have hshift : Integrable (fun v : RealPlane => f (v - p)) :=
    hf_int.comp_sub_right p
  have hleft : Integrable (fun v : RealPlane => ‖f (v - p) - f v‖) :=
    (hshift.sub hf_int).norm
  have hright : Integrable (fun v : RealPlane => ‖f (v - p)‖ + ‖f v‖) :=
    hshift.norm.add hf_int.norm
  calc
    (∫ v : RealPlane, ‖f (v - p) - f v‖) ≤
        ∫ v : RealPlane, (‖f (v - p)‖ + ‖f v‖) := by
          apply integral_mono hleft hright
          intro v
          exact norm_sub_le _ _
    _ = (∫ v : RealPlane, ‖f (v - p)‖) + ∫ v : RealPlane, ‖f v‖ := by
          rw [integral_add hshift.norm hf_int.norm]
    _ = 2 * ∫ v : RealPlane, ‖f v‖ := by
          rw [integral_sub_right_eq_self (fun v : RealPlane => ‖f v‖) p]
          ring

/-- Pointwise small-scale convergence of the outer shear-error integrand. -/
theorem aux_shear_difference_pointwise_tendsto
    {f : RealPlane → ℝ} (hf : MemW0 f) (q : ℝ) :
    Tendsto (fun t : ℝ =>
      ∫ v : RealPlane, ‖standardBump q *
        (f (v - q • (t, t)) - f v)‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hmap : Tendsto (fun t : ℝ => (q • (t, t) : RealPlane))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have ht : Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hq : Tendsto (fun t : ℝ => q * t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      convert tendsto_const_nhds.mul ht using 1 <;> simp
    change Tendsto (fun t : ℝ => (q * t, q * t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0, 0))
    rw [nhds_prod_eq]
    exact hq.prodMk hq
  have htrans := (aux_w0_translation_tendsto_integral_norm hf).comp hmap
  have hmul : Tendsto (fun t : ℝ => |standardBump q| *
      ∫ v : RealPlane, ‖f (v - q • (t, t)) - f v‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => |standardBump q|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds |standardBump q|)).mul htrans)
  simpa only [norm_mul, Real.norm_eq_abs, integral_const_mul] using hmul

/-- A domination estimate for the outer shear-error integral. -/
theorem aux_shear_difference_pointwise_bound
    {f : RealPlane → ℝ} (hf : MemW0 f) (t q : ℝ) :
    (∫ v : RealPlane, ‖standardBump q *
      (f (v - q • (t, t)) - f v)‖) ≤
      (2 * ∫ v : RealPlane, ‖f v‖) * |standardBump q| := by
  simp_rw [norm_mul]
  rw [integral_const_mul, Real.norm_eq_abs]
  calc
    |standardBump q| * (∫ v : RealPlane, ‖f (v - q • (t, t)) - f v‖) ≤
        |standardBump q| * (2 * ∫ v : RealPlane, ‖f v‖) :=
      mul_le_mul_of_nonneg_left (aux_translation_difference_bound hf _) (abs_nonneg _)
    _ = (2 * ∫ v : RealPlane, ‖f v‖) * |standardBump q| := by ring

/-- Dominated convergence for the outer shear-error integral. -/
theorem aux_shear_difference_integral_tendsto
    {f : RealPlane → ℝ} (hf : MemW0 f) :
    Tendsto (fun t : ℝ => ∫ q : ℝ, ∫ v : RealPlane,
      ‖standardBump q * (f (v - q • (t, t)) - f v)‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let B : ℝ → ℝ := fun q =>
    (2 * ∫ v : RealPlane, ‖f v‖) * |standardBump q|
  have hB_int : Integrable B := by
    exact (aux_integrable_standardBump.norm).const_mul _
  have hmeas : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (fun q : ℝ => ∫ v : RealPlane,
        ‖standardBump q * (f (v - q • (t, t)) - f v)‖) := by
    filter_upwards [] with t
    exact (aux_integrable_shear_difference hf t).integral_norm_prod_right.aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ᵐ q : ℝ,
      ‖∫ v : RealPlane,
        ‖standardBump q * (f (v - q • (t, t)) - f v)‖‖ ≤ B q := by
    filter_upwards [] with t
    filter_upwards [] with q
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact aux_shear_difference_pointwise_bound hf t q
  have hlim : ∀ᵐ q : ℝ,
      Tendsto (fun t : ℝ => ∫ v : RealPlane,
        ‖standardBump q * (f (v - q • (t, t)) - f v)‖)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [] with q
    exact aux_shear_difference_pointwise_tendsto hf q
  simpa using
    (MeasureTheory.tendsto_integral_filter_of_dominated_convergence B hmeas hbound hB_int hlim)

/-- The difference between a scaled bump convolution and its input is its scaled shear error. -/
theorem aux_lMultiplierAtScale_scaled_convolution_difference
    {f : RealPlane → ℝ} (hf : MemW0 f) (t : ℝ) (ht : 0 < t) (v : RealPlane) :
    (∫ p : ℝ, f (v.1 - p, v.2 - p) * standardBumpRescale t p) - f v =
      ∫ q : ℝ, standardBump q * (f (v - q • (t, t)) - f v) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (RealPlane × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let P : RealPlane × ℝ → ℝ := fun z => f z.1 * standardBump z.2
  have hP : MemW0 P := by
    simpa [P] using hf.aux_mul_prod aux_standardBump_memW0
  have hPs : MemW0 (P ∘ Codex.Preliminaries.MKernels.aux_convolutionAlongShear (t, t)) :=
    Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hP _
  have hA : Integrable (fun q : ℝ => f (v - q • (t, t)) * standardBump q) := by
    have hslice := hPs.aux_memW0_slice_of_addHaar v
    have hslice_int := Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hslice
    convert hslice_int using 1
    funext q
    dsimp [P, Function.comp_def, Codex.Preliminaries.MKernels.aux_convolutionAlongShear]
  have hA' : Integrable (fun q : ℝ =>
      f (v.1 - t * q, v.2 - t * q) * standardBump q) := by
    convert hA using 1
    funext q
    rcases v with ⟨v₁, v₂⟩
    change f (v₁ - t * q, v₂ - t * q) * standardBump q =
      f (v₁ - q * t, v₂ - q * t) * standardBump q
    rw [mul_comm q t]
  have hB : Integrable (fun q : ℝ => f v * standardBump q) :=
    aux_integrable_standardBump.const_mul (f v)
  calc
    (∫ p : ℝ, f (v.1 - p, v.2 - p) * standardBumpRescale t p) - f v =
        (∫ q : ℝ, f (v.1 - t * q, v.2 - t * q) * standardBump q) - f v := by
          rw [aux_lMultiplierAtScale_rescale_convolution f v t ht]
    _ = (∫ q : ℝ, f (v.1 - t * q, v.2 - t * q) * standardBump q) -
          f v * ∫ q : ℝ, standardBump q := by
          rw [aux_standardBump_integral_one, mul_one]
    _ = ∫ q : ℝ,
        f (v.1 - t * q, v.2 - t * q) * standardBump q - f v * standardBump q := by
          rw [← integral_const_mul]
          exact (integral_sub hA' hB).symm
    _ = ∫ q : ℝ, standardBump q * (f (v - q • (t, t)) - f v) := by
          apply integral_congr_ae
          filter_upwards [] with q
          have hv : v - q • (t, t) = (v.1 - t * q, v.2 - t * q) := by
            rcases v with ⟨v₁, v₂⟩
            change (v₁ - q * t, v₂ - q * t) = (v₁ - t * q, v₂ - t * q)
            rw [mul_comm q t]
          rw [hv]
          ring

/-- The outer `L¹` bound for the scaled convolution error, including the Fubini swap. -/
theorem aux_lMultiplierAtScale_error_le
    {f : RealPlane → ℝ} (hf : MemW0 f) (t : ℝ) (ht : 0 < t) :
    (∫ v : RealPlane, |(∫ p : ℝ,
      f (v.1 - p, v.2 - p) * standardBumpRescale t p) - f v|) ≤
      ∫ q : ℝ, ∫ v : RealPlane,
        ‖standardBump q * (f (v - q • (t, t)) - f v)‖ := by
  letI : MeasureSpace (RealPlane × ℝ) := Measure.prod.measureSpace
  letI : Measure.IsAddHaarMeasure (volume : Measure (RealPlane × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hphi : MemW0 (standardBumpRescale t) := aux_standardBumpRescale_memW0 ht
  have hconv := Codex.Preliminaries.MKernels.aux_memW0_convolutionAlong
    f hf (standardBumpRescale t) hphi (1, 1)
  have hconv_int : Integrable (fun v : RealPlane => ∫ p : ℝ,
      f (v.1 - p, v.2 - p) * standardBumpRescale t p) := by
    have hconv' : Integrable (fun v : RealPlane => ∫ p : ℝ,
        f (v - p • (1, 1)) * standardBumpRescale t p) :=
      Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hconv
    convert hconv' using 1
    funext v
    rcases v with ⟨v₁, v₂⟩
    simp [smul_eq_mul, sub_eq_add_neg]
  have hf_int : Integrable f :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hf
  have hleft : Integrable (fun v : RealPlane =>
      |(∫ p : ℝ, f (v.1 - p, v.2 - p) * standardBumpRescale t p) - f v|) := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using (hconv_int.sub hf_int).norm
  have hD : Integrable (fun z : RealPlane × ℝ =>
      standardBump z.2 * (f (z.1 - z.2 • (t, t)) - f z.1)) :=
    aux_integrable_shear_difference hf t
  have hright : Integrable (fun v : RealPlane => ∫ q : ℝ,
      ‖standardBump q * (f (v - q • (t, t)) - f v)‖) := by
    simpa only [Measure.volume_eq_prod] using hD.integral_norm_prod_left
  calc
    (∫ v : RealPlane, |(∫ p : ℝ,
      f (v.1 - p, v.2 - p) * standardBumpRescale t p) - f v|) ≤
        ∫ v : RealPlane, ∫ q : ℝ,
          ‖standardBump q * (f (v - q • (t, t)) - f v)‖ := by
      apply integral_mono hleft hright
      intro v
      change |(∫ p : ℝ, f (v.1 - p, v.2 - p) * standardBumpRescale t p) - f v| ≤
        ∫ q : ℝ, ‖standardBump q * (f (v - q • (t, t)) - f v)‖
      rw [← Real.norm_eq_abs, aux_lMultiplierAtScale_scaled_convolution_difference hf t ht v]
      exact norm_integral_le_integral_norm _
    _ = ∫ q : ℝ, ∫ v : RealPlane,
        ‖standardBump q * (f (v - q • (t, t)) - f v)‖ := by
      let D : RealPlane → ℝ → ℝ := fun v q =>
        ‖standardBump q * (f (v - q • (t, t)) - f v)‖
      simpa only [D, Function.uncurry, Measure.volume_eq_prod] using
        (integral_integral_swap hD.norm)

/-- The ordinary `L¹` small-scale convergence used to prove `L:F_t`. -/
theorem aux_lMultiplierAtScale_tendsto_integral_norm
    {f : RealPlane → ℝ} (hf : MemW0 f) :
    Tendsto (fun t : ℝ => ∫ v : RealPlane,
      |(∫ p : ℝ, f (v.1 - p, v.2 - p) * standardBumpRescale t p) - f v|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (aux_shear_difference_integral_tendsto hf)
  · filter_upwards [] with t
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact aux_lMultiplierAtScale_error_le hf t ht

/--
Let $\gamma=(k,u,a)\in \Gamma$.  For $i\in[k)$ and $j\in\mathbb Z$,
\[
\lim_{t\to0_+}(L_{\gamma,t})_{i,j}=(H_\gamma)_{i,j}\quad\text{in }L^1.
\]
-/
theorem lMultiplierAtScale_tendsto_hMultiplier
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) :
    Tendsto (fun t : ℝ =>
      eLpNorm (lMultiplierAtScale γ t i j - hMultiplier γ i j) 1 volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hOuter : Tendsto (fun t : ℝ => ∫ v : RealPlane,
      |lMultiplierAtScale γ t i j v - hMultiplier γ i j v|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [lMultiplierAtScale] using
      (aux_lMultiplierAtScale_tendsto_integral_norm
        (hMultiplier_memDoubleSequence γ i j))
  have hOuter' : Tendsto (fun t : ℝ => ENNReal.ofReal
      (∫ v : RealPlane, |lMultiplierAtScale γ t i j v - hMultiplier γ i j v|))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hOuter
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) hOuter'
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hL : Integrable (lMultiplierAtScale γ t i j) :=
      Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
        (lMultiplierAtScale_memDoubleSequence γ ht i j)
    have hH : Integrable (hMultiplier γ i j) :=
      Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
        (hMultiplier_memDoubleSequence γ i j)
    refine aux_eLpNorm_one_le_of_integral_norm_le (hL.sub hH) ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact le_rfl

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

/-- The raw plane Fourier transform factors over product functions. -/
theorem aux_fourierPlane_tensor (f g : ℝ → ℝ) (ξ η : ℝ) :
    aux_fourierPlane (fun v : RealPlane => f v.1 * g v.2) (ξ, η) =
      aux_fourierReal f ξ * aux_fourierReal g η := by
  unfold aux_fourierPlane aux_fourierReal
  rw [Measure.volume_eq_prod]
  let F : ℝ → ℂ := fun x => (f x : ℂ) *
    Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * x * ξ))
  let G : ℝ → ℂ := fun y => (g y : ℂ) *
    Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * y * η))
  calc
    (∫ v : ℝ × ℝ, ((f v.1 * g v.2 : ℝ) : ℂ) *
        Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * (v.1 * ξ + v.2 * η)))) =
        ∫ v : ℝ × ℝ, F v.1 * G v.2 := by
          apply integral_congr_ae
          filter_upwards [] with v
          dsimp [F, G]
          push_cast
          calc
            ↑(f v.1) * ↑(g v.2) *
                Complex.exp (-(2 * ↑Real.pi * Complex.I *
                  (↑v.1 * ↑ξ + ↑v.2 * ↑η))) =
                (↑(f v.1) * ↑(g v.2)) *
                  (Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑v.1 * ↑ξ)) *
                    Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑v.2 * ↑η))) := by
                  rw [← Complex.exp_add]
                  congr 1
                  ring
            _ = ↑(f v.1) * Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑v.1 * ↑ξ)) *
                (↑(g v.2) * Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑v.2 * ↑η))) := by
                  ring
    _ = (∫ x, F x) * ∫ y, G y := integral_prod_mul F G
    _ = aux_fourierReal f ξ * aux_fourierReal g η := by rfl

/-- This identifies the raw one-dimensional Fourier integral with mathlib's transform. -/
theorem aux_fourierReal_eq_fourier (f : ℝ → ℝ) (ξ : ℝ) :
    aux_fourierReal f ξ = FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) ξ := by
  rw [aux_fourierReal, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul]
  have hExp : -((2 : ℂ) * Real.pi * Complex.I * (x : ℂ) * (ξ : ℂ)) =
      ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hExp]
  ring

/-- The one-dimensional square-root multiplier has the prescribed Fourier transform. -/
theorem aux_squareRootGaussianDifference_fourier {a : ℤ → ℝ}
    (ha : SpacedSequence a) (j : ℤ) (ξ : ℝ) :
    aux_fourierReal (squareRootGaussianDifference a ha j) ξ =
      (Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
        Codex.Preliminaries.Notation.gaussian (a j * ξ)) : ℂ) := by
  let f : ℝ → ℝ := fun η =>
    Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * η) -
      Codex.Preliminaries.Notation.gaussian (a j * η))
  have hf : Integrable f := by
    simpa only [f] using aux_squareRootGaussianDifference_integrable ha j
  have hfeven : ∀ η : ℝ, f (-η) = f η := by
    intro η
    simp [f, Codex.Preliminaries.Notation.gaussian]
  have hcont : Continuous f := by
    dsimp [f]
    apply Continuous.sqrt
    exact (gaussian_continuous.comp (continuous_const.mul continuous_id)).sub
      (gaussian_continuous.comp (continuous_const.mul continuous_id))
  have him (x : ℝ) :
      (FourierTransformInv.fourierInv (fun η : ℝ => (f η : ℂ)) x).im = 0 :=
    aux_diagonalSquareRoot_inverseFourier_real_of_even f hf hfeven x
  have hs_eq_inv (x : ℝ) :
      (squareRootGaussianDifference a ha j x : ℂ) =
        FourierTransformInv.fourierInv (fun η : ℝ => (f η : ℂ)) x := by
    apply Complex.ext
    · simpa only [Complex.ofReal_re, squareRootGaussianDifference, f] using
        (aux_realInverseFourier_eq_cosineIntegral hf x).symm
    · simpa only [Complex.ofReal_im] using (him x).symm
  have hinv_eq_fourier :
      FourierTransformInv.fourierInv (fun η : ℝ => (f η : ℂ)) =
        FourierTransform.fourier (fun η : ℝ => (f η : ℂ)) := by
    rw [Real.fourierInv_eq_fourier_comp_neg]
    funext x
    apply Real.fourier_congr_ae
    filter_upwards [] with η
    exact_mod_cast hfeven η
  have hsint : Integrable (fun x : ℝ => (squareRootGaussianDifference a ha j x : ℂ)) := by
    exact (Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (squareRootGaussianDifference_memW0 ha j)).ofReal
  have hfourierint : Integrable (FourierTransform.fourier (fun η : ℝ => (f η : ℂ))) := by
    rw [← hinv_eq_fourier, ← funext hs_eq_inv]
    exact hsint
  have hprofile : FourierTransform.fourier
      (fun x : ℝ => (squareRootGaussianDifference a ha j x : ℂ)) ξ = (f ξ : ℂ) := by
    rw [funext hs_eq_inv]
    exact congrFun ((Complex.continuous_ofReal.comp hcont).fourier_fourierInv_eq
      hf.ofReal hfourierint) ξ
  calc
    aux_fourierReal (squareRootGaussianDifference a ha j) ξ =
        FourierTransform.fourier (fun x : ℝ => (squareRootGaussianDifference a ha j x : ℂ)) ξ :=
      aux_fourierReal_eq_fourier _ _
    _ = (f ξ : ℂ) := hprofile
    _ = _ := rfl

/-- The normalized rescaled Gaussian has its expected raw Fourier transform. -/
theorem aux_fourierReal_gaussianRescale (t : ℝ) (ht : 0 < t) (ξ : ℝ) :
    aux_fourierReal (gaussianRescale t) ξ =
      (Codex.Preliminaries.Notation.gaussian (t * ξ) : ℂ) := by
  rw [aux_fourierReal_eq_fourier]
  exact congrFun (gaussianRescale_fourier t ht) ξ

/-- The identity-orientation two-dimensional Gaussian factors into one-dimensional transforms. -/
theorem aux_fourierPlane_twoDimensionalGaussian_zero (q : Fin 2 → ℝ)
    (hq : ∀ r, 0 < q r) (ξ η : ℝ) :
    aux_fourierPlane (twoDimensionalGaussian q 0) (ξ, η) =
      (Codex.Preliminaries.Notation.gaussian (q 0 * ξ) *
        Codex.Preliminaries.Notation.gaussian (q 1 * η) : ℂ) := by
  rw [show twoDimensionalGaussian q 0 =
      fun v : RealPlane => gaussianRescale (q 0) v.1 * gaussianRescale (q 1) v.2 by
        ext v
        simp [twoDimensionalGaussian, W]]
  rw [aux_fourierPlane_tensor,
    aux_fourierReal_gaussianRescale (q 0) (hq 0) ξ,
    aux_fourierReal_gaussianRescale (q 1) (hq 1) η]

/-- The rotated two-dimensional Gaussian is evaluated by the measure-preserving $W_1$ change. -/
theorem aux_fourierPlane_twoDimensionalGaussian_one (q : Fin 2 → ℝ)
    (hq : ∀ r, 0 < q r) (ξ η : ℝ) :
    aux_fourierPlane (twoDimensionalGaussian q 1) (ξ, η) =
      (Codex.Preliminaries.Notation.gaussian (q 0 * ((ξ + η) / Real.sqrt 2)) *
        Codex.Preliminaries.Notation.gaussian (q 1 * ((-ξ + η) / Real.sqrt 2)) : ℂ) := by
  let g : RealPlane → ℝ := fun w =>
    gaussianRescale (q 0) w.1 * gaussianRescale (q 1) w.2
  let F : RealPlane → ℂ := fun w => (g w : ℂ) * Complex.exp
    (-((2 : ℂ) * Real.pi * Complex.I *
      ((aux_WOneContinuousLinearEquiv.symm w).1 * ξ +
        (aux_WOneContinuousLinearEquiv.symm w).2 * η)))
  have hchange : (∫ v : RealPlane, F (aux_WOneContinuousLinearEquiv v)) =
      ∫ w : RealPlane, F w :=
    aux_measurePreserving_WOne.integral_comp
      aux_WOneContinuousLinearEquiv.toHomeomorph.measurableEmbedding F
  have hinv_apply (w : RealPlane) : aux_WOneContinuousLinearEquiv.symm w =
      ((w.1 - w.2) / Real.sqrt 2, (w.1 + w.2) / Real.sqrt 2) := by
    rfl
  calc
    aux_fourierPlane (twoDimensionalGaussian q 1) (ξ, η) =
        ∫ v : RealPlane, F (aux_WOneContinuousLinearEquiv v) := by
          unfold aux_fourierPlane
          apply integral_congr_ae
          filter_upwards [] with v
          dsimp [F]
          rw [aux_WOneContinuousLinearEquiv.symm_apply_apply]
          simp only [g]
          rw [show twoDimensionalGaussian q 1 v =
              g (aux_WOneContinuousLinearEquiv v) by
                simp [g, twoDimensionalGaussian, W, aux_WOneContinuousLinearEquiv]]
    _ = ∫ w : RealPlane, F w := hchange
    _ = aux_fourierPlane
        (fun w : RealPlane => gaussianRescale (q 0) w.1 * gaussianRescale (q 1) w.2)
        ((ξ + η) / Real.sqrt 2, (-ξ + η) / Real.sqrt 2) := by
          unfold aux_fourierPlane
          apply integral_congr_ae
          filter_upwards [] with w
          dsimp only [F, g]
          rw [hinv_apply w]
          congr 1
          congr 1
          push_cast
          ring
    _ = _ := by
      rw [aux_fourierPlane_tensor,
        aux_fourierReal_gaussianRescale (q 0) (hq 0) ((ξ + η) / Real.sqrt 2),
        aux_fourierReal_gaussianRescale (q 1) (hq 1) ((-ξ + η) / Real.sqrt 2)]

/-- The two identity-orientation Fourier factors combine into the diagonal scale. -/
theorem aux_gaussian_mul_diag (a b x : ℝ) :
    (Codex.Preliminaries.Notation.gaussian (a * x) *
      Codex.Preliminaries.Notation.gaussian (b * (-x)) : ℂ) =
      (Codex.Preliminaries.Notation.gaussian (Real.sqrt (a ^ 2 + b ^ 2) * x) : ℂ) := by
  norm_cast
  unfold Codex.Preliminaries.Notation.gaussian
  rw [← Real.exp_add]
  congr 1
  have hsqrt : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 :=
    Real.sq_sqrt (by positivity)
  calc
    -Real.pi * (a * x) ^ 2 + -Real.pi * (b * -x) ^ 2 =
        -Real.pi * ((a ^ 2 + b ^ 2) * x ^ 2) := by ring
    _ = -Real.pi * (Real.sqrt (a ^ 2 + b ^ 2) ^ 2 * x ^ 2) := by rw [hsqrt]
    _ = -Real.pi * (Real.sqrt (a ^ 2 + b ^ 2) * x) ^ 2 := by ring

/-- The rotated diagonal frequency reduces to the second scale. -/
theorem aux_gaussian_wOne_diag (a x : ℝ) :
    (Codex.Preliminaries.Notation.gaussian
      (a * ((-x + -x) / Real.sqrt 2)) : ℂ) =
      (Codex.Preliminaries.Notation.gaussian (Real.sqrt 2 * a * x) : ℂ) := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hroot : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have harg : a * ((-x + -x) / Real.sqrt 2) = -(Real.sqrt 2 * a * x) := by
    field_simp
    rw [hsqrt]
    ring
  rw [harg]
  simp [Codex.Preliminaries.Notation.gaussian]

/-- The Fourier transform of a gamma Gaussian on the anti-diagonal. -/
theorem aux_gammaGaussian_fourier_diagonal {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (ξ : ℝ) :
    aux_fourierPlane (gammaGaussian γ i j) (ξ, -ξ) =
      if _h : γ.orientation i = 0 then
        (Codex.Preliminaries.Notation.gaussian
          (Real.sqrt ((γ.scales i 0 j) ^ 2 + (γ.scales i 1 j) ^ 2) * ξ) : ℂ)
      else
        (Codex.Preliminaries.Notation.gaussian
          (Real.sqrt 2 * γ.scales i 1 j * ξ) : ℂ) := by
  have horient : γ.orientation i = 0 ∨ γ.orientation i = 1 := by
    have hfin (u : Fin 2) : u = 0 ∨ u = 1 := by
      fin_cases u <;> simp
    exact hfin (γ.orientation i)
  rcases horient with hzero | hone
  · rw [dif_pos hzero]
    have hq : ∀ r, 0 < γ.scales i r j := fun r =>
      aux_spacedSequence_pos (γ.scales_spaced i r) j
    rw [gammaGaussian, hzero,
      aux_fourierPlane_twoDimensionalGaussian_zero
        (fun r => γ.scales i r j) hq ξ (-ξ)]
    exact aux_gaussian_mul_diag _ _ _
  · rw [dif_neg (by omega)]
    have hq : ∀ r, 0 < γ.scales i r j := fun r =>
      aux_spacedSequence_pos (γ.scales_spaced i r) j
    rw [gammaGaussian, hone,
      aux_fourierPlane_twoDimensionalGaussian_one
        (fun r => γ.scales i r j) hq ξ (-ξ)]
    have hzero : Codex.Preliminaries.Notation.gaussian
        (γ.scales i 0 j * ((ξ + -ξ) / Real.sqrt 2)) = 1 := by
      simp [Codex.Preliminaries.Notation.gaussian]
    rw [hzero]
    norm_num
    exact_mod_cast aux_gaussian_wOne_diag (γ.scales i 1 j) ξ

/-- The two anti-diagonal Fourier factors of a square-root Gaussian recover its difference. -/
theorem aux_squareRootGaussianDifference_fourier_diagonal {a : ℤ → ℝ}
    (ha : SpacedSequence a) (j : ℤ) (ξ : ℝ) :
    aux_fourierReal (squareRootGaussianDifference a ha j) ξ *
      aux_fourierReal (squareRootGaussianDifference a ha j) (-ξ) =
      (Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
        Codex.Preliminaries.Notation.gaussian (a j * ξ) : ℂ) := by
  rw [aux_squareRootGaussianDifference_fourier ha j ξ,
    aux_squareRootGaussianDifference_fourier ha j (-ξ)]
  have hscale : 2 * a (j - 1) ≤ a j := by
    convert (ha (j - 1)).2 using 1 <;> ring
  have hrad : 0 ≤ Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
      Codex.Preliminaries.Notation.gaussian (a j * ξ) :=
    aux_diagonalSquareRootFrequency_nonneg (by nlinarith [(ha (j - 1)).1]) hscale ξ
  have hneg :
      Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * -ξ) -
        Codex.Preliminaries.Notation.gaussian (a j * -ξ)) =
      Real.sqrt (Codex.Preliminaries.Notation.gaussian (a (j - 1) * ξ) -
        Codex.Preliminaries.Notation.gaussian (a j * ξ)) := by
    congr 1
    simp [Codex.Preliminaries.Notation.gaussian]
  rw [hneg]
  norm_cast
  simpa [pow_two] using Real.sq_sqrt hrad

/-- The tensor square of the $s$ multiplier has the corresponding Gaussian difference. -/
theorem aux_sMultiplier_tensor_fourier_diagonal {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (ξ : ℝ) :
    aux_fourierPlane (fun v : RealPlane =>
      sMultiplier γ i j v.1 * sMultiplier γ i j v.2) (ξ, -ξ) =
      if _h : γ.orientation i = 0 then
        (Codex.Preliminaries.Notation.gaussian
          (Real.sqrt ((γ.scales i 0 (j - 1)) ^ 2 + (γ.scales i 1 (j - 1)) ^ 2) * ξ) -
          Codex.Preliminaries.Notation.gaussian
            (Real.sqrt ((γ.scales i 0 j) ^ 2 + (γ.scales i 1 j) ^ 2) * ξ) : ℂ)
      else
        (Codex.Preliminaries.Notation.gaussian
          (Real.sqrt 2 * γ.scales i 1 (j - 1) * ξ) -
          Codex.Preliminaries.Notation.gaussian
            (Real.sqrt 2 * γ.scales i 1 j * ξ) : ℂ) := by
  by_cases h : γ.orientation i = 0
  · rw [dif_pos h, aux_fourierPlane_tensor, sMultiplier, dif_pos h]
    exact aux_squareRootGaussianDifference_fourier_diagonal
      (sqrt_sq_add_sq_mem_A (γ.scales_spaced i 0) (γ.scales_spaced i 1)) j ξ
  · rw [dif_neg h, aux_fourierPlane_tensor, sMultiplier, dif_neg h]
    exact aux_squareRootGaussianDifference_fourier_diagonal
      (smul_mem_A (γ.scales_spaced i 1) (Real.sqrt_pos.2 (by norm_num))) j ξ

/-- Raw Fourier integration is linear for the integrable functions used below. -/
theorem aux_fourierPlane_sub (f g : RealPlane → ℝ)
    (hf : Integrable f) (hg : Integrable g) (ξ : RealPlane) :
    aux_fourierPlane (fun v => f v - g v) ξ =
      aux_fourierPlane f ξ - aux_fourierPlane g ξ := by
  let e : RealPlane → ℂ := fun v => Complex.exp
    (-((2 : ℂ) * Real.pi * Complex.I * (v.1 * ξ.1 + v.2 * ξ.2)))
  have he : Continuous e := by
    dsimp [e]
    fun_prop
  have he_bound : ∀ v, ‖e v‖ ≤ (1 : ℝ) := by
    intro v
    rw [show e v = Complex.exp
        ((↑(-2 * Real.pi * (v.1 * ξ.1 + v.2 * ξ.2)) : ℂ) * Complex.I) by
          dsimp [e]
          push_cast
          ring,
      Complex.norm_exp]
    norm_num
  have hf' : Integrable (fun v : RealPlane => (f v : ℂ) * e v) := by
    apply (hf.ofReal.bdd_mul he.aestronglyMeasurable (ae_of_all _ he_bound)).congr
    filter_upwards [] with v
    exact mul_comm _ _
  have hg' : Integrable (fun v : RealPlane => (g v : ℂ) * e v) := by
    apply (hg.ofReal.bdd_mul he.aestronglyMeasurable (ae_of_all _ he_bound)).congr
    filter_upwards [] with v
    exact mul_comm _ _
  unfold aux_fourierPlane
  change (∫ v : RealPlane, ((f v - g v : ℝ) : ℂ) * e v) = _
  calc
    (∫ v : RealPlane, ((f v - g v : ℝ) : ℂ) * e v) =
        ∫ v : RealPlane, ((f v : ℂ) * e v - (g v : ℂ) * e v) := by
          apply integral_congr_ae
          filter_upwards [] with v
          push_cast
          ring
    _ = (∫ v : RealPlane, (f v : ℂ) * e v) -
        ∫ v : RealPlane, (g v : ℂ) * e v := integral_sub hf' hg'
    _ = _ := rfl

/-- The Gaussian difference transforms to the difference of its two gamma Gaussian transforms. -/
theorem aux_gaussianDifference_fourier_diagonal {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (ξ : ℝ) :
    aux_fourierPlane (gaussianDifference γ i j) (ξ, -ξ) =
      aux_fourierPlane (gammaGaussian γ i (j - 1)) (ξ, -ξ) -
        aux_fourierPlane (gammaGaussian γ i j) (ξ, -ξ) := by
  unfold gaussianDifference
  apply aux_fourierPlane_sub
  · exact Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (aux_gammaGaussian_memW0 γ i (j - 1))
  · exact Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (aux_gammaGaussian_memW0 γ i j)

/--
For every $γ\in\Gamma$, $i\in[k)$, $j\in\mathbb Z$, and $ξ\in\mathbb R$, the Fourier transform
of $(H_\gamma)_{i,j}$ vanishes on the anti-diagonal $(\xi,-\xi)$.
-/
theorem hMultiplier_fourier_diagonal_vanishing {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (ξ : ℝ) :
    aux_fourierPlane (hMultiplier γ i j) (ξ, -ξ) = 0 := by
  change aux_fourierPlane (fun v : RealPlane =>
    sMultiplier γ i j v.1 * sMultiplier γ i j v.2 - gaussianDifference γ i j v) (ξ, -ξ) = 0
  rw [aux_fourierPlane_sub]
  · rw [aux_sMultiplier_tensor_fourier_diagonal,
      aux_gaussianDifference_fourier_diagonal,
      aux_gammaGaussian_fourier_diagonal,
      aux_gammaGaussian_fourier_diagonal]
    by_cases h : γ.orientation i = 0
    · simp only [dif_pos h]
      ring
    · simp only [dif_neg h]
      ring
  · exact Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      ((sMultiplier_memW0 γ i j).aux_mul_prod (sMultiplier_memW0 γ i j))
  · exact Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (aux_gaussianDifference_mem γ i j)

/-- The measure-preserving shear turning a diagonal line integral into a coordinate slice. -/
noncomputable def aux_diagonalShear : RealPlane ≃L[ℝ] RealPlane where
  toFun := fun v => (v.1 + v.2, v.2)
  invFun := fun v => (v.1 - v.2, v.2)
  left_inv := by
    rintro ⟨x, y⟩
    refine Prod.ext ?_ ?_
    · dsimp
      ring
    · rfl
  right_inv := by
    rintro ⟨x, y⟩
    refine Prod.ext ?_ ?_
    · dsimp
      ring
    · rfl
  map_add' := by
    rintro ⟨x, y⟩ ⟨z, w⟩
    refine Prod.ext ?_ ?_
    · dsimp
      ring
    · rfl
  map_smul' := by
    rintro c ⟨x, y⟩
    refine Prod.ext ?_ ?_
    · dsimp
      ring
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The diagonal shear preserves Lebesgue measure. -/
theorem aux_measurePreserving_diagonalShear :
    MeasurePreserving (aux_diagonalShear : RealPlane → RealPlane) volume volume := by
  change MeasurePreserving (fun v : ℝ × ℝ => (v.1 + v.2, v.2))
    ((volume : Measure ℝ).prod (volume : Measure ℝ))
    ((volume : Measure ℝ).prod (volume : Measure ℝ))
  exact measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)

/-- The Fourier transform of a diagonal line integral is the anti-diagonal slice in frequency. -/
theorem aux_fourierReal_diagonalSlice (f : RealPlane → ℝ) (hf : MemW0 f)
    (ξ : ℝ) :
    aux_fourierReal (fun z : ℝ => ∫ p : ℝ, f (z + p, p)) ξ =
      aux_fourierPlane f (ξ, -ξ) := by
  let S : RealPlane → ℝ := fun q => f (aux_diagonalShear q)
  have hS : MemW0 S := by
    change MemW0 (f ∘ (aux_diagonalShear : RealPlane → RealPlane))
    exact Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hf
      aux_diagonalShear
  have hSint : Integrable S :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hS
  let phase : RealPlane → ℂ := fun q => Complex.exp
    (-((2 : ℂ) * Real.pi * Complex.I * q.1 * ξ))
  have hphase : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hphase_bound : ∀ q : RealPlane, ‖phase q‖ ≤ (1 : ℝ) := by
    intro q
    dsimp [phase]
    rw [Complex.norm_exp]
    norm_num
  let F : RealPlane → ℂ := fun q => (S q : ℂ) * phase q
  have hF : Integrable F :=
    hSint.ofReal.mul_bdd hphase.aestronglyMeasurable (ae_of_all _ hphase_bound)
  let G : RealPlane → ℂ := fun v => (f v : ℂ) * Complex.exp
    (-((2 : ℂ) * Real.pi * Complex.I * (v.1 - v.2) * ξ))
  have hFG (q : RealPlane) : F q = G (aux_diagonalShear q) := by
    dsimp [F, S, phase, G, aux_diagonalShear]
    congr 1
    push_cast
    ring
  have hchange : (∫ q : RealPlane, G (aux_diagonalShear q)) =
      ∫ v : RealPlane, G v :=
    aux_measurePreserving_diagonalShear.integral_comp
      aux_diagonalShear.toHomeomorph.measurableEmbedding G
  unfold aux_fourierReal
  calc
    (∫ z : ℝ, (∫ p : ℝ, f (z + p, p)) *
        Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * z * ξ))) =
        ∫ z : ℝ, (∫ p : ℝ, (f (z + p, p) : ℂ)) *
          Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * z * ξ)) := by
          apply integral_congr_ae
          filter_upwards [] with z
          apply congrArg (fun c : ℂ => c *
            Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * z * ξ)))
          exact (integral_ofReal (f := fun p : ℝ => f (z + p, p))).symm
    _ = ∫ z : ℝ, ∫ p : ℝ, (f (z + p, p) : ℂ) *
          Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * z * ξ)) := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [← integral_mul_const]
    _ = ∫ q : RealPlane, F q := by
          have hprod : (∫ q : RealPlane, F q) =
              ∫ z : ℝ, ∫ p : ℝ, F (z, p) := by
            simpa only [Measure.volume_eq_prod] using integral_prod F hF
          calc
            (∫ z : ℝ, ∫ p : ℝ, (f (z + p, p) : ℂ) *
                Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * z * ξ))) =
                ∫ z : ℝ, ∫ p : ℝ, F (z, p) := by
                  apply integral_congr_ae
                  filter_upwards [] with z
                  apply integral_congr_ae
                  filter_upwards [] with p
                  dsimp [F, S, phase, aux_diagonalShear]
            _ = ∫ q : RealPlane, F q := hprod.symm
    _ = ∫ q : RealPlane, G (aux_diagonalShear q) := by
          apply integral_congr_ae
          filter_upwards [] with q
          exact hFG q
    _ = ∫ v : RealPlane, G v := hchange
    _ = aux_fourierPlane f (ξ, -ξ) := by
          unfold aux_fourierPlane
          apply integral_congr_ae
          filter_upwards [] with v
          dsimp [G]
          congr 1
          push_cast
          ring

/--
For every $γ\in\Gamma$, $i\in[k)$, $j\in\mathbb Z$, and $z\in\mathbb R$, the integral of
$(H_γ)_{i,j}$ along the diagonal line through $(z,0)$ vanishes.
-/
theorem hMultiplier_vanishing_integral {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (z : ℝ) :
    (∫ p : ℝ, hMultiplier γ i j (z + p, p)) = 0 := by
  have hH : MemW0 (hMultiplier γ i j) := hMultiplier_memDoubleSequence γ i j
  let L : ℝ → ℝ := fun u => ∫ p : ℝ, hMultiplier γ i j (u + p, p)
  have hS : MemW0 (fun q : RealPlane => hMultiplier γ i j (aux_diagonalShear q)) :=
    Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hH
      aux_diagonalShear
  have hL : MemW0 L := by
    have hslice := Codex.Preliminaries.KKernels.aux_memW0_integral_slice_of_addHaar hS
    have hslice_eq :
        (fun u : ℝ => ∫ v : ℝ,
          hMultiplier γ i j (aux_diagonalShear (u, v))) = L := by
      funext u
      dsimp [L, aux_diagonalShear]
    rw [hslice_eq] at hslice
    exact hslice
  have hLInt : Integrable (fun u : ℝ => (L u : ℂ)) :=
    (Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hL).ofReal
  have hLCont : Continuous (fun u : ℝ => (L u : ℂ)) :=
    Complex.continuous_ofReal.comp hL.1
  have hFourierZero (ξ : ℝ) :
      FourierTransform.fourier (fun u : ℝ => (L u : ℂ)) ξ = 0 := by
    rw [← aux_fourierReal_eq_fourier]
    change aux_fourierReal (fun u : ℝ => ∫ p : ℝ, hMultiplier γ i j (u + p, p)) ξ = 0
    rw [aux_fourierReal_diagonalSlice (hMultiplier γ i j) hH]
    exact hMultiplier_fourier_diagonal_vanishing γ i j ξ
  have hFourierInt : Integrable (FourierTransform.fourier (fun u : ℝ => (L u : ℂ))) := by
    apply (integrable_zero ℝ ℂ volume).congr
    filter_upwards [] with ξ
    exact (hFourierZero ξ).symm
  have hinv : FourierTransformInv.fourierInv
      (FourierTransform.fourier (fun u : ℝ => (L u : ℂ))) =
      fun u : ℝ => (L u : ℂ) :=
    hLCont.fourierInv_fourier_eq hLInt hFourierInt
  have hzeroC : (L z : ℂ) = 0 := by
    calc
      (L z : ℂ) = FourierTransformInv.fourierInv
          (FourierTransform.fourier (fun u : ℝ => (L u : ℂ))) z :=
        (congrFun hinv z).symm
      _ = FourierTransformInv.fourierInv (0 : ℝ → ℂ) z := by
        change VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ)
            (FourierTransform.fourier (fun u : ℝ => (L u : ℂ))) z =
          VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) 0 z
        apply congrFun
        apply VectorFourier.fourierIntegral_congr_ae 𝐞 volume (-innerₗ ℝ)
        filter_upwards [] with ξ
        exact hFourierZero ξ
      _ = 0 := by
        change VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) (0 : ℝ → ℂ) z = 0
        unfold VectorFourier.fourierIntegral
        simp
  have hzero : L z = 0 := by
    exact_mod_cast hzeroC
  simpa [L] using hzero

/-- Translation is continuous in ordinary `L¹` for one-dimensional Wiener functions. -/
theorem aux_w0_translation_tendsto_integral_norm_oneDim
    {f : ℝ → ℝ} (hf : MemW0 f) :
    Tendsto (fun p : ℝ => ∫ v : ℝ, ‖f (v - p) - f v‖)
      (nhds 0) (nhds 0) := by
  let B : ℝ → ℝ := fun v => 2 * wienerEnvelope f 1 v
  have hB_int : Integrable B := by
    exact hf.aux_integrable_envelope.const_mul 2
  have hsmall : ∀ᶠ p : ℝ in nhds 0, ‖p‖ ≤ 1 := by
    exact Metric.eventually_nhds_iff.2 ⟨1, zero_lt_one, by
      intro p hp
      simpa [dist_zero_right] using hp.le⟩
  have hmeas : ∀ᶠ p : ℝ in nhds 0,
      AEStronglyMeasurable (fun v : ℝ => ‖f (v - p) - f v‖) := by
    filter_upwards [] with p
    exact ((hf.aux_continuous.comp (continuous_id.sub continuous_const)).sub
      hf.aux_continuous).norm.aestronglyMeasurable
  have hbound : ∀ᶠ p : ℝ in nhds 0,
      ∀ᵐ v : ℝ, ‖‖f (v - p) - f v‖‖ ≤ B v := by
    filter_upwards [hsmall] with p hp
    filter_upwards [] with v
    have hpball : v - p ∈ closedBall v 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using hp
    have hzero : v ∈ closedBall v 1 := Metric.mem_closedBall_self zero_le_one
    have hfirst : ‖f (v - p)‖ ≤ wienerEnvelope f 1 v :=
      aux_norm_le_wienerEnvelope_of_mem_closedBall hf.aux_continuous hpball
    have hsecond : ‖f v‖ ≤ wienerEnvelope f 1 v :=
      aux_norm_le_wienerEnvelope_of_mem_closedBall hf.aux_continuous hzero
    dsimp [B]
    simp only [abs_of_nonneg (abs_nonneg _)]
    calc
      ‖f (v - p) - f v‖ ≤ ‖f (v - p)‖ + ‖f v‖ := norm_sub_le _ _
      _ ≤ wienerEnvelope f 1 v + wienerEnvelope f 1 v := add_le_add hfirst hsecond
      _ = 2 * wienerEnvelope f 1 v := by ring
  have hlim : ∀ᵐ v : ℝ,
      Tendsto (fun p : ℝ => ‖f (v - p) - f v‖) (nhds 0) (nhds (0 : ℝ)) := by
    filter_upwards [] with v
    have harg : Tendsto (fun p : ℝ => v - p) (nhds 0) (nhds v) := by
      have hconst : Tendsto (fun _ : ℝ => v) (nhds 0) (nhds v) := tendsto_const_nhds
      have hid : Tendsto (fun p : ℝ => p) (nhds 0) (nhds 0) := tendsto_id
      simpa using hconst.sub hid
    have hdiff : Tendsto (fun p : ℝ => f (v - p) - f v) (nhds 0) (nhds 0) := by
      have hconst : Tendsto (fun _ : ℝ => f v) (nhds 0) (nhds (f v)) := tendsto_const_nhds
      simpa only [Function.comp_apply, sub_self] using
        ((hf.aux_continuous.tendsto v).comp harg).sub hconst
    simpa using hdiff.norm
  simpa using
    (MeasureTheory.tendsto_integral_filter_of_dominated_convergence B hmeas hbound hB_int hlim)

/-- Change of scale for the translated standard bump. -/
theorem aux_standardBumpRescale_translation_integral_norm
    (t q : ℝ) (ht : 0 < t) :
    (∫ y : ℝ, |standardBumpRescale t (y - q) - standardBumpRescale t y|) =
      ∫ z : ℝ, |standardBump (z - q / t) - standardBump z| := by
  let g : ℝ → ℝ := fun z => |standardBump (z - q / t) - standardBump z|
  calc
    (∫ y : ℝ, |standardBumpRescale t (y - q) - standardBumpRescale t y|) =
        ∫ y : ℝ, t⁻¹ * g (t⁻¹ * y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          dsimp [g, standardBumpRescale]
          have htinv : 0 < t⁻¹ := inv_pos.mpr ht
          rw [← mul_sub, abs_mul, abs_of_pos htinv]
          congr 1
          congr 2 <;> field_simp
    _ = t⁻¹ * ∫ y : ℝ, g (t⁻¹ * y) := by
          rw [integral_const_mul]
    _ = t⁻¹ * (|(t⁻¹)⁻¹| * ∫ z : ℝ, g z) := by
          rw [Measure.integral_comp_mul_left]
          simp only [smul_eq_mul]
    _ = ∫ z : ℝ, |standardBump (z - q / t) - standardBump z| := by
          dsimp [g]
          rw [inv_inv, abs_of_pos ht]
          calc
            t⁻¹ * (t * ∫ z : ℝ, |standardBump (z - q / t) - standardBump z|) =
                (t⁻¹ * t) * ∫ z : ℝ, |standardBump (z - q / t) - standardBump z| := by ring
            _ = ∫ z : ℝ, |standardBump (z - q / t) - standardBump z| := by
                rw [inv_mul_cancel₀ ht.ne', one_mul]

/-- A uniform `L¹` bound for translated standard-bump differences. -/
theorem aux_standardBump_translation_integral_norm_le (r : ℝ) :
    (∫ z : ℝ, ‖standardBump (z - r) - standardBump z‖) ≤
      2 * ∫ z : ℝ, ‖standardBump z‖ := by
  have hphi : Integrable (fun z : ℝ => ‖standardBump z‖) :=
    aux_integrable_standardBump.norm
  have hphi_trans : Integrable (fun z : ℝ => ‖standardBump (z - r)‖) := by
    simpa using hphi.comp_sub_right r
  have hdiff : Integrable (fun z : ℝ => standardBump (z - r) - standardBump z) :=
    (aux_integrable_standardBump.comp_sub_right r).sub aux_integrable_standardBump
  calc
    (∫ z : ℝ, ‖standardBump (z - r) - standardBump z‖) ≤
        ∫ z : ℝ, (‖standardBump (z - r)‖ + ‖standardBump z‖) := by
          exact integral_mono hdiff.norm (hphi_trans.add hphi)
            (fun z => norm_sub_le _ _)
    _ = (∫ z : ℝ, ‖standardBump (z - r)‖) + ∫ z : ℝ, ‖standardBump z‖ := by
          rw [integral_add hphi_trans hphi]
    _ = 2 * ∫ z : ℝ, ‖standardBump z‖ := by
          rw [integral_sub_right_eq_self (fun z : ℝ => ‖standardBump z‖) r]
          ring

/-- The one-dimensional translation-distance functional of a Wiener function is continuous. -/
theorem aux_w0_translation_integral_norm_continuous_oneDim
    {f : ℝ → ℝ} (hf : MemW0 f) :
    Continuous (fun p : ℝ => ∫ z : ℝ, ‖f (z - p) - f z‖) := by
  let ω : ℝ → ℝ := fun p => ∫ z : ℝ, ‖f (z - p) - f z‖
  have hfint : Integrable f :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hf
  have hω_diff (p p₀ : ℝ) : |ω p - ω p₀| ≤ ω (p - p₀) := by
    have hA : Integrable (fun z : ℝ => f (z - p) - f z) :=
      (hfint.comp_sub_right p).sub hfint
    have hB : Integrable (fun z : ℝ => f (z - p₀) - f z) :=
      (hfint.comp_sub_right p₀).sub hfint
    have hR : Integrable (fun z : ℝ => ‖f (z - p) - f (z - p₀)‖) :=
      ((hfint.comp_sub_right p).sub (hfint.comp_sub_right p₀)).norm
    have hL : Integrable (fun z : ℝ =>
        |‖f (z - p) - f z‖ - ‖f (z - p₀) - f z‖|) :=
      (hA.norm.sub hB.norm).norm
    have hbound (z : ℝ) :
        |‖f (z - p) - f z‖ - ‖f (z - p₀) - f z‖| ≤
          ‖f (z - p) - f (z - p₀)‖ := by
      calc
        |‖f (z - p) - f z‖ - ‖f (z - p₀) - f z‖| ≤
            ‖(f (z - p) - f z) - (f (z - p₀) - f z)‖ :=
              abs_norm_sub_norm_le _ _
        _ = ‖f (z - p) - f (z - p₀)‖ := by ring_nf
    have htranslate :
        (∫ z : ℝ, ‖f (z - p) - f (z - p₀)‖) = ω (p - p₀) := by
      change (∫ z : ℝ, ‖f (z - p) - f (z - p₀)‖) =
        ∫ z : ℝ, ‖f (z - (p - p₀)) - f z‖
      calc
        (∫ z : ℝ, ‖f (z - p) - f (z - p₀)‖) =
            ∫ z : ℝ, ‖f ((z - p₀) - (p - p₀)) - f (z - p₀)‖ := by
              apply integral_congr_ae
              filter_upwards [] with z
              congr 2 <;> ring
        _ = ∫ z : ℝ, ‖f (z - (p - p₀)) - f z‖ :=
              integral_sub_right_eq_self (fun z : ℝ => ‖f (z - (p - p₀)) - f z‖) p₀
    change |(∫ z : ℝ, ‖f (z - p) - f z‖) -
        ∫ z : ℝ, ‖f (z - p₀) - f z‖| ≤ _
    rw [← integral_sub hA.norm hB.norm]
    calc
      |∫ z : ℝ, (‖f (z - p) - f z‖ - ‖f (z - p₀) - f z‖)| ≤
          ∫ z : ℝ, |‖f (z - p) - f z‖ - ‖f (z - p₀) - f z‖| :=
            abs_integral_le_integral_abs
      _ ≤ ∫ z : ℝ, ‖f (z - p) - f (z - p₀)‖ :=
            integral_mono hL hR hbound
      _ = ω (p - p₀) := htranslate
  rw [continuous_iff_continuousAt]
  intro p₀
  change Tendsto ω (nhds p₀) (nhds (ω p₀))
  have harg : Tendsto (fun p : ℝ => p - p₀) (nhds p₀) (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => p₀) (nhds p₀) (nhds p₀) := tendsto_const_nhds
    have hid : Tendsto (fun p : ℝ => p) (nhds p₀) (nhds p₀) := tendsto_id
    simpa using hid.sub hconst
  have hω_zero : Tendsto ω (nhds 0) (nhds 0) := by
    simpa only [ω] using aux_w0_translation_tendsto_integral_norm_oneDim hf
  have hupper : Tendsto (fun p : ℝ => ω (p - p₀)) (nhds p₀) (nhds 0) :=
    hω_zero.comp harg
  have habs : Tendsto (fun p : ℝ => |ω p - ω p₀|) (nhds p₀) (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (nhds p₀) (nhds 0)) hupper
    · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
    · exact Filter.Eventually.of_forall fun p => hω_diff p p₀
  have hsub : Tendsto (fun p : ℝ => ω p - ω p₀) (nhds p₀) (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 (by
      simpa only [Real.norm_eq_abs] using habs)
  simpa using hsub.add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => ω p₀) (nhds p₀) (nhds (ω p₀)))

/-- Dominated convergence for large-scale translated standard-bump cancellation. -/
theorem aux_weighted_standardBump_translation_tendsto
    (g : ℝ → ℝ) (hg : Integrable g) (hg_nonneg : ∀ q : ℝ, 0 ≤ g q) :
    Tendsto (fun t : ℝ => ∫ q : ℝ,
      (∫ z : ℝ, ‖standardBump (z - q / t) - standardBump z‖) * g q)
      atTop (nhds 0) := by
  let ω : ℝ → ℝ := fun p => ∫ z : ℝ, ‖standardBump (z - p) - standardBump z‖
  have hωcont : Continuous ω := by
    exact aux_w0_translation_integral_norm_continuous_oneDim aux_standardBump_memW0
  have hω_zero : Tendsto ω (nhds 0) (nhds 0) := by
    simpa only [ω] using
      aux_w0_translation_tendsto_integral_norm_oneDim aux_standardBump_memW0
  let B : ℝ → ℝ := fun q => (2 * ∫ z : ℝ, ‖standardBump z‖) * g q
  have hB_int : Integrable B := by
    exact hg.const_mul _
  have hmeas : ∀ᶠ t : ℝ in atTop, AEStronglyMeasurable (fun q : ℝ => ω (q / t) * g q) := by
    filter_upwards [] with t
    have hdiv : Continuous (fun q : ℝ => q / t) := by fun_prop
    exact ((hωcont.comp hdiv).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ᵐ q : ℝ,
      ‖ω (q / t) * g q‖ ≤ B q := by
    filter_upwards [] with t
    filter_upwards [] with q
    have hω_nonneg : 0 ≤ ω (q / t) := by
      dsimp [ω]
      exact integral_nonneg fun _ => abs_nonneg _
    have hω_le : ω (q / t) ≤ 2 * ∫ z : ℝ, ‖standardBump z‖ := by
      dsimp [ω]
      exact aux_standardBump_translation_integral_norm_le _
    dsimp [B]
    rw [abs_of_nonneg (mul_nonneg hω_nonneg (hg_nonneg q))]
    exact mul_le_mul_of_nonneg_right hω_le (hg_nonneg q)
  have hlim : ∀ᵐ q : ℝ,
      Tendsto (fun t : ℝ => ω (q / t) * g q) atTop (nhds (0 : ℝ)) := by
    filter_upwards [] with q
    have harg : Tendsto (fun t : ℝ => q / t) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => q) atTop (nhds q)).mul
          tendsto_inv_atTop_zero)
    simpa using (hω_zero.comp harg).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => g q) atTop (nhds (g q)))
  change Tendsto (fun t : ℝ => ∫ q : ℝ, ω (q / t) * g q) atTop (nhds 0)
  simpa using
    (MeasureTheory.tendsto_integral_filter_of_dominated_convergence B hmeas hbound hB_int hlim)

/-- The coordinate reorder `((x,y),q) ↦ ((x,q),y)`. -/
noncomputable def aux_lMultiplierAtScale_largeScaleReorder :
    (RealPlane × ℝ) ≃L[ℝ] (RealPlane × ℝ) where
  toFun := fun p => ((p.1.1, p.2), p.1.2)
  invFun := fun p => ((p.1.1, p.2), p.1.2)
  left_inv := by
    intro p
    rcases p with ⟨⟨x, y⟩, q⟩
    rfl
  right_inv := by
    intro p
    rcases p with ⟨⟨x, q⟩, y⟩
    rfl
  map_add' := by
    intro p q
    rcases p with ⟨⟨x, y⟩, r⟩
    rcases q with ⟨⟨x', y'⟩, r'⟩
    rfl
  map_smul' := by
    intro c p
    rcases p with ⟨⟨x, y⟩, q⟩
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The coordinate shear `((x,y),q) ↦ ((x,q),y-q)`. -/
noncomputable def aux_lMultiplierAtScale_largeScaleShear :
    (RealPlane × ℝ) ≃L[ℝ] (RealPlane × ℝ) where
  toFun := fun p => ((p.1.1, p.2), p.1.2 - p.2)
  invFun := fun p => ((p.1.1, p.2 + p.1.2), p.1.2)
  left_inv := by
    intro p
    rcases p with ⟨⟨x, y⟩, q⟩
    ext <;> dsimp <;> ring
  right_inv := by
    intro p
    rcases p with ⟨⟨x, q⟩, r⟩
    ext <;> dsimp <;> ring
  map_add' := by
    intro p q
    rcases p with ⟨⟨x, y⟩, r⟩
    rcases q with ⟨⟨x', y'⟩, r'⟩
    ext <;> dsimp <;> ring
  map_smul' := by
    intro c p
    rcases p with ⟨⟨x, y⟩, q⟩
    ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The cancellative large-scale integrand remains in `W₀` on three variables. -/
theorem aux_lMultiplierAtScale_largeScaleIntegrand_memW0
    {F : RealPlane → ℝ} (hF : MemW0 F) (t : ℝ) (ht : 0 < t) :
    MemW0 (fun z : RealPlane × ℝ =>
      F (z.1.1, z.2) *
        (standardBumpRescale t (z.1.2 - z.2) - standardBumpRescale t z.1.2)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (RealPlane × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let P : RealPlane × ℝ → ℝ := fun z => F z.1 * standardBumpRescale t z.2
  have hP : MemW0 P := by
    simpa [P] using hF.aux_mul_prod (aux_standardBumpRescale_memW0 ht)
  have hshift : MemW0 (P ∘ aux_lMultiplierAtScale_largeScaleShear) :=
    Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hP
      aux_lMultiplierAtScale_largeScaleShear
  have hplain : MemW0 (P ∘ aux_lMultiplierAtScale_largeScaleReorder) :=
    Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hP
      aux_lMultiplierAtScale_largeScaleReorder
  have hsub := Codex.Preliminaries.KKernels.aux_memW0_sub hshift hplain
  convert hsub using 1
  funext z
  rcases z with ⟨⟨x, y⟩, q⟩
  dsimp [P, Function.comp_def, aux_lMultiplierAtScale_largeScaleShear,
    aux_lMultiplierAtScale_largeScaleReorder]
  ring

/-- Cancellation bounds the diagonal convolution by the translated bump error. -/
theorem aux_lMultiplierAtScale_largeScaleConvolution_bound
    {F : RealPlane → ℝ} (hF : MemW0 F)
    (hzero : ∀ x : ℝ, (∫ q : ℝ, F (x, q)) = 0)
    (t : ℝ) (ht : 0 < t) :
    (∫ xy : RealPlane, |∫ q : ℝ,
      F (xy.1, q) * standardBumpRescale t (xy.2 - q)|) ≤
      ∫ q : ℝ, (∫ x : ℝ, ‖F (x, q)‖) *
        (∫ z : ℝ, ‖standardBump (z - q / t) - standardBump z‖) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (RealPlane × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let φ : ℝ → ℝ := standardBumpRescale t
  let K : RealPlane × ℝ → ℝ := fun z =>
    F (z.1.1, z.2) * (φ (z.1.2 - z.2) - φ z.1.2)
  have hKmem : MemW0 K := by
    simpa [K, φ] using aux_lMultiplierAtScale_largeScaleIntegrand_memW0 hF t ht
  have hK : Integrable K :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hKmem
  have hFint : Integrable F :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hF
  have hφmem : MemW0 φ := by
    simpa [φ] using aux_standardBumpRescale_memW0 ht
  have hφint : Integrable φ :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hφmem
  let C : RealPlane → ℝ := fun xy => ∫ q : ℝ, F (xy.1, q) * φ (xy.2 - q)
  let R : RealPlane → ℝ := fun xy => ∫ q : ℝ, ‖K (xy, q)‖
  have hC_eq (xy : RealPlane) : C xy = ∫ q : ℝ, K (xy, q) := by
    have hFslice_mem : MemW0 (fun q : ℝ => F (xy.1, q)) :=
      hF.aux_memW0_slice_of_addHaar xy.1
    have hFslice : Integrable (fun q : ℝ => F (xy.1, q)) :=
      Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hFslice_mem
    have hB : Integrable (fun q : ℝ => F (xy.1, q) * φ xy.2) :=
      hFslice.mul_const _
    have hKslice : Integrable (fun q : ℝ => K (xy, q)) :=
      Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
        (hKmem.aux_memW0_slice_of_addHaar xy)
    have hA : Integrable (fun q : ℝ => F (xy.1, q) * φ (xy.2 - q)) := by
      have hsum := hKslice.add hB
      refine hsum.congr ?_
      filter_upwards [] with q
      dsimp [K]
      ring
    have hBzero : (∫ q : ℝ, F (xy.1, q) * φ xy.2) = 0 := by
      rw [integral_mul_const, hzero xy.1, zero_mul]
    dsimp [C]
    calc
      (∫ q : ℝ, F (xy.1, q) * φ (xy.2 - q)) =
          (∫ q : ℝ, F (xy.1, q) * φ (xy.2 - q)) -
            ∫ q : ℝ, F (xy.1, q) * φ xy.2 := by rw [hBzero, sub_zero]
      _ = ∫ q : ℝ,
          F (xy.1, q) * φ (xy.2 - q) - F (xy.1, q) * φ xy.2 :=
            (integral_sub hA hB).symm
      _ = ∫ q : ℝ, K (xy, q) := by
            apply integral_congr_ae
            filter_upwards [] with q
            dsimp [K]
            ring
  have hC : Integrable C := by
    have hs := hK.integral_prod_left
    convert hs using 1
    funext xy
    exact hC_eq xy
  have hR : Integrable R := by
    have hs := hK.integral_norm_prod_left
    convert hs using 1
  have hpoint (xy : RealPlane) : |C xy| ≤ R xy := by
    rw [hC_eq xy, ← Real.norm_eq_abs]
    exact norm_integral_le_integral_norm _
  have hfirst : (∫ xy : RealPlane, |C xy|) ≤ ∫ xy : RealPlane, R xy := by
    have hCnorm : Integrable (fun xy : RealPlane => |C xy|) := by
      simpa only [Real.norm_eq_abs] using hC.norm
    exact integral_mono hCnorm hR hpoint
  let Fswap : RealPlane → ℝ := fun xq => F (xq.2, xq.1)
  have hFswap : MemW0 Fswap := by
    have hs := Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hF
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
    convert hs using 1
    funext xq
    rcases xq with ⟨x, q⟩
    rfl
  have hinner (q : ℝ) :
      (∫ xy : RealPlane, ‖K (xy, q)‖) =
        (∫ x : ℝ, ‖F (x, q)‖) *
          ∫ y : ℝ, ‖φ (y - q) - φ y‖ := by
    have hFxmem : MemW0 (fun x : ℝ => F (x, q)) := by
      have hs := hFswap.aux_memW0_slice_of_addHaar q
      convert hs using 1
    have hFx : Integrable (fun x : ℝ => ‖F (x, q)‖) :=
      (Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hFxmem).norm
    have hφdiff : Integrable (fun y : ℝ => φ (y - q) - φ y) :=
      (hφint.comp_sub_right q).sub hφint
    have hφnorm : Integrable (fun y : ℝ => ‖φ (y - q) - φ y‖) := hφdiff.norm
    calc
      (∫ xy : RealPlane, ‖K (xy, q)‖) =
          ∫ xy : RealPlane, ‖F (xy.1, q)‖ * ‖φ (xy.2 - q) - φ xy.2‖ := by
            apply integral_congr_ae
            filter_upwards [] with xy
            dsimp [K]
            rw [abs_mul]
      _ = (∫ x : ℝ, ‖F (x, q)‖) * ∫ y : ℝ, ‖φ (y - q) - φ y‖ := by
            simpa only [Measure.volume_eq_prod] using
              (integral_prod_mul (fun x : ℝ => ‖F (x, q)‖)
                (fun y : ℝ => ‖φ (y - q) - φ y‖))
  change (∫ xy : RealPlane, |C xy|) ≤ _
  calc
    (∫ xy : RealPlane, |C xy|) ≤ ∫ xy : RealPlane, R xy := hfirst
    _ = ∫ q : ℝ, ∫ xy : RealPlane, ‖K (xy, q)‖ := by
      change (∫ xy : RealPlane, ∫ q : ℝ, ‖K (xy, q)‖) = _
      simpa only [Measure.volume_eq_prod] using (integral_integral_swap hK.norm)
    _ = ∫ q : ℝ, (∫ x : ℝ, ‖F (x, q)‖) *
          ∫ y : ℝ, ‖φ (y - q) - φ y‖ := by
      apply integral_congr_ae
      filter_upwards [] with q
      exact hinner q
    _ = ∫ q : ℝ, (∫ x : ℝ, ‖F (x, q)‖) *
          (∫ z : ℝ, ‖standardBump (z - q / t) - standardBump z‖) := by
      apply integral_congr_ae
      filter_upwards [] with q
      have hscale : (∫ y : ℝ, ‖φ (y - q) - φ y‖) =
          ∫ z : ℝ, ‖standardBump (z - q / t) - standardBump z‖ := by
        simpa only [φ, Real.norm_eq_abs] using
          aux_standardBumpRescale_translation_integral_norm t q ht
      rw [hscale]

/-- The raw large-scale `L¹` convergence for `L_{γ,t}`. -/
theorem aux_lMultiplierAtScale_tendsto_integral_norm_atTop
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) :
    Tendsto (fun t : ℝ => ∫ v : RealPlane, |lMultiplierAtScale γ t i j v|)
      atTop (nhds 0) := by
  let F : RealPlane → ℝ := fun xq => hMultiplier γ i j (xq.1 + xq.2, xq.2)
  have hH : MemW0 (hMultiplier γ i j) := hMultiplier_memDoubleSequence γ i j
  have hF : MemW0 F := by
    change MemW0 (hMultiplier γ i j ∘ aux_diagonalShear)
    exact Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hH
      aux_diagonalShear
  have hzero (x : ℝ) : (∫ q : ℝ, F (x, q)) = 0 := by
    exact hMultiplier_vanishing_integral γ i j x
  let g : ℝ → ℝ := fun q => ∫ x : ℝ, ‖F (x, q)‖
  have hFint : Integrable F :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hF
  have hg : Integrable g := by
    simpa [g] using hFint.integral_norm_prod_right
  have hg_nonneg (q : ℝ) : 0 ≤ g q := by
    dsimp [g]
    exact integral_nonneg fun _ => abs_nonneg _
  have houter := aux_weighted_standardBump_translation_tendsto g hg hg_nonneg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)) houter
  · filter_upwards [] with t
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hcoord (xy : RealPlane) :
        lMultiplierAtScale γ t i j (aux_diagonalShear xy) =
          ∫ q : ℝ, F (xy.1, q) * standardBumpRescale t (xy.2 - q) := by
      rcases xy with ⟨x, y⟩
      let A : ℝ → ℝ := fun p =>
        hMultiplier γ i j (x + y - p, y - p) * standardBumpRescale t p
      calc
        lMultiplierAtScale γ t i j (aux_diagonalShear (x, y)) = ∫ p : ℝ, A p := by
          apply integral_congr_ae
          filter_upwards [] with p
          dsimp [A, lMultiplierAtScale, aux_diagonalShear]
        _ = ∫ q : ℝ, A (y - q) :=
          (integral_sub_left_eq_self A volume y).symm
        _ = ∫ q : ℝ, F (x, q) * standardBumpRescale t (y - q) := by
          apply integral_congr_ae
          filter_upwards [] with q
          dsimp [A, F]
          ring_nf
    have hmeasure :
        (∫ xy : RealPlane, |lMultiplierAtScale γ t i j (aux_diagonalShear xy)|) =
          ∫ v : RealPlane, |lMultiplierAtScale γ t i j v| :=
      aux_measurePreserving_diagonalShear.integral_comp
        aux_diagonalShear.toHomeomorph.measurableEmbedding
        (fun v : RealPlane => |lMultiplierAtScale γ t i j v|)
    calc
      (∫ v : RealPlane, |lMultiplierAtScale γ t i j v|) =
          ∫ xy : RealPlane, |lMultiplierAtScale γ t i j (aux_diagonalShear xy)| :=
            hmeasure.symm
      _ = ∫ xy : RealPlane, |∫ q : ℝ,
          F (xy.1, q) * standardBumpRescale t (xy.2 - q)| := by
            apply integral_congr_ae
            filter_upwards [] with xy
            rw [hcoord xy]
      _ ≤ ∫ q : ℝ, (∫ x : ℝ, ‖F (x, q)‖) *
          (∫ z : ℝ, ‖standardBump (z - q / t) - standardBump z‖) :=
            aux_lMultiplierAtScale_largeScaleConvolution_bound hF hzero t ht
      _ = ∫ q : ℝ,
          (∫ z : ℝ, ‖standardBump (z - q / t) - standardBump z‖) * g q := by
            apply integral_congr_ae
            filter_upwards [] with q
            dsimp [g]
            ring

/-- The large-scale `L¹` convergence in the blueprint's `eLpNorm` convention. -/
theorem lMultiplierAtScale_tendsto_zero
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) :
    Tendsto (fun t : ℝ => eLpNorm (lMultiplierAtScale γ t i j) 1 volume)
      atTop (nhds 0) := by
  have hraw := aux_lMultiplierAtScale_tendsto_integral_norm_atTop γ i j
  have hraw' : Tendsto (fun t : ℝ => ENNReal.ofReal
      (∫ v : RealPlane, |lMultiplierAtScale γ t i j v|)) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hraw
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (nhds 0)) hraw'
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hL : Integrable (lMultiplierAtScale γ t i j) :=
      Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
        (lMultiplierAtScale_memDoubleSequence γ ht i j)
    refine aux_eLpNorm_one_le_of_integral_norm_le hL ?_
    simp only [Real.norm_eq_abs]
    exact le_rfl

theorem aux_hMultiplier_diagonal_translate_integrable
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (v : RealPlane) :
    Integrable (fun p : ℝ => hMultiplier γ i j (v.1 - p, v.2 - p)) := by
  let S : RealPlane → ℝ := hMultiplier γ i j ∘ aux_diagonalShear
  have hS : MemW0 S := by
    exact Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv
      (hMultiplier_memDoubleSequence γ i j) aux_diagonalShear
  have hG : MemW0 (fun q : ℝ => hMultiplier γ i j ((v.1 - v.2) + q, q)) := by
    simpa [S, Function.comp_def, aux_diagonalShear] using
      hS.aux_memW0_slice_of_addHaar (v.1 - v.2)
  have hGint : Integrable (fun q : ℝ => hMultiplier γ i j ((v.1 - v.2) + q, q)) :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hG
  have hmp : MeasurePreserving (fun p : ℝ => v.2 - p) volume volume := by
    convert (Measure.measurePreserving_neg (volume : Measure ℝ)).comp
      (measurePreserving_sub_right (volume : Measure ℝ) v.2) using 1
    funext p
    simp only [Function.comp_apply]
    change v.2 - p = -(p - v.2)
    ring
  have hcomp := hmp.integrable_comp_of_integrable hGint
  convert hcomp using 1
  funext p
  dsimp
  ring_nf

theorem aux_integrable_lMultiplierAtScale_integrand
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) (v : RealPlane)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : ℝ => hMultiplier γ i j (v.1 - p, v.2 - p) *
      standardBumpRescale t p) := by
  have hH := aux_hMultiplier_diagonal_translate_integrable γ i j v
  have hphi : MemW0 (standardBumpRescale t) := aux_standardBumpRescale_memW0 ht
  have hmeas : AEStronglyMeasurable (standardBumpRescale t) volume :=
    hphi.aux_continuous.aestronglyMeasurable
  have hbound : ∀ p : ℝ, ‖standardBumpRescale t p‖ ≤ t⁻¹ * (3 / 2) := by
    intro p
    rw [standardBumpRescale, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr ht)]
    exact mul_le_mul_of_nonneg_left (aux_standardBump_abs_le_threeHalves _) (inv_nonneg.mpr ht.le)
  exact hH.mul_bdd hmeas (Filter.Eventually.of_forall hbound)

theorem aux_lMultiplierAtScale_sub_eq_convolution_difference
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    lMultiplierAtScale γ s i j - lMultiplierAtScale γ t i j = fun v =>
      ∫ p : ℝ, hMultiplier γ i j (v.1 - p, v.2 - p) *
        (standardBumpRescale s p - standardBumpRescale t p) := by
  funext v
  rw [Pi.sub_apply, lMultiplierAtScale, lMultiplierAtScale]
  rw [← integral_sub
    (aux_integrable_lMultiplierAtScale_integrand γ i j v hs)
    (aux_integrable_lMultiplierAtScale_integrand γ i j v ht)]
  apply integral_congr_ae
  filter_upwards [] with p
  ring

theorem aux_lMultiplier_vertical_eq
    {n : ℕ} (γ : GeometricParameters n) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 = 0) :
    lMultiplier γ ι i j =
      lMultiplierAtScale γ (γ.scales i 1 (j + ι.1.2 - 1)) i j -
        lMultiplierAtScale γ (γ.scales i 1 (j + ι.1.2)) i j := by
  rw [aux_lMultiplierAtScale_sub_eq_convolution_difference _ _ _
    (aux_spacedSequence_pos (γ.scales_spaced i 1) _)
    (aux_spacedSequence_pos (γ.scales_spaced i 1) _)]
  unfold lMultiplier
  simp [hzero]

theorem aux_lMultiplier_positive_eq
    {n : ℕ} (γ : GeometricParameters n) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 ≠ 0) (hpositive : 0 < ι.1.1) :
    lMultiplier γ ι i j =
      lMultiplierAtScale γ ((2 : ℝ) ^ (ι.1.1 - 1) *
        γ.scales i 1 (j + (geometricDelta γ : ℤ))) i j -
        lMultiplierAtScale γ ((2 : ℝ) ^ ι.1.1 *
          γ.scales i 1 (j + (geometricDelta γ : ℤ))) i j := by
  rw [aux_lMultiplierAtScale_sub_eq_convolution_difference _ _ _
    (mul_pos (zpow_pos (by norm_num) _)
      (aux_spacedSequence_pos (γ.scales_spaced i 1) _))
    (mul_pos (zpow_pos (by norm_num) _)
      (aux_spacedSequence_pos (γ.scales_spaced i 1) _))]
  unfold lMultiplier
  simp [hzero, hpositive]

theorem aux_lMultiplier_negative_eq
    {n : ℕ} (γ : GeometricParameters n) (ι : MultiplierIndex γ)
    (i : Fin γ.k) (j : ℤ) (hzero : ι.1.1 ≠ 0) (hnegative : ι.1.1 < 0) :
    lMultiplier γ ι i j =
      lMultiplierAtScale γ ((2 : ℝ) ^ ι.1.1 *
        γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) i j -
        lMultiplierAtScale γ ((2 : ℝ) ^ (ι.1.1 + 1) *
          γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) i j := by
  rw [aux_lMultiplierAtScale_sub_eq_convolution_difference _ _ _
    (mul_pos (zpow_pos (by norm_num) _)
      (aux_spacedSequence_pos (γ.scales_spaced i 1) _))
    (mul_pos (zpow_pos (by norm_num) _)
      (aux_spacedSequence_pos (γ.scales_spaced i 1) _))]
  unfold lMultiplier
  simp [hzero, not_lt_of_ge hnegative.le]

theorem aux_lMultiplierPartialSum_boundary_tendsto_hMultiplier
    {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ) :
    Tendsto (fun N : ℕ => eLpNorm
      ((lMultiplierAtScale γ
          ((2 : ℝ) ^ (-(N : ℤ)) *
            γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) i j -
        lMultiplierAtScale γ
          ((2 : ℝ) ^ (N : ℤ) *
            γ.scales i 1 (j + (geometricDelta γ : ℤ))) i j) -
        hMultiplier γ i j) 1 volume) atTop (nhds 0) := by
  let aMinus : ℝ := γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)
  let aPlus : ℝ := γ.scales i 1 (j + (geometricDelta γ : ℤ))
  have haMinus : 0 < aMinus :=
    aux_spacedSequence_pos (γ.scales_spaced i 1) _
  have haPlus : 0 < aPlus :=
    aux_spacedSequence_pos (γ.scales_spaced i 1) _
  have hsmallScale : Tendsto (fun N : ℕ => (2 : ℝ) ^ (-(N : ℤ)) * aMinus)
      atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    have hpow : Tendsto (fun N : ℕ => ((1 / 2 : ℝ) ^ N)) atTop
        (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_pow_atTop_nhdsWithin_zero_of_lt_one (by norm_num) (by norm_num)
    have hmul : Tendsto (fun N : ℕ => ((1 / 2 : ℝ) ^ N) * aMinus)
        atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      simpa using Filter.TendstoNhdsWithinIoi.mul_const haMinus hpow
    refine hmul.congr' ?_
    filter_upwards [] with N
    simp [zpow_neg, zpow_natCast, div_pow]
  have hlargeScale : Tendsto (fun N : ℕ => (2 : ℝ) ^ (N : ℤ) * aPlus)
      atTop atTop := by
    simpa only [zpow_natCast] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const haPlus
  have hsmall : Tendsto (fun N : ℕ => eLpNorm
      (lMultiplierAtScale γ ((2 : ℝ) ^ (-(N : ℤ)) * aMinus) i j -
        hMultiplier γ i j) 1 volume) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (lMultiplierAtScale_tendsto_hMultiplier γ i j).comp hsmallScale
  have hlarge : Tendsto (fun N : ℕ => eLpNorm
      (lMultiplierAtScale γ ((2 : ℝ) ^ (N : ℤ) * aPlus) i j) 1 volume)
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (lMultiplierAtScale_tendsto_zero γ i j).comp hlargeScale
  have hsum : Tendsto (fun N : ℕ => eLpNorm
      (lMultiplierAtScale γ ((2 : ℝ) ^ (-(N : ℤ)) * aMinus) i j -
        hMultiplier γ i j) 1 volume +
      eLpNorm (lMultiplierAtScale γ ((2 : ℝ) ^ (N : ℤ) * aPlus) i j) 1 volume)
      atTop (nhds 0) := by
    simpa using hsmall.add hlarge
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0)) hsum
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with N
    have hs : 0 < (2 : ℝ) ^ (-(N : ℤ)) * aMinus :=
      mul_pos (zpow_pos (by norm_num) _) haMinus
    have hl : 0 < (2 : ℝ) ^ (N : ℤ) * aPlus :=
      mul_pos (zpow_pos (by norm_num) _) haPlus
    have hSmallMeas : AEStronglyMeasurable
        (lMultiplierAtScale γ ((2 : ℝ) ^ (-(N : ℤ)) * aMinus) i j -
          hMultiplier γ i j) volume :=
      ((lMultiplierAtScale_memDoubleSequence γ hs i j).aux_continuous.sub
        (hMultiplier_memDoubleSequence γ i j).aux_continuous).aestronglyMeasurable
    have hLargeMeas : AEStronglyMeasurable
        (lMultiplierAtScale γ ((2 : ℝ) ^ (N : ℤ) * aPlus) i j) volume :=
      (lMultiplierAtScale_memDoubleSequence γ hl i j).aux_continuous.aestronglyMeasurable
    have hrew :
        (lMultiplierAtScale γ ((2 : ℝ) ^ (-(N : ℤ)) * aMinus) i j -
          lMultiplierAtScale γ ((2 : ℝ) ^ (N : ℤ) * aPlus) i j) -
          hMultiplier γ i j =
        (lMultiplierAtScale γ ((2 : ℝ) ^ (-(N : ℤ)) * aMinus) i j -
          hMultiplier γ i j) -
          lMultiplierAtScale γ ((2 : ℝ) ^ (N : ℤ) * aPlus) i j := by
      funext v
      simp only [Pi.sub_apply]
      ring
    rw [hrew]
    exact eLpNorm_sub_le hSmallMeas hLargeMeas (by norm_num)

noncomputable def aux_lMultiplierNegIndices (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N : ℤ)) (-1)).image fun h => (h, 0)

noncomputable def aux_lMultiplierVerticalIndices (D : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(D : ℤ)) D).image fun l => (0, l)

noncomputable def aux_lMultiplierPosIndices (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 1 (N : ℤ)).image fun h => (h, 0)

theorem aux_int_natAbs_le_iff (z : ℤ) (N : ℕ) :
    z.natAbs ≤ N ↔ (-(N : ℤ) ≤ z ∧ z ≤ N) := by
  rw [← Int.ofNat_le]
  simpa only [Int.natCast_natAbs] using (abs_le (a := z) (b := (N : ℤ)))

theorem aux_lMultiplier_truncation_decomp {n : ℕ} (γ : GeometricParameters n) (N : ℕ)
    (hN : geometricDelta γ < N) :
    aux_multiplierIndexTruncation γ N =
      (aux_lMultiplierNegIndices N ∪ aux_lMultiplierVerticalIndices (geometricDelta γ)) ∪
        aux_lMultiplierPosIndices N := by
  classical
  ext x
  rcases x with ⟨h, l⟩
  simp [aux_multiplierIndexTruncation, multiplierIndexSet, aux_lMultiplierNegIndices,
    aux_lMultiplierVerticalIndices, aux_lMultiplierPosIndices, aux_int_natAbs_le_iff]
  omega

theorem aux_sum_Ico_int_telescope {A : Type*} [AddCommGroup A] (f : ℤ → A)
    (a : ℤ) (N : ℕ) :
    (∑ r ∈ Finset.Ico a (a + (N : ℤ)), (f r - f (r + 1))) =
      f a - f (a + (N : ℤ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ha : a ≤ a + (N : ℤ) := by omega
    rw [show a + ((N + 1 : ℕ) : ℤ) = (a + (N : ℤ)) + 1 by omega]
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one ha]
    rw [ih]
    abel

theorem aux_sum_range_sub_translate {A : Type*} [AddCommGroup A]
    (f : ℤ → A) (a : ℤ) (N : ℕ) :
    (∑ r ∈ Finset.range N, (f (a + r) - f (a + r + 1))) =
      f a - f (a + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    abel

theorem aux_sum_Icc_sub_translate {A : Type*} [AddCommGroup A]
    (f : ℤ → A) (a : ℤ) (N : ℕ) :
    (∑ z ∈ Finset.Icc a (a + N), (f (z - 1) - f z)) =
      f (a - 1) - f (a + N) := by
  rw [Int.Icc_eq_finset_map]
  simp only [Finset.sum_map, Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  have hlen : (a + (N : ℤ) + 1 - a).toNat = N + 1 := by omega
  rw [hlen]
  have h := aux_sum_range_sub_translate f (a - 1) (N + 1)
  convert h using 1 <;> push_cast <;> ring

noncomputable def aux_lMultiplierTerm {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k)
    (j : ℤ) (x : ℤ × ℤ) : RealPlane → ℝ := by
  classical
  exact if hx : x ∈ multiplierIndexSet γ then lMultiplier γ ⟨x, hx⟩ i j else 0

noncomputable def lMultiplierPartialSum {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (N : ℕ) : RealPlane → ℝ :=
  ∑ ι ∈ aux_multiplierIndexTruncation γ N, aux_lMultiplierTerm γ i j ι

theorem aux_lMultiplier_negative_block_eq {n : ℕ} (γ : GeometricParameters n) (i : Fin γ.k) (j : ℤ)
    (N : ℕ) :
    ∑ x ∈ aux_lMultiplierNegIndices N, aux_lMultiplierTerm γ i j x =
      lMultiplierAtScale γ ((2 : ℝ) ^ (-(N : ℤ)) *
        γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) i j -
      lMultiplierAtScale γ (γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) i j := by
  classical
  let F : ℤ → RealPlane → ℝ := fun h =>
    lMultiplierAtScale γ ((2 : ℝ) ^ h *
      γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) i j
  calc
    ∑ x ∈ aux_lMultiplierNegIndices N, aux_lMultiplierTerm γ i j x =
        ∑ h ∈ Finset.Icc (-(N : ℤ)) (-1), aux_lMultiplierTerm γ i j (h, 0) := by
      unfold aux_lMultiplierNegIndices
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact congrArg Prod.fst hab
    _ = ∑ h ∈ Finset.Icc (-(N : ℤ)) (-1), (F h - F (h + 1)) := by
      apply Finset.sum_congr rfl
      intro h hh
      have hneg : h < 0 := by
        simp only [Finset.mem_Icc] at hh
        omega
      have hmem : (h, 0) ∈ multiplierIndexSet γ := by
        simp [multiplierIndexSet, hneg.ne]
      simp [aux_lMultiplierTerm, hmem]
      simpa [F] using aux_lMultiplier_negative_eq γ ⟨(h, 0), hmem⟩ i j
        (by change h ≠ 0; omega) hneg
    _ = ∑ h ∈ Finset.Ico (-(N : ℤ)) 0, (F h - F (h + 1)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc (-(N : ℤ)) (-1)]
      norm_num
    _ = F (-(N : ℤ)) - F ((-(N : ℤ)) + (N : ℤ)) := by
      simpa using aux_sum_Ico_int_telescope F (-(N : ℤ)) N
    _ = F (-(N : ℤ)) - F 0 := by congr 2 <;> omega
    _ = _ := by simp [F]

theorem aux_lMultiplier_vertical_block_eq {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) :
    ∑ x ∈ aux_lMultiplierVerticalIndices (geometricDelta γ), aux_lMultiplierTerm γ i j x =
      lMultiplierAtScale γ (γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) i j -
      lMultiplierAtScale γ (γ.scales i 1 (j + (geometricDelta γ : ℤ))) i j := by
  classical
  let D := geometricDelta γ
  let F : ℤ → RealPlane → ℝ := fun l =>
    lMultiplierAtScale γ (γ.scales i 1 (j + l - 1)) i j
  calc
    ∑ x ∈ aux_lMultiplierVerticalIndices D, aux_lMultiplierTerm γ i j x =
        ∑ l ∈ Finset.Icc (-(D : ℤ)) D, aux_lMultiplierTerm γ i j (0, l) := by
      unfold aux_lMultiplierVerticalIndices
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact congrArg Prod.snd hab
    _ = ∑ l ∈ Finset.Icc (-(D : ℤ)) D, (F l - F (l + 1)) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hmem : (0, l) ∈ multiplierIndexSet γ := by
        change (0 ≠ 0 ∧ l = 0) ∨ (0 = 0 ∧ l.natAbs ≤ D)
        refine Or.inr ⟨rfl, (aux_int_natAbs_le_iff l D).mpr ?_⟩
        exact Finset.mem_Icc.mp hl
      simp [aux_lMultiplierTerm, hmem]
      convert aux_lMultiplier_vertical_eq γ ⟨(0, l), hmem⟩ i j rfl using 1 <;>
        simp [F] <;> congr 3 <;> omega
    _ = ∑ l ∈ Finset.Ico (-(D : ℤ)) ((D : ℤ) + 1), (F l - F (l + 1)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc (-(D : ℤ)) D]
    _ = F (-(D : ℤ)) - F ((-(D : ℤ)) + ((2 * D + 1 : ℕ) : ℤ)) := by
      have hlen : (-(D : ℤ)) + ((2 * D + 1 : ℕ) : ℤ) = (D : ℤ) + 1 := by
        push_cast
        ring
      rw [← hlen]
      exact aux_sum_Ico_int_telescope F (-(D : ℤ)) (2 * D + 1)
    _ = F (-(D : ℤ)) - F ((D : ℤ) + 1) := by congr 2 <;> omega
    _ = _ := by
      simp [F]
      congr 3 <;> omega

theorem aux_lMultiplier_positive_block_eq {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (N : ℕ) :
    ∑ x ∈ aux_lMultiplierPosIndices N, aux_lMultiplierTerm γ i j x =
      lMultiplierAtScale γ (γ.scales i 1 (j + (geometricDelta γ : ℤ))) i j -
      lMultiplierAtScale γ ((2 : ℝ) ^ (N : ℤ) *
        γ.scales i 1 (j + (geometricDelta γ : ℤ))) i j := by
  classical
  let F : ℤ → RealPlane → ℝ := fun h =>
    lMultiplierAtScale γ ((2 : ℝ) ^ (h - 1) *
      γ.scales i 1 (j + (geometricDelta γ : ℤ))) i j
  calc
    ∑ x ∈ aux_lMultiplierPosIndices N, aux_lMultiplierTerm γ i j x =
        ∑ h ∈ Finset.Icc 1 (N : ℤ), aux_lMultiplierTerm γ i j (h, 0) := by
      unfold aux_lMultiplierPosIndices
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact congrArg Prod.fst hab
    _ = ∑ h ∈ Finset.Icc 1 (N : ℤ), (F h - F (h + 1)) := by
      apply Finset.sum_congr rfl
      intro h hh
      have hpos : 0 < h := by
        exact lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hh).1
      have hmem : (h, 0) ∈ multiplierIndexSet γ := by
        change (h ≠ 0 ∧ 0 = 0) ∨ (h = 0 ∧ (0 : ℤ).natAbs ≤ geometricDelta γ)
        exact Or.inl ⟨by omega, rfl⟩
      simp [aux_lMultiplierTerm, hmem]
      convert aux_lMultiplier_positive_eq γ ⟨(h, 0), hmem⟩ i j
        (by change h ≠ 0; omega) hpos using 1 <;>
        simp [F] <;> congr 3 <;> omega
    _ = ∑ h ∈ Finset.Ico 1 ((N : ℤ) + 1), (F h - F (h + 1)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc 1 (N : ℤ)]
    _ = F 1 - F (1 + (N : ℤ)) := by
      convert aux_sum_Ico_int_telescope F 1 N using 1 <;> ring
    _ = _ := by
      simp [F]

theorem aux_lMultiplierPartialSum_eq_boundary {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (N : ℕ) (hN : geometricDelta γ < N) :
    lMultiplierPartialSum γ i j N =
      lMultiplierAtScale γ ((2 : ℝ) ^ (-(N : ℤ)) *
        γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) i j -
      lMultiplierAtScale γ ((2 : ℝ) ^ (N : ℤ) *
        γ.scales i 1 (j + (geometricDelta γ : ℤ))) i j := by
  classical
  have hnv : Disjoint (aux_lMultiplierNegIndices N) (aux_lMultiplierVerticalIndices (geometricDelta γ)) := by
    rw [Finset.disjoint_left]
    rintro ⟨h, l⟩ hneg hvert
    simp [aux_lMultiplierNegIndices, aux_lMultiplierVerticalIndices] at hneg hvert
    omega
  have hnvpos : Disjoint (aux_lMultiplierNegIndices N ∪ aux_lMultiplierVerticalIndices (geometricDelta γ))
      (aux_lMultiplierPosIndices N) := by
    rw [Finset.disjoint_left]
    rintro ⟨h, l⟩ hleft hpos
    simp [aux_lMultiplierNegIndices, aux_lMultiplierVerticalIndices, aux_lMultiplierPosIndices] at hleft hpos
    rcases hleft with hneg | hvert <;> omega
  unfold lMultiplierPartialSum
  rw [aux_lMultiplier_truncation_decomp γ N hN]
  rw [Finset.sum_union hnvpos, Finset.sum_union hnv]
  rw [aux_lMultiplier_negative_block_eq, aux_lMultiplier_vertical_block_eq, aux_lMultiplier_positive_block_eq]
  abel

theorem lMultiplier_memDoubleSequence {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) : MemDoubleSequence γ.k (lMultiplier γ ι) := by
  intro i j
  unfold lMultiplier
  split_ifs with hzero hpositive
  · have hphi : MemW0 (fun p : ℝ =>
        standardBumpRescale (γ.scales i 1 (j + ι.1.2 - 1)) p -
          standardBumpRescale (γ.scales i 1 (j + ι.1.2)) p) :=
      Codex.Preliminaries.KKernels.aux_memW0_sub
        (aux_standardBumpRescale_memW0
          (aux_spacedSequence_pos (γ.scales_spaced i 1) _))
        (aux_standardBumpRescale_memW0
          (aux_spacedSequence_pos (γ.scales_spaced i 1) _))
    have hconv := Codex.Preliminaries.MKernels.aux_memW0_convolutionAlong
      (hMultiplier γ i j) (hMultiplier_memDoubleSequence γ i j) _ hphi (1, 1)
    convert hconv using 1
    funext v
    rcases v with ⟨v₁, v₂⟩
    simp [smul_eq_mul, sub_eq_add_neg]
  · have hphi : MemW0 (fun p : ℝ =>
        standardBumpRescale ((2 : ℝ) ^ (ι.1.1 - 1) *
          γ.scales i 1 (j + (geometricDelta γ : ℤ))) p -
          standardBumpRescale ((2 : ℝ) ^ ι.1.1 *
            γ.scales i 1 (j + (geometricDelta γ : ℤ))) p) :=
      Codex.Preliminaries.KKernels.aux_memW0_sub
        (aux_standardBumpRescale_memW0
          (mul_pos (zpow_pos (by norm_num) _)
            (aux_spacedSequence_pos (γ.scales_spaced i 1) _)))
        (aux_standardBumpRescale_memW0
          (mul_pos (zpow_pos (by norm_num) _)
            (aux_spacedSequence_pos (γ.scales_spaced i 1) _)))
    have hconv := Codex.Preliminaries.MKernels.aux_memW0_convolutionAlong
      (hMultiplier γ i j) (hMultiplier_memDoubleSequence γ i j) _ hphi (1, 1)
    convert hconv using 1
    funext v
    rcases v with ⟨v₁, v₂⟩
    simp [smul_eq_mul, sub_eq_add_neg]
  · have hphi : MemW0 (fun p : ℝ =>
        standardBumpRescale ((2 : ℝ) ^ ι.1.1 *
          γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) p -
          standardBumpRescale ((2 : ℝ) ^ (ι.1.1 + 1) *
            γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1)) p) :=
      Codex.Preliminaries.KKernels.aux_memW0_sub
        (aux_standardBumpRescale_memW0
          (mul_pos (zpow_pos (by norm_num) _)
            (aux_spacedSequence_pos (γ.scales_spaced i 1) _)))
        (aux_standardBumpRescale_memW0
          (mul_pos (zpow_pos (by norm_num) _)
            (aux_spacedSequence_pos (γ.scales_spaced i 1) _)))
    have hconv := Codex.Preliminaries.MKernels.aux_memW0_convolutionAlong
      (hMultiplier γ i j) (hMultiplier_memDoubleSequence γ i j) _ hphi (1, 1)
    convert hconv using 1
    funext v
    rcases v with ⟨v₁, v₂⟩
    simp [smul_eq_mul, sub_eq_add_neg]

/-- The finite truncations of the L multipliers converge to the H multiplier in `L¹`. -/
theorem sumLMultiplierConvergenceL1 {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) :
    MemDoubleSequence γ.k (lMultiplier γ ι) ∧
      ∀ i : Fin γ.k, ∀ j : ℤ,
        Tendsto (fun N : ℕ =>
          eLpNorm (lMultiplierPartialSum γ i j N - hMultiplier γ i j) 1 volume)
          atTop (nhds 0) := by
  refine ⟨lMultiplier_memDoubleSequence γ ι, ?_⟩
  intro i j
  have hendpoint := aux_lMultiplierPartialSum_boundary_tendsto_hMultiplier γ i j
  apply hendpoint.congr'
  filter_upwards [eventually_gt_atTop (geometricDelta γ)] with N hN
  rw [aux_lMultiplierPartialSum_eq_boundary γ i j N hN]

noncomputable def multiplierIndexPartialSum {n : ℕ} (γ : GeometricParameters n)
    (Xι : MultiplierIndex γ → DoubleSequence γ.k) (i : Fin γ.k) (j : ℤ) (N : ℕ) :
    RealPlane → ℝ := by
  classical
  exact ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
    if hξ : ξ ∈ multiplierIndexSet γ then Xι ⟨ξ, hξ⟩ i j else 0

noncomputable def sandwichMultiplierIndexPartialSum {n : ℕ} (γ : GeometricParameters n)
    (Xι : MultiplierIndex γ → DoubleSequence γ.k) (i : Fin γ.k) (j : ℤ) (N : ℕ) :
    Codex.Preliminaries.MKernels.MKernel γ.k := by
  classical
  exact ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
    if hξ : ξ ∈ multiplierIndexSet γ then sandwichKernel γ (Xι ⟨ξ, hξ⟩) i j else 0

theorem aux_multiplierIndexPartialSum_memW0 {n : ℕ} (γ : GeometricParameters n)
    (Xι : MultiplierIndex γ → DoubleSequence γ.k)
    (hXι : ∀ ι, MemDoubleSequence γ.k (Xι ι))
    (i : Fin γ.k) (j : ℤ) (N : ℕ) :
    MemW0 (multiplierIndexPartialSum γ Xι i j N) := by
  classical
  unfold multiplierIndexPartialSum
  have hsum : MemW0 (fun x : RealPlane => ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
      (if hξ : ξ ∈ multiplierIndexSet γ then Xι ⟨ξ, hξ⟩ i j else 0) x) := by
    apply Codex.Preliminaries.KKernels.aux_memW0_finset_sum
    intro ξ hξ
    have hmem : ξ ∈ multiplierIndexSet γ :=
      (Finset.mem_filter.mp hξ).2
    simpa [hmem] using hXι ⟨ξ, hmem⟩ i j
  convert hsum using 1
  funext x
  simp only [Finset.sum_apply]

noncomputable def multiplierIndexPartialDifference {n : ℕ} (γ : GeometricParameters n)
    (X : DoubleSequence γ.k) (Xι : MultiplierIndex γ → DoubleSequence γ.k) (N : ℕ) :
    DoubleSequence γ.k := fun i j => multiplierIndexPartialSum γ Xι i j N - X i j

theorem aux_sandwichMultiplierIndexPartialSum_sub_eq_sandwichKernel {n : ℕ}
    (γ : GeometricParameters n) (X : DoubleSequence γ.k)
    (Xι : MultiplierIndex γ → DoubleSequence γ.k)
    (i : Fin γ.k) (j : ℤ) (N : ℕ) :
    sandwichMultiplierIndexPartialSum γ Xι i j N - sandwichKernel γ X i j =
      sandwichKernel γ (multiplierIndexPartialDifference γ X Xι N) i j := by
  classical
  funext y
  unfold sandwichMultiplierIndexPartialSum multiplierIndexPartialDifference
    multiplierIndexPartialSum sandwichKernel
  simp only [Pi.sub_apply, Finset.sum_apply]
  have hkernel_apply (ξ : ℤ × ℤ) :
      (if hξ : ξ ∈ multiplierIndexSet γ then
        (fun z : Codex.Preliminaries.KKernels.RealVector γ.k ×
            Codex.Preliminaries.KKernels.RealVector γ.k =>
          (∏ m ∈ Finset.univ.filter (fun m => m < i), gammaGaussian γ m j (z.1 m, z.2 m)) *
            Xι ⟨ξ, hξ⟩ i j (z.1 i, z.2 i) *
          (∏ m ∈ Finset.univ.filter (fun m => i < m),
            gammaGaussian γ m (j - 1) (z.1 m, z.2 m))) else
          (0 : Codex.Preliminaries.MKernels.MKernel γ.k)) y =
        if hξ : ξ ∈ multiplierIndexSet γ then
          (∏ m ∈ Finset.univ.filter (fun m => m < i), gammaGaussian γ m j (y.1 m, y.2 m)) *
            Xι ⟨ξ, hξ⟩ i j (y.1 i, y.2 i) *
          (∏ m ∈ Finset.univ.filter (fun m => i < m),
            gammaGaussian γ m (j - 1) (y.1 m, y.2 m)) else 0 := by
    split_ifs <;> rfl
  have hmiddle_apply (ξ : ℤ × ℤ) :
      (if hξ : ξ ∈ multiplierIndexSet γ then Xι ⟨ξ, hξ⟩ i j else 0) (y.1 i, y.2 i) =
        if hξ : ξ ∈ multiplierIndexSet γ then Xι ⟨ξ, hξ⟩ i j (y.1 i, y.2 i) else 0 := by
    split_ifs <;> rfl
  simp_rw [hkernel_apply, hmiddle_apply]
  let A : ℝ := ∏ m ∈ Finset.univ.filter (fun m => m < i),
    gammaGaussian γ m j (y.1 m, y.2 m)
  let B : ℝ := ∏ m ∈ Finset.univ.filter (fun m => i < m),
    gammaGaussian γ m (j - 1) (y.1 m, y.2 m)
  change (∑ ξ ∈ aux_multiplierIndexTruncation γ N,
      if hξ : ξ ∈ multiplierIndexSet γ then
        A * Xι ⟨ξ, hξ⟩ i j (y.1 i, y.2 i) * B else 0) -
      A * X i j (y.1 i, y.2 i) * B =
    A * ((∑ ξ ∈ aux_multiplierIndexTruncation γ N,
      if hξ : ξ ∈ multiplierIndexSet γ then Xι ⟨ξ, hξ⟩ i j (y.1 i, y.2 i) else 0) -
      X i j (y.1 i, y.2 i)) * B
  have hterm (ξ : ℤ × ℤ) :
      (if hξ : ξ ∈ multiplierIndexSet γ then
        A * Xι ⟨ξ, hξ⟩ i j (y.1 i, y.2 i) * B else 0) =
      A * (if hξ : ξ ∈ multiplierIndexSet γ then
        Xι ⟨ξ, hξ⟩ i j (y.1 i, y.2 i) else 0) * B := by
    split_ifs <;> ring
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change A * _ * B - A * X i j (y.1 i, y.2 i) * B =
    A * (_ - X i j (y.1 i, y.2 i)) * B
  ring

theorem sandwichSumsL1 {n : ℕ} (γ : GeometricParameters n) (X : DoubleSequence γ.k)
    (Xι : MultiplierIndex γ → DoubleSequence γ.k)
    (hX : MemDoubleSequence γ.k X)
    (hXι : ∀ ι, MemDoubleSequence γ.k (Xι ι))
    (hconverges : ∀ i : Fin γ.k, ∀ j : ℤ,
      Tendsto (fun N : ℕ => eLpNorm (multiplierIndexPartialSum γ Xι i j N - X i j) 1 volume)
        atTop (nhds 0)) :
    ∀ i : Fin γ.k, ∀ j : ℤ,
      Tendsto (fun N : ℕ =>
        eLpNorm (sandwichMultiplierIndexPartialSum γ Xι i j N - sandwichKernel γ X i j) 1 volume)
          atTop (nhds 0) := by
  intro i j
  apply (hconverges i j).congr'
  filter_upwards [] with N
  rw [aux_sandwichMultiplierIndexPartialSum_sub_eq_sandwichKernel]
  exact (aux_eLpNorm_one_sandwichKernel γ
    (multiplierIndexPartialDifference γ X Xι N) i j
    (Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (Codex.Preliminaries.KKernels.aux_memW0_sub
        (aux_multiplierIndexPartialSum_memW0 γ Xι hXι i j N) (hX i j)))).symm

noncomputable def mKernelMultiplierIndexPartialSum {n : ℕ}
    (γ : GeometricParameters n)
    (Mι : MultiplierIndex γ → Codex.Preliminaries.MKernels.MKernel γ.k) (N : ℕ) :
    Codex.Preliminaries.MKernels.MKernel γ.k := by
  classical
  exact ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
    if hξ : ξ ∈ multiplierIndexSet γ then Mι ⟨ξ, hξ⟩ else 0

theorem aux_mKernelMultiplierIndexPartialSum_memW0 {n : ℕ}
    (γ : GeometricParameters n)
    (Mι : MultiplierIndex γ → Codex.Preliminaries.MKernels.MKernel γ.k)
    (hMι : ∀ ι, MemW0 (Mι ι)) (N : ℕ) :
    MemW0 (mKernelMultiplierIndexPartialSum γ Mι N) := by
  classical
  unfold mKernelMultiplierIndexPartialSum
  have hsum : MemW0 (fun x : Codex.Preliminaries.KKernels.RealVector γ.k ×
      Codex.Preliminaries.KKernels.RealVector γ.k =>
      ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
        (if hξ : ξ ∈ multiplierIndexSet γ then Mι ⟨ξ, hξ⟩ else 0) x) := by
    apply Codex.Preliminaries.KKernels.aux_memW0_finset_sum
    intro ξ hξ
    have hmem : ξ ∈ multiplierIndexSet γ := (Finset.mem_filter.mp hξ).2
    simpa [hmem] using hMι ⟨ξ, hmem⟩
  convert hsum using 1
  funext x
  simp only [Finset.sum_apply]

theorem aux_prismForm_finset_sum {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {α : Type*} (s : Finset α) (M : α → Codex.Preliminaries.MKernels.MKernel k)
    (hM : ∀ a ∈ s, MemW0 (M a))
    (F : Fin n → SchwartzMap (Codex.Preliminaries.KKernels.RealVector n) ℝ) :
    Codex.Preliminaries.MKernels.prismForm n k hk hkn (fun y => ∑ a ∈ s, M a y)
        (fun i => F i) =
      ∑ a ∈ s, Codex.Preliminaries.MKernels.prismForm n k hk hkn (M a) (fun i => F i) := by
  classical
  let e : Fin (Fintype.card {a // a ∈ s}) ≃ {a // a ∈ s} :=
    (Fintype.equivFin {a // a ∈ s}).symm
  let M' : Fin (Fintype.card {a // a ∈ s}) → Codex.Preliminaries.MKernels.MKernel k :=
    fun q => M (e q).1
  have hM' (q : Fin (Fintype.card {a // a ∈ s})) : MemW0 (M' q) := hM (e q).1 (e q).2
  have hsum (f : α → ℝ) : (∑ q, f (e q).1) = ∑ a ∈ s, f a := by
    calc
      (∑ q, f (e q).1) = ∑ a : {a // a ∈ s}, f a.1 :=
        Equiv.sum_comp e (fun a => f a.1)
      _ = ∑ a ∈ s, f a := by
        simpa using Finset.sum_attach s f
  have hsumM (y : Codex.Preliminaries.KKernels.RealVector k ×
      Codex.Preliminaries.KKernels.RealVector k) :
      (∑ q, M' q y) = ∑ a ∈ s, M a y := by
    simpa [M'] using hsum (fun a => M a y)
  have hsumP :
      (∑ q, Codex.Preliminaries.KKernels.prismBrascampLiebForm n k hk hkn
        (Codex.Preliminaries.MKernels.mToK k hk (M' q)) (fun i x => F i x)) =
        ∑ a ∈ s, Codex.Preliminaries.KKernels.prismBrascampLiebForm n k hk hkn
          (Codex.Preliminaries.MKernels.mToK k hk (M a)) (fun i x => F i x) := by
    simpa [M'] using hsum (fun a =>
      Codex.Preliminaries.KKernels.prismBrascampLiebForm n k hk hkn
        (Codex.Preliminaries.MKernels.mToK k hk (M a)) (fun i x => F i x))
  calc
    Codex.Preliminaries.MKernels.prismForm n k hk hkn (fun y => ∑ a ∈ s, M a y)
        (fun i => F i) =
        Codex.Preliminaries.KKernels.prismBrascampLiebForm n k hk hkn
          (Codex.Preliminaries.MKernels.mToK k hk (fun y => ∑ q, M' q y))
          (fun i x => F i x) := by
      congr 3
      funext y
      exact (hsumM y).symm
    _ = Codex.Preliminaries.KKernels.prismBrascampLiebForm n k hk hkn
        (fun z => ∑ q, Codex.Preliminaries.MKernels.mToK k hk (M' q) z)
        (fun i x => F i x) := by
      rw [Codex.Preliminaries.MKernels.aux_mToK_finset_sum k
        (Fintype.card {a // a ∈ s}) hk M' hM']
    _ = ∑ q, Codex.Preliminaries.KKernels.prismBrascampLiebForm n k hk hkn
        (Codex.Preliminaries.MKernels.mToK k hk (M' q)) (fun i x => F i x) := by
      apply Codex.Preliminaries.MKernels.aux_prismBrascampLiebForm_finset_sum
      intro q
      exact Codex.Preliminaries.MKernels.mToK_memW0 n k hk hkn (M' q) (hM' q)
    _ = ∑ a ∈ s, Codex.Preliminaries.KKernels.prismBrascampLiebForm n k hk hkn
        (Codex.Preliminaries.MKernels.mToK k hk (M a)) (fun i x => F i x) := hsumP
    _ = ∑ a ∈ s, Codex.Preliminaries.MKernels.prismForm n k hk hkn (M a)
        (fun i => F i) := by rfl

noncomputable def prismMultiplierIndexPartialAbsoluteSum {n : ℕ}
    (γ : GeometricParameters n)
    (Mι : MultiplierIndex γ → Codex.Preliminaries.MKernels.MKernel γ.k)
    (F : Fin n → SchwartzMap (Codex.Preliminaries.KKernels.RealVector n) ℝ) (N : ℕ) :
    ℝ≥0∞ := by
  classical
  exact ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
    if hξ : ξ ∈ multiplierIndexSet γ then
      ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n
        (Mι ⟨ξ, hξ⟩) (fun i => F i)‖ₑ
    else 0

noncomputable def prismMultiplierIndexPartialSum {n : ℕ}
    (γ : GeometricParameters n)
    (Mι : MultiplierIndex γ → Codex.Preliminaries.MKernels.MKernel γ.k)
    (F : Fin n → SchwartzMap (Codex.Preliminaries.KKernels.RealVector n) ℝ) (N : ℕ) :
    ℝ := by
  classical
  exact ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
    if hξ : ξ ∈ multiplierIndexSet γ then
      Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n
        (Mι ⟨ξ, hξ⟩) (fun i => F i)
    else 0

theorem aux_prismForm_mKernelMultiplierIndexPartialSum {n : ℕ} (γ : GeometricParameters n)
    (Mι : MultiplierIndex γ → Codex.Preliminaries.MKernels.MKernel γ.k)
    (hMι : ∀ ι, MemW0 (Mι ι))
    (F : Fin n → SchwartzMap (Codex.Preliminaries.KKernels.RealVector n) ℝ) (N : ℕ) :
    Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n
        (mKernelMultiplierIndexPartialSum γ Mι N) (fun i => F i) =
      prismMultiplierIndexPartialSum γ Mι F N := by
  classical
  unfold prismMultiplierIndexPartialSum
  unfold mKernelMultiplierIndexPartialSum
  have hfun :
      (∑ ξ ∈ aux_multiplierIndexTruncation γ N,
        if hξ : ξ ∈ multiplierIndexSet γ then Mι ⟨ξ, hξ⟩ else 0) =
      (fun y => ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
        (if hξ : ξ ∈ multiplierIndexSet γ then Mι ⟨ξ, hξ⟩ else 0) y) := by
    funext y
    simp only [Finset.sum_apply]
  rw [hfun]
  rw [aux_prismForm_finset_sum γ.one_le_k γ.k_le_n]
  · apply Finset.sum_congr rfl
    intro ξ hξ
    have hmem : ξ ∈ multiplierIndexSet γ := (Finset.mem_filter.mp hξ).2
    simp [hmem]
  · intro ξ hξ
    have hmem : ξ ∈ multiplierIndexSet γ := (Finset.mem_filter.mp hξ).2
    simpa [hmem] using hMι ⟨ξ, hmem⟩

theorem aux_mToK_sub {k : ℕ} (hk : 1 ≤ k)
    (M₁ M₂ : Codex.Preliminaries.MKernels.MKernel k)
    (hM₁ : MemW0 M₁) (hM₂ : MemW0 M₂) :
    Codex.Preliminaries.MKernels.mToK k hk (fun y => M₁ y - M₂ y) =
      fun z => Codex.Preliminaries.MKernels.mToK k hk M₁ z -
        Codex.Preliminaries.MKernels.mToK k hk M₂ z := by
  funext z
  unfold Codex.Preliminaries.MKernels.mToK
  rw [integral_sub]
  · exact Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (Codex.Preliminaries.MKernels.mToK_integrand_memW0 k k hk le_rfl M₁ hM₁ z)
  · exact Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (Codex.Preliminaries.MKernels.mToK_integrand_memW0 k k hk le_rfl M₂ hM₂ z)

theorem aux_prismForm_sub {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (M₁ M₂ : Codex.Preliminaries.MKernels.MKernel k)
    (hM₁ : MemW0 M₁) (hM₂ : MemW0 M₂)
    (F : Fin n → SchwartzMap (Codex.Preliminaries.KKernels.RealVector n) ℝ) :
    Codex.Preliminaries.MKernels.prismForm n k hk hkn M₁ (fun i => F i) -
      Codex.Preliminaries.MKernels.prismForm n k hk hkn M₂ (fun i => F i) =
      Codex.Preliminaries.MKernels.prismForm n k hk hkn (fun y => M₁ y - M₂ y)
        (fun i => F i) := by
  unfold Codex.Preliminaries.MKernels.prismForm
  rw [aux_mToK_sub hk M₁ M₂ hM₁ hM₂]
  exact Codex.Preliminaries.KKernels.aux_prismBrascampLiebForm_sub n k hk hkn
    (Codex.Preliminaries.MKernels.mToK k hk M₁)
    (Codex.Preliminaries.MKernels.mToK k hk M₂)
    (Codex.Preliminaries.MKernels.mToK_memW0 n k hk hkn M₁ hM₁)
    (Codex.Preliminaries.MKernels.mToK_memW0 n k hk hkn M₂ hM₂) F

theorem aux_enorm_prismForm_mKernelMultiplierIndexPartialSum_le {n : ℕ}
    (γ : GeometricParameters n)
    (Mι : MultiplierIndex γ → Codex.Preliminaries.MKernels.MKernel γ.k)
    (hMι : ∀ ι, MemW0 (Mι ι))
    (F : Fin n → SchwartzMap (Codex.Preliminaries.KKernels.RealVector n) ℝ) (N : ℕ) :
    ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n
        (mKernelMultiplierIndexPartialSum γ Mι N) (fun i => F i)‖ₑ ≤
      prismMultiplierIndexPartialAbsoluteSum γ Mι F N := by
  classical
  rw [aux_prismForm_mKernelMultiplierIndexPartialSum γ Mι hMι F N]
  unfold prismMultiplierIndexPartialAbsoluteSum
  calc
    ‖prismMultiplierIndexPartialSum γ Mι F N‖ₑ ≤
        ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
          ‖if hξ : ξ ∈ multiplierIndexSet γ then
            Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n
              (Mι ⟨ξ, hξ⟩) (fun i => F i)
          else 0‖ₑ := by
      exact enorm_sum_le _ _
    _ = ∑ ξ ∈ aux_multiplierIndexTruncation γ N,
          if hξ : ξ ∈ multiplierIndexSet γ then
            ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n
              (Mι ⟨ξ, hξ⟩) (fun i => F i)‖ₑ
          else 0 := by
      apply Finset.sum_congr rfl
      intro ξ _
      split_ifs <;> simp

theorem aux_le_iSup_of_tendsto_error {a S : ℝ≥0∞} {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (nhds 0)) (h : ∀ N, a ≤ S + e N) : a ≤ S := by
  have hright : Tendsto (fun N : ℕ => S + e N) atTop (nhds (S + 0)) :=
    tendsto_const_nhds.add he
  have hright' : Tendsto (fun N : ℕ => S + e N) atTop (nhds S) := by
    simpa using hright
  exact ge_of_tendsto' hright' h

/-- A symmetrically `L¹`-convergent multiplier series has its prism form bounded by the
extended supremum of its finite absolute prism sums. -/
theorem prismSumLeSumPrismL1 {n : ℕ} (γ : GeometricParameters n)
    (M : Codex.Preliminaries.MKernels.MKernel γ.k)
    (Mι : MultiplierIndex γ → Codex.Preliminaries.MKernels.MKernel γ.k)
    (hM : MemW0 M) (hMι : ∀ ι, MemW0 (Mι ι))
    (hconverges : Tendsto (fun N : ℕ =>
      eLpNorm (mKernelMultiplierIndexPartialSum γ Mι N - M) 1 volume)
      atTop (nhds 0))
    (F : Fin n → SchwartzMap (Codex.Preliminaries.KKernels.RealVector n) ℝ)
    (hF : F ∈ Codex.Preliminaries.KKernels.normalizedFunctionTuples n) :
    ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n M
        (fun i => F i)‖ₑ ≤
      ⨆ N : ℕ, prismMultiplierIndexPartialAbsoluteSum γ Mι F N := by
  classical
  apply aux_le_iSup_of_tendsto_error hconverges
  intro N
  let P := mKernelMultiplierIndexPartialSum γ Mι N
  have hP : MemW0 P := aux_mKernelMultiplierIndexPartialSum_memW0 γ Mι hMι N
  have hdiff : MemW0 (P - M) :=
    Codex.Preliminaries.KKernels.aux_memW0_sub hP hM
  have hform_sub :
      Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n P
          (fun i => F i) -
        Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n M
          (fun i => F i) =
        Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n (P - M)
          (fun i => F i) := by
    exact aux_prismForm_sub γ.one_le_k γ.k_le_n P M hP hM F
  have herror :
      ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n (P - M)
          (fun i => F i)‖ₑ ≤ eLpNorm (P - M) 1 volume := by
    change ‖Codex.Preliminaries.KKernels.prismBrascampLiebForm n γ.k γ.one_le_k γ.k_le_n
        (Codex.Preliminaries.MKernels.mToK γ.k γ.one_le_k (P - M))
          (fun i x => F i x)‖ₑ ≤ _
    exact
      (Codex.Preliminaries.KKernels.prismBLInequality n γ.k γ.one_le_k γ.k_le_n
        (Codex.Preliminaries.MKernels.mToK γ.k γ.one_le_k (P - M))
        (Codex.Preliminaries.MKernels.mToK_memW0 n γ.k γ.one_le_k γ.k_le_n
          (P - M) hdiff) F hF).trans
      (Codex.Preliminaries.MKernels.mToK_eLpNorm_one_le n γ.k γ.one_le_k γ.k_le_n
        (P - M) hdiff)
  have hpartial :
      ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n P
          (fun i => F i)‖ₑ ≤ prismMultiplierIndexPartialAbsoluteSum γ Mι F N := by
    dsimp [P]
    exact aux_enorm_prismForm_mKernelMultiplierIndexPartialSum_le γ Mι hMι F N
  calc
    ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n M
        (fun i => F i)‖ₑ =
        ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n P
            (fun i => F i) -
          Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n (P - M)
            (fun i => F i)‖ₑ := by
          rw [← hform_sub]
          congr 1
          ring
    _ ≤ ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n P
            (fun i => F i)‖ₑ +
          ‖Codex.Preliminaries.MKernels.prismForm n γ.k γ.one_le_k γ.k_le_n (P - M)
            (fun i => F i)‖ₑ := enorm_sub_le
    _ ≤ prismMultiplierIndexPartialAbsoluteSum γ Mι F N +
          eLpNorm (P - M) 1 volume := add_le_add hpartial herror
    _ ≤ (⨆ N : ℕ, prismMultiplierIndexPartialAbsoluteSum γ Mι F N) +
          eLpNorm (mKernelMultiplierIndexPartialSum γ Mι N - M) 1 volume := by
      dsimp [P]
      gcongr
      exact le_iSup (fun N : ℕ => prismMultiplierIndexPartialAbsoluteSum γ Mι F N) N


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

/-
\begin{definition}[N multiplier]\label{N multiplier}
For every $\iota\in\mathcal{I}_{\gamma}$ we define $N_{\gamma,\iota}= (N_{\gamma,\iota})_{i\in [k),j\in \Z}$ such that
\begin{equation}
 (N_{\gamma,\iota})_{i,j} = 
 \mathcal F^{-1}((\xi,\eta) \mapsto \widehat{\sigma_{\gamma,\iota,i,j}}(\xi+\eta)^{-\nu}\widehat{(L_{\gamma,\iota})_{i,j}}(\xi,\eta))\, .
\end{equation}
\end{definition}
-/
/-- The frequency-side integrand in the displayed definition of the N multiplier.
The convolution representative below is the implementation used for the real kernel. -/
noncomputable def nMultiplierFrequency {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) : RealPlane → ℂ := fun ξ =>
  (aux_fourierReal (sigmaMultiplier γ ι i j) (ξ.1 + ξ.2))⁻¹ ^
      (if γ.k < n - 1 then 1 else 2) *
    aux_fourierPlane (lMultiplier γ ι i j) ξ

/-- The unbridged raw-coordinate inverse-Fourier expression from the displayed definition
of the N multiplier. No equality with the convolution representative is asserted until the
product-coordinate Fourier/convolution bridge is formalized. -/
noncomputable def nMultiplierRawInverseFourier {n : ℕ} (γ : GeometricParameters n)
    (_hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) : DoubleSequence γ.k := fun i j v =>
  (aux_inverseFourierPlane (nMultiplierFrequency γ ι i j) v).re

/-- The exponent occurring in the four-scale Gaussian representative. -/
noncomputable def nMultiplierFourScaleExponent {n : ℕ} (γ : GeometricParameters n) : ℝ :=
  if γ.k < n - 1 then -(1 / 2 : ℝ) else -1

/-- The complex one-dimensional four-scale kernel used to represent an N multiplier. -/
noncomputable def nMultiplierRhoComplex {n : ℕ} (γ : GeometricParameters n)
    (_hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) : ℝ → ℂ :=
  if _hzero : ι.1.1 = 0 then
    fourScaleGaussianRho
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))
      (γ.scales i 1 (j + ι.1.2 - 1)) (γ.scales i 1 (j + ι.1.2))
      (γ.scales i 1 (j + ι.1.2 - 1)) (γ.scales i 1 (j + ι.1.2))
      (nMultiplierFourScaleExponent γ)
  else if _hpositive : 0 < ι.1.1 then
    fourScaleGaussianRho
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))
      ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ) - 1))
      ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ)))
      ((2 : ℝ) ^ (ι.1.1 - 1) * γ.scales i 1 (j + (geometricDelta γ : ℤ)))
      ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j + (geometricDelta γ : ℤ)))
      (nMultiplierFourScaleExponent γ)
  else
    fourScaleGaussianRho
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))
      ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1))
      ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j - (geometricDelta γ : ℤ)))
      ((2 : ℝ) ^ ι.1.1 * γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1))
      ((2 : ℝ) ^ (ι.1.1 + 1) * γ.scales i 1 (j - (geometricDelta γ : ℤ) - 1))
      (nMultiplierFourScaleExponent γ)

/-- The real kernel used in the convolution representative of an N multiplier. -/
noncomputable def nMultiplierRho {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) : ℝ → ℝ :=
  fun q => (nMultiplierRhoComplex γ hkn ι i j q).re

/-- Taking real parts preserves the Wiener space. -/
theorem aux_memW0_re {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] {f : E → ℂ} (hf : MemW0 f) :
    MemW0 (fun x => (f x).re) := by
  let hcont : Continuous (fun x => (f x).re) := Complex.continuous_re.comp hf.1
  refine ⟨hcont, ?_⟩
  refine hf.2.mono_nonneg (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hcont (by norm_num) x)
    (ae_of_all _ fun x => ?_)
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _)
  rintro _ ⟨z, hz, rfl⟩
  change ‖(f (x + z)).re‖ ≤ sSup ((fun w : E => ‖f (x + w)‖) '' closedBall 0 1)
  calc
    ‖(f (x + z)).re‖ ≤ ‖f (x + z)‖ := by
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    _ ≤ sSup ((fun w : E => ‖f (x + w)‖) '' closedBall 0 1) :=
      aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1 (by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

/-- The complex standard bump is in the Wiener space. -/
theorem aux_standardBumpComplex_memW0 : MemW0 (fun x : ℝ => (standardBump x : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp aux_standardBump_memW0.1, ?_⟩
  have hEnvelope : wienerEnvelope (fun x : ℝ => (standardBump x : ℂ)) 1 =
      wienerEnvelope standardBump 1 := by
    funext x
    simp [wienerEnvelope, Real.norm_eq_abs]
  rw [hEnvelope]
  exact aux_standardBump_memW0.2

/-- The four-scale Gaussian theorem applied to the standard bump. -/
theorem aux_fourScaleGaussianRho_memW0 {muMinus muPlus lambdaMinus lambdaPlus nu : ℝ}
    (hmuMinus : 0 < muMinus) (hmuPlus : 0 < muPlus)
    (hlambdaMinus : 0 < lambdaMinus) (hlambdaPlus : 0 < lambdaPlus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧ 2 * lambdaMinus ≤ lambdaPlus ∧
      lambdaPlus ≤ muPlus)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    MemW0 (fourScaleGaussianRho
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))
      muMinus muPlus lambdaMinus lambdaPlus nu) := by
  refine (fourScaleGaussianKernel ((2 : ℝ) ^ 18) 2 (by norm_num)
    (fun x : ℝ => (standardBump x : ℂ))
    (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))
    aux_standardBumpComplex_memW0 rfl (by positivity)
    ?_ ?_ ?_ ?_ muMinus muPlus lambdaMinus lambdaPlus nu
    hmuMinus hmuPlus hlambdaMinus hlambdaPlus hscales hnu).1
  · exact closure_minimal (standardBumpProperties_fourierShape).2.1 isClosed_Icc
  · exact (standardBumpProperties_fourierShape).2.2
  · apply aux_standardBumpComplex_fourier_contDiff.of_le
    exact WithTop.coe_le_coe.mpr le_top
  · intro m hm xi
    interval_cases m
    · exact (aux_standardBump_fourier_iteratedDeriv_le_zero xi).trans (by norm_num)
    · exact (aux_standardBump_fourier_iteratedDeriv_le_one xi).trans (by norm_num)
    · exact aux_standardBump_fourier_iteratedDeriv_le_two xi

/-- The central-band scale tuple satisfies the four-scale hypotheses. -/
theorem aux_fourScaleGaussianRho_spaced_memW0 (a : ℤ → ℝ) (ha : SpacedSequence a)
    (r : ℤ) (nu : ℝ) (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    MemW0 (fourScaleGaussianRho
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))
      (a (r - 1)) (a r) (a (r - 1)) (a r) nu) := by
  apply aux_fourScaleGaussianRho_memW0
  · exact (ha (r - 1)).1
  · exact (ha r).1
  · exact (ha (r - 1)).1
  · exact (ha r).1
  · refine ⟨le_rfl, ?_, le_rfl⟩
    convert (ha (r - 1)).2 using 1 <;> ring
  · exact hnu

/-- The positive-band scale tuple satisfies the four-scale hypotheses. -/
theorem aux_fourScaleGaussianRho_positive_memW0 (a : ℤ → ℝ) (ha : SpacedSequence a)
    (r h : ℤ) (nu : ℝ) (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    MemW0 (fourScaleGaussianRho
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))
      ((2 : ℝ) ^ h * a (r - 1)) ((2 : ℝ) ^ h * a r)
      ((2 : ℝ) ^ (h - 1) * a r) ((2 : ℝ) ^ h * a r) nu) := by
  have hpow : (2 : ℝ) ^ h = 2 * (2 : ℝ) ^ (h - 1) := by
    rw [show h = (h - 1) + 1 by omega, zpow_add₀ (by norm_num), zpow_one]
    ring
  refine aux_fourScaleGaussianRho_memW0
    (mul_pos (zpow_pos (by norm_num) _) (ha (r - 1)).1)
    (mul_pos (zpow_pos (by norm_num) _) (ha r).1)
    (mul_pos (zpow_pos (by norm_num) _) (ha r).1)
    (mul_pos (zpow_pos (by norm_num) _) (ha r).1)
    ?_ hnu
  refine ⟨?_, ?_, le_rfl⟩
  · calc
      2 * ((2 : ℝ) ^ h * a (r - 1)) =
          (2 * (2 : ℝ) ^ (h - 1)) * (2 * a (r - 1)) := by rw [hpow]; ring
      _ ≤ (2 * (2 : ℝ) ^ (h - 1)) * a r :=
        mul_le_mul_of_nonneg_left (by
          simpa only [sub_add_cancel] using (ha (r - 1)).2) (by positivity)
      _ = 2 * ((2 : ℝ) ^ (h - 1) * a r) := by ring
  · rw [hpow]
    apply le_of_eq
    ring

/-- The negative-band scale tuple satisfies the four-scale hypotheses. -/
theorem aux_fourScaleGaussianRho_negative_memW0 (a : ℤ → ℝ) (ha : SpacedSequence a)
    (r h : ℤ) (nu : ℝ) (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    MemW0 (fourScaleGaussianRho
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))
      ((2 : ℝ) ^ h * a r) ((2 : ℝ) ^ h * a (r + 1))
      ((2 : ℝ) ^ h * a r) ((2 : ℝ) ^ (h + 1) * a r) nu) := by
  have hpow : (2 : ℝ) ^ (h + 1) = (2 : ℝ) ^ h * 2 := by
    rw [zpow_add₀ (by norm_num), zpow_one]
  refine aux_fourScaleGaussianRho_memW0
    (mul_pos (zpow_pos (by norm_num) _) (ha r).1)
    (mul_pos (zpow_pos (by norm_num) _) (ha (r + 1)).1)
    (mul_pos (zpow_pos (by norm_num) _) (ha r).1)
    (mul_pos (zpow_pos (by norm_num) _) (ha r).1)
    ?_ hnu
  refine ⟨le_rfl, ?_, ?_⟩
  · rw [hpow]
    apply le_of_eq
    ring
  · calc
      (2 : ℝ) ^ (h + 1) * a r = (2 : ℝ) ^ h * (2 * a r) := by rw [hpow]; ring
      _ ≤ (2 : ℝ) ^ h * a (r + 1) :=
        mul_le_mul_of_nonneg_left (ha r).2 (by positivity)

/-- The exponent used for N multipliers lies in the range of the four-scale theorem. -/
theorem nMultiplierFourScaleExponent_memIco {n : ℕ} (γ : GeometricParameters n) :
    nMultiplierFourScaleExponent γ ∈ Set.Ico (-1 : ℝ) 0 := by
  unfold nMultiplierFourScaleExponent
  split <;> norm_num

/-- The complex four-scale representative is a Wiener function. -/
theorem nMultiplierRhoComplex_memW0 {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) :
    MemW0 (nMultiplierRhoComplex γ hkn ι i j) := by
  have hnu : nMultiplierFourScaleExponent γ ∈ Set.Ico (-1 : ℝ) 0 :=
    nMultiplierFourScaleExponent_memIco γ
  unfold nMultiplierRhoComplex
  split_ifs with hzero hpositive
  · exact aux_fourScaleGaussianRho_spaced_memW0 (γ.scales i 1) (γ.scales_spaced i 1)
      (j + ι.1.2) _ hnu
  · exact aux_fourScaleGaussianRho_positive_memW0 (γ.scales i 1) (γ.scales_spaced i 1)
      (j + (geometricDelta γ : ℤ)) ι.1.1 _ hnu
  · simpa only [sub_add_cancel] using
      (aux_fourScaleGaussianRho_negative_memW0 (γ.scales i 1) (γ.scales_spaced i 1)
        (j - (geometricDelta γ : ℤ) - 1) ι.1.1 _ hnu)

/-- The real four-scale representative is a Wiener function. -/
theorem nMultiplierRho_memW0 {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) :
    MemW0 (nMultiplierRho γ hkn ι i j) := by
  exact aux_memW0_re (nMultiplierRhoComplex_memW0 γ hkn ι i j)

/-- The convolution representative of the N multiplier. -/
noncomputable def nMultiplier {n : ℕ} (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1)
    (ι : MultiplierIndex γ) : DoubleSequence γ.k := fun i j v =>
  ∫ q : ℝ, hMultiplier γ i j (v.1 - q, v.2 - q) * nMultiplierRho γ hkn ι i j q

/-- Every N multiplier is a double sequence of Wiener-space functions. -/
theorem nKernelWellDefinedness {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) :
    MemDoubleSequence γ.k (nMultiplier γ hkn ι) := by
  intro i j
  have hconv := Codex.Preliminaries.MKernels.aux_memW0_convolutionAlong
    (hMultiplier γ i j) (hMultiplier_memDoubleSequence γ i j)
    (nMultiplierRho γ hkn ι i j) (nMultiplierRho_memW0 γ hkn ι i j) (1, 1)
  unfold nMultiplier
  convert hconv using 1
  funext v
  rcases v with ⟨v₁, v₂⟩
  simp [smul_eq_mul, sub_eq_add_neg]

/-- Diagonal cancellation rewrites the convolution representative of an N multiplier using a
difference of its one-dimensional kernel. -/
theorem aux_hMultiplier_diagonal_convolution_cancellation
    {n : ℕ} {rho : ℝ → ℝ} (hrho : MemW0 rho) (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) (x y c : ℝ) :
    (∫ p : ℝ, hMultiplier γ i j (x + y - p, y - p) * rho p) =
      ∫ q : ℝ, hMultiplier γ i j (x + q, q) * (rho (y - q) - rho c) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (RealPlane × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let F : RealPlane → ℝ := fun z => hMultiplier γ i j (aux_diagonalShear z)
  have hF : MemW0 F := by
    exact Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv
      (hMultiplier_memDoubleSequence γ i j) aux_diagonalShear
  let P : RealPlane × ℝ → ℝ := fun z => F z.1 * rho z.2
  have hP : MemW0 P := by
    simpa [P] using hF.aux_mul_prod hrho
  have hshift : MemW0 (P ∘ aux_lMultiplierAtScale_largeScaleShear) :=
    Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hP
      aux_lMultiplierAtScale_largeScaleShear
  have hplain : MemW0 (P ∘ aux_lMultiplierAtScale_largeScaleReorder) :=
    Codex.Preliminaries.KKernels.aux_memW0_comp_continuousLinearEquiv hP
      aux_lMultiplierAtScale_largeScaleReorder
  let K : RealPlane × ℝ → ℝ := fun z =>
    F (z.1.1, z.2) * (rho (z.1.2 - z.2) - rho z.1.2)
  have hKmem : MemW0 K := by
    have hsub := Codex.Preliminaries.KKernels.aux_memW0_sub hshift hplain
    convert hsub using 1
    funext z
    rcases z with ⟨⟨u, v⟩, q⟩
    dsimp [P, Function.comp_def, aux_lMultiplierAtScale_largeScaleShear,
      aux_lMultiplierAtScale_largeScaleReorder, K]
    ring
  have hFslice_mem : MemW0 (fun q : ℝ => F (x, q)) :=
    hF.aux_memW0_slice_of_addHaar x
  have hFslice : Integrable (fun q : ℝ => F (x, q)) :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar hFslice_mem
  have hB : Integrable (fun q : ℝ => F (x, q) * rho y) := hFslice.mul_const _
  have hKslice : Integrable (fun q : ℝ => K ((x, y), q)) :=
    Codex.Preliminaries.KKernels.aux_memW0_integrable_of_addHaar
      (hKmem.aux_memW0_slice_of_addHaar (x, y))
  have hA : Integrable (fun q : ℝ => F (x, q) * rho (y - q)) := by
    have hsum := hKslice.add hB
    refine hsum.congr ?_
    filter_upwards [] with q
    dsimp [K]
    ring
  have hzero : (∫ q : ℝ, F (x, q)) = 0 := by
    simpa [F, aux_diagonalShear] using hMultiplier_vanishing_integral γ i j x
  have hBc : Integrable (fun q : ℝ => F (x, q) * rho c) := hFslice.mul_const _
  have hBzero : (∫ q : ℝ, F (x, q) * rho c) = 0 := by
    rw [integral_mul_const, hzero, zero_mul]
  have hcoordinate :
      (∫ p : ℝ, hMultiplier γ i j (x + y - p, y - p) * rho p) =
        ∫ q : ℝ, F (x, q) * rho (y - q) := by
    let A : ℝ → ℝ := fun p => hMultiplier γ i j (x + y - p, y - p) * rho p
    calc
      (∫ p : ℝ, hMultiplier γ i j (x + y - p, y - p) * rho p) = ∫ p : ℝ, A p := by rfl
      _ = ∫ q : ℝ, A (y - q) := (integral_sub_left_eq_self A volume y).symm
      _ = ∫ q : ℝ, F (x, q) * rho (y - q) := by
        apply integral_congr_ae
        filter_upwards [] with q
        dsimp [A, F, aux_diagonalShear]
        ring
  calc
    (∫ p : ℝ, hMultiplier γ i j (x + y - p, y - p) * rho p) =
        ∫ q : ℝ, F (x, q) * rho (y - q) := hcoordinate
    _ = (∫ q : ℝ, F (x, q) * rho (y - q)) - ∫ q : ℝ, F (x, q) * rho c := by
      rw [hBzero, sub_zero]
    _ = ∫ q : ℝ, F (x, q) * rho (y - q) - F (x, q) * rho c :=
      (integral_sub hA hBc).symm
    _ = ∫ q : ℝ, hMultiplier γ i j (x + q, q) * (rho (y - q) - rho c) := by
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp [F, aux_diagonalShear]
      ring

/-- The preceding cancellation identity specialized to the convolution representative of an N
multiplier. -/
theorem aux_nMultiplier_diagonal_cancellation {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ)
    (x y : ℝ) :
    nMultiplier γ hkn ι i j (aux_diagonalShear (x, y)) =
      ∫ q : ℝ, hMultiplier γ i j (x + q, q) *
        (nMultiplierRho γ hkn ι i j (y - q) - nMultiplierRho γ hkn ι i j y) := by
  simpa [nMultiplier, aux_diagonalShear] using
    aux_hMultiplier_diagonal_convolution_cancellation
      (nMultiplierRho_memW0 γ hkn ι i j) γ i j x y y

/-- The positive-band cancellation identity in the rotated coordinates used by the first
Gaussian-domination case. -/
theorem aux_nMultiplier_caseOne_cancellation {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ)
    (w₀ w₁ : ℝ) :
    nMultiplier γ hkn ι i j (w₀ - w₁, w₀ + w₁) =
      ∫ p : ℝ, (nMultiplierRho γ hkn ι i j (w₀ + p) -
        nMultiplierRho γ hkn ι i j w₀) * hMultiplier γ i j (-w₁ - p, w₁ - p) := by
  rw [show (w₀ - w₁, w₀ + w₁) = aux_diagonalShear (-2 * w₁, w₀ + w₁) by
    ext <;> dsimp [aux_diagonalShear] <;> ring]
  calc
    nMultiplier γ hkn ι i j (aux_diagonalShear (-2 * w₁, w₀ + w₁)) =
      ∫ q : ℝ, hMultiplier γ i j (-2 * w₁ + q, q) *
          (nMultiplierRho γ hkn ι i j (w₀ + w₁ - q) -
            nMultiplierRho γ hkn ι i j w₀) :=
      by
        simpa [nMultiplier, aux_diagonalShear] using
          aux_hMultiplier_diagonal_convolution_cancellation
            (nMultiplierRho_memW0 γ hkn ι i j) γ i j (-2 * w₁) (w₀ + w₁) w₀
    _ = ∫ p : ℝ, (nMultiplierRho γ hkn ι i j (w₀ + p) -
        nMultiplierRho γ hkn ι i j w₀) * hMultiplier γ i j (-w₁ - p, w₁ - p) := by
      let A : ℝ → ℝ := fun q => hMultiplier γ i j (-2 * w₁ + q, q) *
        (nMultiplierRho γ hkn ι i j (w₀ + w₁ - q) - nMultiplierRho γ hkn ι i j w₀)
      calc
        (∫ q : ℝ, hMultiplier γ i j (-2 * w₁ + q, q) *
            (nMultiplierRho γ hkn ι i j (w₀ + w₁ - q) - nMultiplierRho γ hkn ι i j w₀)) =
              ∫ q : ℝ, A q := by rfl
        _ = ∫ p : ℝ, A (w₁ - p) := (integral_sub_left_eq_self A volume w₁).symm
        _ = ∫ p : ℝ, (nMultiplierRho γ hkn ι i j (w₀ + p) -
            nMultiplierRho γ hkn ι i j w₀) * hMultiplier γ i j (-w₁ - p, w₁ - p) := by
          apply integral_congr_ae
          filter_upwards [] with p
          dsimp [A]
          ring

end

end Codex.MainArgument.MultipliersHLN
