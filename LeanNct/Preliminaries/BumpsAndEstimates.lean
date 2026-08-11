import LeanNct.Preliminaries.Gaussians
import LeanNct.Preliminaries.Notation
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Bumps and their estimates

The concrete bump functions and explicit constants used in the manuscript's bump estimates.
-/

namespace Codex.Preliminaries.BumpsAndEstimates

open MeasureTheory Filter
open scoped BigOperators FourierTransform Real RealInnerProductSpace Convolution Pointwise EuclideanSpace
open Codex.Preliminaries.Notation
open Codex.Preliminaries.Gaussians

noncomputable section

/-- For \ref{lem:smoothdecay}, compact support is preserved under the iterated derivatives
appearing in the integration-by-parts estimate. -/
theorem aux_hasCompactSupport_iteratedDeriv (zeta : ℝ → ℂ)
    (hzeta : HasCompactSupport zeta) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n zeta) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hzeta
  | succ n hn =>
      rw [iteratedDeriv_succ]
      exact hn.deriv

/-- For \ref{lem:smoothdecay}, a continuous iterated derivative with compact support is
integrable.  This supplies the hypotheses for Fourier integration by parts. -/
theorem aux_integrable_iteratedDeriv_of_contDiff_compactSupport
    (N n : ℕ) (zeta : ℝ → ℂ) (hzeta : ContDiff ℝ N zeta)
    (hzetaSupport : HasCompactSupport zeta) (hn : n ≤ N) :
    Integrable (iteratedDeriv n zeta) := by
  exact (hzeta.continuous_iteratedDeriv n (by exact_mod_cast hn)).integrable_of_hasCompactSupport
    (aux_hasCompactSupport_iteratedDeriv zeta hzetaSupport n)

/-- For \ref{lem:smoothdecay}, this is the elementary $L^1$ bound for an inverse Fourier
transform. -/
theorem aux_norm_inverseFourier_le_integral_norm (zeta : ℝ → ℂ) (x : ℝ) :
    ‖FourierTransformInv.fourierInv zeta x‖ ≤ ∫ xi : ℝ, ‖zeta xi‖ := by
  rw [Real.fourierInv_eq]
  calc
    ‖∫ xi : ℝ, 𝐞 ⟪xi, x⟫ • zeta xi‖ ≤ ∫ xi : ℝ, ‖𝐞 ⟪xi, x⟫ • zeta xi‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ xi : ℝ, ‖zeta xi‖ := by
      apply integral_congr_ae
      filter_upwards [] with xi
      rw [Circle.norm_smul]

/-- For \ref{mean value bump estimate 2} and `meanValueBumpEstimate`, this rewrites a
translated inverse Fourier transform as the inverse transform of its frequency-side difference. -/
theorem aux_fourierInv_translate_sub (f : ℝ → ℂ) (hf : Integrable f) (x y : ℝ) :
    FourierTransformInv.fourierInv f (x + y) - FourierTransformInv.fourierInv f x =
      FourierTransformInv.fourierInv
        (fun xi => f xi * ((𝐞 (xi * y) : ℂ) - 1)) x := by
  let phaseCoeff : ℝ → ℂ := fun t => 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
  let phase : ℝ → ℝ → ℂ := fun t xi => Complex.exp (phaseCoeff t * (xi : ℂ))
  let phaseDiff : ℝ → ℝ → ℂ := fun t xi => phase t xi - 1
  have hphaseCont (t : ℝ) : ContDiff ℝ ⊤ (phase t) := by
    unfold phase
    apply Complex.contDiff_exp.comp
    simpa only [Complex.ofRealCLM_apply, smul_eq_mul] using
      (Complex.ofRealCLM.contDiff.const_smul (phaseCoeff t))
  have hphaseNorm (t xi : ℝ) : ‖phase t xi‖ = 1 := by
    unfold phase phaseCoeff
    have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) * (xi : ℂ) =
        ((2 * Real.pi * xi * t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  have hphaseMul (u v xi : ℝ) : phase (u + v) xi = phase u xi * phase v xi := by
    unfold phase phaseCoeff
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphaseChar (t xi : ℝ) : phase t xi = (𝐞 (xi * t) : ℂ) := by
    unfold phase phaseCoeff
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  have hphaseInt (t : ℝ) : Integrable (fun xi => phase t xi * f xi) := by
    rw [← integrable_norm_iff]
    · simpa only [norm_mul, hphaseNorm, one_mul] using hf.norm
    · exact (hphaseCont t).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
  rw [Real.fourierInv_eq', Real.fourierInv_eq', Real.fourierInv_eq']
  simp only [smul_eq_mul]
  have hphase (t xi : ℝ) :
      Complex.exp ((↑(2 * Real.pi * ⟪xi, t⟫) : ℂ) * Complex.I) = phase t xi := by
    rw [Real.inner_apply]
    unfold phase phaseCoeff
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  have hphaseDiff (xi : ℝ) : (𝐞 (xi * y) : ℂ) - 1 = phaseDiff y xi := by
    unfold phaseDiff
    rw [hphaseChar]
  simp_rw [hphaseDiff]
  change
    (∫ xi : ℝ, phase (x + y) xi * f xi) - ∫ xi : ℝ, phase x xi * f xi =
      ∫ xi : ℝ, phase x xi * (f xi * phaseDiff y xi)
  rw [← integral_sub (hphaseInt (x + y)) (hphaseInt x)]
  apply integral_congr_ae
  filter_upwards [] with xi
  rw [hphaseMul]
  unfold phaseDiff
  ring

/-- For \ref{lem:smoothdecay}, this rewrites the inverse Fourier transform of an iterated
derivative after repeated integration by parts. -/
theorem aux_inverseFourier_iteratedDeriv (N : ℕ) (zeta : ℝ → ℂ)
    (hzeta : ContDiff ℝ N zeta)
    (hzetaInt : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n zeta)) (x : ℝ) :
    FourierTransformInv.fourierInv (iteratedDeriv N zeta) x =
      (-(2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))) ^ N *
        FourierTransformInv.fourierInv zeta x := by
  have hfourier := Real.fourier_iteratedDeriv (N := (N : ℕ∞)) (n := N) hzeta
    (fun n hn => hzetaInt n (by exact_mod_cast hn)) (by simp)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg, hfourier]
  simp only [smul_eq_mul]
  have hfactor : 2 * (Real.pi : ℂ) * Complex.I * ((-x : ℝ) : ℂ) =
      -(2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by
    push_cast
    ring
  rw [hfactor]

/-- For \ref{lem:smoothdecay}, a uniform bound together with quadratic decay gives the
integrable quadratic majorant used to prove the Wiener-space conclusion. -/
theorem aux_norm_le_two_mul_add_mul_inv_one_add_sq {f : ℝ → ℂ} (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (huniform : ∀ x : ℝ, ‖f x‖ ≤ a)
    (hdecay : ∀ x : ℝ, x ≠ 0 → ‖f x‖ ≤ b * |x|⁻¹ ^ 2) (x : ℝ) :
    ‖f x‖ ≤ 2 * (a + b) * (1 + x ^ 2)⁻¹ := by
  have hden : 0 < 1 + x ^ 2 := by positivity
  by_cases hx : |x| ≤ 1
  · have hxsq : x ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using
        (sq_le_sq₀ (abs_nonneg x) zero_le_one).mpr hx
    calc
      ‖f x‖ ≤ a := huniform x
      _ ≤ 2 * (a + b) * (1 + x ^ 2)⁻¹ := by
        rw [show 2 * (a + b) * (1 + x ^ 2)⁻¹ =
          (2 * (a + b)) / (1 + x ^ 2) by field_simp]
        apply (le_div_iff₀ hden).2
        have hmul : a * (1 + x ^ 2) ≤ a * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) ha
        nlinarith
  · have hxone : 1 < |x| := lt_of_not_ge hx
    have hxne : x ≠ 0 := by
      intro hzero
      subst x
      norm_num at hxone
    have habspos : 0 < |x| := abs_pos.mpr hxne
    have habssq : 1 ≤ |x| ^ 2 := by
      simpa only [one_pow] using
        (sq_le_sq₀ zero_le_one (by positivity)).mpr (le_of_lt hxone)
    have hinv : |x|⁻¹ ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [show |x|⁻¹ ^ 2 = 1 / |x| ^ 2 by field_simp,
        show 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by field_simp]
      apply (div_le_div_iff₀ (sq_pos_of_pos habspos) hden).2
      rw [sq_abs] at habssq ⊢
      nlinarith
    calc
      ‖f x‖ ≤ b * |x|⁻¹ ^ 2 := hdecay x hxne
      _ ≤ b * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hinv hb
      _ ≤ 2 * (a + b) * (1 + x ^ 2)⁻¹ := by
        have hinv_nonneg : 0 ≤ (1 + x ^ 2)⁻¹ := inv_nonneg.mpr hden.le
        calc
          b * (2 * (1 + x ^ 2)⁻¹) = (2 * b) * (1 + x ^ 2)⁻¹ := by ring
          _ ≤ (2 * (a + b)) * (1 + x ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (by linarith) hinv_nonneg

/-- For \ref{lem:smoothdecay}, a continuous function with the displayed quadratic majorant has
an integrable unit local supremum and hence lies in $W_0$. -/
theorem aux_memW0_of_quadratic_decay {f : ℝ → ℂ} (c : ℝ) (hc : 0 ≤ c)
    (hcont : Continuous f)
    (hdecay : ∀ x : ℝ, ‖f x‖ ≤ c * (1 + x ^ 2)⁻¹) : MemW0 f := by
  have hlocal (x : ℝ) :
      wienerEnvelope f 1 x ≤ 4 * c * (1 + x ^ 2)⁻¹ := by
    have hdenx : 0 < 1 + x ^ 2 := by positivity
    unfold wienerEnvelope
    apply csSup_le
    · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
    rintro _ ⟨z, hz, rfl⟩
    have hzabs : |z| ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hz
    have hshift_sq : 1 + x ^ 2 ≤ 4 * (1 + (x + z) ^ 2) := by
      have hzsq : z ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using
          (sq_le_sq₀ (abs_nonneg z) zero_le_one).mpr hzabs
      have hxsq : x ^ 2 ≤ 2 * (x + z) ^ 2 + 2 * z ^ 2 := by
        nlinarith [sq_nonneg (x + 2 * z)]
      nlinarith
    have hdeny : 0 < 1 + (x + z) ^ 2 := by positivity
    have hinv : (1 + (x + z) ^ 2)⁻¹ ≤ 4 * (1 + x ^ 2)⁻¹ := by
      rw [show (1 + (x + z) ^ 2)⁻¹ = 1 / (1 + (x + z) ^ 2) by field_simp,
        show 4 * (1 + x ^ 2)⁻¹ = 4 / (1 + x ^ 2) by field_simp]
      exact (div_le_div_iff₀ hdeny hdenx).2 (by simpa using hshift_sq)
    calc
      ‖f (x + z)‖ ≤ c * (1 + (x + z) ^ 2)⁻¹ := hdecay _
      _ ≤ c * (4 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hinv hc
      _ = 4 * c * (1 + x ^ 2)⁻¹ := by ring
  refine ⟨hcont, ?_⟩
  have hmajorant : Integrable (fun x : ℝ => 4 * c * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (4 * c)
  refine hmajorant.mono_nonneg
    (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hcont zero_le_one x)
    (ae_of_all _ fun x => hlocal x)

/-- For \ref{lem:smoothdecay}, this turns the repeated integration-by-parts identity into the
quantitative inverse-Fourier decay estimate at any positive derivative order. -/
theorem aux_inverseFourier_iteratedDeriv_decay (n : ℕ) (zeta : ℝ → ℂ)
    (hzeta : ContDiff ℝ n zeta)
    (hzetaInt : ∀ k : ℕ, k ≤ n → Integrable (iteratedDeriv k zeta))
    (x : ℝ) (hx : x ≠ 0) :
    ‖FourierTransformInv.fourierInv zeta x‖ ≤
      (2 * Real.pi)⁻¹ ^ n * |x|⁻¹ ^ n * ∫ xi : ℝ, ‖iteratedDeriv n zeta xi‖ := by
  have hid := aux_inverseFourier_iteratedDeriv n zeta hzeta hzetaInt x
  have hfactorNorm :
      ‖FourierTransformInv.fourierInv (iteratedDeriv n zeta) x‖ =
        (2 * Real.pi * |x|) ^ n * ‖FourierTransformInv.fourierInv zeta x‖ := by
    rw [hid, norm_mul, norm_pow, aux_norm_fourier_derivative_factor]
  have hbound := aux_norm_inverseFourier_le_integral_norm (iteratedDeriv n zeta) x
  have habspos : 0 < |x| := abs_pos.mpr hx
  have hfactorpos : 0 < (2 * Real.pi * |x|) ^ n :=
    pow_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) habspos) _
  apply le_of_mul_le_mul_left ?_ hfactorpos
  calc
    (2 * Real.pi * |x|) ^ n * ‖FourierTransformInv.fourierInv zeta x‖ =
        ‖FourierTransformInv.fourierInv (iteratedDeriv n zeta) x‖ := hfactorNorm.symm
    _ ≤ ∫ xi : ℝ, ‖iteratedDeriv n zeta xi‖ := hbound
    _ = (2 * Real.pi * |x|) ^ n *
        ((2 * Real.pi)⁻¹ ^ n * |x|⁻¹ ^ n * ∫ xi : ℝ, ‖iteratedDeriv n zeta xi‖) := by
      have hpi : 2 * Real.pi ≠ 0 := ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
      have habs : |x| ≠ 0 := ne_of_gt habspos
      have hscale : (2 * Real.pi * |x|) ^ n *
          ((2 * Real.pi)⁻¹ ^ n * |x|⁻¹ ^ n) = 1 := by
        rw [show 2 * Real.pi * |x| = (2 * Real.pi) * |x| by ring, mul_pow,
          inv_pow, inv_pow]
        field_simp
      calc
        ∫ xi : ℝ, ‖iteratedDeriv n zeta xi‖ =
            1 * ∫ xi : ℝ, ‖iteratedDeriv n zeta xi‖ := by ring
        _ = ((2 * Real.pi * |x|) ^ n *
            ((2 * Real.pi)⁻¹ ^ n * |x|⁻¹ ^ n)) *
            ∫ xi : ℝ, ‖iteratedDeriv n zeta xi‖ := by rw [hscale]
        _ = (2 * Real.pi * |x|) ^ n *
            ((2 * Real.pi)⁻¹ ^ n * |x|⁻¹ ^ n *
              ∫ xi : ℝ, ‖iteratedDeriv n zeta xi‖) := by ring

/--
\begin{lemma}
\label{lem:smoothdecay}
Let $N\geq 2$ be an integer. Let $\zeta:\R\to\C$ be an $N$ times continuously differentiable function with compact support. Then the function $\phi=\mathcal F^{-1}\zeta$ belongs to $W_0(\R)$ and we have for all $x\in\R$, $x\neq0$, the estimate

\begin{equation}\label{auto:Fourier-decay-minimum-bound}|\phi(x)|\le \min(\|\widehat{\phi}\|_1, \|\widehat{\phi}^{(N)}\|_1 (2\pi)^{-N} |x|^{-N}).\end{equation}
\end{lemma}
-/
theorem smoothDecay (N : ℕ) (hN : 2 ≤ N) (zeta : ℝ → ℂ)
    (hzeta : ContDiff ℝ N zeta) (hzetaSupport : HasCompactSupport zeta) :
    MemW0 (FourierTransformInv.fourierInv zeta) ∧
      ∀ x : ℝ, x ≠ 0 →
        ‖FourierTransformInv.fourierInv zeta x‖ ≤
          min (∫ xi : ℝ, ‖zeta xi‖)
            ((2 * Real.pi)⁻¹ ^ N * |x|⁻¹ ^ N *
              ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) := by
  have hzetaInt : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n zeta) :=
    fun n hn => aux_integrable_iteratedDeriv_of_contDiff_compactSupport N n zeta hzeta
      hzetaSupport hn
  have hcont : Continuous (FourierTransformInv.fourierInv zeta) := by
    change Continuous (VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) zeta)
    apply VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    · fun_prop
    · exact hzetaInt 0 zero_le
  have hzetaTwo : ContDiff ℝ 2 zeta :=
    hzeta.of_le (by exact_mod_cast hN)
  have hzetaIntTwo : ∀ n : ℕ, n ≤ 2 → Integrable (iteratedDeriv n zeta) :=
    fun n hn => hzetaInt n (hn.trans hN)
  let a : ℝ := ∫ xi : ℝ, ‖zeta xi‖
  let b : ℝ := (2 * Real.pi)⁻¹ ^ 2 * ∫ xi : ℝ, ‖iteratedDeriv 2 zeta xi‖
  have ha : 0 ≤ a := by
    dsimp [a]
    exact integral_nonneg fun _ => norm_nonneg _
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hquad (x : ℝ) :
      ‖FourierTransformInv.fourierInv zeta x‖ ≤
        2 * (a + b) * (1 + x ^ 2)⁻¹ := by
    apply aux_norm_le_two_mul_add_mul_inv_one_add_sq a b ha hb
    · intro y
      simpa only [a] using aux_norm_inverseFourier_le_integral_norm zeta y
    · intro y hy
      calc
        ‖FourierTransformInv.fourierInv zeta y‖ ≤
            (2 * Real.pi)⁻¹ ^ 2 * |y|⁻¹ ^ 2 *
              ∫ xi : ℝ, ‖iteratedDeriv 2 zeta xi‖ :=
          aux_inverseFourier_iteratedDeriv_decay 2 zeta hzetaTwo hzetaIntTwo y hy
        _ = b * |y|⁻¹ ^ 2 := by
          dsimp only [b]
          ring
  have hmem : MemW0 (FourierTransformInv.fourierInv zeta) :=
    aux_memW0_of_quadratic_decay (2 * (a + b)) (by positivity) hcont hquad
  refine ⟨hmem, ?_⟩
  intro x hx
  refine le_min (aux_norm_inverseFourier_le_integral_norm zeta x) ?_
  exact aux_inverseFourier_iteratedDeriv_decay N zeta hzeta hzetaInt x hx


/--
The Fourier transform of the characteristic function of $[-r,r]$, written explicitly so that
the finite products in the definition of the standard bump are real-valued functions.
-/
def aux_intervalIndicatorFourier (r x : ℝ) : ℝ :=
  if x = 0 then 2 * r else Real.sin (2 * Real.pi * r * x) / (Real.pi * x)

/--
\begin{definition}[standard bump]\label{standard bump}
Define, for \(l\in \N_{>0}\),
\begin{equation}
 \Phi_l
 =
 \widehat{1_{[-3/4,3/4]}}
 \prod_{i\in [l)}
 2^{i+2}
 \widehat{1_{[-2^{-i-3},2^{-i-3}]}} .
\end{equation}
\end{definition}
-/
def standardBumpFinite (l : ℕ) : ℝ → ℝ := fun x =>
  aux_intervalIndicatorFourier (3 / 4) x *
    ∏ i ∈ Finset.range l,
      (2 : ℝ) ^ (i + 2) *
        aux_intervalIndicatorFourier ((2 : ℝ) ^ (-(i : ℤ) - 3)) x

/--
\begin{definition}[standard bump]\label{standard bump}
For $x\in\R$, define
\[\Phi(x)=\lim_{l\to\infty}\Phi_l(x).\]
\end{definition}
-/
def standardBump : ℝ → ℝ := fun x =>
  Filter.limUnder (Filter.atTop : Filter ℕ) (fun l => standardBumpFinite l x)

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
rewrites the Fourier transform of an interval indicator in the sinc form used to control the
finite products. -/
theorem aux_intervalIndicatorFourier_eq_two_mul_sinc (r x : ℝ) :
    aux_intervalIndicatorFourier r x =
      2 * r * Real.sinc (2 * Real.pi * r * x) := by
  by_cases hx : x = 0
  · simp [aux_intervalIndicatorFourier, hx]
  by_cases hr : r = 0
  · simp [aux_intervalIndicatorFourier, hx, hr]
  rw [aux_intervalIndicatorFourier, if_neg hx]
  rw [Real.sinc_of_ne_zero]
  · field_simp [hx, hr, Real.pi_ne_zero]
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr) hx

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
expresses each normalized short-interval Fourier factor as a sinc factor. -/
theorem aux_standardBump_small_factor_eq_sinc (i : ℕ) (x : ℝ) :
    (2 : ℝ) ^ (i + 2) *
        aux_intervalIndicatorFourier ((2 : ℝ) ^ (-(i : ℤ) - 3)) x =
      Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) := by
  rw [aux_intervalIndicatorFourier_eq_two_mul_sinc]
  have hpow : (2 : ℝ) ^ (-(i : ℤ) - 3) =
      (1 / 8 : ℝ) * ((2 : ℝ)⁻¹) ^ i := by
    rw [show (-(i : ℤ) - 3) = -((i : ℤ) + 3) by omega, zpow_neg]
    rw [zpow_add₀ (by norm_num)]
    norm_num
    rw [← inv_pow]
    norm_num
  rw [hpow]
  have hcoeff : (2 : ℝ) ^ (i + 2) *
      (2 * ((1 / 8 : ℝ) * ((2 : ℝ)⁻¹) ^ i)) = 1 := by
    rw [pow_add, pow_two]
    field_simp
    have htwo : (1 / 2 : ℝ) ^ i = ((2 : ℝ) ^ i)⁻¹ := by
      rw [← inv_pow]
      norm_num
    rw [htwo]
    field_simp
    norm_num
  have harg : 2 * Real.pi * ((1 / 8 : ℝ) * ((2 : ℝ)⁻¹) ^ i) * x =
      (Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i := by ring
  rw [harg]
  calc
    (2 : ℝ) ^ (i + 2) *
        (2 * ((1 / 8 : ℝ) * ((2 : ℝ)⁻¹) ^ i) *
          Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)) =
        ((2 : ℝ) ^ (i + 2) *
          (2 * ((1 / 8 : ℝ) * ((2 : ℝ)⁻¹) ^ i))) *
          Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) := by ring
    _ = Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) := by rw [hcoeff, one_mul]

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
rewrites each finite standard-bump product in a form suitable for infinite-product convergence. -/
theorem aux_standardBumpFinite_eq_sincProduct (l : ℕ) (x : ℝ) :
    standardBumpFinite l x =
      aux_intervalIndicatorFourier (3 / 4) x *
        ∏ i ∈ Finset.range l,
          Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) := by
  rw [standardBumpFinite]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact aux_standardBump_small_factor_eq_sinc i x

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is the quadratic Taylor remainder estimate that makes the sinc-factor deviations summable on
compact intervals. -/
theorem aux_sinc_sub_one_sq_bound (t : ℝ) :
    |Real.sinc t - 1| ≤ t ^ 2 := by
  by_cases ht : t = 0
  · simp [ht]
  rw [Real.sinc_of_ne_zero ht]
  have hsin : |t - Real.sin t| ≤ |t| ^ 3 := by
    refine (Real.abs_sub_sin_le t).trans ?_
    exact div_le_self (pow_nonneg (abs_nonneg t) _) (by norm_num)
  have habspos : 0 < |t| := abs_pos.mpr ht
  have hrewrite : Real.sin t / t - 1 = (Real.sin t - t) / t := by
    field_simp
  rw [hrewrite, abs_div]
  calc
    |Real.sin t - t| / |t| = |t - Real.sin t| / |t| := by
      rw [abs_sub_comm]
    _ ≤ |t| ^ 3 / |t| :=
      div_le_div_of_nonneg_right hsin habspos.le
    _ = t ^ 2 := by
      rw [show |t| ^ 3 / |t| = |t| ^ 2 by field_simp [ne_of_gt habspos], sq_abs]

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
gives the geometric compact-interval bound for the deviations of the sinc factors from one. -/
theorem aux_sinc_standard_factor_tail (R : ℝ) (hR : 0 ≤ R) (i : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-R) R) :
    |Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) - 1| ≤
      ((Real.pi / 4) * R) ^ 2 * ((1 / 4 : ℝ) ^ i) := by
  have habsx : |x| ≤ R := abs_le.mpr hx
  have hxsq : x ^ 2 ≤ R ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg x) hR).mpr habsx
    simpa only [sq_abs] using h
  have hinvpow : (((2 : ℝ)⁻¹) ^ i) ^ 2 = (1 / 4 : ℝ) ^ i := by
    rw [← pow_mul, show i * 2 = 2 * i by omega, pow_mul]
    norm_num
  calc
    |Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) - 1| ≤
        ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) ^ 2 :=
      aux_sinc_sub_one_sq_bound _
    _ = ((Real.pi / 4) ^ 2 * x ^ 2) * ((1 / 4 : ℝ) ^ i) := by
      rw [mul_pow, mul_pow, hinvpow]
    _ ≤ ((Real.pi / 4) ^ 2 * R ^ 2) * ((1 / 4 : ℝ) ^ i) := by
      gcongr
    _ = ((Real.pi / 4) * R) ^ 2 * ((1 / 4 : ℝ) ^ i) := by ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
records summability of the geometric majorant for the sinc-product tail. -/
theorem aux_standard_factor_tail_summable (R : ℝ) :
    Summable (fun i : ℕ => ((Real.pi / 4) * R) ^ 2 * ((1 / 4 : ℝ) ^ i)) := by
  exact (summable_geometric_of_lt_one (by norm_num)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left _

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
constructs the compact-uniform infinite product of the normalized sinc factors. -/
theorem aux_sinc_standard_factors_hasProdUniformlyOn (R : ℝ) (hR : 0 ≤ R) :
    HasProdUniformlyOn
      (fun (i : ℕ) (x : ℝ) => Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i))
      (fun x => ∏' i, Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i))
      (Set.Icc (-R) R) := by
  have h := (aux_standard_factor_tail_summable R).hasProdUniformlyOn_nat_one_add
    (K := Set.Icc (-R) R)
    (f := fun (i : ℕ) (x : ℝ) =>
      Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) - 1)
    isCompact_Icc
    (by
      filter_upwards [] with i
      intro x hx
      simpa only [Real.norm_eq_abs] using aux_sinc_standard_factor_tail R hR i hx)
    (by
      intro i
      have harg : Continuous (fun x : ℝ =>
          (Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) := by fun_prop
      exact ((Real.continuous_sinc.comp harg).sub continuous_const).continuousOn)
  have hident :
      (fun (i : ℕ) (x : ℝ) =>
        1 + (Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) - 1)) =
      (fun (i : ℕ) (x : ℝ) =>
        Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)) := by
    funext i x
    ring
  have hprodident :
      (fun x : ℝ => tprod (fun i : ℕ =>
        1 + (Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) - 1))) =
      (fun x : ℝ => tprod (fun i : ℕ =>
        Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i))) := by
    funext x
    apply tprod_congr
    intro i
    ring
  rw [hident, hprodident] at h
  exact h

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is the local-uniform convergence of the finite sinc products to their infinite product. -/
theorem aux_sinc_standard_factors_tendstoUniformlyOn (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun (n : ℕ) (x : ℝ) => ∏ i ∈ Finset.range n,
        Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i))
      (fun x => ∏' i, Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i))
      atTop (Set.Icc (-R) R) := by
  exact (aux_sinc_standard_factors_hasProdUniformlyOn R hR).tendstoUniformlyOn_finsetRange

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
identifies the pointwise limit of the finite standard-bump products. -/
theorem aux_standardBumpFinite_tendsto_sincProduct (x : ℝ) :
    Tendsto
      (fun n : ℕ => standardBumpFinite n x)
      atTop
      (nhds (aux_intervalIndicatorFourier (3 / 4) x *
        ∏' (i : ℕ), Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i))) := by
  have hx : x ∈ Set.Icc (-|x|) |x| := ⟨neg_abs_le x, le_abs_self x⟩
  have hprod :=
    (aux_sinc_standard_factors_tendstoUniformlyOn |x| (abs_nonneg x)).tendsto_at hx
  have hmul : Continuous (fun z : ℝ =>
      aux_intervalIndicatorFourier (3 / 4) x * z) :=
    continuous_const.mul continuous_id
  have hfinite :
      (fun n : ℕ => standardBumpFinite n x) =
      (fun n : ℕ => aux_intervalIndicatorFourier (3 / 4) x *
        ∏ i ∈ Finset.range n,
          Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)) := by
    funext n
    exact aux_standardBumpFinite_eq_sincProduct n x
  rw [hfinite]
  change Tendsto
    ((fun z : ℝ => aux_intervalIndicatorFourier (3 / 4) x * z) ∘
      fun n : ℕ => ∏ i ∈ Finset.range n,
        Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i))
    atTop _
  exact (hmul.tendsto _).comp hprod

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
rewrites the `limUnder` definition of the standard bump using the established pointwise product
limit. -/
theorem aux_standardBump_eq_sincTprod (x : ℝ) :
    standardBump x =
      aux_intervalIndicatorFourier (3 / 4) x *
        ∏' (i : ℕ), Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) := by
  have hlim := aux_standardBumpFinite_tendsto_sincProduct x
  unfold standardBump
  exact hlim.limUnder_eq

/-- For \ref{standard bump properties}, these are the radii of the short probability densities
on the Fourier side. -/
def aux_standardBumpRadius (i : ℕ) : ℝ :=
  (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ i

/-- For \ref{standard bump properties}, this is the total radius contributed by the first
`n` short probability densities. -/
def aux_standardBumpRadiusSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, aux_standardBumpRadius i

/-- For \ref{standard bump properties}, this is the unnormalized initial interval density on
the Fourier side. -/
def aux_standardBumpBaseDensity : ℝ → ℝ :=
  Set.indicator (Set.Icc (-(3 / 4 : ℝ)) (3 / 4)) (fun _ : ℝ => 1)

/-- For \ref{standard bump properties}, this is the normalized density on a symmetric interval. -/
def aux_standardBumpIntervalDensity (r : ℝ) : ℝ → ℝ := fun t =>
  (2 * r)⁻¹ * Set.indicator (Set.Icc (-r) r) (fun _ : ℝ => 1) t

/-- For \ref{standard bump properties}, this recursively constructs the real Fourier-side
density corresponding to a finite standard-bump product. -/
def aux_standardBumpFiniteDensity : ℕ → ℝ → ℝ
  | 0 => aux_standardBumpBaseDensity
  | n + 1 => aux_standardBumpFiniteDensity n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      aux_standardBumpIntervalDensity (aux_standardBumpRadius n)

/-- For \ref{standard bump properties}, the short interval radii are positive. -/
theorem aux_standardBumpRadius_pos (i : ℕ) : 0 < aux_standardBumpRadius i := by
  simp [aux_standardBumpRadius]

/-- For \ref{standard bump properties}, the short interval radii are nonnegative. -/
theorem aux_standardBumpRadius_nonneg (i : ℕ) : 0 ≤ aux_standardBumpRadius i :=
  (aux_standardBumpRadius_pos i).le

/-- For \ref{standard bump properties}, finite sums of the short interval radii are nonnegative. -/
theorem aux_standardBumpRadiusSum_nonneg (n : ℕ) : 0 ≤ aux_standardBumpRadiusSum n := by
  exact Finset.sum_nonneg fun i _ => aux_standardBumpRadius_nonneg i

/-- For \ref{standard bump properties}, this is the recursive decomposition of the radius sum. -/
theorem aux_standardBumpRadiusSum_succ (n : ℕ) :
    aux_standardBumpRadiusSum (n + 1) =
      aux_standardBumpRadiusSum n + aux_standardBumpRadius n := by
  simp [aux_standardBumpRadiusSum, Finset.sum_range_succ]

/-- For \ref{standard bump properties}, this evaluates the finite geometric radius sum. -/
theorem aux_standardBumpRadiusSum_formula (n : ℕ) :
    aux_standardBumpRadiusSum n =
      1 / 4 - (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  unfold aux_standardBumpRadiusSum
  simp only [aux_standardBumpRadius]
  rw [← Finset.mul_sum]
  have h := geom_sum_mul (1 / 2 : ℝ) n
  norm_num at h ⊢
  linarith

/-- For \ref{standard bump properties}, this converts the finite tail radius to the manuscript's
integer-exponent notation. -/
theorem aux_standardBumpTail_eq_zpow (n : ℕ) :
    (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ (-(n : ℤ) - 2) := by
  rw [show (-(n : ℤ) - 2) = -((n : ℤ) + 2) by omega, zpow_neg]
  rw [zpow_add₀ (by norm_num)]
  norm_num
  rw [← inv_pow]
  norm_num

/-- For \ref{standard bump properties}, this identifies the manuscript's short radius with its
nonnegative geometric expression. -/
theorem aux_standardBumpRadius_eq_zpow (i : ℕ) :
    aux_standardBumpRadius i = (2 : ℝ) ^ (-(i : ℤ) - 3) := by
  unfold aux_standardBumpRadius
  rw [show (-(i : ℤ) - 3) = -((i : ℤ) + 3) by omega, zpow_neg]
  rw [zpow_add₀ (by norm_num)]
  norm_num
  rw [← inv_pow]
  norm_num

/-- For \ref{standard bump properties}, the base density vanishes outside its defining interval. -/
theorem aux_standardBumpBaseDensity_support :
    Function.support aux_standardBumpBaseDensity ⊆
      Set.Icc (-(3 / 4 : ℝ)) (3 / 4) := by
  intro t ht
  by_contra htr
  change aux_standardBumpBaseDensity t ≠ 0 at ht
  simp only [aux_standardBumpBaseDensity, Set.indicator_apply, if_neg htr] at ht
  exact ht rfl

/-- For \ref{standard bump properties}, the base interval density is nonnegative. -/
theorem aux_standardBumpBaseDensity_nonneg (t : ℝ) :
    0 ≤ aux_standardBumpBaseDensity t := by
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) t

/-- For \ref{standard bump properties}, the base interval density is bounded by one. -/
theorem aux_standardBumpBaseDensity_le_one (t : ℝ) :
    aux_standardBumpBaseDensity t ≤ 1 := by
  by_cases ht : t ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4)
  · simp [aux_standardBumpBaseDensity, ht]
  · simp [aux_standardBumpBaseDensity, ht]

/-- For \ref{standard bump properties}, the base density is integrable. -/
theorem aux_standardBumpBaseDensity_integrable :
    Integrable aux_standardBumpBaseDensity := by
  rw [aux_standardBumpBaseDensity,
    MeasureTheory.integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (ne_of_lt measure_Icc_lt_top)

/-- For \ref{standard bump properties}, the base density has the interval's mass. -/
theorem aux_standardBumpBaseDensity_integral :
    ∫ t : ℝ, aux_standardBumpBaseDensity t = 3 / 2 := by
  change ∫ t : ℝ,
    Set.indicator (Set.Icc (-(3 / 4 : ℝ)) (3 / 4)) (1 : ℝ → ℝ) t = 3 / 2
  rw [MeasureTheory.integral_indicator_one measurableSet_Icc,
    MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
  · norm_num
  · norm_num

/-- For \ref{standard bump properties}, a normalized interval density vanishes outside its
defining interval. -/
theorem aux_standardBumpIntervalDensity_support (r : ℝ) :
    Function.support (aux_standardBumpIntervalDensity r) ⊆ Set.Icc (-r) r := by
  intro t ht
  by_contra htr
  change aux_standardBumpIntervalDensity r t ≠ 0 at ht
  simp only [aux_standardBumpIntervalDensity, Set.indicator_apply, if_neg htr, mul_zero] at ht
  exact ht rfl

/-- For \ref{standard bump properties}, a nonnegative radius gives a nonnegative normalized
interval density. -/
theorem aux_standardBumpIntervalDensity_nonneg (r : ℝ) (hr : 0 ≤ r) (t : ℝ) :
    0 ≤ aux_standardBumpIntervalDensity r t := by
  simp only [aux_standardBumpIntervalDensity]
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (Set.indicator_nonneg (fun _ _ => zero_le_one) t)

/-- For \ref{standard bump properties}, every normalized interval density is integrable. -/
theorem aux_standardBumpIntervalDensity_integrable (r : ℝ) :
    Integrable (aux_standardBumpIntervalDensity r) := by
  exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (ne_of_lt measure_Icc_lt_top)) |>.const_mul _

/-- For \ref{standard bump properties}, a positive-radius interval density has mass one. -/
theorem aux_standardBumpIntervalDensity_integral_one (r : ℝ) (hr : 0 < r) :
    ∫ t : ℝ, aux_standardBumpIntervalDensity r t = 1 := by
  change ∫ t : ℝ, (2 * r)⁻¹ *
    Set.indicator (Set.Icc (-r) r) (fun _ : ℝ => 1) t = 1
  rw [MeasureTheory.integral_const_mul]
  change (2 * r)⁻¹ * ∫ t : ℝ,
    Set.indicator (Set.Icc (-r) r) (1 : ℝ → ℝ) t = 1
  rw [MeasureTheory.integral_indicator_one measurableSet_Icc,
    MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
  · field_simp
    norm_num
  · linarith

/-- For \ref{standard bump properties}, this auxiliary identifies differentiation through one
normalized interval convolution with a symmetric difference quotient.  It is used to control
successive derivatives of the finite Fourier-side densities. -/
theorem aux_intervalDensity_convolution_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f)
    (r x : ℝ) (hr : 0 < r) :
    HasDerivAt
      (fun y : ℝ => (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        aux_standardBumpIntervalDensity r) y)
      ((f (x + r) - f (x - r)) / (2 * r)) x := by
  have hwindow : HasDerivAt (fun y : ℝ => ∫ t : ℝ in y - r..y + r, f t)
      (f (x + r) - f (x - r)) x := by
    let F : ℝ → ℝ := fun u => ∫ t : ℝ in 0..u, f t
    have hFplus : HasDerivAt F (f (x + r)) (x + r) := by
      exact intervalIntegral.integral_hasDerivAt_right
        (hf.intervalIntegrable 0 (x + r))
        (hf.stronglyMeasurableAtFilter volume (nhds (x + r)))
        hf.continuousAt
    have hFminus : HasDerivAt F (f (x - r)) (x - r) := by
      exact intervalIntegral.integral_hasDerivAt_right
        (hf.intervalIntegrable 0 (x - r))
        (hf.stronglyMeasurableAtFilter volume (nhds (x - r)))
        hf.continuousAt
    have hplus : HasDerivAt (fun y : ℝ => F (y + r)) (f (x + r)) x := by
      have hinner : HasDerivAt (fun y : ℝ => y + r) 1 x := by
        simpa using (hasDerivAt_id x).add_const r
      have hcomp : HasDerivAt (F ∘ fun y : ℝ => y + r) (f (x + r) * 1) x :=
        HasDerivAt.comp x hFplus hinner
      simpa [Function.comp_def] using hcomp
    have hminus : HasDerivAt (fun y : ℝ => F (y - r)) (f (x - r)) x := by
      have hinner : HasDerivAt (fun y : ℝ => y - r) 1 x := by
        simpa using (hasDerivAt_id x).sub_const r
      have hcomp : HasDerivAt (F ∘ fun y : ℝ => y - r) (f (x - r) * 1) x :=
        HasDerivAt.comp x hFminus hinner
      simpa [Function.comp_def] using hcomp
    have heq : (fun y : ℝ => ∫ t : ℝ in y - r..y + r, f t) =
        ((fun y : ℝ => F (y + r)) - fun y : ℝ => F (y - r)) := by
      funext y
      dsimp [F]
      have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hf.intervalIntegrable 0 (y - r)) (hf.intervalIntegrable (y - r) (y + r))
      linarith
    rw [heq]
    exact hplus.sub hminus
  have hconv : (fun y : ℝ => (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      aux_standardBumpIntervalDensity r) y) =
      fun y : ℝ => (2 * r)⁻¹ * ∫ t : ℝ in y - r..y + r, f t := by
    funext y
    rw [MeasureTheory.convolution_mul_swap]
    unfold aux_standardBumpIntervalDensity
    have hpoint : (fun t : ℝ => f (y - t) * ((2 * r)⁻¹ *
        Set.indicator (Set.Icc (-r) r) (fun _ : ℝ => 1) t)) =
        fun t : ℝ => (2 * r)⁻¹ *
          Set.indicator (Set.Icc (-r) r) (fun t => f (y - t)) t := by
      funext t
      by_cases ht : t ∈ Set.Icc (-r) r <;> simp [ht] <;> ring
    rw [hpoint, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator measurableSet_Icc]
    congr 1
    calc
      ∫ t : ℝ in Set.Icc (-r) r, f (y - t) =
          ∫ t : ℝ in Set.Ioc (-r) r, f (y - t) := integral_Icc_eq_integral_Ioc
      _ = ∫ t : ℝ in -r..r, f (y - t) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
      _ = ∫ t : ℝ in y - r..y + r, f t := by
        simpa only [sub_neg_eq_add] using
          intervalIntegral.integral_comp_sub_left (a := -r) (b := r) f y
  rw [hconv]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hwindow.const_mul ((2 * r)⁻¹)

/-- For \ref{standard bump properties}, this auxiliary turns a uniform bound into the sharp
bound for one symmetric interval difference quotient. -/
theorem aux_intervalDifferenceQuotient_le_of_bound (f : ℝ → ℝ) (A r x : ℝ)
    (hr : 0 < r) (hbound : ∀ z : ℝ, |f z| ≤ A) :
    |(f (x + r) - f (x - r)) / (2 * r)| ≤ A / r := by
  have hden : 0 < 2 * r := by positivity
  rw [abs_div, abs_of_pos hden]
  calc
    |f (x + r) - f (x - r)| / (2 * r) ≤
        (|f (x + r)| + |f (x - r)|) / (2 * r) := by
      apply div_le_div_of_nonneg_right _ hden.le
      simpa using (abs_sub_le (f (x + r)) 0 (f (x - r)))
    _ ≤ (A + A) / (2 * r) :=
      div_le_div_of_nonneg_right (add_le_add (hbound _) (hbound _)) hden.le
    _ = A / r := by field_simp; ring

/-- For \ref{standard bump properties}, this auxiliary shows that a symmetric interval
difference quotient does not enlarge a Lipschitz bound. -/
theorem aux_intervalDifferenceQuotient_le_of_lipschitz (f : ℝ → ℝ) (L r x : ℝ)
    (hr : 0 < r) (hLip : ∀ a b : ℝ, |f a - f b| ≤ L * |a - b|) :
    |(f (x + r) - f (x - r)) / (2 * r)| ≤ L := by
  have hden : 0 < 2 * r := by positivity
  rw [abs_div, abs_of_pos hden]
  have h := hLip (x + r) (x - r)
  have habs : |(x + r) - (x - r)| = 2 * r := by
    convert abs_of_pos hden using 1 <;> ring
  rw [habs] at h
  calc
    |f (x + r) - f (x - r)| / (2 * r) ≤ (L * (2 * r)) / (2 * r) :=
      div_le_div_of_nonneg_right h hden.le
    _ = L := by field_simp

/-- For \ref{standard bump properties}, this auxiliary propagates a Lipschitz bound through
the symmetric interval difference quotient, producing the next reciprocal-radius factor. -/
theorem aux_intervalDifferenceQuotient_lipschitz (f : ℝ → ℝ) (L r x y : ℝ)
    (hr : 0 < r) (hLip : ∀ a b : ℝ, |f a - f b| ≤ L * |a - b|) :
    |((f (x + r) - f (x - r)) / (2 * r)) -
      ((f (y + r) - f (y - r)) / (2 * r))| ≤ (L / r) * |x - y| := by
  have htri (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    calc
      |a - b| ≤ |a - 0| + |0 - b| := abs_sub_le a 0 b
      _ = |a| + |b| := by simp
  have hden : 0 < 2 * r := by positivity
  have hp : |f (x + r) - f (y + r)| ≤ L * |x - y| := by
    convert hLip (x + r) (y + r) using 1 <;> ring_nf
  have hm : |f (x - r) - f (y - r)| ≤ L * |x - y| := by
    convert hLip (x - r) (y - r) using 1 <;> ring_nf
  rw [show ((f (x + r) - f (x - r)) / (2 * r)) -
      ((f (y + r) - f (y - r)) / (2 * r)) =
      ((f (x + r) - f (y + r)) - (f (x - r) - f (y - r))) / (2 * r) by ring]
  rw [abs_div, abs_of_pos hden]
  calc
    |(f (x + r) - f (y + r)) - (f (x - r) - f (y - r))| / (2 * r) ≤
        (|f (x + r) - f (y + r)| + |f (x - r) - f (y - r)|) / (2 * r) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact htri _ _
    _ ≤ (L * |x - y| + L * |x - y|) / (2 * r) :=
      div_le_div_of_nonneg_right (add_le_add hp hm) hden.le
    _ = (L / r) * |x - y| := by field_simp; ring

/-- For \ref{standard bump properties}, convolution preserves nonnegativity of real densities. -/
theorem aux_standardBumpConvolution_nonneg (f g : ℝ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (x : ℝ) :
    0 ≤ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x := by
  rw [MeasureTheory.convolution_mul]
  exact integral_nonneg fun t => mul_nonneg (hf t) (hg (x - t))

/-- For \ref{standard bump properties}, convolution with a probability density preserves the
upper bound one. -/
theorem aux_standardBumpConvolution_le_one (f g : ℝ → ℝ)
    (hfInt : Integrable f) (hgInt : Integrable g)
    (hfnonneg : ∀ x, 0 ≤ f x) (hfle : ∀ x, f x ≤ 1)
    (hgnonneg : ∀ x, 0 ≤ g x) (hgint : ∫ x : ℝ, g x = 1) (x : ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x ≤ 1 := by
  rw [MeasureTheory.convolution_mul_swap]
  have hleftInt : Integrable (fun t : ℝ => f (x - t) * g t) := by
    refine hgInt.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · exact (hfInt.comp_sub_left x).aestronglyMeasurable.mul hgInt.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (hfnonneg _) (hgnonneg _))]
      exact mul_le_of_le_one_left (hgnonneg _) (hfle _)
  calc
    ∫ t : ℝ, f (x - t) * g t ≤ ∫ t : ℝ, 1 * g t :=
      integral_mono hleftInt (by simpa using hgInt) (fun t =>
        mul_le_mul_of_nonneg_right (hfle _) (hgnonneg _))
    _ = 1 := by simpa using hgint

/-- For \ref{standard bump properties}, this evaluates the integral of a convolution of
integrable real densities. -/
theorem aux_standardBump_integral_convolution (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) :
    ∫ x : ℝ, (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x =
      (∫ x : ℝ, f x) * (∫ x : ℝ, g x) := by
  convert MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf hg using 1
  rfl

/-- For \ref{standard bump properties}, convolving with a supported probability density preserves
a plateau after shrinking it by the support radius. -/
theorem aux_standardBumpConvolution_eq_one_on (f u : ℝ → ℝ) (a b r x : ℝ)
    (huSupp : Function.support u ⊆ Set.Icc (-r) r)
    (huMass : ∫ t : ℝ, u t = 1)
    (hfOne : ∀ z ∈ Set.Icc a b, f z = 1)
    (hx : x ∈ Set.Icc (a + r) (b - r)) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] u) x = 1 := by
  rw [MeasureTheory.convolution_mul_swap]
  calc
    ∫ t : ℝ, f (x - t) * u t = ∫ t : ℝ, u t := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Function.support u
      · have htI := huSupp ht
        have hxt : x - t ∈ Set.Icc a b := by
          constructor <;> linarith [hx.1, hx.2, htI.1, htI.2]
        rw [hfOne _ hxt, one_mul]
      · have hut : u t = 0 := Function.notMem_support.mp ht
        rw [hut, mul_zero]
    _ = 1 := huMass

/-- For \ref{standard bump properties}, every finite physical-side density is integrable. -/
theorem aux_standardBumpFiniteDensity_integrable (n : ℕ) :
    Integrable (aux_standardBumpFiniteDensity n) := by
  induction n with
  | zero => exact aux_standardBumpBaseDensity_integrable
  | succ n ih =>
      rw [aux_standardBumpFiniteDensity]
      exact ih.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
        (aux_standardBumpIntervalDensity_integrable _)

/-- For \ref{standard bump properties}, this tracks the support of each finite physical-side
density. -/
theorem aux_standardBumpFiniteDensity_support (n : ℕ) :
    Function.support (aux_standardBumpFiniteDensity n) ⊆
      Set.Icc (-(3 / 4 : ℝ) - aux_standardBumpRadiusSum n)
        (3 / 4 + aux_standardBumpRadiusSum n) := by
  induction n with
  | zero =>
      simpa [aux_standardBumpFiniteDensity, aux_standardBumpRadiusSum] using
        aux_standardBumpBaseDensity_support
  | succ n ih =>
      rw [aux_standardBumpFiniteDensity]
      calc
        Function.support
            (aux_standardBumpFiniteDensity n ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
              aux_standardBumpIntervalDensity (aux_standardBumpRadius n)) ⊆
            Function.support (aux_standardBumpFiniteDensity n) +
              Function.support (aux_standardBumpIntervalDensity (aux_standardBumpRadius n)) :=
          MeasureTheory.support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)
        _ ⊆ Set.Icc (-(3 / 4 : ℝ) - aux_standardBumpRadiusSum n)
            (3 / 4 + aux_standardBumpRadiusSum n) +
            Set.Icc (-(aux_standardBumpRadius n)) (aux_standardBumpRadius n) :=
          Set.add_subset_add ih (aux_standardBumpIntervalDensity_support _)
        _ = Set.Icc (-(3 / 4 : ℝ) - aux_standardBumpRadiusSum (n + 1))
            (3 / 4 + aux_standardBumpRadiusSum (n + 1)) := by
          rw [Set.Icc_add_Icc (by linarith [aux_standardBumpRadiusSum_nonneg n])
            (by linarith [aux_standardBumpRadius_nonneg n])]
          rw [aux_standardBumpRadiusSum_succ]
          congr 1 <;> ring

/-- For \ref{standard bump properties}, every finite physical-side density has the base mass. -/
theorem aux_standardBumpFiniteDensity_integral (n : ℕ) :
    ∫ x : ℝ, aux_standardBumpFiniteDensity n x = 3 / 2 := by
  induction n with
  | zero => simpa [aux_standardBumpFiniteDensity] using aux_standardBumpBaseDensity_integral
  | succ n ih =>
      rw [aux_standardBumpFiniteDensity, aux_standardBump_integral_convolution _ _
        (aux_standardBumpFiniteDensity_integrable n)
        (aux_standardBumpIntervalDensity_integrable _), ih,
        aux_standardBumpIntervalDensity_integral_one _ (aux_standardBumpRadius_pos _), mul_one]

/-- For \ref{standard bump properties}, every finite physical-side density is nonnegative. -/
theorem aux_standardBumpFiniteDensity_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ aux_standardBumpFiniteDensity n x := by
  induction n generalizing x with
  | zero => simpa [aux_standardBumpFiniteDensity] using aux_standardBumpBaseDensity_nonneg x
  | succ n ih =>
      rw [aux_standardBumpFiniteDensity]
      exact aux_standardBumpConvolution_nonneg _ _ (fun y => ih y)
        (aux_standardBumpIntervalDensity_nonneg _ (aux_standardBumpRadius_nonneg _)) x

/-- For \ref{standard bump properties}, every finite physical-side density is bounded by one. -/
theorem aux_standardBumpFiniteDensity_le_one (n : ℕ) (x : ℝ) :
    aux_standardBumpFiniteDensity n x ≤ 1 := by
  induction n generalizing x with
  | zero => simpa [aux_standardBumpFiniteDensity] using aux_standardBumpBaseDensity_le_one x
  | succ n ih =>
      rw [aux_standardBumpFiniteDensity]
      exact aux_standardBumpConvolution_le_one _ _ (aux_standardBumpFiniteDensity_integrable n)
        (aux_standardBumpIntervalDensity_integrable _) (aux_standardBumpFiniteDensity_nonneg n)
        (fun y => ih y)
        (aux_standardBumpIntervalDensity_nonneg _ (aux_standardBumpRadius_nonneg _))
        (aux_standardBumpIntervalDensity_integral_one _ (aux_standardBumpRadius_pos _)) x

/-- For \ref{standard bump properties}, this tracks the plateau of each finite physical-side
density. -/
theorem aux_standardBumpFiniteDensity_eq_one_on (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-(3 / 4 : ℝ) + aux_standardBumpRadiusSum n)
      (3 / 4 - aux_standardBumpRadiusSum n)) :
    aux_standardBumpFiniteDensity n x = 1 := by
  induction n generalizing x with
  | zero =>
      change aux_standardBumpBaseDensity x = 1
      have hx' : x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4) := by
        simpa [aux_standardBumpRadiusSum] using hx
      rw [aux_standardBumpBaseDensity, Set.indicator_of_mem hx']
  | succ n ih =>
      rw [aux_standardBumpFiniteDensity]
      apply aux_standardBumpConvolution_eq_one_on _ _
        (-(3 / 4 : ℝ) + aux_standardBumpRadiusSum n)
        (3 / 4 - aux_standardBumpRadiusSum n) (aux_standardBumpRadius n) x
        (aux_standardBumpIntervalDensity_support _)
        (aux_standardBumpIntervalDensity_integral_one _ (aux_standardBumpRadius_pos _))
        (fun z hz => ih z hz)
      rcases hx with ⟨hxlo, hxhi⟩
      constructor
      · calc
          -(3 / 4 : ℝ) + aux_standardBumpRadiusSum n + aux_standardBumpRadius n =
              -(3 / 4 : ℝ) + aux_standardBumpRadiusSum (n + 1) := by
                rw [aux_standardBumpRadiusSum_succ]
                ring
          _ ≤ x := hxlo
      · calc
          x ≤ 3 / 4 - aux_standardBumpRadiusSum (n + 1) := hxhi
          _ = (3 / 4 - aux_standardBumpRadiusSum n) - aux_standardBumpRadius n := by
            rw [aux_standardBumpRadiusSum_succ]
            ring

/-- For \ref{standard bump properties}, this is the finite support bound in the manuscript's
explicit endpoint form. -/
theorem aux_standardBumpFiniteDensity_support_stated (n : ℕ) :
    Function.support (aux_standardBumpFiniteDensity n) ⊆
      Set.Icc (-1 + (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n)
        (1 - (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n) := by
  intro x hx
  have h := aux_standardBumpFiniteDensity_support n hx
  rw [aux_standardBumpRadiusSum_formula] at h
  constructor <;> linarith [h.1, h.2]

/-- For \ref{standard bump properties}, this is the finite plateau bound in the manuscript's
explicit endpoint form. -/
theorem aux_standardBumpFiniteDensity_eq_one_on_stated (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-(1 / 2 : ℝ) - (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n)
      (1 / 2 + (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n)) :
    aux_standardBumpFiniteDensity n x = 1 := by
  apply aux_standardBumpFiniteDensity_eq_one_on n x
  rw [aux_standardBumpRadiusSum_formula]
  constructor <;> linarith [hx.1, hx.2]

/-- For \ref{standard bump properties}, this restates the finite support bound using the
manuscript's integer-exponent notation. -/
theorem aux_standardBumpFiniteDensity_support_stated_zpow (n : ℕ) :
    Function.support (aux_standardBumpFiniteDensity n) ⊆
      Set.Icc (-1 + (2 : ℝ) ^ (-(n : ℤ) - 2))
        (1 - (2 : ℝ) ^ (-(n : ℤ) - 2)) := by
  simpa only [aux_standardBumpTail_eq_zpow] using
    aux_standardBumpFiniteDensity_support_stated n

/-- For \ref{standard bump properties}, this restates the finite plateau bound using the
manuscript's integer-exponent notation. -/
theorem aux_standardBumpFiniteDensity_eq_one_on_stated_zpow (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-(1 / 2 : ℝ) - (2 : ℝ) ^ (-(n : ℤ) - 2))
      (1 / 2 + (2 : ℝ) ^ (-(n : ℤ) - 2))) :
    aux_standardBumpFiniteDensity n x = 1 := by
  apply aux_standardBumpFiniteDensity_eq_one_on_stated n x
  simpa only [aux_standardBumpTail_eq_zpow] using hx

/-- For \ref{standard bump properties}, this complex-valued interval indicator is the auxiliary
form needed to use Mathlib's Fourier-transform API. -/
def aux_standardBumpComplexIntervalIndicator (r : ℝ) : ℝ → ℂ :=
  Set.indicator (Set.Icc (-r) r) (fun _ : ℝ => (1 : ℂ))

/-- For \ref{standard bump properties}, this recursively packages the complex physical-side
convolutions whose Fourier transforms are the finite standard-bump products. -/
def aux_standardBumpComplexFiniteDensity : ℕ → ℝ → ℂ
  | 0 => aux_standardBumpComplexIntervalIndicator (3 / 4)
  | n + 1 => aux_standardBumpComplexFiniteDensity n ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
    (fun t => (2 * aux_standardBumpRadius n : ℂ)⁻¹ *
      aux_standardBumpComplexIntervalIndicator (aux_standardBumpRadius n) t)

/-- For \ref{standard bump properties}, the complex interval indicator is integrable. -/
theorem aux_standardBumpComplexIntervalIndicator_integrable (r : ℝ) :
    Integrable (aux_standardBumpComplexIntervalIndicator r) := by
  rw [aux_standardBumpComplexIntervalIndicator,
    MeasureTheory.integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (ne_of_lt measure_Icc_lt_top)

/-- For \ref{standard bump properties}, this rewrites the interval-indicator Fourier integrand
as an interval-restricted exponential. -/
theorem aux_standardBumpComplexIntervalIndicator_integrand (r x : ℝ) :
    (fun v : ℝ => Complex.exp (((-2 * Real.pi * v * x : ℝ) : ℂ) * Complex.I) •
      aux_standardBumpComplexIntervalIndicator r v) =
    Set.indicator (Set.Icc (-r) r)
      (fun v : ℝ => Complex.exp (((-2 * Real.pi * v * x : ℝ) : ℂ) * Complex.I)) := by
  funext v
  simp [aux_standardBumpComplexIntervalIndicator, Set.indicator_apply]

/-- For \ref{standard bump properties}, this expresses the Fourier transform of a complex
interval indicator as an interval integral. -/
theorem aux_fourier_standardBumpComplexIntervalIndicator_to_interval (r x : ℝ) (hr : 0 ≤ r) :
    𝓕 (aux_standardBumpComplexIntervalIndicator r) x =
      ∫ v : ℝ in -r..r,
        Complex.exp ((-2 * Real.pi * v * x : ℝ) * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, aux_standardBumpComplexIntervalIndicator_integrand,
    MeasureTheory.integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le]
  linarith

/-- For \ref{standard bump properties}, this evaluates the preceding interval integral in the
sinc normalization. -/
theorem aux_fourier_standardBumpComplexIntervalIndicator_sinc (r x : ℝ) (hr : 0 ≤ r) :
    𝓕 (aux_standardBumpComplexIntervalIndicator r) x =
      (2 * r * Real.sinc (2 * Real.pi * r * x) : ℂ) := by
  rw [aux_fourier_standardBumpComplexIntervalIndicator_to_interval r x hr]
  by_cases hx : x = 0
  · subst x
    simp
    ring
  let c : ℝ := -2 * Real.pi * x
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hphase (v : ℝ) : -2 * Real.pi * v * x = c * v := by
    dsimp [c]
    ring
  simp_rw [hphase]
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ =>
    Complex.exp ((t : ℂ) * Complex.I)) hc]
  have hbounds : c * -r = -(c * r) := by ring
  rw [hbounds, integral_exp_mul_I_eq_sinc]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
  have hcr : c * r = -(2 * Real.pi * r * x) := by
    dsimp [c]
    ring
  rw [hcr, Real.sinc_neg]
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  field_simp

/-- For \ref{standard bump properties}, this identifies the complex interval Fourier transform
with the real-valued factor used in `standardBumpFinite`. -/
theorem aux_fourier_standardBumpComplexIntervalIndicator (r x : ℝ) (hr : 0 ≤ r) :
    𝓕 (aux_standardBumpComplexIntervalIndicator r) x =
      (aux_intervalIndicatorFourier r x : ℂ) := by
  rw [aux_fourier_standardBumpComplexIntervalIndicator_sinc r x hr,
    aux_intervalIndicatorFourier_eq_two_mul_sinc]
  norm_cast

/-- For \ref{standard bump properties}, this pulls a complex scalar through the Fourier
integral. -/
theorem aux_standardBump_fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun t => c * f t) x = c * 𝓕 f x := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← MeasureTheory.integral_const_mul]
  congr with t
  ring

/-- For \ref{standard bump properties}, this evaluates the Fourier transform of a normalized
complex short-interval density. -/
theorem aux_fourier_standardBumpComplexIntervalDensity (r x : ℝ) (hr : 0 < r) :
    𝓕 (fun t : ℝ => (2 * r : ℂ)⁻¹ * aux_standardBumpComplexIntervalIndicator r t) x =
      (Real.sinc (2 * Real.pi * r * x) : ℂ) := by
  rw [aux_standardBump_fourier_const_mul,
    aux_fourier_standardBumpComplexIntervalIndicator_sinc r x hr.le]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  field_simp

/-- For \ref{standard bump properties}, this puts a normalized short-interval Fourier factor
in the exact sinc form occurring in the finite product. -/
theorem aux_fourier_standardBumpComplexIntervalDensity_factor (i : ℕ) (x : ℝ) :
    𝓕 (fun t : ℝ => (2 * aux_standardBumpRadius i : ℂ)⁻¹ *
      aux_standardBumpComplexIntervalIndicator (aux_standardBumpRadius i) t) x =
      (Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) : ℂ) := by
  rw [aux_fourier_standardBumpComplexIntervalDensity _ x (aux_standardBumpRadius_pos i)]
  congr 1
  simp only [aux_standardBumpRadius]
  ring

/-- For \ref{standard bump properties}, every complex finite physical-side convolution is
integrable. -/
theorem aux_standardBumpComplexFiniteDensity_integrable (n : ℕ) :
    Integrable (aux_standardBumpComplexFiniteDensity n) := by
  induction n with
  | zero => exact aux_standardBumpComplexIntervalIndicator_integrable _
  | succ n ih =>
      rw [aux_standardBumpComplexFiniteDensity]
      exact ih.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
        ((aux_standardBumpComplexIntervalIndicator_integrable _).const_mul _)

/-- For \ref{standard bump properties}, this transfers a real convolution to its pointwise
complexification; it is used to identify the physical-side finite densities. -/
theorem aux_standardBumpComplexConvolution_coe (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g)
    (hfnonneg : ∀ t, 0 ≤ f t) (hfle : ∀ t, f t ≤ 1) (x : ℝ) :
    ((fun t : ℝ => (f t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      (fun t : ℝ => (g t : ℂ))) x =
      ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x : ℂ) := by
  rw [MeasureTheory.convolution_mul, MeasureTheory.convolution_mul]
  have hfg : Integrable (fun t : ℝ => f t * g (x - t)) := by
    refine (hg.comp_sub_left x).mono ?_ (Filter.Eventually.of_forall fun t => ?_)
    · exact hf.aestronglyMeasurable.mul (hg.comp_sub_left x).aestronglyMeasurable
    · calc
        ‖f t * g (x - t)‖ = ‖f t‖ * ‖g (x - t)‖ := norm_mul _ _
        _ ≤ 1 * ‖g (x - t)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Real.norm_of_nonneg (hfnonneg t)]
          exact hfle t
        _ = ‖g (x - t)‖ := one_mul _
  simpa only [← Complex.ofReal_mul, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.integral_comp_comm hfg

/-- For \ref{standard bump properties}, this identifies the normalized complex interval
density with the complexification of its real counterpart. -/
theorem aux_standardBumpComplexIntervalDensity_coe (r t : ℝ) :
    (2 * r : ℂ)⁻¹ * aux_standardBumpComplexIntervalIndicator r t =
      (aux_standardBumpIntervalDensity r t : ℂ) := by
  by_cases ht : t ∈ Set.Icc (-r) r <;>
    simp [aux_standardBumpComplexIntervalIndicator, aux_standardBumpIntervalDensity, ht,
      Complex.ofReal_mul, Complex.ofReal_inv]

/-- For \ref{standard bump properties}, this identifies the complex finite convolution density
with the complexification of the real density, transferring its support and plateau bounds. -/
theorem aux_standardBumpComplexFiniteDensity_coe (n : ℕ) (x : ℝ) :
    aux_standardBumpComplexFiniteDensity n x = (aux_standardBumpFiniteDensity n x : ℂ) := by
  induction n generalizing x with
  | zero =>
      by_cases hx : x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4) <;>
        simp [aux_standardBumpComplexFiniteDensity, aux_standardBumpFiniteDensity,
          aux_standardBumpComplexIntervalIndicator, aux_standardBumpBaseDensity, hx]
  | succ n ih =>
      rw [aux_standardBumpComplexFiniteDensity, aux_standardBumpFiniteDensity]
      have hF : aux_standardBumpComplexFiniteDensity n =
          fun t : ℝ => (aux_standardBumpFiniteDensity n t : ℂ) := by
        funext t
        exact ih t
      have hG : (fun t : ℝ => (2 * aux_standardBumpRadius n : ℂ)⁻¹ *
          aux_standardBumpComplexIntervalIndicator (aux_standardBumpRadius n) t) =
          fun t : ℝ => (aux_standardBumpIntervalDensity (aux_standardBumpRadius n) t : ℂ) := by
        funext t
        exact aux_standardBumpComplexIntervalDensity_coe _ _
      rw [hF, hG]
      exact aux_standardBumpComplexConvolution_coe _ _
        (aux_standardBumpFiniteDensity_integrable n)
        (aux_standardBumpIntervalDensity_integrable _)
        (aux_standardBumpFiniteDensity_nonneg n)
        (aux_standardBumpFiniteDensity_le_one n) x

/-- For \ref{standard bump properties}, this is the finite convolution-to-product Fourier
identity before evaluating the individual interval factors. -/
theorem aux_fourier_standardBumpComplexFiniteDensity_product (n : ℕ) (x : ℝ) :
    𝓕 (aux_standardBumpComplexFiniteDensity n) x =
      𝓕 (aux_standardBumpComplexIntervalIndicator (3 / 4)) x *
        ∏ i ∈ Finset.range n,
          𝓕 (fun t : ℝ => (2 * aux_standardBumpRadius i : ℂ)⁻¹ *
            aux_standardBumpComplexIntervalIndicator (aux_standardBumpRadius i) t) x := by
  induction n with
  | zero => simp [aux_standardBumpComplexFiniteDensity]
  | succ n ih =>
      rw [aux_standardBumpComplexFiniteDensity,
        Real.fourier_mul_convolution_eq (aux_standardBumpComplexFiniteDensity_integrable n)
          ((aux_standardBumpComplexIntervalIndicator_integrable _).const_mul _) x,
        ih, Finset.prod_range_succ]
      ring

/-- For \ref{standard bump properties}, this identifies each finite standard-bump product as
the Fourier transform of its complex physical-side convolution density. -/
theorem aux_fourier_standardBumpComplexFiniteDensity_eq_standardBumpFinite (n : ℕ) (x : ℝ) :
    𝓕 (aux_standardBumpComplexFiniteDensity n) x = (standardBumpFinite n x : ℂ) := by
  rw [aux_fourier_standardBumpComplexFiniteDensity_product,
    aux_fourier_standardBumpComplexIntervalIndicator (3 / 4) x (by norm_num)]
  have hprod :
      (∏ i ∈ Finset.range n,
        𝓕 (fun t : ℝ => (2 * aux_standardBumpRadius i : ℂ)⁻¹ *
          aux_standardBumpComplexIntervalIndicator (aux_standardBumpRadius i) t) x) =
      ∏ i ∈ Finset.range n,
        (Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i) : ℂ) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact aux_fourier_standardBumpComplexIntervalDensity_factor i x
  rw [hprod, aux_standardBumpFinite_eq_sincProduct]
  norm_cast

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is the elementary inverse-absolute-value decay of sinc away from zero. -/
theorem aux_abs_sinc_le_inv_abs {t : ℝ} (ht : t ≠ 0) :
    |Real.sinc t| ≤ |t|⁻¹ := by
  rw [Real.sinc_of_ne_zero ht, abs_div]
  calc
    |Real.sin t| / |t| ≤ 1 / |t| :=
      div_le_div_of_nonneg_right (Real.abs_sin_le_one t) (abs_pos.mpr ht).le
    _ = |t|⁻¹ := by rw [one_div]

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
turns the boundedness and inverse decay of a sinc factor into a globally integrable-type
majorant after multiplication by a positive scale. -/
theorem aux_abs_sinc_mul_le_majorant {a c : ℝ} (ha : 0 < a) (hc : 2 ≤ c)
    (hca : 2 ≤ c * a) (x : ℝ) :
    |Real.sinc (a * x)| ≤ c * (1 + |x|)⁻¹ := by
  have hden : 0 < 1 + |x| := by positivity
  by_cases hx : |x| ≤ 1
  · calc
      |Real.sinc (a * x)| ≤ 1 := Real.abs_sinc_le_one _
      _ ≤ c * (1 + |x|)⁻¹ := by
        rw [show c * (1 + |x|)⁻¹ = c / (1 + |x|) by field_simp]
        apply (le_div_iff₀ hden).2
        nlinarith
  · have hxone : 1 < |x| := lt_of_not_ge hx
    have hxne : x ≠ 0 := by
      intro h
      subst x
      norm_num at hxone
    calc
      |Real.sinc (a * x)| ≤ |a * x|⁻¹ :=
        aux_abs_sinc_le_inv_abs (mul_ne_zero (ne_of_gt ha) hxne)
      _ = (a * |x|)⁻¹ := by rw [abs_mul, abs_of_pos ha]
      _ = 1 / (a * |x|) := by rw [one_div]
      _ ≤ c / (1 + |x|) := by
        apply (div_le_div_iff₀ (mul_pos ha (abs_pos.mpr hxne)) hden).2
        calc
          1 * (1 + |x|) = 1 + |x| := by ring
          _ ≤ 2 * |x| := by nlinarith
          _ ≤ (c * a) * |x| :=
            mul_le_mul_of_nonneg_right hca (abs_nonneg x)
          _ = c * (a * |x|) := by ring
      _ = c * (1 + |x|)⁻¹ := by field_simp

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is a global decay bound for the initial, long-interval sinc factor. -/
theorem aux_standardBump_base_sinc_abs_le_majorant (x : ℝ) :
    |aux_intervalIndicatorFourier (3 / 4) x| ≤ 3 * (1 + |x|)⁻¹ := by
  rw [aux_intervalIndicatorFourier_eq_two_mul_sinc]
  have hphase : |Real.sinc ((3 * Real.pi / 2) * x)| ≤ 2 * (1 + |x|)⁻¹ := by
    apply aux_abs_sinc_mul_le_majorant
    · positivity
    · norm_num
    · nlinarith [Real.pi_gt_three]
  have harg : 2 * Real.pi * (3 / 4) * x = (3 * Real.pi / 2) * x := by ring
  rw [harg]
  calc
    |2 * (3 / 4) * Real.sinc ((3 * Real.pi / 2) * x)| =
        (3 / 2) * |Real.sinc ((3 * Real.pi / 2) * x)| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ (3 / 2) * (2 * (1 + |x|)⁻¹) :=
      mul_le_mul_of_nonneg_left hphase (by norm_num)
    _ = 3 * (1 + |x|)⁻¹ := by ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is a global decay bound for the first short-interval sinc factor. -/
theorem aux_standardBump_first_sinc_abs_le_majorant (x : ℝ) :
    |Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ 0)| ≤
      4 * (1 + |x|)⁻¹ := by
  have hphase : |Real.sinc ((Real.pi / 4) * x)| ≤ 4 * (1 + |x|)⁻¹ := by
    apply aux_abs_sinc_mul_le_majorant
    · positivity
    · norm_num
    · nlinarith [Real.pi_gt_three]
  simpa using hphase

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, the
remaining finite sinc factors have product of absolute value at most one. -/
theorem aux_standardBump_sinc_tail_abs_le_one (n : ℕ) (x : ℝ) :
    |∏ i ∈ Finset.range n,
      Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ (i + 1))| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro i hi
    exact abs_nonneg _
  · intro i hi
    exact Real.abs_sinc_le_one _

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is the integrable two-sinc majorant for every nontrivial finite standard-bump product. -/
theorem aux_standardBumpFinite_succ_abs_le_majorant (n : ℕ) (x : ℝ) :
    |standardBumpFinite (n + 1) x| ≤ 12 * (1 + x ^ 2)⁻¹ := by
  rw [aux_standardBumpFinite_eq_sincProduct, Finset.prod_range_succ']
  rw [abs_mul, abs_mul]
  have htail :
      |(∏ i ∈ Finset.range n,
        Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ (i + 1)))| ≤ 1 :=
    aux_standardBump_sinc_tail_abs_le_one n x
  have hfirst := aux_standardBump_first_sinc_abs_le_majorant x
  have htailFirst :
      abs (∏ i ∈ Finset.range n,
        Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ (i + 1))) *
          abs (Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ 0)) ≤
        1 * (4 * (1 + |x|)⁻¹) :=
    mul_le_mul htail hfirst (abs_nonneg _) (by positivity)
  have hbase := aux_standardBump_base_sinc_abs_le_majorant x
  have hden : 0 < 1 + |x| := by positivity
  have hdenSq : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos hden
  have hcompare : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  have hinv : ((1 + |x|) ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ :=
    (inv_le_inv₀ hdenSq (by positivity)).2 hcompare
  calc
    abs (aux_intervalIndicatorFourier (3 / 4) x) *
        (abs (∏ i ∈ Finset.range n,
          Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ (i + 1))) *
          abs (Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ 0))) ≤
        (3 * (1 + |x|)⁻¹) * (1 * (4 * (1 + |x|)⁻¹)) :=
      mul_le_mul hbase htailFirst (by positivity) (by positivity)
    _ = 12 * ((1 + |x|) ^ 2)⁻¹ := by
      field_simp [ne_of_gt hden]
      ring
    _ ≤ 12 * (1 + x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_l1Convergence`, this is the continuity of the interval Fourier factor
needed for the measurability of the finite products. -/
theorem aux_continuous_intervalIndicatorFourier (r : ℝ) :
    Continuous (aux_intervalIndicatorFourier r) := by
  rw [show aux_intervalIndicatorFourier r =
      fun x : ℝ => 2 * r * Real.sinc (2 * Real.pi * r * x) by
    funext x
    exact aux_intervalIndicatorFourier_eq_two_mul_sinc r x]
  fun_prop

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_l1Convergence`, this supplies continuity, hence strong measurability, of
each finite standard-bump product. -/
theorem aux_continuous_standardBumpFinite (n : ℕ) :
    Continuous (standardBumpFinite n) := by
  unfold standardBumpFinite
  apply (aux_continuous_intervalIndicatorFourier _).mul
  apply continuous_finsetProd
  intro i hi
  exact continuous_const.mul (aux_continuous_intervalIndicatorFourier _)

/-- For \ref{standard bump properties} and the public theorems
`standardBumpProperties_l1Convergence` and `standardBumpProperties_linfConvergence`, this
identifies the pointwise finite-product limit with the standard bump. -/
theorem aux_standardBumpFinite_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => standardBumpFinite n x) atTop (nhds (standardBump x)) := by
  rw [aux_standardBump_eq_sincTprod]
  exact aux_standardBumpFinite_tendsto_sincProduct x

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_l1Convergence`, this derives the strong measurability of the limiting
standard bump from the continuous finite products and their pointwise limit. -/
theorem aux_standardBump_aestronglyMeasurable :
    AEStronglyMeasurable standardBump volume := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (aux_continuous_standardBumpFinite n).aestronglyMeasurable)
  filter_upwards [] with x
  exact aux_standardBumpFinite_tendsto x

/-- For \ref{standard bump properties} and the public theorems
`standardBumpProperties_l1Convergence` and `standardBumpProperties_linfConvergence`, this passes
the finite two-sinc majorant to the pointwise standard-bump limit. -/
theorem aux_standardBump_abs_le_majorant (x : ℝ) :
    |standardBump x| ≤ 12 * (1 + x ^ 2)⁻¹ := by
  have hlim := (Filter.tendsto_add_atTop_iff_nat 1).2
    (aux_standardBumpFinite_tendsto x)
  have habs : Tendsto (fun n : ℕ => |standardBumpFinite (n + 1) x|)
      atTop (nhds |standardBump x|) := by
    simpa only [Real.norm_eq_abs] using hlim.norm
  exact le_of_tendsto' habs
    (fun n => aux_standardBumpFinite_succ_abs_le_majorant n x)

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
gives the global one-factor decay estimate used to obtain arbitrary polynomial moments of the
standard bump. -/
theorem aux_standardBump_sinc_factor_abs_le_majorant (i : ℕ) (x : ℝ) :
    |Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)| ≤
      (2 : ℝ) ^ (i + 2) * (1 + |x|)⁻¹ := by
  have harg : (Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i =
      ((Real.pi / 4) * ((2 : ℝ)⁻¹) ^ i) * x := by ring
  rw [harg]
  apply aux_abs_sinc_mul_le_majorant
  · positivity
  · have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    nlinarith [show (4 : ℝ) ≤ 2 ^ (i + 2) by
      rw [pow_add]
      norm_num
      nlinarith]
  · have hpow : (2 : ℝ) ^ (i + 2) * ((Real.pi / 4) * ((2 : ℝ)⁻¹) ^ i) = Real.pi := by
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, pow_add]
      norm_num
      calc
        2 ^ i * 4 * (Real.pi / 4 * (1 / 2) ^ i) =
            Real.pi * (2 ^ i * (1 / 2) ^ i) := by ring
        _ = Real.pi := by rw [← mul_pow]; norm_num
    rw [hpow]
    linarith [Real.pi_gt_three]

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
multiplies the one-factor estimates through a finite prefix of the sinc product. -/
theorem aux_standardBump_sinc_prefix_abs_le_majorant (r : ℕ) (x : ℝ) :
    |∏ i ∈ Finset.range r,
      Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)| ≤
      (2 : ℝ) ^ (r * (r - 1) / 2 + 2 * r) * (1 + |x|)⁻¹ ^ r := by
  have hcoeff : (∏ i ∈ Finset.range r, (2 : ℝ) ^ (i + 2)) =
      (2 : ℝ) ^ (r * (r - 1) / 2 + 2 * r) := by
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_range_id]
    simp
    ring
  rw [Finset.abs_prod]
  calc
    (∏ i ∈ Finset.range r,
        |Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)|) ≤
      ∏ i ∈ Finset.range r,
        ((2 : ℝ) ^ (i + 2) * (1 + |x|)⁻¹) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact abs_nonneg _
      · intro i hi
        exact aux_standardBump_sinc_factor_abs_le_majorant i x
    _ = (2 : ℝ) ^ (r * (r - 1) / 2 + 2 * r) * (1 + |x|)⁻¹ ^ r := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, hcoeff]

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
records that every shifted residual sinc product has absolute value at most one. -/
theorem aux_standardBump_sinc_shifted_tail_abs_le_one (r l : ℕ) (x : ℝ) :
    (∏ i ∈ Finset.range l,
      abs (Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ (r + i)))) ≤ 1 := by
  apply Finset.prod_le_one
  · intro i hi
    exact abs_nonneg _
  · intro i hi
    exact Real.abs_sinc_le_one _

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is the arbitrary-order finite-product majorant from which the weighted bounds are passed to the
limit. -/
theorem aux_standardBumpFinite_add_abs_le_highMajorant (r l : ℕ) (x : ℝ) :
    |standardBumpFinite (r + l) x| ≤
      3 * (2 : ℝ) ^ (r * (r - 1) / 2 + 2 * r) * (1 + |x|)⁻¹ ^ (r + 1) := by
  rw [aux_standardBumpFinite_eq_sincProduct, Finset.prod_range_add]
  rw [abs_mul, abs_mul]
  have hbase := aux_standardBump_base_sinc_abs_le_majorant x
  have hprefix := aux_standardBump_sinc_prefix_abs_le_majorant r x
  have htail := aux_standardBump_sinc_shifted_tail_abs_le_one r l x
  have htail' :
      abs (∏ x_1 ∈ Finset.range l,
        Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ (r + x_1))) ≤ 1 := by
    rw [Finset.abs_prod]
    exact htail
  have hinner :
      |∏ x_1 ∈ Finset.range r,
          Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ x_1)| *
        |∏ x_1 ∈ Finset.range l,
          Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ (r + x_1))| ≤
        ((2 : ℝ) ^ (r * (r - 1) / 2 + 2 * r) * (1 + |x|)⁻¹ ^ r) * 1 := by
    apply mul_le_mul hprefix htail'
    · exact abs_nonneg _
    · positivity
  calc
    |aux_intervalIndicatorFourier (3 / 4) x| *
          (|∏ x_1 ∈ Finset.range r,
              Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ x_1)| *
            |∏ x_1 ∈ Finset.range l,
              Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ (r + x_1))|) ≤
        (3 * (1 + |x|)⁻¹) *
          ((2 : ℝ) ^ (r * (r - 1) / 2 + 2 * r) * (1 + |x|)⁻¹ ^ r * 1) := by
      exact mul_le_mul hbase hinner
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
    _ = 3 * (2 : ℝ) ^ (r * (r - 1) / 2 + 2 * r) * (1 + |x|)⁻¹ ^ (r + 1) := by
      rw [show r + 1 = r.succ by omega, pow_succ]
      ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
passes the arbitrary finite-product majorant to the standard-bump limit. -/
theorem aux_standardBump_abs_le_highMajorant (r : ℕ) (x : ℝ) :
    |standardBump x| ≤
      3 * (2 : ℝ) ^ (r * (r - 1) / 2 + 2 * r) * (1 + |x|)⁻¹ ^ (r + 1) := by
  have hlim := (Filter.tendsto_add_atTop_iff_nat r).2
    (aux_standardBumpFinite_tendsto x)
  have habs : Tendsto (fun l : ℕ => |standardBumpFinite (r + l) x|)
      atTop (nhds |standardBump x|) := by
    simpa only [Real.norm_eq_abs, add_comm] using hlim.norm
  exact le_of_tendsto' habs (fun l => aux_standardBumpFinite_add_abs_le_highMajorant r l x)

/--
\begin{proposition}[standard bump]\label{standard bump properties}
The limit $\lim_{l\to \infty} \Phi_l$ exists in $L^1$ sense.
\end{proposition}
-/
theorem standardBumpProperties_l1Convergence :
    Tendsto (fun n : ℕ => eLpNorm (standardBumpFinite n - standardBump) 1 volume)
      atTop (nhds 0) := by
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (standardBumpFinite (n + 1)) volume := fun n =>
    (aux_continuous_standardBumpFinite _).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ x : ℝ ∂volume,
      ‖standardBumpFinite (n + 1) x‖ ≤ 24 * (1 + x ^ 2)⁻¹ := by
    intro n
    filter_upwards [] with x
    exact (aux_standardBumpFinite_succ_abs_le_majorant n x).trans
      (by
        apply mul_le_mul_of_nonneg_right (by norm_num : (12 : ℝ) ≤ 24)
        positivity)
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n : ℕ => standardBumpFinite (n + 1) x)
        atTop (nhds (standardBump x)) := by
    filter_upwards [] with x
    exact (Filter.tendsto_add_atTop_iff_nat 1).2 (aux_standardBumpFinite_tendsto x)
  have h := tendsto_lintegral_norm_of_dominated_convergence hmeas
      ((integrable_inv_one_add_sq.const_mul 24).hasFiniteIntegral) hbound hpoint
  simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply,
    ← ofReal_norm_eq_enorm] using h

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_linfConvergence`, this turns the decay of the base sinc factor into the
uniform bound used on compact sets. -/
theorem aux_standardBump_base_abs_le_three (x : ℝ) :
    |aux_intervalIndicatorFourier (3 / 4) x| ≤ 3 := by
  calc
    |aux_intervalIndicatorFourier (3 / 4) x| ≤ 3 * (1 + |x|)⁻¹ :=
      aux_standardBump_base_sinc_abs_le_majorant x
    _ ≤ 3 * 1 := by
      gcongr
      exact (inv_le_one₀ (by positivity)).2 (by linarith [abs_nonneg x])
    _ = 3 := by ring

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_linfConvergence`, this transfers compact-uniform convergence of the sinc
product to compact-uniform convergence of the finite standard bumps. -/
theorem aux_standardBumpFinite_tendstoUniformlyOn (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => standardBumpFinite n x)
      standardBump atTop (Set.Icc (-R) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hconv := aux_sinc_standard_factors_tendstoUniformlyOn R hR
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  filter_upwards [hconv (ε / 3) (by positivity)] with n hn x hx
  let p : ℝ := ∏' (i : ℕ), Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)
  let q : ℝ := ∏ i ∈ Finset.range n,
    Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)
  have hprod : dist p q < ε / 3 := by
    exact hn x hx
  rw [Real.dist_eq, aux_standardBump_eq_sincTprod,
    aux_standardBumpFinite_eq_sincProduct, ← mul_sub, abs_mul]
  have hbase := aux_standardBump_base_abs_le_three x
  rw [Real.dist_eq] at hprod
  change |aux_intervalIndicatorFourier (3 / 4) x| * |p - q| < ε
  calc
    |aux_intervalIndicatorFourier (3 / 4) x| * |p - q| ≤
        3 * |p - q| :=
      mul_le_mul_of_nonneg_right hbase (abs_nonneg _)
    _ < 3 * (ε / 3) := mul_lt_mul_of_pos_left hprod (by norm_num)
    _ = ε := by field_simp

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_linfConvergence`, this makes the uniform tail from the two-sinc majorant
quantitative. -/
theorem aux_standardBump_tail_lt (ε x : ℝ) (hε : 0 < ε)
    (hx : max 1 (24 / ε) < |x|) :
    24 * (1 + x ^ 2)⁻¹ < ε := by
  have habsone : 1 ≤ |x| := by
    calc
      1 ≤ max 1 (24 / ε) := le_max_left _ _
      _ ≤ |x| := hx.le
  have habsden : |x| ≤ 1 + x ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg x]
  have hdiv : 24 / ε < 1 + x ^ 2 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hx) habsden
  have hden : 0 < 1 + x ^ 2 := by positivity
  have hcross : 24 < (1 + x ^ 2) * ε :=
    (div_lt_iff₀ hε).mp hdiv
  rw [show 24 * (1 + x ^ 2)⁻¹ = 24 / (1 + x ^ 2) by field_simp]
  exact (div_lt_iff₀ hden).2 (by nlinarith)

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_linfConvergence`, this combines compact-uniform convergence with the
uniform two-sinc tail to obtain global uniform convergence. -/
theorem aux_standardBumpFinite_tendstoUniformly :
    TendstoUniformly (fun (n : ℕ) (x : ℝ) => standardBumpFinite n x)
      standardBump atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let R : ℝ := max 1 (24 / ε)
  have hR : 0 ≤ R := by
    dsimp [R]
    exact le_trans zero_le_one (le_max_left _ _)
  have hlocal := aux_standardBumpFinite_tendstoUniformlyOn R hR
  rw [Metric.tendstoUniformlyOn_iff] at hlocal
  filter_upwards [hlocal ε hε, eventually_ge_atTop 1] with n hn hn1 x
  by_cases hx : x ∈ Set.Icc (-R) R
  · exact hn x hx
  · have hxabs : R < |x| := by
      by_contra h
      have habsle : |x| ≤ R := le_of_not_gt h
      apply hx
      exact ⟨(neg_le_neg habsle).trans (neg_abs_le x),
        (le_abs_self x).trans habsle⟩
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn1
    subst n
    rw [Real.dist_eq]
    calc
      |standardBump x - standardBumpFinite (1 + k) x| ≤
          |standardBump x| + |standardBumpFinite (1 + k) x| := by
        simpa [add_comm] using
          (abs_sub_le (standardBump x) 0 (standardBumpFinite (1 + k) x))
      _ ≤ 12 * (1 + x ^ 2)⁻¹ + 12 * (1 + x ^ 2)⁻¹ :=
        add_le_add (aux_standardBump_abs_le_majorant x)
          (by simpa [add_comm] using aux_standardBumpFinite_succ_abs_le_majorant k x)
      _ = 24 * (1 + x ^ 2)⁻¹ := by ring
      _ < ε := by
        apply aux_standardBump_tail_lt ε x hε
        simpa [R] using hxabs

/--
\begin{proposition}[standard bump]\label{standard bump properties}
The limit $\lim_{l\to \infty} \Phi_l$ exists in $L^\infty$ sense.
\end{proposition}
-/
theorem standardBumpProperties_linfConvergence :
    Tendsto (fun n : ℕ => eLpNorm (standardBumpFinite n - standardBump) ⊤ volume)
      atTop (nhds 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨0, fun n hn => ?_⟩
    simp [htop]
  · have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    have huniform := aux_standardBumpFinite_tendstoUniformly
    rw [Metric.tendstoUniformly_iff] at huniform
    rcases (eventually_atTop.1 (huniform ε.toReal hεreal)) with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    rw [eLpNorm_exponent_top]
    calc
      eLpNormEssSup (standardBumpFinite n - standardBump) volume ≤
          ENNReal.ofReal ε.toReal :=
        eLpNormEssSup_le_of_ae_bound (ae_of_all _ fun x => by
          have hdist := hN n hn x
          rw [Real.dist_eq] at hdist
          simpa only [Real.norm_eq_abs, Pi.sub_apply, abs_sub_comm] using hdist.le)
      _ = ε := ENNReal.ofReal_toReal htop

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this records that an interval density is continuous away
from its two endpoints.  It supplies the dominated-convergence proof of continuity for the first
finite convolution density. -/
theorem aux_continuousAt_standardBumpIntervalDensity_offBoundary (r z : ℝ)
    (hlo : z ≠ -r) (hhi : z ≠ r) :
    ContinuousAt (aux_standardBumpIntervalDensity r) z := by
  unfold aux_standardBumpIntervalDensity
  by_cases hz : z ∈ Set.Icc (-r) r
  · have hzl : -r < z := lt_of_le_of_ne hz.1 (Ne.symm hlo)
    have hzr : z < r := lt_of_le_of_ne hz.2 hhi
    apply (show (fun y : ℝ => (2 * r)⁻¹ *
        Set.indicator (Set.Icc (-r) r) (fun _ : ℝ => 1) y) =ᶠ[nhds z]
        fun _ => (2 * r)⁻¹ from ?_).continuousAt
    filter_upwards [eventually_gt_nhds hzl, eventually_lt_nhds hzr] with y hyl hyr
    simp [hyl.le, hyr.le]
  · by_cases hzl : z < -r
    · apply (show (fun y : ℝ => (2 * r)⁻¹ *
          Set.indicator (Set.Icc (-r) r) (fun _ : ℝ => 1) y) =ᶠ[nhds z]
          fun _ => 0 from ?_).continuousAt
      filter_upwards [eventually_lt_nhds hzl] with y hy
      simp [not_le.mpr hy]
    · have hlow : -r ≤ z := le_of_not_gt hzl
      have hzr : r < z := by
        by_contra h
        exact hz ⟨hlow, le_of_not_gt h⟩
      apply (show (fun y : ℝ => (2 * r)⁻¹ *
          Set.indicator (Set.Icc (-r) r) (fun _ : ℝ => 1) y) =ᶠ[nhds z]
          fun _ => 0 from ?_).continuousAt
      filter_upwards [eventually_gt_nhds hzr] with y hy
      simp [not_le.mpr hy]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this proves continuity of the first nontrivial finite
physical-side density by dominated convergence. -/
theorem aux_continuous_standardBumpFiniteDensity_one :
    Continuous (aux_standardBumpFiniteDensity 1) := by
  change Continuous (aux_standardBumpBaseDensity ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
    aux_standardBumpIntervalDensity (aux_standardBumpRadius 0))
  rw [continuous_iff_continuousAt]
  intro x0
  change ContinuousAt (fun x : ℝ => ∫ t : ℝ, aux_standardBumpBaseDensity t *
    aux_standardBumpIntervalDensity (aux_standardBumpRadius 0) (x - t)) x0
  let r : ℝ := aux_standardBumpRadius 0
  change ContinuousAt (fun x : ℝ => ∫ t : ℝ, aux_standardBumpBaseDensity t *
    aux_standardBumpIntervalDensity r (x - t)) x0
  have hmeas (x : ℝ) : AEStronglyMeasurable
      (fun t : ℝ => aux_standardBumpBaseDensity t *
        aux_standardBumpIntervalDensity r (x - t)) volume := by
    exact aux_standardBumpBaseDensity_integrable.aestronglyMeasurable.mul
      ((aux_standardBumpIntervalDensity_integrable r).comp_sub_left x).aestronglyMeasurable
  have hbound (y : ℝ) : ‖aux_standardBumpIntervalDensity r y‖ ≤ 4 := by
    unfold aux_standardBumpIntervalDensity
    dsimp [r]
    by_cases hy : y ∈ Set.Icc (-aux_standardBumpRadius 0) (aux_standardBumpRadius 0)
    · rw [Set.indicator_of_mem hy]
      norm_num [aux_standardBumpRadius]
    · simp [hy]
  refine continuousAt_of_dominated
    (Filter.Eventually.of_forall fun x => hmeas x)
    (Filter.Eventually.of_forall fun x =>
      Filter.Eventually.of_forall fun t => by
        calc
          ‖aux_standardBumpBaseDensity t * aux_standardBumpIntervalDensity r (x - t)‖ =
              ‖aux_standardBumpBaseDensity t‖ *
                ‖aux_standardBumpIntervalDensity r (x - t)‖ := norm_mul _ _
          _ ≤ ‖aux_standardBumpBaseDensity t‖ * 4 :=
            mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
          _ = 4 * aux_standardBumpBaseDensity t := by
            rw [Real.norm_of_nonneg (aux_standardBumpBaseDensity_nonneg t)]
            ring)
    (aux_standardBumpBaseDensity_integrable.const_mul 4) ?_
  have hneLeft : ∀ᵐ t : ℝ ∂volume, x0 - t ≠ -r := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬ x0 - t ≠ -r} = {x0 + r} := by
      ext t
      simp only [Set.mem_ofPred_eq, not_not, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hset, measure_singleton]
  have hneRight : ∀ᵐ t : ℝ ∂volume, x0 - t ≠ r := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬ x0 - t ≠ r} = {x0 - r} := by
      ext t
      simp only [Set.mem_ofPred_eq, not_not, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hset, measure_singleton]
  filter_upwards [hneLeft, hneRight] with t htLeft htRight
  have hsub : ContinuousAt (fun x : ℝ => x - t) x0 :=
    continuousAt_id.sub continuousAt_const
  have hinter : ContinuousAt (fun x : ℝ => aux_standardBumpIntervalDensity r (x - t)) x0 := by
    change ContinuousAt (aux_standardBumpIntervalDensity r ∘ fun x : ℝ => x - t) x0
    exact ContinuousAt.comp (f := fun x : ℝ => x - t) (x := x0)
      (aux_continuousAt_standardBumpIntervalDensity_offBoundary r (x0 - t) htLeft htRight) hsub
  exact (continuousAt_const : ContinuousAt (fun _ : ℝ => aux_standardBumpBaseDensity t) x0).mul
    hinter

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this propagates continuity through every later finite
convolution density. -/
theorem aux_continuous_standardBumpFiniteDensity_succ (n : ℕ) :
    Continuous (aux_standardBumpFiniteDensity (n + 1)) := by
  induction n with
  | zero => simpa using aux_continuous_standardBumpFiniteDensity_one
  | succ n ih =>
      change Continuous (aux_standardBumpFiniteDensity (n + 1) ⋆[
        ContinuousLinearMap.mul ℝ ℝ, volume]
          aux_standardBumpIntervalDensity (aux_standardBumpRadius (n + 1)))
      apply BddAbove.continuous_convolution_left_of_integrable
        (ContinuousLinearMap.mul ℝ ℝ)
      · refine ⟨1, ?_⟩
        rintro _ ⟨x, rfl⟩
        change ‖aux_standardBumpFiniteDensity (n + 1) x‖ ≤ 1
        rw [Real.norm_of_nonneg (aux_standardBumpFiniteDensity_nonneg (n + 1) x)]
        exact aux_standardBumpFiniteDensity_le_one (n + 1) x
      · exact ih
      · exact aux_standardBumpIntervalDensity_integrable _

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this records the symmetry of the initial interval
density. -/
theorem aux_standardBumpBaseDensity_even (x : ℝ) :
    aux_standardBumpBaseDensity (-x) = aux_standardBumpBaseDensity x := by
  have hmem : -x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4) ↔
      x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4) := by
    constructor <;> rintro ⟨hx1, hx2⟩ <;> constructor <;> linarith
  by_cases hx : x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4) <;>
    simp [aux_standardBumpBaseDensity, hx, hmem]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this records the symmetry of each normalized interval
density. -/
theorem aux_standardBumpIntervalDensity_even (r x : ℝ) :
    aux_standardBumpIntervalDensity r (-x) = aux_standardBumpIntervalDensity r x := by
  have hmem : -x ∈ Set.Icc (-r) r ↔ x ∈ Set.Icc (-r) r := by
    constructor <;> rintro ⟨hx1, hx2⟩ <;> constructor <;> linarith
  by_cases hx : x ∈ Set.Icc (-r) r <;>
    simp [aux_standardBumpIntervalDensity, hx, hmem]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this propagates evenness to every finite physical-side
density, allowing forward Fourier inversion to be used without reflection. -/
theorem aux_standardBumpFiniteDensity_even (n : ℕ) (x : ℝ) :
    aux_standardBumpFiniteDensity n (-x) = aux_standardBumpFiniteDensity n x := by
  induction n generalizing x with
  | zero => simpa [aux_standardBumpFiniteDensity] using aux_standardBumpBaseDensity_even x
  | succ n ih =>
      rw [aux_standardBumpFiniteDensity]
      exact MeasureTheory.convolution_neg_of_neg_eq (ContinuousLinearMap.mul ℝ ℝ)
        (Filter.Eventually.of_forall fun y => ih y)
        (Filter.Eventually.of_forall fun y =>
          aux_standardBumpIntervalDensity_even (aux_standardBumpRadius n) y)

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this supplies integrability of every nontrivial finite
standard bump for the Fourier inversion argument. -/
theorem aux_integrable_standardBumpFinite_succ (n : ℕ) :
    Integrable (standardBumpFinite (n + 1)) := by
  apply (integrable_inv_one_add_sq.const_mul 12).mono'
    (aux_continuous_standardBumpFinite _).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using aux_standardBumpFinite_succ_abs_le_majorant n x

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this uses Fourier inversion and evenness to identify the
forward Fourier transform of a nontrivial finite bump with its finite physical-side density. -/
theorem aux_fourier_standardBumpFinite_succ_eq_density (n : ℕ) (x : ℝ) :
    𝓕 (fun y : ℝ => (standardBumpFinite (n + 1) y : ℂ)) x =
      (aux_standardBumpFiniteDensity (n + 1) x : ℂ) := by
  let d : ℝ → ℂ := fun y => (aux_standardBumpFiniteDensity (n + 1) y : ℂ)
  let sb : ℝ → ℂ := fun y => (standardBumpFinite (n + 1) y : ℂ)
  have hdcont : Continuous d :=
    Complex.continuous_ofReal.comp (aux_continuous_standardBumpFiniteDensity_succ n)
  have hdint : Integrable d := by
    exact (aux_standardBumpFiniteDensity_integrable (n + 1)).ofReal
  have hsbint : Integrable sb := by
    exact (aux_integrable_standardBumpFinite_succ n).ofReal
  have hd : aux_standardBumpComplexFiniteDensity (n + 1) = d := by
    funext y
    exact aux_standardBumpComplexFiniteDensity_coe (n + 1) y
  have hF : 𝓕 d = sb := by
    rw [← hd]
    funext y
    exact aux_fourier_standardBumpComplexFiniteDensity_eq_standardBumpFinite (n + 1) y
  have hFdint : Integrable (𝓕 d) := by
    rw [hF]
    exact hsbint
  have hinv : 𝓕⁻ (𝓕 d) = d := hdcont.fourierInv_fourier_eq hdint hFdint
  have heven : ∀ y : ℝ, d (-y) = d y := fun y => by
    dsimp [d]
    rw [aux_standardBumpFiniteDensity_even]
  change 𝓕 sb x = d x
  calc
    𝓕 sb x = 𝓕 (𝓕 d) x := by rw [hF]
    _ = 𝓕⁻ (𝓕 d) (-x) := by
      simpa using (Real.fourierInv_eq_fourier_neg (𝓕 d) (-x)).symm
    _ = d (-x) := congrFun hinv (-x)
    _ = d x := heven x

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this supplies integrability of the limiting standard bump
from its already-proved two-sinc majorant. -/
theorem aux_integrable_standardBump : Integrable standardBump := by
  apply (integrable_inv_one_add_sq.const_mul 12).mono'
    aux_standardBump_aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using aux_standardBump_abs_le_majorant x

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this converts the established $L^1$ convergence into
convergence of the ordinary real integral of the absolute error. -/
theorem aux_standardBumpFinite_tendsto_integral_norm :
    Tendsto (fun n : ℕ => ∫ x : ℝ, |standardBumpFinite n x - standardBump x|)
      atTop (nhds 0) := by
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (standardBumpFinite n - standardBump) volume := fun n =>
    (aux_continuous_standardBumpFinite n).aestronglyMeasurable.sub
      aux_standardBump_aestronglyMeasurable
  have heq (n : ℕ) :
      (∫ x : ℝ, |standardBumpFinite n x - standardBump x|) =
        (eLpNorm (standardBumpFinite n - standardBump) 1 volume).toReal := by
    rw [show (fun x : ℝ => |standardBumpFinite n x - standardBump x|) =
      fun x : ℝ => ‖(standardBumpFinite n - standardBump) x‖ by
      funext x
      simp only [Pi.sub_apply, Real.norm_eq_abs]]
    rw [integral_norm_eq_lintegral_enorm (hmeas n), ← eLpNorm_one_eq_lintegral_enorm]
  have hlim := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp
    standardBumpProperties_l1Convergence
  apply hlim.congr'
  filter_upwards [] with n
  exact (heq n).symm

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this is the $L^1$ Lipschitz bound for the Fourier
transform at a fixed frequency. -/
theorem aux_norm_fourier_sub_le_integral (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) (xi : ℝ) :
    ‖𝓕 (fun x : ℝ => (f x : ℂ)) xi - 𝓕 (fun x : ℝ => (g x : ℂ)) xi‖ ≤
      ∫ x : ℝ, |f x - g x| := by
  have hphaseF : Integrable (fun v : ℝ => 𝐞 (-(v * xi)) • (f v : ℂ)) := by
    simpa only [Real.inner_apply] using
      (Real.fourierIntegral_convergent_iff xi).2 hf.ofReal
  have hphaseG : Integrable (fun v : ℝ => 𝐞 (-(v * xi)) • (g v : ℂ)) := by
    simpa only [Real.inner_apply] using
      (Real.fourierIntegral_convergent_iff xi).2 hg.ofReal
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_sub hphaseF hphaseG]
  calc
    ‖∫ v : ℝ, 𝐞 (-(v * xi)) • (f v : ℂ) - 𝐞 (-(v * xi)) • (g v : ℂ)‖ =
        ‖∫ v : ℝ, 𝐞 (-(v * xi)) • ((f v - g v : ℝ) : ℂ)‖ := by
      congr 2
      funext v
      simp only [smul_sub, Complex.ofReal_sub]
    _ ≤ ∫ v : ℝ, ‖𝐞 (-(v * xi)) • ((f v - g v : ℝ) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ v : ℝ, |f v - g v| := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [Circle.norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this passes the $L^1$ convergence of finite standard
bumps to pointwise convergence of their Fourier transforms. -/
theorem aux_fourier_standardBumpFinite_succ_tendsto (xi : ℝ) :
    Tendsto (fun n : ℕ => 𝓕 (fun x : ℝ => (standardBumpFinite (n + 1) x : ℂ)) xi)
      atTop (nhds (𝓕 (fun x : ℝ => (standardBump x : ℂ)) xi)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hshift := (Filter.tendsto_add_atTop_iff_nat 1).2
    aux_standardBumpFinite_tendsto_integral_norm
  rw [Metric.tendsto_atTop] at hshift
  rcases hshift eps heps with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact (aux_norm_fourier_sub_le_integral (standardBumpFinite (n + 1)) standardBump
    (aux_integrable_standardBumpFinite_succ n) aux_integrable_standardBump xi).trans_lt
      (by
        simpa only [Real.dist_eq, sub_zero,
          abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] using hN n hn)

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this identifies the pointwise Fourier limit of the finite
density sequence. -/
theorem aux_standardBumpFiniteDensity_tendsto_fourier_standardBump (xi : ℝ) :
    Tendsto (fun n : ℕ => (aux_standardBumpFiniteDensity (n + 1) xi : ℂ))
      atTop (nhds (𝓕 (fun x : ℝ => (standardBump x : ℂ)) xi)) := by
  simpa only [aux_fourier_standardBumpFinite_succ_eq_density] using
    aux_fourier_standardBumpFinite_succ_tendsto xi

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this transfers the finite density bounds to show that the
limiting Fourier transform is real-valued and lies in $[0,1]$. -/
theorem aux_fourier_standardBump_range (xi : ℝ) :
    ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧
      𝓕 (fun x : ℝ => (standardBump x : ℂ)) xi = r := by
  let h : ℂ := 𝓕 (fun x : ℝ => (standardBump x : ℂ)) xi
  have hdens := aux_standardBumpFiniteDensity_tendsto_fourier_standardBump xi
  change Tendsto (fun n : ℕ => (aux_standardBumpFiniteDensity (n + 1) xi : ℂ))
    atTop (nhds h) at hdens
  have hre : Tendsto (fun n : ℕ => aux_standardBumpFiniteDensity (n + 1) xi)
      atTop (nhds h.re) := by
    have h' := (Complex.continuous_re.tendsto h).comp hdens
    simpa only [Function.comp_def, Complex.ofReal_re] using h'
  have hupper : h.re ≤ 1 := le_of_tendsto' hre
    (fun n => aux_standardBumpFiniteDensity_le_one (n + 1) xi)
  have hneg : Tendsto (fun n : ℕ => -aux_standardBumpFiniteDensity (n + 1) xi)
      atTop (nhds (-h.re)) := hre.neg
  have hlower : 0 ≤ h.re := by
    have hle : -h.re ≤ 0 := le_of_tendsto' hneg
      (fun n => neg_nonpos.mpr (aux_standardBumpFiniteDensity_nonneg (n + 1) xi))
    linarith
  have him : Tendsto (fun n : ℕ => (aux_standardBumpFiniteDensity (n + 1) xi : ℂ).im)
      atTop (nhds h.im) := by
    exact (Complex.continuous_im.tendsto h).comp hdens
  have himzero : h.im = 0 := by
    have him' : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds h.im) := by
      simpa using him
    exact tendsto_nhds_unique him' tendsto_const_nhds
  refine ⟨h.re, ⟨hlower, hupper⟩, ?_⟩
  change h = (h.re : ℂ)
  apply Complex.ext <;> simp [himzero]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this transfers the finite support bounds to the limiting
Fourier transform. -/
theorem aux_fourier_standardBump_support :
    Function.support (𝓕 (fun x : ℝ => (standardBump x : ℂ))) ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro xi hxi
  by_contra hxiIcc
  have hdens := aux_standardBumpFiniteDensity_tendsto_fourier_standardBump xi
  have hzero (n : ℕ) : aux_standardBumpFiniteDensity (n + 1) xi = 0 := by
    apply Function.notMem_support.mp
    intro hmem
    apply hxiIcc
    have htail : 0 ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (n + 1) := by positivity
    have hmem' := aux_standardBumpFiniteDensity_support_stated (n + 1) hmem
    exact ⟨by linarith [hmem'.1], by linarith [hmem'.2]⟩
  have hzeroTend : Tendsto (fun n : ℕ => (aux_standardBumpFiniteDensity (n + 1) xi : ℂ))
      atTop (nhds 0) := by
    convert tendsto_const_nhds using 1
    funext n
    simp [hzero n]
  exact hxi (tendsto_nhds_unique hdens hzeroTend)

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierShape`, this transfers the finite plateau bounds to the limiting
Fourier transform. -/
theorem aux_fourier_standardBump_eq_one_on (xi : ℝ)
    (hxi : xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    𝓕 (fun x : ℝ => (standardBump x : ℂ)) xi = 1 := by
  have hdens := aux_standardBumpFiniteDensity_tendsto_fourier_standardBump xi
  have hone (n : ℕ) : aux_standardBumpFiniteDensity (n + 1) xi = 1 := by
    apply aux_standardBumpFiniteDensity_eq_one_on_stated (n + 1) xi
    have htail : 0 ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ (n + 1) := by positivity
    exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
  have honeTend : Tendsto (fun n : ℕ => (aux_standardBumpFiniteDensity (n + 1) xi : ℂ))
      atTop (nhds 1) := by
    convert tendsto_const_nhds using 1
    funext n
    simp [hone n]
  exact tendsto_nhds_unique hdens honeTend

/--
\begin{proposition}[standard bump]\label{standard bump properties}
whose Fourier transform takes values in $[0,1]$, is supported in $[-1,1]$, and constant $1$
on $[-1/2,1/2]$.
\end{proposition}
-/
theorem standardBumpProperties_fourierShape :
    (∀ xi : ℝ, ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧
      𝓕 (fun x : ℝ => (standardBump x : ℂ)) xi = r) ∧
    Function.support (𝓕 (fun x : ℝ => (standardBump x : ℂ))) ⊆ Set.Icc (-1 : ℝ) 1 ∧
    ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
      𝓕 (fun x : ℝ => (standardBump x : ℂ)) xi = 1 := by
  exact ⟨aux_fourier_standardBump_range,
    aux_fourier_standardBump_support,
    fun xi hxi => aux_fourier_standardBump_eq_one_on xi hxi⟩

/--
For $t>0$, the manuscript's rescaling of the standard bump is $\Phi_{(t)}(x)=t^{-1}\Phi(t^{-1}x)$.
-/
def standardBumpRescale (t : ℝ) : ℝ → ℝ := fun x =>
  t⁻¹ * standardBump (t⁻¹ * x)

/-- Source label `\ref{standard bump properties}`; the explicit Fourier-side constant used by
the public theorem `standardBumpProperties`. -/
def C_standardBumpPropertiesTilde (m N : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * m + 2 * N ^ 2 + 5 * N)

/-- Source label `\ref{standard bump properties}`; the explicit physical-side constant used by
the public theorem `standardBumpProperties`. -/
def C_standardBumpProperties (m N : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * m + 2 * N ^ 2 + 6 * N + 2)

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this computes the first derivative of the
real restriction of a complex monomial. -/
theorem aux_deriv_complexOfReal_pow (k : ℕ) (x : ℝ) :
    deriv (fun t : ℝ => (t : ℂ) ^ k) x =
      (k : ℂ) * (x : ℂ) ^ (k - 1) := by
  have h := (((hasDerivAt_id (x : ℂ)).pow k).comp_ofReal).deriv
  have hfun : (fun y : ℝ => (id ^ k : ℂ → ℂ) (y : ℂ)) =
      fun y : ℝ => (y : ℂ) ^ k := by
    funext y
    simp
  rw [hfun] at h
  simpa only [id_eq, mul_one] using h

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this evaluates all iterated derivatives of
the real restriction of a complex monomial, including the vanishing orders above its degree. -/
theorem aux_iteratedDeriv_complexOfReal_pow (m q : ℕ) (x : ℝ) :
    iteratedDeriv q (fun t : ℝ => (t : ℂ) ^ m) x =
      (m.descFactorial q : ℂ) * (x : ℂ) ^ (m - q) := by
  induction q generalizing x with
  | zero => simp
  | succ q ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv q (fun t : ℝ => (t : ℂ) ^ m) =
        fun t : ℝ => (m.descFactorial q : ℂ) * (t : ℂ) ^ (m - q) := by
      funext t
      exact ih t
    rw [hfun]
    have hd : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) ^ (m - q)) x :=
      (((hasDerivAt_id (x : ℂ)).pow (m - q)).comp_ofReal).differentiableAt
    rw [deriv_const_mul _ hd, aux_deriv_complexOfReal_pow,
      Nat.descFactorial_succ]
    by_cases hqm : q < m
    · have hsub : m - q - 1 = m - (q + 1) := by omega
      rw [hsub]
      have hcast : ((m - q : ℕ) : ℂ) = (m : ℂ) - (q : ℂ) := by
        rw [Nat.cast_sub (by omega : q ≤ m)]
      rw [hcast]
      push_cast
      rw [hcast]
      ring
    · have hmq : m ≤ q := by omega
      have hzero : m - q = 0 := Nat.sub_eq_zero_of_le hmq
      rw [hzero]
      simp

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the exact iterated-derivative
formula for the polynomial Fourier multiplier \((2\pi i\xi)^m\). -/
theorem aux_iteratedDeriv_standardBumpMultiplier (m q : ℕ) (x : ℝ) :
    iteratedDeriv q
      (fun t : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m) x =
      (2 * (Real.pi : ℂ) * Complex.I) ^ m *
        (m.descFactorial q : ℂ) * (x : ℂ) ^ (m - q) := by
  have hfactor : (fun t : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m) =
      fun t : ℝ => (2 * (Real.pi : ℂ) * Complex.I) ^ m * (t : ℂ) ^ m := by
    funext t
    rw [mul_pow]
  rw [hfactor]
  have hcont : ContDiffAt ℝ (q : ℕ∞) (fun t : ℝ => (t : ℂ) ^ m) x := by
    have h : ContDiff ℝ (q : ℕ∞) (fun t : ℝ => (Complex.ofRealCLM t) ^ m) :=
      (Complex.ofRealCLM.contDiff).pow m
    exact h.contDiffAt
  rw [iteratedDeriv_const_mul _ hcont]
  rw [aux_iteratedDeriv_complexOfReal_pow]
  ring

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this elementary bound turns polynomial
degree factors into powers of two. -/
theorem aux_nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    omega

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this bounds a factorial by the quadratic
power-of-two budget used in the Leibniz estimate. -/
theorem aux_factorial_le_two_pow_sq (n : ℕ) : n.factorial ≤ 2 ^ (n ^ 2) := by
  calc
    n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (aux_nat_le_two_pow n) n
    _ = 2 ^ (n ^ 2) := by rw [← Nat.pow_mul, pow_two]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this bounds the falling-factorial
coefficient in an iterated derivative of the Fourier multiplier. -/
theorem aux_descFactorial_le_two_pow (m q : ℕ) :
    m.descFactorial q ≤ 2 ^ (m + q ^ 2) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  calc
    q.factorial * m.choose q ≤ 2 ^ (q ^ 2) * 2 ^ m :=
      Nat.mul_le_mul (aux_factorial_le_two_pow_sq q) (Nat.choose_le_two_pow m q)
    _ = 2 ^ (m + q ^ 2) := by rw [← pow_add]; congr 1 <;> omega

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this bounds each derivative of
\((2\pi i\xi)^m\) on the Fourier support interval. -/
theorem aux_norm_iteratedDeriv_standardBumpMultiplier_le (m q : ℕ) (x : ℝ)
    (hx : |x| ≤ 1) :
    ‖iteratedDeriv q
      (fun t : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m) x‖ ≤
      (2 : ℝ) ^ (4 * m + q ^ 2) := by
  rw [aux_iteratedDeriv_standardBumpMultiplier, norm_mul, norm_mul, norm_pow]
  have hfac : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul]
    norm_num [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hfac, norm_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hpi : 2 * Real.pi ≤ (2 : ℝ) ^ 3 := by
    norm_num
    linarith [Real.pi_lt_four]
  have hdesc : (m.descFactorial q : ℝ) ≤ (2 : ℝ) ^ (m + q ^ 2) := by
    exact_mod_cast aux_descFactorial_le_two_pow m q
  have habs : |x| ^ (m - q) ≤ 1 := by
    exact pow_le_one₀ (abs_nonneg x) hx
  calc
    (2 * Real.pi) ^ m * ↑(m.descFactorial q) * |x| ^ (m - q) ≤
        ((2 : ℝ) ^ 3) ^ m * (2 : ℝ) ^ (m + q ^ 2) * 1 := by
          gcongr
    _ = (2 : ℝ) ^ (4 * m + q ^ 2) := by
      rw [← pow_mul, ← pow_add]
      ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
transfers absolute polynomial moments of a function to explicit pointwise bounds for the
corresponding derivatives of its Fourier transform. -/
theorem aux_norm_iteratedDeriv_fourier_le_moment (f : ℝ → ℂ) (n : ℕ)
    (hfmeas : AEStronglyMeasurable f volume)
    (hmom : ∀ j : ℕ, j ≤ n → Integrable (fun x : ℝ => |x| ^ j * ‖f x‖)) (xi : ℝ) :
    ‖iteratedDeriv n (FourierTransform.fourier f) xi‖ ≤
      (2 * Real.pi) ^ n * ∫ x : ℝ, |x| ^ n * ‖f x‖ := by
  have hvector : ∀ j : ℕ, (j : ℕ∞) ≤ (n : ℕ∞) →
      Integrable (fun x : ℝ => x ^ j • f x) := by
    intro j hj
    have hj' : j ≤ n := by exact_mod_cast hj
    apply Integrable.mono' (hmom j hj')
    · exact ((continuous_id.pow j).aestronglyMeasurable.smul hfmeas)
    · filter_upwards [] with x
      simp only [norm_smul, Real.norm_eq_abs, abs_pow]
      exact le_rfl
  rw [Real.iteratedDeriv_fourier (N := (n : ℕ∞)) hvector (by simp)]
  have hFourier (g : ℝ → ℂ) : FourierTransform.fourier g xi =
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) g xi := by
    rw [Real.fourier_eq]
    unfold VectorFourier.fourierIntegral
    apply integral_congr_ae
    filter_upwards [] with x
    rw [innerₗ_apply_apply, Real.inner_apply]
  calc
    ‖FourierTransform.fourier
        (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n • f x) xi‖
        = ‖VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
            (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n • f x) xi‖ := by
          rw [hFourier]
    _ ≤ ∫ x : ℝ, ‖(-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n • f x‖ := by
          exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
            (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n • f x) xi
    _ = (2 * Real.pi) ^ n * ∫ x : ℝ, |x| ^ n * ‖f x‖ := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      have hs : ‖(-2 : ℂ) * (Real.pi : ℂ) * Complex.I * (x : ℂ)‖ =
          2 * Real.pi * |x| := by
        rw [norm_mul, norm_mul, norm_mul]
        norm_num [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [norm_smul, norm_pow, hs, mul_pow]
      ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
converts the arbitrary sinc-product decay into an integrable majorant for each polynomial
moment of the standard bump. -/
theorem aux_standardBump_weighted_abs_le_majorant (N : ℕ) (x : ℝ) :
    |x| ^ N * |standardBump x| ≤
      (3 * (2 : ℝ) ^ ((N + 2) * (N + 2 - 1) / 2 + 2 * (N + 2))) *
        (1 + x ^ 2)⁻¹ := by
  let d : ℝ := (1 + |x|)⁻¹
  let A : ℝ := 3 * (2 : ℝ) ^ ((N + 2) * (N + 2 - 1) / 2 + 2 * (N + 2))
  have hdecay := aux_standardBump_abs_le_highMajorant (N + 2) x
  change |standardBump x| ≤ A * d ^ (N + 2 + 1) at hdecay
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hd : 0 ≤ d := by
    dsimp [d]
    positivity
  have hratio : |x| * d ≤ 1 := by
    dsimp [d]
    have hden : 0 < 1 + |x| := by positivity
    rw [show |x| * (1 + |x|)⁻¹ = |x| / (1 + |x|) by field_simp]
    exact (div_le_one₀ hden).2 (by linarith [abs_nonneg x])
  have hratioPow : |x| ^ N * d ^ N ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg (abs_nonneg x) hd) hratio
  have hthree : d ^ 3 ≤ (1 + x ^ 2)⁻¹ := by
    have hdle : d ≤ 1 := by
      dsimp [d]
      exact (inv_le_one₀ (by positivity)).2 (by linarith [abs_nonneg x])
    have hpow : d ^ 3 ≤ d ^ 2 := by
      rw [show 3 = Nat.succ 2 by norm_num, pow_succ]
      calc
        d ^ 2 * d ≤ d ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hdle (pow_nonneg hd 2)
        _ = d ^ 2 := by ring
    have hcompare : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    have hinv : ((1 + |x|) ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ :=
      (inv_le_inv₀ (sq_pos_of_pos (by positivity)) (by positivity)).2 hcompare
    calc
      d ^ 3 ≤ d ^ 2 := hpow
      _ = ((1 + |x|) ^ 2)⁻¹ := by
        dsimp [d]
        rw [inv_pow]
      _ ≤ (1 + x ^ 2)⁻¹ := hinv
  calc
    |x| ^ N * |standardBump x| ≤ |x| ^ N * (A * d ^ (N + 2 + 1)) :=
      mul_le_mul_of_nonneg_left hdecay (pow_nonneg (abs_nonneg x) N)
    _ = A * (|x| ^ N * d ^ N) * d ^ 3 := by
      have hpow : N + 2 + 1 = N + 3 := by omega
      rw [hpow, pow_add]
      ring
    _ ≤ A * 1 * d ^ 3 := by
      gcongr
    _ ≤ A * 1 * (1 + x ^ 2)⁻¹ := by
      gcongr
    _ = A * (1 + x ^ 2)⁻¹ := by ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
supplies every absolute polynomial moment needed to differentiate the Fourier transform of the
standard bump. -/
theorem aux_standardBump_weighted_norm_integrable (N : ℕ) :
    Integrable (fun x : ℝ => |x| ^ N * ‖(standardBump x : ℂ)‖) := by
  let A : ℝ := 3 * (2 : ℝ) ^ ((N + 2) * (N + 2 - 1) / 2 + 2 * (N + 2))
  have hcast : AEStronglyMeasurable (fun x : ℝ => (standardBump x : ℂ)) volume :=
    Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      aux_standardBump_aestronglyMeasurable
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul A)
  · exact ((continuous_abs.comp continuous_id).pow N).aestronglyMeasurable.mul hcast.norm
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact aux_standardBump_weighted_abs_le_majorant N x
    · exact mul_nonneg (pow_nonneg (abs_nonneg x) N) (norm_nonneg _)

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
uses the polynomial moment bounds to establish the qualitative smoothness of the Fourier-side
standard bump.  The separate finite-density argument supplies the manuscript's sharp constants. -/
theorem aux_standardBumpComplex_fourier_contDiff :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))) := by
  apply Real.contDiff_fourier (N := ⊤)
  intro n _
  simpa only [Real.norm_eq_abs] using aux_standardBump_weighted_norm_integrable n

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this uses the high-product decay with exactly
two residual powers to obtain the quantitative polynomial-moment majorant needed at orders
greater than two. -/
theorem aux_standardBump_weighted_abs_le_highMomentMajorant (N : ℕ) (x : ℝ) :
    |x| ^ N * |standardBump x| ≤
      (3 * (2 : ℝ) ^ (N * (N + 1) / 2 + 2 * (N + 1))) *
        (1 + x ^ 2)⁻¹ := by
  let d : ℝ := (1 + |x|)⁻¹
  let A : ℝ := 3 * (2 : ℝ) ^ (N * (N + 1) / 2 + 2 * (N + 1))
  have hdecay := aux_standardBump_abs_le_highMajorant (N + 1) x
  have hcoeff : 3 * (2 : ℝ) ^ ((N + 1) * (N + 1 - 1) / 2 + 2 * (N + 1)) = A := by
    dsimp [A]
    congr 2
    simp [Nat.mul_comm]
  rw [hcoeff] at hdecay
  change |standardBump x| ≤ A * d ^ (N + 1 + 1) at hdecay
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hd : 0 ≤ d := by
    dsimp [d]
    positivity
  have hratio : |x| * d ≤ 1 := by
    dsimp [d]
    have hden : 0 < 1 + |x| := by positivity
    rw [show |x| * (1 + |x|)⁻¹ = |x| / (1 + |x|) by field_simp]
    exact (div_le_one₀ hden).2 (by linarith [abs_nonneg x])
  have hratioPow : |x| ^ N * d ^ N ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg (abs_nonneg x) hd) hratio
  have htwo : d ^ 2 ≤ (1 + x ^ 2)⁻¹ := by
    have hcompare : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    have hinv : ((1 + |x|) ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ :=
      (inv_le_inv₀ (sq_pos_of_pos (by positivity)) (by positivity)).2 hcompare
    calc
      d ^ 2 = ((1 + |x|) ^ 2)⁻¹ := by
        dsimp [d]
        rw [inv_pow]
      _ ≤ (1 + x ^ 2)⁻¹ := hinv
  calc
    |x| ^ N * |standardBump x| ≤ |x| ^ N * (A * d ^ (N + 1 + 1)) :=
      mul_le_mul_of_nonneg_left hdecay (pow_nonneg (abs_nonneg x) N)
    _ = A * (|x| ^ N * d ^ N) * d ^ 2 := by
      have hpow : N + 1 + 1 = N + 2 := by omega
      rw [hpow, pow_add]
      ring
    _ ≤ A * 1 * d ^ 2 := by
      gcongr
    _ ≤ A * 1 * (1 + x ^ 2)⁻¹ := by
      gcongr
    _ = A * (1 + x ^ 2)⁻¹ := by ring

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this integrates the sharp high-order
polynomial-moment majorant for the standard bump. -/
theorem aux_standardBump_weighted_norm_integral_le_highMomentMajorant (N : ℕ) :
    ∫ x : ℝ, |x| ^ N * ‖(standardBump x : ℂ)‖ ≤
      (3 * (2 : ℝ) ^ (N * (N + 1) / 2 + 2 * (N + 1))) * Real.pi := by
  let A : ℝ := 3 * (2 : ℝ) ^ (N * (N + 1) / 2 + 2 * (N + 1))
  have hweight : Integrable (fun x : ℝ => |x| ^ N * ‖(standardBump x : ℂ)‖) :=
    aux_standardBump_weighted_norm_integrable N
  have hmajorant : Integrable (fun x : ℝ => A * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul A
  calc
    ∫ x : ℝ, |x| ^ N * ‖(standardBump x : ℂ)‖ ≤
        ∫ x : ℝ, A * (1 + x ^ 2)⁻¹ := by
          apply integral_mono hweight hmajorant
          intro x
          change |x| ^ N * ‖(standardBump x : ℂ)‖ ≤ A * (1 + x ^ 2)⁻¹
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact aux_standardBump_weighted_abs_le_highMomentMajorant N x
    _ = A * Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the quantitative high-order
derivative profile of the Fourier transform of the standard bump.  Lower orders are improved by
separate auxiliaries before the final Leibniz estimate. -/
theorem aux_standardBump_fourier_iteratedDeriv_le_highProfile (N : ℕ) (xi : ℝ) :
    ‖iteratedDeriv N
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))) xi‖ ≤
      (2 : ℝ) ^ (N * (N + 1) / 2 + 5 * N + 6) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (standardBump x : ℂ)) volume :=
    Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      aux_standardBump_aestronglyMeasurable
  have hmoment : ∀ j : ℕ, j ≤ N →
      Integrable (fun x : ℝ => |x| ^ j * ‖(standardBump x : ℂ)‖) := by
    intro j _
    exact aux_standardBump_weighted_norm_integrable j
  let A : ℝ := 3 * (2 : ℝ) ^ (N * (N + 1) / 2 + 2 * (N + 1))
  have hint := aux_standardBump_weighted_norm_integral_le_highMomentMajorant N
  change ∫ x : ℝ, |x| ^ N * ‖(standardBump x : ℂ)‖ ≤ A * Real.pi at hint
  have hpi : 2 * Real.pi ≤ (2 : ℝ) ^ 3 := by
    norm_num
    linarith [Real.pi_lt_four]
  have hpi' : Real.pi ≤ (2 : ℝ) ^ 2 := by
    norm_num
    linarith [Real.pi_lt_four]
  have hthree : (3 : ℝ) ≤ (2 : ℝ) ^ 2 := by norm_num
  calc
    ‖iteratedDeriv N
        (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))) xi‖ ≤
        (2 * Real.pi) ^ N * ∫ x : ℝ, |x| ^ N * ‖(standardBump x : ℂ)‖ :=
      aux_norm_iteratedDeriv_fourier_le_moment _ N hmeas hmoment xi
    _ ≤ ((2 : ℝ) ^ 3) ^ N * (A * Real.pi) := by gcongr
    _ ≤ ((2 : ℝ) ^ 3) ^ N *
        ((2 : ℝ) ^ 2 * (2 : ℝ) ^ (N * (N + 1) / 2 + 2 * (N + 1)) *
          (2 : ℝ) ^ 2) := by
      dsimp [A]
      gcongr
    _ = (2 : ℝ) ^ (N * (N + 1) / 2 + 5 * N + 6) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
converts each short sinc factor into its sharp inverse-absolute-value bound away from zero. -/
theorem aux_standardBump_sinc_factor_abs_le_inverse (i : ℕ) (x : ℝ) (hx : x ≠ 0) :
    |Real.sinc ((Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i)| ≤
      (2 : ℝ) ^ (i + 2) * (Real.pi * |x|)⁻¹ := by
  let a : ℝ := (Real.pi / 4) * ((2 : ℝ)⁻¹) ^ i
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have harg : (Real.pi / 4) * x * ((2 : ℝ)⁻¹) ^ i = a * x := by
    dsimp [a]
    ring
  rw [harg]
  calc
    |Real.sinc (a * x)| ≤ |a * x|⁻¹ :=
      aux_abs_sinc_le_inv_abs (mul_ne_zero (ne_of_gt ha) hx)
    _ = (a * |x|)⁻¹ := by rw [abs_mul, abs_of_pos ha]
    _ = (2 : ℝ) ^ (i + 2) * (Real.pi * |x|)⁻¹ := by
      dsimp [a]
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, pow_add]
      have hpow : (1 / 2 : ℝ) ^ i * 2 ^ i = 1 := by
        rw [← mul_pow]
        norm_num
      field_simp
      nlinarith

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is the inverse-absolute-value bound for the initial long sinc factor. -/
theorem aux_standardBump_base_abs_le_inverse (x : ℝ) (hx : x ≠ 0) :
    |aux_intervalIndicatorFourier (3 / 4) x| ≤ (Real.pi * |x|)⁻¹ := by
  rw [aux_intervalIndicatorFourier, if_neg hx, abs_div]
  calc
    |Real.sin (2 * Real.pi * (3 / 4) * x)| / |Real.pi * x| ≤
        1 / |Real.pi * x| := by
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
    _ = (Real.pi * |x|)⁻¹ := by
      rw [abs_mul, abs_of_pos Real.pi_pos, one_div]

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
passes the three-factor inverse decay estimate from finite products to the standard bump. -/
theorem aux_standardBump_abs_le_threeInverse (x : ℝ) (hx : x ≠ 0) :
    |standardBump x| ≤ 32 * (Real.pi * |x|)⁻¹ ^ 3 := by
  have hfinite (l : ℕ) :
      |standardBumpFinite (2 + l) x| ≤ 32 * (Real.pi * |x|)⁻¹ ^ 3 := by
    rw [aux_standardBumpFinite_eq_sincProduct, Finset.prod_range_add]
    rw [abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    let q : ℝ := (Real.pi * |x|)⁻¹
    have hq : 0 ≤ q := by
      dsimp [q]
      positivity
    have hbase : |aux_intervalIndicatorFourier (3 / 4) x| ≤ q := by
      simpa only [q] using aux_standardBump_base_abs_le_inverse x hx
    have hzero : |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ 0)| ≤ 4 * q := by
      have h := aux_standardBump_sinc_factor_abs_le_inverse 0 x hx
      norm_num [q] at h ⊢
      exact h
    have hone : |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ 1)| ≤ 8 * q := by
      have h := aux_standardBump_sinc_factor_abs_le_inverse 1 x hx
      norm_num [q] at h ⊢
      exact h
    have htail : ∏ i ∈ Finset.range l,
        |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ (2 + i))| ≤ 1 :=
      aux_standardBump_sinc_shifted_tail_abs_le_one 2 l x
    calc
      |aux_intervalIndicatorFourier (3 / 4) x| *
          (1 * |Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ 0)| *
            |Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ 1)| *
            ∏ x_1 ∈ Finset.range l, |Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ (2 + x_1))|) ≤
          q * (1 * (4 * q) * (8 * q) * 1) := by
        gcongr
      _ = 32 * (Real.pi * |x|)⁻¹ ^ 3 := by
        dsimp [q]
        ring
  have hlim := (Filter.tendsto_add_atTop_iff_nat 2).2
    (aux_standardBumpFinite_tendsto x)
  have habs : Tendsto (fun l : ℕ => |standardBumpFinite (2 + l) x|)
      atTop (nhds |standardBump x|) := by
    simpa only [Real.norm_eq_abs, add_comm] using hlim.norm
  exact le_of_tendsto' habs hfinite

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
passes the four-factor inverse decay estimate from finite products to the standard bump. -/
theorem aux_standardBump_abs_le_fourInverse (x : ℝ) (hx : x ≠ 0) :
    |standardBump x| ≤ 512 * (Real.pi * |x|)⁻¹ ^ 4 := by
  have hfinite (l : ℕ) :
      |standardBumpFinite (3 + l) x| ≤ 512 * (Real.pi * |x|)⁻¹ ^ 4 := by
    rw [aux_standardBumpFinite_eq_sincProduct, Finset.prod_range_add]
    rw [abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    let q : ℝ := (Real.pi * |x|)⁻¹
    have hq : 0 ≤ q := by
      dsimp [q]
      positivity
    have hbase : |aux_intervalIndicatorFourier (3 / 4) x| ≤ q := by
      simpa only [q] using aux_standardBump_base_abs_le_inverse x hx
    have hzero : |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ 0)| ≤ 4 * q := by
      have h := aux_standardBump_sinc_factor_abs_le_inverse 0 x hx
      norm_num [q] at h ⊢
      exact h
    have hone : |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ 1)| ≤ 8 * q := by
      have h := aux_standardBump_sinc_factor_abs_le_inverse 1 x hx
      norm_num [q] at h ⊢
      exact h
    have htwo : |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ 2)| ≤ 16 * q := by
      have h := aux_standardBump_sinc_factor_abs_le_inverse 2 x hx
      norm_num [q] at h ⊢
      exact h
    have htail : ∏ i ∈ Finset.range l,
        |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ (3 + i))| ≤ 1 :=
      aux_standardBump_sinc_shifted_tail_abs_le_one 3 l x
    calc
      |aux_intervalIndicatorFourier (3 / 4) x| *
          (1 * |Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ 0)| *
            |Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ 1)| *
            |Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ 2)| *
            ∏ x_1 ∈ Finset.range l, |Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ (3 + x_1))|) ≤
          q * (1 * (4 * q) * (8 * q) * (16 * q) * 1) := by
        gcongr
      _ = 512 * (Real.pi * |x|)⁻¹ ^ 4 := by
        dsimp [q]
        ring
  have hlim := (Filter.tendsto_add_atTop_iff_nat 3).2
    (aux_standardBumpFinite_tendsto x)
  have habs : Tendsto (fun l : ℕ => |standardBumpFinite (3 + l) x|)
      atTop (nhds |standardBump x|) := by
    simpa only [Real.norm_eq_abs, add_comm] using hlim.norm
  exact le_of_tendsto' habs hfinite

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
gives the bounded branch of the low-order sinc estimates. -/
theorem aux_standardBump_abs_le_threeHalves (x : ℝ) :
    |standardBump x| ≤ 3 / 2 := by
  have hfinite (l : ℕ) : |standardBumpFinite l x| ≤ 3 / 2 := by
    rw [aux_standardBumpFinite_eq_sincProduct, abs_mul, Finset.abs_prod]
    have hbase : |aux_intervalIndicatorFourier (3 / 4) x| ≤ 3 / 2 := by
      rw [aux_intervalIndicatorFourier_eq_two_mul_sinc]
      calc
        |2 * (3 / 4) * Real.sinc (2 * Real.pi * (3 / 4) * x)| =
            (3 / 2) * |Real.sinc (2 * Real.pi * (3 / 4) * x)| := by
          rw [abs_mul, abs_mul]
          norm_num
        _ ≤ (3 / 2) * 1 := by
          gcongr
          exact Real.abs_sinc_le_one _
        _ = 3 / 2 := by ring
    have hprod : ∏ i ∈ Finset.range l,
        |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ i)| ≤ 1 := by
      apply Finset.prod_le_one
      · intro i hi
        exact abs_nonneg _
      · intro i hi
        exact Real.abs_sinc_le_one _
    have hprodNonneg : 0 ≤ ∏ i ∈ Finset.range l,
        |Real.sinc (Real.pi / 4 * x * (2 : ℝ)⁻¹ ^ i)| := by
      apply Finset.prod_nonneg
      intro i hi
      exact abs_nonneg _
    calc
      |aux_intervalIndicatorFourier (3 / 4) x| *
          ∏ i ∈ Finset.range l, |Real.sinc (Real.pi / 4 * x * 2⁻¹ ^ i)| ≤
          (3 / 2) * 1 := mul_le_mul hbase hprod hprodNonneg (by norm_num)
      _ = 3 / 2 := by ring
  have habs : Tendsto (fun l : ℕ => |standardBumpFinite l x|)
      atTop (nhds |standardBump x|) := by
    simpa only [Real.norm_eq_abs] using (aux_standardBumpFinite_tendsto x).norm
  exact le_of_tendsto' habs hfinite

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
combines the bounded and three-factor branches into the first sharp weighted estimate. -/
theorem aux_standardBump_weighted_abs_one (x : ℝ) :
    |x| * |standardBump x| ≤ 4 * (1 + x ^ 2)⁻¹ := by
  by_cases hx : |x| ≤ 1
  · have hbound := aux_standardBump_abs_le_threeHalves x
    have hweight : |x| * |standardBump x| ≤ 3 / 2 := by
      calc
        |x| * |standardBump x| ≤ 1 * (3 / 2) :=
          mul_le_mul hx hbound (abs_nonneg _) (by norm_num)
        _ = 3 / 2 := by ring
    have hxSq : x ^ 2 ≤ 1 := by
      have h := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)).mpr hx
      simpa only [sq_abs, one_pow] using h
    have hden : 0 < 1 + x ^ 2 := by positivity
    rw [show 4 * (1 + x ^ 2)⁻¹ = 4 / (1 + x ^ 2) by rw [div_eq_mul_inv]]
    apply (le_div_iff₀ hden).2
    calc
      (|x| * |standardBump x|) * (1 + x ^ 2) ≤ (3 / 2) * 2 := by
        gcongr
        nlinarith
      _ ≤ 4 := by norm_num
  · have hx' : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hx'
    have hxne : x ≠ 0 := abs_ne_zero.mp (ne_of_gt hxpos)
    have hraw := aux_standardBump_abs_le_threeInverse x hxne
    have hpi3 : 27 < Real.pi ^ 3 := by
      have hfactor : 0 < (Real.pi - 3) * (Real.pi ^ 2 + 3 * Real.pi + 9) := by
        apply mul_pos
        · linarith [Real.pi_gt_three]
        · positivity
      nlinarith
    have hxSq : 1 ≤ x ^ 2 := by
      rw [← sq_abs]
      exact one_le_pow₀ hx'
    have hden : 0 < 1 + x ^ 2 := by positivity
    have hpoly : 32 * (1 + x ^ 2) ≤ x ^ 2 * (Real.pi ^ 3 * 4) := by
      calc
        32 * (1 + x ^ 2) ≤ 32 * (2 * x ^ 2) := by
          gcongr
          nlinarith
        _ = 64 * x ^ 2 := by ring
        _ ≤ (4 * Real.pi ^ 3) * x ^ 2 := by
          gcongr
          nlinarith [hpi3]
        _ = x ^ 2 * (Real.pi ^ 3 * 4) := by ring
    have hcompare : |x| * (32 * (Real.pi * |x|)⁻¹ ^ 3) ≤ 4 / (1 + x ^ 2) := by
      apply (le_div_iff₀ hden).2
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hxpos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hpoly
    calc
      |x| * |standardBump x| ≤ |x| * (32 * (Real.pi * |x|)⁻¹ ^ 3) :=
        mul_le_mul_of_nonneg_left hraw (abs_nonneg _)
      _ ≤ 4 / (1 + x ^ 2) := hcompare
      _ = 4 * (1 + x ^ 2)⁻¹ := by rw [div_eq_mul_inv]

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
combines the bounded and four-factor branches into the second sharp weighted estimate. -/
theorem aux_standardBump_weighted_abs_two (x : ℝ) :
    |x| ^ 2 * |standardBump x| ≤ 16 * (1 + x ^ 2)⁻¹ := by
  by_cases hx : |x| ≤ 1
  · have hbound := aux_standardBump_abs_le_threeHalves x
    have hxPow : |x| ^ 2 ≤ 1 := by
      exact pow_le_one₀ (abs_nonneg x) hx
    have hweight : |x| ^ 2 * |standardBump x| ≤ 3 / 2 := by
      calc
        |x| ^ 2 * |standardBump x| ≤ 1 * (3 / 2) :=
          mul_le_mul hxPow hbound (abs_nonneg _) (by norm_num)
        _ = 3 / 2 := by ring
    have hxSq : x ^ 2 ≤ 1 := by
      have h := (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)).mpr hx
      simpa only [sq_abs, one_pow] using h
    have hden : 0 < 1 + x ^ 2 := by positivity
    rw [show 16 * (1 + x ^ 2)⁻¹ = 16 / (1 + x ^ 2) by rw [div_eq_mul_inv]]
    apply (le_div_iff₀ hden).2
    calc
      (|x| ^ 2 * |standardBump x|) * (1 + x ^ 2) ≤ (3 / 2) * 2 := by
        gcongr
        nlinarith
      _ ≤ 16 := by norm_num
  · have hx' : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hx'
    have hxne : x ≠ 0 := abs_ne_zero.mp (ne_of_gt hxpos)
    have hraw := aux_standardBump_abs_le_fourInverse x hxne
    have hpi4 : 64 < Real.pi ^ 4 := by
      have hfactor : 0 < (Real.pi - 3) *
          (Real.pi ^ 3 + 3 * Real.pi ^ 2 + 9 * Real.pi + 27) := by
        apply mul_pos
        · linarith [Real.pi_gt_three]
        · positivity
      nlinarith
    have hxSq : 1 ≤ x ^ 2 := by
      rw [← sq_abs]
      exact one_le_pow₀ hx'
    have hden : 0 < 1 + x ^ 2 := by positivity
    have hpoly : 512 * (1 + x ^ 2) ≤ x ^ 2 * (Real.pi ^ 4 * 16) := by
      calc
        512 * (1 + x ^ 2) ≤ 512 * (2 * x ^ 2) := by
          gcongr
          nlinarith
        _ = 1024 * x ^ 2 := by ring
        _ ≤ (16 * Real.pi ^ 4) * x ^ 2 := by
          gcongr
          nlinarith [hpi4]
        _ = x ^ 2 * (Real.pi ^ 4 * 16) := by ring
    have hcompare : |x| ^ 2 * (512 * (Real.pi * |x|)⁻¹ ^ 4) ≤
        16 / (1 + x ^ 2) := by
      apply (le_div_iff₀ hden).2
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hxpos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hpoly
    calc
      |x| ^ 2 * |standardBump x| ≤ |x| ^ 2 *
          (512 * (Real.pi * |x|)⁻¹ ^ 4) :=
        mul_le_mul_of_nonneg_left hraw (pow_nonneg (abs_nonneg _) _)
      _ ≤ 16 / (1 + x ^ 2) := hcompare
      _ = 16 * (1 + x ^ 2)⁻¹ := by rw [div_eq_mul_inv]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this integrates the first sharp weighted
estimate used for the low Fourier derivative order. -/
theorem aux_standardBump_weighted_norm_integral_one_le :
    ∫ x : ℝ, |x| * ‖(standardBump x : ℂ)‖ ≤ 16 := by
  have hleft : Integrable (fun x : ℝ => |x| * ‖(standardBump x : ℂ)‖) :=
    by simpa only [pow_one] using aux_standardBump_weighted_norm_integrable 1
  have hright : Integrable (fun x : ℝ => 4 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 4
  calc
    ∫ x : ℝ, |x| * ‖(standardBump x : ℂ)‖ ≤
        ∫ x : ℝ, 4 * (1 + x ^ 2)⁻¹ :=
      integral_mono hleft hright (fun x => by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using aux_standardBump_weighted_abs_one x)
    _ = 4 * Real.pi := by
      rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
    _ ≤ 16 := by nlinarith [Real.pi_le_four]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this integrates the second sharp weighted
estimate used for the low Fourier derivative order. -/
theorem aux_standardBump_weighted_norm_integral_two_le :
    ∫ x : ℝ, |x| ^ 2 * ‖(standardBump x : ℂ)‖ ≤ 64 := by
  have hleft : Integrable (fun x : ℝ => |x| ^ 2 * ‖(standardBump x : ℂ)‖) :=
    aux_standardBump_weighted_norm_integrable 2
  have hright : Integrable (fun x : ℝ => 16 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 16
  calc
    ∫ x : ℝ, |x| ^ 2 * ‖(standardBump x : ℂ)‖ ≤
        ∫ x : ℝ, 16 * (1 + x ^ 2)⁻¹ :=
      integral_mono hleft hright (fun x => by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using aux_standardBump_weighted_abs_two x)
    _ = 16 * Real.pi := by
      rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
    _ ≤ 64 := by nlinarith [Real.pi_le_four]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the order-zero sharp Fourier
profile estimate. -/
theorem aux_standardBump_fourier_iteratedDeriv_le_zero (xi : ℝ) :
    ‖iteratedDeriv 0 (FourierTransform.fourier
      (fun x : ℝ => (standardBump x : ℂ))) xi‖ ≤ (2 : ℝ) ^ 0 := by
  obtain ⟨r, hr, hfourier⟩ := (standardBumpProperties_fourierShape).1 xi
  rw [iteratedDeriv_zero, hfourier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr.1]
  norm_num
  exact hr.2

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the order-one sharp Fourier
profile estimate. -/
theorem aux_standardBump_fourier_iteratedDeriv_le_one (xi : ℝ) :
    ‖iteratedDeriv 1 (FourierTransform.fourier
      (fun x : ℝ => (standardBump x : ℂ))) xi‖ ≤ (2 : ℝ) ^ 7 := by
  let f : ℝ → ℂ := fun x => (standardBump x : ℂ)
  have hfmeas : AEStronglyMeasurable f volume := by
    exact Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      aux_standardBump_aestronglyMeasurable
  have hmom : ∀ j : ℕ, j ≤ 1 → Integrable (fun x : ℝ => |x| ^ j * ‖f x‖) := by
    intro j hj
    interval_cases j
    · simpa only [f, pow_zero, one_mul] using aux_standardBump_weighted_norm_integrable 0
    · simpa only [f, pow_one] using aux_standardBump_weighted_norm_integrable 1
  have hderiv := aux_norm_iteratedDeriv_fourier_le_moment f 1 hfmeas hmom xi
  have hscale : (2 * Real.pi) ^ 1 ≤ 8 := by
    norm_num
    nlinarith [Real.pi_le_four]
  have hmoment : ∫ x : ℝ, |x| ^ 1 * ‖f x‖ ≤ 16 := by
    simpa only [f, pow_one] using aux_standardBump_weighted_norm_integral_one_le
  have hmomentNonneg : 0 ≤ ∫ x : ℝ, |x| ^ 1 * ‖f x‖ :=
    integral_nonneg fun x => mul_nonneg (pow_nonneg (abs_nonneg x) _) (norm_nonneg _)
  calc
    ‖iteratedDeriv 1 (FourierTransform.fourier
        (fun x : ℝ => (standardBump x : ℂ))) xi‖ =
        ‖iteratedDeriv 1 (FourierTransform.fourier f) xi‖ := by rfl
    _ ≤ (2 * Real.pi) ^ 1 * ∫ x : ℝ, |x| ^ 1 * ‖f x‖ := hderiv
    _ ≤ 8 * 16 := mul_le_mul hscale hmoment hmomentNonneg (by norm_num)
    _ = (2 : ℝ) ^ 7 := by norm_num

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the order-two sharp Fourier
profile estimate. -/
theorem aux_standardBump_fourier_iteratedDeriv_le_two (xi : ℝ) :
    ‖iteratedDeriv 2 (FourierTransform.fourier
      (fun x : ℝ => (standardBump x : ℂ))) xi‖ ≤ (2 : ℝ) ^ 18 := by
  let f : ℝ → ℂ := fun x => (standardBump x : ℂ)
  have hfmeas : AEStronglyMeasurable f volume := by
    exact Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      aux_standardBump_aestronglyMeasurable
  have hmom : ∀ j : ℕ, j ≤ 2 → Integrable (fun x : ℝ => |x| ^ j * ‖f x‖) := by
    intro j hj
    interval_cases j
    · simpa only [f, pow_zero, one_mul] using aux_standardBump_weighted_norm_integrable 0
    · simpa only [f, pow_one] using aux_standardBump_weighted_norm_integrable 1
    · simpa only [f] using aux_standardBump_weighted_norm_integrable 2
  have hderiv := aux_norm_iteratedDeriv_fourier_le_moment f 2 hfmeas hmom xi
  have hscale0 : 2 * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
  have hscale : (2 * Real.pi) ^ 2 ≤ 64 := by
    have hsquare := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (by norm_num : (0 : ℝ) ≤ 8)).mpr hscale0
    norm_num at hsquare ⊢
    exact hsquare
  have hmoment : ∫ x : ℝ, |x| ^ 2 * ‖f x‖ ≤ 64 := by
    simpa only [f] using aux_standardBump_weighted_norm_integral_two_le
  have hmomentNonneg : 0 ≤ ∫ x : ℝ, |x| ^ 2 * ‖f x‖ :=
    integral_nonneg fun x => mul_nonneg (pow_nonneg (abs_nonneg x) _) (norm_nonneg _)
  calc
    ‖iteratedDeriv 2 (FourierTransform.fourier
        (fun x : ℝ => (standardBump x : ℂ))) xi‖ =
        ‖iteratedDeriv 2 (FourierTransform.fourier f) xi‖ := by rfl
    _ ≤ (2 * Real.pi) ^ 2 * ∫ x : ℝ, |x| ^ 2 * ‖f x‖ := hderiv
    _ ≤ 64 * 64 := mul_le_mul hscale hmoment hmomentNonneg (by norm_num)
    _ ≤ (2 : ℝ) ^ 18 := by norm_num

/--
\begin{proposition}[standard bump]\label{standard bump properties}
The limit $\lim_{l\to \infty} \Phi_l$ is a Schwartz function $\Phi$.
\end{proposition}
-/
theorem standardBumpProperties_schwartz :
    ∃ Phi : SchwartzMap ℝ ℂ, ∀ x : ℝ, Phi x = (standardBump x : ℂ) := by
  let f : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))
  obtain ⟨_, hsupport, _⟩ := standardBumpProperties_fourierShape
  have htsupport : tsupport f ⊆ Set.Icc (-1 : ℝ) 1 := by
    change tsupport (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))) ⊆
      Set.Icc (-1 : ℝ) 1
    exact closure_minimal hsupport isClosed_Icc
  have hcompact : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure htsupport
  have hcontDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) f := by
    simpa only [f] using aux_standardBumpComplex_fourier_contDiff
  let H : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hcontDiff
  let Phi : SchwartzMap ℝ ℂ := FourierTransformInv.fourierInv H
  refine ⟨Phi, ?_⟩
  have hcont : Continuous (fun x : ℝ => (standardBump x : ℂ)) := by
    exact Complex.continuous_ofReal.comp
      (aux_standardBumpFinite_tendstoUniformly.continuous
        (Filter.Frequently.of_forall fun n => aux_continuous_standardBumpFinite n))
  have hint : Integrable (fun x : ℝ => (standardBump x : ℂ)) :=
    aux_integrable_standardBump.ofReal
  have hFint : Integrable f :=
    hcontDiff.continuous.integrable_of_hasCompactSupport hcompact
  have hinv : FourierTransformInv.fourierInv f = fun x : ℝ => (standardBump x : ℂ) :=
    hcont.fourierInv_fourier_eq hint hFint
  intro x
  change (FourierTransformInv.fourierInv H) x = (standardBump x : ℂ)
  rw [SchwartzMap.fourierInv_coe]
  change FourierTransformInv.fourierInv f x = (standardBump x : ℂ)
  exact congrFun hinv x

/--
\begin{lemma}
    \label{lem: min and bracket} Let $N\ge 1$ be an integer, then
\begin{equation}\label{auto:min-power-bracket-bound}\min(1, |x|^{-N})\le 2^N   \langle x\rangle^{N}\, .\end{equation}
\end{lemma}
-/
theorem min_and_bracket (N : ℕ) (_hN : 1 ≤ N) (x : ℝ) :
    min 1 (|x|⁻¹ ^ N) ≤ (2 : ℝ) ^ N * (bracketBump x) ^ N := by
  rw [bracketBump]
  have hden : 0 < 1 + |x| := by positivity
  rw [show (2 : ℝ) ^ N * (1 + |x|)⁻¹ ^ N = (2 / (1 + |x|)) ^ N by
    rw [div_eq_mul_inv, mul_pow]]
  by_cases hx : |x| ≤ 1
  · have hbase : 1 ≤ 2 / (1 + |x|) := by
      apply (le_div_iff₀ hden).2
      linarith
    calc
      min 1 (|x|⁻¹ ^ N) ≤ 1 := min_le_left _ _
      _ ≤ (2 / (1 + |x|)) ^ N := one_le_pow₀ hbase
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hx'
    have hbase : |x|⁻¹ ≤ 2 / (1 + |x|) := by
      field_simp [ne_of_gt hxpos, ne_of_gt hden]
      nlinarith
    calc
      min 1 (|x|⁻¹ ^ N) ≤ |x|⁻¹ ^ N := min_le_right _ _
      _ ≤ (2 / (1 + |x|)) ^ N := by gcongr

/-- Source label `\ref{lem:smoothdecay2}`; the explicit constant used by the public theorem
`smoothDecay2`. -/
def C_smoothDecay2 (N : ℕ) : ℝ := (2 : ℝ) ^ N

/-- For \ref{lem:smoothdecay2}, this bounds the integral of a bounded function by the
measure of any finite-measure set containing its support.  It is used in
`smoothDecay2` to pass from the $L^1$ estimates of `smoothDecay` to the stated
supremum estimates. -/
theorem aux_integralNorm_le_bound_mul_measure_of_support_subset
    {f : ℝ → ℂ} {s : Set ℝ} (hs : Function.support f ⊆ s)
    (hsfin : volume s < ⊤) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ x, ‖f x‖) ≤ B * (volume s).toReal := by
  have hzero : ∀ x ∉ s, ‖f x‖ = 0 := by
    intro x hx
    rw [norm_eq_zero]
    apply Function.notMem_support.mp
    intro hfx
    exact hx (hs hfx)
  have hset : (∫ x, ‖f x‖) = ∫ x in s, ‖f x‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hnonneg : 0 ≤ ∫ x in s, ‖f x‖ :=
    integral_nonneg fun x => norm_nonneg (f x)
  calc
    (∫ x, ‖f x‖) = ∫ x in s, ‖f x‖ := hset
    _ = ‖∫ x in s, ‖f x‖‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ B * (volume s).toReal := by
      apply MeasureTheory.norm_setIntegral_le_of_norm_le_const hsfin
      intro x _
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (f x))]
      exact hB x

/-- For \ref{lem:smoothdecay2}, iterated derivatives have topological support contained in
the topological support of the original function.  This lets `smoothDecay2` use a common
support-measure factor. -/
theorem aux_tsupport_iteratedDeriv_subset (zeta : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n zeta) ⊆ tsupport zeta := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using (Set.Subset.rfl : tsupport zeta ⊆ tsupport zeta)
  | succ n hn =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans hn

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this specializes the existing preservation of
topological support under iterated derivatives to the Fourier transform of the standard bump. -/
theorem aux_standardBump_fourier_iteratedDeriv_support (n : ℕ) :
    tsupport (iteratedDeriv n
      (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)))) ⊆
      Set.Icc (-1 : ℝ) 1 := by
  apply aux_tsupport_iteratedDeriv_subset _ n |>.trans
  exact closure_minimal aux_fourier_standardBump_support isClosed_Icc

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this elementary inequality controls the
triangular exponent in the high-order Fourier derivative profile. -/
theorem aux_triangular_le_sq (r : ℕ) : r * (r + 1) / 2 ≤ r ^ 2 := by
  by_cases hr : r = 0
  · simp [hr]
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hstep : r + 1 ≤ 2 * r := by omega
    have hprod : r * (r + 1) ≤ r * (2 * r) := Nat.mul_le_mul_left r hstep
    calc
      r * (r + 1) / 2 ≤ (r * (2 * r)) / 2 := Nat.div_le_div_right hprod
      _ = r ^ 2 := by
        rw [show r * (2 * r) = r ^ 2 * 2 by ring, Nat.mul_div_cancel _ (by omega)]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this bounds the two quadratic exponents
arising in one Leibniz summand. -/
theorem aux_square_sub_split (N i : ℕ) (hi : i ≤ N) :
    i ^ 2 + (N - i) ^ 2 ≤ N ^ 2 := by
  have hsum : i + (N - i) = N := Nat.add_sub_of_le hi
  nlinarith

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the exponent ledger for one
Leibniz summand in every order at least three. -/
theorem aux_standardBump_leibniz_exponent (m N i : ℕ) (hN : 3 ≤ N) (hi : i ≤ N) :
    N + (4 * m + i ^ 2) +
      ((N - i) * (N - i + 1) / 2 + 5 * (N - i) + 6) ≤
      4 * m + 2 * N ^ 2 + 4 * N := by
  have htri : (N - i) * (N - i + 1) / 2 ≤ (N - i) ^ 2 :=
    aux_triangular_le_sq (N - i)
  have hsq : i ^ 2 + (N - i) ^ 2 ≤ N ^ 2 := aux_square_sub_split N i hi
  rcases hN.eq_or_lt with rfl | hN
  · interval_cases i <;> omega
  · have hN4 : 4 ≤ N := by omega
    have htail : 5 * (N - i) + 6 ≤ N ^ 2 + 3 * N := by
      calc
        5 * (N - i) + 6 ≤ 5 * N + 6 := by omega
        _ ≤ N ^ 2 + 3 * N := by nlinarith
    nlinarith

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this supplies the smoothness hypothesis for
the polynomial Fourier multiplier \((2\pi i\xi)^m\) in the Leibniz estimate. -/
theorem aux_standardBumpMultiplier_contDiff (m : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun t : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m) := by
  have hlin : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun t : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply, smul_eq_mul] using
      (Complex.ofRealCLM.contDiff.const_smul (2 * (Real.pi : ℂ) * Complex.I))
  exact hlin.pow m

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this sharper zeroth-order bound for the
polynomial multiplier leaves enough room for the two low-order Leibniz estimates. -/
theorem aux_standardBumpMultiplier_norm_le_zero (m : ℕ) (xi : ℝ) (hxi : |xi| ≤ 1) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)) ^ m‖ ≤ (2 : ℝ) ^ (3 * m) := by
  rw [norm_pow]
  have hfac : ‖2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)‖ = 2 * Real.pi * |xi| := by
    rw [norm_mul, norm_mul, norm_mul]
    norm_num [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hfac]
  have hpi : 2 * Real.pi ≤ (2 : ℝ) ^ 3 := by
    norm_num
    linarith [Real.pi_lt_four]
  calc
    (2 * Real.pi * |xi|) ^ m ≤ ((2 : ℝ) ^ 3 * 1) ^ m := by
      gcongr
    _ = (2 : ℝ) ^ (3 * m) := by rw [mul_one, ← pow_mul]

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the order-zero case of the
Fourier-multiplier estimate, using the sharp Fourier profile bound. -/
theorem aux_standardBumpMultiplier_iteratedDeriv_le_zero (m : ℕ) (xi : ℝ) :
    ‖iteratedDeriv 0
      (fun u : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) ^ m *
        FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) u) xi‖ ≤
      C_standardBumpPropertiesTilde m 0 := by
  let P : ℝ → ℂ := fun t => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m
  let H : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))
  change ‖iteratedDeriv 0 (P * H) xi‖ ≤ C_standardBumpPropertiesTilde m 0
  rw [iteratedDeriv_zero]
  change ‖P xi * H xi‖ ≤ C_standardBumpPropertiesTilde m 0
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have hxab : |xi| ≤ 1 := abs_le.2 hxi
    have hP : ‖P xi‖ ≤ (2 : ℝ) ^ (3 * m) := by
      simpa only [P] using aux_standardBumpMultiplier_norm_le_zero m xi hxab
    have hH : ‖H xi‖ ≤ (2 : ℝ) ^ 0 := by
      simpa only [H, iteratedDeriv_zero] using
        aux_standardBump_fourier_iteratedDeriv_le_zero xi
    calc
      ‖P xi * H xi‖ = ‖P xi‖ * ‖H xi‖ := norm_mul _ _
      _ ≤ (2 : ℝ) ^ (3 * m) * (2 : ℝ) ^ 0 :=
        mul_le_mul hP hH (norm_nonneg _) (by positivity)
      _ = (2 : ℝ) ^ (3 * m) := by norm_num
      _ ≤ (2 : ℝ) ^ (4 * m + 0 ^ 2) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      _ = C_standardBumpPropertiesTilde m 0 := by
        norm_num [C_standardBumpPropertiesTilde]
  · have hH : H xi = 0 := by
      have hzero : iteratedDeriv 0 H xi = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        apply hxi
        simpa only [H] using
          aux_standardBump_fourier_iteratedDeriv_support 0 (subset_closure hmem)
      simpa only [iteratedDeriv_zero] using hzero
    rw [hH, mul_zero, norm_zero, C_standardBumpPropertiesTilde]
    positivity

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the order-one case of the
Fourier-multiplier estimate. -/
theorem aux_standardBumpMultiplier_iteratedDeriv_le_one (m : ℕ) (xi : ℝ) :
    ‖iteratedDeriv 1
      (fun u : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) ^ m *
        FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) u) xi‖ ≤
      C_standardBumpPropertiesTilde m 1 := by
  let P : ℝ → ℂ := fun t => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m
  let H : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))
  change ‖iteratedDeriv 1 (P * H) xi‖ ≤ C_standardBumpPropertiesTilde m 1
  by_cases hm : m = 0
  · subst m
    have hPone : P = fun _ : ℝ => (1 : ℂ) := by
      funext u
      simp [P]
    rw [hPone]
    have hPH : (fun _ : ℝ => (1 : ℂ)) * H = H := by
      funext u
      simp
    rw [hPH]
    convert aux_standardBump_fourier_iteratedDeriv_le_one xi using 1 <;>
      norm_num [H, C_standardBumpPropertiesTilde]
  have hPcont : ContDiffAt ℝ 1 P xi := by
    apply (aux_standardBumpMultiplier_contDiff m).contDiffAt.of_le
    exact WithTop.coe_le_coe.mpr le_top
  have hHcont : ContDiffAt ℝ 1 H xi := by
    apply aux_standardBumpComplex_fourier_contDiff.contDiffAt.of_le
    exact WithTop.coe_le_coe.mpr le_top
  rw [iteratedDeriv_mul hPcont hHcont]
  norm_num [Finset.sum_range_succ]
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have hxab : |xi| ≤ 1 := abs_le.2 hxi
    have hP0 : ‖P xi‖ ≤ (2 : ℝ) ^ (3 * m) := by
      simpa only [P] using aux_standardBumpMultiplier_norm_le_zero m xi hxab
    have hP1 : ‖deriv P xi‖ ≤ (2 : ℝ) ^ (4 * m + 1 ^ 2) := by
      simpa only [P, iteratedDeriv_succ, iteratedDeriv_zero] using
        aux_norm_iteratedDeriv_standardBumpMultiplier_le m 1 xi hxab
    have hH0 : ‖H xi‖ ≤ (2 : ℝ) ^ 0 := by
      simpa only [H, iteratedDeriv_zero] using
        aux_standardBump_fourier_iteratedDeriv_le_zero xi
    have hH1 : ‖deriv H xi‖ ≤ (2 : ℝ) ^ 7 := by
      simpa only [H, iteratedDeriv_succ, iteratedDeriv_zero] using
        aux_standardBump_fourier_iteratedDeriv_le_one xi
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    calc
      ‖P xi * deriv H xi + deriv P xi * H xi‖ ≤
          ‖P xi * deriv H xi‖ + ‖deriv P xi * H xi‖ := norm_add_le _ _
      _ = ‖P xi‖ * ‖deriv H xi‖ + ‖deriv P xi‖ * ‖H xi‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ (2 : ℝ) ^ (3 * m) * (2 : ℝ) ^ 7 +
          (2 : ℝ) ^ (4 * m + 1 ^ 2) * (2 : ℝ) ^ 0 := by
        gcongr
      _ ≤ (2 : ℝ) ^ (4 * m + 6) + (2 : ℝ) ^ (4 * m + 6) := by
        apply add_le_add
        · rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        · norm_num
          exact pow_le_pow_right₀ (by norm_num) (by omega)
      _ = C_standardBumpPropertiesTilde m 1 := by
        rw [show (2 : ℝ) ^ (4 * m + 6) + (2 : ℝ) ^ (4 * m + 6) =
          (2 : ℝ) ^ (4 * m + 6) * 2 by ring, ← pow_succ,
          C_standardBumpPropertiesTilde]
        congr 1
  · have hH0 : H xi = 0 := by
      have hzero : iteratedDeriv 0 H xi = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        apply hxi
        simpa only [H] using
          aux_standardBump_fourier_iteratedDeriv_support 0 (subset_closure hmem)
      simpa only [iteratedDeriv_zero] using hzero
    have hH1 : deriv H xi = 0 := by
      have hzero : iteratedDeriv 1 H xi = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        apply hxi
        simpa only [H] using
          aux_standardBump_fourier_iteratedDeriv_support 1 (subset_closure hmem)
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hzero
    simp only [hH0, hH1, mul_zero, add_zero, norm_zero]
    rw [C_standardBumpPropertiesTilde]
    positivity

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the order-two case of the
Fourier-multiplier estimate. -/
theorem aux_standardBumpMultiplier_iteratedDeriv_le_two (m : ℕ) (xi : ℝ) :
    ‖iteratedDeriv 2
      (fun u : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) ^ m *
        FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) u) xi‖ ≤
      C_standardBumpPropertiesTilde m 2 := by
  let P : ℝ → ℂ := fun t => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m
  let H : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))
  change ‖iteratedDeriv 2 (P * H) xi‖ ≤ C_standardBumpPropertiesTilde m 2
  by_cases hm : m = 0
  · subst m
    have hPone : P = fun _ : ℝ => (1 : ℂ) := by
      funext u
      simp [P]
    rw [hPone]
    have hPH : (fun _ : ℝ => (1 : ℂ)) * H = H := by
      funext u
      simp
    rw [hPH]
    convert aux_standardBump_fourier_iteratedDeriv_le_two xi using 1 <;>
      norm_num [H, C_standardBumpPropertiesTilde]
  have hPcont : ContDiffAt ℝ 2 P xi := by
    apply (aux_standardBumpMultiplier_contDiff m).contDiffAt.of_le
    exact WithTop.coe_le_coe.mpr le_top
  have hHcont : ContDiffAt ℝ 2 H xi := by
    apply aux_standardBumpComplex_fourier_contDiff.contDiffAt.of_le
    exact WithTop.coe_le_coe.mpr le_top
  rw [iteratedDeriv_mul hPcont hHcont]
  norm_num [Finset.sum_range_succ]
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have hxab : |xi| ≤ 1 := abs_le.2 hxi
    have hP0 : ‖P xi‖ ≤ (2 : ℝ) ^ (3 * m) := by
      simpa only [P] using aux_standardBumpMultiplier_norm_le_zero m xi hxab
    have hP1 : ‖deriv P xi‖ ≤ (2 : ℝ) ^ (4 * m + 1 ^ 2) := by
      simpa only [P, iteratedDeriv_succ, iteratedDeriv_zero] using
        aux_norm_iteratedDeriv_standardBumpMultiplier_le m 1 xi hxab
    have hP2 : ‖iteratedDeriv 2 P xi‖ ≤ (2 : ℝ) ^ (4 * m + 2 ^ 2) := by
      simpa only [P] using aux_norm_iteratedDeriv_standardBumpMultiplier_le m 2 xi hxab
    have hH0 : ‖H xi‖ ≤ (2 : ℝ) ^ 0 := by
      simpa only [H, iteratedDeriv_zero] using
        aux_standardBump_fourier_iteratedDeriv_le_zero xi
    have hH1 : ‖deriv H xi‖ ≤ (2 : ℝ) ^ 7 := by
      simpa only [H, iteratedDeriv_succ, iteratedDeriv_zero] using
        aux_standardBump_fourier_iteratedDeriv_le_one xi
    have hH2 : ‖iteratedDeriv 2 H xi‖ ≤ (2 : ℝ) ^ 18 := by
      simpa only [H] using aux_standardBump_fourier_iteratedDeriv_le_two xi
    calc
      ‖P xi * iteratedDeriv 2 H xi + 2 * deriv P xi * deriv H xi +
          iteratedDeriv 2 P xi * H xi‖ ≤
          ‖P xi * iteratedDeriv 2 H xi‖ + ‖2 * deriv P xi * deriv H xi‖ +
            ‖iteratedDeriv 2 P xi * H xi‖ := by
        calc
          _ ≤ ‖P xi * iteratedDeriv 2 H xi + 2 * deriv P xi * deriv H xi‖ +
              ‖iteratedDeriv 2 P xi * H xi‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ = ‖P xi‖ * ‖iteratedDeriv 2 H xi‖ +
            2 * ‖deriv P xi‖ * ‖deriv H xi‖ +
            ‖iteratedDeriv 2 P xi‖ * ‖H xi‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        norm_num
      _ ≤ (2 : ℝ) ^ (3 * m) * (2 : ℝ) ^ 18 +
            2 * (2 : ℝ) ^ (4 * m + 1 ^ 2) * (2 : ℝ) ^ 7 +
            (2 : ℝ) ^ (4 * m + 2 ^ 2) * (2 : ℝ) ^ 0 := by
        gcongr
      _ ≤ C_standardBumpPropertiesTilde m 2 := by
        by_cases hmone : m = 1
        · subst m
          norm_num [C_standardBumpPropertiesTilde]
        · have hm2 : 2 ≤ m := by omega
          have hfirst : (2 : ℝ) ^ (3 * m) * (2 : ℝ) ^ 18 ≤
              (2 : ℝ) ^ (4 * m + 16) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          have hsecond : 2 * (2 : ℝ) ^ (4 * m + 1 ^ 2) * (2 : ℝ) ^ 7 ≤
              (2 : ℝ) ^ (4 * m + 16) := by
            calc
              2 * (2 : ℝ) ^ (4 * m + 1 ^ 2) * (2 : ℝ) ^ 7 =
                  ((2 : ℝ) ^ (4 * m + 1) * (2 : ℝ) ^ 7) * 2 := by
                    norm_num
                    ring
              _ = (2 : ℝ) ^ (4 * m + 1 + 7) * 2 := by rw [← pow_add]
              _ = (2 : ℝ) ^ (4 * m + 1 + 7) * (2 : ℝ) ^ 1 := by norm_num
              _ = (2 : ℝ) ^ (4 * m + 1 + 7 + 1) := by rw [← pow_add]
              _ ≤ (2 : ℝ) ^ (4 * m + 16) :=
                pow_le_pow_right₀ (by norm_num) (by omega)
          have hthird : (2 : ℝ) ^ (4 * m + 2 ^ 2) * (2 : ℝ) ^ 0 ≤
              (2 : ℝ) ^ (4 * m + 16) := by
            norm_num
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          calc
            (2 : ℝ) ^ (3 * m) * (2 : ℝ) ^ 18 +
                2 * (2 : ℝ) ^ (4 * m + 1 ^ 2) * (2 : ℝ) ^ 7 +
                (2 : ℝ) ^ (4 * m + 2 ^ 2) * (2 : ℝ) ^ 0 ≤
                (2 : ℝ) ^ (4 * m + 16) + (2 : ℝ) ^ (4 * m + 16) +
                  (2 : ℝ) ^ (4 * m + 16) := by gcongr
            _ = 3 * (2 : ℝ) ^ (4 * m + 16) := by ring
            _ ≤ 4 * (2 : ℝ) ^ (4 * m + 16) := by
              nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (4 * m + 16)]
            _ = C_standardBumpPropertiesTilde m 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add,
                C_standardBumpPropertiesTilde]
              congr 1
              omega
  · have hH0 : H xi = 0 := by
      have hzero : iteratedDeriv 0 H xi = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        apply hxi
        simpa only [H] using
          aux_standardBump_fourier_iteratedDeriv_support 0 (subset_closure hmem)
      simpa only [iteratedDeriv_zero] using hzero
    have hH1 : deriv H xi = 0 := by
      have hzero : iteratedDeriv 1 H xi = 0 := by
        apply Function.notMem_support.mp
        intro hmem
        apply hxi
        simpa only [H] using
          aux_standardBump_fourier_iteratedDeriv_support 1 (subset_closure hmem)
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hzero
    have hH2 : iteratedDeriv 2 H xi = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      apply hxi
      simpa only [H] using
        aux_standardBump_fourier_iteratedDeriv_support 2 (subset_closure hmem)
    simp only [hH0, hH1, hH2, mul_zero, add_zero, norm_zero]
    rw [C_standardBumpPropertiesTilde]
    positivity

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this combines the three sharp low-order
Fourier-multiplier bounds so that the final estimate can split at derivative order two. -/
theorem aux_standardBumpMultiplier_iteratedDeriv_le_low (m N : ℕ) (hN : N ≤ 2) (xi : ℝ) :
    ‖iteratedDeriv N
      (fun u : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) ^ m *
        FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) u) xi‖ ≤
      C_standardBumpPropertiesTilde m N := by
  interval_cases N
  · exact aux_standardBumpMultiplier_iteratedDeriv_le_zero m xi
  · exact aux_standardBumpMultiplier_iteratedDeriv_le_one m xi
  · exact aux_standardBumpMultiplier_iteratedDeriv_le_two m xi

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this bounds one weighted Leibniz summand in
the high-order Fourier-multiplier estimate. -/
theorem aux_standardBumpMultiplier_leibnizTerm (m N i : ℕ) (hN : 3 ≤ N) (hi : i ≤ N)
    (xi : ℝ) (hxi : |xi| ≤ 1) :
    ‖(N.choose i : ℂ) *
        iteratedDeriv i
          (fun t : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m) xi *
        iteratedDeriv (N - i)
          (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))) xi‖ ≤
      (N.choose i : ℝ) * (2 : ℝ) ^ (4 * m + 2 * N ^ 2 + 4 * N) := by
  let P : ℝ → ℂ := fun t => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m
  let H : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))
  change ‖(N.choose i : ℂ) * iteratedDeriv i P xi * iteratedDeriv (N - i) H xi‖ ≤ _
  rw [norm_mul, norm_mul, norm_natCast]
  have hmult : ‖iteratedDeriv i P xi‖ ≤ (2 : ℝ) ^ (4 * m + i ^ 2) := by
    simpa only [P] using aux_norm_iteratedDeriv_standardBumpMultiplier_le m i xi hxi
  have hhat : ‖iteratedDeriv (N - i) H xi‖ ≤
      (2 : ℝ) ^ ((N - i) * (N - i + 1) / 2 + 5 * (N - i) + 6) := by
    simpa only [H] using aux_standardBump_fourier_iteratedDeriv_le_highProfile (N - i) xi
  have hexp : 4 * m + i ^ 2 +
      ((N - i) * (N - i + 1) / 2 + 5 * (N - i) + 6) ≤
      4 * m + 2 * N ^ 2 + 4 * N := by
    have hfull := aux_standardBump_leibniz_exponent m N i hN hi
    omega
  calc
    (N.choose i : ℝ) * ‖iteratedDeriv i P xi‖ * ‖iteratedDeriv (N - i) H xi‖ ≤
        (N.choose i : ℝ) * (2 : ℝ) ^ (4 * m + i ^ 2) *
          (2 : ℝ) ^ ((N - i) * (N - i + 1) / 2 + 5 * (N - i) + 6) := by
      gcongr
    _ = (N.choose i : ℝ) * (2 : ℝ) ^
        (4 * m + i ^ 2 + ((N - i) * (N - i + 1) / 2 + 5 * (N - i) + 6)) := by
      rw [mul_assoc, ← pow_add]
    _ ≤ (N.choose i : ℝ) * (2 : ℝ) ^ (4 * m + 2 * N ^ 2 + 4 * N) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hexp) (by positivity)

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this is the pointwise high-order part of the
Fourier-multiplier profile.  The orders zero, one, and two are handled separately with sharper
moment estimates. -/
theorem aux_standardBumpMultiplier_iteratedDeriv_le_high (m N : ℕ) (hN : 3 ≤ N) (xi : ℝ) :
    ‖iteratedDeriv N
      (fun u : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)) ^ m *
        FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) u) xi‖ ≤
      C_standardBumpPropertiesTilde m N := by
  let P : ℝ → ℂ := fun t => (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ m
  let H : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))
  change ‖iteratedDeriv N (P * H) xi‖ ≤ C_standardBumpPropertiesTilde m N
  have hP : ContDiffAt ℝ N P xi := by
    apply (aux_standardBumpMultiplier_contDiff m).contDiffAt.of_le
    exact WithTop.coe_le_coe.mpr le_top
  have hH : ContDiffAt ℝ N H xi := by
    apply aux_standardBumpComplex_fourier_contDiff.contDiffAt.of_le
    exact WithTop.coe_le_coe.mpr le_top
  rw [iteratedDeriv_mul hP hH]
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have hxiabs : |xi| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hxi.1, hxi.2]
    calc
      ‖∑ i ∈ Finset.range (N + 1), (N.choose i : ℂ) *
          iteratedDeriv i P xi * iteratedDeriv (N - i) H xi‖ ≤
          ∑ i ∈ Finset.range (N + 1), ‖(N.choose i : ℂ) *
            iteratedDeriv i P xi * iteratedDeriv (N - i) H xi‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (N + 1),
          (N.choose i : ℝ) * (2 : ℝ) ^ (4 * m + 2 * N ^ 2 + 4 * N) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact aux_standardBumpMultiplier_leibnizTerm m N i hN hiN xi hxiabs
      _ = (2 : ℝ) ^ N * (2 : ℝ) ^ (4 * m + 2 * N ^ 2 + 4 * N) := by
        rw [← Finset.sum_mul]
        congr 1
        norm_cast
        exact Nat.sum_range_choose N
      _ = C_standardBumpPropertiesTilde m N := by
        rw [C_standardBumpPropertiesTilde, ← pow_add]
        congr 1
        omega
  · have hzero (k : ℕ) : iteratedDeriv k H xi = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      exact hxi (aux_standardBump_fourier_iteratedDeriv_support k (subset_closure hmem))
    have hC : 0 ≤ C_standardBumpPropertiesTilde m N := by
      rw [C_standardBumpPropertiesTilde]
      positivity
    simpa [hzero] using hC

/-- For \ref{standard bump properties} and the public theorem
`standardBumpProperties_fourierDerivativeEstimate`, this makes the explicit Fourier-side
constant available uniformly for every derivative order at most the stated order. -/
theorem aux_C_standardBumpPropertiesTilde_mono (m k N : ℕ) (hk : k ≤ N) :
    C_standardBumpPropertiesTilde m k ≤ C_standardBumpPropertiesTilde m N := by
  rw [C_standardBumpPropertiesTilde, C_standardBumpPropertiesTilde]
  apply pow_le_pow_right₀ (by norm_num)
  have hsq : k ^ 2 ≤ N ^ 2 := by
    exact pow_le_pow_left' hk 2
  omega

/--
\begin{lemma}
   \label{lem:smoothdecay2}\using{lem:smoothdecay}\using{lem: min and bracket}
Let $N\geq 2$ be an integer. Let $\zeta:\R\to\C$ be an $N$ times continuously differentiable function with compact support.
Then the function $\phi=\mathcal F^{-1} \zeta$ belongs to $W_0(\R)$ and we have for all $x\in \R$ the estimate
\begin{equation}\label{E:smoothdecay2}
|\phi(x)|\leq C_{\ref{lem:smoothdecay2}, N} \max(\|\widehat{\phi}\|_\infty, (2\pi )^{-N}\|\widehat{\phi}^{(N)}\|_\infty)|\supp (\widehat{\phi})|   \langle x\rangle^{N}
\end{equation}
with $C_{\ref{lem:smoothdecay2}, N}=2^{N} $.
\end{lemma}
-/
theorem smoothDecay2 (N : ℕ) (hN : 2 ≤ N) (zeta : ℝ → ℂ)
    (hzeta : ContDiff ℝ N zeta) (hzetaSupport : HasCompactSupport zeta) :
    MemW0 (FourierTransformInv.fourierInv zeta) ∧
      ∀ x : ℝ, ‖FourierTransformInv.fourierInv zeta x‖ ≤
        C_smoothDecay2 N *
          max (sSup (Set.range fun xi : ℝ => ‖zeta xi‖))
            ((2 * Real.pi)⁻¹ ^ N *
              sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N zeta xi‖)) *
          (volume (tsupport zeta)).toReal * bracketBump x ^ N := by
  obtain ⟨hmem, hdecay⟩ := smoothDecay N hN zeta hzeta hzetaSupport
  have hmeasure : volume (tsupport zeta) < ⊤ :=
    hzetaSupport.isCompact.measure_lt_top
  have hzetaBounded : BddAbove (Set.range fun xi : ℝ => ‖zeta xi‖) := by
    obtain ⟨C, hC⟩ := hzeta.continuous.bounded_above_of_compact_support hzetaSupport
    refine ⟨C, ?_⟩
    rintro _ ⟨xi, rfl⟩
    exact hC xi
  have hderivCont : Continuous (iteratedDeriv N zeta) :=
    hzeta.continuous_iteratedDeriv N (by simp)
  have hderivSupport : HasCompactSupport (iteratedDeriv N zeta) :=
    aux_hasCompactSupport_iteratedDeriv zeta hzetaSupport N
  have hderivBounded : BddAbove (Set.range fun xi : ℝ => ‖iteratedDeriv N zeta xi‖) := by
    obtain ⟨C, hC⟩ := hderivCont.bounded_above_of_compact_support hderivSupport
    refine ⟨C, ?_⟩
    rintro _ ⟨xi, rfl⟩
    exact hC xi
  let A : ℝ := sSup (Set.range fun xi : ℝ => ‖zeta xi‖)
  let D : ℝ := sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N zeta xi‖)
  let S : ℝ := (2 * Real.pi)⁻¹ ^ N
  let V : ℝ := (volume (tsupport zeta)).toReal
  let M : ℝ := max A (S * D)
  have hApoint (xi : ℝ) : ‖zeta xi‖ ≤ A := by
    exact le_csSup hzetaBounded ⟨xi, rfl⟩
  have hDpoint (xi : ℝ) : ‖iteratedDeriv N zeta xi‖ ≤ D := by
    exact le_csSup hderivBounded ⟨xi, rfl⟩
  have hA : 0 ≤ A := (norm_nonneg (zeta 0)).trans (hApoint 0)
  have hD : 0 ≤ D := (norm_nonneg (iteratedDeriv N zeta 0)).trans (hDpoint 0)
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    exact ENNReal.toReal_nonneg
  have hM : 0 ≤ M := hA.trans (le_max_left _ _)
  have hAleM : A ≤ M := le_max_left _ _
  have hSDleM : S * D ≤ M := le_max_right _ _
  have hL1zeta : (∫ xi : ℝ, ‖zeta xi‖) ≤ A * V := by
    exact aux_integralNorm_le_bound_mul_measure_of_support_subset
      (subset_tsupport zeta) hmeasure hApoint
  have hL1deriv : (∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤ D * V := by
    apply aux_integralNorm_le_bound_mul_measure_of_support_subset
      ((subset_tsupport (iteratedDeriv N zeta)).trans
        (aux_tsupport_iteratedDeriv_subset zeta N)) hmeasure
    exact hDpoint
  refine ⟨hmem, ?_⟩
  intro x
  change ‖FourierTransformInv.fourierInv zeta x‖ ≤
    C_smoothDecay2 N * M * V * bracketBump x ^ N
  by_cases hx : x = 0
  · subst x
    have hC : 1 ≤ C_smoothDecay2 N := by
      rw [C_smoothDecay2]
      exact one_le_pow₀ (by norm_num)
    calc
      ‖FourierTransformInv.fourierInv zeta 0‖ ≤ ∫ xi : ℝ, ‖zeta xi‖ :=
        aux_norm_inverseFourier_le_integral_norm zeta 0
      _ ≤ A * V := hL1zeta
      _ ≤ M * V := mul_le_mul_of_nonneg_right hAleM hV
      _ = 1 * (M * V) := by ring
      _ ≤ C_smoothDecay2 N * (M * V) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg hM hV)
      _ = C_smoothDecay2 N * M * V * bracketBump 0 ^ N := by
        simp [bracketBump]
        ring
  · have hr : 0 ≤ |x|⁻¹ ^ N := by positivity
    have hdecay' := hdecay x hx
    change ‖FourierTransformInv.fourierInv zeta x‖ ≤
      min (∫ xi : ℝ, ‖zeta xi‖)
        (S * |x|⁻¹ ^ N * ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) at hdecay'
    have hderivTerm :
        S * |x|⁻¹ ^ N * (∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤
          (S * D * |x|⁻¹ ^ N) * V := by
      calc
        S * |x|⁻¹ ^ N * (∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤
            S * |x|⁻¹ ^ N * (D * V) :=
          mul_le_mul_of_nonneg_left hL1deriv (mul_nonneg hS hr)
        _ = (S * D * |x|⁻¹ ^ N) * V := by ring
    have hminL1 :
        min (∫ xi : ℝ, ‖zeta xi‖)
          (S * |x|⁻¹ ^ N * ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤
          V * min A (S * D * |x|⁻¹ ^ N) := by
      calc
        min (∫ xi : ℝ, ‖zeta xi‖)
            (S * |x|⁻¹ ^ N * ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤
            min (A * V) ((S * D * |x|⁻¹ ^ N) * V) :=
          min_le_min hL1zeta hderivTerm
        _ = min A (S * D * |x|⁻¹ ^ N) * V := by
          rw [min_mul_of_nonneg _ _ hV]
        _ = V * min A (S * D * |x|⁻¹ ^ N) := by ring
    have hminM : min A (S * D * |x|⁻¹ ^ N) ≤
        M * min 1 (|x|⁻¹ ^ N) := by
      calc
        min A (S * D * |x|⁻¹ ^ N) ≤ min M (M * |x|⁻¹ ^ N) :=
          min_le_min hAleM (mul_le_mul_of_nonneg_right hSDleM hr)
        _ = M * min 1 (|x|⁻¹ ^ N) := by
          simpa only [mul_one] using (mul_min_of_nonneg 1 (|x|⁻¹ ^ N) hM).symm
    have hbracket : min 1 (|x|⁻¹ ^ N) ≤ C_smoothDecay2 N * bracketBump x ^ N := by
      simpa only [C_smoothDecay2] using min_and_bracket N (by omega) x
    calc
      ‖FourierTransformInv.fourierInv zeta x‖ ≤
          min (∫ xi : ℝ, ‖zeta xi‖)
            (S * |x|⁻¹ ^ N * ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) := hdecay'
      _ ≤ V * min A (S * D * |x|⁻¹ ^ N) := hminL1
      _ ≤ V * (M * min 1 (|x|⁻¹ ^ N)) :=
        mul_le_mul_of_nonneg_left hminM hV
      _ ≤ V * (M * (C_smoothDecay2 N * bracketBump x ^ N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbracket hM) hV
      _ = C_smoothDecay2 N * M * V * bracketBump x ^ N := by ring

/-- Source label `\ref{mean value bump estimate 2}`; the sharp pass-8 constant used by the
public theorem `meanValueBumpEstimate`. -/
def C_meanValueBumpEstimate (N : ℕ) : ℝ :=
  (2 : ℝ) ^ N * max 2 ((1 + (2 * Real.pi)⁻¹) ^ N)

/-- The sharp pass-8 mean-value constant is bounded by the former conservative fallback.
This is retained for downstream explicit-constant estimates. -/
theorem aux_C_meanValueBumpEstimate_le (N : ℕ) :
    C_meanValueBumpEstimate N ≤ (2 : ℝ) ^ (2 * N + 1) := by
  let q : ℝ := (2 * Real.pi)⁻¹
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqle : q ≤ 1 := by
    dsimp [q]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by nlinarith [Real.pi_gt_three] : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hpow : (1 + q) ^ N ≤ (2 : ℝ) ^ N := by
    apply pow_le_pow_left₀
    · linarith
    · linarith
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ (2 : ℝ) ^ (N + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow' : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (N + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hmax : max 2 ((1 + q) ^ N) ≤ (2 : ℝ) ^ (N + 1) :=
    max_le htwo (hpow.trans hpow')
  rw [C_meanValueBumpEstimate]
  change (2 : ℝ) ^ N * max 2 ((1 + q) ^ N) ≤ (2 : ℝ) ^ (2 * N + 1)
  calc
    (2 : ℝ) ^ N * max 2 ((1 + q) ^ N) ≤
        (2 : ℝ) ^ N * (2 : ℝ) ^ (N + 1) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = (2 : ℝ) ^ (2 * N + 1) := by
      rw [← pow_add]
      congr 1
      omega

/-- The pass-8 mean-value constant has the stated finite-order value. -/
theorem aux_C_meanValueBumpEstimate_two :
    C_meanValueBumpEstimate 2 = 8 := by
  let q : ℝ := (2 * Real.pi)⁻¹
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqle : q ≤ 1 / 6 := by
    dsimp [q]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by nlinarith [Real.pi_gt_three] : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hpow : (1 + q) ^ 2 ≤ 2 := by
    calc
      (1 + q) ^ 2 ≤ (7 / 6 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ 2 := by norm_num
  rw [C_meanValueBumpEstimate]
  change (2 : ℝ) ^ 2 * max 2 ((1 + q) ^ 2) = 8
  rw [max_eq_left hpow]
  norm_num

/-- Source labels `\ref{mean value bump estimate 2}`, `\ref{L:faa-di-bruno}`, and
`\ref{mean four scale Gaussian kernel}`; this finite maximum is used by
`meanValueBumpEstimate`, `faaDiBruno`, and `meanFourScaleGaussianKernel`. -/
noncomputable def aux_maxUpTo (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image f).max' (by
    refine ⟨f 0, Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
    exact Finset.mem_range.mpr (Nat.succ_pos _))

/-- For \ref{mean value bump estimate 2}, `aux_maxUpTo` bounds each of the finitely many
derivative profiles used by the public theorem `meanValueBumpEstimate`. -/
theorem aux_le_maxUpTo (f : ℕ → ℝ) {nu N : ℕ} (hnu : nu ≤ N) :
    f nu ≤ aux_maxUpTo f N := by
  unfold aux_maxUpTo
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨nu, Finset.mem_range.mpr (Nat.lt_succ_of_le hnu), rfl⟩

/-- For \ref{mean value bump estimate 2}, this gives the smoothness of the Fourier phase
used in the proof of `meanValueBumpEstimate`. -/
theorem aux_fourierPhase_contDiff (N : ℕ) (y : ℝ) :
    ContDiff ℝ N (fun t : ℝ => (Real.fourierChar (t * y)).1) := by
  have hreal : ContDiff ℝ N (fun t : ℝ => 2 * Real.pi * (t * y)) := by
    fun_prop
  have hcomplex : ContDiff ℝ N
      (fun t : ℝ => ((2 * Real.pi * (t * y) : ℝ) : ℂ)) := by
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp hreal)
  rw [show (fun t : ℝ => (Real.fourierChar (t * y)).1) =
      fun t => Complex.exp (((2 * Real.pi * (t * y) : ℝ) : ℂ) * Complex.I) by
    funext t
    rw [Real.fourierChar_apply]]
  exact (hcomplex.mul contDiff_const).cexp

/-- For \ref{mean value bump estimate 2}, this is the first derivative of the Fourier phase
needed by the public theorem `meanValueBumpEstimate`. -/
theorem aux_deriv_fourierPhase (xi y : ℝ) :
    deriv (fun t : ℝ => (Real.fourierChar (t * y)).1) xi =
      (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) *
        (Real.fourierChar (xi * y)).1 := by
  have hlin : HasDerivAt (fun t : ℝ => t * y) y xi := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id xi).mul_const y
  have h := (Real.hasDerivAt_fourierChar (xi * y)).scomp xi hlin
  have heq : (y : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I * (Real.fourierChar (xi * y)).1) =
      (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) *
        (Real.fourierChar (xi * y)).1 := by
    ring
  rw [← heq]
  simpa [Function.comp_def, Complex.real_smul] using h.deriv

/-- For \ref{mean value bump estimate 2}, this iterates the phase derivative appearing in the
proof of the public theorem `meanValueBumpEstimate`. -/
theorem aux_iteratedDeriv_fourierPhase (n : ℕ) (y : ℝ) :
    iteratedDeriv n (fun t : ℝ => (Real.fourierChar (t * y)).1) =
      fun t => (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) ^ n *
        (Real.fourierChar (t * y)).1 := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [iteratedDeriv_succ, hn]
      funext t
      have hdiff : DifferentiableAt ℝ
          (fun u : ℝ => (Real.fourierChar (u * y)).1) t := by
        have hlin : HasDerivAt (fun u : ℝ => u * y) y t := by
          simpa only [id_eq, one_mul] using (hasDerivAt_id t).mul_const y
        exact ((Real.hasDerivAt_fourierChar (t * y)).scomp t hlin).differentiableAt
      rw [deriv_const_mul _ hdiff, aux_deriv_fourierPhase]
      ring

/-- For \ref{mean value bump estimate 2}, this separates the zeroth derivative of the phase
difference from its positive-order derivatives for `meanValueBumpEstimate`. -/
theorem aux_iteratedDeriv_fourierPhase_sub_one (n : ℕ) (y t : ℝ) :
    iteratedDeriv n (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) t =
      if n = 0 then (Real.fourierChar (t * y)).1 - 1 else
        (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) ^ n *
          (Real.fourierChar (t * y)).1 := by
  cases n with
  | zero => simp
  | succ n =>
      change iteratedDeriv (n + 1)
        ((fun u : ℝ => (Real.fourierChar (u * y)).1) - fun _ => (1 : ℂ)) t = _
      have hphase : ContDiffAt ℝ (n + 1)
          (fun u : ℝ => (Real.fourierChar (u * y)).1) t :=
        (aux_fourierPhase_contDiff (n + 1) y).contDiffAt
      have hconst : ContDiffAt ℝ (n + 1) (fun _ : ℝ => (1 : ℂ)) t :=
        contDiff_const.contDiffAt
      rw [iteratedDeriv_sub hphase hconst, iteratedDeriv_const,
        if_neg (Nat.succ_ne_zero _)]
      rw [aux_iteratedDeriv_fourierPhase]
      simp

/-- For \ref{mean value bump estimate 2} and `meanValueBumpEstimate`, this is the
elementary mean-value estimate for the Fourier phase difference. -/
theorem aux_norm_fourierPhase_sub_one_le (xi y : ℝ) :
    ‖(Real.fourierChar (xi * y)).1 - 1‖ ≤ 2 * Real.pi * |xi| * |y| := by
  rw [Real.fourierChar_apply]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (xi * y))
  rw [show ((2 * Real.pi * (xi * y) : ℝ) : ℂ) * Complex.I =
      Complex.I * ((2 * Real.pi * (xi * y) : ℝ) : ℂ) by ring]
  rw [Real.norm_eq_abs] at h
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos Real.pi_pos] at h
  norm_num at h
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- For \ref{mean value bump estimate 2} and `meanValueBumpEstimate`, this keeps the
`(2π)⁻¹` weight attached to every derivative of the Fourier phase difference in the
small-translation regime. -/
theorem aux_scaledIteratedDeriv_fourierPhase_sub_one_le (k : ℕ) (xi y : ℝ)
    (hxi : |xi| ≤ 1) (hsmall : 2 * Real.pi * |y| ≤ 1) :
    (2 * Real.pi)⁻¹ ^ k *
        ‖iteratedDeriv k (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖ ≤
      (2 * Real.pi)⁻¹ ^ k * (2 * Real.pi * |y|) := by
  let a : ℝ := 2 * Real.pi * |y|
  let q : ℝ := (2 * Real.pi)⁻¹
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqle : q ≤ 1 := by
    dsimp [q]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by nlinarith [Real.pi_gt_three] : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hpowq (n : ℕ) : q ^ n ≤ 1 := by
    induction n with
    | zero => simp
    | succ n hn =>
        rw [pow_succ]
        calc
          q ^ n * q ≤ 1 * 1 := mul_le_mul hn hqle hq zero_le_one
          _ = 1 := by ring
  have hpowaone (n : ℕ) : a ^ n ≤ 1 := by
    induction n with
    | zero => simp
    | succ n hn =>
        rw [pow_succ]
        calc
          a ^ n * a ≤ 1 * 1 := mul_le_mul hn hsmall ha zero_le_one
          _ = 1 := by ring
  have hpowa (n : ℕ) (hn : 1 ≤ n) : a ^ n ≤ a := by
    cases n with
    | zero => omega
    | succ n =>
        rw [pow_succ]
        calc
          a ^ n * a ≤ 1 * a := mul_le_mul_of_nonneg_right (hpowaone n) ha
          _ = a := by ring
  change q ^ k *
      ‖iteratedDeriv k (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖ ≤ q ^ k * a
  cases k with
  | zero =>
      simp only [pow_zero, iteratedDeriv_zero, one_mul]
      calc
        ‖(Real.fourierChar (xi * y)).1 - 1‖ ≤ 2 * Real.pi * |xi| * |y| :=
          aux_norm_fourierPhase_sub_one_le xi y
        _ ≤ 2 * Real.pi * |y| := by
          have hnonneg : 0 ≤ 2 * Real.pi * |y| := by positivity
          nlinarith
        _ = a := rfl
  | succ k =>
      rw [aux_iteratedDeriv_fourierPhase_sub_one,
        if_neg (Nat.succ_ne_zero _), norm_mul, norm_pow]
      have hcoeff : ‖2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)‖ = a := by
        change ‖2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)‖ = 2 * Real.pi * |y|
        calc
          ‖2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)‖ =
              ‖-(2 * (Real.pi : ℂ) * Complex.I * (y : ℂ))‖ := (norm_neg _).symm
          _ = ‖-(2 * Real.pi * Complex.I * y)‖ := by congr 1
          _ = 2 * Real.pi * |y| := aux_norm_fourier_derivative_factor y
      have hchar : ‖(Real.fourierChar (xi * y)).1‖ = 1 := by
        rw [Real.fourierChar_apply]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [hcoeff, hchar, mul_one]
      exact mul_le_mul_of_nonneg_left (hpowa (k + 1) (by omega)) (pow_nonneg hq _)

/-- For \ref{mean value bump estimate 2}, this controls each scaled Fourier-side derivative by
the finite maximum used in the public theorem `meanValueBumpEstimate`. -/
theorem aux_scaledIteratedDeriv_le_maxUpTo (N n : ℕ) (zeta : ℝ → ℂ)
    (hzeta : ContDiff ℝ N zeta) (hzetaSupport : HasCompactSupport zeta)
    (hn : n ≤ N) (xi : ℝ) :
    (2 * Real.pi)⁻¹ ^ n * ‖iteratedDeriv n zeta xi‖ ≤
      aux_maxUpTo
        (fun nu => (2 * Real.pi)⁻¹ ^ nu *
          sSup (Set.range fun u : ℝ => ‖iteratedDeriv nu zeta u‖)) N := by
  have hcontNorm : Continuous (fun u : ℝ => ‖iteratedDeriv n zeta u‖) :=
    (hzeta.continuous_iteratedDeriv n (by exact_mod_cast hn)).norm
  have hbounded : BddAbove (Set.range fun u : ℝ => ‖iteratedDeriv n zeta u‖) :=
    hcontNorm.bddAbove_range_of_hasCompactSupport
      (aux_hasCompactSupport_iteratedDeriv zeta hzetaSupport n).norm
  have hpoint : ‖iteratedDeriv n zeta xi‖ ≤
      sSup (Set.range fun u : ℝ => ‖iteratedDeriv n zeta u‖) :=
    le_csSup hbounded (Set.mem_range_self xi)
  calc
    (2 * Real.pi)⁻¹ ^ n * ‖iteratedDeriv n zeta xi‖ ≤
        (2 * Real.pi)⁻¹ ^ n *
          sSup (Set.range fun u : ℝ => ‖iteratedDeriv n zeta u‖) :=
      mul_le_mul_of_nonneg_left hpoint (by positivity)
    _ ≤ aux_maxUpTo
        (fun nu => (2 * Real.pi)⁻¹ ^ nu *
          sSup (Set.range fun u : ℝ => ‖iteratedDeriv nu zeta u‖)) N :=
      aux_le_maxUpTo
        (fun nu => (2 * Real.pi)⁻¹ ^ nu *
          sSup (Set.range fun u : ℝ => ‖iteratedDeriv nu zeta u‖)) hn

/-- For \ref{mean value bump estimate 2} and `meanValueBumpEstimate`, this is the
weighted Leibniz estimate for the scaled highest derivative of the frequency-side translated
difference on the support interval. -/
theorem aux_scaledIteratedDeriv_modulated_le (N : ℕ) (rhoHat : ℝ → ℂ)
    (hrhoHat : ContDiff ℝ N rhoHat) (hrhoHatSupport : HasCompactSupport rhoHat)
    (xi y : ℝ) (hxi : |xi| ≤ 1) (hsmall : 2 * Real.pi * |y| ≤ 1) :
    (2 * Real.pi)⁻¹ ^ N *
        ‖iteratedDeriv N
          (fun u : ℝ => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)) xi‖ ≤
      (1 + (2 * Real.pi)⁻¹) ^ N *
        aux_maxUpTo
          (fun nu => (2 * Real.pi)⁻¹ ^ nu *
            sSup (Set.range fun u : ℝ => ‖iteratedDeriv nu rhoHat u‖)) N *
        (2 * Real.pi * |y|) := by
  let M : ℝ := aux_maxUpTo
    (fun nu => (2 * Real.pi)⁻¹ ^ nu *
      sSup (Set.range fun u : ℝ => ‖iteratedDeriv nu rhoHat u‖)) N
  let a : ℝ := 2 * Real.pi * |y|
  let q : ℝ := (2 * Real.pi)⁻¹
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hphaseCont : ContDiffAt ℝ N
      (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi :=
    ((aux_fourierPhase_contDiff N y).sub contDiff_const).contDiffAt
  have hM : 0 ≤ M := by
    have hzero := aux_scaledIteratedDeriv_le_maxUpTo N 0 rhoHat hrhoHat
      hrhoHatSupport zero_le xi
    have hzero' : ‖rhoHat xi‖ ≤ M := by
      simpa only [pow_zero, one_mul, iteratedDeriv_zero] using hzero
    exact (norm_nonneg (rhoHat xi)).trans hzero'
  change q ^ N *
      ‖iteratedDeriv N
        (rhoHat * fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖ ≤
      (1 + q) ^ N * M * a
  rw [iteratedDeriv_mul hrhoHat.contDiffAt hphaseCont]
  calc
    q ^ N *
        ‖∑ i ∈ Finset.range (N + 1),
          ↑(N.choose i) * iteratedDeriv i rhoHat xi *
            iteratedDeriv (N - i)
              (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖ ≤
        q ^ N * ∑ i ∈ Finset.range (N + 1),
          ‖↑(N.choose i) * iteratedDeriv i rhoHat xi *
            iteratedDeriv (N - i)
              (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hq _)
    _ = ∑ i ∈ Finset.range (N + 1), q ^ N *
          ‖↑(N.choose i) * iteratedDeriv i rhoHat xi *
            iteratedDeriv (N - i)
              (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (N + 1),
        (N.choose i : ℝ) * (q ^ (N - i) * (M * a)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hRho := aux_scaledIteratedDeriv_le_maxUpTo N i rhoHat hrhoHat
        hrhoHatSupport hiN xi
      have hPhase := aux_scaledIteratedDeriv_fourierPhase_sub_one_le (N - i) xi y
        (by omega) hsmall
      have hterm :
          q ^ N *
              ‖↑(N.choose i) * iteratedDeriv i rhoHat xi *
                iteratedDeriv (N - i)
                  (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖ =
            (N.choose i : ℝ) *
              (q ^ i * ‖iteratedDeriv i rhoHat xi‖) *
              (q ^ (N - i) *
                ‖iteratedDeriv (N - i)
                  (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖) := by
        rw [norm_mul, norm_mul, norm_natCast]
        have hpow : q ^ N = q ^ i * q ^ (N - i) := by
          rw [← pow_add, Nat.add_sub_of_le hiN]
        rw [hpow]
        ring
      rw [hterm]
      calc
        (N.choose i : ℝ) * (q ^ i * ‖iteratedDeriv i rhoHat xi‖) *
            (q ^ (N - i) *
              ‖iteratedDeriv (N - i)
                (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖) =
            (N.choose i : ℝ) *
              ((q ^ i * ‖iteratedDeriv i rhoHat xi‖) *
                (q ^ (N - i) *
                  ‖iteratedDeriv (N - i)
                    (fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) xi‖)) := by
          ring
        _ ≤ (N.choose i : ℝ) * (M * (q ^ (N - i) * a)) := by
          apply mul_le_mul_of_nonneg_left
          exact mul_le_mul hRho hPhase (by positivity) hM
          positivity
        _ = (N.choose i : ℝ) * (q ^ (N - i) * (M * a)) := by ring
    _ = ∑ i ∈ Finset.range (N + 1),
        ((N.choose i : ℝ) * q ^ (N - i)) * (M * a) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i ∈ Finset.range (N + 1),
        (N.choose i : ℝ) * q ^ (N - i)) * (M * a) :=
      (Finset.sum_mul _ _ _).symm
    _ = (1 + q) ^ N * M * a := by
      have hsum : (∑ i ∈ Finset.range (N + 1),
          (N.choose i : ℝ) * q ^ (N - i)) = (1 + q) ^ N := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow (1 : ℝ) q N).symm
      rw [hsum]
      ring

/-- For \ref{mean value bump estimate 2} and `meanValueBumpEstimate`, this lifts the
weighted small-translation product estimates from the Fourier support interval to the two
supremum profiles used by inverse-Fourier decay. -/
theorem aux_modulated_profile_le (N : ℕ) (rhoHat : ℝ → ℂ)
    (hrhoHat : ContDiff ℝ N rhoHat) (hrhoHatSupport : HasCompactSupport rhoHat)
    (hsupp : tsupport rhoHat ⊆ Set.Icc (-1) 1) (y : ℝ)
    (hsmall : 2 * Real.pi * |y| ≤ 1) :
    max
        (sSup (Set.range fun xi : ℝ =>
          ‖rhoHat xi * ((Real.fourierChar (xi * y)).1 - 1)‖))
        ((2 * Real.pi)⁻¹ ^ N *
          sSup (Set.range fun xi : ℝ =>
            ‖iteratedDeriv N
              (fun u : ℝ => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)) xi‖)) ≤
      (1 + (2 * Real.pi)⁻¹) ^ N *
        aux_maxUpTo
          (fun nu => (2 * Real.pi)⁻¹ ^ nu *
            sSup (Set.range fun u : ℝ => ‖iteratedDeriv nu rhoHat u‖)) N *
        (2 * Real.pi * |y|) := by
  let g : ℝ → ℂ := fun u => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)
  let M : ℝ := aux_maxUpTo
    (fun nu => (2 * Real.pi)⁻¹ ^ nu *
      sSup (Set.range fun u : ℝ => ‖iteratedDeriv nu rhoHat u‖)) N
  let a : ℝ := 2 * Real.pi * |y|
  let q : ℝ := (2 * Real.pi)⁻¹
  let B : ℝ := (1 + q) ^ N * M * a
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hM : 0 ≤ M := by
    have hzero := aux_scaledIteratedDeriv_le_maxUpTo N 0 rhoHat hrhoHat
      hrhoHatSupport zero_le 0
    have hzero' : ‖rhoHat 0‖ ≤ M := by
      simpa only [pow_zero, one_mul, iteratedDeriv_zero] using hzero
    exact (norm_nonneg (rhoHat 0)).trans hzero'
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpow : 1 ≤ (1 + q) ^ N :=
    one_le_pow₀ (by linarith)
  have hgsupp : tsupport g ⊆ tsupport rhoHat := by
    change tsupport (rhoHat * fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) ⊆
      tsupport rhoHat
    exact tsupport_mul_subset_left
  have hderivSupp : tsupport (iteratedDeriv N g) ⊆ tsupport rhoHat :=
    (aux_tsupport_iteratedDeriv_subset g N).trans hgsupp
  have hpoint (xi : ℝ) : ‖g xi‖ ≤ B := by
    by_cases hxiMem : xi ∈ tsupport rhoHat
    · have hinterval := hsupp hxiMem
      have hxi : |xi| ≤ 1 := abs_le.2 ⟨by linarith [hinterval.1], hinterval.2⟩
      have hRho := aux_scaledIteratedDeriv_le_maxUpTo N 0 rhoHat hrhoHat
        hrhoHatSupport zero_le xi
      have hPhase := aux_scaledIteratedDeriv_fourierPhase_sub_one_le 0 xi y hxi hsmall
      have hRho' : ‖rhoHat xi‖ ≤ M := by
        simpa only [pow_zero, one_mul, iteratedDeriv_zero] using hRho
      have hPhase' : ‖(Real.fourierChar (xi * y)).1 - 1‖ ≤ a := by
        simpa [iteratedDeriv_zero] using hPhase
      have hmain : ‖rhoHat xi * ((Real.fourierChar (xi * y)).1 - 1)‖ ≤ M * a := by
        rw [norm_mul]
        exact mul_le_mul hRho' hPhase' (norm_nonneg _) hM
      change ‖rhoHat xi * ((Real.fourierChar (xi * y)).1 - 1)‖ ≤ B
      calc
        ‖rhoHat xi * ((Real.fourierChar (xi * y)).1 - 1)‖ ≤ M * a := hmain
        _ = 1 * (M * a) := by ring
        _ ≤ (1 + q) ^ N * (M * a) :=
          mul_le_mul_of_nonneg_right hpow (mul_nonneg hM ha)
        _ = B := by dsimp [B]; ring
    · have hzero : g xi = 0 := by
        apply Function.notMem_support.mp
        intro hxiSupport
        exact hxiMem (hgsupp (subset_tsupport g hxiSupport))
      rw [hzero]
      simpa using hB
  have hderivPoint (xi : ℝ) : q ^ N * ‖iteratedDeriv N g xi‖ ≤ B := by
    by_cases hxiMem : xi ∈ tsupport rhoHat
    · have hinterval := hsupp hxiMem
      have hxi : |xi| ≤ 1 := abs_le.2 ⟨by linarith [hinterval.1], hinterval.2⟩
      change q ^ N *
          ‖iteratedDeriv N
            (fun u : ℝ => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)) xi‖ ≤ B
      simpa only [q, M, a, B] using
        aux_scaledIteratedDeriv_modulated_le N rhoHat hrhoHat hrhoHatSupport xi y hxi hsmall
    · have hzero : iteratedDeriv N g xi = 0 := by
        apply Function.notMem_support.mp
        intro hxiSupport
        exact hxiMem (hderivSupp (subset_tsupport _ hxiSupport))
      rw [hzero, norm_zero, mul_zero]
      exact hB
  have hsup : sSup (Set.range fun xi : ℝ => ‖g xi‖) ≤ B := by
    apply csSup_le
    · exact ⟨‖g 0‖, ⟨0, rfl⟩⟩
    rintro _ ⟨xi, rfl⟩
    exact hpoint xi
  have hderivSup :
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖) ≤ B / q ^ N := by
    apply csSup_le
    · exact ⟨‖iteratedDeriv N g 0‖, ⟨0, rfl⟩⟩
    rintro _ ⟨xi, rfl⟩
    apply (le_div_iff₀ (pow_pos hqpos _)).2
    calc
      ‖iteratedDeriv N g xi‖ * q ^ N = q ^ N * ‖iteratedDeriv N g xi‖ := by ring
      _ ≤ B := hderivPoint xi
  have hscaledSup : q ^ N *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖) ≤ B := by
    calc
      q ^ N * sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖) ≤
          q ^ N * (B / q ^ N) :=
        mul_le_mul_of_nonneg_left hderivSup (pow_nonneg hq _)
      _ = B := by
        field_simp [ne_of_gt (pow_pos hqpos N)]
  change max (sSup (Set.range fun xi : ℝ => ‖g xi‖))
      (q ^ N * sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖)) ≤ B
  exact max_le hsup hscaledSup

/-- For \ref{mean value bump estimate 2} and `meanValueBumpEstimate`, this is the
pointwise part of `smoothDecay2` at every positive derivative order. It supplies the
case `N = 1`, for which the Wiener-space conclusion of `smoothDecay2` is unavailable. -/
theorem aux_smoothDecay2_pointwise (N : ℕ) (hN : 1 ≤ N) (zeta : ℝ → ℂ)
    (hzeta : ContDiff ℝ N zeta) (hzetaSupport : HasCompactSupport zeta) :
    ∀ x : ℝ, ‖FourierTransformInv.fourierInv zeta x‖ ≤
      C_smoothDecay2 N *
        max (sSup (Set.range fun xi : ℝ => ‖zeta xi‖))
          ((2 * Real.pi)⁻¹ ^ N *
            sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N zeta xi‖)) *
        (volume (tsupport zeta)).toReal * bracketBump x ^ N := by
  have hzetaInt : ∀ n : ℕ, n ≤ N → Integrable (iteratedDeriv n zeta) :=
    fun n hn => aux_integrable_iteratedDeriv_of_contDiff_compactSupport N n zeta hzeta
      hzetaSupport hn
  have hmeasure : volume (tsupport zeta) < ⊤ :=
    hzetaSupport.isCompact.measure_lt_top
  have hzetaBounded : BddAbove (Set.range fun xi : ℝ => ‖zeta xi‖) := by
    obtain ⟨C, hC⟩ := hzeta.continuous.bounded_above_of_compact_support hzetaSupport
    refine ⟨C, ?_⟩
    rintro _ ⟨xi, rfl⟩
    exact hC xi
  have hderivCont : Continuous (iteratedDeriv N zeta) :=
    hzeta.continuous_iteratedDeriv N (by simp)
  have hderivSupport : HasCompactSupport (iteratedDeriv N zeta) :=
    aux_hasCompactSupport_iteratedDeriv zeta hzetaSupport N
  have hderivBounded : BddAbove (Set.range fun xi : ℝ => ‖iteratedDeriv N zeta xi‖) := by
    obtain ⟨C, hC⟩ := hderivCont.bounded_above_of_compact_support hderivSupport
    refine ⟨C, ?_⟩
    rintro _ ⟨xi, rfl⟩
    exact hC xi
  let A : ℝ := sSup (Set.range fun xi : ℝ => ‖zeta xi‖)
  let D : ℝ := sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N zeta xi‖)
  let S : ℝ := (2 * Real.pi)⁻¹ ^ N
  let V : ℝ := (volume (tsupport zeta)).toReal
  let M : ℝ := max A (S * D)
  have hApoint (xi : ℝ) : ‖zeta xi‖ ≤ A := by
    exact le_csSup hzetaBounded ⟨xi, rfl⟩
  have hDpoint (xi : ℝ) : ‖iteratedDeriv N zeta xi‖ ≤ D := by
    exact le_csSup hderivBounded ⟨xi, rfl⟩
  have hA : 0 ≤ A := (norm_nonneg (zeta 0)).trans (hApoint 0)
  have hD : 0 ≤ D := (norm_nonneg (iteratedDeriv N zeta 0)).trans (hDpoint 0)
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    exact ENNReal.toReal_nonneg
  have hM : 0 ≤ M := hA.trans (le_max_left _ _)
  have hAleM : A ≤ M := le_max_left _ _
  have hSDleM : S * D ≤ M := le_max_right _ _
  have hL1zeta : (∫ xi : ℝ, ‖zeta xi‖) ≤ A * V := by
    exact aux_integralNorm_le_bound_mul_measure_of_support_subset
      (subset_tsupport zeta) hmeasure hApoint
  have hL1deriv : (∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤ D * V := by
    apply aux_integralNorm_le_bound_mul_measure_of_support_subset
      ((subset_tsupport (iteratedDeriv N zeta)).trans
        (aux_tsupport_iteratedDeriv_subset zeta N)) hmeasure
    exact hDpoint
  intro x
  change ‖FourierTransformInv.fourierInv zeta x‖ ≤
    C_smoothDecay2 N * M * V * bracketBump x ^ N
  by_cases hx : x = 0
  · subst x
    have hC : 1 ≤ C_smoothDecay2 N := by
      rw [C_smoothDecay2]
      exact one_le_pow₀ (by norm_num)
    calc
      ‖FourierTransformInv.fourierInv zeta 0‖ ≤ ∫ xi : ℝ, ‖zeta xi‖ :=
        aux_norm_inverseFourier_le_integral_norm zeta 0
      _ ≤ A * V := hL1zeta
      _ ≤ M * V := mul_le_mul_of_nonneg_right hAleM hV
      _ = 1 * (M * V) := by ring
      _ ≤ C_smoothDecay2 N * (M * V) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg hM hV)
      _ = C_smoothDecay2 N * M * V * bracketBump 0 ^ N := by
        simp [bracketBump]
        ring
  · have hr : 0 ≤ |x|⁻¹ ^ N := by positivity
    have hdecay' : ‖FourierTransformInv.fourierInv zeta x‖ ≤
        min (∫ xi : ℝ, ‖zeta xi‖)
          (S * |x|⁻¹ ^ N * ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) := by
      refine le_min (aux_norm_inverseFourier_le_integral_norm zeta x) ?_
      simpa only [S] using
        aux_inverseFourier_iteratedDeriv_decay N zeta hzeta hzetaInt x hx
    have hderivTerm :
        S * |x|⁻¹ ^ N * (∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤
          (S * D * |x|⁻¹ ^ N) * V := by
      calc
        S * |x|⁻¹ ^ N * (∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤
            S * |x|⁻¹ ^ N * (D * V) :=
          mul_le_mul_of_nonneg_left hL1deriv (mul_nonneg hS hr)
        _ = (S * D * |x|⁻¹ ^ N) * V := by ring
    have hminL1 :
        min (∫ xi : ℝ, ‖zeta xi‖)
          (S * |x|⁻¹ ^ N * ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤
          V * min A (S * D * |x|⁻¹ ^ N) := by
      calc
        min (∫ xi : ℝ, ‖zeta xi‖)
            (S * |x|⁻¹ ^ N * ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) ≤
            min (A * V) ((S * D * |x|⁻¹ ^ N) * V) :=
          min_le_min hL1zeta hderivTerm
        _ = min A (S * D * |x|⁻¹ ^ N) * V := by
          rw [min_mul_of_nonneg _ _ hV]
        _ = V * min A (S * D * |x|⁻¹ ^ N) := by ring
    have hminM : min A (S * D * |x|⁻¹ ^ N) ≤
        M * min 1 (|x|⁻¹ ^ N) := by
      calc
        min A (S * D * |x|⁻¹ ^ N) ≤ min M (M * |x|⁻¹ ^ N) :=
          min_le_min hAleM (mul_le_mul_of_nonneg_right hSDleM hr)
        _ = M * min 1 (|x|⁻¹ ^ N) := by
          simpa only [mul_one] using (mul_min_of_nonneg 1 (|x|⁻¹ ^ N) hM).symm
    have hbracket : min 1 (|x|⁻¹ ^ N) ≤ C_smoothDecay2 N * bracketBump x ^ N := by
      simpa only [C_smoothDecay2] using min_and_bracket N hN x
    calc
      ‖FourierTransformInv.fourierInv zeta x‖ ≤
          min (∫ xi : ℝ, ‖zeta xi‖)
            (S * |x|⁻¹ ^ N * ∫ xi : ℝ, ‖iteratedDeriv N zeta xi‖) := hdecay'
      _ ≤ V * min A (S * D * |x|⁻¹ ^ N) := hminL1
      _ ≤ V * (M * min 1 (|x|⁻¹ ^ N)) :=
        mul_le_mul_of_nonneg_left hminM hV
      _ ≤ V * (M * (C_smoothDecay2 N * bracketBump x ^ N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbracket hM) hV
      _ = C_smoothDecay2 N * M * V * bracketBump x ^ N := by ring

/-- For the small-translation branch of `meanValueBumpEstimate`, inverse-Fourier decay
combined with the weighted profile estimate gives a one-sided bracket bound. -/
theorem aux_small_modulated_inverse_bound (N : ℕ) (hN : 1 ≤ N)
    (rhoHat : ℝ → ℂ) (hsupp : tsupport rhoHat ⊆ Set.Icc (-1) 1)
    (hrhoHat : ContDiff ℝ N rhoHat) (z y : ℝ)
    (hsmall : 2 * Real.pi * |y| ≤ 1) :
    ‖FourierTransformInv.fourierInv
        (fun u : ℝ => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)) z‖ ≤
      (2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N *
        aux_maxUpTo
          (fun nu => (2 * Real.pi)⁻¹ ^ nu *
            sSup (Set.range fun xi : ℝ => ‖iteratedDeriv nu rhoHat xi‖)) N *
        (2 * Real.pi * |y|) * bracketBump z ^ N := by
  have hrhoHatSupport : HasCompactSupport rhoHat :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hsupp
  let P : ℝ := aux_maxUpTo
    (fun nu => (2 * Real.pi)⁻¹ ^ nu *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv nu rhoHat xi‖)) N
  let a : ℝ := 2 * Real.pi * |y|
  let g : ℝ → ℂ := fun u => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)
  let Q : ℝ := max
    (sSup (Set.range fun xi : ℝ => ‖g xi‖))
    ((2 * Real.pi)⁻¹ ^ N *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖))
  let Vg : ℝ := (volume (tsupport g)).toReal
  have hP : 0 ≤ P := by
    have hzero := aux_scaledIteratedDeriv_le_maxUpTo N 0 rhoHat hrhoHat
      hrhoHatSupport zero_le 0
    have hzero' : ‖rhoHat 0‖ ≤ P := by
      simpa only [P, pow_zero, one_mul, iteratedDeriv_zero] using hzero
    exact (norm_nonneg (rhoHat 0)).trans hzero'
  have hgCont : ContDiff ℝ N g := by
    change ContDiff ℝ N
      (rhoHat * fun u : ℝ => (Real.fourierChar (u * y)).1 - 1)
    exact hrhoHat.mul ((aux_fourierPhase_contDiff N y).sub contDiff_const)
  have hgSupport : HasCompactSupport g := by
    change HasCompactSupport
      (rhoHat * fun u : ℝ => (Real.fourierChar (u * y)).1 - 1)
    exact hrhoHatSupport.mul_right
  have hgsupp : tsupport g ⊆ Set.Icc (-1) 1 := by
    change tsupport (rhoHat * fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) ⊆
      Set.Icc (-1) 1
    exact tsupport_mul_subset_left.trans hsupp
  have hmeasureg : volume (tsupport g) ≤ volume (Set.Icc (-1 : ℝ) 1) :=
    MeasureTheory.measure_mono hgsupp
  have hIccFinite : volume (Set.Icc (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    norm_num
  have hVg : Vg ≤ 2 := by
    dsimp [Vg]
    calc
      (volume (tsupport g)).toReal ≤ (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono hIccFinite hmeasureg
      _ = 2 := by
        rw [Real.volume_Icc]
        norm_num
  have hVgnonneg : 0 ≤ Vg := by
    dsimp [Vg]
    exact ENNReal.toReal_nonneg
  have hQ : Q ≤ (1 + (2 * Real.pi)⁻¹) ^ N * P * a := by
    simpa only [Q, g, P, a] using
      aux_modulated_profile_le N rhoHat hrhoHat hrhoHatSupport hsupp y hsmall
  have hgDecay : ‖FourierTransformInv.fourierInv g z‖ ≤
      (2 : ℝ) ^ N * Q * Vg * bracketBump z ^ N := by
    simpa only [C_smoothDecay2, Q, Vg] using
      aux_smoothDecay2_pointwise N hN g hgCont hgSupport z
  have hbracket : 0 ≤ bracketBump z ^ N := by
    rw [bracketBump]
    positivity
  have hfactor : 0 ≤ (2 : ℝ) ^ N * Vg * bracketBump z ^ N :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) N) hVgnonneg) hbracket
  change ‖FourierTransformInv.fourierInv g z‖ ≤
    (2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N * P * a * bracketBump z ^ N
  calc
    ‖FourierTransformInv.fourierInv g z‖ ≤
        (2 : ℝ) ^ N * Q * Vg * bracketBump z ^ N := hgDecay
    _ = ((2 : ℝ) ^ N * Vg * bracketBump z ^ N) * Q := by ring
    _ ≤ ((2 : ℝ) ^ N * Vg * bracketBump z ^ N) *
          ((1 + (2 * Real.pi)⁻¹) ^ N * P * a) :=
      mul_le_mul_of_nonneg_left hQ hfactor
    _ = ((2 : ℝ) ^ N * ((1 + (2 * Real.pi)⁻¹) ^ N * P * a)) * Vg *
          bracketBump z ^ N := by ring
    _ ≤ ((2 : ℝ) ^ N * ((1 + (2 * Real.pi)⁻¹) ^ N * P * a)) * 2 *
          bracketBump z ^ N := by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_left hVg
      positivity
      exact hbracket
    _ = (2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N * P * a *
          bracketBump z ^ N := by
      rw [pow_succ]
      ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
identifies physical iterated derivatives with inverse Fourier transforms of polynomial
multipliers. -/
theorem aux_iteratedDeriv_fourierInv (m : ℕ) (hat : ℝ → ℂ)
    (hmom : ∀ n : ℕ, n ≤ m → Integrable (fun xi : ℝ => xi ^ n • hat xi)) (x : ℝ) :
    iteratedDeriv m (FourierTransformInv.fourierInv hat) x =
      FourierTransformInv.fourierInv
        (fun xi : ℝ => (2 * Real.pi * Complex.I * (xi : ℂ)) ^ m * hat xi) x := by
  rw [show (FourierTransformInv.fourierInv hat) =
      fun t => FourierTransform.fourier hat (-t) by
    funext t
    exact Real.fourierInv_eq_fourier_neg hat t]
  rw [iteratedDeriv_comp_neg]
  rw [Real.iteratedDeriv_fourier (N := (m : ℕ∞))
    (fun n hn => hmom n (by exact_mod_cast hn)) (by simp)]
  rw [Real.fourierInv_eq_fourier_neg]
  rw [Complex.real_smul]
  push_cast
  rw [← smul_eq_mul]
  rw [Real.fourier_eq, Real.fourier_eq]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with xi
  simp only [smul_eq_mul]
  have hsign : ((-2 : ℂ) ^ m) * (-1) ^ m = 2 ^ m := by
    rw [← mul_pow]
    norm_num
  ring_nf
  simp only [Circle.smul_def, smul_eq_mul]
  calc
    ↑(𝐞 (-⟪xi, -x⟫)) * (↑Real.pi ^ m * Complex.I ^ m * ↑xi ^ m * hat xi * (-2) ^ m) *
        (-1) ^ m =
      ↑(𝐞 (-⟪xi, -x⟫)) * (↑Real.pi ^ m * Complex.I ^ m * ↑xi ^ m * hat xi *
        (((-2 : ℂ) ^ m) * (-1) ^ m)) := by ring
    _ = ↑(𝐞 (-⟪xi, -x⟫)) * (↑Real.pi ^ m * Complex.I ^ m * ↑xi ^ m * hat xi * 2 ^ m) := by
      rw [hsign]

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
is the zero-order compact-support bound needed to complement the positive-order inverse-Fourier
decay argument. -/
theorem aux_fourierProfile_decay_zero (g : ℝ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hsupp : tsupport g ⊆ Set.Icc (-1 : ℝ) 1)
    (hprofile : ∀ xi : ℝ, ‖g xi‖ ≤ B) (x : ℝ) :
    ‖FourierTransformInv.fourierInv g x‖ ≤
      (2 : ℝ) ^ (0 + 2) * B * bracketBump x ^ (0 : ℕ) := by
  let V : ℝ := (volume (tsupport g)).toReal
  have hcompact : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hsupp
  have hmeasureFin : volume (tsupport g) < ⊤ :=
    hcompact.isCompact.measure_lt_top
  have hmeasure : volume (tsupport g) ≤ volume (Set.Icc (-1 : ℝ) 1) :=
    MeasureTheory.measure_mono hsupp
  have hIccFinite : volume (Set.Icc (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    norm_num
  have hV : V ≤ 2 := by
    dsimp [V]
    calc
      (volume (tsupport g)).toReal ≤ (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono hIccFinite hmeasure
      _ = 2 := by
        rw [Real.volume_Icc]
        norm_num
  have hL1 : (∫ xi : ℝ, ‖g xi‖) ≤ B * V := by
    exact aux_integralNorm_le_bound_mul_measure_of_support_subset
      (subset_tsupport g) hmeasureFin hprofile
  calc
    ‖FourierTransformInv.fourierInv g x‖ ≤ ∫ xi : ℝ, ‖g xi‖ :=
      aux_norm_inverseFourier_le_integral_norm g x
    _ ≤ B * V := hL1
    _ ≤ B * 2 := mul_le_mul_of_nonneg_left hV hB
    _ ≤ (2 : ℝ) ^ (0 + 2) * B * bracketBump x ^ (0 : ℕ) := by
      simp [bracketBump]
      linarith

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
turns a uniform compactly-supported Fourier derivative profile into the pointwise inverse-Fourier
decay needed for the physical derivative estimate at positive order. -/
theorem aux_fourierProfile_decay_pos (N : ℕ) (hN : 1 ≤ N) (g : ℝ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hg : ContDiff ℝ N g)
    (hsupp : tsupport g ⊆ Set.Icc (-1 : ℝ) 1)
    (hprofile : ∀ k : ℕ, k ≤ N → ∀ xi : ℝ,
      ‖iteratedDeriv k g xi‖ ≤ B) (x : ℝ) :
    ‖FourierTransformInv.fourierInv g x‖ ≤
      (2 : ℝ) ^ (N + 2) * B * bracketBump x ^ N := by
  let q : ℝ := (2 * Real.pi)⁻¹
  let V : ℝ := (volume (tsupport g)).toReal
  let M : ℝ := max (sSup (Set.range fun xi : ℝ => ‖g xi‖))
    (q ^ N * sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖))
  have hcompact : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hsupp
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqle : q ≤ 1 := by
    dsimp [q]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by nlinarith [Real.pi_gt_three] : 0 < 2 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hqpow : q ^ N ≤ 1 := by
    simpa using pow_le_pow_left₀ hq hqle N
  have hmeasure : volume (tsupport g) ≤ volume (Set.Icc (-1 : ℝ) 1) :=
    MeasureTheory.measure_mono hsupp
  have hIccFinite : volume (Set.Icc (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    norm_num
  have hV : V ≤ 2 := by
    dsimp [V]
    calc
      (volume (tsupport g)).toReal ≤ (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono hIccFinite hmeasure
      _ = 2 := by
        rw [Real.volume_Icc]
        norm_num
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    exact ENNReal.toReal_nonneg
  have hzero (xi : ℝ) : ‖g xi‖ ≤ B := by
    simpa only [iteratedDeriv_zero] using hprofile 0 zero_le xi
  have hNth (xi : ℝ) : ‖iteratedDeriv N g xi‖ ≤ B := hprofile N le_rfl xi
  have hscaledPoint (xi : ℝ) : q ^ N * ‖iteratedDeriv N g xi‖ ≤ B := by
    calc
      q ^ N * ‖iteratedDeriv N g xi‖ ≤ q ^ N * B :=
        mul_le_mul_of_nonneg_left (hNth xi) (pow_nonneg hq _)
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hqpow hB
      _ = B := by ring
  have hsup : sSup (Set.range fun xi : ℝ => ‖g xi‖) ≤ B := by
    apply csSup_le
    · exact Set.range_nonempty _
    rintro _ ⟨xi, rfl⟩
    exact hzero xi
  have hderivSup :
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖) ≤ B / q ^ N := by
    apply csSup_le
    · exact Set.range_nonempty _
    rintro _ ⟨xi, rfl⟩
    apply (le_div_iff₀ (pow_pos hqpos _)).2
    calc
      ‖iteratedDeriv N g xi‖ * q ^ N = q ^ N * ‖iteratedDeriv N g xi‖ := by ring
      _ ≤ B := hscaledPoint xi
  have hscaledSup : q ^ N *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖) ≤ B := by
    calc
      q ^ N * sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N g xi‖) ≤
          q ^ N * (B / q ^ N) :=
        mul_le_mul_of_nonneg_left hderivSup (pow_nonneg hq _)
      _ = B := by
        field_simp [ne_of_gt (pow_pos hqpos N)]
  have hprofileSup : M ≤ B := by
    dsimp [M]
    exact max_le hsup hscaledSup
  have hbracket : 0 ≤ bracketBump x ^ N := by
    rw [bracketBump]
    positivity
  have hMV : M * V ≤ B * 2 :=
    mul_le_mul hprofileSup hV hVnonneg hB
  have hdecay := aux_smoothDecay2_pointwise N hN g hg hcompact x
  change ‖FourierTransformInv.fourierInv g x‖ ≤
    (2 : ℝ) ^ (N + 2) * B * bracketBump x ^ N
  calc
    ‖FourierTransformInv.fourierInv g x‖ ≤
        (2 : ℝ) ^ N * M * V * bracketBump x ^ N := by
      simpa only [C_smoothDecay2, q, V, M] using hdecay
    _ = ((2 : ℝ) ^ N * bracketBump x ^ N) * (M * V) := by ring
    _ ≤ ((2 : ℝ) ^ N * bracketBump x ^ N) * (B * 2) :=
      mul_le_mul_of_nonneg_left hMV
        (mul_nonneg (pow_nonneg (by norm_num) N) hbracket)
    _ = ((2 : ℝ) ^ N * 2) * (B * bracketBump x ^ N) := by ring
    _ ≤ (2 : ℝ) ^ (N + 2) * (B * bracketBump x ^ N) := by
      apply mul_le_mul_of_nonneg_right
      · calc
          (2 : ℝ) ^ N * 2 = (2 : ℝ) ^ N * 2 ^ 1 := by norm_num
          _ = (2 : ℝ) ^ (N + 1) := by rw [← pow_add]
          _ ≤ (2 : ℝ) ^ (N + 2) := by
            exact pow_le_pow_right₀ (by norm_num) (by omega)
      · exact mul_nonneg hB hbracket
    _ = (2 : ℝ) ^ (N + 2) * B * bracketBump x ^ N := by ring

/-- For \ref{standard bump properties} and the public theorem `standardBumpProperties`, this
converts the sharp compactly-supported Fourier derivative profile into the manuscript's physical
iterated-derivative decay, including the orders $N=0$ and $N=1$. -/
theorem aux_standardBump_iteratedDeriv_decay_of_profile (m N : ℕ)
    (hcont : ContDiff ℝ N
      (fun xi : ℝ => (2 * Real.pi * Complex.I * (xi : ℂ)) ^ m *
        FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) xi))
    (hprofile : ∀ k : ℕ, k ≤ N → ∀ xi : ℝ,
      ‖iteratedDeriv k
        (fun u : ℝ => (2 * Real.pi * Complex.I * (u : ℂ)) ^ m *
          FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) u) xi‖ ≤
        C_standardBumpPropertiesTilde m N) (x : ℝ) :
    ‖iteratedDeriv m (fun x : ℝ => (standardBump x : ℂ)) x‖ ≤
      C_standardBumpProperties m N * bracketBump x ^ N := by
  let phi : ℝ → ℂ := fun x : ℝ => (standardBump x : ℂ)
  let hat : ℝ → ℂ := FourierTransform.fourier phi
  let g : ℝ → ℂ := fun xi : ℝ =>
    (2 * Real.pi * Complex.I * (xi : ℂ)) ^ m * hat xi
  obtain ⟨_, hhatSuppFun, _⟩ := standardBumpProperties_fourierShape
  have hhatSupp : tsupport hat ⊆ Set.Icc (-1 : ℝ) 1 := by
    change tsupport (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))) ⊆
      Set.Icc (-1 : ℝ) 1
    exact closure_minimal hhatSuppFun isClosed_Icc
  have hhatCompact : HasCompactSupport hat :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hhatSupp
  have hhatContDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) hat := by
    simpa only [hat, phi] using aux_standardBumpComplex_fourier_contDiff
  have hhatCont : Continuous hat := hhatContDiff.continuous
  have hhatInt : Integrable hat :=
    hhatCont.integrable_of_hasCompactSupport hhatCompact
  have hmom (n : ℕ) (hn : n ≤ m) : Integrable (fun xi : ℝ => xi ^ n • hat xi) := by
    apply ((continuous_id.pow n).smul hhatCont).integrable_of_hasCompactSupport
    apply hhatCompact.mono
    intro xi hxi
    rw [Function.mem_support] at hxi ⊢
    intro hzero
    apply hxi
    simp [hzero]
  have hphiCont : Continuous phi := by
    dsimp [phi]
    exact Complex.continuous_ofReal.comp
      (aux_standardBumpFinite_tendstoUniformly.continuous
        (Filter.Frequently.of_forall fun n => aux_continuous_standardBumpFinite n))
  have hphiInt : Integrable phi := by
    change Integrable (fun x : ℝ => (standardBump x : ℂ))
    exact aux_integrable_standardBump.ofReal
  have hInv : FourierTransformInv.fourierInv hat = phi := by
    dsimp [hat]
    exact hphiCont.fourierInv_fourier_eq hphiInt hhatInt
  have hderiv (z : ℝ) : iteratedDeriv m phi z =
      FourierTransformInv.fourierInv g z := by
    rw [← hInv]
    simpa only [g] using aux_iteratedDeriv_fourierInv m hat hmom z
  have hgSupp : tsupport g ⊆ Set.Icc (-1 : ℝ) 1 := by
    change tsupport (fun xi : ℝ =>
      (2 * Real.pi * Complex.I * (xi : ℂ)) ^ m * hat xi) ⊆ Set.Icc (-1 : ℝ) 1
    exact tsupport_mul_subset_right.trans hhatSupp
  have hgCont : ContDiff ℝ N g := by
    simpa only [g, hat, phi] using hcont
  have hgProfile : ∀ k : ℕ, k ≤ N → ∀ xi : ℝ,
      ‖iteratedDeriv k g xi‖ ≤ C_standardBumpPropertiesTilde m N := by
    simpa only [g, hat, phi] using hprofile
  rw [show (fun x : ℝ => (standardBump x : ℂ)) = phi by rfl]
  by_cases hN : N = 0
  · subst N
    have hC : 0 ≤ C_standardBumpPropertiesTilde m 0 := by
      rw [C_standardBumpPropertiesTilde]
      positivity
    calc
      ‖iteratedDeriv m phi x‖ = ‖FourierTransformInv.fourierInv g x‖ := by
        rw [hderiv]
      _ ≤ (2 : ℝ) ^ (0 + 2) * C_standardBumpPropertiesTilde m 0 *
          bracketBump x ^ (0 : ℕ) :=
        aux_fourierProfile_decay_zero g (C_standardBumpPropertiesTilde m 0) hC hgSupp
          (by intro xi; exact hgProfile 0 zero_le xi) x
      _ = C_standardBumpProperties m 0 * bracketBump x ^ (0 : ℕ) := by
        rw [show (2 : ℝ) ^ (0 + 2) * C_standardBumpPropertiesTilde m 0 =
          C_standardBumpProperties m 0 by
          rw [C_standardBumpPropertiesTilde, C_standardBumpProperties, ← pow_add]
          congr 1
          omega]
  · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hC : 0 ≤ C_standardBumpPropertiesTilde m N := by
      rw [C_standardBumpPropertiesTilde]
      positivity
    calc
      ‖iteratedDeriv m phi x‖ = ‖FourierTransformInv.fourierInv g x‖ := by
        rw [hderiv]
      _ ≤ (2 : ℝ) ^ (N + 2) * C_standardBumpPropertiesTilde m N *
          bracketBump x ^ N :=
        aux_fourierProfile_decay_pos N hNpos g (C_standardBumpPropertiesTilde m N) hC hgCont hgSupp
          hgProfile x
      _ = C_standardBumpProperties m N * bracketBump x ^ N := by
        rw [show (2 : ℝ) ^ (N + 2) * C_standardBumpPropertiesTilde m N =
          C_standardBumpProperties m N by
          rw [C_standardBumpPropertiesTilde, C_standardBumpProperties, ← pow_add]
          congr 1
          omega]

/--
\begin{proposition}[standard bump]\label{standard bump properties}
It satisfies for every $m,N\in\N$,
\begin{equation}
    \label{Phi_derbound}
    \|  (\widehat{\Phi^{(m)}})^{(N)}  \|_\infty \le \tilde{C}_{\ref{standard bump properties},m,N}.
\end{equation}
\end{proposition}
-/
theorem standardBumpProperties_fourierDerivativeEstimate (m N : ℕ) :
    eLpNorm (iteratedDeriv N
      (fun ξ : ℝ => (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ m *
        FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) ξ)) ⊤ volume ≤
      ENNReal.ofReal (C_standardBumpPropertiesTilde m N) := by
  have hpoint : ∀ ξ : ℝ,
      ‖iteratedDeriv N
        (fun u : ℝ => (2 * Real.pi * Complex.I * (u : ℂ)) ^ m *
          FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) u) ξ‖ ≤
        C_standardBumpPropertiesTilde m N := by
    intro ξ
    by_cases hN : N ≤ 2
    · exact aux_standardBumpMultiplier_iteratedDeriv_le_low m N hN ξ
    · exact aux_standardBumpMultiplier_iteratedDeriv_le_high m N (by omega) ξ
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hpoint)

/--
\begin{proposition}[standard bump]\label{standard bump properties}
For every $m,N\in\N$ and every $x\in\R$,
\begin{equation}\label{auto:standard-bump-derivative-decay}
|\Phi^{(m)}(x)| \le C_{\ref{standard bump properties},m,N} \langle x\rangle^N.
\end{equation}
\end{proposition}
-/
theorem standardBumpProperties_derivativeDecay (m N : ℕ) (x : ℝ) :
    ‖iteratedDeriv m (fun y : ℝ => (standardBump y : ℂ)) x‖ ≤
      C_standardBumpProperties m N * bracketBump x ^ N := by
  apply aux_standardBump_iteratedDeriv_decay_of_profile m N
  · apply
      ((aux_standardBumpMultiplier_contDiff m).mul
        aux_standardBumpComplex_fourier_contDiff).of_le
    exact WithTop.coe_le_coe.mpr le_top
  · intro k hk ξ
    calc
      ‖iteratedDeriv k
          (fun u : ℝ => (2 * Real.pi * Complex.I * (u : ℂ)) ^ m *
            FourierTransform.fourier (fun y : ℝ => (standardBump y : ℂ)) u) ξ‖ ≤
          C_standardBumpPropertiesTilde m k := by
            by_cases hk' : k ≤ 2
            · exact aux_standardBumpMultiplier_iteratedDeriv_le_low m k hk' ξ
            · exact aux_standardBumpMultiplier_iteratedDeriv_le_high m k (by omega) ξ
      _ ≤ C_standardBumpPropertiesTilde m N :=
        aux_C_standardBumpPropertiesTilde_mono m k N hk

/--
\begin{proposition}[standard bump]\label{standard bump properties}\using{lem:smoothdecay2}
The limit $\lim_{l\to \infty} \Phi_l$ exists in $L^\infty$  and $L^1$ sense and is a Schwartz function $\Phi$
whose Fourier transform takes values in $[0,1]$, is supported in $[-1,1]$, and constant $1$
on $[-1/2,1/2]$.

It satisfies for every $m,N\in\N$ and every $x\in\R$,
\begin{equation}
    \label{Phi_derbound}
    \|  (\widehat{\Phi^{(m)}})^{(N)}  \|_\infty \le \tilde{C}_{\ref{standard bump properties},m,N}
\end{equation}
and
\begin{equation}\label{auto:standard-bump-derivative-decay} |\Phi^{(m)}(x)| \le C_{\ref{standard bump properties},m,N} \langle x\rangle^N, \end{equation}
where $\tilde{C}_{\ref{standard bump properties},m,N}=2^{4m + 2N^2 + 5N}$ and $C_{\ref{standard bump properties},m,N}=2^{4m+2N^2+6N+2}.$
\end{proposition}
-/
theorem standardBumpProperties :
    Tendsto (fun n : ℕ => eLpNorm (standardBumpFinite n - standardBump) 1 volume)
      atTop (nhds 0) ∧
    Tendsto (fun n : ℕ => eLpNorm (standardBumpFinite n - standardBump) ⊤ volume)
      atTop (nhds 0) ∧
    (∃ Phi : SchwartzMap ℝ ℂ, ∀ x : ℝ, Phi x = (standardBump x : ℂ)) ∧
    (∀ ξ : ℝ, ∃ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 ∧
      FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) ξ = r) ∧
    Function.support (FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ))) ⊆
      Set.Icc (-1 : ℝ) 1 ∧
    (∀ ξ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
      FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) ξ = 1) ∧
    (∀ m N : ℕ, eLpNorm (iteratedDeriv N
      (fun ξ : ℝ => (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ m *
        FourierTransform.fourier (fun x : ℝ => (standardBump x : ℂ)) ξ)) ⊤ volume ≤
      ENNReal.ofReal (C_standardBumpPropertiesTilde m N)) ∧
    ∀ m N : ℕ, ∀ x : ℝ,
      ‖iteratedDeriv m (fun y : ℝ => (standardBump y : ℂ)) x‖ ≤
        C_standardBumpProperties m N * bracketBump x ^ N := by
  obtain ⟨hfourierRange, hfourierSupport, hfourierPlateau⟩ :=
    standardBumpProperties_fourierShape
  exact ⟨standardBumpProperties_l1Convergence,
    standardBumpProperties_linfConvergence,
    standardBumpProperties_schwartz,
    hfourierRange,
    hfourierSupport,
    hfourierPlateau,
    standardBumpProperties_fourierDerivativeEstimate,
    standardBumpProperties_derivativeDecay⟩

/--
\begin{proposition}[mean value bump estimate]\label{mean value bump estimate 2}\using{lem:smoothdecay2}
Let $N\in\mathbb N$ with $N\ge1$ and let $\rho$ be a $W_0(1)$ function with
$\widehat{\rho}$ supported in $[-1,1]$ and $\widehat{\rho}$ being $N$ times continuously differentiable.

Then for all $x,y\in\mathbb{R}$
\begin{equation}\label{auto:mean-value-bump-bound} |\rho(x+y)-\rho(x)| \le 2^N\max(2,(1+(2\pi)^{-1})^N)\max_{0\le \nu\le N}\|(2\pi)^{-\nu}\widehat{\rho}^{(\nu)}\|_\infty \min(1, 2\pi |y|) (\langle x+y\rangle^N + \langle x\rangle^N). \end{equation}
\end{proposition}
-/
theorem meanValueBumpEstimate (N : ℕ) (hN : 1 ≤ N) (rho rhoHat : ℝ → ℂ)
    (_hrhoW0 : MemW0 rho) (hrhoInv : rho = FourierTransformInv.fourierInv rhoHat)
    (hsupp : tsupport rhoHat ⊆ Set.Icc (-1) 1) (hrhoHat : ContDiff ℝ N rhoHat)
    (x y : ℝ) :
    ‖rho (x + y) - rho x‖ ≤
      C_meanValueBumpEstimate N *
        aux_maxUpTo
          (fun nu => (2 * Real.pi)⁻¹ ^ nu *
            sSup (Set.range fun xi : ℝ => ‖iteratedDeriv nu rhoHat xi‖)) N *
        min 1 (2 * Real.pi * |y|) *
        (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
  have hrhoHatSupport : HasCompactSupport rhoHat :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hsupp
  let P : ℝ := aux_maxUpTo
    (fun nu => (2 * Real.pi)⁻¹ ^ nu *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv nu rhoHat xi‖)) N
  let a : ℝ := 2 * Real.pi * |y|
  let V : ℝ := (volume (tsupport rhoHat)).toReal
  let R : ℝ := bracketBump (x + y) ^ N + bracketBump x ^ N
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hP : 0 ≤ P := by
    have hzero := aux_scaledIteratedDeriv_le_maxUpTo N 0 rhoHat hrhoHat
      hrhoHatSupport zero_le 0
    have hzero' : ‖rhoHat 0‖ ≤ P := by
      simpa only [P, pow_zero, one_mul, iteratedDeriv_zero] using hzero
    exact (norm_nonneg (rhoHat 0)).trans hzero'
  have hbracketNonneg (z : ℝ) : 0 ≤ bracketBump z := by
    rw [bracketBump]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact add_nonneg (pow_nonneg (hbracketNonneg (x + y)) N)
      (pow_nonneg (hbracketNonneg x) N)
  have hmeasure : volume (tsupport rhoHat) ≤ volume (Set.Icc (-1 : ℝ) 1) :=
    MeasureTheory.measure_mono hsupp
  have hIccFinite : volume (Set.Icc (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    norm_num
  have hV : V ≤ 2 := by
    dsimp [V]
    calc
      (volume (tsupport rhoHat)).toReal ≤ (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono hIccFinite hmeasure
      _ = 2 := by
        rw [Real.volume_Icc]
        norm_num
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    exact ENNReal.toReal_nonneg
  have hrhoHatInt : Integrable rhoHat :=
    hrhoHat.continuous.integrable_of_hasCompactSupport hrhoHatSupport
  let g : ℝ → ℂ := fun u => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)
  have hgCont : ContDiff ℝ N g := by
    change ContDiff ℝ N
      (rhoHat * fun u : ℝ => (Real.fourierChar (u * y)).1 - 1)
    exact hrhoHat.mul ((aux_fourierPhase_contDiff N y).sub contDiff_const)
  have hgSupport : HasCompactSupport g := by
    change HasCompactSupport
      (rhoHat * fun u : ℝ => (Real.fourierChar (u * y)).1 - 1)
    exact hrhoHatSupport.mul_right
  have hgsupp : tsupport g ⊆ Set.Icc (-1) 1 := by
    change tsupport (rhoHat * fun u : ℝ => (Real.fourierChar (u * y)).1 - 1) ⊆
      Set.Icc (-1) 1
    exact tsupport_mul_subset_left.trans hsupp
  let Vg : ℝ := (volume (tsupport g)).toReal
  have hmeasureg : volume (tsupport g) ≤ volume (Set.Icc (-1 : ℝ) 1) :=
    MeasureTheory.measure_mono hgsupp
  have hVg : Vg ≤ 2 := by
    dsimp [Vg]
    calc
      (volume (tsupport g)).toReal ≤ (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono hIccFinite hmeasureg
      _ = 2 := by
        rw [Real.volume_Icc]
        norm_num
  have hVgnonneg : 0 ≤ Vg := by
    dsimp [Vg]
    exact ENNReal.toReal_nonneg
  have hdiff : rho (x + y) - rho x = FourierTransformInv.fourierInv
      (fun u : ℝ => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)) x := by
    rw [hrhoInv]
    simpa only [g] using aux_fourierInv_translate_sub rhoHat hrhoHatInt x y
  have hrhoDecay := aux_smoothDecay2_pointwise N hN rhoHat hrhoHat hrhoHatSupport
  have hRhoProfile :
      max (sSup (Set.range fun xi : ℝ => ‖rhoHat xi‖))
        ((2 * Real.pi)⁻¹ ^ N *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N rhoHat xi‖)) ≤ P := by
    apply max_le
    · have hzero := aux_le_maxUpTo
        (fun nu => (2 * Real.pi)⁻¹ ^ nu *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv nu rhoHat xi‖))
        (show 0 ≤ N from zero_le)
      simpa only [P, pow_zero, one_mul, iteratedDeriv_zero] using hzero
    · simpa only [P] using aux_le_maxUpTo
        (fun nu => (2 * Real.pi)⁻¹ ^ nu *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv nu rhoHat xi‖))
        (show N ≤ N from le_rfl)
  have hCpow : (2 : ℝ) ^ (N + 1) ≤ C_meanValueBumpEstimate N := by
    rw [C_meanValueBumpEstimate]
    calc
      (2 : ℝ) ^ (N + 1) = (2 : ℝ) ^ N * 2 := by
        rw [pow_succ]
      _ ≤ (2 : ℝ) ^ N * max 2 ((1 + (2 * Real.pi)⁻¹) ^ N) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  change ‖rho (x + y) - rho x‖ ≤ C_meanValueBumpEstimate N * P * min 1 a * R
  by_cases hlarge : 1 ≤ a
  · have hleft : ‖FourierTransformInv.fourierInv rhoHat (x + y)‖ ≤
        (2 : ℝ) ^ N * P * V * bracketBump (x + y) ^ N := by
      calc
        ‖FourierTransformInv.fourierInv rhoHat (x + y)‖ ≤
            (2 : ℝ) ^ N *
              max (sSup (Set.range fun xi : ℝ => ‖rhoHat xi‖))
                ((2 * Real.pi)⁻¹ ^ N *
                  sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N rhoHat xi‖)) *
              V * bracketBump (x + y) ^ N := by
          simpa only [C_smoothDecay2, V] using hrhoDecay (x + y)
        _ = ((2 : ℝ) ^ N * V * bracketBump (x + y) ^ N) *
              max (sSup (Set.range fun xi : ℝ => ‖rhoHat xi‖))
                ((2 * Real.pi)⁻¹ ^ N *
                  sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N rhoHat xi‖)) := by ring
        _ ≤ ((2 : ℝ) ^ N * V * bracketBump (x + y) ^ N) * P :=
          mul_le_mul_of_nonneg_left hRhoProfile
            (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) N) hVnonneg)
              (pow_nonneg (hbracketNonneg (x + y)) N))
        _ = (2 : ℝ) ^ N * P * V * bracketBump (x + y) ^ N := by ring
    have hright : ‖FourierTransformInv.fourierInv rhoHat x‖ ≤
        (2 : ℝ) ^ N * P * V * bracketBump x ^ N := by
      calc
        ‖FourierTransformInv.fourierInv rhoHat x‖ ≤
            (2 : ℝ) ^ N *
              max (sSup (Set.range fun xi : ℝ => ‖rhoHat xi‖))
                ((2 * Real.pi)⁻¹ ^ N *
                  sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N rhoHat xi‖)) *
              V * bracketBump x ^ N := by
          simpa only [C_smoothDecay2, V] using hrhoDecay x
        _ = ((2 : ℝ) ^ N * V * bracketBump x ^ N) *
              max (sSup (Set.range fun xi : ℝ => ‖rhoHat xi‖))
                ((2 * Real.pi)⁻¹ ^ N *
                  sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N rhoHat xi‖)) := by ring
        _ ≤ ((2 : ℝ) ^ N * V * bracketBump x ^ N) * P :=
          mul_le_mul_of_nonneg_left hRhoProfile
            (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) N) hVnonneg)
              (pow_nonneg (hbracketNonneg x) N))
        _ = (2 : ℝ) ^ N * P * V * bracketBump x ^ N := by ring
    have hsum :
        ‖FourierTransformInv.fourierInv rhoHat (x + y) -
            FourierTransformInv.fourierInv rhoHat x‖ ≤
          (2 : ℝ) ^ (N + 1) * P * R := by
      calc
        ‖FourierTransformInv.fourierInv rhoHat (x + y) -
            FourierTransformInv.fourierInv rhoHat x‖ ≤
            ‖FourierTransformInv.fourierInv rhoHat (x + y)‖ +
              ‖FourierTransformInv.fourierInv rhoHat x‖ := norm_sub_le _ _
        _ ≤ (2 : ℝ) ^ N * P * V * bracketBump (x + y) ^ N +
              (2 : ℝ) ^ N * P * V * bracketBump x ^ N :=
          add_le_add hleft hright
        _ = ((2 : ℝ) ^ N * P) * V * R := by
          dsimp [R]
          ring
        _ ≤ ((2 : ℝ) ^ N * P) * 2 * R := by
          apply mul_le_mul_of_nonneg_right
          apply mul_le_mul_of_nonneg_left hV
          positivity
          exact hR
        _ = (2 : ℝ) ^ (N + 1) * P * R := by
          rw [pow_succ]
          ring
    rw [min_eq_left hlarge]
    calc
      ‖rho (x + y) - rho x‖ =
          ‖FourierTransformInv.fourierInv rhoHat (x + y) -
            FourierTransformInv.fourierInv rhoHat x‖ := by rw [hrhoInv]
      _ ≤ (2 : ℝ) ^ (N + 1) * P * R := hsum
      _ ≤ C_meanValueBumpEstimate N * P * R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCpow hP) hR
      _ = C_meanValueBumpEstimate N * P * 1 * R := by ring
  · have hsmall : a ≤ 1 := le_of_not_ge hlarge
    have hsmallNeg : 2 * Real.pi * |-y| ≤ 1 := by
      simpa only [abs_neg] using hsmall
    have hboundx := aux_small_modulated_inverse_bound N hN rhoHat hsupp hrhoHat x y
      (by simpa only [a] using hsmall)
    have hboundxy := aux_small_modulated_inverse_bound N hN rhoHat hsupp hrhoHat (x + y) (-y)
      hsmallNeg
    have hdiffNeg : rho x - rho (x + y) = FourierTransformInv.fourierInv
        (fun u : ℝ => rhoHat u * ((Real.fourierChar (u * (-y))).1 - 1)) (x + y) := by
      rw [hrhoInv]
      simpa only [add_neg_cancel_right] using
        aux_fourierInv_translate_sub rhoHat hrhoHatInt (x + y) (-y)
    have hnormx : ‖rho (x + y) - rho x‖ ≤
        (2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N * P * a *
          bracketBump x ^ N := by
      calc
        ‖rho (x + y) - rho x‖ = ‖FourierTransformInv.fourierInv
            (fun u : ℝ => rhoHat u * ((Real.fourierChar (u * y)).1 - 1)) x‖ :=
          congrArg norm hdiff
        _ ≤ (2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N * P * a *
            bracketBump x ^ N := by
          simpa only [P, a] using hboundx
    have hnormxy : ‖rho (x + y) - rho x‖ ≤
        (2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N * P * a *
          bracketBump (x + y) ^ N := by
      calc
        ‖rho (x + y) - rho x‖ = ‖-(rho x - rho (x + y))‖ := by
          congr 1
          ring
        _ = ‖rho x - rho (x + y)‖ := norm_neg _
        _ = ‖FourierTransformInv.fourierInv
            (fun u : ℝ => rhoHat u * ((Real.fourierChar (u * (-y))).1 - 1)) (x + y)‖ :=
          congrArg norm hdiffNeg
        _ ≤ (2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N * P * a *
            bracketBump (x + y) ^ N := by
          simpa only [P, a, abs_neg] using hboundxy
    have haverage : ‖rho (x + y) - rho x‖ ≤
        (2 : ℝ) ^ N * (1 + (2 * Real.pi)⁻¹) ^ N * P * a * R := by
      calc
        ‖rho (x + y) - rho x‖ =
            (‖rho (x + y) - rho x‖ + ‖rho (x + y) - rho x‖) / 2 := by ring
        _ ≤ (((2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N * P * a *
              bracketBump x ^ N) +
            ((2 : ℝ) ^ (N + 1) * (1 + (2 * Real.pi)⁻¹) ^ N * P * a *
              bracketBump (x + y) ^ N)) / 2 :=
          div_le_div_of_nonneg_right (add_le_add hnormx hnormxy) (by norm_num)
        _ = (2 : ℝ) ^ N * (1 + (2 * Real.pi)⁻¹) ^ N * P * a * R := by
          dsimp [R]
          rw [pow_succ]
          ring
    have hDle : (1 + (2 * Real.pi)⁻¹) ^ N ≤
        max 2 ((1 + (2 * Real.pi)⁻¹) ^ N) := le_max_right _ _
    have htail : 0 ≤ (2 : ℝ) ^ N * P * a * R := by positivity
    rw [min_eq_right hsmall]
    calc
      ‖rho (x + y) - rho x‖ ≤
          (2 : ℝ) ^ N * (1 + (2 * Real.pi)⁻¹) ^ N * P * a * R := haverage
      _ = ((2 : ℝ) ^ N * P * a * R) * (1 + (2 * Real.pi)⁻¹) ^ N := by ring
      _ ≤ ((2 : ℝ) ^ N * P * a * R) * max 2 ((1 + (2 * Real.pi)⁻¹) ^ N) :=
        mul_le_mul_of_nonneg_left hDle htail
      _ = C_meanValueBumpEstimate N * P * a * R := by
        rw [C_meanValueBumpEstimate]
        ring

/-- For source label `\ref{compare brackets}` and public theorem `compare_brackets`, this
supplies the unscaled natural-exponent comparison used by `aux_compareBracketsNat`. -/
theorem aux_compareBracketsNat_base (N : ℕ) {lam mu x y : ℝ}
    (hlam : 0 < lam) (hmu : 0 < mu) (hlammu : lam ≤ mu)
    (hxy : lam * |y| ≤ mu * |x|) :
    mu⁻¹ ^ N * bracketBump x ^ N ≤ lam⁻¹ ^ N * bracketBump y ^ N := by
  have hden : lam * (1 + |y|) ≤ mu * (1 + |x|) := by
    calc
      lam * (1 + |y|) = lam + lam * |y| := by ring
      _ ≤ mu + mu * |x| := add_le_add hlammu hxy
      _ = mu * (1 + |x|) := by ring
  have hleft : 0 < lam * (1 + |y|) := mul_pos hlam (by positivity)
  have hbase : (mu * (1 + |x|))⁻¹ ≤ (lam * (1 + |y|))⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hleft hden
  have hp : (mu * (1 + |x|))⁻¹ ^ N ≤ (lam * (1 + |y|))⁻¹ ^ N :=
    pow_le_pow_left₀ (by positivity) hbase N
  calc
    mu⁻¹ ^ N * bracketBump x ^ N = (mu * (1 + |x|))⁻¹ ^ N := by
      rw [bracketBump, ← mul_pow]
      congr 1
      field_simp
    _ ≤ (lam * (1 + |y|))⁻¹ ^ N := hp
    _ = lam⁻¹ ^ N * bracketBump y ^ N := by
      rw [bracketBump, ← mul_pow]
      congr 1
      field_simp

/-- For source label `\ref{compare brackets}` and public theorem `compare_brackets`, this
supplies the natural-exponent specialization needed by the subsequent auxiliary estimates. -/
theorem aux_compareBracketsNat (N : ℕ) {lam mu s x y : ℝ}
    (hs : 0 < s) (_hN : 0 < N) (hlam : 0 < lam) (hlammu : lam ≤ mu)
    (hmuone : 1 ≤ mu) (hxy : lam * |y| ≤ mu * |x|) :
    mu⁻¹ ^ N * scaledBracketBump N s x ≤ lam⁻¹ ^ N * scaledBracketBump N s y := by
  have hmu : 0 < mu := lt_of_lt_of_le zero_lt_one hmuone
  have hxy' : lam * |s⁻¹ * y| ≤ mu * |s⁻¹ * x| := by
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hs]
    calc
      lam * (s⁻¹ * |y|) = s⁻¹ * (lam * |y|) := by ring
      _ ≤ s⁻¹ * (mu * |x|) :=
        mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr hs.le)
      _ = mu * (s⁻¹ * |x|) := by ring
  have hbase := aux_compareBracketsNat_base N hlam hmu hlammu hxy'
  unfold scaledBracketBump
  calc
    mu⁻¹ ^ N * (s⁻¹ * bracketBump (s⁻¹ * x) ^ N) =
        s⁻¹ * (mu⁻¹ ^ N * bracketBump (s⁻¹ * x) ^ N) := by ring
    _ ≤ s⁻¹ * (lam⁻¹ ^ N * bracketBump (s⁻¹ * y) ^ N) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hs.le)
    _ = lam⁻¹ ^ N * (s⁻¹ * bracketBump (s⁻¹ * y) ^ N) := by ring

/-- For source label `\ref{compare brackets}` and public theorem `compare_brackets`, this
reduces the real-exponent comparison to antitonicity of `Real.rpow` at a nonpositive exponent. -/
theorem aux_compareBracketsReal_base (N : ℝ) {lam mu x y : ℝ}
    (hN : 0 < N) (hlam : 0 < lam) (hmu : 0 < mu) (hlammu : lam ≤ mu)
    (hxy : lam * |y| ≤ mu * |x|) :
    Real.rpow mu (-N) * Real.rpow (1 + |x|) (-N) ≤
      Real.rpow lam (-N) * Real.rpow (1 + |y|) (-N) := by
  have hden : lam * (1 + |y|) ≤ mu * (1 + |x|) := by
    calc
      lam * (1 + |y|) = lam + lam * |y| := by ring
      _ ≤ mu + mu * |x| := add_le_add hlammu hxy
      _ = mu * (1 + |x|) := by ring
  have hleft : 0 < lam * (1 + |y|) := mul_pos hlam (by positivity)
  have hpow : Real.rpow (mu * (1 + |x|)) (-N) ≤
      Real.rpow (lam * (1 + |y|)) (-N) :=
    Real.rpow_le_rpow_of_nonpos hleft hden (by linarith)
  change (mu * (1 + |x|)) ^ (-N) ≤ (lam * (1 + |y|)) ^ (-N) at hpow
  rw [Real.mul_rpow hmu.le (by positivity),
    Real.mul_rpow hlam.le (by positivity)] at hpow
  exact hpow

/--
\begin{proposition}\label{compare brackets}
Let $0<\lambda\le\mu$ with $1\le\mu$ and let $\lambda|y|\le\mu|x|$. Then for every $s,N>0$,
\begin{equation}\label{compare brackets estimate}
\mu^{-N}\langle x\rangle_{(s)}^N\le\lambda^{-N}\langle y\rangle_{(s)}^N.
\end{equation}
\end{proposition}
-/
theorem compare_brackets (N : ℝ) {lam mu s x y : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hlam : 0 < lam) (hlammu : lam ≤ mu)
    (hmuone : 1 ≤ mu) (hxy : lam * |y| ≤ mu * |x|) :
    Real.rpow mu (-N) * scaledBracketBumpReal N s x ≤
      Real.rpow lam (-N) * scaledBracketBumpReal N s y := by
  have hmu : 0 < mu := lt_of_lt_of_le zero_lt_one hmuone
  have hxy' : lam * |s⁻¹ * y| ≤ mu * |s⁻¹ * x| := by
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hs]
    calc
      lam * (s⁻¹ * |y|) = s⁻¹ * (lam * |y|) := by ring
      _ ≤ s⁻¹ * (mu * |x|) :=
        mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr hs.le)
      _ = mu * (s⁻¹ * |x|) := by ring
  have hbase := aux_compareBracketsReal_base N hN hlam hmu hlammu hxy'
  unfold scaledBracketBumpReal
  calc
    Real.rpow mu (-N) * (s⁻¹ * Real.rpow (1 + |s⁻¹ * x|) (-N)) =
        s⁻¹ * (Real.rpow mu (-N) * Real.rpow (1 + |s⁻¹ * x|) (-N)) := by ring
    _ ≤ s⁻¹ * (Real.rpow lam (-N) * Real.rpow (1 + |s⁻¹ * y|) (-N)) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hs.le)
    _ = Real.rpow lam (-N) * (s⁻¹ * Real.rpow (1 + |s⁻¹ * y|) (-N)) := by ring

/-- Source label `\ref{bump triangle}`; auxiliary for `bump_triangle`. -/
theorem aux_scaledBracketBump_nonneg (N : ℕ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 ≤ scaledBracketBump N s x := by
  unfold scaledBracketBump
  positivity

/-- Source label `\ref{bump triangle}`; auxiliary for `bump_triangle`. -/
theorem aux_scaledBracketBump_le_of_abs_le_mul (N : ℕ) {A s u w : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hA : 0 < A) (h : |w| ≤ A * |u|) :
    scaledBracketBump N s u ≤
      max (A ^ N) (A⁻¹ ^ N) * scaledBracketBump N s w := by
  by_cases hAone : 1 ≤ A
  · have hcomp := aux_compareBracketsNat (x := u) (y := w) N hs hN
      (by norm_num : 0 < (1 : ℝ)) hAone hAone (by simpa using h)
    have hmul := mul_le_mul_of_nonneg_left hcomp (pow_nonneg hA.le N)
    have hEq : A ^ N * (A⁻¹ ^ N * scaledBracketBump N s u) =
        scaledBracketBump N s u := by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hA), one_pow, one_mul]
    rw [hEq] at hmul
    calc
      scaledBracketBump N s u ≤ A ^ N * scaledBracketBump N s w := by
        simpa [one_mul] using hmul
      _ ≤ max (A ^ N) (A⁻¹ ^ N) * scaledBracketBump N s w := by
        apply mul_le_mul_of_nonneg_right (le_max_left _ _)
        exact aux_scaledBracketBump_nonneg N hs w
  · have hAone' : A ≤ 1 := le_of_not_ge hAone
    have hcond : A * |w| ≤ 1 * |u| := by
      calc
        A * |w| ≤ A * (A * |u|) :=
          mul_le_mul_of_nonneg_left h hA.le
        _ = A ^ 2 * |u| := by ring
        _ ≤ 1 * |u| := by
          gcongr
          nlinarith
    have hcomp := aux_compareBracketsNat (x := u) (y := w) N hs hN hA hAone'
      (by norm_num : 1 ≤ (1 : ℝ)) hcond
    calc
      scaledBracketBump N s u ≤ A⁻¹ ^ N * scaledBracketBump N s w := by
        simpa using hcomp
      _ ≤ max (A ^ N) (A⁻¹ ^ N) * scaledBracketBump N s w := by
        apply mul_le_mul_of_nonneg_right (le_max_right _ _)
        exact aux_scaledBracketBump_nonneg N hs w

/-- Source label `\ref{Gaussian domination}`; the explicit constant used by the public theorem
`gaussianDomination`. -/
def C_gaussianDomination : ℝ := Real.exp Real.pi

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this records nonnegativity of a
rescaled Gaussian at a positive scale. -/
theorem aux_gaussianDomination_gaussianRescale_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ gaussianRescale t x := by
  unfold gaussianRescale
  exact mul_nonneg (inv_nonneg.mpr ht.le) (aux_gaussian_pos _).le

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this bounds a rescaled Gaussian
by the reciprocal of its positive scale. -/
theorem aux_gaussianDomination_gaussianRescale_le_inv {t : ℝ} (ht : 0 < t) (x : ℝ) :
    gaussianRescale t x ≤ t⁻¹ := by
  unfold gaussianRescale
  calc
    t⁻¹ * Gaussians.gaussian (t⁻¹ * x) ≤ t⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (aux_gaussian_le_one _) (inv_nonneg.mpr ht.le)
    _ = t⁻¹ := by ring

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this supplies convergence of the
Gaussian majorant series. -/
theorem aux_gaussianDomination_weight_summable (N s x : ℝ) (hN : 1 < N) (hs : 0 < s) :
    Summable (fun m : ℕ =>
      Real.rpow 2 ((1 - N) * (m : ℝ)) * gaussianRescale ((2 : ℝ) ^ m * s) x) := by
  let r : ℝ := Real.rpow 2 (1 - N)
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable (fun m : ℕ => r ^ m) :=
    summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos hrpos]
      exact hrlt)
  have hmajor : Summable (fun m : ℕ => s⁻¹ * r ^ m) := hgeom.mul_left _
  apply Summable.of_nonneg_of_le (f := fun m : ℕ => s⁻¹ * r ^ m)
  · intro m
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianDomination_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hs) x)
  · intro m
    have hscale : s ≤ (2 : ℝ) ^ m * s := by
      rw [← one_mul s]
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hs.le)
    have hscalePos : 0 < (2 : ℝ) ^ m * s := mul_pos (pow_pos (by norm_num) _) hs
    have hinv : ((2 : ℝ) ^ m * s)⁻¹ ≤ s⁻¹ := (inv_le_inv₀ hscalePos hs).2 hscale
    calc
      Real.rpow 2 ((1 - N) * (m : ℝ)) * gaussianRescale ((2 : ℝ) ^ m * s) x ≤
          Real.rpow 2 ((1 - N) * (m : ℝ)) * s⁻¹ :=
        mul_le_mul_of_nonneg_left
          ((aux_gaussianDomination_gaussianRescale_le_inv hscalePos x).trans hinv)
          (Real.rpow_nonneg (by norm_num) _)
      _ = s⁻¹ * r ^ m := by
        dsimp [r]
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        ring
  · exact hmajor

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this produces a dyadic scale
above a prescribed real number. -/
theorem aux_gaussianDomination_exists_dyadic_upper (y : ℝ) :
    ∃ m : ℕ, y ≤ (2 : ℝ) ^ m := by
  have h_eventually : ∀ᶠ m : ℕ in atTop, y ≤ (2 : ℝ) ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop y
  exact h_eventually.exists

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this chooses the first dyadic
scale above a prescribed real number. -/
theorem aux_gaussianDomination_dyadic_selector (y : ℝ) :
    ∃ m : ℕ, y ≤ (2 : ℝ) ^ m ∧ (m = 0 ∨ (2 : ℝ) ^ (m - 1) < y) := by
  let m : ℕ := Nat.find (aux_gaussianDomination_exists_dyadic_upper y)
  have hm : y ≤ (2 : ℝ) ^ m := Nat.find_spec (aux_gaussianDomination_exists_dyadic_upper y)
  refine ⟨m, hm, ?_⟩
  by_cases hm0 : m = 0
  · exact Or.inl hm0
  · right
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    apply lt_of_not_ge
    intro hle
    have hmin : m ≤ m - 1 := Nat.find_min' (aux_gaussianDomination_exists_dyadic_upper y) hle
    exact (Nat.not_le_of_gt (Nat.sub_lt hmpos (by norm_num))) hmin

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this gives the Gaussian lower
bound on the unit interval needed at the selected dyadic scale. -/
theorem aux_gaussianDomination_exp_mul_gaussian_ge_one {z : ℝ} (hz : |z| ≤ 1) :
    1 ≤ Real.exp Real.pi * Gaussians.gaussian z := by
  have hsqabs : |z| ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg z) (by norm_num)).2 hz
  have hsq : z ^ 2 ≤ 1 := by
    nlinarith [sq_abs z]
  have harg : 0 ≤ Real.pi + (-Real.pi * z ^ 2) := by
    nlinarith [Real.pi_pos]
  calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (Real.pi + (-Real.pi * z ^ 2)) := Real.exp_le_exp.mpr harg
    _ = Real.exp Real.pi * Gaussians.gaussian z := by
      rw [Real.exp_add]
      rfl

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this turns the unit-interval
Gaussian lower bound into a lower bound for a rescaled Gaussian. -/
theorem aux_gaussianDomination_inv_le_exp_mul_gaussianRescale {t x : ℝ} (ht : 0 < t)
    (habs : |t⁻¹ * x| ≤ 1) :
    t⁻¹ ≤ Real.exp Real.pi * gaussianRescale t x := by
  have hbase := aux_gaussianDomination_exp_mul_gaussian_ge_one habs
  have hinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  unfold gaussianRescale
  calc
    t⁻¹ = t⁻¹ * 1 := by ring
    _ ≤ t⁻¹ * (Real.exp Real.pi * Gaussians.gaussian (t⁻¹ * x)) :=
      mul_le_mul_of_nonneg_left hbase hinv
    _ = Real.exp Real.pi * (t⁻¹ * Gaussians.gaussian (t⁻¹ * x)) := by ring

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this is the exponent algebra
that identifies the selected dyadic summand. -/
theorem aux_gaussianDomination_dyadic_weight_identity (N : ℝ) (m : ℕ) :
    Real.rpow 2 N * Real.rpow 2 ((1 - N) * (m : ℝ)) * ((2 : ℝ) ^ m)⁻¹ =
      Real.rpow 2 (-N * ((m : ℝ) - 1)) := by
  have hneg : ((2 : ℝ) ^ m)⁻¹ = Real.rpow 2 (-(m : ℝ)) := by
    simp only [← Real.rpow_natCast]
    exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (m : ℝ)).symm
  rw [hneg]
  have hfirst : Real.rpow 2 N * Real.rpow 2 ((1 - N) * (m : ℝ)) =
      Real.rpow 2 (N + (1 - N) * (m : ℝ)) :=
    (Real.rpow_add (x := (2 : ℝ)) (by norm_num) N ((1 - N) * (m : ℝ))).symm
  rw [hfirst]
  have hsecond : Real.rpow 2 (N + (1 - N) * (m : ℝ)) * Real.rpow 2 (-(m : ℝ)) =
      Real.rpow 2 (N + (1 - N) * (m : ℝ) + -(m : ℝ)) :=
    (Real.rpow_add (x := (2 : ℝ)) (by norm_num) _ _).symm
  rw [hsecond]
  congr 1
  ring

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this puts the argument of the
selected rescaled Gaussian in the unit interval. -/
theorem aux_gaussianDomination_dyadic_argument_bound (s x : ℝ) (hs : 0 < s) (m : ℕ)
    (hy : |s⁻¹ * x| ≤ (2 : ℝ) ^ m) :
    |(((2 : ℝ) ^ m * s)⁻¹ * x)| ≤ 1 := by
  have hp : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) _
  have hrewrite : ((2 : ℝ) ^ m * s)⁻¹ * x = ((2 : ℝ) ^ m)⁻¹ * (s⁻¹ * x) := by
    field_simp [hp.ne', hs.ne']
  rw [hrewrite, abs_mul, abs_inv, abs_of_pos hp]
  calc
    ((2 : ℝ) ^ m)⁻¹ * |s⁻¹ * x| ≤ ((2 : ℝ) ^ m)⁻¹ * (2 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this bounds the bracket decay
by the dyadic power associated with a nonzero selected index. -/
theorem aux_gaussianDomination_bracket_decay_at_dyadic (N y : ℝ) (hN : 1 < N) (m : ℕ)
    (hm : 0 < m) (hlow : (2 : ℝ) ^ (m - 1) < y) :
    (1 + y) ^ (-N) ≤ Real.rpow 2 (-N * ((m : ℝ) - 1)) := by
  have hp : 0 < (2 : ℝ) ^ (m - 1) := pow_pos (by norm_num) _
  have hbase : (2 : ℝ) ^ (m - 1) ≤ 1 + y := by linarith
  have hraw : (1 + y) ^ (-N) ≤ ((2 : ℝ) ^ (m - 1)) ^ (-N) :=
    Real.rpow_le_rpow_of_nonpos hp hbase (by linarith)
  calc
    (1 + y) ^ (-N) ≤ ((2 : ℝ) ^ (m - 1)) ^ (-N) := hraw
    _ = Real.rpow 2 (-N * ((m : ℝ) - 1)) := by
      have hmone : 1 ≤ m := Nat.succ_le_iff.mpr hm
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [Nat.cast_sub hmone]
      norm_num
      congr 1
      ring

/-- For `\ref{Gaussian domination}` and `gaussianDomination`, this shows that the single
dyadic summand selected from the size of the input dominates the bracket bump. -/
theorem aux_gaussianDomination_one_term_bound (N s x : ℝ) (hN : 1 < N) (hs : 0 < s)
    (m : ℕ) (hupper : |s⁻¹ * x| ≤ (2 : ℝ) ^ m)
    (hbranch : m = 0 ∨ (2 : ℝ) ^ (m - 1) < |s⁻¹ * x|) :
    scaledBracketBumpReal N s x ≤
      Real.exp Real.pi * Real.rpow 2 N *
        (Real.rpow 2 ((1 - N) * (m : ℝ)) * gaussianRescale ((2 : ℝ) ^ m * s) x) := by
  have hsInv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hpowN : 1 ≤ Real.rpow 2 N := Real.one_le_rpow (by norm_num) (by linarith)
  have ht : 0 < (2 : ℝ) ^ m * s := mul_pos (pow_pos (by norm_num) _) hs
  have harg : |(((2 : ℝ) ^ m * s)⁻¹ * x)| ≤ 1 :=
    aux_gaussianDomination_dyadic_argument_bound s x hs m hupper
  have hgauss : ((2 : ℝ) ^ m * s)⁻¹ ≤
      Real.exp Real.pi * gaussianRescale ((2 : ℝ) ^ m * s) x :=
    aux_gaussianDomination_inv_le_exp_mul_gaussianRescale ht harg
  rcases hbranch with rfl | hlow
  · have hbase : 1 ≤ 1 + |s⁻¹ * x| := by linarith [abs_nonneg (s⁻¹ * x)]
    have hbracket : (1 + |s⁻¹ * x|) ^ (-N) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    unfold scaledBracketBumpReal
    simp only [Nat.cast_zero, mul_zero, pow_zero, one_mul]
    calc
      s⁻¹ * (1 + |s⁻¹ * x|) ^ (-N) ≤ s⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hbracket hsInv
      _ = s⁻¹ := by ring
      _ = 1 * s⁻¹ := by ring
      _ ≤ Real.rpow 2 N * s⁻¹ := mul_le_mul_of_nonneg_right hpowN hsInv
      _ ≤ Real.rpow 2 N * (Real.exp Real.pi * gaussianRescale s x) :=
        mul_le_mul_of_nonneg_left (by simpa using hgauss) (Real.rpow_nonneg (by norm_num) _)
      _ = Real.exp Real.pi * Real.rpow 2 N * gaussianRescale s x := by ring
      _ = Real.exp Real.pi * Real.rpow 2 N *
          (Real.rpow 2 (0 : ℝ) * gaussianRescale s x) := by
        norm_num [Real.rpow_zero]
  · have hm : 0 < m := by
      by_contra hm0
      have : m = 0 := Nat.eq_zero_of_not_pos hm0
      subst m
      norm_num at hlow hupper
      linarith
    have hbracket : (1 + |s⁻¹ * x|) ^ (-N) ≤
        Real.rpow 2 (-N * ((m : ℝ) - 1)) :=
      aux_gaussianDomination_bracket_decay_at_dyadic N |s⁻¹ * x| hN m hm hlow
    have hfactor : 0 ≤ Real.rpow 2 N * Real.rpow 2 ((1 - N) * (m : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    have hidentity := aux_gaussianDomination_dyadic_weight_identity N m
    unfold scaledBracketBumpReal
    calc
      s⁻¹ * (1 + |s⁻¹ * x|) ^ (-N) ≤
          s⁻¹ * Real.rpow 2 (-N * ((m : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hbracket hsInv
      _ = (Real.rpow 2 N * Real.rpow 2 ((1 - N) * (m : ℝ)) * ((2 : ℝ) ^ m)⁻¹) * s⁻¹ := by
        rw [hidentity]
        ring
      _ = (Real.rpow 2 N * Real.rpow 2 ((1 - N) * (m : ℝ))) *
          (((2 : ℝ) ^ m * s)⁻¹) := by
        field_simp [hs.ne', (pow_pos (by norm_num : (0 : ℝ) < 2) m).ne']
      _ ≤ (Real.rpow 2 N * Real.rpow 2 ((1 - N) * (m : ℝ))) *
          (Real.exp Real.pi * gaussianRescale ((2 : ℝ) ^ m * s) x) :=
        mul_le_mul_of_nonneg_left hgauss hfactor
      _ = Real.exp Real.pi * Real.rpow 2 N *
          (Real.rpow 2 ((1 - N) * (m : ℝ)) * gaussianRescale ((2 : ℝ) ^ m * s) x) := by
        ring

/--
\begin{proposition}[Gaussian domination]\label{Gaussian domination}
    Let
    $N,s\in\R$, $N>1$, and $s>0$. Then
\begin{equation}\label{auto:bracket-Gaussian-domination}
    \left< x\right>^{N}_{(s)}  \le C_{\ref{Gaussian domination}} 2^N   \sum_{m\in {\N}}  2^{(1-N)m} \g_{(2^ms)}(x),
\end{equation}
where $C_{\ref{Gaussian domination}}=e^\pi$.
\end{proposition}
-/
theorem gaussianDomination (N s x : ℝ) (hN : 1 < N) (hs : 0 < s) :
    scaledBracketBumpReal N s x ≤
      C_gaussianDomination * Real.rpow 2 N *
        ∑' m : ℕ, Real.rpow 2 ((1 - N) * (m : ℝ)) *
          gaussianRescale ((2 : ℝ) ^ m * s) x := by
  let f : ℕ → ℝ := fun m =>
    Real.rpow 2 ((1 - N) * (m : ℝ)) * gaussianRescale ((2 : ℝ) ^ m * s) x
  have hsum : Summable f := by
    simpa only [f] using aux_gaussianDomination_weight_summable N s x hN hs
  have hnonneg (m : ℕ) : 0 ≤ f m := by
    dsimp [f]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (aux_gaussianDomination_gaussianRescale_nonneg (mul_pos (pow_pos (by norm_num) _) hs) x)
  obtain ⟨m, hmupper, hmbranch⟩ := aux_gaussianDomination_dyadic_selector |s⁻¹ * x|
  have hterm : scaledBracketBumpReal N s x ≤
      Real.exp Real.pi * Real.rpow 2 N * f m := by
    dsimp [f]
    exact aux_gaussianDomination_one_term_bound N s x hN hs m hmupper hmbranch
  have hle : f m ≤ ∑' j : ℕ, f j :=
    hsum.le_tsum m (fun j _ => hnonneg j)
  have hcoeff : 0 ≤ Real.exp Real.pi * Real.rpow 2 N :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by norm_num) _)
  rw [C_gaussianDomination]
  calc
    scaledBracketBumpReal N s x ≤ Real.exp Real.pi * Real.rpow 2 N * f m := hterm
    _ ≤ Real.exp Real.pi * Real.rpow 2 N * ∑' j : ℕ, f j :=
      mul_le_mul_of_nonneg_left hle hcoeff
    _ = Real.exp Real.pi * Real.rpow 2 N *
        ∑' m : ℕ, Real.rpow 2 ((1 - N) * (m : ℝ)) *
          gaussianRescale ((2 : ℝ) ^ m * s) x := by rfl

/-- Source label `\ref{two bump estimate}`; the explicit constant used by the public theorem
`twoBumpEstimate`. -/
def C_twoBumpEstimate (n₀ n₁ : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 + min n₀ n₁) * (1 + (min n₀ n₁ - 1)⁻¹)

/-- Source label `\ref{two bump estimate}`; auxiliary for `twoBumpEstimate`, recording the
only specialization of its final constant claim used later. -/
theorem aux_twoBumpEstimate_two_two : C_twoBumpEstimate 2 2 = 16 := by
  norm_num [C_twoBumpEstimate, Real.rpow_natCast]

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
evaluates the one-sided integral of the unscaled real-exponent bracket profile. -/
theorem aux_twoBump_halfIntegral (n : ℝ) (hn : 1 < n) :
    ∫ x : ℝ in Set.Ioi 0, (1 + x) ^ (-n) = 1 / (n - 1) := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (t + 1) ^ ((-n) + 1) / ((-n) + 1))
        ((x + 1) ^ (-n)) x := by
    intro x hx
    convert! (((hasDerivAt_id x).add_const 1).rpow_const _).div_const _ using 1
    · simp [show (-n) + 1 ≠ 0 by linarith]
    · left
      have hpos : 0 < x + 1 := by linarith [Set.mem_Ici.mp hx]
      simpa using hpos.ne'
  have ht : Tendsto (fun t : ℝ => (t + 1) ^ ((-n) + 1) / ((-n) + 1))
      atTop (nhds (0 / ((-n) + 1))) := by
    rw [show (-n) + 1 = -(-((-n) + 1)) by ring]
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < -((-n) + 1))).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_id) |>.div_const _
  have hmain : ∫ x : ℝ in Set.Ioi 0, (x + 1) ^ (-n) = 1 / (n - 1) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd
      (integrableOn_add_rpow_Ioi_of_lt (a := -n) (m := 1) (c := 0) (by linarith) (by norm_num)) ht]
    simp only [zero_div, zero_add, Real.one_rpow, zero_sub]
    have h : -n + 1 = -(n - 1) := by ring
    rw [h, div_neg]
    ring
  simpa [add_comm] using hmain

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
computes the mass of the unscaled bracket profile. -/
theorem aux_twoBump_baseIntegral (n : ℝ) (hn : 1 < n) :
    ∫ x : ℝ, (1 + |x|) ^ (-n) = 2 / (n - 1) := by
  have habs := integral_comp_abs (f := fun x : ℝ => (1 + x) ^ (-n))
  rw [aux_twoBump_halfIntegral n hn] at habs
  convert habs using 1 <;> ring

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
computes the mass of a translated and scaled bracket profile. -/
theorem aux_integral_scaledBracketBumpReal_eq (n s a : ℝ) (hn : 1 < n) (hs : 0 < s) :
    ∫ x : ℝ, scaledBracketBumpReal n s (a - x) = 2 / (n - 1) := by
  rw [integral_sub_left_eq_self (fun x : ℝ => scaledBracketBumpReal n s x) volume a]
  unfold scaledBracketBumpReal
  rw [integral_const_mul]
  change s⁻¹ * (∫ a : ℝ, (1 + |s⁻¹ * a|) ^ (-n)) = _
  have hscale := MeasureTheory.Measure.integral_comp_inv_mul_left
    (fun y : ℝ => (1 + |y|) ^ (-n)) s
  rw [hscale]
  rw [smul_eq_mul, abs_of_pos hs, aux_twoBump_baseIntegral n hn]
  field_simp

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
establishes integrability of the unscaled bracket profile. -/
theorem aux_twoBump_baseIntegrable (n : ℝ) (hn : 1 < n) :
    Integrable (fun x : ℝ => (1 + |x|) ^ (-n)) := by
  have hIoiRaw : IntegrableOn (fun x : ℝ => (x + 1) ^ (-n)) (Set.Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -n) (m := 1) (c := 0) (by linarith) (by norm_num)
  have hIoi : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-n)) (Set.Ioi 0) := by
    refine hIoiRaw.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change (x + 1) ^ (-n) = (1 + |x|) ^ (-n)
    rw [abs_of_pos (Set.mem_Ioi.mp hx)]
    congr 1
    ring
  have hIic : IntegrableOn (fun x : ℝ => (1 + |x|) ^ (-n)) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    have hset : (fun x : ℝ => -x) ⁻¹' Set.Iic 0 = Set.Ici 0 := by
      ext x
      simp
    rw [hset]
    change IntegrableOn (fun x : ℝ => (1 + |-x|) ^ (-n)) (Set.Ici 0)
    simp only [abs_neg]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hIoi
  simpa only [Set.Iic_union_Ioi, Measure.restrict_univ] using (hIic.union hIoi).integrable

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
establishes integrability of a scaled bracket profile. -/
theorem aux_integrable_scaledBracketBumpReal (n s : ℝ) (hn : 1 < n) (hs : 0 < s) :
    Integrable (fun x : ℝ => scaledBracketBumpReal n s x) := by
  unfold scaledBracketBumpReal
  change Integrable (fun x : ℝ => s⁻¹ * (1 + |s⁻¹ * x|) ^ (-n))
  have hcomp : Integrable (fun x : ℝ => (1 + |s⁻¹ * x|) ^ (-n)) :=
    (aux_twoBump_baseIntegrable n hn).comp_mul_left' (inv_ne_zero hs.ne')
  exact hcomp.const_mul s⁻¹

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
transports scaled-bracket integrability to a translated reflection. -/
theorem aux_integrable_scaledBracketBumpReal_translate (n s a : ℝ)
    (hn : 1 < n) (hs : 0 < s) :
    Integrable (fun x : ℝ => scaledBracketBumpReal n s (a - x)) := by
  exact (aux_integrable_scaledBracketBumpReal n s hn hs).comp_sub_left a

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this is
the weighted power estimate used after normalizing the two scales. -/
theorem aux_twoBump_denominator_power {A B r n D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r) (hr1 : r ≤ 1)
    (hn : 1 ≤ n) (hD : 0 ≤ D) (hDle : D ≤ A + r * B) :
    D ^ n ≤ 2 ^ (n - 1) * (A ^ n + r * B ^ n) := by
  calc
    D ^ n ≤ (A + r * B) ^ n := Real.rpow_le_rpow hD hDle (by linarith)
    _ ≤ 2 ^ (n - 1) * (A ^ n + (r * B) ^ n) := by
      have hnn := NNReal.rpow_add_le_mul_rpow_add_rpow
        ⟨A, hA⟩ ⟨r * B, mul_nonneg hr.le hB⟩ hn
      exact_mod_cast hnn
    _ = 2 ^ (n - 1) * (A ^ n + r ^ n * B ^ n) := by
      rw [Real.mul_rpow hr.le hB]
    _ ≤ 2 ^ (n - 1) * (A ^ n + r * B ^ n) := by
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add_right
        apply mul_le_mul_of_nonneg_right
        · simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_ge hr hr1 hn
        · exact Real.rpow_nonneg hB n
      · exact Real.rpow_nonneg (by norm_num) _

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
clears the positive normalized denominators in the pointwise estimate. -/
theorem aux_twoBump_inverse_denominators {A B D r n K : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (hr : 0 < r)
    (hpow : D ^ n ≤ K * (A ^ n + r * B ^ n)) :
    r⁻¹ * A ^ (-n) * B ^ (-n) ≤
      K * D ^ (-n) * (A ^ (-n) + r⁻¹ * B ^ (-n)) := by
  rw [Real.rpow_neg hA.le, Real.rpow_neg hB.le, Real.rpow_neg hD.le]
  have hAp : 0 < A ^ n := Real.rpow_pos_of_pos hA _
  have hBp : 0 < B ^ n := Real.rpow_pos_of_pos hB _
  have hDp : 0 < D ^ n := Real.rpow_pos_of_pos hD _
  have hden : 0 < r * A ^ n * B ^ n * D ^ n := by positivity
  calc
    r⁻¹ * (A ^ n)⁻¹ * (B ^ n)⁻¹ = D ^ n / (r * A ^ n * B ^ n * D ^ n) := by
      field_simp
      <;> ring
    _ ≤ (K * (A ^ n + r * B ^ n)) / (r * A ^ n * B ^ n * D ^ n) :=
      (div_le_div_iff_of_pos_right hden).mpr hpow
    _ = K * (D ^ n)⁻¹ * ((A ^ n)⁻¹ + r⁻¹ * (B ^ n)⁻¹) := by
      field_simp
      <;> ring

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this is
the normalized same-exponent pointwise convolution majorization. -/
theorem aux_twoBump_pointwise_sameExponent (n s₀ s₁ u v : ℝ)
    (hn : 1 < n) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hs : s₁ ≤ s₀) :
    scaledBracketBumpReal n s₀ u * scaledBracketBumpReal n s₁ v ≤
      2 ^ (n - 1) * scaledBracketBumpReal n s₀ (u + v) *
        (scaledBracketBumpReal n s₀ u + scaledBracketBumpReal n s₁ v) := by
  let r : ℝ := s₀⁻¹ * s₁
  let A : ℝ := 1 + |s₀⁻¹ * u|
  let B : ℝ := 1 + |s₁⁻¹ * v|
  let D : ℝ := 1 + |s₀⁻¹ * (u + v)|
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    calc
      s₀⁻¹ * s₁ ≤ s₀⁻¹ * s₀ :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hs₀.le)
      _ = 1 := inv_mul_cancel₀ hs₀.ne'
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hDle : D ≤ A + r * B := by
    have huv : s₀⁻¹ * (u + v) = s₀⁻¹ * u + r * (s₁⁻¹ * v) := by
      dsimp [r]
      field_simp <;> ring
    have hrabs : |r * (s₁⁻¹ * v)| = r * |s₁⁻¹ * v| := by
      rw [abs_mul, abs_of_nonneg hr.le]
    dsimp [D, A, B]
    rw [huv]
    calc
      1 + |s₀⁻¹ * u + r * (s₁⁻¹ * v)| ≤
          1 + (|s₀⁻¹ * u| + |r * (s₁⁻¹ * v)|) := by
            gcongr
            exact abs_add_le _ _
      _ = (1 + |s₀⁻¹ * u|) + r * (1 + |s₁⁻¹ * v|) - r := by
            rw [hrabs]
            ring
      _ ≤ (1 + |s₀⁻¹ * u|) + r * (1 + |s₁⁻¹ * v|) := by linarith
  have hpow : D ^ n ≤ 2 ^ (n - 1) * (A ^ n + r * B ^ n) :=
    aux_twoBump_denominator_power hA.le hB.le hr hr1 hn.le hD.le hDle
  have hinv := aux_twoBump_inverse_denominators hA hB hD hr hpow
  have hsrel : s₁⁻¹ = s₀⁻¹ * r⁻¹ := by
    dsimp [r]
    field_simp <;> ring
  change (s₀⁻¹ * A ^ (-n)) * (s₁⁻¹ * B ^ (-n)) ≤
    2 ^ (n - 1) * (s₀⁻¹ * D ^ (-n)) *
      (s₀⁻¹ * A ^ (-n) + s₁⁻¹ * B ^ (-n))
  calc
    (s₀⁻¹ * A ^ (-n)) * (s₁⁻¹ * B ^ (-n)) =
        (s₀⁻¹ * s₀⁻¹) * (r⁻¹ * A ^ (-n) * B ^ (-n)) := by
          rw [hsrel]
          ring
    _ ≤ (s₀⁻¹ * s₀⁻¹) *
        (2 ^ (n - 1) * D ^ (-n) * (A ^ (-n) + r⁻¹ * B ^ (-n))) :=
      mul_le_mul_of_nonneg_left hinv
        (mul_nonneg (inv_nonneg.mpr hs₀.le) (inv_nonneg.mpr hs₀.le))
    _ = 2 ^ (n - 1) * (s₀⁻¹ * D ^ (-n)) *
        (s₀⁻¹ * A ^ (-n) + s₁⁻¹ * B ^ (-n)) := by
          rw [hsrel]
          ring

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
records nonnegativity of scaled bracket profiles. -/
theorem aux_scaledBracketBumpReal_nonneg (n s x : ℝ) (hs : 0 < s) :
    0 ≤ scaledBracketBumpReal n s x := by
  unfold scaledBracketBumpReal
  exact mul_nonneg (inv_nonneg.mpr hs.le) (Real.rpow_nonneg (by positivity) _)

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
lowers a real bracket exponent. -/
theorem aux_scaledBracketBumpReal_exponent_reduce (n N s x : ℝ) (hs : 0 < s)
    (hnN : n ≤ N) :
    scaledBracketBumpReal N s x ≤ scaledBracketBumpReal n s x := by
  unfold scaledBracketBumpReal
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le
    · linarith [abs_nonneg (s⁻¹ * x)]
    · linarith
  · exact inv_nonneg.mpr hs.le

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
records evenness of scaled bracket profiles. -/
theorem aux_scaledBracketBumpReal_neg (n s x : ℝ) :
    scaledBracketBumpReal n s (-x) = scaledBracketBumpReal n s x := by
  unfold scaledBracketBumpReal
  rw [mul_neg, abs_neg]

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
integrates a nonnegative pointwise majorization. -/
theorem aux_twoBump_integral_pointwise {f g h : ℝ → ℝ} {K w : ℝ}
    (hg : Integrable g) (hh : Integrable h) (hfn : ∀ x, 0 ≤ f x)
    (hpoint : ∀ x, f x ≤ K * w * (g x + h x)) :
    ∫ x : ℝ, f x ≤ K * w * ((∫ x : ℝ, g x) + ∫ x : ℝ, h x) := by
  have hright : Integrable (fun x : ℝ => K * w * (g x + h x)) :=
    (hg.add hh).const_mul (K * w)
  calc
    ∫ x : ℝ, f x ≤ ∫ x : ℝ, K * w * (g x + h x) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall hfn) hright
        (Filter.Eventually.of_forall hpoint)
    _ = K * w * ((∫ x : ℝ, g x) + ∫ x : ℝ, h x) := by
      rw [integral_const_mul, integral_add hg hh]

/-- For source label `\ref{two bump estimate}` and public theorem `twoBumpEstimate`, this
compares the integrated pointwise constant with `C_twoBumpEstimate`. -/
theorem aux_twoBump_constant_bound (n : ℝ) (hn : 1 < n) :
    (2 : ℝ) ^ (n - 1) * (4 / (n - 1)) ≤
      2 ^ (1 + n) * (1 + (n - 1)⁻¹) := by
  rw [div_eq_mul_inv]
  have htwo : (2 : ℝ) ^ (n - 1) * 4 = 2 ^ (1 + n) := by
    have hfour : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [hfour, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [← mul_assoc, htwo]
  have hp : 0 ≤ (2 : ℝ) ^ (1 + n) := Real.rpow_nonneg (by norm_num) _
  have hi : 0 ≤ (n - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  nlinarith

/--
\begin{proposition}[two bump estimate]\label{two bump estimate}
    Consider real numbers $x_i$ and  $s_i>0$ and $n_i>1$ for $i=0,1$.  Assume $s_0\ge s_1$ and define
\begin{equation}\label{tb0}
     C_{\ref{two bump estimate},n_0,n_1}:=2^{1+\min(n_0,n_1)} [1+(\min(n_0,n_1)-1)^{-1}]
\end{equation}
  Then
\begin{equation}\label{two decays}
   | \int_{\R} (\prod_{i=0}^1 \left<x_i-p\right>^{n_i}_{(s_i)}) dp|\le C_{\ref{two bump estimate},n_0,n_1}
\left<x_0-x_1\right>^{\min(n_0,n_1)}_{(s_0)}\, .
\end{equation}
\end{proposition}
-/
theorem twoBumpEstimate (x₀ x₁ s₀ s₁ n₀ n₁ : ℝ)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hs : s₁ ≤ s₀)
    (hn₀ : 1 < n₀) (hn₁ : 1 < n₁) :
    |∫ p : ℝ, scaledBracketBumpReal n₀ s₀ (x₀ - p) *
      scaledBracketBumpReal n₁ s₁ (x₁ - p)| ≤
      C_twoBumpEstimate n₀ n₁ *
        scaledBracketBumpReal (min n₀ n₁) s₀ (x₀ - x₁) := by
  let n : ℝ := min n₀ n₁
  have hn : 1 < n := lt_min hn₀ hn₁
  have hn₀' : n ≤ n₀ := min_le_left _ _
  have hn₁' : n ≤ n₁ := min_le_right _ _
  let f : ℝ → ℝ := fun p =>
    scaledBracketBumpReal n₀ s₀ (x₀ - p) * scaledBracketBumpReal n₁ s₁ (x₁ - p)
  let g : ℝ → ℝ := fun p => scaledBracketBumpReal n s₀ (x₀ - p)
  let h : ℝ → ℝ := fun p => scaledBracketBumpReal n s₁ (x₁ - p)
  let K : ℝ := 2 ^ (n - 1)
  let w : ℝ := scaledBracketBumpReal n s₀ (x₀ - x₁)
  have hg : Integrable g := aux_integrable_scaledBracketBumpReal_translate n s₀ x₀ hn hs₀
  have hh : Integrable h := aux_integrable_scaledBracketBumpReal_translate n s₁ x₁ hn hs₁
  have hfn (p : ℝ) : 0 ≤ f p := by
    dsimp [f]
    exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hs₀)
      (aux_scaledBracketBumpReal_nonneg _ _ _ hs₁)
  have hpoint (p : ℝ) : f p ≤ K * w * (g p + h p) := by
    have hred₀ := aux_scaledBracketBumpReal_exponent_reduce n n₀ s₀ (x₀ - p) hs₀ hn₀'
    have hred₁ := aux_scaledBracketBumpReal_exponent_reduce n n₁ s₁ (x₁ - p) hs₁ hn₁'
    have hlower : f p ≤
        scaledBracketBumpReal n s₀ (x₀ - p) * scaledBracketBumpReal n s₁ (x₁ - p) := by
      dsimp [f]
      calc
        scaledBracketBumpReal n₀ s₀ (x₀ - p) * scaledBracketBumpReal n₁ s₁ (x₁ - p) ≤
            scaledBracketBumpReal n s₀ (x₀ - p) * scaledBracketBumpReal n₁ s₁ (x₁ - p) :=
          mul_le_mul_of_nonneg_right hred₀ (aux_scaledBracketBumpReal_nonneg _ _ _ hs₁)
        _ ≤ scaledBracketBumpReal n s₀ (x₀ - p) * scaledBracketBumpReal n s₁ (x₁ - p) :=
          mul_le_mul_of_nonneg_left hred₁ (aux_scaledBracketBumpReal_nonneg _ _ _ hs₀)
    have hsame := aux_twoBump_pointwise_sameExponent n s₀ s₁ (x₀ - p) (p - x₁) hn hs₀ hs₁ hs
    have hsign : scaledBracketBumpReal n s₁ (x₁ - p) =
        scaledBracketBumpReal n s₁ (p - x₁) := by
      rw [show x₁ - p = -(p - x₁) by ring, aux_scaledBracketBumpReal_neg]
    have hsum : (x₀ - p) + (p - x₁) = x₀ - x₁ := by ring
    dsimp [K, w, g, h]
    rw [hsign] at hlower
    rw [hsum] at hsame
    have hcombined := hlower.trans hsame
    rw [← hsign] at hcombined
    exact hcombined
  have hint := aux_twoBump_integral_pointwise hg hh hfn hpoint
  have hgval : ∫ p : ℝ, g p = 2 / (n - 1) :=
    aux_integral_scaledBracketBumpReal_eq n s₀ x₀ hn hs₀
  have hhval : ∫ p : ℝ, h p = 2 / (n - 1) :=
    aux_integral_scaledBracketBumpReal_eq n s₁ x₁ hn hs₁
  have hC : K * (4 / (n - 1)) ≤ C_twoBumpEstimate n₀ n₁ := by
    dsimp [K, n]
    simpa [C_twoBumpEstimate] using aux_twoBump_constant_bound n hn
  have hw : 0 ≤ w := aux_scaledBracketBumpReal_nonneg _ _ _ hs₀
  have hfinal : ∫ p : ℝ, f p ≤ C_twoBumpEstimate n₀ n₁ * w := by
    calc
      ∫ p : ℝ, f p ≤ K * w * ((∫ p : ℝ, g p) + ∫ p : ℝ, h p) := hint
      _ = (K * (4 / (n - 1))) * w := by rw [hgval, hhval]; ring
      _ ≤ C_twoBumpEstimate n₀ n₁ * w := mul_le_mul_of_nonneg_right hC hw
  change |∫ p : ℝ, f p| ≤ C_twoBumpEstimate n₀ n₁ * w
  rw [abs_of_nonneg (integral_nonneg hfn)]
  exact hfinal

/-- Source label `\ref{orthogonal domination}`; auxiliary for `orthogonalDomination`, proving
positivity of the transverse coefficient from linear independence. -/
theorem aux_orthogonalDomination_transverse_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (α₀ α₁ : E)
    (hα₀ : ‖α₀‖ = 1) (hα₁ : ‖α₁‖ = 1)
    (hlin : LinearIndependent ℝ ![α₀, α₁]) :
    0 < |inner ℝ α₀ (o.rightAngleRotation α₁)| := by
  refine abs_pos.mpr ?_
  intro hdet
  have harea : (o.areaForm α₀) α₁ = 0 := by
    rw [← neg_eq_zero, ← o.inner_rightAngleRotation_right]
    exact hdet
  have hpyth := o.inner_sq_add_areaForm_sq α₀ α₁
  norm_num [harea, hα₀, hα₁] at hpyth
  have hinterAbs : |inner ℝ α₀ α₁| = 1 := by
    rcases hpyth with hpyth | hpyth
    · simp [hpyth]
    · simp [hpyth]
  have hα₀ne : α₀ ≠ 0 := by
    rintro rfl
    norm_num at hα₀
  have hα₁ne : α₁ ≠ 0 := by
    rintro rfl
    norm_num at hα₁
  obtain ⟨r, hr, hα⟩ := (norm_inner_eq_norm_iff (𝕜 := ℝ) hα₀ne hα₁ne).mp (by
    norm_num [Real.norm_eq_abs, hinterAbs, hα₀, hα₁])
  have hz : (-r) • α₀ + (1 : ℝ) • α₁ = 0 := by
    rw [hα]
    module
  have hzero := (LinearIndependent.pair_iff.mp hlin) (-r) 1 hz
  exact hr (neg_eq_zero.mp hzero.1)

/-- Source label `\ref{orthogonal domination}`; auxiliary for `orthogonalDomination`, giving
the first coordinate estimate in the oriented orthonormal basis. -/
theorem aux_orthogonalDomination_coordinate_first
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (α₀ α₁ x : E)
    (hα₀ : ‖α₀‖ = 1) :
    |inner ℝ x (o.rightAngleRotation α₀)| *
        |inner ℝ α₀ (o.rightAngleRotation α₁)| ≤
      |inner ℝ x α₁| + |inner ℝ x α₀| * |inner ℝ α₀ α₁| := by
  have hcoord := o.inner_mul_inner_add_areaForm_mul_areaForm α₀ x α₁
  rw [hα₀] at hcoord
  have hcoord' : (o.areaForm α₀) x * (o.areaForm α₀) α₁ =
      inner ℝ x α₁ - inner ℝ x α₀ * inner ℝ α₀ α₁ := by
    rw [real_inner_comm x α₀] at hcoord
    norm_num at hcoord
    nlinarith [hcoord]
  calc
    |inner ℝ x (o.rightAngleRotation α₀)| *
        |inner ℝ α₀ (o.rightAngleRotation α₁)| =
        |(o.areaForm α₀) x * (o.areaForm α₀) α₁| := by
          rw [real_inner_comm (o.rightAngleRotation α₀) x,
            o.inner_rightAngleRotation_left α₀ x,
            o.inner_rightAngleRotation_right α₀ α₁, abs_neg, abs_mul]
    _ = |inner ℝ x α₁ - inner ℝ x α₀ * inner ℝ α₀ α₁| := by rw [hcoord']
    _ ≤ |inner ℝ x α₁| + |inner ℝ x α₀ * inner ℝ α₀ α₁| := by
      rw [← abs_neg (inner ℝ x α₀ * inner ℝ α₀ α₁)]
      exact abs_add_le _ _
    _ = |inner ℝ x α₁| + |inner ℝ x α₀| * |inner ℝ α₀ α₁| := by rw [abs_mul]

/-- Source label `\ref{orthogonal domination}`; auxiliary for `orthogonalDomination`, giving
the second coordinate estimate in the oriented orthonormal basis. -/
theorem aux_orthogonalDomination_coordinate_second
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (α₀ α₁ x : E)
    (hα₀ : ‖α₀‖ = 1) :
    |inner ℝ x (o.rightAngleRotation α₁)| ≤
      |inner ℝ α₀ (o.rightAngleRotation α₁)| * |inner ℝ x α₀| +
        |inner ℝ α₀ α₁| * |inner ℝ x (o.rightAngleRotation α₀)| := by
  have hcoord := o.inner_mul_inner_add_areaForm_mul_areaForm α₀ x
    (o.rightAngleRotation α₁)
  rw [hα₀, o.areaForm_rightAngleRotation_right] at hcoord
  have hcoord' : inner ℝ x (o.rightAngleRotation α₁) =
      inner ℝ x α₀ * inner ℝ α₀ (o.rightAngleRotation α₁) +
        (o.areaForm α₀) x * inner ℝ α₀ α₁ := by
    rw [o.inner_rightAngleRotation_right x α₁,
      o.inner_rightAngleRotation_right α₀ α₁]
    rw [real_inner_comm x α₀] at hcoord
    norm_num at hcoord
    nlinarith [hcoord]
  calc
    |inner ℝ x (o.rightAngleRotation α₁)| =
        |inner ℝ x α₀ * inner ℝ α₀ (o.rightAngleRotation α₁) +
          (o.areaForm α₀) x * inner ℝ α₀ α₁| := by rw [hcoord']
    _ ≤ |inner ℝ x α₀ * inner ℝ α₀ (o.rightAngleRotation α₁)| +
        |(o.areaForm α₀) x * inner ℝ α₀ α₁| := abs_add_le _ _
    _ = |inner ℝ α₀ (o.rightAngleRotation α₁)| * |inner ℝ x α₀| +
        |inner ℝ α₀ α₁| * |inner ℝ x (o.rightAngleRotation α₀)| := by
      rw [abs_mul, abs_mul, ← o.inner_rightAngleRotation_left α₀ x,
        real_inner_comm (o.rightAngleRotation α₀) x]
      ring

/-- Source label `\ref{orthogonal domination}`; auxiliary for `orthogonalDomination`, recording
the unit-vector Pythagorean identity for the parallel and transverse coefficients. -/
theorem aux_orthogonalDomination_square_add_square
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (α₀ α₁ : E)
    (hα₀ : ‖α₀‖ = 1) (hα₁ : ‖α₁‖ = 1) :
    |inner ℝ α₀ (o.rightAngleRotation α₁)| ^ 2 + |inner ℝ α₀ α₁| ^ 2 = 1 := by
  have h := o.inner_sq_add_areaForm_sq α₀ α₁
  rw [hα₀, hα₁] at h
  rw [o.inner_rightAngleRotation_right α₀ α₁, sq_abs, sq_abs]
  nlinarith [h]

/-- Source label `\ref{orthogonal domination}`; auxiliary for `orthogonalDomination`, combining
the two coordinate estimates into the stated alternative. -/
theorem aux_orthogonalDomination_algebra (s c A B P Q : ℝ)
    (hs : 0 < s) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hsq : s ^ 2 + c ^ 2 = 1)
    (hfirst : P * s ≤ B + A * c)
    (hsecond : Q ≤ s * A + c * P) :
    P ≤ 2 * s⁻¹ * B ∨ Q ≤ 2 * s⁻¹ * A := by
  by_cases hleft : P ≤ 2 * s⁻¹ * B
  · exact Or.inl hleft
  · right
    have hlt : 2 * s⁻¹ * B < P := lt_of_not_ge hleft
    have hmul : 2 * B < s * P := by
      calc
        2 * B = s * (2 * s⁻¹ * B) := by
          field_simp [ne_of_gt hs]
        _ < s * P := mul_lt_mul_of_pos_left hlt hs
    have hBlt : B < c * A := by
      nlinarith [hfirst, hmul]
    have hsp : s * P < 2 * c * A := by
      nlinarith [hfirst, hBlt]
    have hspc : c * (s * P) ≤ 2 * c ^ 2 * A := by
      calc
        c * (s * P) ≤ c * (2 * c * A) :=
          mul_le_mul_of_nonneg_left (le_of_lt hsp) hc
        _ = 2 * c ^ 2 * A := by ring
    have hcSq : c ^ 2 ≤ 1 := by
      nlinarith [hsq, sq_nonneg s]
    have hcA : c ^ 2 * A ≤ A := by
      calc
        c ^ 2 * A ≤ 1 * A := mul_le_mul_of_nonneg_right hcSq hA
        _ = A := one_mul A
    have hmain : s * Q ≤ 2 * A := by
      calc
        s * Q ≤ s * (s * A + c * P) :=
          mul_le_mul_of_nonneg_left hsecond hs.le
        _ = s ^ 2 * A + c * (s * P) := by ring
        _ ≤ s ^ 2 * A + 2 * c ^ 2 * A := by gcongr
        _ = (s ^ 2 + c ^ 2) * A + c ^ 2 * A := by ring
        _ = A + c ^ 2 * A := by rw [hsq]; ring
        _ ≤ 2 * A := by linarith
    calc
      Q = s⁻¹ * (s * Q) := by
        field_simp [ne_of_gt hs]
      _ ≤ s⁻¹ * (2 * A) :=
        mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hs.le)
      _ = 2 * s⁻¹ * A := by ring

/--
\begin{proposition}\label{orthogonal domination}
Let     $\alpha_0 ,\alpha_1\in\mathbb{R}^2$ be linearly independent unit vectors.
Then for every $x\in \R^2$ we have
 \begin{equation}\label{auto:orthogonal-coordinate-first-bound}
     |x\cdot \alpha_0^\perp|\le  2|\alpha_0\cdot \alpha_1^\perp|^{-1}| x\cdot \alpha_1|
 \end{equation}
or
 \begin{equation}\label{auto:orthogonal-coordinate-second-bound}
     | x\cdot \alpha_1^\perp|\le   2| \alpha_0\cdot \alpha_1^\perp|^{-1}|x\cdot \alpha_0|
 \end{equation}
\end{proposition}
-/
theorem orthogonalDomination
    (α₀ α₁ x : EuclideanSpace ℝ (Fin 2))
    (hα₀ : ‖α₀‖ = 1) (hα₁ : ‖α₁‖ = 1)
    (hlin : LinearIndependent ℝ ![α₀, α₁]) :
    |inner ℝ x ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₀)| ≤
        2 * |inner ℝ α₀
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)|⁻¹ *
          |inner ℝ x α₁| ∨
      |inner ℝ x ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)| ≤
        2 * |inner ℝ α₀
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)|⁻¹ *
          |inner ℝ x α₀| := by
  exact aux_orthogonalDomination_algebra
    |inner ℝ α₀ ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)|
    |inner ℝ α₀ α₁|
    |inner ℝ x α₀|
    |inner ℝ x α₁|
    |inner ℝ x ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₀)|
    |inner ℝ x ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)|
    (aux_orthogonalDomination_transverse_pos
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation α₀ α₁ hα₀ hα₁ hlin)
    (abs_nonneg _)
    (abs_nonneg _)
    (aux_orthogonalDomination_square_add_square
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation α₀ α₁ hα₀ hα₁)
    (aux_orthogonalDomination_coordinate_first
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation α₀ α₁ x hα₀)
    (aux_orthogonalDomination_coordinate_second
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation α₀ α₁ x hα₀)

/-- For source label `\ref{orthogonal decay}` and public theorem `orthogonalDecay`, this is the
explicit constant in the orthogonal-decay estimate. -/
def C_orthogonalDecay (α₀ α₁ : EuclideanSpace ℝ (Fin 2)) (n₀ n₁ : ℝ) : ℝ :=
  max
    (Real.rpow
      (2 * |inner ℝ α₀
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)|⁻¹) n₀)
    (Real.rpow
      (2 * |inner ℝ α₀
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)|⁻¹) n₁)

/-- For source label `\ref{orthogonal decay}` and public theorem `orthogonalDecay`, this turns
one of the two scalar coordinate dominations into the required two-bump bound. -/
theorem aux_orthogonalDecay_from_domination {A n₀ n₁ s₀ s₁ u₀ u₁ p₀ p₁ : ℝ}
    (hA : 0 < A) (hAone : 1 ≤ A) (hn₀ : 0 < n₀) (hn₁ : 0 < n₁)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (hdom : |p₀| ≤ A * |u₁| ∨ |p₁| ≤ A * |u₀|) :
    scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ u₁ ≤
      max (Real.rpow A n₀) (Real.rpow A n₁) *
        (scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ p₀ +
          scaledBracketBumpReal n₀ s₀ p₁ * scaledBracketBumpReal n₁ s₁ u₁) := by
  have hnon₀ (z : ℝ) : 0 ≤ scaledBracketBumpReal n₀ s₀ z :=
    aux_scaledBracketBumpReal_nonneg n₀ s₀ z hs₀
  have hnon₁ (z : ℝ) : 0 ≤ scaledBracketBumpReal n₁ s₁ z :=
    aux_scaledBracketBumpReal_nonneg n₁ s₁ z hs₁
  rcases hdom with hdom | hdom
  · have hcomp := compare_brackets n₁ hn₁ hs₁ (by norm_num : (0 : ℝ) < 1) hAone hAone
      (by simpa using hdom)
    have hcomp' : Real.rpow A (-n₁) * scaledBracketBumpReal n₁ s₁ u₁ ≤
        scaledBracketBumpReal n₁ s₁ p₀ := by
      simpa using hcomp
    have hB : scaledBracketBumpReal n₁ s₁ u₁ ≤
        Real.rpow A n₁ * scaledBracketBumpReal n₁ s₁ p₀ := by
      calc
        scaledBracketBumpReal n₁ s₁ u₁ = Real.rpow A n₁ *
            (Real.rpow A (-n₁) * scaledBracketBumpReal n₁ s₁ u₁) := by
          change scaledBracketBumpReal n₁ s₁ u₁ = A ^ n₁ *
            (A ^ (-n₁) * scaledBracketBumpReal n₁ s₁ u₁)
          rw [← mul_assoc, ← Real.rpow_add hA]
          norm_num
        _ ≤ Real.rpow A n₁ * scaledBracketBumpReal n₁ s₁ p₀ :=
          mul_le_mul_of_nonneg_left hcomp' (Real.rpow_nonneg hA.le _)
    have hprod : scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ u₁ ≤
        Real.rpow A n₁ *
          (scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ p₀) := by
      calc
        scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ u₁ ≤
            scaledBracketBumpReal n₀ s₀ u₀ *
              (Real.rpow A n₁ * scaledBracketBumpReal n₁ s₁ p₀) :=
          mul_le_mul_of_nonneg_left hB (hnon₀ _)
        _ = Real.rpow A n₁ * (scaledBracketBumpReal n₀ s₀ u₀ *
            scaledBracketBumpReal n₁ s₁ p₀) := by ring
    calc
      scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ u₁ ≤
          Real.rpow A n₁ *
            (scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ p₀) := hprod
      _ ≤ max (Real.rpow A n₀) (Real.rpow A n₁) *
          (scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ p₀ +
            scaledBracketBumpReal n₀ s₀ p₁ * scaledBracketBumpReal n₁ s₁ u₁) := by
        apply mul_le_mul
        · exact le_max_right _ _
        · exact le_add_of_nonneg_right (mul_nonneg (hnon₀ _) (hnon₁ _))
        · exact mul_nonneg (hnon₀ _) (hnon₁ _)
        · exact (Real.rpow_nonneg hA.le _).trans (le_max_right _ _)
  · have hcomp := compare_brackets n₀ hn₀ hs₀ (by norm_num : (0 : ℝ) < 1) hAone hAone
      (by simpa using hdom)
    have hcomp' : Real.rpow A (-n₀) * scaledBracketBumpReal n₀ s₀ u₀ ≤
        scaledBracketBumpReal n₀ s₀ p₁ := by
      simpa using hcomp
    have hB : scaledBracketBumpReal n₀ s₀ u₀ ≤
        Real.rpow A n₀ * scaledBracketBumpReal n₀ s₀ p₁ := by
      calc
        scaledBracketBumpReal n₀ s₀ u₀ = Real.rpow A n₀ *
            (Real.rpow A (-n₀) * scaledBracketBumpReal n₀ s₀ u₀) := by
          change scaledBracketBumpReal n₀ s₀ u₀ = A ^ n₀ *
            (A ^ (-n₀) * scaledBracketBumpReal n₀ s₀ u₀)
          rw [← mul_assoc, ← Real.rpow_add hA]
          norm_num
        _ ≤ Real.rpow A n₀ * scaledBracketBumpReal n₀ s₀ p₁ :=
          mul_le_mul_of_nonneg_left hcomp' (Real.rpow_nonneg hA.le _)
    have hprod : scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ u₁ ≤
        Real.rpow A n₀ *
          (scaledBracketBumpReal n₀ s₀ p₁ * scaledBracketBumpReal n₁ s₁ u₁) := by
      calc
        scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ u₁ ≤
            (Real.rpow A n₀ * scaledBracketBumpReal n₀ s₀ p₁) *
              scaledBracketBumpReal n₁ s₁ u₁ :=
          mul_le_mul_of_nonneg_right hB (hnon₁ _)
        _ = Real.rpow A n₀ * (scaledBracketBumpReal n₀ s₀ p₁ *
            scaledBracketBumpReal n₁ s₁ u₁) := by ring
    calc
      scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ u₁ ≤
          Real.rpow A n₀ *
            (scaledBracketBumpReal n₀ s₀ p₁ * scaledBracketBumpReal n₁ s₁ u₁) := hprod
      _ ≤ max (Real.rpow A n₀) (Real.rpow A n₁) *
          (scaledBracketBumpReal n₀ s₀ u₀ * scaledBracketBumpReal n₁ s₁ p₀ +
            scaledBracketBumpReal n₀ s₀ p₁ * scaledBracketBumpReal n₁ s₁ u₁) := by
        apply mul_le_mul
        · exact le_max_left _ _
        · exact le_add_of_nonneg_left (mul_nonneg (hnon₀ _) (hnon₁ _))
        · exact mul_nonneg (hnon₀ _) (hnon₁ _)
        · exact (Real.rpow_nonneg hA.le _).trans (le_max_left _ _)

/--
\begin{proposition}[orthogonal decay]\label{orthogonal decay}\using{compare brackets}\using{orthogonal domination}
Let $\alpha_0,\alpha_1\in\mathbb{R}^2$ be linearly independent unit vectors.
Let $\alpha_{m}^\perp$ be unit vectors orthogonal to $\alpha_m$ and note that $\alpha_0\cdot \alpha_1^\perp\neq 0$. Setting \begin{equation}\label{auto:orthogonal-decay-constant}
    C_{\ref{orthogonal decay}, \alpha_0,\alpha_1,n_0,n_1}:=\max( (2 |\alpha_0\cdot \alpha_1^\perp|^{-1})^{n_0},(2 |\alpha_0\cdot \alpha_1^\perp|^{-1})^{n_1}) \, ,
\end{equation}
then for all $n_0,n_1,s_0,s_1>0$ and $x\in\mathbb{R}^2$,
\begin{equation}\label{eq:two bump}
    \langle x\cdot \alpha_0\rangle_{(s_0)}^{n_0} \langle x\cdot \alpha_1\rangle_{(s_1)}^{n_1}
\le C_{\ref{orthogonal decay},\alpha_0,\alpha_1,n_0,n_1} (\langle x\cdot \alpha_0\rangle_{(s_0)}^{n_0}\langle x\cdot \alpha_0^\perp\rangle_{(s_1)}^{n_1} +
\langle x\cdot \alpha_1^\perp\rangle_{(s_0)}^{n_0}\langle x\cdot \alpha_1\rangle_{(s_1)}^{n_1}).
\end{equation}
\end{proposition}
-/
theorem orthogonalDecay
    (α₀ α₁ x : EuclideanSpace ℝ (Fin 2))
    (hα₀ : ‖α₀‖ = 1) (hα₁ : ‖α₁‖ = 1)
    (hlin : LinearIndependent ℝ ![α₀, α₁])
    (n₀ n₁ s₀ s₁ : ℝ) (hn₀ : 0 < n₀) (hn₁ : 0 < n₁)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) :
    scaledBracketBumpReal n₀ s₀ (inner ℝ x α₀) *
        scaledBracketBumpReal n₁ s₁ (inner ℝ x α₁) ≤
      C_orthogonalDecay α₀ α₁ n₀ n₁ *
        (scaledBracketBumpReal n₀ s₀ (inner ℝ x α₀) *
            scaledBracketBumpReal n₁ s₁
              (inner ℝ x ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₀)) +
          scaledBracketBumpReal n₀ s₀
              (inner ℝ x ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)) *
            scaledBracketBumpReal n₁ s₁ (inner ℝ x α₁)) := by
  let A : ℝ := 2 * |inner ℝ α₀
    ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)|⁻¹
  have htransverse : 0 < |inner ℝ α₀
      ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)| :=
    aux_orthogonalDomination_transverse_pos
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation α₀ α₁ hα₀ hα₁ hlin
  have hbound : |inner ℝ α₀
      ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)| ≤ 1 := by
    calc
      |inner ℝ α₀
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)| ≤
          ‖α₀‖ * ‖(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁‖ :=
        abs_real_inner_le_norm α₀
          ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)
      _ = 1 := by
        rw [hα₀,
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation.norm_map,
          hα₁]
        norm_num
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hAone : 1 ≤ A := by
    dsimp [A]
    have hinv : 1 ≤ |inner ℝ α₀
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation.rightAngleRotation α₁)|⁻¹ :=
      (one_le_inv₀ htransverse).mpr hbound
    nlinarith
  have hdom := orthogonalDomination α₀ α₁ x hα₀ hα₁ hlin
  simpa only [C_orthogonalDecay, A] using
    aux_orthogonalDecay_from_domination hA hAone hn₀ hn₁ hs₀ hs₁ hdom

/-- Source label `\ref{bump triangle}`; the auxiliary constant used by the public theorem
`bump_triangle`. -/
def C_bumpTriangleTilde (c₀ c₁ : ℝ) : ℝ :=
  max (max (2 * |c₀|) (2 * |c₀|)⁻¹) (max (2 * |c₁|) (2 * |c₁|)⁻¹)

/-- Source label `\ref{bump triangle}`; the real-exponent constant used by the public theorem
`bump_triangle`. -/
def C_bumpTriangle (c₀ c₁ n₀ n₁ : ℝ) : ℝ :=
  max (Real.rpow (C_bumpTriangleTilde c₀ c₁) n₀)
    (Real.rpow (C_bumpTriangleTilde c₀ c₁) n₁)

/-- Source label `\ref{bump triangle}`; auxiliary natural-exponent constant for
`bump_triangle`. -/
def aux_C_bumpTriangleNat (c₀ c₁ : ℝ) (n₀ n₁ : ℕ) : ℝ :=
  max (C_bumpTriangleTilde c₀ c₁ ^ n₀)
    (C_bumpTriangleTilde c₀ c₁ ^ n₁)

/-- Source label `\ref{bump triangle}`; auxiliary for `bump_triangle`, retaining the earlier
natural-exponent scalar specialization. -/
theorem aux_bumpTriangleNat (n₀ n₁ : ℕ) {c₀ c₁ u v w s₀ s₁ : ℝ}
    (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hw : w = c₀ * u + c₁ * v) :
    scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ v ≤
      aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
        (scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ w +
          scaledBracketBump n₀ s₀ w * scaledBracketBump n₁ s₁ v) := by
  have hA₀pos : 0 < 2 * |c₀| := mul_pos (by norm_num) (abs_pos.mpr hc₀)
  have hA₁pos : 0 < 2 * |c₁| := mul_pos (by norm_num) (abs_pos.mpr hc₁)
  have hT₀ : 2 * |c₀| ≤ C_bumpTriangleTilde c₀ c₁ := by
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hT₀inv : (2 * |c₀|)⁻¹ ≤ C_bumpTriangleTilde c₀ c₁ := by
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hT₁ : 2 * |c₁| ≤ C_bumpTriangleTilde c₀ c₁ := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hT₁inv : (2 * |c₁|)⁻¹ ≤ C_bumpTriangleTilde c₀ c₁ := by
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hTnonneg : 0 ≤ C_bumpTriangleTilde c₀ c₁ := hA₀pos.le.trans hT₀
  have hCbnonneg : 0 ≤ aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ :=
    (pow_nonneg hTnonneg n₀).trans (le_max_left _ _)
  by_cases hbranch : 2 * |c₀| * |u| ≥ 2 * |c₁| * |v|
  · have hrel : |w| ≤ (2 * |c₀|) * |u| := by
      rw [hw]
      calc
        |c₀ * u + c₁ * v| ≤ |c₀ * u| + |c₁ * v| := abs_add_le _ _
        _ = |c₀| * |u| + |c₁| * |v| := by rw [abs_mul, abs_mul]
        _ ≤ 2 * |c₀| * |u| := by nlinarith
    have hcomp := aux_scaledBracketBump_le_of_abs_le_mul n₀ hn₀ hs₀ hA₀pos hrel
    have hlocal : max ((2 * |c₀|) ^ n₀) ((2 * |c₀|)⁻¹ ^ n₀) ≤
        aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ := by
      apply max_le
      · exact (pow_le_pow_left₀ hA₀pos.le hT₀ n₀).trans (le_max_left _ _)
      · exact (pow_le_pow_left₀ (inv_nonneg.mpr hA₀pos.le) hT₀inv n₀).trans (le_max_left _ _)
    have hprod : scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ v ≤
        aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
          (scaledBracketBump n₀ s₀ w * scaledBracketBump n₁ s₁ v) := by
      calc
        scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ v ≤
            (max ((2 * |c₀|) ^ n₀) ((2 * |c₀|)⁻¹ ^ n₀) * scaledBracketBump n₀ s₀ w) *
              scaledBracketBump n₁ s₁ v := by
          exact mul_le_mul_of_nonneg_right hcomp (aux_scaledBracketBump_nonneg n₁ hs₁ v)
        _ ≤ (aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ * scaledBracketBump n₀ s₀ w) *
              scaledBracketBump n₁ s₁ v := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hlocal (aux_scaledBracketBump_nonneg n₀ hs₀ w))
            (aux_scaledBracketBump_nonneg n₁ hs₁ v)
        _ = aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
            (scaledBracketBump n₀ s₀ w * scaledBracketBump n₁ s₁ v) := by ring
    calc
      scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ v ≤
          aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
            (scaledBracketBump n₀ s₀ w * scaledBracketBump n₁ s₁ v) := hprod
      _ ≤ aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
          (scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ w +
            scaledBracketBump n₀ s₀ w * scaledBracketBump n₁ s₁ v) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_left
            (mul_nonneg (aux_scaledBracketBump_nonneg n₀ hs₀ u)
              (aux_scaledBracketBump_nonneg n₁ hs₁ w))
        · exact hCbnonneg
  · have hbranch' : 2 * |c₀| * |u| ≤ 2 * |c₁| * |v| := le_of_not_ge hbranch
    have hrel : |w| ≤ (2 * |c₁|) * |v| := by
      rw [hw]
      calc
        |c₀ * u + c₁ * v| ≤ |c₀ * u| + |c₁ * v| := abs_add_le _ _
        _ = |c₀| * |u| + |c₁| * |v| := by rw [abs_mul, abs_mul]
        _ ≤ 2 * |c₁| * |v| := by nlinarith
    have hcomp := aux_scaledBracketBump_le_of_abs_le_mul n₁ hn₁ hs₁ hA₁pos hrel
    have hlocal : max ((2 * |c₁|) ^ n₁) ((2 * |c₁|)⁻¹ ^ n₁) ≤
        aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ := by
      apply max_le
      · exact (pow_le_pow_left₀ hA₁pos.le hT₁ n₁).trans (le_max_right _ _)
      · exact (pow_le_pow_left₀ (inv_nonneg.mpr hA₁pos.le) hT₁inv n₁).trans (le_max_right _ _)
    have hprod : scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ v ≤
        aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
          (scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ w) := by
      calc
        scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ v ≤ scaledBracketBump n₀ s₀ u *
            (max ((2 * |c₁|) ^ n₁) ((2 * |c₁|)⁻¹ ^ n₁) * scaledBracketBump n₁ s₁ w) := by
          exact mul_le_mul_of_nonneg_left hcomp (aux_scaledBracketBump_nonneg n₀ hs₀ u)
        _ ≤ scaledBracketBump n₀ s₀ u *
            (aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ * scaledBracketBump n₁ s₁ w) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hlocal (aux_scaledBracketBump_nonneg n₁ hs₁ w))
            (aux_scaledBracketBump_nonneg n₀ hs₀ u)
        _ = aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
            (scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ w) := by ring
    calc
      scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ v ≤
          aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
            (scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ w) := hprod
      _ ≤ aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
          (scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ w +
            scaledBracketBump n₀ s₀ w * scaledBracketBump n₁ s₁ v) := by
        apply mul_le_mul_of_nonneg_left
        · exact le_add_of_nonneg_right
            (mul_nonneg (aux_scaledBracketBump_nonneg n₀ hs₀ w)
              (aux_scaledBracketBump_nonneg n₁ hs₁ v))
        · exact hCbnonneg

/-- Source label `\ref{bump triangle}`; auxiliary for `bump_triangle`, comparing a
real-exponent bracket after a controlled change of scalar coordinate. -/
theorem aux_scaledBracketBumpReal_le_of_abs_le_mul (N : ℝ) {A T s u w : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hA : 0 < A)
    (hAT : A ≤ T) (hAinvT : A⁻¹ ≤ T) (h : |w| ≤ A * |u|) :
    scaledBracketBumpReal N s u ≤ Real.rpow T N * scaledBracketBumpReal N s w := by
  have hw : 0 ≤ scaledBracketBumpReal N s w :=
    aux_scaledBracketBumpReal_nonneg N s w hs
  by_cases hAone : 1 ≤ A
  · have hcomp := compare_brackets N (lam := 1) (mu := A) (s := s) (x := u) (y := w)
      hN hs (by norm_num) hAone hAone (by simpa using h)
    have hcomp' : Real.rpow A (-N) * scaledBracketBumpReal N s u ≤
        scaledBracketBumpReal N s w := by
      simpa using hcomp
    have hB : scaledBracketBumpReal N s u ≤
        Real.rpow A N * scaledBracketBumpReal N s w := by
      calc
        scaledBracketBumpReal N s u = Real.rpow A N *
            (Real.rpow A (-N) * scaledBracketBumpReal N s u) := by
          change scaledBracketBumpReal N s u = A ^ N *
            (A ^ (-N) * scaledBracketBumpReal N s u)
          rw [← mul_assoc, ← Real.rpow_add hA]
          norm_num
        _ ≤ Real.rpow A N * scaledBracketBumpReal N s w :=
          mul_le_mul_of_nonneg_left hcomp' (Real.rpow_nonneg hA.le _)
    calc
      scaledBracketBumpReal N s u ≤ Real.rpow A N * scaledBracketBumpReal N s w := hB
      _ ≤ Real.rpow T N * scaledBracketBumpReal N s w :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hA.le hAT hN.le) hw
  · have hAone' : A ≤ 1 := le_of_not_ge hAone
    have hcond : A * |w| ≤ 1 * |u| := by
      calc
        A * |w| ≤ A * (A * |u|) := mul_le_mul_of_nonneg_left h hA.le
        _ = A ^ 2 * |u| := by ring
        _ ≤ 1 * |u| := by
          gcongr
          nlinarith
    have hcomp := compare_brackets N (lam := A) (mu := 1) (s := s) (x := u) (y := w)
      hN hs hA hAone' (by norm_num) hcond
    have hB : scaledBracketBumpReal N s u ≤
        Real.rpow A (-N) * scaledBracketBumpReal N s w := by
      simpa using hcomp
    have hneg : Real.rpow A (-N) = Real.rpow A⁻¹ N := by
      change A ^ (-N) = A⁻¹ ^ N
      rw [Real.rpow_neg hA.le, Real.inv_rpow hA.le]
    calc
      scaledBracketBumpReal N s u ≤ Real.rpow A (-N) * scaledBracketBumpReal N s w := hB
      _ = Real.rpow A⁻¹ N * scaledBracketBumpReal N s w := by rw [hneg]
      _ ≤ Real.rpow T N * scaledBracketBumpReal N s w :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (inv_nonneg.mpr hA.le) hAinvT hN.le) hw

/-- Source label `\ref{bump triangle}`; auxiliary for `bump_triangle`, proving the scalar
real-exponent form before applying it to Euclidean inner products. -/
theorem aux_bumpTriangleReal {c₀ c₁ u v w s₀ s₁ n₀ n₁ : ℝ}
    (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (hw : w = c₀ * u + c₁ * v) :
    scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ v ≤
      C_bumpTriangle c₀ c₁ n₀ n₁ *
        (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w +
          scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v) := by
  let T : ℝ := C_bumpTriangleTilde c₀ c₁
  have hA₀pos : 0 < 2 * |c₀| := mul_pos (by norm_num) (abs_pos.mpr hc₀)
  have hA₁pos : 0 < 2 * |c₁| := mul_pos (by norm_num) (abs_pos.mpr hc₁)
  have hT₀ : 2 * |c₀| ≤ T := by
    dsimp [T, C_bumpTriangleTilde]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hT₀inv : (2 * |c₀|)⁻¹ ≤ T := by
    dsimp [T, C_bumpTriangleTilde]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hT₁ : 2 * |c₁| ≤ T := by
    dsimp [T, C_bumpTriangleTilde]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hT₁inv : (2 * |c₁|)⁻¹ ≤ T := by
    dsimp [T, C_bumpTriangleTilde]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hTnonneg : 0 ≤ T := hA₀pos.le.trans hT₀
  have hCnonneg : 0 ≤ C_bumpTriangle c₀ c₁ n₀ n₁ := by
    unfold C_bumpTriangle
    exact (Real.rpow_nonneg hTnonneg n₀).trans (le_max_left _ _)
  have hnon₀ (z : ℝ) : 0 ≤ scaledBracketBumpReal n₀ s₀ z :=
    aux_scaledBracketBumpReal_nonneg n₀ s₀ z hs₀
  have hnon₁ (z : ℝ) : 0 ≤ scaledBracketBumpReal n₁ s₁ z :=
    aux_scaledBracketBumpReal_nonneg n₁ s₁ z hs₁
  by_cases hbranch : 2 * |c₀| * |u| ≥ 2 * |c₁| * |v|
  · have hrel : |w| ≤ (2 * |c₀|) * |u| := by
      rw [hw]
      calc
        |c₀ * u + c₁ * v| ≤ |c₀ * u| + |c₁ * v| := abs_add_le _ _
        _ = |c₀| * |u| + |c₁| * |v| := by rw [abs_mul, abs_mul]
        _ ≤ 2 * |c₀| * |u| := by nlinarith
    have hcomp : scaledBracketBumpReal n₀ s₀ u ≤
        Real.rpow T n₀ * scaledBracketBumpReal n₀ s₀ w := by
      exact aux_scaledBracketBumpReal_le_of_abs_le_mul n₀ hn₀ hs₀ hA₀pos
        hT₀ hT₀inv hrel
    have hprod : scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ v ≤
        Real.rpow T n₀ *
          (scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v) := by
      calc
        scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ v ≤
            (Real.rpow T n₀ * scaledBracketBumpReal n₀ s₀ w) *
              scaledBracketBumpReal n₁ s₁ v :=
          mul_le_mul_of_nonneg_right hcomp (hnon₁ _)
        _ = Real.rpow T n₀ *
            (scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v) := by ring
    calc
      scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ v ≤
          Real.rpow T n₀ *
            (scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v) := hprod
      _ ≤ C_bumpTriangle c₀ c₁ n₀ n₁ *
          (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w +
            scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v) := by
        change Real.rpow T n₀ *
            (scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v) ≤
          max (Real.rpow T n₀) (Real.rpow T n₁) *
            (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w +
              scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v)
        apply mul_le_mul
        · exact le_max_left _ _
        · exact le_add_of_nonneg_left (mul_nonneg (hnon₀ _) (hnon₁ _))
        · exact mul_nonneg (hnon₀ _) (hnon₁ _)
        · exact (Real.rpow_nonneg hTnonneg _).trans (le_max_left _ _)
  · have hbranch' : 2 * |c₀| * |u| ≤ 2 * |c₁| * |v| := le_of_not_ge hbranch
    have hrel : |w| ≤ (2 * |c₁|) * |v| := by
      rw [hw]
      calc
        |c₀ * u + c₁ * v| ≤ |c₀ * u| + |c₁ * v| := abs_add_le _ _
        _ = |c₀| * |u| + |c₁| * |v| := by rw [abs_mul, abs_mul]
        _ ≤ 2 * |c₁| * |v| := by nlinarith
    have hcomp : scaledBracketBumpReal n₁ s₁ v ≤
        Real.rpow T n₁ * scaledBracketBumpReal n₁ s₁ w := by
      exact aux_scaledBracketBumpReal_le_of_abs_le_mul n₁ hn₁ hs₁ hA₁pos
        hT₁ hT₁inv hrel
    have hprod : scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ v ≤
        Real.rpow T n₁ *
          (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w) := by
      calc
        scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ v ≤
            scaledBracketBumpReal n₀ s₀ u *
              (Real.rpow T n₁ * scaledBracketBumpReal n₁ s₁ w) :=
          mul_le_mul_of_nonneg_left hcomp (hnon₀ _)
        _ = Real.rpow T n₁ *
            (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w) := by ring
    calc
      scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ v ≤
          Real.rpow T n₁ *
            (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w) := hprod
      _ ≤ C_bumpTriangle c₀ c₁ n₀ n₁ *
          (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w +
            scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v) := by
        change Real.rpow T n₁ *
            (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w) ≤
          max (Real.rpow T n₀) (Real.rpow T n₁) *
            (scaledBracketBumpReal n₀ s₀ u * scaledBracketBumpReal n₁ s₁ w +
              scaledBracketBumpReal n₀ s₀ w * scaledBracketBumpReal n₁ s₁ v)
        apply mul_le_mul
        · exact le_max_right _ _
        · exact le_add_of_nonneg_right (mul_nonneg (hnon₀ _) (hnon₁ _))
        · exact mul_nonneg (hnon₀ _) (hnon₁ _)
        · exact (Real.rpow_nonneg hTnonneg _).trans (le_max_right _ _)

/--
\begin{proposition}[bump triangle]\label{bump triangle}\using{compare brackets}
Let $\alpha_0,\alpha_1\in\mathbb{R}^2$ and let $\alpha_2=c_0\alpha_0+c_1\alpha_1$ be a non-trivial linear combination of $\alpha_0,\alpha_1$, i.e. $c_0\not=0, c_1\not=0$.
Let
\begin{equation}\label{auto:bump-triangle-scale-constant}\tilde{C}_{\ref{bump triangle},c_0,c_1}=\max(2|c_0|, (2|c_0|)^{-1},2|c_1|, (2|c_1|)^{-1}),\end{equation}
\begin{equation}\label{auto:bump-triangle-constant}
    C_{\ref{bump triangle},c_0,c_1,n_0,n_1}=\max(\tilde{C}_{\ref{bump triangle},c_0,c_1}^{n_0}, \tilde{C}_{\ref{bump triangle},c_0,c_1}^{n_1}).
\end{equation}
Then
\begin{equation}\label{auto:bump-triangle-bound} \langle x\cdot \alpha_0\rangle_{(s_0)}^{n_0} \langle x\cdot \alpha_1\rangle_{(s_1)}^{n_1}
\le C_{\ref{bump triangle},c_0,c_1,n_0,n_1}(\langle x\cdot \alpha_0\rangle_{(s_0)}^{n_0}\langle x\cdot \alpha_2\rangle_{(s_1)}^{n_1} + \langle x\cdot \alpha_2\rangle_{(s_0)}^{n_0}\langle x\cdot \alpha_1\rangle_{(s_1)}^{n_1}).
\end{equation}
\end{proposition}
-/
theorem bump_triangle
    (α₀ α₁ α₂ x : EuclideanSpace ℝ (Fin 2))
    (c₀ c₁ n₀ n₁ s₀ s₁ : ℝ)
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    (hn₀ : 0 < n₀) (hn₁ : 0 < n₁) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (hα₂ : α₂ = c₀ • α₀ + c₁ • α₁) :
    scaledBracketBumpReal n₀ s₀ (inner ℝ x α₀) *
        scaledBracketBumpReal n₁ s₁ (inner ℝ x α₁) ≤
      C_bumpTriangle c₀ c₁ n₀ n₁ *
        (scaledBracketBumpReal n₀ s₀ (inner ℝ x α₀) *
            scaledBracketBumpReal n₁ s₁ (inner ℝ x α₂) +
          scaledBracketBumpReal n₀ s₀ (inner ℝ x α₂) *
            scaledBracketBumpReal n₁ s₁ (inner ℝ x α₁)) := by
  have hw : inner ℝ x α₂ = c₀ * inner ℝ x α₀ + c₁ * inner ℝ x α₁ := by
    rw [hα₂, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact aux_bumpTriangleReal hn₀ hn₁ hc₀ hc₁ hs₀ hs₁ hw

/-- Source label `\ref{diagonal square root}`; frequency-side definition used by
`diagonalSquareRoot_memW0` and `diagonalSquareRoot_bound`. -/
def diagonalSquareRootFrequency (t₀ t₁ ξ : ℝ) : ℝ :=
  Real.sqrt (Gaussians.gaussian (t₀ * ξ) - Gaussians.gaussian (t₁ * ξ))

/-- Source label `\ref{diagonal square root}`; the kernel used by
`diagonalSquareRoot_memW0` and `diagonalSquareRoot_bound`. -/
def diagonalSquareRoot (t₀ t₁ : ℝ) : ℝ → ℝ := fun x =>
  (FourierTransformInv.fourierInv
    (fun ξ : ℝ => (diagonalSquareRootFrequency t₀ t₁ ξ : ℂ)) x).re

/-- Source label `\ref{diagonal square root}`; auxiliary for
`diagonalSquareRoot_memW0` and `diagonalSquareRoot_bound`. -/
theorem aux_diagonalSquareRootFrequency_nonneg {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) (ξ : ℝ) :
    0 ≤ Gaussians.gaussian (t₀ * ξ) - Gaussians.gaussian (t₁ * ξ) := by
  have ht₀ : 0 ≤ t₀ := by linarith
  have ht₀₁ : t₀ ≤ t₁ := by linarith
  have hsquares : (t₀ * ξ) ^ 2 ≤ (t₁ * ξ) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ ht₀ ht₀₁ 2) (sq_nonneg ξ)
  have hexp : Gaussians.gaussian (t₁ * ξ) ≤ Gaussians.gaussian (t₀ * ξ) := by
    change Real.exp (-Real.pi * (t₁ * ξ) ^ 2) ≤
      Real.exp (-Real.pi * (t₀ * ξ) ^ 2)
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, hsquares]
  linarith

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this proves that inverse Fourier transforms of integrable even real
profiles have zero imaginary part. -/
theorem aux_diagonalSquareRoot_inverseFourier_real_of_even (f : ℝ → ℝ) (hf : Integrable f)
    (heven : ∀ ξ : ℝ, f (-ξ) = f ξ) (x : ℝ) :
    (FourierTransformInv.fourierInv (fun ξ : ℝ => (f ξ : ℂ)) x).im = 0 := by
  rw [Real.fourierInv_eq']
  have hInt : Integrable (fun ξ : ℝ =>
      Complex.exp ((↑(2 * Real.pi * ⟪ξ, x⟫) : ℂ) * Complex.I) • (f ξ : ℂ)) := by
    have h := (Real.fourierIntegral_convergent_iff
      (f := fun ξ : ℝ => (f ξ : ℂ)) (μ := volume) (-x)).mpr hf.ofReal
    simpa [Circle.smul_def, Real.fourierChar_apply, Real.inner_apply] using h
  change Complex.imCLM (∫ ξ : ℝ,
    Complex.exp ((↑(2 * Real.pi * ⟪ξ, x⟫) : ℂ) * Complex.I) • (f ξ : ℂ)) = 0
  rw [← Complex.imCLM.integral_comp_comm hInt]
  let q : ℝ → ℝ := fun ξ =>
    (Complex.exp ((↑(2 * Real.pi * ⟪ξ, x⟫) : ℂ) * Complex.I) • (f ξ : ℂ)).im
  change (∫ ξ : ℝ, q ξ) = 0
  have hodd (ξ : ℝ) : q (-ξ) = -q ξ := by
    dsimp [q]
    simp only [Circle.smul_def, smul_eq_mul, Real.inner_apply, starRingEnd_apply, star_trivial]
    rw [heven]
    have hphase : 2 * Real.pi * (x * -ξ) = -(2 * Real.pi * (x * ξ)) := by ring
    rw [hphase, Complex.ofReal_neg, neg_mul]
    rw [Complex.mul_im, Complex.mul_im]
    simp [Complex.exp_re, Complex.exp_im, Real.sin_neg]
  have hchange : (∫ ξ : ℝ, q (-ξ)) = ∫ ξ : ℝ, q ξ :=
    integral_neg_eq_self q volume
  have hanti : (∫ ξ : ℝ, q ξ) = -(∫ ξ : ℝ, q ξ) := by
    calc
      ∫ ξ : ℝ, q ξ = ∫ ξ : ℝ, q (-ξ) := hchange.symm
      _ = ∫ ξ : ℝ, -q ξ := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        exact hodd ξ
      _ = -(∫ ξ : ℝ, q ξ) := by simpa using (integral_neg q)
  linarith

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this identifies the real square-root-Gaussian kernel with its complex
inverse Fourier transform. -/
theorem aux_diagonalSquareRoot_sqrtGaussianKernel_real (x : ℝ) :
    aux_sqrtGaussianKernel x = (aux_sqrtGaussianDecayKernel x : ℂ) := by
  apply Complex.ext
  · simp [aux_sqrtGaussianDecayKernel]
  · change (aux_sqrtGaussianKernel x).im = 0
    apply aux_diagonalSquareRoot_inverseFourier_real_of_even
      (fun ξ : ℝ => 1 - sqrtOneMinusGaussian ξ)
      aux_sqrtGaussianFrequencyProfile_integrable_real
    intro ξ
    simp [sqrtOneMinusGaussian, Codex.Preliminaries.Notation.gaussian]

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this supplies the integrability needed for Fourier convolution of the
square-root-Gaussian kernel. -/
theorem aux_diagonalSquareRoot_sqrtGaussianKernel_integrable : Integrable aux_sqrtGaussianKernel := by
  have hmem := aux_sqrtGaussianDecayKernel_memW0
  have hreal : Integrable aux_sqrtGaussianDecayKernel := by
    refine hmem.2.mono hmem.1.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Codex.aux_wienerEnvelope_nonneg hmem.1 zero_le_one x)] using
      Codex.aux_norm_le_wienerEnvelope hmem.1 zero_le_one x
  apply hreal.ofReal.congr
  filter_upwards [] with x
  exact (aux_diagonalSquareRoot_sqrtGaussianKernel_real x).symm

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this is the square-root identity for the Gaussian factor. -/
theorem aux_diagonalSquareRoot_sqrtGaussian_half (z : ℝ) :
    Real.sqrt (Gaussians.gaussian z) =
      Gaussians.gaussian (z * (Real.sqrt 2)⁻¹) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (aux_gaussian_pos _).le).mp
  rw [Real.sq_sqrt (aux_gaussian_pos _).le]
  unfold Gaussians.gaussian Codex.Preliminaries.Notation.gaussian
  rw [← Real.exp_nat_mul]
  congr 1
  have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  field_simp
  rw [hsqrt]
  ring

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this is the frequency-side factorization with
`r^2 = t_1^2 - t_0^2`. -/
theorem aux_diagonalSquareRoot_frequency_factor {t₀ t₁ r ξ : ℝ}
    (hrsq : r ^ 2 = t₁ ^ 2 - t₀ ^ 2) :
    Real.sqrt (Gaussians.gaussian (t₀ * ξ) - Gaussians.gaussian (t₁ * ξ)) =
      Gaussians.gaussian ((t₀ * (Real.sqrt 2)⁻¹) * ξ) *
        Real.sqrt (1 - Gaussians.gaussian (r * ξ)) := by
  have hprod : Gaussians.gaussian (t₀ * ξ) * Gaussians.gaussian (r * ξ) =
      Gaussians.gaussian (t₁ * ξ) := by
    have ht : t₁ ^ 2 = t₀ ^ 2 + r ^ 2 := by linarith
    have hsq : (t₁ * ξ) ^ 2 = (t₀ * ξ) ^ 2 + (r * ξ) ^ 2 := by
      calc
        (t₁ * ξ) ^ 2 = t₁ ^ 2 * ξ ^ 2 := by ring
        _ = (t₀ ^ 2 + r ^ 2) * ξ ^ 2 := by rw [ht]
        _ = (t₀ * ξ) ^ 2 + (r * ξ) ^ 2 := by ring
    unfold Gaussians.gaussian Codex.Preliminaries.Notation.gaussian
    rw [← Real.exp_add]
    congr 1
    rw [hsq]
    ring
  rw [← hprod]
  have hfactor : Gaussians.gaussian (t₀ * ξ) -
      Gaussians.gaussian (t₀ * ξ) * Gaussians.gaussian (r * ξ) =
      Gaussians.gaussian (t₀ * ξ) * (1 - Gaussians.gaussian (r * ξ)) := by ring
  rw [hfactor]
  rw [Real.sqrt_mul (aux_gaussian_pos _).le]
  congr 1
  convert aux_diagonalSquareRoot_sqrtGaussian_half (t₀ * ξ) using 1 <;> ring

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this evaluates the inverse transform of a scaled Gaussian. -/
theorem aux_diagonalSquareRoot_inverseGaussian_scaled (a x : ℝ) (ha : 0 < a) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => (Gaussians.gaussian (a * ξ) : ℂ)) x =
      (gaussianRescale a x : ℂ) := by
  rw [aux_inverseFourier_comp_mul_pos (fun ξ : ℝ => (Gaussians.gaussian ξ : ℂ)) a x ha]
  have hbase : FourierTransformInv.fourierInv (fun ξ : ℝ => (Gaussians.gaussian ξ : ℂ)) =
      fun x : ℝ => (Gaussians.gaussian x : ℂ) := by
    funext y
    rw [Real.fourierInv_eq_fourier_neg, gaussian_fourier_fixed]
    simp [Codex.Preliminaries.Notation.gaussian]
  rw [hbase]
  simp [gaussianRescale]

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this evaluates the inverse transform of the scaled square-root
Gaussian profile. -/
theorem aux_diagonalSquareRoot_inverseRho_scaled (r x : ℝ) (hr : 0 < r) :
    FourierTransformInv.fourierInv
        (fun ξ : ℝ => aux_sqrtGaussianFrequencyProfile (r * ξ)) x =
      (r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * x) := by
  rw [aux_inverseFourier_comp_mul_pos aux_sqrtGaussianFrequencyProfile r x hr]
  rfl

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this is the integrable linearity of the inverse Fourier transform. -/
theorem aux_diagonalSquareRoot_inverseFourier_sub (f g : ℝ → ℂ) (hf : Integrable f)
    (hg : Integrable g) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => f ξ - g ξ) x =
      FourierTransformInv.fourierInv f x - FourierTransformInv.fourierInv g x := by
  have hphaseCont : Continuous (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫) := by
    apply Real.continuous_fourierChar.comp
    fun_prop
  have hphaseInt {u : ℝ → ℂ} (hu : Integrable u) :
      Integrable (fun ξ : ℝ => 𝐞 ⟪ξ, x⟫ • u ξ) := by
    rw [← integrable_norm_iff]
    · simpa only [Circle.norm_smul] using hu.norm
    · exact hphaseCont.aestronglyMeasurable.smul hu.aestronglyMeasurable
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq,
    ← integral_sub (hphaseInt hf) (hphaseInt hg)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [smul_sub]

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this is the complex-valued Fourier-convolution representation of the
diagonal square-root kernel. -/
theorem aux_diagonalSquareRoot_complexRepresentation {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) :
    let σ : ℝ := t₀ * (Real.sqrt 2)⁻¹
    let r : ℝ := Real.sqrt (t₁ ^ 2 - t₀ ^ 2)
    FourierTransformInv.fourierInv
        (fun ξ : ℝ => (diagonalSquareRootFrequency t₀ t₁ ξ : ℂ)) =
      (fun x : ℝ => (gaussianRescale σ x : ℂ)) -
        ((fun x : ℝ => (gaussianRescale σ x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
          fun x : ℝ => (r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * x)) := by
  dsimp
  let σ : ℝ := t₀ * (Real.sqrt 2)⁻¹
  let r : ℝ := Real.sqrt (t₁ ^ 2 - t₀ ^ 2)
  have ht₀ : 0 < t₀ := by linarith
  have ht₁ : 0 < t₁ := by linarith
  have hrad : 0 ≤ t₁ ^ 2 - t₀ ^ 2 := by
    nlinarith [sq_nonneg (t₁ - t₀), mul_nonneg (show 0 ≤ t₁ + t₀ by linarith)
      (show 0 ≤ t₁ - t₀ by linarith)]
  have hrsq : r ^ 2 = t₁ ^ 2 - t₀ ^ 2 := by
    dsimp [r]
    exact Real.sq_sqrt hrad
  have hr : 0 < r := by
    dsimp [r]
    rw [Real.sqrt_pos]
    nlinarith
  have hσ : 0 < σ := by
    dsimp [σ]
    positivity
  let G : ℝ → ℂ := fun x => (gaussianRescale σ x : ℂ)
  let R : ℝ → ℂ := fun x => (r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * x)
  let ghat : ℝ → ℂ := fun ξ => (Gaussians.gaussian (σ * ξ) : ℂ)
  let rhohat : ℝ → ℂ := fun ξ => aux_sqrtGaussianFrequencyProfile (r * ξ)
  have hGint : Integrable G := by
    have hmem := aux_gaussianRescale_memW0 hσ
    have hreal : Integrable (gaussianRescale σ) := by
      refine hmem.2.mono hmem.1.aestronglyMeasurable (ae_of_all _ fun x => ?_)
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Codex.aux_wienerEnvelope_nonneg hmem.1 zero_le_one x)] using
        Codex.aux_norm_le_wienerEnvelope hmem.1 zero_le_one x
    change Integrable (fun x : ℝ => (gaussianRescale σ x : ℂ))
    exact hreal.ofReal
  have hGcont : Continuous G := by
    change Continuous (fun x : ℝ => (gaussianRescale σ x : ℂ))
    exact Complex.continuous_ofReal.comp (aux_gaussianRescale_memW0 hσ).1
  have hRint : Integrable R := by
    have hcomp : Integrable (fun x : ℝ => aux_sqrtGaussianKernel (r⁻¹ * x)) :=
      aux_diagonalSquareRoot_sqrtGaussianKernel_integrable.comp_mul_left'
        (inv_ne_zero hr.ne')
    change Integrable (fun x : ℝ => (r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * x))
    convert hcomp.smul (r⁻¹ : ℝ) using 1
    ext x
    simp
  have hRcont : Continuous R := by
    have hcomp : Continuous (fun x : ℝ => aux_sqrtGaussianKernel (r⁻¹ * x)) :=
      aux_sqrtGaussianKernel_continuous.comp (continuous_const.mul continuous_id)
    change Continuous (fun x : ℝ => (r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * x))
    exact (show Continuous (fun _ : ℝ => (r⁻¹ : ℝ)) from continuous_const).smul hcomp
  have hghat_int : Integrable ghat := by
    have hbase : Integrable (fun ξ : ℝ => (Gaussians.gaussian ξ : ℂ)) :=
      aux_gaussian_integrable.ofReal
    change Integrable (fun ξ : ℝ => (Gaussians.gaussian (σ * ξ) : ℂ))
    exact hbase.comp_mul_left' hσ.ne'
  have hrhohat_int : Integrable rhohat := by
    simpa [rhohat] using
      (aux_sqrtGaussianFrequencyProfile_integrable.comp_mul_left' hr.ne')
  have hrhohat_cont : Continuous rhohat := by
    dsimp only [rhohat, aux_sqrtGaussianFrequencyProfile]
    exact Complex.continuous_ofReal.comp
      ((continuous_const.sub continuous_sqrtOneMinusGaussian).comp
        (continuous_const.mul continuous_id))
  have hRinv : FourierTransformInv.fourierInv rhohat = R := by
    funext x
    dsimp [rhohat, R]
    exact aux_diagonalSquareRoot_inverseRho_scaled r x hr
  have hFR : FourierTransform.fourier R = rhohat := by
    have heven : ∀ ξ : ℝ, rhohat (-ξ) = rhohat ξ := by
      intro ξ
      dsimp only [rhohat, aux_sqrtGaussianFrequencyProfile]
      simp [sqrtOneMinusGaussian, Codex.Preliminaries.Notation.gaussian]
    have hinv_eq_fourier : FourierTransformInv.fourierInv rhohat =
        FourierTransform.fourier rhohat := by
      rw [Real.fourierInv_eq_fourier_comp_neg]
      congr with ξ
      exact heven ξ
    have hFourierInt : Integrable (FourierTransform.fourier rhohat) := by
      rw [← hinv_eq_fourier, hRinv]
      exact hRint
    rw [← hRinv]
    exact hrhohat_cont.fourier_fourierInv_eq hrhohat_int hFourierInt
  have hFG : FourierTransform.fourier G = ghat := by
    simpa [G, ghat] using gaussianRescale_fourier σ hσ
  have hprod_int : Integrable (fun ξ : ℝ => ghat ξ * rhohat ξ) := by
    refine hghat_int.norm.mono' (hghat_int.aestronglyMeasurable.mul
      hrhohat_int.aestronglyMeasurable) ?_
    filter_upwards [] with ξ
    have hnon : 0 ≤ 1 - sqrtOneMinusGaussian (r * ξ) :=
      aux_one_sub_sqrtOneMinusGaussian_nonneg _
    have hle : 1 - sqrtOneMinusGaussian (r * ξ) ≤ 1 :=
      le_trans (aux_one_sub_sqrtOneMinusGaussian_le_gaussian _)
        (aux_gaussian_le_one _)
    have hnorm : ‖rhohat ξ‖ ≤ 1 := by
      dsimp only [rhohat, aux_sqrtGaussianFrequencyProfile]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnon]
      exact hle
    calc
      ‖ghat ξ * rhohat ξ‖ = ‖ghat ξ‖ * ‖rhohat ξ‖ := norm_mul _ _
      _ ≤ ‖ghat ξ‖ * 1 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ‖ghat ξ‖ := by ring
  have hGbounded : BddAbove (Set.range fun x => ‖G x‖) := by
    refine ⟨σ⁻¹, ?_⟩
    rintro _ ⟨x, rfl⟩
    change ‖(gaussianRescale σ x : ℂ)‖ ≤ σ⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, gaussianRescale,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hσ.le),
      abs_of_nonneg (aux_gaussian_pos _).le]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hσ.le) (aux_gaussian_le_one _)
  have hconv_cont : Continuous (G ⋆[ContinuousLinearMap.mul ℂ ℂ] R) := by
    exact BddAbove.continuous_convolution_left_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) hGbounded hGcont hRint
  have hconv_int : Integrable (G ⋆[ContinuousLinearMap.mul ℂ ℂ] R) :=
    hGint.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hRint
  have hconv_fourier : FourierTransform.fourier (G ⋆[ContinuousLinearMap.mul ℂ ℂ] R) =
      fun ξ : ℝ => ghat ξ * rhohat ξ := by
    funext ξ
    rw [Real.fourier_mul_convolution_eq hGint hRint ξ, hFG, hFR]
  have hinv_product : FourierTransformInv.fourierInv
      (fun ξ : ℝ => ghat ξ * rhohat ξ) = G ⋆[ContinuousLinearMap.mul ℂ ℂ] R := by
    rw [← hconv_fourier]
    apply hconv_cont.fourierInv_fourier_eq hconv_int
    rw [hconv_fourier]
    exact hprod_int
  have hfactor : (fun ξ : ℝ => (diagonalSquareRootFrequency t₀ t₁ ξ : ℂ)) =
      fun ξ : ℝ => ghat ξ - ghat ξ * rhohat ξ := by
    funext ξ
    dsimp [ghat, rhohat]
    rw [diagonalSquareRootFrequency, aux_diagonalSquareRoot_frequency_factor hrsq]
    simp only [aux_sqrtGaussianFrequencyProfile, sqrtOneMinusGaussian]
    push_cast
    ring
  rw [hfactor]
  funext x
  rw [aux_diagonalSquareRoot_inverseFourier_sub ghat
    (fun ξ : ℝ => ghat ξ * rhohat ξ) hghat_int hprod_int x]
  change FourierTransformInv.fourierInv ghat x -
      FourierTransformInv.fourierInv (fun ξ : ℝ => ghat ξ * rhohat ξ) x =
        G x - (G ⋆[ContinuousLinearMap.mul ℂ ℂ] R) x
  have hGinv : FourierTransformInv.fourierInv ghat = G := by
    funext x
    dsimp [ghat, G]
    exact aux_diagonalSquareRoot_inverseGaussian_scaled σ x hσ
  rw [hGinv, hinv_product]

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this is the real rescaling of the square-root-Gaussian kernel used in
the convolution representation. -/
def aux_diagonalSquareRoot_rhoScale (r : ℝ) : ℝ → ℝ :=
  fun x => r⁻¹ * aux_sqrtGaussianDecayKernel (r⁻¹ * x)

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this identifies the complex scaled kernel with the real rescaling. -/
theorem aux_diagonalSquareRoot_rhoScale_complex (r x : ℝ) :
    (r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * x) =
      (aux_diagonalSquareRoot_rhoScale r x : ℂ) := by
  unfold aux_diagonalSquareRoot_rhoScale
  rw [aux_diagonalSquareRoot_sqrtGaussianKernel_real]
  simp [smul_eq_mul]

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this turns the complex convolution in the Fourier representation into
the real convolution used by the manuscript. -/
theorem aux_diagonalSquareRoot_complexConvolution_eq_realConvolution (a r x : ℝ) :
    ((fun y : ℝ => (gaussianRescale a y : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
      fun y : ℝ => (r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * y)) x =
      (∫ y : ℝ, gaussianRescale a (x - y) * aux_diagonalSquareRoot_rhoScale r y : ℝ) := by
  rw [convolution_eq_swap]
  change (∫ y : ℝ, (gaussianRescale a (x - y) : ℂ) *
      ((r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * y))) = _
  rw [show (fun y : ℝ => (gaussianRescale a (x - y) : ℂ) *
      ((r⁻¹ : ℝ) • aux_sqrtGaussianKernel (r⁻¹ * y))) =
      (fun y : ℝ =>
        ((gaussianRescale a (x - y) * aux_diagonalSquareRoot_rhoScale r y : ℝ) : ℂ)) by
        ext y
        rw [aux_diagonalSquareRoot_rhoScale_complex]
        norm_cast]
  exact integral_ofReal

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this is the real convolution representation from the proof. -/
theorem aux_diagonalSquareRoot_representation {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) (x : ℝ) :
    diagonalSquareRoot t₀ t₁ x =
      gaussianRescale (t₀ * (Real.sqrt 2)⁻¹) x -
        ∫ y : ℝ, gaussianRescale (t₀ * (Real.sqrt 2)⁻¹) (x - y) *
          aux_diagonalSquareRoot_rhoScale (Real.sqrt (t₁ ^ 2 - t₀ ^ 2)) y := by
  have h := congrFun (aux_diagonalSquareRoot_complexRepresentation ht hscale) x
  change (FourierTransformInv.fourierInv
      (fun ξ : ℝ => (diagonalSquareRootFrequency t₀ t₁ ξ : ℂ)) x).re = _
  rw [h]
  simp only [Pi.sub_apply, Complex.sub_re, Complex.ofReal_re]
  rw [aux_diagonalSquareRoot_complexConvolution_eq_realConvolution]
  simp

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this rescales the decay estimate for the square-root-Gaussian
kernel. -/
theorem aux_diagonalSquareRoot_rhoScale_nonneg_bound (r y : ℝ) (hr : 0 < r) :
    0 ≤ aux_diagonalSquareRoot_rhoScale r y ∧
      aux_diagonalSquareRoot_rhoScale r y ≤
        C_squareRootGaussianDecay * scaledBracketBump 2 r y := by
  have h := sqrtGaussianDecay.2 (r⁻¹ * y)
  constructor
  · unfold aux_diagonalSquareRoot_rhoScale
    exact mul_nonneg (inv_nonneg.mpr hr.le) h.1
  · unfold aux_diagonalSquareRoot_rhoScale scaledBracketBump
    have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
    calc
      r⁻¹ * aux_sqrtGaussianDecayKernel (r⁻¹ * y) ≤
          r⁻¹ * (C_squareRootGaussianDecay * ((1 + |r⁻¹ * y|)⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left h.2 hinv
      _ = C_squareRootGaussianDecay *
          (r⁻¹ * (1 + |r⁻¹ * y|)⁻¹ ^ 2) := by ring

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this is Gaussian bump decay after positive rescaling. -/
theorem aux_diagonalSquareRoot_gaussianRescale_bound (s x : ℝ) (hs : 0 < s) (N : ℕ) :
    |gaussianRescale s x| ≤ C_gaussianBumpDecay 0 N * scaledBracketBump N s x := by
  have h := gaussianBumpDecay (s⁻¹ * x) 0 N
  rw [iteratedDeriv_zero] at h
  rw [abs_of_pos (aux_gaussian_pos _)] at h
  unfold gaussianRescale scaledBracketBump
  simp only [bracketBump] at h
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hs.le),
    abs_of_nonneg (aux_gaussian_pos _).le]
  calc
    s⁻¹ * Gaussians.gaussian (s⁻¹ * x) ≤
        s⁻¹ * (C_gaussianBumpDecay 0 N * ((1 + |s⁻¹ * x|)⁻¹) ^ N) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs.le)
    _ = C_gaussianBumpDecay 0 N * (s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N) := by
      ac_rfl

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this specializes the real-exponent bracket bump to exponent two. -/
theorem aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq (s x : ℝ) :
    scaledBracketBumpReal 2 s x = scaledBracketBump 2 s x := by
  unfold scaledBracketBumpReal scaledBracketBump
  change s⁻¹ * (1 + |s⁻¹ * x|) ^ (-2 : ℝ) =
    s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ (2 : ℕ)
  rw [Real.rpow_neg_ofNat]
  norm_num

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this supplies an elementary integrable majorant for a scaled
two-bump profile. -/
theorem aux_diagonalSquareRoot_scaledBracketBumpReal_two_le_inv (s x : ℝ) (hs : 0 < s) :
    scaledBracketBumpReal 2 s x ≤ s⁻¹ := by
  unfold scaledBracketBumpReal
  have hbase : 1 ≤ 1 + |s⁻¹ * x| := by linarith [abs_nonneg (s⁻¹ * x)]
  have hpow : (1 + |s⁻¹ * x|) ^ (-2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)
  simpa using mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hs.le)

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this supplies integrability of the two-bump majorant used to control
the convolution. -/
theorem aux_diagonalSquareRoot_scaledBracketBumpReal_product_integrable (sigma r x : ℝ)
    (hsigma : 0 < sigma) (hr : 0 < r) :
    Integrable (fun y : ℝ =>
      scaledBracketBumpReal 2 sigma (x - y) * scaledBracketBumpReal 2 r y) := by
  have hbase : Integrable (fun y : ℝ => scaledBracketBumpReal 2 sigma (x - y)) :=
    aux_integrable_scaledBracketBumpReal_translate 2 sigma x (by norm_num) hsigma
  refine (hbase.const_mul r⁻¹).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    have hleftBase : Continuous (fun y : ℝ => 1 + |sigma⁻¹ * (x - y)|) := by fun_prop
    have hrightBase : Continuous (fun y : ℝ => 1 + |r⁻¹ * y|) := by fun_prop
    have hleft : Continuous (fun y : ℝ => scaledBracketBumpReal 2 sigma (x - y)) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro y
      exact hleftBase.continuousAt.rpow_const (Or.inl (by positivity))
    have hright : Continuous (fun y : ℝ => scaledBracketBumpReal 2 r y) := by
      unfold scaledBracketBumpReal
      apply continuous_const.mul
      rw [continuous_iff_continuousAt]
      intro y
      exact hrightBase.continuousAt.rpow_const (Or.inl (by positivity))
    exact hleft.mul hright
  · filter_upwards [] with y
    have hleft : 0 ≤ scaledBracketBumpReal 2 sigma (x - y) :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hsigma
    have hright : 0 ≤ scaledBracketBumpReal 2 r y :=
      aux_scaledBracketBumpReal_nonneg _ _ _ hr
    have hle := aux_diagonalSquareRoot_scaledBracketBumpReal_two_le_inv r y hr
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft hright)]
    calc
      scaledBracketBumpReal 2 sigma (x - y) * scaledBracketBumpReal 2 r y ≤
          scaledBracketBumpReal 2 sigma (x - y) * r⁻¹ :=
        mul_le_mul_of_nonneg_left hle hleft
      _ = r⁻¹ * scaledBracketBumpReal 2 sigma (x - y) := by ring

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this is the two-bump estimate for the convolution term in the
diagonal representation. -/
theorem aux_diagonalSquareRoot_convolution_bound (sigma r x : ℝ)
    (hsigma : 0 < sigma) (hr : 0 < r) (hsigma_r : sigma ≤ r) :
    |∫ y : ℝ, gaussianRescale sigma (x - y) * aux_diagonalSquareRoot_rhoScale r y| ≤
      C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 r x := by
  let b : ℝ → ℝ := fun y => scaledBracketBumpReal 2 sigma (x - y)
  let c : ℝ → ℝ := fun y => scaledBracketBumpReal 2 r y
  let K : ℝ := C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay
  have hK : 0 ≤ K := by
    dsimp [K, C_gaussianBumpDecay, C_squareRootGaussianDecay]
    positivity
  have hbcInt : Integrable (fun y : ℝ => b y * c y) := by
    simpa [b, c] using
      aux_diagonalSquareRoot_scaledBracketBumpReal_product_integrable sigma r x hsigma hr
  have hmajorInt : Integrable (fun y : ℝ => K * (b y * c y)) := hbcInt.const_mul K
  have hpoint (y : ℝ) :
      |gaussianRescale sigma (x - y) * aux_diagonalSquareRoot_rhoScale r y| ≤
        K * (b y * c y) := by
    have hg0 : 0 ≤ gaussianRescale sigma (x - y) := by
      unfold gaussianRescale
      exact mul_nonneg (inv_nonneg.mpr hsigma.le) (aux_gaussian_pos _).le
    have hg := aux_diagonalSquareRoot_gaussianRescale_bound sigma (x - y) hsigma 2
    rw [abs_of_nonneg hg0] at hg
    have hg' : gaussianRescale sigma (x - y) ≤ C_gaussianBumpDecay 0 2 * b y := by
      simpa [b] using hg.trans_eq (congrArg (fun z => C_gaussianBumpDecay 0 2 * z)
        (aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq sigma (x - y)).symm)
    have hrho := aux_diagonalSquareRoot_rhoScale_nonneg_bound r y hr
    have hrho' : aux_diagonalSquareRoot_rhoScale r y ≤ C_squareRootGaussianDecay * c y := by
      simpa [c] using hrho.2.trans_eq (congrArg (fun z => C_squareRootGaussianDecay * z)
        (aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq r y).symm)
    have hright : 0 ≤ C_squareRootGaussianDecay * c y := le_trans hrho.1 hrho'
    rw [abs_of_nonneg (mul_nonneg hg0 hrho.1)]
    calc
      gaussianRescale sigma (x - y) * aux_diagonalSquareRoot_rhoScale r y ≤
          gaussianRescale sigma (x - y) * (C_squareRootGaussianDecay * c y) :=
        mul_le_mul_of_nonneg_left hrho' hg0
      _ ≤ (C_gaussianBumpDecay 0 2 * b y) * (C_squareRootGaussianDecay * c y) :=
        mul_le_mul_of_nonneg_right hg' hright
      _ = K * (b y * c y) := by
        dsimp [K]
        ac_rfl
  have hnorm : |∫ y : ℝ, gaussianRescale sigma (x - y) *
      aux_diagonalSquareRoot_rhoScale r y| ≤ ∫ y : ℝ, K * (b y * c y) := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le
        (f := fun y : ℝ => gaussianRescale sigma (x - y) *
          aux_diagonalSquareRoot_rhoScale r y)
        hmajorInt (ae_of_all _ hpoint))
  have hbcnon (y : ℝ) : 0 ≤ b y * c y := by
    dsimp [b, c]
    exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hsigma)
      (aux_scaledBracketBumpReal_nonneg _ _ _ hr)
  have hbcIntNon : 0 ≤ ∫ y : ℝ, b y * c y := integral_nonneg hbcnon
  have hEq : (∫ y : ℝ, b y * c y) =
      ∫ y : ℝ, scaledBracketBumpReal 2 r (0 - y) *
        scaledBracketBumpReal 2 sigma (x - y) := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [b, c]
    rw [show 0 - y = -y by ring, aux_scaledBracketBumpReal_neg]
    ring
  have htwo := twoBumpEstimate 0 x r sigma 2 2 hr hsigma hsigma_r
    (by norm_num) (by norm_num)
  have hbcBound : ∫ y : ℝ, b y * c y ≤
      C_twoBumpEstimate 2 2 * scaledBracketBumpReal 2 r x := by
    calc
      ∫ y : ℝ, b y * c y = |∫ y : ℝ, b y * c y| := (abs_of_nonneg hbcIntNon).symm
      _ = |∫ y : ℝ, scaledBracketBumpReal 2 r (0 - y) *
          scaledBracketBumpReal 2 sigma (x - y)| := by rw [hEq]
      _ ≤ C_twoBumpEstimate 2 2 * scaledBracketBumpReal (min 2 2) r (0 - x) := htwo
      _ = C_twoBumpEstimate 2 2 * scaledBracketBumpReal 2 r x := by
        rw [show (min (2 : ℝ) 2) = 2 by norm_num, show 0 - x = -x by ring,
          aux_scaledBracketBumpReal_neg]
  calc
    |∫ y : ℝ, gaussianRescale sigma (x - y) * aux_diagonalSquareRoot_rhoScale r y| ≤
        ∫ y : ℝ, K * (b y * c y) := hnorm
    _ = K * ∫ y : ℝ, b y * c y := by rw [integral_const_mul]
    _ ≤ K * (C_twoBumpEstimate 2 2 * scaledBracketBumpReal 2 r x) :=
      mul_le_mul_of_nonneg_left hbcBound hK
    _ = C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2 *
        scaledBracketBump 2 r x := by
      rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
      dsimp [K]
      ring

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this compares scaled bracket bumps at two comparable positive
scales. -/
theorem aux_scaledBracketBump_scale_le (N : ℕ) {s t A x : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) (hA : 0 ≤ A) (hAt : t ≤ A * s) :
    scaledBracketBump N s x ≤ A * scaledBracketBump N t x := by
  have hinv : t⁻¹ ≤ s⁻¹ := (inv_le_inv₀ ht hs).2 hst
  have habs : |t⁻¹ * x| ≤ |s⁻¹ * x| := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ht), abs_of_pos (inv_pos.mpr hs)]
    exact mul_le_mul_of_nonneg_right hinv (abs_nonneg x)
  have hden : 1 + |t⁻¹ * x| ≤ 1 + |s⁻¹ * x| := by
    simpa [add_comm] using add_le_add_left habs 1
  have hbase : (1 + |s⁻¹ * x|)⁻¹ ≤ (1 + |t⁻¹ * x|)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hden
  have hpow : (1 + |s⁻¹ * x|)⁻¹ ^ N ≤ (1 + |t⁻¹ * x|)⁻¹ ^ N :=
    pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hbase N
  have hratio : t / s ≤ A := by
    apply (div_le_iff₀ hs).2
    simpa [mul_comm] using hAt
  have hinvA : s⁻¹ ≤ A * t⁻¹ := by
    calc
      s⁻¹ = (t / s) * t⁻¹ := by field_simp [hs.ne']
      _ ≤ A * t⁻¹ := mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr ht.le)
  unfold scaledBracketBump
  calc
    s⁻¹ * (1 + |s⁻¹ * x|)⁻¹ ^ N ≤ s⁻¹ * (1 + |t⁻¹ * x|)⁻¹ ^ N :=
      mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hs.le)
    _ ≤ (A * t⁻¹) * (1 + |t⁻¹ * x|)⁻¹ ^ N :=
      mul_le_mul_of_nonneg_right hinvA (pow_nonneg (inv_nonneg.mpr (by positivity)) N)
    _ = A * (t⁻¹ * (1 + |t⁻¹ * x|)⁻¹ ^ N) := by ring

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this records the elementary relations among the two intermediate
scales in the proof. -/
theorem aux_diagonalScaleGeometry {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) :
    let σ := t₀ * (Real.sqrt 2)⁻¹
    let r := Real.sqrt (t₁ ^ 2 - t₀ ^ 2)
    0 < σ ∧ σ ≤ r ∧ r ≤ t₁ ∧
      t₀ ≤ Real.sqrt 2 * σ ∧ t₁ ≤ Real.sqrt 2 * r := by
  dsimp
  have ht₀ : 0 < t₀ := by linarith
  have ht₁ : 0 < t₁ := by linarith
  have hroot₂ : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hroot₂_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hscaleSq : (2 * t₀) ^ 2 ≤ t₁ ^ 2 :=
    (sq_le_sq₀ (by positivity) ht₁.le).2 hscale
  have hrad : 0 < t₁ ^ 2 - t₀ ^ 2 := by
    calc
      t₁ ^ 2 - t₀ ^ 2 = (t₁ - t₀) * (t₁ + t₀) := by ring
      _ > 0 := mul_pos (by linarith) (by positivity)
  have hr : 0 < Real.sqrt (t₁ ^ 2 - t₀ ^ 2) := Real.sqrt_pos.2 hrad
  have hσ : 0 < t₀ * (Real.sqrt 2)⁻¹ :=
    mul_pos ht₀ (inv_pos.mpr hroot₂)
  have hσsq : (t₀ * (Real.sqrt 2)⁻¹) ^ 2 = t₀ ^ 2 / 2 := by
    field_simp [hroot₂.ne']
    nlinarith [hroot₂_sq]
  have hrsq : (Real.sqrt (t₁ ^ 2 - t₀ ^ 2)) ^ 2 = t₁ ^ 2 - t₀ ^ 2 :=
    Real.sq_sqrt hrad.le
  refine ⟨hσ, ?_, ?_, ?_, ?_⟩
  · apply (sq_le_sq₀ hσ.le hr.le).mp
    rw [hσsq, hrsq]
    nlinarith [hscaleSq]
  · apply (sq_le_sq₀ hr.le ht₁.le).mp
    rw [hrsq]
    nlinarith [sq_nonneg t₀]
  · have hid : Real.sqrt 2 * (t₀ * (Real.sqrt 2)⁻¹) = t₀ := by
      calc
        Real.sqrt 2 * (t₀ * (Real.sqrt 2)⁻¹) =
            t₀ * (Real.sqrt 2 * (Real.sqrt 2)⁻¹) := by ring
        _ = t₀ := by rw [mul_inv_cancel₀ hroot₂.ne', mul_one]
    exact hid.symm.le
  · apply (sq_le_sq₀ ht₁.le (mul_nonneg hroot₂.le hr.le)).mp
    rw [mul_pow, hroot₂_sq, hrsq]
    nlinarith [hscaleSq]

/-- For source label `\ref{diagonal square root}` and public theorem
`diagonalSquareRoot_bound`, this applies the scale geometry to the two bump terms. -/
theorem aux_diagonalScaleComparisons (N : ℕ) {t₀ t₁ x : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) :
    scaledBracketBump N (t₀ * (Real.sqrt 2)⁻¹) x ≤
      Real.sqrt 2 * scaledBracketBump N t₀ x ∧
    scaledBracketBump 2 (Real.sqrt (t₁ ^ 2 - t₀ ^ 2)) x ≤
      Real.sqrt 2 * scaledBracketBump 2 t₁ x := by
  obtain ⟨hσ, _hσr, hrt, ht₀σ, ht₁r⟩ := aux_diagonalScaleGeometry ht hscale
  have ht₀ : 0 < t₀ := by linarith
  have ht₁ : 0 < t₁ := by linarith
  have hroot₂ : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hroot₂_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot₂_one : 1 ≤ Real.sqrt 2 := by
    nlinarith [hroot₂_sq, Real.sqrt_nonneg (2 : ℝ)]
  have hσt₀ : t₀ * (Real.sqrt 2)⁻¹ ≤ t₀ := by
    have hinv : (Real.sqrt 2)⁻¹ ≤ 1 := (inv_le_one₀ hroot₂).2 hroot₂_one
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hinv ht₀.le
  constructor
  · exact aux_scaledBracketBump_scale_le N hσ ht₀ hσt₀ hroot₂.le ht₀σ
  · exact aux_scaledBracketBump_scale_le 2
      (Real.sqrt_pos.2 (by
        calc
          t₁ ^ 2 - t₀ ^ 2 = (t₁ - t₀) * (t₁ + t₀) := by ring
          _ > 0 := mul_pos (by linarith) (by positivity)))
      ht₁ hrt hroot₂.le ht₁r

/-- Source label `\ref{diagonal square root}`; the explicit constant used by
`diagonalSquareRoot_bound`. -/
def C_diagonalSquareRoot (N : ℕ) : ℝ :=
  Real.sqrt 2 * max (C_gaussianBumpDecay 0 N)
    (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2)

/--
For all $N\in \mathbb N$ with $N\geq 1$ and $x\in \R$, the following estimate holds:
\begin{equation}\label{E:s-estimate}
    |s(x)|\le  C_{\ref{diagonal square root},N} ( \left<x\right>^N_{(t_0)}+ \left<x\right>^2_{(t_1)}),
\end{equation}
where
$C_{\ref{diagonal square root},N}=\sqrt{2}\max(C_{\ref{Gaussian bump decay},0,N}, C_{\ref{Gaussian bump decay},0,2}C_{\ref{square root of Gaussian decay}}C_{\ref{two bump estimate},2,2})$.
-/
theorem diagonalSquareRoot_bound (N : ℕ) (_hN : 1 ≤ N) {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) (x : ℝ) :
    |diagonalSquareRoot t₀ t₁ x| ≤ C_diagonalSquareRoot N *
      (scaledBracketBump N t₀ x + scaledBracketBump 2 t₁ x) := by
  let σ : ℝ := t₀ * (Real.sqrt 2)⁻¹
  let r : ℝ := Real.sqrt (t₁ ^ 2 - t₀ ^ 2)
  obtain ⟨hσ, hσr, _hrle, _ht₀σ, _ht₁r⟩ := aux_diagonalScaleGeometry ht hscale
  have hr : 0 < r := by
    dsimp [r]
    apply Real.sqrt_pos.2
    calc
      t₁ ^ 2 - t₀ ^ 2 = (t₁ - t₀) * (t₁ + t₀) := by ring
      _ > 0 := mul_pos (by linarith) (by linarith)
  have hgauss := aux_diagonalSquareRoot_gaussianRescale_bound σ x hσ N
  have hconv := aux_diagonalSquareRoot_convolution_bound σ r x hσ hr hσr
  have hrepresentation := aux_diagonalSquareRoot_representation ht hscale x
  have hmain : |diagonalSquareRoot t₀ t₁ x| ≤
      C_gaussianBumpDecay 0 N * scaledBracketBump N σ x +
        (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2) *
          scaledBracketBump 2 r x := by
    rw [hrepresentation]
    refine (show |gaussianRescale σ x -
      ∫ y : ℝ, gaussianRescale σ (x - y) * aux_diagonalSquareRoot_rhoScale r y| ≤
        |gaussianRescale σ x| +
          |∫ y : ℝ, gaussianRescale σ (x - y) * aux_diagonalSquareRoot_rhoScale r y| by
      simpa using (abs_sub_le (gaussianRescale σ x) 0
        (∫ y : ℝ, gaussianRescale σ (x - y) * aux_diagonalSquareRoot_rhoScale r y))).trans ?_
    exact add_le_add hgauss hconv
  obtain ⟨hσscale, hrscale⟩ := aux_diagonalScaleComparisons N ht hscale
  have hA : 0 ≤ C_gaussianBumpDecay 0 N := by
    unfold C_gaussianBumpDecay
    apply mul_nonneg <;> exact Real.rpow_nonneg (by positivity) _
  have hB : 0 ≤ C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay *
      C_twoBumpEstimate 2 2 := by
    have hgauss : 0 ≤ C_gaussianBumpDecay 0 2 := by
      unfold C_gaussianBumpDecay
      apply mul_nonneg <;> exact Real.rpow_nonneg (by positivity) _
    have hsqrt : 0 ≤ C_squareRootGaussianDecay := by
      norm_num [C_squareRootGaussianDecay]
    have htwo : 0 ≤ C_twoBumpEstimate 2 2 := by
      rw [aux_twoBumpEstimate_two_two]
      norm_num
    exact mul_nonneg (mul_nonneg hgauss hsqrt) htwo
  have hσb : 0 ≤ scaledBracketBump N σ x := by
    unfold scaledBracketBump
    positivity
  have hrb : 0 ≤ scaledBracketBump 2 r x := by
    unfold scaledBracketBump
    positivity
  calc
    |diagonalSquareRoot t₀ t₁ x| ≤
        C_gaussianBumpDecay 0 N * scaledBracketBump N σ x +
          (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2) *
            scaledBracketBump 2 r x := hmain
    _ ≤ max (C_gaussianBumpDecay 0 N)
          (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2) *
          scaledBracketBump N σ x +
        max (C_gaussianBumpDecay 0 N)
          (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2) *
          scaledBracketBump 2 r x := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hσb
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hrb
    _ = max (C_gaussianBumpDecay 0 N)
          (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2) *
        (scaledBracketBump N σ x + scaledBracketBump 2 r x) := by ring
    _ ≤ max (C_gaussianBumpDecay 0 N)
          (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2) *
        (Real.sqrt 2 * scaledBracketBump N t₀ x +
          Real.sqrt 2 * scaledBracketBump 2 t₁ x) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hσscale hrscale
      · exact le_trans hA (le_max_left _ _)
    _ = C_diagonalSquareRoot N *
        (scaledBracketBump N t₀ x + scaledBracketBump 2 t₁ x) := by
      rw [C_diagonalSquareRoot]
      ring

/-- For \ref{diagonal square root} and `diagonalSquareRoot_memW0`, this puts a
quadratic scaled bracket bump under an integrable unscaled quadratic majorant. -/
theorem aux_diagonalSquareRoot_scaledBracketBump_two_le_quadratic (t x : ℝ) (ht : 0 < t) :
    scaledBracketBump 2 t x ≤ (t⁻¹ + t) * (1 + x ^ 2)⁻¹ := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hinvt : 0 < t⁻¹ := inv_pos.mpr ht
  have hA : 0 < 1 + |t⁻¹ * x| := by positivity
  have hAsq : 0 < (1 + |t⁻¹ * x|) ^ 2 := sq_pos_of_pos hA
  have hB : 0 < 1 + x ^ 2 := by positivity
  have hxsq : x ^ 2 = t ^ 2 * (t⁻¹ * x) ^ 2 := by field_simp [ht0]
  have hBbound : 1 + x ^ 2 ≤ (1 + t ^ 2) * (1 + |t⁻¹ * x|) ^ 2 := by
    have habsSq : |t⁻¹ * x| ^ 2 = (t⁻¹ * x) ^ 2 := sq_abs _
    rw [hxsq]
    nlinarith [sq_nonneg t, abs_nonneg (t⁻¹ * x), habsSq]
  rw [scaledBracketBump]
  rw [show (1 + |t⁻¹ * x|)⁻¹ ^ (2 : ℕ) = 1 / (1 + |t⁻¹ * x|) ^ 2 by field_simp]
  rw [show (1 + x ^ 2)⁻¹ = 1 / (1 + x ^ 2) by field_simp]
  calc
    t⁻¹ * (1 / (1 + |t⁻¹ * x|) ^ 2) = t⁻¹ / (1 + |t⁻¹ * x|) ^ 2 := by ring
    _ ≤ (t⁻¹ + t) / (1 + x ^ 2) := by
      apply (div_le_div_iff₀ hAsq hB).2
      calc
        t⁻¹ * (1 + x ^ 2) ≤ t⁻¹ * ((1 + t ^ 2) * (1 + |t⁻¹ * x|) ^ 2) :=
          mul_le_mul_of_nonneg_left hBbound hinvt.le
        _ = (t⁻¹ + t) * (1 + |t⁻¹ * x|) ^ 2 := by field_simp [ht0]
    _ = (t⁻¹ + t) * (1 / (1 + x ^ 2)) := by ring

/--
For $t_0,t_1\in\R$ with $0<2t_0\le t_1$ define
\begin{equation}\label{auto:diagonal-square-root-definition} s = \mathcal{F}^{-1}(\xi\mapsto \sqrt{\g(t_0 \xi)- \g(t_1 \xi)}), \end{equation}
where the function under the square root is nonnegative. Then

$s\in W_0(\R)$.
-/
theorem diagonalSquareRoot_memW0 {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) :
    MemW0 (diagonalSquareRoot t₀ t₁) := by
  have ht₀ : 0 < t₀ := by linarith
  have ht₁ : 0 < t₁ := by linarith
  let σ : ℝ := t₀ * (Real.sqrt 2)⁻¹
  have hσ : 0 < σ := by
    dsimp [σ]
    positivity
  have hfreq_cont : Continuous (diagonalSquareRootFrequency t₀ t₁) := by
    unfold diagonalSquareRootFrequency
    apply Continuous.sqrt
    exact (gaussian_continuous.comp (continuous_const.mul continuous_id)).sub
      (gaussian_continuous.comp (continuous_const.mul continuous_id))
  have hfreq_bound (ξ : ℝ) :
      diagonalSquareRootFrequency t₀ t₁ ξ ≤ Gaussians.gaussian (σ * ξ) := by
    have hle : Gaussians.gaussian (t₀ * ξ) - Gaussians.gaussian (t₁ * ξ) ≤
        Gaussians.gaussian (t₀ * ξ) :=
      sub_le_self _ (aux_gaussian_pos _).le
    calc
      diagonalSquareRootFrequency t₀ t₁ ξ ≤ Real.sqrt (Gaussians.gaussian (t₀ * ξ)) :=
        Real.sqrt_le_sqrt hle
      _ = Gaussians.gaussian ((t₀ * (Real.sqrt 2)⁻¹) * ξ) := by
        rw [aux_diagonalSquareRoot_sqrtGaussian_half]
        congr 1
        ring
      _ = Gaussians.gaussian (σ * ξ) := by rfl
  have hfreq_int_real : Integrable (diagonalSquareRootFrequency t₀ t₁) := by
    have hgauss_int : Integrable (fun ξ : ℝ => Gaussians.gaussian (σ * ξ)) :=
      aux_gaussian_integrable.comp_mul_left' hσ.ne'
    refine hgauss_int.mono_nonneg hfreq_cont.aestronglyMeasurable
      (ae_of_all _ fun ξ => Real.sqrt_nonneg _) (ae_of_all _ hfreq_bound)
  have hfreq_int : Integrable (fun ξ : ℝ => (diagonalSquareRootFrequency t₀ t₁ ξ : ℂ)) :=
    hfreq_int_real.ofReal
  have hinv_cont : Continuous (FourierTransformInv.fourierInv
      (fun ξ : ℝ => (diagonalSquareRootFrequency t₀ t₁ ξ : ℂ))) := by
    change Continuous
      (VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ)
        (fun ξ : ℝ => (diagonalSquareRootFrequency t₀ t₁ ξ : ℂ)))
    apply VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    · fun_prop
    · exact hfreq_int
  have hcont : Continuous (diagonalSquareRoot t₀ t₁) := by
    unfold diagonalSquareRoot
    exact Complex.continuous_re.comp hinv_cont
  let c : ℝ := C_diagonalSquareRoot 2 *
    ((t₀⁻¹ + t₀) + (t₁⁻¹ + t₁))
  have hC : 0 ≤ C_diagonalSquareRoot 2 := by
    rw [C_diagonalSquareRoot]
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hfirst : 0 ≤ C_gaussianBumpDecay 0 2 := by
      unfold C_gaussianBumpDecay
      apply mul_nonneg <;> exact Real.rpow_nonneg (by positivity) _
    exact hfirst.trans (le_max_left _ _)
  have hc : 0 ≤ c := by
    dsimp [c]
    apply mul_nonneg hC
    have hsum₀ : 0 ≤ t₀⁻¹ + t₀ := by positivity
    have hsum₁ : 0 ≤ t₁⁻¹ + t₁ := by positivity
    linarith
  have hdecay (x : ℝ) : ‖(diagonalSquareRoot t₀ t₁ x : ℂ)‖ ≤
      c * (1 + x ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hpoint := diagonalSquareRoot_bound 2 (by norm_num) ht hscale x
    have h₀ := aux_diagonalSquareRoot_scaledBracketBump_two_le_quadratic t₀ x ht₀
    have h₁ := aux_diagonalSquareRoot_scaledBracketBump_two_le_quadratic t₁ x ht₁
    calc
      |diagonalSquareRoot t₀ t₁ x| ≤ C_diagonalSquareRoot 2 *
          (scaledBracketBump 2 t₀ x + scaledBracketBump 2 t₁ x) := hpoint
      _ ≤ C_diagonalSquareRoot 2 *
          ((t₀⁻¹ + t₀) * (1 + x ^ 2)⁻¹ +
            (t₁⁻¹ + t₁) * (1 + x ^ 2)⁻¹) := by
        apply mul_le_mul_of_nonneg_left
        · exact add_le_add h₀ h₁
        · exact hC
      _ = c * (1 + x ^ 2)⁻¹ := by
        dsimp [c]
        ring
  have hcomplex : MemW0 (fun x : ℝ => (diagonalSquareRoot t₀ t₁ x : ℂ)) :=
    aux_memW0_of_quadratic_decay c hc (Complex.continuous_ofReal.comp hcont) hdecay
  refine ⟨hcont, ?_⟩
  have hEnvelope : wienerEnvelope (diagonalSquareRoot t₀ t₁) 1 =
      wienerEnvelope (fun x : ℝ => (diagonalSquareRoot t₀ t₁ x : ℂ)) 1 := by
    funext x
    simp [wienerEnvelope, Real.norm_eq_abs]
  rw [hEnvelope]
  exact hcomplex.2

/-- Source label `\ref{derivative of diagonal square root}`; the explicit constant used by
`derivativeDiagonalSquareRoot_bound`. -/
def C_derivativeDiagonalSquareRoot (N : ℕ) : ℝ :=
  2 * max (C_gaussianBumpDecay 1 N)
    (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2)

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this rescales the first-order Gaussian bump estimate. -/
theorem aux_derivativeDiagonalSquareRoot_gaussianRescale_deriv_bound
    (s x : ℝ) (hs : 0 < s) (N : ℕ) :
    |deriv (gaussianRescale s) x| ≤
      s⁻¹ * C_gaussianBumpDecay 1 N * scaledBracketBump N s x := by
  rw [(gaussianRescale_hasDerivAt s x).deriv]
  have hbase := gaussianBumpDecay (s⁻¹ * x) 1 N
  rw [iteratedDeriv_one] at hbase
  rw [(aux_gaussian_hasDerivAt (s⁻¹ * x)).deriv] at hbase
  have hinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  calc
    |s⁻¹ * (-2 * Real.pi * (s⁻¹ * x) * Gaussians.gaussian (s⁻¹ * x)) * s⁻¹| =
        s⁻¹ * |-2 * Real.pi * (s⁻¹ * x) * Gaussians.gaussian (s⁻¹ * x)| * s⁻¹ := by
      rw [abs_mul, abs_mul, abs_of_nonneg hinv]
    _ ≤ s⁻¹ * (C_gaussianBumpDecay 1 N * bracketBump (s⁻¹ * x) ^ N) * s⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hinv) hinv
    _ = s⁻¹ * C_gaussianBumpDecay 1 N * scaledBracketBump N s x := by
      unfold scaledBracketBump bracketBump
      ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this is the telescoping relation for the positive
Gaussian-mixture coefficients. -/
theorem aux_derivativeDiagonalSquareRoot_coefficient_step (n : ℕ) :
    (2 * (n : ℝ) + 2) * aux_sqrtGaussianCoefficient n -
      (2 * ((n + 1 : ℕ) : ℝ) + 2) * aux_sqrtGaussianCoefficient (n + 1) =
        aux_sqrtGaussianCoefficient n := by
  rw [aux_sqrtGaussianCoefficient_succ]
  push_cast
  have hpos : 0 < (n : ℝ) + 2 := by positivity
  field_simp [ne_of_gt hpos]
  ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this evaluates the finite coefficient mass. -/
theorem aux_derivativeDiagonalSquareRoot_coefficient_partialSum (n : ℕ) :
    ∑ i ∈ Finset.range n, aux_sqrtGaussianCoefficient i =
      1 - (2 * (n : ℝ) + 2) * aux_sqrtGaussianCoefficient n := by
  let A : ℕ → ℝ := fun i =>
    (2 * (i : ℝ) + 2) * aux_sqrtGaussianCoefficient i
  calc
    ∑ i ∈ Finset.range n, aux_sqrtGaussianCoefficient i =
        ∑ i ∈ Finset.range n, (A i - A (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (aux_derivativeDiagonalSquareRoot_coefficient_step i).symm
    _ = A 0 - A n := Finset.sum_range_sub' A n
    _ = 1 - (2 * (n : ℝ) + 2) * aux_sqrtGaussianCoefficient n := by
      dsimp [A]
      norm_num [aux_sqrtGaussianCoefficient]

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this gives the finite partial-sum bound for the
positive Gaussian-mixture coefficients. -/
theorem aux_derivativeDiagonalSquareRoot_coefficient_partialSum_le_one (n : ℕ) :
    ∑ i ∈ Finset.range n, aux_sqrtGaussianCoefficient i ≤ 1 := by
  rw [aux_derivativeDiagonalSquareRoot_coefficient_partialSum]
  have hc : 0 ≤ aux_sqrtGaussianCoefficient n :=
    aux_sqrtGaussianCoefficient_nonneg n
  have hfactor : 0 ≤ 2 * (n : ℝ) + 2 := by positivity
  nlinarith [mul_nonneg hfactor hc]

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this makes the positive Gaussian-mixture coefficients
summable. -/
theorem aux_derivativeDiagonalSquareRoot_coefficient_summable :
    Summable aux_sqrtGaussianCoefficient := by
  exact _root_.summable_of_sum_range_le aux_sqrtGaussianCoefficient_nonneg
    aux_derivativeDiagonalSquareRoot_coefficient_partialSum_le_one

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this bounds the total coefficient mass by one. -/
theorem aux_derivativeDiagonalSquareRoot_coefficient_tsum_le_one :
    ∑' n, aux_sqrtGaussianCoefficient n ≤ 1 := by
  exact Real.tsum_le_of_sum_range_le aux_sqrtGaussianCoefficient_nonneg
    aux_derivativeDiagonalSquareRoot_coefficient_partialSum_le_one

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this records positivity of the Gaussian bump constants. -/
theorem aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg (m N : ℕ) :
    0 ≤ C_gaussianBumpDecay m N := by
  unfold C_gaussianBumpDecay
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this bounds a quadratic scaled bracket bump by its
inverse scale. -/
theorem aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv {t x : ℝ}
    (ht : 0 < t) : scaledBracketBump 2 t x ≤ t⁻¹ := by
  rw [← aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
  exact aux_diagonalSquareRoot_scaledBracketBumpReal_two_le_inv t x ht

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this rewrites the scaled quadratic bump in an
unscaled form. -/
theorem aux_derivativeDiagonalSquareRoot_inv_mul_scaledBracketBump_two {t x : ℝ}
    (ht : 0 < t) :
    t⁻¹ * scaledBracketBump 2 t x = (t + |x|)⁻¹ ^ 2 := by
  unfold scaledBracketBump
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le)]
  have hpos : 0 < t + |x| := by positivity
  field_simp [ne_of_gt ht, ne_of_gt hpos]

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this compares a large-scale quadratic bump to the
unscaled bracket bump. -/
theorem aux_derivativeDiagonalSquareRoot_inv_mul_scaledBracketBump_two_le_bracket {t x : ℝ}
    (ht : 1 ≤ t) :
    t⁻¹ * scaledBracketBump 2 t x ≤ bracketBump x ^ 2 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [aux_derivativeDiagonalSquareRoot_inv_mul_scaledBracketBump_two htpos, bracketBump]
  have hleft : 0 < 1 + |x| := by positivity
  have hright : 0 < t + |x| := by positivity
  apply pow_le_pow_left₀ (inv_nonneg.mpr hright.le)
    (inv_le_inv₀ hright hleft |>.mpr ?_) 2
  linarith [abs_nonneg x]

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this gives an unscaled bracket bound for derivatives
of unit-or-larger Gaussian rescalings. -/
theorem aux_derivativeDiagonalSquareRoot_gaussianRescale_deriv_bracket {t x : ℝ}
    (ht : 1 ≤ t) :
    |deriv (gaussianRescale t) x| ≤ C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  calc
    |deriv (gaussianRescale t) x| ≤
        t⁻¹ * C_gaussianBumpDecay 1 2 * scaledBracketBump 2 t x :=
      gaussianRescale_deriv_bound htpos
    _ = C_gaussianBumpDecay 1 2 * (t⁻¹ * scaledBracketBump 2 t x) := by ring
    _ ≤ C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 :=
      mul_le_mul_of_nonneg_left
        (aux_derivativeDiagonalSquareRoot_inv_mul_scaledBracketBump_two_le_bracket ht)
        (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 2)

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this gives the uniform derivative bound for the
Gaussian-mixture terms. -/
theorem aux_derivativeDiagonalSquareRoot_gaussianRescale_deriv_uniform {t x : ℝ}
    (ht : 1 ≤ t) :
    |deriv (gaussianRescale t) x| ≤ C_gaussianBumpDecay 1 2 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hinv : t⁻¹ ≤ 1 := (inv_le_one₀ htpos).mpr ht
  have hsbb : scaledBracketBump 2 t x ≤ t⁻¹ :=
    aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv htpos
  have hleft : 0 ≤ t⁻¹ * C_gaussianBumpDecay 1 2 :=
    mul_nonneg (inv_nonneg.mpr htpos.le)
      (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 2)
  calc
    |deriv (gaussianRescale t) x| ≤
        t⁻¹ * C_gaussianBumpDecay 1 2 * scaledBracketBump 2 t x :=
      gaussianRescale_deriv_bound htpos
    _ = (t⁻¹ * C_gaussianBumpDecay 1 2) * scaledBracketBump 2 t x := by ring
    _ ≤ (t⁻¹ * C_gaussianBumpDecay 1 2) * t⁻¹ :=
      mul_le_mul_of_nonneg_left hsbb hleft
    _ = t⁻¹ * C_gaussianBumpDecay 1 2 * t⁻¹ := by ring
    _ = C_gaussianBumpDecay 1 2 * (t⁻¹ * t⁻¹) := by ring
    _ ≤ C_gaussianBumpDecay 1 2 * 1 :=
      mul_le_mul_of_nonneg_left
        (mul_le_one₀ hinv (inv_nonneg.mpr htpos.le) hinv)
        (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 2)
    _ = C_gaussianBumpDecay 1 2 := by ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this records that every Gaussian scale in the positive
mixture is at least one. -/
theorem aux_derivativeDiagonalSquareRoot_sqrt_succ_one_le (n : ℕ) :
    1 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  apply Real.one_le_sqrt.mpr
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this differentiates the positive Gaussian mixture
termwise. -/
theorem aux_sqrtGaussianDecayKernel_hasDerivAt (x : ℝ) :
    HasDerivAt aux_sqrtGaussianDecayKernel
      (∑' n : ℕ, aux_sqrtGaussianCoefficient n *
        deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x) x := by
  let g : ℕ → ℝ → ℝ := fun n z => aux_sqrtGaussianCoefficient n *
    gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ)) z
  let g' : ℕ → ℝ → ℝ := fun n z => aux_sqrtGaussianCoefficient n *
    deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) z
  let c : ℝ := C_gaussianBumpDecay 1 2
  have hsum : Summable (fun n : ℕ => c * aux_sqrtGaussianCoefficient n) :=
    aux_derivativeDiagonalSquareRoot_coefficient_summable.mul_left c
  have htsum : HasDerivAt (fun z : ℝ => ∑' n : ℕ, g n z) (∑' n : ℕ, g' n x) x := by
    refine hasDerivAt_tsum (g := g) (g' := g') (y₀ := 0) hsum ?_ ?_ ?_ x
    · intro n y
      dsimp [g, g']
      rw [(gaussianRescale_hasDerivAt (Real.sqrt ((n + 1 : ℕ) : ℝ)) y).deriv]
      exact (gaussianRescale_hasDerivAt (Real.sqrt ((n + 1 : ℕ) : ℝ)) y).const_mul
        (aux_sqrtGaussianCoefficient n)
    · intro n y
      simp only [g', Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (aux_sqrtGaussianCoefficient_nonneg n)]
      have h := aux_derivativeDiagonalSquareRoot_gaussianRescale_deriv_uniform
        (x := y) (aux_derivativeDiagonalSquareRoot_sqrt_succ_one_le n)
      calc
        aux_sqrtGaussianCoefficient n *
            |deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) y| ≤
            aux_sqrtGaussianCoefficient n * c :=
          mul_le_mul_of_nonneg_left (by simpa only [c] using h)
            (aux_sqrtGaussianCoefficient_nonneg n)
        _ = c * aux_sqrtGaussianCoefficient n := by ring
    · simpa only [g, Nat.cast_add, Nat.cast_one] using
        (aux_sqrtGaussianDecayKernel_hasSum 0).summable
  have hfun : (fun z : ℝ => ∑' n : ℕ, g n z) = aux_sqrtGaussianDecayKernel := by
    funext z
    simpa only [g, Nat.cast_add, Nat.cast_one] using
      (aux_sqrtGaussianDecayKernel_hasSum z).tsum_eq
  rw [hfun] at htsum
  simpa only [g'] using htsum

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this supplies summability of the differentiated
Gaussian-mixture terms. -/
theorem aux_derivativeDiagonalSquareRoot_derivTerms_summable (x : ℝ) : Summable
    (fun n : ℕ => aux_sqrtGaussianCoefficient n *
      deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x) := by
  let c : ℝ := C_gaussianBumpDecay 1 2
  refine (aux_derivativeDiagonalSquareRoot_coefficient_summable.mul_left c).of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (aux_sqrtGaussianCoefficient_nonneg n)]
  have h := aux_derivativeDiagonalSquareRoot_gaussianRescale_deriv_uniform
    (x := x) (aux_derivativeDiagonalSquareRoot_sqrt_succ_one_le n)
  calc
    aux_sqrtGaussianCoefficient n *
        |deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x| ≤
        aux_sqrtGaussianCoefficient n * c :=
      mul_le_mul_of_nonneg_left (by simpa only [c] using h)
        (aux_sqrtGaussianCoefficient_nonneg n)
    _ = c * aux_sqrtGaussianCoefficient n := by ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this majorizes one differentiated Gaussian-mixture term. -/
theorem aux_derivativeDiagonalSquareRoot_derivTerm_le_bracket (x : ℝ) (n : ℕ) :
    |aux_sqrtGaussianCoefficient n *
        deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x| ≤
      C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 *
        aux_sqrtGaussianCoefficient n := by
  rw [abs_mul, abs_of_nonneg (aux_sqrtGaussianCoefficient_nonneg n)]
  have h := aux_derivativeDiagonalSquareRoot_gaussianRescale_deriv_bracket
    (x := x) (aux_derivativeDiagonalSquareRoot_sqrt_succ_one_le n)
  calc
    aux_sqrtGaussianCoefficient n *
        |deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x| ≤
        aux_sqrtGaussianCoefficient n *
          (C_gaussianBumpDecay 1 2 * bracketBump x ^ 2) :=
      mul_le_mul_of_nonneg_left h (aux_sqrtGaussianCoefficient_nonneg n)
    _ = C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 *
        aux_sqrtGaussianCoefficient n := by ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this makes the bracket majorant for differentiated
mixture terms summable. -/
theorem aux_derivativeDiagonalSquareRoot_derivTerms_majorant_summable (x : ℝ) : Summable
    (fun n : ℕ => C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 *
      aux_sqrtGaussianCoefficient n) :=
  aux_derivativeDiagonalSquareRoot_coefficient_summable.mul_left
    (C_gaussianBumpDecay 1 2 * bracketBump x ^ 2)

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this identifies the derivative of the square-root
Gaussian kernel with its differentiated mixture. -/
theorem aux_derivativeDiagonalSquareRoot_kernel_deriv_eq_tsum (x : ℝ) :
    deriv aux_sqrtGaussianDecayKernel x =
      ∑' n : ℕ, aux_sqrtGaussianCoefficient n *
        deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x :=
  (aux_sqrtGaussianDecayKernel_hasDerivAt x).deriv

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this is the quadratic derivative bound for the
square-root Gaussian kernel. -/
theorem aux_sqrtGaussianDecayKernel_deriv_bound (x : ℝ) :
    |deriv aux_sqrtGaussianDecayKernel x| ≤
      C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 := by
  have hsumAbs :
      |∑' n : ℕ, aux_sqrtGaussianCoefficient n *
          deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x| ≤
        ∑' n : ℕ, |aux_sqrtGaussianCoefficient n *
          deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x| :=
    norm_tsum_le_tsum_norm
      (aux_derivativeDiagonalSquareRoot_derivTerms_summable x).norm
  have hmajorant :
      ∑' n : ℕ, |aux_sqrtGaussianCoefficient n *
          deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x| ≤
        ∑' n : ℕ, C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 *
          aux_sqrtGaussianCoefficient n :=
    Summable.tsum_le_tsum
      (aux_derivativeDiagonalSquareRoot_derivTerm_le_bracket x)
      (aux_derivativeDiagonalSquareRoot_derivTerms_summable x).norm
      (aux_derivativeDiagonalSquareRoot_derivTerms_majorant_summable x)
  have hlast :
      ∑' n : ℕ, C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 *
          aux_sqrtGaussianCoefficient n ≤ C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 := by
    calc
      ∑' n : ℕ, C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 *
          aux_sqrtGaussianCoefficient n = C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 *
          ∑' n : ℕ, aux_sqrtGaussianCoefficient n := by
        rw [tsum_mul_left]
      _ ≤ C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left
          aux_derivativeDiagonalSquareRoot_coefficient_tsum_le_one
          (mul_nonneg (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 2)
            (sq_nonneg (bracketBump x)))
      _ = C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 := by ring
  calc
    |deriv aux_sqrtGaussianDecayKernel x| =
        |∑' n : ℕ, aux_sqrtGaussianCoefficient n *
          deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x| := by
      rw [aux_derivativeDiagonalSquareRoot_kernel_deriv_eq_tsum]
    _ ≤ ∑' n : ℕ, |aux_sqrtGaussianCoefficient n *
        deriv (gaussianRescale (Real.sqrt ((n + 1 : ℕ) : ℝ))) x| := hsumAbs
    _ ≤ ∑' n : ℕ, C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 *
        aux_sqrtGaussianCoefficient n := hmajorant
    _ ≤ C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 := hlast

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this applies the chain rule to the scaled
square-root Gaussian kernel. -/
theorem aux_diagonalSquareRoot_rhoScale_hasDerivAt (r x : ℝ) (_hr : 0 < r) :
    HasDerivAt (aux_diagonalSquareRoot_rhoScale r)
      (r⁻¹ * deriv aux_sqrtGaussianDecayKernel (r⁻¹ * x) * r⁻¹) x := by
  unfold aux_diagonalSquareRoot_rhoScale
  have hbase : HasDerivAt aux_sqrtGaussianDecayKernel
      (deriv aux_sqrtGaussianDecayKernel (r⁻¹ * x)) (r⁻¹ * x) := by
    rw [(aux_sqrtGaussianDecayKernel_hasDerivAt (r⁻¹ * x)).deriv]
    exact aux_sqrtGaussianDecayKernel_hasDerivAt _
  simpa only [Function.comp_apply, mul_assoc] using
    (hbase.comp x (hasDerivAt_const_mul r⁻¹)).const_mul r⁻¹

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this transports the kernel derivative bound through
the positive rescaling. -/
theorem aux_diagonalSquareRoot_rhoScale_deriv_bound {r x : ℝ} (hr : 0 < r) :
    |deriv (aux_diagonalSquareRoot_rhoScale r) x| ≤
      C_gaussianBumpDecay 1 2 * r⁻¹ * scaledBracketBump 2 r x := by
  rw [(aux_diagonalSquareRoot_rhoScale_hasDerivAt r x hr).deriv]
  have hrinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  calc
    |r⁻¹ * deriv aux_sqrtGaussianDecayKernel (r⁻¹ * x) * r⁻¹| =
        r⁻¹ * r⁻¹ * |deriv aux_sqrtGaussianDecayKernel (r⁻¹ * x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hrinv]
      ring
    _ ≤ r⁻¹ * r⁻¹ *
        (C_gaussianBumpDecay 1 2 * bracketBump (r⁻¹ * x) ^ 2) :=
      mul_le_mul_of_nonneg_left (aux_sqrtGaussianDecayKernel_deriv_bound _)
        (mul_nonneg hrinv hrinv)
    _ = C_gaussianBumpDecay 1 2 * r⁻¹ * scaledBracketBump 2 r x := by
      unfold scaledBracketBump bracketBump
      ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_differentiable`, this differentiates a noncompact scalar
convolution using an integrable Gaussian majorant. -/
theorem aux_derivativeDiagonalSquareRoot_hasDerivAt_integral_convolution_right
    (f g : ℝ → ℝ) (x A B : ℝ) (hf : Integrable f)
    (hg : Continuous g)
    (hgBound : ∀ z : ℝ, |g z| ≤ A)
    (hgDeriv : ∀ z : ℝ, HasDerivAt g (deriv g z) z)
    (hgDerivBound : ∀ z : ℝ, |deriv g z| ≤ B) :
    Integrable (fun y : ℝ => f y * deriv g (x - y)) ∧
      HasDerivAt (fun z : ℝ => ∫ y : ℝ, f y * g (z - y))
        (∫ y : ℝ, f y * deriv g (x - y)) x := by
  let F : ℝ → ℝ → ℝ := fun z y => f y * g (z - y)
  let F' : ℝ → ℝ → ℝ := fun z y => f y * deriv g (z - y)
  have hFmeas (z : ℝ) : AEStronglyMeasurable (F z) volume := by
    apply hf.aestronglyMeasurable.mul
    exact (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hFint : Integrable (F x) := by
    refine (hf.norm.const_mul A).mono' (hFmeas x) ?_
    filter_upwards [] with y
    dsimp [F]
    change |f y * g (x - y)| ≤ A * |f y|
    rw [abs_mul]
    calc
      |f y| * |g (x - y)| ≤ |f y| * A :=
        mul_le_mul_of_nonneg_left (hgBound _) (abs_nonneg _)
      _ = A * ‖f y‖ := by rw [Real.norm_eq_abs]; ring
  have hF'derivMeas : AEStronglyMeasurable (F' x) volume := by
    apply hf.aestronglyMeasurable.mul
    exact ((stronglyMeasurable_deriv g).comp_measurable
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hboundInt : Integrable (fun y : ℝ => B * ‖f y‖) := hf.norm.const_mul B
  have hbound : ∀ᵐ y : ℝ ∂volume, ∀ z ∈ Set.univ,
      ‖F' z y‖ ≤ B * ‖f y‖ := by
    filter_upwards [] with y z hz
    dsimp [F']
    rw [abs_mul]
    calc
      |f y| * |deriv g (z - y)| ≤ |f y| * B :=
        mul_le_mul_of_nonneg_left (hgDerivBound _) (abs_nonneg _)
      _ = B * |f y| := by ring
  have hdiff : ∀ᵐ y : ℝ ∂volume, ∀ z ∈ Set.univ,
      HasDerivAt (F · y) (F' z y) z := by
    filter_upwards [] with y z hz
    dsimp [F, F']
    simpa using
      ((hgDeriv (z - y)).comp z ((hasDerivAt_id z).sub (hasDerivAt_const z y))).const_mul (f y)
  obtain ⟨hderivInt, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (bound := fun y : ℝ => B * ‖f y‖)
    (s := Set.univ) (x₀ := x) univ_mem
    (Filter.Eventually.of_forall hFmeas) hFint hF'derivMeas hbound hboundInt hdiff
  simpa only [F, F'] using ⟨hderivInt, hderiv⟩

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_differentiable`, this gives a uniform bound for the scaled
square-root Gaussian kernel. -/
theorem aux_derivativeDiagonalSquareRoot_rhoScale_abs_uniform {r x : ℝ} (hr : 0 < r) :
    |aux_diagonalSquareRoot_rhoScale r x| ≤ C_squareRootGaussianDecay * r⁻¹ := by
  have h := aux_diagonalSquareRoot_rhoScale_nonneg_bound r x hr
  rw [abs_of_nonneg h.1]
  have hC : 0 ≤ C_squareRootGaussianDecay := by
    rw [C_squareRootGaussianDecay]
    norm_num
  calc
    aux_diagonalSquareRoot_rhoScale r x ≤
        C_squareRootGaussianDecay * scaledBracketBump 2 r x := h.2
    _ ≤ C_squareRootGaussianDecay * r⁻¹ :=
      mul_le_mul_of_nonneg_left
        (aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv hr) hC

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_differentiable`, this turns the scaled kernel derivative
estimate into a uniform bound. -/
theorem aux_derivativeDiagonalSquareRoot_rhoScale_deriv_uniform {r x : ℝ} (hr : 0 < r) :
    |deriv (aux_diagonalSquareRoot_rhoScale r) x| ≤
      C_gaussianBumpDecay 1 2 * r⁻¹ * r⁻¹ := by
  calc
    |deriv (aux_diagonalSquareRoot_rhoScale r) x| ≤
        C_gaussianBumpDecay 1 2 * r⁻¹ * scaledBracketBump 2 r x :=
      aux_diagonalSquareRoot_rhoScale_deriv_bound hr
    _ = (C_gaussianBumpDecay 1 2 * r⁻¹) * scaledBracketBump 2 r x := by ring
    _ ≤ (C_gaussianBumpDecay 1 2 * r⁻¹) * r⁻¹ :=
      mul_le_mul_of_nonneg_left
        (aux_derivativeDiagonalSquareRoot_scaledBracketBump_two_le_inv hr)
        (mul_nonneg (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 2)
          (inv_nonneg.mpr hr.le))
    _ = C_gaussianBumpDecay 1 2 * r⁻¹ * r⁻¹ := by ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_differentiable`, this extracts integrability of a positive
Gaussian rescaling from its Wiener-space membership. -/
theorem aux_derivativeDiagonalSquareRoot_gaussianRescale_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (gaussianRescale s) := by
  have hmem := aux_gaussianRescale_memW0 hs
  refine hmem.2.mono hmem.1.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Codex.aux_wienerEnvelope_nonneg hmem.1 zero_le_one x)] using
      Codex.aux_norm_le_wienerEnvelope hmem.1 zero_le_one x

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_differentiable`, this flips the real convolution to put the
derivative on the scaled square-root Gaussian kernel. -/
theorem aux_derivativeDiagonalSquareRoot_convolution_flip (s r x : ℝ) :
    (∫ y : ℝ, gaussianRescale s (x - y) * aux_diagonalSquareRoot_rhoScale r y) =
      ∫ y : ℝ, gaussianRescale s y * aux_diagonalSquareRoot_rhoScale r (x - y) := by
  rw [← integral_sub_left_eq_self
    (fun y : ℝ => gaussianRescale s y * aux_diagonalSquareRoot_rhoScale r (x - y)) volume x]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_differentiable`, this differentiates the convolution term in the
diagonal representation. -/
theorem aux_derivativeDiagonalSquareRoot_convolution_hasDerivAt (s r x : ℝ)
    (hs : 0 < s) (hr : 0 < r) :
    Integrable (fun y : ℝ => gaussianRescale s y *
      deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)) ∧
      HasDerivAt (fun z : ℝ => ∫ y : ℝ, gaussianRescale s y *
        aux_diagonalSquareRoot_rhoScale r (z - y))
        (∫ y : ℝ, gaussianRescale s y *
          deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)) x := by
  have hdiff : Differentiable ℝ (aux_diagonalSquareRoot_rhoScale r) :=
    fun z => (aux_diagonalSquareRoot_rhoScale_hasDerivAt r z hr).differentiableAt
  have hderiv (z : ℝ) : HasDerivAt (aux_diagonalSquareRoot_rhoScale r)
      (deriv (aux_diagonalSquareRoot_rhoScale r) z) z := by
    rw [(aux_diagonalSquareRoot_rhoScale_hasDerivAt r z hr).deriv]
    exact aux_diagonalSquareRoot_rhoScale_hasDerivAt r z hr
  exact aux_derivativeDiagonalSquareRoot_hasDerivAt_integral_convolution_right
    (gaussianRescale s) (aux_diagonalSquareRoot_rhoScale r) x
    (C_squareRootGaussianDecay * r⁻¹)
    (C_gaussianBumpDecay 1 2 * r⁻¹ * r⁻¹)
    (aux_derivativeDiagonalSquareRoot_gaussianRescale_integrable hs) hdiff.continuous
    (fun z => aux_derivativeDiagonalSquareRoot_rhoScale_abs_uniform (x := z) hr)
    hderiv
    (fun z => aux_derivativeDiagonalSquareRoot_rhoScale_deriv_uniform (x := z) hr)

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this is the two-bump bound for the differentiated
convolution in the diagonal representation. -/
theorem aux_derivativeDiagonalSquareRoot_derivativeConvolution_bound (sigma r x : ℝ)
    (hsigma : 0 < sigma) (hr : 0 < r) (hsigma_r : sigma ≤ r) :
    |∫ y : ℝ, gaussianRescale sigma y *
        deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| ≤
      C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2 *
        r⁻¹ * scaledBracketBump 2 r x := by
  let b : ℝ → ℝ := fun y => scaledBracketBumpReal 2 r (x - y)
  let c : ℝ → ℝ := fun y => scaledBracketBumpReal 2 sigma y
  let K : ℝ := C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * r⁻¹
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 0 2)
        (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 2))
      (inv_nonneg.mpr hr.le)
  have hbcInt : Integrable (fun y : ℝ => b y * c y) := by
    simpa [b, c] using
      aux_diagonalSquareRoot_scaledBracketBumpReal_product_integrable r sigma x hr hsigma
  have hmajorInt : Integrable (fun y : ℝ => K * (b y * c y)) := hbcInt.const_mul K
  have hpoint (y : ℝ) :
      |gaussianRescale sigma y * deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| ≤
        K * (b y * c y) := by
    have hgaussNonneg : 0 ≤ gaussianRescale sigma y := by
      unfold gaussianRescale
      exact mul_nonneg (inv_nonneg.mpr hsigma.le) (aux_gaussian_pos _).le
    have hgauss := aux_diagonalSquareRoot_gaussianRescale_bound sigma y hsigma 2
    rw [abs_of_nonneg hgaussNonneg] at hgauss
    have hgauss' : gaussianRescale sigma y ≤ C_gaussianBumpDecay 0 2 * c y := by
      simpa [c] using hgauss.trans_eq (congrArg (fun z => C_gaussianBumpDecay 0 2 * z)
        (aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq sigma y).symm)
    have hdriv := aux_diagonalSquareRoot_rhoScale_deriv_bound (r := r) (x := x - y) hr
    have hdriv' : |deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| ≤
        C_gaussianBumpDecay 1 2 * r⁻¹ * b y := by
      simpa [b] using hdriv.trans_eq (congrArg
        (fun z => C_gaussianBumpDecay 1 2 * r⁻¹ * z)
        (aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq r (x - y)).symm)
    have hright : 0 ≤ C_gaussianBumpDecay 1 2 * r⁻¹ * b y := by
      apply mul_nonneg
      · exact mul_nonneg (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 2)
          (inv_nonneg.mpr hr.le)
      · dsimp [b]
        exact aux_scaledBracketBumpReal_nonneg _ _ _ hr
    rw [abs_mul, abs_of_nonneg hgaussNonneg]
    calc
      gaussianRescale sigma y * |deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| ≤
          gaussianRescale sigma y * (C_gaussianBumpDecay 1 2 * r⁻¹ * b y) :=
        mul_le_mul_of_nonneg_left hdriv' hgaussNonneg
      _ ≤ (C_gaussianBumpDecay 0 2 * c y) *
          (C_gaussianBumpDecay 1 2 * r⁻¹ * b y) :=
        mul_le_mul_of_nonneg_right hgauss' hright
      _ = K * (b y * c y) := by
        dsimp [K]
        ring
  have hnorm : |∫ y : ℝ, gaussianRescale sigma y *
      deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| ≤
      ∫ y : ℝ, K * (b y * c y) := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le
        (f := fun y : ℝ => gaussianRescale sigma y *
          deriv (aux_diagonalSquareRoot_rhoScale r) (x - y))
        hmajorInt (ae_of_all _ hpoint))
  have hbcnon (y : ℝ) : 0 ≤ b y * c y := by
    dsimp [b, c]
    exact mul_nonneg (aux_scaledBracketBumpReal_nonneg _ _ _ hr)
      (aux_scaledBracketBumpReal_nonneg _ _ _ hsigma)
  have hbcIntNon : 0 ≤ ∫ y : ℝ, b y * c y := integral_nonneg hbcnon
  have hEq : (∫ y : ℝ, b y * c y) =
      ∫ y : ℝ, scaledBracketBumpReal 2 r (x - y) *
        scaledBracketBumpReal 2 sigma (0 - y) := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [b, c]
    rw [show 0 - y = -y by ring, aux_scaledBracketBumpReal_neg]
  have htwo := twoBumpEstimate x 0 r sigma 2 2 hr hsigma hsigma_r
    (by norm_num) (by norm_num)
  have hbcBound : ∫ y : ℝ, b y * c y ≤
      C_twoBumpEstimate 2 2 * scaledBracketBumpReal 2 r x := by
    calc
      ∫ y : ℝ, b y * c y = |∫ y : ℝ, b y * c y| := (abs_of_nonneg hbcIntNon).symm
      _ = |∫ y : ℝ, scaledBracketBumpReal 2 r (x - y) *
          scaledBracketBumpReal 2 sigma (0 - y)| := by rw [hEq]
      _ ≤ C_twoBumpEstimate 2 2 * scaledBracketBumpReal (min 2 2) r (x - 0) := htwo
      _ = C_twoBumpEstimate 2 2 * scaledBracketBumpReal 2 r x := by norm_num
  calc
    |∫ y : ℝ, gaussianRescale sigma y *
        deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| ≤
        ∫ y : ℝ, K * (b y * c y) := hnorm
    _ = K * ∫ y : ℝ, b y * c y := by rw [integral_const_mul]
    _ ≤ K * (C_twoBumpEstimate 2 2 * scaledBracketBumpReal 2 r x) :=
      mul_le_mul_of_nonneg_left hbcBound hK
    _ = C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2 *
        r⁻¹ * scaledBracketBump 2 r x := by
      rw [aux_diagonalSquareRoot_scaledBracketBumpReal_two_eq]
      dsimp [K]
      ring

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_differentiable`, this differentiates the diagonal square-root
representation. -/
theorem aux_derivativeDiagonalSquareRoot_hasDerivAt {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) (x : ℝ) :
    HasDerivAt (diagonalSquareRoot t₀ t₁)
      (deriv (gaussianRescale (t₀ * (Real.sqrt 2)⁻¹)) x -
        ∫ y : ℝ, gaussianRescale (t₀ * (Real.sqrt 2)⁻¹) y *
          deriv (aux_diagonalSquareRoot_rhoScale (Real.sqrt (t₁ ^ 2 - t₀ ^ 2))) (x - y)) x := by
  let sigma : ℝ := t₀ * (Real.sqrt 2)⁻¹
  let r : ℝ := Real.sqrt (t₁ ^ 2 - t₀ ^ 2)
  obtain ⟨hsigma, _hsigma_r, _hr_le, _ht₀_sigma, _ht₁_r⟩ :=
    aux_diagonalScaleGeometry ht hscale
  have hr : 0 < r := by
    dsimp [r]
    apply Real.sqrt_pos.2
    calc
      t₁ ^ 2 - t₀ ^ 2 = (t₁ - t₀) * (t₁ + t₀) := by ring
      _ > 0 := mul_pos (by linarith) (by linarith)
  obtain ⟨_hconvInt, hconv⟩ :=
    aux_derivativeDiagonalSquareRoot_convolution_hasDerivAt sigma r x hsigma hr
  have hgauss : HasDerivAt (gaussianRescale sigma)
      (deriv (gaussianRescale sigma) x) x := by
    rw [(gaussianRescale_hasDerivAt sigma x).deriv]
    exact gaussianRescale_hasDerivAt sigma x
  have hrepresentation : diagonalSquareRoot t₀ t₁ = fun z : ℝ =>
      gaussianRescale sigma z - ∫ y : ℝ, gaussianRescale sigma y *
        aux_diagonalSquareRoot_rhoScale r (z - y) := by
    funext z
    dsimp [sigma, r]
    rw [aux_diagonalSquareRoot_representation ht hscale z,
      aux_derivativeDiagonalSquareRoot_convolution_flip]
  rw [hrepresentation]
  exact hgauss.sub hconv

/-- For source label `\ref{derivative of diagonal square root}` and public theorem
`derivativeDiagonalSquareRoot_bound`, this establishes the differentiability needed to
interpret the manuscript's derivative. -/
theorem derivativeDiagonalSquareRoot_differentiable {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) :
    Differentiable ℝ (diagonalSquareRoot t₀ t₁) :=
  fun x => (aux_derivativeDiagonalSquareRoot_hasDerivAt ht hscale x).differentiableAt

/--
Let $t_0,t_1,s$ be as in Proposition \ref{diagonal square root}.
Then for all $N\in\N$ with $N\ge1$ and all $x\in\R$:
\begin{equation}\label{E:s-derivative-estimate}
    |s'(x)|\le  C_{\ref{derivative of diagonal square root},N}
    ( t_0^{-1} \left<x\right>^N_{(t_0)}+ t_1^{-1}\left<x\right>^2_{(t_1)}),
\end{equation}
where
$C_{\ref{derivative of diagonal square root},N}
=2\max\bigl(C_{\ref{Gaussian bump decay},1,N},
C_{\ref{Gaussian bump decay},0,2}C_{\ref{Gaussian bump decay},1,2}
C_{\ref{two bump estimate},2,2}\bigr).$
-/
theorem derivativeDiagonalSquareRoot_bound (N : ℕ) (_hN : 1 ≤ N) {t₀ t₁ : ℝ}
    (ht : 0 < 2 * t₀) (hscale : 2 * t₀ ≤ t₁) (x : ℝ) :
    |deriv (diagonalSquareRoot t₀ t₁) x| ≤
      C_derivativeDiagonalSquareRoot N *
        (t₀⁻¹ * scaledBracketBump N t₀ x + t₁⁻¹ * scaledBracketBump 2 t₁ x) := by
  let sigma : ℝ := t₀ * (Real.sqrt 2)⁻¹
  let r : ℝ := Real.sqrt (t₁ ^ 2 - t₀ ^ 2)
  obtain ⟨hsigma, hsigma_r, _hr_le, _ht₀_sigma, ht₁_r⟩ :=
    aux_diagonalScaleGeometry ht hscale
  have ht₀ : 0 < t₀ := by linarith
  have ht₁ : 0 < t₁ := by linarith
  have hr : 0 < r := by
    dsimp [r]
    apply Real.sqrt_pos.2
    calc
      t₁ ^ 2 - t₀ ^ 2 = (t₁ - t₀) * (t₁ + t₀) := by ring
      _ > 0 := mul_pos (by linarith) (by linarith)
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hroot_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot_mul : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [hroot_sq]
  have hgauss := aux_derivativeDiagonalSquareRoot_gaussianRescale_deriv_bound
    sigma x hsigma N
  have hconv := aux_derivativeDiagonalSquareRoot_derivativeConvolution_bound
    sigma r x hsigma hr hsigma_r
  have hderiv := aux_derivativeDiagonalSquareRoot_hasDerivAt ht hscale x
  have hmain : |deriv (diagonalSquareRoot t₀ t₁) x| ≤
      C_gaussianBumpDecay 1 N *
          (sigma⁻¹ * scaledBracketBump N sigma x) +
        (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2) *
          (r⁻¹ * scaledBracketBump 2 r x) := by
    rw [hderiv.deriv]
    refine (show |deriv (gaussianRescale sigma) x -
        ∫ y : ℝ, gaussianRescale sigma y *
          deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| ≤
        |deriv (gaussianRescale sigma) x| +
          |∫ y : ℝ, gaussianRescale sigma y *
            deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| by
      simpa using (abs_sub_le (deriv (gaussianRescale sigma) x) 0
        (∫ y : ℝ, gaussianRescale sigma y *
          deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)))).trans ?_
    calc
      |deriv (gaussianRescale sigma) x| +
          |∫ y : ℝ, gaussianRescale sigma y *
            deriv (aux_diagonalSquareRoot_rhoScale r) (x - y)| ≤
          sigma⁻¹ * C_gaussianBumpDecay 1 N * scaledBracketBump N sigma x +
            C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2 *
              r⁻¹ * scaledBracketBump 2 r x :=
        add_le_add hgauss hconv
      _ = C_gaussianBumpDecay 1 N *
          (sigma⁻¹ * scaledBracketBump N sigma x) +
          (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2) *
            (r⁻¹ * scaledBracketBump 2 r x) := by ring
  obtain ⟨hsigma_scale, hr_scale⟩ := aux_diagonalScaleComparisons N ht hscale
  have hsigma_inv : sigma⁻¹ = Real.sqrt 2 * t₀⁻¹ := by
    dsimp [sigma]
    field_simp [ne_of_gt ht₀, ne_of_gt hroot]
  have hr_ratio : t₁ / r ≤ Real.sqrt 2 := by
    apply (div_le_iff₀ hr).2
    simpa [mul_comm] using ht₁_r
  have hr_inv : r⁻¹ ≤ Real.sqrt 2 * t₁⁻¹ := by
    calc
      r⁻¹ = (t₁ / r) * t₁⁻¹ := by field_simp [ne_of_gt hr, ne_of_gt ht₁]
      _ ≤ Real.sqrt 2 * t₁⁻¹ :=
        mul_le_mul_of_nonneg_right hr_ratio (inv_nonneg.mpr ht₁.le)
  have hsigma_term : sigma⁻¹ * scaledBracketBump N sigma x ≤
      2 * (t₀⁻¹ * scaledBracketBump N t₀ x) := by
    rw [hsigma_inv]
    calc
      (Real.sqrt 2 * t₀⁻¹) * scaledBracketBump N sigma x ≤
          (Real.sqrt 2 * t₀⁻¹) *
            (Real.sqrt 2 * scaledBracketBump N t₀ x) :=
        mul_le_mul_of_nonneg_left hsigma_scale
          (mul_nonneg hroot.le (inv_nonneg.mpr ht₀.le))
      _ = 2 * (t₀⁻¹ * scaledBracketBump N t₀ x) := by
        calc
          (Real.sqrt 2 * t₀⁻¹) * (Real.sqrt 2 * scaledBracketBump N t₀ x) =
              (Real.sqrt 2 * Real.sqrt 2) *
                (t₀⁻¹ * scaledBracketBump N t₀ x) := by ring
          _ = 2 * (t₀⁻¹ * scaledBracketBump N t₀ x) := by rw [hroot_mul]
  have hbb_r : 0 ≤ scaledBracketBump 2 r x := by
    unfold scaledBracketBump
    exact mul_nonneg (inv_nonneg.mpr hr.le)
      (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
  have hr_term : r⁻¹ * scaledBracketBump 2 r x ≤
      2 * (t₁⁻¹ * scaledBracketBump 2 t₁ x) := by
    calc
      r⁻¹ * scaledBracketBump 2 r x ≤
          (Real.sqrt 2 * t₁⁻¹) * scaledBracketBump 2 r x :=
        mul_le_mul_of_nonneg_right hr_inv hbb_r
      _ ≤ (Real.sqrt 2 * t₁⁻¹) *
          (Real.sqrt 2 * scaledBracketBump 2 t₁ x) :=
        mul_le_mul_of_nonneg_left hr_scale
          (mul_nonneg hroot.le (inv_nonneg.mpr ht₁.le))
      _ = 2 * (t₁⁻¹ * scaledBracketBump 2 t₁ x) := by
        calc
          (Real.sqrt 2 * t₁⁻¹) * (Real.sqrt 2 * scaledBracketBump 2 t₁ x) =
              (Real.sqrt 2 * Real.sqrt 2) *
                (t₁⁻¹ * scaledBracketBump 2 t₁ x) := by ring
          _ = 2 * (t₁⁻¹ * scaledBracketBump 2 t₁ x) := by rw [hroot_mul]
  have hA : 0 ≤ C_gaussianBumpDecay 1 N :=
    aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 N
  have hB : 0 ≤ C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 *
      C_twoBumpEstimate 2 2 := by
    apply mul_nonneg
    · exact mul_nonneg
        (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 0 2)
        (aux_derivativeDiagonalSquareRoot_C_gaussianBumpDecay_nonneg 1 2)
    · rw [aux_twoBumpEstimate_two_two]
      norm_num
  have hu : 0 ≤ t₀⁻¹ * scaledBracketBump N t₀ x := by
    unfold scaledBracketBump
    apply mul_nonneg (inv_nonneg.mpr ht₀.le)
    exact mul_nonneg (inv_nonneg.mpr ht₀.le)
      (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
  have hv : 0 ≤ t₁⁻¹ * scaledBracketBump 2 t₁ x := by
    unfold scaledBracketBump
    apply mul_nonneg (inv_nonneg.mpr ht₁.le)
    exact mul_nonneg (inv_nonneg.mpr ht₁.le)
      (pow_nonneg (inv_nonneg.mpr (by positivity)) _)
  calc
    |deriv (diagonalSquareRoot t₀ t₁) x| ≤
        C_gaussianBumpDecay 1 N * (sigma⁻¹ * scaledBracketBump N sigma x) +
          (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2) *
            (r⁻¹ * scaledBracketBump 2 r x) := hmain
    _ ≤ C_gaussianBumpDecay 1 N * (2 * (t₀⁻¹ * scaledBracketBump N t₀ x)) +
          (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2) *
            (2 * (t₁⁻¹ * scaledBracketBump 2 t₁ x)) :=
      add_le_add (mul_le_mul_of_nonneg_left hsigma_term hA)
        (mul_le_mul_of_nonneg_left hr_term hB)
    _ ≤ max (C_gaussianBumpDecay 1 N)
          (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2) *
            (2 * (t₀⁻¹ * scaledBracketBump N t₀ x)) +
          max (C_gaussianBumpDecay 1 N)
          (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2) *
            (2 * (t₁⁻¹ * scaledBracketBump 2 t₁ x)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = C_derivativeDiagonalSquareRoot N *
        (t₀⁻¹ * scaledBracketBump N t₀ x + t₁⁻¹ * scaledBracketBump 2 t₁ x) := by
      rw [C_derivativeDiagonalSquareRoot]
      ring

/-- For `constantDiagonalSquareRoot`, this elementary induction bounds `N + 1` by a
power of four. -/
theorem aux_constantDiagonalSquareRoot_one_add_le_four_pow (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) ≤ 4 ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      rw [pow_succ]
      have hpow : 1 ≤ (4 : ℝ) ^ N := one_le_pow₀ (by norm_num)
      nlinarith

/-- For `constantDiagonalSquareRoot`, this upgrades the elementary power-of-four
bound to the Gaussian base appearing in the defining constant. -/
theorem aux_constantDiagonalSquareRoot_four_mul_one_add_le_four_pow_succ (N : ℕ) :
    4 * ((N + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) := by
  calc
    4 * ((N + 1 : ℕ) : ℝ) ≤ 4 * (4 : ℝ) ^ N :=
      mul_le_mul_of_nonneg_left
        (aux_constantDiagonalSquareRoot_one_add_le_four_pow N) (by norm_num)
    _ = (4 : ℝ) ^ (N + 1) := by rw [pow_succ]; ring

/-- For `constantDiagonalSquareRoot`, this normalizes the real power occurring after
the Gaussian-base comparison to a natural power of two. -/
theorem aux_constantDiagonalSquareRoot_rpow_four_pow_succ (N : ℕ) :
    ((4 : ℝ) ^ (N + 1)) ^ ((N : ℝ) / 2) = (2 : ℝ) ^ (N * (N + 1)) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
  rw [← Real.rpow_natCast]
  conv_lhs => rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  conv_rhs => rw [← Real.rpow_natCast]
  congr 1
  norm_num
  ring

/-- For `constantDiagonalSquareRoot`, this is the required zero-order Gaussian
constant estimate. -/
theorem aux_constantDiagonalSquareRoot_gaussianBumpDecay_zero_bound (N : ℕ) :
    C_gaussianBumpDecay 0 N ≤ (2 : ℝ) ^ ((N + 1) ^ 2) := by
  rw [C_gaussianBumpDecay]
  norm_num [Real.rpow_zero, Real.rpow_one]
  have hbase := aux_constantDiagonalSquareRoot_four_mul_one_add_le_four_pow_succ N
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 4 * ((N + 1 : ℕ) : ℝ)) hbase
    (by positivity : 0 ≤ (N : ℝ) / 2)
  have hnat : N * (N + 1) ≤ (N + 1) ^ 2 := by
    nlinarith [Nat.zero_le N]
  calc
    (4 * ((N : ℝ) + 1)) ^ ((N : ℝ) / 2) ≤
        ((4 : ℝ) ^ (N + 1)) ^ ((N : ℝ) / 2) := by
      simpa [Nat.cast_add, Nat.cast_one] using hpow
    _ = (2 : ℝ) ^ (N * (N + 1)) :=
      aux_constantDiagonalSquareRoot_rpow_four_pow_succ N
    _ ≤ (2 : ℝ) ^ ((N + 1) ^ 2) :=
      pow_le_pow_right₀ (by norm_num) hnat

/-- For `constantDerivativeDiagonalSquareRoot`, this is the corresponding
first-order Gaussian constant estimate. -/
theorem aux_constantDerivativeDiagonalSquareRoot_gaussianBumpDecay_one_bound (N : ℕ) :
    C_gaussianBumpDecay 1 N ≤ (2 : ℝ) ^ ((N + 1) ^ 2 + 4) := by
  rw [C_gaussianBumpDecay]
  norm_num [Real.rpow_one, Real.sqrt_eq_rpow]
  have hzero : (4 * ((N : ℝ) + 1)) ^ ((N : ℝ) / 2) ≤
      (2 : ℝ) ^ ((N + 1) ^ 2) := by
    simpa [C_gaussianBumpDecay, Real.rpow_zero, Real.rpow_one] using
      aux_constantDiagonalSquareRoot_gaussianBumpDecay_zero_bound N
  have hroot : (76 : ℝ) ^ (1 / 2 : ℝ) ≤ 16 := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 76),
      Real.sqrt_nonneg (76 : ℝ)]
  calc
    76 ^ (1 / 2 : ℝ) * (4 * ((N : ℝ) + 1)) ^ ((N : ℝ) / 2) ≤
        16 * (2 : ℝ) ^ ((N + 1) ^ 2) := by
      apply mul_le_mul hroot hzero
      · positivity
      · norm_num
    _ = (2 : ℝ) ^ ((N + 1) ^ 2 + 4) := by
      rw [pow_add]
      norm_num
      ring

/-- For `constantDiagonalSquareRoot`, this evaluates the fixed `N = 2` constant. -/
theorem aux_constantDiagonalSquareRoot_two :
    C_diagonalSquareRoot 2 = 51 * 2 ^ 6 * Real.sqrt 2 := by
  rw [C_diagonalSquareRoot, C_squareRootGaussianDecay,
    aux_twoBumpEstimate_two_two]
  norm_num [C_gaussianBumpDecay, Real.rpow_natCast, Real.sqrt_eq_rpow]
  ring

/-- For `constantDiagonalSquareRoot`, this supplies the displayed small numerical bound. -/
theorem aux_constantDiagonalSquareRoot_two_lt :
    C_diagonalSquareRoot 2 < 2 ^ 13 := by
  rw [aux_constantDiagonalSquareRoot_two]
  have hsqrt : Real.sqrt (2 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg (2 : ℝ)]
  nlinarith

/--
\begin{lemma}[constant $C_{\ref{diagonal square root},N}$ \auto]\label{constant diagonal square root}
For every $N\ge1$,
\[
C_{\ref{diagonal square root},N}
\le2^{1+\max((N+1)^2,12)}.
\]
Moreover,
\[
C_{\ref{diagonal square root},2}=51\cdot2^6\sqrt2<2^{13}.
\]
\end{lemma}
-/
theorem constantDiagonalSquareRoot :
    (∀ N : ℕ, 1 ≤ N →
      C_diagonalSquareRoot N ≤ (2 : ℝ) ^ (1 + max ((N + 1) ^ 2) 12)) ∧
    C_diagonalSquareRoot 2 = 51 * 2 ^ 6 * Real.sqrt 2 ∧
    C_diagonalSquareRoot 2 < 2 ^ 13 := by
  constructor
  · intro N _hN
    rw [C_diagonalSquareRoot]
    have hzero := aux_constantDiagonalSquareRoot_gaussianBumpDecay_zero_bound N
    have hsecond :
        C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2 ≤
          (2 : ℝ) ^ 12 := by
      rw [C_squareRootGaussianDecay, aux_twoBumpEstimate_two_two]
      norm_num [C_gaussianBumpDecay, Real.rpow_natCast, Real.sqrt_eq_rpow]
    have hmax : max (C_gaussianBumpDecay 0 N)
        (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2) ≤
          (2 : ℝ) ^ max ((N + 1) ^ 2) 12 := by
      apply max_le
      · exact hzero.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_max_left _ _))
      · exact hsecond.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_max_right _ _))
    have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg (2 : ℝ)]
    have hfirstnonneg : 0 ≤ C_gaussianBumpDecay 0 N := by
      unfold C_gaussianBumpDecay
      apply mul_nonneg
      · exact Real.rpow_nonneg (by positivity) _
      · exact Real.rpow_nonneg (by positivity) _
    calc
      Real.sqrt 2 * max (C_gaussianBumpDecay 0 N)
          (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2) ≤
          2 * (2 : ℝ) ^ max ((N + 1) ^ 2) 12 := by
        apply mul_le_mul hsqrt hmax
        · exact hfirstnonneg.trans (le_max_left _ _)
        · norm_num
      _ = (2 : ℝ) ^ (1 + max ((N + 1) ^ 2) 12) := by
        rw [pow_succ]
        ring
  exact ⟨aux_constantDiagonalSquareRoot_two,
    aux_constantDiagonalSquareRoot_two_lt⟩

/-- For `constantDerivativeDiagonalSquareRoot`, this evaluates the fixed `N = 2`
constant using the retained stronger Gaussian coefficient `38`. -/
theorem aux_constantDerivativeDiagonalSquareRoot_two :
    C_derivativeDiagonalSquareRoot 2 = 9 * 2 ^ 10 * Real.sqrt 19 := by
  rw [C_derivativeDiagonalSquareRoot, aux_twoBumpEstimate_two_two]
  norm_num [C_gaussianBumpDecay, Real.rpow_natCast, Real.sqrt_eq_rpow]
  have hz : 0 ≤ (76 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hmax : (76 : ℝ) ^ (1 / 2 : ℝ) * 12 ≤
      12 * ((76 : ℝ) ^ (1 / 2 : ℝ) * 12) * 16 := by
    nlinarith [mul_nonneg hz (by norm_num : (0 : ℝ) ≤ 12)]
  rw [max_eq_right hmax]
  rw [← Real.sqrt_eq_rpow]
  rw [show (76 : ℝ) = 4 * 19 by norm_num, Real.sqrt_mul (by norm_num)]
  have hsqrt19 : (19 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 19 := by
    rw [← Real.sqrt_eq_rpow]
  rw [hsqrt19]
  norm_num
  ring

/-- For `constantDerivativeDiagonalSquareRoot`, this supplies the displayed small numerical
bound for the retained stronger Gaussian coefficient. -/
theorem aux_constantDerivativeDiagonalSquareRoot_two_lt :
    C_derivativeDiagonalSquareRoot 2 < 2 ^ 16 := by
  rw [aux_constantDerivativeDiagonalSquareRoot_two]
  have hsqrt : Real.sqrt (19 : ℝ) < 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19),
      Real.sqrt_nonneg (19 : ℝ)]
  nlinarith

/--
\begin{lemma}[constant $C_{\ref{derivative of diagonal square root},N}$ \auto]
\label{constant derivative diagonal square root}
For every $N\ge1$,
\[
C_{\ref{derivative of diagonal square root},N}
\le2^{1+\max((N+1)^2+4,15)}.
\]
Moreover, with the retained stronger coefficient `38` in
`C_gaussianBumpDecay`,
\[
C_{\ref{derivative of diagonal square root},2}=9\cdot2^{10}\sqrt{19}<2^{16}.
\]
\end{lemma}
-/
theorem constantDerivativeDiagonalSquareRoot :
    (∀ N : ℕ, 1 ≤ N →
      C_derivativeDiagonalSquareRoot N ≤
        (2 : ℝ) ^ (1 + max ((N + 1) ^ 2 + 4) 15)) ∧
    C_derivativeDiagonalSquareRoot 2 = 9 * 2 ^ 10 * Real.sqrt 19 ∧
    C_derivativeDiagonalSquareRoot 2 < 2 ^ 16 := by
  constructor
  · intro N _hN
    rw [C_derivativeDiagonalSquareRoot]
    have hone := aux_constantDerivativeDiagonalSquareRoot_gaussianBumpDecay_one_bound N
    have hsecond :
        C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2 ≤
          (2 : ℝ) ^ 15 := by
      rw [aux_twoBumpEstimate_two_two]
      norm_num [C_gaussianBumpDecay, Real.rpow_natCast, Real.sqrt_eq_rpow]
      have hroot : (76 : ℝ) ^ (1 / 2 : ℝ) ≤ 9 := by
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 76),
          Real.sqrt_nonneg (76 : ℝ)]
      nlinarith
    have hmax : max (C_gaussianBumpDecay 1 N)
        (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2) ≤
          (2 : ℝ) ^ max ((N + 1) ^ 2 + 4) 15 := by
      apply max_le
      · exact hone.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_max_left _ _))
      · exact hsecond.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_max_right _ _))
    calc
      2 * max (C_gaussianBumpDecay 1 N)
          (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2) ≤
          2 * (2 : ℝ) ^ max ((N + 1) ^ 2 + 4) 15 :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ = (2 : ℝ) ^ (1 + max ((N + 1) ^ 2 + 4) 15) := by
        rw [pow_succ]
        ring
  exact ⟨aux_constantDerivativeDiagonalSquareRoot_two,
    aux_constantDerivativeDiagonalSquareRoot_two_lt⟩

/-- Source label `\ref{L:gaussian-estimate}`; the explicit constant used by the public theorem
`gaussianEstimate`. -/
def C_gaussianEstimate (N : ℕ) : ℝ :=
  Real.exp Real.pi *
    ∑ l ∈ Finset.range (N / 2 + 1),
      (N.factorial : ℝ) / ((l.factorial : ℝ) * ((N - 2 * l).factorial : ℝ)) *
        (2 : ℝ) ^ (N - 2 * l) * Real.pi ^ (N - l)

/-- For \ref{L:gaussian-estimate}, this is the coefficient of the auxiliary polynomial
describing derivatives of the reciprocal Gaussian. -/
noncomputable def aux_gaussianEstimate_coeff (n l : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((l.factorial : ℝ) * ((n - 2 * l).factorial : ℝ)) *
    (2 : ℝ) ^ (n - 2 * l) * Real.pi ^ (n - l)

/-- For \ref{L:gaussian-estimate}, this polynomial gives the factor left after taking
derivatives of the reciprocal Gaussian. -/
noncomputable def aux_gaussianEstimate_polynomial (n : ℕ) : ℝ → ℝ :=
  ∑ l ∈ Finset.range (n / 2 + 1), fun x =>
    aux_gaussianEstimate_coeff n l * x ^ (n - 2 * l)

/-- For \ref{L:gaussian-estimate}, this differentiates the auxiliary polynomial termwise. -/
theorem aux_gaussianEstimate_polynomial_deriv (n : ℕ) (x : ℝ) :
    deriv (aux_gaussianEstimate_polynomial n) x =
      ∑ l ∈ Finset.range (n / 2 + 1),
        aux_gaussianEstimate_coeff n l * ((n - 2 * l : ℕ) : ℝ) *
          x ^ (n - 2 * l - 1) := by
  unfold aux_gaussianEstimate_polynomial
  let s := Finset.range (n / 2 + 1)
  have h' : HasDerivAt
      (∑ l ∈ s, fun y : ℝ => aux_gaussianEstimate_coeff n l * y ^ (n - 2 * l))
      (∑ l ∈ s, aux_gaussianEstimate_coeff n l * ((n - 2 * l : ℕ) : ℝ) *
        x ^ (n - 2 * l - 1)) x := by
    apply HasDerivAt.sum
    intro l _
    simpa [mul_assoc] using
      ((hasDerivAt_id x).pow (n - 2 * l)).const_mul (aux_gaussianEstimate_coeff n l)
  exact h'.deriv

/-- For \ref{L:gaussian-estimate}, this is the initial coefficient identity in the odd
derivative recurrence. -/
theorem aux_gaussianEstimate_coeff_odd_zero (q : ℕ) :
    aux_gaussianEstimate_coeff (2 * q + 1) 0 =
      2 * Real.pi * aux_gaussianEstimate_coeff (2 * q) 0 := by
  simp [aux_gaussianEstimate_coeff]
  have h1 : ((2 * q + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * q).factorial : ℝ) ≠ 0 := by positivity
  rw [div_self h1, div_self h2]
  rw [show 2 * q + 1 = 2 * q + 1 by omega, pow_succ, pow_succ]
  ring

/-- For \ref{L:gaussian-estimate}, this is the coefficient recurrence for an odd
derivative. -/
theorem aux_gaussianEstimate_coeff_odd_succ (q j : ℕ) (hj : j < q) :
    aux_gaussianEstimate_coeff (2 * q + 1) (j + 1) =
      2 * Real.pi * aux_gaussianEstimate_coeff (2 * q) (j + 1) +
        aux_gaussianEstimate_coeff (2 * q) j * ((2 * q - 2 * j : ℕ) : ℝ) := by
  set d : ℕ := 2 * q - 2 * j
  have hd2 : 2 ≤ d := by dsimp [d]; omega
  have hd1 : 1 ≤ d := by omega
  have hsubL : 2 * q + 1 - 2 * (j + 1) = d - 1 := by dsimp [d]; omega
  have hsubF : 2 * q - 2 * (j + 1) = d - 2 := by dsimp [d]; omega
  have hpowL : 2 * q + 1 - (j + 1) = 2 * q - j := by omega
  have hpowF : 2 * q - (j + 1) = 2 * q - j - 1 := by omega
  have hjfac : (j + 1).factorial = (j + 1) * j.factorial := Nat.factorial_succ j
  have hdfac : d.factorial = d * (d - 1).factorial := by
    calc
      d.factorial = ((d - 1) + 1).factorial := by rw [Nat.sub_add_cancel hd1]
      _ = ((d - 1) + 1) * (d - 1).factorial := Nat.factorial_succ _
      _ = d * (d - 1).factorial := by rw [Nat.sub_add_cancel hd1]
  have hd1fac : (d - 1).factorial = (d - 1) * (d - 2).factorial := by
    rw [show d - 1 = (d - 2) + 1 by omega, Nat.factorial_succ]
  have hnfact : (2 * q + 1).factorial = (2 * q + 1) * (2 * q).factorial :=
    Nat.factorial_succ (2 * q)
  simp only [aux_gaussianEstimate_coeff]
  rw [hsubL, hsubF, hpowL, hpowF, hjfac, hdfac, hd1fac, hnfact]
  push_cast
  have hpow2L : (2 : ℝ) ^ (d - 1) = 2 ^ (d - 2) * 2 := by
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
  have hpow2D : (2 : ℝ) ^ d = 2 ^ (d - 2) * 4 := by
    rw [show d = (d - 2) + 2 by omega, pow_add]
    norm_num
  have hpowPi : Real.pi ^ (2 * q - j) =
      Real.pi ^ (2 * q - j - 1) * Real.pi := by
    calc
      Real.pi ^ (2 * q - j) = Real.pi ^ ((2 * q - j - 1) + 1) := by
        congr 1
        omega
      _ = Real.pi ^ (2 * q - j - 1) * Real.pi := pow_succ _ _
  rw [hpow2L, hpow2D, hpowPi]
  have hdcast : (d : ℝ) = 2 * q - 2 * j := by
    dsimp [d]
    have h2j : 2 * j ≤ 2 * q := by omega
    rw [Nat.cast_sub h2j]
    push_cast
    ring
  have hd1ne : ((d - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_iff_lt.mpr hd2)
  have hd1cast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd1]
    norm_num
  field_simp [hd1ne]
  rw [hd1cast, hdcast]
  ring

/-- For \ref{L:gaussian-estimate}, this reindexes the finite sum in the odd derivative
recurrence. -/
theorem aux_gaussianEstimate_sum_range_odd_reindex (q : ℕ) (A B C : ℕ → ℝ)
    (hzero : B 0 = A 0)
    (hinner : ∀ j : ℕ, j < q → B (j + 1) = A (j + 1) + C j)
    (htop : C q = 0) :
    ∑ l ∈ Finset.range (q + 1), B l =
      (∑ j ∈ Finset.range (q + 1), A j) + ∑ j ∈ Finset.range (q + 1), C j := by
  rw [Finset.sum_range_succ' B q, Finset.sum_range_succ' A q,
    Finset.sum_range_succ C q, htop, hzero]
  have hsum : ∑ j ∈ Finset.range q, B (j + 1) =
      ∑ j ∈ Finset.range q, (A (j + 1) + C j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hinner j (Finset.mem_range.mp hj)
  rw [hsum, Finset.sum_add_distrib]
  ring

/-- For \ref{L:gaussian-estimate}, this is the recurrence for the auxiliary polynomial at
an odd index. -/
theorem aux_gaussianEstimate_polynomial_odd_recurrence (q : ℕ) (x : ℝ) :
    aux_gaussianEstimate_polynomial (2 * q + 1) x =
      deriv (aux_gaussianEstimate_polynomial (2 * q)) x +
        2 * Real.pi * x * aux_gaussianEstimate_polynomial (2 * q) x := by
  let A : ℕ → ℝ := fun j =>
    2 * Real.pi * x *
      (aux_gaussianEstimate_coeff (2 * q) j * x ^ (2 * q - 2 * j))
  let B : ℕ → ℝ := fun j =>
    aux_gaussianEstimate_coeff (2 * q + 1) j * x ^ (2 * q + 1 - 2 * j)
  let C : ℕ → ℝ := fun j =>
    aux_gaussianEstimate_coeff (2 * q) j * ((2 * q - 2 * j : ℕ) : ℝ) *
      x ^ (2 * q - 2 * j - 1)
  have hzero : B 0 = A 0 := by
    dsimp [A, B]
    rw [aux_gaussianEstimate_coeff_odd_zero]
    rw [show 2 * q + 1 = 2 * q + 1 by omega, pow_succ]
    ring
  have hinner : ∀ j : ℕ, j < q → B (j + 1) = A (j + 1) + C j := by
    intro j hj
    set d : ℕ := 2 * q - 2 * j
    have hB : 2 * q + 1 - 2 * (j + 1) = d - 1 := by
      dsimp [d]
      omega
    have hA : 2 * q - 2 * (j + 1) = d - 2 := by
      dsimp [d]
      omega
    have hC : 2 * q - 2 * j - 1 = d - 1 := by rfl
    dsimp [A, B, C]
    rw [aux_gaussianEstimate_coeff_odd_succ q j hj, hB, hA, hC]
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
    ring
  have htop : C q = 0 := by
    dsimp [C]
    have hzero : 2 * q - 2 * q = 0 := by omega
    rw [hzero]
    ring
  have hsum := aux_gaussianEstimate_sum_range_odd_reindex q A B C hzero hinner htop
  have hA : (∑ j ∈ Finset.range (q + 1), A j) =
      2 * Real.pi * x * aux_gaussianEstimate_polynomial (2 * q) x := by
    dsimp [A, aux_gaussianEstimate_polynomial]
    simp only [Finset.sum_apply]
    rw [show (2 * q) / 2 + 1 = q + 1 by omega, ← Finset.mul_sum]
  have hC : (∑ j ∈ Finset.range (q + 1), C j) =
      deriv (aux_gaussianEstimate_polynomial (2 * q)) x := by
    rw [aux_gaussianEstimate_polynomial_deriv]
    rw [show (2 * q) / 2 + 1 = q + 1 by omega]
  calc
    aux_gaussianEstimate_polynomial (2 * q + 1) x =
        ∑ j ∈ Finset.range (q + 1), B j := by
      simp only [aux_gaussianEstimate_polynomial, Finset.sum_apply]
      dsimp [B]
      rw [show (2 * q + 1) / 2 + 1 = q + 1 by omega]
    _ = (∑ j ∈ Finset.range (q + 1), A j) + ∑ j ∈ Finset.range (q + 1), C j := hsum
    _ = deriv (aux_gaussianEstimate_polynomial (2 * q)) x +
        2 * Real.pi * x * aux_gaussianEstimate_polynomial (2 * q) x := by
      rw [hA, hC]
      ring

/-- For \ref{L:gaussian-estimate}, this reindexes the finite sum in the even derivative
recurrence. -/
theorem aux_gaussianEstimate_sum_range_even_reindex (q : ℕ) (A B C : ℕ → ℝ)
    (hzero : B 0 = A 0)
    (hinner : ∀ j, j < q → B (j + 1) = A (j + 1) + C j)
    (htop : B (q + 1) = C q) :
    ∑ l ∈ Finset.range (q + 2), B l =
      (∑ j ∈ Finset.range (q + 1), A j) + ∑ j ∈ Finset.range (q + 1), C j := by
  rw [show q + 2 = (q + 1) + 1 by omega, Finset.sum_range_succ' B (q + 1)]
  rw [Finset.sum_range_succ (fun j => B (j + 1)) q,
    Finset.sum_range_succ' A q, Finset.sum_range_succ C q, htop, hzero]
  have hsum : ∑ x ∈ Finset.range q, B (x + 1) =
      ∑ x ∈ Finset.range q, (A (x + 1) + C x) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hinner x (Finset.mem_range.mp hx)
  rw [hsum, Finset.sum_add_distrib]
  ring

/-- For \ref{L:gaussian-estimate}, this is the coefficient recurrence for an even
derivative away from its endpoint. -/
theorem aux_gaussianEstimate_coeff_even_succ (q j : ℕ) (hj : j < q) :
    aux_gaussianEstimate_coeff (2 * q + 2) (j + 1) =
      2 * Real.pi * aux_gaussianEstimate_coeff (2 * q + 1) (j + 1) +
        aux_gaussianEstimate_coeff (2 * q + 1) j * ((2 * q + 1 - 2 * j : ℕ) : ℝ) := by
  set d : ℕ := 2 * q + 1 - 2 * j
  have hd2 : 2 ≤ d := by
    dsimp [d]
    omega
  have hd1 : 1 ≤ d := by omega
  have hsubL : 2 * q + 2 - 2 * (j + 1) = d - 1 := by
    dsimp [d]
    omega
  have hsubF : 2 * q + 1 - 2 * (j + 1) = d - 2 := by
    dsimp [d]
    omega
  have hpowL : 2 * q + 2 - (j + 1) = 2 * q + 1 - j := by omega
  have hpowF : 2 * q + 1 - (j + 1) = 2 * q - j := by omega
  have hjfac : (j + 1).factorial = (j + 1) * j.factorial := Nat.factorial_succ j
  have hdfac : d.factorial = d * (d - 1).factorial := by
    calc
      d.factorial = ((d - 1) + 1).factorial := by rw [Nat.sub_add_cancel hd1]
      _ = ((d - 1) + 1) * (d - 1).factorial := Nat.factorial_succ _
      _ = d * (d - 1).factorial := by rw [Nat.sub_add_cancel hd1]
  have hd1fac : (d - 1).factorial = (d - 1) * (d - 2).factorial := by
    rw [show d - 1 = (d - 2) + 1 by omega, Nat.factorial_succ]
  have hnfact : (2 * q + 2).factorial =
      (2 * q + 2) * (2 * q + 1).factorial := by
    rw [show 2 * q + 2 = (2 * q + 1) + 1 by omega, Nat.factorial_succ]
  simp only [aux_gaussianEstimate_coeff]
  rw [hsubL, hsubF, hpowL, hpowF, hjfac, hdfac, hd1fac, hnfact]
  push_cast
  have hpow2L : (2 : ℝ) ^ (d - 1) = 2 ^ (d - 2) * 2 := by
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
  have hpow2D : (2 : ℝ) ^ d = 2 ^ (d - 2) * 4 := by
    rw [show d = (d - 2) + 2 by omega, pow_add]
    norm_num
  have hpowPiL : Real.pi ^ (2 * q + 1 - j) =
      Real.pi ^ (2 * q - j) * Real.pi := by
    calc
      Real.pi ^ (2 * q + 1 - j) = Real.pi ^ ((2 * q - j) + 1) := by
        congr 1
        omega
      _ = Real.pi ^ (2 * q - j) * Real.pi := pow_succ _ _
  rw [hpow2L, hpow2D, hpowPiL]
  have hdcast : (d : ℝ) = 2 * q + 1 - 2 * j := by
    dsimp [d]
    have h2j : 2 * j ≤ 2 * q + 1 := by omega
    rw [Nat.cast_sub h2j]
    push_cast
    ring
  have hd1ne : ((d - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_iff_lt.mpr hd2)
  have hd1cast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd1]
    norm_num
  field_simp [hd1ne]
  rw [hd1cast, hdcast]
  ring

/-- For \ref{L:gaussian-estimate}, this is the initial coefficient identity in the even
derivative recurrence. -/
theorem aux_gaussianEstimate_coeff_even_succ_zero (q : ℕ) :
    aux_gaussianEstimate_coeff (2 * q + 2) 0 =
      2 * Real.pi * aux_gaussianEstimate_coeff (2 * q + 1) 0 := by
  simp [aux_gaussianEstimate_coeff, Nat.factorial_succ]
  field_simp
  ring

/-- For \ref{L:gaussian-estimate}, this is the terminal coefficient identity in the even
derivative recurrence. -/
theorem aux_gaussianEstimate_coeff_even_succ_top (q : ℕ) :
    aux_gaussianEstimate_coeff (2 * q + 2) (q + 1) =
      aux_gaussianEstimate_coeff (2 * q + 1) q := by
  have hsubL : 2 * q + 2 - 2 * (q + 1) = 0 := by omega
  have hsubR : 2 * q + 1 - 2 * q = 1 := by omega
  have hpowL : 2 * q + 2 - (q + 1) = q + 1 := by omega
  have hpowR : 2 * q + 1 - q = q + 1 := by omega
  have hqfac : (q + 1).factorial = (q + 1) * q.factorial := Nat.factorial_succ q
  have hnfact : (2 * q + 2).factorial =
      (2 * q + 2) * (2 * q + 1).factorial := by
    rw [show 2 * q + 2 = (2 * q + 1) + 1 by omega, Nat.factorial_succ]
  simp only [aux_gaussianEstimate_coeff]
  rw [hsubL, hsubR, hpowL, hpowR, hqfac, hnfact]
  push_cast
  field_simp
  ring

/-- For \ref{L:gaussian-estimate}, this is the recurrence for the auxiliary polynomial at
an even index. -/
theorem aux_gaussianEstimate_polynomial_even_recurrence (q : ℕ) (x : ℝ) :
    aux_gaussianEstimate_polynomial (2 * q + 2) x =
      2 * Real.pi * x * aux_gaussianEstimate_polynomial (2 * q + 1) x +
        ∑ j ∈ Finset.range (q + 1), aux_gaussianEstimate_coeff (2 * q + 1) j *
          ((2 * q + 1 - 2 * j : ℕ) : ℝ) * x ^ (2 * q + 1 - 2 * j - 1) := by
  let A : ℕ → ℝ := fun j =>
    2 * Real.pi * x *
      (aux_gaussianEstimate_coeff (2 * q + 1) j * x ^ (2 * q + 1 - 2 * j))
  let B : ℕ → ℝ := fun j =>
    aux_gaussianEstimate_coeff (2 * q + 2) j * x ^ (2 * q + 2 - 2 * j)
  let C : ℕ → ℝ := fun j =>
    aux_gaussianEstimate_coeff (2 * q + 1) j * ((2 * q + 1 - 2 * j : ℕ) : ℝ) *
      x ^ (2 * q + 1 - 2 * j - 1)
  have hzero : B 0 = A 0 := by
    dsimp [A, B]
    rw [aux_gaussianEstimate_coeff_even_succ_zero]
    rw [show 2 * q + 2 = (2 * q + 1) + 1 by omega, pow_succ]
    ring
  have hinner : ∀ j : ℕ, j < q → B (j + 1) = A (j + 1) + C j := by
    intro j hj
    set d : ℕ := 2 * q + 1 - 2 * j
    have hB : 2 * q + 2 - 2 * (j + 1) = d - 1 := by
      dsimp [d]
      omega
    have hA : 2 * q + 1 - 2 * (j + 1) = d - 2 := by
      dsimp [d]
      omega
    have hC : 2 * q + 1 - 2 * j - 1 = d - 1 := by
      dsimp [d]
    dsimp [A, B, C]
    rw [aux_gaussianEstimate_coeff_even_succ q j hj, hB, hA, hC]
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
    ring
  have htop : B (q + 1) = C q := by
    dsimp [B, C]
    rw [aux_gaussianEstimate_coeff_even_succ_top]
    have hB : 2 * q + 2 - 2 * (q + 1) = 0 := by omega
    have hC : 2 * q + 1 - 2 * q - 1 = 0 := by omega
    have hD : 2 * q + 1 - 2 * q = 1 := by omega
    rw [hB, hC, hD]
    ring
  have hsum := aux_gaussianEstimate_sum_range_even_reindex q A B C hzero hinner htop
  have hA : (∑ j ∈ Finset.range (q + 1), A j) =
      2 * Real.pi * x * aux_gaussianEstimate_polynomial (2 * q + 1) x := by
    dsimp [A, aux_gaussianEstimate_polynomial]
    simp only [Finset.sum_apply]
    rw [show (2 * q + 1) / 2 + 1 = q + 1 by omega, ← Finset.mul_sum]
  calc
    aux_gaussianEstimate_polynomial (2 * q + 2) x =
        ∑ j ∈ Finset.range (q + 2), B j := by
      simp only [aux_gaussianEstimate_polynomial, Finset.sum_apply]
      dsimp [B]
      rw [show (2 * q + 2) / 2 + 1 = q + 2 by omega]
    _ = (∑ j ∈ Finset.range (q + 1), A j) + ∑ j ∈ Finset.range (q + 1), C j := hsum
    _ = 2 * Real.pi * x * aux_gaussianEstimate_polynomial (2 * q + 1) x +
        ∑ j ∈ Finset.range (q + 1), aux_gaussianEstimate_coeff (2 * q + 1) j *
          ((2 * q + 1 - 2 * j : ℕ) : ℝ) * x ^ (2 * q + 1 - 2 * j - 1) := by
      rw [hA]

/-- For \ref{L:gaussian-estimate}, this gives the recurrence satisfied by all of the
auxiliary polynomials. -/
theorem aux_gaussianEstimate_polynomial_recurrence (n : ℕ) (x : ℝ) :
    aux_gaussianEstimate_polynomial (n + 1) x =
      deriv (aux_gaussianEstimate_polynomial n) x +
        2 * Real.pi * x * aux_gaussianEstimate_polynomial n x := by
  rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
  · exact aux_gaussianEstimate_polynomial_odd_recurrence q x
  · rw [show 2 * q + 1 + 1 = 2 * q + 2 by omega,
      aux_gaussianEstimate_polynomial_even_recurrence,
      aux_gaussianEstimate_polynomial_deriv]
    rw [show (2 * q + 1) / 2 + 1 = q + 1 by omega]
    ring

/-- For \ref{L:gaussian-estimate}, this is the explicit formula for iterated derivatives
of the reciprocal Gaussian. -/
theorem aux_gaussianEstimate_iteratedDeriv (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => Real.exp (Real.pi * y ^ 2)) x =
      aux_gaussianEstimate_polynomial n x * Real.exp (Real.pi * x ^ 2) := by
  induction n generalizing x with
  | zero =>
      simp [aux_gaussianEstimate_polynomial, aux_gaussianEstimate_coeff]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hih : iteratedDeriv n (fun y : ℝ => Real.exp (Real.pi * y ^ 2)) =
          fun y => aux_gaussianEstimate_polynomial n y * Real.exp (Real.pi * y ^ 2) :=
        funext ih
      rw [hih]
      have hP : DifferentiableAt ℝ (aux_gaussianEstimate_polynomial n) x := by
        unfold aux_gaussianEstimate_polynomial
        fun_prop
      have hInner : HasDerivAt (fun y : ℝ => Real.pi * y ^ 2) (2 * Real.pi * x) x := by
        have hInner' : HasDerivAt (fun y : ℝ => Real.pi * y ^ 2)
            (Real.pi * (2 * x)) x := by
          have hraw := (hasDerivAt_const x Real.pi).mul ((hasDerivAt_id x).pow 2)
          have hfunc : ((fun _ : ℝ => Real.pi) * id ^ 2) =
              (fun y : ℝ => Real.pi * y ^ 2) := by
            funext y
            simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
          rw [hfunc] at hraw
          have hval : 0 * ((id : ℝ → ℝ) ^ 2) x +
              Real.pi * ((2 : ℝ) * id x ^ (2 - 1) * 1) = Real.pi * (2 * x) := by
            norm_num [Pi.pow_apply]
          rw [← hval]
          exact hraw
        convert hInner' using 1 <;> ring
      have hExp : HasDerivAt (fun y : ℝ => Real.exp (Real.pi * y ^ 2))
          (Real.exp (Real.pi * x ^ 2) * (2 * Real.pi * x)) x := by
        simpa using hInner.exp
      rw [deriv_fun_mul hP hExp.differentiableAt, hExp.deriv]
      calc
        deriv (aux_gaussianEstimate_polynomial n) x * Real.exp (Real.pi * x ^ 2) +
            aux_gaussianEstimate_polynomial n x *
              (Real.exp (Real.pi * x ^ 2) * (2 * Real.pi * x)) =
            (deriv (aux_gaussianEstimate_polynomial n) x +
                2 * Real.pi * x * aux_gaussianEstimate_polynomial n x) *
              Real.exp (Real.pi * x ^ 2) := by ring
        _ = aux_gaussianEstimate_polynomial (n + 1) x *
              Real.exp (Real.pi * x ^ 2) := by
          rw [aux_gaussianEstimate_polynomial_recurrence]

/-- For \ref{L:gaussian-estimate}, this rewrites the reciprocal Gaussian in a form whose
derivatives are explicit. -/
theorem aux_gaussianEstimate_inverseGaussian (x : ℝ) :
    (Codex.Preliminaries.Gaussians.gaussian x)⁻¹ = Real.exp (Real.pi * x ^ 2) := by
  unfold Codex.Preliminaries.Gaussians.gaussian Codex.Preliminaries.Notation.gaussian
  rw [← Real.exp_neg]
  congr 1
  ring

/-- For \ref{L:gaussian-estimate}, all coefficients of the auxiliary polynomial are
nonnegative. -/
theorem aux_gaussianEstimate_coeff_nonneg (n l : ℕ) :
    0 ≤ aux_gaussianEstimate_coeff n l := by
  unfold aux_gaussianEstimate_coeff
  positivity

/-- For \ref{L:gaussian-estimate}, the auxiliary polynomial is bounded on the unit
interval by the sum of its coefficients. -/
theorem aux_gaussianEstimate_polynomial_abs_bound (n : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |aux_gaussianEstimate_polynomial n x| ≤
      ∑ l ∈ Finset.range (n / 2 + 1), aux_gaussianEstimate_coeff n l := by
  simp only [aux_gaussianEstimate_polynomial, Finset.sum_apply]
  calc
    |∑ l ∈ Finset.range (n / 2 + 1),
        aux_gaussianEstimate_coeff n l * x ^ (n - 2 * l)| ≤
        ∑ l ∈ Finset.range (n / 2 + 1),
          |aux_gaussianEstimate_coeff n l * x ^ (n - 2 * l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l ∈ Finset.range (n / 2 + 1),
        aux_gaussianEstimate_coeff n l * |x| ^ (n - 2 * l) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [abs_mul, abs_pow, abs_of_nonneg (aux_gaussianEstimate_coeff_nonneg n l)]
    _ ≤ ∑ l ∈ Finset.range (n / 2 + 1), aux_gaussianEstimate_coeff n l * 1 := by
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left
        (pow_le_one₀ (abs_nonneg x) hx) (aux_gaussianEstimate_coeff_nonneg n l)
    _ = ∑ l ∈ Finset.range (n / 2 + 1), aux_gaussianEstimate_coeff n l := by simp

/-- Source label `\ref{L:gaussian-estimate}`. Let `N ∈ ℕ`. For `xi ∈ ℝ` with
`|xi| ≤ 1`, one has `|(g⁻¹)^(N)(xi)| ≤ C_{L:gaussian-estimate,N}`. -/
theorem gaussianEstimate (N : ℕ) (xi : ℝ) (hxi : |xi| ≤ 1) :
    |iteratedDeriv N (fun y : ℝ => (Codex.Preliminaries.Gaussians.gaussian y)⁻¹) xi| ≤
      C_gaussianEstimate N := by
  have hinv : (fun y : ℝ => (Codex.Preliminaries.Gaussians.gaussian y)⁻¹) =
      fun y : ℝ => Real.exp (Real.pi * y ^ 2) := by
    funext y
    exact aux_gaussianEstimate_inverseGaussian y
  rw [hinv, aux_gaussianEstimate_iteratedDeriv]
  have hsqabs : |xi| ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg xi) (by norm_num)).2 hxi
  have hsq : xi ^ 2 ≤ 1 := by
    nlinarith [sq_abs xi]
  have hExp : Real.exp (Real.pi * xi ^ 2) ≤ Real.exp Real.pi := by
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
  have hsum : 0 ≤ ∑ l ∈ Finset.range (N / 2 + 1), aux_gaussianEstimate_coeff N l := by
    apply Finset.sum_nonneg
    intro l _
    exact aux_gaussianEstimate_coeff_nonneg N l
  calc
    |aux_gaussianEstimate_polynomial N xi * Real.exp (Real.pi * xi ^ 2)| =
        |aux_gaussianEstimate_polynomial N xi| * Real.exp (Real.pi * xi ^ 2) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (∑ l ∈ Finset.range (N / 2 + 1), aux_gaussianEstimate_coeff N l) *
        Real.exp Real.pi :=
      mul_le_mul (aux_gaussianEstimate_polynomial_abs_bound N xi hxi) hExp
        (Real.exp_nonneg _) hsum
    _ = C_gaussianEstimate N := by
      unfold C_gaussianEstimate aux_gaussianEstimate_coeff
      ring

/-- Source label `\ref{L:gaussian-bump-estimate}`; the explicit constant used by the public
theorem `gaussianBumpEstimate`. -/
def C_gaussianBumpEstimate (N : ℕ) : ℝ :=
  Real.rpow (2 * Real.pi) (-(N : ℝ)) *
    ∑ l ∈ Finset.range (N + 1), (Nat.choose N l : ℝ) * C_gaussianEstimate l

/-- For `\ref{L:gaussian-bump-estimate}`, the explicit Gaussian-bump constant is
nonnegative. -/
theorem aux_C_gaussianBumpEstimate_nonneg (N : ℕ) :
    0 ≤ C_gaussianBumpEstimate N := by
  unfold C_gaussianBumpEstimate
  apply mul_nonneg
  · exact Real.rpow_nonneg (by positivity) _
  · apply Finset.sum_nonneg
    intro l _
    apply mul_nonneg
    · positivity
    · unfold C_gaussianEstimate
      apply mul_nonneg (le_of_lt (Real.exp_pos _))
      apply Finset.sum_nonneg
      intro m _
      apply mul_nonneg
      · apply mul_nonneg
        · apply div_nonneg <;> positivity
        · positivity
      · positivity

/-- Source definition `\ref{auto:Gaussian-bump-quotient}`. -/
def gaussianBumpQuotient (mu : ℝ) (phiHat : ℝ → ℂ) : ℝ → ℂ := fun xi =>
  (((Gaussians.gaussian (mu * xi))⁻¹ : ℝ) : ℂ) * phiHat xi

/-- For `\ref{L:gaussian-bump-estimate}`, iterated derivatives commute with coercion from
real-valued functions to complex-valued functions. -/
theorem aux_gaussianBumpEstimate_iteratedDeriv_ofReal (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (n + 1) f) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => (f y : ℂ)) x =
      ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n generalizing f x with
  | zero => simp
  | succ n ih =>
    have hfprev : ContDiff ℝ (n + 1) f := by
      apply hf.of_le
      norm_num
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun y : ℝ => (f y : ℂ)) =
        fun y : ℝ => ((iteratedDeriv n f y : ℝ) : ℂ) := by
      funext y
      exact ih f hfprev y
    rw [hfun]
    have hderiv : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
      rw [iteratedDeriv_succ]
      exact (hfprev.differentiable_iteratedDeriv' n).differentiableAt.hasDerivAt
    simpa using ((hasDerivAt_const x Complex.ofRealCLM).clm_apply hderiv).deriv

/-- For `\ref{L:gaussian-bump-estimate}`, the reciprocal Gaussian is smooth. -/
theorem aux_gaussianBumpEstimate_inverseGaussian_contDiff (n : ℕ) :
    ContDiff ℝ (n + 1) (fun x : ℝ => (Gaussians.gaussian x)⁻¹) := by
  rw [show (fun x : ℝ => (Gaussians.gaussian x)⁻¹) =
      fun x : ℝ => Real.exp (Real.pi * x ^ 2) by
    funext x
    exact aux_gaussianEstimate_inverseGaussian x]
  fun_prop

/-- For `\ref{L:gaussian-bump-estimate}`, the complex-valued reciprocal Gaussian is smooth. -/
theorem aux_gaussianBumpEstimate_complexInverseGaussian_contDiff (n : ℕ) :
    ContDiff ℝ (n + 1) (fun x : ℝ => (((Gaussians.gaussian x)⁻¹ : ℝ) : ℂ)) := by
  simpa [Function.comp_def, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.contDiff.comp (aux_gaussianBumpEstimate_inverseGaussian_contDiff n)

/-- For `\ref{L:gaussian-bump-estimate}`, the complex reciprocal Gaussian has the required
finite smoothness. -/
theorem aux_gaussianBumpEstimate_complexInverseGaussian_contDiff_at (n : ℕ) :
    ContDiff ℝ n (fun x : ℝ => (((Gaussians.gaussian x)⁻¹ : ℝ) : ℂ)) := by
  exact (aux_gaussianBumpEstimate_complexInverseGaussian_contDiff n).of_le (by norm_num)

/-- For `\ref{L:gaussian-bump-estimate}`, this is the iterated-derivative scaling rule for
the reciprocal Gaussian. -/
theorem aux_gaussianBumpEstimate_scaledInverseGaussian_iteratedDeriv
    (n : ℕ) (mu xi : ℝ) :
    iteratedDeriv n (fun x : ℝ => (((Gaussians.gaussian (mu * x))⁻¹ : ℝ) : ℂ)) xi =
      mu ^ n •
        ((iteratedDeriv n (fun y : ℝ => (Gaussians.gaussian y)⁻¹) (mu * xi) : ℝ) : ℂ) := by
  have hcomp := congrFun
    (iteratedDeriv_comp_const_smul
      (aux_gaussianBumpEstimate_complexInverseGaussian_contDiff_at n) mu) xi
  rw [aux_gaussianBumpEstimate_iteratedDeriv_ofReal n
    (fun y : ℝ => (Gaussians.gaussian y)⁻¹)
    (aux_gaussianBumpEstimate_inverseGaussian_contDiff n) (mu * xi)] at hcomp
  exact hcomp

/-- For `\ref{L:gaussian-bump-estimate}`, the quotient in
`\ref{auto:Gaussian-bump-quotient}` is as smooth as its bump factor. -/
theorem aux_gaussianBumpEstimate_contDiff (N : ℕ) (mu : ℝ) (phiHat : ℝ → ℂ)
    (hphi : ContDiff ℝ N phiHat) :
    ContDiff ℝ N (gaussianBumpQuotient mu phiHat) := by
  have hlin : ContDiff ℝ N (fun x : ℝ => mu * x) := by fun_prop
  have hinv : ContDiff ℝ N (fun x : ℝ => (((Gaussians.gaussian (mu * x))⁻¹ : ℝ) : ℂ)) :=
    (aux_gaussianBumpEstimate_complexInverseGaussian_contDiff_at N).comp hlin
  exact hinv.mul hphi

/-- For `\ref{L:gaussian-bump-estimate}`, this identifies the natural-number power in the
Fourier normalization with the real power in `C_gaussianBumpEstimate`. -/
theorem aux_gaussianBumpEstimate_qpow_eq_rpow (N : ℕ) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ N = Real.rpow (2 * Real.pi) (-(N : ℝ)) := by
  calc
    ((2 * Real.pi)⁻¹ : ℝ) ^ N = Real.rpow ((2 * Real.pi)⁻¹) (N : ℝ) :=
      (Real.rpow_natCast ((2 * Real.pi)⁻¹) N).symm
    _ = (Real.rpow (2 * Real.pi) (N : ℝ))⁻¹ :=
      Real.inv_rpow (by positivity : 0 ≤ 2 * Real.pi) (N : ℝ)
    _ = Real.rpow (2 * Real.pi) (-(N : ℝ)) :=
      (Real.rpow_neg (by positivity : 0 ≤ 2 * Real.pi) (N : ℝ)).symm

/-- For `\ref{L:gaussian-bump-estimate}`, this is the pointwise Leibniz bound for the
Gaussian bump quotient. -/
theorem aux_gaussianBumpEstimate_pointwise (N : ℕ) (c mu : ℝ) (phiHat : ℝ → ℂ)
    (hc : 0 ≤ c) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (xi : ℝ) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ N *
        ‖iteratedDeriv N (gaussianBumpQuotient mu phiHat) xi‖ ≤
      c * C_gaussianBumpEstimate N := by
  let q : ℝ := (2 * Real.pi)⁻¹
  let Q : ℝ → ℂ := gaussianBumpQuotient mu phiHat
  let A : ℝ → ℂ := fun x => (((Gaussians.gaussian (mu * x))⁻¹ : ℝ) : ℂ)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hQ : Q = A * phiHat := by
    funext x
    rfl
  have hA : ContDiff ℝ N A := by
    dsimp [A]
    have hlin : ContDiff ℝ N (fun x : ℝ => mu * x) := by fun_prop
    exact (aux_gaussianBumpEstimate_complexInverseGaussian_contDiff_at N).comp hlin
  have hQSupp : tsupport Q ⊆ tsupport phiHat := by
    rw [hQ]
    exact tsupport_mul_subset_right
  have hQDerivSupp : tsupport (iteratedDeriv N Q) ⊆ tsupport phiHat :=
    (aux_tsupport_iteratedDeriv_subset Q N).trans hQSupp
  have hgauss (m : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
      |iteratedDeriv m (fun y : ℝ => (Gaussians.gaussian y)⁻¹) x| ≤
        C_gaussianEstimate m :=
    gaussianEstimate m x hx
  have hC (m : ℕ) : 0 ≤ C_gaussianEstimate m := by
    exact (abs_nonneg (iteratedDeriv m (fun y : ℝ => (Gaussians.gaussian y)⁻¹) 0)).trans
      (hgauss m 0 (by norm_num))
  have hsum : ‖iteratedDeriv N Q xi‖ ≤
      c * ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * C_gaussianEstimate i := by
    by_cases hmem : xi ∈ tsupport phiHat
    · have hxi : |xi| ≤ 1 := by
        have hinterval := hsupp hmem
        exact abs_le.2 hinterval
      have hAderiv (i : ℕ) : ‖iteratedDeriv i A xi‖ ≤ C_gaussianEstimate i := by
        have hscaled : |mu * xi| ≤ 1 := by
          calc
            |mu * xi| = |mu| * |xi| := abs_mul _ _
            _ = mu * |xi| := by rw [abs_of_nonneg hmu0]
            _ ≤ 1 * 1 := mul_le_mul hmu1 hxi (abs_nonneg _) zero_le_one
            _ = 1 := by ring
        rw [show A = fun x : ℝ => (((Gaussians.gaussian (mu * x))⁻¹ : ℝ) : ℂ) by rfl,
          aux_gaussianBumpEstimate_scaledInverseGaussian_iteratedDeriv]
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        have hmupow : |mu ^ i| ≤ 1 := by
          rw [abs_of_nonneg (pow_nonneg hmu0 _)]
          exact pow_le_one₀ hmu0 hmu1
        calc
          |mu ^ i| * |iteratedDeriv i (fun y : ℝ => (Gaussians.gaussian y)⁻¹) (mu * xi)| ≤
              1 * C_gaussianEstimate i :=
            mul_le_mul hmupow (hgauss i (mu * xi) hscaled) (abs_nonneg _) zero_le_one
          _ = C_gaussianEstimate i := by ring
      rw [hQ, iteratedDeriv_mul hA.contDiffAt hphi.contDiffAt]
      calc
        ‖∑ i ∈ Finset.range (N + 1), (N.choose i : ℂ) *
            iteratedDeriv i A xi * iteratedDeriv (N - i) phiHat xi‖ ≤
            ∑ i ∈ Finset.range (N + 1), ‖(N.choose i : ℂ) *
              iteratedDeriv i A xi * iteratedDeriv (N - i) phiHat xi‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (N + 1),
            (N.choose i : ℝ) * C_gaussianEstimate i * c := by
          apply Finset.sum_le_sum
          intro i hi
          have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          rw [norm_mul, norm_mul, norm_natCast]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hAderiv i) (by positivity))
            (hphiBound (N - i) (Nat.sub_le _ _) xi)
            (norm_nonneg _) (mul_nonneg (by positivity) (hC i))
        _ = c * ∑ i ∈ Finset.range (N + 1),
            (N.choose i : ℝ) * C_gaussianEstimate i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    · have hzero : iteratedDeriv N Q xi = 0 := by
        apply Function.notMem_support.mp
        intro hsupport
        exact hmem (hQDerivSupp (subset_tsupport _ hsupport))
      rw [hzero, norm_zero]
      have hsumNonneg : 0 ≤ ∑ i ∈ Finset.range (N + 1),
          (N.choose i : ℝ) * C_gaussianEstimate i := by
        apply Finset.sum_nonneg
        intro i _
        exact mul_nonneg (by positivity) (hC i)
      exact mul_nonneg hc hsumNonneg
  calc
    ((2 * Real.pi)⁻¹ : ℝ) ^ N * ‖iteratedDeriv N Q xi‖ ≤
        q ^ N * (c * ∑ i ∈ Finset.range (N + 1),
          (N.choose i : ℝ) * C_gaussianEstimate i) := by
      simpa only [q] using mul_le_mul_of_nonneg_left hsum (pow_nonneg hq _)
    _ = c * C_gaussianBumpEstimate N := by
      rw [C_gaussianBumpEstimate, ← aux_gaussianBumpEstimate_qpow_eq_rpow]
      ring

/-- For `\ref{L:gaussian-bump-estimate}`, the pointwise estimate gives the stated
`L^∞` estimate. -/
theorem aux_gaussianBumpEstimate_eLpNorm (N : ℕ) (c mu : ℝ) (phiHat : ℝ → ℂ)
    (hc : 0 ≤ c) (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c) :
    eLpNorm (fun xi : ℝ => ((2 * Real.pi)⁻¹ : ℝ) ^ N •
      iteratedDeriv N (gaussianBumpQuotient mu phiHat) xi) ⊤ volume ≤
      ENNReal.ofReal (c * C_gaussianBumpEstimate N) := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [] with xi
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) _)]
  exact aux_gaussianBumpEstimate_pointwise N c mu phiHat hc hmu0 hmu1 hphi hsupp
    hphiBound xi

/--
For source label `\ref{L:gaussian-bump-estimate}`, let `c > 0` and let `phiHat` be supported
in `[-1, 1]`, `N` times continuously differentiable, with all iterated derivatives through
order `N` bounded by `c`. The reciprocal-Gaussian quotient is `N` times continuously
differentiable and satisfies the stated Fourier-normalized uniform derivative estimate.
-/
theorem gaussianBumpEstimate (c : ℝ) (N : ℕ) (phiHat : ℝ → ℂ)
    (hc : 0 < c) (mu : ℝ) (hmu : 0 < mu) (hmuOne : mu ≤ 1)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c) :
    ContDiff ℝ N (gaussianBumpQuotient mu phiHat) ∧
    eLpNorm (fun xi : ℝ => ((2 * Real.pi)⁻¹ : ℝ) ^ N •
      iteratedDeriv N (gaussianBumpQuotient mu phiHat) xi) ⊤ volume ≤
      ENNReal.ofReal (c * C_gaussianBumpEstimate N) := by
  constructor
  · exact aux_gaussianBumpEstimate_contDiff N mu phiHat hphi
  · exact aux_gaussianBumpEstimate_eLpNorm N c mu phiHat hc.le hmu.le hmuOne hphi hsupp
      hphiBound

theorem aux_exp_one_lt_three : Real.exp 1 < 3 := by
  calc
    Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    _ < 3 := by norm_num

theorem aux_exp_pi_lt_128 : Real.exp Real.pi < (2 : ℝ) ^ 7 := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  calc
    Real.exp Real.pi < Real.exp 4 := (Real.exp_lt_exp).mpr hpi
    _ = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ < 3 ^ 4 :=
      pow_lt_pow_left₀ aux_exp_one_lt_three (Real.exp_pos _).le (by norm_num)
    _ < (2 : ℝ) ^ 7 := by norm_num

theorem aux_exp_pi_lt_81 : Real.exp Real.pi < 81 := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  calc
    Real.exp Real.pi < Real.exp 4 := (Real.exp_lt_exp).mpr hpi
    _ = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ < 3 ^ 4 :=
      pow_lt_pow_left₀ aux_exp_one_lt_three (Real.exp_pos _).le (by norm_num)
    _ = 81 := by norm_num

theorem aux_inv_pi_lt_third : Real.pi⁻¹ < (1 / 3 : ℝ) := by
  calc
    Real.pi⁻¹ < (3 : ℝ)⁻¹ :=
      (inv_lt_inv₀ Real.pi_pos (by norm_num)).mpr Real.pi_gt_three
    _ = 1 / 3 := by norm_num

theorem aux_inv_two_pi_lt_sixth : (2 * Real.pi)⁻¹ < (1 / 6 : ℝ) := by
  calc
    (2 * Real.pi)⁻¹ < (6 : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by norm_num)).mpr
        (by nlinarith [Real.pi_gt_three])
    _ = 1 / 6 := by norm_num

theorem aux_inv_four_pi_sq_lt_one_36 :
    (4 * Real.pi ^ 2)⁻¹ < (1 / 36 : ℝ) := by
  have hpiSq : 9 < Real.pi ^ 2 := by
    have h : (3 : ℝ) ^ 2 < Real.pi ^ 2 :=
      pow_lt_pow_left₀ Real.pi_gt_three (by norm_num) (by norm_num)
    norm_num at h
    exact h
  calc
    (4 * Real.pi ^ 2)⁻¹ < (36 : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith)
    _ = 1 / 36 := by norm_num

theorem aux_inv_two_pi_sq_lt_one_18 :
    (2 * Real.pi ^ 2)⁻¹ < (1 / 18 : ℝ) := by
  have hpiSq : 9 < Real.pi ^ 2 := by
    have h : (3 : ℝ) ^ 2 < Real.pi ^ 2 :=
      pow_lt_pow_left₀ Real.pi_gt_three (by norm_num) (by norm_num)
    norm_num at h
    exact h
  calc
    (2 * Real.pi ^ 2)⁻¹ < (18 : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith)
    _ = 1 / 18 := by norm_num

theorem aux_inv_eight_pi_cube_lt_one_216 :
    (8 * Real.pi ^ 3)⁻¹ < (1 / 216 : ℝ) := by
  have hpiSq : 9 < Real.pi ^ 2 := by
    have h : (3 : ℝ) ^ 2 < Real.pi ^ 2 :=
      pow_lt_pow_left₀ Real.pi_gt_three (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hpiCube : 27 < Real.pi ^ 3 := by
    calc
      27 = 9 * 3 := by norm_num
      _ < 9 * Real.pi := mul_lt_mul_of_pos_left Real.pi_gt_three (by norm_num)
      _ < Real.pi ^ 2 * Real.pi := mul_lt_mul_of_pos_right hpiSq Real.pi_pos
      _ = Real.pi ^ 3 := by ring
  calc
    (8 * Real.pi ^ 3)⁻¹ < (216 : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith)
    _ = 1 / 216 := by norm_num

theorem aux_C_gaussianEstimate_zero :
    C_gaussianEstimate 0 ≤ (2 : ℝ) ^ (7 * (0 + 1) ^ 2) := by
  simpa [C_gaussianEstimate] using (le_of_lt aux_exp_pi_lt_128)

theorem aux_gaussianEstimate_term_bound (n k : ℕ) :
    (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - 2 * k).factorial : ℝ)) *
        (2 : ℝ) ^ (n - 2 * k) * Real.pi ^ (n - k) ≤
      (2 : ℝ) ^ (n ^ 2 + 3 * n) := by
  have hden : 1 ≤ (k.factorial : ℝ) * ((n - 2 * k).factorial : ℝ) := by
    apply one_le_mul_of_one_le_of_one_le <;>
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hquot : (n.factorial : ℝ) /
      ((k.factorial : ℝ) * ((n - 2 * k).factorial : ℝ)) ≤ n.factorial :=
    div_le_self (by positivity) hden
  have hfac : (n.factorial : ℝ) ≤ (2 : ℝ) ^ (n ^ 2) := by
    exact_mod_cast aux_factorial_le_two_pow_sq n
  have htwo : (2 : ℝ) ^ (n - 2 * k) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hpiSmall : Real.pi ^ (n - k) ≤ (4 : ℝ) ^ (n - k) :=
    pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le _
  have hpi : Real.pi ^ (n - k) ≤ (4 : ℝ) ^ n :=
    hpiSmall.trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
  calc
    (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - 2 * k).factorial : ℝ)) *
        (2 : ℝ) ^ (n - 2 * k) * Real.pi ^ (n - k) ≤
        (n.factorial : ℝ) * (2 : ℝ) ^ n * (4 : ℝ) ^ n := by gcongr
    _ ≤ (2 : ℝ) ^ (n ^ 2) * (2 : ℝ) ^ n * (4 : ℝ) ^ n := by gcongr
    _ = (2 : ℝ) ^ (n ^ 2 + 3 * n) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

theorem aux_gaussianEstimate_sum_bound (n : ℕ) :
    ∑ k ∈ Finset.range (n / 2 + 1),
      (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - 2 * k).factorial : ℝ)) *
        (2 : ℝ) ^ (n - 2 * k) * Real.pi ^ (n - k) ≤
      ((n / 2 + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (n ^ 2 + 3 * n) := by
  simpa [Finset.card_range, nsmul_eq_mul] using
    (Finset.sum_le_card_nsmul (Finset.range (n / 2 + 1))
      (fun k => (n.factorial : ℝ) /
        ((k.factorial : ℝ) * ((n - 2 * k).factorial : ℝ)) *
          (2 : ℝ) ^ (n - 2 * k) * Real.pi ^ (n - k))
      ((2 : ℝ) ^ (n ^ 2 + 3 * n)) (by
        intro k _
        exact aux_gaussianEstimate_term_bound n k))

theorem aux_C_gaussianEstimate_bound (n : ℕ) :
    C_gaussianEstimate n ≤ (2 : ℝ) ^ (7 * (n + 1) ^ 2) := by
  by_cases hn : n = 0
  · subst n
    exact aux_C_gaussianEstimate_zero
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hcard : ((n / 2 + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast (le_trans (by omega : n / 2 + 1 ≤ n + 1)
        (aux_nat_le_two_pow (n + 1)))
    unfold C_gaussianEstimate
    calc
      Real.exp Real.pi *
          ∑ k ∈ Finset.range (n / 2 + 1),
            (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - 2 * k).factorial : ℝ)) *
              (2 : ℝ) ^ (n - 2 * k) * Real.pi ^ (n - k) ≤
          Real.exp Real.pi *
            (((n / 2 + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (n ^ 2 + 3 * n)) := by
              gcongr
              exact aux_gaussianEstimate_sum_bound n
      _ ≤ (2 : ℝ) ^ 7 * ((2 : ℝ) ^ (n + 1) *
          (2 : ℝ) ^ (n ^ 2 + 3 * n)) := by
        gcongr
        exact le_of_lt aux_exp_pi_lt_128
      _ = (2 : ℝ) ^ (n ^ 2 + 4 * n + 8) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ (2 : ℝ) ^ (7 * (n + 1) ^ 2) := by
        apply pow_le_pow_right₀ (by norm_num)
        nlinarith

theorem aux_C_gaussianBumpEstimate_bound (N : ℕ) :
    C_gaussianBumpEstimate N ≤ (2 : ℝ) ^ (8 * (N + 1) ^ 2) := by
  let B : ℝ := (2 : ℝ) ^ (7 * (N + 1) ^ 2)
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hC (l : ℕ) (hl : l ≤ N) : C_gaussianEstimate l ≤ B := by
    dsimp [B]
    calc
      C_gaussianEstimate l ≤ (2 : ℝ) ^ (7 * (l + 1) ^ 2) :=
        aux_C_gaussianEstimate_bound l
      _ ≤ (2 : ℝ) ^ (7 * (N + 1) ^ 2) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact Nat.mul_le_mul_left 7
          (Nat.pow_le_pow_left (Nat.succ_le_succ hl) 2)
  have hCnonneg (l : ℕ) : 0 ≤ C_gaussianEstimate l := by
    unfold C_gaussianEstimate
    apply mul_nonneg (Real.exp_pos _).le
    apply Finset.sum_nonneg
    intro k _
    exact aux_gaussianEstimate_coeff_nonneg l k
  have hterm (l : ℕ) (hl : l ∈ Finset.range (N + 1)) :
      (N.choose l : ℝ) * C_gaussianEstimate l ≤ (2 : ℝ) ^ N * B := by
    have hlN : l ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hchoose : (N.choose l : ℝ) ≤ (2 : ℝ) ^ N := by
      exact_mod_cast (Nat.choose_le_two_pow N l)
    exact mul_le_mul hchoose (hC l hlN) (hCnonneg l) (by positivity)
  have hsum : ∑ l ∈ Finset.range (N + 1),
      (N.choose l : ℝ) * C_gaussianEstimate l ≤
      ((N + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ N * B) := by
    simpa [Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul (Finset.range (N + 1))
        (fun l => (N.choose l : ℝ) * C_gaussianEstimate l)
        ((2 : ℝ) ^ N * B) (by
          intro l hl
          exact hterm l hl))
  have hsumNonneg : 0 ≤ ∑ l ∈ Finset.range (N + 1),
      (N.choose l : ℝ) * C_gaussianEstimate l := by
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (by positivity) (hCnonneg l)
  have hrpow : Real.rpow (2 * Real.pi) (-(N : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · nlinarith [Real.pi_gt_three]
    · push_cast
      linarith
  have hcard : ((N + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
    norm_cast
    exact (aux_nat_le_two_pow (N + 1))
  unfold C_gaussianBumpEstimate
  calc
    Real.rpow (2 * Real.pi) (-(N : ℝ)) *
        ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * C_gaussianEstimate l ≤
      ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * C_gaussianEstimate l := by
        simpa using mul_le_mul_of_nonneg_right hrpow hsumNonneg
    _ ≤ ((N + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ N * B) := hsum
    _ ≤ (2 : ℝ) ^ (N + 1) * ((2 : ℝ) ^ N * B) := by gcongr
    _ = (2 : ℝ) ^ (7 * (N + 1) ^ 2 + 2 * N + 1) := by
      dsimp [B]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ (2 : ℝ) ^ (8 * (N + 1) ^ 2) := by
      apply pow_le_pow_right₀ (by norm_num)
      nlinarith

theorem aux_C_gaussianBumpEstimate_zero_eq :
    C_gaussianBumpEstimate 0 = Real.exp Real.pi := by
  norm_num [C_gaussianBumpEstimate, C_gaussianEstimate]

theorem aux_C_gaussianBumpEstimate_one_eq :
    C_gaussianBumpEstimate 1 = Real.exp Real.pi * (1 + (2 * Real.pi)⁻¹) := by
  unfold C_gaussianBumpEstimate
  rw [← aux_gaussianBumpEstimate_qpow_eq_rpow 1]
  norm_num [C_gaussianEstimate, Finset.sum_range_succ]
  field_simp
  ring

theorem aux_C_gaussianBumpEstimate_two_eq :
    C_gaussianBumpEstimate 2 = Real.exp Real.pi *
      (1 + 3 * (2 * Real.pi)⁻¹ + (4 * Real.pi ^ 2)⁻¹) := by
  unfold C_gaussianBumpEstimate
  rw [← aux_gaussianBumpEstimate_qpow_eq_rpow 2]
  norm_num [C_gaussianEstimate, Finset.sum_range_succ]
  field_simp
  ring

theorem aux_C_gaussianBumpEstimate_three_eq :
    C_gaussianBumpEstimate 3 = Real.exp Real.pi *
      (1 + 3 * Real.pi⁻¹ + 3 * (2 * Real.pi ^ 2)⁻¹ + (8 * Real.pi ^ 3)⁻¹) := by
  unfold C_gaussianBumpEstimate
  rw [← aux_gaussianBumpEstimate_qpow_eq_rpow 3]
  norm_num [C_gaussianEstimate, Finset.sum_range_succ]
  field_simp
  ring

theorem aux_C_gaussianBumpEstimate_zero_lt_81 :
    C_gaussianBumpEstimate 0 < 81 := by
  rw [aux_C_gaussianBumpEstimate_zero_eq]
  exact aux_exp_pi_lt_81

theorem aux_C_gaussianBumpEstimate_one_lt_95 :
    C_gaussianBumpEstimate 1 < 95 := by
  rw [aux_C_gaussianBumpEstimate_one_eq]
  have hbracket : 1 + (2 * Real.pi)⁻¹ < (7 / 6 : ℝ) := by
    nlinarith [aux_inv_two_pi_lt_sixth]
  have hpos : 0 < 1 + (2 * Real.pi)⁻¹ := by positivity
  calc
    Real.exp Real.pi * (1 + (2 * Real.pi)⁻¹) <
        81 * (1 + (2 * Real.pi)⁻¹) :=
      mul_lt_mul_of_pos_right aux_exp_pi_lt_81 hpos
    _ < 81 * (7 / 6 : ℝ) := mul_lt_mul_of_pos_left hbracket (by norm_num)
    _ < 95 := by norm_num

theorem aux_C_gaussianBumpEstimate_two_lt_124 :
    C_gaussianBumpEstimate 2 < 124 := by
  rw [aux_C_gaussianBumpEstimate_two_eq]
  have hbracket : 1 + 3 * (2 * Real.pi)⁻¹ + (4 * Real.pi ^ 2)⁻¹ <
      (55 / 36 : ℝ) := by
    nlinarith [aux_inv_two_pi_lt_sixth, aux_inv_four_pi_sq_lt_one_36]
  have hpos : 0 < 1 + 3 * (2 * Real.pi)⁻¹ + (4 * Real.pi ^ 2)⁻¹ := by positivity
  calc
    Real.exp Real.pi * (1 + 3 * (2 * Real.pi)⁻¹ + (4 * Real.pi ^ 2)⁻¹) <
        81 * (1 + 3 * (2 * Real.pi)⁻¹ + (4 * Real.pi ^ 2)⁻¹) :=
      mul_lt_mul_of_pos_right aux_exp_pi_lt_81 hpos
    _ < 81 * (55 / 36 : ℝ) := mul_lt_mul_of_pos_left hbracket (by norm_num)
    _ < 124 := by norm_num

theorem aux_C_gaussianBumpEstimate_three_lt_176 :
    C_gaussianBumpEstimate 3 < 176 := by
  rw [aux_C_gaussianBumpEstimate_three_eq]
  have hbracket : 1 + 3 * Real.pi⁻¹ + 3 * (2 * Real.pi ^ 2)⁻¹ +
      (8 * Real.pi ^ 3)⁻¹ < (469 / 216 : ℝ) := by
    nlinarith [aux_inv_pi_lt_third, aux_inv_two_pi_sq_lt_one_18,
      aux_inv_eight_pi_cube_lt_one_216]
  have hpos : 0 < 1 + 3 * Real.pi⁻¹ + 3 * (2 * Real.pi ^ 2)⁻¹ +
      (8 * Real.pi ^ 3)⁻¹ := by positivity
  calc
    Real.exp Real.pi * (1 + 3 * Real.pi⁻¹ + 3 * (2 * Real.pi ^ 2)⁻¹ +
        (8 * Real.pi ^ 3)⁻¹) <
      81 * (1 + 3 * Real.pi⁻¹ + 3 * (2 * Real.pi ^ 2)⁻¹ +
        (8 * Real.pi ^ 3)⁻¹) :=
      mul_lt_mul_of_pos_right aux_exp_pi_lt_81 hpos
    _ < 81 * (469 / 216 : ℝ) := mul_lt_mul_of_pos_left hbracket (by norm_num)
    _ < 176 := by norm_num

/-- Source label `\ref{constant gaussian bump estimate}`. -/
theorem constantGaussianBumpEstimate (N : ℕ) :
    C_gaussianBumpEstimate N ≤ (2 : ℝ) ^ (8 * (N + 1) ^ 2) ∧
      C_gaussianBumpEstimate 0 < 81 ∧ C_gaussianBumpEstimate 1 < 95 ∧
        C_gaussianBumpEstimate 2 < 124 ∧ C_gaussianBumpEstimate 3 < 176 := by
  exact ⟨aux_C_gaussianBumpEstimate_bound N,
    aux_C_gaussianBumpEstimate_zero_lt_81,
    aux_C_gaussianBumpEstimate_one_lt_95,
    aux_C_gaussianBumpEstimate_two_lt_124,
    aux_C_gaussianBumpEstimate_three_lt_176⟩

/-- Source label `\ref{L:derivative-estimate-for-G}`; the explicit constant used by the public
theorem `derivativeEstimateForG`. -/
def C_derivativeEstimateForG (N : ℕ) : ℝ :=
  (N.factorial : ℝ) *
    Real.rpow (1 - Real.exp (-3 * Real.pi / 16)) (-((N + 1 : ℕ) : ℝ))

/-- For `derivativeEstimateForG`, the falling-factorial coefficient of the positive-order
derivative is bounded by the corresponding factorial on `[-1, 0]`. -/
theorem aux_derivativeEstimateForG_descPochhammer_bound (N : ℕ) {nu : ℝ}
    (hnu : -1 ≤ nu) (hnu0 : nu ≤ 0) :
    |(descPochhammer ℝ N).eval nu| ≤ N.factorial := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [descPochhammer_succ_eval, abs_mul]
      have hterm_nonpos : nu - (N : ℝ) ≤ 0 := by
        have hN : (0 : ℝ) ≤ N := by positivity
        linarith
      have hterm : |nu - (N : ℝ)| ≤ (N.succ : ℝ) := by
        rw [abs_of_nonpos hterm_nonpos]
        push_cast
        linarith
      calc
        |(descPochhammer ℝ N).eval nu| * |nu - (N : ℝ)| ≤
            (N.factorial : ℝ) * (N.succ : ℝ) := by
          gcongr
        _ = (N.succ.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring

/-- For `derivativeEstimateForG`, this compares the real-power factor in the derivative
formula with its value at the endpoint `e^{-3π/16}`. -/
theorem aux_derivativeEstimateForG_rpow_bound {N : ℕ} {nu x : ℝ}
    (hnu : -1 ≤ nu) (hnu0 : nu ≤ 0)
    (hxa : x ≤ Real.exp (-3 * Real.pi / 16)) :
    (1 - x) ^ (nu - (N : ℝ)) ≤
      (1 - Real.exp (-3 * Real.pi / 16)) ^ (-((N + 1 : ℕ) : ℝ)) := by
  let a : ℝ := 1 - Real.exp (-3 * Real.pi / 16)
  have hexp : Real.exp (-3 * Real.pi / 16) < 1 := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    have : 0 < Real.pi := Real.pi_pos
    linarith
  have ha0 : 0 < a := by
    dsimp [a]
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have : 0 < Real.exp (-3 * Real.pi / 16) := Real.exp_pos _
    linarith
  have hbase : a ≤ 1 - x := by
    dsimp [a]
    linarith
  have hpow1 : (1 - x) ^ (nu - (N : ℝ)) ≤ a ^ (nu - (N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha0 hbase (by
      have hN : (0 : ℝ) ≤ N := by positivity
      linarith)
  have hexponents : -((N + 1 : ℕ) : ℝ) ≤ nu - (N : ℝ) := by
    push_cast
    linarith
  exact hpow1.trans (Real.rpow_le_rpow_of_exponent_ge ha0 ha1 hexponents)

/-- For `derivativeEstimateForG`, this is the explicit positive-order derivative formula for
`x ↦ (1 - x)^ν - 1`. -/
theorem aux_derivativeEstimateForG_iteratedDeriv_pos (N : ℕ) (hN : 0 < N) (nu x : ℝ) :
    iteratedDeriv N (fun y : ℝ => (1 - y) ^ nu - 1) x =
      (-1 : ℝ) ^ N * (descPochhammer ℝ N).eval nu *
        (1 - x) ^ (nu - (N : ℝ)) := by
  have hsub : iteratedDeriv N (fun y : ℝ => (1 - y) ^ nu - 1) x =
      iteratedDeriv N (fun y : ℝ => (1 - y) ^ nu) x := by
    calc
      iteratedDeriv N (fun y : ℝ => (1 - y) ^ nu - 1) x =
          -iteratedDeriv N (fun y : ℝ => 1 - (1 - y) ^ nu) x := by
            rw [show (fun y : ℝ => (1 - y) ^ nu - 1) =
              fun y => -(1 - (1 - y) ^ nu) by
                funext y
                ring]
            rw [iteratedDeriv_fun_neg]
      _ = -iteratedDeriv N (-(fun y : ℝ => (1 - y) ^ nu)) x := by
            rw [iteratedDeriv_const_sub hN (1 : ℝ)]
      _ = iteratedDeriv N (fun y : ℝ => (1 - y) ^ nu) x := by
            rw [iteratedDeriv_neg]
            ring
  rw [hsub]
  rw [iteratedDeriv_comp_const_sub N (fun y : ℝ => y ^ nu) 1]
  simp only [smul_eq_mul, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  ring

/--
\begin{lemma}\label{L:derivative-estimate-for-G}
Let $N\in \N$, $\nu\in [-1,0)$ and let $H(x)=(1-x)^{\nu}-1$ for $x\in [0,1)$. Then for
$x\in [0,e^{-3\pi/16}]$, we have
\begin{equation}\label{auto:exponential-composition-derivative-bound}
|H^{(N)}(x)| \leq C_{\ref{L:derivative-estimate-for-G},N},
\end{equation}
where $C_{\ref{L:derivative-estimate-for-G},N}= N! \left(1 - e^{-3\pi/16}\right)^{-(N+1)}$.
\end{lemma}
-/
theorem derivativeEstimateForG (N : ℕ) {nu x : ℝ}
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hx : x ∈ Set.Icc (0 : ℝ) (Real.exp (-3 * Real.pi / 16))) :
    |iteratedDeriv N (fun y : ℝ => (1 - y) ^ nu - 1) x| ≤
      C_derivativeEstimateForG N := by
  let a : ℝ := 1 - Real.exp (-3 * Real.pi / 16)
  have hexp : Real.exp (-3 * Real.pi / 16) < 1 := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    have : 0 < Real.pi := Real.pi_pos
    linarith
  have ha0 : 0 < a := by
    dsimp [a]
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have : 0 < Real.exp (-3 * Real.pi / 16) := Real.exp_pos _
    linarith
  have hbase : a ≤ 1 - x := by
    dsimp [a]
    linarith [hx.2]
  have hbase0 : 0 < 1 - x := ha0.trans_le hbase
  have hbase1 : 1 - x ≤ 1 := by linarith [hx.1]
  by_cases hN : N = 0
  · subst N
    have hpower : 1 ≤ (1 - x) ^ nu :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hbase0 hbase1 hnu.2.le
    have hcomp : (1 - x) ^ nu ≤ (1 - x) ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1
      linarith [hnu.1]
    have hscale : (1 - x) ^ (-1 : ℝ) ≤ a ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ha0 hbase (by norm_num)
    rw [iteratedDeriv_zero, abs_of_nonneg (sub_nonneg.mpr hpower)]
    calc
      (1 - x) ^ nu - 1 ≤ (1 - x) ^ nu := sub_le_self _ zero_le_one
      _ ≤ (1 - x) ^ (-1 : ℝ) := hcomp
      _ ≤ a ^ (-1 : ℝ) := hscale
      _ = C_derivativeEstimateForG 0 := by
        simp [C_derivativeEstimateForG, a]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hformula := aux_derivativeEstimateForG_iteratedDeriv_pos N hNpos nu x
    rw [hformula, abs_mul, abs_mul]
    have hsign : |(-1 : ℝ) ^ N| = 1 := by
      rw [abs_pow]
      norm_num
    have hpowerpos : 0 < (1 - x) ^ (nu - (N : ℝ)) :=
      Real.rpow_pos_of_pos hbase0 _
    rw [hsign, abs_of_pos hpowerpos, one_mul]
    have hcoeff : |(descPochhammer ℝ N).eval nu| ≤ (N.factorial : ℝ) :=
      aux_derivativeEstimateForG_descPochhammer_bound N hnu.1 hnu.2.le
    have hpowbound : (1 - x) ^ (nu - (N : ℝ)) ≤
        a ^ (-((N + 1 : ℕ) : ℝ)) := by
      exact aux_derivativeEstimateForG_rpow_bound hnu.1 hnu.2.le hx.2
    calc
      |(descPochhammer ℝ N).eval nu| * (1 - x) ^ (nu - (N : ℝ)) ≤
          (N.factorial : ℝ) * a ^ (-((N + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul hcoeff hpowbound (Real.rpow_nonneg hbase0.le _) (by positivity)
      _ = C_derivativeEstimateForG N := by
        simp [C_derivativeEstimateForG, a]

/-- Source label `\ref{L:faa-di-bruno}`; the explicit constant used by the public theorem
`faaDiBruno`. -/
noncomputable def C_faaDiBruno (N : ℕ) : ℝ :=
  if N = 0 then
    2 * C_derivativeEstimateForG 0 * C_gaussianBumpDecay 0 2
  else
    (2 : ℝ) ^ (N + 1) *
      ∑ c : OrderedFinpartition N,
        C_derivativeEstimateForG c.length *
          ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)

theorem aux_C_derivativeEstimateForG_nonneg (N : ℕ) :
    0 ≤ C_derivativeEstimateForG N := by
  unfold C_derivativeEstimateForG
  apply mul_nonneg
  · positivity
  · apply Real.rpow_nonneg
    have hexp : Real.exp (-3 * Real.pi / 16) < 1 := by
      rw [← Real.exp_zero, Real.exp_lt_exp]
      nlinarith [Real.pi_pos]
    linarith

theorem aux_C_gaussianBumpDecay_nonneg (m N : ℕ) :
    0 ≤ C_gaussianBumpDecay m N := by
  unfold C_gaussianBumpDecay
  apply mul_nonneg <;> exact Real.rpow_nonneg (by positivity) _

theorem aux_C_faaDiBruno_nonneg (N : ℕ) : 0 ≤ C_faaDiBruno N := by
  rw [C_faaDiBruno]
  split_ifs with hN
  · exact mul_nonneg (mul_nonneg (by positivity) (aux_C_derivativeEstimateForG_nonneg 0))
      (aux_C_gaussianBumpDecay_nonneg 0 2)
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro c _
    apply mul_nonneg (aux_C_derivativeEstimateForG_nonneg c.length)
    apply Finset.prod_nonneg
    intro j _
    exact aux_C_gaussianBumpDecay_nonneg (c.partSize j) (N + 2)

theorem aux_faaDiBruno_ordered_bound
    (N : ℕ) (f g : ℝ → ℝ) (x : ℝ)
    (hg : ContDiffAt ℝ N g (f x)) (hf : ContDiffAt ℝ N f x)
    (A B : ℕ → ℝ)
    (hA : ∀ m : ℕ, m ≤ N → |iteratedDeriv m g (f x)| ≤ A m)
    (hB : ∀ m : ℕ, m ≤ N → |iteratedDeriv m f x| ≤ B m) :
    |iteratedDeriv N (g ∘ f) x| ≤
      ∑ c : OrderedFinpartition N, A c.length * ∏ j, B (c.partSize j) := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hg hf le_rfl]
  calc
    |∑ c : OrderedFinpartition N,
        iteratedDeriv c.length g (f x) * ∏ j, iteratedDeriv (c.partSize j) f x| ≤
        ∑ c : OrderedFinpartition N,
          |iteratedDeriv c.length g (f x) * ∏ j, iteratedDeriv (c.partSize j) f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : OrderedFinpartition N, A c.length * ∏ j, B (c.partSize j) := by
      apply Finset.sum_le_sum
      intro c _
      rw [abs_mul, Finset.abs_prod]
      have hAc : 0 ≤ A c.length :=
        (abs_nonneg (iteratedDeriv c.length g (f x))).trans (hA c.length c.length_le)
      apply mul_le_mul (hA c.length c.length_le)
      · apply Finset.prod_le_prod
        · intro j _
          exact abs_nonneg (iteratedDeriv (c.partSize j) f x)
        · intro j _
          exact hB (c.partSize j) (c.partSize_le j)
      · exact Finset.prod_nonneg fun j _ =>
          abs_nonneg (iteratedDeriv (c.partSize j) f x)
      · exact hAc

theorem aux_faaDiBruno_scale_tail (N : ℕ) {t xi : ℝ}
    (ht : Real.sqrt 3 / 2 ≤ t) (hxi : 1 / 2 ≤ |xi|) :
    t ^ N * bracketBump (t * xi) ^ (N + 2) ≤
      (2 : ℝ) ^ (N + 1) * |xi|⁻¹ ^ 2 := by
  have htpos : 0 < t := by
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    linarith
  have hxipos : 0 < |xi| := by linarith
  have htxpos : 0 < t * |xi| := mul_pos htpos hxipos
  have hbracket : bracketBump (t * xi) ≤ (t * |xi|)⁻¹ := by
    rw [bracketBump, abs_mul, abs_of_nonneg htpos.le]
    simpa only [one_div] using one_div_le_one_div_of_le htxpos (by linarith)
  have hbracketNonneg : 0 ≤ bracketBump (t * xi) := by
    rw [bracketBump]
    positivity
  have hpow : bracketBump (t * xi) ^ (N + 2) ≤ ((t * |xi|)⁻¹) ^ (N + 2) :=
    pow_le_pow_left₀ hbracketNonneg hbracket _
  have htSq : (3 : ℝ) / 4 ≤ t ^ 2 := by
    have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    calc
      (3 : ℝ) / 4 = (Real.sqrt 3 / 2) ^ 2 := by
        rw [div_pow, hsqrtSq]
        norm_num
      _ ≤ t ^ 2 := (sq_le_sq₀ (by positivity) htpos.le).2 ht
  have htInvSq : t⁻¹ ^ 2 ≤ 2 := by
    calc
      t⁻¹ ^ 2 = (t ^ 2)⁻¹ := by rw [inv_pow]
      _ ≤ ((3 : ℝ) / 4)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) htSq
      _ ≤ 2 := by norm_num
  have hxiInv : |xi|⁻¹ ≤ 2 := by
    calc
      |xi|⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hxi
      _ = 2 := by norm_num
  have hxiInvPow : |xi|⁻¹ ^ N ≤ (2 : ℝ) ^ N :=
    pow_le_pow_left₀ (inv_nonneg.mpr hxipos.le) hxiInv _
  calc
    t ^ N * bracketBump (t * xi) ^ (N + 2) ≤
        t ^ N * ((t * |xi|)⁻¹) ^ (N + 2) :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg htpos.le _)
    _ = t⁻¹ ^ 2 * (|xi|⁻¹ ^ N * |xi|⁻¹ ^ 2) := by
      rw [mul_inv_rev, pow_add, mul_pow, mul_pow]
      have htn : t ^ N * t⁻¹ ^ N = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt htpos), one_pow]
      rw [show t ^ N * (|xi|⁻¹ ^ N * t⁻¹ ^ N * (|xi|⁻¹ ^ 2 * t⁻¹ ^ 2)) =
          (t ^ N * t⁻¹ ^ N) * t⁻¹ ^ 2 * (|xi|⁻¹ ^ N * |xi|⁻¹ ^ 2) by ring, htn]
      ring
    _ ≤ 2 * ((2 : ℝ) ^ N * |xi|⁻¹ ^ 2) := by
      apply mul_le_mul htInvSq
      · apply mul_le_mul_of_nonneg_right hxiInvPow
        exact pow_nonneg (inv_nonneg.mpr hxipos.le) _
      · exact mul_nonneg (pow_nonneg (by positivity) _)
          (pow_nonneg (inv_nonneg.mpr hxipos.le) _)
      · norm_num
    _ = (2 : ℝ) ^ (N + 1) * |xi|⁻¹ ^ 2 := by
      rw [pow_succ]
      ring

theorem aux_faaDiBruno_scaledGaussian_iteratedDeriv (k : ℕ) (t xi : ℝ) :
    iteratedDeriv k (fun y : ℝ => Gaussians.gaussian (t * y)) xi =
      t ^ k * iteratedDeriv k Gaussians.gaussian (t * xi) := by
  have hgauss : ContDiff ℝ k Gaussians.gaussian :=
    aux_gaussian_contDiff.of_le (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ by exact le_top))
  have hcomp := congrFun (iteratedDeriv_comp_const_smul hgauss t) xi
  simpa only [Function.comp_def, smul_eq_mul] using hcomp

theorem aux_faaDiBruno_scaledGaussian_bound (N k : ℕ) {t xi : ℝ} (ht : 0 ≤ t) :
    |iteratedDeriv k (fun y : ℝ => Gaussians.gaussian (t * y)) xi| ≤
      t ^ k * C_gaussianBumpDecay k (N + 2) * bracketBump (t * xi) ^ (N + 2) := by
  rw [aux_faaDiBruno_scaledGaussian_iteratedDeriv, abs_mul,
    abs_of_nonneg (pow_nonneg ht _)]
  calc
    t ^ k * |iteratedDeriv k Gaussians.gaussian (t * xi)| ≤
        t ^ k * (C_gaussianBumpDecay k (N + 2) * bracketBump (t * xi) ^ (N + 2)) :=
      mul_le_mul_of_nonneg_left (gaussianBumpDecay (t * xi) k (N + 2))
        (pow_nonneg ht _)
    _ = t ^ k * C_gaussianBumpDecay k (N + 2) * bracketBump (t * xi) ^ (N + 2) := by
      ring

theorem aux_faaDiBruno_scaledGaussian_range {t xi : ℝ}
    (ht : Real.sqrt 3 / 2 ≤ t) (hxi : 1 / 2 ≤ |xi|) :
    Gaussians.gaussian (t * xi) ∈ Set.Icc (0 : ℝ) (Real.exp (-3 * Real.pi / 16)) := by
  have htpos : 0 < t := by
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    linarith
  have htxabs : Real.sqrt 3 / 4 ≤ |t * xi| := by
    rw [abs_mul, abs_of_nonneg htpos.le]
    calc
      Real.sqrt 3 / 4 = (Real.sqrt 3 / 2) * (1 / 2) := by ring
      _ ≤ t * |xi| := mul_le_mul ht hxi (by positivity) (by positivity)
  have hsq : (3 : ℝ) / 16 ≤ (t * xi) ^ 2 := by
    calc
      (3 : ℝ) / 16 = (Real.sqrt 3 / 4) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      _ ≤ |t * xi| ^ 2 := (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 htxabs
      _ = (t * xi) ^ 2 := sq_abs _
  constructor
  · exact (aux_gaussian_pos _).le
  · change Real.exp (-Real.pi * (t * xi) ^ 2) ≤ Real.exp (-3 * Real.pi / 16)
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]

theorem aux_faaDiBruno_partSize_sum {N : ℕ} (c : OrderedFinpartition N) :
    ∑ j, c.partSize j = N := by
  simpa using Fintype.card_congr c.equivSigma

theorem aux_faaDiBruno_ordered_product_bound (N : ℕ) (c : OrderedFinpartition N)
    (t b : ℝ) (hN : 0 < N) (ht : 0 ≤ t) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∏ j, (t ^ c.partSize j * C_gaussianBumpDecay (c.partSize j) (N + 2) * b ^ (N + 2)) ≤
      (∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
        (t ^ N * b ^ (N + 2)) := by
  have hcpos : 0 < c.length := c.length_pos hN
  have hCnonneg (j : Fin c.length) :
      0 ≤ C_gaussianBumpDecay (c.partSize j) (N + 2) :=
    aux_C_gaussianBumpDecay_nonneg _ _
  have htpow : ∏ j, t ^ c.partSize j = t ^ N := by
    rw [Finset.prod_pow_eq_pow_sum, aux_faaDiBruno_partSize_sum]
  have hbprod : ∏ _j : Fin c.length, b ^ (N + 2) ≤ b ^ (N + 2) := by
    rw [Finset.prod_pow]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, Nat.mul_comm]
    have hle : N + 2 ≤ (N + 2) * c.length := Nat.le_mul_of_pos_right _ hcpos
    exact pow_le_pow_of_le_one hb0 hb1 hle
  calc
    ∏ j, (t ^ c.partSize j * C_gaussianBumpDecay (c.partSize j) (N + 2) * b ^ (N + 2)) =
        (∏ j, t ^ c.partSize j) *
          (∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
            ∏ _j : Fin c.length, b ^ (N + 2) := by
      simp_rw [mul_assoc]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ t ^ N * (∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) * b ^ (N + 2) := by
      rw [htpow]
      apply mul_le_mul_of_nonneg_left hbprod
      exact mul_nonneg (pow_nonneg ht _)
        (Finset.prod_nonneg fun j _ => hCnonneg j)
    _ = (∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
        (t ^ N * b ^ (N + 2)) := by
      ring

theorem aux_faaDiBruno_zero_cancellation {nu z : ℝ}
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hz : z ∈ Set.Icc (0 : ℝ) (Real.exp (-3 * Real.pi / 16))) :
    |(1 - z) ^ nu - 1| ≤ C_derivativeEstimateForG 0 * z := by
  let a : ℝ := 1 - Real.exp (-3 * Real.pi / 16)
  have hexp : Real.exp (-3 * Real.pi / 16) < 1 := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    nlinarith [Real.pi_pos]
  have ha0 : 0 < a := by
    dsimp [a]
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have : 0 < Real.exp (-3 * Real.pi / 16) := Real.exp_pos _
    linarith
  have hbase : a ≤ 1 - z := by
    dsimp [a]
    linarith [hz.2]
  have hbase0 : 0 < 1 - z := ha0.trans_le hbase
  have hbase1 : 1 - z ≤ 1 := by linarith [hz.1]
  have hpower : 1 ≤ (1 - z) ^ nu :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hbase0 hbase1 hnu.2.le
  have hcomp : (1 - z) ^ nu ≤ (1 - z) ^ (-1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1
    linarith [hnu.1]
  have hscale : (1 - z) ^ (-1 : ℝ) ≤ a ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ha0 hbase (by norm_num)
  rw [abs_of_nonneg (sub_nonneg.mpr hpower)]
  calc
    (1 - z) ^ nu - 1 ≤ (1 - z) ^ (-1 : ℝ) - 1 :=
      sub_le_sub_right hcomp 1
    _ = z * (1 - z)⁻¹ := by
      rw [Real.rpow_neg_one]
      field_simp
      ring
    _ ≤ z * a⁻¹ :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.rpow_neg_one] using hscale) hz.1
    _ = C_derivativeEstimateForG 0 * z := by
      simp [C_derivativeEstimateForG, a, Real.rpow_neg_one, mul_comm]

theorem aux_faaDiBruno_zero {nu t xi : ℝ}
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (ht : Real.sqrt 3 / 2 ≤ t) (hxi : 1 / 2 ≤ |xi|) :
    |iteratedDeriv 0 (fun y : ℝ => (1 - Gaussians.gaussian (t * y)) ^ nu - 1) xi| ≤
      C_faaDiBruno 0 * |xi|⁻¹ ^ 2 := by
  let z : ℝ := Gaussians.gaussian (t * xi)
  let b : ℝ := bracketBump (t * xi)
  have hz : z ∈ Set.Icc (0 : ℝ) (Real.exp (-3 * Real.pi / 16)) := by
    simpa [z] using aux_faaDiBruno_scaledGaussian_range ht hxi
  have hgauss : z ≤ C_gaussianBumpDecay 0 2 * b ^ 2 := by
    have h := gaussianBumpDecay (t * xi) 0 2
    simpa [z, b, abs_of_pos (aux_gaussian_pos _)] using h
  have hscale : b ^ 2 ≤ 2 * |xi|⁻¹ ^ 2 := by
    simpa [b] using aux_faaDiBruno_scale_tail 0 ht hxi
  rw [iteratedDeriv_zero]
  change |(1 - z) ^ nu - 1| ≤ C_faaDiBruno 0 * |xi|⁻¹ ^ 2
  calc
    |(1 - z) ^ nu - 1| ≤ C_derivativeEstimateForG 0 * z :=
      aux_faaDiBruno_zero_cancellation hnu hz
    _ ≤ C_derivativeEstimateForG 0 *
        (C_gaussianBumpDecay 0 2 * b ^ 2) :=
      mul_le_mul_of_nonneg_left hgauss (aux_C_derivativeEstimateForG_nonneg 0)
    _ = (C_derivativeEstimateForG 0 * C_gaussianBumpDecay 0 2) * b ^ 2 := by
      ring
    _ ≤ (C_derivativeEstimateForG 0 * C_gaussianBumpDecay 0 2) *
        (2 * |xi|⁻¹ ^ 2) := by
      apply mul_le_mul_of_nonneg_left hscale
      exact mul_nonneg (aux_C_derivativeEstimateForG_nonneg 0)
        (aux_C_gaussianBumpDecay_nonneg 0 2)
    _ = C_faaDiBruno 0 * |xi|⁻¹ ^ 2 := by
      simp [C_faaDiBruno]
      ring

theorem aux_faaDiBruno_positive (N : ℕ) (hN : 0 < N) {nu t xi : ℝ}
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (ht : Real.sqrt 3 / 2 ≤ t) (hxi : 1 / 2 ≤ |xi|) :
    |iteratedDeriv N (fun y : ℝ => (1 - Gaussians.gaussian (t * y)) ^ nu - 1) xi| ≤
      C_faaDiBruno N * |xi|⁻¹ ^ 2 := by
  let H : ℝ → ℝ := fun y => (1 - y) ^ nu - 1
  let F : ℝ → ℝ := fun y => Gaussians.gaussian (t * y)
  let b : ℝ := bracketBump (t * xi)
  have htpos : 0 < t := by
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    linarith
  have hRange : F xi ∈ Set.Icc (0 : ℝ) (Real.exp (-3 * Real.pi / 16)) := by
    simpa [F] using aux_faaDiBruno_scaledGaussian_range ht hxi
  have hexp : Real.exp (-3 * Real.pi / 16) < 1 := by
    rw [← Real.exp_zero, Real.exp_lt_exp]
    nlinarith [Real.pi_pos]
  have hbase : 1 - F xi ≠ 0 := ne_of_gt (sub_pos.mpr (hRange.2.trans_lt hexp))
  have hH : ContDiffAt ℝ N H (F xi) := by
    have haff : ContDiffAt ℝ N (fun y : ℝ => 1 - y) (F xi) := by fun_prop
    exact (Real.contDiffAt_rpow_const_of_ne hbase).comp _ haff |>.sub contDiffAt_const
  have hF : ContDiffAt ℝ N F xi := by
    have hlin : ContDiff ℝ N (fun y : ℝ => t * y) := by fun_prop
    have hgauss : ContDiff ℝ N Gaussians.gaussian :=
      aux_gaussian_contDiff.of_le (by
        exact_mod_cast (show (N : ℕ∞) ≤ ⊤ by exact le_top))
    simpa [F, Function.comp_def] using (hgauss.comp hlin).contDiffAt
  have hHbound (m : ℕ) (hm : m ≤ N) :
      |iteratedDeriv m H (F xi)| ≤ C_derivativeEstimateForG m := by
    simpa [H] using derivativeEstimateForG m hnu hRange
  have hFbound (m : ℕ) (hm : m ≤ N) :
      |iteratedDeriv m F xi| ≤
        t ^ m * C_gaussianBumpDecay m (N + 2) * b ^ (N + 2) := by
    simpa [F, b] using aux_faaDiBruno_scaledGaussian_bound N m htpos.le
  have hmain := aux_faaDiBruno_ordered_bound N F H xi hH hF
    C_derivativeEstimateForG
    (fun m => t ^ m * C_gaussianBumpDecay m (N + 2) * b ^ (N + 2))
    hHbound hFbound
  have hb0 : 0 ≤ b := by
    dsimp [b]
    rw [bracketBump]
    positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    rw [bracketBump]
    exact (inv_le_one₀ (by positivity)).mpr (by linarith [abs_nonneg (t * xi)])
  have hterm (c : OrderedFinpartition N) :
      C_derivativeEstimateForG c.length *
          ∏ j, (t ^ c.partSize j * C_gaussianBumpDecay (c.partSize j) (N + 2) *
            b ^ (N + 2)) ≤
        (C_derivativeEstimateForG c.length *
          ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
          (t ^ N * b ^ (N + 2)) := by
    calc
      C_derivativeEstimateForG c.length *
          ∏ j, (t ^ c.partSize j * C_gaussianBumpDecay (c.partSize j) (N + 2) *
            b ^ (N + 2)) ≤
          C_derivativeEstimateForG c.length *
            ((∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
              (t ^ N * b ^ (N + 2))) :=
        mul_le_mul_of_nonneg_left
          (aux_faaDiBruno_ordered_product_bound N c t b hN htpos.le hb0 hb1)
          (aux_C_derivativeEstimateForG_nonneg c.length)
      _ = (C_derivativeEstimateForG c.length *
          ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
          (t ^ N * b ^ (N + 2)) := by ring
  have hsum :
      ∑ c : OrderedFinpartition N, C_derivativeEstimateForG c.length *
          ∏ j, (t ^ c.partSize j * C_gaussianBumpDecay (c.partSize j) (N + 2) *
            b ^ (N + 2)) ≤
        ∑ c : OrderedFinpartition N,
          (C_derivativeEstimateForG c.length *
            ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
            (t ^ N * b ^ (N + 2)) := by
    apply Finset.sum_le_sum
    intro c _
    exact hterm c
  have hsumNonneg : 0 ≤ ∑ c : OrderedFinpartition N,
      C_derivativeEstimateForG c.length *
        ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) := by
    apply Finset.sum_nonneg
    intro c _
    apply mul_nonneg (aux_C_derivativeEstimateForG_nonneg c.length)
    apply Finset.prod_nonneg
    intro j _
    exact aux_C_gaussianBumpDecay_nonneg _ _
  have hscale : t ^ N * b ^ (N + 2) ≤ (2 : ℝ) ^ (N + 1) * |xi|⁻¹ ^ 2 := by
    simpa [b] using aux_faaDiBruno_scale_tail N ht hxi
  have hfactor :
      ∑ c : OrderedFinpartition N,
          (C_derivativeEstimateForG c.length *
            ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
            (t ^ N * b ^ (N + 2)) =
        (∑ c : OrderedFinpartition N,
          C_derivativeEstimateForG c.length *
            ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
          (t ^ N * b ^ (N + 2)) := by
    rw [Finset.sum_mul]
  rw [show (fun y : ℝ => (1 - Gaussians.gaussian (t * y)) ^ nu - 1) = H ∘ F by
    funext y
    rfl]
  calc
    |iteratedDeriv N (H ∘ F) xi| ≤
        ∑ c : OrderedFinpartition N, C_derivativeEstimateForG c.length *
          ∏ j, (t ^ c.partSize j * C_gaussianBumpDecay (c.partSize j) (N + 2) *
            b ^ (N + 2)) := hmain
    _ ≤ ∑ c : OrderedFinpartition N,
          (C_derivativeEstimateForG c.length *
            ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
            (t ^ N * b ^ (N + 2)) := hsum
    _ = (∑ c : OrderedFinpartition N,
          C_derivativeEstimateForG c.length *
            ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
          (t ^ N * b ^ (N + 2)) := hfactor
    _ ≤ (∑ c : OrderedFinpartition N,
          C_derivativeEstimateForG c.length *
            ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) *
          ((2 : ℝ) ^ (N + 1) * |xi|⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left hscale hsumNonneg
    _ = C_faaDiBruno N * |xi|⁻¹ ^ 2 := by
      rw [C_faaDiBruno, if_neg (Nat.ne_of_gt hN)]
      ring

/--
Source label `\ref{L:faa-di-bruno}`. Let `N ∈ ℕ`, `ν ∈ [-1, 0)`, and
`t ≥ √3 / 2`, and put `S(ξ) = (1 - gaussian (t * ξ)) ^ ν - 1`. For
`|ξ| ≥ 1 / 2`, this proves
`|S^(N)(ξ)| ≤ C_faaDiBruno N * |ξ|⁻¹ ^ 2`.
-/
theorem faaDiBruno (N : ℕ) {nu t xi : ℝ}
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (ht : Real.sqrt 3 / 2 ≤ t) (hxi : 1 / 2 ≤ |xi|) :
    |iteratedDeriv N (fun y : ℝ => (1 - Gaussians.gaussian (t * y)) ^ nu - 1) xi| ≤
      C_faaDiBruno N * |xi|⁻¹ ^ 2 := by
  by_cases hN : N = 0
  · subst N
    exact aux_faaDiBruno_zero hnu ht hxi
  · exact aux_faaDiBruno_positive N (Nat.pos_of_ne_zero hN) hnu ht hxi

theorem aux_derivativeEstimateForG_base_ge_third :
    (1 / 3 : ℝ) ≤ 1 - Real.exp (-3 * Real.pi / 16) := by
  have hExpLower : (25 / 16 : ℝ) ≤ Real.exp (9 / 16 : ℝ) := by
    nlinarith [Real.add_one_le_exp (9 / 16 : ℝ)]
  have hInv : (Real.exp (9 / 16 : ℝ))⁻¹ ≤ (16 / 25 : ℝ) := by
    calc
      (Real.exp (9 / 16 : ℝ))⁻¹ ≤ (25 / 16 : ℝ)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hExpLower
      _ = 16 / 25 := by norm_num
  have hExp : Real.exp (-3 * Real.pi / 16) ≤ (16 / 25 : ℝ) := by
    calc
      Real.exp (-3 * Real.pi / 16) ≤ Real.exp (-(9 / 16 : ℝ)) := by
        apply (Real.exp_le_exp).mpr
        nlinarith [Real.pi_gt_three]
      _ = (Real.exp (9 / 16 : ℝ))⁻¹ := by rw [← Real.exp_neg]
      _ ≤ 16 / 25 := hInv
  linarith

theorem aux_third_rpow_neg_eq_three_pow (q : ℕ) :
    Real.rpow (1 / 3 : ℝ) (-((q + 1 : ℕ) : ℝ)) = (3 : ℝ) ^ (q + 1) := by
  change (1 / 3 : ℝ) ^ (-((q + 1 : ℕ) : ℝ)) = (3 : ℝ) ^ (q + 1)
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]

theorem aux_C_derivativeEstimateForG_le (q : ℕ) :
    C_derivativeEstimateForG q ≤ (q.factorial : ℝ) * (3 : ℝ) ^ (q + 1) := by
  unfold C_derivativeEstimateForG
  have hpow : Real.rpow (1 - Real.exp (-3 * Real.pi / 16)) (-((q + 1 : ℕ) : ℝ)) ≤
      Real.rpow (1 / 3 : ℝ) (-((q + 1 : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_nonpos (by norm_num)
      aux_derivativeEstimateForG_base_ge_third
    push_cast
    linarith
  calc
    (q.factorial : ℝ) * Real.rpow (1 - Real.exp (-3 * Real.pi / 16))
        (-((q + 1 : ℕ) : ℝ)) ≤
      (q.factorial : ℝ) * Real.rpow (1 / 3 : ℝ) (-((q + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (q.factorial : ℝ) * (3 : ℝ) ^ (q + 1) := by
      rw [aux_third_rpow_neg_eq_three_pow]

theorem aux_C_gaussianBumpDecay_le_pow (N m : ℕ) (hm : m ≤ N) :
    C_gaussianBumpDecay m (N + 2) ≤ (2 : ℝ) ^ (2 * N ^ 2 + 14 * N + 10) := by
  have hmOne : m + 1 ≤ N + 1 := Nat.succ_le_succ hm
  have hbase1 : 38 * ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N + 7) := by
    calc
      38 * ((m + 1 : ℕ) : ℝ) ≤ 64 * ((N + 1 : ℕ) : ℝ) := by
        apply mul_le_mul (by norm_num : (38 : ℝ) ≤ 64)
        · exact_mod_cast hmOne
        · positivity
        · norm_num
      _ ≤ 64 * (2 : ℝ) ^ (N + 1) := by
        gcongr
        exact_mod_cast aux_nat_le_two_pow (N + 1)
      _ = (2 : ℝ) ^ (N + 7) := by
        rw [show (64 : ℝ) = 2 ^ 6 by norm_num]
        rw [← pow_add]
        congr 1
        omega
  have hbase2 : 4 * ((N + 3 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N + 5) := by
    calc
      4 * ((N + 3 : ℕ) : ℝ) ≤ 4 * (2 : ℝ) ^ (N + 3) := by
        gcongr
        exact_mod_cast aux_nat_le_two_pow (N + 3)
      _ = (2 : ℝ) ^ (N + 5) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        rw [← pow_add]
        congr 1
        omega
  have hpow1 : Real.rpow (38 * ((m + 1 : ℕ) : ℝ)) ((m : ℝ) / 2) ≤
      (2 : ℝ) ^ ((N + 7) * N) := by
    calc
      Real.rpow (38 * ((m + 1 : ℕ) : ℝ)) ((m : ℝ) / 2) ≤
          Real.rpow ((2 : ℝ) ^ (N + 7)) ((m : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hbase1 (by positivity)
      _ ≤ Real.rpow ((2 : ℝ) ^ (N + 7)) (m : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact one_le_pow₀ (by norm_num)
        · have : 0 ≤ (m : ℝ) := by positivity
          nlinarith
      _ = ((2 : ℝ) ^ (N + 7)) ^ m := Real.rpow_natCast _ m
      _ = (2 : ℝ) ^ ((N + 7) * m) := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ ((N + 7) * N) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact Nat.mul_le_mul_left _ hm
  have hpow2 : Real.rpow (4 * ((N + 3 : ℕ) : ℝ)) (((N + 2 : ℕ) : ℝ) / 2) ≤
      (2 : ℝ) ^ ((N + 5) * (N + 2)) := by
    calc
      Real.rpow (4 * ((N + 3 : ℕ) : ℝ)) (((N + 2 : ℕ) : ℝ) / 2) ≤
          Real.rpow ((2 : ℝ) ^ (N + 5)) (((N + 2 : ℕ) : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hbase2 (by positivity)
      _ ≤ Real.rpow ((2 : ℝ) ^ (N + 5)) ((N + 2 : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact one_le_pow₀ (by norm_num)
        · have : 0 ≤ (N : ℝ) := by positivity
          nlinarith
      _ = ((2 : ℝ) ^ (N + 5)) ^ (N + 2) := Real.rpow_natCast _ _
      _ = (2 : ℝ) ^ ((N + 5) * (N + 2)) := by rw [← pow_mul]
  unfold C_gaussianBumpDecay
  calc
    Real.rpow (38 * ((m + 1 : ℕ) : ℝ)) ((m : ℝ) / 2) *
        Real.rpow (4 * (((N + 2) + 1 : ℕ) : ℝ)) (((N + 2 : ℕ) : ℝ) / 2) ≤
      (2 : ℝ) ^ ((N + 7) * N) * (2 : ℝ) ^ ((N + 5) * (N + 2)) := by
        simpa [Nat.add_assoc] using
          (mul_le_mul hpow1 hpow2 (Real.rpow_nonneg (by positivity) _)
            (by positivity : 0 ≤ (2 : ℝ) ^ ((N + 7) * N)))
    _ = (2 : ℝ) ^ (2 * N ^ 2 + 14 * N + 10) := by
      rw [← pow_add]
      congr 1
      ring

theorem aux_orderedFinpartition_card_le_factorial (N : ℕ) :
    Fintype.card (OrderedFinpartition N) ≤ N.factorial := by
  induction N with
  | zero =>
      have hcard : Fintype.card (OrderedFinpartition 0) = 1 := Fintype.card_unique
      simpa [hcard]
  | succ N ih =>
      calc
        Fintype.card (OrderedFinpartition (N + 1)) =
            ∑ c : OrderedFinpartition N, Fintype.card (Option (Fin c.length)) := by
              rw [← Fintype.card_sigma]
              exact (Fintype.card_congr (OrderedFinpartition.extendEquiv N)).symm
        _ = ∑ c : OrderedFinpartition N, (c.length + 1) := by
              congr with c
              simp
        _ ≤ ∑ _c : OrderedFinpartition N, (N + 1) := by
              apply Finset.sum_le_sum
              intro c _
              exact Nat.succ_le_succ c.length_le
        _ = Fintype.card (OrderedFinpartition N) * (N + 1) := by simp [mul_comm]
        _ ≤ N.factorial * (N + 1) := Nat.mul_le_mul_right _ ih
        _ = (N + 1).factorial := by rw [Nat.factorial_succ, Nat.mul_comm]

theorem aux_C_derivativeEstimateForG_le_pow (N q : ℕ) (hq : q ≤ N) :
    C_derivativeEstimateForG q ≤ (2 : ℝ) ^ (N ^ 2 + 2 * N + 2) := by
  calc
    C_derivativeEstimateForG q ≤ (q.factorial : ℝ) * (3 : ℝ) ^ (q + 1) :=
      aux_C_derivativeEstimateForG_le q
    _ ≤ (2 : ℝ) ^ (q ^ 2) * (4 : ℝ) ^ (q + 1) := by
      apply mul_le_mul
      · exact_mod_cast aux_factorial_le_two_pow_sq q
      · exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      · positivity
      · positivity
    _ = (2 : ℝ) ^ (q ^ 2 + 2 * (q + 1)) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    _ ≤ (2 : ℝ) ^ (N ^ 2 + 2 * N + 2) := by
      apply pow_le_pow_right₀ (by norm_num)
      nlinarith

theorem aux_C_faaDiBruno_prod_bound (N : ℕ) (c : OrderedFinpartition N) :
    ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) ≤
      (2 : ℝ) ^ (N * (2 * N ^ 2 + 14 * N + 10)) := by
  let D : ℝ := (2 : ℝ) ^ (2 * N ^ 2 + 14 * N + 10)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact one_le_pow₀ (by norm_num)
  calc
    ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) ≤ ∏ _j : Fin c.length, D := by
      refine Finset.prod_le_prod ?_ ?_
      · intro j _
        exact aux_C_gaussianBumpDecay_nonneg (c.partSize j) (N + 2)
      · intro j _
        exact aux_C_gaussianBumpDecay_le_pow N (c.partSize j) (c.partSize_le j)
    _ = D ^ c.length := by simp [D]
    _ ≤ D ^ N := pow_le_pow_right₀ hD c.length_le
    _ = (2 : ℝ) ^ (N * (2 * N ^ 2 + 14 * N + 10)) := by
      dsimp [D]
      rw [← pow_mul]
      congr 1
      ring

theorem aux_orderedFinpartition_card_le_two_pow_sq (N : ℕ) :
    Fintype.card (OrderedFinpartition N) ≤ 2 ^ (N ^ 2) :=
  (aux_orderedFinpartition_card_le_factorial N).trans
    (aux_factorial_le_two_pow_sq N)

theorem aux_C_faaDiBruno_term_bound (N : ℕ) (c : OrderedFinpartition N) :
    C_derivativeEstimateForG c.length *
        ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) ≤
      (2 : ℝ) ^ (2 * N ^ 3 + 15 * N ^ 2 + 12 * N + 2) := by
  calc
    C_derivativeEstimateForG c.length *
        ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) ≤
      (2 : ℝ) ^ (N ^ 2 + 2 * N + 2) *
        (2 : ℝ) ^ (N * (2 * N ^ 2 + 14 * N + 10)) := by
          apply mul_le_mul
          · exact aux_C_derivativeEstimateForG_le_pow N c.length c.length_le
          · exact aux_C_faaDiBruno_prod_bound N c
          · apply Finset.prod_nonneg
            intro j _
            exact aux_C_gaussianBumpDecay_nonneg (c.partSize j) (N + 2)
          · positivity
    _ = (2 : ℝ) ^ (2 * N ^ 3 + 15 * N ^ 2 + 12 * N + 2) := by
      rw [← pow_add]
      congr 1
      ring

theorem aux_C_faaDiBruno_sum_bound (N : ℕ) :
    ∑ c : OrderedFinpartition N,
      C_derivativeEstimateForG c.length *
        ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) ≤
      (2 : ℝ) ^ (2 * N ^ 3 + 16 * N ^ 2 + 12 * N + 2) := by
  let T : ℝ := (2 : ℝ) ^ (2 * N ^ 3 + 15 * N ^ 2 + 12 * N + 2)
  have hsum : ∑ c : OrderedFinpartition N,
      C_derivativeEstimateForG c.length *
        ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) ≤
      (Fintype.card (OrderedFinpartition N) : ℝ) * T := by
    simpa [T, nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul (Finset.univ : Finset (OrderedFinpartition N))
        (fun c => C_derivativeEstimateForG c.length *
          ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2)) T (by
            intro c _
            exact aux_C_faaDiBruno_term_bound N c))
  have hcard : (Fintype.card (OrderedFinpartition N) : ℝ) ≤ (2 : ℝ) ^ (N ^ 2) := by
    exact_mod_cast aux_orderedFinpartition_card_le_two_pow_sq N
  calc
    ∑ c : OrderedFinpartition N,
      C_derivativeEstimateForG c.length *
        ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) ≤
      (Fintype.card (OrderedFinpartition N) : ℝ) * T := hsum
    _ ≤ (2 : ℝ) ^ (N ^ 2) * T := by gcongr
    _ = (2 : ℝ) ^ (2 * N ^ 3 + 16 * N ^ 2 + 12 * N + 2) := by
      dsimp [T]
      rw [← pow_add]
      congr 1
      ring

theorem aux_C_faaDiBruno_zero_le : C_faaDiBruno 0 ≤ 72 := by
  rw [C_faaDiBruno, if_pos rfl]
  have hderiv : C_derivativeEstimateForG 0 ≤ 3 := by
    simpa using aux_C_derivativeEstimateForG_le 0
  have hdecay : C_gaussianBumpDecay 0 2 = 12 := by
    norm_num [C_gaussianBumpDecay]
  rw [hdecay]
  calc
    2 * C_derivativeEstimateForG 0 * 12 ≤ 2 * 3 * 12 := by gcongr
    _ = 72 := by norm_num

theorem aux_C_faaDiBruno_nonzero_bound (N : ℕ) (hN : N ≠ 0) :
    C_faaDiBruno N ≤ (2 : ℝ) ^ (10 * (N + 1) ^ 3) := by
  rw [C_faaDiBruno, if_neg hN]
  calc
    (2 : ℝ) ^ (N + 1) *
        ∑ c : OrderedFinpartition N,
          C_derivativeEstimateForG c.length *
            ∏ j, C_gaussianBumpDecay (c.partSize j) (N + 2) ≤
      (2 : ℝ) ^ (N + 1) *
        (2 : ℝ) ^ (2 * N ^ 3 + 16 * N ^ 2 + 12 * N + 2) := by
          gcongr
          exact aux_C_faaDiBruno_sum_bound N
    _ = (2 : ℝ) ^ (2 * N ^ 3 + 16 * N ^ 2 + 13 * N + 3) := by
      rw [← pow_add]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (10 * (N + 1) ^ 3) := by
      apply pow_le_pow_right₀ (by norm_num)
      nlinarith

theorem aux_C_faaDiBruno_bound (N : ℕ) :
    C_faaDiBruno N ≤ (2 : ℝ) ^ (10 * (N + 1) ^ 3) := by
  by_cases hN : N = 0
  · subst N
    calc
      C_faaDiBruno 0 ≤ 72 := aux_C_faaDiBruno_zero_le
      _ ≤ (2 : ℝ) ^ (10 * (0 + 1) ^ 3) := by norm_num
  · exact aux_C_faaDiBruno_nonzero_bound N hN

theorem aux_C_gaussianBumpDecay_one_three_le : C_gaussianBumpDecay 1 3 ≤ 576 := by
  have hpow16 : (16 : ℝ) ^ (3 / 2 : ℝ) = 64 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.rpow_add_one (by norm_num : (16 : ℝ) ≠ 0)]
    rw [← Real.sqrt_eq_rpow]
    norm_num
  have hsqrt : Real.sqrt 76 ≤ 9 := by
    have hsquare : (Real.sqrt 76) ^ 2 = 76 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (76 : ℝ)]
  unfold C_gaussianBumpDecay
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  change (76 : ℝ) ^ (1 / 2 : ℝ) * (16 : ℝ) ^ (3 / 2 : ℝ) ≤ 576
  rw [show (76 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 76 by
    rw [Real.sqrt_eq_rpow], hpow16]
  nlinarith

private theorem aux_C_faaDiBruno_one_eq :
    C_faaDiBruno 1 = 4 * C_derivativeEstimateForG 1 * C_gaussianBumpDecay 1 3 := by
  rw [C_faaDiBruno, if_neg (by norm_num)]
  rw [Fintype.sum_unique]
  simp only [OrderedFinpartition.default_eq]
  norm_num [OrderedFinpartition.atomic]
  ring

theorem aux_C_faaDiBruno_one_lt : C_faaDiBruno 1 < 27648 := by
  rw [aux_C_faaDiBruno_one_eq]
  have hderiv : C_derivativeEstimateForG 1 ≤ 9 := by
    calc
      C_derivativeEstimateForG 1 ≤ ((1 : ℕ).factorial : ℝ) * (3 : ℝ) ^ (1 + 1) :=
        aux_C_derivativeEstimateForG_le 1
      _ = 9 := by norm_num
  calc
    4 * C_derivativeEstimateForG 1 * C_gaussianBumpDecay 1 3 ≤ 4 * 9 * 576 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hderiv (by norm_num)
      · exact aux_C_gaussianBumpDecay_one_three_le
      · exact aux_C_gaussianBumpDecay_nonneg 1 3
      · positivity
    _ < 27648 := by norm_num

set_option maxHeartbeats 2000000 in
private theorem aux_atomicOne_extendLeft_prod :
    ∏ j, C_gaussianBumpDecay
      ((OrderedFinpartition.atomic 1).extendLeft.partSize j) 4 =
      C_gaussianBumpDecay 1 4 * C_gaussianBumpDecay 1 4 := by
  change (∏ j : Fin 2, C_gaussianBumpDecay
    (Fin.cons (α := fun _ : Fin 2 => ℕ) 1 (fun _ : Fin 1 => 1) j) 4) =
    C_gaussianBumpDecay 1 4 * C_gaussianBumpDecay 1 4
  rw [Fin.prod_univ_two]
  norm_num

set_option maxHeartbeats 2000000 in
private theorem aux_atomicOne_extendMiddle_prod (x : Fin (OrderedFinpartition.atomic 1).length) :
    (∏ j, C_gaussianBumpDecay
      (((OrderedFinpartition.atomic 1).extendMiddle x).partSize j) 4) =
      C_gaussianBumpDecay 2 4 := by
  change Fin 1 at x
  have hx : x = 0 := Fin.eq_zero x
  subst x
  change (∏ j : Fin 1, C_gaussianBumpDecay
    (Function.update (fun _ : Fin 1 => 1) 0 (1 + 1) j) 4) =
    C_gaussianBumpDecay 2 4
  rw [Fin.prod_univ_one]
  norm_num

private theorem aux_C_gaussianBumpDecay_one_four_le :
    C_gaussianBumpDecay 1 4 ≤ 3600 := by
  have hpow20 : Real.rpow 20 2 = 400 := by
    norm_num [Real.rpow_natCast]
  have hsqrt : Real.sqrt 76 ≤ 9 := by
    have hsquare : (Real.sqrt 76) ^ 2 = 76 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (76 : ℝ)]
  unfold C_gaussianBumpDecay
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  change Real.rpow 76 (1 / 2 : ℝ) * Real.rpow 20 2 ≤ 3600
  rw [show Real.rpow 76 (1 / 2 : ℝ) = Real.sqrt 76 by
    exact (Real.sqrt_eq_rpow 76).symm, hpow20]
  nlinarith

private theorem aux_C_gaussianBumpDecay_two_four_eq :
    C_gaussianBumpDecay 2 4 = 45600 := by
  unfold C_gaussianBumpDecay
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  change Real.rpow 114 1 * Real.rpow 20 2 = 45600
  norm_num [Real.rpow_natCast]

private theorem aux_N2_left_term_le :
    C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft).length *
        ∏ j, C_gaussianBumpDecay
          ((OrderedFinpartition.atomic 1).extendLeft.partSize j) 4 ≤
      54 * 3600 * 3600 := by
  have hderiv : C_derivativeEstimateForG 2 ≤ 54 := by
    calc
      C_derivativeEstimateForG 2 ≤ ((2 : ℕ).factorial : ℝ) * (3 : ℝ) ^ (2 + 1) :=
        aux_C_derivativeEstimateForG_le 2
      _ = 54 := by norm_num
  have hterm_eq :
      C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft).length *
          ∏ j, C_gaussianBumpDecay
            ((OrderedFinpartition.atomic 1).extendLeft.partSize j) 4 =
        C_derivativeEstimateForG 2 *
          (C_gaussianBumpDecay 1 4 * C_gaussianBumpDecay 1 4) := by
    rw [aux_atomicOne_extendLeft_prod]
    simp [OrderedFinpartition.extendLeft_length, OrderedFinpartition.atomic_length]
  rw [hterm_eq]
  calc
    C_derivativeEstimateForG 2 *
        (C_gaussianBumpDecay 1 4 * C_gaussianBumpDecay 1 4) ≤
      54 * (3600 * 3600) := by
        apply mul_le_mul
        · exact hderiv
        · exact mul_le_mul aux_C_gaussianBumpDecay_one_four_le
            aux_C_gaussianBumpDecay_one_four_le
            (aux_C_gaussianBumpDecay_nonneg 1 4) (by norm_num)
        · exact mul_nonneg (aux_C_gaussianBumpDecay_nonneg 1 4)
            (aux_C_gaussianBumpDecay_nonneg 1 4)
        · positivity
    _ = 54 * 3600 * 3600 := by ring

private theorem aux_N2_right_term_le (x : Fin (OrderedFinpartition.atomic 1).length) :
    C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendMiddle x).length *
        (∏ j, C_gaussianBumpDecay
          (((OrderedFinpartition.atomic 1).extendMiddle x).partSize j) 4) ≤
      9 * 45600 := by
  have hderiv : C_derivativeEstimateForG 1 ≤ 9 := by
    calc
      C_derivativeEstimateForG 1 ≤ ((1 : ℕ).factorial : ℝ) * (3 : ℝ) ^ (1 + 1) :=
        aux_C_derivativeEstimateForG_le 1
      _ = 9 := by norm_num
  have hterm_eq :
      C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendMiddle x).length *
          (∏ j, C_gaussianBumpDecay
            (((OrderedFinpartition.atomic 1).extendMiddle x).partSize j) 4) =
        C_derivativeEstimateForG 1 * C_gaussianBumpDecay 2 4 := by
    rw [aux_atomicOne_extendMiddle_prod x]
    simp [OrderedFinpartition.extendMiddle_length, OrderedFinpartition.atomic_length]
  rw [hterm_eq, aux_C_gaussianBumpDecay_two_four_eq]
  exact mul_le_mul_of_nonneg_right hderiv (by norm_num)

private theorem aux_N2_raw_right_term_le (x : Fin (OrderedFinpartition.atomic 1).length) :
    let summand : OrderedFinpartition 2 → ℝ := fun c =>
      C_derivativeEstimateForG c.length *
        (∏ j, C_gaussianBumpDecay (c.partSize j) 4)
    summand ((OrderedFinpartition.extendEquiv 1)
      ⟨OrderedFinpartition.atomic 1, some x⟩) ≤ 9 * 45600 := by
  let summand : OrderedFinpartition 2 → ℝ := fun c =>
    C_derivativeEstimateForG c.length *
      (∏ j, C_gaussianBumpDecay (c.partSize j) 4)
  change summand ((OrderedFinpartition.extendEquiv 1)
    ⟨OrderedFinpartition.atomic 1, some x⟩) ≤ 9 * 45600
  have summand_congr {c d : OrderedFinpartition 2} (h : c = d) :
      summand c = summand d := by
    subst d
    rfl
  have heq :
      (OrderedFinpartition.extendEquiv 1)
          ⟨OrderedFinpartition.atomic 1, some x⟩ =
        (OrderedFinpartition.atomic 1).extendMiddle x := by
    rw [OrderedFinpartition.extendEquiv_apply, OrderedFinpartition.extend_some]
  calc
    summand ((OrderedFinpartition.extendEquiv 1)
        ⟨OrderedFinpartition.atomic 1, some x⟩) =
      summand ((OrderedFinpartition.atomic 1).extendMiddle x) := summand_congr heq
    _ ≤ 9 * 45600 := by
      dsimp [summand]
      exact aux_N2_right_term_le x

private theorem aux_N2_raw_left_term_le :
    let summand : OrderedFinpartition 2 → ℝ := fun c =>
      C_derivativeEstimateForG c.length *
        (∏ j, C_gaussianBumpDecay (c.partSize j) 4)
    summand ((OrderedFinpartition.extendEquiv 1)
      ⟨OrderedFinpartition.atomic 1, none⟩) ≤ 54 * 3600 * 3600 := by
  let summand : OrderedFinpartition 2 → ℝ := fun c =>
    C_derivativeEstimateForG c.length *
      (∏ j, C_gaussianBumpDecay (c.partSize j) 4)
  change summand ((OrderedFinpartition.extendEquiv 1)
    ⟨OrderedFinpartition.atomic 1, none⟩) ≤ 54 * 3600 * 3600
  have summand_congr {c d : OrderedFinpartition 2} (h : c = d) :
      summand c = summand d := by
    subst d
    rfl
  have heq :
      (OrderedFinpartition.extendEquiv 1)
          ⟨OrderedFinpartition.atomic 1, none⟩ =
        (OrderedFinpartition.atomic 1).extendLeft := by
    rw [OrderedFinpartition.extendEquiv_apply, OrderedFinpartition.extend_none]
  calc
    summand ((OrderedFinpartition.extendEquiv 1)
        ⟨OrderedFinpartition.atomic 1, none⟩) =
      summand ((OrderedFinpartition.atomic 1).extendLeft) := summand_congr heq
    _ ≤ 54 * 3600 * 3600 := by
      dsimp [summand]
      exact aux_N2_left_term_le

private theorem aux_C_faaDiBruno_two_sum_bound :
    ∑ c : OrderedFinpartition 2,
      C_derivativeEstimateForG c.length *
        (∏ j, C_gaussianBumpDecay (c.partSize j) 4) ≤
      54 * 3600 * 3600 + 9 * 45600 := by
  let summand : OrderedFinpartition 2 → ℝ := fun c =>
    C_derivativeEstimateForG c.length *
      (∏ j, C_gaussianBumpDecay (c.partSize j) 4)
  change (∑ c : OrderedFinpartition 2, summand c) ≤
    54 * 3600 * 3600 + 9 * 45600
  have hleft : summand ((OrderedFinpartition.extendEquiv 1)
      ⟨OrderedFinpartition.atomic 1, none⟩) ≤ 54 * 3600 * 3600 := by
    exact aux_N2_raw_left_term_le
  have hright (x : Fin (OrderedFinpartition.atomic 1).length) :
      summand ((OrderedFinpartition.extendEquiv 1)
        ⟨OrderedFinpartition.atomic 1, some x⟩) ≤ 9 * 45600 := by
    exact aux_N2_raw_right_term_le x
  have hsumright :
      ∑ x : Fin (OrderedFinpartition.atomic 1).length,
        summand ((OrderedFinpartition.extendEquiv 1)
          ⟨OrderedFinpartition.atomic 1, some x⟩) ≤ 9 * 45600 := by
    simpa [nsmul_eq_mul, OrderedFinpartition.atomic_length] using
      (Finset.sum_le_card_nsmul
        (Finset.univ : Finset (Fin (OrderedFinpartition.atomic 1).length))
        (fun x => summand ((OrderedFinpartition.extendEquiv 1)
          ⟨OrderedFinpartition.atomic 1, some x⟩))
        (9 * 45600) (by
          intro x _
          exact hright x))
  rw [← (OrderedFinpartition.extendEquiv 1).sum_comp]
  simp only [Fintype.sum_sigma, Fintype.sum_unique, OrderedFinpartition.default_eq,
    Fintype.sum_option]
  exact add_le_add hleft hsumright

theorem aux_C_faaDiBruno_two_lt : C_faaDiBruno 2 < 8852889600 := by
  rw [C_faaDiBruno, if_neg (by norm_num)]
  calc
    (2 : ℝ) ^ (2 + 1) *
        ∑ c : OrderedFinpartition 2,
          C_derivativeEstimateForG c.length *
            (∏ j, C_gaussianBumpDecay (c.partSize j) (2 + 2)) ≤
      8 * (54 * 3600 * 3600 + 9 * 45600) := by
        calc
          (2 : ℝ) ^ (2 + 1) *
              ∑ c : OrderedFinpartition 2,
                C_derivativeEstimateForG c.length *
                  (∏ j, C_gaussianBumpDecay (c.partSize j) (2 + 2)) =
            8 * ∑ c : OrderedFinpartition 2,
              C_derivativeEstimateForG c.length *
                (∏ j, C_gaussianBumpDecay (c.partSize j) 4) := by norm_num
          _ ≤ 8 * (54 * 3600 * 3600 + 9 * 45600) :=
            mul_le_mul_of_nonneg_left aux_C_faaDiBruno_two_sum_bound (by norm_num)
    _ = 5602003200 := by norm_num
    _ < 8852889600 := by norm_num

private theorem aux_sqrt_twentyFour_le_five : Real.sqrt 24 ≤ 5 := by
  have hsquare : (Real.sqrt 24) ^ 2 = 24 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (24 : ℝ)]

private theorem aux_rpow_twentyFour_five_halves_le :
    Real.rpow 24 (5 / 2 : ℝ) ≤ 2880 := by
  calc
    Real.rpow 24 (5 / 2 : ℝ) = Real.rpow 24 (1 / 2 + 2 : ℝ) := by
      congr 1
      norm_num
    _ = Real.rpow 24 (1 / 2 : ℝ) * (24 : ℝ) ^ 2 := by
      exact Real.rpow_add_natCast (by norm_num) _ _
    _ = Real.sqrt 24 * 576 := by
      rw [show Real.rpow 24 (1 / 2 : ℝ) = Real.sqrt 24 by
        exact (Real.sqrt_eq_rpow 24).symm]
      norm_num
    _ ≤ 5 * 576 := by
      exact mul_le_mul_of_nonneg_right aux_sqrt_twentyFour_le_five (by norm_num)
    _ = 2880 := by norm_num

private theorem aux_C_gaussianBumpDecay_one_five_le :
    C_gaussianBumpDecay 1 5 ≤ 25920 := by
  have hsqrt : Real.sqrt 76 ≤ 9 := by
    have hsquare : (Real.sqrt 76) ^ 2 = 76 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (76 : ℝ)]
  unfold C_gaussianBumpDecay
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  change Real.rpow 76 (1 / 2 : ℝ) * Real.rpow 24 (5 / 2 : ℝ) ≤ 25920
  rw [show Real.rpow 76 (1 / 2 : ℝ) = Real.sqrt 76 by
    exact (Real.sqrt_eq_rpow 76).symm]
  calc
    Real.sqrt 76 * Real.rpow 24 (5 / 2 : ℝ) ≤ 9 * 2880 := by
      exact mul_le_mul hsqrt aux_rpow_twentyFour_five_halves_le
        (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    _ = 25920 := by norm_num

private theorem aux_C_gaussianBumpDecay_two_five_le :
    C_gaussianBumpDecay 2 5 ≤ 328320 := by
  unfold C_gaussianBumpDecay
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  change Real.rpow 114 1 * Real.rpow 24 (5 / 2 : ℝ) ≤ 328320
  rw [show Real.rpow 114 1 = 114 by norm_num [Real.rpow_one]]
  calc
    114 * Real.rpow 24 (5 / 2 : ℝ) ≤ 114 * 2880 := by
      exact mul_le_mul_of_nonneg_left aux_rpow_twentyFour_five_halves_le (by norm_num)
    _ = 328320 := by norm_num

private theorem aux_C_gaussianBumpDecay_three_five_le :
    C_gaussianBumpDecay 3 5 ≤ 5690880 := by
  have hsqrt : Real.sqrt 152 ≤ 13 := by
    have hsquare : (Real.sqrt 152) ^ 2 = 152 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (152 : ℝ)]
  have hpow : Real.rpow 152 (3 / 2 : ℝ) ≤ 1976 := by
    calc
      Real.rpow 152 (3 / 2 : ℝ) = Real.rpow 152 (1 / 2 + 1 : ℝ) := by
        congr 1
        norm_num
      _ = Real.rpow 152 (1 / 2 : ℝ) * (152 : ℝ) := by
        exact Real.rpow_add_one (by norm_num) _
      _ = Real.sqrt 152 * 152 := by
        rw [show Real.rpow 152 (1 / 2 : ℝ) = Real.sqrt 152 by
          exact (Real.sqrt_eq_rpow 152).symm]
      _ ≤ 13 * 152 := by gcongr
      _ = 1976 := by norm_num
  unfold C_gaussianBumpDecay
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  change Real.rpow 152 (3 / 2 : ℝ) * Real.rpow 24 (5 / 2 : ℝ) ≤ 5690880
  calc
    Real.rpow 152 (3 / 2 : ℝ) * Real.rpow 24 (5 / 2 : ℝ) ≤ 1976 * 2880 := by
      exact mul_le_mul hpow aux_rpow_twentyFour_five_halves_le
        (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    _ = 5690880 := by norm_num

private def aux_faaAtomicOneIndex : Fin (OrderedFinpartition.atomic 1).length :=
  ⟨0, by change 0 < 1; norm_num⟩

private def aux_faaAtomicOneMiddleIndex :
    Fin ((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).length :=
  ⟨0, by
    rw [OrderedFinpartition.extendMiddle_length,
      OrderedFinpartition.atomic_length]
    norm_num⟩

set_option maxHeartbeats 2000000 in
private theorem aux_N3_111_prod :
    (∏ j, C_gaussianBumpDecay
      ((OrderedFinpartition.atomic 1).extendLeft.extendLeft.partSize j) 5) =
      C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 1 5 := by
  change (∏ _ : Fin 3, C_gaussianBumpDecay 1 5) =
    C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 1 5
  simp
  ring

set_option maxHeartbeats 2000000 in
private theorem aux_N3_11_middle_prod_bound
    (x : Fin ((OrderedFinpartition.atomic 1).extendLeft).length) :
    (∏ j, C_gaussianBumpDecay
      (((OrderedFinpartition.atomic 1).extendLeft.extendMiddle x).partSize j) 5) ≤
      328320 * 25920 := by
  change Fin 2 at x
  fin_cases x
  · change (∏ j : Fin 2, C_gaussianBumpDecay
      (Function.update
        (Fin.cons (α := fun _ : Fin 2 => ℕ) 1 (fun _ : Fin 1 => 1))
        0 (1 + 1) j) 5) ≤ 328320 * 25920
    rw [Fin.prod_univ_two]
    change C_gaussianBumpDecay 2 5 * C_gaussianBumpDecay 1 5 ≤ 328320 * 25920
    exact mul_le_mul aux_C_gaussianBumpDecay_two_five_le
      aux_C_gaussianBumpDecay_one_five_le
      (aux_C_gaussianBumpDecay_nonneg 1 5) (by norm_num)
  · change (∏ j : Fin 2, C_gaussianBumpDecay
      (Function.update
        (Fin.cons (α := fun _ : Fin 2 => ℕ) 1 (fun _ : Fin 1 => 1))
        1 (1 + 1) j) 5) ≤ 328320 * 25920
    rw [Fin.prod_univ_two]
    change C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 2 5 ≤ 328320 * 25920
    simpa [mul_comm] using
      (mul_le_mul aux_C_gaussianBumpDecay_two_five_le
        aux_C_gaussianBumpDecay_one_five_le
        (aux_C_gaussianBumpDecay_nonneg 1 5) (by norm_num))

set_option maxHeartbeats 2000000 in
private theorem aux_N3_middle_left_prod :
    (∏ j, C_gaussianBumpDecay
      (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft.partSize j) 5) =
      C_gaussianBumpDecay 2 5 * C_gaussianBumpDecay 1 5 := by
  unfold aux_faaAtomicOneIndex
  change (∏ j : Fin 2,
    C_gaussianBumpDecay ((Fin.cons 1 (fun _ : Fin 1 => 2) : Fin 2 → ℕ) j) 5) = _
  rw [Fin.prod_univ_two]
  norm_num
  ring

set_option maxHeartbeats 2000000 in
private theorem aux_N3_middle_middle_prod :
    (∏ j, C_gaussianBumpDecay
      (((((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
        aux_faaAtomicOneMiddleIndex).partSize j)) 5) =
      C_gaussianBumpDecay 3 5 := by
  unfold aux_faaAtomicOneIndex aux_faaAtomicOneMiddleIndex
  change (∏ j : Fin 1,
    C_gaussianBumpDecay (Function.update (fun _ : Fin 1 => 2) 0 (2 + 1) j) 5) = _
  rw [Fin.prod_univ_one]
  norm_num

set_option maxHeartbeats 2000000 in
private theorem aux_faaAtomicOne_extendLeft_sum_middle (F : OrderedFinpartition 3 → ℝ) :
    (∑ x : Fin (OrderedFinpartition.atomic 1).extendLeft.length,
      F ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle x)) =
      F ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle (0 : Fin 2)) +
        F ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle (1 : Fin 2)) := by
  change (∑ x : Fin 2,
    F ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle x)) = _
  rw [Fin.sum_univ_two]

set_option maxHeartbeats 2000000 in
private theorem aux_faaAtomicOne_sum_branches (F : OrderedFinpartition 3 → ℝ) :
    (∑ x : Fin (OrderedFinpartition.atomic 1).length,
      (F ((OrderedFinpartition.atomic 1).extendMiddle x).extendLeft +
        ∑ x_1 : Fin ((OrderedFinpartition.atomic 1).extendMiddle x).length,
          F (((OrderedFinpartition.atomic 1).extendMiddle x).extendMiddle x_1))) =
      F (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft) +
        F (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
          aux_faaAtomicOneMiddleIndex) := by
  letI : Unique (Fin (OrderedFinpartition.atomic 1).length) := by
    change Unique (Fin 1)
    infer_instance
  rw [Fintype.sum_unique]
  have hdefault : (default : Fin (OrderedFinpartition.atomic 1).length) =
      aux_faaAtomicOneIndex := Subsingleton.elim _ _
  rw [hdefault]
  letI : Unique (Fin ((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).length) := by
    change Unique (Fin 1)
    infer_instance
  rw [Fintype.sum_unique]
  have hdefault' :
      (default : Fin ((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).length) =
        aux_faaAtomicOneMiddleIndex := Subsingleton.elim _ _
  rw [hdefault']

private theorem aux_sum_orderedFinpartition_three (F : OrderedFinpartition 3 → ℝ) :
    (∑ c : OrderedFinpartition 3, F c) =
      F (OrderedFinpartition.atomic 1).extendLeft.extendLeft +
        F ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle (0 : Fin 2)) +
          F ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle (1 : Fin 2)) +
            F (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft) +
              F (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
                aux_faaAtomicOneMiddleIndex) := by
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp,
    ← (OrderedFinpartition.extendEquiv 2).sum_comp, Fintype.sum_sigma,
    Fintype.sum_option, Nat.reduceAdd, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    OrderedFinpartition.extendMiddle_length, OrderedFinpartition.default_eq,
    Fintype.sum_unique, OrderedFinpartition.atomic_length,
    OrderedFinpartition.extendLeft_length, Fin.sum_univ_two]
  have sum_middle_congr {c d : OrderedFinpartition 2} (h : c = d) :
      (∑ x : Fin c.length, F (c.extendMiddle x)) =
        ∑ x : Fin d.length, F (d.extendMiddle x) := by
    subst d
    rfl
  have hnone :
      (OrderedFinpartition.extendEquiv 1)
        ⟨OrderedFinpartition.atomic 1, none⟩ =
      (OrderedFinpartition.atomic 1).extendLeft := by
    rw [OrderedFinpartition.extendEquiv_apply,
      OrderedFinpartition.extend_none]
  rw [sum_middle_congr hnone]
  have hsome (x : Fin (OrderedFinpartition.atomic 1).length) :
      (OrderedFinpartition.extendEquiv 1)
        ⟨OrderedFinpartition.atomic 1, some x⟩ =
      (OrderedFinpartition.atomic 1).extendMiddle x := by
    rw [OrderedFinpartition.extendEquiv_apply,
      OrderedFinpartition.extend_some]
  have hright (x : Fin (OrderedFinpartition.atomic 1).length) :
      (∑ x_1 : Fin
          ((OrderedFinpartition.extendEquiv 1)
            ⟨OrderedFinpartition.atomic 1, some x⟩).length,
        F (((OrderedFinpartition.extendEquiv 1)
          ⟨OrderedFinpartition.atomic 1, some x⟩).extendMiddle x_1)) =
        ∑ x_1 : Fin ((OrderedFinpartition.atomic 1).extendMiddle x).length,
          F (((OrderedFinpartition.atomic 1).extendMiddle x).extendMiddle x_1) :=
    sum_middle_congr (hsome x)
  simp_rw [hright]
  rw [aux_faaAtomicOne_extendLeft_sum_middle F, aux_faaAtomicOne_sum_branches F]
  ring

private theorem aux_C_derivativeEstimateForG_one_le_nine :
    C_derivativeEstimateForG 1 ≤ 9 := by
  calc
    C_derivativeEstimateForG 1 ≤ ((1 : ℕ).factorial : ℝ) * (3 : ℝ) ^ (1 + 1) :=
      aux_C_derivativeEstimateForG_le 1
    _ = 9 := by norm_num

private theorem aux_C_derivativeEstimateForG_two_le_fiftyFour :
    C_derivativeEstimateForG 2 ≤ 54 := by
  calc
    C_derivativeEstimateForG 2 ≤ ((2 : ℕ).factorial : ℝ) * (3 : ℝ) ^ (2 + 1) :=
      aux_C_derivativeEstimateForG_le 2
    _ = 54 := by norm_num

private theorem aux_C_derivativeEstimateForG_three_le_fourHundredEightySix :
    C_derivativeEstimateForG 3 ≤ 486 := by
  calc
    C_derivativeEstimateForG 3 ≤ ((3 : ℕ).factorial : ℝ) * (3 : ℝ) ^ (3 + 1) :=
      aux_C_derivativeEstimateForG_le 3
    _ = 486 := by norm_num

private theorem aux_N3_one_cube_bound :
    C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 1 5 ≤
      25920 * 25920 * 25920 := by
  have hnonneg : 0 ≤ C_gaussianBumpDecay 1 5 :=
    aux_C_gaussianBumpDecay_nonneg 1 5
  have hpair : C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 1 5 ≤ 25920 * 25920 :=
    mul_le_mul aux_C_gaussianBumpDecay_one_five_le
      aux_C_gaussianBumpDecay_one_five_le hnonneg (by norm_num)
  exact mul_le_mul hpair aux_C_gaussianBumpDecay_one_five_le hnonneg (by norm_num)

private theorem aux_N3_two_one_bound :
    C_gaussianBumpDecay 2 5 * C_gaussianBumpDecay 1 5 ≤ 328320 * 25920 := by
  exact mul_le_mul aux_C_gaussianBumpDecay_two_five_le
    aux_C_gaussianBumpDecay_one_five_le
    (aux_C_gaussianBumpDecay_nonneg 1 5) (by norm_num)

private theorem aux_N3_111_term_le :
    C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft.extendLeft).length *
        (∏ j, C_gaussianBumpDecay
          ((OrderedFinpartition.atomic 1).extendLeft.extendLeft.partSize j) 5) ≤
      8463329722368000 := by
  calc
    C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft.extendLeft).length *
        (∏ j, C_gaussianBumpDecay
          ((OrderedFinpartition.atomic 1).extendLeft.extendLeft.partSize j) 5) =
        C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft.extendLeft).length *
          (C_gaussianBumpDecay 1 5 * C_gaussianBumpDecay 1 5 *
            C_gaussianBumpDecay 1 5) := by rw [aux_N3_111_prod]
    _ ≤ C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft.extendLeft).length *
          (25920 * 25920 * 25920) :=
      mul_le_mul_of_nonneg_left aux_N3_one_cube_bound
        (aux_C_derivativeEstimateForG_nonneg _)
    _ = C_derivativeEstimateForG 3 * (25920 * 25920 * 25920) := by
      simp [OrderedFinpartition.extendLeft_length, OrderedFinpartition.atomic_length]
    _ ≤ 486 * (25920 * 25920 * 25920) :=
      mul_le_mul_of_nonneg_right aux_C_derivativeEstimateForG_three_le_fourHundredEightySix
        (by norm_num)
    _ = 8463329722368000 := by norm_num

private theorem aux_N3_11_middle_term_le
    (x : Fin ((OrderedFinpartition.atomic 1).extendLeft).length) :
    C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle x).length *
        (∏ j, C_gaussianBumpDecay
          (((OrderedFinpartition.atomic 1).extendLeft.extendMiddle x).partSize j) 5) ≤
      459542937600 := by
  calc
    C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle x).length *
        (∏ j, C_gaussianBumpDecay
          (((OrderedFinpartition.atomic 1).extendLeft.extendMiddle x).partSize j) 5) ≤
        C_derivativeEstimateForG ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle x).length *
          (328320 * 25920) :=
      mul_le_mul_of_nonneg_left (aux_N3_11_middle_prod_bound x)
        (aux_C_derivativeEstimateForG_nonneg _)
    _ = C_derivativeEstimateForG 2 * (328320 * 25920) := by
      simp [OrderedFinpartition.extendMiddle_length, OrderedFinpartition.extendLeft_length,
        OrderedFinpartition.atomic_length]
    _ ≤ 54 * (328320 * 25920) :=
      mul_le_mul_of_nonneg_right aux_C_derivativeEstimateForG_two_le_fiftyFour (by norm_num)
    _ = 459542937600 := by norm_num

private theorem aux_N3_middle_left_term_le :
    C_derivativeEstimateForG
        (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft).length *
        (∏ j, C_gaussianBumpDecay
          ((((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft).partSize j) 5) ≤
      459542937600 := by
  calc
    C_derivativeEstimateForG
        (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft).length *
        (∏ j, C_gaussianBumpDecay
          ((((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft).partSize j) 5) =
        C_derivativeEstimateForG
          (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft).length *
          (C_gaussianBumpDecay 2 5 * C_gaussianBumpDecay 1 5) := by
      rw [aux_N3_middle_left_prod]
    _ ≤ C_derivativeEstimateForG
          (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft).length *
          (328320 * 25920) :=
      mul_le_mul_of_nonneg_left aux_N3_two_one_bound
        (aux_C_derivativeEstimateForG_nonneg _)
    _ = C_derivativeEstimateForG 2 * (328320 * 25920) := by
      simp [OrderedFinpartition.extendLeft_length, OrderedFinpartition.extendMiddle_length,
        OrderedFinpartition.atomic_length]
    _ ≤ 54 * (328320 * 25920) :=
      mul_le_mul_of_nonneg_right aux_C_derivativeEstimateForG_two_le_fiftyFour (by norm_num)
    _ = 459542937600 := by norm_num

private theorem aux_N3_middle_middle_term_le :
    C_derivativeEstimateForG
        (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
          aux_faaAtomicOneMiddleIndex).length *
        (∏ j, C_gaussianBumpDecay
          (((((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
            aux_faaAtomicOneMiddleIndex).partSize j)) 5) ≤
      51217920 := by
  calc
    C_derivativeEstimateForG
        (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
          aux_faaAtomicOneMiddleIndex).length *
        (∏ j, C_gaussianBumpDecay
          (((((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
            aux_faaAtomicOneMiddleIndex).partSize j)) 5) =
        C_derivativeEstimateForG
          (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
            aux_faaAtomicOneMiddleIndex).length * C_gaussianBumpDecay 3 5 := by
      rw [aux_N3_middle_middle_prod]
    _ ≤ C_derivativeEstimateForG
          (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
            aux_faaAtomicOneMiddleIndex).length * 5690880 :=
      mul_le_mul_of_nonneg_left aux_C_gaussianBumpDecay_three_five_le
        (aux_C_derivativeEstimateForG_nonneg _)
    _ = C_derivativeEstimateForG 1 * 5690880 := by
      simp [OrderedFinpartition.extendMiddle_length, OrderedFinpartition.atomic_length]
    _ ≤ 9 * 5690880 :=
      mul_le_mul_of_nonneg_right aux_C_derivativeEstimateForG_one_le_nine (by norm_num)
    _ = 51217920 := by norm_num

private theorem aux_C_faaDiBruno_three_sum_bound :
    (∑ c : OrderedFinpartition 3,
      C_derivativeEstimateForG c.length *
        (∏ j, C_gaussianBumpDecay (c.partSize j) 5)) ≤
      8464708402398720 := by
  let summand : OrderedFinpartition 3 → ℝ := fun c =>
    C_derivativeEstimateForG c.length *
      (∏ j, C_gaussianBumpDecay (c.partSize j) 5)
  change (∑ c : OrderedFinpartition 3, summand c) ≤ 8464708402398720
  rw [aux_sum_orderedFinpartition_three summand]
  exact calc
    summand ((OrderedFinpartition.atomic 1).extendLeft.extendLeft) +
        summand ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle (0 : Fin 2)) +
          summand ((OrderedFinpartition.atomic 1).extendLeft.extendMiddle (1 : Fin 2)) +
            summand (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendLeft) +
              summand (((OrderedFinpartition.atomic 1).extendMiddle aux_faaAtomicOneIndex).extendMiddle
                aux_faaAtomicOneMiddleIndex) ≤
      8463329722368000 + 459542937600 + 459542937600 + 459542937600 + 51217920 := by
        dsimp [summand]
        exact add_le_add
          (add_le_add
            (add_le_add
              (add_le_add aux_N3_111_term_le
                (aux_N3_11_middle_term_le (0 : Fin 2)))
              (aux_N3_11_middle_term_le (1 : Fin 2)))
            aux_N3_middle_left_term_le)
          aux_N3_middle_middle_term_le
    _ = 8464708402398720 := by norm_num

theorem aux_C_faaDiBruno_three_lt :
    C_faaDiBruno 3 < 255689986286813184 := by
  rw [C_faaDiBruno, if_neg (by norm_num)]
  calc
    (2 : ℝ) ^ (3 + 1) *
        ∑ c : OrderedFinpartition 3,
          C_derivativeEstimateForG c.length *
            (∏ j, C_gaussianBumpDecay (c.partSize j) (3 + 2)) =
        16 *
          ∑ c : OrderedFinpartition 3,
            C_derivativeEstimateForG c.length *
              (∏ j, C_gaussianBumpDecay (c.partSize j) 5) := by norm_num
    _ ≤ 16 * 8464708402398720 :=
      mul_le_mul_of_nonneg_left aux_C_faaDiBruno_three_sum_bound (by norm_num)
    _ = 135435334438379520 := by norm_num
    _ < 255689986286813184 := by norm_num

theorem constantFaaDiBruno (N : ℕ) :
    C_faaDiBruno N ≤ (2 : ℝ) ^ (10 * (N + 1) ^ 3) ∧
      C_faaDiBruno 0 ≤ 72 ∧ C_faaDiBruno 1 < (2 : ℝ) ^ 15 ∧
        C_faaDiBruno 2 < (2 : ℝ) ^ 34 ∧ C_faaDiBruno 3 < (2 : ℝ) ^ 58 := by
  refine ⟨aux_C_faaDiBruno_bound N, aux_C_faaDiBruno_zero_le, ?_, ?_, ?_⟩
  · calc
      C_faaDiBruno 1 < 27648 := aux_C_faaDiBruno_one_lt
      _ < (2 : ℝ) ^ 15 := by norm_num
  · calc
      C_faaDiBruno 2 < 8852889600 := aux_C_faaDiBruno_two_lt
      _ < (2 : ℝ) ^ 34 := by norm_num
  · calc
      C_faaDiBruno 3 < 255689986286813184 := aux_C_faaDiBruno_three_lt
      _ < (2 : ℝ) ^ 58 := by norm_num

/-- Source label `\ref{L:second-gaussian-estimate}`; the explicit constant used by the public
theorem `secondGaussianEstimate`. -/
noncomputable def C_secondGaussianEstimate (N : ℕ) : ℝ :=
  8 * ∑ l ∈ Finset.range (N + 1),
    (Nat.choose N l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
      C_gaussianBumpEstimate l * C_faaDiBruno (N - l)

/-- Source definition `\ref{auto:second-Gaussian-multiplier}`. -/
def aux_secondGaussianQ (phiHat : ℝ → ℂ) (mu lambda : ℝ) : ℝ → ℂ := fun xi =>
  (((Gaussians.gaussian (mu * xi))⁻¹ : ℝ) : ℂ) *
    (phiHat (lambda * xi) - phiHat xi)

/-- Source definition `\ref{auto:second-Gaussian-multiplier}`. -/
def aux_secondGaussianS (t nu : ℝ) : ℝ → ℂ := fun xi =>
  (((1 - Gaussians.gaussian (t * xi)) ^ nu - 1 : ℝ) : ℂ)

/-- Source definition `\ref{auto:second-Gaussian-multiplier}`. -/
def secondGaussianMultiplier (phiHat : ℝ → ℂ) (mu lambda t nu : ℝ) : ℝ → ℂ :=
  aux_secondGaussianQ phiHat mu lambda * aux_secondGaussianS t nu

/-- For `\ref{L:second-gaussian-estimate}`, iterated derivatives commute with real-to-complex
coercion locally at points where the real function is sufficiently smooth. -/
theorem aux_secondGaussian_iteratedDeriv_ofReal_at (n : ℕ) (f : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ (n + 1) f x) :
    iteratedDeriv n (fun y : ℝ => (f y : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n generalizing f x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (fun y : ℝ => (f y : ℂ)) =ᶠ[nhds x]
          fun y : ℝ => ((iteratedDeriv n f y : ℝ) : ℂ) := by
        filter_upwards [hf.eventually (by simp)] with y hy
        exact ih f y (hy.of_le (by simp))
      rw [hfun.deriv_eq]
      have hdiff : DifferentiableAt ℝ (iteratedDeriv n f) x := by
        simpa only [iteratedDerivWithin_univ, differentiableWithinAt_univ] using
          hf.differentiableWithinAt_iteratedDerivWithin
            (by norm_cast; omega) (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ Set.univ))
      have hderiv : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
        rw [iteratedDeriv_succ]
        exact hdiff.hasDerivAt
      simpa using ((hasDerivAt_const x Complex.ofRealCLM).clm_apply hderiv).deriv

/-- For `\ref{L:second-gaussian-estimate}`, scaling an argument by a factor in `[0,1]`
does not enlarge the Fourier-normalized derivative norm. -/
theorem aux_secondGaussian_scaled_normalized_deriv_le (n : ℕ) (lambda : ℝ) (F : ℝ → ℂ) (x : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) (hF : ContDiff ℝ n F) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ n * ‖iteratedDeriv n (fun z : ℝ => F (lambda * z)) x‖ ≤
      ((2 * Real.pi)⁻¹ : ℝ) ^ n * ‖iteratedDeriv n F (lambda * x)‖ := by
  have hlpow0 : 0 ≤ lambda ^ n := pow_nonneg hlambda0 _
  have hlpow1 : lambda ^ n ≤ 1 := by simpa using pow_le_one₀ hlambda0 hlambda1
  have hq : 0 ≤ ((2 * Real.pi)⁻¹ : ℝ) ^ n := by positivity
  rw [show iteratedDeriv n (fun z : ℝ => F (lambda * z)) =
      fun z => lambda ^ n • iteratedDeriv n F (lambda * z) by
      exact iteratedDeriv_comp_const_smul hF lambda]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlpow0]
  have hinner : lambda ^ n * ‖iteratedDeriv n F (lambda * x)‖ ≤
      ‖iteratedDeriv n F (lambda * x)‖ :=
    mul_le_of_le_one_left (norm_nonneg _) hlpow1
  exact mul_le_mul_of_nonneg_left hinner hq

/-- For `\ref{L:second-gaussian-estimate}`, the first multiplier factor is a difference of
two Gaussian bump quotients. -/
theorem aux_secondGaussianQ_eq_gaussianBumpQuotients (phiHat : ℝ → ℂ) (mu lambda : ℝ)
    (hlambda : lambda ≠ 0) :
    aux_secondGaussianQ phiHat mu lambda =
      (fun xi : ℝ => gaussianBumpQuotient (mu / lambda) phiHat (lambda * xi)) -
        gaussianBumpQuotient mu phiHat := by
  funext xi
  simp only [aux_secondGaussianQ, gaussianBumpQuotient, Pi.sub_apply]
  have hscale : (mu / lambda) * (lambda * xi) = mu * xi := by
    field_simp
  rw [hscale]
  ring

/-- For `\ref{L:second-gaussian-estimate}`, the first multiplier factor has the required
finite smoothness. -/
theorem aux_secondGaussianQ_contDiff (N : ℕ) (phiHat : ℝ → ℂ) (mu lambda : ℝ)
    (hphi : ContDiff ℝ N phiHat) :
    ContDiff ℝ N (aux_secondGaussianQ phiHat mu lambda) := by
  change ContDiff ℝ N
    ((fun xi : ℝ => (((Gaussians.gaussian (mu * xi))⁻¹ : ℝ) : ℂ)) *
      (fun xi : ℝ => phiHat (lambda * xi) - phiHat xi))
  have hlin : ContDiff ℝ N (fun xi : ℝ => mu * xi) := by fun_prop
  have hinv : ContDiff ℝ N (fun xi : ℝ =>
      (((Gaussians.gaussian (mu * xi))⁻¹ : ℝ) : ℂ)) :=
    (aux_gaussianBumpEstimate_complexInverseGaussian_contDiff_at N).comp hlin
  have hscale : ContDiff ℝ N (fun xi : ℝ => phiHat (lambda * xi)) := by fun_prop
  exact hinv.mul (hscale.sub hphi)

/-- For `\ref{L:second-gaussian-estimate}`, the first multiplier factor satisfies the
Fourier-normalized Gaussian-bump estimate. -/
theorem aux_secondGaussianQ_normalized_bound (N l : ℕ) (c : ℝ) (phiHat : ℝ → ℂ)
    (mu lambda : ℝ) (hc : 0 ≤ c) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (hl : l ≤ N) (xi : ℝ) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ l * ‖iteratedDeriv l (aux_secondGaussianQ phiHat mu lambda) xi‖ ≤
      2 * c * C_gaussianBumpEstimate l := by
  let A : ℝ → ℂ := fun x => gaussianBumpQuotient (mu / lambda) phiHat (lambda * x)
  let B : ℝ → ℂ := gaussianBumpQuotient mu phiHat
  have hlambdaPos : 0 < lambda := hmu.trans_le hmulambda
  have hlambda0 : 0 ≤ lambda := hlambdaPos.le
  have hlambda1 : lambda ≤ 1 := by linarith
  have hmuDiv0 : 0 ≤ mu / lambda := div_nonneg hmu.le hlambda0
  have hmuDiv1 : mu / lambda ≤ 1 := by
    rw [div_le_iff₀ hlambdaPos]
    simpa using hmulambda
  have hphi_l : ContDiff ℝ l phiHat := hphi.of_le (by exact_mod_cast hl)
  have hphiBound_l : ∀ m : ℕ, m ≤ l → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c := by
    intro m hm xi
    exact hphiBound m (hm.trans hl) xi
  have hAcont : ContDiff ℝ l A := by
    dsimp [A]
    have hlin : ContDiff ℝ l (fun x : ℝ => lambda * x) := by fun_prop
    exact (aux_gaussianBumpEstimate_contDiff l (mu / lambda) phiHat hphi_l).comp hlin
  have hBcont : ContDiff ℝ l B := by
    exact aux_gaussianBumpEstimate_contDiff l mu phiHat hphi_l
  have hApoint : ((2 * Real.pi)⁻¹ : ℝ) ^ l * ‖iteratedDeriv l A xi‖ ≤
      c * C_gaussianBumpEstimate l := by
    calc
      ((2 * Real.pi)⁻¹ : ℝ) ^ l * ‖iteratedDeriv l A xi‖ ≤
          ((2 * Real.pi)⁻¹ : ℝ) ^ l *
            ‖iteratedDeriv l (gaussianBumpQuotient (mu / lambda) phiHat) (lambda * xi)‖ := by
          simpa only [A] using aux_secondGaussian_scaled_normalized_deriv_le l lambda
            (gaussianBumpQuotient (mu / lambda) phiHat) xi hlambda0 hlambda1
            (aux_gaussianBumpEstimate_contDiff l (mu / lambda) phiHat hphi_l)
      _ ≤ c * C_gaussianBumpEstimate l :=
        aux_gaussianBumpEstimate_pointwise l c (mu / lambda) phiHat hc hmuDiv0 hmuDiv1
          hphi_l hsupp hphiBound_l (lambda * xi)
  have hBpoint : ((2 * Real.pi)⁻¹ : ℝ) ^ l * ‖iteratedDeriv l B xi‖ ≤
      c * C_gaussianBumpEstimate l := by
    exact aux_gaussianBumpEstimate_pointwise l c mu phiHat hc hmu.le
      (hmulambda.trans hlambda1) hphi_l hsupp hphiBound_l xi
  have hQeq : aux_secondGaussianQ phiHat mu lambda = A - B := by
    simpa only [A, B] using
      aux_secondGaussianQ_eq_gaussianBumpQuotients phiHat mu lambda hlambdaPos.ne'
  rw [hQeq, iteratedDeriv_sub hAcont.contDiffAt hBcont.contDiffAt]
  have hq : 0 ≤ ((2 * Real.pi)⁻¹ : ℝ) ^ l := by positivity
  calc
    ((2 * Real.pi)⁻¹ : ℝ) ^ l * ‖iteratedDeriv l A xi - iteratedDeriv l B xi‖ ≤
        ((2 * Real.pi)⁻¹ : ℝ) ^ l *
          (‖iteratedDeriv l A xi‖ + ‖iteratedDeriv l B xi‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hq
    _ = ((2 * Real.pi)⁻¹ : ℝ) ^ l * ‖iteratedDeriv l A xi‖ +
        ((2 * Real.pi)⁻¹ : ℝ) ^ l * ‖iteratedDeriv l B xi‖ := by ring
    _ ≤ c * C_gaussianBumpEstimate l + c * C_gaussianBumpEstimate l :=
      add_le_add hApoint hBpoint
    _ = 2 * c * C_gaussianBumpEstimate l := by ring

/-- For `\ref{L:second-gaussian-estimate}`, this removes the Fourier normalization from the
bound for the first multiplier factor. -/
theorem aux_secondGaussianQ_bound (N l : ℕ) (c : ℝ) (phiHat : ℝ → ℂ)
    (mu lambda : ℝ) (hc : 0 ≤ c) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (hl : l ≤ N) (xi : ℝ) :
    ‖iteratedDeriv l (aux_secondGaussianQ phiHat mu lambda) xi‖ ≤
      2 * c * (2 * Real.pi) ^ l * C_gaussianBumpEstimate l := by
  have hnorm := aux_secondGaussianQ_normalized_bound N l c phiHat mu lambda hc hmu hmulambda
    hlambda hphi hsupp hphiBound hl xi
  have hbase : 0 < 2 * Real.pi := by positivity
  have hpow : ((2 * Real.pi)⁻¹ : ℝ) ^ l * (2 * Real.pi) ^ l = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hbase.ne', one_pow]
  calc
    ‖iteratedDeriv l (aux_secondGaussianQ phiHat mu lambda) xi‖ =
        (1 : ℝ) * ‖iteratedDeriv l (aux_secondGaussianQ phiHat mu lambda) xi‖ := by ring
    _ = (((2 * Real.pi)⁻¹ : ℝ) ^ l * (2 * Real.pi) ^ l) *
        ‖iteratedDeriv l (aux_secondGaussianQ phiHat mu lambda) xi‖ := by rw [hpow]
    _ = (((2 * Real.pi)⁻¹ : ℝ) ^ l *
          ‖iteratedDeriv l (aux_secondGaussianQ phiHat mu lambda) xi‖) * (2 * Real.pi) ^ l := by
      ring
    _ ≤ (2 * c * C_gaussianBumpEstimate l) * (2 * Real.pi) ^ l :=
      mul_le_mul_of_nonneg_right hnorm (pow_nonneg hbase.le _)
    _ = 2 * c * (2 * Real.pi) ^ l * C_gaussianBumpEstimate l := by ring

/-- For `\ref{L:second-gaussian-estimate}`, the singular real factor is smooth away from the
origin. -/
theorem aux_secondGaussianS_real_contDiffAt (N : ℕ) (t nu x : ℝ)
    (ht : Real.sqrt 3 / 2 ≤ t) (hx : x ≠ 0) :
    ContDiffAt ℝ N (fun y : ℝ => (1 - Gaussians.gaussian (t * y)) ^ nu - 1) x := by
  have htpos : 0 < t := by
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    linarith
  have htx : t * x ≠ 0 := mul_ne_zero htpos.ne' hx
  have hgauss_lt : Gaussians.gaussian (t * x) < 1 := by
    have hneg : -Real.pi * (t * x) ^ 2 < 0 := by
      nlinarith [Real.pi_pos, sq_pos_of_ne_zero htx]
    simpa [Gaussians.gaussian, Notation.gaussian] using (Real.exp_lt_exp.mpr hneg)
  have hrad : 1 - Gaussians.gaussian (t * x) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hgauss_lt)
  have haff : ContDiffAt ℝ N (fun y : ℝ => 1 - Gaussians.gaussian (t * y)) x := by
    have hlin : ContDiff ℝ N (fun y : ℝ => t * y) := by fun_prop
    have hgauss : ContDiff ℝ N Gaussians.gaussian :=
      aux_gaussian_contDiff.of_le (by
        exact_mod_cast (show (N : ℕ∞) ≤ ⊤ by exact le_top))
    exact contDiffAt_const.sub (by
      simpa [Function.comp_def] using (hgauss.comp hlin).contDiffAt)
  have hrpow : ContDiffAt ℝ N (fun z : ℝ => z ^ nu)
      (1 - Gaussians.gaussian (t * x)) :=
    Real.contDiffAt_rpow_const_of_ne hrad
  exact (hrpow.comp x haff).sub contDiffAt_const

/-- For `\ref{L:second-gaussian-estimate}`, the complex singular factor is smooth away from
the origin. -/
theorem aux_secondGaussianS_contDiffAt (N : ℕ) (t nu x : ℝ)
    (ht : Real.sqrt 3 / 2 ≤ t) (hx : x ≠ 0) :
    ContDiffAt ℝ N (aux_secondGaussianS t nu) x := by
  have hreal := aux_secondGaussianS_real_contDiffAt N t nu x ht hx
  change ContDiffAt ℝ N
    (fun y : ℝ => (((1 - Gaussians.gaussian (t * y)) ^ nu - 1 : ℝ) : ℂ)) x
  simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff).contDiffAt.comp x hreal

/-- For `\ref{L:second-gaussian-estimate}`, Faa di Bruno gives the quadratic-tail bound for
the singular factor. -/
theorem aux_secondGaussianS_bound (k : ℕ) (t nu xi : ℝ)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) (ht : Real.sqrt 3 / 2 ≤ t)
    (hxi : 1 / 2 ≤ |xi|) :
    ‖iteratedDeriv k (aux_secondGaussianS t nu) xi‖ ≤
      C_faaDiBruno k * |xi|⁻¹ ^ 2 := by
  have hxi0 : xi ≠ 0 := by
    intro h
    subst xi
    norm_num at hxi
  let H : ℝ → ℝ := fun y => (1 - Gaussians.gaussian (t * y)) ^ nu - 1
  change ‖iteratedDeriv k (fun y : ℝ => (H y : ℂ)) xi‖ ≤
      C_faaDiBruno k * |xi|⁻¹ ^ 2
  rw [aux_secondGaussian_iteratedDeriv_ofReal_at k H xi (by
    simpa [H] using aux_secondGaussianS_real_contDiffAt (k + 1) t nu xi ht hxi0),
    Complex.norm_real]
  simpa [H, Real.norm_eq_abs] using faaDiBruno k hnu ht hxi

/-- For `\ref{L:second-gaussian-estimate}`, the plateau forces the multiplier to vanish near
the origin. -/
theorem aux_secondGaussianMultiplier_eq_zero_of_abs_lt (phiHat : ℝ → ℂ)
    (mu lambda t nu : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ 1 / 2)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    {xi : ℝ} (hxi : |xi| < 1 / 2) :
    secondGaussianMultiplier phiHat mu lambda t nu xi = 0 := by
  have hxiIcc : xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [abs_lt] at hxi
    exact ⟨hxi.1.le, hxi.2.le⟩
  have hscaledAbs : |lambda * xi| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hlambda0]
    have hxiLe : |xi| ≤ 1 / 2 := hxi.le
    calc
      lambda * |xi| ≤ lambda * (1 / 2) :=
        mul_le_mul_of_nonneg_left hxiLe hlambda0
      _ ≤ 1 / 2 := by nlinarith
  have hscaledIcc : lambda * xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    exact abs_le.mp hscaledAbs
  rw [secondGaussianMultiplier, Pi.mul_apply, aux_secondGaussianQ,
    hplateau (lambda * xi) hscaledIcc, hplateau xi hxiIcc, sub_self, mul_zero]
  simp

/-- For `\ref{L:second-gaussian-estimate}`, every iterated derivative vanishes on the
interior plateau. -/
theorem aux_secondGaussianMultiplier_iteratedDeriv_eq_zero_of_abs_lt (N : ℕ)
    (phiHat : ℝ → ℂ) (mu lambda t nu : ℝ) (hlambda0 : 0 ≤ lambda)
    (hlambda : lambda ≤ 1 / 2)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    {xi : ℝ} (hxi : |xi| < 1 / 2) :
    iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi = 0 := by
  have hEq : Set.EqOn (secondGaussianMultiplier phiHat mu lambda t nu)
      (fun _ : ℝ => (0 : ℂ)) (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro x hx
    have hxabs : |x| < 1 / 2 := by
      rw [abs_lt]
      exact hx
    exact aux_secondGaussianMultiplier_eq_zero_of_abs_lt phiHat mu lambda t nu hlambda0 hlambda
      hplateau hxabs
  have hderiv := hEq.iteratedDeriv_of_isOpen isOpen_Ioo N
  have hximem : xi ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [abs_lt] at hxi
    exact hxi
  simpa using hderiv hximem

/-- For `\ref{L:second-gaussian-estimate}`, the multiplier is smooth despite the apparent
singularity at the origin, because its first factor vanishes on a neighborhood there. -/
theorem aux_secondGaussianMultiplier_contDiff (N : ℕ) (phiHat : ℝ → ℂ) (mu lambda t nu : ℝ)
    (hmu : 0 < mu) (hmulambda : mu ≤ lambda) (hlambda : lambda ≤ 1 / 2)
    (ht : Real.sqrt 3 / 2 ≤ t)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    (hphi : ContDiff ℝ N phiHat) :
    ContDiff ℝ N (secondGaussianMultiplier phiHat mu lambda t nu) := by
  have hlambda0 : 0 ≤ lambda := hmu.le.trans hmulambda
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hzero : ContDiffAt ℝ N (fun _ : ℝ => (0 : ℂ)) 0 := contDiffAt_const
    exact hzero.congr_of_eventuallyEq (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 / 2 : ℝ))] with y hy
      have hy' : |y| < 1 / 2 := by
        rw [Metric.mem_ball, Real.dist_eq] at hy
        simpa using hy
      exact aux_secondGaussianMultiplier_eq_zero_of_abs_lt phiHat mu lambda t nu hlambda0 hlambda
        hplateau hy')
  · exact (aux_secondGaussianQ_contDiff N phiHat mu lambda hphi).contDiffAt.mul
      (aux_secondGaussianS_contDiffAt N t nu x ht hx)

/-- For `\ref{L:second-gaussian-estimate}`, the multiplier has compact support inherited from
the bump difference. -/
theorem aux_secondGaussianMultiplier_hasCompactSupport (phiHat : ℝ → ℂ) (mu lambda t nu : ℝ)
    (hlambda : lambda ≠ 0) (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1) :
    HasCompactSupport (secondGaussianMultiplier phiHat mu lambda t nu) := by
  have hphiCompact : HasCompactSupport phiHat :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hsupp
  have hscaled : HasCompactSupport (fun xi : ℝ => phiHat (lambda * xi)) := by
    simpa only [smul_eq_mul] using hphiCompact.comp_smul hlambda
  have hdiff : HasCompactSupport (fun xi : ℝ => phiHat (lambda * xi) - phiHat xi) :=
    hscaled.sub hphiCompact
  have hQ : HasCompactSupport (aux_secondGaussianQ phiHat mu lambda) := by
    change HasCompactSupport
      ((fun xi : ℝ => (((Gaussians.gaussian (mu * xi))⁻¹ : ℝ) : ℂ)) *
        (fun xi : ℝ => phiHat (lambda * xi) - phiHat xi))
    exact hdiff.mul_left
  change HasCompactSupport (aux_secondGaussianQ phiHat mu lambda * aux_secondGaussianS t nu)
  exact hQ.mul_right

/-- For `\ref{L:second-gaussian-estimate}`, the relevant iterated derivative is integrable. -/
theorem aux_secondGaussianMultiplier_iteratedDeriv_integrable (N : ℕ) (phiHat : ℝ → ℂ)
    (mu lambda t nu : ℝ) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (ht : Real.sqrt 3 / 2 ≤ t)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    (hphi : ContDiff ℝ N phiHat) (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1) :
    Integrable (iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu)) := by
  have hlambdaPos : 0 < lambda := hmu.trans_le hmulambda
  exact aux_integrable_iteratedDeriv_of_contDiff_compactSupport N N
    (secondGaussianMultiplier phiHat mu lambda t nu)
    (aux_secondGaussianMultiplier_contDiff N phiHat mu lambda t nu hmu hmulambda hlambda ht
      hplateau hphi)
    (aux_secondGaussianMultiplier_hasCompactSupport phiHat mu lambda t nu hlambdaPos.ne' hsupp)
    le_rfl

/-- For `\ref{L:second-gaussian-estimate}`, this is the complex-valued Leibniz estimate used
to combine the Gaussian-bump and Faa di Bruno bounds. -/
theorem aux_secondGaussian_leibniz_majorant (N : ℕ) (Q S : ℝ → ℂ) (x T : ℝ)
    (A B : ℕ → ℝ) (hQcont : ContDiffAt ℝ N Q x)
    (hScont : ContDiffAt ℝ N S x) (_hT : 0 ≤ T)
    (hA : ∀ l : ℕ, l ≤ N → 0 ≤ A l)
    (hB : ∀ l : ℕ, l ≤ N → 0 ≤ B l)
    (hQ : ∀ l : ℕ, l ≤ N → ‖iteratedDeriv l Q x‖ ≤ A l)
    (hS : ∀ l : ℕ, l ≤ N → ‖iteratedDeriv l S x‖ ≤ B l * T) :
    ‖iteratedDeriv N (Q * S) x‖ ≤
      ∑ l ∈ Finset.range (N + 1), (Nat.choose N l : ℝ) * A l * B (N - l) * T := by
  rw [iteratedDeriv_mul hQcont hScont]
  calc
    ‖∑ i ∈ Finset.range (N + 1), (N.choose i : ℂ) * iteratedDeriv i Q x *
        iteratedDeriv (N - i) S x‖ ≤
        ∑ i ∈ Finset.range (N + 1), ‖(N.choose i : ℂ) * iteratedDeriv i Q x *
          iteratedDeriv (N - i) S x‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) *
          ‖iteratedDeriv i Q x‖ * ‖iteratedDeriv (N - i) S x‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul, norm_mul, Complex.norm_natCast]
    _ ≤ ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * A i * B (N - i) * T := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hsub : N - i ≤ N := Nat.sub_le _ _
      have hcoeff : 0 ≤ (N.choose i : ℝ) := by positivity
      have hBi : 0 ≤ B (N - i) := hB _ hsub
      have hAi : 0 ≤ A i := hA _ hiN
      calc
        (N.choose i : ℝ) * ‖iteratedDeriv i Q x‖ * ‖iteratedDeriv (N - i) S x‖ ≤
            (N.choose i : ℝ) * A i * (B (N - i) * T) := by
          gcongr
          · exact hQ i hiN
          · exact hS (N - i) hsub
        _ = (N.choose i : ℝ) * A i * B (N - i) * T := by ring

/-- For `\ref{L:second-gaussian-estimate}`, this is the pointwise derivative bound outside
the plateau region. -/
theorem aux_secondGaussianMultiplier_pointwise_bound (N : ℕ) (c : ℝ) (phiHat : ℝ → ℂ)
    (mu lambda t nu : ℝ) (hc : 0 ≤ c) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (ht : Real.sqrt 3 / 2 ≤ t)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (xi : ℝ) (hxi : 1 / 2 ≤ |xi|) :
    ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖ ≤
      (2 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
        C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) * |xi|⁻¹ ^ 2 := by
  have hQ : ContDiff ℝ N (aux_secondGaussianQ phiHat mu lambda) :=
    aux_secondGaussianQ_contDiff N phiHat mu lambda hphi
  have hxi0 : xi ≠ 0 := by
    intro h
    subst xi
    norm_num at hxi
  have hS : ContDiffAt ℝ N (aux_secondGaussianS t nu) xi :=
    aux_secondGaussianS_contDiffAt N t nu xi ht hxi0
  have hA (l : ℕ) (_hl : l ≤ N) :
      0 ≤ 2 * c * (2 * Real.pi) ^ l * C_gaussianBumpEstimate l := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg <;> positivity
      · positivity
    · exact aux_C_gaussianBumpEstimate_nonneg l
  have hB (l : ℕ) (_hl : l ≤ N) : 0 ≤ C_faaDiBruno l :=
    aux_C_faaDiBruno_nonneg l
  have hQbound (l : ℕ) (hl : l ≤ N) :
      ‖iteratedDeriv l (aux_secondGaussianQ phiHat mu lambda) xi‖ ≤
        2 * c * (2 * Real.pi) ^ l * C_gaussianBumpEstimate l :=
    aux_secondGaussianQ_bound N l c phiHat mu lambda hc hmu hmulambda hlambda hphi hsupp
      hphiBound hl xi
  have hSbound (l : ℕ) (_hl : l ≤ N) :
      ‖iteratedDeriv l (aux_secondGaussianS t nu) xi‖ ≤
        C_faaDiBruno l * |xi|⁻¹ ^ 2 :=
    aux_secondGaussianS_bound l t nu xi hnu ht hxi
  have hmain := aux_secondGaussian_leibniz_majorant N (aux_secondGaussianQ phiHat mu lambda)
    (aux_secondGaussianS t nu) xi (|xi|⁻¹ ^ 2)
    (fun l => 2 * c * (2 * Real.pi) ^ l * C_gaussianBumpEstimate l)
    C_faaDiBruno hQ.contDiffAt hS (by positivity) hA hB hQbound hSbound
  calc
    ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖ ≤
        ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) *
          (2 * c * (2 * Real.pi) ^ l * C_gaussianBumpEstimate l) *
            C_faaDiBruno (N - l) * |xi|⁻¹ ^ 2 := by
      simpa only [secondGaussianMultiplier] using hmain
    _ = (2 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
        C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) * |xi|⁻¹ ^ 2 := by
      symm
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- For `\ref{L:second-gaussian-estimate}`, the closed quadratic tail agrees almost everywhere
with the open tail whose integral is elementary. -/
theorem aux_secondGaussian_tail_closed_ae_eq :
    (fun x : ℝ => if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0) =ᵐ[volume]
      fun x : ℝ => if (1 / 2 : ℝ) < |x| then |x| ^ (-2 : ℝ) else 0 := by
  change ∀ᵐ x : ℝ ∂volume,
    (if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0) =
      (if (1 / 2 : ℝ) < |x| then |x| ^ (-2 : ℝ) else 0)
  rw [ae_iff]
  apply MeasureTheory.measure_mono_null
  · intro x hx
    have hxeq : |x| = (1 / 2 : ℝ) := by
      by_contra hne
      apply hx
      by_cases hclosed : (1 / 2 : ℝ) ≤ |x|
      · have hopen : (1 / 2 : ℝ) < |x| :=
          lt_of_le_of_ne hclosed (fun h => hne h.symm)
        rw [if_pos hclosed, if_pos hopen]
      · have hopen : ¬ (1 / 2 : ℝ) < |x| := not_lt.mpr (le_of_not_ge hclosed)
        rw [if_neg hclosed, if_neg hopen]
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hxeq
  · have hnull : volume ({(1 / 2 : ℝ)} ∪ {-(1 / 2 : ℝ)}) = 0 :=
      MeasureTheory.measure_union_null (measure_singleton _) (measure_singleton _)
    simpa only [Set.singleton_union] using hnull

/-- For `\ref{L:second-gaussian-estimate}`, the open quadratic tail has integral four. -/
theorem aux_secondGaussian_openTail_integral :
    (∫ x : ℝ, if (1 / 2 : ℝ) < |x| then |x| ^ (-2 : ℝ) else 0) = 4 := by
  let f : ℝ → ℝ := fun r => if (1 / 2 : ℝ) < r then r ^ (-2 : ℝ) else 0
  have hpos : (∫ x : ℝ in Set.Ioi (1 / 2 : ℝ), x ^ (-2 : ℝ)) = 2 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : 0 < (1 / 2 : ℝ))]
    norm_num
  have hpos' : (∫ x : ℝ in Set.Ioi (0 : ℝ), f x) = 2 := by
    calc
      (∫ x : ℝ in Set.Ioi (0 : ℝ), f x) =
          ∫ x : ℝ in Set.Ioi (0 : ℝ) ∩ Set.Ioi (1 / 2 : ℝ), x ^ (-2 : ℝ) := by
        rw [← MeasureTheory.setIntegral_indicator measurableSet_Ioi]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [f, Set.mem_Ioi, Set.indicator_apply]
      _ = ∫ x : ℝ in Set.Ioi (1 / 2 : ℝ), x ^ (-2 : ℝ) := by
        congr 2
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioi]
        constructor
        · exact fun hx => hx.2
        · intro hx
          constructor <;> linarith
      _ = 2 := hpos
  have hrewrite : (∫ x : ℝ, if (1 / 2 : ℝ) < |x| then |x| ^ (-2 : ℝ) else 0) =
      ∫ x : ℝ, f |x| := by
    congr with x
  rw [hrewrite]
  rw [integral_comp_abs, hpos']
  norm_num

/-- For `\ref{L:second-gaussian-estimate}`, the open quadratic tail is integrable. -/
theorem aux_secondGaussian_openTail_integrable :
    Integrable (fun x : ℝ => if (1 / 2 : ℝ) < |x| then |x| ^ (-2 : ℝ) else 0) := by
  let f : ℝ → ℝ := fun r => if (1 / 2 : ℝ) < r then r ^ (-2 : ℝ) else 0
  have hpos : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi (1 / 2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hf : Integrable f := by
    rw [show f = (Set.Ioi (1 / 2 : ℝ)).indicator (fun x : ℝ => x ^ (-2 : ℝ)) by
      funext x
      simp only [f, Set.indicator_apply, Set.mem_Ioi]]
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).mpr hpos
  have hfneg : Integrable (fun x : ℝ => f (-x)) := by
    exact (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hf
  have hrewrite : (fun x : ℝ => if (1 / 2 : ℝ) < |x| then |x| ^ (-2 : ℝ) else 0) =
      fun x : ℝ => f x + f (-x) := by
    funext x
    simp only [f]
    by_cases hpos : (1 / 2 : ℝ) < x
    · have habs : |x| = x := abs_of_pos (by linarith)
      rw [habs]
      have hneg : ¬ (1 / 2 : ℝ) < -x := by linarith
      rw [if_pos hpos, if_neg hneg, add_zero]
    · by_cases hneg : (1 / 2 : ℝ) < -x
      · have habs : |x| = -x := abs_of_neg (by linarith)
        rw [habs]
        rw [if_pos hneg, if_neg hpos, zero_add]
      · have habs : |x| ≤ (1 / 2 : ℝ) := by
          rw [abs_le]
          constructor <;> linarith
        rw [if_neg (not_lt.mpr habs), if_neg hpos, if_neg hneg]
        norm_num
  rw [hrewrite]
  exact hf.add (by simpa [Function.comp_def] using hfneg)

/-- For `\ref{L:second-gaussian-estimate}`, the closed quadratic tail is integrable and has
integral four. -/
theorem aux_secondGaussian_tail_closed_integrable :
    Integrable (fun x : ℝ => if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0) := by
  exact aux_secondGaussian_openTail_integrable.congr aux_secondGaussian_tail_closed_ae_eq.symm

/-- For `\ref{L:second-gaussian-estimate}`, the closed quadratic tail has integral four. -/
theorem aux_secondGaussian_tail_closed_integral :
    (∫ x : ℝ, if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0) = 4 := by
  rw [MeasureTheory.integral_congr_ae aux_secondGaussian_tail_closed_ae_eq]
  exact aux_secondGaussian_openTail_integral

/-- For `\ref{L:second-gaussian-estimate}`, a pointwise closed-tail majorant gives the stated
real $L^1$ estimate. -/
theorem aux_secondGaussian_l1_tail_bound {g : ℝ → ℂ} (A : ℝ) (hg : Integrable g)
    (hpoint : ∀ x : ℝ,
      ‖g x‖ ≤ A * (if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0)) :
    (∫ x : ℝ, ‖g x‖) ≤ 4 * A := by
  let tail : ℝ → ℝ := fun x =>
    if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0
  have htail : Integrable tail := by
    simpa only [tail] using aux_secondGaussian_tail_closed_integrable
  calc
    (∫ x : ℝ, ‖g x‖) ≤ ∫ x : ℝ, A * tail x :=
      MeasureTheory.integral_mono hg.norm (htail.const_mul A) (fun x => by
        simpa only [tail] using hpoint x)
    _ = A * ∫ x : ℝ, tail x := MeasureTheory.integral_const_mul A tail
    _ = 4 * A := by
      rw [show (∫ x : ℝ, tail x) = 4 by
        calc
          (∫ x : ℝ, tail x) = ∫ x : ℝ,
              if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0 := by rfl
          _ = 4 := aux_secondGaussian_tail_closed_integral]
      ring

/-- For `\ref{L:second-gaussian-estimate}`, the closed quadratic tail is uniformly bounded
by four. -/
theorem aux_secondGaussian_tail_closed_le_four (x : ℝ) :
    (if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0) ≤ 4 := by
  by_cases h : (1 / 2 : ℝ) ≤ |x|
  · rw [if_pos h, Real.rpow_neg (abs_nonneg x) (2 : ℝ)]
    have hx : 0 < |x| := by linarith
    have hsq : 1 ≤ 4 * |x| ^ 2 := by nlinarith
    have hpow : |x| ^ (2 : ℝ) = |x| ^ (2 : ℕ) := by
      norm_num [Real.rpow_natCast]
    rw [hpow]
    rw [inv_le_iff_one_le_mul₀ (sq_pos_of_pos hx)]
    nlinarith
  · rw [if_neg h]
    norm_num

/-- For `\ref{L:second-gaussian-estimate}`, a pointwise closed-tail majorant gives the stated
uniform derivative estimate. -/
theorem aux_secondGaussian_linf_tail_bound {g : ℝ → ℂ} (A : ℝ) (hA : 0 ≤ A)
    (hpoint : ∀ x : ℝ,
      ‖g x‖ ≤ A * (if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0)) :
    sSup (Set.range fun x : ℝ => ‖g x‖) ≤ 4 * A := by
  apply csSup_le
  · exact ⟨‖g 0‖, ⟨0, rfl⟩⟩
  rintro _ ⟨x, rfl⟩
  calc
    ‖g x‖ ≤ A * (if (1 / 2 : ℝ) ≤ |x| then |x| ^ (-2 : ℝ) else 0) := hpoint x
    _ ≤ A * 4 := mul_le_mul_of_nonneg_left (aux_secondGaussian_tail_closed_le_four x) hA
    _ = 4 * A := by ring

/-- For `\ref{L:second-gaussian-estimate}`, this is the global derivative majorant obtained
from plateau cancellation and the exterior Leibniz estimate. -/
theorem aux_secondGaussianMultiplier_tail_bound (N : ℕ) (c : ℝ) (phiHat : ℝ → ℂ)
    (mu lambda t nu : ℝ) (hc : 0 ≤ c) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (ht : Real.sqrt 3 / 2 ≤ t)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (xi : ℝ) :
    ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖ ≤
      (2 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
        C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) *
        (if (1 / 2 : ℝ) ≤ |xi| then |xi| ^ (-2 : ℝ) else 0) := by
  have hlambda0 : 0 ≤ lambda := hmu.le.trans hmulambda
  by_cases hxi : (1 / 2 : ℝ) ≤ |xi|
  · rw [if_pos hxi]
    rw [Real.rpow_neg (abs_nonneg xi) (2 : ℝ)]
    have hpow : |xi| ^ (2 : ℝ) = |xi| ^ (2 : ℕ) := by
      norm_num [Real.rpow_natCast]
    rw [hpow]
    simpa only [inv_pow] using
      aux_secondGaussianMultiplier_pointwise_bound N c phiHat mu lambda t nu hc hmu hmulambda
        hlambda ht hnu hphi hsupp hphiBound xi hxi
  · rw [if_neg hxi]
    have hxi' : |xi| < 1 / 2 := lt_of_not_ge hxi
    rw [aux_secondGaussianMultiplier_iteratedDeriv_eq_zero_of_abs_lt N phiHat mu lambda t nu
      hlambda0 hlambda hplateau hxi']
    norm_num

/-- For `\ref{L:second-gaussian-estimate}`, this rewrites the unnormalized tail estimate in
the exact Fourier-normalized constant. -/
theorem aux_secondGaussian_constant_normalization (N : ℕ) (c : ℝ) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ N *
      (8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
        C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) =
      c * C_secondGaussianEstimate N := by
  have hsum :
      (∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
        C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) =
      ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
        (C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hsum' :
      (∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) *
        Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
          (C_gaussianBumpEstimate l * C_faaDiBruno (N - l))) =
      ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) *
        Real.rpow (2 * Real.pi) ((l : ℝ) - N) * C_gaussianBumpEstimate l *
          C_faaDiBruno (N - l) := by
    apply Finset.sum_congr rfl
    intro l _
    ring
  calc
    ((2 * Real.pi)⁻¹ : ℝ) ^ N *
        (8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
          C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) =
        8 * c * (((2 * Real.pi)⁻¹ : ℝ) ^ N *
          ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
            C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) := by ring
    _ = 8 * c * (((2 * Real.pi)⁻¹ : ℝ) ^ N *
          ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
            (C_gaussianBumpEstimate l * C_faaDiBruno (N - l))) := by rw [hsum]
    _ = 8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) *
          Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
            (C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) := by
      rw [Finset.mul_sum]
      apply congrArg (fun z : ℝ => 8 * c * z)
      apply Finset.sum_congr rfl
      intro l _
      have hbase : 0 < 2 * Real.pi := by positivity
      have hmul : ((2 * Real.pi)⁻¹ : ℝ) ^ N * (2 * Real.pi) ^ l =
          Real.rpow (2 * Real.pi) ((l : ℝ) - N) := by
        calc
          ((2 * Real.pi)⁻¹ : ℝ) ^ N * (2 * Real.pi) ^ l =
              Real.rpow (2 * Real.pi) (-(N : ℝ)) * Real.rpow (2 * Real.pi) (l : ℝ) := by
            rw [aux_gaussianBumpEstimate_qpow_eq_rpow]
            congr 1
            exact (Real.rpow_natCast (2 * Real.pi) l).symm
          _ = Real.rpow (2 * Real.pi) (-(N : ℝ) + (l : ℝ)) :=
            (Real.rpow_add hbase _ _).symm
          _ = Real.rpow (2 * Real.pi) ((l : ℝ) - N) := by
            congr 1
            ring
      rw [show ((2 * Real.pi)⁻¹ : ℝ) ^ N *
          ((N.choose l : ℝ) * (2 * Real.pi) ^ l *
            (C_gaussianBumpEstimate l * C_faaDiBruno (N - l))) =
          (N.choose l : ℝ) * (((2 * Real.pi)⁻¹ : ℝ) ^ N * (2 * Real.pi) ^ l) *
            (C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) by ring,
        hmul]
    _ = c * C_secondGaussianEstimate N := by
      rw [hsum', C_secondGaussianEstimate]
      ring

/-- For \ref{L:second-gaussian-estimate}, the Fourier-normalized L¹ derivative bound
obtained from the inverse-square tail. -/
theorem aux_secondGaussianMultiplier_l1_bound (N : ℕ) (c : ℝ) (phiHat : ℝ → ℂ)
    (mu lambda t nu : ℝ) (hc : 0 ≤ c) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (ht : Real.sqrt 3 / 2 ≤ t)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ N *
      (∫ xi : ℝ, ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤
      c * C_secondGaussianEstimate N := by
  let A : ℝ := 2 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) *
    (2 * Real.pi) ^ l * C_gaussianBumpEstimate l * C_faaDiBruno (N - l)
  have hInt : Integrable (iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu)) :=
    aux_secondGaussianMultiplier_iteratedDeriv_integrable N phiHat mu lambda t nu hmu hmulambda
      hlambda ht hplateau hphi hsupp
  have hraw : (∫ xi : ℝ, ‖iteratedDeriv N
      (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤ 4 * A := by
    exact aux_secondGaussian_l1_tail_bound A hInt (by
      intro xi
      simpa only [A] using aux_secondGaussianMultiplier_tail_bound N c phiHat mu lambda t nu
        hc hmu hmulambda hlambda ht hnu hplateau hphi hsupp hphiBound xi)
  have hraw' : (∫ xi : ℝ, ‖iteratedDeriv N
      (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤
      8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
        C_gaussianBumpEstimate l * C_faaDiBruno (N - l) := by
    calc
      (∫ xi : ℝ, ‖iteratedDeriv N
          (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤ 4 * A := hraw
      _ = 8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
          C_gaussianBumpEstimate l * C_faaDiBruno (N - l) := by
        dsimp [A]
        ring
  calc
    ((2 * Real.pi)⁻¹ : ℝ) ^ N *
        (∫ xi : ℝ, ‖iteratedDeriv N
          (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤
      ((2 * Real.pi)⁻¹ : ℝ) ^ N *
        (8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
          C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) :=
      mul_le_mul_of_nonneg_left hraw' (by positivity)
    _ = c * C_secondGaussianEstimate N := aux_secondGaussian_constant_normalization N c

/-- For \ref{L:second-gaussian-estimate}, the Fourier-normalized L∞ derivative bound
obtained from the inverse-square tail. -/
theorem aux_secondGaussianMultiplier_linf_bound (N : ℕ) (c : ℝ) (phiHat : ℝ → ℂ)
    (mu lambda t nu : ℝ) (hc : 0 ≤ c) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (ht : Real.sqrt 3 / 2 ≤ t)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ N *
      sSup (Set.range fun xi : ℝ =>
        ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤
      c * C_secondGaussianEstimate N := by
  let A : ℝ := 2 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) *
    (2 * Real.pi) ^ l * C_gaussianBumpEstimate l * C_faaDiBruno (N - l)
  have hA : 0 ≤ A := by
    dsimp [A]
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) hc
    · apply Finset.sum_nonneg
      intro l _
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg <;> positivity
        · exact aux_C_gaussianBumpEstimate_nonneg l
      · exact aux_C_faaDiBruno_nonneg _
  have hraw : sSup (Set.range fun xi : ℝ =>
      ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤ 4 * A := by
    exact aux_secondGaussian_linf_tail_bound A hA (by
      intro xi
      simpa only [A] using aux_secondGaussianMultiplier_tail_bound N c phiHat mu lambda t nu
        hc hmu hmulambda hlambda ht hnu hplateau hphi hsupp hphiBound xi)
  have hraw' : sSup (Set.range fun xi : ℝ =>
      ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤
      8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
        C_gaussianBumpEstimate l * C_faaDiBruno (N - l) := by
    calc
      sSup (Set.range fun xi : ℝ =>
          ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤ 4 * A := hraw
      _ = 8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
          C_gaussianBumpEstimate l * C_faaDiBruno (N - l) := by
        dsimp [A]
        ring
  calc
    ((2 * Real.pi)⁻¹ : ℝ) ^ N *
        sSup (Set.range fun xi : ℝ =>
          ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖) ≤
      ((2 * Real.pi)⁻¹ : ℝ) ^ N *
        (8 * c * ∑ l ∈ Finset.range (N + 1), (N.choose l : ℝ) * (2 * Real.pi) ^ l *
          C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) :=
      mul_le_mul_of_nonneg_left hraw' (by positivity)
    _ = c * C_secondGaussianEstimate N := aux_secondGaussian_constant_normalization N c

/--
For source label \ref{L:second-gaussian-estimate}, let c > 0, and let phi be a
W₀(ℝ) function whose Fourier transform phiHat is supported in [-1, 1], equals 1 on
[-1 / 2, 1 / 2], is N times continuously differentiable, and has all iterated derivatives
through order N bounded by c. If 0 < mu ≤ lambda ≤ 1 / 2, sqrt 3 / 2 ≤ t, and
nu ∈ [-1, 0), then the second Gaussian multiplier is N times continuously differentiable and
(2π)⁻ᴺ max(‖R^(N)‖₁, ‖R^(N)‖∞) ≤ c * C_secondGaussianEstimate N.
-/
theorem secondGaussianEstimate (c : ℝ) (N : ℕ) (phi phiHat : ℝ → ℂ)
    (_hphiW0 : MemW0 phi) (_hphiHat : phiHat = FourierTransform.fourier phi)
    (hc : 0 < c) (mu lambda t nu : ℝ) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (ht : Real.sqrt 3 / 2 ≤ t)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c) :
    ContDiff ℝ N (secondGaussianMultiplier phiHat mu lambda t nu) ∧
      ((2 * Real.pi)⁻¹ : ℝ) ^ N *
        max (∫ xi : ℝ, ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖)
          (sSup (Set.range fun xi : ℝ =>
            ‖iteratedDeriv N (secondGaussianMultiplier phiHat mu lambda t nu) xi‖)) ≤
      c * C_secondGaussianEstimate N := by
  constructor
  · exact aux_secondGaussianMultiplier_contDiff N phiHat mu lambda t nu hmu hmulambda hlambda ht
      hplateau hphi
  · rw [mul_max_of_nonneg _ _ (by positivity)]
    exact max_le
      (aux_secondGaussianMultiplier_l1_bound N c phiHat mu lambda t nu hc.le hmu hmulambda
        hlambda ht hnu hplateau hphi hsupp hphiBound)
      (aux_secondGaussianMultiplier_linf_bound N c phiHat mu lambda t nu hc.le hmu hmulambda
        hlambda ht hnu hplateau hphi hsupp hphiBound)

/-- Rewrite the second-Gaussian constant in terms of powers of `(2π)⁻¹`. -/
theorem aux_C_secondGaussianEstimate_eq_q_sum (N : ℕ) :
    C_secondGaussianEstimate N = 8 * ∑ l ∈ Finset.range (N + 1),
      (Nat.choose N l : ℝ) * ((2 * Real.pi)⁻¹ : ℝ) ^ (N - l) *
        C_gaussianBumpEstimate l * C_faaDiBruno (N - l) := by
  rw [C_secondGaussianEstimate]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  have hlN : l ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have hsub : (l : ℝ) - N = -((N - l : ℕ) : ℝ) := by
    rw [Nat.cast_sub hlN]
    ring
  rw [hsub, ← aux_gaussianBumpEstimate_qpow_eq_rpow]

theorem aux_C_secondGaussianEstimate_zero_eq : C_secondGaussianEstimate 0 =
    8 * C_gaussianBumpEstimate 0 * C_faaDiBruno 0 := by
  rw [aux_C_secondGaussianEstimate_eq_q_sum]
  norm_num [Finset.sum_range_succ]
  ring

theorem aux_C_secondGaussianEstimate_one_eq : C_secondGaussianEstimate 1 =
    8 * (((2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 0 * C_faaDiBruno 1) +
      (C_gaussianBumpEstimate 1 * C_faaDiBruno 0)) := by
  rw [aux_C_secondGaussianEstimate_eq_q_sum]
  norm_num [Finset.sum_range_succ]

theorem aux_C_secondGaussianEstimate_two_eq : C_secondGaussianEstimate 2 =
    8 * ((((2 * Real.pi)⁻¹) ^ 2 * C_gaussianBumpEstimate 0 * C_faaDiBruno 2) +
      (2 * (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 1 * C_faaDiBruno 1) +
      (C_gaussianBumpEstimate 2 * C_faaDiBruno 0)) := by
  rw [aux_C_secondGaussianEstimate_eq_q_sum]
  norm_num [Finset.sum_range_succ]

theorem aux_C_secondGaussianEstimate_three_eq : C_secondGaussianEstimate 3 =
    8 * ((((2 * Real.pi)⁻¹) ^ 3 * C_gaussianBumpEstimate 0 * C_faaDiBruno 3) +
      (3 * ((2 * Real.pi)⁻¹) ^ 2 * C_gaussianBumpEstimate 1 * C_faaDiBruno 2) +
      (3 * (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 2 * C_faaDiBruno 1) +
      (C_gaussianBumpEstimate 3 * C_faaDiBruno 0)) := by
  rw [aux_C_secondGaussianEstimate_eq_q_sum]
  norm_num [Finset.sum_range_succ]

/-- The general explicit bound for the second-Gaussian constant. -/
theorem aux_C_secondGaussianEstimate_bound (N : ℕ) :
    C_secondGaussianEstimate N ≤ (2 : ℝ) ^ (20 * (N + 1) ^ 3) := by
  by_cases hN : N = 0
  · subst N
    rw [aux_C_secondGaussianEstimate_zero_eq]
    have hG0 : C_gaussianBumpEstimate 0 ≤ 81 :=
      (constantGaussianBumpEstimate 0).2.1.le
    have hF0 : C_faaDiBruno 0 ≤ 72 := aux_C_faaDiBruno_zero_le
    calc
      8 * C_gaussianBumpEstimate 0 * C_faaDiBruno 0 =
          8 * (C_gaussianBumpEstimate 0 * C_faaDiBruno 0) := by ring
      _ ≤ 8 * (81 * 72) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hG0 hF0 (aux_C_faaDiBruno_nonneg 0)
            (by norm_num : (0 : ℝ) ≤ 81)) (by norm_num)
      _ ≤ (1048576 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ (20 * (0 + 1) ^ 3) := by norm_num
  · let G : ℝ := (2 : ℝ) ^ (8 * (N + 1) ^ 2)
    let F : ℝ := (2 : ℝ) ^ (10 * (N + 1) ^ 3)
    have hGnonneg : 0 ≤ G := by dsimp [G]; positivity
    have hFnonneg : 0 ≤ F := by dsimp [F]; positivity
    have hG (l : ℕ) (hl : l ≤ N) : C_gaussianBumpEstimate l ≤ G := by
      calc
        C_gaussianBumpEstimate l ≤ (2 : ℝ) ^ (8 * (l + 1) ^ 2) :=
          (constantGaussianBumpEstimate l).1
        _ ≤ (2 : ℝ) ^ (8 * (N + 1) ^ 2) := by
          apply pow_le_pow_right₀ (by norm_num)
          exact Nat.mul_le_mul_left 8
            (Nat.pow_le_pow_left (Nat.succ_le_succ hl) 2)
        _ = G := by rfl
    have hF (l : ℕ) (hl : l ≤ N) : C_faaDiBruno (N - l) ≤ F := by
      calc
        C_faaDiBruno (N - l) ≤ (2 : ℝ) ^ (10 * (N - l + 1) ^ 3) :=
          (constantFaaDiBruno (N - l)).1
        _ ≤ (2 : ℝ) ^ (10 * (N + 1) ^ 3) := by
          apply pow_le_pow_right₀ (by norm_num)
          exact Nat.mul_le_mul_left 10
            (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.sub_le _ _)) 3)
        _ = F := by rfl
    have hterm (l : ℕ) (hl : l ∈ Finset.range (N + 1)) :
        (N.choose l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
          C_gaussianBumpEstimate l * C_faaDiBruno (N - l) ≤
          (2 : ℝ) ^ N * G * F := by
      have hlN : l ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have hchoose : (N.choose l : ℝ) ≤ (2 : ℝ) ^ N := by
        exact_mod_cast Nat.choose_le_two_pow N l
      have hrpow : Real.rpow (2 * Real.pi) ((l : ℝ) - N) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos
        · nlinarith [Real.pi_gt_three]
        · have hcast : (l : ℝ) ≤ (N : ℝ) := by exact_mod_cast hlN
          linarith
      have hcoeff : (N.choose l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) ≤
          (2 : ℝ) ^ N := by
        calc
          (N.choose l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) ≤
              (N.choose l : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hrpow (by positivity)
          _ = (N.choose l : ℝ) := by ring
          _ ≤ (2 : ℝ) ^ N := hchoose
      have hGF : C_gaussianBumpEstimate l * C_faaDiBruno (N - l) ≤ G * F :=
        mul_le_mul (hG l hlN) (hF l hlN) (aux_C_faaDiBruno_nonneg (N - l)) hGnonneg
      have hCGCF : 0 ≤ C_gaussianBumpEstimate l * C_faaDiBruno (N - l) :=
        mul_nonneg (aux_C_gaussianBumpEstimate_nonneg l) (aux_C_faaDiBruno_nonneg (N - l))
      calc
        (N.choose l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
            C_gaussianBumpEstimate l * C_faaDiBruno (N - l) =
            ((N.choose l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N)) *
              (C_gaussianBumpEstimate l * C_faaDiBruno (N - l)) := by ring
        _ ≤ (2 : ℝ) ^ N * (G * F) :=
          mul_le_mul hcoeff hGF hCGCF (by positivity)
        _ = (2 : ℝ) ^ N * G * F := by ring
    have hsum : ∑ l ∈ Finset.range (N + 1),
        (N.choose l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
          C_gaussianBumpEstimate l * C_faaDiBruno (N - l) ≤
        ((N + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ N * G * F) := by
      simpa [Finset.card_range, nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (Finset.range (N + 1))
          (fun l => (N.choose l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
            C_gaussianBumpEstimate l * C_faaDiBruno (N - l))
          ((2 : ℝ) ^ N * G * F) (by
            intro l hl
            exact hterm l hl))
    have hcard : ((N + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N + 1) := by
      norm_cast
      exact aux_nat_le_two_pow (N + 1)
    have hExponent : 4 + 2 * N + 8 * (N + 1) ^ 2 + 10 * (N + 1) ^ 3 ≤
        20 * (N + 1) ^ 3 := by
      have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      nlinarith
    rw [C_secondGaussianEstimate]
    calc
      8 * ∑ l ∈ Finset.range (N + 1),
          (N.choose l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
            C_gaussianBumpEstimate l * C_faaDiBruno (N - l) ≤
          8 * (((N + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ N * G * F)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ 8 * ((2 : ℝ) ^ (N + 1) * ((2 : ℝ) ^ N * G * F)) := by
        gcongr
      _ = (2 : ℝ) ^ (4 + 2 * N + 8 * (N + 1) ^ 2 + 10 * (N + 1) ^ 3) := by
        dsimp [G, F]
        rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_add, ← pow_add, ← pow_add,
          ← pow_add]
        congr 1
        omega
      _ ≤ (2 : ℝ) ^ (20 * (N + 1) ^ 3) := by
        exact pow_le_pow_right₀ (by norm_num) hExponent

/-- The first two small-order second-Gaussian constant estimates. -/
theorem aux_C_secondGaussianEstimate_zero_lt :
    C_secondGaussianEstimate 0 < (2 : ℝ) ^ 16 := by
  rw [aux_C_secondGaussianEstimate_zero_eq]
  have hG0 : C_gaussianBumpEstimate 0 ≤ 81 :=
    (constantGaussianBumpEstimate 0).2.1.le
  have hF0 : C_faaDiBruno 0 ≤ 72 := aux_C_faaDiBruno_zero_le
  calc
    8 * C_gaussianBumpEstimate 0 * C_faaDiBruno 0 =
        8 * (C_gaussianBumpEstimate 0 * C_faaDiBruno 0) := by ring
    _ ≤ 8 * (81 * 72) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hG0 hF0 (aux_C_faaDiBruno_nonneg 0)
          (by norm_num : (0 : ℝ) ≤ 81)) (by norm_num)
    _ < (65536 : ℝ) := by norm_num
    _ = (2 : ℝ) ^ 16 := by norm_num

theorem aux_C_secondGaussianEstimate_one_lt :
    C_secondGaussianEstimate 1 < (2 : ℝ) ^ 22 := by
  have hG0 : C_gaussianBumpEstimate 0 ≤ 81 :=
    (constantGaussianBumpEstimate 0).2.1.le
  have hG1 : C_gaussianBumpEstimate 1 ≤ 95 :=
    (constantGaussianBumpEstimate 0).2.2.1.le
  have hF0 : C_faaDiBruno 0 ≤ 72 := aux_C_faaDiBruno_zero_le
  have hF1 : C_faaDiBruno 1 ≤ 27648 := (aux_C_faaDiBruno_one_lt).le
  have hq : (2 * Real.pi)⁻¹ ≤ (1 / 6 : ℝ) := (aux_inv_two_pi_lt_sixth).le
  have hA : (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 0 * C_faaDiBruno 1 ≤
      (1 / 6 : ℝ) * 81 * 27648 := by
    have hqG : (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 0 ≤ (1 / 6 : ℝ) * 81 :=
      mul_le_mul hq hG0 (aux_C_gaussianBumpEstimate_nonneg 0) (by norm_num)
    calc
      (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 0 * C_faaDiBruno 1 ≤
          ((1 / 6 : ℝ) * 81) * C_faaDiBruno 1 :=
        mul_le_mul_of_nonneg_right hqG (aux_C_faaDiBruno_nonneg 1)
      _ ≤ ((1 / 6 : ℝ) * 81) * 27648 :=
        mul_le_mul_of_nonneg_left hF1 (by norm_num)
      _ = (1 / 6 : ℝ) * 81 * 27648 := by ring
  have hB : C_gaussianBumpEstimate 1 * C_faaDiBruno 0 ≤ 95 * 72 :=
    mul_le_mul hG1 hF0 (aux_C_faaDiBruno_nonneg 0) (by norm_num)
  rw [aux_C_secondGaussianEstimate_one_eq]
  calc
    8 * ((2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 0 * C_faaDiBruno 1 +
        C_gaussianBumpEstimate 1 * C_faaDiBruno 0) ≤
        8 * ((1 / 6 : ℝ) * 81 * 27648 + 95 * 72) :=
      mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
    _ < (4194304 : ℝ) := by norm_num
    _ = (2 : ℝ) ^ 22 := by norm_num

/-- Positivity of the zero-order Gaussian-bump constant, used for strict finite estimates. -/
theorem aux_C_gaussianBumpEstimate_zero_pos : 0 < C_gaussianBumpEstimate 0 := by
  norm_num [C_gaussianBumpEstimate, C_gaussianEstimate]
  exact Real.exp_pos _

/-- The sharp direct-substitution second-Gaussian estimate at order two. -/
theorem aux_C_secondGaussianEstimate_two_lt_value :
    C_secondGaussianEstimate 2 < 159359088384 := by
  have hG0 : C_gaussianBumpEstimate 0 ≤ 81 :=
    (constantGaussianBumpEstimate 0).2.1.le
  have hG1 : C_gaussianBumpEstimate 1 ≤ 95 :=
    (constantGaussianBumpEstimate 0).2.2.1.le
  have hG2 : C_gaussianBumpEstimate 2 ≤ 124 :=
    (constantGaussianBumpEstimate 0).2.2.2.1.le
  have hF0 : C_faaDiBruno 0 ≤ 72 := aux_C_faaDiBruno_zero_le
  have hF1 : C_faaDiBruno 1 ≤ 27648 := (aux_C_faaDiBruno_one_lt).le
  have hF2 : C_faaDiBruno 2 < 8852889600 := aux_C_faaDiBruno_two_lt
  have hq : (2 * Real.pi)⁻¹ ≤ (1 / 6 : ℝ) := (aux_inv_two_pi_lt_sixth).le
  have hq2 : ((2 * Real.pi)⁻¹ : ℝ) ^ 2 ≤ (1 / 6 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hq 2
  have hA : ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 0 *
      C_faaDiBruno 2 < (1 / 6 : ℝ) ^ 2 * 81 * 8852889600 := by
    have hqGpos : 0 < ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 0 :=
      mul_pos (pow_pos (by positivity) _) aux_C_gaussianBumpEstimate_zero_pos
    have hqG : ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 0 ≤
        (1 / 6 : ℝ) ^ 2 * 81 :=
      mul_le_mul hq2 hG0 (aux_C_gaussianBumpEstimate_nonneg 0) (by norm_num)
    calc
      ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 0 * C_faaDiBruno 2 =
          (((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 0) * C_faaDiBruno 2 := by
        ring
      _ < (((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 0) * 8852889600 :=
        mul_lt_mul_of_pos_left hF2 hqGpos
      _ ≤ ((1 / 6 : ℝ) ^ 2 * 81) * 8852889600 :=
        mul_le_mul_of_nonneg_right hqG (by norm_num)
      _ = (1 / 6 : ℝ) ^ 2 * 81 * 8852889600 := by ring
  have hBraw : (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 1 * C_faaDiBruno 1 ≤
      (1 / 6 : ℝ) * 95 * 27648 := by
    have hqG : (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 1 ≤ (1 / 6 : ℝ) * 95 :=
      mul_le_mul hq hG1 (aux_C_gaussianBumpEstimate_nonneg 1) (by norm_num)
    calc
      (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 1 * C_faaDiBruno 1 ≤
          ((1 / 6 : ℝ) * 95) * C_faaDiBruno 1 :=
        mul_le_mul_of_nonneg_right hqG (aux_C_faaDiBruno_nonneg 1)
      _ ≤ ((1 / 6 : ℝ) * 95) * 27648 :=
        mul_le_mul_of_nonneg_left hF1 (by norm_num)
      _ = (1 / 6 : ℝ) * 95 * 27648 := by ring
  have hB : 2 * (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 1 * C_faaDiBruno 1 ≤
      2 * (1 / 6 : ℝ) * 95 * 27648 := by
    calc
      2 * (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 1 * C_faaDiBruno 1 =
          2 * ((2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 1 * C_faaDiBruno 1) := by ring
      _ ≤ 2 * ((1 / 6 : ℝ) * 95 * 27648) :=
        mul_le_mul_of_nonneg_left hBraw (by norm_num)
      _ = 2 * (1 / 6 : ℝ) * 95 * 27648 := by ring
  have hC : C_gaussianBumpEstimate 2 * C_faaDiBruno 0 ≤ 124 * 72 :=
    mul_le_mul hG2 hF0 (aux_C_faaDiBruno_nonneg 0) (by norm_num)
  rw [aux_C_secondGaussianEstimate_two_eq]
  calc
    8 * (((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 0 * C_faaDiBruno 2 +
        2 * (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 1 * C_faaDiBruno 1 +
        C_gaussianBumpEstimate 2 * C_faaDiBruno 0) <
        8 * ((1 / 6 : ℝ) ^ 2 * 81 * 8852889600 +
          2 * (1 / 6 : ℝ) * 95 * 27648 + 124 * 72) :=
      mul_lt_mul_of_pos_left
        (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le hA hB) hC) (by norm_num)
    _ = 159359088384 := by norm_num

theorem aux_C_secondGaussianEstimate_two_lt :
    C_secondGaussianEstimate 2 < (2 : ℝ) ^ 38 := by
  calc
    C_secondGaussianEstimate 2 < 159359088384 := aux_C_secondGaussianEstimate_two_lt_value
    _ < (2 : ℝ) ^ 38 := by norm_num

/-- The sharp direct-substitution second-Gaussian estimate at order three. -/
theorem aux_C_secondGaussianEstimate_three_lt_value :
    C_secondGaussianEstimate 3 < 767070519557262336 := by
  have hG0 : C_gaussianBumpEstimate 0 ≤ 81 :=
    (constantGaussianBumpEstimate 0).2.1.le
  have hG1 : C_gaussianBumpEstimate 1 ≤ 95 :=
    (constantGaussianBumpEstimate 0).2.2.1.le
  have hG2 : C_gaussianBumpEstimate 2 ≤ 124 :=
    (constantGaussianBumpEstimate 0).2.2.2.1.le
  have hG3 : C_gaussianBumpEstimate 3 ≤ 176 :=
    (constantGaussianBumpEstimate 0).2.2.2.2.le
  have hF0 : C_faaDiBruno 0 ≤ 72 := aux_C_faaDiBruno_zero_le
  have hF1 : C_faaDiBruno 1 ≤ 27648 := (aux_C_faaDiBruno_one_lt).le
  have hF2 : C_faaDiBruno 2 ≤ 8852889600 := (aux_C_faaDiBruno_two_lt).le
  have hF3 : C_faaDiBruno 3 < 255689986286813184 := aux_C_faaDiBruno_three_lt
  have hq : (2 * Real.pi)⁻¹ ≤ (1 / 6 : ℝ) := (aux_inv_two_pi_lt_sixth).le
  have hq2 : ((2 * Real.pi)⁻¹ : ℝ) ^ 2 ≤ (1 / 6 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hq 2
  have hq3 : ((2 * Real.pi)⁻¹ : ℝ) ^ 3 ≤ (1 / 6 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hq 3
  have hA : ((2 * Real.pi)⁻¹ : ℝ) ^ 3 * C_gaussianBumpEstimate 0 *
      C_faaDiBruno 3 < (1 / 6 : ℝ) ^ 3 * 81 * 255689986286813184 := by
    have hqGpos : 0 < ((2 * Real.pi)⁻¹ : ℝ) ^ 3 * C_gaussianBumpEstimate 0 :=
      mul_pos (pow_pos (by positivity) _) aux_C_gaussianBumpEstimate_zero_pos
    have hqG : ((2 * Real.pi)⁻¹ : ℝ) ^ 3 * C_gaussianBumpEstimate 0 ≤
        (1 / 6 : ℝ) ^ 3 * 81 :=
      mul_le_mul hq3 hG0 (aux_C_gaussianBumpEstimate_nonneg 0) (by norm_num)
    calc
      ((2 * Real.pi)⁻¹ : ℝ) ^ 3 * C_gaussianBumpEstimate 0 * C_faaDiBruno 3 =
          (((2 * Real.pi)⁻¹ : ℝ) ^ 3 * C_gaussianBumpEstimate 0) * C_faaDiBruno 3 := by
        ring
      _ < (((2 * Real.pi)⁻¹ : ℝ) ^ 3 * C_gaussianBumpEstimate 0) * 255689986286813184 :=
        mul_lt_mul_of_pos_left hF3 hqGpos
      _ ≤ ((1 / 6 : ℝ) ^ 3 * 81) * 255689986286813184 :=
        mul_le_mul_of_nonneg_right hqG (by norm_num)
      _ = (1 / 6 : ℝ) ^ 3 * 81 * 255689986286813184 := by ring
  have hBraw : ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 1 *
      C_faaDiBruno 2 ≤ (1 / 6 : ℝ) ^ 2 * 95 * 8852889600 := by
    have hqG : ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 1 ≤
        (1 / 6 : ℝ) ^ 2 * 95 :=
      mul_le_mul hq2 hG1 (aux_C_gaussianBumpEstimate_nonneg 1) (by norm_num)
    calc
      ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 1 * C_faaDiBruno 2 ≤
          ((1 / 6 : ℝ) ^ 2 * 95) * C_faaDiBruno 2 :=
        mul_le_mul_of_nonneg_right hqG (aux_C_faaDiBruno_nonneg 2)
      _ ≤ ((1 / 6 : ℝ) ^ 2 * 95) * 8852889600 :=
        mul_le_mul_of_nonneg_left hF2 (by norm_num)
      _ = (1 / 6 : ℝ) ^ 2 * 95 * 8852889600 := by ring
  have hB : 3 * ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 1 *
      C_faaDiBruno 2 ≤ 3 * (1 / 6 : ℝ) ^ 2 * 95 * 8852889600 := by
    calc
      3 * ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 1 * C_faaDiBruno 2 =
          3 * (((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 1 * C_faaDiBruno 2) := by
        ring
      _ ≤ 3 * ((1 / 6 : ℝ) ^ 2 * 95 * 8852889600) :=
        mul_le_mul_of_nonneg_left hBraw (by norm_num)
      _ = 3 * (1 / 6 : ℝ) ^ 2 * 95 * 8852889600 := by ring
  have hCraw : (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 2 * C_faaDiBruno 1 ≤
      (1 / 6 : ℝ) * 124 * 27648 := by
    have hqG : (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 2 ≤ (1 / 6 : ℝ) * 124 :=
      mul_le_mul hq hG2 (aux_C_gaussianBumpEstimate_nonneg 2) (by norm_num)
    calc
      (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 2 * C_faaDiBruno 1 ≤
          ((1 / 6 : ℝ) * 124) * C_faaDiBruno 1 :=
        mul_le_mul_of_nonneg_right hqG (aux_C_faaDiBruno_nonneg 1)
      _ ≤ ((1 / 6 : ℝ) * 124) * 27648 :=
        mul_le_mul_of_nonneg_left hF1 (by norm_num)
      _ = (1 / 6 : ℝ) * 124 * 27648 := by ring
  have hC : 3 * (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 2 * C_faaDiBruno 1 ≤
      3 * (1 / 6 : ℝ) * 124 * 27648 := by
    calc
      3 * (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 2 * C_faaDiBruno 1 =
          3 * ((2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 2 * C_faaDiBruno 1) := by ring
      _ ≤ 3 * ((1 / 6 : ℝ) * 124 * 27648) :=
        mul_le_mul_of_nonneg_left hCraw (by norm_num)
      _ = 3 * (1 / 6 : ℝ) * 124 * 27648 := by ring
  have hD : C_gaussianBumpEstimate 3 * C_faaDiBruno 0 ≤ 176 * 72 :=
    mul_le_mul hG3 hF0 (aux_C_faaDiBruno_nonneg 0) (by norm_num)
  rw [aux_C_secondGaussianEstimate_three_eq]
  calc
    8 * (((2 * Real.pi)⁻¹ : ℝ) ^ 3 * C_gaussianBumpEstimate 0 * C_faaDiBruno 3 +
        3 * ((2 * Real.pi)⁻¹ : ℝ) ^ 2 * C_gaussianBumpEstimate 1 * C_faaDiBruno 2 +
        3 * (2 * Real.pi)⁻¹ * C_gaussianBumpEstimate 2 * C_faaDiBruno 1 +
        C_gaussianBumpEstimate 3 * C_faaDiBruno 0) <
        8 * ((1 / 6 : ℝ) ^ 3 * 81 * 255689986286813184 +
          3 * (1 / 6 : ℝ) ^ 2 * 95 * 8852889600 +
          3 * (1 / 6 : ℝ) * 124 * 27648 + 176 * 72) :=
      mul_lt_mul_of_pos_left
        (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le hA hB) hC) hD)
        (by norm_num)
    _ = 767070519557262336 := by norm_num

theorem aux_C_secondGaussianEstimate_three_lt :
    C_secondGaussianEstimate 3 < (2 : ℝ) ^ 60 := by
  calc
    C_secondGaussianEstimate 3 < 767070519557262336 := aux_C_secondGaussianEstimate_three_lt_value
    _ < (2 : ℝ) ^ 60 := by norm_num

/-- Source label `\ref{constant second gaussian estimate}`. -/
theorem constantSecondGaussianEstimate (N : ℕ) :
    C_secondGaussianEstimate N ≤ (2 : ℝ) ^ (20 * (N + 1) ^ 3) ∧
      C_secondGaussianEstimate 0 < (2 : ℝ) ^ 16 ∧ C_secondGaussianEstimate 1 < (2 : ℝ) ^ 22 ∧
        C_secondGaussianEstimate 2 < (2 : ℝ) ^ 38 ∧ C_secondGaussianEstimate 3 < (2 : ℝ) ^ 60 := by
  exact ⟨aux_C_secondGaussianEstimate_bound N, aux_C_secondGaussianEstimate_zero_lt,
    aux_C_secondGaussianEstimate_one_lt, aux_C_secondGaussianEstimate_two_lt,
    aux_C_secondGaussianEstimate_three_lt⟩

/-- Source label `\ref{L:gaussian-bump-decomposition}`; frequency-side auxiliary definition for
the public theorem `gaussianBumpDecomposition`. -/
def fourScaleGaussianRhoFrequency (phiHat : ℝ → ℂ)
    (muMinus muPlus lambdaMinus lambdaPlus nu : ℝ) : ℝ → ℂ := fun xi =>
  (phiHat (lambdaMinus * xi) - phiHat (lambdaPlus * xi)) *
    (Real.rpow (Gaussians.gaussian (muMinus * xi) - Gaussians.gaussian (muPlus * xi)) nu : ℂ)

/-- Source label `\ref{L:gaussian-bump-decomposition}`; inverse-transform auxiliary definition
for the public theorem `gaussianBumpDecomposition`. -/
def fourScaleGaussianRho (phiHat : ℝ → ℂ)
    (muMinus muPlus lambdaMinus lambdaPlus nu : ℝ) : ℝ → ℂ :=
  FourierTransformInv.fourierInv
    (fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu)

/-- Source label `\ref{L:gaussian-bump-decomposition}`; the first frequency component used by
the public theorem `gaussianBumpDecomposition`. -/
def fourScaleGaussianVarRho0Frequency (phiHat : ℝ → ℂ)
    (muMinus lambdaMinus nu : ℝ) : ℝ → ℂ := fun xi =>
  (Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹ *
    phiHat (lambdaMinus * xi)

/-- Source label `\ref{L:gaussian-bump-decomposition}`; the second frequency component used by
the public theorem `gaussianBumpDecomposition`. -/
def fourScaleGaussianVarRho1Frequency (phiHat : ℝ → ℂ)
    (muMinus lambdaPlus nu : ℝ) : ℝ → ℂ := fun xi =>
  -((Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹ *
    phiHat (lambdaPlus * xi))

/-- Source label `\ref{L:gaussian-bump-decomposition}`; the third frequency component used by
the public theorem `gaussianBumpDecomposition`. -/
def fourScaleGaussianVarRho2Frequency (phiHat : ℝ → ℂ)
    (muMinus muPlus lambdaMinus lambdaPlus nu : ℝ) : ℝ → ℂ := fun xi =>
  (Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹ *
    (phiHat (lambdaMinus * xi) - phiHat (lambdaPlus * xi)) *
      ((Real.rpow
        (1 - Gaussians.gaussian (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * xi)) nu - 1 : ℝ) : ℂ)

/-- Source label `\ref{L:gaussian-bump-decomposition}`; inverse-transform auxiliary definition
for the public theorem `gaussianBumpDecomposition`. -/
def fourScaleGaussianVarRho0 (phiHat : ℝ → ℂ)
    (muMinus lambdaMinus nu : ℝ) : ℝ → ℂ :=
  FourierTransformInv.fourierInv
    (fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu)

/-- Source label `\ref{L:gaussian-bump-decomposition}`; inverse-transform auxiliary definition
for the public theorem `gaussianBumpDecomposition`. -/
def fourScaleGaussianVarRho1 (phiHat : ℝ → ℂ)
    (muMinus lambdaPlus nu : ℝ) : ℝ → ℂ :=
  FourierTransformInv.fourierInv
    (fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu)

/-- Source label `\ref{L:gaussian-bump-decomposition}`; inverse-transform auxiliary definition
for the public theorem `gaussianBumpDecomposition`. -/
def fourScaleGaussianVarRho2 (phiHat : ℝ → ℂ)
    (muMinus muPlus lambdaMinus lambdaPlus nu : ℝ) : ℝ → ℂ :=
  FourierTransformInv.fourierInv
    (fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu)

/-- Auxiliary for gaussianBumpDecomposition: compact support is preserved by a positive
frequency rescaling. -/
theorem aux_gaussianBumpDecomposition_scaledSupport {f : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hsupp : tsupport f ⊆ Set.Icc (-1 : ℝ) 1) :
    HasCompactSupport (fun x : ℝ => f (a * x)) := by
  apply HasCompactSupport.intro (K := Set.Icc (-(a⁻¹)) a⁻¹)
  · exact isCompact_Icc
  · intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hx
    have hax : a * x ∈ Set.Icc (-1 : ℝ) 1 := hsupp hmem
    constructor
    · rw [show -(a⁻¹) = (-1 : ℝ) / a by field_simp]
      apply (div_le_iff₀ ha).mpr
      simpa [mul_comm] using hax.1
    · rw [show a⁻¹ = (1 : ℝ) / a by field_simp]
      apply (le_div_iff₀ ha).mpr
      simpa [mul_comm] using hax.2

/-- Auxiliary for gaussianBumpDecomposition: the Fourier transform of a W₀ function is
continuous. -/
theorem aux_gaussianBumpDecomposition_phiHat_continuous
    (phi phiHat : ℝ → ℂ) (hphi : MemW0 phi)
    (hphiHat : phiHat = FourierTransform.fourier phi) : Continuous phiHat := by
  rw [hphiHat]
  change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) phi)
  apply VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
  · fun_prop
  · refine hphi.2.mono hphi.1.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (aux_wienerEnvelope_nonneg hphi.1 zero_le_one x)]
    exact aux_norm_le_wienerEnvelope hphi.1 zero_le_one x

/-- Auxiliary for gaussianBumpDecomposition: the plateau cancels the scaled Fourier
difference near zero. -/
theorem aux_gaussianBumpDecomposition_phiDifference_eventuallyEq_zero (phiHat : ℝ → ℂ)
    (hplateau : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat xi = 1)
    (a b : ℝ) :
    (fun xi : ℝ => phiHat (a * xi) - phiHat (b * xi)) =ᶠ[nhds 0] 0 := by
  have hI : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ nhds (0 : ℝ) := by
    apply Ioo_mem_nhds <;> norm_num
  have ha : ContinuousAt (fun xi : ℝ => a * xi) 0 := by fun_prop
  have hb : ContinuousAt (fun xi : ℝ => b * xi) 0 := by fun_prop
  have hIa : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ nhds (a * 0) := by simpa using hI
  have hIb : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ nhds (b * 0) := by simpa using hI
  have ha' := ha.preimage_mem_nhds hIa
  have hb' := hb.preimage_mem_nhds hIb
  filter_upwards [ha', hb'] with xi hxa hxb
  change a * xi ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) at hxa
  change b * xi ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) at hxb
  rw [hplateau _ ⟨hxa.1.le, hxa.2.le⟩, hplateau _ ⟨hxb.1.le, hxb.2.le⟩]
  norm_num

/-- Auxiliary for gaussianBumpDecomposition: the Gaussian difference is positive away from zero. -/
theorem aux_gaussianBumpDecomposition_gaussianDifference_pos {a b x : ℝ} (ha : 0 < a)
    (hab : 2 * a ≤ b) (hx : x ≠ 0) :
    0 < Gaussians.gaussian (a * x) - Gaussians.gaussian (b * x) := by
  have hab' : a < b := by linarith
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have habsq : a ^ 2 < b ^ 2 := by nlinarith
  have hsq : (a * x) ^ 2 < (b * x) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_lt_mul_of_pos_right habsq hx2
  apply sub_pos.mpr
  change Real.exp (-Real.pi * (b * x) ^ 2) < Real.exp (-Real.pi * (a * x) ^ 2)
  rw [Real.exp_lt_exp]
  nlinarith [Real.pi_pos]

/-- Auxiliary for gaussianBumpDecomposition: the complementary Gaussian factor is positive
away from zero. -/
theorem aux_gaussianBumpDecomposition_oneSubGaussian_pos {t x : ℝ} (ht : 0 < t) (hx : x ≠ 0) :
    0 < 1 - Gaussians.gaussian (t * x) := by
  apply sub_pos.mpr
  change Real.exp (-Real.pi * (t * x) ^ 2) < 1
  rw [← Real.exp_zero, Real.exp_lt_exp]
  have htx : t * x ≠ 0 := mul_ne_zero (ne_of_gt ht) hx
  nlinarith [Real.pi_pos, sq_pos_of_ne_zero htx]

/-- Auxiliary for gaussianBumpDecomposition: continuity of the Gaussian-difference real
power away from zero. -/
theorem aux_gaussianBumpDecomposition_gaussianDifference_rpow_continuousAt {a b nu x : ℝ}
    (ha : 0 < a) (hab : 2 * a ≤ b) (hx : x ≠ 0) :
    ContinuousAt (fun y : ℝ =>
      ((Gaussians.gaussian (a * y) - Gaussians.gaussian (b * y)) ^ nu : ℝ)) x := by
  have hdiff : ContinuousAt
      (fun y : ℝ => Gaussians.gaussian (a * y) - Gaussians.gaussian (b * y)) x :=
    ((gaussian_continuous.comp (by fun_prop)).sub
      (gaussian_continuous.comp (by fun_prop))).continuousAt
  have houter := Real.continuousAt_rpow_const
    (Gaussians.gaussian (a * x) - Gaussians.gaussian (b * x)) nu
    (Or.inl (ne_of_gt (aux_gaussianBumpDecomposition_gaussianDifference_pos ha hab hx)))
  simpa only [Function.comp_def] using houter.comp
    (f := fun y : ℝ => Gaussians.gaussian (a * y) - Gaussians.gaussian (b * y)) hdiff

/-- Auxiliary for gaussianBumpDecomposition: continuity of the remainder real power away
from zero. -/
theorem aux_gaussianBumpDecomposition_oneSubGaussian_rpow_continuousAt {t nu x : ℝ}
    (ht : 0 < t) (hx : x ≠ 0) :
    ContinuousAt (fun y : ℝ => (1 - Gaussians.gaussian (t * y)) ^ nu) x := by
  have hdiff : ContinuousAt (fun y : ℝ => 1 - Gaussians.gaussian (t * y)) x :=
    (continuous_const.sub (gaussian_continuous.comp (by fun_prop))).continuousAt
  have houter := Real.continuousAt_rpow_const (1 - Gaussians.gaussian (t * x)) nu
    (Or.inl (ne_of_gt (aux_gaussianBumpDecomposition_oneSubGaussian_pos ht hx)))
  simpa only [Function.comp_def] using houter.comp
    (f := fun y : ℝ => 1 - Gaussians.gaussian (t * y)) hdiff

/-- Auxiliary for gaussianBumpDecomposition: the defining frequency multiplier is continuous. -/
theorem aux_gaussianBumpDecomposition_rhoFrequency_continuous (phiHat : ℝ → ℂ)
    (hphi : Continuous phiHat)
    (hplateau : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat xi = 1)
    {muMinus muPlus lambdaMinus lambdaPlus nu : ℝ}
    (hmuMinus : 0 < muMinus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧
      2 * lambdaMinus ≤ lambdaPlus ∧ lambdaPlus ≤ muPlus) :
    Continuous (fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) := by
  rw [continuous_iff_continuousAt]
  intro xi
  by_cases hxi : xi = 0
  · subst xi
    have hzero := aux_gaussianBumpDecomposition_phiDifference_eventuallyEq_zero
      phiHat hplateau lambdaMinus lambdaPlus
    have hfreq :
        fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu =ᶠ[nhds 0]
          fun _ : ℝ => 0 := by
      filter_upwards [hzero] with y hy
      simp [fourScaleGaussianRhoFrequency, hy]
    exact continuousAt_const.congr_of_eventuallyEq hfreq
  · have hD : ContinuousAt
        (fun y : ℝ => phiHat (lambdaMinus * y) - phiHat (lambdaPlus * y)) xi :=
      ((hphi.comp (by fun_prop)).sub (hphi.comp (by fun_prop))).continuousAt
    have hmu : 2 * muMinus ≤ muPlus := hscales.1.trans (hscales.2.1.trans hscales.2.2)
    have hreal := aux_gaussianBumpDecomposition_gaussianDifference_rpow_continuousAt
      hmuMinus hmu hxi (nu := nu)
    have hG : ContinuousAt
        (fun y : ℝ =>
          ((Gaussians.gaussian (muMinus * y) - Gaussians.gaussian (muPlus * y)) ^ nu : ℝ)) xi :=
      hreal
    have hGc : ContinuousAt
        (fun y : ℝ =>
          (((Gaussians.gaussian (muMinus * y) -
            Gaussians.gaussian (muPlus * y)) ^ nu : ℝ) : ℂ)) xi := by
      simpa only [Function.comp_def] using Complex.continuous_ofReal.continuousAt.comp
        (f := fun y : ℝ =>
          ((Gaussians.gaussian (muMinus * y) -
            Gaussians.gaussian (muPlus * y)) ^ nu : ℝ)) hG
    change ContinuousAt (fun y : ℝ =>
      (phiHat (lambdaMinus * y) - phiHat (lambdaPlus * y)) *
        (((Gaussians.gaussian (muMinus * y) -
          Gaussians.gaussian (muPlus * y)) ^ nu : ℝ) : ℂ)) xi
    exact hD.mul hGc

/-- Auxiliary for gaussianBumpDecomposition: reciprocals of scaled Gaussians are continuous. -/
theorem aux_gaussianBumpDecomposition_inverseGaussianScaled_continuous (a : ℝ) :
    Continuous (fun x : ℝ => (Gaussians.gaussian (a * x) : ℂ)⁻¹) := by
  have hbase : Continuous (fun x : ℝ => (Gaussians.gaussian (a * x) : ℂ)) :=
    Complex.continuous_ofReal.comp (gaussian_continuous.comp (by fun_prop))
  apply hbase.inv₀
  intro x
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (aux_gaussian_pos (a * x)))

/-- Auxiliary for gaussianBumpDecomposition: the first frequency component is continuous. -/
theorem aux_gaussianBumpDecomposition_varRho0Frequency_continuous
    (phiHat : ℝ → ℂ) (hphi : Continuous phiHat) (muMinus lambdaMinus nu : ℝ) :
    Continuous (fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu) := by
  change Continuous (fun x : ℝ =>
    (Gaussians.gaussian (muMinus * Real.sqrt |nu| * x) : ℂ)⁻¹ *
      phiHat (lambdaMinus * x))
  exact (aux_gaussianBumpDecomposition_inverseGaussianScaled_continuous
    (muMinus * Real.sqrt |nu|)).mul (hphi.comp (by fun_prop))

/-- Auxiliary for gaussianBumpDecomposition: the second frequency component is continuous. -/
theorem aux_gaussianBumpDecomposition_varRho1Frequency_continuous
    (phiHat : ℝ → ℂ) (hphi : Continuous phiHat) (muMinus lambdaPlus nu : ℝ) :
    Continuous (fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu) := by
  change Continuous (fun x : ℝ => -
    ((Gaussians.gaussian (muMinus * Real.sqrt |nu| * x) : ℂ)⁻¹ *
      phiHat (lambdaPlus * x)))
  exact ((aux_gaussianBumpDecomposition_inverseGaussianScaled_continuous
    (muMinus * Real.sqrt |nu|)).mul (hphi.comp (by fun_prop))).neg

/-- Auxiliary for gaussianBumpDecomposition: the third frequency component is continuous. -/
theorem aux_gaussianBumpDecomposition_varRho2Frequency_continuous (phiHat : ℝ → ℂ)
    (hphi : Continuous phiHat)
    (hplateau : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat xi = 1)
    {muMinus muPlus lambdaMinus lambdaPlus nu : ℝ}
    (hmuMinus : 0 < muMinus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧
      2 * lambdaMinus ≤ lambdaPlus ∧ lambdaPlus ≤ muPlus) :
    Continuous
      (fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) := by
  have hmu : 2 * muMinus ≤ muPlus := hscales.1.trans (hscales.2.1.trans hscales.2.2)
  have hmuplus : muMinus < muPlus := by linarith
  have hrad : 0 < muPlus ^ 2 - muMinus ^ 2 := by nlinarith
  have ht : 0 < Real.sqrt (muPlus ^ 2 - muMinus ^ 2) := Real.sqrt_pos.2 hrad
  rw [continuous_iff_continuousAt]
  intro xi
  by_cases hxi : xi = 0
  · subst xi
    have hzero := aux_gaussianBumpDecomposition_phiDifference_eventuallyEq_zero
      phiHat hplateau lambdaMinus lambdaPlus
    have hfreq :
        fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu
          =ᶠ[nhds 0] fun _ : ℝ => 0 := by
      filter_upwards [hzero] with y hy
      simp [fourScaleGaussianVarRho2Frequency, hy]
    exact continuousAt_const.congr_of_eventuallyEq hfreq
  · have hD : ContinuousAt
        (fun y : ℝ => phiHat (lambdaMinus * y) - phiHat (lambdaPlus * y)) xi :=
      ((hphi.comp (by fun_prop)).sub (hphi.comp (by fun_prop))).continuousAt
    have hinv : ContinuousAt (fun y : ℝ =>
        (Gaussians.gaussian (muMinus * Real.sqrt |nu| * y) : ℂ)⁻¹) xi :=
      (aux_gaussianBumpDecomposition_inverseGaussianScaled_continuous
        (muMinus * Real.sqrt |nu|)).continuousAt
    have hreal :=
      aux_gaussianBumpDecomposition_oneSubGaussian_rpow_continuousAt ht hxi (nu := nu)
    have hS : ContinuousAt
        (fun y : ℝ =>
          (((1 - Gaussians.gaussian
            (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * y)) ^ nu - 1 : ℝ) : ℂ)) xi := by
      have hsub : ContinuousAt (fun y : ℝ =>
          (1 - Gaussians.gaussian
            (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * y)) ^ nu - 1) xi :=
        hreal.sub continuousAt_const
      simpa only [Function.comp_def] using Complex.continuous_ofReal.continuousAt.comp
        (f := fun y : ℝ =>
          (1 - Gaussians.gaussian
            (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * y)) ^ nu - 1) hsub
    change ContinuousAt (fun y : ℝ =>
      (Gaussians.gaussian (muMinus * Real.sqrt |nu| * y) : ℂ)⁻¹ *
        (phiHat (lambdaMinus * y) - phiHat (lambdaPlus * y)) *
        (((1 - Gaussians.gaussian
          (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * y)) ^ nu - 1 : ℝ) : ℂ)) xi
    exact (hinv.mul hD).mul hS

/-- Auxiliary for gaussianBumpDecomposition: the scale assumptions imply positivity of
lambdaMinus. -/
theorem aux_gaussianBumpDecomposition_lambdaMinus_pos {muMinus lambdaMinus : ℝ}
    (hmuMinus : 0 < muMinus) (hscale : 2 * muMinus ≤ 2 * lambdaMinus) :
    0 < lambdaMinus := by
  linarith

/-- Auxiliary for gaussianBumpDecomposition: the scale assumptions imply positivity of
lambdaPlus. -/
theorem aux_gaussianBumpDecomposition_lambdaPlus_pos {muMinus lambdaMinus lambdaPlus : ℝ}
    (hmuMinus : 0 < muMinus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧ 2 * lambdaMinus ≤ lambdaPlus) :
    0 < lambdaPlus := by
  have hminus := aux_gaussianBumpDecomposition_lambdaMinus_pos hmuMinus hscales.1
  linarith

/-- Auxiliary for gaussianBumpDecomposition: the Fourier-side difference has compact support. -/
theorem aux_gaussianBumpDecomposition_phiDifference_compactSupport (phiHat : ℝ → ℂ)
    {lambdaMinus lambdaPlus : ℝ} (hlambdaMinus : 0 < lambdaMinus)
    (hlambdaPlus : 0 < lambdaPlus) (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1) :
    HasCompactSupport (fun xi : ℝ => phiHat (lambdaMinus * xi) - phiHat (lambdaPlus * xi)) := by
  have hminus := aux_gaussianBumpDecomposition_scaledSupport hlambdaMinus hsupp
  have hplus := aux_gaussianBumpDecomposition_scaledSupport hlambdaPlus hsupp
  change HasCompactSupport
    ((fun xi : ℝ => phiHat (lambdaMinus * xi)) - fun xi : ℝ => phiHat (lambdaPlus * xi))
  exact hminus.sub hplus

/-- Auxiliary for gaussianBumpDecomposition: the defining frequency multiplier has compact
support. -/
theorem aux_gaussianBumpDecomposition_rhoFrequency_compactSupport (phiHat : ℝ → ℂ)
    {lambdaMinus lambdaPlus : ℝ} (hlambdaMinus : 0 < lambdaMinus)
    (hlambdaPlus : 0 < lambdaPlus) (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (muMinus muPlus nu : ℝ) :
    HasCompactSupport
      (fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) := by
  have hD := aux_gaussianBumpDecomposition_phiDifference_compactSupport
    phiHat hlambdaMinus hlambdaPlus hsupp
  change HasCompactSupport ((fun xi : ℝ =>
    phiHat (lambdaMinus * xi) - phiHat (lambdaPlus * xi)) * fun xi : ℝ =>
      (((Gaussians.gaussian (muMinus * xi) - Gaussians.gaussian (muPlus * xi)) ^ nu : ℝ) : ℂ))
  exact hD.mul_right

/-- Auxiliary for gaussianBumpDecomposition: the first frequency component has compact support. -/
theorem aux_gaussianBumpDecomposition_varRho0Frequency_compactSupport (phiHat : ℝ → ℂ)
    {lambdaMinus : ℝ} (hlambdaMinus : 0 < lambdaMinus)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1) (muMinus nu : ℝ) :
    HasCompactSupport (fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu) := by
  have h := aux_gaussianBumpDecomposition_scaledSupport hlambdaMinus hsupp
  change HasCompactSupport ((fun xi : ℝ =>
    (Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹) *
      fun xi : ℝ => phiHat (lambdaMinus * xi))
  exact h.mul_left

/-- Auxiliary for gaussianBumpDecomposition: the second frequency component has compact support. -/
theorem aux_gaussianBumpDecomposition_varRho1Frequency_compactSupport (phiHat : ℝ → ℂ)
    {lambdaPlus : ℝ} (hlambdaPlus : 0 < lambdaPlus)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1) (muMinus nu : ℝ) :
    HasCompactSupport (fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu) := by
  have h := aux_gaussianBumpDecomposition_scaledSupport hlambdaPlus hsupp
  change HasCompactSupport (-((fun xi : ℝ =>
    (Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹) *
      fun xi : ℝ => phiHat (lambdaPlus * xi)))
  exact h.mul_left.neg

/-- Auxiliary for gaussianBumpDecomposition: the third frequency component has compact support. -/
theorem aux_gaussianBumpDecomposition_varRho2Frequency_compactSupport (phiHat : ℝ → ℂ)
    {lambdaMinus lambdaPlus : ℝ} (hlambdaMinus : 0 < lambdaMinus)
    (hlambdaPlus : 0 < lambdaPlus) (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (muMinus muPlus nu : ℝ) :
    HasCompactSupport
      (fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) := by
  have hD := aux_gaussianBumpDecomposition_phiDifference_compactSupport
    phiHat hlambdaMinus hlambdaPlus hsupp
  change HasCompactSupport (((fun xi : ℝ =>
    (Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹) *
      (fun xi : ℝ => phiHat (lambdaMinus * xi) - phiHat (lambdaPlus * xi))) *
      fun xi : ℝ =>
        (((1 - Gaussians.gaussian
          (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * xi)) ^ nu - 1 : ℝ) : ℂ))
  exact (hD.mul_left).mul_right

/-- Auxiliary for gaussianBumpDecomposition: inverse Fourier transforms of integrable
functions are continuous. -/
theorem aux_gaussianBumpDecomposition_fourierInv_continuous (f : ℝ → ℂ) (hf : Integrable f) :
    Continuous (FourierTransformInv.fourierInv f) := by
  change Continuous (VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) f)
  apply VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
  · fun_prop
  · exact hf

/-- Auxiliary for gaussianBumpDecomposition: a real Gaussian power rescales its argument. -/
theorem aux_gaussianBumpDecomposition_gaussian_rpow (a s x : ℝ) (hs : 0 ≤ s) :
    Gaussians.gaussian (a * x) ^ s = Gaussians.gaussian (a * Real.sqrt s * x) := by
  rw [Real.rpow_def_of_pos (aux_gaussian_pos _)]
  simp only [Gaussians.gaussian, Codex.Preliminaries.Notation.gaussian, Real.log_exp]
  congr 1
  simp only [mul_pow]
  rw [Real.sq_sqrt hs]
  ring

/-- Auxiliary for gaussianBumpDecomposition: this factors a Gaussian at a larger scale. -/
theorem aux_gaussianBumpDecomposition_gaussian_split {a b x : ℝ} (h : 0 ≤ b ^ 2 - a ^ 2) :
    Gaussians.gaussian (b * x) =
      Gaussians.gaussian (a * x) *
        Gaussians.gaussian (Real.sqrt (b ^ 2 - a ^ 2) * x) := by
  change Real.exp (-Real.pi * (b * x) ^ 2) =
    Real.exp (-Real.pi * (a * x) ^ 2) *
      Real.exp (-Real.pi * (Real.sqrt (b ^ 2 - a ^ 2) * x) ^ 2)
  rw [← Real.exp_add]
  congr 1
  simp only [mul_pow]
  rw [Real.sq_sqrt h]
  ring

/-- Auxiliary for gaussianBumpDecomposition: this factors the real power of the Gaussian
difference. -/
theorem aux_gaussianBumpDecomposition_gaussianDifference_rpow {a b nu x : ℝ}
    (h : 0 ≤ b ^ 2 - a ^ 2) (hnu : nu ≤ 0) :
    (Gaussians.gaussian (a * x) - Gaussians.gaussian (b * x)) ^ nu =
      (Gaussians.gaussian (a * Real.sqrt |nu| * x))⁻¹ *
        (1 - Gaussians.gaussian (Real.sqrt (b ^ 2 - a ^ 2) * x)) ^ nu := by
  have hsplit : Gaussians.gaussian (a * x) - Gaussians.gaussian (b * x) =
      Gaussians.gaussian (a * x) *
        (1 - Gaussians.gaussian (Real.sqrt (b ^ 2 - a ^ 2) * x)) := by
    rw [aux_gaussianBumpDecomposition_gaussian_split h]
    ring
  have hnu' : nu = -|nu| := by
    rw [abs_of_nonpos hnu]
    ring
  have hpow : Gaussians.gaussian (a * x) ^ nu =
      (Gaussians.gaussian (a * Real.sqrt |nu| * x))⁻¹ := by
    calc
      Gaussians.gaussian (a * x) ^ nu = Gaussians.gaussian (a * x) ^ (-|nu|) := by
        conv_lhs => rw [hnu']
      _ = (Gaussians.gaussian (a * x) ^ |nu|)⁻¹ :=
        Real.rpow_neg (aux_gaussian_pos _).le _
      _ = (Gaussians.gaussian (a * Real.sqrt |nu| * x))⁻¹ := by
        rw [aux_gaussianBumpDecomposition_gaussian_rpow a |nu| x (abs_nonneg nu)]
  rw [hsplit, Real.mul_rpow (aux_gaussian_pos _).le
    (aux_one_sub_gaussian_nonneg _)]
  rw [hpow]

/-- Auxiliary for gaussianBumpDecomposition: the three frequency components sum to the
defining multiplier. -/
theorem aux_gaussianBumpDecomposition_frequency_decomposition (phiHat : ℝ → ℂ)
    {muMinus muPlus lambdaMinus lambdaPlus nu : ℝ}
    (hmuMinus : 0 < muMinus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧
      2 * lambdaMinus ≤ lambdaPlus ∧ lambdaPlus ≤ muPlus)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu =
      fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu +
        fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu +
          fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu := by
  funext xi
  have hmu : muMinus < muPlus := by
    have : 2 * muMinus ≤ muPlus := hscales.1.trans (hscales.2.1.trans hscales.2.2)
    linarith
  have hrad : 0 ≤ muPlus ^ 2 - muMinus ^ 2 := by nlinarith
  have hfactorReal := aux_gaussianBumpDecomposition_gaussianDifference_rpow
    (a := muMinus) (b := muPlus) (nu := nu) (x := xi) hrad hnu.2.le
  have hfactor :
      (Real.rpow (Gaussians.gaussian (muMinus * xi) - Gaussians.gaussian (muPlus * xi)) nu : ℂ) =
        (Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹ *
          ((Real.rpow
            (1 - Gaussians.gaussian
              (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * xi)) nu : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    exact congrArg (fun z : ℝ => (z : ℂ)) hfactorReal
  change
    (phiHat (lambdaMinus * xi) - phiHat (lambdaPlus * xi)) *
        (Real.rpow
          (Gaussians.gaussian (muMinus * xi) - Gaussians.gaussian (muPlus * xi)) nu : ℂ) =
      (Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹ * phiHat (lambdaMinus * xi) +
        -((Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹ *
          phiHat (lambdaPlus * xi)) +
          (Gaussians.gaussian (muMinus * Real.sqrt |nu| * xi) : ℂ)⁻¹ *
            (phiHat (lambdaMinus * xi) - phiHat (lambdaPlus * xi)) *
              (((Real.rpow
                (1 - Gaussians.gaussian
                  (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * xi)) nu : ℝ) - 1 : ℝ) : ℂ)
  rw [hfactor]
  push_cast
  ring

/-- Auxiliary for gaussianBumpDecomposition: inverse Fourier transform preserves addition
for integrable functions. -/
theorem aux_gaussianBumpDecomposition_inverseFourier_add (f g : ℝ → ℂ) (hf : Integrable f)
    (hg : Integrable g) :
    FourierTransformInv.fourierInv (f + g) =
      FourierTransformInv.fourierInv f + FourierTransformInv.fourierInv g := by
  funext x
  have hphaseCont : Continuous (fun xi : ℝ => 𝐞 ⟪xi, x⟫) := by
    apply Real.continuous_fourierChar.comp
    fun_prop
  have hphaseInt {u : ℝ → ℂ} (hu : Integrable u) :
      Integrable (fun xi : ℝ => 𝐞 ⟪xi, x⟫ • u xi) := by
    rw [← integrable_norm_iff]
    · simpa only [Circle.norm_smul] using hu.norm
    · exact hphaseCont.aestronglyMeasurable.smul hu.aestronglyMeasurable
  rw [Real.fourierInv_eq]
  change (∫ xi : ℝ, 𝐞 ⟪xi, x⟫ • (f + g) xi) =
    FourierTransformInv.fourierInv f x + FourierTransformInv.fourierInv g x
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  rw [← integral_add (hphaseInt hf) (hphaseInt hg)]
  apply integral_congr_ae
  filter_upwards [] with xi
  rw [Pi.add_apply, smul_add]

/--
\begin{lemma}\label{L:gaussian-bump-decomposition}
Let $\phi$ be a $W_0(\R)$ function such that
$\widehat{\phi}$ is supported in $[-1,1]$ and equal to $1$ on $[-1/2,1/2]$.
Let $\mu_\pm,\lambda_\pm\in\mathbb R$ be positive and satisfy
\begin{equation}\label{E:assumption-on-mu-lambda}
2\mu_-\le 2\lambda_-\le \lambda_+\le \mu_+,
\end{equation}
and let $\nu\in [-1,0)$.

Define a function $\rho$ by
\begin{equation}\label{E:definition-rho}
\rho = \mathcal F^{-1}\left(\xi \mapsto
  (\widehat{\phi}(\lambda_-\xi) - \widehat{\phi}(\lambda_+\xi))
  (\g(\mu_- \xi)-\g(\mu_+\xi))^{\nu}\right).
\end{equation}
Also, for $\xi \in \R$ we define
\begin{equation}\label{auto:four-scale-Gaussian-first-multiplier}
    \varrho_0(\xi)=(\g(\mu_{-}|\nu|^{1/2}\xi))^{-1}\widehat{\phi}(\lambda_{-}\xi)
\end{equation}
\begin{equation}\label{auto:four-scale-Gaussian-second-multiplier}
    \varrho_1(\xi)=-(\g(\mu_{-}|\nu|^{1/2}\xi))^{-1}\widehat{\phi}(\lambda_{+}\xi)
\end{equation}
\begin{equation}\label{auto:four-scale-Gaussian-remainder-multiplier}
    \varrho_2(\xi)=(\g(\mu_{-}|\nu|^{1/2}\xi))^{-1}
      \left(\widehat{\phi}(\lambda_{-}\xi)-\widehat{\phi}(\lambda_{+}\xi)\right)
      \left((1-\g(t\xi))^{\nu} -1\right)
\end{equation}
with $t=\sqrt{\mu_{+}^2-\mu_{-}^2}$.
Then $\rho$ is a well-defined continuous function and
\begin{equation}\label{E:decomposition-rho}
\rho=\sum_{l\in [3)} \mathcal F^{-1} (\varrho_l).
\end{equation}
\end{lemma}
-/
theorem gaussianBumpDecomposition (phi phiHat : ℝ → ℂ) (hphi : MemW0 phi)
    (hphiHat : phiHat = FourierTransform.fourier phi)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hplateau : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat xi = 1)
    {muMinus muPlus lambdaMinus lambdaPlus nu : ℝ}
    (hmuMinus : 0 < muMinus) (_hmuPlus : 0 < muPlus)
    (_hlambdaMinus : 0 < lambdaMinus) (_hlambdaPlus : 0 < lambdaPlus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧
      2 * lambdaMinus ≤ lambdaPlus ∧ lambdaPlus ≤ muPlus)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    Continuous (fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu) ∧
      fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu =
        fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu +
          fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu +
            fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu := by
  have hphiCont : Continuous phiHat :=
    aux_gaussianBumpDecomposition_phiHat_continuous phi phiHat hphi hphiHat
  have hlambdaMinus : 0 < lambdaMinus :=
    aux_gaussianBumpDecomposition_lambdaMinus_pos hmuMinus hscales.1
  have hlambdaPlus : 0 < lambdaPlus :=
    aux_gaussianBumpDecomposition_lambdaPlus_pos hmuMinus ⟨hscales.1, hscales.2.1⟩
  have hrhoFreqCont : Continuous
      (fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) :=
    aux_gaussianBumpDecomposition_rhoFrequency_continuous phiHat hphiCont hplateau hmuMinus hscales
  have hrhoFreqSupp := aux_gaussianBumpDecomposition_rhoFrequency_compactSupport phiHat
    hlambdaMinus hlambdaPlus hsupp muMinus muPlus nu
  have hrhoFreqInt : Integrable
      (fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) :=
    hrhoFreqCont.integrable_of_hasCompactSupport hrhoFreqSupp
  have h0Cont :=
    aux_gaussianBumpDecomposition_varRho0Frequency_continuous phiHat hphiCont muMinus lambdaMinus nu
  have h0Supp :=
    aux_gaussianBumpDecomposition_varRho0Frequency_compactSupport
      phiHat hlambdaMinus hsupp muMinus nu
  have h0Int : Integrable (fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu) :=
    h0Cont.integrable_of_hasCompactSupport h0Supp
  have h1Cont :=
    aux_gaussianBumpDecomposition_varRho1Frequency_continuous phiHat hphiCont muMinus lambdaPlus nu
  have h1Supp :=
    aux_gaussianBumpDecomposition_varRho1Frequency_compactSupport
      phiHat hlambdaPlus hsupp muMinus nu
  have h1Int : Integrable (fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu) :=
    h1Cont.integrable_of_hasCompactSupport h1Supp
  have h2Cont : Continuous
      (fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) :=
    aux_gaussianBumpDecomposition_varRho2Frequency_continuous
      phiHat hphiCont hplateau hmuMinus hscales
  have h2Supp :=
    aux_gaussianBumpDecomposition_varRho2Frequency_compactSupport
      phiHat hlambdaMinus hlambdaPlus hsupp
      muMinus muPlus nu
  have h2Int : Integrable
      (fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) :=
    h2Cont.integrable_of_hasCompactSupport h2Supp
  refine ⟨?_, ?_⟩
  · simpa only [fourScaleGaussianRho] using
      aux_gaussianBumpDecomposition_fourierInv_continuous _ hrhoFreqInt
  · have hfreq :=
      aux_gaussianBumpDecomposition_frequency_decomposition phiHat hmuMinus hscales hnu
    change FourierTransformInv.fourierInv
        (fourScaleGaussianRhoFrequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) =
      FourierTransformInv.fourierInv
        (fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu) +
        FourierTransformInv.fourierInv
          (fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu) +
          FourierTransformInv.fourierInv
            (fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu)
    rw [hfreq]
    calc
      FourierTransformInv.fourierInv
          (fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu +
            fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu +
              fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) =
          FourierTransformInv.fourierInv
            (fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu +
              fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu) +
            FourierTransformInv.fourierInv
              (fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu) :=
        aux_gaussianBumpDecomposition_inverseFourier_add _ _ (h0Int.add h1Int) h2Int
      _ = _ := by
        rw [aux_gaussianBumpDecomposition_inverseFourier_add _ _ h0Int h1Int]

/-- Source label `\ref{four scale Gaussian kernel}`; the explicit constant used by the public
theorem `fourScaleGaussianKernel`. -/
noncomputable def C_fourScaleGaussianKernel (N : ℕ) : ℝ :=
  2 * C_smoothDecay2 N * max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N) +
    (2 : ℝ) ^ N * max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate N)

/-- A rescaled `smoothDecay2` estimate with the support-volume factor specialized to `[-1, 1]`. -/
theorem aux_fourScaleGaussian_rescaledSmoothDecay2 (N : ℕ) (hN : 2 ≤ N) (q : ℝ → ℂ)
    (hq : ContDiff ℝ N q) (hsupp : tsupport q ⊆ Set.Icc (-1 : ℝ) 1)
    (A B a : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hzero : ∀ xi : ℝ, ‖q xi‖ ≤ A)
    (hNth : ∀ xi : ℝ, ((2 * Real.pi)⁻¹ : ℝ) ^ N * ‖iteratedDeriv N q xi‖ ≤ B)
    (ha : 0 < a) :
    MemW0 (FourierTransformInv.fourierInv (fun xi : ℝ => q (a * xi))) ∧
      ∀ x : ℝ, ‖FourierTransformInv.fourierInv (fun xi : ℝ => q (a * xi)) x‖ ≤
        2 * C_smoothDecay2 N * max A B * scaledBracketBump N a x := by
  let Q : ℝ → ℂ := fun xi => q (a * xi)
  let V : ℝ := (volume (tsupport q)).toReal
  let P : ℝ := max (sSup (Set.range fun xi : ℝ => ‖q xi‖))
    (((2 * Real.pi)⁻¹ : ℝ) ^ N *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N q xi‖))
  have hqcompact : HasCompactSupport q :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hsupp
  have hQcont : ContDiff ℝ N Q := by
    dsimp [Q]
    exact hq.comp (by fun_prop)
  have hQcompact : HasCompactSupport Q := by
    simpa only [Q, smul_eq_mul] using hqcompact.comp_smul (ne_of_gt ha)
  have hqmem : MemW0 (FourierTransformInv.fourierInv Q) :=
    (smoothDecay2 N hN Q hQcont hQcompact).1
  refine ⟨hqmem, ?_⟩
  have hqscale : 0 < ((2 * Real.pi)⁻¹ : ℝ) := by positivity
  have hs0 : sSup (Set.range fun xi : ℝ => ‖q xi‖) ≤ A := by
    apply csSup_le
    · exact Set.range_nonempty _
    rintro _ ⟨xi, rfl⟩
    exact hzero xi
  have hsN : sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N q xi‖) ≤
      B / ((2 * Real.pi)⁻¹ : ℝ) ^ N := by
    apply csSup_le
    · exact Set.range_nonempty _
    rintro _ ⟨xi, rfl⟩
    apply (le_div_iff₀ (pow_pos hqscale _)).2
    calc
      ‖iteratedDeriv N q xi‖ * ((2 * Real.pi)⁻¹ : ℝ) ^ N =
          ((2 * Real.pi)⁻¹ : ℝ) ^ N * ‖iteratedDeriv N q xi‖ := by ring
      _ ≤ B := hNth xi
  have hsN' : ((2 * Real.pi)⁻¹ : ℝ) ^ N *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N q xi‖) ≤ B := by
    calc
      ((2 * Real.pi)⁻¹ : ℝ) ^ N *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv N q xi‖) ≤
          ((2 * Real.pi)⁻¹ : ℝ) ^ N *
            (B / ((2 * Real.pi)⁻¹ : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left hsN (pow_nonneg hqscale.le _)
      _ = B := by field_simp [ne_of_gt (pow_pos hqscale N)]
  have hP : P ≤ max A B := by
    dsimp [P]
    exact max_le (hs0.trans (le_max_left _ _)) (hsN'.trans (le_max_right _ _))
  have hmeasure : volume (tsupport q) ≤ volume (Set.Icc (-1 : ℝ) 1) :=
    MeasureTheory.measure_mono hsupp
  have hIccFinite : volume (Set.Icc (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Icc]
    norm_num
  have hV : V ≤ 2 := by
    dsimp [V]
    calc
      (volume (tsupport q)).toReal ≤ (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
        ENNReal.toReal_mono hIccFinite hmeasure
      _ = 2 := by rw [Real.volume_Icc]; norm_num
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ max A B := hA.trans (le_max_left _ _)
  have hPV : P * V ≤ max A B * 2 :=
    mul_le_mul hP hV hV0 hM0
  intro x
  have hC : 0 ≤ C_smoothDecay2 N := by
    rw [C_smoothDecay2]
    positivity
  have hbracket : 0 ≤ bracketBump (a⁻¹ * x) ^ N := by
    rw [bracketBump]
    positivity
  have hbase : ‖FourierTransformInv.fourierInv q (a⁻¹ * x)‖ ≤
      2 * C_smoothDecay2 N * max A B * bracketBump (a⁻¹ * x) ^ N := by
    have hdecay := (smoothDecay2 N hN q hq hqcompact).2 (a⁻¹ * x)
    change ‖FourierTransformInv.fourierInv q (a⁻¹ * x)‖ ≤
      C_smoothDecay2 N * P * V * bracketBump (a⁻¹ * x) ^ N at hdecay
    calc
      ‖FourierTransformInv.fourierInv q (a⁻¹ * x)‖ ≤
          C_smoothDecay2 N * P * V * bracketBump (a⁻¹ * x) ^ N := hdecay
      _ = (C_smoothDecay2 N * bracketBump (a⁻¹ * x) ^ N) * (P * V) := by ring
      _ ≤ (C_smoothDecay2 N * bracketBump (a⁻¹ * x) ^ N) * (max A B * 2) :=
        mul_le_mul_of_nonneg_left hPV (mul_nonneg hC hbracket)
      _ = 2 * C_smoothDecay2 N * max A B * bracketBump (a⁻¹ * x) ^ N := by ring
  rw [show FourierTransformInv.fourierInv Q x =
      FourierTransformInv.fourierInv (fun xi : ℝ => q (a * xi)) x by rfl,
    aux_inverseFourier_comp_mul_pos q a x ha, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr ha.le)]
  calc
    a⁻¹ * ‖FourierTransformInv.fourierInv q (a⁻¹ * x)‖ ≤
        a⁻¹ * (2 * C_smoothDecay2 N * max A B * bracketBump (a⁻¹ * x) ^ N) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr ha.le)
    _ = 2 * C_smoothDecay2 N * max A B * scaledBracketBump N a x := by
      simp only [scaledBracketBump, bracketBump]
      ring

/-- A rescaled `smoothDecay` estimate. -/
theorem aux_fourScaleGaussian_rescaledSmoothDecay (N : ℕ) (hN : 2 ≤ N) (r : ℝ → ℂ)
    (hr : ContDiff ℝ N r) (hrcompact : HasCompactSupport r)
    (A B a : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hzero : (∫ xi : ℝ, ‖r xi‖) ≤ A)
    (hNth : ((2 * Real.pi)⁻¹ : ℝ) ^ N *
      (∫ xi : ℝ, ‖iteratedDeriv N r xi‖) ≤ B)
    (ha : 0 < a) :
    MemW0 (FourierTransformInv.fourierInv (fun xi : ℝ => r (a * xi))) ∧
      ∀ x : ℝ, ‖FourierTransformInv.fourierInv (fun xi : ℝ => r (a * xi)) x‖ ≤
        (2 : ℝ) ^ N * max A B * scaledBracketBump N a x := by
  let R : ℝ → ℂ := fun xi => r (a * xi)
  have hRcont : ContDiff ℝ N R := by
    dsimp [R]
    exact hr.comp (by fun_prop)
  have hRcompact : HasCompactSupport R := by
    simpa only [R, smul_eq_mul] using hrcompact.comp_smul (ne_of_gt ha)
  have hRmem : MemW0 (FourierTransformInv.fourierInv R) :=
    (smoothDecay N hN R hRcont hRcompact).1
  refine ⟨hRmem, ?_⟩
  have hM : 0 ≤ max A B := hA.trans (le_max_left _ _)
  have hpowTwo : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  intro x
  have hbase : ‖FourierTransformInv.fourierInv r (a⁻¹ * x)‖ ≤
      (2 : ℝ) ^ N * max A B * bracketBump (a⁻¹ * x) ^ N := by
    by_cases hx : a⁻¹ * x = 0
    · rw [hx]
      calc
        ‖FourierTransformInv.fourierInv r 0‖ ≤ ∫ xi : ℝ, ‖r xi‖ :=
          aux_norm_inverseFourier_le_integral_norm r 0
        _ ≤ A := hzero
        _ ≤ max A B := le_max_left _ _
        _ = 1 * max A B * bracketBump 0 ^ N := by simp [bracketBump]
        _ ≤ (2 : ℝ) ^ N * max A B * bracketBump 0 ^ N := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hpowTwo hM) (by simp [bracketBump])
    · have hdecay := (smoothDecay N hN r hr hrcompact).2 (a⁻¹ * x) hx
      have hderiv :
          ((2 * Real.pi)⁻¹ : ℝ) ^ N * |a⁻¹ * x|⁻¹ ^ N *
              (∫ xi : ℝ, ‖iteratedDeriv N r xi‖) ≤
            |a⁻¹ * x|⁻¹ ^ N * B := by
        calc
          ((2 * Real.pi)⁻¹ : ℝ) ^ N * |a⁻¹ * x|⁻¹ ^ N *
              (∫ xi : ℝ, ‖iteratedDeriv N r xi‖) =
            |a⁻¹ * x|⁻¹ ^ N *
              (((2 * Real.pi)⁻¹ : ℝ) ^ N *
                (∫ xi : ℝ, ‖iteratedDeriv N r xi‖)) := by ring
          _ ≤ |a⁻¹ * x|⁻¹ ^ N * B :=
            mul_le_mul_of_nonneg_left hNth (by positivity)
      have hmin :
          min (∫ xi : ℝ, ‖r xi‖)
              (((2 * Real.pi)⁻¹ : ℝ) ^ N * |a⁻¹ * x|⁻¹ ^ N *
                ∫ xi : ℝ, ‖iteratedDeriv N r xi‖) ≤
            max A B * min 1 (|a⁻¹ * x|⁻¹ ^ N) := by
        calc
          min (∫ xi : ℝ, ‖r xi‖)
              (((2 * Real.pi)⁻¹ : ℝ) ^ N * |a⁻¹ * x|⁻¹ ^ N *
                ∫ xi : ℝ, ‖iteratedDeriv N r xi‖) ≤
              min A (|a⁻¹ * x|⁻¹ ^ N * B) := min_le_min hzero hderiv
          _ = min A (B * |a⁻¹ * x|⁻¹ ^ N) := by ring
          _ ≤ min (max A B) (max A B * |a⁻¹ * x|⁻¹ ^ N) :=
            min_le_min (le_max_left _ _) (mul_le_mul_of_nonneg_right
              (le_max_right _ _) (by positivity))
          _ = max A B * min 1 (|a⁻¹ * x|⁻¹ ^ N) := by
            simpa only [mul_one] using
              (mul_min_of_nonneg 1 (|a⁻¹ * x|⁻¹ ^ N) hM).symm
      have hbracket : min 1 (|a⁻¹ * x|⁻¹ ^ N) ≤
          (2 : ℝ) ^ N * bracketBump (a⁻¹ * x) ^ N :=
        min_and_bracket N (by omega) (a⁻¹ * x)
      calc
        ‖FourierTransformInv.fourierInv r (a⁻¹ * x)‖ ≤
            min (∫ xi : ℝ, ‖r xi‖)
              (((2 * Real.pi)⁻¹ : ℝ) ^ N * |a⁻¹ * x|⁻¹ ^ N *
                ∫ xi : ℝ, ‖iteratedDeriv N r xi‖) := hdecay
        _ ≤ max A B * min 1 (|a⁻¹ * x|⁻¹ ^ N) := hmin
        _ ≤ max A B * ((2 : ℝ) ^ N * bracketBump (a⁻¹ * x) ^ N) :=
          mul_le_mul_of_nonneg_left hbracket hM
        _ = (2 : ℝ) ^ N * max A B * bracketBump (a⁻¹ * x) ^ N := by ring
  rw [show FourierTransformInv.fourierInv R x =
      FourierTransformInv.fourierInv (fun xi : ℝ => r (a * xi)) x by rfl,
    aux_inverseFourier_comp_mul_pos r a x ha, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr ha.le)]
  calc
    a⁻¹ * ‖FourierTransformInv.fourierInv r (a⁻¹ * x)‖ ≤
        a⁻¹ * ((2 : ℝ) ^ N * max A B * bracketBump (a⁻¹ * x) ^ N) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr ha.le)
    _ = (2 : ℝ) ^ N * max A B * scaledBracketBump N a x := by
      simp only [scaledBracketBump, bracketBump]
      ring

/-- The Wiener norm is closed under addition. -/
theorem aux_fourScaleGaussian_memW0_add (f g : ℝ → ℂ) (hf : MemW0 f) (hg : MemW0 g) :
    MemW0 (fun x => f x + g x) := by
  let hcont : Continuous (fun x : ℝ => f x + g x) := hf.1.add hg.1
  refine ⟨hcont, ?_⟩
  have hsum : Integrable (fun x : ℝ => wienerEnvelope f 1 x + wienerEnvelope g 1 x) :=
    hf.2.add hg.2
  refine hsum.mono_nonneg (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hcont zero_le_one x)
    (ae_of_all _ fun x => ?_)
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨z, hz, rfl⟩
  change ‖f (x + z) + g (x + z)‖ ≤
    sSup ((fun w : ℝ => ‖f (x + w)‖) '' Metric.closedBall 0 1) +
      sSup ((fun w : ℝ => ‖g (x + w)‖) '' Metric.closedBall 0 1)
  calc
    ‖f (x + z) + g (x + z)‖ ≤ ‖f (x + z)‖ + ‖g (x + z)‖ := norm_add_le _ _
    _ ≤ sSup ((fun w : ℝ => ‖f (x + w)‖) '' Metric.closedBall 0 1) +
        sSup ((fun w : ℝ => ‖g (x + w)‖) '' Metric.closedBall 0 1) :=
      add_le_add
        (aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1 (by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz))
        (aux_norm_le_wienerEnvelope_of_mem_closedBall hg.1 (by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz))

/-- The Wiener norm is closed under negation. -/
theorem aux_fourScaleGaussian_memW0_neg (f : ℝ → ℂ) (hf : MemW0 f) :
    MemW0 (fun x => -f x) := by
  refine ⟨hf.1.neg, ?_⟩
  have hEnvelope : wienerEnvelope (fun x : ℝ => -f x) 1 = wienerEnvelope f 1 := by
    funext x
    simp [wienerEnvelope]
  rw [hEnvelope]
  exact hf.2

/-- Inverse Fourier transform commutes with negation. -/
theorem aux_fourScaleGaussian_inverseFourier_neg (f : ℝ → ℂ) :
    FourierTransformInv.fourierInv (fun xi : ℝ => -f xi) =
      fun x : ℝ => -FourierTransformInv.fourierInv f x := by
  funext x
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  simp_rw [smul_neg]
  exact integral_neg _

/-- The first multiplier is a rescaled Gaussian-bump quotient. -/
theorem aux_fourScaleGaussian_varRho0Frequency_rescale (phiHat : ℝ → ℂ)
    (muMinus lambdaMinus nu : ℝ) (hlambdaMinus : lambdaMinus ≠ 0) :
    (fun xi : ℝ => gaussianBumpQuotient
      (muMinus * Real.sqrt |nu| / lambdaMinus) phiHat (lambdaMinus * xi)) =
      fourScaleGaussianVarRho0Frequency phiHat muMinus lambdaMinus nu := by
  funext xi
  have harg :
      (muMinus * Real.sqrt |nu| / lambdaMinus) * (lambdaMinus * xi) =
        muMinus * Real.sqrt |nu| * xi := by
    field_simp
  simp only [gaussianBumpQuotient, fourScaleGaussianVarRho0Frequency]
  rw [harg]
  simp

/-- The second multiplier is a negated rescaled Gaussian-bump quotient. -/
theorem aux_fourScaleGaussian_varRho1Frequency_rescale (phiHat : ℝ → ℂ)
    (muMinus lambdaPlus nu : ℝ) (hlambdaPlus : lambdaPlus ≠ 0) :
    (fun xi : ℝ => -gaussianBumpQuotient
      (muMinus * Real.sqrt |nu| / lambdaPlus) phiHat (lambdaPlus * xi)) =
      fourScaleGaussianVarRho1Frequency phiHat muMinus lambdaPlus nu := by
  funext xi
  have harg :
      (muMinus * Real.sqrt |nu| / lambdaPlus) * (lambdaPlus * xi) =
        muMinus * Real.sqrt |nu| * xi := by
    field_simp
  simp only [gaussianBumpQuotient, fourScaleGaussianVarRho1Frequency]
  rw [harg]
  simp

theorem aux_fourScaleGaussian_varRho0_rescale (phiHat : ℝ → ℂ)
    (muMinus lambdaMinus nu : ℝ) (hlambdaMinus : lambdaMinus ≠ 0) :
    fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu =
      FourierTransformInv.fourierInv (fun xi : ℝ => gaussianBumpQuotient
        (muMinus * Real.sqrt |nu| / lambdaMinus) phiHat (lambdaMinus * xi)) := by
  unfold fourScaleGaussianVarRho0
  rw [← aux_fourScaleGaussian_varRho0Frequency_rescale phiHat muMinus lambdaMinus nu hlambdaMinus]

theorem aux_fourScaleGaussian_varRho1_rescale (phiHat : ℝ → ℂ)
    (muMinus lambdaPlus nu : ℝ) (hlambdaPlus : lambdaPlus ≠ 0) :
    fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu =
      fun x : ℝ => -FourierTransformInv.fourierInv (fun xi : ℝ => gaussianBumpQuotient
        (muMinus * Real.sqrt |nu| / lambdaPlus) phiHat (lambdaPlus * xi)) x := by
  unfold fourScaleGaussianVarRho1
  rw [← aux_fourScaleGaussian_varRho1Frequency_rescale phiHat muMinus lambdaPlus nu hlambdaPlus]
  exact aux_fourScaleGaussian_inverseFourier_neg _

/-- The remainder multiplier is the normalized second Gaussian multiplier. -/
theorem aux_fourScaleGaussian_varRho2Frequency_rescale (phiHat : ℝ → ℂ)
    (muMinus muPlus lambdaMinus lambdaPlus nu : ℝ) (hlambdaPlus : lambdaPlus ≠ 0) :
    (fun xi : ℝ => secondGaussianMultiplier phiHat
      (muMinus * Real.sqrt |nu| / lambdaPlus) (lambdaMinus / lambdaPlus)
      (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) / lambdaPlus) nu (lambdaPlus * xi)) =
      fourScaleGaussianVarRho2Frequency phiHat muMinus muPlus lambdaMinus lambdaPlus nu := by
  funext xi
  have hmu :
      (muMinus * Real.sqrt |nu| / lambdaPlus) * (lambdaPlus * xi) =
        muMinus * Real.sqrt |nu| * xi := by
    field_simp
  have hlambda : (lambdaMinus / lambdaPlus) * (lambdaPlus * xi) = lambdaMinus * xi := by
    field_simp
  have ht :
      (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) / lambdaPlus) * (lambdaPlus * xi) =
        Real.sqrt (muPlus ^ 2 - muMinus ^ 2) * xi := by
    field_simp
  simp only [secondGaussianMultiplier, aux_secondGaussianQ, aux_secondGaussianS,
    fourScaleGaussianVarRho2Frequency, Pi.mul_apply]
  rw [hmu, hlambda, ht]
  simp

theorem aux_fourScaleGaussian_varRho2_rescale (phiHat : ℝ → ℂ)
    (muMinus muPlus lambdaMinus lambdaPlus nu : ℝ) (hlambdaPlus : lambdaPlus ≠ 0) :
    fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu =
      FourierTransformInv.fourierInv (fun xi : ℝ => secondGaussianMultiplier phiHat
        (muMinus * Real.sqrt |nu| / lambdaPlus) (lambdaMinus / lambdaPlus)
        (Real.sqrt (muPlus ^ 2 - muMinus ^ 2) / lambdaPlus) nu (lambdaPlus * xi)) := by
  unfold fourScaleGaussianVarRho2
  rw [← aux_fourScaleGaussian_varRho2Frequency_rescale phiHat muMinus muPlus lambdaMinus lambdaPlus nu
    hlambdaPlus]

/-- The normalized separation parameter is at least `sqrt 3 / 2`. -/
theorem aux_fourScaleGaussian_t_lower_bound
    {muMinus muPlus lambdaMinus lambdaPlus : ℝ}
    (hmuMinus : 0 < muMinus) (hmuPlus : 0 < muPlus)
    (hlambdaMinus : 0 < lambdaMinus) (hlambdaPlus : 0 < lambdaPlus)
    (hscale0 : 2 * muMinus ≤ 2 * lambdaMinus)
    (hscale1 : 2 * lambdaMinus ≤ lambdaPlus)
    (hscale2 : lambdaPlus ≤ muPlus) :
    Real.sqrt 3 / 2 ≤
      Real.sqrt (muPlus ^ 2 - muMinus ^ 2) / lambdaPlus := by
  have hmuMinusHalf : muMinus ≤ lambdaPlus / 2 := by
    linarith
  have hmuPlusSq : lambdaPlus ^ 2 ≤ muPlus ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self hlambdaPlus.le hscale2
  have hmuMinusSq : muMinus ^ 2 ≤ (lambdaPlus / 2) ^ 2 := by
    exact (sq_le_sq₀ hmuMinus.le (by positivity)).2 hmuMinusHalf
  have hdiff : (3 / 4 : ℝ) * lambdaPlus ^ 2 ≤ muPlus ^ 2 - muMinus ^ 2 := by
    nlinarith
  have hdiffNonneg : 0 ≤ muPlus ^ 2 - muMinus ^ 2 := by
    nlinarith [sq_nonneg lambdaPlus]
  rw [le_div_iff₀ hlambdaPlus]
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hdiffNonneg]
  have hsqrtThree : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The rescaled parameters obey the hypotheses of the Gaussian multiplier estimates. -/
theorem aux_fourScaleGaussian_normalized_parameters
    {muMinus lambdaMinus lambdaPlus nu : ℝ}
    (hmuMinus : 0 < muMinus) (hlambdaMinus : 0 < lambdaMinus)
    (hlambdaPlus : 0 < lambdaPlus)
    (hscale0 : 2 * muMinus ≤ 2 * lambdaMinus)
    (hscale1 : 2 * lambdaMinus ≤ lambdaPlus)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    0 ≤ muMinus * Real.sqrt |nu| / lambdaMinus ∧
      muMinus * Real.sqrt |nu| / lambdaMinus ≤ 1 ∧
      0 ≤ muMinus * Real.sqrt |nu| / lambdaPlus ∧
      muMinus * Real.sqrt |nu| / lambdaPlus ≤ 1 ∧
      0 < muMinus * Real.sqrt |nu| / lambdaPlus ∧
      muMinus * Real.sqrt |nu| / lambdaPlus ≤ lambdaMinus / lambdaPlus ∧
      lambdaMinus / lambdaPlus ≤ 1 / 2 := by
  have habsPos : 0 < |nu| := abs_pos.mpr (ne_of_lt hnu.2)
  have habsLe : |nu| ≤ 1 := by
    rw [abs_of_nonpos hnu.2.le]
    linarith [hnu.1]
  have hsqrtPos : 0 < Real.sqrt |nu| := Real.sqrt_pos.2 habsPos
  have hsqrtLe : Real.sqrt |nu| ≤ 1 := Real.sqrt_le_one.2 habsLe
  have hmuLambdaMinus : muMinus ≤ lambdaMinus := by linarith
  have hmuLambdaPlus : muMinus ≤ lambdaPlus := by linarith
  have hnumMinus : muMinus * Real.sqrt |nu| ≤ lambdaMinus := by
    calc
      muMinus * Real.sqrt |nu| ≤ muMinus * 1 :=
        mul_le_mul_of_nonneg_left hsqrtLe hmuMinus.le
      _ = muMinus := by ring
      _ ≤ lambdaMinus := hmuLambdaMinus
  have hnumPlus : muMinus * Real.sqrt |nu| ≤ lambdaPlus := by
    calc
      muMinus * Real.sqrt |nu| ≤ muMinus * 1 :=
        mul_le_mul_of_nonneg_left hsqrtLe hmuMinus.le
      _ = muMinus := by ring
      _ ≤ lambdaPlus := hmuLambdaPlus
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg hmuMinus.le hsqrtPos.le) hlambdaMinus.le
  · exact (div_le_one₀ hlambdaMinus).2 hnumMinus
  · exact div_nonneg (mul_nonneg hmuMinus.le hsqrtPos.le) hlambdaPlus.le
  · exact (div_le_one₀ hlambdaPlus).2 hnumPlus
  · exact div_pos (mul_pos hmuMinus hsqrtPos) hlambdaPlus
  · apply (div_le_div_iff₀ hlambdaPlus hlambdaPlus).2
    exact mul_le_mul_of_nonneg_right hnumMinus hlambdaPlus.le
  · apply (div_le_iff₀ hlambdaPlus).2
    nlinarith

/-- Combine the three Wiener estimates supplied by the Gaussian decomposition. -/
theorem aux_fourScaleGaussian_assemble (rho varrho0 varrho1 varrho2 : ℝ → ℂ)
    (A B : ℝ) (hB : 0 ≤ B) (sMinus sPlus : ℝ → ℝ)
    (hsMinus : ∀ x : ℝ, 0 ≤ sMinus x)
    (hdecomp : ∀ x : ℝ, rho x = (varrho0 x + varrho1 x) + varrho2 x)
    (h0mem : MemW0 varrho0) (h1mem : MemW0 varrho1) (h2mem : MemW0 varrho2)
    (h0 : ∀ x : ℝ, ‖varrho0 x‖ ≤ A * sMinus x)
    (h1 : ∀ x : ℝ, ‖varrho1 x‖ ≤ A * sPlus x)
    (h2 : ∀ x : ℝ, ‖varrho2 x‖ ≤ B * sPlus x) :
    MemW0 rho ∧ ∀ x : ℝ, ‖rho x‖ ≤ (A + B) * (sMinus x + sPlus x) := by
  have hrho : rho = fun x => (varrho0 x + varrho1 x) + varrho2 x := funext hdecomp
  constructor
  · rw [hrho]
    exact aux_fourScaleGaussian_memW0_add _ _
      (aux_fourScaleGaussian_memW0_add _ _ h0mem h1mem) h2mem
  · intro x
    rw [hdecomp x]
    calc
      ‖(varrho0 x + varrho1 x) + varrho2 x‖ ≤
          ‖varrho0 x + varrho1 x‖ + ‖varrho2 x‖ := norm_add_le _ _
      _ ≤ (‖varrho0 x‖ + ‖varrho1 x‖) + ‖varrho2 x‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (A * sMinus x + A * sPlus x) + B * sPlus x :=
        add_le_add (add_le_add (h0 x) (h1 x)) (h2 x)
      _ = (A + B) * (sMinus x + sPlus x) - B * sMinus x := by ring
      _ ≤ (A + B) * (sMinus x + sPlus x) :=
        sub_le_self _ (mul_nonneg hB (hsMinus x))

/-- Estimate a rescaled Gaussian-bump component. -/
theorem aux_fourScaleGaussian_gaussian_component_rescale (c : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (phiHat : ℝ → ℂ) (hc : 0 < c) (beta a : ℝ) (hbeta : 0 ≤ beta)
    (hbetaOne : beta ≤ 1) (ha : 0 < a) (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c) :
    MemW0 (FourierTransformInv.fourierInv
      (fun xi : ℝ => gaussianBumpQuotient beta phiHat (a * xi))) ∧
      ∀ x : ℝ, ‖FourierTransformInv.fourierInv
        (fun xi : ℝ => gaussianBumpQuotient beta phiHat (a * xi)) x‖ ≤
        c * (2 * C_smoothDecay2 N *
          max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N)) *
          scaledBracketBump N a x := by
  let Q : ℝ → ℂ := gaussianBumpQuotient beta phiHat
  have hQsupp : tsupport Q ⊆ Set.Icc (-1 : ℝ) 1 := by
    change tsupport (fun xi : ℝ =>
      (((Gaussians.gaussian (beta * xi))⁻¹ : ℝ) : ℂ) * phiHat xi) ⊆ Set.Icc (-1 : ℝ) 1
    exact tsupport_mul_subset_right.trans hsupp
  have hGaussianEstimateNonneg (k : ℕ) : 0 ≤ C_gaussianEstimate k := by
    unfold C_gaussianEstimate
    apply mul_nonneg (Real.exp_pos _).le
    apply Finset.sum_nonneg
    intro l _
    exact aux_gaussianEstimate_coeff_nonneg k l
  have hGaussianBumpEstimateNonneg (k : ℕ) : 0 ≤ C_gaussianBumpEstimate k := by
    unfold C_gaussianBumpEstimate
    apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (by positivity) (hGaussianEstimateNonneg l)
  have hA : 0 ≤ c * C_gaussianBumpEstimate 0 :=
    mul_nonneg hc.le (hGaussianBumpEstimateNonneg 0)
  have hB : 0 ≤ c * C_gaussianBumpEstimate N :=
    mul_nonneg hc.le (hGaussianBumpEstimateNonneg N)
  have hphi0 : ContDiff ℝ 0 phiHat := hphi.of_le zero_le
  have hphiBound0 : ∀ m : ℕ, m ≤ 0 → ∀ xi : ℝ,
      ‖iteratedDeriv m phiHat xi‖ ≤ c := fun m hm xi =>
    hphiBound m (hm.trans (Nat.zero_le _)) xi
  have hzero : ∀ xi : ℝ, ‖Q xi‖ ≤ c * C_gaussianBumpEstimate 0 := by
    intro xi
    simpa only [Q, pow_zero, one_mul, iteratedDeriv_zero] using
      aux_gaussianBumpEstimate_pointwise 0 c beta phiHat hc.le hbeta hbetaOne hphi0 hsupp
        hphiBound0 xi
  have hNth : ∀ xi : ℝ, ((2 * Real.pi)⁻¹ : ℝ) ^ N *
      ‖iteratedDeriv N Q xi‖ ≤ c * C_gaussianBumpEstimate N := by
    intro xi
    simpa only [Q] using
      aux_gaussianBumpEstimate_pointwise N c beta phiHat hc.le hbeta hbetaOne hphi hsupp
        hphiBound xi
  obtain ⟨hmem, hbound⟩ := aux_fourScaleGaussian_rescaledSmoothDecay2 N hN Q
    (aux_gaussianBumpEstimate_contDiff N beta phiHat hphi) hQsupp
    (c * C_gaussianBumpEstimate 0) (c * C_gaussianBumpEstimate N) a hA hB hzero hNth ha
  refine ⟨?_, ?_⟩
  · simpa only [Q] using hmem
  · intro x
    have hx := hbound x
    change ‖FourierTransformInv.fourierInv (fun xi : ℝ => Q (a * xi)) x‖ ≤ _
    calc
      ‖FourierTransformInv.fourierInv (fun xi : ℝ => Q (a * xi)) x‖ ≤
          2 * C_smoothDecay2 N *
            max (c * C_gaussianBumpEstimate 0) (c * C_gaussianBumpEstimate N) *
              scaledBracketBump N a x := hx
      _ = c * (2 * C_smoothDecay2 N *
          max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N)) *
          scaledBracketBump N a x := by
        rw [← mul_max_of_nonneg (C_gaussianBumpEstimate 0)
          (C_gaussianBumpEstimate N) hc.le]
        ring

/-- The second Gaussian estimate constant is nonnegative. -/
theorem aux_C_secondGaussianEstimate_nonneg (N : ℕ) :
    0 ≤ C_secondGaussianEstimate N := by
  unfold C_secondGaussianEstimate
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro l _
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact Real.rpow_nonneg (by positivity) _
    · exact aux_C_gaussianBumpEstimate_nonneg l
  · exact aux_C_faaDiBruno_nonneg (N - l)

/-- Estimate the rescaled second Gaussian component. -/
theorem aux_fourScaleGaussian_second_component_rescale (c : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (phiHat : ℝ → ℂ) (hc : 0 < c) (mu lambda t nu a : ℝ)
    (hmu : 0 < mu) (hmulambda : mu ≤ lambda) (hlambda : lambda ≤ 1 / 2)
    (ht : Real.sqrt 3 / 2 ≤ t) (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    (hphi : ContDiff ℝ N phiHat) (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (ha : 0 < a) :
    MemW0 (FourierTransformInv.fourierInv
      (fun xi : ℝ => secondGaussianMultiplier phiHat mu lambda t nu (a * xi))) ∧
      ∀ x : ℝ, ‖FourierTransformInv.fourierInv
        (fun xi : ℝ => secondGaussianMultiplier phiHat mu lambda t nu (a * xi)) x‖ ≤
        c * ((2 : ℝ) ^ N * max (C_secondGaussianEstimate 0)
          (C_secondGaussianEstimate N)) * scaledBracketBump N a x := by
  let R : ℝ → ℂ := secondGaussianMultiplier phiHat mu lambda t nu
  have hlambdaPos : 0 < lambda := hmu.trans_le hmulambda
  have hC0 : 0 ≤ C_secondGaussianEstimate 0 := aux_C_secondGaussianEstimate_nonneg 0
  have hCN : 0 ≤ C_secondGaussianEstimate N := aux_C_secondGaussianEstimate_nonneg N
  have hA : 0 ≤ c * C_secondGaussianEstimate 0 := mul_nonneg hc.le hC0
  have hB : 0 ≤ c * C_secondGaussianEstimate N := mul_nonneg hc.le hCN
  have hphi0 : ContDiff ℝ 0 phiHat := hphi.of_le zero_le
  have hphiBound0 : ∀ m : ℕ, m ≤ 0 → ∀ xi : ℝ,
      ‖iteratedDeriv m phiHat xi‖ ≤ c := by
    intro m hm xi
    exact hphiBound m (hm.trans (Nat.zero_le _)) xi
  have hzero : (∫ xi : ℝ, ‖R xi‖) ≤ c * C_secondGaussianEstimate 0 := by
    simpa only [R, pow_zero, one_mul, iteratedDeriv_zero] using
      aux_secondGaussianMultiplier_l1_bound 0 c phiHat mu lambda t nu hc.le hmu hmulambda
        hlambda ht hnu hplateau hphi0 hsupp hphiBound0
  have hNth : ((2 * Real.pi)⁻¹ : ℝ) ^ N *
      (∫ xi : ℝ, ‖iteratedDeriv N R xi‖) ≤ c * C_secondGaussianEstimate N := by
    simpa only [R] using
      aux_secondGaussianMultiplier_l1_bound N c phiHat mu lambda t nu hc.le hmu hmulambda
        hlambda ht hnu hplateau hphi hsupp hphiBound
  obtain ⟨hmem, hbound⟩ := aux_fourScaleGaussian_rescaledSmoothDecay N hN R
    (aux_secondGaussianMultiplier_contDiff N phiHat mu lambda t nu hmu hmulambda hlambda ht
      hplateau hphi)
    (aux_secondGaussianMultiplier_hasCompactSupport phiHat mu lambda t nu hlambdaPos.ne' hsupp)
    (c * C_secondGaussianEstimate 0) (c * C_secondGaussianEstimate N) a hA hB hzero hNth ha
  refine ⟨?_, ?_⟩
  · simpa only [R] using hmem
  · intro x
    have hx := hbound x
    change ‖FourierTransformInv.fourierInv (fun xi : ℝ => R (a * xi)) x‖ ≤ _
    calc
      ‖FourierTransformInv.fourierInv (fun xi : ℝ => R (a * xi)) x‖ ≤
          (2 : ℝ) ^ N * max (c * C_secondGaussianEstimate 0)
            (c * C_secondGaussianEstimate N) * scaledBracketBump N a x := hx
      _ = c * ((2 : ℝ) ^ N * max (C_secondGaussianEstimate 0)
          (C_secondGaussianEstimate N)) * scaledBracketBump N a x := by
        rw [← mul_max_of_nonneg (C_secondGaussianEstimate 0)
          (C_secondGaussianEstimate N) hc.le]
        ring

/-- Source label `\ref{four scale Gaussian kernel}`. -/
theorem fourScaleGaussianKernel (c : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (phi phiHat : ℝ → ℂ) (hphiW0 : MemW0 phi)
    (hphiHat : phiHat = FourierTransform.fourier phi) (hc : 0 < c)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hplateau : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat xi = 1)
    (hphi : ContDiff ℝ N phiHat)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (muMinus muPlus lambdaMinus lambdaPlus nu : ℝ)
    (hmuMinus : 0 < muMinus) (hmuPlus : 0 < muPlus)
    (hlambdaMinus : 0 < lambdaMinus) (hlambdaPlus : 0 < lambdaPlus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧ 2 * lambdaMinus ≤ lambdaPlus ∧
      lambdaPlus ≤ muPlus)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    MemW0 (fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu) ∧
      ∀ x : ℝ, ‖fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ ≤
        c * C_fourScaleGaussianKernel N *
          (scaledBracketBump N lambdaMinus x + scaledBracketBump N lambdaPlus x) := by
  rcases hscales with ⟨hscale0, hscale1, hscale2⟩
  let betaMinus : ℝ := muMinus * Real.sqrt |nu| / lambdaMinus
  let beta : ℝ := muMinus * Real.sqrt |nu| / lambdaPlus
  let a : ℝ := lambdaMinus / lambdaPlus
  let t : ℝ := Real.sqrt (muPlus ^ 2 - muMinus ^ 2) / lambdaPlus
  rcases aux_fourScaleGaussian_normalized_parameters hmuMinus hlambdaMinus hlambdaPlus hscale0 hscale1 hnu with
    ⟨hbetaMinus0, hbetaMinusOne, hbeta0, hbetaOne, hbetaPos, hbetaLeA, haOne⟩
  have hbetaMinus0' : 0 ≤ betaMinus := by simpa only [betaMinus] using hbetaMinus0
  have hbetaMinusOne' : betaMinus ≤ 1 := by simpa only [betaMinus] using hbetaMinusOne
  have hbeta0' : 0 ≤ beta := by simpa only [beta] using hbeta0
  have hbetaOne' : beta ≤ 1 := by simpa only [beta] using hbetaOne
  have hbetaPos' : 0 < beta := by simpa only [beta] using hbetaPos
  have hbetaLeA' : beta ≤ a := by simpa only [beta, a] using hbetaLeA
  have haOne' : a ≤ 1 / 2 := by simpa only [a] using haOne
  have ht : Real.sqrt 3 / 2 ≤ t := by
    simpa only [t] using aux_fourScaleGaussian_t_lower_bound hmuMinus hmuPlus hlambdaMinus hlambdaPlus
      hscale0 hscale1 hscale2
  obtain ⟨h0rawMem, h0rawBound⟩ := aux_fourScaleGaussian_gaussian_component_rescale c N hN phiHat hc
    betaMinus lambdaMinus hbetaMinus0' hbetaMinusOne' hlambdaMinus hphi hsupp hphiBound
  obtain ⟨h1rawMem, h1rawBound⟩ := aux_fourScaleGaussian_gaussian_component_rescale c N hN phiHat hc
    beta lambdaPlus hbeta0' hbetaOne' hlambdaPlus hphi hsupp hphiBound
  obtain ⟨h2rawMem, h2rawBound⟩ := aux_fourScaleGaussian_second_component_rescale c N hN phiHat hc
    beta a t nu lambdaPlus hbetaPos' hbetaLeA' haOne' ht hnu hplateau hphi hsupp hphiBound
      hlambdaPlus
  have h0eq := aux_fourScaleGaussian_varRho0_rescale phiHat muMinus lambdaMinus nu hlambdaMinus.ne'
  have h1eq := aux_fourScaleGaussian_varRho1_rescale phiHat muMinus lambdaPlus nu hlambdaPlus.ne'
  have h2eq := aux_fourScaleGaussian_varRho2_rescale phiHat muMinus muPlus lambdaMinus lambdaPlus nu hlambdaPlus.ne'
  let A : ℝ := c * (2 * C_smoothDecay2 N *
    max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N))
  let B : ℝ := c * ((2 : ℝ) ^ N *
    max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate N))
  have h0mem : MemW0 (fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu) := by
    rw [h0eq]
    exact h0rawMem
  have h1mem : MemW0 (fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu) := by
    rw [h1eq]
    exact aux_fourScaleGaussian_memW0_neg _ h1rawMem
  have h2mem : MemW0 (fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu) := by
    rw [h2eq]
    exact h2rawMem
  have h0bound (x : ℝ) :
      ‖fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x‖ ≤
        A * scaledBracketBump N lambdaMinus x := by
    rw [h0eq]
    simpa only [A] using h0rawBound x
  have h1bound (x : ℝ) :
      ‖fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu x‖ ≤
        A * scaledBracketBump N lambdaPlus x := by
    rw [h1eq]
    simpa only [A, beta, norm_neg] using h1rawBound x
  have h2bound (x : ℝ) :
      ‖fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ ≤
        B * scaledBracketBump N lambdaPlus x := by
    rw [h2eq]
    simpa only [B] using h2rawBound x
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    apply mul_nonneg hc.le
    apply mul_nonneg (by positivity)
    exact (aux_C_secondGaussianEstimate_nonneg 0).trans
      (le_max_left (C_secondGaussianEstimate 0) (C_secondGaussianEstimate N))
  have hdecompEq := (gaussianBumpDecomposition phi phiHat hphiW0 hphiHat hsupp hplateau
    hmuMinus hmuPlus hlambdaMinus hlambdaPlus ⟨hscale0, hscale1, hscale2⟩ hnu).2
  have hdecomp : ∀ x : ℝ,
      fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu x =
        (fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x +
          fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu x) +
            fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x := by
    intro x
    simpa only [Pi.add_apply] using congrFun hdecompEq x
  obtain ⟨hmem, hbound⟩ := aux_fourScaleGaussian_assemble
    (fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu)
    (fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu)
    (fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu)
    (fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu)
    A B hBnonneg
    (scaledBracketBump N lambdaMinus) (scaledBracketBump N lambdaPlus)
    (fun x => aux_scaledBracketBump_nonneg N hlambdaMinus x)
    hdecomp h0mem h1mem h2mem h0bound h1bound h2bound
  refine ⟨hmem, ?_⟩
  intro x
  calc
    ‖fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ ≤
        (A + B) * (scaledBracketBump N lambdaMinus x + scaledBracketBump N lambdaPlus x) :=
      hbound x
    _ = c * C_fourScaleGaussianKernel N *
        (scaledBracketBump N lambdaMinus x + scaledBracketBump N lambdaPlus x) := by
      rw [C_fourScaleGaussianKernel]
      dsimp [A, B]
      ring

/-- The general pass-8 bound for the four-scale Gaussian kernel constant. -/
private theorem aux_C_fourScaleGaussianKernel_bound (N : ℕ) :
    C_fourScaleGaussianKernel N ≤ (2 : ℝ) ^ (25 * (N + 1) ^ 3) := by
  have hG0 : C_gaussianBumpEstimate 0 ≤ (2 : ℝ) ^ 8 := by
    simpa using (constantGaussianBumpEstimate 0).1
  have hS0 : C_secondGaussianEstimate 0 ≤ (2 : ℝ) ^ 20 := by
    simpa using (constantSecondGaussianEstimate 0).1
  have hGexp0 : 8 ≤ 8 * (N + 1) ^ 2 := by
    nlinarith [Nat.zero_le N]
  have hSexp0 : 20 ≤ 20 * (N + 1) ^ 3 := by
    nlinarith [Nat.zero_le N]
  have hGmax : max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N) ≤
      (2 : ℝ) ^ (8 * (N + 1) ^ 2) := by
    apply max_le
    · exact hG0.trans (pow_le_pow_right₀ (by norm_num) hGexp0)
    · exact (constantGaussianBumpEstimate N).1
  have hSmax : max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate N) ≤
      (2 : ℝ) ^ (20 * (N + 1) ^ 3) := by
    apply max_le
    · exact hS0.trans (pow_le_pow_right₀ (by norm_num) hSexp0)
    · exact (constantSecondGaussianEstimate N).1
  have hfirst : 2 * (2 : ℝ) ^ N *
      max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N) ≤
      (2 : ℝ) ^ (1 + N + 8 * (N + 1) ^ 2) := by
    have hfac : 0 ≤ 2 * (2 : ℝ) ^ N := by positivity
    calc
      2 * (2 : ℝ) ^ N * max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N) ≤
          2 * (2 : ℝ) ^ N * (2 : ℝ) ^ (8 * (N + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hGmax hfac
      _ = (2 : ℝ) ^ (1 + N + 8 * (N + 1) ^ 2) := by
        rw [pow_add, pow_add]
        norm_num
  have hsecond : (2 : ℝ) ^ N * max (C_secondGaussianEstimate 0)
      (C_secondGaussianEstimate N) ≤ (2 : ℝ) ^ (N + 20 * (N + 1) ^ 3) := by
    calc
      (2 : ℝ) ^ N * max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate N) ≤
          (2 : ℝ) ^ N * (2 : ℝ) ^ (20 * (N + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left hSmax (by positivity)
      _ = (2 : ℝ) ^ (N + 20 * (N + 1) ^ 3) := by rw [pow_add]
  have hfirstExp : (1 + N + 8 * (N + 1) ^ 2) + 1 ≤ 25 * (N + 1) ^ 3 := by
    nlinarith [Nat.zero_le N]
  have hsecondExp : (N + 20 * (N + 1) ^ 3) + 1 ≤ 25 * (N + 1) ^ 3 := by
    nlinarith [Nat.zero_le N]
  have hmaxExp : max (1 + N + 8 * (N + 1) ^ 2) (N + 20 * (N + 1) ^ 3) + 1 ≤
      25 * (N + 1) ^ 3 := by
    apply Nat.succ_le_iff.mpr
    apply max_lt
    · exact Nat.lt_of_succ_le hfirstExp
    · exact Nat.lt_of_succ_le hsecondExp
  rw [C_fourScaleGaussianKernel, C_smoothDecay2]
  calc
    2 * (2 : ℝ) ^ N * max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N) +
        (2 : ℝ) ^ N * max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate N) ≤
        (2 : ℝ) ^ (1 + N + 8 * (N + 1) ^ 2) +
          (2 : ℝ) ^ (N + 20 * (N + 1) ^ 3) := add_le_add hfirst hsecond
    _ ≤ (2 : ℝ) ^ max (1 + N + 8 * (N + 1) ^ 2) (N + 20 * (N + 1) ^ 3) +
          (2 : ℝ) ^ max (1 + N + 8 * (N + 1) ^ 2) (N + 20 * (N + 1) ^ 3) := by
      apply add_le_add
      · exact pow_le_pow_right₀ (by norm_num) (Nat.le_max_left _ _)
      · exact pow_le_pow_right₀ (by norm_num) (Nat.le_max_right _ _)
    _ = (2 : ℝ) ^ (max (1 + N + 8 * (N + 1) ^ 2) (N + 20 * (N + 1) ^ 3) + 1) := by
      rw [pow_succ]
      ring
    _ ≤ (2 : ℝ) ^ (25 * (N + 1) ^ 3) :=
      pow_le_pow_right₀ (by norm_num) hmaxExp

/-- Sharp finite value for the four-scale Gaussian kernel constant at order two. -/
theorem aux_C_fourScaleGaussianKernel_two_lt_value :
    C_fourScaleGaussianKernel 2 < 637436354528 := by
  have hG0 : C_gaussianBumpEstimate 0 < 81 :=
    (constantGaussianBumpEstimate 0).2.1
  have hG2 : C_gaussianBumpEstimate 2 < 124 :=
    (constantGaussianBumpEstimate 2).2.2.2.1
  have hS0 : C_secondGaussianEstimate 0 < (2 : ℝ) ^ 16 :=
    (constantSecondGaussianEstimate 0).2.1
  have hS2 : C_secondGaussianEstimate 2 < 159359088384 :=
    aux_C_secondGaussianEstimate_two_lt_value
  have hGmax : max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 2) < 124 := by
    apply max_lt
    · exact hG0.trans (by norm_num)
    · exact hG2
  have hSmax : max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 2) <
      159359088384 := by
    apply max_lt
    · exact hS0.trans (by norm_num)
    · exact hS2
  rw [C_fourScaleGaussianKernel, C_smoothDecay2]
  calc
    2 * (2 : ℝ) ^ 2 * max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 2) +
        (2 : ℝ) ^ 2 * max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 2) <
        2 * (2 : ℝ) ^ 2 * 124 + (2 : ℝ) ^ 2 * 159359088384 :=
      add_lt_add
        (mul_lt_mul_of_pos_left hGmax (by positivity))
        (mul_lt_mul_of_pos_left hSmax (by positivity))
    _ = 637436354528 := by norm_num

/-- Sharp finite value for the four-scale Gaussian kernel constant at order three. -/
theorem aux_C_fourScaleGaussianKernel_three_lt_value :
    C_fourScaleGaussianKernel 3 < 6136564156458101504 := by
  have hG0 : C_gaussianBumpEstimate 0 < 81 :=
    (constantGaussianBumpEstimate 0).2.1
  have hG3 : C_gaussianBumpEstimate 3 < 176 :=
    (constantGaussianBumpEstimate 3).2.2.2.2
  have hS0 : C_secondGaussianEstimate 0 < (2 : ℝ) ^ 16 :=
    (constantSecondGaussianEstimate 0).2.1
  have hS3 : C_secondGaussianEstimate 3 < 767070519557262336 :=
    aux_C_secondGaussianEstimate_three_lt_value
  have hGmax : max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) < 176 := by
    apply max_lt
    · exact hG0.trans (by norm_num)
    · exact hG3
  have hSmax : max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) <
      767070519557262336 := by
    apply max_lt
    · exact hS0.trans (by norm_num)
    · exact hS3
  rw [C_fourScaleGaussianKernel, C_smoothDecay2]
  calc
    2 * (2 : ℝ) ^ 3 * max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate 3) +
        (2 : ℝ) ^ 3 * max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate 3) <
        2 * (2 : ℝ) ^ 3 * 176 + (2 : ℝ) ^ 3 * 767070519557262336 :=
      add_lt_add
        (mul_lt_mul_of_pos_left hGmax (by positivity))
        (mul_lt_mul_of_pos_left hSmax (by positivity))
    _ = 6136564156458101504 := by norm_num

/-- Source label `\ref{constant four scale Gaussian kernel}`. -/
theorem constantFourScaleGaussianKernel :
    (∀ N : ℕ, C_fourScaleGaussianKernel N ≤ (2 : ℝ) ^ (25 * (N + 1) ^ 3)) ∧
      C_fourScaleGaussianKernel 2 < (2 : ℝ) ^ 40 ∧
        C_fourScaleGaussianKernel 3 < (2 : ℝ) ^ 63 := by
  exact ⟨aux_C_fourScaleGaussianKernel_bound,
    aux_C_fourScaleGaussianKernel_two_lt_value.trans (by norm_num),
    aux_C_fourScaleGaussianKernel_three_lt_value.trans (by norm_num)⟩

/-- Source label `\ref{mean four scale Gaussian kernel}`; the explicit constant used by the
public theorem `meanFourScaleGaussianKernel`. -/
noncomputable def C_meanFourScaleGaussianKernel (N : ℕ) : ℝ :=
  5 * C_meanValueBumpEstimate N * aux_maxUpTo C_gaussianBumpEstimate N +
    4 * C_meanValueBumpEstimate N *
      aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N

/-- Transfer a pointwise normalized derivative bound to its `L∞` profile. -/
theorem aux_mean_profile_sSup_le (n : ℕ) (A : ℝ) (F : ℝ → ℂ)
    (h : ∀ xi : ℝ, ((2 * Real.pi)⁻¹ : ℝ) ^ n * ‖iteratedDeriv n F xi‖ ≤ A) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ n *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv n F xi‖) ≤ A := by
  have hq : 0 < ((2 * Real.pi)⁻¹ : ℝ) ^ n := by positivity
  have hs : sSup (Set.range fun xi : ℝ => ‖iteratedDeriv n F xi‖) ≤
      A / ((2 * Real.pi)⁻¹ : ℝ) ^ n := by
    apply csSup_le
    · exact Set.range_nonempty _
    rintro _ ⟨xi, rfl⟩
    apply (le_div_iff₀ hq).2
    calc
      ‖iteratedDeriv n F xi‖ * ((2 * Real.pi)⁻¹ : ℝ) ^ n =
          ((2 * Real.pi)⁻¹ : ℝ) ^ n * ‖iteratedDeriv n F xi‖ := by ring
      _ ≤ A := h xi
  calc
    ((2 * Real.pi)⁻¹ : ℝ) ^ n *
        sSup (Set.range fun xi : ℝ => ‖iteratedDeriv n F xi‖) ≤
      ((2 * Real.pi)⁻¹ : ℝ) ^ n * (A / ((2 * Real.pi)⁻¹ : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hs hq.le
    _ = A := by field_simp [ne_of_gt hq]

/-- Bound a finite `aux_maxUpTo` profile from its individual entries. -/
theorem aux_mean_maxUpTo_le (f : ℕ → ℝ) (N : ℕ) (B : ℝ)
    (h : ∀ n : ℕ, n ≤ N → f n ≤ B) :
    aux_maxUpTo f N ≤ B := by
  unfold aux_maxUpTo
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
  exact h n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

/-- The mean-value bump estimate for a normalized Gaussian-bump quotient. -/
theorem aux_mean_gaussian_base_difference (N : ℕ) (hN : 2 ≤ N)
    (c beta : ℝ) (phiHat : ℝ → ℂ) (hc : 0 < c)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (x y : ℝ) :
    ‖FourierTransformInv.fourierInv (gaussianBumpQuotient beta phiHat) (x + y) -
        FourierTransformInv.fourierInv (gaussianBumpQuotient beta phiHat) x‖ ≤
      C_meanValueBumpEstimate N *
        (c * aux_maxUpTo C_gaussianBumpEstimate N) *
        min 1 (2 * Real.pi * |y|) *
        (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
  let Q : ℝ → ℂ := gaussianBumpQuotient beta phiHat
  have hQ : ContDiff ℝ N Q :=
    aux_gaussianBumpEstimate_contDiff N beta phiHat hphi
  have hQsupp : tsupport Q ⊆ Set.Icc (-1 : ℝ) 1 := by
    change tsupport (fun xi : ℝ =>
      (((Gaussians.gaussian (beta * xi))⁻¹ : ℝ) : ℂ) * phiHat xi) ⊆ Set.Icc (-1 : ℝ) 1
    exact tsupport_mul_subset_right.trans hsupp
  have hQcompact : HasCompactSupport Q :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hQsupp
  let P : ℝ := aux_maxUpTo (fun m : ℕ =>
    ((2 * Real.pi)⁻¹ : ℝ) ^ m *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m Q xi‖)) N
  have hPm (m : ℕ) (hm : m ≤ N) :
      ((2 * Real.pi)⁻¹ : ℝ) ^ m *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m Q xi‖) ≤
        c * C_gaussianBumpEstimate m := by
    apply aux_mean_profile_sSup_le
    intro xi
    dsimp [Q]
    exact aux_gaussianBumpEstimate_pointwise m c beta phiHat hc.le hbeta0 hbeta1
      (hphi.of_le (by exact_mod_cast hm)) hsupp
      (fun k hk z => hphiBound k (hk.trans hm) z) xi
  have hP : P ≤ c * aux_maxUpTo C_gaussianBumpEstimate N := by
    dsimp [P]
    apply aux_mean_maxUpTo_le
    intro m hm
    calc
      ((2 * Real.pi)⁻¹ : ℝ) ^ m *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m Q xi‖) ≤
        c * C_gaussianBumpEstimate m := hPm m hm
      _ ≤ c * aux_maxUpTo C_gaussianBumpEstimate N :=
        mul_le_mul_of_nonneg_left (aux_le_maxUpTo C_gaussianBumpEstimate hm) hc.le
  have hbase := meanValueBumpEstimate N (by omega)
    (FourierTransformInv.fourierInv Q) Q
    ((smoothDecay2 N hN Q hQ hQcompact).1) rfl hQsupp hQ x y
  change ‖FourierTransformInv.fourierInv Q (x + y) -
      FourierTransformInv.fourierInv Q x‖ ≤ _
  calc
    ‖FourierTransformInv.fourierInv Q (x + y) -
        FourierTransformInv.fourierInv Q x‖ ≤
      C_meanValueBumpEstimate N * P * min 1 (2 * Real.pi * |y|) *
        (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
          simpa only [P] using hbase
    _ ≤ C_meanValueBumpEstimate N *
        (c * aux_maxUpTo C_gaussianBumpEstimate N) *
        min 1 (2 * Real.pi * |y|) *
        (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
      have hfactor : 0 ≤ C_meanValueBumpEstimate N *
          min 1 (2 * Real.pi * |y|) *
          (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
        apply mul_nonneg
        · apply mul_nonneg
          · unfold C_meanValueBumpEstimate
            positivity
          · exact le_min (by norm_num) (by positivity)
        · simp only [bracketBump]
          positivity
      calc
        C_meanValueBumpEstimate N * P * min 1 (2 * Real.pi * |y|) *
            (bracketBump (x + y) ^ N + bracketBump x ^ N) =
          (C_meanValueBumpEstimate N * min 1 (2 * Real.pi * |y|) *
            (bracketBump (x + y) ^ N + bracketBump x ^ N)) * P := by ring
        _ ≤ (C_meanValueBumpEstimate N * min 1 (2 * Real.pi * |y|) *
            (bracketBump (x + y) ^ N + bracketBump x ^ N)) *
            (c * aux_maxUpTo C_gaussianBumpEstimate N) :=
          mul_le_mul_of_nonneg_left hP hfactor
        _ = C_meanValueBumpEstimate N *
            (c * aux_maxUpTo C_gaussianBumpEstimate N) *
            min 1 (2 * Real.pi * |y|) *
              (bracketBump (x + y) ^ N + bracketBump x ^ N) := by ring

/-- Rescale a normalized mean-value difference bound on the Fourier side. -/
theorem aux_mean_rescaled_difference (N : ℕ) (Q : ℝ → ℂ) (a A : ℝ)
    (ha : 0 < a)
    (hbase : ∀ u v : ℝ,
      ‖FourierTransformInv.fourierInv Q (u + v) -
          FourierTransformInv.fourierInv Q u‖ ≤
        A * min 1 (2 * Real.pi * |v|) *
          (bracketBump (u + v) ^ N + bracketBump u ^ N))
    (x y : ℝ) :
    ‖FourierTransformInv.fourierInv (fun xi : ℝ => Q (a * xi)) (x + y) -
        FourierTransformInv.fourierInv (fun xi : ℝ => Q (a * xi)) x‖ ≤
      A * min 1 (2 * Real.pi * a⁻¹ * |y|) *
        (scaledBracketBump N a (x + y) + scaledBracketBump N a x) := by
  have hinv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hbase' := hbase (a⁻¹ * x) (a⁻¹ * y)
  have harg : a⁻¹ * x + a⁻¹ * y = a⁻¹ * (x + y) := by ring
  rw [harg] at hbase'
  have hscale : |a⁻¹ * y| = a⁻¹ * |y| := by
    rw [abs_mul, abs_of_nonneg hinv]
  rw [hscale] at hbase'
  rw [aux_inverseFourier_comp_mul_pos Q a (x + y) ha,
    aux_inverseFourier_comp_mul_pos Q a x ha, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
  calc
    a⁻¹ * ‖FourierTransformInv.fourierInv Q (a⁻¹ * (x + y)) -
        FourierTransformInv.fourierInv Q (a⁻¹ * x)‖ ≤
      a⁻¹ * (A * min 1 (2 * Real.pi * (a⁻¹ * |y|)) *
        (bracketBump (a⁻¹ * (x + y)) ^ N + bracketBump (a⁻¹ * x) ^ N)) :=
      mul_le_mul_of_nonneg_left hbase' hinv
    _ = A * min 1 (2 * Real.pi * a⁻¹ * |y|) *
        (scaledBracketBump N a (x + y) + scaledBracketBump N a x) := by
      simp only [scaledBracketBump, bracketBump]
      ring

/-- The rescaled Gaussian-bump component satisfies the normalized mean estimate. -/
theorem aux_mean_gaussian_rescaled_difference (N : ℕ) (hN : 2 ≤ N)
    (c beta a : ℝ) (phiHat : ℝ → ℂ) (hc : 0 < c)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) (ha : 0 < a)
    (hphi : ContDiff ℝ N phiHat)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (x y : ℝ) :
    ‖FourierTransformInv.fourierInv
        (fun xi : ℝ => gaussianBumpQuotient beta phiHat (a * xi)) (x + y) -
      FourierTransformInv.fourierInv
        (fun xi : ℝ => gaussianBumpQuotient beta phiHat (a * xi)) x‖ ≤
      C_meanValueBumpEstimate N *
        (c * aux_maxUpTo C_gaussianBumpEstimate N) *
        min 1 (2 * Real.pi * a⁻¹ * |y|) *
        (scaledBracketBump N a (x + y) + scaledBracketBump N a x) := by
  exact aux_mean_rescaled_difference N (gaussianBumpQuotient beta phiHat) a
    (C_meanValueBumpEstimate N * (c * aux_maxUpTo C_gaussianBumpEstimate N)) ha
    (fun u v => aux_mean_gaussian_base_difference N hN c beta phiHat hc hbeta0 hbeta1
      hphi hsupp hphiBound u v) x y

/-- Pull the Fourier support `[-1,1]` back under the map `xi ↦ 2 xi`. -/
theorem aux_mean_tsupport_comp_two_subset (phiHat : ℝ → ℂ)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1) :
    tsupport (fun xi : ℝ => phiHat (2 * xi)) ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  change closure (Function.support (fun xi : ℝ => phiHat (2 * xi))) ⊆
    Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  apply closure_minimal
  · intro xi hxi
    by_contra hxiIcc
    apply hxi
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hscaled := hsupp hmem
    have hinterval : xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      constructor <;> linarith [hscaled.1, hscaled.2]
    exact (hxiIcc hinterval).elim
  · exact isClosed_Icc

/-- The twice-rescaled second-Gaussian multiplier is supported in `[-1,1]`. -/
theorem aux_mean_second_tilde_support (phiHat : ℝ → ℂ) (mu lambda t nu : ℝ)
    (hlambda : lambda = 1 / 2)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1) :
    tsupport (fun xi : ℝ => secondGaussianMultiplier phiHat mu lambda t nu (2 * xi)) ⊆
      Set.Icc (-1 : ℝ) 1 := by
  change tsupport (fun xi : ℝ =>
    aux_secondGaussianQ phiHat mu lambda (2 * xi) * aux_secondGaussianS t nu (2 * xi)) ⊆
      Set.Icc (-1 : ℝ) 1
  refine tsupport_mul_subset_left.trans ?_
  change tsupport (fun xi : ℝ =>
    (((Gaussians.gaussian (mu * (2 * xi)))⁻¹ : ℝ) : ℂ) *
      (phiHat (lambda * (2 * xi)) - phiHat (2 * xi))) ⊆ Set.Icc (-1 : ℝ) 1
  refine tsupport_mul_subset_right.trans ?_
  refine (tsupport_sub _ _).trans ?_
  apply Set.union_subset
  · have heq : (fun xi : ℝ => phiHat (lambda * (2 * xi))) = phiHat := by
      funext xi
      rw [hlambda]
      congr 1
      ring
    rw [heq]
    exact hsupp
  · exact (aux_mean_tsupport_comp_two_subset phiHat hsupp).trans (by
      intro xi hxi
      constructor <;> linarith [hxi.1, hxi.2])

/-- Rescaling by `2` multiplies the normalized `L∞` derivative profile by at most `2^n`. -/
theorem aux_mean_profile_comp_two_le (n : ℕ) (F : ℝ → ℂ)
    (hF : ContDiff ℝ n F) (hFcompact : HasCompactSupport F) (A : ℝ)
    (h : ((2 * Real.pi)⁻¹ : ℝ) ^ n *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv n F xi‖) ≤ A) :
    ((2 * Real.pi)⁻¹ : ℝ) ^ n *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv n (fun xi : ℝ => F (2 * xi)) xi‖) ≤
        (2 : ℝ) ^ n * A := by
  have hFbdd : BddAbove (Set.range fun xi : ℝ => ‖iteratedDeriv n F xi‖) :=
    (hF.continuous_iteratedDeriv n (by simp)).norm.bddAbove_range_of_hasCompactSupport
      (aux_hasCompactSupport_iteratedDeriv F hFcompact n).norm
  apply aux_mean_profile_sSup_le
  intro xi
  have hmem : ‖iteratedDeriv n F (2 * xi)‖ ≤
      sSup (Set.range fun z : ℝ => ‖iteratedDeriv n F z‖) :=
    le_csSup hFbdd ⟨2 * xi, rfl⟩
  have hderiv := congrFun (iteratedDeriv_comp_const_smul hF 2) xi
  rw [hderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ((2 * Real.pi)⁻¹ : ℝ) ^ n *
        ((2 : ℝ) ^ n * ‖iteratedDeriv n F (2 * xi)‖) =
      (2 : ℝ) ^ n *
        (((2 * Real.pi)⁻¹ : ℝ) ^ n * ‖iteratedDeriv n F (2 * xi)‖) := by ring
    _ ≤ (2 : ℝ) ^ n *
        (((2 * Real.pi)⁻¹ : ℝ) ^ n *
          sSup (Set.range fun z : ℝ => ‖iteratedDeriv n F z‖)) := by
          gcongr
    _ ≤ (2 : ℝ) ^ n * A := mul_le_mul_of_nonneg_left h (by positivity)

/-- The normalized second-Gaussian component satisfies the mean-value bump estimate. -/
theorem aux_mean_second_tilde_base_difference (c : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (phi phiHat : ℝ → ℂ) (hphiW0 : MemW0 phi)
    (hphiHat : phiHat = FourierTransform.fourier phi) (hc : 0 < c)
    (mu lambda t nu : ℝ) (hmu : 0 < mu) (hmulambda : mu ≤ lambda)
    (hlambda : lambda ≤ 1 / 2) (hlambdaEq : lambda = 1 / 2)
    (ht : Real.sqrt 3 / 2 ≤ t) (hnu : nu ∈ Set.Ico (-1 : ℝ) 0)
    (hplateau : ∀ u ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat u = 1)
    (hphi : ContDiff ℝ N phiHat) (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (x y : ℝ) :
    ‖FourierTransformInv.fourierInv
        (fun xi : ℝ => secondGaussianMultiplier phiHat mu lambda t nu (2 * xi)) (x + y) -
      FourierTransformInv.fourierInv
        (fun xi : ℝ => secondGaussianMultiplier phiHat mu lambda t nu (2 * xi)) x‖ ≤
      C_meanValueBumpEstimate N *
        (c * aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N) *
        min 1 (2 * Real.pi * |y|) *
          (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
  let R : ℝ → ℂ := secondGaussianMultiplier phiHat mu lambda t nu
  let T : ℝ → ℂ := fun xi : ℝ => R (2 * xi)
  have hlambdaPos : 0 < lambda := hmu.trans_le hmulambda
  have hRcont : ContDiff ℝ N R := by
    simpa only [R] using
      (secondGaussianEstimate c N phi phiHat hphiW0 hphiHat hc mu lambda t nu hmu hmulambda
        hlambda ht hnu hplateau hphi hsupp hphiBound).1
  have hRcompact : HasCompactSupport R := by
    simpa only [R] using
      aux_secondGaussianMultiplier_hasCompactSupport phiHat mu lambda t nu hlambdaPos.ne' hsupp
  have hTcont : ContDiff ℝ N T := by
    dsimp [T]
    exact hRcont.comp (by fun_prop)
  have hTsupp : tsupport T ⊆ Set.Icc (-1 : ℝ) 1 := by
    dsimp [T, R]
    exact aux_mean_second_tilde_support phiHat mu lambda t nu hlambdaEq hsupp
  have hTcompact : HasCompactSupport T :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hTsupp
  let P : ℝ := aux_maxUpTo (fun m : ℕ =>
    ((2 * Real.pi)⁻¹ : ℝ) ^ m *
      sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m T xi‖)) N
  have hPm (m : ℕ) (hm : m ≤ N) :
      ((2 * Real.pi)⁻¹ : ℝ) ^ m *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m T xi‖) ≤
        c * ((2 : ℝ) ^ m * C_secondGaussianEstimate m) := by
    have hRm : ((2 * Real.pi)⁻¹ : ℝ) ^ m *
        sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m R xi‖) ≤
          c * C_secondGaussianEstimate m := by
      have hsecond := secondGaussianEstimate c m phi phiHat hphiW0 hphiHat hc mu lambda t nu
        hmu hmulambda hlambda ht hnu hplateau
        (hphi.of_le (by exact_mod_cast hm)) hsupp
        (fun k hk z => hphiBound k (hk.trans hm) z)
      calc
        ((2 * Real.pi)⁻¹ : ℝ) ^ m *
            sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m R xi‖) ≤
          ((2 * Real.pi)⁻¹ : ℝ) ^ m *
            max (∫ xi : ℝ, ‖iteratedDeriv m R xi‖)
              (sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m R xi‖)) := by
                gcongr
                exact le_max_right _ _
        _ ≤ c * C_secondGaussianEstimate m := by
          simpa only [R] using hsecond.2
    calc
      ((2 * Real.pi)⁻¹ : ℝ) ^ m *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m T xi‖) ≤
        (2 : ℝ) ^ m * (c * C_secondGaussianEstimate m) := by
          simpa only [T] using
            aux_mean_profile_comp_two_le m R (hRcont.of_le (by exact_mod_cast hm)) hRcompact
              (c * C_secondGaussianEstimate m) hRm
      _ = c * ((2 : ℝ) ^ m * C_secondGaussianEstimate m) := by ring
  have hP : P ≤ c * aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N := by
    dsimp [P]
    apply aux_mean_maxUpTo_le
    intro m hm
    calc
      ((2 * Real.pi)⁻¹ : ℝ) ^ m *
          sSup (Set.range fun xi : ℝ => ‖iteratedDeriv m T xi‖) ≤
        c * ((2 : ℝ) ^ m * C_secondGaussianEstimate m) := hPm m hm
      _ ≤ c * aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N :=
        mul_le_mul_of_nonneg_left
          (aux_le_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) hm) hc.le
  have hbase := meanValueBumpEstimate N (by omega)
    (FourierTransformInv.fourierInv T) T
    ((smoothDecay2 N hN T hTcont hTcompact).1) rfl hTsupp hTcont x y
  change ‖FourierTransformInv.fourierInv T (x + y) -
      FourierTransformInv.fourierInv T x‖ ≤ _
  calc
    ‖FourierTransformInv.fourierInv T (x + y) -
        FourierTransformInv.fourierInv T x‖ ≤
      C_meanValueBumpEstimate N * P * min 1 (2 * Real.pi * |y|) *
        (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
          simpa only [P] using hbase
    _ ≤ C_meanValueBumpEstimate N *
        (c * aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N) *
        min 1 (2 * Real.pi * |y|) *
          (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
      have hfactor : 0 ≤ C_meanValueBumpEstimate N * min 1 (2 * Real.pi * |y|) *
          (bracketBump (x + y) ^ N + bracketBump x ^ N) := by
        apply mul_nonneg
        · apply mul_nonneg
          · unfold C_meanValueBumpEstimate
            positivity
          · exact le_min (by norm_num) (by positivity)
        · simp only [bracketBump]
          positivity
      calc
        C_meanValueBumpEstimate N * P * min 1 (2 * Real.pi * |y|) *
            (bracketBump (x + y) ^ N + bracketBump x ^ N) =
          (C_meanValueBumpEstimate N * min 1 (2 * Real.pi * |y|) *
            (bracketBump (x + y) ^ N + bracketBump x ^ N)) * P := by ring
        _ ≤ (C_meanValueBumpEstimate N * min 1 (2 * Real.pi * |y|) *
            (bracketBump (x + y) ^ N + bracketBump x ^ N)) *
            (c * aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N) :=
          mul_le_mul_of_nonneg_left hP hfactor
        _ = C_meanValueBumpEstimate N *
            (c * aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N) *
            min 1 (2 * Real.pi * |y|) *
              (bracketBump (x + y) ^ N + bracketBump x ^ N) := by ring

/-- The elementary min comparison used when passing from the lower to the upper scale. -/
theorem aux_mean_min_double (z : ℝ) :
    min 1 (2 * z) ≤ 2 * min 1 z := by
  by_cases hzOne : 1 ≤ z
  · calc
      min 1 (2 * z) ≤ 1 := min_le_left _ _
      _ ≤ 2 * 1 := by norm_num
      _ = 2 * min 1 z := by rw [min_eq_left hzOne]
  · have hzOne' : z ≤ 1 := le_of_lt (lt_of_not_ge hzOne)
    calc
      min 1 (2 * z) ≤ 2 * z := min_le_right _ _
      _ = 2 * min 1 z := by rw [min_eq_right hzOne']

/-- Compare the lower-scale mean-value profile to the upper-scale profile when the scales differ
by a factor of two. -/
theorem aux_mean_half_scale_compare (N : ℕ) {lambdaMinus lambdaPlus x y : ℝ}
    (hlambdaMinus : 0 < lambdaMinus) (hlambdaPlus : 0 < lambdaPlus)
    (hhalf : lambdaPlus = 2 * lambdaMinus) :
    min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) *
        (scaledBracketBump N lambdaMinus (x + y) + scaledBracketBump N lambdaMinus x) ≤
      4 * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
        (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by
  have hscale : lambdaMinus ≤ lambdaPlus := by rw [hhalf]; nlinarith
  have hAt : lambdaPlus ≤ 2 * lambdaMinus := by rw [hhalf]
  have hbracket (z : ℝ) :
      scaledBracketBump N lambdaMinus z ≤ 2 * scaledBracketBump N lambdaPlus z :=
    aux_scaledBracketBump_scale_le N hlambdaMinus hlambdaPlus hscale (by norm_num) hAt
  have hbracketSum :
      scaledBracketBump N lambdaMinus (x + y) + scaledBracketBump N lambdaMinus x ≤
        2 * (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by
    calc
      scaledBracketBump N lambdaMinus (x + y) + scaledBracketBump N lambdaMinus x ≤
          2 * scaledBracketBump N lambdaPlus (x + y) + 2 * scaledBracketBump N lambdaPlus x :=
        add_le_add (hbracket (x + y)) (hbracket x)
      _ = 2 * (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by ring
  have hphase : 2 * Real.pi * lambdaMinus⁻¹ * |y| =
      2 * (2 * Real.pi * lambdaPlus⁻¹ * |y|) := by
    rw [hhalf]
    field_simp [hlambdaMinus.ne']
  let z : ℝ := 2 * Real.pi * lambdaPlus⁻¹ * |y|
  have hmin : min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) ≤ 2 * min 1 z := by
    rw [hphase]
    exact aux_mean_min_double z
  have hsumNonneg : 0 ≤ scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x := by
    apply add_nonneg <;> exact aux_scaledBracketBump_nonneg N hlambdaPlus _
  have hminNonneg : 0 ≤ min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) := by
    exact le_min (by norm_num) (by positivity)
  calc
    min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) *
        (scaledBracketBump N lambdaMinus (x + y) + scaledBracketBump N lambdaMinus x) ≤
        min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) *
          (2 * (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x)) :=
      mul_le_mul_of_nonneg_left hbracketSum hminNonneg
    _ ≤ (2 * min 1 z) * (2 * (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x)) :=
      mul_le_mul_of_nonneg_right hmin (mul_nonneg (by norm_num) hsumNonneg)
    _ = 4 * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
        (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by
      dsimp [z]
      ring

/-- Source label `\ref{mean four scale Gaussian kernel}`. -/
theorem meanFourScaleGaussianKernel (c : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (phi phiHat : ℝ → ℂ) (hphiW0 : MemW0 phi)
    (hphiHat : phiHat = FourierTransform.fourier phi) (hc : 0 < c)
    (hsupp : tsupport phiHat ⊆ Set.Icc (-1 : ℝ) 1)
    (hplateau : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), phiHat xi = 1)
    (hphi : ContDiff ℝ N phiHat)
    (hphiBound : ∀ m : ℕ, m ≤ N → ∀ xi : ℝ, ‖iteratedDeriv m phiHat xi‖ ≤ c)
    (muMinus muPlus lambdaMinus lambdaPlus nu : ℝ)
    (hmuMinus : 0 < muMinus) (hmuPlus : 0 < muPlus)
    (hlambdaMinus : 0 < lambdaMinus) (hlambdaPlus : 0 < lambdaPlus)
    (hscales : 2 * muMinus ≤ 2 * lambdaMinus ∧ 2 * lambdaMinus ≤ lambdaPlus ∧
      lambdaPlus ≤ muPlus)
    (hlambdaEq : lambdaPlus = 2 * lambdaMinus)
    (hnu : nu ∈ Set.Ico (-1 : ℝ) 0) :
    MemW0 (fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu) ∧
      ∀ x y : ℝ,
        ‖fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
          fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ ≤
          c * C_meanFourScaleGaussianKernel N *
            min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
              (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by
  rcases hscales with ⟨hscale0, hscale1, hscale2⟩
  let betaMinus : ℝ := muMinus * Real.sqrt |nu| / lambdaMinus
  let beta : ℝ := muMinus * Real.sqrt |nu| / lambdaPlus
  let a : ℝ := lambdaMinus / lambdaPlus
  let t : ℝ := Real.sqrt (muPlus ^ 2 - muMinus ^ 2) / lambdaPlus
  rcases aux_fourScaleGaussian_normalized_parameters hmuMinus hlambdaMinus hlambdaPlus hscale0 hscale1 hnu with
    ⟨hbetaMinus0, hbetaMinusOne, hbeta0, hbetaOne, hbetaPos, hbetaLeA, haOne⟩
  have hbetaMinus0' : 0 ≤ betaMinus := by simpa only [betaMinus] using hbetaMinus0
  have hbetaMinusOne' : betaMinus ≤ 1 := by simpa only [betaMinus] using hbetaMinusOne
  have hbeta0' : 0 ≤ beta := by simpa only [beta] using hbeta0
  have hbetaOne' : beta ≤ 1 := by simpa only [beta] using hbetaOne
  have hbetaPos' : 0 < beta := by simpa only [beta] using hbetaPos
  have hbetaLeA' : beta ≤ a := by simpa only [beta, a] using hbetaLeA
  have haOne' : a ≤ 1 / 2 := by simpa only [a] using haOne
  have haHalf : a = 1 / 2 := by
    dsimp [a]
    rw [hlambdaEq]
    field_simp [hlambdaMinus.ne']
  have ht : Real.sqrt 3 / 2 ≤ t := by
    simpa only [t] using aux_fourScaleGaussian_t_lower_bound hmuMinus hmuPlus hlambdaMinus hlambdaPlus
      hscale0 hscale1 hscale2
  let K : ℝ := C_meanValueBumpEstimate N
  let G : ℝ := aux_maxUpTo C_gaussianBumpEstimate N
  let S : ℝ := aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N
  have hK : 0 ≤ K := by
    dsimp [K, C_meanValueBumpEstimate]
    positivity
  have hG : 0 ≤ G := by
    dsimp [G]
    exact (aux_C_gaussianBumpEstimate_nonneg 0).trans
      (aux_le_maxUpTo C_gaussianBumpEstimate (Nat.zero_le _))
  have hS : 0 ≤ S := by
    dsimp [S]
    have hzero : 0 ≤ (2 : ℝ) ^ 0 * C_secondGaussianEstimate 0 := by
      simpa using aux_C_secondGaussianEstimate_nonneg 0
    exact hzero.trans
      (aux_le_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) (Nat.zero_le _))
  have hKG : 0 ≤ K * (c * G) := mul_nonneg hK (mul_nonneg hc.le hG)
  have hKS : 0 ≤ K * (c * S) := mul_nonneg hK (mul_nonneg hc.le hS)
  have h0eq := aux_fourScaleGaussian_varRho0_rescale phiHat muMinus lambdaMinus nu hlambdaMinus.ne'
  have h1eq := aux_fourScaleGaussian_varRho1_rescale phiHat muMinus lambdaPlus nu hlambdaPlus.ne'
  have h2eq := aux_fourScaleGaussian_varRho2_rescale phiHat muMinus muPlus lambdaMinus lambdaPlus nu
    hlambdaPlus.ne'
  have h0raw (x y : ℝ) :
      ‖fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu (x + y) -
        fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x‖ ≤
        K * (c * G) * min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) *
          (scaledBracketBump N lambdaMinus (x + y) + scaledBracketBump N lambdaMinus x) := by
    rw [h0eq]
    simpa only [K, G] using
      aux_mean_gaussian_rescaled_difference N hN c betaMinus lambdaMinus phiHat hc hbetaMinus0'
        hbetaMinusOne' hlambdaMinus hphi hsupp hphiBound x y
  have h1raw (x y : ℝ) :
      ‖fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu (x + y) -
        fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu x‖ ≤
        K * (c * G) * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
          (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by
    rw [h1eq]
    let F : ℝ → ℂ := FourierTransformInv.fourierInv (fun xi : ℝ => gaussianBumpQuotient
      (muMinus * Real.sqrt |nu| / lambdaPlus) phiHat (lambdaPlus * xi))
    change ‖-F (x + y) - -F x‖ ≤ _
    have hneg : -F (x + y) - -F x = -(F (x + y) - F x) := by ring
    rw [hneg, norm_neg]
    simpa [F, K, G, beta] using
      aux_mean_gaussian_rescaled_difference N hN c beta lambdaPlus phiHat hc hbeta0'
        hbetaOne' hlambdaPlus hphi hsupp hphiBound x y
  have h2frequency :
      (fun xi : ℝ => secondGaussianMultiplier phiHat beta a t nu (lambdaPlus * xi)) =
        (fun xi : ℝ => (fun z : ℝ => secondGaussianMultiplier phiHat beta a t nu (2 * z))
          (lambdaMinus * xi)) := by
    funext xi
    rw [hlambdaEq]
    congr 1
    ring
  have h2raw (x y : ℝ) :
      ‖fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
        fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ ≤
        K * (c * S) * min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) *
          (scaledBracketBump N lambdaMinus (x + y) + scaledBracketBump N lambdaMinus x) := by
    rw [h2eq, h2frequency]
    simpa only [K, S] using aux_mean_rescaled_difference N
      (fun z : ℝ => secondGaussianMultiplier phiHat beta a t nu (2 * z)) lambdaMinus
      (C_meanValueBumpEstimate N *
        (c * aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N))
      hlambdaMinus
      (fun u v => aux_mean_second_tilde_base_difference c N hN phi phiHat hphiW0 hphiHat hc
        beta a t nu hbetaPos' hbetaLeA' haOne' haHalf ht hnu hplateau hphi hsupp hphiBound u v) x y
  have h0 (x y : ℝ) :
      ‖fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu (x + y) -
        fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x‖ ≤
        4 * K * (c * G) * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
          (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by
    calc
      ‖fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu (x + y) -
          fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x‖ ≤
        K * (c * G) * (min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) *
          (scaledBracketBump N lambdaMinus (x + y) + scaledBracketBump N lambdaMinus x)) := by
          convert h0raw x y using 1 <;> ring
      _ ≤ K * (c * G) *
          (4 * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
            (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x)) :=
          mul_le_mul_of_nonneg_left
            (aux_mean_half_scale_compare N hlambdaMinus hlambdaPlus hlambdaEq) hKG
      _ = 4 * K * (c * G) * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
          (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by ring
  have h2 (x y : ℝ) :
      ‖fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
        fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ ≤
        4 * K * (c * S) * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
          (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by
    calc
      ‖fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
          fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ ≤
        K * (c * S) * (min 1 (2 * Real.pi * lambdaMinus⁻¹ * |y|) *
          (scaledBracketBump N lambdaMinus (x + y) + scaledBracketBump N lambdaMinus x)) := by
          convert h2raw x y using 1 <;> ring
      _ ≤ K * (c * S) *
          (4 * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
            (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x)) :=
          mul_le_mul_of_nonneg_left
            (aux_mean_half_scale_compare N hlambdaMinus hlambdaPlus hlambdaEq) hKS
      _ = 4 * K * (c * S) * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
          (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by ring
  have hmem := (fourScaleGaussianKernel c N hN phi phiHat hphiW0 hphiHat hc hsupp hplateau hphi
    hphiBound muMinus muPlus lambdaMinus lambdaPlus nu hmuMinus hmuPlus hlambdaMinus hlambdaPlus
    ⟨hscale0, hscale1, hscale2⟩ hnu).1
  refine ⟨hmem, ?_⟩
  intro x y
  have hdecompEq := (gaussianBumpDecomposition phi phiHat hphiW0 hphiHat hsupp hplateau
    hmuMinus hmuPlus hlambdaMinus hlambdaPlus ⟨hscale0, hscale1, hscale2⟩ hnu).2
  have hdecomp (z : ℝ) :
      fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu z =
        (fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu z +
          fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu z) +
          fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu z := by
    simpa only [Pi.add_apply] using congrFun hdecompEq z
  have hd :
      fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
        fourScaleGaussianRho phiHat muMinus muPlus lambdaMinus lambdaPlus nu x =
      ((fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu (x + y) -
          fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x) +
        (fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu (x + y) -
          fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu x)) +
        (fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
          fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x) := by
    rw [hdecomp (x + y), hdecomp x]
    ring
  rw [hd]
  calc
    ‖(fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu (x + y) -
        fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x +
      (fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu (x + y) -
        fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu x)) +
      (fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
        fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x)‖ ≤
      ‖fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu (x + y) -
        fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x +
        (fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu (x + y) -
          fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu x)‖ +
        ‖fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
          fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ :=
        norm_add_le _ _
    _ ≤ (‖fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu (x + y) -
        fourScaleGaussianVarRho0 phiHat muMinus lambdaMinus nu x‖ +
      ‖fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu (x + y) -
        fourScaleGaussianVarRho1 phiHat muMinus lambdaPlus nu x‖) +
        ‖fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu (x + y) -
          fourScaleGaussianVarRho2 phiHat muMinus muPlus lambdaMinus lambdaPlus nu x‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (4 * K * (c * G) * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
        (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) +
      K * (c * G) * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
        (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x)) +
        4 * K * (c * S) * min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
          (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) :=
        add_le_add (add_le_add (h0 x y) (h1raw x y)) (h2 x y)
    _ = c * C_meanFourScaleGaussianKernel N *
        min 1 (2 * Real.pi * lambdaPlus⁻¹ * |y|) *
          (scaledBracketBump N lambdaPlus (x + y) + scaledBracketBump N lambdaPlus x) := by
      dsimp [C_meanFourScaleGaussianKernel, K, G, S]
      ring

/-- Bound a finite `aux_maxUpTo` profile strictly from its individual entries. -/
theorem aux_mean_maxUpTo_lt (f : ℕ → ℝ) (N : ℕ) (B : ℝ)
    (h : ∀ n : ℕ, n ≤ N → f n < B) :
    aux_maxUpTo f N < B := by
  unfold aux_maxUpTo
  apply (Finset.max'_lt_iff _ _).mpr
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
  exact h n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

/-- The general explicit bound for the mean four-scale Gaussian-kernel constant. -/
theorem aux_C_meanFourScaleGaussianKernel_bound (N : ℕ) :
    C_meanFourScaleGaussianKernel N ≤ (2 : ℝ) ^ (30 * (N + 1) ^ 3) := by
  let K : ℝ := (2 : ℝ) ^ (2 * N + 1)
  let G : ℝ := (2 : ℝ) ^ (8 * (N + 1) ^ 2)
  let S : ℝ := (2 : ℝ) ^ (N + 20 * (N + 1) ^ 3)
  let M : ℝ := aux_maxUpTo C_gaussianBumpEstimate N
  let T : ℝ := aux_maxUpTo (fun n => (2 : ℝ) ^ n * C_secondGaussianEstimate n) N
  have hK : C_meanValueBumpEstimate N ≤ K := by
    simpa only [K] using aux_C_meanValueBumpEstimate_le N
  have hM : M ≤ G := by
    dsimp [M, G]
    apply aux_mean_maxUpTo_le
    intro n hn
    calc
      C_gaussianBumpEstimate n ≤ (2 : ℝ) ^ (8 * (n + 1) ^ 2) :=
        (constantGaussianBumpEstimate n).1
      _ ≤ (2 : ℝ) ^ (8 * (N + 1) ^ 2) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact Nat.mul_le_mul_left 8
          (Nat.pow_le_pow_left (Nat.succ_le_succ hn) 2)
  have hT : T ≤ S := by
    dsimp [T, S]
    apply aux_mean_maxUpTo_le
    intro n hn
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ N :=
      pow_le_pow_right₀ (by norm_num) hn
    have hsecond : C_secondGaussianEstimate n ≤ (2 : ℝ) ^ (20 * (N + 1) ^ 3) := by
      calc
        C_secondGaussianEstimate n ≤ (2 : ℝ) ^ (20 * (n + 1) ^ 3) :=
          (constantSecondGaussianEstimate n).1
        _ ≤ (2 : ℝ) ^ (20 * (N + 1) ^ 3) := by
          apply pow_le_pow_right₀ (by norm_num)
          exact Nat.mul_le_mul_left 20
            (Nat.pow_le_pow_left (Nat.succ_le_succ hn) 3)
    calc
      (2 : ℝ) ^ n * C_secondGaussianEstimate n ≤
          (2 : ℝ) ^ N * (2 : ℝ) ^ (20 * (N + 1) ^ 3) :=
        mul_le_mul hpow hsecond (aux_C_secondGaussianEstimate_nonneg n) (by positivity)
      _ = (2 : ℝ) ^ (N + 20 * (N + 1) ^ 3) := by rw [← pow_add]
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    exact (aux_C_gaussianBumpEstimate_nonneg 0).trans
      (aux_le_maxUpTo C_gaussianBumpEstimate (Nat.zero_le _))
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    have hzero : 0 ≤ (2 : ℝ) ^ 0 * C_secondGaussianEstimate 0 := by
      simpa using aux_C_secondGaussianEstimate_nonneg 0
    exact hzero.trans
      (aux_le_maxUpTo (fun n => (2 : ℝ) ^ n * C_secondGaussianEstimate n) (Nat.zero_le _))
  have hfirst : 5 * C_meanValueBumpEstimate N * M ≤ 5 * K * G := by
    have hKG : C_meanValueBumpEstimate N * M ≤ K * G :=
      mul_le_mul hK hM hMnonneg (by positivity)
    nlinarith [hKG]
  have hsecond : 4 * C_meanValueBumpEstimate N * T ≤ 4 * K * S := by
    have hKT : C_meanValueBumpEstimate N * T ≤ K * S :=
      mul_le_mul hK hT hTnonneg (by positivity)
    nlinarith [hKT]
  have hcubeOne : 1 ≤ (N + 1) ^ 3 := by
    calc
      1 = 1 ^ 3 := by norm_num
      _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.zero_le _)) 3
  have hNcube : N ≤ (N + 1) ^ 3 := by
    calc
      N ≤ N + 1 := Nat.le_succ _
      _ = (N + 1) ^ 1 := by simp
      _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have hsqCube : (N + 1) ^ 2 ≤ (N + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have hExpFirst : 4 + 2 * N + 8 * (N + 1) ^ 2 ≤ 30 * (N + 1) ^ 3 - 1 := by
    omega
  have hExpSecond : 3 * N + 3 + 20 * (N + 1) ^ 3 ≤ 30 * (N + 1) ^ 3 - 1 := by
    omega
  have hfirstPow : 5 * K * G ≤ (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) := by
    calc
      5 * K * G ≤ 8 * K * G := by
        have hKGnonneg : 0 ≤ K * G := mul_nonneg (by dsimp [K]; positivity)
          (by dsimp [G]; positivity)
        nlinarith
      _ = (2 : ℝ) ^ (4 + 2 * N + 8 * (N + 1) ^ 2) := by
        dsimp [K, G]
        rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) :=
        pow_le_pow_right₀ (by norm_num) hExpFirst
  have hsecondPow : 4 * K * S ≤ (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) := by
    calc
      4 * K * S = (2 : ℝ) ^ (3 * N + 3 + 20 * (N + 1) ^ 3) := by
        dsimp [K, S]
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) :=
        pow_le_pow_right₀ (by norm_num) hExpSecond
  have htargetPos : 0 < 30 * (N + 1) ^ 3 := by positivity
  rw [C_meanFourScaleGaussianKernel]
  change 5 * C_meanValueBumpEstimate N * M + 4 * C_meanValueBumpEstimate N * T ≤ _
  calc
    5 * C_meanValueBumpEstimate N * M + 4 * C_meanValueBumpEstimate N * T ≤
        5 * K * G + 4 * K * S := add_le_add hfirst hsecond
    _ ≤ (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) +
        (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) := add_le_add hfirstPow hsecondPow
    _ = (2 : ℝ) ^ (30 * (N + 1) ^ 3) := by
      calc
        (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) +
            (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) =
            (2 : ℝ) ^ (30 * (N + 1) ^ 3 - 1) * 2 := by ring
        _ = (2 : ℝ) ^ ((30 * (N + 1) ^ 3 - 1) + 1) := (pow_succ _ _).symm
        _ = (2 : ℝ) ^ (30 * (N + 1) ^ 3) := by
          congr 1

/-- The exact finite numerical upper bound at order two for the mean four-scale
Gaussian-kernel constant. -/
theorem aux_C_meanFourScaleGaussianKernel_two_lt_value :
    C_meanFourScaleGaussianKernel 2 < 20397963318112 := by
  have hM : aux_maxUpTo C_gaussianBumpEstimate 2 < 124 := by
    apply aux_mean_maxUpTo_lt
    intro n hn
    interval_cases n
    · exact (constantGaussianBumpEstimate 0).2.1.trans (by norm_num)
    · exact (constantGaussianBumpEstimate 0).2.2.1.trans (by norm_num)
    · exact (constantGaussianBumpEstimate 0).2.2.2.1
  have hS : aux_maxUpTo (fun n => (2 : ℝ) ^ n * C_secondGaussianEstimate n) 2 <
      4 * 159359088384 := by
    apply aux_mean_maxUpTo_lt
    intro n hn
    interval_cases n
    · calc
        (2 : ℝ) ^ 0 * C_secondGaussianEstimate 0 < (2 : ℝ) ^ 16 := by
          simpa using (constantSecondGaussianEstimate 0).2.1
        _ < 4 * 159359088384 := by norm_num
    · calc
        (2 : ℝ) ^ 1 * C_secondGaussianEstimate 1 = 2 * C_secondGaussianEstimate 1 := by
          norm_num
        _ < 2 * (2 : ℝ) ^ 22 :=
          mul_lt_mul_of_pos_left (constantSecondGaussianEstimate 0).2.2.1 (by norm_num)
        _ < 4 * 159359088384 := by norm_num
    · calc
        (2 : ℝ) ^ 2 * C_secondGaussianEstimate 2 = 4 * C_secondGaussianEstimate 2 := by
          norm_num
        _ < 4 * 159359088384 :=
          mul_lt_mul_of_pos_left aux_C_secondGaussianEstimate_two_lt_value (by norm_num)
  rw [C_meanFourScaleGaussianKernel, aux_C_meanValueBumpEstimate_two]
  have hfirst : 5 * 8 * aux_maxUpTo C_gaussianBumpEstimate 2 < 5 * 8 * 124 :=
    mul_lt_mul_of_pos_left hM (by norm_num)
  have hsecond : 4 * 8 * aux_maxUpTo (fun n => (2 : ℝ) ^ n * C_secondGaussianEstimate n) 2 <
      4 * 8 * (4 * 159359088384) := mul_lt_mul_of_pos_left hS (by norm_num)
  calc
    5 * 8 * aux_maxUpTo C_gaussianBumpEstimate 2 +
        4 * 8 * aux_maxUpTo (fun n => (2 : ℝ) ^ n * C_secondGaussianEstimate n) 2 <
        5 * 8 * 124 + 4 * 8 * (4 * 159359088384) := add_lt_add hfirst hsecond
    _ = 20397963318112 := by norm_num

/-- The sharp finite-order mean four-scale Gaussian-kernel constant estimate. -/
theorem aux_C_meanFourScaleGaussianKernel_two_lt :
    C_meanFourScaleGaussianKernel 2 < (2 : ℝ) ^ 45 :=
  aux_C_meanFourScaleGaussianKernel_two_lt_value.trans (by norm_num)

/-- Source label `\ref{constant mean four scale Gaussian kernel}`. -/
theorem constantMeanFourScaleGaussianKernel :
    (∀ N : ℕ, C_meanFourScaleGaussianKernel N ≤ (2 : ℝ) ^ (30 * (N + 1) ^ 3)) ∧
      C_meanFourScaleGaussianKernel 2 < (2 : ℝ) ^ 45 := by
  exact ⟨aux_C_meanFourScaleGaussianKernel_bound, aux_C_meanFourScaleGaussianKernel_two_lt⟩

end

end Codex.Preliminaries.BumpsAndEstimates
