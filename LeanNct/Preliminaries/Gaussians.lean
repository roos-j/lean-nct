import LeanNct.WienerSpace
import LeanNct.Preliminaries.Notation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Gaussians

The Gaussian objects from the manuscript, together with the Fourier-normalized facts supplied by
mathlib.
-/

namespace Codex.Preliminaries.Gaussians

open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
open Codex.Preliminaries.Notation

noncomputable section

/--
Recall that $\g(x)=e^{-\pi x^2}$ for $x\in\R$.
-/
abbrev gaussian : ℝ → ℝ := Notation.gaussian

/--
For $\lambda>0$, the rescaled Gaussian is $\g_{(\lambda)}(x)=\lambda^{-1}\g(\lambda^{-1}x)$.
-/
def gaussianRescale (t : ℝ) : ℝ → ℝ := fun x => t⁻¹ * gaussian (t⁻¹ * x)

/-- The explicit constant prescribed by Proposition \ref{Gaussian bump decay}. -/
def C_gaussianBumpDecay (m N : ℕ) : ℝ :=
  Real.rpow (100 * ((m + N + 1 : ℕ) : ℝ)) (((m + N : ℕ) : ℝ) / 2)

/-- The Gaussian is strictly positive at every real point. -/
theorem aux_gaussian_pos (x : ℝ) : 0 < gaussian x := by
  change 0 < Real.exp (-Real.pi * x ^ 2)
  exact Real.exp_pos _

/-- The Gaussian takes values at most one. -/
theorem aux_gaussian_le_one (x : ℝ) : gaussian x ≤ 1 := by
  change Real.exp (-Real.pi * x ^ 2) ≤ 1
  apply Real.exp_le_one_iff.mpr
  nlinarith [Real.pi_pos, sq_nonneg x]

/-- The Gaussian is an even function. -/
theorem aux_gaussian_neg (x : ℝ) : gaussian (-x) = gaussian x := by
  change Real.exp (-Real.pi * (-x) ^ 2) = Real.exp (-Real.pi * x ^ 2)
  congr 1
  ring

/-- This is the zero-th, zero-decay instance of the Gaussian bump estimate and is useful when
normalizing later Gaussian bounds. -/
theorem aux_gaussianBumpDecay_zero_zero (x : ℝ) :
    |gaussian x| ≤ C_gaussianBumpDecay 0 0 * bracketBump x ^ 0 := by
  rw [abs_of_pos (aux_gaussian_pos x)]
  simp only [pow_zero, mul_one, C_gaussianBumpDecay]
  norm_num [Real.rpow_zero]
  exact aux_gaussian_le_one x

/-- This auxiliary quadratic-decay estimate supplies the zero-order case used below. -/
theorem gaussian_le_four_bracket_sq (x : ℝ) :
    gaussian x ≤ 4 * bracketBump x ^ 2 := by
  rw [bracketBump]
  have hden : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos (by positivity)
  have hrewrite : 4 * (1 + |x|)⁻¹ ^ 2 = 4 / (1 + |x|) ^ 2 := by
    field_simp
  rw [hrewrite]
  by_cases hx : |x| ≤ 1
  · calc
      gaussian x ≤ 1 := aux_gaussian_le_one x
      _ ≤ 4 / (1 + |x|) ^ 2 := by
        apply (le_div_iff₀ hden).2
        have hbase : 1 + |x| ≤ (2 : ℝ) := by linarith
        have hsquare : (1 + |x|) ^ 2 ≤ (2 : ℝ) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by norm_num)).2 hbase
        norm_num at hsquare
        nlinarith
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    have hApos : 0 < 1 + Real.pi * x ^ 2 := by positivity
    have hexp : 1 + Real.pi * x ^ 2 ≤ Real.exp (Real.pi * x ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (Real.pi * x ^ 2)
    have hinv : Real.exp (-Real.pi * x ^ 2) ≤ (1 + Real.pi * x ^ 2)⁻¹ := by
      rw [show -Real.pi * x ^ 2 = -(Real.pi * x ^ 2) by ring, Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) hApos).2 hexp
    calc
      gaussian x = Real.exp (-Real.pi * x ^ 2) := rfl
      _ ≤ (1 + Real.pi * x ^ 2)⁻¹ := hinv
      _ ≤ 4 / (1 + |x|) ^ 2 := by
        have hrewrite' : 4 / (1 + |x|) ^ 2 = ((1 + |x|) ^ 2 / 4)⁻¹ := by
          field_simp
        rw [hrewrite']
        apply (inv_le_inv₀ hApos (by positivity)).2
        rw [← sq_abs x]
        have hquad : (1 + |x|) ^ 2 ≤ 4 * |x| ^ 2 := by
          nlinarith [sq_nonneg (|x| - 1)]
        have hpi : 3 * |x| ^ 2 ≤ Real.pi * |x| ^ 2 :=
          mul_le_mul_of_nonneg_right (le_of_lt Real.pi_gt_three) (sq_nonneg _)
        nlinarith

/-- This auxiliary quartic-decay estimate is used when differentiating the Gaussian. -/
theorem gaussian_le_sixteen_bracket_four (x : ℝ) :
    gaussian x ≤ 16 * bracketBump x ^ 4 := by
  rw [bracketBump]
  have hden : 0 < (1 + |x|) ^ 4 := pow_pos (by positivity) _
  have hrewrite : 16 * (1 + |x|)⁻¹ ^ 4 = 16 / (1 + |x|) ^ 4 := by
    field_simp
  rw [hrewrite]
  by_cases hx : |x| ≤ 1
  · calc
      gaussian x ≤ 1 := aux_gaussian_le_one x
      _ ≤ 16 / (1 + |x|) ^ 4 := by
        apply (le_div_iff₀ hden).2
        have hbase : 1 + |x| ≤ (2 : ℝ) := by linarith
        have hpower : (1 + |x|) ^ 4 ≤ (2 : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hbase 4
        norm_num at hpower
        nlinarith
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    let a : ℝ := Real.pi * x ^ 2
    have ha : 0 ≤ a := by
      dsimp [a]
      positivity
    have hhalf : a / 2 ≤ Real.exp (a / 2) := by
      calc
        a / 2 ≤ 1 + a / 2 := by linarith
        _ ≤ Real.exp (a / 2) := by
          simpa [add_comm] using Real.add_one_le_exp (a / 2)
    have hsquare : (a / 2) ^ 2 ≤ Real.exp (a / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hhalf 2
    have hexpa : (a / 2) ^ 2 ≤ Real.exp a := by
      calc
        (a / 2) ^ 2 ≤ Real.exp (a / 2) ^ 2 := hsquare
        _ = Real.exp a := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
    have hpi2 : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hpi2mul : 2 * x ^ 2 ≤ Real.pi * x ^ 2 :=
      mul_le_mul_of_nonneg_right hpi2 (sq_nonneg _)
    have hrsq : |x| ^ 2 ≤ a / 2 := by
      rw [sq_abs]
      dsimp [a]
      nlinarith
    have hrfour : |x| ^ 4 ≤ (a / 2) ^ 2 := by
      calc
        |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
        _ ≤ (a / 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hrsq 2
    have hrpos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx'
    have hrfourpos : 0 < |x| ^ 4 := pow_pos hrpos _
    have hinv : Real.exp (-a) ≤ (|x| ^ 4)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) hrfourpos).2 (hrfour.trans hexpa)
    have hscale : (1 + |x|) ^ 4 / 16 ≤ |x| ^ 4 := by
      have hbase : 1 + |x| ≤ 2 * |x| := by linarith
      have hpower : (1 + |x|) ^ 4 ≤ (2 * |x|) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase 4
      have htwopow : (2 * |x|) ^ 4 = 16 * |x| ^ 4 := by ring
      rw [htwopow] at hpower
      nlinarith
    have hlast : (|x| ^ 4)⁻¹ ≤ 16 / (1 + |x|) ^ 4 := by
      have hrewrite' : 16 / (1 + |x|) ^ 4 = ((1 + |x|) ^ 4 / 16)⁻¹ := by
        field_simp
      rw [hrewrite']
      exact (inv_le_inv₀ hrfourpos (by positivity)).2 hscale
    calc
      gaussian x = Real.exp (-a) := by simp [a, gaussian, Notation.gaussian]
      _ ≤ (|x| ^ 4)⁻¹ := hinv
      _ ≤ 16 / (1 + |x|) ^ 4 := hlast

/-- This rescaled zero-order bound is the instance of Gaussian decay used by the diagonal kernel. -/
theorem gaussianRescale_le_C_gaussianBumpDecay_zero_two {t x : ℝ} (ht : 0 < t) :
    |gaussianRescale t x| ≤
      C_gaussianBumpDecay 0 2 * scaledBracketBump 2 t x := by
  rw [gaussianRescale,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ht.le) (aux_gaussian_pos _).le)]
  change t⁻¹ * gaussian (t⁻¹ * x) ≤
    C_gaussianBumpDecay 0 2 * (t⁻¹ * bracketBump (t⁻¹ * x) ^ 2)
  have hC : (4 : ℝ) ≤ C_gaussianBumpDecay 0 2 := by
    norm_num [C_gaussianBumpDecay, Real.rpow_one]
  calc
    t⁻¹ * gaussian (t⁻¹ * x) ≤ t⁻¹ * (4 * bracketBump (t⁻¹ * x) ^ 2) :=
      mul_le_mul_of_nonneg_left (gaussian_le_four_bracket_sq (t⁻¹ * x))
        (inv_nonneg.mpr ht.le)
    _ ≤ t⁻¹ * (C_gaussianBumpDecay 0 2 * bracketBump (t⁻¹ * x) ^ 2) := by
      gcongr
    _ = C_gaussianBumpDecay 0 2 * (t⁻¹ * bracketBump (t⁻¹ * x) ^ 2) := by ring

/-- This auxiliary derivative formula starts the first-order Gaussian decay estimate. -/
theorem gaussian_hasDerivAt (x : ℝ) :
    HasDerivAt gaussian (-2 * Real.pi * x * gaussian x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  have hinner : HasDerivAt (fun y : ℝ => -Real.pi * y ^ 2) (-2 * Real.pi * x) x := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hpow.const_mul (-Real.pi)
  change HasDerivAt (fun y : ℝ => Real.exp (-Real.pi * y ^ 2))
    (-2 * Real.pi * x * Real.exp (-Real.pi * x ^ 2)) x
  convert (Real.hasDerivAt_exp (-Real.pi * x ^ 2)).comp x hinner using 1 <;> first | rfl | ring

/-- This auxiliary chain-rule formula transports the Gaussian derivative through rescaling. -/
theorem gaussianRescale_hasDerivAt (t x : ℝ) :
    HasDerivAt (gaussianRescale t)
      (t⁻¹ * (-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)) * t⁻¹) x := by
  have hlinear : HasDerivAt (fun y : ℝ => t⁻¹ * y) t⁻¹ x := hasDerivAt_const_mul t⁻¹
  have hcomposed := (gaussian_hasDerivAt (t⁻¹ * x)).comp x hlinear
  have hscaled := hcomposed.const_mul t⁻¹
  change HasDerivAt (fun y : ℝ => t⁻¹ * gaussian (t⁻¹ * y))
    (t⁻¹ * (-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)) * t⁻¹) x
  convert hscaled using 1 <;> first | rfl | ring

/-- This auxiliary estimate is the first-derivative, quadratic-decay Gaussian bound needed to
transport the manuscript's derivative estimate through a positive rescaling. -/
theorem aux_gaussian_deriv_le_C_gaussianBumpDecay_one_two (x : ℝ) :
    |-2 * Real.pi * x * gaussian x| ≤
      C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 := by
  have hbracket : |x| * bracketBump x ^ 4 ≤ bracketBump x ^ 2 := by
    rw [bracketBump]
    have hden : 0 < 1 + |x| := by positivity
    have habs : |x| ≤ (1 + |x|) ^ 2 := by
      nlinarith [abs_nonneg x]
    calc
      |x| * (1 + |x|)⁻¹ ^ 4 ≤
          (1 + |x|) ^ 2 * (1 + |x|)⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      _ = (1 + |x|)⁻¹ ^ 2 := by
        field_simp [ne_of_gt hden]
  have hconstant : 32 * Real.pi ≤ C_gaussianBumpDecay 1 2 := by
    calc
      32 * Real.pi ≤ 128 := by nlinarith [Real.pi_le_four]
      _ ≤ 400 := by norm_num
      _ ≤ C_gaussianBumpDecay 1 2 := by
        convert Real.self_le_rpow_of_one_le (x := (400 : ℝ)) (y := (3 : ℝ) / 2)
          (by norm_num) (by norm_num) using 1 <;>
          norm_num [C_gaussianBumpDecay]
  have hfactor : 0 ≤ 2 * Real.pi * |x| := by positivity
  calc
    |-2 * Real.pi * x * gaussian x| = 2 * Real.pi * |x| * gaussian x := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg Real.pi_pos.le,
        abs_of_nonneg (aux_gaussian_pos x).le]
    _ ≤ 2 * Real.pi * |x| * (16 * bracketBump x ^ 4) :=
      mul_le_mul_of_nonneg_left (gaussian_le_sixteen_bracket_four x) hfactor
    _ = (32 * Real.pi) * (|x| * bracketBump x ^ 4) := by ring
    _ ≤ (32 * Real.pi) * bracketBump x ^ 2 :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ C_gaussianBumpDecay 1 2 * bracketBump x ^ 2 :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)

/-- This first-order rescaled estimate is a downstream instance of Gaussian bump decay. -/
theorem gaussianRescale_deriv_bound {t x : ℝ} (ht : 0 < t) :
    |deriv (gaussianRescale t) x| ≤
      t⁻¹ * C_gaussianBumpDecay 1 2 * scaledBracketBump 2 t x := by
  rw [(gaussianRescale_hasDerivAt t x).deriv]
  have htin : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  have hbase := aux_gaussian_deriv_le_C_gaussianBumpDecay_one_two (t⁻¹ * x)
  calc
    |t⁻¹ * (-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)) * t⁻¹| =
        t⁻¹ * |-2 * Real.pi * (t⁻¹ * x) * gaussian (t⁻¹ * x)| * t⁻¹ := by
      rw [abs_mul, abs_mul, abs_of_nonneg htin]
    _ ≤ t⁻¹ * (C_gaussianBumpDecay 1 2 * bracketBump (t⁻¹ * x) ^ 2) * t⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase htin) htin
    _ = t⁻¹ * C_gaussianBumpDecay 1 2 * scaledBracketBump 2 t x := by
      unfold scaledBracketBump
      simp only [bracketBump]
      ring

/-- Auxiliary for Proposition \ref{Elementary Gaussian properties}, formalized as
gaussian_memW0. It supplies the continuity used there. -/
theorem gaussian_continuous : Continuous gaussian := by
  fun_prop [gaussian, Notation.gaussian]

/-- Auxiliary for Proposition \ref{Elementary Gaussian properties}, formalized as
gaussian_memW0. It supplies the integrability used there. -/
theorem gaussian_integrable : Integrable gaussian := by
  change Integrable (fun x : ℝ => Real.exp (-Real.pi * x ^ 2))
  exact integrable_exp_neg_mul_sq Real.pi_pos

/-- This auxiliary envelope estimate supplies the integrable majorant needed to put the Gaussian
in the manuscript's Wiener space. -/
theorem aux_wienerEnvelope_gaussian_le (x : ℝ) :
    wienerEnvelope gaussian 1 x ≤
      Real.exp Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) := by
  unfold wienerEnvelope
  apply csSup_le
  · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
  rintro _ ⟨z, hz, rfl⟩
  change ‖gaussian (x + z)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (aux_gaussian_pos _)]
  change Real.exp (-Real.pi * (x + z) ^ 2) ≤
    Real.exp Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)
  have hzabs : |z| ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hz
  have hzsq : z ^ 2 ≤ 1 := by
    rw [← sq_abs z]
    simpa using (sq_le_sq₀ (abs_nonneg z) zero_le_one).mpr hzabs
  have hsq : x ^ 2 / 2 - 1 ≤ (x + z) ^ 2 := by
    nlinarith [sq_nonneg (x + 2 * z)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos, hsq]

/-- Proposition \ref{Elementary Gaussian properties}, claim (i): $\g\in W_0(\R)$. -/
theorem gaussian_memW0 : MemW0 gaussian := by
  refine ⟨gaussian_continuous, ?_⟩
  have hmajorant : Integrable (fun x : ℝ =>
      Real.exp Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 2)).const_mul (Real.exp Real.pi)
  refine hmajorant.mono_nonneg
    (continuous_wienerEnvelope gaussian_continuous 1).aestronglyMeasurable
    (ae_of_all _ fun x => aux_wienerEnvelope_nonneg gaussian_continuous zero_le_one x)
    (ae_of_all _ aux_wienerEnvelope_gaussian_le)

/-- This auxiliary envelope estimate transports the Gaussian Wiener bound to a positive
rescaling. -/
theorem aux_wienerEnvelope_gaussianRescale_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    wienerEnvelope (gaussianRescale t) 1 x ≤
      t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2) := by
  have htin : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  unfold wienerEnvelope
  apply csSup_le
  · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
  rintro _ ⟨z, hz, rfl⟩
  change ‖t⁻¹ * gaussian (t⁻¹ * (x + z))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htin,
    abs_of_pos (aux_gaussian_pos _)]
  have hzabs : |z| ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hz
  have hzsq : z ^ 2 ≤ 1 := by
    rw [← sq_abs z]
    simpa using (sq_le_sq₀ (abs_nonneg z) zero_le_one).mpr hzabs
  have hscaled_z_sq : (t⁻¹ * z) ^ 2 ≤ t⁻¹ ^ 2 := by
    calc
      (t⁻¹ * z) ^ 2 = t⁻¹ ^ 2 * z ^ 2 := by ring
      _ ≤ t⁻¹ ^ 2 * 1 := mul_le_mul_of_nonneg_left hzsq (sq_nonneg _)
      _ = t⁻¹ ^ 2 := by ring
  have hsq_base : (t⁻¹ * x) ^ 2 / 2 - (t⁻¹ * z) ^ 2 ≤
      (t⁻¹ * x + t⁻¹ * z) ^ 2 := by
    nlinarith [sq_nonneg (t⁻¹ * x + 2 * (t⁻¹ * z))]
  have hsq : (t⁻¹ * x) ^ 2 / 2 - t⁻¹ ^ 2 ≤ (t⁻¹ * (x + z)) ^ 2 := by
    calc
      (t⁻¹ * x) ^ 2 / 2 - t⁻¹ ^ 2 ≤
          (t⁻¹ * x) ^ 2 / 2 - (t⁻¹ * z) ^ 2 := sub_le_sub_left hscaled_z_sq _
      _ ≤ (t⁻¹ * x + t⁻¹ * z) ^ 2 := hsq_base
      _ = (t⁻¹ * (x + z)) ^ 2 := by ring
  have hexp : Real.exp (-Real.pi * (t⁻¹ * (x + z)) ^ 2) ≤
      Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, hsq]
  change t⁻¹ * Real.exp (-Real.pi * (t⁻¹ * (x + z)) ^ 2) ≤ _
  calc
    t⁻¹ * Real.exp (-Real.pi * (t⁻¹ * (x + z)) ^ 2) ≤
        t⁻¹ * (Real.exp (Real.pi * t⁻¹ ^ 2) *
          Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp htin
    _ = t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2) := by ring

/-- Positive rescalings of the Gaussian remain in the manuscript's Wiener space; this helper is
used by the sandwich-kernel construction. -/
theorem gaussianRescale_memW0 {t : ℝ} (ht : 0 < t) : MemW0 (gaussianRescale t) := by
  have hcontinuous : Continuous (gaussianRescale t) := by
    unfold gaussianRescale
    exact continuous_const.mul
      (gaussian_continuous.comp (continuous_const.mul continuous_id))
  refine ⟨hcontinuous, ?_⟩
  have hcoefficient : 0 < Real.pi / 2 * t⁻¹ ^ 2 := by
    positivity
  have hmajorant : Integrable (fun x : ℝ =>
      t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2) *
        Real.exp (-(Real.pi / 2) * (t⁻¹ * x) ^ 2)) := by
    have hbase := (integrable_exp_neg_mul_sq hcoefficient).const_mul
      (t⁻¹ * Real.exp (Real.pi * t⁻¹ ^ 2))
    convert hbase using 1
    funext x
    congr 2
    ring
  refine hmajorant.mono_nonneg
    (continuous_wienerEnvelope hcontinuous 1).aestronglyMeasurable
    (ae_of_all _ fun x => aux_wienerEnvelope_nonneg hcontinuous zero_le_one x)
    (ae_of_all _ fun x => aux_wienerEnvelope_gaussianRescale_le ht x)

/--
The standard Gaussian from the manuscript has unit integral. -/
theorem aux_integral_gaussian : ∫ x : ℝ, gaussian x = 1 := by
  have h := integral_gaussian Real.pi
  simpa [gaussian, Notation.gaussian, Real.pi_ne_zero, div_self, Real.sqrt_one] using h

/-- Proposition \ref{Elementary Gaussian properties}, claim (ii): $\widehat{\g}=\g$. -/
theorem gaussian_fourier_fixed :
    FourierTransform.fourier (fun x : ℝ => (gaussian x : ℂ)) =
      fun ξ : ℝ => (gaussian ξ : ℂ) := by
  simpa [gaussian, Notation.gaussian] using
    (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num))

/-- Definition used in Proposition \ref{square root one minus Gaussian}, formalized by
continuous_sqrtOneMinusGaussian, sqrtOneMinusGaussian_lower, and
sqrtOneMinusGaussian_bounds. -/
def sqrtOneMinusGaussian (x : ℝ) : ℝ := Real.sqrt (1 - gaussian x)

/-- This auxiliary theorem verifies the nonnegative radicand needed to use the manuscript's
nonnegative square root. -/
theorem aux_one_sub_gaussian_nonneg (x : ℝ) : 0 ≤ 1 - gaussian x := by
  rw [show gaussian x = Real.exp (-Real.pi * x ^ 2) by rfl]
  apply sub_nonneg.mpr
  apply Real.exp_le_one_iff.mpr
  nlinarith [Real.pi_pos, sq_nonneg x]

/-- Proposition \ref{square root one minus Gaussian}: $x\mapsto\sqrt{1-\g(x)}$ is continuous. -/
theorem continuous_sqrtOneMinusGaussian : Continuous sqrtOneMinusGaussian := by
  apply Continuous.sqrt
  exact continuous_const.sub gaussian_continuous

/-- Proposition \ref{square root one minus Gaussian}: for $|x|\le\tfrac12$,
$\sqrt{1-\g(x)}\ge\tfrac12|x|$. -/
theorem sqrtOneMinusGaussian_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    1 / 2 * |x| ≤ sqrtOneMinusGaussian x := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have h : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hpi_sq_nonneg : 0 ≤ Real.pi * x ^ 2 :=
    mul_nonneg Real.pi_pos.le (sq_nonneg x)
  have hden_pos : 0 < 1 + Real.pi * x ^ 2 := by positivity
  have hpi_sq_le : Real.pi * x ^ 2 ≤ 1 := by
    calc
      Real.pi * x ^ 2 ≤ 4 * x ^ 2 := by
        exact mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (sq_nonneg x)
      _ ≤ 4 * (1 / 4) := by
        exact mul_le_mul_of_nonneg_left hx2 (by norm_num)
      _ = 1 := by norm_num
  have hden_le : 1 + Real.pi * x ^ 2 ≤ 2 := by linarith
  have hexp : 1 + Real.pi * x ^ 2 ≤ Real.exp (Real.pi * x ^ 2) := by
    simpa [add_comm] using Real.add_one_le_exp (Real.pi * x ^ 2)
  have hrecip : Real.exp (-Real.pi * x ^ 2) ≤ (1 + Real.pi * x ^ 2)⁻¹ := by
    rw [show -Real.pi * x ^ 2 = -(Real.pi * x ^ 2) by ring, Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hden_pos).2 hexp
  have hfrac : x ^ 2 / 4 ≤ 1 - (1 + Real.pi * x ^ 2)⁻¹ := by
    have hid : 1 - (1 + Real.pi * x ^ 2)⁻¹ =
        (Real.pi * x ^ 2) / (1 + Real.pi * x ^ 2) := by
      field_simp
      ring
    rw [hid]
    have hrewrite : x ^ 2 / 4 =
        (x ^ 2 / 4 * (1 + Real.pi * x ^ 2)) / (1 + Real.pi * x ^ 2) := by
      field_simp
    rw [hrewrite]
    apply (div_le_div_iff_of_pos_right hden_pos).2
    calc
      x ^ 2 / 4 * (1 + Real.pi * x ^ 2) ≤ x ^ 2 / 4 * 2 := by
        gcongr
      _ = x ^ 2 / 2 := by ring
      _ ≤ Real.pi * x ^ 2 := by nlinarith [sq_nonneg x, Real.pi_gt_three]
  have hrad : x ^ 2 / 4 ≤ 1 - gaussian x := by
    change x ^ 2 / 4 ≤ 1 - Real.exp (-Real.pi * x ^ 2)
    linarith
  apply le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt]
  · calc
      (1 / 2 * |x|) ^ 2 = x ^ 2 / 4 := by
        rw [show (1 / 2 * |x|) ^ 2 = (1 / 2 : ℝ) ^ 2 * |x| ^ 2 by ring, sq_abs]
        ring
      _ ≤ 1 - gaussian x := hrad
  · exact aux_one_sub_gaussian_nonneg x

/-- Proposition \ref{square root one minus Gaussian}: for $|x|\ge\tfrac12$,
$1-\g(x)\le\sqrt{1-\g(x)}\le1$. -/
theorem sqrtOneMinusGaussian_bounds (x : ℝ) (_hx : 1 / 2 ≤ |x|) :
    1 - gaussian x ≤ sqrtOneMinusGaussian x ∧ sqrtOneMinusGaussian x ≤ 1 := by
  let y := 1 - gaussian x
  have hy0 : 0 ≤ y := aux_one_sub_gaussian_nonneg x
  have hy1 : y ≤ 1 := by
    dsimp [y]
    have hgpos : 0 < gaussian x := by
      rw [show gaussian x = Real.exp (-Real.pi * x ^ 2) by rfl]
      exact Real.exp_pos _
    linarith
  have hsqrt : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0
  have hsqrtnonneg : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  constructor
  · change y ≤ Real.sqrt y
    nlinarith
  · change Real.sqrt y ≤ 1
    nlinarith

/-- This auxiliary derivative is used in the removable-singularity analysis of the
derivatives of the manuscript's auxiliary function $B$. -/
theorem aux_one_sub_gaussian_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - gaussian y)
      (2 * Real.pi * x * gaussian x) x := by
  have hraw0 := (hasDerivAt_const x (1 : ℝ)).sub (gaussian_hasDerivAt x)
  have hscalar : 0 - (-2 * Real.pi * x * gaussian x) =
      2 * Real.pi * x * gaussian x := by ring
  rw [← hscalar]
  exact hraw0.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp)

/-- This auxiliary L'Hôpital computation identifies the quadratic coefficient of
`1 - \g` at the origin.  It is used to remove the square-root singularity in $B'$. -/
theorem aux_one_sub_gaussian_div_sq_tendsto :
    Tendsto (fun x : ℝ => (1 - gaussian x) / x ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 Real.pi) := by
  refine HasDerivAt.lhopital_zero_nhdsNE
    (f := fun x : ℝ => 1 - gaussian x)
    (g := fun x : ℝ => x ^ 2)
    (f' := fun x : ℝ => 2 * Real.pi * x * gaussian x)
    (g' := fun x : ℝ => 2 * x) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall aux_one_sub_gaussian_hasDerivAt
  · exact Filter.Eventually.of_forall fun x => by
      have hraw0 := (hasDerivAt_id x).mul (hasDerivAt_id x)
      have hscalar : 1 * x + x * 1 = 2 * x := by ring
      have hraw : HasDerivAt (fun y : ℝ => y * y) (2 * x) x := by
        rw [← hscalar]
        exact hraw0.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y => by simp [pow_two])
      simpa only [pow_two] using hraw
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero (by norm_num) hx0
  · have hcont : Continuous (fun x : ℝ => (1 : ℝ) - gaussian x) :=
      continuous_const.sub gaussian_continuous
    have h := hcont.tendsto (0 : ℝ)
    simpa [gaussian, Notation.gaussian] using h.mono_left nhdsWithin_le_nhds
  · have hcont : Continuous (fun x : ℝ => x ^ 2) := continuous_id.pow 2
    have h := hcont.tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  · have hcont : Continuous (fun x : ℝ => Real.pi * gaussian x) :=
      continuous_const.mul gaussian_continuous
    have h : Tendsto (fun x : ℝ => Real.pi * gaussian x)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 Real.pi) := by
      have h' := hcont.tendsto (0 : ℝ)
      simpa [gaussian, Notation.gaussian] using h'.mono_left nhdsWithin_le_nhds
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    field_simp [hx0]

/-- This auxiliary limit is the positive square-root form of the preceding quadratic
Gaussian quotient.  It makes the extension at the origin in the formula for $B'$ explicit. -/
theorem aux_sqrtOneMinusGaussian_div_abs_tendsto :
    Tendsto (fun x : ℝ => sqrtOneMinusGaussian x / |x|)
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 (Real.sqrt Real.pi)) := by
  refine aux_one_sub_gaussian_div_sq_tendsto.sqrt.congr' ?_
  exact Filter.Eventually.of_forall fun x => by
    change Real.sqrt ((1 - gaussian x) / x ^ 2) =
      sqrtOneMinusGaussian x / |x|
    unfold sqrtOneMinusGaussian
    rw [Real.sqrt_div (aux_one_sub_gaussian_nonneg x), Real.sqrt_sq_eq_abs]

/-- This auxiliary positivity statement supplies the nonzero square-root denominators that
occur in the formula for $B'$ away from the origin. -/
theorem aux_sqrtOneMinusGaussian_pos {x : ℝ} (hx : x ≠ 0) :
    0 < sqrtOneMinusGaussian x := by
  apply Real.sqrt_pos.2
  apply sub_pos.mpr
  have hneg : -Real.pi * x ^ 2 < 0 := by
    nlinarith [Real.pi_pos, sq_pos_of_ne_zero hx]
  simpa [gaussian, Notation.gaussian] using (Real.exp_lt_exp.mpr hneg)

/-- Definition used in Proposition \ref{poisson to abel}, formalized as
poissonKernel_fourier. -/
def poissonKernel (x : ℝ) : ℝ := 2 * (1 + (2 * Real.pi * x) ^ 2)⁻¹

/-- The Poisson kernel in the manuscript is strictly positive. -/
theorem aux_poissonKernel_pos (x : ℝ) : 0 < poissonKernel x := by
  unfold poissonKernel
  positivity

/-- This auxiliary frequency-side function is the asserted Fourier transform
$e^{-|\xi|}$ of the manuscript's Poisson kernel. -/
def aux_poissonFrequency (ξ : ℝ) : ℝ := Real.exp (-|ξ|)

/-- This auxiliary continuity fact supplies a Fourier-inversion hypothesis for the Poisson
kernel. -/
theorem aux_poissonKernel_continuous : Continuous poissonKernel := by
  unfold poissonKernel
  refine continuous_const.mul ?_
  refine Continuous.inv₀ ?_ ?_
  · fun_prop
  · intro x
    positivity

/-- This auxiliary integrability fact supplies a Fourier-inversion hypothesis for the Poisson
kernel. -/
theorem aux_poissonKernel_integrable : Integrable poissonKernel := by
  have hmajorant : Integrable (fun x : ℝ => 2 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul 2
  refine hmajorant.mono_nonneg aux_poissonKernel_continuous.aestronglyMeasurable
    (ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · unfold poissonKernel
    positivity
  · unfold poissonKernel
    have hscale : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hsq : x ^ 2 ≤ (2 * Real.pi * x) ^ 2 := by
      calc
        x ^ 2 = 1 * x ^ 2 := by ring
        _ ≤ (2 * Real.pi) ^ 2 * x ^ 2 := by
          gcongr
          nlinarith [sq_nonneg (2 * Real.pi - 1)]
        _ = (2 * Real.pi * x) ^ 2 := by ring
    have hden : 1 + x ^ 2 ≤ 1 + (2 * Real.pi * x) ^ 2 := by linarith
    have hdenpos : 0 < 1 + x ^ 2 := by positivity
    have hinv : (1 + (2 * Real.pi * x) ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le hdenpos hden
    gcongr

/-- This auxiliary continuity fact is used to apply Fourier inversion to the Abel profile. -/
theorem aux_poissonFrequency_continuous : Continuous aux_poissonFrequency := by
  unfold aux_poissonFrequency
  fun_prop

/-- This auxiliary theorem supplies the integrability hypothesis for Fourier inversion in the
Poisson-to-Abel identity by splitting $e^{-|\xi|}$ at the origin. -/
theorem aux_poissonFrequency_integrable : Integrable aux_poissonFrequency := by
  have hleft : IntegrableOn aux_poissonFrequency (Set.Iic (0 : ℝ)) := by
    refine (integrableOn_exp_Iic 0).congr_fun ?_ measurableSet_Iic
    intro ξ hξ
    have hξ' : ξ ≤ 0 := hξ
    simp [aux_poissonFrequency, abs_of_nonpos hξ']
  have hright : IntegrableOn aux_poissonFrequency (Set.Ioi (0 : ℝ)) := by
    refine (integrableOn_exp_neg_Ioi 0).congr_fun ?_ measurableSet_Ioi
    intro ξ hξ
    have hξ' : 0 < ξ := hξ
    simp [aux_poissonFrequency, abs_of_pos hξ']
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi]
  exact hleft.union hright

/-- This auxiliary integral evaluation normalizes the Abel profile used in the Poisson-to-Abel
argument. -/
theorem aux_integral_poissonFrequency : ∫ ξ : ℝ, aux_poissonFrequency ξ = 2 := by
  have hleft : IntegrableOn aux_poissonFrequency (Set.Iic (0 : ℝ)) := by
    refine (integrableOn_exp_Iic 0).congr_fun ?_ measurableSet_Iic
    intro ξ hξ
    have hξ' : ξ ≤ 0 := hξ
    simp [aux_poissonFrequency, abs_of_nonpos hξ']
  have hright : IntegrableOn aux_poissonFrequency (Set.Ioi (0 : ℝ)) := by
    refine (integrableOn_exp_neg_Ioi 0).congr_fun ?_ measurableSet_Ioi
    intro ξ hξ
    have hξ' : 0 < ξ := hξ
    simp [aux_poissonFrequency, abs_of_pos hξ']
  have hleft_value : (∫ ξ in Set.Iic (0 : ℝ), aux_poissonFrequency ξ) = 1 := by
    calc
      (∫ ξ in Set.Iic (0 : ℝ), aux_poissonFrequency ξ) =
          ∫ ξ in Set.Iic (0 : ℝ), Real.exp ξ := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro ξ hξ
        have hξ' : ξ ≤ 0 := hξ
        simp [aux_poissonFrequency, abs_of_nonpos hξ']
      _ = 1 := integral_exp_Iic_zero
  have hright_value : (∫ ξ in Set.Ioi (0 : ℝ), aux_poissonFrequency ξ) = 1 := by
    calc
      (∫ ξ in Set.Ioi (0 : ℝ), aux_poissonFrequency ξ) =
          ∫ ξ in Set.Ioi (0 : ℝ), Real.exp (-ξ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro ξ hξ
        have hξ' : 0 < ξ := hξ
        simp [aux_poissonFrequency, abs_of_pos hξ']
      _ = 1 := integral_exp_neg_Ioi_zero
  calc
    (∫ ξ : ℝ, aux_poissonFrequency ξ) =
        ∫ ξ in Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ), aux_poissonFrequency ξ := by
      rw [Set.Iic_union_Ioi, setIntegral_univ]
    _ = (∫ ξ in Set.Iic (0 : ℝ), aux_poissonFrequency ξ) +
          ∫ ξ in Set.Ioi (0 : ℝ), aux_poissonFrequency ξ :=
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hleft hright
    _ = 2 := by rw [hleft_value, hright_value]; norm_num

/-- This auxiliary computation is the inverse-Fourier half of the Poisson-to-Abel identity.
It evaluates the two exponential half-line integrals before applying Fourier inversion. -/
theorem aux_inverseFourier_poissonFrequency (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ)) x =
      (poissonKernel x : ℂ) := by
  let ω : ℝ := 2 * Real.pi * x
  let F : ℝ → ℂ := fun ξ =>
    Complex.exp ((↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I) *
      (aux_poissonFrequency ξ : ℂ)
  let aNeg : ℂ := -1 + (ω : ℂ) * Complex.I
  let aPos : ℂ := 1 + (ω : ℂ) * Complex.I
  have hleft_eq : Set.EqOn F (fun ξ : ℝ => Complex.exp (aPos * ξ)) (Set.Iic 0) := by
    intro ξ hξ
    dsimp [F, aPos, ω, aux_poissonFrequency]
    have hξ' : ξ ≤ 0 := hξ
    rw [abs_of_nonpos hξ']
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hright_eq : Set.EqOn F (fun ξ : ℝ => Complex.exp (aNeg * ξ)) (Set.Ioi 0) := by
    intro ξ hξ
    dsimp [F, aNeg, ω, aux_poissonFrequency]
    have hξ' : 0 < ξ := hξ
    rw [abs_of_pos hξ']
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hleft_exp : IntegrableOn (fun ξ : ℝ => Complex.exp (aPos * ξ)) (Set.Iic 0) := by
    apply integrableOn_exp_mul_complex_Iic
    simp [aPos]
  have hright_exp : IntegrableOn (fun ξ : ℝ => Complex.exp (aNeg * ξ)) (Set.Ioi 0) := by
    apply integrableOn_exp_mul_complex_Ioi
    simp [aNeg]
  have hleft : IntegrableOn F (Set.Iic 0) :=
    hleft_exp.congr_fun hleft_eq.symm measurableSet_Iic
  have hright : IntegrableOn F (Set.Ioi 0) :=
    hright_exp.congr_fun hright_eq.symm measurableSet_Ioi
  have hleft_value : ∫ ξ in Set.Iic (0 : ℝ), F ξ = 1 / aPos := by
    calc
      (∫ ξ in Set.Iic (0 : ℝ), F ξ) =
          ∫ ξ in Set.Iic (0 : ℝ), Complex.exp (aPos * ξ) :=
        setIntegral_congr_fun measurableSet_Iic hleft_eq
      _ = 1 / aPos := by
        simpa using (integral_exp_mul_complex_Iic (a := aPos) (by simp [aPos]) 0)
  have hright_value : ∫ ξ in Set.Ioi (0 : ℝ), F ξ = -1 / aNeg := by
    calc
      (∫ ξ in Set.Ioi (0 : ℝ), F ξ) =
          ∫ ξ in Set.Ioi (0 : ℝ), Complex.exp (aNeg * ξ) :=
        setIntegral_congr_fun measurableSet_Ioi hright_eq
      _ = -1 / aNeg := by
        simpa using (integral_exp_mul_complex_Ioi (a := aNeg) (by simp [aNeg]) 0)
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul, Real.inner_apply]
  change (∫ ξ : ℝ, F ξ) = _
  calc
    (∫ ξ : ℝ, F ξ) = ∫ ξ in Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ), F ξ := by
      rw [Set.Iic_union_Ioi, setIntegral_univ]
    _ = (∫ ξ in Set.Iic (0 : ℝ), F ξ) + ∫ ξ in Set.Ioi (0 : ℝ), F ξ :=
      setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hleft hright
    _ = 1 / aPos + -1 / aNeg := by rw [hleft_value, hright_value]
    _ = (poissonKernel x : ℂ) := by
      have hpos : (1 + (ω : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num at hre
      have hneg : (-1 + (ω : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num at hre
      have hden : 1 + ω ^ 2 ≠ 0 := by positivity
      have hdenC : 1 + (ω : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast hden
      calc
        1 / aPos + -1 / aNeg = (2 : ℂ) / ((1 + ω ^ 2 : ℝ) : ℂ) := by
          dsimp [aPos, aNeg]
          push_cast
          field_simp [hpos, hneg, hdenC]
          ring_nf
          rw [Complex.I_sq]
          ring
        _ = (poissonKernel x : ℂ) := by
          rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div]
          congr 1

/-- Proposition \ref{poisson to abel}: $\widehat p(\xi)=e^{-|\xi|}$. -/
theorem poissonKernel_fourier :
    FourierTransform.fourier (fun x : ℝ => (poissonKernel x : ℂ)) =
      fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ) := by
  let q : ℝ → ℂ := fun ξ => (aux_poissonFrequency ξ : ℂ)
  have hq_continuous : Continuous q :=
    Complex.continuous_ofReal.comp aux_poissonFrequency_continuous
  have hq_integrable : Integrable q := by
    change Integrable (fun ξ : ℝ => (aux_poissonFrequency ξ : ℂ))
    exact aux_poissonFrequency_integrable.ofReal
  have hinv : FourierTransformInv.fourierInv q =
      fun x : ℝ => (poissonKernel x : ℂ) := by
    funext x
    simpa [q] using aux_inverseFourier_poissonFrequency x
  have hq_neg : (fun x : ℝ => q (-x)) = q := by
    funext x
    simp [q, aux_poissonFrequency]
  have hinv_eq_fourier : FourierTransformInv.fourierInv q =
      FourierTransform.fourier q := by
    calc
      FourierTransformInv.fourierInv q =
          FourierTransform.fourier (fun x : ℝ => q (-x)) :=
        Real.fourierInv_eq_fourier_comp_neg q
      _ = FourierTransform.fourier q := by rw [hq_neg]
  have hqFourierIntegrable : Integrable (FourierTransform.fourier q) := by
    rw [← hinv_eq_fourier, hinv]
    exact aux_poissonKernel_integrable.ofReal
  rw [← hinv]
  exact hq_continuous.fourier_fourierInv_eq hq_integrable hqFourierIntegrable

/-- This auxiliary estimate controls the Abel profile at the scale $\sqrt\pi$ by the
integrable unscaled Abel profile. -/
theorem aux_exp_neg_abs_sqrt_pi_le_poissonFrequency (x : ℝ) :
    Real.exp (-|Real.sqrt Real.pi * x|) ≤ aux_poissonFrequency x := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hsqrt_ge_one : 1 ≤ Real.sqrt Real.pi := by
    nlinarith [Real.pi_gt_three]
  unfold aux_poissonFrequency
  apply Real.exp_le_exp.mpr
  rw [abs_mul, abs_of_nonneg hsqrt_nonneg]
  nlinarith [abs_nonneg x]

/-- This auxiliary theorem proves integrability of the Abel profile appearing in $B$ after
the manuscript's $\sqrt\pi$ rescaling. -/
theorem aux_exp_neg_abs_sqrt_pi_integrable :
    Integrable (fun x : ℝ => Real.exp (-|Real.sqrt Real.pi * x|)) := by
  refine aux_poissonFrequency_integrable.mono_nonneg
    (by fun_prop) (ae_of_all _ fun x => by positivity)
    (ae_of_all _ aux_exp_neg_abs_sqrt_pi_le_poissonFrequency)

/-- Definition used in Proposition \ref{auxiliary function B}, formalized by
auxiliaryFunctionB_properties. -/
def auxiliaryFunctionB (ξ : ℝ) : ℝ :=
  1 - sqrtOneMinusGaussian ξ - Real.exp (-|Real.sqrt Real.pi * ξ|)

/-- This auxiliary rewrite verifies that the concrete definition of $B$ uses precisely the
Fourier transform of the Poisson kernel appearing in the manuscript. -/
theorem aux_auxiliaryFunctionB_eq_fourierPoisson (ξ : ℝ) :
    auxiliaryFunctionB ξ = 1 - sqrtOneMinusGaussian ξ -
      (FourierTransform.fourier (fun x : ℝ => (poissonKernel x : ℂ))
        (Real.sqrt Real.pi * ξ)).re := by
  rw [poissonKernel_fourier]
  change 1 - sqrtOneMinusGaussian ξ - Real.exp (-|Real.sqrt Real.pi * ξ|) =
    1 - sqrtOneMinusGaussian ξ -
      (Complex.exp ((- |Real.sqrt Real.pi * ξ| : ℝ) : ℂ)).re
  rw [Complex.exp_ofReal_re]

/-- This auxiliary continuity fact supplies the continuity clause of
`auxiliaryFunctionB_properties`, the formalization of Proposition \ref{auxiliary function B}. -/
theorem aux_auxiliaryFunctionB_continuous : Continuous auxiliaryFunctionB := by
  unfold auxiliaryFunctionB
  exact (continuous_const.sub continuous_sqrtOneMinusGaussian).sub
    (Real.continuous_exp.comp
      ((continuous_abs.comp (continuous_const.mul continuous_id)).neg))

/-- Auxiliary for Proposition \ref{auxiliary function B}, formalized as
auxiliaryFunctionB_properties. It is the chosen extension representing $B'$. -/
def auxiliaryFunctionBDerivative (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x) +
      Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
        Real.exp (-|Real.sqrt Real.pi * x|)

/-- This auxiliary off-origin derivative computation supplies the $B'$ formula used in
`auxiliaryFunctionB_properties`. -/
theorem aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt auxiliaryFunctionB (auxiliaryFunctionBDerivative x) x := by
  have hgauss_lt_one : gaussian x < 1 := by
    have hneg : -Real.pi * x ^ 2 < 0 := by
      nlinarith [Real.pi_pos, sq_pos_of_ne_zero hx]
    simpa [gaussian, Notation.gaussian] using (Real.exp_lt_exp.mpr hneg)
  have hrad_pos : 0 < 1 - gaussian x := sub_pos.mpr hgauss_lt_one
  have hrad_deriv : HasDerivAt (fun y : ℝ => 1 - gaussian y)
      (2 * Real.pi * x * gaussian x) x := by
    have hraw0 := (hasDerivAt_const x (1 : ℝ)).sub (gaussian_hasDerivAt x)
    have hscalar : 0 - (-2 * Real.pi * x * gaussian x) =
        2 * Real.pi * x * gaussian x := by ring
    rw [← hscalar]
    exact hraw0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
  have hsqrt : HasDerivAt sqrtOneMinusGaussian
      ((2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)) x := by
    unfold sqrtOneMinusGaussian
    exact hrad_deriv.sqrt (ne_of_gt hrad_pos)
  have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hlinear : HasDerivAt (fun y : ℝ => Real.sqrt Real.pi * y) (Real.sqrt Real.pi) x := by
    exact hasDerivAt_const_mul (x := x) (Real.sqrt Real.pi)
  have habs : HasDerivAt (fun y : ℝ => |Real.sqrt Real.pi * y|)
      ((SignType.sign (Real.sqrt Real.pi * x) : ℝ) * Real.sqrt Real.pi) x := by
    exact (hasDerivAt_abs (mul_ne_zero (ne_of_gt hsqrtpi) hx)).comp x hlinear
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-|Real.sqrt Real.pi * y|))
      (Real.exp (-|Real.sqrt Real.pi * x|) *
        (-((SignType.sign (Real.sqrt Real.pi * x) : ℝ) * Real.sqrt Real.pi))) x := by
    exact (Real.hasDerivAt_exp (-|Real.sqrt Real.pi * x|)).comp x habs.neg
  have hB := ((hasDerivAt_const x 1).sub hsqrt).sub hexp
  have hD : auxiliaryFunctionBDerivative x =
      0 - (2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x) -
        (Real.exp (-|Real.sqrt Real.pi * x|) *
          (-((SignType.sign (Real.sqrt Real.pi * x) : ℝ) * Real.sqrt Real.pi))) := by
    simp [auxiliaryFunctionBDerivative, hx]
    ring
  rw [hD]
  exact hB.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => by simp [auxiliaryFunctionB])

/-- This auxiliary smoothness fact supplies the off-origin smoothness clause of
`auxiliaryFunctionB_properties`. -/
theorem aux_auxiliaryFunctionB_smoothOffZero :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) auxiliaryFunctionB ({0}ᶜ : Set ℝ) := by
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hgauss_lt_one : gaussian x < 1 := by
    have hneg : -Real.pi * x ^ 2 < 0 := by
      nlinarith [Real.pi_pos, sq_pos_of_ne_zero hx0]
    simpa [gaussian, Notation.gaussian] using (Real.exp_lt_exp.mpr hneg)
  have hrad : 1 - gaussian x ≠ 0 := ne_of_gt (sub_pos.mpr hgauss_lt_one)
  have hgaussian : ContDiff ℝ (↑(⊤ : ℕ∞)) gaussian := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => Real.exp (-Real.pi * y ^ 2))
    fun_prop
  have hsqrt : ContDiffAt ℝ (↑(⊤ : ℕ∞)) sqrtOneMinusGaussian x := by
    unfold sqrtOneMinusGaussian
    exact (contDiffAt_const.sub hgaussian.contDiffAt).sqrt hrad
  have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hlinear : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => Real.sqrt Real.pi * y) x := by
    exact (contDiff_const.mul contDiff_id).contDiffAt
  have habsAbs : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (|·| : ℝ → ℝ) (Real.sqrt Real.pi * x) := by
    simpa using
      (contDiffAt_abs (n := (⊤ : ℕ∞)) (mul_ne_zero (ne_of_gt hsqrtpi) hx0))
  have habs : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ => |Real.sqrt Real.pi * y|) x :=
    habsAbs.comp x hlinear
  have hexp : ContDiffAt ℝ (↑(⊤ : ℕ∞))
      (fun y : ℝ => Real.exp (-|Real.sqrt Real.pi * y|)) x :=
    Real.contDiff_exp.contDiffAt.comp x habs.neg
  unfold auxiliaryFunctionB
  exact ((contDiffAt_const.sub hsqrt).sub hexp).contDiffWithinAt

/-- This auxiliary continuity statement transfers the smooth off-origin derivative of $B$ to
the explicit formula used for its continuous extension. -/
theorem aux_auxiliaryFunctionBDerivative_continuousAt_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt auxiliaryFunctionBDerivative x := by
  have hmem : x ∈ ({0}ᶜ : Set ℝ) := by simpa using hx
  have hopen : ({0}ᶜ : Set ℝ) ∈ 𝓝 x :=
    (isOpen_compl_singleton : IsOpen ({0}ᶜ : Set ℝ)).mem_nhds hmem
  have hBdiff : ContDiffAt ℝ (↑(⊤ : ℕ∞)) auxiliaryFunctionB x :=
    (aux_auxiliaryFunctionB_smoothOffZero x hmem).contDiffAt hopen
  have hderiv : ContinuousAt (deriv auxiliaryFunctionB) x :=
    (hBdiff.derivWithin (m := 0) (by simp)).continuousAt
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact (aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero hy).deriv.symm

/-- This auxiliary deleted-neighborhood limit verifies that the displayed formula for $B'$ has
the continuous value zero at the origin. -/
theorem aux_auxiliaryFunctionBDerivative_tendsto_zero :
    Tendsto auxiliaryFunctionBDerivative
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 0) := by
  let q : ℝ → ℝ := fun y => sqrtOneMinusGaussian y / |y|
  have hsqrtpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsqrtpi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrtpi_pos
  have hpi_div : Real.pi / Real.sqrt Real.pi = Real.sqrt Real.pi := by
    apply (div_eq_iff hsqrtpi_ne).2
    calc
      Real.pi = (Real.sqrt Real.pi) ^ 2 := (Real.sq_sqrt Real.pi_pos.le).symm
      _ = Real.sqrt Real.pi * Real.sqrt Real.pi := by ring
  have hq : Tendsto q (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ))
      (𝓝 (Real.sqrt Real.pi)) := by
    simpa only [q] using aux_sqrtOneMinusGaussian_div_abs_tendsto
  have hpiGaussian : Tendsto (fun y : ℝ => Real.pi * gaussian y)
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 Real.pi) := by
    have hcont : Continuous (fun y : ℝ => Real.pi * gaussian y) :=
      continuous_const.mul gaussian_continuous
    have h := hcont.tendsto (0 : ℝ)
    simpa [gaussian, Notation.gaussian] using h.mono_left nhdsWithin_le_nhds
  have habel : Tendsto (fun y : ℝ =>
      Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (𝓝 (Real.sqrt Real.pi)) := by
    have hcont : Continuous (fun y : ℝ =>
        Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|)) := by
      fun_prop
    have h := hcont.tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hq_right : Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_gt hy)) hq
  have hpiGaussian_right : Tendsto (fun y : ℝ => Real.pi * gaussian y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 Real.pi) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_gt hy)) hpiGaussian
  have habel_right : Tendsto (fun y : ℝ =>
      Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_gt hy)) habel
  have hquotient_right : Tendsto (fun y : ℝ =>
      (Real.pi * gaussian y) / q y) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (Real.sqrt Real.pi)) := by
    have hd := hpiGaussian_right.div hq_right hsqrtpi_ne
    rw [hpi_div] at hd
    refine hd.congr' ?_
    filter_upwards [] with y
    rfl
  have hright_raw : Tendsto (fun y : ℝ =>
      -(Real.pi * gaussian y / q y) +
        Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    simpa using hquotient_right.neg.add habel_right
  have hright : Tendsto auxiliaryFunctionBDerivative
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    refine hright_raw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have hroot : sqrtOneMinusGaussian y ≠ 0 :=
      (aux_sqrtOneMinusGaussian_pos hy0).ne'
    have hscale : 0 < Real.sqrt Real.pi * y := mul_pos hsqrtpi_pos hy
    dsimp only [q]
    simp only [auxiliaryFunctionBDerivative, if_neg hy0,
      sign_pos hscale, one_mul]
    rw [abs_of_pos hy]
    field_simp [hroot, hy0]
    norm_num
  have hq_left : Tendsto q (nhdsWithin (0 : ℝ) (Set.Iio 0))
      (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_lt hy)) hq
  have hpiGaussian_left : Tendsto (fun y : ℝ => Real.pi * gaussian y)
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 Real.pi) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_lt hy)) hpiGaussian
  have habel_left : Tendsto (fun y : ℝ =>
      Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 (Real.sqrt Real.pi)) :=
    tendsto_nhdsWithin_mono_left
      (by intro y hy; simpa using (ne_of_lt hy)) habel
  have hquotient_left : Tendsto (fun y : ℝ =>
      (Real.pi * gaussian y) / q y) (nhdsWithin (0 : ℝ) (Set.Iio 0))
      (𝓝 (Real.sqrt Real.pi)) := by
    have hd := hpiGaussian_left.div hq_left hsqrtpi_ne
    rw [hpi_div] at hd
    refine hd.congr' ?_
    filter_upwards [] with y
    rfl
  have hleft_raw : Tendsto (fun y : ℝ =>
      Real.pi * gaussian y / q y -
        Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * y|))
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 0) := by
    simpa using hquotient_left.sub habel_left
  have hleft : Tendsto auxiliaryFunctionBDerivative
      (nhdsWithin (0 : ℝ) (Set.Iio 0)) (𝓝 0) := by
    refine hleft_raw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := ne_of_lt hy
    have hroot : sqrtOneMinusGaussian y ≠ 0 :=
      (aux_sqrtOneMinusGaussian_pos hy0).ne'
    have hscale : Real.sqrt Real.pi * y < 0 := mul_neg_of_pos_of_neg hsqrtpi_pos hy
    dsimp only [q]
    simp only [auxiliaryFunctionBDerivative, if_neg hy0,
      sign_neg hscale]
    rw [abs_of_neg hy]
    field_simp [hroot, hy0]
    norm_num
    ring
  rw [← Set.Iio_union_Ioi, nhdsWithin_union, tendsto_sup]
  exact ⟨hleft, hright⟩

/-- This auxiliary continuity fact supplies the continuous-extension clause for $B'$ in
`auxiliaryFunctionB_properties`. -/
theorem aux_auxiliaryFunctionBDerivative_continuous : Continuous auxiliaryFunctionBDerivative := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x = 0
  · subst x
    rw [continuousAt_iff_punctured_nhds]
    simpa [auxiliaryFunctionBDerivative] using aux_auxiliaryFunctionBDerivative_tendsto_zero
  · exact aux_auxiliaryFunctionBDerivative_continuousAt_of_ne_zero hx

/-- This auxiliary extension theorem upgrades the off-origin derivative formula for $B$ to the
continuous derivative extension at zero, which is needed for Fourier integration by parts. -/
theorem aux_auxiliaryFunctionB_hasDerivAt (x : ℝ) :
    HasDerivAt auxiliaryFunctionB (auxiliaryFunctionBDerivative x) x := by
  by_cases hx : x = 0
  · subst x
    exact hasDerivAt_of_hasDerivAt_of_ne
      (fun y hy => aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero hy)
      aux_auxiliaryFunctionB_continuous.continuousAt
      aux_auxiliaryFunctionBDerivative_continuous.continuousAt
  · exact aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero hx

/-- This auxiliary differentiability consequence is the hypothesis needed to transfer the
integrable $B'$ bound through the Fourier derivative identity. -/
theorem aux_auxiliaryFunctionB_differentiable : Differentiable ℝ auxiliaryFunctionB := by
  intro x
  exact (aux_auxiliaryFunctionB_hasDerivAt x).differentiableAt

/-- This auxiliary lower bound controls the square-root denominator in the formula for $B'$ by
a Gaussian factor. -/
theorem aux_sqrtOneMinusGaussian_lower (x : ℝ) :
    Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      sqrtOneMinusGaussian x := by
  let u : ℝ := Real.pi * x ^ 2
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hprod : (1 + u) * Real.exp (-u) ≤ 1 := by
    calc
      (1 + u) * Real.exp (-u) ≤ Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right
          (by simpa [add_comm] using Real.add_one_le_exp u) (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        norm_num
  have hu_exp : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
    nlinarith
  have hrad : 0 ≤ 1 - gaussian x := aux_one_sub_gaussian_nonneg x
  have hleft_nonneg : 0 ≤
      Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2) := by
    positivity
  have hright_nonneg : 0 ≤ sqrtOneMinusGaussian x := Real.sqrt_nonneg _
  have hsqrtpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hhalf_sq : Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 =
      Real.exp (-(Real.pi * x ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq :
      (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 ≤
        (sqrtOneMinusGaussian x) ^ 2 := by
    calc
      (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 =
          u * Real.exp (-u) := by
        calc
          (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) ^ 2 =
              (Real.sqrt Real.pi) ^ 2 * |x| ^ 2 *
                Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 := by ring
          _ = u * Real.exp (-u) := by
            rw [hsqrtpi, sq_abs, hhalf_sq]
      _ ≤ 1 - Real.exp (-u) := hu_exp
      _ = (sqrtOneMinusGaussian x) ^ 2 := by
        rw [sqrtOneMinusGaussian, Real.sq_sqrt hrad]
        simp [u, gaussian, Notation.gaussian]
  nlinarith

/-- This auxiliary quotient estimate turns the lower bound on the square-root denominator into
the Gaussian part of an integrable majorant for $B'$. -/
theorem aux_auxiliaryFunctionBDerivative_gaussianTerm_bound {x : ℝ} (hx : x ≠ 0) :
    |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| ≤
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) := by
  have hroot : 0 < sqrtOneMinusGaussian x := aux_sqrtOneMinusGaussian_pos hx
  have hden : 0 < 2 * sqrtOneMinusGaussian x := by positivity
  have hhalf_sq : Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 = gaussian x := by
    change Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 =
      Real.exp (-Real.pi * x ^ 2)
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (aux_gaussian_pos x).le,
    abs_of_nonneg (by positivity : 0 ≤ 2 * sqrtOneMinusGaussian x)]
  apply (div_le_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left (aux_sqrtOneMinusGaussian_lower x)
    (show 0 ≤ 2 * Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) by positivity)
  have hsqrtpi : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt (le_of_lt Real.pi_pos)
  calc
    2 * Real.pi * |x| * gaussian x =
        (2 * Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) *
          (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
      rw [← hhalf_sq]
      calc
        2 * Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 =
            2 * (Real.sqrt Real.pi) ^ 2 * |x| *
              Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2 := by rw [hsqrtpi]
        _ = (2 * Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) *
              (Real.sqrt Real.pi * |x| * Real.exp (-(Real.pi / 2) * x ^ 2)) := by ring
    _ ≤ (2 * Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) *
          sqrtOneMinusGaussian x := hmul
    _ = (Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) *
          (2 * sqrtOneMinusGaussian x) := by ring

/-- This auxiliary pointwise bound supplies a single integrable majorant for the continuous
extension of $B'$. -/
theorem aux_auxiliaryFunctionBDerivative_norm_le (x : ℝ) :
    ‖auxiliaryFunctionBDerivative x‖ ≤
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.sqrt Real.pi * aux_poissonFrequency x := by
  rw [Real.norm_eq_abs]
  by_cases hx : x = 0
  · subst x
    simp [auxiliaryFunctionBDerivative, aux_poissonFrequency] <;> positivity
  · rw [auxiliaryFunctionBDerivative, if_neg hx]
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have hscale : Real.sqrt Real.pi * x < 0 :=
        mul_neg_of_pos_of_neg (Real.sqrt_pos.2 Real.pi_pos) hneg
      have habel :
          |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| =
            Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
        rw [sign_neg hscale]
        simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.exp_pos _).le]
      calc
        |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x) +
            Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| ≤
            |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| +
              |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
                Real.exp (-|Real.sqrt Real.pi * x|)| := abs_add_le _ _
        _ = |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| +
              Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by rw [habel]
        _ ≤ Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
              Real.sqrt Real.pi * aux_poissonFrequency x := by
          have hgaussian := aux_auxiliaryFunctionBDerivative_gaussianTerm_bound hx
          have hpoisson : Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤
              Real.sqrt Real.pi * aux_poissonFrequency x :=
            mul_le_mul_of_nonneg_left (aux_exp_neg_abs_sqrt_pi_le_poissonFrequency x)
              (Real.sqrt_nonneg _)
          exact add_le_add hgaussian hpoisson

    · have hscale : 0 < Real.sqrt Real.pi * x :=
        mul_pos (Real.sqrt_pos.2 Real.pi_pos) hpos
      have habel :
          |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| =
            Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
        have hsign :
            (SignType.sign (Real.sqrt Real.pi * x) : ℝ) = 1 := by
          simpa using congrArg (fun s : SignType => (s : ℝ)) (sign_pos hscale)
        have hnonneg : 0 ≤
            Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
        calc
          |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| =
              |Real.sqrt Real.pi * 1 * Real.exp (-|Real.sqrt Real.pi * x|)| := by rw [hsign]
          _ = Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
            rw [mul_one, abs_of_nonneg hnonneg]
      calc
        |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x) +
            Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
              Real.exp (-|Real.sqrt Real.pi * x|)| ≤
            |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| +
              |Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * x) : ℝ) *
                Real.exp (-|Real.sqrt Real.pi * x|)| := abs_add_le _ _
        _ = |(-2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)| +
              Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by rw [habel]
        _ ≤ Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
              Real.sqrt Real.pi * aux_poissonFrequency x := by
          have hgaussian := aux_auxiliaryFunctionBDerivative_gaussianTerm_bound hx
          have hpoisson : Real.sqrt Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤
              Real.sqrt Real.pi * aux_poissonFrequency x :=
            mul_le_mul_of_nonneg_left (aux_exp_neg_abs_sqrt_pi_le_poissonFrequency x)
              (Real.sqrt_nonneg _)
          exact add_le_add hgaussian hpoisson

/-- This auxiliary integrability fact is used to convert the pointwise $B'$ majorant into its
explicit $L^1$ estimate. -/
theorem aux_auxiliaryFunctionBDerivative_integrable :
    Integrable auxiliaryFunctionBDerivative := by
  have hgaussian : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
    simpa using
      (integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 2)).const_mul
        (Real.sqrt Real.pi)
  have habel : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * aux_poissonFrequency x) := by
    simpa using aux_poissonFrequency_integrable.const_mul (Real.sqrt Real.pi)
  have hmajorant : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.sqrt Real.pi * aux_poissonFrequency x) := hgaussian.add habel
  exact hmajorant.mono' aux_auxiliaryFunctionBDerivative_continuous.aestronglyMeasurable
    (ae_of_all _ aux_auxiliaryFunctionBDerivative_norm_le)

/-- This auxiliary $L^1$ estimate supplies the $B'$ norm clause of
`auxiliaryFunctionB_properties`. -/
theorem aux_auxiliaryFunctionBDerivative_eLpNorm_one_le :
    eLpNorm auxiliaryFunctionBDerivative 1 volume ≤ ENNReal.ofReal 20 := by
  have hgaussian : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
    simpa using
      (integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi / 2)).const_mul
        (Real.sqrt Real.pi)
  have habel : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * aux_poissonFrequency x) := by
    simpa using aux_poissonFrequency_integrable.const_mul (Real.sqrt Real.pi)
  have hmajorant : Integrable (fun x : ℝ =>
      Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.sqrt Real.pi * aux_poissonFrequency x) := hgaussian.add habel
  have hgaussian_integral :
      (∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2)) = Real.sqrt 2 := by
    calc
      (∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2)) =
          Real.sqrt (Real.pi / (Real.pi / 2)) := by
        simpa using (integral_gaussian (Real.pi / 2))
      _ = Real.sqrt 2 := by
        congr 1
        field_simp [Real.pi_ne_zero]
  have hnorm_bound : (∫ x : ℝ, ‖auxiliaryFunctionBDerivative x‖) ≤ 20 := by
    calc
      (∫ x : ℝ, ‖auxiliaryFunctionBDerivative x‖) ≤
          ∫ x : ℝ, Real.sqrt Real.pi * Real.exp (-(Real.pi / 2) * x ^ 2) +
            Real.sqrt Real.pi * aux_poissonFrequency x := by
        apply integral_mono aux_auxiliaryFunctionBDerivative_integrable.norm hmajorant
        intro x
        exact aux_auxiliaryFunctionBDerivative_norm_le x
      _ = (∫ x : ℝ, Real.sqrt Real.pi *
            Real.exp (-(Real.pi / 2) * x ^ 2)) +
          ∫ x : ℝ, Real.sqrt Real.pi * aux_poissonFrequency x :=
        integral_add hgaussian habel
      _ = Real.sqrt Real.pi * Real.sqrt 2 + Real.sqrt Real.pi * 2 := by
        rw [integral_const_mul, hgaussian_integral,
          integral_const_mul, aux_integral_poissonFrequency]
      _ ≤ 20 := by
        have hsqrtpi_le : Real.sqrt Real.pi ≤ 2 := by
          nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi,
            Real.pi_le_four]
        have hsqrttwo_le : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
            Real.sqrt_nonneg (2 : ℝ)]
        have hprod' : Real.sqrt Real.pi * Real.sqrt 2 ≤ (2 : ℝ) * 2 :=
          mul_le_mul hsqrtpi_le hsqrttwo_le (Real.sqrt_nonneg _) (by norm_num)
        norm_num at hprod'
        have hprod : Real.sqrt Real.pi * Real.sqrt 2 ≤ 4 := hprod'
        have htwice : Real.sqrt Real.pi * 2 ≤ 4 := by nlinarith
        nlinarith
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm aux_auxiliaryFunctionBDerivative_integrable]
  exact ENNReal.ofReal_le_ofReal hnorm_bound

/-- This auxiliary numerator records the cancellation between the two Gaussian quotient terms
in the off-origin expression for $B''$. -/
def aux_BSecondNumerator (x : ℝ) : ℝ :=
  Real.pi * x ^ 2 - (1 - gaussian x) +
    (1 - Real.pi * x ^ 2) * (1 - gaussian x) ^ 2

/-- This auxiliary Taylor-free estimate controls the numerator left after the cancellation in
the Gaussian quotient part of $B''$ on the only interval where its denominator is small. -/
theorem aux_BSecondNumerator_bounds {x : ℝ} (hx : |x| ≤ 1 / 2) :
    0 ≤ aux_BSecondNumerator x ∧
      aux_BSecondNumerator x ≤ 2 * (Real.pi * x ^ 2) ^ 2 := by
  let u : ℝ := Real.pi * x ^ 2
  let t : ℝ := 1 - gaussian x
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have h : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hu0 : 0 ≤ u := by
    dsimp [u]
    positivity
  have hu1 : u ≤ 1 := by
    calc
      u ≤ 4 * x ^ 2 := by
        dsimp [u]
        exact mul_le_mul_of_nonneg_right Real.pi_le_four (sq_nonneg x)
      _ ≤ 4 * (1 / 4) := mul_le_mul_of_nonneg_left hx2 (by norm_num)
      _ = 1 := by norm_num
  have ht0 : 0 ≤ t := by
    simpa [t] using aux_one_sub_gaussian_nonneg x
  have hgauss : gaussian x = Real.exp (-u) := by
    simp [u, gaussian, Notation.gaussian]
  have ht_le_u : t ≤ u := by
    dsimp [t]
    rw [hgauss]
    have h : 1 - u ≤ Real.exp (-u) := by
      have h' := Real.add_one_le_exp (-u)
      linarith
    linarith
  have hdenpos : 0 < 1 + u := by linarith
  have hexp : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hinv : Real.exp (-u) ≤ (1 + u)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos u) hdenpos).2 hexp
  have ht_lower : u / (1 + u) ≤ t := by
    dsimp [t]
    rw [hgauss]
    have hfrac : u / (1 + u) = 1 - (1 + u)⁻¹ := by
      field_simp
      ring
    rw [hfrac]
    linarith
  have hsub : u - t ≤ u ^ 2 := by
    calc
      u - t ≤ u - u / (1 + u) := sub_le_sub_left ht_lower u
      _ = u ^ 2 / (1 + u) := by
        field_simp
        ring
      _ ≤ u ^ 2 := (div_le_iff₀ hdenpos).2 (by nlinarith [sq_nonneg u])
  have hrest : (1 - u) * t ^ 2 ≤ u ^ 2 := by
    have htsq : t ^ 2 ≤ u ^ 2 := (sq_le_sq₀ ht0 hu0).2 ht_le_u
    calc
      (1 - u) * t ^ 2 ≤ 1 * t ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
      _ ≤ 1 * u ^ 2 := mul_le_mul_of_nonneg_left htsq zero_le_one
      _ = u ^ 2 := by ring
  change 0 ≤ u - t + (1 - u) * t ^ 2 ∧
    u - t + (1 - u) * t ^ 2 ≤ 2 * u ^ 2
  constructor
  · exact add_nonneg (sub_nonneg.mpr ht_le_u)
      (mul_nonneg (by linarith) (sq_nonneg t))
  · linarith

/-- This auxiliary numerical estimate bounds the harmless exponential factor appearing after
the cancellation in the local $B''$ estimate. -/
theorem aux_exp_three_half_pi_sq_le_nine {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤ 9 := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    have h : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg x) (by norm_num)).2 hx
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hu : Real.pi * x ^ 2 ≤ 1 := by
    calc
      Real.pi * x ^ 2 ≤ 4 * x ^ 2 :=
        mul_le_mul_of_nonneg_right Real.pi_le_four (sq_nonneg x)
      _ ≤ 4 * (1 / 4) := mul_le_mul_of_nonneg_left hx2 (by norm_num)
      _ = 1 := by norm_num
  calc
    Real.exp (3 * (Real.pi * x ^ 2) / 2) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr (by nlinarith)
    _ = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      congr 1 <;> norm_num
    _ ≤ 3 * 3 := mul_le_mul (le_of_lt Real.exp_one_lt_three)
      (le_of_lt Real.exp_one_lt_three) (Real.exp_pos _).le (by norm_num)
    _ = 9 := by norm_num

/-- The zero extension used for the second derivative assertion in Proposition
\ref{auxiliary function B}. -/
def auxiliaryFunctionBSecondDerivative (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
        (2 * sqrtOneMinusGaussian x) +
      (-2 * Real.pi * x * gaussian x) ^ 2 /
        (4 * sqrtOneMinusGaussian x ^ 3) -
      Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)

/-- This auxiliary identity exposes the cancellation that controls the apparent singularity in
the Gaussian part of $B''$. -/
theorem aux_BSecondGaussianPart_eq_cancelled {x : ℝ} (hx : x ≠ 0) :
    ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
        (2 * sqrtOneMinusGaussian x) +
      (-2 * Real.pi * x * gaussian x) ^ 2 /
        (4 * sqrtOneMinusGaussian x ^ 3) =
      Real.pi * aux_BSecondNumerator x /
        sqrtOneMinusGaussian x ^ 3 := by
  have hroot : sqrtOneMinusGaussian x ≠ 0 :=
    (aux_sqrtOneMinusGaussian_pos hx).ne'
  have hroot_sq : sqrtOneMinusGaussian x ^ 2 = 1 - gaussian x :=
    Real.sq_sqrt (aux_one_sub_gaussian_nonneg x)
  field_simp [hroot]
  rw [hroot_sq]
  unfold aux_BSecondNumerator
  ring

/-- This auxiliary local envelope is the cancellation estimate required to control the Gaussian
quotient part of $B''$ at its removable singularity. -/
theorem aux_BSecondGaussianPart_abs_le_near_zero {x : ℝ}
    (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 2) :
    |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| ≤ 144 * |x| := by
  rw [aux_BSecondGaussianPart_eq_cancelled hx0]
  let u : ℝ := Real.pi * x ^ 2
  let L : ℝ := Real.sqrt Real.pi * |x| * Real.exp (-u / 2)
  let T : ℝ := 2 * Real.pi * Real.sqrt Real.pi * |x| *
    Real.exp (3 * u / 2)
  have hnum := aux_BSecondNumerator_bounds hx
  have hfpos : 0 < sqrtOneMinusGaussian x := aux_sqrtOneMinusGaussian_pos hx0
  have hL : L ≤ sqrtOneMinusGaussian x := by
    dsimp [L, u]
    convert aux_sqrtOneMinusGaussian_lower x using 1 <;> ring
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (abs_pos.mpr hx0))
      (Real.exp_pos _)
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    positivity
  have hnumscaled : Real.pi * aux_BSecondNumerator x ≤
      2 * Real.pi ^ 3 * x ^ 4 := by
    calc
      Real.pi * aux_BSecondNumerator x ≤ Real.pi * (2 * u ^ 2) :=
        mul_le_mul_of_nonneg_left hnum.2 Real.pi_pos.le
      _ = 2 * Real.pi ^ 3 * x ^ 4 := by
        dsimp [u]
        ring
  have hfcube : L ^ 3 ≤ sqrtOneMinusGaussian x ^ 3 :=
    pow_le_pow_left₀ hLpos.le hL 3
  have hsqrtsq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hexp : Real.exp (3 * u / 2) * Real.exp (-u / 2) ^ 3 = 1 := by
    calc
      Real.exp (3 * u / 2) * Real.exp (-u / 2) ^ 3 =
          Real.exp (3 * u / 2) * Real.exp (3 * (-u / 2)) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ = Real.exp (3 * u / 2 + 3 * (-u / 2)) := by rw [← Real.exp_add]
      _ = 1 := by
        rw [show 3 * u / 2 + 3 * (-u / 2) = 0 by ring, Real.exp_zero]
  have hTL : T * L ^ 3 = 2 * Real.pi ^ 3 * x ^ 4 := by
    calc
      T * L ^ 3 = 2 * Real.pi * (Real.sqrt Real.pi) ^ 4 * |x| ^ 4 *
          (Real.exp (3 * u / 2) * Real.exp (-u / 2) ^ 3) := by
        dsimp [T, L]
        ring
      _ = 2 * Real.pi ^ 3 * x ^ 4 := by
        rw [hexp, show (Real.sqrt Real.pi) ^ 4 =
            (Real.sqrt Real.pi ^ 2) ^ 2 by ring, hsqrtsq,
          show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]
        ring
  have hcore : Real.pi * aux_BSecondNumerator x ≤
      T * sqrtOneMinusGaussian x ^ 3 := by
    calc
      Real.pi * aux_BSecondNumerator x ≤ 2 * Real.pi ^ 3 * x ^ 4 := hnumscaled
      _ = T * L ^ 3 := hTL.symm
      _ ≤ T * sqrtOneMinusGaussian x ^ 3 :=
        mul_le_mul_of_nonneg_left hfcube hTnonneg
  have hquot : Real.pi * aux_BSecondNumerator x /
      sqrtOneMinusGaussian x ^ 3 ≤ T :=
    (div_le_iff₀ (pow_pos hfpos 3)).2 hcore
  have hquotnonneg : 0 ≤ Real.pi * aux_BSecondNumerator x /
      sqrtOneMinusGaussian x ^ 3 :=
    div_nonneg (mul_nonneg Real.pi_pos.le hnum.1) (pow_nonneg hfpos.le _)
  rw [abs_of_nonneg hquotnonneg]
  calc
    Real.pi * aux_BSecondNumerator x / sqrtOneMinusGaussian x ^ 3 ≤ T := hquot
    _ ≤ 144 * |x| := by
      have hcoeff : 2 * Real.pi * Real.sqrt Real.pi ≤ 16 := by
        have hsqrt : Real.sqrt Real.pi ≤ 2 := by
          nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi,
            Real.pi_le_four]
        have hp : Real.pi * Real.sqrt Real.pi ≤ 4 * 2 :=
          mul_le_mul Real.pi_le_four hsqrt (Real.sqrt_nonneg _) (by norm_num)
        nlinarith
      have hexp9 : Real.exp (3 * u / 2) ≤ 9 := by
        dsimp [u]
        exact aux_exp_three_half_pi_sq_le_nine hx
      have habs : 0 ≤ |x| := abs_nonneg x
      calc
        T ≤ (16 * |x|) * Real.exp (3 * u / 2) := by
          dsimp [T]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoeff habs) (Real.exp_pos _).le
        _ ≤ (16 * |x|) * 9 :=
          mul_le_mul_of_nonneg_left hexp9 (by positivity)
        _ = 144 * |x| := by ring

/-- This auxiliary elementary estimate replaces the linear Gaussian factor arising in the
off-origin $B''$ bound by a standard integrable Gaussian. -/
theorem aux_abs_mul_exp_neg_pi_half_sq_le (x : ℝ) :
    |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      Real.exp (-(1 / 2) * x ^ 2) := by
  have habs : |x| ≤ Real.exp (x ^ 2) := by
    calc
      |x| ≤ 1 + x ^ 2 := by
        rw [← sq_abs x]
        nlinarith [sq_nonneg (|x| - (1 / 2 : ℝ))]
      _ ≤ Real.exp (x ^ 2) := by
        simpa [add_comm] using Real.add_one_le_exp (x ^ 2)
  calc
    |x| * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
        Real.exp (x ^ 2) * Real.exp (-(Real.pi / 2) * x ^ 2) :=
      mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
    _ = Real.exp (x ^ 2 + (-(Real.pi / 2) * x ^ 2)) := by rw [← Real.exp_add]
    _ ≤ Real.exp (-(1 / 2) * x ^ 2) := Real.exp_le_exp.mpr (by
      nlinarith [Real.pi_gt_three, sq_nonneg x])

/-- This auxiliary numerical estimate gives the coefficient used in the integrable
off-origin $B''$ Gaussian envelope. -/
theorem aux_two_pi_sqrt_pi_le_twelve :
    2 * Real.pi * Real.sqrt Real.pi ≤ 12 := by
  have hp : Real.pi ≤ (9 / 5 : ℝ) ^ 2 := by
    nlinarith [Real.pi_lt_d2]
  have hs : Real.sqrt Real.pi ≤ 9 / 5 := by
    calc
      Real.sqrt Real.pi ≤ Real.sqrt ((9 / 5 : ℝ) ^ 2) := Real.sqrt_le_sqrt hp
      _ = 9 / 5 := by rw [Real.sqrt_sq_eq_abs]; norm_num
  have hprod : Real.pi * Real.sqrt Real.pi ≤ (3.15 : ℝ) * (9 / 5 : ℝ) :=
    mul_le_mul (le_of_lt Real.pi_lt_d2) hs (Real.sqrt_nonneg _) (by norm_num)
  nlinarith

/-- This auxiliary off-origin envelope controls the Gaussian quotient part of $B''$ by two
integrable Gaussian functions. -/
theorem aux_BSecondGaussianPart_abs_le_outer {x : ℝ}
    (hx : 1 / 2 ≤ |x|) :
    |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| ≤
      12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  let q : ℝ := Real.exp (-(Real.pi / 2) * x ^ 2)
  let L : ℝ := Real.sqrt Real.pi * |x| * q
  let A : ℝ := 2 * Real.pi * Real.sqrt Real.pi * |x| * q +
    2 * Real.sqrt Real.pi * q
  let B : ℝ := 2 * Real.sqrt Real.pi * q
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hL : L ≤ sqrtOneMinusGaussian x := by
    dsimp [L, q]
    convert aux_sqrtOneMinusGaussian_lower x using 1 <;> ring
  have hLpos : 0 < L := by
    dsimp [L, q]
    exact mul_pos (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (abs_pos.mpr hx0))
      (Real.exp_pos _)
  have hfpos : 0 < sqrtOneMinusGaussian x :=
    aux_sqrtOneMinusGaussian_pos hx0
  have hgaussian : gaussian x = q ^ 2 := by
    dsimp [q]
    change Real.exp (-Real.pi * x ^ 2) =
      Real.exp (-(Real.pi / 2) * x ^ 2) ^ 2
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsqrtsq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hbase : 0 ≤ 2 * |x| - 1 := by linarith
  have hAnonneg : 0 ≤ A := by
    dsimp [A, q]
    positivity
  have hBnonneg : 0 ≤ B := by
    dsimp [B, q]
    positivity
  have hcoef :
      |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| ≤
        4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi := by
    calc
      |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| ≤
          |4 * Real.pi ^ 2 * x ^ 2| + |2 * Real.pi| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (4 * Real.pi ^ 2 * x ^ 2) 0 (2 * Real.pi))
      _ = 4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hAcore :
      (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * gaussian x ≤ A * (2 * L) := by
    rw [hgaussian]
    have hnonneg : 0 ≤ 2 * Real.pi * q ^ 2 * (2 * |x| - 1) :=
      mul_nonneg (mul_nonneg (by positivity) (sq_nonneg q)) hbase
    calc
      (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * q ^ 2 ≤
          (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * q ^ 2 +
            2 * Real.pi * q ^ 2 * (2 * |x| - 1) :=
        le_add_of_nonneg_right hnonneg
      _ = 4 * Real.pi ^ 2 * x ^ 2 * q ^ 2 +
          4 * Real.pi * |x| * q ^ 2 := by ring
      _ = A * (2 * L) := by
        symm
        calc
          A * (2 * L) =
              4 * Real.pi * (Real.sqrt Real.pi) ^ 2 * |x| ^ 2 * q ^ 2 +
                4 * (Real.sqrt Real.pi) ^ 2 * |x| * q ^ 2 := by
            dsimp [A, L]
            ring
          _ = 4 * Real.pi ^ 2 * x ^ 2 * q ^ 2 +
                4 * Real.pi * |x| * q ^ 2 := by
            rw [hsqrtsq, sq_abs]
            ring
  have hA :
      |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x)| ≤ A := by
    have hden : 0 < 2 * sqrtOneMinusGaussian x := by positivity
    calc
      |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x)| =
          |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x /
            (2 * sqrtOneMinusGaussian x) := by
        rw [abs_div, abs_mul, abs_of_pos (aux_gaussian_pos x), abs_of_pos hden]
      _ ≤ A := (div_le_iff₀ hden).2 <| by
        calc
          |4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi| * gaussian x ≤
              (4 * Real.pi ^ 2 * x ^ 2 + 2 * Real.pi) * gaussian x :=
            mul_le_mul_of_nonneg_right hcoef (aux_gaussian_pos x).le
          _ ≤ A * (2 * L) := hAcore
          _ ≤ A * (2 * sqrtOneMinusGaussian x) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hL (by norm_num)) hAnonneg
  have hLcube : L ^ 3 ≤ sqrtOneMinusGaussian x ^ 3 :=
    pow_le_pow_left₀ hLpos.le hL 3
  have hBcore :
      (-2 * Real.pi * x * gaussian x) ^ 2 ≤ B * (4 * L ^ 3) := by
    rw [hgaussian]
    have hnonneg :
        0 ≤ 4 * Real.pi ^ 2 * |x| ^ 2 * q ^ 4 * (2 * |x| - 1) := by
      have h4 : (0 : ℝ) ≤ 4 := by norm_num
      have hp2 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
      have hx2 : 0 ≤ |x| ^ 2 := sq_nonneg _
      have hq4 : 0 ≤ q ^ 4 := pow_nonneg hqpos.le _
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h4 hp2) hx2) hq4) hbase
    calc
      (-2 * Real.pi * x * q ^ 2) ^ 2 =
          4 * Real.pi ^ 2 * x ^ 2 * q ^ 4 := by ring
      _ ≤ 4 * Real.pi ^ 2 * x ^ 2 * q ^ 4 +
            4 * Real.pi ^ 2 * |x| ^ 2 * q ^ 4 * (2 * |x| - 1) :=
        le_add_of_nonneg_right hnonneg
      _ = 8 * Real.pi ^ 2 * |x| ^ 3 * q ^ 4 := by
        rw [show x ^ 2 = |x| ^ 2 by rw [sq_abs]]
        ring
      _ = B * (4 * L ^ 3) := by
        symm
        calc
          B * (4 * L ^ 3) =
              8 * (Real.sqrt Real.pi) ^ 4 * |x| ^ 3 * q ^ 4 := by
            dsimp [B, L]
            ring
          _ = 8 * Real.pi ^ 2 * |x| ^ 3 * q ^ 4 := by
            rw [show Real.sqrt Real.pi ^ 4 =
              (Real.sqrt Real.pi ^ 2) ^ 2 by ring, hsqrtsq]
  have hB :
      |(-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| ≤ B := by
    have hden : 0 < 4 * sqrtOneMinusGaussian x ^ 3 := by positivity
    calc
      |(-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| =
          (-2 * Real.pi * x * gaussian x) ^ 2 /
            (4 * sqrtOneMinusGaussian x ^ 3) := by
        rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hden]
      _ ≤ B := (div_le_iff₀ hden).2 <| by
        calc
          (-2 * Real.pi * x * gaussian x) ^ 2 ≤ B * (4 * L ^ 3) := hBcore
          _ ≤ B * (4 * sqrtOneMinusGaussian x ^ 3) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hLcube (by norm_num)) hBnonneg
  have hsqrtle : Real.sqrt Real.pi ≤ 2 := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi,
      Real.pi_le_four]
  have hfirst :
      2 * Real.pi * Real.sqrt Real.pi * |x| * q ≤
        12 * Real.exp (-(1 / 2) * x ^ 2) := by
    calc
      2 * Real.pi * Real.sqrt Real.pi * |x| * q =
          (2 * Real.pi * Real.sqrt Real.pi) * (|x| * q) := by ring
      _ ≤ 12 * (|x| * q) :=
        mul_le_mul_of_nonneg_right aux_two_pi_sqrt_pi_le_twelve
          (mul_nonneg (abs_nonneg x) hqpos.le)
      _ ≤ 12 * Real.exp (-(1 / 2) * x ^ 2) :=
        mul_le_mul_of_nonneg_left (aux_abs_mul_exp_neg_pi_half_sq_le x) (by norm_num)
  have hsecond : 4 * Real.sqrt Real.pi * q ≤ 8 * q := by
    calc
      4 * Real.sqrt Real.pi * q ≤ (4 * 2) * q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrtle (by norm_num)) hqpos.le
      _ = 8 * q := by ring
  calc
    |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)| ≤
        |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x)| +
          |(-2 * Real.pi * x * gaussian x) ^ 2 /
            (4 * sqrtOneMinusGaussian x ^ 3)| := abs_add_le _ _
    _ ≤ A + B := add_le_add hA hB
    _ = 2 * Real.pi * Real.sqrt Real.pi * |x| * q +
          4 * Real.sqrt Real.pi * q := by
      dsimp [A, B]
      ring
    _ ≤ 12 * Real.exp (-(1 / 2) * x ^ 2) + 8 * q := add_le_add hfirst hsecond

/-- This auxiliary integral computes the compactly supported local majorant used in the
explicit $L^1$ estimate for $B''$. -/
theorem aux_integral_indicator_localQuadratic :
    (∫ x : ℝ, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun y : ℝ => y ^ 2 + 1 / 4) x) = 1 / 3 := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hpow : IntervalIntegrable (fun y : ℝ => y ^ 2) volume
      (-(1 / 2 : ℝ)) (1 / 2) :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ)) volume
      (-(1 / 2 : ℝ)) (1 / 2) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hpow hconst, integral_pow]
  norm_num

/-- This auxiliary integral computes the measure of the compact interval in the local
majorant for $B''$. -/
theorem aux_integral_indicator_localOne :
    (∫ x : ℝ, (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun _ : ℝ => (1 : ℝ)) x) = 1 := by
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  simp
  norm_num

/-- This auxiliary pointwise estimate combines the local cancellation and off-origin Gaussian
envelopes into a single integrable majorant for the zero extension of $B''$. -/
theorem aux_auxiliaryFunctionBSecondDerivative_norm_le (x : ℝ) :
    ‖auxiliaryFunctionBSecondDerivative x‖ ≤
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x := by
  let S : Set ℝ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  let G : ℝ → ℝ := fun y =>
    144 * S.indicator (fun z : ℝ => z ^ 2 + 1 / 4) y +
      4 * S.indicator (fun _ : ℝ => (1 : ℝ)) y +
      12 * Real.exp (-(1 / 2) * y ^ 2) +
      8 * Real.exp (-(Real.pi / 2) * y ^ 2) +
      Real.pi * aux_poissonFrequency y
  change ‖auxiliaryFunctionBSecondDerivative x‖ ≤ G x
  by_cases hx : x ∈ S
  · have hxabs : |x| ≤ 1 / 2 := by
      rw [abs_le]
      simpa [S] using hx
    by_cases hx0 : x = 0
    · subst x
      dsimp [G]
      simp [auxiliaryFunctionBSecondDerivative, S]
      have hpoisson : 0 ≤ aux_poissonFrequency 0 := by
        unfold aux_poissonFrequency
        positivity
      nlinarith [Real.pi_pos]
    · have hquot := aux_BSecondGaussianPart_abs_le_near_zero hx0 hxabs
      have habel_nonneg : 0 ≤ Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
        positivity
      have habel_le_four : Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤ 4 := by
        calc
          Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤ Real.pi * 1 := by
            apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
          _ ≤ 4 := by simpa using Real.pi_le_four
      have habsquad : |x| ≤ x ^ 2 + 1 / 4 := by
        rw [← sq_abs x]
        nlinarith [sq_nonneg (|x| - (1 / 2 : ℝ))]
      rw [Real.norm_eq_abs, auxiliaryFunctionBSecondDerivative, if_neg hx0]
      calc
        |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3) -
            Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)| ≤
            |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
                (2 * sqrtOneMinusGaussian x) +
              (-2 * Real.pi * x * gaussian x) ^ 2 /
                (4 * sqrtOneMinusGaussian x ^ 3)| +
              |Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)| := by
              simpa only [sub_zero, zero_sub, abs_neg] using
                (abs_sub_le
                  (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
                      (2 * sqrtOneMinusGaussian x) +
                    (-2 * Real.pi * x * gaussian x) ^ 2 /
                      (4 * sqrtOneMinusGaussian x ^ 3))
                  0 (Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)))
        _ = |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
                (2 * sqrtOneMinusGaussian x) +
              (-2 * Real.pi * x * gaussian x) ^ 2 /
                (4 * sqrtOneMinusGaussian x ^ 3)| +
              Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
              rw [abs_of_nonneg habel_nonneg]
        _ ≤ 144 * |x| + 4 := add_le_add hquot habel_le_four
        _ ≤ 144 * (x ^ 2 + 1 / 4) + 4 :=
          add_le_add (mul_le_mul_of_nonneg_left habsquad (by norm_num)) le_rfl
        _ ≤ G x := by
          dsimp [G]
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          have hrest : 0 ≤ 12 * Real.exp (-(1 / 2) * x ^ 2) +
              8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
              Real.pi * aux_poissonFrequency x := by
            unfold aux_poissonFrequency
            positivity
          linarith
  · have hxhalf : 1 / 2 ≤ |x| := by
      apply le_of_not_ge
      intro hsmall
      apply hx
      simpa [S] using (abs_le.mp hsmall)
    have hx0 : x ≠ 0 := by
      intro hzero
      subst x
      apply hx
      simp [S]
    have hquot := aux_BSecondGaussianPart_abs_le_outer hxhalf
    have habel_nonneg : 0 ≤ Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
      positivity
    have habel : Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) ≤
        Real.pi * aux_poissonFrequency x :=
      mul_le_mul_of_nonneg_left (aux_exp_neg_abs_sqrt_pi_le_poissonFrequency x)
        Real.pi_pos.le
    rw [Real.norm_eq_abs, auxiliaryFunctionBSecondDerivative, if_neg hx0]
    calc
      |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
            (2 * sqrtOneMinusGaussian x) +
          (-2 * Real.pi * x * gaussian x) ^ 2 /
            (4 * sqrtOneMinusGaussian x ^ 3) -
          Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)| ≤
          |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)| +
            |Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              (abs_sub_le
                (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
                    (2 * sqrtOneMinusGaussian x) +
                  (-2 * Real.pi * x * gaussian x) ^ 2 /
                    (4 * sqrtOneMinusGaussian x ^ 3))
                0 (Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)))
      _ = |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)| +
            Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
            rw [abs_of_nonneg habel_nonneg]
      _ ≤ 12 * Real.exp (-(1 / 2) * x ^ 2) +
            8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
            Real.pi * aux_poissonFrequency x :=
          add_le_add hquot habel
      _ ≤ G x := by
          dsimp [G]
          rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
          simp only [mul_zero, zero_add]
          exact le_rfl

/-- This auxiliary theorem proves integrability of the explicit pointwise majorant for the
zero extension of $B''$, so that it can be used both for integrability and the stated norm
estimate. -/
theorem aux_BSecondMajorant_integrable :
    Integrable (fun x : ℝ =>
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x) := by
  have hquad : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun y : ℝ => y ^ 2 + 1 / 4)) :=
    (((continuous_id.pow 2).add continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hone : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hhalf : Integrable (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have hpi : Integrable (fun x : ℝ => Real.exp (-(Real.pi / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < Real.pi / 2)
  have hsum :=
    (((hquad.const_mul 144).add (hone.const_mul 4)).add (hhalf.const_mul 12)).add
      ((hpi.const_mul 8).add (aux_poissonFrequency_integrable.const_mul Real.pi))
  refine hsum.congr ?_
  filter_upwards [] with x
  simp only [Pi.add_apply]
  ring

/-- This auxiliary calculation integrates the explicit $B''$ majorant and checks that the
numerical total is below the constant in Proposition \ref{auxiliary function B}. -/
theorem aux_BSecondMajorant_integral_le_hundred :
    (∫ x : ℝ,
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x) ≤ 100 := by
  have hquad : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun y : ℝ => y ^ 2 + 1 / 4)) :=
    (((continuous_id.pow 2).add continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).integrable_indicator measurableSet_Icc
  have hone : Integrable ((Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun _ : ℝ => (1 : ℝ))) :=
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  have hhalf : Integrable (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  have hpi : Integrable (fun x : ℝ => Real.exp (-(Real.pi / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < Real.pi / 2)
  have hquadMul := hquad.const_mul 144
  have honeMul := hone.const_mul 4
  have hhalfMul := hhalf.const_mul 12
  have hpiMul := hpi.const_mul 8
  have hpoissonMul := aux_poissonFrequency_integrable.const_mul Real.pi
  have hquadOne : Integrable (fun x : ℝ =>
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x) := by
    have hsum := hquadMul.add honeMul
    refine hsum.congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply]
  have hquadOneHalf : Integrable (fun x : ℝ =>
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2)) := by
    have hsum := hquadOne.add hhalfMul
    refine hsum.congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply]
  have hquadOneHalfPi : Integrable (fun x : ℝ =>
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
    have hsum := hquadOneHalf.add hpiMul
    refine hsum.congr ?_
    filter_upwards [] with x
    simp only [Pi.add_apply]
  have hhalf_integral :
      (∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2)) = Real.sqrt (2 * Real.pi) := by
    calc
      (∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2)) =
          Real.sqrt (Real.pi / (1 / 2)) := by
        simpa using (integral_gaussian (1 / 2 : ℝ))
      _ = Real.sqrt (2 * Real.pi) := by
        congr 1
        ring
  have hpi_integral :
      (∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2)) = Real.sqrt 2 := by
    calc
      (∫ x : ℝ, Real.exp (-(Real.pi / 2) * x ^ 2)) =
          Real.sqrt (Real.pi / (Real.pi / 2)) := by
        simpa using (integral_gaussian (Real.pi / 2))
      _ = Real.sqrt 2 := by
        congr 1
        field_simp [Real.pi_ne_zero]
  have hsqrtTwoPi : Real.sqrt (2 * Real.pi) ≤ 251 / 100 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity),
      Real.sqrt_nonneg (2 * Real.pi), Real.pi_lt_d2]
  have hsqrtTwo : Real.sqrt 2 ≤ 10 / 7 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hpi_bound : Real.pi ≤ 63 / 20 := by
    nlinarith [Real.pi_lt_d2]
  calc
    (∫ x : ℝ,
      144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
          (fun y : ℝ => y ^ 2 + 1 / 4) x +
        4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator (fun _ : ℝ => (1 : ℝ)) x +
        12 * Real.exp (-(1 / 2) * x ^ 2) +
        8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
        Real.pi * aux_poissonFrequency x) =
        ((144 * (1 / 3) + 4 * 1) + 12 * Real.sqrt (2 * Real.pi)) +
          8 * Real.sqrt 2 + Real.pi * 2 := by
      rw [integral_add hquadOneHalfPi hpoissonMul,
        integral_add hquadOneHalf hpiMul,
        integral_add hquadOne hhalfMul,
        integral_add hquadMul honeMul,
        integral_const_mul, aux_integral_indicator_localQuadratic,
        integral_const_mul, aux_integral_indicator_localOne,
        integral_const_mul, hhalf_integral,
        integral_const_mul, hpi_integral,
        integral_const_mul, aux_integral_poissonFrequency]
    _ ≤ 100 := by
      nlinarith

/-- This auxiliary second-derivative formula is used to differentiate the Gaussian quotient
in the off-origin expression for $B''$. -/
theorem aux_gaussian_deriv_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => -2 * Real.pi * y * gaussian y)
      ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) x := by
  have h := ((hasDerivAt_id x).mul (gaussian_hasDerivAt x)).const_mul
    (-2 * Real.pi)
  have hfun : (fun y : ℝ => -2 * Real.pi * y * gaussian y) =ᶠ[𝓝 x]
      (fun y : ℝ => -2 * Real.pi * ((id : ℝ → ℝ) * gaussian) y) := by
    filter_upwards [] with y
    simp only [Pi.mul_apply, id_eq]
    ring
  have h' := h.congr_of_eventuallyEq hfun
  have hcoef : -2 * Real.pi *
      (1 * gaussian x + id x * (-2 * Real.pi * x * gaussian x)) =
      (4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x := by
    simp only [id_eq, one_mul]
    ring
  rw [hcoef] at h'
  exact h'

/-- This auxiliary differentiability formula supplies the square-root denominator derivative
away from its removable singularity. -/
theorem aux_sqrtOneMinusGaussian_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt sqrtOneMinusGaussian
      ((2 * Real.pi * x * gaussian x) / (2 * sqrtOneMinusGaussian x)) x := by
  have hlt : gaussian x < 1 := by
    have hneg : -Real.pi * x ^ 2 < 0 := by
      nlinarith [Real.pi_pos, sq_pos_of_ne_zero hx]
    simpa [gaussian, Notation.gaussian] using (Real.exp_lt_exp.mpr hneg)
  unfold sqrtOneMinusGaussian
  exact (aux_one_sub_gaussian_hasDerivAt x).sqrt (ne_of_gt (sub_pos.mpr hlt))

/-- This auxiliary quotient-rule calculation differentiates the Gaussian part of the displayed
formula for $B'$ away from zero. -/
theorem aux_BDerivative_gaussianTerm_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ =>
      (-2 * Real.pi * y * gaussian y) / (2 * sqrtOneMinusGaussian y))
      (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)) x := by
  have hroot : sqrtOneMinusGaussian x ≠ 0 :=
    (aux_sqrtOneMinusGaussian_pos hx).ne'
  have hu := aux_gaussian_deriv_hasDerivAt x
  have hf := aux_sqrtOneMinusGaussian_hasDerivAt hx
  have hden : 2 * sqrtOneMinusGaussian x ≠ 0 :=
    mul_ne_zero two_ne_zero hroot
  have hraw := hu.div (hf.const_mul 2) hden
  have hfun : (fun y : ℝ =>
      (-2 * Real.pi * y * gaussian y) / (2 * sqrtOneMinusGaussian y)) =ᶠ[𝓝 x]
      ((fun y : ℝ => -2 * Real.pi * y * gaussian y) /
        (fun y : ℝ => 2 * sqrtOneMinusGaussian y)) := by
    filter_upwards [] with y
    rfl
  have hraw' := hraw.congr_of_eventuallyEq hfun
  have hcoef :
      (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) *
          (2 * sqrtOneMinusGaussian x) -
        (-2 * Real.pi * x * gaussian x) *
          (2 * ((2 * Real.pi * x * gaussian x) /
            (2 * sqrtOneMinusGaussian x)))) /
          (2 * sqrtOneMinusGaussian x) ^ 2 =
        ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
            (2 * sqrtOneMinusGaussian x) +
          (-2 * Real.pi * x * gaussian x) ^ 2 /
            (4 * sqrtOneMinusGaussian x ^ 3) := by
    field_simp [hroot]
    ring
  rw [hcoef] at hraw'
  exact hraw'

/-- This auxiliary fixed-sign calculation differentiates the Abel summand in $B'$ without
crossing its absolute-value singularity. -/
theorem aux_BDerivative_abelTerm_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ =>
      Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * y) : ℝ) *
        Real.exp (-|Real.sqrt Real.pi * y|))
      (-Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) x := by
  have hsqrtpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsquare : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hscale : Real.sqrt Real.pi * x < 0 :=
      mul_neg_of_pos_of_neg hsqrtpi_pos hneg
    have hlin : HasDerivAt (fun y : ℝ => Real.sqrt Real.pi * y)
        (Real.sqrt Real.pi) x := hasDerivAt_const_mul (x := x) _
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (Real.sqrt Real.pi * y))
        (Real.exp (Real.sqrt Real.pi * x) * Real.sqrt Real.pi) x :=
      (Real.hasDerivAt_exp _).comp x hlin
    have hbase := hexp.const_mul (-Real.sqrt Real.pi)
    have hbase' : HasDerivAt (fun y : ℝ =>
        -Real.sqrt Real.pi * Real.exp (Real.sqrt Real.pi * y))
        (-Real.pi * Real.exp (Real.sqrt Real.pi * x)) x := by
      have hderiv :
          -Real.sqrt Real.pi * (Real.exp (Real.sqrt Real.pi * x) * Real.sqrt Real.pi) =
            -Real.pi * Real.exp (Real.sqrt Real.pi * x) := by
        calc
          -Real.sqrt Real.pi * (Real.exp (Real.sqrt Real.pi * x) * Real.sqrt Real.pi) =
              -(Real.sqrt Real.pi * Real.sqrt Real.pi) *
                Real.exp (Real.sqrt Real.pi * x) := by ring
          _ = -Real.pi * Real.exp (Real.sqrt Real.pi * x) := by rw [hsquare]
      simpa only [neg_mul, hderiv] using hbase
    have hIio : Set.Iio (0 : ℝ) ∈ 𝓝 x := isOpen_Iio.mem_nhds hneg
    have heq : (fun y : ℝ =>
        Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * y) : ℝ) *
          Real.exp (-|Real.sqrt Real.pi * y|)) =ᶠ[𝓝 x]
        (fun y : ℝ => -Real.sqrt Real.pi * Real.exp (Real.sqrt Real.pi * y)) := by
      filter_upwards [hIio] with y hy
      have hy_scale : Real.sqrt Real.pi * y < 0 :=
        mul_neg_of_pos_of_neg hsqrtpi_pos hy
      have hsign : (SignType.sign (Real.sqrt Real.pi * y) : ℝ) = -1 := by
        simpa using congrArg (fun s : SignType => (s : ℝ)) (sign_neg hy_scale)
      rw [hsign, abs_of_neg hy_scale]
      ring
    simpa [abs_of_neg hscale] using hbase'.congr_of_eventuallyEq heq
  · have hscale : 0 < Real.sqrt Real.pi * x := mul_pos hsqrtpi_pos hpos
    have hlin : HasDerivAt (fun y : ℝ => -Real.sqrt Real.pi * y)
        (-Real.sqrt Real.pi) x := hasDerivAt_const_mul (x := x) _
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-Real.sqrt Real.pi * y))
        (Real.exp (-Real.sqrt Real.pi * x) * (-Real.sqrt Real.pi)) x :=
      (Real.hasDerivAt_exp _).comp x hlin
    have hbase := hexp.const_mul (Real.sqrt Real.pi)
    have hbase' : HasDerivAt (fun y : ℝ =>
        Real.sqrt Real.pi * Real.exp (-Real.sqrt Real.pi * y))
        (-Real.pi * Real.exp (-Real.sqrt Real.pi * x)) x := by
      have hderiv :
          Real.sqrt Real.pi *
              (Real.exp (-Real.sqrt Real.pi * x) * (-Real.sqrt Real.pi)) =
            -Real.pi * Real.exp (-Real.sqrt Real.pi * x) := by
        calc
          Real.sqrt Real.pi *
              (Real.exp (-Real.sqrt Real.pi * x) * (-Real.sqrt Real.pi)) =
              -(Real.sqrt Real.pi * Real.sqrt Real.pi) *
                Real.exp (-Real.sqrt Real.pi * x) := by ring
          _ = -Real.pi * Real.exp (-Real.sqrt Real.pi * x) := by rw [hsquare]
      simpa only [hderiv] using hbase
    have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 x := isOpen_Ioi.mem_nhds hpos
    have heq : (fun y : ℝ =>
        Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * y) : ℝ) *
          Real.exp (-|Real.sqrt Real.pi * y|)) =ᶠ[𝓝 x]
        (fun y : ℝ => Real.sqrt Real.pi * Real.exp (-Real.sqrt Real.pi * y)) := by
      filter_upwards [hIoi] with y hy
      have hy_scale : 0 < Real.sqrt Real.pi * y := mul_pos hsqrtpi_pos hy
      have hsign : (SignType.sign (Real.sqrt Real.pi * y) : ℝ) = 1 := by
        simpa using congrArg (fun s : SignType => (s : ℝ)) (sign_pos hy_scale)
      rw [hsign, abs_of_pos hy_scale, mul_one]
      ring
    simpa [abs_of_pos hscale, neg_mul] using hbase'.congr_of_eventuallyEq heq

/-- This auxiliary off-origin theorem identifies the derivative of the continuous extension of
$B'$ with the displayed zero-extension formula for $B''$. -/
theorem aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt auxiliaryFunctionBDerivative (auxiliaryFunctionBSecondDerivative x) x := by
  have hq := aux_BDerivative_gaussianTerm_hasDerivAt hx
  have ha := aux_BDerivative_abelTerm_hasDerivAt hx
  have hsum := hq.add ha
  have heq : auxiliaryFunctionBDerivative =ᶠ[𝓝 x]
      (fun y : ℝ =>
        (-2 * Real.pi * y * gaussian y) / (2 * sqrtOneMinusGaussian y) +
          Real.sqrt Real.pi * (SignType.sign (Real.sqrt Real.pi * y) : ℝ) *
            Real.exp (-|Real.sqrt Real.pi * y|)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [auxiliaryFunctionBDerivative, hy]
  have hsum' := hsum.congr_of_eventuallyEq heq
  have hcoef :
      (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)) +
        (-Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) =
      ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3) -
        Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
    ring
  rw [hcoef] at hsum'
  have hsecond : auxiliaryFunctionBSecondDerivative x =
      ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x) +
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3) -
        Real.pi * Real.exp (-|Real.sqrt Real.pi * x|) := by
    simp [auxiliaryFunctionBSecondDerivative, hx]
  rw [hsecond]
  exact hsum'

/-- This auxiliary measurability fact supplies the Borel-measurability conclusion for the
zero extension of $B''$ in Proposition \ref{auxiliary function B}. -/
theorem aux_auxiliaryFunctionBSecondDerivative_measurable :
    Measurable auxiliaryFunctionBSecondDerivative := by
  unfold auxiliaryFunctionBSecondDerivative
  apply Measurable.ite
    (by simpa only [Set.setOf_eq_eq_singleton] using (measurableSet_singleton (0 : ℝ)))
  · exact measurable_const
  · have hg : Measurable gaussian := gaussian_continuous.measurable
    have hf : Measurable sqrtOneMinusGaussian :=
      continuous_sqrtOneMinusGaussian.measurable
    have hpoly : Measurable (fun x : ℝ =>
        4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) := by
      exact (measurable_const.mul (measurable_id'.pow_const 2)).sub measurable_const
    have htermone : Measurable (fun x : ℝ =>
        ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
          (2 * sqrtOneMinusGaussian x)) :=
      (hpoly.mul hg).div (measurable_const.mul hf)
    have hlinear : Measurable (fun x : ℝ => -2 * Real.pi * x * gaussian x) :=
      (measurable_const.mul measurable_id').mul hg
    have htermtwo : Measurable (fun x : ℝ =>
        (-2 * Real.pi * x * gaussian x) ^ 2 /
          (4 * sqrtOneMinusGaussian x ^ 3)) :=
      (hlinear.pow_const 2).div (measurable_const.mul (hf.pow_const 3))
    have habel : Measurable (fun x : ℝ =>
        Real.pi * Real.exp (-|Real.sqrt Real.pi * x|)) :=
      measurable_const.mul ((measurable_const.mul measurable_id').abs.neg.exp)
    exact (htermone.add htermtwo).sub habel

/-- This auxiliary continuity statement supplies the actual derivative value $-\pi$ at the
removable singularity of $B'$.  The manuscript's measurable $B''$ remains defined to be zero
there, since changing one point does not affect its integrability. -/
theorem aux_auxiliaryFunctionBTrueSecondDerivative_continuousAt_zero :
    ContinuousAt (fun x : ℝ =>
      if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x) 0 := by
  unfold ContinuousAt
  simp only [if_pos]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmajor : Tendsto (fun x : ℝ =>
      144 * |x| + Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ =>
        144 * |x| + Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)|) := by
      fun_prop
    have hcontAt : ContinuousAt (fun x : ℝ =>
        144 * |x| + Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)|) 0 :=
      hcont.continuousAt
    simpa [ContinuousAt] using hcontAt
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hmajor
  filter_upwards [show Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 0 by
    exact isOpen_Ioo.mem_nhds ⟨by norm_num, by norm_num⟩] with x hx
  have hxabs : |x| ≤ 1 / 2 := by
    rw [abs_le]
    exact ⟨hx.1.le, hx.2.le⟩
  by_cases hx0 : x = 0
  · subst x
    simp
  · have hgaussian := aux_BSecondGaussianPart_abs_le_near_zero hx0 hxabs
    rw [Real.norm_eq_abs]
    simp only [if_neg hx0]
    have hrewrite :
        auxiliaryFunctionBSecondDerivative x - -Real.pi =
          (((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)) +
            Real.pi * (1 - Real.exp (-|Real.sqrt Real.pi * x|)) := by
      simp [auxiliaryFunctionBSecondDerivative, hx0]
      ring
    rw [hrewrite]
    calc
      |(((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)) +
            Real.pi * (1 - Real.exp (-|Real.sqrt Real.pi * x|))| ≤
          |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)| +
            |Real.pi * (1 - Real.exp (-|Real.sqrt Real.pi * x|))| := abs_add_le _ _
      _ = |((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) * gaussian x) /
              (2 * sqrtOneMinusGaussian x) +
            (-2 * Real.pi * x * gaussian x) ^ 2 /
              (4 * sqrtOneMinusGaussian x ^ 3)| +
            Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ 144 * |x| + Real.pi * |1 - Real.exp (-|Real.sqrt Real.pi * x|)| :=
        add_le_add hgaussian le_rfl

/-- This auxiliary derivative fact restores the genuine derivative at zero needed for Fourier
integration by parts.  Away from zero it is exactly the displayed formula for $B''$. -/
theorem aux_auxiliaryFunctionBDerivative_hasDerivAt_zero :
    HasDerivAt auxiliaryFunctionBDerivative (-Real.pi) 0 := by
  have h := hasDerivAt_of_hasDerivAt_of_ne
    (f := auxiliaryFunctionBDerivative)
    (g := fun x : ℝ =>
      if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x)
    (x := 0)
    (fun y hy => by
      simpa [hy] using aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero hy)
    aux_auxiliaryFunctionBDerivative_continuous.continuousAt
    aux_auxiliaryFunctionBTrueSecondDerivative_continuousAt_zero
  simpa using h

/-- This auxiliary differentiability theorem packages the off-origin formula and its removable
value at zero for use in Fourier integration by parts. -/
theorem aux_auxiliaryFunctionBDerivative_differentiable :
    Differentiable ℝ auxiliaryFunctionBDerivative := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact aux_auxiliaryFunctionBDerivative_hasDerivAt_zero.differentiableAt
  · exact (aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero hx).differentiableAt

/-- This auxiliary identity identifies the ordinary derivative of the continuous extension of
$B'$; it differs from the manuscript's zero extension of $B''$ only at the origin. -/
theorem aux_deriv_auxiliaryFunctionBDerivative (x : ℝ) :
    deriv auxiliaryFunctionBDerivative x =
      if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x := by
  by_cases hx : x = 0
  · subst x
    simpa using aux_auxiliaryFunctionBDerivative_hasDerivAt_zero.deriv
  · simpa [hx] using (aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero hx).deriv

/-- This auxiliary integrability theorem turns the explicit majorant for the zero extension of
$B''$ into the integrability component of Proposition \ref{auxiliary function B}. -/
theorem aux_auxiliaryFunctionBSecondDerivative_integrable :
    Integrable auxiliaryFunctionBSecondDerivative := by
  exact aux_BSecondMajorant_integrable.mono'
    aux_auxiliaryFunctionBSecondDerivative_measurable.aestronglyMeasurable
    (ae_of_all _ aux_auxiliaryFunctionBSecondDerivative_norm_le)

/-- This auxiliary integrability fact replaces the manuscript's value $B''(0)=0$ by the true
derivative value $-\pi$ at a single null point, so it can serve as `deriv B'` in Fourier
integration by parts. -/
theorem aux_auxiliaryFunctionBTrueSecondDerivative_integrable :
    Integrable (fun x : ℝ =>
      if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x) := by
  apply aux_auxiliaryFunctionBSecondDerivative_integrable.congr
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using (measure_singleton (0 : ℝ))
  filter_upwards [hne] with x hx
  simp [hx]

/-- This is the $B''$ norm component of Proposition \ref{auxiliary function B}; the complete
source proposition is recorded in `auxiliaryFunctionB_properties`. -/
theorem aux_auxiliaryFunctionBSecondDerivative_eLpNorm_one_le :
    eLpNorm auxiliaryFunctionBSecondDerivative 1 volume ≤ ENNReal.ofReal 100 := by
  have hnorm_bound : (∫ x : ℝ, ‖auxiliaryFunctionBSecondDerivative x‖) ≤ 100 := by
    calc
      (∫ x : ℝ, ‖auxiliaryFunctionBSecondDerivative x‖) ≤
          ∫ x : ℝ,
            144 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
                (fun y : ℝ => y ^ 2 + 1 / 4) x +
              4 * (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator
                (fun _ : ℝ => (1 : ℝ)) x +
              12 * Real.exp (-(1 / 2) * x ^ 2) +
              8 * Real.exp (-(Real.pi / 2) * x ^ 2) +
              Real.pi * aux_poissonFrequency x := by
        apply integral_mono aux_auxiliaryFunctionBSecondDerivative_integrable.norm
          aux_BSecondMajorant_integrable
        intro x
        exact aux_auxiliaryFunctionBSecondDerivative_norm_le x
      _ ≤ 100 := aux_BSecondMajorant_integral_le_hundred
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm aux_auxiliaryFunctionBSecondDerivative_integrable]
  exact ENNReal.ofReal_le_ofReal hnorm_bound

/-- Definition used in Proposition \ref{square root of Gaussian decay}; its currently formalized
continuity claim is sqrtGaussianKernel_continuous. -/
def sqrtGaussianFrequencyProfile (ξ : ℝ) : ℂ :=
  (1 - sqrtOneMinusGaussian ξ : ℝ)

/-- Definition used in Proposition \ref{square root of Gaussian decay}; its currently formalized
continuity claim is sqrtGaussianKernel_continuous. -/
def sqrtGaussianKernel : ℝ → ℂ :=
  FourierTransformInv.fourierInv sqrtGaussianFrequencyProfile

/-- This auxiliary inequality is the nonnegative branch condition for the frequency profile
in the square-root Gaussian kernel. -/
theorem aux_one_sub_sqrtOneMinusGaussian_nonneg (x : ℝ) :
    0 ≤ 1 - sqrtOneMinusGaussian x := by
  have hrad : 0 ≤ 1 - gaussian x := aux_one_sub_gaussian_nonneg x
  have hsquare : sqrtOneMinusGaussian x ^ 2 = 1 - gaussian x :=
    Real.sq_sqrt hrad
  have hsqrt : 0 ≤ sqrtOneMinusGaussian x := Real.sqrt_nonneg _
  have hgauss : 0 < gaussian x := aux_gaussian_pos x
  nlinarith

/-- This auxiliary inequality gives an integrable Gaussian majorant for the square-root
Gaussian frequency profile. -/
theorem aux_one_sub_sqrtOneMinusGaussian_le_gaussian (x : ℝ) :
    1 - sqrtOneMinusGaussian x ≤ gaussian x := by
  have hrad : 0 ≤ 1 - gaussian x := aux_one_sub_gaussian_nonneg x
  have hsquare : sqrtOneMinusGaussian x ^ 2 = 1 - gaussian x :=
    Real.sq_sqrt hrad
  have hsqrt : 0 ≤ sqrtOneMinusGaussian x := Real.sqrt_nonneg _
  have hgauss : 0 < gaussian x := aux_gaussian_pos x
  nlinarith

/-- This auxiliary theorem proves integrability of the real frequency profile defining the
square-root Gaussian kernel. -/
theorem aux_sqrtGaussianFrequencyProfile_integrable_real :
    Integrable (fun ξ : ℝ => 1 - sqrtOneMinusGaussian ξ) := by
  refine gaussian_integrable.mono_nonneg
    (continuous_const.sub continuous_sqrtOneMinusGaussian).aestronglyMeasurable
    (ae_of_all _ aux_one_sub_sqrtOneMinusGaussian_nonneg)
    (ae_of_all _ aux_one_sub_sqrtOneMinusGaussian_le_gaussian)

/-- This auxiliary theorem gives the complex-valued integrability hypothesis required by the
inverse Fourier transform defining $\rho$. -/
theorem aux_sqrtGaussianFrequencyProfile_integrable :
    Integrable sqrtGaussianFrequencyProfile := by
  unfold sqrtGaussianFrequencyProfile
  exact aux_sqrtGaussianFrequencyProfile_integrable_real.ofReal

/-- The inverse-Fourier kernel $\rho$ from Proposition \ref{square root of Gaussian decay} is
continuous. -/
theorem sqrtGaussianKernel_continuous : Continuous sqrtGaussianKernel := by
  change Continuous
    (VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) sqrtGaussianFrequencyProfile)
  apply VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
  · fun_prop
  · exact aux_sqrtGaussianFrequencyProfile_integrable

/-- This auxiliary integrability fact is the starting point for the later integration-by-parts
control of the inverse Fourier transform of $B$. -/
theorem aux_auxiliaryFunctionB_integrable : Integrable auxiliaryFunctionB := by
  unfold auxiliaryFunctionB
  exact aux_sqrtGaussianFrequencyProfile_integrable_real.sub
    aux_exp_neg_abs_sqrt_pi_integrable

/-- This auxiliary $L^1$ estimate supplies the $B$ norm clause of
`auxiliaryFunctionB_properties`. -/
theorem aux_auxiliaryFunctionB_eLpNorm_one_le :
    eLpNorm auxiliaryFunctionB 1 volume ≤ ENNReal.ofReal 8 := by
  have hprofile_bound :
      (∫ x : ℝ, 1 - sqrtOneMinusGaussian x) ≤ ∫ x : ℝ, gaussian x := by
    apply integral_mono aux_sqrtGaussianFrequencyProfile_integrable_real gaussian_integrable
    intro x
    exact aux_one_sub_sqrtOneMinusGaussian_le_gaussian x
  have habel_bound :
      (∫ x : ℝ, Real.exp (-|Real.sqrt Real.pi * x|)) ≤
        ∫ x : ℝ, aux_poissonFrequency x := by
    apply integral_mono aux_exp_neg_abs_sqrt_pi_integrable aux_poissonFrequency_integrable
    intro x
    exact aux_exp_neg_abs_sqrt_pi_le_poissonFrequency x
  have hnorm_bound : (∫ x : ℝ, ‖auxiliaryFunctionB x‖) ≤ 8 := by
    have hsum_integrable : Integrable (fun x : ℝ =>
        (1 - sqrtOneMinusGaussian x) + Real.exp (-|Real.sqrt Real.pi * x|)) :=
      aux_sqrtGaussianFrequencyProfile_integrable_real.add
        aux_exp_neg_abs_sqrt_pi_integrable
    calc
      (∫ x : ℝ, ‖auxiliaryFunctionB x‖) ≤
          ∫ x : ℝ, (1 - sqrtOneMinusGaussian x) +
            Real.exp (-|Real.sqrt Real.pi * x|) := by
        apply integral_mono aux_auxiliaryFunctionB_integrable.norm hsum_integrable
        intro x
        unfold auxiliaryFunctionB
        calc
          |1 - sqrtOneMinusGaussian x - Real.exp (-|Real.sqrt Real.pi * x|)| ≤
              |1 - sqrtOneMinusGaussian x| + |Real.exp (-|Real.sqrt Real.pi * x|)| :=
            by
              simpa using
                (abs_sub_le (1 - sqrtOneMinusGaussian x) 0
                  (Real.exp (-|Real.sqrt Real.pi * x|)))
          _ = (1 - sqrtOneMinusGaussian x) + Real.exp (-|Real.sqrt Real.pi * x|) := by
            rw [abs_of_nonneg (aux_one_sub_sqrtOneMinusGaussian_nonneg x),
              abs_of_nonneg (Real.exp_pos _).le]
      _ = (∫ x : ℝ, 1 - sqrtOneMinusGaussian x) +
          ∫ x : ℝ, Real.exp (-|Real.sqrt Real.pi * x|) := by
        rw [integral_add aux_sqrtGaussianFrequencyProfile_integrable_real
          aux_exp_neg_abs_sqrt_pi_integrable]
      _ ≤ (∫ x : ℝ, gaussian x) + ∫ x : ℝ, aux_poissonFrequency x := by
        exact add_le_add hprofile_bound habel_bound
      _ = (3 : ℝ) := by
        rw [aux_integral_gaussian, aux_integral_poissonFrequency]
        norm_num
      _ ≤ (8 : ℝ) := by norm_num
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm aux_auxiliaryFunctionB_integrable]
  exact ENNReal.ofReal_le_ofReal hnorm_bound

/-- Proposition \ref{auxiliary function B}: $B$ is continuous and smooth off $0$; its chosen
first derivative extension is continuous and integrable; its zero-extended second derivative is
measurable and integrable; and their stated eLpNorm bounds are $8$, $20$, and $100$. -/
theorem auxiliaryFunctionB_properties :
    Continuous auxiliaryFunctionB ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) auxiliaryFunctionB ({0}ᶜ : Set ℝ) ∧
      (∀ x : ℝ, x ≠ 0 →
        HasDerivAt auxiliaryFunctionB (auxiliaryFunctionBDerivative x) x) ∧
      Continuous auxiliaryFunctionBDerivative ∧
      Integrable auxiliaryFunctionBDerivative ∧
      (∀ x : ℝ, x ≠ 0 →
        HasDerivAt auxiliaryFunctionBDerivative (auxiliaryFunctionBSecondDerivative x) x) ∧
      Measurable auxiliaryFunctionBSecondDerivative ∧
      Integrable auxiliaryFunctionBSecondDerivative ∧
      eLpNorm auxiliaryFunctionB 1 volume ≤ ENNReal.ofReal 8 ∧
      eLpNorm auxiliaryFunctionBDerivative 1 volume ≤ ENNReal.ofReal 20 ∧
      eLpNorm auxiliaryFunctionBSecondDerivative 1 volume ≤ ENNReal.ofReal 100 := by
  exact ⟨aux_auxiliaryFunctionB_continuous, aux_auxiliaryFunctionB_smoothOffZero,
    fun x hx ↦ aux_auxiliaryFunctionB_hasDerivAt_of_ne_zero hx,
    aux_auxiliaryFunctionBDerivative_continuous, aux_auxiliaryFunctionBDerivative_integrable,
    fun x hx ↦ aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero hx,
    aux_auxiliaryFunctionBSecondDerivative_measurable, aux_auxiliaryFunctionBSecondDerivative_integrable,
    aux_auxiliaryFunctionB_eLpNorm_one_le, aux_auxiliaryFunctionBDerivative_eLpNorm_one_le,
    aux_auxiliaryFunctionBSecondDerivative_eLpNorm_one_le⟩

/-- This auxiliary integration-by-parts identity transfers integrable derivative bounds to
inverse Fourier transforms in the normalization used in this formalization. -/
theorem aux_inverseFourier_deriv {f : ℝ → ℂ}
    (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) (x : ℝ) :
    FourierTransformInv.fourierInv (deriv f) x =
      (-(2 * Real.pi * Complex.I * x)) * FourierTransformInv.fourierInv f x := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_deriv hf h'f hf']
  simp only [smul_eq_mul, neg_mul]
  rw [← Real.fourierInv_eq_fourier_neg]
  push_cast
  ring

/-- This auxiliary derivative formula complexifies the global differentiability of $B$ so that
the Fourier derivative theorem can be applied. -/
theorem aux_auxiliaryFunctionB_complex_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (auxiliaryFunctionB y : ℂ))
      (auxiliaryFunctionBDerivative x) x := by
  exact (aux_auxiliaryFunctionB_hasDerivAt x).ofReal_comp

/-- This auxiliary identity gives the complex derivative of $B$ used in inverse-Fourier
integration by parts. -/
theorem aux_deriv_auxiliaryFunctionB_complex (x : ℝ) :
    deriv (fun y : ℝ => (auxiliaryFunctionB y : ℂ)) x =
      (auxiliaryFunctionBDerivative x : ℂ) := by
  simpa using (aux_auxiliaryFunctionB_complex_hasDerivAt x).deriv

/-- This auxiliary derivative formula complexifies the true derivative of the continuous
extension of $B'$ for the second integration-by-parts step. -/
theorem aux_auxiliaryFunctionBDerivative_complex_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (auxiliaryFunctionBDerivative y : ℂ))
      ((if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x) : ℝ) x := by
  by_cases hx : x = 0
  · subst x
    simpa using aux_auxiliaryFunctionBDerivative_hasDerivAt_zero.ofReal_comp
  · simpa [hx] using (aux_auxiliaryFunctionBDerivative_hasDerivAt_of_ne_zero hx).ofReal_comp

/-- This auxiliary identity gives the complex derivative of the continuous extension of $B'$.
It uses the derivative value $-\pi$ at zero rather than the manuscript's separately extended
value of $B''$. -/
theorem aux_deriv_auxiliaryFunctionBDerivative_complex (x : ℝ) :
    deriv (fun y : ℝ => (auxiliaryFunctionBDerivative y : ℂ)) x =
      ((if x = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative x) : ℝ) := by
  simpa using (aux_auxiliaryFunctionBDerivative_complex_hasDerivAt x).deriv

/-- This auxiliary integrability statement supplies the derivative hypothesis for the first
inverse-Fourier integration-by-parts step. -/
theorem aux_deriv_auxiliaryFunctionB_complex_integrable :
    Integrable (deriv (fun y : ℝ => (auxiliaryFunctionB y : ℂ))) := by
  convert aux_auxiliaryFunctionBDerivative_integrable.ofReal using 1
  funext x
  exact aux_deriv_auxiliaryFunctionB_complex x

/-- This auxiliary integrability statement supplies the derivative hypothesis for the second
inverse-Fourier integration-by-parts step. -/
theorem aux_deriv_auxiliaryFunctionBDerivative_complex_integrable :
    Integrable (deriv (fun y : ℝ => (auxiliaryFunctionBDerivative y : ℂ))) := by
  convert aux_auxiliaryFunctionBTrueSecondDerivative_integrable.ofReal using 1
  funext x
  exact aux_deriv_auxiliaryFunctionBDerivative_complex x

/-- This auxiliary Fourier identity is the first integration-by-parts relation for $B$. -/
theorem aux_inverseFourier_auxiliaryFunctionBDerivative (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionBDerivative ξ : ℂ)) x =
      (-(2 * Real.pi * Complex.I * x)) *
        FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x := by
  have hderiv : deriv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) =
      fun ξ : ℝ => (auxiliaryFunctionBDerivative ξ : ℂ) := by
    funext ξ
    exact aux_deriv_auxiliaryFunctionB_complex ξ
  rw [← hderiv]
  exact aux_inverseFourier_deriv (f := fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ))
    aux_auxiliaryFunctionB_integrable.ofReal
    (fun ξ => (aux_auxiliaryFunctionB_complex_hasDerivAt ξ).differentiableAt)
    aux_deriv_auxiliaryFunctionB_complex_integrable x

/-- This auxiliary Fourier identity is the second integration-by-parts relation for the true
derivative of the continuous extension of $B'$. -/
theorem aux_inverseFourier_auxiliaryFunctionBTrueSecondDerivative (x : ℝ) :
    FourierTransformInv.fourierInv
        (fun ξ : ℝ => (((if ξ = 0 then -Real.pi
          else auxiliaryFunctionBSecondDerivative ξ) : ℝ) : ℂ)) x =
      (-(2 * Real.pi * Complex.I * x)) *
        FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionBDerivative ξ : ℂ)) x := by
  have hderiv : deriv (fun ξ : ℝ => (auxiliaryFunctionBDerivative ξ : ℂ)) =
      fun ξ : ℝ => (((if ξ = 0 then -Real.pi
        else auxiliaryFunctionBSecondDerivative ξ) : ℝ) : ℂ) := by
    funext ξ
    exact aux_deriv_auxiliaryFunctionBDerivative_complex ξ
  rw [← hderiv]
  exact aux_inverseFourier_deriv (f := fun ξ : ℝ => (auxiliaryFunctionBDerivative ξ : ℂ))
    aux_auxiliaryFunctionBDerivative_integrable.ofReal
    (fun ξ => (aux_auxiliaryFunctionBDerivative_complex_hasDerivAt ξ).differentiableAt)
    aux_deriv_auxiliaryFunctionBDerivative_complex_integrable x

/-- This auxiliary real-valued estimate extracts the $L^1$ bound for $B$ from the corresponding
`eLpNorm` clause of `auxiliaryFunctionB_properties`. -/
theorem aux_integral_norm_auxiliaryFunctionB_le_eight :
    (∫ ξ : ℝ, ‖auxiliaryFunctionB ξ‖) ≤ 8 := by
  have h := aux_auxiliaryFunctionB_eLpNorm_one_le
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm aux_auxiliaryFunctionB_integrable] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h

/-- This auxiliary uniform estimate is the zeroth-order inverse-Fourier bound for $B$. -/
theorem aux_norm_inverseFourier_auxiliaryFunctionB_le_eight (x : ℝ) :
    ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤ 8 := by
  rw [Real.fourierInv_eq]
  calc
    ‖∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • (auxiliaryFunctionB ξ : ℂ)‖ ≤
        ∫ ξ : ℝ, ‖𝐞 ⟪ξ, x⟫ • (auxiliaryFunctionB ξ : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖auxiliaryFunctionB ξ‖ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp [Circle.norm_smul]
    _ ≤ 8 := aux_integral_norm_auxiliaryFunctionB_le_eight

/-- This auxiliary real-valued estimate extracts the $L^1$ bound for the manuscript's zero
extension of $B''$ from `auxiliaryFunctionB_properties`. -/
theorem aux_integral_norm_auxiliaryFunctionBSecondDerivative_le_hundred :
    (∫ ξ : ℝ, ‖auxiliaryFunctionBSecondDerivative ξ‖) ≤ 100 := by
  have h := aux_auxiliaryFunctionBSecondDerivative_eLpNorm_one_le
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm
      aux_auxiliaryFunctionBSecondDerivative_integrable] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h

/-- This auxiliary $L^1$ estimate changes the zero extension of $B''$ to the true derivative of
the continuous extension of $B'$; the functions differ only on a null singleton. -/
theorem aux_integral_norm_auxiliaryFunctionBTrueSecondDerivative_le_hundred :
    (∫ ξ : ℝ, ‖if ξ = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative ξ‖) ≤ 100 := by
  have hne : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using (measure_singleton (0 : ℝ))
  calc
    (∫ ξ : ℝ, ‖if ξ = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative ξ‖) =
        ∫ ξ : ℝ, ‖auxiliaryFunctionBSecondDerivative ξ‖ := by
      apply integral_congr_ae
      filter_upwards [hne] with ξ hξ
      simp [hξ]
    _ ≤ 100 := aux_integral_norm_auxiliaryFunctionBSecondDerivative_le_hundred

/-- This auxiliary uniform estimate is the zeroth-order inverse-Fourier bound for the true
second derivative of the continuous extension of $B'$. -/
theorem aux_norm_inverseFourier_auxiliaryFunctionBTrueSecondDerivative_le_hundred (x : ℝ) :
    ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => (((if ξ = 0 then -Real.pi
          else auxiliaryFunctionBSecondDerivative ξ) : ℝ) : ℂ)) x‖ ≤ 100 := by
  rw [Real.fourierInv_eq]
  calc
    ‖∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ •
        (((if ξ = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative ξ) : ℝ) : ℂ)‖ ≤
        ∫ ξ : ℝ, ‖𝐞 ⟪ξ, x⟫ •
          (((if ξ = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative ξ) : ℝ) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, ‖if ξ = 0 then -Real.pi else auxiliaryFunctionBSecondDerivative ξ‖ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp [Circle.norm_smul]
    _ ≤ 100 := aux_integral_norm_auxiliaryFunctionBTrueSecondDerivative_le_hundred

/-- This auxiliary norm computation records the Fourier multiplier introduced by one
integration-by-parts step. -/
theorem aux_norm_fourier_derivative_factor (x : ℝ) :
    ‖-(2 * Real.pi * Complex.I * x)‖ = 2 * Real.pi * |x| := by
  rw [norm_neg, norm_mul, norm_mul, norm_mul]
  simp [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]

/-- This auxiliary identity combines the two inverse-Fourier integration-by-parts formulas into
the quadratic multiplier relation used for decay of the inverse transform of $B$. -/
theorem aux_auxiliaryFunctionBTrueSecondDerivative_factor_norm (x : ℝ) :
    ‖FourierTransformInv.fourierInv
        (fun ξ : ℝ => (((if ξ = 0 then -Real.pi
          else auxiliaryFunctionBSecondDerivative ξ) : ℝ) : ℂ)) x‖ =
      (4 * Real.pi ^ 2 * x ^ 2) *
        ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ := by
  rw [aux_inverseFourier_auxiliaryFunctionBTrueSecondDerivative,
    aux_inverseFourier_auxiliaryFunctionBDerivative]
  rw [norm_mul, norm_mul, aux_norm_fourier_derivative_factor]
  ring_nf
  rw [sq_abs]
  ring

/-- This auxiliary estimate is the quadratic inverse-Fourier decay bound for $B$ obtained from
its second derivative. -/
theorem aux_quadratic_inverseFourier_auxiliaryFunctionB_bound (x : ℝ) :
    (4 * Real.pi ^ 2 * x ^ 2) *
        ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤ 100 := by
  rw [← aux_auxiliaryFunctionBTrueSecondDerivative_factor_norm]
  exact aux_norm_inverseFourier_auxiliaryFunctionBTrueSecondDerivative_le_hundred x

/-- This auxiliary decay estimate combines the uniform and quadratic bounds for the inverse
Fourier transform of $B$ into the bracket-bump majorant used in `sqrtGaussianDecay`. -/
theorem aux_norm_inverseFourier_auxiliaryFunctionB_le_hundred_bracket_sq (x : ℝ) :
    ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ ≤
      100 * bracketBump x ^ 2 := by
  rw [bracketBump]
  have hden : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos (by positivity)
  have hrewrite : 100 * (1 + |x|)⁻¹ ^ 2 = 100 / (1 + |x|) ^ 2 := by
    field_simp
  rw [hrewrite]
  by_cases hx : |x| ≤ 1
  · apply (le_div_iff₀ hden).2
    have hsmall := aux_norm_inverseFourier_auxiliaryFunctionB_le_eight x
    have hfactor : (1 + |x|) ^ 2 ≤ 4 := by
      calc
        (1 + |x|) ^ 2 ≤ (2 : ℝ) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
        _ = 4 := by norm_num
    calc
      ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
          (1 + |x|) ^ 2 ≤ 8 * (1 + |x|) ^ 2 :=
        mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
      _ ≤ 8 * 4 := mul_le_mul_of_nonneg_left hfactor (by norm_num)
      _ ≤ 100 := by norm_num
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    apply (le_div_iff₀ hden).2
    have hquad := aux_quadratic_inverseFourier_auxiliaryFunctionB_bound x
    have hsum : 1 + |x| ≤ 2 * |x| := by linarith
    have hfactor : (1 + |x|) ^ 2 ≤ 4 * Real.pi ^ 2 * x ^ 2 := by
      calc
        (1 + |x|) ^ 2 ≤ (2 * |x|) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
        _ = 4 * x ^ 2 := by
          have habs_sq : |x| ^ 2 = x ^ 2 := sq_abs x
          rw [show (2 * |x|) ^ 2 = 4 * |x| ^ 2 by ring, habs_sq]
        _ ≤ 4 * Real.pi ^ 2 * x ^ 2 := by
          have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
          have hmul : 1 * x ^ 2 ≤ Real.pi ^ 2 * x ^ 2 :=
            mul_le_mul_of_nonneg_right hpi (sq_nonneg x)
          nlinarith
    calc
      ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
          (1 + |x|) ^ 2 ≤
          ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ *
            (4 * Real.pi ^ 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)
      _ = (4 * Real.pi ^ 2 * x ^ 2) *
          ‖FourierTransformInv.fourierInv (fun ξ : ℝ => (auxiliaryFunctionB ξ : ℂ)) x‖ := by ring
      _ ≤ 100 := hquad

/-- This auxiliary bound is the zero-th order Fourier estimate for the square-root Gaussian
kernel. It supplies the uniform part of the later decay argument. -/
theorem aux_norm_sqrtGaussianKernel_le_one (x : ℝ) :
    ‖sqrtGaussianKernel x‖ ≤ 1 := by
  rw [sqrtGaussianKernel, Real.fourierInv_eq]
  unfold sqrtGaussianFrequencyProfile
  calc
    ‖∫ ξ : ℝ, 𝐞 ⟪ξ, x⟫ • ((1 - sqrtOneMinusGaussian ξ : ℝ) : ℂ)‖ ≤
        ∫ ξ : ℝ, ‖𝐞 ⟪ξ, x⟫ • ((1 - sqrtOneMinusGaussian ξ : ℝ) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ : ℝ, 1 - sqrtOneMinusGaussian ξ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [Circle.norm_smul]
      simp only [one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (aux_one_sub_sqrtOneMinusGaussian_nonneg ξ)]
    _ ≤ ∫ ξ : ℝ, gaussian ξ := by
      apply integral_mono aux_sqrtGaussianFrequencyProfile_integrable_real gaussian_integrable
      intro ξ
      exact aux_one_sub_sqrtOneMinusGaussian_le_gaussian ξ
    _ = 1 := aux_integral_gaussian

/-- Constant associated with Proposition \ref{square root of Gaussian decay}; the currently
formalized continuity claim is sqrtGaussianKernel_continuous. -/
def C_squareRootGaussianDecay : ℝ := 100

end

end Codex.Preliminaries.Gaussians
