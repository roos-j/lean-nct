import LeanNct.Preliminaries.Gaussians
import LeanNct.Preliminaries.Notation

/-!
# Bumps and their estimates

The concrete bump functions and explicit constants used in the manuscript's bump estimates.
-/

namespace Codex.Preliminaries.BumpsAndEstimates

open MeasureTheory Filter
open scoped BigOperators Real
open Codex.Preliminaries.Notation
open Codex.Preliminaries.Gaussians

noncomputable section

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
  (2 : ℝ) ^ (10 * m + 10 * N ^ 2 + 10)

/-- For `1 ≤ N`, `min 1 (|x|⁻¹ ^ N) ≤ 2^N * bracketBump x ^ N`. -/
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

/-- Source label `\ref{mean value bump estimate 2}`; the explicit constant used by the public
theorem `meanValueBumpEstimate`. -/
def C_meanValueBumpEstimate (N : ℕ) : ℝ := (2 : ℝ) ^ (N + 1)

/-- Source label `\ref{compare brackets}`; auxiliary for `compare_brackets`. -/
theorem aux_compareBrackets_base (N : ℕ) {lam mu x y : ℝ}
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

/-- If `0 < s`, `0 < N`, `0 < lam ≤ mu`, `1 ≤ mu`, and
`lam * |y| ≤ mu * |x|`, then
`mu⁻¹ ^ N * scaledBracketBump N s x ≤ lam⁻¹ ^ N * scaledBracketBump N s y`. -/
theorem compare_brackets (N : ℕ) {lam mu s x y : ℝ}
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
  have hbase := aux_compareBrackets_base N hlam hmu hlammu hxy'
  unfold scaledBracketBump
  calc
    mu⁻¹ ^ N * (s⁻¹ * bracketBump (s⁻¹ * x) ^ N) =
        s⁻¹ * (mu⁻¹ ^ N * bracketBump (s⁻¹ * x) ^ N) := by ring
    _ ≤ s⁻¹ * (lam⁻¹ ^ N * bracketBump (s⁻¹ * y) ^ N) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hs.le)
    _ = lam⁻¹ ^ N * (s⁻¹ * bracketBump (s⁻¹ * y) ^ N) := by ring

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
  · have hcomp := compare_brackets (x := u) (y := w) N hs hN
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
    have hcomp := compare_brackets (x := u) (y := w) N hs hN hA hAone'
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

/-- Source label `\ref{two bump estimate}`; the explicit constant used by the public theorem
`twoBumpEstimate`. -/
def C_twoBumpEstimate (n₀ n₁ : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 + min n₀ n₁) * (1 + (min n₀ n₁ - 1)⁻¹)

/-- Source label `\ref{two bump estimate}`; auxiliary for `twoBumpEstimate`, recording the
only specialization of its final constant claim used later. -/
theorem aux_twoBumpEstimate_two_two : C_twoBumpEstimate 2 2 = 16 := by
  norm_num [C_twoBumpEstimate, Real.rpow_natCast]

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

/-- If `0 < n₀`, `0 < n₁`, `c₀ ≠ 0`, `c₁ ≠ 0`, `0 < s₀`, `0 < s₁`, and
`w = c₀ * u + c₁ * v`, then
`scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ v ≤
  aux_C_bumpTriangleNat c₀ c₁ n₀ n₁ *
    (scaledBracketBump n₀ s₀ u * scaledBracketBump n₁ s₁ w +
      scaledBracketBump n₀ s₀ w * scaledBracketBump n₁ s₁ v)`. -/
theorem bump_triangle (n₀ n₁ : ℕ) {c₀ c₁ u v w s₀ s₁ : ℝ}
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

/-- Source label `\ref{diagonal square root}`; the explicit constant used by
`diagonalSquareRoot_bound`. -/
def C_diagonalSquareRoot (N : ℕ) : ℝ :=
  Real.sqrt 2 * max (C_gaussianBumpDecay 0 N)
    (C_gaussianBumpDecay 0 2 * C_squareRootGaussianDecay * C_twoBumpEstimate 2 2)

/-- Source label `\ref{derivative of diagonal square root}`; the explicit constant used by
`derivativeDiagonalSquareRoot_bound`. -/
def C_derivativeDiagonalSquareRoot (N : ℕ) : ℝ :=
  2 * max (C_gaussianBumpDecay 1 N)
    (C_gaussianBumpDecay 0 2 * C_gaussianBumpDecay 1 2 * C_twoBumpEstimate 2 2)

/-- Source label `\ref{L:gaussian-estimate}`; the explicit constant used by the public theorem
`gaussianEstimate`. -/
def C_gaussianEstimate (N : ℕ) : ℝ :=
  Real.exp Real.pi *
    ∑ l ∈ Finset.range (N / 2 + 1),
      (N.factorial : ℝ) / ((l.factorial : ℝ) * ((N - 2 * l).factorial : ℝ)) *
        (2 : ℝ) ^ (N - 2 * l) * Real.pi ^ (N - l)

/-- Source label `\ref{L:gaussian-bump-estimate}`; the explicit constant used by the public
theorem `gaussianBumpEstimate`. -/
def C_gaussianBumpEstimate (N : ℕ) : ℝ :=
  Real.rpow (2 * Real.pi) (-(N : ℝ)) *
    ∑ l ∈ Finset.range (N + 1), (Nat.choose N l : ℝ) * C_gaussianEstimate l

/-- Source label `\ref{L:derivative-estimate-for-G}`; the explicit constant used by the public
theorem `derivativeEstimateForG`. -/
def C_derivativeEstimateForG (N : ℕ) : ℝ :=
  (N.factorial : ℝ) *
    Real.rpow (1 - Real.exp (-3 * Real.pi / 16)) (-((N + 1 : ℕ) : ℝ))

/-- Source labels `\ref{L:faa-di-bruno}` and `\ref{mean four scale Gaussian kernel}`;
auxiliary for `faaDiBruno` and `meanFourScaleGaussianKernel`. -/
noncomputable def aux_maxUpTo (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((Finset.range (N + 1)).image f).max' (by
    refine ⟨f 0, Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
    exact Finset.mem_range.mpr (Nat.succ_pos _))

/-- Source label `\ref{L:faa-di-bruno}`; the explicit constant used by the public theorem
`faaDiBruno`. -/
noncomputable def C_faaDiBruno (N : ℕ) : ℝ :=
  ((2 : ℝ) ^ (N + 1) / Real.sqrt 3) *
    ∑ p : Finpartition (Finset.range N),
      C_derivativeEstimateForG p.parts.card *
        ∏ B ∈ p.parts, C_gaussianBumpDecay B.card (N + 2)

/-- Source label `\ref{L:second-gaussian-estimate}`; the explicit constant used by the public
theorem `secondGaussianEstimate`. -/
noncomputable def C_secondGaussianEstimate (N : ℕ) : ℝ :=
  8 * ∑ l ∈ Finset.range (N + 1),
    (Nat.choose N l : ℝ) * Real.rpow (2 * Real.pi) ((l : ℝ) - N) *
      C_gaussianBumpEstimate l * C_faaDiBruno (N - l)

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

/-- Source label `\ref{four scale Gaussian kernel}`; the explicit constant used by the public
theorem `fourScaleGaussianKernel`. -/
noncomputable def C_fourScaleGaussianKernel (N : ℕ) : ℝ :=
  2 * C_smoothDecay2 N * max (C_gaussianBumpEstimate 0) (C_gaussianBumpEstimate N) +
    (2 : ℝ) ^ N * max (C_secondGaussianEstimate 0) (C_secondGaussianEstimate N)

/-- Source label `\ref{mean four scale Gaussian kernel}`; the explicit constant used by the
public theorem `meanFourScaleGaussianKernel`. -/
noncomputable def C_meanFourScaleGaussianKernel (N : ℕ) : ℝ :=
  5 * (2 : ℝ) ^ (N + 1) * aux_maxUpTo C_gaussianBumpEstimate N +
    (2 : ℝ) ^ (N + 1) * aux_maxUpTo (fun l => (2 : ℝ) ^ l * C_secondGaussianEstimate l) N

end

end Codex.Preliminaries.BumpsAndEstimates
