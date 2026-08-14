import LeanNct.Reduction.TwistedAverages
import LeanNct.Reduction.AToLambda
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
open Codex.Preliminaries.MKernels
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN
open Codex.Reduction.TwistedAverages
open Codex.Reduction.AToLambda
open Codex.Reduction.WindowsAndPairs
open Codex.Reduction.BumpFunctions
open Codex.Reduction.SmoothingDecomposition
open Codex.Reduction.Miscellany
open Codex.Reduction.OnDiagonalOffDiagonal
open Codex.Reduction.VariationSeminorms

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

/-- The first main-auxiliary constant is nonnegative. -/
private theorem aux_C_mainAuxOne_nonneg (n : ℕ) : 0 ≤ C_mainAuxOne n := by
  have hdiagonal : 0 ≤ C_diagonalBandReduction := by
    unfold C_diagonalBandReduction
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) aux_CincreaseDataReduction_nonneg)
  have hnonWhitney : 0 ≤ C_inductPositiveTermsReductionNonWhitney := by
    unfold C_inductPositiveTermsReductionNonWhitney
    apply add_nonneg
    · norm_num [C_oneScaleEstimateWindow, C_uniPair]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (by positivity)) hdiagonal
  have hskip : 0 ≤ C_inductPositiveTermsReductionNonWhitneySkip n := by
    unfold C_inductPositiveTermsReductionNonWhitneySkip
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hnonWhitney
  have hgap : 0 ≤ C_inductPositiveTermsReductionWhitneyGap n := by
    unfold C_inductPositiveTermsReductionWhitneyGap
    exact add_nonneg (mul_nonneg (by norm_num) hskip)
      (mul_nonneg (mul_nonneg (by positivity) (add_nonneg (sq_nonneg _)
        (sq_nonneg _))) hdiagonal)
  have hWhitney : 0 ≤ C_inductPositiveTermsReductionWhitney n := by
    unfold C_inductPositiveTermsReductionWhitney
    exact mul_nonneg (by norm_num) hgap
  have hproduct : 0 ≤ C_inductPositiveTermsReductionWhitneyProduct n := by
    unfold C_inductPositiveTermsReductionWhitneyProduct
    exact mul_nonneg (by positivity) hWhitney
  unfold C_mainAuxOne
  exact mul_nonneg (by positivity) hproduct

private theorem aux_mainAuxOne_windowRescale_fourier (t : ℝ) (ht : 0 < t)
    (phi : SchwartzMap ℝ ℝ) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (aux_windowRescale phi t x : ℂ)) xi =
      FourierTransform.fourier (fun x : ℝ => (phi x : ℂ)) (t * xi) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun q => (phi q : ℂ) *
    Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * (q : ℂ) * ((t * xi : ℝ) : ℂ)))
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I) •
        (aux_windowRescale phi t x : ℂ)) = ∫ x : ℝ, (t⁻¹ : ℂ) * g (t⁻¹ * x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [g, aux_windowRescale]
      have hphase : Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I) =
          Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * ((t⁻¹ * x : ℝ) : ℂ) *
            ((t * xi : ℝ) : ℂ))) := by
        congr 1
        push_cast
        field_simp [ne_of_gt ht]
      rw [hphase]
      push_cast
      ring
    _ = (t⁻¹ : ℂ) * ∫ x : ℝ, g (t⁻¹ * x) := by rw [integral_const_mul]
    _ = (t⁻¹ : ℂ) * (|t| • ∫ y : ℝ, g y) := by
      rw [Measure.integral_comp_inv_mul_left]
    _ = ∫ y : ℝ, g y := by
      rw [abs_of_pos ht]
      field_simp [ne_of_gt ht]
      rw [Complex.real_smul]
    _ = ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * (t * xi)) * Complex.I) •
        (phi x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [g]
      push_cast
      ring

private theorem aux_mainAuxOne_fourier_real_const_mul (c : ℝ) (f : ℝ → ℝ) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => ((c * f x : ℝ) : ℂ)) xi =
      (c : ℂ) * FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) xi := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  push_cast
  ring

private noncomputable def aux_mainAuxOne_windowSchwartz (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) : SchwartzMap ℝ ℝ :=
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 t⁻¹ (inv_ne_zero ht.ne'))
  t⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e psi

private theorem aux_mainAuxOne_windowSchwartz_apply (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    aux_mainAuxOne_windowSchwartz psi t ht x = aux_windowRescale psi t x := by
  simp [aux_mainAuxOne_windowSchwartz, aux_windowRescale,
    ContinuousLinearEquiv.smulLeft_apply_apply]

private noncomputable def aux_mainAuxOne_scaledWindowSchwartz (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) : SchwartzMap ℝ ℝ :=
  (2 : ℝ) ^ (-2 : ℤ) • aux_mainAuxOne_windowSchwartz psi t ht

private theorem aux_mainAuxOne_scaledWindowSchwartz_apply (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    aux_mainAuxOne_scaledWindowSchwartz psi t ht x =
      (2 : ℝ) ^ (-2 : ℤ) * aux_windowRescale psi t x := by
  rw [aux_mainAuxOne_scaledWindowSchwartz, smul_apply,
    aux_mainAuxOne_windowSchwartz_apply]
  rfl

private theorem aux_mainAuxOne_scaledWindowSchwartz_fourier (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) (xi : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t ht x : ℂ)) xi =
      ((2 : ℝ) ^ (-2 : ℤ) : ℂ) *
        FourierTransform.fourier (fun x : ℝ => (psi x : ℂ)) (t * xi) := by
  rw [show (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t ht x : ℂ)) =
      fun x => (((2 : ℝ) ^ (-2 : ℤ) * aux_windowRescale psi t x : ℝ) : ℂ) by
        funext x
        norm_cast]
  rw [aux_mainAuxOne_fourier_real_const_mul,
    aux_mainAuxOne_windowRescale_fourier t ht psi xi]
  norm_cast

private theorem aux_mainAuxOne_scaledWindowSchwartz_support (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryHypotheses psi) (t : ℝ) (ht : t ∈ Set.Icc 1 2) :
    Function.support
      (FourierTransform.fourier
        (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t
          (lt_of_lt_of_le zero_lt_one ht.1) x : ℂ))) ⊆
      Codex.Reduction.BumpFunctions.aux_annulusOne 1 ((2 : ℝ) ^ 3) := by
  rcases hpsi with ⟨hsupp, hderiv⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  intro xi hxi
  have hne := Function.mem_support.mp hxi
  rw [aux_mainAuxOne_scaledWindowSchwartz_fourier psi t htpos xi] at hne
  have hbase : FourierTransform.fourier (fun x : ℝ => (psi x : ℂ)) (t * xi) ≠ 0 := by
    exact (mul_ne_zero_iff.mp hne).2
  have hmem := hsupp (Function.mem_support.mpr hbase)
  unfold Codex.Reduction.BumpFunctions.aux_annulusOne at hmem ⊢
  change 1 / ((2 : ℝ) ^ 2) ≤ |t * xi| ∧ |t * xi| ≤ (2 : ℝ) ^ 2 * 1 at hmem
  change 1 / ((2 : ℝ) ^ 3) ≤ |xi| ∧ |xi| ≤ (2 : ℝ) ^ 3 * 1
  rw [abs_mul, abs_of_pos htpos] at hmem
  norm_num at hmem ⊢
  constructor
  · have hmul : t * |xi| ≤ 2 * |xi| :=
      mul_le_mul_of_nonneg_right ht.2 (abs_nonneg xi)
    linarith [hmem.1.trans hmul]
  · calc
      |xi| = 1 * |xi| := by ring
      _ ≤ t * |xi| := mul_le_mul_of_nonneg_right ht.1 (abs_nonneg xi)
      _ ≤ 4 := hmem.2
      _ ≤ 8 := by norm_num

private theorem aux_mainAuxOne_scaledWindowSchwartz_deriv (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryHypotheses psi) (t : ℝ) (ht : t ∈ Set.Icc 1 2) :
    ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m
        (FourierTransform.fourier
          (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t
            (lt_of_lt_of_le zero_lt_one ht.1) x : ℂ))) xi‖ ≤ 1 := by
  rcases hpsi with ⟨hsupp, hderiv⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (psi x : ℂ))
  have hF : ContDiff ℝ 2 F := by
    let psiC : SchwartzMap ℝ ℂ :=
      SchwartzMap.postcompCLM Complex.ofRealCLM psi
    have hs : ContDiff ℝ 2 (FourierTransform.fourier psiC : ℝ → ℂ) :=
      (FourierTransform.fourier psiC).smooth 2
    have hpsiC : (psiC : ℝ → ℂ) = fun y : ℝ => (psi y : ℂ) := by
      funext y
      simp [psiC, SchwartzMap.postcompCLM_apply]
    rw [SchwartzMap.fourier_coe, hpsiC] at hs
    exact hs
  intro m hm xi
  have hFbound : ∀ q : ℕ, q < 3 → ∀ x : ℝ, ‖iteratedDeriv q F x‖ ≤ 1 := by
    intro q hq x
    exact hderiv q hq x
  have hformula :
      (fun z : ℝ => FourierTransform.fourier
        (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t htpos x : ℂ)) z) =
        fun z => ((2 : ℝ) ^ (-2 : ℤ) : ℂ) * F (t * z) := by
    funext z
    exact aux_mainAuxOne_scaledWindowSchwartz_fourier psi t htpos z
  change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier
        (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t htpos x : ℂ)) z) xi‖ ≤ 1
  rw [hformula, iteratedDeriv_const_mul_field]
  rw [show iteratedDeriv m (fun z : ℝ => F (t * z)) xi =
      t ^ m • iteratedDeriv m F (t * xi) by
        exact congrFun (iteratedDeriv_comp_const_smul
          (hF.of_le (by norm_cast; omega)) t) xi]
  rw [norm_mul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg htpos.le _)]
  have hcoef : ‖((2 : ℝ) ^ (-2 : ℤ) : ℂ)‖ = (2 : ℝ) ^ (-2 : ℤ) := by
    norm_num
  rw [hcoef]
  have hpow : t ^ m ≤ 4 := by
    have hpow' : t ^ m ≤ (2 : ℝ) ^ m :=
      pow_le_pow_left₀ htpos.le ht.2 m
    have hm2 : m ≤ 2 := by omega
    calc
      t ^ m ≤ (2 : ℝ) ^ m := hpow'
      _ ≤ 4 := by interval_cases m <;> norm_num
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℤ) := by positivity
  calc
    (2 : ℝ) ^ (-2 : ℤ) * (t ^ m * ‖iteratedDeriv m F (t * xi)‖) ≤
        (2 : ℝ) ^ (-2 : ℤ) * (t ^ m * 1) := by
          gcongr
          exact hFbound m hm (t * xi)
    _ ≤ 1 := by
      have hscale : (2 : ℝ) ^ (-2 : ℤ) * t ^ m ≤ 1 := by
        calc
          (2 : ℝ) ^ (-2 : ℤ) * t ^ m ≤ (2 : ℝ) ^ (-2 : ℤ) * 4 := by
            gcongr
          _ = 1 := by norm_num
      nlinarith

/-- Extend the finite dyadic scales selected by a `TwistedDyadicChain` to a
multiplicatively spaced bi-infinite sequence. -/
private theorem aux_mainAuxOne_extend_dyadic_chain (J : ℕ) (hJ : 0 < J)
    (k : aux_dyadicChain J) :
    ∃ a : ℤ → ℝ, SpacedSequence a ∧
      ∀ j : Fin J, a (j : ℤ) = (2 : ℝ) ^ (k.1 j.castSucc) := by
  let b : ℤ → ℝ := fun z => if hz : 0 ≤ z ∧ z < (J : ℤ) then
    (2 : ℝ) ^ (k.1 (⟨z.toNat, by omega⟩ : Fin J).castSucc) else 1
  obtain ⟨a, ha, hrestrict, hlarge, hsmall⟩ :=
    (extensionOfSequences J hJ b (by
      intro z hz0 hzJ
      rw [show b z = (2 : ℝ) ^
          (k.1 (⟨z.toNat, by omega⟩ : Fin J).castSucc) by
        simp [b, hz0, hzJ]]
      exact zpow_pos (by norm_num) _)
      (by
        intro z hz0 hznext
        have hzJ : z < (J : ℤ) := by omega
        have hznextJ : z + 1 < (J : ℤ) := hznext
        let j : Fin J := ⟨z.toNat, by omega⟩
        have hsucc :
            (⟨(z + 1).toNat, by omega⟩ : Fin J).castSucc = j.succ := by
          apply Fin.ext
          dsimp [j]
          omega
        have hfin : j.castSucc < j.succ := Fin.castSucc_lt_succ
        have hstrict : k.1 j.castSucc < k.1 j.succ := k.2 hfin
        have hexp : k.1 j.castSucc + 1 ≤ k.1 j.succ :=
          Int.add_one_le_iff.mpr hstrict
        have hbz : b z = (2 : ℝ) ^ (k.1 j.castSucc) := by
          dsimp [b]
          rw [dif_pos ⟨hz0, hzJ⟩]
          congr 3
        have hbnext : b (z + 1) = (2 : ℝ) ^ (k.1 j.succ) := by
          dsimp [b]
          rw [dif_pos ⟨by omega, hznextJ⟩]
          simpa using congrArg (fun q : Fin (J + 1) =>
            (2 : ℝ) ^ (k.1 q)) hsucc
        rw [hbz, hbnext]
        calc
          2 * (2 : ℝ) ^ (k.1 j.castSucc) =
              (2 : ℝ) ^ (k.1 j.castSucc + 1) := by
                rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                norm_num
                ring
          _ ≤ (2 : ℝ) ^ (k.1 j.succ) := by
                exact (zpow_le_zpow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mpr hexp)).exists
  refine ⟨a, ha, ?_⟩
  intro j
  rw [hrestrict (j : ℤ) (by omega) (by omega)]
  dsimp [b]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 3

private theorem aux_mainAuxOne_scaled_product_bound {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryHypotheses psi)
    (t : ℝ) (ht : t ∈ Set.Icc 1 2) (a : ℤ → ℝ) (ha : SpacedSequence a) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_whitneyProductSequence
        (aux_mainAuxOne_scaledWindowSchwartz psi t
          (lt_of_lt_of_le zero_lt_one ht.1)) a) ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionWhitneyProduct n) := by
  apply inductPositiveTermsReductionWhitneyProduct hn a ha
  · exact aux_mainAuxOne_scaledWindowSchwartz_support psi hpsi t ht
  · exact aux_mainAuxOne_scaledWindowSchwartz_deriv psi hpsi t ht

private theorem aux_mainAuxOne_normalizer_mul_variation (n : ℕ) (hn : 2 ≤ n)
    (J : ℕ) (hJ : 0 < J) :
    ENNReal.ofReal (min 1
      (Real.rpow (J : ℝ) (-1 + (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ) + 1)))) *
      ENNReal.ofReal ((J : ℝ) ^ variationExponent n) = 1 := by
  have hJone : 1 ≤ (J : ℝ) := by
    exact_mod_cast (show 1 ≤ J by omega)
  have hJpos : 0 < (J : ℝ) := lt_of_lt_of_le zero_lt_one hJone
  have hpow : (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ) + 1) =
      (2 : ℝ) ^ (-(n : ℝ) + 2) := by
    rw [← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hvar : 0 ≤ variationExponent n := by
    unfold variationExponent
    rw [← hpow]
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnonpos : (-(n : ℝ) + 2) ≤ 0 := by linarith
    have hsmall : (2 : ℝ) ^ (-(n : ℝ) + 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hnonpos
    linarith
  have hweight : min 1
      (Real.rpow (J : ℝ) (-1 + (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ) + 1))) =
      (J : ℝ) ^ (-variationExponent n) := by
    rw [hpow]
    have hexp : -1 + (2 : ℝ) ^ (-(n : ℝ) + 2) = -variationExponent n := by
      unfold variationExponent
      ring
    rw [hexp]
    exact min_eq_right
      (Real.rpow_le_one_of_one_le_of_nonpos hJone (neg_nonpos.mpr hvar))
  rw [hweight, ← ENNReal.ofReal_mul (Real.rpow_nonneg hJpos.le _)]
  rw [← Real.rpow_add hJpos]
  ring_nf
  simp

private theorem aux_mainAuxOne_prefix_from_seminorm {n : ℕ} (hn : 2 ≤ n)
    (M : KernelSequence 1) (C : ℝ)
    (hM : kernelSequenceSeminorm n 1 (by omega) (by omega) M ≤ ENNReal.ofReal C)
    (J : ℕ) (hJ : 0 < J) (F : NormalizedFunctionTuple n) :
    ENNReal.ofReal
      |prismForm n 1 (by omega) (by omega)
        (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
        (fun i => F.1 i)| ≤
      ENNReal.ofReal C * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let w : ℝ := min 1
    (Real.rpow (J : ℝ) (-1 + (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ) + 1)))
  have hterm : ENNReal.ofReal
      (w * |prismForm n 1 (by omega) (by omega)
        (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
        (fun i => F.1 i)|) ≤
      kernelSequenceSeminorm n 1 (by omega) (by omega) M := by
    unfold kernelSequenceSeminorm
    apply le_iSup_of_le ⟨J, hJ⟩
    apply le_iSup_of_le F
    rfl
  have hterm' : ENNReal.ofReal
      (w * |prismForm n 1 (by omega) (by omega)
        (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
        (fun i => F.1 i)|) ≤ ENNReal.ofReal C := hterm.trans hM
  have hwr : ENNReal.ofReal w * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) = 1 := by
    dsimp [w]
    exact aux_mainAuxOne_normalizer_mul_variation n hn J hJ
  rw [ENNReal.ofReal_mul (by
    dsimp [w]
    exact le_min zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))] at hterm'
  calc
    ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i => F.1 i)| =
        1 * ENNReal.ofReal
          |prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
            (fun i => F.1 i)| := by rw [one_mul]
    _ = (ENNReal.ofReal w * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) *
        ENNReal.ofReal
          |prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
            (fun i => F.1 i)| := by rw [hwr]
    _ = (ENNReal.ofReal w * ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i => F.1 i)|) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by ac_rfl
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
      mul_le_mul_of_nonneg_right hterm' bot_le

private theorem aux_mainAuxOne_product_rescale_identity (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) (a : ℤ → ℝ) (ha : SpacedSequence a)
    (j : ℤ) (y : RealVector 1 × RealVector 1) :
    aux_liftPlaneKernel
      (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j * t)
        (mul_pos (ha j).1 ht))) y =
      (2 : ℝ) ^ 4 *
        aux_whitneyProductSequence (aux_mainAuxOne_scaledWindowSchwartz psi t ht) a j y := by
  simp only [aux_liftPlaneKernel, tensorSquare, aux_whitneyProductSequence,
    aux_windowRescale, aux_mainAuxOne_windowSchwartz_apply,
    aux_mainAuxOne_scaledWindowSchwartz_apply]
  have hapos : a j ≠ 0 := ne_of_gt (ha j).1
  field_simp [hapos, ht.ne']

private theorem aux_mainAuxOne_twistedAverage_window {n : ℕ} (psi : SchwartzMap ℝ ℝ)
    (s : ℝ) (hs : 0 < s)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    twistedAverage (aux_mainAuxOne_windowSchwartz psi s hs) f =
      twistedAverageAtScale s (fun x ↦ psi x) f := by
  unfold twistedAverage twistedAverageAtScale
  congr 1

private theorem aux_mainAuxOne_rescaled_sequence_bound {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryHypotheses psi)
    (t : ℝ) (ht : t ∈ Set.Icc 1 2) (a : ℤ → ℝ) (ha : SpacedSequence a) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (fun j y => aux_liftPlaneKernel
        (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j * t)
          (mul_pos (ha j).1 (lt_of_lt_of_le zero_lt_one ht.1)))) y) ≤
      ENNReal.ofReal (C_mainAuxOne n) := by
  let eta := aux_mainAuxOne_scaledWindowSchwartz psi t
    (lt_of_lt_of_le zero_lt_one ht.1)
  have hscaled : kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_whitneyProductSequence eta a) ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionWhitneyProduct n) := by
    dsimp [eta]
    exact aux_mainAuxOne_scaled_product_bound hn psi hpsi t ht a ha
  have hseq :
      (fun j y => aux_liftPlaneKernel
        (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j * t)
          (mul_pos (ha j).1 (lt_of_lt_of_le zero_lt_one ht.1)))) y) =
      fun j y => (2 : ℝ) ^ 4 * aux_whitneyProductSequence eta a j y := by
    funext j y
    dsimp [eta]
    exact aux_mainAuxOne_product_rescale_identity psi t
      (lt_of_lt_of_le zero_lt_one ht.1) a ha j y
  rw [hseq, aux_kernelSequenceSeminorm_const_mul (by omega) (by omega)
    ((2 : ℝ) ^ 4) (by positivity)]
  calc
    ENNReal.ofReal ((2 : ℝ) ^ 4) *
        kernelSequenceSeminorm n 1 (by omega) (by omega)
          (aux_whitneyProductSequence eta a) ≤
        ENNReal.ofReal ((2 : ℝ) ^ 4) *
          ENNReal.ofReal (C_inductPositiveTermsReductionWhitneyProduct n) :=
      mul_le_mul_of_nonneg_left hscaled bot_le
    _ = ENNReal.ofReal (C_mainAuxOne n) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      rfl

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
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc) * t) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ 2 ≤
      ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  classical
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  obtain ⟨a, ha, ha_restrict⟩ := aux_mainAuxOne_extend_dyadic_chain J hJ k
  let phi : Fin J → SchwartzMap ℝ ℝ := fun j =>
    aux_mainAuxOne_windowSchwartz psi (a (j : ℤ) * t) (mul_pos (ha (j : ℤ)).1 htpos)
  obtain ⟨F, hFnorm, hsum⟩ := aToLambda_fin_sum (n := n) (J := J) (by omega) phi f.1
  let Fnorm : NormalizedFunctionTuple n := ⟨F, by
    intro i
    convert (hFnorm i ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2))).trans
      (f.2 i) using 1 <;> norm_num⟩
  let M : KernelSequence 1 := fun j y => aux_liftPlaneKernel
    (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j * t)
      (mul_pos (ha j).1 htpos))) y
  have hMbound : kernelSequenceSeminorm n 1 (by omega) (by omega) M ≤
      ENNReal.ofReal (C_mainAuxOne n) := by
    dsimp [M]
    exact aux_mainAuxOne_rescaled_sequence_bound hn psi hpsi t ht a ha
  have hprefix := aux_mainAuxOne_prefix_from_seminorm hn M (C_mainAuxOne n) hMbound J hJ Fnorm
  have hleft :
      (∑ j : Fin J,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc) * t)
          (fun x ↦ psi x) (fun i x ↦ f.1 i x)) 2 volume ^ 2) =
      ∑ j : Fin J,
        eLpNorm (twistedAverage (phi j) (fun i x ↦ f.1 i x)) 2 volume ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [phi]
    rw [aux_mainAuxOne_twistedAverage_window]
    rw [ha_restrict j]
  have hkernel :
      (fun y : RealVector 1 × RealVector 1 =>
        ∑ j : Fin J, phi j (y.1 0) * phi j (y.2 0)) =
      fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y := by
    funext y
    let g : ℕ → ℝ := fun r => if hr : r < J then M (r : ℤ) y else 0
    calc
      (∑ j : Fin J, phi j (y.1 0) * phi j (y.2 0)) =
          ∑ r ∈ Finset.range J, g r := by
            rw [← Fin.sum_univ_eq_sum_range g J]
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [g]
            rw [if_pos j.2]
            simp only [M, phi, aux_liftPlaneKernel, tensorSquare]
      _ = ∑ r ∈ Finset.range J, M (r : ℤ) y := by
            apply Finset.sum_congr rfl
            intro r hr
            dsimp [g]
            rw [if_pos (Finset.mem_range.mp hr)]
  have hsum' :
      (∑ j : Fin J,
        eLpNorm (twistedAverage (phi j) (fun i x ↦ f.1 i x)) 2 volume ^ 2) =
      ENNReal.ofReal
        (prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i x ↦ F i x)) := by
    rw [hsum, hkernel]
  calc
    ∑ j : Fin J,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc) * t)
          (fun x ↦ psi x) (fun i x ↦ f.1 i x)) 2 volume ^ 2 =
        ENNReal.ofReal
          (prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
            (fun i x ↦ F i x)) := hleft.trans hsum'
    _ ≤ ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i x ↦ F i x)| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      simpa [Fnorm] using hprefix

/-- The sharp Whitney-product reduction estimate used for the first final-reduction
constant. -/
private theorem aux_constantWhitneyProductReduction_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_inductPositiveTermsReductionWhitneyProduct n <
      (1397 / 2048 : ℝ) * (2 : ℝ) ^ 569 := by
  unfold C_inductPositiveTermsReductionWhitneyProduct
    C_inductPositiveTermsReductionWhitney
  calc
    (2 : ℝ) ^ 12 * (11 * C_inductPositiveTermsReductionWhitneyGap n) <
        (2 : ℝ) ^ 12 * (11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553)) := by
      exact mul_lt_mul_of_pos_left
        (mul_lt_mul_of_pos_left (constantWhitneyGapReduction hn) (by norm_num))
        (by positivity)
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 569 := by
      calc
        (2 : ℝ) ^ 12 * (11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553)) =
            ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 16) * (2 : ℝ) ^ 553 := by
              rw [show (2 : ℝ) ^ 12 = 4096 by norm_num,
                show (2 : ℝ) ^ 16 = 65536 by norm_num]
              ring
        _ = (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 16 * (2 : ℝ) ^ 553) := by ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 569 := by rw [← pow_add]

/-- The sharper form of the `mainAuxOne` constant estimate before its final
relaxation to a pure power of two. -/
private theorem aux_constantMainAuxOne_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxOne n < (1397 / 2048 : ℝ) * (2 : ℝ) ^ 573 := by
  unfold C_mainAuxOne
  calc
    (2 : ℝ) ^ 4 * C_inductPositiveTermsReductionWhitneyProduct n <
        (2 : ℝ) ^ 4 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 569) :=
      mul_lt_mul_of_pos_left (aux_constantWhitneyProductReduction_sharp hn) (by positivity)
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 573 := by
      calc
        (2 : ℝ) ^ 4 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 569) =
            (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 4 * (2 : ℝ) ^ 569) := by ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 573 := by rw [← pow_add]

/-- The numerical estimate in Lemma \ref{constant main auxiliary one}. -/
theorem constantMainAuxiliaryOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxOne n < (2 : ℝ) ^ 573 := by
  calc
    C_mainAuxOne n < (1397 / 2048 : ℝ) * (2 : ℝ) ^ 573 :=
      aux_constantMainAuxOne_sharp hn
    _ < (2 : ℝ) ^ 573 := by
      apply mul_lt_of_lt_one_left
      · positivity
      · norm_num

private noncomputable def aux_shortLong_scaleKernel (phi : SchwartzMap ℝ ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s ↦ t⁻¹ * phi (t⁻¹ * s)

private theorem aux_shortLong_scaleKernel_memLp (phi : SchwartzMap ℝ ℝ) (t : ℝ) :
    MemLp (aux_shortLong_scaleKernel phi t) 2 volume := by
  by_cases ht : t = 0
  · subst t
    have : aux_shortLong_scaleKernel phi 0 = 0 := by
      funext s
      simp [aux_shortLong_scaleKernel]
    rw [this]
    exact MemLp.zero
  · have hmeas : AEStronglyMeasurable (aux_shortLong_scaleKernel phi t) volume := by
      change AEStronglyMeasurable (fun s : ℝ ↦ t⁻¹ * phi (t⁻¹ * s)) (volume : Measure ℝ)
      exact (continuous_const.mul
        (phi.continuous.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hmeas).mpr
    have hsq : Integrable (fun s : ℝ ↦ phi s ^ 2) (volume : Measure ℝ) :=
        (phi.memLp 2).integrable_sq
    have hrescale : Integrable (fun s : ℝ ↦
        t⁻¹ ^ 2 * phi (t⁻¹ * s) ^ 2) (volume : Measure ℝ) :=
      (hsq.comp_mul_left' (inv_ne_zero ht)).const_mul (t⁻¹ ^ 2)
    have heq : (fun s : ℝ ↦ aux_shortLong_scaleKernel phi t s ^ 2) =
        fun s ↦ t⁻¹ ^ 2 * phi (t⁻¹ * s) ^ 2 := by
      funext s
      dsimp [aux_shortLong_scaleKernel]
      ring
    rw [heq]
    exact hrescale

private noncomputable def aux_shortLong_averageLp {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (t : ℝ) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi t)
    (aux_shortLong_scaleKernel_memLp phi t)).toLp _

private theorem aux_shortLong_twistedAverageAtScale_contDiffOn {n : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ContDiffOn ℝ 1
      (fun t ↦ twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x)
      (Set.Icc α β) := by
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x
  let b : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (aux_tBump phi) (fun i y ↦ f i y) x
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext u
    change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  have hdiff : DifferentiableOn ℝ a (Set.Icc α β) := by
    intro t ht
    exact (aux_twistedAverageAtScale_hasDerivAt phi f x t
      (lt_of_lt_of_le hα ht.1)).differentiableAt.differentiableWithinAt
  have hcontb : ContinuousOn b (Set.Icc α β) := by
    have hconttau : ContinuousOn
        (fun t ↦ twistedAverageAtScale t (fun u ↦ tau u) (fun i y ↦ f i y) x)
        (Set.Icc α β) := by
      apply HasDerivAt.continuousOn
      intro t ht
      exact aux_twistedAverageAtScale_hasDerivAt tau f x t
        (lt_of_lt_of_le hα ht.1)
    refine hconttau.congr ?_
    intro t ht
    dsimp [b]
    rw [← htau]
  have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc α β) := by
    exact continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le hα ht.1))
  have hcontg : ContinuousOn (fun t : ℝ ↦ -t⁻¹ * b t) (Set.Icc α β) := by
    change ContinuousOn ((fun t : ℝ ↦ -(t⁻¹)) * b) (Set.Icc α β)
    exact hinv.neg.mul hcontb
  rw [show (1 : WithTop ℕ∞) = 1 by rfl,
    contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hαβ)]
  refine ⟨hdiff, hcontg.congr ?_⟩
  intro t ht
  exact (aux_twistedAverageAtScale_hasDerivAt phi f x t
    (lt_of_lt_of_le hα ht.1)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hαβ) t ht)

private theorem aux_shortLong_averageLp_enorm_sub {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (s t : ℝ) :
    (‖aux_shortLong_averageLp hn phi f s - aux_shortLong_averageLp hn phi f t‖₊ : ℝ≥0∞) =
      eLpNorm
        (fun x ↦ twistedAverageAtScale s (fun u ↦ phi u) (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f.1 i y) x)
        2 volume := by
  let hs := aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi s)
    (aux_shortLong_scaleKernel_memLp phi s)
  let ht := aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi t)
    (aux_shortLong_scaleKernel_memLp phi t)
  change ‖hs.toLp _ - ht.toLp _‖ₑ = _
  rw [← hs.toLp_sub ht]
  rw [Lp.enorm_toLp]
  rfl

private theorem aux_shortLong_ftcATphi_lintegral {n : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : ℤ) :
    (∫⁻ t,
      ‖t * deriv (fun s ↦
        twistedAverageAtScale s (fun u ↦ phi u) (fun i y ↦ f i y) x) t‖ₑ ^ (2 : ℝ)
        ∂aux_logarithmicMeasure ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
  let α : ℝ := (2 : ℝ) ^ k
  let β : ℝ := (2 : ℝ) ^ (k + 1)
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x
  let g : ℝ → ℝ := fun t ↦
    twistedAverageAtScale (α * t) (aux_tBump phi) (fun i y ↦ f i y) x
  have hα : 0 < α := by
    dsimp [α]
    exact zpow_pos (by norm_num) _
  have hβ : β = α * 2 := by
    dsimp [α, β]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have hαβ : α < β := by rw [hβ]; nlinarith
  have hconta := aux_shortLong_twistedAverageAtScale_contDiffOn phi f x hα hαβ
  have hcontb : ContinuousOn
      (fun t ↦ twistedAverageAtScale t (aux_tBump phi) (fun i y ↦ f i y) x)
      (Set.Icc α β) := by
    let psi : SchwartzMap ℝ ℝ :=
      SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
    let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
    have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
      funext u
      change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
      simp only [SchwartzMap.derivCLM_apply, aux_tBump]
      congr 1
      funext z
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      simp only [smul_eq_mul]
    have hconttau : ContinuousOn
        (fun t ↦ twistedAverageAtScale t (fun u ↦ tau u) (fun i y ↦ f i y) x)
        (Set.Icc α β) := by
      apply HasDerivAt.continuousOn
      intro t ht
      exact aux_twistedAverageAtScale_hasDerivAt tau f x t
        (lt_of_lt_of_le hα ht.1)
    refine hconttau.congr ?_
    intro t ht
    rw [← htau]
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc α β) :
      t * deriv a t = -twistedAverageAtScale t (aux_tBump phi)
        (fun i y ↦ f i y) x := by
    have h := aux_twistedAverageAtScale_hasDerivAt phi f x t
      (lt_of_lt_of_le hα ht.1)
    rw [h.deriv]
    field_simp [ne_of_gt (lt_of_lt_of_le hα ht.1)]
  have hcontd : ContinuousOn (fun t ↦ t * deriv a t) (Set.Icc α β) := by
    refine hcontb.neg.congr ?_
    intro t ht
    exact hderiv t ht
  have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc α β) :=
    continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le hα ht.1))
  have hleftCont : ContinuousOn (fun t ↦ |t * deriv a t| ^ 2 * t⁻¹)
      (Set.Icc α β) := by
    change ContinuousOn ((fun t ↦ |t * deriv a t| ^ 2) * fun t ↦ t⁻¹)
      (Set.Icc α β)
    exact (hcontd.abs.pow 2).mul hinv
  have hleftInt : Integrable (fun t ↦ |t * deriv a t| ^ 2 * t⁻¹)
      (volume.restrict (Set.Icc α β)) := hleftCont.integrableOn_Icc
  have hcontg : ContinuousOn g (Set.Icc (1 : ℝ) 2) := by
    have hscale : ContinuousOn (fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2) :=
      (continuous_const.mul continuous_id).continuousOn
    have hmaps : MapsTo (fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2)
        (Set.Icc α β) := by
      intro t ht
      constructor
      · calc
          α = α * 1 := (mul_one _).symm
          _ ≤ α * t := mul_le_mul_of_nonneg_left ht.1 hα.le
      · calc
          α * t ≤ α * 2 := mul_le_mul_of_nonneg_left ht.2 hα.le
          _ = β := hβ.symm
    change ContinuousOn
      ((fun t ↦ twistedAverageAtScale t (aux_tBump phi) (fun i y ↦ f i y) x) ∘
        fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2)
    exact hcontb.comp hscale hmaps
  have hinvOne : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc (1 : ℝ) 2) :=
    continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hrightCont : ContinuousOn (fun t ↦ |g t| ^ 2 * t⁻¹)
      (Set.Icc (1 : ℝ) 2) := by
    change ContinuousOn ((fun t ↦ |g t| ^ 2) * fun t ↦ t⁻¹)
      (Set.Icc (1 : ℝ) 2)
    exact (hcontg.abs.pow 2).mul hinvOne
  have hrightInt : Integrable (fun t ↦ |g t| ^ 2 * t⁻¹)
      (volume.restrict (Set.Icc (1 : ℝ) 2)) := hrightCont.integrableOn_Icc
  have hFTC :
      (∫ t in Set.Icc α β, |t * deriv a t| ^ 2 * t⁻¹) =
        ∫ t in Set.Icc (1 : ℝ) 2, |g t| ^ 2 * t⁻¹ := by
    simpa only [α, β, a, g] using ftcATphi phi f x k
  have hleftNonneg : 0 ≤ᵐ[volume.restrict (Set.Icc α β)]
      fun t ↦ |t * deriv a t| ^ 2 * t⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (lt_of_lt_of_le hα ht.1).le)
  have hrightNonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)]
      fun t ↦ |g t| ^ 2 * t⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (lt_of_lt_of_le zero_lt_one ht.1).le)
  have hleftOfReal := ofReal_integral_eq_lintegral_ofReal hleftInt hleftNonneg
  have hrightOfReal := ofReal_integral_eq_lintegral_ofReal hrightInt hrightNonneg
  have hweightMeas : AEMeasurable (fun t : ℝ ↦ ENNReal.ofReal t⁻¹)
      (volume.restrict (Set.Icc α β)) :=
    (measurable_inv.comp measurable_id).ennreal_ofReal.aemeasurable
  have hweightFinite : ∀ᵐ t : ℝ ∂volume.restrict (Set.Icc α β),
      ENNReal.ofReal t⁻¹ < ∞ :=
    ae_of_all _ fun _ ↦ lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
  have hleftDensity :
      (∫⁻ t,
        ‖t * deriv a t‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β) =
        ∫⁻ t in Set.Icc α β,
          ENNReal.ofReal (|t * deriv a t| ^ 2 * t⁻¹) := by
    unfold aux_logarithmicMeasure
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hweightMeas hweightFinite]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    have htpos : 0 < t := lt_of_lt_of_le hα ht.1
    change ENNReal.ofReal t⁻¹ * ‖t * deriv a t‖ₑ ^ (2 : ℝ) = _
    rw [show ‖t * deriv a t‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (|t * deriv a t| ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two,
        Real.rpow_two]]
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [ENNReal.ofReal_inv_of_pos htpos]
    ring
  have hrightEnorm :
      (∫⁻ t in Set.Icc (1 : ℝ) 2,
        ENNReal.ofReal (|g t| ^ 2 * t⁻¹)) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖g t‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [show ENNReal.ofReal (|g t| ^ 2) = ‖g t‖ₑ ^ (2 : ℝ) by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two,
        Real.rpow_two]]
  change (∫⁻ t, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
      ∂aux_logarithmicMeasure α β) =
    ∫⁻ t in Set.Icc (1 : ℝ) 2, ‖g t‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  rw [hleftDensity, ← hleftOfReal, hFTC, hrightOfReal, hrightEnorm]

private theorem aux_shortLong_pointwise_local_energy {n : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (J : ℕ) (k : ℤ)
    (u : Fin (J + 1) → aux_dyadicInterval k) (hu : Monotone u) :
    (∑ j : Fin J,
      ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f i y) x -
        twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f i y) x‖ₑ ^
          (2 : ℝ)) ≤
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
  let α : ℝ := (2 : ℝ) ^ k
  let β : ℝ := (2 : ℝ) ^ (k + 1)
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun q ↦ phi q) (fun i y ↦ f i y) x
  have hα : 0 < α := by
    dsimp [α]
    exact zpow_pos (by norm_num) _
  have hβ : β = α * 2 := by
    dsimp [α, β]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have hαβ : α < β := by rw [hβ]; nlinarith
  have hcont : ContDiffOn ℝ 1 a (Set.Icc α β) := by
    exact aux_shortLong_twistedAverageAtScale_contDiffOn phi f x hα hαβ
  let U : {v : Fin (J + 1) → Set.Icc α β // Monotone v} :=
    ⟨fun j ↦ ⟨u j, by simpa only [α, β, aux_dyadicInterval] using (u j).2⟩,
      by
        intro i j hij
        exact hu hij⟩
  have hchain :
      (∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
        finiteVariationSeminorm (fun s : Set.Icc α β ↦ a s) 2 J := by
    rw [finiteVariationSeminorm]
    exact le_iSup (fun v : {v : Fin (J + 1) → Set.Icc α β // Monotone v} ↦
      (∑ j : Fin J,
        (‖a (v.1 j.succ) - a (v.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ^
          ((2 : ℝ)⁻¹)) U
  have hratio : (β - α) / α = 1 := by
    rw [hβ]
    field_simp [ne_of_gt hα]
    norm_num
  have hftc := (ftcCsR J hα hαβ a hcont).1
  have hroot :
      (∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by
    calc
      (∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
          finiteVariationSeminorm (fun s : Set.Icc α β ↦ a s) 2 J := hchain
      _ ≤ (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
          aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := hftc
      _ = aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by rw [hratio]; norm_num
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hleft :
      ((∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)) ^
          (2 : ℝ) =
        ∑ j : Fin J,
          ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hsquare
  have hlogSq : (aux_logarithmicL2 α β (fun t ↦ t * deriv a t)) ^ (2 : ℝ) =
      ∫⁻ t, ‖t * deriv a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
    unfold aux_logarithmicL2
    have h := eLpNorm_nnreal_pow_eq_lintegral (μ := aux_logarithmicMeasure α β)
      (f := fun t ↦ t * deriv a t) (p := (2 : NNReal))
      (by norm_num : (2 : NNReal) ≠ 0)
    simpa [ENNReal.rpow_two] using h
  calc
    (∑ j : Fin J,
      ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f i y) x -
        twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f i y) x‖ₑ ^
          (2 : ℝ)) =
        ∑ j : Fin J,
          ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ) := by
      congr 2 with j
    _ ≤ (aux_logarithmicL2 α β (fun t ↦ t * deriv a t)) ^ (2 : ℝ) := hsquare
    _ = ∫⁻ t, ‖t * deriv a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := hlogSq
    _ = ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ :=
      aux_shortLong_ftcATphi_lintegral phi f x k

private theorem aux_shortLong_joint_measurable_twistedAverageAtScale {n : ℕ}
    (psi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (α : ℝ) :
    StronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
      twistedAverageAtScale (α * tx.1) (fun u ↦ psi u) (fun i y ↦ f i y) tx.2) := by
  let F : ((ℝ × EuclideanSpace ℝ (Fin n)) × ℝ) → ℝ := fun z ↦
    (α * z.1.1)⁻¹ * psi ((α * z.1.1)⁻¹ * z.2) *
      ∏ i, f i (z.1.2 + z.2 • WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  have hInt : StronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
      ∫ s : ℝ, F (tx, s) ∂(volume : Measure ℝ)) :=
    hF.stronglyMeasurable.integral_prod_right' (ν := volume)
  simpa only [F, twistedAverageAtScale, twistedAverage] using hInt

private theorem aux_shortLong_lp_chain_energy_eq_lintegral {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (J : ℕ) (k : ℤ)
    (u : Fin (J + 1) → aux_dyadicInterval k) (hu : Monotone u) :
    (∑ j : Fin J,
      ‖aux_shortLong_averageLp hn phi f (u j.succ) -
        aux_shortLong_averageLp hn phi f (u j.castSucc)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x,
        ∑ j : Fin J,
          ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q)
              (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) := by
  let g : Fin J → EuclideanSpace ℝ (Fin n) → ℝ := fun j x ↦
    twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
      twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x
  have hmem (j : Fin J) : MemLp (g j) 2 volume := by
    let hs := aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi (u j.succ))
      (aux_shortLong_scaleKernel_memLp phi (u j.succ))
    let ht := aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi (u j.castSucc))
      (aux_shortLong_scaleKernel_memLp phi (u j.castSucc))
    change MemLp
      (twistedAverage (aux_shortLong_scaleKernel phi (u j.succ)) (fun i y ↦ f.1 i y) -
        twistedAverage (aux_shortLong_scaleKernel phi (u j.castSucc)) (fun i y ↦ f.1 i y)) 2 volume
    exact hs.sub ht
  have hmeas (j : Fin J) : AEMeasurable (fun x ↦ ‖g j x‖ₑ ^ (2 : ℝ)) volume :=
    (hmem j).aestronglyMeasurable.enorm.pow_const _
  calc
    (∑ j : Fin J,
      ‖aux_shortLong_averageLp hn phi f (u j.succ) -
        aux_shortLong_averageLp hn phi f (u j.castSucc)‖ₑ ^ (2 : ℝ)) =
        ∑ j : Fin J, eLpNorm (g j) 2 volume ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℝ))
        (aux_shortLong_averageLp_enorm_sub hn phi f (u j.succ) (u j.castSucc))
    _ = ∑ j : Fin J, ∫⁻ x, ‖g j x‖ₑ ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := g j)
        (p := (2 : NNReal)) (by norm_num)
    _ = ∫⁻ x, ∑ j : Fin J, ‖g j x‖ₑ ^ (2 : ℝ) := by
      simpa using (lintegral_finset_sum' (μ := volume) Finset.univ
        (f := fun j x ↦ ‖g j x‖ₑ ^ (2 : ℝ)) (fun j _ ↦ hmeas j)).symm

private theorem aux_shortLong_local_variation_sq_le {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (J : ℕ) (k : ℤ) :
    (finiteVariationSeminorm
      (fun s : aux_dyadicInterval k ↦ aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext u
    change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  let R : ℝ≥0∞ := ∫⁻ t in Set.Icc (1 : ℝ) 2,
    eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ tau u)
      (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  have hR : R = ∫⁻ t in Set.Icc (1 : ℝ) 2,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
        (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    dsimp [R]
    rw [htau]
  have hchain (u : {v : Fin (J + 1) → aux_dyadicInterval k // Monotone v}) :
      (∑ j : Fin J,
        ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
          aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ≤ R := by
    let H : EuclideanSpace ℝ (Fin n) → ℝ → ℝ≥0∞ := fun x t ↦
      ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
        (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
    have hpoint (x : EuclideanSpace ℝ (Fin n)) :
        (∑ j : Fin J,
          ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
              (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t := by
      have h := aux_shortLong_pointwise_local_energy phi f.1 x J k u.1 u.2
      rw [← htau] at h
      exact h
    have hpointInt :
        (∫⁻ x,
          ∑ j : Fin J,
            ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
                (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ x, ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t := by
      apply lintegral_mono
      exact hpoint
    have hjoint : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦
          twistedAverageAtScale ((2 : ℝ) ^ k * z.2) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) z.1)
        (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
      exact (aux_shortLong_joint_measurable_twistedAverageAtScale tau f.1 ((2 : ℝ) ^ k)
        |>.comp_measurable measurable_swap).aestronglyMeasurable
    have hHmeas : AEMeasurable (Function.uncurry H)
        (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
      have hweight : AEMeasurable
          (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦ ENNReal.ofReal z.2⁻¹)
          (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) :=
        ((measurable_inv.comp measurable_snd).ennreal_ofReal).aemeasurable
      change AEMeasurable
        ((fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦
          ‖twistedAverageAtScale ((2 : ℝ) ^ k * z.2) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) z.1‖ₑ ^ (2 : ℝ)) *
          fun z ↦ ENNReal.ofReal z.2⁻¹) _
      exact (hjoint.enorm.pow_const _).mul hweight
    have hswap := lintegral_lintegral_swap hHmeas
    have htonelli :
        (∫⁻ x, ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t) = R := by
      rw [hswap]
      change (∫⁻ t in Set.Icc (1 : ℝ) 2,
        ∫⁻ x, ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
          (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) = R
      dsimp [R]
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      rw [lintegral_mul_const' (ENNReal.ofReal t⁻¹)
        (fun x ↦ ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
          (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ)) ENNReal.ofReal_ne_top]
      have hnorm : eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) x) 2 volume ^ (2 : ℝ) =
          ∫⁻ x, ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) := by
        have h := eLpNorm_nnreal_pow_eq_lintegral (μ := volume)
          (f := fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) x) (p := (2 : NNReal)) (by norm_num)
        simpa [ENNReal.rpow_two] using h
      rw [← hnorm]
    calc
      (∑ j : Fin J,
        ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
          aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
          ∫⁻ x,
            ∑ j : Fin J,
              ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q)
                  (fun i y ↦ f.1 i y) x -
                twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
                  (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) :=
          aux_shortLong_lp_chain_energy_eq_lintegral hn phi f J k u.1 u.2
      _ ≤ ∫⁻ x, ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t := hpointInt
      _ = R := htonelli
  have hroot : finiteVariationSeminorm
      (fun s : aux_dyadicInterval k ↦ aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J ≤
      R ^ ((2 : ℝ)⁻¹) := by
    rw [finiteVariationSeminorm]
    apply iSup_le
    intro u
    have h := ENNReal.rpow_le_rpow (hchain u) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    simpa only [← enorm_eq_nnnorm] using h
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hright : (R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = R := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hright] at hsquare
  rw [← hR]
  exact hsquare

private noncomputable def aux_shortLong_intEnergy (d : ℤ → ℤ → ℝ≥0∞) {J : ℕ}
    (t : Fin (J + 1) → ℤ) : ℝ≥0∞ :=
  ∑ j : Fin J, d (t j.succ) (t j.castSucc)

private theorem aux_shortLong_compress_mono_chain
    (d : ℤ → ℤ → ℝ≥0∞) (hdiag : ∀ z, d z z = 0) :
    ∀ (J : ℕ) (t : Fin (J + 1) → ℤ), Monotone t →
      ∃ M : ℕ, M ≤ J ∧ ∃ q : Fin (M + 1) → ℤ,
        StrictMono q ∧ q 0 = t 0 ∧ q (Fin.last M) = t (Fin.last J) ∧
          aux_shortLong_intEnergy d t = aux_shortLong_intEnergy d q := by
  intro J
  induction J with
  | zero =>
      intro t ht
      refine ⟨0, le_rfl, t, ?_, rfl, rfl, ?_⟩
      · intro i j hij
        omega
      · simp [aux_shortLong_intEnergy]
  | succ J ih =>
      intro t ht
      let u : Fin (J + 1) → ℤ := fun i => t i.succ
      have hu : Monotone u := by
        intro i j hij
        dsimp [u]
        apply ht
        exact Fin.succ_le_succ_iff.mpr hij
      obtain ⟨M, hMJ, q, hq, hq0, hqlast, henergy⟩ := ih u hu
      have hsplit : aux_shortLong_intEnergy d t =
          d (t 1) (t 0) + aux_shortLong_intEnergy d u := by
        unfold aux_shortLong_intEnergy
        rw [Fin.sum_univ_succ]
        rfl
      by_cases h01 : t 0 = t 1
      · refine ⟨M, le_trans hMJ (Nat.le_succ _), q, hq, ?_, ?_, ?_⟩
        · simpa [u, h01] using hq0
        · simpa [u, Fin.succ_last] using hqlast
        · rw [hsplit, h01, hdiag, zero_add, henergy]
      · have h01lt : t 0 < t 1 := lt_of_le_of_ne (ht (Fin.zero_le _)) h01
        let q' : Fin (M + 2) → ℤ := fun i => Fin.cases (t 0) q i
        have hq'strict : StrictMono q' := by
          intro i j hij
          by_cases hi : i = 0
          · subst i
            have hj0 : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hij)
            obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero hj0
            subst j
            have hqle : q 0 ≤ q j' := hq.monotone (Fin.zero_le _)
            have hfirst : t 0 < q 0 := by
              calc
                t 0 < t 1 := h01lt
                _ = u 0 := rfl
                _ = q 0 := hq0.symm
            exact hfirst.trans_le hqle
          · obtain ⟨i', hi'⟩ := Fin.exists_succ_eq_of_ne_zero hi
            subst i
            have hj0 : j ≠ 0 := by
              intro hj
              subst j
              exact (Fin.not_lt_zero i'.succ hij).elim
            obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero hj0
            subst j
            exact hq (Fin.succ_lt_succ_iff.mp hij)
        refine ⟨M + 1, Nat.succ_le_succ hMJ, q', hq'strict, ?_, ?_, ?_⟩
        · rfl
        · simp only [q', Fin.succ_last]
          exact hqlast
        · have hqsplit : aux_shortLong_intEnergy d q' = d (t 1) (t 0) + aux_shortLong_intEnergy d q := by
            unfold aux_shortLong_intEnergy
            rw [Fin.sum_univ_succ]
            have hqone : q' (Fin.succ 0) = t 1 := by
              change q 0 = t 1
              simpa [u] using hq0
            rw [hqone]
            rfl
          rw [hsplit, henergy, hqsplit]

private theorem aux_shortLong_variationExponent_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ variationExponent n := by
  unfold variationExponent
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(n : ℝ) + 2 ≤ 0 := by linarith
  have hpow : (2 : ℝ) ^ (-(n : ℝ) + 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  linarith

private theorem aux_shortLong_energy_of_root_le (E S V : ℝ≥0∞)
    (h : E ^ ((2 : ℝ)⁻¹) ≤ 2 * S ^ ((2 : ℝ)⁻¹) + V) :
    E ≤ 8 * S + 2 * V ^ (2 : ℝ) := by
  have hsquare := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  have hleft : (E ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = E := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hsquare
  calc
    E ≤ (2 * S ^ ((2 : ℝ)⁻¹) + V) ^ (2 : ℝ) := hsquare
    _ ≤ (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
        (((2 * S ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ)) + V ^ (2 : ℝ)) := by
      exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (p := (2 : ℝ)) (by norm_num)
    _ = 8 * S + 2 * V ^ (2 : ℝ) := by
      rw [show (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 by norm_num]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      have hterm : (S ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = S := by
        rw [← ENNReal.rpow_mul]
        norm_num
      rw [hterm]
      norm_num [mul_add]
      congr 1
      · rw [← mul_assoc]
        norm_num

private theorem aux_shortLong_long_variation_sq_le {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (A : ℝ) (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1) :
    (finiteVariationSeminorm
      (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦
        aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let R : ℝ≥0∞ := ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  have hexpNonneg : 0 ≤ variationExponent n := aux_shortLong_variationExponent_nonneg hn
  have hchain (u : {v : Fin (J + 1) → Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) //
      Monotone v}) :
      (∑ j : Fin J,
        ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
          aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ≤ R := by
    let z : Fin (J + 1) → ℤ := fun j ↦ (u.1 j).2.choose
    have hzval (j : Fin (J + 1)) : (2 : ℝ) ^ z j = u.1 j :=
      (u.1 j).2.choose_spec
    have hzmono : Monotone z := by
      intro i j hij
      apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      calc
        (2 : ℝ) ^ z i = u.1 i := hzval i
        _ ≤ u.1 j := u.2 hij
        _ = (2 : ℝ) ^ z j := (hzval j).symm
    let d : ℤ → ℤ → ℝ≥0∞ := fun p q ↦
      ‖aux_shortLong_averageLp hn phi f ((2 : ℝ) ^ p) -
        aux_shortLong_averageLp hn phi f ((2 : ℝ) ^ q)‖ₑ ^ (2 : ℕ)
    have hdiag (p : ℤ) : d p p = 0 := by
      simp [d]
    obtain ⟨M, hMJ, q, hq, hq0, hqlast, hcompress⟩ :=
      aux_shortLong_compress_mono_chain d hdiag J z hzmono
    have horig :
        (∑ j : Fin J,
          ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
            aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
          aux_shortLong_intEnergy d z := by
      unfold aux_shortLong_intEnergy d
      simp only [ENNReal.rpow_two]
      apply Finset.sum_congr rfl
      intro j _
      rw [hzval]
      rw [hzval]
    by_cases hM : M = 0
    · subst M
      have hzero : aux_shortLong_intEnergy d q = 0 := by simp [aux_shortLong_intEnergy]
      rw [horig, hcompress, hzero]
      exact bot_le
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
      let qc : aux_dyadicChain M := ⟨q, hq⟩
      have hqEnergy : aux_shortLong_intEnergy d q =
          aux_dyadicJumpEnergy (fun x ↦ phi x) f.1 M qc := by
        unfold aux_shortLong_intEnergy d aux_dyadicJumpEnergy
        apply Finset.sum_congr rfl
        intro j _
        dsimp [qc]
        simpa only [← enorm_eq_nnnorm] using congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℕ))
          (aux_shortLong_averageLp_enorm_sub hn phi f ((2 : ℝ) ^ (q j.succ))
            ((2 : ℝ) ^ (q j.castSucc)))
      have hq := hA M hMpos qc
      have hMJreal : (M : ℝ) ≤ J := by exact_mod_cast hMJ
      have hpow : (M : ℝ) ^ variationExponent n ≤
          (J : ℝ) ^ variationExponent n :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hMJreal hexpNonneg
      have hpowENN : ENNReal.ofReal ((M : ℝ) ^ variationExponent n) ≤
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
        ENNReal.ofReal_le_ofReal hpow
      calc
        (∑ j : Fin J,
          ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
            aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
            aux_shortLong_intEnergy d z := horig
        _ = aux_shortLong_intEnergy d q := hcompress
        _ = aux_dyadicJumpEnergy (fun x ↦ phi x) f.1 M qc := hqEnergy
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal ((M : ℝ) ^ variationExponent n) := hq
        _ ≤ R := by
          dsimp [R]
          exact mul_le_mul_of_nonneg_left hpowENN bot_le
  have hroot : finiteVariationSeminorm
      (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦
        aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J ≤ R ^ ((2 : ℝ)⁻¹) := by
    rw [finiteVariationSeminorm]
    apply iSup_le
    intro u
    have h := ENNReal.rpow_le_rpow (hchain u)
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    simpa only [← enorm_eq_nnnorm] using h
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hright : (R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = R := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hright] at hsquare
  exact hsquare

private theorem aux_shortLong_dyadic_index_unique {x : ℝ} {k l : ℤ}
    (hk : (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1))
    (hl : (2 : ℝ) ^ l ≤ x ∧ x < (2 : ℝ) ^ (l + 1)) :
    k = l := by
  apply le_antisymm
  · by_contra hnot
    have hlt : l < k := lt_of_not_ge hnot
    have hstep : l + 1 ≤ k := Int.add_one_le_iff.mpr hlt
    have hp : (2 : ℝ) ^ (l + 1) ≤ (2 : ℝ) ^ k :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hstep
    exact (not_lt_of_ge (hp.trans hk.1)) hl.2
  · by_contra hnot
    have hlt : k < l := lt_of_not_ge hnot
    have hstep : k + 1 ≤ l := Int.add_one_le_iff.mpr hlt
    have hp : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ l :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hstep
    exact (not_lt_of_ge (hp.trans hl.1)) hk.2

private theorem aux_shortLong_kappa_card_le {J : ℕ}
    (t : Fin (J + 1) → ℝ) (htpos : ∀ j, 0 < t j)
    (kappa : Finset ℤ)
    (hkappa : ∀ k, k ∈ kappa ↔ ∃ j,
      (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1)) :
    kappa.card ≤ J + 1 := by
  classical
  choose q hq using fun k : kappa => (hkappa k).mp k.property
  have hqin : Function.Injective q := by
    intro k l hkl
    apply Subtype.ext
    apply aux_shortLong_dyadic_index_unique (x := t (q k)) (k := (k : ℤ)) (l := (l : ℤ))
    · exact hq k
    · simpa [hkl] using hq l
  simpa using Fintype.card_le_of_injective q hqin

private theorem aux_shortLong_finset_sum_as_dyadic_chain (kappa : Finset ℤ)
    (hkappa : kappa.Nonempty) :
    ∃ (K : ℕ) (_ : 0 < K) (_ : K = kappa.card) (q : aux_dyadicChain K),
      ∀ F : ℤ → ℝ≥0∞,
        (∑ k ∈ kappa, F k) = ∑ j : Fin K, F (q.1 j.castSucc) := by
  classical
  obtain ⟨M, hcard⟩ : ∃ M : ℕ, kappa.card = M + 1 := by
    have hpos : 0 < kappa.card := Finset.card_pos.mpr hkappa
    refine ⟨kappa.card - 1, ?_⟩
    omega
  let e : Fin (M + 1) ↪o ℤ := kappa.orderEmbOfFin hcard
  let qfun : Fin (M + 2) → ℤ :=
    Fin.lastCases (e (Fin.last M) + 1) e
  have hqfun : StrictMono qfun := by
    intro i j hij
    by_cases hj : j = Fin.last (M + 1)
    · subst j
      change i.1 < M + 1 at hij
      let i' : Fin (M + 1) := ⟨i.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      rw [hi]
      simp only [qfun, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hle : e i' ≤ e (Fin.last M) := e.monotone (Fin.le_last i')
      omega
    · have hjlt : j < Fin.last (M + 1) := Fin.lt_last_iff_ne_last.mpr hj
      change i.1 < j.1 at hij
      change j.1 < M + 1 at hjlt
      let i' : Fin (M + 1) := ⟨i.1, by omega⟩
      let j' : Fin (M + 1) := ⟨j.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      have hj' : j = j'.castSucc := by rfl
      rw [hi, hj']
      simp only [qfun, Fin.lastCases_castSucc]
      apply e.strictMono
      simpa [i', j'] using hij
  let q : aux_dyadicChain (M + 1) := ⟨qfun, hqfun⟩
  refine ⟨M + 1, Nat.zero_lt_succ _, hcard.symm, q, ?_⟩
  intro F
  let e' : Fin (M + 1) → kappa := fun i ↦
    ⟨e i, Finset.orderEmbOfFin_mem kappa hcard i⟩
  have he'inj : Function.Injective e' := by
    intro i j hij
    apply e.injective
    exact congrArg Subtype.val hij
  have he'bij : Function.Bijective e' := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨he'inj, ?_⟩
    simp [hcard]
  let equiv : Fin (M + 1) ≃ kappa := Equiv.ofBijective e' he'bij
  calc
    (∑ k ∈ kappa, F k) = ∑ k : kappa, F k := (Finset.sum_coe_sort kappa F).symm
    _ = ∑ j : Fin (M + 1), F (equiv j) := by
      exact (Equiv.sum_comp equiv (fun k : kappa ↦ F k)).symm
    _ = ∑ j : Fin (M + 1), F (q.1 j.castSucc) := by
      apply Finset.sum_congr rfl
      intro j _
      change F (e j) = F (qfun j.castSucc)
      simp [qfun]

private theorem aux_shortLong_mainAuxOne_finset_pointwise {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryHypotheses psi)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (kappa : Finset ℤ) (hcard : kappa.card ≤ J + 1)
    (t : ℝ) (ht : t ∈ Set.Icc 1 2) :
    (∑ k ∈ kappa,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ)) ≤
      2 * ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  by_cases hkappa : kappa.Nonempty
  · obtain ⟨K, hK, hKcard, q, hsum⟩ :=
      aux_shortLong_finset_sum_as_dyadic_chain kappa hkappa
    let F : ℤ → ℝ≥0∞ := fun k ↦
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ)
    have hmain : (∑ j : Fin K, F (q.1 j.castSucc)) ≤
        ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((K : ℝ) ^ variationExponent n) := by
      simpa [F] using mainAuxOne hn psi hpsi f t ht K hK q
    have hexpNonneg : 0 ≤ variationExponent n := by
      unfold variationExponent
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : (2 : ℝ) ^ (-(n : ℝ) + 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      linarith
    have hexpLeOne : variationExponent n ≤ 1 := by
      unfold variationExponent
      have hpow : 0 ≤ (2 : ℝ) ^ (-(n : ℝ) + 2) :=
        Real.rpow_nonneg (by norm_num) _
      linarith
    have hKle : K ≤ J + 1 := by simpa [hKcard] using hcard
    have hKreal : (K : ℝ) ≤ 2 * J := by
      have hKJ : (K : ℝ) ≤ J + 1 := by exact_mod_cast hKle
      have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      nlinarith
    have htwo : (2 : ℝ) ^ variationExponent n ≤ 2 := by
      calc
        (2 : ℝ) ^ variationExponent n ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpLeOne
        _ = 2 := by norm_num
    have hpow : (K : ℝ) ^ variationExponent n ≤
        2 * (J : ℝ) ^ variationExponent n := by
      calc
        (K : ℝ) ^ variationExponent n ≤ (2 * J : ℝ) ^ variationExponent n :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hKreal hexpNonneg
        _ = (2 : ℝ) ^ variationExponent n * (J : ℝ) ^ variationExponent n :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * (J : ℝ) ^ variationExponent n := by gcongr
    have hpowENN : ENNReal.ofReal ((K : ℝ) ^ variationExponent n) ≤
        2 * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      calc
        ENNReal.ofReal ((K : ℝ) ^ variationExponent n) ≤
            ENNReal.ofReal (2 * (J : ℝ) ^ variationExponent n) :=
          ENNReal.ofReal_le_ofReal hpow
        _ = 2 * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    calc
      (∑ k ∈ kappa,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
          (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ)) =
          ∑ j : Fin K, F (q.1 j.castSucc) := hsum F
      _ ≤ ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((K : ℝ) ^ variationExponent n) := hmain
      _ ≤ ENNReal.ofReal (C_mainAuxOne n) *
          (2 * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
        gcongr
      _ = 2 * ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by ring
  · have hempty : kappa = ∅ := Finset.not_nonempty_iff_eq_empty.mp hkappa
    simp [hempty]

private theorem aux_shortLong_finish {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (A : ℝ)
    (hApos : 0 < A) (hCnonneg : 0 ≤ C_mainAuxOne n)
    (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1)
    (hlocal : ∀ (J : ℕ), 0 < J → ∀ κ : Finset ℤ, κ.card ≤ J + 1 →
      ∑ k ∈ κ,
        (finiteVariationSeminorm
          (fun s : aux_dyadicInterval k ↦ aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
        2 * ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :
    aux_variationBound (16 * C_mainAuxOne n + 2 * A) (fun x ↦ phi x) f.1 := by
  unfold aux_variationBound
  intro J hJ t
  let a : ℝ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    aux_shortLong_averageLp hn phi f
  obtain ⟨κ, hκ, hsplit⟩ :=
    (shortlongJumps a J 2 (by norm_num : (1 : ℝ) ≤ 2)).1 t.1 t.2.1.monotone t.2.2
  let S : ℝ≥0∞ := ∑ k ∈ κ,
    (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) 2 J) ^ (2 : ℝ)
  let V : ℝ≥0∞ := finiteVariationSeminorm
    (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) 2 J
  have henergy :
      (∑ j : Fin J,
        (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ≤
        8 * S + 2 * V ^ (2 : ℝ) := by
    exact aux_shortLong_energy_of_root_le _ S V hsplit
  have hlocal' : S ≤ 2 * ENNReal.ofReal (C_mainAuxOne n) *
      ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    have hcard : κ.card ≤ J + 1 :=
      aux_shortLong_kappa_card_le t.1 t.2.2 κ hκ
    dsimp [S, a]
    exact hlocal J hJ κ hcard
  have hlong' : V ^ (2 : ℝ) ≤
      ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    dsimp [V, a]
    exact aux_shortLong_long_variation_sq_le hn phi f J hJ A hA
  have htarget :
      8 * S + 2 * V ^ (2 : ℝ) ≤
        ENNReal.ofReal (16 * C_mainAuxOne n + 2 * A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    calc
      8 * S + 2 * V ^ (2 : ℝ) ≤
          8 * (2 * ENNReal.ofReal (C_mainAuxOne n) *
            ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) +
          2 * (ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
            gcongr
      _ = (16 * ENNReal.ofReal (C_mainAuxOne n) + 2 * ENNReal.ofReal A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by ring
      _ = ENNReal.ofReal (16 * C_mainAuxOne n + 2 * A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
        rw [ENNReal.ofReal_add]
        · rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        · exact mul_nonneg (by norm_num) hCnonneg
        · exact mul_nonneg (by norm_num) hApos.le
  have hjump : aux_jumpEnergy (fun x ↦ phi x) f.1 J t =
      ∑ j : Fin J,
        (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ) := by
    unfold aux_jumpEnergy twistedJumpEnergy
    simp only [ENNReal.rpow_two]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [← enorm_eq_nnnorm, ENNReal.rpow_two] using
      (congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℕ))
        (aux_shortLong_averageLp_enorm_sub hn phi f (t.1 j.succ) (t.1 j.castSucc))).symm
  rw [hjump]
  exact henergy.trans htarget

private theorem aux_shortLong_T_eq_tBump (phi : SchwartzMap ℝ ℝ) :
    Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ phi x) = aux_tBump phi := by
  funext x
  unfold Codex.Reduction.BumpFunctions.aux_T
    Codex.Reduction.BumpFunctions.multiplicationOperatorX aux_tBump
  simp only [smul_eq_mul]

private theorem aux_shortLong_tBump_auxHyp (phi : SchwartzMap ℝ ℝ)
    (hTphi : aux_mainAuxiliaryFourierHypotheses
      (Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ phi x))) :
    ∃ tau : SchwartzMap ℝ ℝ, (tau : ℝ → ℝ) = aux_tBump phi ∧
      aux_mainAuxiliaryHypotheses tau := by
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext u
    change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  refine ⟨tau, htau, ?_⟩
  · unfold aux_mainAuxiliaryHypotheses
    change aux_mainAuxiliaryFourierHypotheses (fun x ↦ tau x)
    rw [show (fun x : ℝ ↦ tau x) =
      Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ phi x) by
        exact htau.trans (aux_shortLong_T_eq_tBump phi).symm]
    exact hTphi

private theorem aux_shortLong_finset_log_integral_le (κ : Finset ℤ) (g : ℤ → ℝ → ℝ≥0∞)
    (hg : ∀ k ∈ κ, AEMeasurable (g k) (volume.restrict (Set.Icc (1 : ℝ) 2)))
    (B : ℝ≥0∞)
    (hpoint : ∀ᵐ t ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      ∑ k ∈ κ, g k t ≤ B) :
    (∑ k ∈ κ, ∫⁻ t in Set.Icc (1 : ℝ) 2,
      g k t * ENNReal.ofReal t⁻¹) ≤ B := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (1 : ℝ) 2)
  have hweight : AEMeasurable (fun t : ℝ ↦ ENNReal.ofReal t⁻¹) μ :=
    (ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable
  calc
    (∑ k ∈ κ, ∫⁻ t in Set.Icc (1 : ℝ) 2,
        g k t * ENNReal.ofReal t⁻¹) =
        ∫⁻ t in Set.Icc (1 : ℝ) 2,
          ∑ k ∈ κ, g k t * ENNReal.ofReal t⁻¹ := by
      rw [MeasureTheory.lintegral_finset_sum']
      intro k hk
      exact (hg k hk).mul hweight
    _ = ∫⁻ t in Set.Icc (1 : ℝ) 2,
          (∑ k ∈ κ, g k t) * ENNReal.ofReal t⁻¹ := by
      apply lintegral_congr_ae
      filter_upwards with t
      rw [Finset.sum_mul]
    _ ≤ ∫⁻ _t in Set.Icc (1 : ℝ) 2, B := by
      apply lintegral_mono_ae
      filter_upwards [hpoint, self_mem_ae_restrict measurableSet_Icc] with t ht hmem
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one hmem.1
      have htinv : t⁻¹ ≤ 1 := (inv_le_one₀ htpos).mpr hmem.1
      calc
        (∑ k ∈ κ, g k t) * ENNReal.ofReal t⁻¹ ≤
            B * ENNReal.ofReal t⁻¹ := mul_le_mul_left ht _
        _ ≤ B * 1 := by
          simpa using mul_le_mul_right (ENNReal.ofReal_le_ofReal htinv) B
        _ = B := mul_one _
    _ = B := by
      rw [MeasureTheory.lintegral_const]
      simp [Real.volume_Icc]
      norm_num

private theorem aux_shortLong_eLpNorm_sq_aemeasurable_of_joint {n : ℕ}
    (g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hjoint : AEStronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
      g tx.1 tx.2) (volume.prod volume)) :
    AEMeasurable (fun t ↦ eLpNorm (g t) 2 volume ^ (2 : ℝ)) volume := by
  have hinner : AEMeasurable (fun t ↦ ∫⁻ x,
      ‖g t x‖ₑ ^ (2 : ℝ)) volume := by
    exact (hjoint.enorm.pow_const _).lintegral_prod_right
  refine hinner.congr ?_
  filter_upwards [] with t
  symm
  simpa [ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := g t)
      (p := (2 : NNReal)) (by norm_num))

private theorem aux_shortLong_mainAuxOne_finset_log_lintegral {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryHypotheses psi)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (kappa : Finset ℤ) (hcard : kappa.card ≤ J + 1)
    (hmeas : ∀ k ∈ kappa,
      AEMeasurable (fun t ↦
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
          (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ))
        (volume.restrict (Set.Icc (1 : ℝ) 2))) :
    (∑ k ∈ kappa, ∫⁻ t in Set.Icc (1 : ℝ) 2,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) ≤
      2 * ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let F : ℤ → ℝ → ℝ≥0∞ := fun k t ↦
    eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
      (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ)
  refine aux_shortLong_finset_log_integral_le kappa F ?_
    (2 * ENNReal.ofReal (C_mainAuxOne n) *
      ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) ?_
  · intro k hk
    simpa [F] using hmeas k hk
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    simpa [F] using aux_shortLong_mainAuxOne_finset_pointwise hn psi hpsi f J hJ kappa hcard t ht

private theorem aux_shortLong_local_finset_bound {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (tau : SchwartzMap ℝ ℝ) (htau : (tau : ℝ → ℝ) = aux_tBump phi)
    (htauHyp : aux_mainAuxiliaryHypotheses tau)
    (J : ℕ) (hJ : 0 < J) (kappa : Finset ℤ) (hcard : kappa.card ≤ J + 1) :
    ∑ k ∈ kappa,
      (finiteVariationSeminorm
        (fun s : aux_dyadicInterval k ↦ aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      2 * ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  have hterm (k : ℤ) :
      (finiteVariationSeminorm
        (fun s : aux_dyadicInterval k ↦ aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
        ∫⁻ t in Set.Icc (1 : ℝ) 2,
          eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ tau u)
            (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    have h := aux_shortLong_local_variation_sq_le hn phi f J k
    rw [← htau] at h
    exact h
  calc
    (∑ k ∈ kappa,
      (finiteVariationSeminorm
        (fun s : aux_dyadicInterval k ↦ aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ)) ≤
        ∑ k ∈ kappa, ∫⁻ t in Set.Icc (1 : ℝ) 2,
          eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ tau u)
            (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k
    _ ≤ 2 * ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      apply aux_shortLong_mainAuxOne_finset_log_lintegral hn tau htauHyp f J hJ kappa hcard
      intro k hk
      let g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t x ↦
        twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ tau u)
          (fun i y ↦ f.1 i y) x
      have hjoint : AEStronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
          g tx.1 tx.2) (volume.prod volume) := by
        exact (aux_shortLong_joint_measurable_twistedAverageAtScale tau f.1 ((2 : ℝ) ^ k)
          |>.aestronglyMeasurable)
      have hsq := aux_shortLong_eLpNorm_sq_aemeasurable_of_joint g hjoint
      exact hsq.restrict


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
    (hApos : 0 < A) (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1) :
    aux_variationBound (16 * C_mainAuxOne n + 2 * A) (fun x ↦ phi x) f.1 := by
  obtain ⟨tau, htau, htauHyp⟩ := aux_shortLong_tBump_auxHyp phi hTphi
  apply aux_shortLong_finish hn phi f A hApos (aux_C_mainAuxOne_nonneg n) hA
  intro J hJ kappa hcard
  exact aux_shortLong_local_finset_bound hn phi f tau htau htauHyp J hJ kappa hcard

/-- The constant in Lemma \ref{lem:mainbump1_long1}. -/
noncomputable def C_mainBumpOneLongOne (n : ℕ) : ℝ :=
  (2 * C_uniPair) ^ 2 * C_mainAuxOne n

private theorem aux_mainBumpOneLongOne_fourier_sub_of_integrable (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦ ((f x - g x : ℝ) : ℂ)) xi =
      FourierTransform.fourier (fun x : ℝ ↦ (f x : ℂ)) xi -
        FourierTransform.fourier (fun x : ℝ ↦ (g x : ℂ)) xi := by
  let e : ℝ → ℂ := fun x ↦ Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I)
  have he : Continuous e := by
    dsimp [e]
    fun_prop
  have he_bound : ∀ x, ‖e x‖ ≤ (1 : ℝ) := by
    intro x
    rw [show e x = Complex.exp (((-2 * Real.pi * x * xi : ℝ) : ℂ) * Complex.I) by rfl,
      Complex.norm_exp]
    norm_num
  have hf' : Integrable (fun x : ℝ ↦ e x * (f x : ℂ)) :=
    hf.ofReal.bdd_mul he.aestronglyMeasurable (ae_of_all _ he_bound)
  have hg' : Integrable (fun x : ℝ ↦ e x * (g x : ℂ)) :=
    hg.ofReal.bdd_mul he.aestronglyMeasurable (ae_of_all _ he_bound)
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  change (∫ x : ℝ, e x * ((f x - g x : ℝ) : ℂ)) = _
  calc
    (∫ x : ℝ, e x * ((f x - g x : ℝ) : ℂ)) =
      ∫ x : ℝ, (e x * (f x : ℂ) - e x * (g x : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        push_cast
        ring
    _ = (∫ x : ℝ, e x * (f x : ℂ)) - ∫ x : ℝ, e x * (g x : ℂ) :=
      integral_sub hf' hg'
    _ = _ := by rfl

private theorem aux_mainBumpOneLongOne_window_profile_smooth (phi : SchwartzMap ℝ ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) := by
  let phiC : SchwartzMap ℝ ℂ :=
    phi.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hs : ContDiff ℝ (⊤ : ℕ∞) (FourierTransform.fourier phiC : ℝ → ℂ) :=
    (FourierTransform.fourier phiC).smooth (⊤ : ℕ∞)
  have hphiC : (phiC : ℝ → ℂ) = fun x : ℝ => (phi x : ℂ) := by
    funext x
    simp [phiC, SchwartzMap.postcompCLM_apply]
  rw [SchwartzMap.fourier_coe, hphiC] at hs
  exact hs

private theorem aux_mainBumpOneLongOne_window_profile_deriv_bound (c : ℝ) (N : ℕ)
    (phi : SchwartzMap ℝ ℝ) (hwin : cnWindow c N phi)
    (m : ℕ) (hm : m ≤ N) (xi : ℝ) :
    ‖iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi‖ ≤ c := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))
  have hFsupp : Function.support F ⊆ Set.Icc (-1 : ℝ) 1 := by
    simpa [F] using hwin.2.2.1
  have hFtsupp : tsupport F ⊆ Set.Icc (-1 : ℝ) 1 :=
    closure_minimal hFsupp isClosed_Icc
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · change ‖iteratedDeriv m F xi‖ ≤ c
    exact hwin.2.2.2.2 xi hxi m hm
  · have hderivSupp : Function.support (iteratedDeriv m F) ⊆
        Set.Icc (-1 : ℝ) 1 :=
      (subset_tsupport _).trans
        ((Codex.Preliminaries.BumpsAndEstimates.aux_tsupport_iteratedDeriv_subset F m).trans
          hFtsupp)
    have hzero : iteratedDeriv m F xi = 0 := by
      apply Function.notMem_support.mp
      intro hsupp
      exact hxi (hderivSupp hsupp)
    rw [hzero, norm_zero]
    exact hwin.1.le

private noncomputable def aux_mainBumpOneLongOne_psi
    (phi0 phi1 : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  (2 * C_uniPair)⁻¹ • (phi0 - phi1)

private theorem aux_mainBumpOneLongOne_psi_fourier (phi0 phi1 : SchwartzMap ℝ ℝ)
    (xi : ℝ) :
    FourierTransform.fourier
      (fun x : ℝ => (aux_mainBumpOneLongOne_psi phi0 phi1 x : ℂ)) xi =
      (((2 * C_uniPair)⁻¹ : ℝ) : ℂ) *
        (FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ)) xi -
          FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ)) xi) := by
  rw [show (fun x : ℝ => (aux_mainBumpOneLongOne_psi phi0 phi1 x : ℂ)) =
      fun x => (((2 * C_uniPair)⁻¹ * (phi0 x - phi1 x) : ℝ) : ℂ) by
        funext x
        simp [aux_mainBumpOneLongOne_psi, smul_apply]
    ]
  rw [aux_mainAuxOne_fourier_real_const_mul,
    aux_mainBumpOneLongOne_fourier_sub_of_integrable _ _ phi0.integrable phi1.integrable]

private theorem aux_mainBumpOneLongOne_psi_hypotheses (phi0 phi1 : SchwartzMap ℝ ℝ)
    (hpair : uniPair phi0 phi1) :
    aux_mainAuxiliaryHypotheses (aux_mainBumpOneLongOne_psi phi0 phi1) := by
  rcases hpair with ⟨h0, h1, hpair⟩
  constructor
  · intro xi hxi
    have hne := Function.mem_support.mp hxi
    rw [aux_mainBumpOneLongOne_psi_fourier] at hne
    have hdiff :
        FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ)) xi -
          FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ)) xi ≠ 0 :=
      (mul_ne_zero_iff.mp hne).2
    rw [Codex.Reduction.BumpFunctions.aux_annulusOne]
    constructor
    · by_contra hnot
      push Not at hnot
      have hsmall : |xi| < 1 / 4 := by
        norm_num at hnot ⊢
        exact hnot
      have hmid : xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        rw [mem_Icc]
        rw [abs_lt] at hsmall
        constructor <;> linarith [hsmall.1, hsmall.2]
      rw [h0.2.2.2.1 xi hmid, h1.2.2.2.1 xi hmid] at hdiff
      norm_num at hdiff
    · by_contra hnot
      push Not at hnot
      have hlarge : 4 < |xi| := by
        norm_num at hnot ⊢
        exact hnot
      have hout : xi ∉ Set.Icc (-1 : ℝ) 1 := by
        intro hmem
        have habs : |xi| ≤ 1 := abs_le.mpr hmem
        linarith
      have hzero0 : FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ)) xi = 0 := by
        apply Function.notMem_support.mp
        intro hsupp
        exact hout (h0.2.2.1 hsupp)
      have hzero1 : FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ)) xi = 0 := by
        apply Function.notMem_support.mp
        intro hsupp
        exact hout (h1.2.2.1 hsupp)
      rw [hzero0, hzero1] at hdiff
      exact hdiff (sub_self 0)
  · intro m hm xi
    let F0 : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ))
    let F1 : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ))
    have hF0 : ContDiff ℝ m F0 :=
      (aux_mainBumpOneLongOne_window_profile_smooth phi0).of_le
        (show (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
          exact WithTop.coe_le_coe.mpr le_top)
    have hF1 : ContDiff ℝ m F1 :=
      (aux_mainBumpOneLongOne_window_profile_smooth phi1).of_le
        (show (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
          exact WithTop.coe_le_coe.mpr le_top)
    have h0bound : ‖iteratedDeriv m F0 xi‖ ≤ C_uniPair :=
      aux_mainBumpOneLongOne_window_profile_deriv_bound C_uniPair N_uniPair phi0 h0 m
        (by simpa [N_uniPair] using Nat.le_of_lt hm) xi
    have h1bound : ‖iteratedDeriv m F1 xi‖ ≤ C_uniPair :=
      aux_mainBumpOneLongOne_window_profile_deriv_bound C_uniPair N_uniPair phi1 h1 m
        (by simpa [N_uniPair] using Nat.le_of_lt hm) xi
    have hformula :
        (fun z : ℝ => FourierTransform.fourier
          (fun x : ℝ => (aux_mainBumpOneLongOne_psi phi0 phi1 x : ℂ)) z) =
          fun z => (((2 * C_uniPair)⁻¹ : ℝ) : ℂ) * (F0 z - F1 z) := by
      funext z
      exact aux_mainBumpOneLongOne_psi_fourier phi0 phi1 z
    change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier
        (fun x : ℝ => (aux_mainBumpOneLongOne_psi phi0 phi1 x : ℂ)) z) xi‖ ≤ 1
    rw [hformula, iteratedDeriv_const_mul_field]
    change ‖(((2 * C_uniPair)⁻¹ : ℝ) : ℂ) * iteratedDeriv m (F0 - F1) xi‖ ≤ 1
    rw [iteratedDeriv_sub hF0.contDiffAt hF1.contDiffAt]
    calc
      ‖(((2 * C_uniPair)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv m F0 xi - iteratedDeriv m F1 xi)‖ ≤
          ‖(((2 * C_uniPair)⁻¹ : ℝ) : ℂ)‖ *
            (‖iteratedDeriv m F0 xi‖ + ‖iteratedDeriv m F1 xi‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖(((2 * C_uniPair)⁻¹ : ℝ) : ℂ)‖ * (C_uniPair + C_uniPair) := by
        gcongr
      _ = 1 := by norm_num [C_uniPair]

private theorem aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul {n : ℕ} (c : ℝ)
    (phi : ℝ → ℝ) (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (s : ℝ) :
    twistedAverageAtScale s (fun u => c * phi u) f =
      fun x => c * twistedAverageAtScale s phi f x := by
  funext x
  unfold twistedAverageAtScale twistedAverage
  calc
    (∫ q : ℝ, s⁻¹ * (c * phi (s⁻¹ * q)) * ∏ i,
      f i (x + q • WithLp.toLp 2 (Pi.single i (1 : ℝ)))) =
        ∫ q : ℝ, c *
          (s⁻¹ * phi (s⁻¹ * q) * ∏ i,
            f i (x + q • WithLp.toLp 2 (Pi.single i (1 : ℝ)))) := by
          apply integral_congr_ae
          filter_upwards [] with q
          ring
    _ = _ := integral_const_mul _ _

private theorem aux_mainBumpOneLongOne_twistedAverageAtScale_sub {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (s : ℝ) (hs : s ≠ 0) :
    twistedAverageAtScale s (fun u => phi0 u - phi1 u) (fun i x => f i x) =
      twistedAverageAtScale s (fun u => phi0 u) (fun i x => f i x) -
        twistedAverageAtScale s (fun u => phi1 u) (fun i x => f i x) := by
  funext x
  let P : ℝ → ℝ := fun q => ∏ i,
    f i (x + q • WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  let B : ℝ := ∏ i, ‖(f i).toBoundedContinuousFunction‖
  have hPcont : Continuous P := by
    dsimp [P]
    fun_prop
  have hPbound : ∀ q : ℝ, ‖P q‖ ≤ B := by
    intro q
    rw [show ‖P q‖ = ∏ i, ‖f i (x + q • WithLp.toLp 2 (Pi.single i (1 : ℝ)))‖ by
      simp [P, norm_prod]]
    apply Finset.prod_le_prod
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      exact BoundedContinuousFunction.norm_coe_le_norm
        (f i).toBoundedContinuousFunction _
  have hscaled0 : Integrable (fun q : ℝ => s⁻¹ * phi0 (s⁻¹ * q)) := by
    convert (phi0.integrable.comp_mul_left' (inv_ne_zero hs)).const_mul s⁻¹ using 1
  have hscaled1 : Integrable (fun q : ℝ => s⁻¹ * phi1 (s⁻¹ * q)) := by
    convert (phi1.integrable.comp_mul_left' (inv_ne_zero hs)).const_mul s⁻¹ using 1
  have hI0 : Integrable (fun q : ℝ =>
      (s⁻¹ * phi0 (s⁻¹ * q)) * P q) :=
    hscaled0.mul_bdd hPcont.aestronglyMeasurable (ae_of_all _ hPbound)
  have hI1 : Integrable (fun q : ℝ =>
      (s⁻¹ * phi1 (s⁻¹ * q)) * P q) :=
    hscaled1.mul_bdd hPcont.aestronglyMeasurable (ae_of_all _ hPbound)
  unfold twistedAverageAtScale twistedAverage
  change (∫ q : ℝ, s⁻¹ * (phi0 (s⁻¹ * q) - phi1 (s⁻¹ * q)) * P q) = _
  calc
    (∫ q : ℝ, s⁻¹ * (phi0 (s⁻¹ * q) - phi1 (s⁻¹ * q)) * P q) =
      ∫ q : ℝ, ((s⁻¹ * phi0 (s⁻¹ * q)) * P q -
        (s⁻¹ * phi1 (s⁻¹ * q)) * P q) := by
        apply integral_congr_ae
        filter_upwards [] with q
        ring
    _ = _ := integral_sub hI0 hI1

private theorem aux_mainBumpOneLongOne_psi_twistedAverageAtScale {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (s : ℝ) (hs : s ≠ 0) :
    twistedAverageAtScale s (fun u => aux_mainBumpOneLongOne_psi phi0 phi1 u)
        (fun i x => f i x) =
      fun x => (2 * C_uniPair)⁻¹ *
        (twistedAverageAtScale s (fun u => phi0 u) (fun i x => f i x) x -
          twistedAverageAtScale s (fun u => phi1 u) (fun i x => f i x) x) := by
  rw [show (fun u => aux_mainBumpOneLongOne_psi phi0 phi1 u) =
      fun u => (2 * C_uniPair)⁻¹ * (phi0 u - phi1 u) by
        funext u
        simp [aux_mainBumpOneLongOne_psi, smul_apply]
    ]
  rw [aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul,
    aux_mainBumpOneLongOne_twistedAverageAtScale_sub phi0 phi1 f s hs]
  rfl

private theorem aux_mainBumpOneLongOne_eLpNorm_sq_const_mul {X : Type*} [MeasurableSpace X]
    (c : ℝ) (hc : 0 ≤ c) (g : X → ℝ) (mu : Measure X) :
    eLpNorm (fun x => c * g x) 2 mu ^ 2 =
      ENNReal.ofReal (c ^ 2) * eLpNorm g 2 mu ^ 2 := by
  change eLpNorm (c • g) 2 mu ^ 2 = _
  rw [eLpNorm_const_smul]
  have hnorm : ‖c‖ₑ = ENNReal.ofReal c := by
    change (↑‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal c
    rw [ENNReal.ofReal]
    congr
    exact (Real.nnnorm_of_nonneg hc).trans (Real.toNNReal_of_nonneg hc).symm
  rw [hnorm, mul_pow, ← ENNReal.ofReal_pow hc]

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
  classical
  let c : ℝ := 2 * C_uniPair
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  let psi : SchwartzMap ℝ ℝ := aux_mainBumpOneLongOne_psi phi0 phi1
  have hpsi : aux_mainAuxiliaryHypotheses psi := by
    dsimp [psi]
    exact aux_mainBumpOneLongOne_psi_hypotheses phi0 phi1 hpair
  have hmain := mainAuxOne hn psi hpsi f 1 (by norm_num) J hJ k
  have hmain' :
      ∑ j : Fin J,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun x ↦ psi x) (fun i x ↦ f.1 i x)) 2 volume ^ 2 ≤
        ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    simpa using hmain
  have hpoint (j : Fin J) :
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x) =
        fun x ↦ c * twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ psi u) (fun i y ↦ f.1 i y) x := by
    funext x
    have htw := congrFun (aux_mainBumpOneLongOne_psi_twistedAverageAtScale phi0 phi1 f
      ((2 : ℝ) ^ (k.1 j.castSucc)) (zpow_ne_zero _ (by norm_num))) x
    change twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
        (fun u ↦ psi u) (fun i y ↦ f.1 i y) x =
        c⁻¹ * (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
            (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x) at htw
    calc
      twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
        twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x =
          c * (c⁻¹ * (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
            (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
              (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)) := by
            field_simp [hc.ne']
      _ = c * twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ psi u) (fun i y ↦ f.1 i y) x := by rw [← htw]
  have hterm (j : Fin J) :
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 =
      ENNReal.ofReal (c ^ 2) *
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ psi u) (fun i y ↦ f.1 i y)) 2 volume ^ 2 := by
    rw [hpoint j]
    exact aux_mainBumpOneLongOne_eLpNorm_sq_const_mul c hc.le _ volume
  calc
    ∑ j : Fin J,
        eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
                (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
                (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)
          2 volume ^ 2 =
        ∑ j : Fin J, ENNReal.ofReal (c ^ 2) *
          eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
            (fun u ↦ psi u) (fun i y ↦ f.1 i y)) 2 volume ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j
    _ = ENNReal.ofReal (c ^ 2) *
        ∑ j : Fin J, eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ psi u) (fun i y ↦ f.1 i y)) 2 volume ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (c ^ 2) *
        (ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :=
      mul_le_mul_of_nonneg_left hmain' bot_le
    _ = ENNReal.ofReal (C_mainBumpOneLongOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [← mul_assoc]
      rw [← ENNReal.ofReal_mul (sq_nonneg c)]
      simp [C_mainBumpOneLongOne, c]

/-- The numerical estimate in Lemma \ref{constant main bump one long one}. -/
theorem constantMainBumpOneLongOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLongOne n < (2 : ℝ) ^ 605 := by
  unfold C_mainBumpOneLongOne
  calc
    (2 * C_uniPair) ^ 2 * C_mainAuxOne n <
        (2 * C_uniPair) ^ 2 * (2 : ℝ) ^ 573 :=
      mul_lt_mul_of_pos_left (constantMainAuxiliaryOne hn) (by norm_num [C_uniPair])
    _ = (2 : ℝ) ^ 605 := by
      calc
        (2 * C_uniPair) ^ 2 * (2 : ℝ) ^ 573 =
            (2 : ℝ) ^ 32 * (2 : ℝ) ^ 573 := by norm_num [C_uniPair]
        _ = (2 : ℝ) ^ (32 + 573) := by rw [← pow_add]
        _ = (2 : ℝ) ^ 605 := by norm_num

/-- The constant in Lemma \ref{lem:mainbump1_long2}. -/
noncomputable def C_mainBumpOneLongTwo (n : ℕ) : ℝ :=
  2 * C_inductPositiveTermsReductionNonWhitneySkip n

/-- Extend all finite scales in a dyadic chain to a spaced sequence. -/
private theorem aux_mainBumpOneLongTwo_extend_dyadic_chain (J : ℕ)
    (k : aux_dyadicChain J) :
    ∃ a : ℤ → ℝ, SpacedSequence a ∧
      ∀ j : Fin (J + 1), a (j : ℤ) = (2 : ℝ) ^ (k.1 j) := by
  let b : ℤ → ℝ := fun z => if hz : 0 ≤ z ∧ z < (J + 1 : ℕ) then
    (2 : ℝ) ^ (k.1 (⟨z.toNat, by omega⟩ : Fin (J + 1))) else 1
  obtain ⟨a, ha, hrestrict, hlarge, hsmall⟩ :=
    (extensionOfSequences (J + 1) (by omega) b (by
      intro z hz0 hzJ
      rw [show b z = (2 : ℝ) ^ (k.1 (⟨z.toNat, by omega⟩ : Fin (J + 1))) by
        dsimp [b]
        rw [dif_pos ⟨hz0, by omega⟩]]
      exact zpow_pos (by norm_num) _)
      (by
        intro z hz0 hznext
        have hzJ : z < (J + 1 : ℕ) := by omega
        have hznextJ : z + 1 < (J + 1 : ℕ) := hznext
        let j : Fin J := ⟨z.toNat, by omega⟩
        have hsucc :
            (⟨(z + 1).toNat, by omega⟩ : Fin (J + 1)) = j.succ := by
          apply Fin.ext
          dsimp [j]
          omega
        have hstrict : k.1 j.castSucc < k.1 j.succ := k.2 Fin.castSucc_lt_succ
        have hexp : k.1 j.castSucc + 1 ≤ k.1 j.succ :=
          Int.add_one_le_iff.mpr (by simpa using hstrict)
        have hbz : b z = (2 : ℝ) ^ (k.1 j.castSucc) := by
          dsimp [b]
          rw [dif_pos ⟨hz0, by omega⟩]
          congr 3
        have hbnext : b (z + 1) = (2 : ℝ) ^ (k.1 j.succ) := by
          dsimp [b]
          rw [dif_pos ⟨by omega, hznextJ⟩]
          rw [hsucc]
        rw [hbz, hbnext]
        calc
          2 * (2 : ℝ) ^ (k.1 j.castSucc) =
              (2 : ℝ) ^ (k.1 j.castSucc + 1) := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            norm_num
            ring
          _ ≤ (2 : ℝ) ^ (k.1 j.succ) :=
            (zpow_le_zpow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mpr hexp)).exists
  refine ⟨a, ha, ?_⟩
  intro j
  rw [hrestrict (j : ℤ) (by omega) (by omega)]
  dsimp [b]
  split
  · congr 3
  · rename_i h
    exfalso
    apply h
    omega

private theorem aux_mainBumpOneLongTwo_sum_range_two_mul {M : Type*} [AddCommMonoid M]
    (q : ℕ → M) (K : ℕ) :
    (∑ j ∈ Finset.range (2 * K), q j) =
      (∑ j ∈ Finset.range K, q (2 * j)) +
        ∑ j ∈ Finset.range K, q (2 * j + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp only [Nat.mul_succ, Finset.sum_range_succ, ih]
      ac_rfl

private theorem aux_mainBumpOneLongTwo_sum_range_two_mul_add_one
    {M : Type*} [AddCommMonoid M] (q : ℕ → M) (K : ℕ) :
    (∑ j ∈ Finset.range (2 * K + 1), q j) =
      (∑ j ∈ Finset.range (K + 1), q (2 * j)) +
        ∑ j ∈ Finset.range K, q (2 * j + 1) := by
  rw [Finset.sum_range_succ, aux_mainBumpOneLongTwo_sum_range_two_mul]
  rw [Finset.sum_range_succ]
  ac_rfl

private theorem aux_mainBumpOneLongTwo_nonWhitneySkip_prefix {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) (N : ℕ) (hN : 0 < N) :
    ∑ j : Fin N,
      eLpNorm
        (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
        ENNReal.ofReal ((N : ℝ) ^ variationExponent n) := by
  classical
  let psi : Fin N → SchwartzMap ℝ ℝ := fun j =>
    aux_mainAuxOne_windowSchwartz phi0 (a (2 * (j : ℤ))) (ha (2 * (j : ℤ))).1 -
      aux_mainAuxOne_windowSchwartz phi1 (a (2 * (j : ℤ) + 1))
        (ha (2 * (j : ℤ) + 1)).1
  obtain ⟨F, hFnorm, hsum⟩ := aToLambda_fin_sum (n := n) (J := N) (by omega) psi f.1
  let Fnorm : NormalizedFunctionTuple n := ⟨F, by
    intro i
    convert (hFnorm i ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2))).trans
      (f.2 i) using 1 <;> norm_num⟩
  let M : KernelSequence 1 := aux_nonWhitneySkipSequence phi0 phi1 a
  have hMbound : kernelSequenceSeminorm n 1 (by omega) (by omega) M ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) := by
    dsimp [M]
    exact inductPositiveTermsReductionNonWhitneySkip hn a ha phi0 phi1 hpair
  have hprefix := aux_mainAuxOne_prefix_from_seminorm hn M
    (C_inductPositiveTermsReductionNonWhitneySkip n) hMbound N hN Fnorm
  have hleft :
      (∑ j : Fin N,
        eLpNorm
          (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
                (fun i y ↦ f.1 i y) x)
          2 volume ^ 2) =
      ∑ j : Fin N,
        eLpNorm (twistedAverage (psi j) (fun i x ↦ f.1 i x)) 2 volume ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [psi]
    change eLpNorm
        (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 =
      eLpNorm
        (twistedAverage
          ((fun x ↦ aux_mainAuxOne_windowSchwartz phi0 (a (2 * (j : ℤ)))
              (ha (2 * (j : ℤ))).1 x) -
            (fun x ↦ aux_mainAuxOne_windowSchwartz phi1 (a (2 * (j : ℤ) + 1))
              (ha (2 * (j : ℤ) + 1)).1 x))
          (fun i x ↦ f.1 i x)) 2 volume ^ 2
    rw [aux_twistedAverage_sub_of_memLp hn f.1
      (aux_mainAuxOne_windowSchwartz phi0 (a (2 * (j : ℤ))) (ha (2 * (j : ℤ))).1)
      (aux_mainAuxOne_windowSchwartz phi1 (a (2 * (j : ℤ) + 1))
        (ha (2 * (j : ℤ) + 1)).1)
      ((aux_mainAuxOne_windowSchwartz phi0 (a (2 * (j : ℤ)))
        (ha (2 * (j : ℤ))).1).memLp 2)
      ((aux_mainAuxOne_windowSchwartz phi1 (a (2 * (j : ℤ) + 1))
        (ha (2 * (j : ℤ) + 1)).1).memLp 2)]
    rw [aux_mainAuxOne_twistedAverage_window, aux_mainAuxOne_twistedAverage_window]
    rfl
  have hkernel :
      (fun y : RealVector 1 × RealVector 1 =>
        ∑ j : Fin N, psi j (y.1 0) * psi j (y.2 0)) =
      fun y => ∑ j ∈ Finset.range N, M (j : ℤ) y := by
    funext y
    let g : ℕ → ℝ := fun r => if hr : r < N then M (r : ℤ) y else 0
    calc
      (∑ j : Fin N, psi j (y.1 0) * psi j (y.2 0)) =
          ∑ r ∈ Finset.range N, g r := by
            rw [← Fin.sum_univ_eq_sum_range g N]
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [g]
            rw [if_pos j.2]
            simp only [M, psi, aux_nonWhitneySkipSequence, aux_liftPlaneKernel,
              tensorSquare, sub_apply]
            have h0 (x : ℝ) := aux_mainAuxOne_windowSchwartz_apply phi0
              (a (2 * (j : ℤ))) (ha (2 * (j : ℤ))).1 x
            have h1 (x : ℝ) := aux_mainAuxOne_windowSchwartz_apply phi1
              (a (2 * (j : ℤ) + 1)) (ha (2 * (j : ℤ) + 1)).1 x
            rw [h0 (y.1 0), h1 (y.1 0), h0 (y.2 0), h1 (y.2 0)]
      _ = ∑ r ∈ Finset.range N, M (r : ℤ) y := by
            apply Finset.sum_congr rfl
            intro r hr
            dsimp [g]
            rw [if_pos (Finset.mem_range.mp hr)]
  have hsum' :
      (∑ j : Fin N,
        eLpNorm (twistedAverage (psi j) (fun i x ↦ f.1 i x)) 2 volume ^ 2) =
      ENNReal.ofReal
        (prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range N, M (j : ℤ) y)
          (fun i x ↦ F i x)) := by
    rw [hsum, hkernel]
  calc
    ∑ j : Fin N,
        eLpNorm
          (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
                (fun i y ↦ f.1 i y) x)
          2 volume ^ 2 =
        ENNReal.ofReal
          (prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range N, M (j : ℤ) y)
            (fun i x ↦ F i x)) := hleft.trans hsum'
    _ ≤ ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range N, M (j : ℤ) y)
          (fun i x ↦ F i x)| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
        ENNReal.ofReal ((N : ℝ) ^ variationExponent n) := by
      simpa [Fnorm] using hprefix

private theorem aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) (N J : ℕ) (hNJ : N ≤ J) :
    ∑ j : Fin N,
      eLpNorm
        (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  by_cases hN : N = 0
  · subst N
    simp
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hprefix := aux_mainBumpOneLongTwo_nonWhitneySkip_prefix hn a ha phi0 phi1 hpair f N hNpos
    have hpow : (N : ℝ) ^ variationExponent n ≤ (J : ℝ) ^ variationExponent n :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hNJ)
        (aux_shortLong_variationExponent_nonneg hn)
    have hpowENN : ENNReal.ofReal ((N : ℝ) ^ variationExponent n) ≤
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := ENNReal.ofReal_le_ofReal hpow
    exact hprefix.trans (mul_le_mul_of_nonneg_left hpowENN bot_le)

private theorem aux_mainBumpOneLongTwo_chain_pair_eq {n : ℕ} (a : ℤ → ℝ) (J : ℕ)
    (k : aux_dyadicChain J)
    (ha : ∀ j : Fin (J + 1), a (j : ℤ) = (2 : ℝ) ^ (k.1 j))
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (j : Fin J) :
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume ^ 2 =
    eLpNorm
      (fun x ↦ twistedAverageAtScale (a (j : ℤ)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale (a ((j : ℤ) + 1)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume ^ 2 := by
  rw [← ha j.castSucc, ← ha j.succ]
  congr 5 <;> norm_num

private noncomputable def aux_mainBumpOneLongTwo_pairEnergy {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (a : ℤ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  eLpNorm
    (fun x ↦ twistedAverageAtScale (a (m : ℤ)) (fun u ↦ phi0 u)
          (fun i y ↦ f.1 i y) x -
        twistedAverageAtScale (a ((m : ℤ) + 1)) (fun u ↦ phi1 u)
          (fun i y ↦ f.1 i y) x)
    2 volume ^ 2

private theorem aux_mainBumpOneLongTwo_pairEnergy_even {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (a : ℤ → ℝ) (r : ℕ) :
    aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r) =
      eLpNorm
        (fun x ↦ twistedAverageAtScale (a (2 * (r : ℤ))) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (a (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 := by
  unfold aux_mainBumpOneLongTwo_pairEnergy
  congr 5 <;> norm_num

private theorem aux_mainBumpOneLongTwo_pairEnergy_odd {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (a : ℤ → ℝ) (r : ℕ) :
    aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) =
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((fun z => a (z + 1)) (2 * (r : ℤ)))
              (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((fun z => a (z + 1)) (2 * (r : ℤ) + 1))
              (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 := by
  unfold aux_mainBumpOneLongTwo_pairEnergy
  congr 5 <;> norm_num

private theorem aux_mainBumpOneLongTwo_chain_pairEnergy_eq {n : ℕ} (a : ℤ → ℝ) (J : ℕ)
    (k : aux_dyadicChain J)
    (ha : ∀ j : Fin (J + 1), a (j : ℤ) = (2 : ℝ) ^ (k.1 j))
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (j : Fin J) :
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume ^ 2 = aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a j := by
  exact aux_mainBumpOneLongTwo_chain_pair_eq a J k ha phi0 phi1 f j

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
  classical
  obtain ⟨a, ha, hrestrict⟩ := aux_mainBumpOneLongTwo_extend_dyadic_chain J k
  have hleft :
      (∑ j : Fin J,
        eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
                (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ))
                (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)
          2 volume ^ 2) =
        ∑ m ∈ Finset.range J, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a m := by
    calc
      (∑ j : Fin J,
        eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
                (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ))
                (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)
          2 volume ^ 2) =
          ∑ j : Fin J, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a j := by
            apply Finset.sum_congr rfl
            intro j hj
            exact aux_mainBumpOneLongTwo_chain_pairEnergy_eq a J k hrestrict phi0 phi1 f j
      _ = ∑ m ∈ Finset.range J, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a m := by
            rw [← Fin.sum_univ_eq_sum_range (aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a) J]
  rw [hleft]
  rcases Nat.even_or_odd' J with ⟨K, rfl | rfl⟩
  · rw [aux_mainBumpOneLongTwo_sum_range_two_mul]
    have hevenEq :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) =
          ∑ r : Fin K,
            eLpNorm
              (fun x ↦ twistedAverageAtScale (a (2 * (r : ℤ))) (fun u ↦ phi0 u)
                    (fun i y ↦ f.1 i y) x -
                  twistedAverageAtScale (a (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
                    (fun i y ↦ f.1 i y) x)
              2 volume ^ 2 := by
      calc
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) =
            ∑ r : Fin K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun r => aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) K]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              exact aux_mainBumpOneLongTwo_pairEnergy_even phi0 phi1 f a r
    have heven :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) ≤
          ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n) := by
      rw [hevenEq]
      exact aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le hn a ha phi0 phi1 hpair f K
        (2 * K) (by omega)
    let b : ℤ → ℝ := fun z => a (z + 1)
    have hb : SpacedSequence b := by
      dsimp [b]
      exact shift_mem_A ha 1
    have hoddEq :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) =
          ∑ r : Fin K,
            eLpNorm
              (fun x ↦ twistedAverageAtScale (b (2 * (r : ℤ))) (fun u ↦ phi0 u)
                    (fun i y ↦ f.1 i y) x -
                  twistedAverageAtScale (b (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
                    (fun i y ↦ f.1 i y) x)
              2 volume ^ 2 := by
      calc
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) =
            ∑ r : Fin K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun r => aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) K]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              exact aux_mainBumpOneLongTwo_pairEnergy_odd phi0 phi1 f a r
    have hodd :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) ≤
          ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n) := by
      rw [hoddEq]
      exact aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le hn b hb phi0 phi1 hpair f K
        (2 * K) (by omega)
    calc
      (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) +
          ∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) ≤
          (ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n)) +
          (ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n)) := add_le_add heven hodd
      _ = ENNReal.ofReal (C_mainBumpOneLongTwo n) *
          ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n) := by
            rw [C_mainBumpOneLongTwo, ENNReal.ofReal_mul (by norm_num)]
            norm_num
            ring
  · rw [aux_mainBumpOneLongTwo_sum_range_two_mul_add_one]
    have hevenEq :
        (∑ r ∈ Finset.range (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) =
          ∑ r : Fin (K + 1),
            eLpNorm
              (fun x ↦ twistedAverageAtScale (a (2 * (r : ℤ))) (fun u ↦ phi0 u)
                    (fun i y ↦ f.1 i y) x -
                  twistedAverageAtScale (a (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
                    (fun i y ↦ f.1 i y) x)
              2 volume ^ 2 := by
      calc
        (∑ r ∈ Finset.range (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) =
            ∑ r : Fin (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun r => aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) (K + 1)]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              exact aux_mainBumpOneLongTwo_pairEnergy_even phi0 phi1 f a r
    have heven :
        (∑ r ∈ Finset.range (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) ≤
          ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n) := by
      rw [hevenEq]
      exact aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le hn a ha phi0 phi1 hpair f (K + 1)
        (2 * K + 1) (by omega)
    let b : ℤ → ℝ := fun z => a (z + 1)
    have hb : SpacedSequence b := by
      dsimp [b]
      exact shift_mem_A ha 1
    have hoddEq :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) =
          ∑ r : Fin K,
            eLpNorm
              (fun x ↦ twistedAverageAtScale (b (2 * (r : ℤ))) (fun u ↦ phi0 u)
                    (fun i y ↦ f.1 i y) x -
                  twistedAverageAtScale (b (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
                    (fun i y ↦ f.1 i y) x)
              2 volume ^ 2 := by
      calc
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) =
            ∑ r : Fin K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun r => aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) K]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              exact aux_mainBumpOneLongTwo_pairEnergy_odd phi0 phi1 f a r
    have hodd :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) ≤
          ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n) := by
      rw [hoddEq]
      exact aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le hn b hb phi0 phi1 hpair f K
        (2 * K + 1) (by omega)
    calc
      (∑ r ∈ Finset.range (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) +
          ∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) ≤
          (ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n)) +
          (ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n)) := add_le_add heven hodd
      _ = ENNReal.ofReal (C_mainBumpOneLongTwo n) *
          ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n) := by
            rw [C_mainBumpOneLongTwo, ENNReal.ofReal_mul (by norm_num)]
            norm_num
            ring

/-- The numerical estimate in Lemma \ref{constant main bump one long two}. -/
theorem constantMainBumpOneLongTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLongTwo n < (8 / 9 : ℝ) * (2 : ℝ) ^ 543 := by
  unfold C_mainBumpOneLongTwo
  calc
    2 * C_inductPositiveTermsReductionNonWhitneySkip n <
        2 * ((8 / 9 : ℝ) * (2 : ℝ) ^ 542) :=
      mul_lt_mul_of_pos_left (constantNonWhitneySkipReduction hn) (by norm_num)
    _ = (8 / 9 : ℝ) * (2 : ℝ) ^ 543 := by
      calc
        2 * ((8 / 9 : ℝ) * (2 : ℝ) ^ 542) =
            (8 / 9 : ℝ) * ((2 : ℝ) ^ 1 * (2 : ℝ) ^ 542) := by ring
        _ = (8 / 9 : ℝ) * (2 : ℝ) ^ (1 + 542) := by rw [← pow_add]
        _ = (8 / 9 : ℝ) * (2 : ℝ) ^ 543 := by norm_num

/-- The constant in Lemma \ref{lem:mainbump1_long}. -/
noncomputable def C_mainBumpOneLong (n : ℕ) : ℝ :=
  2 * (C_mainBumpOneLongOne n + C_mainBumpOneLongTwo n)

private theorem aux_mainBumpOneLong_average_aestronglyMeasurable {n : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (t : ℝ) :
    AEStronglyMeasurable
      (twistedAverageAtScale t (fun s ↦ phi s) (fun i x ↦ f i x)) volume := by
  let E := EuclideanSpace ℝ (Fin n)
  let K : E × ℝ → ℝ := fun z ↦
    t⁻¹ * phi (t⁻¹ * z.2) * ∏ i,
      f i (z.1 + z.2 • WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  have hKcont : Continuous K := by
    dsimp [K]
    fun_prop
  have hKmeas : AEStronglyMeasurable K ((volume : Measure E).prod volume) :=
    hKcont.aestronglyMeasurable
  have hI : AEStronglyMeasurable (fun x : E ↦ ∫ s : ℝ, K (x, s)) volume := by
    simpa only [Measure.volume_eq_prod] using hKmeas.integral_prod_right'
  apply hI.congr
  filter_upwards [] with x
  rfl

private theorem aux_mainBumpOneLong_ennreal_add_sq_le (u v : ℝ≥0∞) :
    (u + v) ^ (2 : ℝ) ≤ 2 * (u ^ (2 : ℝ) + v ^ (2 : ℝ)) := by
  simp only [ENNReal.rpow_two]
  by_cases hu : u = ∞
  · simp [hu]
  by_cases hv : v = ∞
  · simp [hv]
  have hu2 : u ^ (2 : ℕ) ≠ ∞ := ENNReal.pow_ne_top hu
  have hv2 : v ^ (2 : ℕ) ≠ ∞ := ENNReal.pow_ne_top hv
  have hsum : u ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hu2, hv2⟩
  have hrhs : 2 * (u ^ (2 : ℕ) + v ^ (2 : ℕ)) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hsum
  rw [← ENNReal.toReal_le_toReal (by simp [hu, hv]) hrhs,
    ENNReal.toReal_pow, ENNReal.toReal_add hu hv,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add hu2 hv2, ENNReal.toReal_pow,
    ENNReal.toReal_pow]
  nlinarith [sq_nonneg (u.toReal - v.toReal)]

private theorem aux_mainBumpOneLong_one_nonneg (n : ℕ) :
    0 ≤ C_mainBumpOneLongOne n := by
  unfold C_mainBumpOneLongOne
  exact mul_nonneg (sq_nonneg _) (aux_C_mainAuxOne_nonneg n)

private theorem aux_mainBumpOneLong_two_nonneg (n : ℕ) :
    0 ≤ C_mainBumpOneLongTwo n := by
  have hdiagonal : 0 ≤ C_diagonalBandReduction := by
    unfold C_diagonalBandReduction
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) aux_CincreaseDataReduction_nonneg)
  have hnonWhitney : 0 ≤ C_inductPositiveTermsReductionNonWhitney := by
    unfold C_inductPositiveTermsReductionNonWhitney
    apply add_nonneg
    · norm_num [C_oneScaleEstimateWindow, C_uniPair]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (by positivity)) hdiagonal
  have hskip : 0 ≤ C_inductPositiveTermsReductionNonWhitneySkip n := by
    unfold C_inductPositiveTermsReductionNonWhitneySkip
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hnonWhitney
  unfold C_mainBumpOneLongTwo
  exact mul_nonneg (by norm_num) hskip

private theorem aux_mainBumpOneLong_shifted_dyadic_chain {J : ℕ}
    (k : aux_dyadicChain J) :
    ∃ q : aux_dyadicChain J, ∀ j : Fin J, q.1 j.castSucc = k.1 j.succ := by
  let qfun : Fin (J + 1) → ℤ :=
    Fin.lastCases (k.1 (Fin.last J) + 1) (fun j : Fin J ↦ k.1 j.succ)
  have hqfun : StrictMono qfun := by
    intro i j hij
    by_cases hj : j = Fin.last J
    · subst j
      change i.1 < J at hij
      let i' : Fin J := ⟨i.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      rw [hi]
      simp only [qfun, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hle : k.1 i'.succ ≤ k.1 (Fin.last J) :=
        k.2.monotone (Fin.le_last i'.succ)
      omega
    · have hjlt : j < Fin.last J := Fin.lt_last_iff_ne_last.mpr hj
      change i.1 < j.1 at hij
      change j.1 < J at hjlt
      let i' : Fin J := ⟨i.1, by omega⟩
      let j' : Fin J := ⟨j.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      have hj' : j = j'.castSucc := by rfl
      rw [hi, hj']
      simp only [qfun, Fin.lastCases_castSucc]
      apply k.2
      exact Fin.succ_lt_succ_iff.mpr (by simpa [i', j'] using hij)
  refine ⟨⟨qfun, hqfun⟩, ?_⟩
  intro j
  simp [qfun]

/-- Lemma \ref{lem:mainbump1_long}. -/
theorem mainBumpOneLong {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) :
    aux_dyadicVariationBound (C_mainBumpOneLong n) (fun x ↦ phi0 x) f.1 := by
  unfold aux_dyadicVariationBound aux_dyadicJumpEnergy twistedDyadicJumpEnergy
  intro J hJ k
  let P : ℝ≥0∞ := ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  let a : Fin J → ℝ≥0∞ := fun j ↦
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume
  let b : Fin J → ℝ≥0∞ := fun j ↦
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume
  let d : Fin J → ℝ≥0∞ := fun j ↦
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x)
      2 volume
  have htri (j : Fin J) : d j ≤ a j + b j := by
    dsimp [a, b, d]
    calc
      eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi0 u)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
                (fun i y ↦ f.1 i y) x)
          2 volume =
          eLpNorm
            ((fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi0 u)
                  (fun i y ↦ f.1 i y) x -
                twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
                  (fun i y ↦ f.1 i y) x) -
              (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
                  (fun i y ↦ f.1 i y) x -
                twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
                  (fun i y ↦ f.1 i y) x))
            2 volume := by
              congr 1
              funext x
              simp only [Pi.sub_apply]
              ring
      _ ≤ _ := eLpNorm_sub_le
        ((aux_mainBumpOneLong_average_aestronglyMeasurable phi0 f.1
          ((2 : ℝ) ^ (k.1 j.succ))).sub
          (aux_mainBumpOneLong_average_aestronglyMeasurable phi1 f.1
            ((2 : ℝ) ^ (k.1 j.succ))))
        ((aux_mainBumpOneLong_average_aestronglyMeasurable phi0 f.1
          ((2 : ℝ) ^ (k.1 j.castSucc))).sub
          (aux_mainBumpOneLong_average_aestronglyMeasurable phi1 f.1
            ((2 : ℝ) ^ (k.1 j.succ))))
        (by norm_num)
  have hpoint (j : Fin J) : d j ^ 2 ≤
      2 * (a j ^ 2 + b j ^ 2) := by
    calc
      d j ^ 2 ≤ (a j + b j) ^ 2 :=
        pow_le_pow_left₀ bot_le (htri j) 2
      _ ≤ 2 * (a j ^ 2 + b j ^ 2) := by
        simpa [ENNReal.rpow_two] using aux_mainBumpOneLong_ennreal_add_sq_le (a j) (b j)
  have hsum : (∑ j : Fin J, d j ^ 2) ≤
      2 * (∑ j : Fin J, a j ^ 2) +
        2 * (∑ j : Fin J, b j ^ 2) := by
    calc
      (∑ j : Fin J, d j ^ 2) ≤
          ∑ j : Fin J, 2 * (a j ^ 2 + b j ^ 2) := by
            exact Finset.sum_le_sum fun j _ ↦ hpoint j
      _ = 2 * (∑ j : Fin J, a j ^ 2) +
          2 * (∑ j : Fin J, b j ^ 2) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  obtain ⟨q, hq⟩ := aux_mainBumpOneLong_shifted_dyadic_chain k
  have hOne : (∑ j : Fin J, a j ^ 2) ≤
      ENNReal.ofReal (C_mainBumpOneLongOne n) * P := by
    dsimp [a, P]
    simpa [hq] using mainBumpOneLongOne hn phi0 phi1 hpair f J hJ q
  have hTwo : (∑ j : Fin J, b j ^ 2) ≤
      ENNReal.ofReal (C_mainBumpOneLongTwo n) * P := by
    dsimp [b, P]
    simpa using mainBumpOneLongTwo hn phi0 phi1 hpair f J hJ k
  have hC1 : 0 ≤ C_mainBumpOneLongOne n := aux_mainBumpOneLong_one_nonneg n
  have hC2 : 0 ≤ C_mainBumpOneLongTwo n := aux_mainBumpOneLong_two_nonneg n
  change (∑ j : Fin J, d j ^ 2) ≤
    ENNReal.ofReal (C_mainBumpOneLong n) * P
  calc
    (∑ j : Fin J, d j ^ 2) ≤
        2 * (∑ j : Fin J, a j ^ 2) +
          2 * (∑ j : Fin J, b j ^ 2) := hsum
    _ ≤ 2 * (ENNReal.ofReal (C_mainBumpOneLongOne n) * P) +
          2 * (ENNReal.ofReal (C_mainBumpOneLongTwo n) * P) := by
            gcongr
    _ = (2 * ENNReal.ofReal (C_mainBumpOneLongOne n) +
          2 * ENNReal.ofReal (C_mainBumpOneLongTwo n)) * P := by ring
    _ = ENNReal.ofReal (C_mainBumpOneLong n) * P := by
      unfold C_mainBumpOneLong
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ENNReal.ofReal_add]
      · norm_num
        ring
      · exact hC1
      · exact hC2

private theorem aux_mainBumpOneLong_one_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLongOne n < (1397 / 2048 : ℝ) * (2 : ℝ) ^ 605 := by
  unfold C_mainBumpOneLongOne
  calc
    (2 * C_uniPair) ^ 2 * C_mainAuxOne n <
        (2 * C_uniPair) ^ 2 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) :=
      mul_lt_mul_of_pos_left (aux_constantMainAuxOne_sharp hn)
        (by norm_num [C_uniPair])
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 605 := by
      calc
        (2 * C_uniPair) ^ 2 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) =
            (2 : ℝ) ^ 32 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) := by
              norm_num [C_uniPair]
        _ = (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 32 * (2 : ℝ) ^ 573) := by ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 605 := by
          rw [← pow_add]

/-- The numerical estimate in Lemma \ref{constant main bump one long}. -/
theorem constantMainBumpOneLong {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLong n < (11 / 16 : ℝ) * (2 : ℝ) ^ 606 := by
  have h1 := aux_mainBumpOneLong_one_sharp hn
  have h2 := constantMainBumpOneLongTwo hn
  have h605 : (2 : ℝ) ^ 605 = (2 : ℝ) ^ 62 * (2 : ℝ) ^ 543 := by
    rw [← pow_add]
  have h606 : (2 : ℝ) ^ 606 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 543 := by
    rw [← pow_add]
  have h63 : (2 : ℝ) ^ 63 = 2 * (2 : ℝ) ^ 62 := by
    rw [show 63 = 1 + 62 by norm_num, pow_add]
    norm_num
  have hcore : (1397 / 2048 : ℝ) * (2 : ℝ) ^ 63 + 16 / 9 <
      (11 / 16 : ℝ) * (2 : ℝ) ^ 63 := by
    set_option exponentiation.threshold 1000 in
      norm_num
  unfold C_mainBumpOneLong
  calc
    2 * (C_mainBumpOneLongOne n + C_mainBumpOneLongTwo n) <
        2 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 605 +
          (8 / 9 : ℝ) * (2 : ℝ) ^ 543) :=
      mul_lt_mul_of_pos_left (add_lt_add h1 h2) (by norm_num)
    _ = ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 63 + 16 / 9) * (2 : ℝ) ^ 543 := by
      rw [h605, h63]
      ring
    _ < ((11 / 16 : ℝ) * (2 : ℝ) ^ 63) * (2 : ℝ) ^ 543 :=
      mul_lt_mul_of_pos_right hcore (by positivity)
    _ = (11 / 16 : ℝ) * (2 : ℝ) ^ 606 := by
      rw [h606]
      ring

/-- The constant in Lemma \ref{lem:mainbump1}. -/
noncomputable def C_mainBumpOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 4 * (3 * C_uniPair) ^ 2 * C_mainAuxOne n +
    2 * C_mainBumpOneLong n

/-! Private Fourier and scalar-normalization infrastructure for `mainBumpOne`. -/

private theorem aux_mainBumpOne_T_cast_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (fun x : ℝ ↦ (Codex.Reduction.SmoothingDecomposition.aux_T f x : ℂ)) =
      Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ (f x : ℂ)) := by
  funext x
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => y * f y) x := by
    exact ((contDiff_id.mul hf).contDiffAt).differentiableAt (by norm_num)
  have hcast :
      deriv (fun y : ℝ => ((y * f y : ℝ) : ℂ)) x =
        ((deriv (fun y : ℝ => y * f y) x : ℝ) : ℂ) := by
    simpa using ((hasDerivAt_const x Complex.ofRealCLM).clm_apply hdiff.hasDerivAt).deriv
  have hfun : (fun y : ℝ => ((y * f y : ℝ) : ℂ)) =
      Codex.Reduction.BumpFunctions.multiplicationOperatorX
        (fun y : ℝ => (f y : ℂ)) := by
    funext y
    simp [Codex.Reduction.BumpFunctions.multiplicationOperatorX]
  unfold Codex.Reduction.SmoothingDecomposition.aux_T
    Codex.Reduction.BumpFunctions.aux_T
  rw [← hfun, hcast]

private theorem aux_mainBumpOne_T_fourier_formula (phi : SchwartzMap ℝ ℝ)
    (m : ℕ) (xi : ℝ) :
    iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ))) xi =
      - ((m : ℂ) * iteratedDeriv m
            (FourierTransform.fourier (fun x : ℝ ↦ (phi x : ℂ))) xi +
          (xi : ℂ) * iteratedDeriv (m + 1)
            (FourierTransform.fourier (fun x : ℝ ↦ (phi x : ℂ))) xi) := by
  let phiC : SchwartzMap ℝ ℂ :=
    phi.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hphiC : (phiC : ℝ → ℂ) = fun x : ℝ => (phi x : ℂ) := by
    funext x
    simp [phiC, SchwartzMap.postcompCLM_apply]
  have hsmooth : ContDiff ℝ 1 (fun x : ℝ => phi x) := by
    exact phi.smooth 1
  rw [aux_mainBumpOne_T_cast_eq _ hsmooth, ← hphiC]
  simpa using Codex.Reduction.BumpFunctions.fourierDerivativeMul phiC m xi

private theorem aux_mainBumpOne_deriv_eq_zero_of_eq_one_on_Icc
    (F : ℝ → ℂ) (x : ℝ) (hx : |x| < 1 / 2)
    (hF : ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), F y = 1) :
    deriv F x = 0 := by
  have hxIoo : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [mem_Ioo]
    rw [abs_lt] at hx
    exact hx
  have hnhds : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ nhds x :=
    IsOpen.mem_nhds isOpen_Ioo hxIoo
  have heq : F =ᶠ[nhds x] (fun _ : ℝ => (1 : ℂ)) := by
    filter_upwards [hnhds] with y hy
    exact hF y (Set.Ioo_subset_Icc_self hy)
  calc
    deriv F x = deriv (fun _ : ℝ => (1 : ℂ)) x := Filter.EventuallyEq.deriv_eq heq
    _ = 0 := deriv_const _ _

private theorem aux_mainBumpOne_T_fourier_support_window (phi : SchwartzMap ℝ ℝ)
    (hwin : cnWindow C_uniPair N_uniPair phi) :
    Function.support
      (FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ))) ⊆
      Codex.Reduction.BumpFunctions.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
  intro xi hxi
  have hne : FourierTransform.fourier
      (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ)) xi ≠ 0 :=
    Function.mem_support.mp hxi
  rw [Codex.Reduction.BumpFunctions.aux_annulusOne]
  constructor
  · by_contra hnot
    push_neg at hnot
    have hsmall : |xi| < 1 / 2 := by
      norm_num at hnot
      linarith
    have hderiv : deriv
        (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi = 0 := by
      apply aux_mainBumpOne_deriv_eq_zero_of_eq_one_on_Icc _ xi hsmall
      intro y hy
      exact hwin.2.2.2.1 y hy
    have hformula := aux_mainBumpOne_T_fourier_formula phi 0 xi
    apply hne
    simpa [iteratedDeriv_zero, hderiv] using hformula
  · by_contra hnot
    push_neg at hnot
    have hlarge : 4 < |xi| := by norm_num at hnot ⊢; exact hnot
    have hout : xi ∉ Set.Icc (-1 : ℝ) 1 := by
      intro hmem
      have habs : |xi| ≤ 1 := abs_le.mpr hmem
      linarith
    have hderivSupp : Function.support
        (iteratedDeriv 1 (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ)))) ⊆
        Set.Icc (-1 : ℝ) 1 := by
      have htsupp : tsupport
          (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) ⊆ Set.Icc (-1 : ℝ) 1 :=
        closure_minimal hwin.2.2.1 isClosed_Icc
      exact (subset_tsupport _).trans
        ((Codex.Preliminaries.BumpsAndEstimates.aux_tsupport_iteratedDeriv_subset _ 1).trans
          htsupp)
    have hderiv' : iteratedDeriv 1
        (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi = 0 := by
      apply Function.notMem_support.mp
      intro hsupp
      exact hout (hderivSupp hsupp)
    have hderiv : deriv
        (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi = 0 := by
      simpa only [iteratedDeriv_one] using hderiv'
    have hformula := aux_mainBumpOne_T_fourier_formula phi 0 xi
    apply hne
    simpa [iteratedDeriv_zero, hderiv] using hformula

private theorem aux_mainBumpOne_T_const_mul (c : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) :
    Codex.Reduction.SmoothingDecomposition.aux_T (fun x ↦ c * f x) =
      fun x ↦ c * Codex.Reduction.SmoothingDecomposition.aux_T f x := by
  funext x
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => y * f y) x := by
    exact ((contDiff_id.mul hf).contDiffAt).differentiableAt (by norm_num)
  unfold Codex.Reduction.SmoothingDecomposition.aux_T
  rw [show (fun y : ℝ => y * (c * f y)) = fun y => c * (y * f y) by
      funext y
      ring]
  rw [deriv_const_mul c hdiff]

private theorem aux_mainBumpOne_window_profile_deriv_zero_outside
    (phi : SchwartzMap ℝ ℝ) (hwin : cnWindow C_uniPair N_uniPair phi)
    (m : ℕ) (xi : ℝ) (hxi : xi ∉ Set.Icc (-1 : ℝ) 1) :
    iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi = 0 := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))
  have hFtsupp : tsupport F ⊆ Set.Icc (-1 : ℝ) 1 :=
    closure_minimal (by simpa [F] using hwin.2.2.1) isClosed_Icc
  have hderivSupp : Function.support (iteratedDeriv m F) ⊆ Set.Icc (-1 : ℝ) 1 :=
    (subset_tsupport _).trans
      ((Codex.Preliminaries.BumpsAndEstimates.aux_tsupport_iteratedDeriv_subset F m).trans
        hFtsupp)
  change iteratedDeriv m F xi = 0
  apply Function.notMem_support.mp
  intro hsupp
  exact hxi (hderivSupp hsupp)

private theorem aux_mainBumpOne_T_fourier_deriv_bound_window
    (phi : SchwartzMap ℝ ℝ) (hwin : cnWindow C_uniPair N_uniPair phi)
    (m : ℕ) (hm : m < 3) (xi : ℝ) :
    ‖iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ))) xi‖ ≤
      3 * C_uniPair := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))
  have hmle : m ≤ 2 := by omega
  have hmN : m ≤ N_uniPair := by simpa [N_uniPair] using Nat.le_of_lt hm
  have hm1N : m + 1 ≤ N_uniPair := by
    simpa [N_uniPair] using Nat.succ_le_of_lt hm
  have h0 : ‖iteratedDeriv m F xi‖ ≤ C_uniPair :=
    aux_mainBumpOneLongOne_window_profile_deriv_bound C_uniPair N_uniPair phi hwin m hmN xi
  have h1 : ‖iteratedDeriv (m + 1) F xi‖ ≤ C_uniPair :=
    aux_mainBumpOneLongOne_window_profile_deriv_bound C_uniPair N_uniPair phi hwin
      (m + 1) hm1N xi
  rw [aux_mainBumpOne_T_fourier_formula phi m xi]
  rw [norm_neg]
  change ‖(m : ℂ) * iteratedDeriv m F xi +
      (xi : ℂ) * iteratedDeriv (m + 1) F xi‖ ≤ 3 * C_uniPair
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have habs : |xi| ≤ 1 := abs_le.mpr hxi
    calc
      ‖(m : ℂ) * iteratedDeriv m F xi +
          (xi : ℂ) * iteratedDeriv (m + 1) F xi‖ ≤
          ‖(m : ℂ) * iteratedDeriv m F xi‖ +
            ‖(xi : ℂ) * iteratedDeriv (m + 1) F xi‖ := norm_add_le _ _
      _ = (m : ℝ) * ‖iteratedDeriv m F xi‖ +
          |xi| * ‖iteratedDeriv (m + 1) F xi‖ := by
            rw [norm_mul, norm_mul, norm_natCast, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (m : ℝ) * C_uniPair + 1 * C_uniPair := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left h0 (by positivity)
            · calc
                |xi| * ‖iteratedDeriv (m + 1) F xi‖ ≤
                    1 * ‖iteratedDeriv (m + 1) F xi‖ := by gcongr
                _ ≤ 1 * C_uniPair := by gcongr
      _ ≤ 3 * C_uniPair := by
            have hC : 0 ≤ C_uniPair := by norm_num [C_uniPair]
            have hmreal : (m : ℝ) ≤ 2 := by exact_mod_cast hmle
            nlinarith
  · have hz0 : iteratedDeriv m F xi = 0 :=
      aux_mainBumpOne_window_profile_deriv_zero_outside phi hwin m xi hxi
    have hz1 : iteratedDeriv (m + 1) F xi = 0 :=
      aux_mainBumpOne_window_profile_deriv_zero_outside phi hwin (m + 1) xi hxi
    simpa [hz0, hz1] using
      (show (0 : ℝ) ≤ 3 * C_uniPair by norm_num [C_uniPair])

private noncomputable def aux_mainBumpOne_psi
    (phi : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  (3 * C_uniPair)⁻¹ • phi

private theorem aux_mainBumpOne_psi_apply (phi : SchwartzMap ℝ ℝ) (x : ℝ) :
    aux_mainBumpOne_psi phi x = (3 * C_uniPair)⁻¹ * phi x := by
  simp [aux_mainBumpOne_psi, smul_apply]

private theorem aux_mainBumpOne_psi_T_fourier (phi : SchwartzMap ℝ ℝ)
    (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦
      (Codex.Reduction.SmoothingDecomposition.aux_T
        (fun y ↦ aux_mainBumpOne_psi phi y) x : ℂ)) xi =
      (((3 * C_uniPair)⁻¹ : ℝ) : ℂ) *
        FourierTransform.fourier (fun x : ℝ ↦
          (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ)) xi := by
  have hsmooth : ContDiff ℝ 1 (fun x : ℝ => phi x) := phi.smooth 1
  have hT := aux_mainBumpOne_T_const_mul (3 * C_uniPair)⁻¹ (fun x : ℝ => phi x)
    hsmooth
  rw [show (fun y : ℝ => aux_mainBumpOne_psi phi y) =
      fun y => (3 * C_uniPair)⁻¹ * phi y by
        funext y
        exact aux_mainBumpOne_psi_apply phi y,
    hT, aux_mainAuxOne_fourier_real_const_mul]

private theorem aux_mainBumpOne_psi_T_hypotheses (phi : SchwartzMap ℝ ℝ)
    (hwin : cnWindow C_uniPair N_uniPair phi) :
    aux_mainAuxiliaryFourierHypotheses
      (Codex.Reduction.SmoothingDecomposition.aux_T
        (fun x ↦ aux_mainBumpOne_psi phi x)) := by
  let c : ℝ := 3 * C_uniPair
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  constructor
  · intro xi hxi
    have hne := Function.mem_support.mp hxi
    rw [aux_mainBumpOne_psi_T_fourier] at hne
    have hrawne : FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ)) xi ≠ 0 :=
      (mul_ne_zero_iff.mp hne).2
    exact aux_mainBumpOne_T_fourier_support_window phi hwin
      (Function.mem_support.mpr hrawne)
  · intro m hm xi
    change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T
          (fun y ↦ aux_mainBumpOne_psi phi y) x : ℂ)) z) xi‖ ≤ 1
    have hformula :
        (fun z : ℝ => FourierTransform.fourier (fun x : ℝ ↦
          (Codex.Reduction.SmoothingDecomposition.aux_T
            (fun y ↦ aux_mainBumpOne_psi phi y) x : ℂ)) z) =
          fun z => (((3 * C_uniPair)⁻¹ : ℝ) : ℂ) *
            FourierTransform.fourier (fun x : ℝ ↦
              (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ)) z := by
      funext z
      exact aux_mainBumpOne_psi_T_fourier phi z
    rw [hformula, iteratedDeriv_const_mul_field]
    have hraw := aux_mainBumpOne_T_fourier_deriv_bound_window phi hwin m hm xi
    change ‖(((3 * C_uniPair)⁻¹ : ℝ) : ℂ) * iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ))) xi‖ ≤ 1
    calc
      ‖(((3 * C_uniPair)⁻¹ : ℝ) : ℂ) * iteratedDeriv m
          (FourierTransform.fourier (fun x : ℝ ↦
            (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ))) xi‖ =
          (3 * C_uniPair)⁻¹ * ‖iteratedDeriv m
            (FourierTransform.fourier (fun x : ℝ ↦
              (Codex.Reduction.SmoothingDecomposition.aux_T (fun y ↦ phi y) x : ℂ))) xi‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      _ ≤ (3 * C_uniPair)⁻¹ * (3 * C_uniPair) := by
            exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
      _ = 1 := by norm_num [C_uniPair]

private theorem aux_mainBumpOne_jumpEnergy_const_mul {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (J : ℕ) (t : aux_scaleChain J) :
    aux_jumpEnergy (fun x => c * chi x) f J t =
      ENNReal.ofReal (c ^ 2) * aux_jumpEnergy chi f J t := by
  unfold aux_jumpEnergy twistedJumpEnergy
  calc
    (∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale (t.1 j.succ) (fun u => c * chi u)
              (fun i y ↦ f i y) x -
            twistedAverageAtScale (t.1 j.castSucc) (fun u => c * chi u)
              (fun i y ↦ f i y) x)
        2 volume ^ 2) =
      ∑ j : Fin J, ENNReal.ofReal (c ^ 2) *
        eLpNorm
          (fun x ↦ twistedAverageAtScale (t.1 j.succ) chi
                (fun i y ↦ f i y) x -
              twistedAverageAtScale (t.1 j.castSucc) chi
                (fun i y ↦ f i y) x)
          2 volume ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hpoint :
            (fun x ↦ twistedAverageAtScale (t.1 j.succ) (fun u => c * chi u)
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale (t.1 j.castSucc) (fun u => c * chi u)
                  (fun i y ↦ f i y) x) =
              fun x ↦ c * (twistedAverageAtScale (t.1 j.succ) chi
                    (fun i y ↦ f i y) x -
                  twistedAverageAtScale (t.1 j.castSucc) chi
                    (fun i y ↦ f i y) x) := by
              funext x
              rw [aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul,
                aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul]
              ring
        rw [hpoint]
        exact aux_mainBumpOneLongOne_eLpNorm_sq_const_mul c hc _ volume
    _ = ENNReal.ofReal (c ^ 2) *
        (∑ j : Fin J,
          eLpNorm
            (fun x ↦ twistedAverageAtScale (t.1 j.succ) chi
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale (t.1 j.castSucc) chi
                  (fun i y ↦ f i y) x)
            2 volume ^ 2) := by
          rw [Finset.mul_sum]

private theorem aux_mainBumpOne_dyadicJumpEnergy_const_mul {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (J : ℕ) (k : aux_dyadicChain J) :
    aux_dyadicJumpEnergy (fun x => c * chi x) f J k =
      ENNReal.ofReal (c ^ 2) * aux_dyadicJumpEnergy chi f J k := by
  unfold aux_dyadicJumpEnergy twistedDyadicJumpEnergy
  calc
    (∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u => c * chi u)
              (fun i y ↦ f i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u => c * chi u)
              (fun i y ↦ f i y) x)
        2 volume ^ 2) =
      ∑ j : Fin J, ENNReal.ofReal (c ^ 2) *
        eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) chi
                (fun i y ↦ f i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) chi
                (fun i y ↦ f i y) x)
          2 volume ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hpoint :
            (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u => c * chi u)
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u => c * chi u)
                  (fun i y ↦ f i y) x) =
              fun x ↦ c * (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) chi
                    (fun i y ↦ f i y) x -
                  twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) chi
                    (fun i y ↦ f i y) x) := by
              funext x
              rw [aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul,
                aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul]
              ring
        rw [hpoint]
        exact aux_mainBumpOneLongOne_eLpNorm_sq_const_mul c hc _ volume
    _ = ENNReal.ofReal (c ^ 2) *
        (∑ j : Fin J,
          eLpNorm
            (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) chi
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) chi
                  (fun i y ↦ f i y) x)
            2 volume ^ 2) := by
          rw [Finset.mul_sum]

private theorem aux_mainBumpOne_variationBound_const_mul {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (A : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hA : aux_variationBound A chi f) :
    aux_variationBound (c ^ 2 * A) (fun x => c * chi x) f := by
  intro J hJ t
  calc
    aux_jumpEnergy (fun x => c * chi x) f J t =
        ENNReal.ofReal (c ^ 2) * aux_jumpEnergy chi f J t :=
      aux_mainBumpOne_jumpEnergy_const_mul c hc chi f J t
    _ ≤ ENNReal.ofReal (c ^ 2) *
        (ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :=
      mul_le_mul_of_nonneg_left (hA J hJ t) bot_le
    _ = ENNReal.ofReal (c ^ 2 * A) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [ENNReal.ofReal_mul (sq_nonneg c)]
      ring

private theorem aux_mainBumpOne_dyadicVariationBound_const_mul {n : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (A : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hA : aux_dyadicVariationBound A chi f) :
    aux_dyadicVariationBound (c ^ 2 * A) (fun x => c * chi x) f := by
  intro J hJ k
  calc
    aux_dyadicJumpEnergy (fun x => c * chi x) f J k =
        ENNReal.ofReal (c ^ 2) * aux_dyadicJumpEnergy chi f J k :=
      aux_mainBumpOne_dyadicJumpEnergy_const_mul c hc chi f J k
    _ ≤ ENNReal.ofReal (c ^ 2) *
        (ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :=
      mul_le_mul_of_nonneg_left (hA J hJ k) bot_le
    _ = ENNReal.ofReal (c ^ 2 * A) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [ENNReal.ofReal_mul (sq_nonneg c)]
      ring

private theorem aux_mainBumpOne_C_mainAuxOne_pos (n : ℕ) : 0 < C_mainAuxOne n := by
  have hdiagonal : 0 ≤ C_diagonalBandReduction := by
    unfold C_diagonalBandReduction
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) aux_CincreaseDataReduction_nonneg)
  have hnonWhitney : 0 < C_inductPositiveTermsReductionNonWhitney := by
    unfold C_inductPositiveTermsReductionNonWhitney
    apply add_pos_of_pos_of_nonneg
    · norm_num [C_oneScaleEstimateWindow, C_uniPair]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (by positivity)) hdiagonal
  have hskip : 0 < C_inductPositiveTermsReductionNonWhitneySkip n := by
    unfold C_inductPositiveTermsReductionNonWhitneySkip
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hnonWhitney
  have hgap : 0 < C_inductPositiveTermsReductionWhitneyGap n := by
    unfold C_inductPositiveTermsReductionWhitneyGap
    apply add_pos_of_pos_of_nonneg
    · exact mul_pos (by norm_num) hskip
    · exact mul_nonneg (mul_nonneg (by positivity) (add_nonneg (sq_nonneg _)
        (sq_nonneg _))) hdiagonal
  have hWhitney : 0 < C_inductPositiveTermsReductionWhitney n := by
    unfold C_inductPositiveTermsReductionWhitney
    exact mul_pos (by norm_num) hgap
  have hproduct : 0 < C_inductPositiveTermsReductionWhitneyProduct n := by
    unfold C_inductPositiveTermsReductionWhitneyProduct
    exact mul_pos (by positivity) hWhitney
  unfold C_mainAuxOne
  exact mul_pos (by positivity) hproduct

private theorem aux_mainBumpOne_C_long_pos (n : ℕ) :
    0 < C_mainBumpOneLong n := by
  have hOne : 0 < C_mainBumpOneLongOne n := by
    unfold C_mainBumpOneLongOne
    exact mul_pos (sq_pos_of_pos (by norm_num [C_uniPair]))
      (aux_mainBumpOne_C_mainAuxOne_pos n)
  unfold C_mainBumpOneLong
  exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hOne
    (aux_mainBumpOneLong_two_nonneg n))

/-- Lemma \ref{lem:mainbump1}. -/
theorem mainBumpOne {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) :
    aux_variationBound (C_mainBumpOne n) (fun x ↦ phi0 x) f.1 := by
  let c : ℝ := 3 * C_uniPair
  let psi : SchwartzMap ℝ ℝ := c⁻¹ • phi0
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  have hpsi_eq : psi = aux_mainBumpOne_psi phi0 := by
    rfl
  have hTpsi : aux_mainAuxiliaryFourierHypotheses
      (Codex.Reduction.SmoothingDecomposition.aux_T (fun x ↦ psi x)) := by
    rw [hpsi_eq]
    exact aux_mainBumpOne_psi_T_hypotheses phi0 hpair.1
  have hTpsiBump : aux_mainAuxiliaryFourierHypotheses
      (Codex.Reduction.BumpFunctions.aux_T (fun x ↦ psi x)) := by
    have hreal : Codex.Reduction.BumpFunctions.aux_T (fun x ↦ psi x) =
        Codex.Reduction.SmoothingDecomposition.aux_T (fun x ↦ psi x) := by
      funext x
      unfold Codex.Reduction.BumpFunctions.aux_T
        Codex.Reduction.SmoothingDecomposition.aux_T
      rfl
    rw [hreal]
    exact hTpsi
  have hlong : aux_dyadicVariationBound (C_mainBumpOneLong n)
      (fun x ↦ phi0 x) f.1 :=
    mainBumpOneLong hn phi0 phi1 hpair f
  have hdyadic : aux_dyadicVariationBound
      ((c⁻¹) ^ 2 * C_mainBumpOneLong n) (fun x ↦ psi x) f.1 := by
    have h := aux_mainBumpOne_dyadicVariationBound_const_mul c⁻¹
      (inv_nonneg.mpr hc.le) (C_mainBumpOneLong n) (fun x ↦ phi0 x) f.1 hlong
    simpa [psi, smul_apply] using h
  have hApos : 0 < (c⁻¹) ^ 2 * C_mainBumpOneLong n := by
    exact mul_pos (sq_pos_of_pos (inv_pos.mpr hc)) (aux_mainBumpOne_C_long_pos n)
  have hshort : aux_variationBound
      (16 * C_mainAuxOne n + 2 * ((c⁻¹) ^ 2 * C_mainBumpOneLong n))
      (fun x ↦ psi x) f.1 :=
    shortLongFtcReduction hn psi hTpsiBump f 1 (by norm_num)
      ((c⁻¹) ^ 2 * C_mainBumpOneLong n) hApos hdyadic
  have hrescaled := aux_mainBumpOne_variationBound_const_mul c hc.le
    (16 * C_mainAuxOne n + 2 * ((c⁻¹) ^ 2 * C_mainBumpOneLong n))
    (fun x ↦ psi x) f.1 hshort
  have hC : c ^ 2 *
      (16 * C_mainAuxOne n + 2 * ((c⁻¹) ^ 2 * C_mainBumpOneLong n)) =
      C_mainBumpOne n := by
    calc
      c ^ 2 * (16 * C_mainAuxOne n +
          2 * ((c⁻¹) ^ 2 * C_mainBumpOneLong n)) =
          16 * c ^ 2 * C_mainAuxOne n + 2 * C_mainBumpOneLong n := by
            field_simp [hc.ne']
      _ = C_mainBumpOne n := by
            dsimp [c]
            simp only [C_mainBumpOne]
            ring
  have hfun : (fun x ↦ c * psi x) = fun x ↦ phi0 x := by
    funext x
    dsimp [psi]
    change c * (c⁻¹ * phi0 x) = phi0 x
    field_simp [hc.ne']
  rw [hC, hfun] at hrescaled
  exact hrescaled

/-- The numerical estimate in Lemma \ref{constant main bump one}. -/
theorem constantMainBumpOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOne n < (7 / 8 : ℝ) * (2 : ℝ) ^ 610 := by
  unfold C_mainBumpOne
  calc
    (2 : ℝ) ^ 4 * (3 * C_uniPair) ^ 2 * C_mainAuxOne n +
        2 * C_mainBumpOneLong n <
        (2 : ℝ) ^ 4 * (3 * C_uniPair) ^ 2 *
          ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) +
          2 * ((11 / 16 : ℝ) * (2 : ℝ) ^ 606) := by
          exact add_lt_add
            (mul_lt_mul_of_pos_left (aux_constantMainAuxOne_sharp hn)
              (by norm_num [C_uniPair]))
            (mul_lt_mul_of_pos_left (constantMainBumpOneLong hn) (by norm_num))
    _ < (7 / 8 : ℝ) * (2 : ℝ) ^ 610 := by
      set_option exponentiation.threshold 1000 in
        norm_num [C_uniPair]

/-- The constant in Lemma \ref{lem:main_aux2}. -/
noncomputable def C_mainAuxTwo (n : ℕ) : ℝ :=
  24 * C_mainAuxOne n

/-- Pad a finite strictly increasing sequence by one terminal exponent. -/
private theorem aux_mainAuxTwo_chain_to_dyadicChain (J : ℕ) (hJ : 0 < J)
    (ks : {u : Fin J → ℤ // StrictMono u}) :
    ∃ q : aux_dyadicChain J, ∀ j : Fin J, q.1 j.castSucc = ks.1 j := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ.ne'
  let qfun : Fin (K + 1 + 1) → ℤ :=
    Fin.lastCases (ks.1 (Fin.last K) + 1) ks.1
  have hqfun : StrictMono qfun := by
    intro i j hij
    by_cases hj : j = Fin.last (K + 1)
    · subst j
      have hilast : i < Fin.last (K + 1) := by simpa using hij
      let i' : Fin (K + 1) := ⟨i.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      rw [hi]
      simp only [qfun, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hle : ks.1 i' ≤ ks.1 (Fin.last K) := ks.2.monotone (Fin.le_last i')
      omega
    · have hjlast : j < Fin.last (K + 1) := Fin.lt_last_iff_ne_last.mpr hj
      let i' : Fin (K + 1) := ⟨i.1, by omega⟩
      let j' : Fin (K + 1) := ⟨j.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      have hj' : j = j'.castSucc := by rfl
      rw [hi, hj']
      simp only [qfun, Fin.lastCases_castSucc]
      apply ks.2
      simpa [i', j'] using hij
  refine ⟨⟨qfun, hqfun⟩, ?_⟩
  intro j
  simp only [qfun, Fin.lastCases_castSucc]

/-- The first auxiliary estimate, together with `bootstrap`, gives the dyadic
variation estimate required by the short-long reduction. -/
private theorem aux_mainAuxTwo_dyadic {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryTwoHypotheses psi)
    (f : ReductionNormalizedTuple n) :
    aux_dyadicVariationBound (4 * C_mainAuxOne n) (fun x ↦ psi x) f.1 := by
  intro J hJ k
  have hsup :
      (⨆ ks : {u : Fin J → ℤ // StrictMono u},
        ∑ j, eLpNorm
          (twistedAverageAtScale ((2 : ℝ) ^ (ks.1 j)) (fun x ↦ psi x)
            (fun i x ↦ f.1 i x)) 2 volume ^ 2) ≤
        ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    apply iSup_le
    intro ks
    obtain ⟨q, hq⟩ := aux_mainAuxTwo_chain_to_dyadicChain J hJ ks
    simpa only [mul_one, hq] using
      (mainAuxOne hn psi hpsi.1 f 1 (by norm_num) J hJ q)
  calc
    aux_dyadicJumpEnergy (fun x ↦ psi x) f.1 J k ≤
        twistedDyadicVariationEnergy (fun x ↦ psi x) (fun i x ↦ f.1 i x) J := by
      change twistedDyadicJumpEnergy (fun x ↦ psi x) (fun i x ↦ f.1 i x) J k ≤ _
      rw [twistedDyadicVariationEnergy]
      exact le_iSup (fun q : aux_dyadicChain J =>
        twistedDyadicJumpEnergy (fun x ↦ psi x) (fun i x ↦ f.1 i x) J q) k
    _ ≤ 4 * ⨆ ks : {u : Fin J → ℤ // StrictMono u},
        ∑ j, eLpNorm
          (twistedAverageAtScale ((2 : ℝ) ^ (ks.1 j)) (fun x ↦ psi x)
            (fun i x ↦ f.1 i x)) 2 volume ^ 2 :=
      bootstrap hn psi f.1 J
    _ ≤ 4 * (ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
      simpa [mul_comm] using mul_le_mul_left hsup 4
    _ = ENNReal.ofReal (4 * C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring

/-- Complexification commutes with the logarithmic-derivative operator. -/
private theorem aux_mainAuxTwo_T_cast_eq (f : SchwartzMap ℝ ℝ) :
    (fun x : ℝ ↦
      ((Codex.Reduction.BumpFunctions.aux_T
        (fun y : ℝ ↦ (f y : ℝ)) : ℝ → ℝ) x : ℂ)) =
      Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ (f x : ℂ)) := by
  funext x
  have hf : ContDiff ℝ 1 (fun y : ℝ ↦ f y) := by
    simpa using f.smooth 1
  have hdiff : DifferentiableAt ℝ (fun y : ℝ ↦ y * f y) x := by
    exact ((contDiff_id.mul hf).contDiffAt).differentiableAt (by norm_num)
  have hcast :
      deriv (fun y : ℝ ↦ ((y * f y : ℝ) : ℂ)) x =
        ((deriv (fun y : ℝ ↦ y * f y) x : ℝ) : ℂ) := by
    simpa using ((hasDerivAt_const x Complex.ofRealCLM).clm_apply hdiff.hasDerivAt).deriv
  have hfun : (fun y : ℝ ↦ ((y * f y : ℝ) : ℂ)) =
      Codex.Reduction.BumpFunctions.multiplicationOperatorX
        (fun y : ℝ ↦ (f y : ℂ)) := by
    funext y
    simp [Codex.Reduction.BumpFunctions.multiplicationOperatorX]
  have hfunreal :
      Codex.Reduction.BumpFunctions.multiplicationOperatorX
        (fun y : ℝ ↦ (f y : ℝ)) = fun y : ℝ ↦ y * f y := by
    funext y
    simp [Codex.Reduction.BumpFunctions.multiplicationOperatorX]
  unfold Codex.Reduction.BumpFunctions.aux_T
  rw [hfunreal, ← hfun, hcast]

/-- The Fourier support assumption for `psi` is stable under the logarithmic
derivative. -/
private theorem aux_mainAuxTwo_T_hyp (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryTwoHypotheses psi) :
    aux_mainAuxiliaryFourierHypotheses
      (Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ psi x)) := by
  have hTderiv : ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m (FourierTransform.fourier
        (fun x : ℝ ↦
          ((Codex.Reduction.BumpFunctions.aux_T
            (fun y : ℝ ↦ (psi y : ℝ)) : ℝ → ℝ) x : ℂ))) xi‖ ≤ 1 := by
    intro m hm xi
    rw [aux_mainAuxTwo_T_cast_eq psi]
    exact hpsi.2 m hm xi
  refine ⟨?_, hTderiv⟩
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ))
  have hFsupp : Function.support F ⊆
      Codex.Reduction.BumpFunctions.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
    simpa [F, aux_mainAuxiliaryTwoHypotheses, aux_mainAuxiliaryHypotheses,
      aux_mainAuxiliaryFourierHypotheses] using hpsi.1.1
  have hannulus_closed : IsClosed
      (Codex.Reduction.BumpFunctions.aux_annulusOne 1 ((2 : ℝ) ^ 2)) := by
    unfold Codex.Reduction.BumpFunctions.aux_annulusOne
    exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have hFtsupp : tsupport F ⊆
      Codex.Reduction.BumpFunctions.aux_annulusOne 1 ((2 : ℝ) ^ 2) :=
    closure_minimal hFsupp hannulus_closed
  have hderivSupp : Function.support (iteratedDeriv 1 F) ⊆
      Codex.Reduction.BumpFunctions.aux_annulusOne 1 ((2 : ℝ) ^ 2) :=
    (subset_tsupport _).trans
      ((Codex.Preliminaries.BumpsAndEstimates.aux_tsupport_iteratedDeriv_subset F 1).trans
        hFtsupp)
  intro xi hxi
  apply hderivSupp
  apply Function.mem_support.mpr
  intro hzero
  apply hxi
  let psiC : SchwartzMap ℝ ℂ :=
    psi.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hpsiC : (psiC : ℝ → ℂ) = fun x : ℝ ↦ (psi x : ℂ) := by
    funext x
    simp [psiC, SchwartzMap.postcompCLM_apply]
  have hformula :
      FourierTransform.fourier
        (Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ (psi x : ℂ))) xi =
        -((xi : ℂ) * iteratedDeriv 1 F xi) := by
    unfold F
    rw [← hpsiC]
    change FourierTransform.fourier
      (Codex.Reduction.BumpFunctions.aux_T (fun x : ℝ ↦ psiC x)) xi = _
    simpa [F] using
      (Codex.Reduction.BumpFunctions.fourierDerivativeMul psiC 0 xi)
  rw [aux_mainAuxTwo_T_cast_eq psi, hformula, hzero]
  simp

/-- Lemma \ref{lem:main_aux2}. -/
theorem mainAuxTwo {n : ℕ} (hn : 2 ≤ n) (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryTwoHypotheses psi)
    (f : ReductionNormalizedTuple n) :
    aux_variationBound (C_mainAuxTwo n) (fun x ↦ psi x) f.1 := by
  have hdyadic := aux_mainAuxTwo_dyadic hn psi hpsi f
  have hT := aux_mainAuxTwo_T_hyp psi hpsi
  rw [C_mainAuxTwo]
  convert shortLongFtcReduction hn psi hT f 1 (by norm_num)
    (4 * C_mainAuxOne n)
    (mul_pos (by norm_num) (aux_mainBumpOne_C_mainAuxOne_pos n)) hdyadic using 1;
    ring

/-- The numerical estimate in Lemma \ref{constant main auxiliary two}. -/
theorem constantMainAuxiliaryTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxTwo n < (2 : ℝ) ^ 578 := by
  unfold C_mainAuxTwo
  calc
    24 * C_mainAuxOne n < 24 * (2 : ℝ) ^ 573 :=
      mul_lt_mul_of_pos_left (constantMainAuxiliaryOne hn) (by norm_num)
    _ = 3 * (2 : ℝ) ^ 576 := by
      calc
        24 * (2 : ℝ) ^ 573 = 3 * ((2 : ℝ) ^ 3 * (2 : ℝ) ^ 573) := by
          norm_num
          ring
        _ = 3 * (2 : ℝ) ^ 576 := by rw [← pow_add]
    _ < 4 * (2 : ℝ) ^ 576 := by
      exact mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = (2 : ℝ) ^ 578 := by
      calc
        4 * (2 : ℝ) ^ 576 = (2 : ℝ) ^ 2 * (2 : ℝ) ^ 576 := by norm_num
        _ = (2 : ℝ) ^ (2 + 576) := by rw [← pow_add]
        _ = (2 : ℝ) ^ 578 := by norm_num

/-- The constant in Lemma \ref{lem:mainbump2}. -/
noncomputable def C_mainBumpTwo (n : ℕ) : ℝ :=
  C_mainAuxTwo n * C_absDerivFourierTPhiThreeLe 2 ^ 2

/-! Private Fourier, normalization, and scale-transport infrastructure for `mainBumpTwo`. -/

private theorem aux_mainBumpTwo_phiThree_eq_rescaled (b : windowBasedBumpFunctions)
    (k : ℤ) :
    windowBasedBumpFunctions.phiThree b k =
      fun x ↦ (2 : ℝ) ^ k * aux_oneRescaled ((2 : ℝ) ^ (-k))
        (windowBasedBumpFunctions.phiZero b k) x := by
  funext x
  rfl

private theorem aux_mainBumpTwo_phiThree_fourier_support_small
    (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) ⊆
      aux_frequencyAnnulus := by
  intro xi hxi
  have hne := Function.mem_support.mp hxi
  have htheta : FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.theta b x : ℂ)) xi ≠ 0 := by
    intro hzero
    rw [fourierPhiThreeEq] at hne
    simp [hzero] at hne
  exact (bumpBasic b).1 (Function.mem_support.mpr htheta)

private theorem aux_mainBumpTwo_frequencyAnnulus_subset_Icc :
    aux_frequencyAnnulus ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  rcases hx with hx | hx <;> exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem aux_mainBumpTwo_phiThree_fourier_support (b : windowBasedBumpFunctions)
    (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) ⊆
      Codex.Reduction.BumpFunctions.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
  intro xi hxi
  have hmem := aux_mainBumpTwo_phiThree_fourier_support_small b k hxi
  unfold Codex.Reduction.BumpFunctions.aux_annulusOne
  rcases hmem with hmem | hmem
  · constructor
    · rw [abs_of_nonpos (by linarith [hmem.2])]
      norm_num
      linarith [hmem.2]
    · rw [abs_of_nonpos (by linarith [hmem.2])]
      norm_num
      linarith [hmem.1]
  · constructor
    · rw [abs_of_nonneg (by linarith [hmem.1])]
      norm_num
      linarith [hmem.1]
    · rw [abs_of_nonneg (by linarith [hmem.1])]
      norm_num
      linarith [hmem.2]

private theorem aux_mainBumpTwo_phiThree_deriv_zero_outside
    (b : windowBasedBumpFunctions) (k : ℤ) (m : ℕ) (xi : ℝ)
    (hxi : xi ∉ Set.Icc (-1 : ℝ) 1) :
    iteratedDeriv m
      (FourierTransform.fourier
        (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi = 0 := by
  let F : ℝ → ℂ := FourierTransform.fourier
    (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))
  have hFtsupp : tsupport F ⊆ Set.Icc (-1 : ℝ) 1 :=
    closure_minimal
      ((aux_mainBumpTwo_phiThree_fourier_support_small b k).trans
        aux_mainBumpTwo_frequencyAnnulus_subset_Icc)
      isClosed_Icc
  have hderivSupp : Function.support (iteratedDeriv m F) ⊆ Set.Icc (-1 : ℝ) 1 :=
    (subset_tsupport _).trans
      ((Codex.Preliminaries.BumpsAndEstimates.aux_tsupport_iteratedDeriv_subset F m).trans
        hFtsupp)
  change iteratedDeriv m F xi = 0
  apply Function.notMem_support.mp
  intro hsupp
  exact hxi (hderivSupp hsupp)

private theorem aux_mainBumpTwo_phiThree_deriv_bound (b : windowBasedBumpFunctions)
    (k : ℤ) (m : ℕ) (hm : m < 3) (xi : ℝ) :
    ‖iteratedDeriv m
      (FourierTransform.fourier
        (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ ≤
      C_absDerivFourierTPhiThreeLe 2 := by
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have habs : |xi| ≤ 1 := abs_le.mpr hxi
    calc
      ‖iteratedDeriv m
          (FourierTransform.fourier
            (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ ≤
          C_absDerivFourierPhiThreeLe m :=
        absDerivFourierPhiThreeLe b m (by omega) k xi habs
      _ ≤ C_absDerivFourierTPhiThreeLe 2 := by
        interval_cases m <;>
          norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
            C_uniPair]
  · rw [aux_mainBumpTwo_phiThree_deriv_zero_outside b k m xi hxi]
    norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
      C_uniPair]

private theorem aux_mainBumpTwo_frequencyAnnulus_closed : IsClosed aux_frequencyAnnulus := by
  exact isClosed_Icc.union isClosed_Icc

private theorem aux_mainBumpTwo_phiThree_T_fourier_formula
    (b : windowBasedBumpFunctions) (k : ℤ) (m : ℕ) (xi : ℝ) :
    iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T
          (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi =
      - ((m : ℂ) * iteratedDeriv m
            (FourierTransform.fourier
              (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi +
          (xi : ℂ) * iteratedDeriv (m + 1)
            (FourierTransform.fourier
              (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi) := by
  simpa only [phiThreeSchwartz_apply] using
    aux_mainBumpOne_T_fourier_formula (phiThreeSchwartz b k) m xi

private theorem aux_mainBumpTwo_phiThree_T_fourier_support_small
    (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier (fun x : ℝ ↦
      (Codex.Reduction.SmoothingDecomposition.aux_T
        (windowBasedBumpFunctions.phiThree b k) x : ℂ))) ⊆ aux_frequencyAnnulus := by
  intro xi hxi
  have hne := Function.mem_support.mp hxi
  have hformula := aux_mainBumpTwo_phiThree_T_fourier_formula b k 0 xi
  simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul] at hformula
  rw [hformula] at hne
  have hderiv : iteratedDeriv 1
      (FourierTransform.fourier
        (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi ≠ 0 := by
    intro hzero
    simp [hzero] at hne
  let F : ℝ → ℂ := FourierTransform.fourier
    (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))
  have hFtsupp : tsupport F ⊆ aux_frequencyAnnulus :=
    closure_minimal (aux_mainBumpTwo_phiThree_fourier_support_small b k)
      aux_mainBumpTwo_frequencyAnnulus_closed
  have hderivSupp : Function.support (iteratedDeriv 1 F) ⊆ aux_frequencyAnnulus :=
    (subset_tsupport _).trans
      ((Codex.Preliminaries.BumpsAndEstimates.aux_tsupport_iteratedDeriv_subset F 1).trans
        hFtsupp)
  apply hderivSupp
  exact Function.mem_support.mpr hderiv

private theorem aux_mainBumpTwo_phiThree_T_deriv_zero_outside
    (b : windowBasedBumpFunctions) (k : ℤ) (m : ℕ) (xi : ℝ)
    (hxi : xi ∉ Set.Icc (-1 : ℝ) 1) :
    iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T
          (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi = 0 := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ ↦
    (Codex.Reduction.SmoothingDecomposition.aux_T
      (windowBasedBumpFunctions.phiThree b k) x : ℂ))
  have hFtsupp : tsupport F ⊆ Set.Icc (-1 : ℝ) 1 :=
    closure_minimal
      ((aux_mainBumpTwo_phiThree_T_fourier_support_small b k).trans
        aux_mainBumpTwo_frequencyAnnulus_subset_Icc)
      isClosed_Icc
  have hderivSupp : Function.support (iteratedDeriv m F) ⊆ Set.Icc (-1 : ℝ) 1 :=
    (subset_tsupport _).trans
      ((Codex.Preliminaries.BumpsAndEstimates.aux_tsupport_iteratedDeriv_subset F m).trans
        hFtsupp)
  change iteratedDeriv m F xi = 0
  apply Function.notMem_support.mp
  intro hsupp
  exact hxi (hderivSupp hsupp)

private theorem aux_mainBumpTwo_phiThree_T_deriv_bound (b : windowBasedBumpFunctions)
    (k : ℤ) (m : ℕ) (hm : m < 3) (xi : ℝ) :
    ‖iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T
          (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi‖ ≤
      C_absDerivFourierTPhiThreeLe 2 := by
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have habs : |xi| ≤ 1 := abs_le.mpr hxi
    exact (absDerivFourierTPhiThreeLe b m hm k xi habs).trans
      (by interval_cases m <;>
        norm_num [C_absDerivFourierTPhiThreeLe,
          C_absDerivFourierPhiThreeLe, C_uniPair])
  · rw [aux_mainBumpTwo_phiThree_T_deriv_zero_outside b k m xi hxi]
    norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
      C_uniPair]

private theorem aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_pos :
    0 < C_absDerivFourierTPhiThreeLe 2 := by
  norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
    C_uniPair]

private noncomputable def aux_mainBumpTwo_psi (b : windowBasedBumpFunctions)
    (k : ℤ) : SchwartzMap ℝ ℝ :=
  (C_absDerivFourierTPhiThreeLe 2)⁻¹ • phiThreeSchwartz b k

private theorem aux_mainBumpTwo_psi_apply (b : windowBasedBumpFunctions) (k : ℤ)
    (x : ℝ) :
    aux_mainBumpTwo_psi b k x = (C_absDerivFourierTPhiThreeLe 2)⁻¹ *
      windowBasedBumpFunctions.phiThree b k x := by
  simp [aux_mainBumpTwo_psi, smul_apply, phiThreeSchwartz_apply]

private theorem aux_mainBumpTwo_psi_fourier (b : windowBasedBumpFunctions) (k : ℤ)
    (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦ (aux_mainBumpTwo_psi b k x : ℂ)) xi =
      (((C_absDerivFourierTPhiThreeLe 2)⁻¹ : ℝ) : ℂ) *
        FourierTransform.fourier
          (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ)) xi := by
  rw [show (fun x : ℝ ↦ (aux_mainBumpTwo_psi b k x : ℂ)) =
      fun x ↦ (((C_absDerivFourierTPhiThreeLe 2)⁻¹ *
        windowBasedBumpFunctions.phiThree b k x : ℝ) : ℂ) by
        funext x
        norm_cast
        exact aux_mainBumpTwo_psi_apply b k x,
    aux_mainAuxOne_fourier_real_const_mul]

private theorem aux_mainBumpTwo_phiThree_smooth (b : windowBasedBumpFunctions)
    (k : ℤ) : ContDiff ℝ 1 (windowBasedBumpFunctions.phiThree b k) := by
  have hfun : windowBasedBumpFunctions.phiThree b k =
      fun x : ℝ ↦ phiThreeSchwartz b k x := by
    funext x
    exact (phiThreeSchwartz_apply b k x).symm
  rw [hfun]
  exact (phiThreeSchwartz b k).smooth 1

private theorem aux_mainBumpTwo_psi_T_fourier (b : windowBasedBumpFunctions) (k : ℤ)
    (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦
      (Codex.Reduction.SmoothingDecomposition.aux_T
        (fun y ↦ aux_mainBumpTwo_psi b k y) x : ℂ)) xi =
      (((C_absDerivFourierTPhiThreeLe 2)⁻¹ : ℝ) : ℂ) *
        FourierTransform.fourier (fun x : ℝ ↦
          (Codex.Reduction.SmoothingDecomposition.aux_T
            (windowBasedBumpFunctions.phiThree b k) x : ℂ)) xi := by
  rw [show (fun y : ℝ ↦ aux_mainBumpTwo_psi b k y) =
      fun y ↦ (C_absDerivFourierTPhiThreeLe 2)⁻¹ *
        windowBasedBumpFunctions.phiThree b k y by
        funext y
        exact aux_mainBumpTwo_psi_apply b k y,
    aux_mainBumpOne_T_const_mul _ _ (aux_mainBumpTwo_phiThree_smooth b k),
    aux_mainAuxOne_fourier_real_const_mul]

private theorem aux_mainBumpTwo_psi_hypotheses (b : windowBasedBumpFunctions)
    (k : ℤ) : aux_mainAuxiliaryTwoHypotheses (aux_mainBumpTwo_psi b k) := by
  let c : ℝ := C_absDerivFourierTPhiThreeLe 2
  have hc : 0 < c := by
    exact aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_pos
  constructor
  · constructor
    · intro xi hxi
      have hne := Function.mem_support.mp hxi
      rw [aux_mainBumpTwo_psi_fourier] at hne
      have hrawne : FourierTransform.fourier
          (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ)) xi ≠ 0 :=
        (mul_ne_zero_iff.mp hne).2
      exact aux_mainBumpTwo_phiThree_fourier_support b k
        (Function.mem_support.mpr hrawne)
    · intro m hm xi
      change ‖iteratedDeriv m
        (fun z : ℝ => FourierTransform.fourier
          (fun x : ℝ ↦ (aux_mainBumpTwo_psi b k x : ℂ)) z) xi‖ ≤ 1
      have hformula :
          (fun z : ℝ => FourierTransform.fourier
            (fun x : ℝ ↦ (aux_mainBumpTwo_psi b k x : ℂ)) z) =
            fun z => ((c⁻¹ : ℝ) : ℂ) * FourierTransform.fourier
              (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ)) z := by
        funext z
        simpa [c] using aux_mainBumpTwo_psi_fourier b k z
      rw [hformula, iteratedDeriv_const_mul_field]
      have hraw := aux_mainBumpTwo_phiThree_deriv_bound b k m hm xi
      change ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
        (FourierTransform.fourier
          (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ ≤ 1
      calc
        ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
            (FourierTransform.fourier
              (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ =
            c⁻¹ * ‖iteratedDeriv m
              (FourierTransform.fourier
                (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hc)]
        _ ≤ c⁻¹ * c := by
              exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
        _ = 1 := by field_simp [hc.ne']
  · intro m hm xi
    have hsmooth : ContDiff ℝ 1 (fun y : ℝ => aux_mainBumpTwo_psi b k y) :=
      (aux_mainBumpTwo_psi b k).smooth 1
    rw [← aux_mainBumpOne_T_cast_eq _ hsmooth]
    change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T
          (fun y ↦ aux_mainBumpTwo_psi b k y) x : ℂ)) z) xi‖ ≤ 1
    have hformula :
        (fun z : ℝ => FourierTransform.fourier (fun x : ℝ ↦
          (Codex.Reduction.SmoothingDecomposition.aux_T
            (fun y ↦ aux_mainBumpTwo_psi b k y) x : ℂ)) z) =
          fun z => ((c⁻¹ : ℝ) : ℂ) * FourierTransform.fourier (fun x : ℝ ↦
            (Codex.Reduction.SmoothingDecomposition.aux_T
              (windowBasedBumpFunctions.phiThree b k) x : ℂ)) z := by
      funext z
      simpa [c] using aux_mainBumpTwo_psi_T_fourier b k z
    rw [hformula, iteratedDeriv_const_mul_field]
    have hraw := aux_mainBumpTwo_phiThree_T_deriv_bound b k m hm xi
    change ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Codex.Reduction.SmoothingDecomposition.aux_T
          (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi‖ ≤ 1
    calc
      ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
          (FourierTransform.fourier (fun x : ℝ ↦
            (Codex.Reduction.SmoothingDecomposition.aux_T
              (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi‖ =
          c⁻¹ * ‖iteratedDeriv m
            (FourierTransform.fourier (fun x : ℝ ↦
              (Codex.Reduction.SmoothingDecomposition.aux_T
                (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hc)]
      _ ≤ c⁻¹ * c := by
            exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
      _ = 1 := by field_simp [hc.ne']

private theorem aux_mainBumpTwo_twistedAverageAtScale_oneRescaled {n : ℕ}
    (phi : ℝ → ℝ) (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (t lambda : ℝ) (ht : 0 < t) (hlambda : 0 < lambda) :
    twistedAverageAtScale t (aux_oneRescaled lambda phi) f =
      twistedAverageAtScale (t * lambda) phi f := by
  unfold twistedAverageAtScale twistedAverage aux_oneRescaled
  funext x
  congr 1
  funext s
  congr 1
  field_simp [ht.ne', hlambda.ne']

private def aux_mainBumpTwo_scaleMul (lambda : ℝ) (hlambda : 0 < lambda)
    {J : ℕ} (t : aux_scaleChain J) : aux_scaleChain J :=
  ⟨fun j ↦ lambda * t.1 j,
    ⟨by
      intro i j hij
      exact mul_lt_mul_of_pos_left (t.2.1 hij) hlambda,
    by
      intro j
      exact mul_pos hlambda (t.2.2 j)⟩⟩

private theorem aux_mainBumpTwo_variationBound_of_oneRescaled {n : ℕ} (lambda : ℝ)
    (hlambda : 0 < lambda) (A : ℝ) (phi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hA : aux_variationBound A (aux_oneRescaled lambda phi) f) :
    aux_variationBound A phi f := by
  intro J hJ t
  let t' : aux_scaleChain J := aux_mainBumpTwo_scaleMul lambda⁻¹ (inv_pos.mpr hlambda) t
  have hscale (j : Fin (J + 1)) : t'.1 j * lambda = t.1 j := by
    dsimp [t', aux_mainBumpTwo_scaleMul]
    field_simp [hlambda.ne']
  have hEq : aux_jumpEnergy (aux_oneRescaled lambda phi) f J t' =
      aux_jumpEnergy phi f J t := by
    unfold aux_jumpEnergy twistedJumpEnergy
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    funext x
    rw [aux_mainBumpTwo_twistedAverageAtScale_oneRescaled phi (fun i y ↦ f i y)
      (t'.1 j.succ) lambda (t'.2.2 j.succ) hlambda,
      aux_mainBumpTwo_twistedAverageAtScale_oneRescaled phi (fun i y ↦ f i y)
        (t'.1 j.castSucc) lambda (t'.2.2 j.castSucc) hlambda,
      hscale j.succ, hscale j.castSucc]
  calc
    aux_jumpEnergy phi f J t = aux_jumpEnergy (aux_oneRescaled lambda phi) f J t' :=
      hEq.symm
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
      hA J hJ t'

/-- Lemma \ref{lem:mainbump2}. -/
theorem mainBumpTwo {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : -2 ≤ k) :
    aux_variationBound (C_mainBumpTwo n * (2 : ℝ) ^ (-2 * k))
      (windowBasedBumpFunctions.phiZero b k) f.1 := by
  let c : ℝ := C_absDerivFourierTPhiThreeLe 2
  have hc : 0 < c := aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_pos
  have hmain : aux_variationBound (C_mainAuxTwo n)
      (fun x ↦ aux_mainBumpTwo_psi b k x) f.1 :=
    mainAuxTwo hn (aux_mainBumpTwo_psi b k)
      (aux_mainBumpTwo_psi_hypotheses b k) f
  have hphiThree' := aux_mainBumpOne_variationBound_const_mul c hc.le
    (C_mainAuxTwo n) (fun x ↦ aux_mainBumpTwo_psi b k x) f.1 hmain
  have hC : c ^ 2 * C_mainAuxTwo n = C_mainBumpTwo n := by
    dsimp [c]
    rw [C_mainBumpTwo]
    ring
  have hfun : (fun x ↦ c * aux_mainBumpTwo_psi b k x) =
      windowBasedBumpFunctions.phiThree b k := by
    funext x
    rw [aux_mainBumpTwo_psi_apply]
    change c * (c⁻¹ * windowBasedBumpFunctions.phiThree b k x) =
      windowBasedBumpFunctions.phiThree b k x
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hC, hfun] at hphiThree'
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hrescaled' := aux_mainBumpOne_variationBound_const_mul a⁻¹
    (inv_nonneg.mpr ha.le) (C_mainBumpTwo n)
    (windowBasedBumpFunctions.phiThree b k) f.1 hphiThree'
  have hfunrescaled : (fun x ↦ a⁻¹ * windowBasedBumpFunctions.phiThree b k x) =
      aux_oneRescaled ((2 : ℝ) ^ (-k)) (windowBasedBumpFunctions.phiZero b k) := by
    funext x
    rw [aux_mainBumpTwo_phiThree_eq_rescaled]
    dsimp [a]
    field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity]
  rw [hfunrescaled] at hrescaled'
  have hrescaled := aux_mainBumpTwo_variationBound_of_oneRescaled ((2 : ℝ) ^ (-k))
    (by positivity) ((a⁻¹) ^ 2 * C_mainBumpTwo n)
    (windowBasedBumpFunctions.phiZero b k) f.1 hrescaled'
  have hCscale : (a⁻¹) ^ 2 * C_mainBumpTwo n =
      C_mainBumpTwo n * (2 : ℝ) ^ (-2 * k) := by
    dsimp [a]
    rw [← zpow_neg]
    rw [show (-2 * k : ℤ) = (-k) * 2 by ring, zpow_mul]
    exact mul_comm _ _
  rw [hCscale] at hrescaled
  exact hrescaled

private theorem aux_mainBumpTwo_C_mainAuxTwo_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxTwo n < (4191 / 8192 : ℝ) * (2 : ℝ) ^ 578 := by
  unfold C_mainAuxTwo
  calc
    24 * C_mainAuxOne n < 24 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) :=
      mul_lt_mul_of_pos_left (aux_constantMainAuxOne_sharp hn) (by norm_num)
    _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ 578 := by
      calc
        24 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) =
            ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 5) * (2 : ℝ) ^ 573 := by
              norm_num
              ring
        _ = (4191 / 8192 : ℝ) * ((2 : ℝ) ^ 5 * (2 : ℝ) ^ 573) := by ring
        _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ 578 := by rw [← pow_add]

private theorem aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_sharp :
    C_absDerivFourierTPhiThreeLe 2 <
      (41 / 64 : ℝ) * (2 : ℝ) ^ 41 := by
  set_option exponentiation.threshold 1000 in
    norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
      C_uniPair]

/-- The numerical estimate in Lemma \ref{constant main bump two}. -/
theorem constantMainBumpTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpTwo n < (27 / 32 : ℝ) * (2 : ℝ) ^ 658 := by
  let c : ℝ := C_absDerivFourierTPhiThreeLe 2
  let d : ℝ := (41 / 64 : ℝ) * (2 : ℝ) ^ 41
  have hc : 0 < c := aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_pos
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hcd : c < d := by
    simpa [c, d] using aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_sharp
  have hsq : c ^ 2 < d ^ 2 :=
    (sq_lt_sq₀ hc.le hd.le).2 hcd
  have haux := aux_mainBumpTwo_C_mainAuxTwo_sharp hn
  unfold C_mainBumpTwo
  calc
    C_mainAuxTwo n * C_absDerivFourierTPhiThreeLe 2 ^ 2 <
        ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 578) *
          C_absDerivFourierTPhiThreeLe 2 ^ 2 := by
      exact mul_lt_mul_of_pos_right haux (sq_pos_of_pos hc)
    _ < ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 578) * d ^ 2 := by
      exact mul_lt_mul_of_pos_left (by simpa [c] using hsq) (by positivity)
    _ = ((4191 / 8192 : ℝ) * (41 / 64 : ℝ) ^ 2) * (2 : ℝ) ^ 660 := by
      dsimp [d]
      rw [mul_pow, ← pow_mul]
      calc
        (4191 / 8192 : ℝ) * (2 : ℝ) ^ 578 *
            ((41 / 64 : ℝ) ^ 2 * (2 : ℝ) ^ (41 * 2)) =
            ((4191 / 8192 : ℝ) * (41 / 64 : ℝ) ^ 2) *
              ((2 : ℝ) ^ 578 * (2 : ℝ) ^ (41 * 2)) := by ring
        _ = ((4191 / 8192 : ℝ) * (41 / 64 : ℝ) ^ 2) * (2 : ℝ) ^ 660 := by
          rw [← pow_add]
    _ < (27 / 128 : ℝ) * (2 : ℝ) ^ 660 := by
      apply mul_lt_mul_of_pos_right
      · norm_num
      · positivity
    _ = (27 / 32 : ℝ) * (2 : ℝ) ^ 658 := by
      rw [show (660 : ℕ) = 2 + 658 by norm_num, pow_add]
      norm_num
      ring

/-- The constant in Lemma \ref{lem:leftbump}. -/
noncomputable def C_leftBump (n : ℕ) : ℝ :=
  C_mainAuxTwo n * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2

private noncomputable def aux_leftBump_psi (b : windowBasedBumpFunctions) :
    SchwartzMap ℝ ℝ :=
  ((2 : ℝ) ^ 14 * C_uniPair)⁻¹ • thetaTildeSchwartz b

private theorem aux_leftBump_psi_apply (b : windowBasedBumpFunctions) (x : ℝ) :
    aux_leftBump_psi b x = ((2 : ℝ) ^ 14 * C_uniPair)⁻¹ *
      windowBasedBumpFunctions.thetaTilde b x := by
  simp [aux_leftBump_psi, smul_apply, thetaTildeSchwartz_apply]

private theorem aux_leftBump_psi_fourier (b : windowBasedBumpFunctions) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (aux_leftBump_psi b x : ℂ)) xi =
      ((((2 : ℝ) ^ 14 * C_uniPair)⁻¹ : ℝ) : ℂ) *
        FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) xi := by
  rw [show (fun x : ℝ => (aux_leftBump_psi b x : ℂ)) =
      fun x => ((((2 : ℝ) ^ 14 * C_uniPair)⁻¹ *
        windowBasedBumpFunctions.thetaTilde b x : ℝ) : ℂ) by
        funext x
        rw [aux_leftBump_psi_apply],
    aux_mainAuxOne_fourier_real_const_mul]

private theorem aux_leftBump_psi_hypotheses (b : windowBasedBumpFunctions) :
    aux_mainAuxiliaryTwoHypotheses (aux_leftBump_psi b) := by
  let c : ℝ := (2 : ℝ) ^ 14 * C_uniPair
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  constructor
  · constructor
    · intro xi hxi
      have hne := Function.mem_support.mp hxi
      rw [aux_leftBump_psi_fourier] at hne
      have hrawne : FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) xi ≠ 0 :=
        (mul_ne_zero_iff.mp hne).2
      have hprim := thetaPrimitive b 2 (by norm_num) (by norm_num [N_uniPair])
      exact hprim.1.2 (hprim.1.1 (Function.mem_support.mpr hrawne))
    · intro m hm xi
      change ‖iteratedDeriv m
        (fun z : ℝ => FourierTransform.fourier
          (fun x : ℝ => (aux_leftBump_psi b x : ℂ)) z) xi‖ ≤ 1
      have hformula :
          (fun z : ℝ => FourierTransform.fourier
            (fun x : ℝ => (aux_leftBump_psi b x : ℂ)) z) =
            fun z => ((c⁻¹ : ℝ) : ℂ) * FourierTransform.fourier
              (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) z := by
        funext z
        simpa [c] using aux_leftBump_psi_fourier b z
      rw [hformula, iteratedDeriv_const_mul_field]
      have hraw := thetaTildeFourier_deriv_bound b m (Nat.le_of_lt hm) xi
      change ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
        (FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))) xi‖ ≤ 1
      calc
        ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
            (FourierTransform.fourier
              (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))) xi‖ =
            c⁻¹ * ‖iteratedDeriv m
              (FourierTransform.fourier
                (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))) xi‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hc)]
        _ ≤ c⁻¹ * c :=
          mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
        _ = 1 := by field_simp [hc.ne']
  · intro m hm xi
    have hsmooth : ContDiff ℝ 1 (fun y : ℝ => aux_leftBump_psi b y) :=
      (aux_leftBump_psi b).smooth 1
    rw [← aux_mainBumpOne_T_cast_eq _ hsmooth]
    change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier (fun x : ℝ =>
        (Codex.Reduction.SmoothingDecomposition.aux_T
          (fun y => aux_leftBump_psi b y) x : ℂ)) z) xi‖ ≤ 1
    have hsmoothTheta : ContDiff ℝ 1
        (windowBasedBumpFunctions.thetaTilde b) := by
      have hfun : (fun x : ℝ => thetaTildeSchwartz b x) =
          windowBasedBumpFunctions.thetaTilde b := by
        funext x
        exact thetaTildeSchwartz_apply b x
      rw [← hfun]
      exact (thetaTildeSchwartz b).smooth 1
    have hformula :
        (fun z : ℝ => FourierTransform.fourier (fun x : ℝ =>
          (Codex.Reduction.SmoothingDecomposition.aux_T
            (fun y => aux_leftBump_psi b y) x : ℂ)) z) =
          fun z => ((c⁻¹ : ℝ) : ℂ) * FourierTransform.fourier
            (fun x : ℝ => (Codex.Reduction.SmoothingDecomposition.aux_T
              (windowBasedBumpFunctions.thetaTilde b) x : ℂ)) z := by
      funext z
      rw [show (fun y : ℝ => aux_leftBump_psi b y) =
          fun y => c⁻¹ * windowBasedBumpFunctions.thetaTilde b y by
            funext y
            simpa [c] using aux_leftBump_psi_apply b y,
        aux_mainBumpOne_T_const_mul c⁻¹ (windowBasedBumpFunctions.thetaTilde b) hsmoothTheta,
        aux_mainAuxOne_fourier_real_const_mul]
    rw [hformula, iteratedDeriv_const_mul_field]
    have hraw := tThetaTildeFourier_deriv_bound b m hm xi
    change ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ =>
        (Codex.Reduction.SmoothingDecomposition.aux_T
          (windowBasedBumpFunctions.thetaTilde b) x : ℂ))) xi‖ ≤ 1
    calc
      ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
          (FourierTransform.fourier (fun x : ℝ =>
            (Codex.Reduction.SmoothingDecomposition.aux_T
              (windowBasedBumpFunctions.thetaTilde b) x : ℂ))) xi‖ =
          c⁻¹ * ‖iteratedDeriv m
            (FourierTransform.fourier (fun x : ℝ =>
              (Codex.Reduction.SmoothingDecomposition.aux_T
                (windowBasedBumpFunctions.thetaTilde b) x : ℂ))) xi‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hc)]
      _ ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
      _ = 1 := by field_simp [hc.ne']

private theorem aux_leftBump_phiOne_eq_scaled_thetaTilde (b : windowBasedBumpFunctions)
    (k : ℤ) :
    windowBasedBumpFunctions.phiOne b k =
      fun x => (2 : ℝ) ^ k *
        aux_oneRescaled ((2 : ℝ) ^ k) (windowBasedBumpFunctions.thetaTilde b) x := by
  funext x
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let g : ℝ → ℝ := fun z => aux_indicator (Set.Ici 0) z *
    windowBasedBumpFunctions.theta b (a⁻¹ * x - z)
  have hind (y : ℝ) :
      aux_indicator (Set.Ici 0) (a⁻¹ * y) = aux_indicator (Set.Ici 0) y := by
    have hmem : a⁻¹ * y ∈ Set.Ici (0 : ℝ) ↔ y ∈ Set.Ici (0 : ℝ) := by
      change 0 ≤ a⁻¹ * y ↔ 0 ≤ y
      exact mul_nonneg_iff_of_pos_left (inv_pos.mpr ha)
    unfold aux_indicator
    by_cases hy : y ∈ Set.Ici (0 : ℝ)
    · have hy' : a⁻¹ * y ∈ Set.Ici (0 : ℝ) := hmem.mpr hy
      simp [hy, hy']
    · have hy' : a⁻¹ * y ∉ Set.Ici (0 : ℝ) := fun h => hy (hmem.mp h)
      simp [hy, hy']
  have hleft :
      (∫ y : ℝ, aux_indicator (Set.Ici 0) y *
        Codex.Reduction.SmoothingDecomposition.aux_realRescaled a
          (windowBasedBumpFunctions.theta b) (x - y)) =
        a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := by
    calc
      (∫ y : ℝ, aux_indicator (Set.Ici 0) y *
          Codex.Reduction.SmoothingDecomposition.aux_realRescaled a
            (windowBasedBumpFunctions.theta b) (x - y)) =
          ∫ y : ℝ, a⁻¹ * g (a⁻¹ * y) := by
            apply integral_congr_ae
            filter_upwards [] with y
            dsimp [g, Codex.Reduction.SmoothingDecomposition.aux_realRescaled]
            rw [hind]
            ring
      _ = a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := by
        rw [integral_const_mul]
  have hchange := Measure.integral_comp_inv_mul_left g a
  rw [abs_of_pos ha, smul_eq_mul] at hchange
  change (∫ y : ℝ, aux_indicator (Set.Ici 0) y *
      Codex.Reduction.SmoothingDecomposition.aux_realRescaled a
        (windowBasedBumpFunctions.theta b) (x - y)) =
    a * (a⁻¹ * ∫ y : ℝ, aux_indicator (Set.Ici 0) y *
      windowBasedBumpFunctions.theta b (a⁻¹ * x - y))
  calc
    (∫ y : ℝ, aux_indicator (Set.Ici 0) y *
        Codex.Reduction.SmoothingDecomposition.aux_realRescaled a
          (windowBasedBumpFunctions.theta b) (x - y)) =
        a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := hleft
    _ = a⁻¹ * (a * ∫ y : ℝ, g y) := by rw [hchange]
    _ = ∫ y : ℝ, g y := by field_simp [ha.ne']
    _ = a * (a⁻¹ * ∫ y : ℝ, aux_indicator (Set.Ici 0) y *
        windowBasedBumpFunctions.theta b (a⁻¹ * x - y)) := by
          dsimp [g]
          field_simp [ha.ne']


/-- Lemma \ref{lem:leftbump}. -/
theorem leftBump {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) :
    aux_variationBound (C_leftBump n * (2 : ℝ) ^ (2 * k))
      (windowBasedBumpFunctions.phiOne b k) f.1 := by
  let c : ℝ := (2 : ℝ) ^ 14 * C_uniPair
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  have hmain : aux_variationBound (C_mainAuxTwo n)
      (fun x => aux_leftBump_psi b x) f.1 :=
    mainAuxTwo hn (aux_leftBump_psi b) (aux_leftBump_psi_hypotheses b) f
  have htheta' := aux_mainBumpOne_variationBound_const_mul c hc.le (C_mainAuxTwo n)
    (fun x => aux_leftBump_psi b x) f.1 hmain
  have hC : c ^ 2 * C_mainAuxTwo n = C_leftBump n := by
    dsimp [c, C_leftBump]
    ring
  have hfun : (fun x => c * aux_leftBump_psi b x) =
      windowBasedBumpFunctions.thetaTilde b := by
    funext x
    rw [aux_leftBump_psi_apply]
    change c * (c⁻¹ * windowBasedBumpFunctions.thetaTilde b x) =
      windowBasedBumpFunctions.thetaTilde b x
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hC, hfun] at htheta'
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hcomp : aux_oneRescaled a⁻¹
      (aux_oneRescaled a (windowBasedBumpFunctions.thetaTilde b)) =
      windowBasedBumpFunctions.thetaTilde b := by
    funext x
    unfold aux_oneRescaled
    field_simp [ha.ne']
  rw [← hcomp] at htheta'
  have hrescaled := aux_mainBumpTwo_variationBound_of_oneRescaled a⁻¹ (inv_pos.mpr ha)
    (C_leftBump n) (aux_oneRescaled a (windowBasedBumpFunctions.thetaTilde b))
    f.1 htheta'
  have hphi' := aux_mainBumpOne_variationBound_const_mul a ha.le (C_leftBump n)
    (aux_oneRescaled a (windowBasedBumpFunctions.thetaTilde b)) f.1 hrescaled
  have hphifun : (fun x => a * aux_oneRescaled a
      (windowBasedBumpFunctions.thetaTilde b) x) =
      windowBasedBumpFunctions.phiOne b k := by
    funext x
    dsimp [a]
    exact congrFun (aux_leftBump_phiOne_eq_scaled_thetaTilde b k).symm x
  have hCscale : a ^ 2 * C_leftBump n =
      C_leftBump n * (2 : ℝ) ^ (2 * k) := by
    dsimp [a]
    calc
      ((2 : ℝ) ^ k) ^ 2 * C_leftBump n =
          C_leftBump n * ((2 : ℝ) ^ k) ^ 2 := by ring
      _ = C_leftBump n * (2 : ℝ) ^ (k * 2) := by
        rw [zpow_mul]
        rfl
      _ = C_leftBump n * (2 : ℝ) ^ (2 * k) := by
        congr 2
        ring
  rw [hCscale, hphifun] at hphi'
  exact hphi'


/-- The numerical estimate in Lemma \ref{constant left bump}. -/
theorem constantLeftBump {n : ℕ} (hn : 2 ≤ n) :
    C_leftBump n < (33 / 64 : ℝ) * (2 : ℝ) ^ 636 := by
  have haux := aux_mainBumpTwo_C_mainAuxTwo_sharp hn
  have hcpos : 0 < ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 := by
    norm_num [C_uniPair]
  have hcsq : ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 = (2 : ℝ) ^ 58 := by
    rw [C_uniPair, ← pow_add, ← pow_mul]
  unfold C_leftBump
  calc
    C_mainAuxTwo n * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 <
        ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 578) *
          ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 :=
      mul_lt_mul_of_pos_right haux hcpos
    _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ 636 := by
      rw [hcsq]
      calc
        ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 578) * (2 : ℝ) ^ 58 =
            (4191 / 8192 : ℝ) * ((2 : ℝ) ^ 578 * (2 : ℝ) ^ 58) := by
              ring
        _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ (578 + 58) := by
              rw [← pow_add]
        _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ 636 := by norm_num
    _ < (33 / 64 : ℝ) * (2 : ℝ) ^ 636 := by
      apply mul_lt_mul_of_pos_right
      · norm_num
      · positivity


/-- Fubini for a first prism form whose kernel is a compact parameter integral. -/
private theorem aux_leftBumpOneShort_prismBrascampLiebForm_setIntegral
    {d : ℕ} (K : ℝ → KKernel 1) (Kint : KKernel 1)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ)
    (hKint : ∀ z : RealVector 1 × ℝ,
      Kint z = ∫ t : ℝ in Set.Icc (1 : ℝ) 2, K t z)
    (hInt : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      K q.1 (q.2.1.2 - q.2.1.1, coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.2.1 q.2.2 h i))
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume)) :
    prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) Kint
      (fun i x => F i x) =
      ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
        prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
          (fun i x => F i x) := by
  let P : KKernel 1 → ((RealVector 1 × RealVector 1) × RealVector (d + 1)) → ℝ :=
    fun L q =>
      L (q.1.2 - q.1.1, coordinateSum q.1.1 + coordinateSum q.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.1 q.2 h i)
  have hInt' : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) => P (K q.1) q.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
    simpa [P] using hInt
  have hPint : Integrable (P Kint) := by
    have h := hInt'.integral_prod_right
    refine h.congr ?_
    filter_upwards [] with q
    dsimp [P]
    rw [hKint]
    rw [integral_mul_const]
  have hIntSwap : Integrable
      (Function.uncurry (fun q : ((RealVector 1 × RealVector 1) ×
        RealVector (d + 1)) => fun t : ℝ => P (K t) q))
      (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
    convert hInt'.swap using 1
    funext q
    rcases q with ⟨q, t⟩
    rfl
  change (∫ y : RealVector 1 × RealVector 1, ∫ x : RealVector (d + 1),
      P Kint (y, x)) = _
  calc
    (∫ y : RealVector 1 × RealVector 1, ∫ x : RealVector (d + 1),
        P Kint (y, x)) =
        ∫ q : ((RealVector 1 × RealVector 1) × RealVector (d + 1)),
          P Kint q := by
          simpa only [Measure.volume_eq_prod] using
            (integral_prod (P Kint) hPint).symm
    _ = ∫ q : ((RealVector 1 × RealVector 1) × RealVector (d + 1)),
        ∫ t : ℝ in Set.Icc (1 : ℝ) 2, P (K t) q := by
          apply integral_congr_ae
          filter_upwards [] with q
          dsimp [P]
          rw [hKint]
          rw [integral_mul_const]
    _ = ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
        ∫ q : ((RealVector 1 × RealVector 1) × RealVector (d + 1)),
          P (K t) q := by
          simpa only [Function.uncurry, Measure.volume_eq_prod] using
            integral_integral_swap hIntSwap
    _ = ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
        prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
          (fun i x => F i x) := by
          apply integral_congr_ae
          filter_upwards [hInt'.prod_right_ae] with t ht
          calc
            ∫ q : ((RealVector 1 × RealVector 1) × RealVector (d + 1)),
                P (K t) q =
                ∫ y : RealVector 1 × RealVector 1, ∫ x : RealVector (d + 1),
                  P (K t) (y, x) := by
                    simpa only [Measure.volume_eq_prod] using
                      integral_prod (P (K t)) ht
            _ = prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
                (fun i x => F i x) := by
                  rfl

/-- The nonnegative extended-real form of the preceding compact-parameter Fubini step. -/
private theorem aux_leftBumpOneShort_lintegral_energy_eq_prism_of_setIntegral
    {d : ℕ} (K : ℝ → KKernel 1) (Kint : KKernel 1)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ)
    (E : ℝ → ℝ≥0∞)
    (hKint : ∀ z : RealVector 1 × ℝ,
      Kint z = ∫ t : ℝ in Set.Icc (1 : ℝ) 2, K t z)
    (hInt : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      K q.1 (q.2.1.2 - q.2.1.1, coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.2.1 q.2.2 h i))
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume))
    (hPint : Integrable (fun t : ℝ =>
      prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
        (fun i x => F i x)) (volume.restrict (Set.Icc (1 : ℝ) 2)))
    (hPnonneg : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      0 ≤ prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
        (fun i x => F i x))
    (hE : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      E t = ENNReal.ofReal
        (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
          (fun i x => F i x))) :
    ∫⁻ t in Set.Icc (1 : ℝ) 2, E t =
      ENNReal.ofReal
        (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) Kint
          (fun i x => F i x)) := by
  calc
    ∫⁻ t in Set.Icc (1 : ℝ) 2, E t =
        ∫⁻ t in Set.Icc (1 : ℝ) 2, ENNReal.ofReal
          (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
            (fun i x => F i x)) := by
          exact lintegral_congr_ae hE
    _ = ENNReal.ofReal (∫ t : ℝ in Set.Icc (1 : ℝ) 2,
          prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
            (fun i x => F i x)) := by
          exact (ofReal_integral_eq_lintegral_ofReal hPint hPnonneg).symm
    _ = ENNReal.ofReal
        (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) Kint
          (fun i x => F i x)) := by
          rw [← aux_leftBumpOneShort_prismBrascampLiebForm_setIntegral K Kint F hKint hInt]

private noncomputable def aux_leftBumpOneShort_integralM
    (s : ℝ) (psi : SchwartzMap ℝ ℝ) : MKernel 1 :=
  fun y => aux_integralFctKernelAtScale s (fun x => psi x)
    (WithLp.toLp 2 ![y.1 0, y.2 0])

private noncomputable def aux_leftBumpOneShort_scaleK
    (s : ℝ) (psi : SchwartzMap ℝ ℝ) (t : ℝ) : KKernel 1 :=
  fun z => t⁻¹ * Codex.Reduction.BumpFunctions.aux_realRescaled (s * t)
      (fun x => psi x) (z.1 0 + z.2) *
    Codex.Reduction.BumpFunctions.aux_realRescaled (s * t)
      (fun x => psi x) z.2

private theorem aux_leftBumpOneShort_mToK_integralM_eq_setIntegral
    (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (z : RealVector 1 × ℝ) :
    mToK 1 (by omega) (aux_leftBumpOneShort_integralM s psi) z =
      ∫ t : ℝ in Set.Icc (1 : ℝ) 2, aux_leftBumpOneShort_scaleK s psi t z := by
  unfold mToK
  rw [aux_integral_realVector_zero]
  have hpoint : mToKPoint 1 (by omega) z (default : RealVector 0) =
      ((fun _ : Fin 1 => z.1 0 + z.2), fun _ : Fin 1 => z.2) := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [mToKPoint, lastIndex, coordinateSum]
  rw [hpoint]
  unfold aux_leftBumpOneShort_integralM aux_leftBumpOneShort_scaleK
  rw [integralFctKernelAtScale_eq s hs.ne' (fun x => psi x)
    (WithLp.toLp 2 ![z.1 0 + z.2, z.2])]
  apply integral_congr_ae
  filter_upwards [] with t
  simp
  ring

private theorem aux_leftBumpOneShort_scaleK_eq_mToK_tensor
    (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (t : ℝ) (ht : 0 < t) :
    aux_leftBumpOneShort_scaleK s psi t = fun z => t⁻¹ *
      mToK 1 (by omega)
        (fun y : RealVector 1 × RealVector 1 =>
          aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.1 0) *
            aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.2 0)) z := by
  funext z
  unfold aux_leftBumpOneShort_scaleK
  rw [Codex.Reduction.AToLambda.aux_aToLambda.mToK_oneTensorSquare_eq]
  rw [aux_mainAuxOne_windowSchwartz_apply, aux_mainAuxOne_windowSchwartz_apply]
  simp only [Codex.Reduction.BumpFunctions.aux_realRescaled, aux_windowRescale]
  ring

private theorem aux_leftBumpOneShort_prism_scaleK_eq_tensor
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (t : ℝ) (ht : 0 < t)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ) :
    prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
      (aux_leftBumpOneShort_scaleK s psi t) (fun i x => F i x) =
      t⁻¹ * prismForm (d + 1) 1 (by omega) (by omega)
        (fun y : RealVector 1 × RealVector 1 =>
          aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.1 0) *
            aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.2 0))
        (fun i x => F i x) := by
  rw [show aux_leftBumpOneShort_scaleK s psi t = fun z => t⁻¹ *
      mToK 1 (by omega)
        (fun y : RealVector 1 × RealVector 1 =>
          aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.1 0) *
            aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.2 0)) z by
      exact aux_leftBumpOneShort_scaleK_eq_mToK_tensor s hs psi t ht]
  unfold prismBrascampLiebForm prismForm
  simp only [mul_assoc]
  simp_rw [integral_const_mul]
  rfl

private theorem aux_leftBumpOneShort_energy_eq_scaleK_prism
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (t : ℝ) (ht : 0 < t)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    ENNReal.ofReal t⁻¹ *
      eLpNorm (twistedAverageAtScale (s * t) (fun x => psi x)
        (fun i x => f i x)) 2 volume ^ 2 =
      ENNReal.ofReal
        (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
          (aux_leftBumpOneShort_scaleK s psi t)
          (fun i x => Codex.Reduction.AToLambda.aux_aToLambda.transformedFunctions f i x)) := by
  rw [← aux_mainAuxOne_twistedAverage_window psi (s * t) (mul_pos hs ht)]
  rw [aToLambda_transformed]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  congr 1
  exact (aux_leftBumpOneShort_prism_scaleK_eq_tensor d s hs psi t ht
    (Codex.Reduction.AToLambda.aux_aToLambda.transformedFunctions f)).symm


private theorem aux_leftBumpOneShort_prism_parameter_integrable
    {d : ℕ} (K : ℝ → KKernel 1)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ)
    (hInt : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      K q.1 (q.2.1.2 - q.2.1.1, coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.2.1 q.2.2 h i))
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume)) :
    Integrable (fun t : ℝ =>
      prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
        (fun i x => F i x)) (volume.restrict (Set.Icc (1 : ℝ) 2)) := by
  let P : KKernel 1 → ((RealVector 1 × RealVector 1) × RealVector (d + 1)) → ℝ :=
    fun L q =>
      L (q.1.2 - q.1.1, coordinateSum q.1.1 + coordinateSum q.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.1 q.2 h i)
  have hInt' : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) => P (K q.1) q.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
    simpa [P] using hInt
  have h := hInt'.integral_prod_left
  refine h.congr ?_
  filter_upwards [hInt'.prod_right_ae] with t ht
  dsimp [P]
  simpa [P, prismBrascampLiebForm, Measure.volume_eq_prod] using
    (integral_prod (P (K t)) ht)

private theorem aux_leftBumpOneShort_prism_scaleK_nonnegative
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (t : ℝ) (ht : 0 < t)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ) :
    0 ≤ prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
      (aux_leftBumpOneShort_scaleK s psi t) (fun i x => F i x) := by
  rw [aux_leftBumpOneShort_prism_scaleK_eq_tensor d s hs psi t ht F]
  apply mul_nonneg (inv_nonneg.mpr ht.le)
  apply aux_prism_one_rankOne_nonnegative (d + 1) (by omega) 1 (by norm_num)
    (aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht)) F
  · exact mToK_memW0 (d + 1) 1 (by omega) (by omega) _
      (Codex.Reduction.AToLambda.aux_aToLambda.oneTensorSquare_memW0
        (aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht)))
  · intro u
    rw [Codex.Reduction.AToLambda.aux_aToLambda.mToK_oneTensorSquare_eq]
    ring

private theorem aux_leftBumpOneShort_scaleK_triple_integrable
    (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) :
    Integrable (fun q : ℝ × (RealVector 1 × ℝ) =>
      aux_leftBumpOneShort_scaleK s psi q.1 q.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (1 : ℝ) 2)
  let H : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ := fun q =>
    Codex.Reduction.BumpFunctions.aux_realRescaled (s * q.1) (fun x => psi x) (q.2 0) *
      Codex.Reduction.BumpFunctions.aux_realRescaled (s * q.1) (fun x => psi x) (q.2 1) * q.1⁻¹
  have hH : Integrable H (μ.prod volume) := by
    simpa [μ, H] using
      (integralFctKernelAtScale_triple_integrable psi s hs).re
  let e1 : RealVector 1 ≃ᵐ ℝ :=
    MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have he1 : MeasurePreserving e1 volume volume := by
    simpa [e1] using volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
  have hpre : MeasurePreserving (fun w : RealVector 1 × ℝ => (e1 w.1, w.2))
      volume volume := by
    change MeasurePreserving (Prod.map e1 id) volume volume
    simpa only [Measure.volume_eq_prod] using
      he1.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hshear : MeasurePreserving (fun p : ℝ × ℝ => (p.1 + p.2, p.2))
      volume volume := by
    change MeasurePreserving (fun p : ℝ × ℝ => (p.1 + p.2, p.2))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume)
    exact measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  let e2 : EuclideanSpace ℝ (Fin 2) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he2 : MeasurePreserving e2 volume volume := by
    simpa [e2] using
      (PiLp.volume_preserving_toLp (Fin 2)).symm.trans
        (MeasureTheory.volume_preserving_finTwoArrow ℝ)
  have he2inv : MeasurePreserving e2.symm volume volume := he2.symm e2
  let e : RealVector 1 × ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun w => e2.symm (e1 w.1 + w.2, w.2)
  have he : MeasurePreserving e volume volume := by
    have hcomp := he2inv.comp (hshear.comp hpre)
    convert hcomp using 1
    funext w
    rfl
  have heprod : MeasurePreserving (Prod.map id e) (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).prod he
  have hcomp := heprod.integrable_comp_of_integrable hH
  refine hcomp.congr ?_
  filter_upwards [] with q
  dsimp [Function.comp_apply, H, e, e1, e2, aux_leftBumpOneShort_scaleK]
  simp
  ring

/-- The parameterized version of the absolute-integrability core for a first prism.
The scale parameter is carried inertly through the standard prism coordinates. -/
private theorem aux_leftBumpOneShort_parameterized_prismIntegrand
    (d : ℕ) (μ : Measure ℝ) [SFinite μ]
    (K : ℝ → KKernel 1)
    (hKmeas : Measurable (Function.uncurry K))
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ)
    (hcore : Integrable (fun q : ℝ ×
      ((RealVector 1 × ℝ) × RealVector (d + 1)) =>
      K q.1 q.2.1 *
        F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega)
          (0 : Fin (d + 1))) q.2.2)
      (μ.prod volume)) :
    Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      K q.1 (q.2.1.2 - q.2.1.1,
        coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega)
              q.2.1 q.2.2 h i))
      (μ.prod volume) := by
  classical
  let n : ℕ := d + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  let I := (Fin 1 → Fin 2) × Fin n
  let a : I := (fun _ => 0, 0)
  let P : I → (RealVector 1 × ℝ) × RealVector n → ℝ := fun hi w =>
    F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)
      (aux_prismPullback n 1 hn hi.1 hi.2 w.1.1 w.1.2 w.2)
  let D : ℝ × ((RealVector 1 × ℝ) × RealVector n) → ℝ := fun q =>
    K q.1 q.2.1 * P a q.2
  let R : (RealVector 1 × ℝ) × RealVector n → ℝ := fun w =>
    ∏ hi ∈ (Finset.univ.erase a), P hi w
  let C : ℝ := ∏ hi ∈ (Finset.univ.erase a),
    SchwartzMap.seminorm ℝ 0 0 (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2))
  let H : ℝ × ((RealVector 1 × ℝ) × RealVector n) → ℝ := fun q =>
    K q.1 q.2.1 * ∏ hi : I, P hi q.2
  have hPmeas (hi : I) : Measurable (P hi) := by
    dsimp [P]
    exact (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)).continuous.measurable.comp
      (aux_measurable_prismPullback n 1 hn hi.1 hi.2)
  have hRbound (w : (RealVector 1 × ℝ) × RealVector n) : ‖R w‖ ≤ C := by
    dsimp [R, C]
    calc
      ‖∏ hi ∈ Finset.univ.erase a, P hi w‖ ≤
          ∏ hi ∈ Finset.univ.erase a, ‖P hi w‖ :=
        Finset.norm_prod_le _ _
      _ ≤ ∏ hi ∈ Finset.univ.erase a,
          SchwartzMap.seminorm ℝ 0 0
            (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)) := by
          gcongr with hi hhi
          exact (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)).norm_le_seminorm ℝ _
  have hfactor (q : ℝ × ((RealVector 1 × ℝ) × RealVector n)) : H q = D q * R q.2 := by
    dsimp [H, D, R]
    rw [← Finset.mul_prod_erase Finset.univ (fun hi => P hi q.2)
      (Finset.mem_univ a)]
    ring
  have hbound (q : ℝ × ((RealVector 1 × ℝ) × RealVector n)) :
      ‖H q‖ ≤ C * ‖D q‖ := by
    rw [hfactor]
    calc
      ‖D q * R q.2‖ = ‖D q‖ * ‖R q.2‖ := norm_mul _ _
      _ ≤ ‖D q‖ * C := mul_le_mul_of_nonneg_left (hRbound q.2) (norm_nonneg _)
      _ = C * ‖D q‖ := mul_comm _ _
  let skew : (RealVector 1 × ℝ) × RealVector n →
      (RealVector 1 × ℝ) × RealVector n :=
    fun w => (w.1, aux_prismPullback n 1 hn a.1 a.2 w.1.1 w.1.2 w.2)
  have hskew : MeasurePreserving skew volume volume := by
    dsimp [skew]
    exact aux_measurePreserving_prismPullbackSkew n 1 hn a.1 a.2
  let liftSkew : ℝ × ((RealVector 1 × ℝ) × RealVector n) →
      ℝ × ((RealVector 1 × ℝ) × RealVector n) :=
    Prod.map id skew
  have hliftSkew : MeasurePreserving liftSkew (μ.prod volume) (μ.prod volume) := by
    dsimp [liftSkew]
    exact (MeasurePreserving.id μ).prod hskew
  have hcore' : Integrable (fun q : ℝ × ((RealVector 1 × ℝ) × RealVector n) =>
      K q.1 q.2.1 *
        F (prismIndex (n := n) (k := 1) (by omega) hn a.2) q.2.2)
      (μ.prod volume) := by
    simpa [a] using hcore
  have hD : Integrable D (μ.prod volume) := by
    have hcomp := hliftSkew.integrable_comp_of_integrable hcore'
    simpa [D, liftSkew, P, Function.comp_def] using hcomp
  have hKsource : Measurable (fun q : ℝ × ((RealVector 1 × ℝ) × RealVector n) =>
      K q.1 q.2.1) := by
    exact hKmeas.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hHmeas : Measurable H := by
    dsimp [H]
    apply hKsource.mul
    apply Finset.measurable_fun_prod Finset.univ
    intro hi _
    exact (hPmeas hi).comp measurable_snd
  have hH : Integrable H (μ.prod volume) := by
    have hDom : Integrable (fun q => C * ‖D q‖) (μ.prod volume) := hD.norm.const_mul C
    exact hDom.mono' hHmeas.aestronglyMeasurable (ae_of_all _ hbound)
  let assoc : RealVector 1 × (ℝ × RealVector n) ≃ᵐ
      (RealVector 1 × ℝ) × RealVector n := MeasurableEquiv.prodAssoc.symm
  have hassoc : MeasurePreserving assoc volume volume := by
    dsimp [assoc]
    exact (MeasureTheory.volume_preserving_prodAssoc).symm _
  let liftAssoc : ℝ × (RealVector 1 × (ℝ × RealVector n)) ≃ᵐ
      ℝ × ((RealVector 1 × ℝ) × RealVector n) :=
    (MeasurableEquiv.refl ℝ).prodCongr assoc
  have hliftAssoc : MeasurePreserving liftAssoc (μ.prod volume) (μ.prod volume) := by
    dsimp [liftAssoc]
    exact (MeasurePreserving.id μ).prod hassoc
  let G : ℝ × ((RealVector 1 × RealVector 1) × RealVector n) → ℝ := fun q =>
    K q.1 (q.2.1.2 - q.2.1.1, coordinateSum q.2.1.1 + coordinateSum q.2.2) *
      ∏ h : Fin 1 → Fin 2, ∏ i : Fin n,
        F (prismIndex (n := n) (k := 1) (by omega) hn i)
          (prismPoint (n := n) (k := 1) (by omega) hn q.2.1 q.2.2 h i)
  let liftCoords : ℝ × (RealVector 1 × (ℝ × RealVector n)) →
      ℝ × ((RealVector 1 × RealVector 1) × RealVector n) :=
    Prod.map id (aux_prismCoordinates n 1 hn)
  have hliftCoords : MeasurePreserving liftCoords (μ.prod volume) (μ.prod volume) := by
    dsimp [liftCoords]
    exact (MeasurePreserving.id μ).prod (aux_measurePreserving_prismCoordinates n 1 hn)
  have hGH : G ∘ liftCoords = H ∘ liftAssoc := by
    funext q
    dsimp [G, H, liftCoords, liftAssoc, assoc, P]
    rw [aux_prismCoordinates_kernelArguments n 1 hn q.2.1 q.2.2.1 q.2.2.2]
    congr 1
    change
      (∏ h : Fin 1 → Fin 2, ∏ i : Fin n,
        F (prismIndex (n := n) (k := 1) (by omega) hn i)
          (prismPoint (n := n) (k := 1) (by omega) hn
            (aux_prismCoordinates n 1 hn q.2).1
            (aux_prismCoordinates n 1 hn q.2).2 h i)) =
      ∏ hi : (Fin 1 → Fin 2) × Fin n,
        F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)
          (aux_prismPullback n 1 hn hi.1 hi.2
            q.2.1 q.2.2.1 q.2.2.2)
    rw [← Fintype.prod_prod_type']
    apply Finset.prod_congr rfl
    intro hi _
    exact congrArg (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2))
      (aux_prismPoint_eq_prismPullbackCoordinates n 1 (by omega) hn
        q.2.1 q.2.2.1 q.2.2.2 hi.1 hi.2)
  have hGcomp : Integrable (G ∘ liftCoords) (μ.prod volume) := by
    rw [hGH]
    exact hliftAssoc.integrable_comp_of_integrable hH
  have hGmeas : Measurable G := by
    dsimp [G]
    have harg : Measurable (fun q : ℝ ×
        ((RealVector 1 × RealVector 1) × RealVector n) =>
        (q.1, (q.2.1.2 - q.2.1.1,
          coordinateSum q.2.1.1 + coordinateSum q.2.2))) := by
      exact measurable_fst.prodMk
        (((measurable_snd.fst.snd.sub measurable_snd.fst.fst).prodMk
        (((aux_continuous_coordinateSum 1).measurable.comp measurable_snd.fst.fst).add
          ((aux_continuous_coordinateSum n).measurable.comp measurable_snd.snd))))
    have hkernel : Measurable (fun q : ℝ ×
        ((RealVector 1 × RealVector 1) × RealVector n) =>
        K q.1 (q.2.1.2 - q.2.1.1,
          coordinateSum q.2.1.1 + coordinateSum q.2.2)) := by
      simpa [Function.comp_def] using hKmeas.comp harg
    refine hkernel.mul ?_
    apply Finset.measurable_fun_prod Finset.univ
    intro h _
    apply Finset.measurable_fun_prod Finset.univ
    intro i _
    have hpointCont : Continuous (fun q : ℝ ×
        ((RealVector 1 × RealVector 1) × RealVector n) =>
        prismPoint (n := n) (k := 1) (by omega) hn q.2.1 q.2.2 h i) := by
      apply continuous_pi
      intro j
      unfold prismPoint concatVector
      split_ifs with hj
      · unfold cubeCorner
        split_ifs <;> fun_prop
      · unfold eraseVector
        fun_prop
    exact (F (prismIndex (n := n) (k := 1) (by omega) hn i)).continuous.measurable.comp
      hpointCont.measurable
  have hG := (hliftCoords.integrable_comp hGmeas.aestronglyMeasurable).mp hGcomp
  simpa [G] using hG

private theorem aux_leftBumpOneShort_scaleK_prism_core_integrable
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ) :
    Integrable (fun q : ℝ × ((RealVector 1 × ℝ) × RealVector (d + 1)) =>
      aux_leftBumpOneShort_scaleK s psi q.1 q.2.1 *
        F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) (0 : Fin (d + 1)))
          q.2.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
  have hK := aux_leftBumpOneShort_scaleK_triple_integrable s hs psi
  have hF : Integrable
      (F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega)
        (0 : Fin (d + 1))) : RealVector (d + 1) → ℝ) :=
    (F _).integrable
  let assoc : ((ℝ × (RealVector 1 × ℝ)) × RealVector (d + 1)) ≃ᵐ
      ℝ × ((RealVector 1 × ℝ) × RealVector (d + 1)) :=
    MeasurableEquiv.prodAssoc
  have hassoc : MeasurePreserving assoc
      (((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume).prod volume)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod (volume.prod volume)) := by
    dsimp [assoc]
    exact MeasureTheory.measurePreserving_prodAssoc _ _ _
  have hprod := hK.mul_prod hF
  have hcomp := (hassoc.symm assoc).integrable_comp_of_integrable hprod
  rw [Measure.volume_eq_prod (RealVector 1 × ℝ) (RealVector (d + 1))]
  convert hcomp using 1
  rfl

private theorem aux_leftBumpOneShort_scaleK_prism_joint_integrable
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ) :
    Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      aux_leftBumpOneShort_scaleK s psi q.1 (q.2.1.2 - q.2.1.1,
        coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.2.1 q.2.2 h i))
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
  exact aux_leftBumpOneShort_parameterized_prismIntegrand d
    (volume.restrict (Set.Icc (1 : ℝ) 2)) (aux_leftBumpOneShort_scaleK s psi)
    (by
      unfold aux_leftBumpOneShort_scaleK Codex.Reduction.BumpFunctions.aux_realRescaled
      fun_prop) F (aux_leftBumpOneShort_scaleK_prism_core_integrable d s hs psi F)

/-- Continuous `A`-to-`Λ₁` for the integral kernel used in the two short estimates. -/
private theorem aux_leftBumpOneShort_continuous_aToLambda_integralFct
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    ∫⁻ t in Set.Icc (1 : ℝ) 2,
      ENNReal.ofReal t⁻¹ *
        eLpNorm (twistedAverageAtScale (s * t) (fun x => psi x)
          (fun i x => f i x)) 2 volume ^ 2 =
      ENNReal.ofReal
        (prismForm (d + 1) 1 (by omega) (by omega)
          (aux_leftBumpOneShort_integralM s psi)
          (fun i x => Codex.Reduction.AToLambda.aux_aToLambda.transformedFunctions f i x)) := by
  let F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ :=
    Codex.Reduction.AToLambda.aux_aToLambda.transformedFunctions f
  have hInt := aux_leftBumpOneShort_scaleK_prism_joint_integrable d s hs psi F
  have hPint := aux_leftBumpOneShort_prism_parameter_integrable
    (aux_leftBumpOneShort_scaleK s psi) F hInt
  have hPnonneg : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      0 ≤ prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
        (aux_leftBumpOneShort_scaleK s psi t) (fun i x => F i x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact aux_leftBumpOneShort_prism_scaleK_nonnegative d s hs psi t
      (lt_of_lt_of_le zero_lt_one ht.1) F
  have hE : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      ENNReal.ofReal t⁻¹ *
        eLpNorm (twistedAverageAtScale (s * t) (fun x => psi x)
          (fun i x => f i x)) 2 volume ^ 2 =
        ENNReal.ofReal
          (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
            (aux_leftBumpOneShort_scaleK s psi t) (fun i x => F i x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa [F] using aux_leftBumpOneShort_energy_eq_scaleK_prism d s hs psi t
      (lt_of_lt_of_le zero_lt_one ht.1) f
  have hmain := aux_leftBumpOneShort_lintegral_energy_eq_prism_of_setIntegral
    (K := aux_leftBumpOneShort_scaleK s psi)
    (Kint := mToK 1 (by omega) (aux_leftBumpOneShort_integralM s psi)) F
    (fun t => ENNReal.ofReal t⁻¹ *
      eLpNorm (twistedAverageAtScale (s * t) (fun x => psi x)
        (fun i x => f i x)) 2 volume ^ 2)
    (aux_leftBumpOneShort_mToK_integralM_eq_setIntegral s hs psi)
    hInt hPint hPnonneg hE
  simpa [prismForm, F] using hmain


/-- The first short-variation constant in Lemma \ref{lem:leftbump1_short1}. -/
noncomputable def C_leftBumpOneShortOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 2 * C_inductPositiveTermsReductionWhitney n * C_thetaPrimitive 2 ^ 2 *
    C_thetaTOffcenter

/-- Lemma \ref{lem:leftbump1_short1}. -/
theorem leftBumpOneShortOne {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (k : ℤ) (hk : k ≤ -1) (J : ℕ) (hJ : 0 < J)
    (ell : aux_dyadicChain J) :
    ∑ j : Fin J,
      ENNReal.ofReal (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)) *
        ∫⁻ t in Set.Icc (1 : ℝ) 2,
          ENNReal.ofReal t⁻¹ *
            eLpNorm
              (twistedAverageAtScale ((2 : ℝ) ^ (ell.1 j.castSucc) * t)
                (windowBasedBumpFunctions.phiFour b k) (fun i x ↦ f.1 i x))
              2 volume ^ 2 ≤
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
    ∑ j : Fin J,
      ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2)) *
        ∫⁻ t in Set.Icc (1 : ℝ) 2,
          ENNReal.ofReal t⁻¹ *
            eLpNorm
              (twistedAverageAtScale ((2 : ℝ) ^ (ell.1 j.castSucc) * t)
                (Codex.Reduction.BumpFunctions.aux_T (windowBasedBumpFunctions.phiFour b k))
                (fun i x ↦ f.1 i x))
              2 volume ^ 2 ≤
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
    aux_dyadicVariationBound (C_leftBumpOneLong n * Real.rpow 2 ((k : ℝ) / 2))
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
    aux_variationBound (C_leftBumpOne n * Real.rpow 2 ((k : ℝ) / 2))
      (windowBasedBumpFunctions.phiTwo b k) f.1 := by
  sorry

/-- The numerical estimate in Lemma \ref{constant left bump one}. -/
theorem constantLeftBumpOne {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOne n < (23 / 32 : ℝ) * (2 : ℝ) ^ 636 := by
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
