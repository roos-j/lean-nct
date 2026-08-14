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
    (hApos : 0 < A) (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1) :
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
    C_mainBumpOneLongTwo n < (8 / 9 : ℝ) * (2 : ℝ) ^ 543 := by
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
    C_mainBumpOneLong n < (11 / 16 : ℝ) * (2 : ℝ) ^ 606 := by
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
    C_mainBumpOne n < (7 / 8 : ℝ) * (2 : ℝ) ^ 610 := by
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
    C_mainBumpTwo n < (27 / 32 : ℝ) * (2 : ℝ) ^ 658 := by
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
    C_leftBump n < (33 / 64 : ℝ) * (2 : ℝ) ^ 636 := by
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
